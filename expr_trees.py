from collections import namedtuple
import itertools as it
from multiprocessing import Process, shared_memory
from multiprocessing.managers import SharedMemoryManager
import time
import mpmath as mp
import numpy as np

Op = namedtuple('Op', ['symbol', 'priority', 'associative'])

Plus = Op('+', 0, True)
Minus = Op('-', 0, False)
Mul = Op('*', 1, True)
Div = Op('/', 1, False)
Pow = Op('^', 2, False)
BaseConv = Op('_', 3, False)
# Variable used later.
_OPS = [Plus, Minus, Mul, Div, Pow, BaseConv]


def gen_expr_trees(n, u, i):
    if i == n:
        yield []
        return
    cnt = max(0, i + 1 - u)
    for x in range(cnt if (i+1 == n) else 0, cnt + 1):
        for y in gen_expr_trees(n, u+x, i+1):
            yield [x] + y


def expr_trees(n, u, i):
    if i == n:
        return [[]]
    cnt = max(0, i + 1 - u)
    s = []
    for x in range(cnt if (i+1 == n) else 0, cnt + 1):
        s.extend([[x] + y for y in expr_trees(n, u+x, i+1)])
    return s


def gen_psfx(ls, ops):
    if len(ls) == 1:
        yield ls
        return
    for op in ops:
        for i in range(1, len(ls)):
            r1 = psfx(ls[:i], ops)
            r2 = psfx(ls[i:], ops)
            for a, b in it.product(r1, r2):
                yield a + b + op


def psfx(ls, ops):
    if len(ls) == 1:
        return ls
    r = []
    for op in ops:
        for i in range(1, len(ls)):
            r1 = psfx(ls[:i], ops)
            r2 = psfx(ls[i:], ops)
            for a, b in it.product(r1, r2):
                r.append(a + b + op)
    return r


_P = dict((op.symbol, op.priority) for op in _OPS)
_ASSOC = set([op.symbol for op in _OPS if op.associative])
_OPERATORS = set([op.symbol for op in _OPS])


def td_psfx_cnt(n, all_ops):
    m = dict()
    reduced_tree_ops = dict((cur_op, ''.join(
        op for op in all_ops
        if _P[op] < _P[cur_op] or _P[op] > _P[cur_op] or op not in _ASSOC
    )) for cur_op in all_ops)

    def recur(n, ops):
        if n == 1:
            return 1
        if (n, ops) in m:
            return m[(n, ops)]
        r = 0
        for op in ops:
            lops = reduced_tree_ops[op]
            rops = all_ops
            for i in range(1, n):
                r1 = recur(i, lops)
                r2 = recur(n-i, rops)
                r += r1 * r2
        m[(n, ops)] = r
        return r
    return recur(n, all_ops)


def td_psfx(vs, all_ops):
    reduced_tree_ops = dict((cur_op, ''.join(
        op for op in all_ops
        if _P[op] < _P[cur_op] or _P[op] > _P[cur_op] or op not in _ASSOC
    )) for cur_op in all_ops)

    def recur(ls, ops):
        if len(ls) == 1:
            return ls
        r = []
        for op in ops:
            lops = reduced_tree_ops[op]
            rops = all_ops
            for i in range(1, len(ls)):
                r1 = recur(ls[:i], lops)
                r2 = recur(ls[i:], rops)
                for a, b in it.product(r1, r2):
                    r.append(a + b + op)
        return r
    return recur(vs, all_ops)


def gen_td_psfx(vs, all_ops):
    reduced_tree_ops = dict((cur_op, ''.join(
        op for op in all_ops
        if _P[op] < _P[cur_op] or _P[op] > _P[cur_op] or op not in _ASSOC
    )) for cur_op in all_ops)

    def recur(ls, ops):
        if len(ls) == 1:
            yield ls
            return
        for op in ops:
            lops = reduced_tree_ops[op]
            rops = all_ops
            for i in range(1, len(ls)):
                r1 = recur(ls[:i], lops)
                r2 = recur(ls[i:], rops)
                for a, b in it.product(r1, r2):
                    yield a + b + op
    return recur(vs, all_ops)


def pset(s):
    n = len(s)
    for r in range(1, n+1):
        for c in it.combinations(s, r):
            yield c


def seq_cnts():
    for op_set in pset("+-*/^"):
        seq = []
        for i in range(0, 9):
            s = "123456789"[:i]
            seq.append(str(sum(1 for _ in td_psfx(s, op_set))))
        print(''.join(list(op_set)), ' '.join(seq))


def choose_sum(n, i, choices):
    # choices: [(c1, int), (c2, int)...]
    if n <= 0 or i >= len(choices):
        return [[]]
    cnt = min(n, choices[i][1])
    leftover = sum(map(lambda x: x[1], choices[i+1:]))
    start = max(0, n - leftover)
    s = []
    for j in range(start, cnt + 1):
        res = choose_sum(n - j, i + 1, choices)
        if j == 0:
            s.extend(res)
            continue
        for y in res:
            y.append((choices[i][0], j))
        s.extend(res)

    return s


def eval_psfx(pf):
    _OPERATORS = {
        '+': lambda x, y: x + y,
        '-': lambda x, y: x - y,
        '*': lambda x, y: x * y,
        '/': lambda x, y: x / y,
        '^': lambda x, y: x ** y
    }

    def apply_op(at, bt, op):
        a, _ = at
        b, _ = bt
        if a is None or b is None:
            return None
        try:
            return _OPERATORS[op](a, b)
        except Exception:
            return None

    s = []
    for c in pf:
        if c not in _OPERATORS:
            s.append((mp.mpc(c), ""))
            continue
        b, a = s.pop(), s.pop()
        d = apply_op(a, b, c)
        s.append((d, c))
    return s.pop()[0]


def postfix_to_infix(pf):
    def _apply_op(at, bt, op):
        a, op1 = at
        b, op2 = bt
        left_b = len(a) > 1 and _P[op1] < _P[op]
        right_b = len(b) > 1 and (
            _P[op2] < _P[op] or
            _P[op2] == _P[op] and op not in _ASSOC)
        s = " " + op + " "
        s = ("({:})" if left_b else "{:}") + s
        s = s + ("({:})" if right_b else "{:}")
        return s.format(a, b)
    s = []
    for c in pf:
        if c not in _OPERATORS:
            s.append((c, ""))
            continue
        b, a = s.pop(), s.pop()
        d = _apply_op(a, b, c)
        s.append((d, c))
    return s.pop()[0]


def chunker(seq, size):
    return (seq[pos:pos + size] for pos in range(0, len(seq), size))


def infxR_to_psfx_map(pfs):
    m = dict()
    for pf in pfs:
        infx = postfix_to_infix(pf)
        ls = m.setdefault(infx, [])
        ls.append(pf)
    return m


def eval_f(task_mem_name, res_mem_name, status_mem_name, start_time_mem_name,
           cur_idx_mem_name,
           status_idx, start_idx, end_idx, goal,
           arr_dim, arr_dtype):
    goal = mp.mpc(goal)

    pfs_mem = shared_memory.SharedMemory(name=task_mem_name)
    pfs = np.ndarray(arr_dim, dtype=arr_dtype, buffer=pfs_mem.buf)
    res_mem = shared_memory.SharedMemory(name=res_mem_name)
    res = np.ndarray(len(res_mem.buf), dtype=np.int8, buffer=res_mem.buf)
    status = shared_memory.ShareableList(name=status_mem_name)
    start_time = shared_memory.ShareableList(name=start_time_mem_name)
    cur_idx_mem = shared_memory.SharedMemory(name=cur_idx_mem_name)
    cur_idx = np.ndarray(
        len(cur_idx_mem.buf)//8, dtype=np.int64, buffer=cur_idx_mem.buf)
    status[status_idx] = "ACQMEM"
    for i in range(start_idx, end_idx):
        status[status_idx] = "CALC"
        start_time[status_idx] = time.time()
        cur_idx[status_idx] = i
        res[i] = -1
        r = eval_psfx(pfs[i].decode('ascii'))
        res[i] = r == goal
    status[status_idx] = "DONE"


def parallel_eval_expr(n, ops, goal, timeout=5, proc_cnt=5):
    s = "123456789"[:n]
    q_type = np.dtype('a' + str(2*len(s)))
    q = np.array(td_psfx(s, ops), dtype=q_type)
    q.sort()
    task_cnt = len(q)
    task_block_size = task_cnt // proc_cnt

    task_ranges = []
    for i in range(proc_cnt):
        start_idx = i * task_block_size
        end_idx = (i + 1) * task_block_size if i + 1 != proc_cnt else task_cnt
        task_ranges.append((start_idx, end_idx))
    smm = SharedMemoryManager()
    smm.start()
    task_mem = smm.SharedMemory(size=q.nbytes)
    tq = np.ndarray(len(q), dtype=q_type, buffer=task_mem.buf)
    tq[:] = q[:]
    del q
    res_mem = smm.SharedMemory(size=len(tq))
    res = np.ndarray(len(tq), dtype=np.int8, buffer=res_mem.buf)
    start_time_mem = smm.ShareableList([0.] * proc_cnt)
    status_mem = smm.ShareableList(["IDLE"] * proc_cnt)
    cur_idx_mem = smm.SharedMemory(size=proc_cnt * 8)
    cur_idx = np.ndarray(proc_cnt, dtype=np.int64, buffer=cur_idx_mem.buf)
    processes = [None] * proc_cnt
    restarts = [0] * proc_cnt
    cur_t = time.time()
    while not all(status_mem[i] == "DONE" for i in range(proc_cnt)):
        try:
            for i, p in enumerate(processes):
                if p is None:
                    continue
                status = status_mem[i]
                if status == "DONE":
                    continue
                start_t = start_time_mem[i]
                idx = cur_idx[i]
                if (cur_t - start_t) > timeout:
                    p.kill()
                    if idx < 0:
                        continue
                    res[idx] = -1

            for i, p in enumerate(processes):
                if p is not None and p.is_alive():
                    continue
                start_t = start_time_mem[i]
                status = status_mem[i]
                idx = cur_idx[i]
                end_idx = task_ranges[i][1]
                if status == "DONE":
                    try:
                        p.close()
                    except Exception:
                        pass
                    processes[i] = None
                    continue
                try:
                    p.close()
                except Exception:
                    pass
                restarts[i] += 1
                processes[i] = Process(
                    target=eval_f,
                    args=(task_mem.name,
                          res_mem.name,
                          status_mem.shm.name,
                          start_time_mem.shm.name,
                          cur_idx_mem.name,
                          i,
                          idx + 1,  # skipping the one that takes too long
                          end_idx,
                          goal,
                          len(tq), q_type)
                )
                processes[i].start()
        except Exception:
            import traceback
            traceback.print_exc()

        cur_t = time.time()
        time.sleep(max(1, timeout - 1))
        print("Status: {:}|Found: {:d}".format(' '.join(
                status_mem[i][0] + " " + str(r)
                for (r, i) in zip(restarts, range(proc_cnt))
            ), np.sum(res > 0))
        )

    for p in processes:
        if p is None:
            continue
        p.join()
        p.close()

    for i, pf in enumerate(tq):
        pf = pf.decode('ascii')
        m = res[i]
        if m == -1:
            print("TLE", pf)
            continue
        if m == 0:
            continue
        print(eval_psfx(pf), '==', postfix_to_infix(pf), pf)

    smm.shutdown()
