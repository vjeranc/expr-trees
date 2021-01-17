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


def bracket_condition(op1, op):
    # Consider expression ((a op1 b) op c):
    # If op1 is of lower priority than op then brackets need to stay. If the
    # priority is equal then brackets need to stay if op is not associative.
    # Otherwise brackets are unnecessary.
    return _P[op1] < _P[op] or _P[op1] == _P[op] and op not in _ASSOC


def make_reduced_tree_ops(all_ops):
    return dict((cur_op, ''.join(
        op for op in all_ops
        if bracket_condition(op, cur_op)
    )) for cur_op in all_ops)


def td_psfx_cnt(n, all_ops):
    m = dict()
    reduced_tree_ops = make_reduced_tree_ops(all_ops)

    def recur(n, ops):
        if n == 1:
            return 1
        if (n, ops) in m:
            return m[(n, ops)]
        r = 0
        for op in ops:
            for i in range(1, n):
                r1 = recur(i, reduced_tree_ops[op])
                r2 = recur(n-i, all_ops)
                r += r1 * r2
        m[(n, ops)] = r
        return r
    return recur(n, all_ops)


def td_psfx(vs, all_ops):
    reduced_tree_ops = make_reduced_tree_ops(all_ops)

    def recur(ls, ops):
        if len(ls) == 1:
            return ls
        r = []
        for op in ops:
            for i in range(1, len(ls)):
                r1 = recur(ls[:i], reduced_tree_ops[op])
                r2 = recur(ls[i:], all_ops)
                for a, b in it.product(r1, r2):
                    r.append(a + b + op)
        return r
    return recur(vs, all_ops)


def gen_td_psfx(vs, all_ops):
    reduced_tree_ops = make_reduced_tree_ops(all_ops)

    def recur(ls, ops):
        if len(ls) == 1:
            yield ls
            return
        for op in ops:
            for i in range(1, len(ls)):
                r1 = recur(ls[:i], reduced_tree_ops[op])
                r2 = recur(ls[i:], all_ops)
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


def _eval_psfx(pf, init):
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
            s.append((init(c), ""))
            continue
        b, a = s.pop(), s.pop()
        d = apply_op(a, b, c)
        s.append((d, c))
    return s.pop()[0]


def eval_psfx(pf):
    return _eval_psfx(pf, mp.mpc)


def float_eval_psfx(pf):
    return _eval_psfx(pf, np.float_)


def postfix_to_infix(pf):
    def _apply_op(at, bt, op):
        a, op1 = at
        b, op2 = bt
        left_b = len(a) > 1 and bracket_condition(op1, op)
        right_b = len(b) > 1 and bracket_condition(op2, op)
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


class ProcStatus:
    IDLE = -1
    ACQMEM = 0
    CALC = 1
    DONE = 2

    def p(s):
        for name in dir(ProcStatus):
            if getattr(ProcStatus, name) == s:
                return name
        return "UNKNOWN"


def access_mem(name, dtype, sz=None):
    shared_mem = shared_memory.SharedMemory(name=name)
    sz = (len(shared_mem.buf) // np.dtype(dtype).itemsize) if not sz else sz
    # shared_mem has to be returned otherwise the memory is unusable
    return shared_mem, np.ndarray(sz, dtype=dtype, buffer=shared_mem.buf)


def eval_f(task_mem_name, res_mem_name, status_mem_name, start_time_mem_name,
           cur_idx_mem_name,
           status_idx, start_idx, end_idx, goal,
           arr_dim, arr_dtype):
    # print("ID {:}: {:}-{:}".format(status_idx, start_idx, end_idx))
    # goal = mp.mpc(goal)
    _m1, pfs = access_mem(task_mem_name, arr_dtype, arr_dim)
    _m2, res = access_mem(res_mem_name, np.int8)
    _m3, status = access_mem(status_mem_name, np.int64)
    _m4, start_time = access_mem(start_time_mem_name, np.float_)
    _m5, cur_idx = access_mem(cur_idx_mem_name, np.int64)
    status[status_idx] = ProcStatus.ACQMEM
    for i in range(start_idx, end_idx):
        start_time[status_idx] = np.float(time.time())
        status[status_idx] = ProcStatus.CALC
        cur_idx[status_idx] = i
        res[i] = -1
        r = eval_psfx(pfs[i].decode('ascii'))
        res[i] = r == goal
    status[status_idx] = ProcStatus.DONE


def calc_task_ranges(proc_cnt, tasks):
    task_cnt = len(tasks)
    block_size = task_cnt // proc_cnt
    tr = [[i * block_size, (i + 1) * block_size] for i in range(proc_cnt)]
    tr[-1][1] = task_cnt
    return [tuple(r) for r in tr]


def make_tasks(n, ops):
    s = "123456789"[:n]
    q_type = np.dtype('a' + str(2*len(s)))
    q = np.array(td_psfx(s, ops), dtype=q_type)
    # q.sort()
    np.random.shuffle(q)
    return q, q_type


def print_status(res, status, cur_idx, restarts, proc_cnt):
    print("Status: {:}|Found: {:d}|Progress: {:d}/{:d}".format(
        ' '.join(
            "{:}{:}".format(ProcStatus.p(status[i]), r)
            for (r, i) in zip(restarts, range(proc_cnt))
        ),
        np.sum(res > 0),
        np.sum(res != -2),
        len(res))
    )


def make_shared_mem(smm, sz, dtype):
    shared_mem = smm.SharedMemory(size=sz * np.dtype(dtype).itemsize)
    shared = np.ndarray(sz, dtype=dtype, buffer=shared_mem.buf)
    # shared_mem has to be returned otherwise the memory is unusable
    return shared_mem, shared


def parallel_eval_expr(n, ops, goal, timeout=1, proc_cnt=16):
    q, q_type = make_tasks(n, ops)
    task_cnt = len(q)
    task_ranges = calc_task_ranges(proc_cnt, q)
    smm = SharedMemoryManager()
    smm.start()
    task_mem, tq = make_shared_mem(smm, task_cnt, q_type)
    tq[:] = q[:]
    del q
    res_mem, res = make_shared_mem(smm, task_cnt, np.int8)
    res[:] = -2  # initial value indicating that result is not being calculated
    start_time_mem, start_time = make_shared_mem(smm, proc_cnt, np.float_)
    status_mem, status = make_shared_mem(smm, proc_cnt, np.int64)
    status[:] = ProcStatus.IDLE
    cur_idx_mem, cur_idx = make_shared_mem(smm, proc_cnt, np.int64)
    cur_idx[:] = -1
    processes = [None] * proc_cnt
    restarts = [0] * proc_cnt
    cur_t = time.time()
    while not all(status[i] == ProcStatus.DONE for i in range(proc_cnt)):
        print_status(res, status, cur_idx, restarts, proc_cnt)
        try:
            for i, p in enumerate(processes):
                if p is None:
                    continue
                if status[i] == ProcStatus.DONE:
                    continue
                if (cur_t - start_time[i]) > timeout:
                    p.kill()
                    if cur_idx[i] < 0:
                        continue
                    res[cur_idx[i]] = -1

            for i, p in enumerate(processes):
                if p is not None and p.is_alive():
                    continue
                if status[i] == ProcStatus.DONE:
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
                is_new_proc = cur_idx[i] == -1
                idx = task_ranges[i][0] if is_new_proc else cur_idx[i]
                end_idx = task_ranges[i][1]
                restarts[i] += 1
                processes[i] = Process(
                    target=eval_f,
                    args=(task_mem.name,
                          res_mem.name,
                          status_mem.name,
                          start_time_mem.name,
                          cur_idx_mem.name,
                          i,
                          # skipping the one that takes too long
                          idx + (0 if is_new_proc else 1),
                          end_idx,
                          goal,
                          task_cnt, q_type)
                )
                processes[i].start()
        except Exception:
            import traceback
            traceback.print_exc()

        cur_t = time.time()
        time.sleep(timeout)

    print_status(res, status, cur_idx, restarts, proc_cnt)

    for p in processes:
        if p is None:
            continue
        p.join()
        p.close()

    for pf in tq[np.argwhere(res == 1)].flatten():
        pf = pf.decode('ascii')
        print(eval_psfx(pf), '==', postfix_to_infix(pf), pf)

    smm.shutdown()
