from collections import namedtuple
import itertools as it
from multiprocessing import Process
import time
import mpmath as mp

Op = namedtuple('Op', ['symbol', 'priority', 'associative'])

Plus = Op('+', 0, True)
Minus = Op('-', 0, False)
Mul = Op('*', 1, True)
Div = Op('/', 1, False)
Pow = Op('^', 2, False)


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


def all_same(ops):
    return len(ops) <= 1


def all_assoc(ops):
    return all(op.associative for _, op in ops)


_MM = dict()


def _psfx(ls, lops, rops, tree='l'):
    # version with cache, variables should be put in with str.format function.
    ops = lops if tree == 'l' else rops
    if (len(ls), ops) in _MM:
        return _MM[(len(ls), ops)]
    if len(ls) == 1:
        return ["{:}"]
    r = []
    for op in ops:
        for i in range(1, len(ls)):
            r1 = _psfx(ls[:i], lops, rops, tree='l')
            r2 = _psfx(ls[i:], lops, rops, tree='r')
            for a, b in it.product(r1, r2):
                r.append(a + b + op)
    _MM[(len(ls), ops)] = r
    return r


def psfx(ls, lops, rops=None):
    rops = rops or lops
    return [s.format(*ls) for s in _psfx(ls, lops, rops)]


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
            seq.append(str(len(infxR_to_psfx_map(len(s), op_set))))
        print(''.join(list(op_set)), ' '.join(seq))


def gen_psfx(ls, lops=None, rops=None, tree='l'):
    rops = rops or lops
    ops = lops if tree == 'l' else rops
    if len(ls) == 1:
        yield ls
        return
    for op in ops:
        for i in range(1, len(ls)):
            r1 = gen_psfx(ls[:i], lops, rops, tree='l')
            r2 = gen_psfx(ls[i:], lops, rops, tree='r')
            for a, b in it.product(r1, r2):
                yield (a + b + op)


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
        except Exception as e:
            print(e)
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
    _P = {  # priority
        '+': 0,
        '-': 0,
        '*': 1,
        '/': 1,
        '^': 2
    }
    _ASSOC = "+*"
    _OPERATORS = set(['+', '-', '*', '/', '^', ])

    def apply_op(at, bt, op):
        a, op1 = at
        b, op2 = bt
        left_b = len(a) > 1 and _P[op1] < _P[op]
        right_b = len(b) > 1 and (_P[op2] < _P[op] or op not in _ASSOC)
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
        d = apply_op(a, b, c)
        s.append((d, c))
    return s.pop()[0]


def eval_f(k, pf_expr, goal_num):
    print(k, eval_psfx(pf_expr))


def chunker(seq, size):
    return (seq[pos:pos + size] for pos in range(0, len(seq), size))


def infxR_to_psfx_map(n, ops):
    s = "123456789"[:n]
    m = dict()
    for pf in psfx(s, ops):
        infx = postfix_to_infix(pf)
        ls = m.setdefault(infx, [])
        ls.append(pf)
    return m


def eval_expr(n, goal):
    m = infxR_to_psfx_map(n, "+-*/^")
    for k, vs in m.items():
        print(k, end=' ', flush=True)
        print(eval_psfx(vs[-1]))


def parallel_eval_expr(n, goal):
    s = "123456789"[:n]
    m = dict()
    for pf in psfx(s, "+-*/^"):
        infx = postfix_to_infix(pf)
        ls = m.setdefault(infx, [])
        ls.append(pf)

    q = list(m.items())
    ps = [Process(target=eval_f, args=("", "12+", 3))] * 100
    pm = dict()
    too_long = []
    while q:
        nps, aps = [], []
        for p in ps:
            if p.is_alive():
                if (time.time() - pm[p][1]) > 10:
                    p.kill()
                    nps.append(p)
                    too_long.append(pm[p][2])
                    del pm[p]
                    continue
                aps.append(p)
            else:
                nps.append(p)
        for p in nps:
            try:
                p.close()
            except Exception:
                aps.append(p)
                continue
            k, vs = q.pop()
            p = Process(target=eval_f, args=(k, vs[-1], goal))
            p.start()
            pm[p] = (p, time.time(), k)
            aps.append(p)
            if not q:
                break
        ps = aps
        time.sleep(0.01)

    for tl in too_long:
        print(tl)
