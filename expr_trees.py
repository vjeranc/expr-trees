from collections import namedtuple
import itertools as it
from multiprocessing import Process
import time

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


def psfx(ls, ops):
    if len(ls) == 1:
        yield ls
        return
    for op in ops:
        for i in range(1, len(ls)):
            r1 = psfx(ls[:i], ops)
            r2 = psfx(ls[i:], ops)
            for a, b in it.product(r1, r2):
                yield (a + b + op)


def all_postfix(vars, ops_cnt):
    if not vars:
        return [""]
    if all_same(ops_cnt) and ops_cnt[0][0].associative:
        return [vars + (ops_cnt[0][0].symbol * (len(vars) - 1))]

    res = []
    for i, (op, cnt) in enumerate(ops_cnt):
        last_op = op
        remaining_ops = ops_cnt[:i] + ops_cnt[i+1:]
        if cnt - 1 > 0:
            remaining_ops.append((op, cnt - 1))
        remaining_vars = vars[:-1]
        res = []
        for i, _ in enumerate(remaining_vars):
            res1 = all_postfix(remaining_vars[:i], remaining_ops)
            res2 = all_postfix(remaining_vars[i:], remaining_ops)
            for t1, t2 in it.product(res1, res2):
                res.append(t1 + t2 + vars[-1] + last_op.symbol)

    return res


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
        '/': lambda x, y: None if y == 0 else (x / y),
        '^': lambda x, y: None if x == 0 and y < 0 else (x ** y)
    }

    def apply_op(at, bt, op):
        a, _ = at
        b, _ = bt
        if a is None or b is None:
            return None
        return _OPERATORS[op](int(a), int(b))
    s = []
    for c in pf:
        if c not in _OPERATORS:
            s.append((c, ""))
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
    r = eval_psfx(pf_expr)
    s = "{:}"
    if type(r) == float:
        s = "{:.5f}"
    s = ("{:40}|{:40}|{:4}").format(
        k,
        s.format(r)[:40],
        r == goal_num
    )
    print(s)


def chunker(seq, size):
    return (seq[pos:pos + size] for pos in range(0, len(seq), size))


def eval_expr(n, goal):
    s = "123456789"[:n]
    m = dict()
    for pf in psfx(s, "+-*/^"):
        infx = postfix_to_infix(pf)
        ls = m.setdefault(infx, [])
        ls.append(pf)

    q = list(m.items())
    ps = [Process(target=eval_f, args=("", "12+", 3))] * 100
    while q:
        nps, aps = [], []
        for p in ps:
            if p.is_alive():
                aps.append(p)
            else:
                nps.append(p)
        for _ in nps:
            k, vs = q.pop()
            p = Process(target=eval_f, args=(k, vs[-1], goal))
            p.start()
            aps.append(p)
            if not q:
                break
        ps = aps
        time.sleep(0.01)
