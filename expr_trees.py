def gen_expr_trees(n, u, i):
    if i == n:
        yield []
        return
    cnt = max(0, i + 1 - u)
    for x in range(cnt if (i+1 == n) else 0, cnt + 1):
        for y in f(n, u+x, i+1):
            yield [x] + y


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
        print(s)
        if c not in _OPERATORS:
            s.append((c, ""))
            continue
        b, a = s.pop(), s.pop()
        d = apply_op(a, b, c)
        s.append((d, c))
    return s.pop()[0]


def expr_trees(n, u, i):
    if i == n:
        return [[]]
    cnt = max(0, i + 1 - u)
    s = []
    for x in range(cnt if (i+1 == n) else 0, cnt + 1):
        s.extend([[x] + y for y in g(n, u+x, i+1)])
    return s
