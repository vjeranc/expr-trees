# Algorihm P
n = 4
a = ['('] * (2 * n + 1)
for k in range(1, n+1):
    a[2 * k - 1] = '('
    a[2 * k] = ')'
a[0] = ')'
m = 2 * n - 1
while m >= 0:
    print(''.join(a[1:]))
    a[m] = ')'
    if a[m - 1] == ')':
        a[m - 1] = '('
        m = m - 1
        continue
    j = m - 1
    k = 2 * n - 1
    while a[j] == '(':
        a[j] = ')'
        a[k] = '('
        j = j - 1
        k = k - 2
    if j == 0:
        break
    a[j] = '('
    m = 2 * n - 1
