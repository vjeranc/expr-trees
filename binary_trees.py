# Algorithm B
def enumerate_binary_trees(n):
    l = [0] * (n + 2)
    r = [0] * (n + 1)
    for k in range(1, n):
        l[k] = k + 1
        r[k] = 0
    l[n + 1] = 1
    l[n] = r[n] = 0
    while True:
        print(l[1:(n+1)], r[1:(n+1)])
        j = 1
        while l[j] == 0:
            r[j] = 0
            l[j] = j + 1
            j = j + 1
            if j > n:
                return
        y = l[j]
        k = 0
        while r[y] > 0:
            k = y
            y = r[y]
        if k > 0:
            r[k] = 0
        else:
            l[j] = 0
        r[y] = r[j]
        r[j] = y


enumerate_binary_trees(4)
