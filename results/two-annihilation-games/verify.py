from itertools import combinations
from collections import deque


def moves(adj):
    return [(i, (1 << i) ^ sum(1 << j for j in S))
            for i, out in enumerate(adj)
            for S in combinations(out, min(2, len(out)))]


def solve(n, M):
    Z = {m for i, m in M if (m >> i) & 1}
    B = []                          # independent generators
    piv = [0] * n                   # elimination basis

    def rem(x):
        for i in range(n - 1, -1, -1):
            if (x >> i) & 1 and piv[i]:
                x ^= piv[i]
        return x

    def representative(c, J):
        # Solve x = c + sum(t_j B_j), x_i = 0 for i in J.
        rows = {}
        for i in J:
            a = sum(((b >> i) & 1) << j for j, b in enumerate(B))
            rhs = (c >> i) & 1
            while a:
                k = a.bit_length() - 1
                if k not in rows:
                    rows[k] = (a, rhs)
                    break
                old_a, old_rhs = rows[k]
                a ^= old_a
                rhs ^= old_rhs
            else:
                if rhs:
                    return None
        t = 0                       # free variables are zero
        for k in sorted(rows):
            a, rhs = rows[k]
            if ((a & t).bit_count() & 1) != rhs:
                t |= 1 << k
        x = c
        for j, b in enumerate(B):
            if (t >> j) & 1:
                x ^= b
        return x

    while True:
        A = {rem(z) for z in Z}
        R = [(i, rem(m)) for i, m in M]
        candidates = {a ^ z for _, a in R for z in A} - {0}
        for c in sorted(candidates):
            J = {i for i, a in R if (c ^ a) not in A}
            b = representative(c, J)
            if b is not None:
                v = rem(b)
                assert v != 0
                B.append(b)
                piv[v.bit_length() - 1] = v
                break
        else:
            return B, rem, A


def retrograde(n, M):
    # Independent explicit game graph; L=loss, W=win, D=draw.
    size = 1 << n
    pred = [[] for _ in range(size)]
    degree = [0] * size
    for x in range(size):
        for i, m in M:
            if (x >> i) & 1:
                pred[x ^ m].append(x)
                degree[x] += 1
    result = ['D'] * size
    queue = deque()
    for x in range(size):
        if degree[x] == 0:
            result[x] = 'L'
            queue.append(x)
    while queue:
        y = queue.popleft()
        for x in pred[y]:
            if result[x] != 'D':
                continue
            if result[y] == 'L':
                result[x] = 'W'
                queue.append(x)
            else:
                degree[x] -= 1
                if degree[x] == 0:
                    result[x] = 'L'
                    queue.append(x)
    return result


def check(n, M):
    B, rem, A = solve(n, M)
    rank = {0: 0}
    for j, b in enumerate(B):
        rank.update({x ^ b: r + (1 << j)
                    for x, r in list(rank.items())})
    reference = retrograde(n, M)
    replies = 0
    for x in range(1 << n):
        c = rem(x)
        result = 'L' if c == 0 else 'W' if c in A else 'D'
        assert result == reference[x], (n, M, x, result)
        if result == 'L':
            for i, m in M:
                if (x >> i) & 1:
                    y = x ^ m
                    assert any((y >> j) & 1 and y ^ a in rank
                                and rank[y ^ a] < rank[x]
                                for j, a in M)
                    replies += 1
    return replies


if __name__ == '__main__':
    for n in range(1, 5):
        graphs = 1 << (n * n)
        replies = 0
        for graph in range(graphs):
            adj = [[j for j in range(n) if (graph >> (n * i + j)) & 1]
                   for i in range(n)]
            replies += check(n, moves(adj))
        print(n, graphs, graphs * (1 << n), replies, flush=True)
