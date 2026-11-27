from collections import Counter
from itertools import combinations

F = [
    [0, 7, 14, 14], [7, 35, 7, 35],
    [14, 14, 0, 7], [28, 0, 35, 28],
    [35, 28, 28, 0],
]
B = [
    [6, 4, 10, 8], [12, 34, 29, 9],
    [18, 31, 20, 30], [1, 21, 37, 22],
    [19, 15, 11, 23], [25, 13, 34, 16],
    [8, 37, 38, 39], [2, 20, 23, 25],
    [32, 23, 33, 38], [15, 36, 2, 10],
    [9, 24, 6, 1], [3, 29, 40, 19],
    [22, 39, 27, 21], [16, 26, 31, 6],
    [4, 9, 24, 15], [29, 32, 12, 11],
    [5, 30, 21, 18], [11, 17, 1, 26],
    [21, 16, 3, 41],
]
A = [[0] + r for r in F + B +
      [[13*x % 42 for x in r] for r in B]]
assert len(A) == 43 and all(len(r) == 5 for r in A)
assert all(0 <= x < 42 for r in A for x in r)
target = Counter(range(42))
target[21] += 1
for i, j in combinations(range(5), 2):
    ds = [(r[j] - r[i]) % 42 for r in A]
    assert Counter(ds) == target, (i+1, j+1)
    hits = [k+1 for k, d in enumerate(ds) if d == 21]
    print(i+1, j+1, len(set(ds)), hits)
print("Verified all 10 pairs.")
