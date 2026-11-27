from collections import Counter
from itertools import combinations

A = [
    (0, 1, 24, 14, 7), (0, 3, 16, 21, 20), (0, 9, 11, 8, 22),
    (0, 2, 2, 9, 25), (0, 6, 1, 23, 6), (0, 18, 17, 18, 3),
    (0, 4, 18, 13, 18), (0, 12, 13, 2, 2), (0, 10, 6, 6, 13),
    (0, 5, 8, 7, 10), (0, 15, 21, 4, 24), (0, 19, 12, 20, 11),
    (0, 7, 20, 11, 0), (0, 21, 7, 0, 8), (0, 11, 0, 24, 21),
    (0, 8, 25, 3, 16), (0, 24, 9, 22, 23), (0, 20, 14, 17, 1),
    (0, 14, 19, 25, 12), (0, 16, 23, 10, 5), (0, 22, 4, 15, 17),
    (0, 17, 15, 1, 13), (0, 25, 3, 13, 19), (0, 23, 13, 5, 9),
    (0, 0, 10, 12, 4), (0, 13, 5, 19, 15), (0, 13, 22, 16, 14),
]
assert len(A) == 27
assert all(len(row) == 5 for row in A)
assert all(0 <= x < 26 for row in A for x in row)
expected = Counter(range(26))
expected[13] += 1
for i, j in combinations(range(5), 2):
    counts = Counter((row[j] - row[i]) % 26 for row in A)
    assert counts == expected, (i+1, j+1, counts)
    print(f"({i+1},{j+1}): PASS")
print("PASS: all 10 column pairs.")
