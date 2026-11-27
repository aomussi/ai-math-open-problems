#!/usr/bin/env python3
# Python 3.10+; standard library only. No input files.
from collections import Counter
from itertools import combinations

V = range(24)
E = set()
def add(u, v):
    E.add(tuple(sorted((u, v))))

for i in range(6):
    add(i, 6 + (i+3)%6)
    for d in (-1, 1):
        add(i, 12 + (i+d)%6)
    add(i, 18 + (i+3)%6)
    for d in (2, 3, 5):
        add(6+i, 18 + (i+d)%6)
    add(12+i, 12 + (i+3)%6)

adj = [0]*24
for u, v in E:
    adj[u] |= 1 << v
    adj[v] |= 1 << u
assert len(E) == 45
assert Counter(a.bit_count() for a in adj) == {3: 6, 4: 18}

# Return sorted sizes of connected components after optional flip.
def components(mask, flip=None):
    sizes = []
    while mask:
        reached = mask & -mask
        front = reached
        while front:
            b = front & -front
            front ^= b
            v = b.bit_length()-1
            a = adj[v]
            if flip is not None:
                u, w = flip
                if v == u: a ^= 1 << w
                if v == w: a ^= 1 << u
            new = a & mask & ~reached
            reached |= new
            front |= new
        sizes.append(reached.bit_count())
        mask &= ~reached
    return tuple(sorted(sizes))

hist = Counter()
witness = {}
count = 0
bits = [1 << v for v in V]
for S in combinations(V, 12):
    count += 1
    mask = sum(bits[v] for v in S)
    bad = [(v, (adj[v] & mask).bit_count()) for v in S
           if (adj[v] & mask).bit_count() != 2]
    if not bad:
        hist[components(mask)] += 1
        continue
    if len(bad) != 2:
        continue
    (u, du), (v, dv) = bad
    pair = (u, v) # combinations lists vertices in sorted order
    if du == dv == 1 and pair not in E:
        pass # adding this edge makes all degrees 2
    elif du == dv == 3 and pair in E:
        pass # deleting this edge makes all degrees 2
    else:
        continue
    if pair not in witness and components(mask, pair) == (12,):
        witness[pair] = S

assert count == 2704156
assert hist == {(5, 7): 24, (6, 6): 6}
assert set(witness) == set(combinations(V, 2))
print('Vertices:', len(V), 'Edges:', len(E))
print('Twelve-subsets:', count)
print('Two-regular component sizes:', sorted(hist.items()))
print('Successful deletions:', len(E & witness.keys()))
print('Successful additions:', len(witness.keys() - E))
print('PASS: C12-induced-saturated')
