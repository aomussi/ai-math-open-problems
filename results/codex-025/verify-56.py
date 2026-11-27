from itertools import combinations
from math import comb

V = range(24)
E = set(combinations(range(4), 2))
E.update(combinations(range(4, 8), 2))
for i in range(4):
   a, b, c, d, e, f = (4*k+i for k in range(6))
   pairs = [(c,d), (b,c), (b,d), (a,c), ((i-1)%4,c),
             (a,d), ((i+1)%4,d), (c,e), (d,f),
             (e,20+(i+1)%4), (e,20+(i+2)%4)]
   E.update(tuple(sorted(p)) for p in pairs)
U = set(combinations(V, 2))
assert len(E) == 56 and len(U-E) == 220
A = [0]*24
for u,v in E:
   A[u] |= 1 << v
   A[v] |= 1 << u

def connected(M, cut=None):
   seen = todo = M & -M
   while todo:
       bit = todo & -todo
       todo ^= bit
       u = bit.bit_length()-1
       N = A[u]
       if cut is not None and u in cut:
           N ^= 1 << (cut[0]+cut[1]-u)
       fresh = N & M & ~seen
       seen |= fresh
       todo |= fresh
   return seen == M

R, add, delete = [], {}, {}
npath = nchord = tested = 0
for S in combinations(V, 12):
   tested += 1
   M = sum(1 << u for u in S)
   deg = [(A[u] & M).bit_count() for u in S]
   if all(d == 2 for d in deg):
       R.append(S)
       assert not connected(M), S
   elif deg.count(1) == 2 and deg.count(2) == 10:
       if connected(M):
           p = tuple(u for u,d in zip(S,deg) if d == 1)
           assert p not in E
           add.setdefault(p,S)
           npath += 1
   elif deg.count(3) == 2 and deg.count(2) == 10:
       p = tuple(u for u,d in zip(S,deg) if d == 3)
       if p in E and connected(M,p):
           delete.setdefault(p,S)
           nchord += 1
assert tested == comb(24,12) == 2704156
assert len(R) == 4 and (npath,nchord) == (1664,444)
assert set(add) == U-E and set(delete) == E
for p,S in {**add, **delete}.items():
   M = sum(1 << u for u in S)
   for u in S:
       N = A[u] ^ (1 << (sum(p)-u) if u in p else 0)
       assert (N & M).bit_count() == 2
   assert connected(M,p)
print('PASS', tested, len(R), npath, nchord,
     len(add), len(delete))
