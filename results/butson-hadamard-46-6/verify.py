a = list(map(int, "04440242440220442420444"))
b = list(map(int, "05311151353333531511135"))
p = 23
assert len(a) == len(b) == p

# Exact coordinates of zeta**e in the basis (1, zeta).
R = ((1,0), (0,1), (-1,1), (-1,0), (0,-1), (1,-1))

# Verify the complete difference-count table.
S = {1, 3, 4, 5, 6, 7, 9}
S |= {(-s) % p for s in S}
for s in range(1, p):
    N = [0] * 6
    for v in (a, b):
        for j in range(p):
            N[(v[j] - v[(j+s) % p]) % 6] += 1
    expected = [14,1,15,0,15,1] if s in S else [16,0,14,2,14,0]
    assert N == expected, (s, N)

# Construct the exponent matrix E: H[i,j] = zeta**E[i][j].
E = [
    [a[(j-i) % p] for j in range(p)]
    + [b[(j-i) % p] for j in range(p)]
    for i in range(p)
]
E += [
    [(-b[(i-j) % p]) % 6 for j in range(p)]
    + [(3-a[(i-j) % p]) % 6 for j in range(p)]
    for i in range(p)
]

# Check every entry of H H* exactly.
for i in range(46):
    for j in range(46):
        u = v = 0
        for k in range(46):
            du, dv = R[(E[i][k] - E[j][k]) % 6]
            u += du
            v += dv
        assert (u, v) == ((46, 0) if i == j else (0, 0))

print("PASS: 22 shifts and all 2116 Gram entries.")
