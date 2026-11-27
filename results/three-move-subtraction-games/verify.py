from itertools import product

def phi(u0,u1,u2,u3,u4,u5,u6,u7):
    return (u0+u1+3*u2+u7+u0*u3
            +u4*(u7-u1-u2)-2*u1*u2*(1-u4))

def psi(v0,v1,v2,v3,v4,v5):
    return (2*v1+2*v3+v0*(v3+v4)
            -v1*(v2+v5-v2*v5))

def omega(w0,w1,w2,w3,w4,w5):
    return 3*w2+w3*(1+w0)-w1*w2*(1-w5)

edges = ('AB AC BD CD EF EG FH GH IJ IK JL KL '
          'AE BF CG DH EI FJ GK HL').split()
count = 0
for bits in product((0,1), repeat=12):
    v = dict(zip('ABCDEFGHIJKL',bits))
    if any(v[x]*v[y] for x,y in edges):
        continue
    A,B,C,D,E,F,G,H,I,J,K,L = bits
    if H != (1-D)*(1-F)*(1-G): continue
    if L != (1-H)*(1-J)*(1-K): continue
    eta = (1-A)*(1-B)*(1-C)*(1-E)
    delta = (phi(A,B,C,D,E,F,G,H)-phi(E,F,G,H,I,J,K,L)
              +psi(A,B,E,F,I,J)-psi(C,D,G,H,K,L)
              +omega(A,C,E,G,I,K)-omega(B,D,F,H,J,L))
    table = {
        (0,0,0): A*(1-I)+(1-E)*(B*J+C*K),
        (1,0,0): I*(1-A),
        (0,1,0): L*(1-C)*(1-A*I),
        (0,0,1): L*(1-B)*(1-A*I),
        (1,1,0): (1-A)+L*(1-A*I),
        (1,0,1): (1-A)+L*(1-A*I),
        (0,1,1): (1-A)*(1+I),
        (1,1,1): (1-A)*(2+I),
    }
    assert -2*eta-delta == table[D,F,G] >= 0, bits
    count += 1
assert count == 93, count
print(f'PASS: {count} admissible configurations.')
