#!/usr/bin/env python3
"""Verify the H_{8t+4} transversal certificate by affine identities, t>=1250.
No search, floating point, symbolic algebra library, or sample-size extrapolation.
"""
import json, sys
from pathlib import Path

if not __debug__:
    raise SystemExit("Run Python without -O or -OO; verification uses assertions.")
TMIN = 1250
N = (8,4)
def add(x,y): return (x[0]+y[0], x[1]+y[1])
def sub(x,y): return (x[0]-y[0], x[1]-y[1])
def mul(x,a): return (x[0]*a,x[1]*a)
def val(x): return TMIN*x[0]+x[1]
def nonneg(x): return x[0]>=0 and val(x)>=0
def pos(x): return x[0]>=0 and val(x)>0
def le(x,y):
    d=sub(y,x)
    if nonneg(d): return True
    if pos(mul(d,-1)): return False
    raise AssertionError(('inequality is not constant on the half-line',x,y))
def lt(x,y): return not le(y,x)
def eq(x,y):
    d=sub(x,y)
    if d==(0,0): return True
    if pos(d) or pos(mul(d,-1)): return False
    raise AssertionError(('equality not certified constant',x,y))
def eqc(x,c): return eq(x,(0,c))
def mod(x,m):
    assert x[0]%m==0
    return x[1]%m

def delta_h(r,c):
    # Exactly the mutually exclusive clauses of equation (7).
    rp=next((z for z in (0,5,10) if eqc(r,z)),None)
    rn=next((z for z in (1,6,11) if eqc(r,z)),None)
    if rp is not None and mod(c,4)==1 and not eqc(c,4*rp//5+1): return 4
    if any(eqc(r,a) and eqc(c,b) for a,b in ((1,1),(6,5),(11,9))): return 3
    if rp is not None and le((0,4*rp//5+1),c) and le(c,(0,4*rp//5+4)): return 1
    if rn is not None and le((0,4*(rn-1)//5+2),c) and le(c,(0,4*(rn-1)//5+4)): return -1
    if any(eqc(r,z) for z in (4,9,14)) and mod(c,4)==1: return -4
    if le((0,15),r) and lt(r,sub(N,(0,21))):
        if mod(r,4)==3 and mod(c,2)==0: return 2
        if mod(r,4)==1 and mod(c,2)==0: return -2
    return 0

def residue(x):
    q=val(x)//val(N)
    y=sub(x,mul(N,q))
    assert nonneg(y) and pos(sub(N,y))
    return y

def distinct(xs):
    # This checks distinctness for every t >= TMIN, by affine inequalities.
    xs=sorted(xs,key=val)
    assert all(pos(sub(y,x)) for x,y in zip(xs,xs[1:]))

def verify(path):
    data=json.load(open(path))
    rows=[tuple(x) for x in data['rows']]
    expected=[(0,j) for j in range(28)]+[(4,j) for j in range(-24,28)]+[(8,j) for j in range(-20,4)]
    assert rows==expected and len(rows)==104
    distinct(rows)
    for x in rows: assert nonneg(x) and pos(sub(N,x))
    trans=data['transversals']
    assert len(trans)==3
    for tr in trans:
        pi=tr['pi']; cols=[tuple(x) for x in tr['columns']]
        assert sorted(pi)==list(range(4)) and pi[1]%2==1 and pi[3]%2==0
        q=[i+pi[i]+(2 if i==3 else 0) for i in range(4)]
        assert len({x%4 for x in q})==4
        # Since n/4=2t+1 is odd, j -> 2j+floor(q_i/4) is a permutation.
        assert sorted(cols)==sorted(rows)
        omit=tr['omit_special_row']
        assert cols[rows.index((0,omit))] != (0,{1:1,6:5,11:9}[omit])
        original=[]; actual=[]
        for r,c in zip(rows,cols):
            i=mod(r,4)
            basec=add(r,(0,pi[i]-i))
            original.append(residue(add(add(r,basec),(0,2 if i==3 else 0))))
            d=delta_h(r,c)
            actual.append(residue(add(add(r,c),(0,d))))
        distinct(original)
        assert sorted(original)==sorted(actual)
        print('Certified transversal omitting special row',tr['omit_special_row'])
    for i in range(4):
        assert len({tr['pi'][i] for tr in trans})>=2
    for z in range(len(rows)):
        assert len({tuple(tr['columns'][z]) for tr in trans})>=2
    print('Certified empty intersection for every integer t >=',TMIN)
    print('Equivalently, every n > 10000 with n congruent to 4 modulo 8.')
if __name__=='__main__':
    verify(sys.argv[1] if len(sys.argv)>1 else Path(__file__).with_name('h_odd_certificate.json'))
