"""Exact finite certificate for H_(4k), even k>=2502.
Only Python standard library required.  No bounded sampling is used.
An affine pair (a,b) represents a*k+b modulo4k.
"""
import json, sys
from pathlib import Path

if not __debug__:
    raise SystemExit("Run Python without -O or -OO; verification uses assertions.")
KMIN=2501

def norm(x,k):
 a=(x+k//2)//k
 return (a%4,x-a*k)

def expr(a,b):return(a%4,b)
def band(a,lo,hi):return {expr(a,b) for b in range(lo,hi+1)}
def add(x,y,z=0):return expr(x[0]+y[0],x[1]+y[1]+z)

def ge0(a,b):
 """Prove sign of a*k+b for every k>=KMIN; reject varying signs."""
 if a>=0 and a*KMIN+b>=0:return True
 if a<=0 and a*KMIN+b<0:return False
 raise AssertionError(('nonconstant sign',a,b))
def eq0(a,b):
 if a==0:return b==0
 # A strict sign at the lower endpoint that does not move toward zero.
 if a>0 and a*KMIN+b>0:return False
 if a<0 and a*KMIN+b<0:return False
 raise AssertionError(('nonconstant equality',a,b))
def rep(x):
 a,b=x
 if a==0 and b<0:a=4
 assert ge0(a,b) and ge0(4-a,-b-1)
 return a,b

def delta(r,c,rho):
 a,b=rep(r);u,v=rep(c)
 def isrow(j):return eq0(a,b-j)
 def iscol(j):return eq0(u,v-j)
 rm=(a*rho+b)%4;cm=(u*rho+v)%4
 if any(isrow(j) for j in (0,5,10)) and cm==1:
  j=next(j for j in (0,5,10) if isrow(j))
  if not iscol(1+4*j//5):return 4
 if any(isrow(j) and iscol(vv) for j,vv in ((1,1),(6,5),(11,9))):return 3
 for j in (0,5,10):
  if isrow(j) and ge0(u,v-4*j//5-1) and ge0(-u,4+4*j//5-v):return 1
 for j in (1,6,11):
  if isrow(j) and ge0(u,v-4*(j-1)//5-2) and ge0(-u,4+4*(j-1)//5-v):return -1
 if any(isrow(j) for j in (4,9,14)) and cm==1:return -4
 interior=ge0(a,b-15) and ge0(4-a,-22-b)
 if interior and rm==3 and cm%2==0:return 2
 if interior and rm==1 and cm%2==0:return -2
 return 0

def expected(rho,d):
 R=band(0,-21,30)|band(1,-rho-21,-rho+30)|band(2,-21,30)|band(3,-rho-21,-rho+30)
 C=band(0,4*d-20,4*d+27)|band(1,-rho+4*d-24,-rho+4*d+27)|band(2,4*d-24,4*d+31)|band(3,-rho+4*d-20,-rho+4*d+31)
 S=band(0,4*d-43,4*d+60)|band(2,4*d-43-2*rho,4*d+60-2*rho)
 assert len(R)==len(C)==len(S)==208
 return R,C,S

def verify_macro_complements(rho,d,R,C,S):
 """Compute the finite complements from the near-complete macro mapping.

 For k=2m, x(t)=t+1_{t>=m}+d on 0<=t<=k-2 is injective,
 missing x=m+d.  y(t)=t+x(t)+1 is injective, missing y=d:
 its first half gives one parity and its second half the other parity.
 The four micro rows in block t are 4t+3+i, with columns
 4x(t)+(0,2,3,1)[i] and symbols 4y(t)+(1,2,4,3)[i].
 """
 # Store z=4t, avoiding fractions of k.  This is exactly the set E
 # of omitted blocks, whose size is 52.  The coefficient 4 is kept
 # here to decide whether t is in the second half before reducing.
 E=[(0,4*j) for j in range(7)]
 E += [(1,4*j-rho) for j in range(-6,7)]
 E += [(2,4*j) for j in range(-6,7)]
 E += [(3,4*j-rho) for j in range(-6,7)]
 E += [(4,4*j) for j in range(-6,0)]
 assert len(E)==52
 RR={expr(a,b+3+i) for a,b in E for i in range(4)}
 CC={expr(2,4*d+i) for i in range(4)}
 SS={expr(0,4*d+i) for i in range(1,5)}
 for a,b in E:
  if (a,b)==(4,-4):continue # omitted row block t=k-1
  jump=int(ge0(a-2,b))
  CC.update(expr(a,b+4*jump+4*d+i) for i in range(4))
  SS.update(expr(2*a,2*b+4*jump+4+4*d+i) for i in range(1,5))
 assert RR==R and CC==C and SS==S

def verify(cert):
 assert set(map(int,cert))=={0,2}
 for rhotxt,data in cert.items():
  rho=int(rhotxt);common=None
  assert {x['shift'] for x in data}=={0,1,2}
  for x in data:
   d=x['shift'];choices=[tuple(tuple(v) for v in cell) for cell in x['choices']]
   assert len(choices)==208
   R,C,S=expected(rho,d)
   verify_macro_complements(rho,d,R,C,S)
   assert {r for r,c,s in choices}==R
   assert {c for r,c,s in choices}==C
   assert {s for r,c,s in choices}==S
   for r,c,s in choices:
    assert add(r,c,delta(r,c,rho))==s,(rho,d,r,c,s,delta(r,c,rho))
   cells={(r,c) for r,c,s in choices}
   common=cells if common is None else common&cells
   assert ((0,x['omit']),(0,{1:1,6:5,11:9}[x['omit']])) not in cells
   allcoords=R|C|S
   # Distinct affine forms cannot alias mod4k: |difference of constants|<k.
   assert max(v[1] for v in allcoords)-min(v[1] for v in allcoords)<KMIN
  assert not common,(rho,common)
 print('Verified all even k >=2502: three transversals of H_(4k) with empty common intersection.')

if __name__=='__main__':
 filename=sys.argv[1] if len(sys.argv)>1 else Path(__file__).with_name('h_even_certificate.json')
 verify(json.load(open(filename)))
