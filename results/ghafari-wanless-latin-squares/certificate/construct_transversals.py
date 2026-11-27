#!/usr/bin/env python3
"""Reconstruct and directly verify the transversal witnesses for a supplied order.

This is a convenience utility. The all-order proof is checked by verify_all.py.
Example: python3 construct_transversals.py 10002 > transversals_10002.json
"""
import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent

if not __debug__:
    raise SystemExit("Run Python without -O or -OO.")

def G(n,r,c):
 k=(n-2)//4
 d=0
 if r in (0,5,10) and c%4==1 and c>r+1:d=4
 elif (r,c) in ((5,3),(10,3),(10,7)):d=4
 elif (r,c) in ((1,2),(6,6),(11,10)):d=3
 elif (r,c) in ((0,3),(0,4),(5,7),(5,8),(10,11),(10,12),(15,12),(15,13),(16,12)):d=1
 elif (r,c) in ((1,3),(1,4),(1,5),(6,7),(6,8),(6,9),(11,11),(11,12),(11,13),(16,13)):d=-1
 elif (r,c) in ((4,2),(4,5),(9,6),(9,9),(14,10),(14,13)):d=-3
 elif r in (4,9,14) and c%4==1 and c>r+1:d=-4
 elif (r,c) in ((9,3),(14,3),(14,7)):d=-4
 elif r==15 and c!=12 and c%2==0:d=2
 elif r==17 and c%2==0:d=-2
 elif 18<=r<3*k-9 and r%3==0 and c%2==0:d=2
 elif 18<=r<3*k-9 and r%3==2 and c%2==0:d=-2
 return (r+c+d)%n

def H(n,r,c):
 d=0
 if r in (0,5,10) and c%4==1 and c-4*r//5!=1:d=4
 elif (r,c) in ((1,1),(6,5),(11,9)):d=3
 elif r in (0,5,10) and 1<=c-4*r//5<=4:d=1
 elif r in (1,6,11) and 2<=c-4*(r-1)//5<=4:d=-1
 elif r in (4,9,14) and c%4==1:d=-4
 elif 15<=r<n-21 and r%4==3 and c%2==0:d=2
 elif 15<=r<n-21 and r%4==1 and c%2==0:d=-2
 return (r+c+d)%n

def check(n,perms,entry):
 common=set(enumerate(perms[0]))
 for p in perms:
  assert len(p)==n and sorted(p)==list(range(n))
  s=[entry(n,r,c) for r,c in enumerate(p)]
  assert sorted(s)==list(range(n)),(n,'symbols',len(set(s)))
  common.intersection_update(enumerate(p))
 assert not common,(n,common)
 return True

def makeG(n):
 k=(n-2)//4;case=(k-9)%2;m=(k-9-case)//2;eps=m%2;u=m//2
 data=json.load(open(ROOT / "g_all_certificate.json"))[f'{case}_{eps}']
 J=list(range(30,u-29))+list(range(u+30,2*u+eps-30))
 out=[]
 for tr in data['transversals']:
  p=[None]*n;shift=tr['shift']
  for t,q,b in data['template']:
   for j in J:
    if t<6:r=18+6*j+t;c=2*(q+1)*m+b+shift-2*j
    else:r=6*m+18+3*case+2*j+t-6;c=2*q*m+b+shift+2*j
    assert p[r] is None
    p[r]=c%n
  # Infer patch rows as actual complement, not by verifier's band formulas.
  missing=[r for r in range(n) if p[r] is None]
  assert len(missing)==len(tr['columns'])
  for r,(a,b) in zip(missing,tr['columns']):p[r]=a*u+b
  out.append(p)
 return out

def makeHodd(n):
 t=(n-4)//8;data=json.load(open(ROOT / "h_odd_certificate.json"));out=[]
 for tr in data['transversals']:
  pi=tr['pi'];p=[4*(r//4)+pi[r%4] for r in range(n)]
  for (a,b),(c,d) in zip(data['rows'],tr['columns']):p[a*t+b]=c*t+d
  out.append(p)
 return out

def makeHeven(n):
 k=n//4;rho=k%4;out=[]
 E=set(range(7))|set(range(k-6,k))
 for center in (k//4,k//2,3*k//4):E.update(range(center-6,center+7))
 assert len(E)==52
 data=json.load(open(ROOT / "h_even_certificate.json"))[str(rho)]
 for tr in data:
  p=[None]*n;d=tr['shift']
  for t in range(k-1):
   if t in E:continue
   x=(t+int(t>=k//2)+d)%k
   for i,c in enumerate((0,2,3,1)):
    r=(4*t+3+i)%n
    assert p[r] is None;p[r]=4*x+c
  for (ar,br),(ac,bc),(ass,bs) in tr['choices']:
   r=(ar*k+br)%n;c=(ac*k+bc)%n;s=(ass*k+bs)%n
   assert p[r] is None;p[r]=c
   assert H(n,r,c)==s
  out.append(p)
 return out


def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('n',type=int,help='an even integer strictly larger than 10000')
 parser.add_argument('--check-only',action='store_true',help='verify without writing the column permutations')
 args=parser.parse_args();n=args.n
 if n<=10000 or n%2:parser.error('n must be even and >10000')
 if n%4==2:perms=makeG(n);entry=G;family='G'
 elif n%8==4:perms=makeHodd(n);entry=H;family='H'
 else:perms=makeHeven(n);entry=H;family='H'
 check(n,perms,entry)
 if args.check_only:
  print(f'PASS n={n}: {len(perms)} transversals, empty common intersection.')
 else:
  # Column P[r] is the selected column in row r, with all indices zero-based.
  json.dump({'order':n,'family':family,'indexing':'zero-based',
             'column_permutations':perms},sys.stdout,separators=(',',':'))
  sys.stdout.write('\n')

if __name__=='__main__':main()
