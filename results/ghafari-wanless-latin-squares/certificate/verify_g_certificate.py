#!/usr/bin/env python3
"""Exact affine verification of G_n witnesses for all n=4k+2 >10000.
The parameter is u>=622; m=2u+epsilon, n=8m+38+4case.
All checks are integer identities or inequalities on this entire half-line.
No search, floating point, randomized step, or enumeration of orders is used.
"""
import json, sys
from pathlib import Path

if not __debug__:
    raise SystemExit("Run Python without -O or -OO; verification uses assertions.")
UMIN=622

def add(x,y):return(x[0]+y[0],x[1]+y[1])
def sub(x,y):return(x[0]-y[0],x[1]-y[1])
def mul(x,t):return(x[0]*t,x[1]*t)
def val(x):return UMIN*x[0]+x[1]
def nonneg(x):return x[0]>=0 and val(x)>=0
def positive(x):return x[0]>=0 and val(x)>0

def ge(x,y):
 d=sub(x,y)
 if nonneg(d):return True
 if positive(mul(d,-1)):return False
 raise AssertionError(('inequality not constant for all u>=UMIN',x,y))
def eq(x,y):
 d=sub(x,y)
 if d==(0,0):return True
 if positive(d) or positive(mul(d,-1)):return False
 raise AssertionError(('equality not constant for all u>=UMIN',x,y))
def eqc(x,c):return eq(x,(0,c))
def mod(x,p,rho):return(x[0]*rho+x[1])%p

def canonical(x,N):
 q=val(x)//val(N)
 y=sub(x,mul(N,q))
 assert nonneg(y) and positive(sub(N,y)),('cannot reduce uniformly',x,N,q)
 return y

def delta_g(r,c,N,case,eps,rho):
 # Equation (3), in the precise order of its clauses.
 specialrow=any(eqc(r,z) for z in (0,5,10))
 if specialrow and mod(c,4,rho)==1 and ge(c,add(r,(0,2))):return 4
 if any(eqc(r,a) and eqc(c,b) for a,b in ((5,3),(10,3),(10,7))):return 4
 if any(eqc(r,a) and eqc(c,b) for a,b in ((1,2),(6,6),(11,10))):return 3
 plus1=((0,3),(0,4),(5,7),(5,8),(10,11),(10,12),(15,12),(15,13),(16,12))
 if any(eqc(r,a) and eqc(c,b) for a,b in plus1):return 1
 minus1=((1,3),(1,4),(1,5),(6,7),(6,8),(6,9),(11,11),(11,12),(11,13),(16,13))
 if any(eqc(r,a) and eqc(c,b) for a,b in minus1):return -1
 if any(eqc(r,a) and eqc(c,b) for a,b in ((4,2),(4,5),(9,6),(9,9),(14,10),(14,13))):return -3
 if any(eqc(r,z) for z in (4,9,14)) and mod(c,4,rho)==1 and ge(c,add(r,(0,2))):return -4
 if any(eqc(r,a) and eqc(c,b) for a,b in ((9,3),(14,3),(14,7))):return -4
 if eqc(r,15) and not eqc(c,12) and mod(c,2,rho)==0:return 2
 if eqc(r,17) and mod(c,2,rho)==0:return -2
 end=(12,6*eps+18+3*case) # 3k-9
 if ge(r,(0,18)) and ge(sub(end,(0,1)),r):
  if mod(r,3,rho)==0 and mod(c,2,rho)==0:return 2
  if mod(r,3,rho)==2 and mod(c,2,rho)==0:return -2
 return 0

def core_rows(case,eps):
 ans=[]
 for a,lo,hi in [(0,0,197),(6,-156,197),(12,6*eps-162,6*eps+77+3*case),(14,6*eps-40+3*case,6*eps+77+3*case),(16,8*eps-42+3*case,8*eps+37+4*case)]:
  ans.extend((a,b) for b in range(lo,hi+1))
 assert len(ans)==990+4*case
 assert all(positive(sub(y,x)) for x,y in zip(ans,ans[1:]))
 return ans

def partition(N,step,background,points):
 """Prove that APs plus points partition every integer in [0,N-1]."""
 buckets=[[] for _ in range(step)]
 for lo,hi in background+[(p,p) for p in points]:
  assert nonneg(sub(hi,lo))
  assert nonneg(lo) and positive(sub(N,hi))
  assert lo[0]%step==hi[0]%step==0
  residue=lo[1]%step
  assert hi[1]%step==residue
  aa=(lo[0]//step,(lo[1]-residue)//step)
  bb=(hi[0]//step,(hi[1]-residue)//step)
  buckets[residue].append((aa,bb))
 for residue,intervals in enumerate(buckets):
  intervals.sort(key=lambda q:val(q[0]))
  nextlo=(0,0)
  for lo,hi in intervals:
   assert lo==nextlo,('partition gap or overlap',step,residue,lo,nextlo)
   nextlo=add(hi,(0,1))
  upper=(N[0]//step,(N[1]-1-residue)//step)
  assert nextlo==add(upper,(0,1))

def bulk_aps(template,case,eps,shift,N):
 C=[];S=[]
 assert sorted(t for t,q,b in template)==list(range(8))
 # The selected j indices, valid for every u>=UMIN.
 intervals=[((0,30),(1,-30)),((1,30),(2,eps-31))]
 for t,q,b in template:
  assert 0<=q<4 and 0<=b<4
  if t<6:
   abase=(4*(q+1),2*(q+1)*eps+b+shift);colstep=-2
   rbase=(0,18+t);rstep=6;delta=2 if t in (0,3) else 0
   if t in (0,3):assert (b+shift)%2==0
   if t in (2,5):assert (b+shift)%2==1
  else:
   abase=(4*q,2*q*eps+b+shift);colstep=2
   rbase=(12,6*eps+18+3*case+t-6);rstep=2;delta=0
  sbase=add(add(abase,rbase),(0,delta));symstep=colstep+rstep
  assert symstep==4
  for jlo,jhi in intervals:
   assert nonneg(sub(jhi,jlo))
   rlo=add(rbase,mul(jlo,rstep));rhi=add(rbase,mul(jhi,rstep))
   end=(12,6*eps+18+3*case)
   assert ge(rlo,(0,18))
   if t<6:assert ge(sub(end,(0,1)),rhi)
   else:assert ge(rlo,end)
   rawc=[add(abase,mul(jlo,colstep)),add(abase,mul(jhi,colstep))]
   if colstep<0:rawc.reverse()
   raws=[add(sbase,mul(jlo,4)),add(sbase,mul(jhi,4))]
   for raw,dest in ((rawc,C),(raws,S)):
    quotient=val(raw[0])//val(N)
    assert val(raw[1])//val(N)==quotient
    lo,hi=(sub(x,mul(N,quotient)) for x in raw)
    assert nonneg(lo) and positive(sub(N,hi))
    dest.append((lo,hi))
 return C,S

def verify(cert):
 assert set(cert)=={'0_0','0_1','1_0','1_1'}
 for key,data in cert.items():
  case=data['case'];eps=data['epsilon'];assert key==f'{case}_{eps}'
  N=(16,8*eps+38+4*case)
  rows=core_rows(case,eps)
  assert all(nonneg(r) and positive(sub(N,r)) for r in rows)
  rap=[]
  for jlo,jhi in [((0,30),(1,-30)),((1,30),(2,eps-31))]:
   rap.append((add((0,18),mul(jlo,6)),add((0,23),mul(jhi,6))))
   rap.append((add((12,6*eps+18+3*case),mul(jlo,2)),add((12,6*eps+19+3*case),mul(jhi,2))))
  partition(N,1,rap,rows)
  trans=data['transversals'];assert [(d['shift'],d['omit']) for d in trans]==[(0,1),(2,6),(4,11),(6,16)]
  allcols=[]
  for d in trans:
   shift=d['shift'];cols=[tuple(c) for c in d['columns']]
   assert len(cols)==len(rows)
   syms=[]
   for r,c in zip(rows,cols):
    assert nonneg(c) and positive(sub(N,c))
    # Modulo 12 covers every residue needed in equation (3).
    values={delta_g(r,c,N,case,eps,rho) for rho in range(12)}
    assert len(values)==1,('delta changes with the parameter',r,c,values)
    dd=values.pop();syms.append(canonical(add(add(r,c),(0,dd)),N))
   cap,sap=bulk_aps(data['template'],case,eps,shift,N)
   partition(N,2,cap,cols)
   partition(N,4,sap,syms)
   om=d['omit'];badc={1:2,6:6,11:10,16:12}[om]
   assert not eq(cols[rows.index((0,om))],(0,badc))
   allcols.append(cols)
  # All four use precisely the same background row set; their background
  # columns differ by shifts 0,2,4,6, so cannot have a common cell there.
  for z in range(len(rows)):
   assert any(not eq(allcols[0][z],cc[z]) for cc in allcols[1:])
  print('Certified case',case,'epsilon',eps,'for every integer u >=',UMIN)
 print('Certified G_n: four transversals with empty intersection for every n>10000, n=2 mod4.')

if __name__=='__main__':
 filename=sys.argv[1] if len(sys.argv)>1 else Path(__file__).with_name('g_all_certificate.json')
 verify(json.load(open(filename)))
