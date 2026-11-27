"""Independent universal verifier for no-H33 Dawson's Kayles.
Uses original octal0.07 moves, not candidate option lists or an outcome oracle.
"""
import json,time,collections
from pathlib import Path
from functools import lru_cache

import os
os.chdir(Path(__file__).resolve().parent)

start=time.monotonic()
B=json.loads(Path('background.json').read_text())
TAB=json.loads(Path('outcomes.json').read_text())['p_table']
A=B['actions'];n=B['states'];assert n==len(TAB)==664
HS=tuple(h for h in range(2,33) if h!=30)
assert A[0]==A[1]==list(range(n))
assert all(len(A[h])==n and set(A[h])<=set(range(n)) for h in HS)
# A deterministic system of commuting heap actions gives a well-defined
# homomorphism from the free commutative background monoid.
for h in HS:
 for j in HS:
  assert all(A[h][A[j][q]]==A[j][A[h][q]] for q in range(n)),(h,j)
seen={0};queue=collections.deque([0])
while queue:
 q=queue.popleft()
 for h in HS:
  r=A[h][q]
  if r not in seen:seen.add(r);queue.append(r)
assert len(seen)==n
for q,w in enumerate(B['representatives']):
 r=0
 for h in w:
  assert h in HS;r=A[h][r]
 assert r==q,(q,w,r)
print('ACTION SYSTEM: commuting, all664states reachable, representatives consistent',flush=True)

# This definition is independent of root2_counter_formula.py.
def cell(k,m):
 if k<0 or m<0:return -1
 if m<=5:
  return 8*m+(k if k<=5 else 6+(k&1))
 row=4+(m&1)
 distance=k-m+row
 if distance<=0:
  col=0 if k==0 else (1 if k&1 else 2)
 else:
  col=distance if distance<=5 else 6+(distance&1)
 return 8*row+col
OFF=((0,0),(-1,0),(1,0),(0,-1),(1,-1))
def signature(k,m):return tuple(cell(k+u,m+v) for u,v in OFF)
def canon(k,m):
 if m<=6:return (k if k<=8 else 9+(k-9)%2,m)
 if k<=1:return (k,7+(m-7)%2)
 d=k-m;e=m%2
 if d<=-7:return (2+k%2,10 if e==0 else 9)
 if d>=3:
  mm=8-e
  return (mm+3+(k-(mm+3))%2,mm)
 mm=8+e
 return (mm+d,mm)
reps={}
for m in range(13):
 for k in range(13):reps.setdefault(signature(k,m),(k,m))
assert len(reps)==69
for m in range(100):
 for k in range(100):
  kk,mm=canon(k,m)
  assert 0<=kk<=12 and 0<=mm<=12 and signature(k,m)==signature(kk,mm)
# Unbounded proof of our separate canonicalization lemma in QF_LIA+mod.
from z3 import Int,If,And,Or,Solver,unsat
k,m=Int('audit_k'),Int('audit_m')
def zcell(k,m):
 row=4+m%2;d=k-m+row
 low=If(k<=5,k,6+k%2)
 high=If(d<=0,If(k==0,0,If(k%2==1,1,2)),If(d<=5,d,6+d%2))
 return If(Or(k<0,m<0),-1,If(m<=5,8*m+low,8*row+high))
e=m%2;d=k-m;high_m=8-e
ck=If(m<=6,If(k<=8,k,9+(k-9)%2),If(k<=1,k,If(d<=-7,2+k%2,If(d>=3,high_m+3+(k-(high_m+3))%2,8+e+d))))
cm=If(m<=6,m,If(k<=1,7+(m-7)%2,If(d<=-7,If(e==0,10,9),If(d>=3,high_m,8+e))))
solver=Solver();solver.add(k>=0,m>=0)
solver.add(Or(ck<0,ck>12,cm<0,cm>12,*[zcell(k+u,m+v)!=zcell(ck+u,cm+v) for u,v in OFF]))
result=solver.check();assert result==unsat,(result,solver.model() if str(result)=='sat' else None)
print('COUNTER COVER: independent0..12canonicalization proved UNSAT;69signatures',flush=True)

points=list(reps.values());sigs=list(reps);ns=len(points);ALL=(1<<ns)-1
# For each shift and each background class, encode the set of counter
# signatures where the candidate says P. Invalid shifts have no legal move.
colors=[[0]*n for _ in OFF]
for t,sig in enumerate(sigs):
 for off,c in enumerate(sig):
  if c<0:continue
  row,col=divmod(c,8)
  for q in range(n):
   if TAB[q][row][col]:colors[off][q]|=1<<t

# Rebuild every legal physical option. phi of option is computed by composing
# actual background heap actions; H30 is kept as a separate counter.
options={}
raw_options={}
for h in tuple(HS)+(30,34):
 zz=[];rr=[]
 for left in range((h-2)//2+1):
  right=h-2-left
  pieces=(left,right)
  delta=sum(t==30 for t in pieces)
  assert delta<=1 and 33 not in pieces and 34 not in pieces
  yy=[]
  for q in range(n):
   target=q
   for piece in pieces:
    if piece!=30:target=A[piece][target]
   yy.append(target)
  z=(delta,tuple(yy))
  if z not in zz:zz.append(z);rr.append(pieces)
 options[h]=zz;raw_options[h]=rr
print('ORIGINAL MOVES:',len(HS),'background heap types,',len(options[30]),'D options,',len(options[34]),'E options',flush=True)

# P has no P-option, checked universally by context-state and counter signature.
checks=0
for h in HS:
 for delta,yy in options[h]:
  c=colors[0 if delta==0 else 2]
  for q in range(n):
   bad=colors[0][A[h][q]] & c[yy[q]]
   assert not bad,('P_TO_P_BACKGROUND',h,q,points[(bad&-bad).bit_length()-1])
   checks+=1
for h,offs in [(30,(1,)),(34,(3,4))]:
 for delta,yy in options[h]:
  if h==30:assert delta==0;off=1
  else:off=3 if delta==0 else 4
  for q in range(n):
   bad=colors[0][q]&colors[off][yy[q]]
   assert not bad,('P_TO_P_COUNTER',h,q,points[(bad&-bad).bit_length()-1])
   checks+=1
print('P-CONDITION: passed',checks,'context-option checks acrossall69signatures',flush=True)

# Minimal nonterminal option-image sets. The empty terminal game is kept
# separately: it may not dominate the nonempty option sets of class0.
basewin=[0]*n
for q in range(n):
 for delta,yy in options[30]:basewin[q]|=colors[1][yy[q]]
 for delta,yy in options[34]:basewin[q]|=colors[3 if delta==0 else 4][yy[q]]
losing_masks=[ALL^colors[0][q] for q in range(n)]
terminal_t=points.index((0,0));assert not (colors[0][0]>>terminal_t)&1
terminal_bad=losing_masks[0]&~basewin[0]&~(1<<terminal_t)
assert not terminal_bad,('TERMINAL_BACKGROUND_OTHER_COUNTERS',terminal_bad)

option_bit_colors=colors[0]+colors[2]
seed={h:[] for h in HS}
for h in HS:
 for q in range(n):
  mask=0
  for delta,yy in options[h]:mask |= 1<<(delta*n+yy[q])
  assert mask
  seed[h].append(mask)
transbits={h:[1<<(d*n+A[h][q]) for d in range(2) for q in range(n)] for h in HS}
@lru_cache(None)
def image(h,mask):
 result=0;tb=transbits[h]
 while mask:
  low=mask&-mask;result |= tb[low.bit_length()-1];mask-=low
 return result
@lru_cache(None)
def background_wins(mask):
 result=0
 while mask:
  low=mask&-mask;result |= option_bit_colors[low.bit_length()-1];mask-=low
 return result
front=[set() for _ in range(n)]
work=collections.deque([(0,0,())])
processed=0;added=0;discarded=0
while work:
 q,mask,w=work.popleft()
 if mask and mask not in front[q]:continue
 if mask:
  bad=losing_masks[q]&~(basewin[q]|background_wins(mask))
  if bad:
   t=(bad&-bad).bit_length()-1
   raise AssertionError(('N_WITHOUT_P_OPTION',q,w,points[t],mask))
 processed+=1
 for h in HS:
  r=A[h][q];new=image(h,mask)|seed[h][q]
  existing=front[r]
  if any(old&new==old for old in existing):continue
  remove=[old for old in existing if new&old==new]
  for old in remove:existing.remove(old);discarded+=1
  existing.add(new);added+=1
  work.append((r,new,tuple(sorted(w+(h,)))))
 if processed%1000==0:print('closure',processed,'front',sum(map(len,front)),'queue',len(work),'sec',round(time.monotonic()-start,3),flush=True)

print('UNIVERSAL RECURRENCE VERIFIED',flush=True)
report={'background_states':n,'counter_signatures':ns,'p_context_option_checks':checks,'processed':processed,'antichain_size':sum(map(len,front)),'insertions':added,'discarded_supersets':discarded,'seconds':time.monotonic()-start,'terminal_exception_separate':True,'original_physical_heaps':list(HS),'coverage':'independent0..12canonicalization, SMT UNSAT'}
Path('independent_report.json').write_text(json.dumps(report,indent=2))
print(json.dumps(report),flush=True)
