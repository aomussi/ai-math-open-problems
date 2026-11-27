from functools import lru_cache
from itertools import combinations_with_replacement
from math import lcm

@lru_cache(None)
def table(a,b):
    Q=1<<b.bit_length()
    if a==1:
        return b+1, (), tuple(max((n^b)-n,0) for n in range(b+1,b+1+Q))
    if a==b:
        return b+1, (), (0,)
    pairs={(r,b) for r in range(1,a)}|{tuple(sorted((a,s))) for s in range(1,b)}
    E=set()
    z=1+((a-1)^(b-1))
    if z>b:E.add(z)
    for s in range(1,b):
        h=f(*sorted((a,s)),b)
        if h:E.add(b+h)
    W=a+b+len(E)+1
    L=lcm(Q,*(len(table(*uv)[2]) for uv in pairs))
    T=max(b+1,1+max(E,default=0),*(table(*uv)[0] for uv in pairs))
    used=set(); seen={}; out=[]; n=b+1
    while True:
        if n>=T:
            state=(n%L,tuple(sorted(x-n for x in used)))
            if state in seen:
                r=seen[state]; i=r-(b+1)
                if (a,b)==(3,4):print('raw',E,W,L,T,r,n,out)
                return r,tuple(out[:i]),tuple(out[i:])
            seen[state]=n
        if n in E or n in used:
            used.discard(n); out.append(0)
        else:
            B={((n-1)^(a-1))-(n-1),((n-1)^(b-1))-(n-1)}|{f(*uv,n) for uv in pairs}
            h=next(h for h in range(1,W+1) if n+h not in E and n+h not in used and h not in B)
            used.add(n+h);out.append(h)
        n+=1

def f(a,b,n):
    assert 1<=a<=b<n
    t,pre,per=table(a,b)
    return pre[n-b-1] if n<t else per[(n-t)%len(per)]

@lru_cache(None)
def direct(p):
    if len(p)<=1:return True
    for i,x in enumerate(p):
        for y in range(x):
            q=tuple(sorted(p[:i]+p[i+1:]+((y,) if y else ())))
            if direct(q):return False
    return True
# direct returns True iff P (terminal true)
def rule(p):
    a,b,c,d=p
    if a==1:return b^c^d==0
    if len(set(p))<4:return a==b and c==d
    return d-c==f(a,b,c)
if __name__=='__main__':
    print('3,4:',table(3,4))
    for limit in (15, 20):
        count = 0
        for position in combinations_with_replacement(range(1, limit + 1), 4):
            assert direct(position) == rule(position), position
            count += 1
        print(limit, count)
