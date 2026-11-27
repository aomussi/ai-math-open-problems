# The minimum-heap-11 slice of three-heap Wythoff Nim

A move either reduces one heap or removes amounts with bitwise XOR zero and positive sum. Write the sorted losing positions of minimum heap 11 as $(11,x_i,x_i+d_i)$, indexed from $i=1$ in increasing order of $x_i$.

Let $F=\{0,\ldots,10,12,18,22,24,28,32,34\}$. Then $x_i$ is the mex of $F$ and the two larger coordinates of all preceding positions. The initial 29 differences are

```text
6 16 26 4 29 32 33 37 39 40 11 45 46 48 49
50 51 53 54 56 57 58 60 61 62 63 64 65 66
```

For $30\le i\le1213$, $d_i=i+38$, and for $i\ge1214$, $d_i=i+39$. Setting $a_d=x_{d-39}$ for $d\ge1253$, we have $|a_d-\lfloor\varphi d\rfloor+61|\le1$, where $\varphi=(1+\sqrt5)/2$. Thus the tail starts at difference 1253 with offset $-61$.

## Exact enumeration and the infinite mex tail

Enumerate minima $m=0,\ldots,11$ and middle coordinates $a=m,\ldots,5254$ in that order. For each permutation $(q,r,s)$ of a known losing target with $q\le m,r\le a$, a zero-XOR move requires $b=s+((m-q)\mathbin{\oplus}(a-r))$. Only moves with positive total removal are legal. The verifier adds the one-heap exclusions and the same-slice endpoint and difference exclusions. If every $b\ge a$ has a one-heap move to a known losing position, the row has no losing position. Otherwise the least admissible $b$ is losing, and all larger $b$ can reduce to it. Sorting after a reduction never increases the middle coordinate. Within each minimum and middle coordinate, the enumeration therefore needs no bound on $b$. It obtains 3,246 positions in the slice, ending at $(11,5254,8539)$.

The checker matches the first 1,213 enumerated positions to the stated mex rule and differences. Let $T$ be $F$ together with their endpoints. Its size is 2,444 and its maximum is 3,216. Define a hypothetical tail by the same mex forward with consecutive differences starting at 1253. Its first pair is $(1967,3220)$. Upper endpoints are increasing and exceed $\max T$. The checker matches all 2,033 tail pairs through difference 3285 to the remaining exact enumeration. For this mex sequence, the continuation criterion requires $m_2>m_1>N+2$, lower endpoints above $\max T$ after $N$, $a_{m_2}>b_{m_1}$, and bounded errors with no three consecutive nonzero errors on the specified finite window. Use $N=2026,m_1=2030,m_2=3285$. Here $a_N=3217$ and $a_{m_2}=5254>b_{m_1}=5253$. The certificate checks $|a_d-\lfloor\varphi d\rfloor+61|\le1$ for $1253\le d\le3285$ and the three-error condition for every triple ending at $m_1-2\le d\le m_2$. Lemma 2.6 gives the same error bound for every $d>3285$. [Sun and Zeilberger, Lemma 2.6](https://sites.math.rutgers.edu/~zeilberg/mamarimY/Zeilberger_y2004_p225.pdf#page=4)

## Moves to smaller minima

If a tail candidate could move to $(j,x,x+c)$, $j<11$, via a zero-XOR move with amounts $(u,v,w)$ to a permuted target $(q,r,s)$, then $|w-v|\le v\oplus w=u=11-q$. The three possible choices of $q$ give $|s-r|+11-q\le c+11-j$, hence $c\ge d-(11-j)$. The middle coordinate cannot increase under a reduction, so $x\le a_d$. For every lower slice $j$ and every $c>691$, the lower-slice theorem gives $|x-\lfloor\varphi c\rfloor-\alpha_j|\le1$, with offsets
$$
(0,-4,-10,-16,-20,-26,-32,-39,-46,-52,-56),
$$
The checker converts the ordinal thresholds in the source's Table 1 into difference cutoffs, all at most 691. Since $c\ge1242$,
$$
x-a_d\ge \alpha_j+59-\lceil(11-j)\varphi\rceil>0,
$$
a contradiction. A one-heap move lowering the 11 heap is excluded by the same comparison with $c=d$. If instead a larger heap is lowered below 11, the unchanged larger heap would have to be in $\{12,18,22,24,28,32,34\}$, by the finitely checked lower losing positions with middle coordinate 11. [Sun and Zeilberger, §3 and Table 1](https://sites.math.rutgers.edu/~zeilberg/mamarimY/Zeilberger_y2004_p225.pdf#page=12)

Let $S$ be the 40 integers in $[0,1252]$ missing from the differences of the first 1,213 pairs. For each $e\in S$ and residue $\rho$ modulo 16, the certificate gives a position $(11,A,A+e)$ with $A\equiv\rho$ at or below the first $a\ge1969$ of that residue, and a zero-XOR move to a smaller-minimum losing position. The removals from the two larger heaps have identical high bits because their XOR is at most 11. Adding $16k$ to both preserves legality and their XOR. These 640 witnesses cover all $a\ge1969$, and the exact enumeration covers the rest.

## Completeness

The two endpoints of each candidate are disjoint from all endpoints of every other candidate, and the differences are distinct. The checker verifies this for the prefix, and the tail mex and increasing upper endpoints preserve it. A one-heap move within the slice keeps one endpoint, even when sorting changes its slot. A zero-XOR move within the slice leaves the 11 heap unchanged and reduces both larger heaps by the same amount. Joint endpoint uniqueness or difference uniqueness therefore excludes a move between candidates. For $a>5254$, mex complementarity means that $a$ is an endpoint. If it is an upper endpoint, reduce the last heap to its paired lower endpoint. If $a=a_d$, reduce $b>a+d$ to $a+d$. For $b<a+d$, a previously used difference gives a move reducing both large heaps by the same amount. An unused difference belongs to $S$ and has its smaller-minimum move as above. This verifies the losing-position recursion for all positions.

## Reproduction

Run `python3 verify_wythoff11.py --output /tmp/wythoff11-replay` in [certificate](certificate/verify_wythoff11.py). The verifier regenerates the finite enumeration, the 640 witnesses and the continuation data. The [published lower slices and continuation lemma](https://doi.org/10.1007/s00026-004-0217-3) are mathematical inputs.
