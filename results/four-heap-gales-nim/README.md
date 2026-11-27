# A finite-state classification for four-heap Gale's Nim

A move reduces one heap. Moving to one positive heap wins immediately. A position is P if the player about to move loses under optimal play. For each fixed $1\le a\le b$ we construct an eventually periodic function $f_{a,b}(n)$ on $n>b$ such that $(a,b,c,d)$ for $b<c<d$ is P exactly when $d-c=f_{a,b}(c)$. A value of zero means no such P position exists with third heap $c$. Computing $f_{a,b}$ requires only finite preprocessing for each fixed $a,b$. [Nowakowski, Problem A8](https://library.slmath.org/books/Book71/files/GONC6-04.pdf#page=9)

## Boundary cases

With two heaps the position is N. With three heaps, all positive sizes can be shifted down by one and the result is the ordinary Nim classification using XOR zero. Emptying a heap leaves two heaps, from which the opponent wins on the next move, so the shifted-Nim recursion gives the result. With four heaps including a 1, removing that heap gives the shifted three-heap test, while keeping a 1 gives ordinary Nim on the remaining heaps. The classification is $b\oplus c\oplus d=0$ for $(1,b,c,d)$. To see that deleting the chosen 1 from a candidate cannot win, if $b\oplus c\oplus d=0$, the lowest bit on which $b,c,d$ have a 1 has exactly two ones. Subtracting one from all three gives either a nonzero lower bit or a nonzero bit at that position. Deleting another heap leaves a 1 and a three-heap P position only if the other two sizes are equal, which is incompatible with XOR zero in the candidate. The ordinary Nim response on three heaps supplies the winning move from any other four-heap position with a 1. If the response empties a heap, the resulting $(1,y,y)$ is P under the shifted three-heap rule. When every size is at least two and some sizes coincide, the P positions are exactly paired sizes. Paired positions cannot move to one another, and an unpaired repeated position can match the other two sizes by reducing the larger. Reducing or deleting a heap from a paired position leaves a 1-case or three-heap P position only if the paired size is zero or one, which is excluded.

## Greedy matching and the proof

For $a=1$, take $f_{1,b}(n)=\max((n\oplus b)-n,0)$. For $2\le a=b$, take $f_{a,a}=0$. For $2\le a<b$, previously constructed pairs of indices are
$$
\mathcal L=\{(r,b):1\le r<a\}\cup\{\operatorname{sort}(a,s):1\le s<b\}.
$$
Define $E$ by adding $1+((a-1)\oplus(b-1))$ if it exceeds $b$, and adding $b+f_{\operatorname{sort}(a,s)}(b)$ for each $1\le s<b$ for which that value of $f$ is positive. The integers in $E$ are precisely the unchanged large heap sizes allowing the other large heap to drop to at most $b$ and yield a P position. For $n>b$, the positive forbidden gaps $B(n)$ are
$$
((n-1)\oplus(a-1))-(n-1),\quad ((n-1)\oplus(b-1))-(n-1),\quad f_{u,v}(n)\ ((u,v)\in\mathcal L).
$$
They correspond to moves decreasing one of the two small heaps. Process $n>b$ in increasing order. If it is excluded or used, set $f(n)=0$. Otherwise match it to the least unused, unexcluded $m>n$ with $m-n\notin B(n)$.

A matched pair cannot move to another matched pair by changing a large heap because it would have to retain an endpoint. Small-heap moves and moves into the boundary cases are excluded by construction. For an unmatched pair $n<m$, exclusion of either endpoint gives a boundary move. A forbidden gap gives a small-heap move. If $n$ was already paired to a smaller endpoint, reduce $m$ to that endpoint. Otherwise $n$ initiates a pair with endpoint $w$. If $w<m$, reduce $m$ to $w$. If $w>m$ and $m$ was already used, reduce $n$ to its earlier partner. The remaining case of unused $m$ and $w>m$ contradicts the greedy choice. By induction on the sum of heap sizes this gives the P positions.

## Finite preprocessing

The undirected graph of forbidden gaps has degree at most $|\mathcal L|+2\le a+b$, since the lower functions and the two XOR maps each give matchings. If $n$ is matched to $m$, an intervening unused vertex was excluded or is a forbidden neighbor of $n$ above $n$. An intervening used vertex was paired to a distinct $u<n$ that was forbidden to pair with $n$, so charge it to that neighbor below $n$. The gap is at most $W=a+b+|E|+1$.

Beyond the largest excluded vertex and all lower preperiods, the forbidden sets are periodic of period $L$, the least common multiple of the lower periods and a power of two greater than $b$. The phase modulo $L$ and the used bits at offsets $0,\ldots,W-1$ determine every next step. A state repeats in at most $L2^W+1$ steps, and the deterministic recursion then repeats its output. The lower pairs have smaller index sum, so preprocessing terminates inductively.

Run `python3 verify.py` in this directory to compare the formula with direct game recursion for 8,855 four-heap positions of maximum size at most 20. The comparison is a finite implementation check. The foregoing proof supplies the unbounded classification.
