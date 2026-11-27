# A power saving for pairwise 2-comparable triples

**Theorem (answering Green's Problem 88).** There is an absolute $\delta>0$ such that every pairwise 2-comparable set $S\subseteq[N]^3$ has $|S|\le N^{2-\delta}$. Two distinct triples are 2-comparable if the difference has at least two strictly positive or at least two strictly negative coordinates.

Write $M(r,s,t)$ for the maximum over $[r]\times[s]\times[t]$, and $G(n)=M(n,n,n)$. Gowers and Long's Proposition 1.10 gives $G(n)=o(n^2)$. Fixed-coordinate sections form strict chains in the other two coordinates. Each two-coordinate projection is injective. [Green, Problem 88](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#page=42) · [Gowers and Long, Proposition 1.10](https://arxiv.org/html/1609.08688#S1.SS2)

## Lean 4 formalization

[Source and verification instructions](lean/README.md) accompany the
written proof. The theorem [`Green88.green_88`](lean/Green88/Theorem.lean)
proves the full power saving, including the qualitative bound from
Mathlib's triangle removal lemma, the rectangular induction, and
removal of the leading constant. The project pins Lean 4.19.0 and
Mathlib v4.19.0.

## Rectangular induction

Take $\eta=2^{-36}$, $L=2^{54}$ and choose a fixed $k\ge L$ so that $(3L/\eta)G(k)\le k^2/32$. Put $\delta=\log 2/\log k$ and $\theta=(2-\delta)/3$. Thus $1/2\le\theta<2/3$, $k^{2-3\theta}=2$,
$$
2\eta^{\theta-1/3}\le1/32,\qquad 2\eta^{-1/3}L^{\theta-1}\le1/32.
$$
We prove $M(r,s,t)\le 2(rst)^\theta$ by strong induction on $rst$. Coordinates can be replaced by their relative ranks, preserving all strict comparisons. If $r\le s\le t$ and $r\le k$, then $M\le rs$ and
$$rs/(rst)^\theta\le r^{1-\theta}s^{1-2\theta}\le r^{2-3\theta}\le2.$$

Otherwise divide each axis into $k$ consecutive intervals differing in length by at most one. Let $a,b,c$ be the maximum interval sizes and $V=abc$. For each box $e$, let $u_e,v_e,w_e$ be the numbers of coordinate values used there, divided by $a,b,c$ respectively, and put $p_e=u_ev_ew_e$. Induction gives $|S_e|\le 2V^\theta p_e^\theta$.

For a fixed first-coordinate value the occupied pairs of coarse indices for the other two coordinates form a nondecreasing sequence, with at most $2k-1$ distinct pairs. Thus $\sum_e u_e\le r(2k-1)/a\le2k^2$, and similarly for the other axes. In particular $\sum_e p_e^{1/3}\le2k^2$.

- Boxes with $p_e\le\eta$ contribute at most $2 V^\theta k^2(2\eta^{\theta-1/3})$.
- There are at most $2\eta^{-1/3}k^2$ boxes with $p_e>\eta$. While an axis-parallel coarse line contains at least $L$ such remaining boxes, remove a group of exactly $L$. The three projection sizes of the group's union have product at most $LV$, and strictly less than $rst$ since two coordinates are confined to a single interval. Consequently induction applies to the whole group. All groups contribute at most $2 V^\theta k^2(2\eta^{-1/3}L^{\theta-1})$.
- Let $R$ be the remaining heavy boxes. In each coarse interval on each axis independently choose one actual coordinate uniformly. Mark each box if all three chosen coordinates occur in its three projections. Its marking probability is at least $p_e>\eta$. When two marked boxes share precisely one coarse coordinate, there are points in the two boxes sharing the chosen actual coordinate. Their other two coordinates must be strictly ordered in the same direction, and their distinct coarse indices also have that order. Select marked boxes greedily, deleting those sharing two coarse coordinates with a selected box. Each step removes at most $3L$ boxes, because every coarse axis-parallel line now contains fewer than $L$. The selected boxes form a 2-comparable set in $[k]^3$. With one equal coordinate the preceding argument applies. With none, at least two comparisons agree. Therefore at most $3LG(k)$ boxes can be marked. Expectation gives $|R|\le 3LG(k)/\eta\le k^2/32$. This last part contributes at most $2V^\theta k^2/32$.

Each coefficient is at most $1/32$. Since $r,s,t>k$, we have $a=\lceil r/k\rceil\le2r/k$, and similarly for $b,c$. Thus $V\le8rst/k^3$. Using $8^\theta\le4$ and $k^{2-3\theta}=2$, the three contributions sum to at most $\tfrac34\cdot2(rst)^\theta$. This completes the induction.

## Removing the leading constant

Take words of length $\ell$ over $S$, and encode each of their three coordinate words by its lexicographic rank in $[N]^\ell$. For two different words, their first differing symbol gives at least two strict comparisons in the same direction, which persist in the encoded coordinates. Thus $|S|^\ell\le G(N^\ell)\le 2N^{\ell(2-\delta)}$. Taking $\ell$th roots and sending $\ell$ to infinity proves the bound.

The input $G(n)=o(n^2)$ can also be obtained from triangle removal. In a tripartite graph with parts of size $n$, let each triple supply a triangle. They are edge-disjoint by injectivity of two-coordinate projections. An extra triangle with vertices $(a,b,c)$ would come from three distinct triples $(a',b,c),(a,b',c),(a,b,c')$. If $a'<a$, comparing the first two triples at fixed $c$ gives $b<b'$. Comparing the second and third triples at fixed $a$ then gives $c>c'$. In the first and third triples the second coordinate is $b$, so $c>c'$ forces $a'>a$, a contradiction. Reversing the inequalities excludes $a'>a$. Hence there are at most $n^2$ triangles altogether, and triangle removal requires $o(n^2)$ edge deletions. The supplied edge-disjoint triangles require at least $|S|$ deletions.
