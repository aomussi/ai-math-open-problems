# Extensions of Green's Problem 88

The [three-dimensional grid theorem](README.md) gives an absolute $\delta>0$ such that $G(N)\le N^{2-\delta}$, where $G(N)$ is the largest size of a pairwise 2-comparable subset of $[N]^3$. Write $M(a,b,c)$ for the rectangular version and $\theta=(2-\delta)/3$. The rectangular induction gives $M(a,b,c)\le 2(abc)^\theta$. Taking length-$\ell$ lexicographic products in each coordinate preserves 2-comparability, since the first differing triple determines two strict comparisons of the coordinate words. This gives $M(a,b,c)^\ell\le 2(abc)^{\ell\theta}$ and hence $M(a,b,c)\le (abc)^\theta$.

## The modular question

For an odd prime $p$, let $H=\{1,\ldots,(p-1)/2\}\subseteq\mathbb F_p$, and let $D_p$ be all coordinate permutations of $(0,u,-v)$ with $u,v\in H$. This is the forbidden difference set in [Green's comment to Problem 88](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#page=42).

**Theorem.** The maximum size of $A\subseteq\mathbb F_p^3$ with $(A-A)\cap D_p=\varnothing$ is exactly $p^2$.

The plane $\{(x,y,x):x,y\in\mathbb F_p\}$ has $p^2$ points. Its differences have the form $(d,e,d)$, and when exactly one entry vanishes the two nonzero entries are equal. They cannot belong to opposite halves $H$ and $-H$.

For the upper bound, use the map $(x,y,z)\mapsto(x,y+z)$. A collision of distinct points gives a difference $(0,d,-d)$ with $d\ne0$. One of $d$ and $-d$ lies in $H$, and the other lies in $-H$, so this difference belongs to $D_p$. The map is injective on $A$ and its target has size $p^2$.

The same proof works over $\mathbb Z/p\mathbb Z$ for every positive odd integer $p$. Both the upper bound and its attainment are checked in Lean 4 in [Green88.Modular](lean/Green88/Modular.lean). See the [verification instructions](lean/README.md).

### A line-occupancy condition that restores a power saving

Call a set in $[N]^3$ weakly admissible if it forbids pairs agreeing in one coordinate with the other two differences nonzero and of opposite signs. Connect consecutive points on each axis-parallel line by an edge in the increasing direction. Two outgoing edges from a point in different directions would have ends that form a forbidden pair. The same holds for incoming edges. Coordinate sums strictly increase along edges, so the graph consists of directed paths, including isolated vertices.

If every axis-parallel line has at most $D$ points, color each path cyclically with $D$ colors. The points on any one line occur consecutively along their path, hence use distinct colors. Within each color, pairs agree in at most one coordinate. If one coordinate agrees the weak condition gives 2-comparability, and otherwise a majority of the three strict comparisons gives it. The total size is at most $D G(N)$.

In fact, the unrestricted weak maximum $W(N)$ satisfies

$$
N^2\le W(N)\le N^2+\left\lfloor\frac{N-1}{3}\right\rfloor .
$$

The plane above supplies the lower bound. For the upper bound, write $m$ for the set size, $c$ for the number of paths and $P$ for the sum of the three two-coordinate projection sizes. Counting the directed edges gives $3m-P=m-c$. Each path has at most $3N-2$ vertices, so $P=2m+c$ and $c\ge m/(3N-2)$. In the tripartite graph whose edges are the three projections, the only triangles are the original triples. An extra triangle would have three supplying points, each differing from the triangle's triple in a different coordinate. Comparing the suppliers pairwise, the weak condition would require those three nonzero changes to have pairwise opposite signs. Each absent triangle has a missing edge, and each missing edge is in $N$ candidate triples. Thus $N^3-m\le N(3N^2-2m-c)$, giving $m\le N^3(3N-2)/(3N^2-3N+1)<N^2+N/3$.

For the modular problem, split each residue axis into two consecutive intervals of length at most $h=(p+1)/2$. In each of the eight boxes, the signs of integer differences agree with the modular halves. Therefore under the additional line occupancy bound $D$, a modular admissible set has size at most $8D G(h)\le 8D h^{2-\delta}$. Forbidding every nonzero axis-parallel difference gives the case $D=1$.

## Higher-dimensional grids

[Lean 4 proof and axiom audit](lean/Green88/HigherDimension.lean) · [Build and verification commands](lean/README.md).

Let $G_{q,r}(N)$ be the largest size of a subset of $[N]^q$ in which each pair has at least $r$ strict coordinate comparisons in one common direction. For every $2\le r<q$,

$$
G_{q,r}(N)\le N^{q-r-1}G(N)\le N^{q-r+1-\delta}.
$$

Fix the values of $q-r-1$ coordinates. In each fiber, any pair has at most one exception to the required direction among the $r+1$ remaining coordinates. Project onto any three of those coordinates. At least two still compare strictly in the same direction, so the projection is injective and its image is 2-comparable. Each fiber has at most $G(N)$ points.

For $r\ge3$, a fixed power saving already follows from [Fox, Sudakov and Wigderson, Proposition 1.5](https://arxiv.org/html/2512.10438v2#S1.SS2) and [Gowers and Long, Theorem 1.13](https://arxiv.org/html/1609.08688#S1.SS4), using the same fiber reduction. Indeed, $r>2(r+1)/3$ makes the comparable-set bound in $r+1$ dimensions equivalent to the bound for increasing sequences. Any such sequence projects onto a 2-increasing sequence in three coordinates. The present bound also covers $r=2$ in every dimension.

By the [correspondence with pod packings](https://arxiv.org/html/2512.10438v2#S1.SS2), the upper bound gives density $O_{q,r}(N^{-\delta})$ for packings by aligned $(q,r)$-pods of side length $N$. A pod consists of the vectors in $\{0,\ldots,N-1\}^q$ with at most $r-1$ positive coordinates and has $O_{q,r}(N^{r-1})$ points. For anchors in one $N$-box, their translates intersect exactly when the coordinatewise maximum of the anchors lies in both pods, equivalently when the anchors are not $r$-comparable. Partition the anchor lattice into $N$-boxes and apply the bound in each box. For $q=3,r=2$ this is the tripod density bound. The same grid theorem bounds the number of filled cells in the [monotone partial matrices of Aronov, Dujmović and Morin](https://arxiv.org/html/1706.10193#S4.SS3), by mapping a filled cell to its column, row and label.

## Color-avoiding paths under an acyclicity assumption

[Lean 4 proof and axiom audit](lean/Green88/ColorAvoiding.lean) · [Build and verification commands](lean/README.md).

In a three-colored tournament of order $m$, write $D_i$ for the spanning digraph of edges outside color $i$, and $L_i$ for the maximum number of vertices in a simple directed path in $D_i$.

**Proposition.** If at least one $D_i$ is acyclic, then

$$
m\le M(L_1,L_2,L_3)\le (L_1L_2L_3)^\theta,\qquad
\max_i L_i\ge m^{1/(2-\delta)} .
$$

For any positive integers $n_1,n_2,n_3$, the maximum order in this class subject to $L_i\le n_i$ is exactly $M(n_1,n_2,n_3)$.

In any digraph $D$, take an inclusion-maximal acyclic spanning subgraph $H$ and label its vertices by the maximum number of vertices in a path in $H$ ending there. Along an edge of $H$ this height strictly increases. Equal-height vertices have no edge between them in $D$. Indeed, an edge $u\to v$ in $D$ outside $H$ forces a path from $v$ to $u$ in $H$ by maximality.

Relabel so that $D_1$ is acyclic, and take $H_1=D_1$ with height $h_1$. Every edge in an $h_1$ level has color 1. Choose a directed Hamilton path in each level's tournament and let $P$ be their union. A tournament has such a path by successively inserting vertices into a directed path.

In $D_2$, the edges of $P$ together with all color-3 edges form an acyclic digraph. Along color-3 edges $h_1$ increases, and within each level $P$ is a path. Extend the digraph to an inclusion-maximal acyclic spanning subgraph $H_2$ and use its height $h_2$. Let $Q$ be all edges whose ends have equal $h_2$. These edges have color 2 and strictly increase $h_1$. Along $P$ the height $h_2$ strictly increases and $h_1$ stays constant. Hence $P\cup Q$ lies in $D_3$ and is acyclic, since $h_1+h_2$ increases. Extend it to an inclusion-maximal acyclic spanning subgraph $H_3$ with height $h_3$.

Now label a vertex by $(h_1,h_2,h_3)$. If two vertices have equal $h_1$, their path order in $P$ increases both $h_2$ and $h_3$. If their $h_2$ agrees, the edge in $Q$ increases both $h_1$ and $h_3$. If their $h_3$ agrees, the edge has color 3 and is in both $H_1$ and $H_2$, so it increases both $h_1$ and $h_2$. Pairs with no equal coordinate compare in the majority direction. This is an injection into an admissible rectangular grid as $h_i\le L_i$.

Conversely, take a 2-comparable set in $[n_1]\times[n_2]\times[n_3]$. Orient each edge toward the point larger in at least two coordinates and color it by the sole coordinate failing to increase, with any color allowed when all three increase. This is the construction from [Fox, Sudakov and Wigderson, equation (3)](https://arxiv.org/html/2512.10438v2#S1.SS2). Each $D_i$ is acyclic and its paths have at most $n_i$ vertices, proving equality of the maxima.

If some $D_i$ can instead be partitioned into $b$ acyclic induced parts, applying the proposition to each induced subtournament gives $m\le bG(L)\le bL^{2-\delta}$, where $L=\max_iL_i$. This argument leaves the unrestricted three-color path problem open.
