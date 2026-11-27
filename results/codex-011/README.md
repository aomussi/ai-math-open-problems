# Partitioning a graph into induced paths with a path quotient is NP-complete

**Theorem.** It is NP-complete to decide whether a simple graph has a partition into induced paths whose simple quotient is a path. The result holds even on connected line graphs of maximum degree six.

The simple quotient has one vertex per part, with an edge when an original edge joins the parts. A part may be a single vertex, and so may the quotient. A certificate gives an ordered partition. In each part verify nonemptiness, connectivity and maximum degree two, and use the edge count to exclude a cycle. Between parts verify that edges occur only between consecutive parts and that each consecutive pair is joined. These tests are polynomial.

## Two paths are forced in a line graph

For a nonempty edge set $S$ of $J$, the graph induced on $S$ in $L(J)$ is a path precisely when $S$ forms a path as an edge subgraph of $J$. The edges of a path share a vertex exactly when they are consecutive. Conversely, if $L(J)[S]$ is a path, the edge subgraph on $S$ is connected, has maximum degree at most two, and is acyclic. Three edges at a vertex would give a triangle, and the line graph of a cycle is itself a cycle.

Suppose $J$ has four leaves and all other vertices have degree four. A valid partition of $L(J)$ gives an edge partition of $J$ into nonempty paths. The four edges at a degree-four vertex form a $K_4$ in $L(J)$. No part contains three of them, and they meet at most two parts because three parts would form a triangle in the quotient. They therefore split two and two. No path ends at a degree-four vertex, and each of the four leaves is an endpoint exactly once. So the partition has exactly two paths and both visit every nonleaf vertex.

## Reduction

Take a simple, planar 3-connected cubic graph $F$. Hamiltonian cycle is NP-complete on this class. Set $H=L(F)$, choose a vertex $q$ of $H$, and replace it with four leaves, each joined to one former neighbor of $q$. Call the graph $J$ and output $L(J)$.

Kotzig's equivalence states that $F$ is Hamiltonian exactly when $H$ decomposes into two edge-disjoint Hamiltonian cycles. Splitting $q$ cuts such cycles into two paths in $J$. The paths meet at all nonleaf vertices, so their quotient in $L(J)$ is $K_2$. Conversely, a valid partition yields two paths as in the preceding lemma. Identifying their four endpoints back to $q$ yields two Hamiltonian cycles that partition $E(H)$, so $F$ is Hamiltonian.

For $n=|V(F)|$ there are $3n$ vertices and $9n-6$ edges in the output. A vertex corresponding to a leaf edge of $J$ has degree three, and the others have degree six. In the restricted source instances $F-e$ is connected for every edge $e$, thus $H-q$, $J$, and $L(J)$ are connected.

## Kotzig's equivalence

The triangles $T_v$ of $L(F)$ induced by the three edges at vertices $v\in V(F)$ partition $E(L(F))$. If $C$ is a Hamiltonian cycle of $F$, orient the perfect matching $M=E(F)\setminus E(C)$ arbitrarily. In $T_v$ let $a,b$ be the two cycle edges and $m$ the matching edge. At the tail of $m$, color the path $a,m,b$ red and the edge $ab$ blue, and at the head reverse the colors. Each color follows $C$, inserting each matching edge as an intermediate vertex exactly once, so both colors are Hamiltonian cycles.

Conversely, color the two Hamiltonian cycles red and blue. In each triangle, one color has two edges and the other has one since a monochromatic triangle would be a whole cycle of that color. Mark the middle vertex of the two-edge path. If the mark corresponds to $uv$, both edges at that vertex in the other triangle must have the opposite color, so it is marked there too. The marked edges form a perfect matching of $F$. Suppressing their vertices in the red cycle produces the line graph of the 2-factor complementary to the matching. Connectivity forces that 2-factor to be a single Hamiltonian cycle.

[Barbados 2026, Problem 2](https://web.math.princeton.edu/~pds/barbados26/problems.pdf#page=1) · [Garey, Johnson and Tarjan](https://doi.org/10.1137/0205049) · [Bryant et al., Hamilton decompositions of line graphs](https://arxiv.org/abs/2012.00988)
