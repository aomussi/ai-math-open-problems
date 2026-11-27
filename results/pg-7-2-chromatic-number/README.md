# The chromatic number of PG(7,2) is six

Let $V=\mathbb F_2^8$. The points are its 255 nonzero vectors, and the lines are triples $\{x,y,x+y\}$ with $x,y$ distinct and nonzero. A cap contains no complete line. Six caps suffice to partition the points, and the computational certificate below excludes a partition into five.

The external input is $\chi(\mathrm{PG}(5,2))=5$. Consequently every color in a hypothetical proper five-coloring meets every 6-dimensional subspace of $V$. Call this property $(*)$. Extending a cap preserves $(*)$. Throughout, a complete cap is a cap maximal under inclusion. [Bishnoi, Cames van Batenburg and Ravi](https://arxiv.org/html/2512.01760v3)

Arévalo showed that a proper five-coloring, if one exists, has a stabilizer that is a 2-group. The proof here excludes all five-colorings by classifying large caps and testing pairs of caps. [Arévalo, Theorem 1](https://fabianarevalo.com/projective-chromatic)

## Classification of large caps

Every cap satisfying $(*)$ has size at most 58. A proof of this bound is given in [the cap bound](cap-bound.md). The classification checks show that the complete caps satisfying $(*)$ with at least 50 points have the following representatives up to $\mathrm{GL}(8,2)$. Vector sums in the formulas are XOR, and integers encode binary vectors in the usual order.

Write $D=\{1,2,4,8,16,32,63\}$, $Q=\{0\}\cup\{d+e:d,e\in D,d<e\}$, $W=\{0,\ldots,63\}$, and $C=\{1,2,4,8,15\}$. Then
$$
\begin{aligned}
A_{58}&=\{x:\operatorname{wt}(x\mathbin{\&}127)\ge5\},\\
A_{53a}&=D\cup(64+\{1,2,4,8\})\cup(128+Q)
  \cup(192+((Q\setminus\{31,47,48\})\cup\{15\})),\\
A_{53b}&=D\cup(64+E_b)\cup(128+Q)\cup(192+(W\setminus(E_b+Q))),
\quad E_b=\{0,3,5,6\},\\
A_{51a}&=D\cup(64+\{1,2,4\})\cup(128+Q)
  \cup(192+((Q\setminus\{24,40,47,48,55\})\cup\{39,56\})),\\
A_{51b}&=\{16u+c:1\le u\le7,\ c\in C\}\cup\{128,\ldots,143\},\\
A_{50}&=E\cup(E+128),\quad E=64+\{64,1,2,4,71\}+\{64,8,16,32,120\}.
\end{aligned}
$$
Here $16u+c$ in $A_{51b}$ uses ordinary integers and concatenates the four-bit representations of $u$ and $c$. A period of a cap $A$ is a vector $p$ such that $A+p=A$. For each of $A_{58}$ and $A_{50}$, 128 is a period, and the image in the quotient by $\langle128\rangle$ has odd size (29 and 25, respectively). Translation by any nonzero vector in the quotient pairs all its points, so neither image can have a nonzero period. Thus 128 is the only nonzero period of either representative. The classification and its replay commands are described in [the certificate guide](verification.md).

## Necessary conditions on a pair of caps

Suppose $A,B$ are caps and $R=V\setminus(\{0\}\cup A\cup B)$ has a proper three-coloring. Put $n(t)=|B\cap(A+t)|$. For any $t$, the sum of two distinct elements of $B\cap(A+t)$ lies in $R$. Coloring the edges of the complete graph on $B\cap(A+t)$ by the colors of these sums cannot produce a monochromatic triangle, since its three sums form a line. Thus $n(t)\le16$. Indeed in a three-colored $K_{17}$ at least six edges incident to one vertex have the same color. The neighbor $K_6$ either has an edge of that color, giving a triangle through the vertex, or is two-colored and has a monochromatic triangle.

For $t\in A$, the $|A|-1$ elements of $(A+t)\setminus\{0\}$ avoid $A$. At most $n(t)$ lie in $B$. In each color class $T$ of $R$, the elements of $(A+t)\cap T$ have pair sums avoiding $A$ and $T$. Color the edges by the remaining two colors and $B$. The same triangle argument gives size at most 16 per color. Thus $n(t)\ge |A|-49$ for $t\in A$, and symmetrically $n(t)\ge |B|-49$ for $t\in B$. We call these bounds and $n(t)\le16$ the root-count bounds.

The sets $A\setminus B,B\setminus A$ satisfy $(*)$, because either of $(A,B\setminus A)$, $(A\setminus B,B)$ can be combined with the three colors on $R$. This gives restrictions on which subspace intersections can be covered by $A\cap B$.

For every 4-dimensional subspace whose 15 nonzero points lie in $R$, all three colors occur five times. Six points of one color would give a two-colored $K_6$ on their sums and hence a monochromatic triangle. Form the incidence matrix $M$ of those 15-point sets. A color indicator $b$ has $Mb=2{\bf 1}$ over $\mathbb F_3$, and a vector $z$ encoding colors $0,1,2$ has $Mz=0$. These conditions support inconsistency witnesses, kernel enumeration, forced monochromatic lines and DRAT proofs on exact kernel colorings.

## Reduction to an $A_{58}$ color

The following pair exclusions certify that $R$ cannot be three-colored for representatives of the indicated types with the indicated maximum intersection. Counts refer to representatives after necessary-condition filtering.

| Pair | Intersection at most | Representatives |
| --- | ---: | ---: |
| $A_{51b},A_{51b}$ | 0 | 106 |
| $A_{51b},A_{53b}$ | 0 | 71 |
| $A_{51b},A_{53a}$ | 0 | 160 |
| $A_{51b},A_{51a}$ | 0 | 16,902 |
| $A_{51a},A_{53b}$ | 0 | 4,184 |
| $A_{53b},A_{53b}$ | 2 | 4,572 |
| $A_{53a},A_{53b}$ | 2 | 28,445 |
| $A_{51a},A_{53a}$ | 0 | 26,923 |
| $A_{51a},A_{51a}$ | 0 | 1,553,693 |
| $A_{53a},A_{53a}$ | 2 | 174,088 |

The ten pair cases require distinct finite certificates. See [the certificate guide](verification.md) for the replay tasks and certificate types.

For a hypothetical five-coloring, enlarge a largest color class by recoloring points until it is a complete cap. It has at least 51 points, and hence 51, 53 or 58 by classification. If it has 51 points, all five colors originally had 51 points. Either one can be enlarged to 53 or 58 points, or all were complete 51-caps and the disjoint 51-pair exclusions apply. Suppose a complete 53-point color $S$ is obtained. The largest of the remaining four colors has at least 51 points. Extend it to a complete cap $B$, allowing points of $S$. If $B$ has size 51 the pair is disjoint, and if $B$ has size 53 the pair intersects in at most two points. The other three colors restrict to the pair's complement. Both cases are excluded. In the remaining case $B$ has size 58 and can be made a color by recoloring. Therefore some hypothetical coloring has $A_{58}$ as a color, up to a linear change of coordinates.

## Pairs with an $A_{58}$ color

For $A=A_{58}$, pair exclusions also cover $B=A_{51a},A_{51b},A_{53a},A_{53b},A_{58}$ with intersection sizes at most $1,1,3,3,8$, respectively. The [certificate guide](verification.md) describes the finite checks. In the last case the finite search covers distinct periods. The following argument deals with a common period.

Suppose $A$ and $B$ are both of type $A_{58}$ and share a nonzero period $p$. Their intersection is a union of pairs $\{x,x+p\}$. For each of the 28 period pairs of $A$ with low seven-bit weight 5 or 6, the six-space check exhibits a 6-space intersecting $A$ in exactly that pair. Since $A\setminus B$ meets every 6-space, none of these pairs can lie in $B$. The same holds with $A$ and $B$ interchanged. The checked minimum-intersection bound for two caps of this type is two, so their intersection is the special pair that remains in each cap.

In the quotient by $p$, write $s=127$, $D=\{x:\operatorname{wt}(x)\ge5\}$ and $Q_0=\{x:\operatorname{wt}(x)\in\{1,2\}\}$. The quotient caps are $D$ and $L(D)$ for an invertible $L$ induced by a linear map carrying $A$ to $B$. This map carries the special pair of $A$ to the special pair of $B$, since the other pairs are identified by their six-space witnesses. The common special pair projects to $s$, so $L(s)=s$ and $D\cap L(D)=\{s\}$. Since $D=s+(\{0\}\cup Q_0)$, we have $Q_0\cap L(Q_0)=\varnothing$. The 28 differences of pairs of words in $\{0,L(e_1),\ldots,L(e_7)\}$ are the distinct elements of $L(Q_0)$. Their weights are 3 through 6 because they avoid $Q_0$, $0$, and $s$.

Append an even-parity bit to each of the eight words. Their pairwise distances are 4 or 6, and their XOR is the all-ones word since $\sum_i L(e_i)=s$. Thus each coordinate contains an odd number $k$ of ones and contributes $k(8-k)\le 15$ to the total of the 28 distances. With $h$ distances equal to 6, this gives $112+2h\le120$, hence $h\le4$. The quotient intersection $L(D)\cap(D+s)$ consists of those $s+y$ with $y\in L(Q_0)$ of weight 5 or 6. These are precisely the $h$ differences with extended distance 6, and each gives two points of $B\cap(A+s)$. Hence $n(s)=2h\le8$, contradicting $n(s)\ge9$ since $s\in A$.

Among the 197 points outside a color $A=A_{58}$, the largest color has size at least 50. Its extension $B$ to a complete cap meets $A$ in at most $|B|-50$ points, so every size above 50 is excluded by the pair checks. Thus the color already is a complete cap of type $A_{50}$, disjoint from $A$. The same reasoning excludes any other color of size above 50, and therefore each of the four non-$A$ colors has between 47 and 50 points.

## Final exclusion

Suppose $A=A_{58}$ and $B$ is a disjoint linear image of $A_{50}$. Their unique nonzero periods are $p=128$ and $q$. If $p=q$, the point $p$ belongs to a color $T$ of the complement. Every $x\in T\setminus\{p\}$ has $p+x$ in the other two colors because translation by $p$ preserves the two removed caps. Each target-color intersection has at most 16 points by the three-color triangle bound above, with $A,B$ and the third residual color as available colors for pair sums. This gives $ |T|\le33<47$.

For $p\ne q$, the root counts require $9\le n(t)\le16$ for $t\in A$ and $n(t)\ge1$ for $t\in B$. Since $n(p)=n(q)=0$, $p\notin B$ and $q\notin A$. Appending an even-parity bit identifies the quotient by $p$ with the even-weight space in eight coordinates. Permuting these coordinates preserves the image of $A$, which consists of all words of weights 6 and 8. The image of $q$ is nonzero and has weight 2 or 4, giving representatives 1 and 7 in seven-bit notation. A shear fixes the remaining $p$ component of the representative. Writing $B=L(A_{50})$, a shear removes the 128 component of $L^{-1}p$. The remaining point lies outside $E\cup\{0\}$. An explicit subgroup of order 1,152 preserving $E$ yields five orbit representatives, $3,7,9,11,27$, checked by the certificate. These choices give ten cases.

In the quotient $U=V/\langle p,q\rangle$, write the counts of $A,B$ over $u\in U$ as $2a(u),2b(u)$. A fiber is four points. Each $p$-line in it meets each $q$-line once. Disjointness is therefore equivalent to disjoint supports of $a,b$, and
$$
|B\cap(A+t)|=\sum_{u\in U} a(u+t)b(u),
$$
with the shift projected to $U$. The value depends only on the induced quotient map, so excluding that map excludes all its lifts. Enumerate each ordered basis image of the 6-dimensional quotient by choosing outside the span of previous basis images. A branch is stopped only when a determined support image violates disjointness. This yields 172,800 and 6,912 disjoint quotient maps in the two cases with source representative 3, and zero in the other eight cases. Each of the 179,712 maps violates the root-count bound for some $t\in A$. A second implementation regenerates the complete list by scalar DFS, with a different source basis, and checks each map by reconstructing a linear map of $V$ and explicitly counting on its image. This contradicts a five-coloring.

## Six colors

Partition the nonzero four-bit words into three caps
$$
\{1,2,4,8,15\},\quad\{3,6,7,12,14\},\quad\{5,9,10,11,13\}
$$
and let $g$ give their labels $1,2,3$. Write $v=16u+w$. Use color $g(u)$ for $u\ne0$, and $3+g(w)$ for $u=0$. For two points of the same color with nonzero high parts, either the high parts coincide and their sum has zero high part, or the cap condition on the high parts excludes the same color for their sum. The low-part colors are caps by construction. The code checks all 10,795 lines directly as well. Thus the chromatic number is six.
