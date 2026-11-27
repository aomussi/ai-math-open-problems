# Three points with a nonclosed geodesic convex hull

Let $T$ be the metric tripod with three rays $A,B,C$ meeting at $o$, and let $D(r)$ denote radius $r$ on ray $D$. The space $X=T^3$ with its Euclidean product metric is the CAT(0) orthant space of the flag complex whose simplices choose at most one vertex from each of three groups of three vertices. It has 27 maximal three-dimensional orthants. Write $[x,y]_t$ for the point a fraction $t$ along the unique geodesic from $x$ to $y$. Interpolation is coordinatewise with this common parameter.

**Theorem.** The three points
$$
a=(A(2),A(1),A(1)),\qquad b=(B(1),B(2),B(1)),\qquad
c=(C(1),C(1),C(2))
$$
have a geodesic convex hull $H$ that is not closed. In fact $O=(o,o,o)\in\overline H\setminus H$. This supplies a counterexample to the closedness question for orthant spaces. [Lin, Sturmfels, Tang and Yoshida, Problem 8 in the authors' preprint](https://arxiv.org/html/1510.08797#S3)

Put $S_0=\{a,b,c\}$ and let $S_{j+1}$ be the union of all geodesic segments joining pairs in $S_j$. These sets are increasing and their union is exactly $H$.

For rays $D$ and $E$ with $E\ne D$, define $h_D(D(r))=r$ and $h_D(E(r))=-r$, with $h_D(o)=0$. This function is affine along a geodesic when the endpoints share a ray or one lies on $D$. Along a geodesic between the other two rays, with endpoint radii $r,s$, it is $-|(1-t)r-ts|$. Thus $F(x)=h_A(x_1)+h_B(x_2)+h_C(x_3)$ is geodesically concave.

At $a,b,c$, $F$ is zero. Between any two different initial points its value is $1-|1-2t|>0$ for $0<t<1$. For $a,b$ the individual terms are $2-3t,-1+3t,-|1-2t|$, and cyclic permutation gives the other pairs. By induction, $F\ge0$ on each $S_j$ and $F=0$ there only at the three initial points. For an interior interpolation, concavity makes $F$ positive if either endpoint is positive. If both endpoints have zero value, use the preceding pairwise computation or the fact that the endpoints coincide. As $F(O)=0$, this excludes $O$ from all the $S_j$.

Take $u_1,u_2,\dots=a,b,c,a,b,c,\dots$, and let $z_1=a$, $z_{m+1}=[z_m,u_{m+1}]_{1/(m+1)}$. Then $z_m\in S_{m-1}$. For $w_m=mz_m$ (radial scaling in each coordinate), the update adds the radii for equal rays and subtracts them for unequal rays, keeping the larger ray. We have $w_2=(A(1),B(1),o)$, and thereafter it follows a cycle.
$$
(o,o,C(2))\xrightarrow{a}(A(2),A(1),C(1))
\xrightarrow{b}(A(1),B(1),o)\xrightarrow{c}(o,o,C(2)).
$$
Thus $z_{3k}\in S_{3k-1}$ and $d(z_{3k},O)=2/(3k)$. This proves the assertion. Each finite stage is compact by continuity of interpolation, so the stages in this example also do not stabilize.

[Lin, Sturmfels, Tang and Yoshida, Convexity in Tree Spaces](https://doi.org/10.1137/16M1079841) · [Authors' preprint](https://arxiv.org/abs/1510.08797)
