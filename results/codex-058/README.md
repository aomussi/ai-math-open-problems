# A counterexample to the proposed algebraic boundary of ternary quartic rank

Let $K$ be the Euclidean closure of the set of real ternary quartics of real Waring rank exactly six. The quartic
$$
f_0=-4x^3z+6x^2z^2+12xy^2z+y^4+z^4
$$
lies on $\partial K$ and avoids the catalecticant determinant $D$, usual discriminant $\Delta$, and Blekherman discriminant $B$. Near $f_0$ the catalecticant is invertible, so the six-term real decomposition locus $\mathcal R_4$ of the source paper is exactly the rank-six locus there. Since the boundary of a closure lies in the boundary of the original set, the projective class of $f_0$ disproves the proposed equality of the algebraic boundary with $V(D\Delta B)$. [Michałek, Moon, Sturmfels and Ventura, Conjecture 4.3](https://doi.org/10.1007/s10231-016-0606-3)

## Negative pairs and the boundary point

Use multinomial-normalized coefficients and index the middle catalecticant $C(f)$ by $x^2,y^2,z^2,xy,xz,yz$. For $\nu(p)=(x^2,y^2,z^2,xy,xz,yz)^T$ evaluated at $p$, put $A_f=C(f)^{-1}$, $Q_f(p)=\nu(p)^TA_f\nu(p)$, and $\beta_f(p,q)=\nu(p)^TA_f\nu(q)$ when $C(f)$ is invertible. A negative pair consists of distinct projective points $p,q$ with $Q_f(p),Q_f(q)<0$ and $\beta_f(p,q)=0$. If $C(f)$ has inertia $(4,2)$ and $f$ has rank six, a decomposition yields $C=V\operatorname{diag}(c_i)V^T$ with columns $\nu(p_i)$. Invertibility implies $V^T A_f V=\operatorname{diag}(1/c_i)$. Inertia forces two negative $c_i$, giving a negative pair.

For $f_0$, the catalecticant determinant is 1 and its quadratic form is
$$
(b+e)^2+(c+a)^2+e^2+\tfrac12(d+h)^2-(a+e)^2-\tfrac12(d-h)^2
$$
in coordinates $(a,b,c,d,e,h)$. The linear forms are independent, giving inertia $(4,2)$. Direct inversion gives
$$
Q_0=-2x^3z+2x^2y^2+x^2z^2+2xz^3+2y^4-2y^2z^2+z^4.
$$
For $L(s)=x+sy+(s^2-s^4)z$, the coefficient of $s^4$ in $L(s)^4$ is $f_0-z^4$. The centered fourth difference uses the five evaluations at $-2h,-h,0,h,2h$ with weights $1,-4,6,-4,1$. Dividing by $24h^4$ and adding $z^4$ gives a signed sum of six fourth powers for $h\ne0$, converging to $f_0$. Its catalecticant is invertible near $h=0$, ensuring rank exactly six. Hence $f_0\in K$.

On $x=0$, $Q_0=y^4+(y^2-z^2)^2>0$ projectively. At $x=1$ the expression is $2y^4+2(1-z^2)y^2+z^2(z+1)^2-2z$. It is positive for $-1\le z<0$. For $z<-1$, completing the $y^2$ square leaves $\tfrac12 z^2(z+2)^2-2z-\tfrac12>0$. At $z=0$ equality requires $y=0$. Thus $Q_0\le0$ implies $xz>0$ or $p=[1:0:0]$.

For affine points $p=(1,y,z),q=(1,v,w)$, set $a=y-v,\ b=z-w,\ m=(y+v)/2,\ n=(z+w)/2$, and $d=\nu(p)-\nu(q)$. Then $d^TA_0d=(a,b)H(m,n)(a,b)^T$, with
$$
H=\begin{pmatrix}8m^2+2n&-(4n+1)m\\-(4n+1)m&(2n+1)^2\end{pmatrix},
\quad
\det H=m^2(16n^2+24n+7)+2n(2n+1)^2.
$$
It is positive definite for $n>0$.

Take $f_t=f_0-ty^4$ for $0<t<1/2$, so $C_t=C_0-tee^T$ with $e$ the $y^2$ coordinate. The determinant is $1-2t$ and inertia remains $(4,2)$. The rank-one inverse update is $A_t=A_0+\frac{t}{1-2t}rr^T$, $r=(1,2,-1,0,-1,0)^T$. Thus $Q_t\ge Q_0$, and $Q_t(1,0,0)>0$. The projective sublevel set $Q_t\le0$ is a compact subset of $xz>0$. Suppose rank-six $g_j\to f_t$. Select the two negative points of each $g_j$ with $\beta_{g_j}=0$ and pass to a projectively convergent subsequence. Both limits lie in that compact set. In affine $x=1$ coordinates the pairs eventually belong to a rectangle $|y|\le M,\ 0<\delta\le z\le M$. On the rectangle $H$ has uniform positive lower eigenvalue and $\nu$ is Lipschitz. Therefore $d_j^T A_t d_j\ge k\|p_j-q_j\|^2$ with $k>0$, and replacing $A_t$ by $A_{g_j}$ changes the quadratic form by at most $o(1)\|p_j-q_j\|^2$. This forces $d_j^TA_{g_j}d_j>0$ for distinct points. The negative-pair properties yield $d_j^TA_{g_j}d_j=Q_{g_j}(p_j)+Q_{g_j}(q_j)<0$, a contradiction. Thus $f_t$ lies outside $K$ and tends to $f_0$, proving $f_0\in\partial K$.

## The three polynomials at $f_0$

We have $D(f_0)=1$. A complex singularity of $f_0$ cannot have $z=0$, since the $y,z$ partials would force $x=y=0$. In the chart $z=1$ the three gradient equations reduce to
$$
-x^2+x+y^2=0,\quad y(y^2+6x)=0,\quad -x^3+3x^2+3xy^2+1=0.
$$
For $y=0$ the first equation restricts $x$ to $0,1$. The third left side is $1,3$, respectively. For $y\ne0$ the first two force $x=-5,y^2=30$, and the final value is $-249$. Thus $\Delta(f_0)\ne0$.

The factorization $\operatorname{disc}(\nu^T\operatorname{adj}(C)\nu)=cD^{14}B$ with $c\ne0$ reduces the last check to smoothness of $Q_0$ over $\mathbb C$. On $x=0$ its $x,y$ partials exclude singularities. For $x=1,y=0$ the equations require $z(z^2+z-3)=0$ and $2z^3+3z^2+z-1=0$. The cubic is nonzero at $z=0$ and reduces to $6z+2$ modulo $z^2+z-3$. The only possible root $z=-1/3$ gives $z^2+z-3=-29/9$. For $x=1,y\ne0$, eliminate $y^2$ using $2y^2=z^2-1$. The equations are $z^3+2z^2-3z-1=0$ and $z^3+3z^2+2z-1=0$. Their difference forces $z=0,-5$, neither satisfying the first. Consequently $B(f_0)\ne0$. [Michałek et al., proof of Theorem 4.1, following (22)](https://arxiv.org/html/1601.06574#S4)
