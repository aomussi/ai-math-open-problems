# Uniqueness of the equilibrium of three noncollinear charges with zero total charge

**Theorem.** Let $a_1,a_2,a_3$ be noncollinear points in $\mathbb R^3$, and let the nonzero real charges $q_i$ sum to zero. Then the function $V(x)=\sum_i q_i/\|x-a_i\|$ has exactly one critical point away from the charges.

Normalize the charges to $(t,1-t,-1)$, where $0<t<1$, by permuting them and multiplying by a common nonzero constant. Write $P$ for their affine plane. At a critical point, put $c_i=q_i/\|x-a_i\|^3$ and $s=\sum_i c_i$. The critical-point equation gives $sx=\sum_i c_i a_i$. If $s=0$, affine independence implies $c_i=0$ for every $i$. Thus $s\ne0$ and $x\in P$. Conversely the normal component of $\nabla V$ vanishes on $P$, so we count zeros of $F=\nabla_P V$.

## The local index is minus one

At a critical point set $u_i=x-a_i$ and $v_i=u_i/\|u_i\|^3$. Then $v_3=tv_1+(1-t)v_2$. The map $u\mapsto u/\|u\|^3$ is injective with inverse $v\mapsto v/\|v\|^{3/2}$, so $v_1\ne v_2$. Their line avoids the origin, since otherwise the $u_i$ and hence the $a_i$ would be collinear. In orthonormal coordinates write $v_i=(s_i,h)$ with $h>0$ and $s_3=ts_1+(1-t)s_2$.

The Hessian of $1/\|u\|$ on $P$ is $3uu^{\mathsf T}/\|u\|^5-I/\|u\|^3$. In terms of $v=(s,h)$ its diagonal entries are
$$
f_h(s)=\frac{2s^2-h^2}{(s^2+h^2)^{1/4}},\qquad
g_h(s)=\frac{2h^2-s^2}{(s^2+h^2)^{1/4}}.
$$
Direct differentiation gives
$$
f_h''(s)=\frac{3(2s^4+3h^2s^2+6h^4)}{4(s^2+h^2)^{9/4}}>0,\qquad
g_h''(s)=-\frac{3(s^4+4h^4)}{4(s^2+h^2)^{9/4}}<0.
$$
At an equilibrium, $D F=tH(v_1)+(1-t)H(v_2)-H(v_3)$, where $H$ is the planar Hessian of the unit-charge potential expressed in the $v$ coordinates. Strict Jensen inequalities give $DF_{11}>0>DF_{22}$. Its symmetry implies $\det D F<0$. Each zero is isolated and has index $-1$.

## Finiteness and the total index

Uniformly on a small circle about $a_i$, $F(a_i+\epsilon\omega)=-q_i\omega/\epsilon^2+O(1)$. There are no zeros sufficiently close to a charge, and the direction field has winding number $+1$ around each charge.

Let $p=\sum_i q_i a_i$. Noncollinearity gives $p\ne0$. On a large circle the expansion, uniformly for $\|\omega\|=1$, is
$$
F(R\omega)=R^{-3}(p-3(p\cdot\omega)\omega)+O(R^{-4}).
$$
The leading vector has squared norm $\|p\|^2+3(p\cdot\omega)^2$, so all zeros lie in a compact set away from the charges. Since the zero set is closed there and each zero is isolated, it is finite. In positively oriented orthonormal coordinates with $p=(\|p\|,0)$ and $\omega=(\cos\theta,\sin\theta)$, the leading vector divided by $\|p\|$ is $-\tfrac12-\tfrac32e^{2i\theta}$. It winds twice around zero. Hence the winding number on the outer circle is $+2$.

Remove small disks around the three charges and all zeros from a large disk. The sum of the winding numbers on its oriented boundaries is zero, since the direction field extends throughout the remaining region. Counting each component counterclockwise, the outer winding is therefore the sum of the inner windings. If there are $N$ zeros this gives $2=3-N$, proving $N=1$.

For three noncollinear nonzero charges of total charge zero, the uniqueness theorem excludes the possibility of three equilibria raised by Kintali. [Kintali, Proposition 9.1 and Remark 9.3](https://shivakintali.github.io/Shiva-Kintali-Maxwell3.pdf#page=32) · [Enciso and Peralta-Salas, related finiteness theorem](https://arxiv.org/html/2609.03965v1)
