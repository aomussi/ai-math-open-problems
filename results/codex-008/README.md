# A positive preperiod for a family of three-move subtraction games

**Theorem.** Let $2\le a<b<2a$, $b<c$, and put $r=c\bmod(a+b)$. For the normal-play subtraction game with moves $a,b,c$, if $0<r<b-a$, the Grundy preperiod is at least $c-a-r>0$. The preperiod is the least index from which the sequence is periodic. For primitive triples, this proves the necessity direction of Manabe’s Conjecture 52 throughout the stated range.

Put $m=a+b$, $d=b-a$, and write $c=qm+r$. We have $q\ge1$ because $c>b>r$. Write $z(n)=1$ exactly when the Grundy value is zero. Any periodic tail of the Grundy sequence gives a periodic tail of $z$ from the same index. For $n\ge c$ the indicator satisfies the NOR recurrence
$$
z(n)=(1-z(n-a))(1-z(n-b))(1-z(n-c)).
$$
We first establish that any periodic binary sequence on $\mathbb Z$ satisfying this recurrence also satisfies the reverse recurrence, obtained by replacing the three minus signs in the arguments with plus signs.

## The reverse recurrence

For a position $n$ use the following array of values, with row and column offsets added to $n$.

| Offset | $0$ | $c$ | $b$ | $b+c$ |
| --- | --- | --- | --- | --- |
| $0$ | $A$ | $B$ | $C$ | $D$ |
| $a$ | $E$ | $F$ | $G$ | $H$ |
| $2a$ | $I$ | $J$ | $K$ | $L$ |

Pairs at a legal move distance cannot both be one. The checker uses the pairs $AB,AC,BD,CD$ and the corresponding four in each remaining row, together with the eight vertically adjacent pairs. It imposes the two recurrence equations $H=(1-D)(1-F)(1-G)$ and $L=(1-H)(1-J)(1-K)$. Coincident cells and further move relations at particular parameter values only add constraints to these checks. Put $\eta=(1-A)(1-B)(1-C)(1-E)$. The three polynomials, with subscripts starting at zero, are
$$
\begin{aligned}
\phi(u)&=u_0+u_1+3u_2+u_7+u_0u_3+u_4(u_7-u_1-u_2)-2u_1u_2(1-u_4),\\
\psi(v)&=2v_1+2v_3+v_0(v_3+v_4)-v_1(v_2+v_5-v_2v_5),\\
\omega(w)&=3w_2+w_3(1+w_0)-w_1w_2(1-w_5).
\end{aligned}
$$
The [included program](verify.py) checks the following exact local inequality on all binary assignments with those constraints.
$$
\begin{aligned}
&\phi(A,B,C,D,E,F,G,H)-\phi(E,F,G,H,I,J,K,L)\\
&+\psi(A,B,E,F,I,J)-\psi(C,D,G,H,K,L)\\
&+\omega(A,C,E,G,I,K)-\omega(B,D,F,H,J,L)\le -2\eta.
\end{aligned}
$$
There are $2^{12}$ assignments and 93 pass the constraints. Each of the three differences is a difference of translates of one local function, shifted by $a,b,c$ respectively. Summing over a period therefore gives $0\le-2\sum_n\eta(n)$, and hence $\eta(n)=0$ throughout. If $z(n)=0$ there is a one among the three successors. If $z(n)=1$ all three successors are zero by the original recurrence. This proves the reverse recurrence.

## The initial blocks

For $0\le n<c$, one has $z(n)=U(n\bmod m)$, with $U=1_{[0,a)}$. Indeed residues in $[a,2a)$ can subtract $a$, residues in $[2a,m)$ can subtract $b$, and all legal moves from $[0,a)$ leave that set modulo $m$.

Put $R=[a,b-r)\cup[b,2a)\cup[m-r,m)$ and $W=1_R$. Then $z(c+x)=W(x\bmod m)$ for $0\le x<c$. To see this, the translates on the cycle are
$$
R+a=[2a,m-r)\cup[0,2a-b)\cup[a-r,a),\quad
R+b=[0,d-r)\cup[d,a)\cup[b-r,b).
$$
Together with $[0,a)$ they cover the complement of $R$ and are disjoint from $R$. This is the NOR rule for $W(x)$ with predecessors $W(x-a),W(x-b),U(x)$. At $x<a$ the move $c$ already goes to a zero Grundy value. For $a\le x<b$, the move $a$ reaches $c+(x-a)$ with $0\le x-a<b-a<a$, where $z=0$. The move $c$ reaches $x$, where $z(x)=U(x)=0$. The move $b$ reaches a position with $z=1$ exactly when $x\ge b-r$. For $x\ge b$ use the translated rule and induction.

For $h=(q-1)m+b-1$, all four values $z(h),z(h+a),z(h+b),z(h+c)$ are zero. The first two occur before $c$ at residues $b-1,m-1$. The third has offset $d-r-1$ after $c$, in $[0,a)$, and the fourth has offset of residue $b-1\in[b-r,b)$. A periodic tail starting at or before $h$ extends to a periodic sequence on $\mathbb Z$ satisfying the forward recurrence everywhere, by translating each equation far enough into the tail. Its reverse recurrence contradicts these four zero values. Since the Grundy sequence is eventually periodic by the finite-state mex recurrence, the claimed bound follows from $h+1=c-a-r$.

Run `python3 verify.py`. The checker passed all 93 admissible assignments. It imposes no bounds on game parameters or periods. [Manabe, Conjecture 52](https://arxiv.org/html/2609.05358v2#S6) · [Related additive case](https://arxiv.org/abs/2603.10414)
