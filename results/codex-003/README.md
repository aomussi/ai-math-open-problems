# No common transversal cell in the Ghafari–Wanless squares

For every even $n>10000$, let $L_n$ be $G_n$ when $n\equiv2\bmod4$ and $H_n$ when $n\equiv0\bmod4$, as defined in equations (3) and (7) of Ghafari and Wanless. We exhibit four transversals of $G_n$ and three of $H_n$ with no cell common to the exhibited transversals of each square. Ghafari and Wanless prove in Lemmas 7 and 8 that every pair of transversals shares a cell in these families. [Ghafari and Wanless, §3](https://arxiv.org/html/2607.17547#S3)

## Uniform checking

The [certificate](certificate/verify_all.py) represents coordinates and progression endpoints by affine functions of the order parameter in each residue case. The position indices within each progression are handled by interval checks. A linear inequality holds throughout the parameter half-line if its slope is nonnegative and its value at the left endpoint is nonnegative. The verifier also tests strict comparisons where needed. Reduction modulo $n$ is performed by certifying $0\le f-qn<n$ throughout, with $q$ an integer. For progressions of step $d$ in the column and symbol lists, split by residues modulo $d$ and map $a+dx$ to $x$. Within a residue, the intervals must be disjoint and cover everything from zero through $\lfloor(n-1-a)/d\rfloor$. Each assertion concerns the entire parameter range.

## The two $H_n$ families

For $n=8t+4$, $t\ge1250$, put $k=2t+1$. On row $4j+i$ use column $4j+\pi_i$ for each of $\pi=(0,1,3,2),(1,3,0,2),(2,3,1,0)$. The provisional symbol is $8j+i+\pi_i+2[i=3]\pmod n$, with the four constant terms in distinct residue classes modulo 4. Multiplication by 2 is invertible modulo $k$. The provisional families use every row, column and symbol exactly once. Outside the exceptional row set
$$
R=[0,27]\cup[4t-24,4t+27]\cup[8t-20,8t+3],
$$
the provisional symbols agree with (7). Each $\pi$ preserves the complete four-row blocks in $R$. The [104-row completion table](certificate/h_odd_certificate.json) permutes their columns, exactly replaces the missing symbols under (7), and has no row in which all three choices are equal. Outside $R$, the three choices are never all equal.

For $n=4k$, $k\ge2502$ even, set $m=k/2$ and use $d=0,1,2$. For $0\le v\le k-2$ let $x_d=(v+[v\ge m]+d)\bmod k$, $y_d=(v+x_d+1)\bmod k$. The images miss only $m+d$ and $d$, respectively. For $0\le i<4$ use rows $4v+3+i$, columns $4x_d+(0,2,3,1)_i$ and provisional symbols $4y_d+(1,2,4,3)_i$ modulo $n$. The complements are taken after excluding the rows $4v+3+i\bmod n$ for the 52 indices $v$ in
$$
[0,6],\quad[\lfloor k/4\rfloor-6,\lfloor k/4\rfloor+6],\quad
[k/2-6,k/2+6],\quad
[\lfloor3k/4\rfloor-6,\lfloor3k/4\rfloor+6],\quad[k-6,k-1].
$$
The index $v=k-1$ accounts for the four rows $n-1,0,1,2$ absent from the provisional construction. The regular symbols agree with (7). The [208-row tables](certificate/h_even_certificate.json) for $k\equiv0,2\bmod4$ fill the complements exactly and exclude a common cell. On regular rows the columns are distinct.

## The $G_n$ families

Write $m=2u+\epsilon$, $n=8m+38+4\eta$, $\epsilon,\eta\in\{0,1\}$, $u\ge622$. The four transversals are indexed by $h=0,2,4,6$. For $j\in[30,u-30]\cup[u+30,m-31]$ and $0\le\ell<8$, the regular cells are
$$
(r,c)=
\begin{cases}
(18+6j+\ell,\ 2(q+1)m+b+h-2j)&\ell<6,\\
(6m+18+3\eta+2j+\ell-6,\ 2qm+b+h+2j)&\ell\ge6 ,
\end{cases}
$$
with columns reduced modulo $n$. The pairs $(q,b)$ start with $(0,0),(2,1),(1,1),(3,0),(2,0),(0,3)$. The last two are $(3,3),(1,2)$ for $\eta=0$ and $(1,0),(3,3)$ for $\eta=1$. Equation (3) gives the symbol $r+c+2$ for $\ell=0,3$ and $r+c$ otherwise, reduced modulo $n$. Thus the regular columns and symbols are progressions of steps $\pm2$ and $4$.

The [completion tables](certificate/g_all_certificate.json) give affine columns on the remaining $990+4\eta$ rows. The verifier builds the row complement, verifies uniform coverage of the columns and recomputed symbols by the progressions and singleton completions, and checks that the four choices are never all equal on a completion row. On a regular row the shift $h$ makes the columns distinct. The four residue choices cover all $G_n$ in the stated range.

## Reproduction

Run `python3 verify_all.py` in `certificate/` with assertions enabled. It must print a PASS covering every even $n>10000$. The file [construct_transversals.py](certificate/construct_transversals.py) materializes the specified transversals for an individual order.
