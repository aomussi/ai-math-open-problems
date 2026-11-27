# A Butson Hadamard matrix BH(46, 6)

**Theorem.** There is a $46\times46$ matrix $H$ of sixth roots of unity with $HH^*=46I_{46}$, where $H^*$ is the conjugate transpose.

Let $\zeta=e^{\pi i/3}$, and take the following two length-23 exponent sequences.
```text
04440242440220442420444
05311151353333531511135
```
Writing these sequences as $a$ and $b$, put $X_{ij}=\zeta^{a_{j-i}}$ and $Y_{ij}=\zeta^{b_{j-i}}$, with indices modulo 23. Use the block matrix
$$
H=\begin{pmatrix}X&Y\\Y^*&-X^*\end{pmatrix}.
$$
The sixth roots are closed under conjugation and multiplication by $-1=\zeta^3$.

For a nonzero shift $s$, count the difference exponents $a_j-a_{j+s}$ and $b_j-b_{j+s}$ modulo six. In order of residue $0,\dots,5$, the counts are as follows.

| Shifts modulo 23 | Combined counts |
| --- | --- |
| $\pm\{1,3,4,5,6,7,9\}$ | $(14,1,15,0,15,1)$ |
| $\pm\{2,8,10,11\}$ | $(16,0,14,2,14,0)$ |

The $(i,i+s)$ entry of $XX^*$ is $\sum_j\zeta^{a_{j+s}-a_j}$ after a cyclic change of index. This is the complex conjugate of the sum used in the table, and the same holds for $YY^*$. Using $\zeta+\zeta^5=1$, $\zeta^2+\zeta^4=-1$ and $\zeta^3=-1$, each table row gives a weighted sum of the powers $\zeta^r$ equal to zero. At $s=0$, the sum is 46. Thus $XX^*+YY^*=46I_{23}$. All four circulants $X,Y,X^*,Y^*$ commute, so block multiplication gives $HH^*=46I_{46}$.

Run `python3 verify.py`. The [integer-arithmetic verifier](verify.py) checks all 22 shifts and all 2,116 entries of the Gram matrix in the basis $(1,\zeta)$, using $\zeta^2=\zeta-1$. Both checks passed locally. The cited survey lists order 46 among the undecided cases for sixth roots of unity. [Problem 9 and known orders](https://arxiv.org/html/2610.27175#S5) · [Related block construction](https://arxiv.org/html/2511.11230v1)
