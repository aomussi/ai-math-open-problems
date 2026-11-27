# A five-column difference covering modulo 26 with the minimum number of rows

**Theorem.** The smallest number of rows of a five-column array over $\mathbb Z/26\mathbb Z$ for which the rowwise differences of every column pair cover the group is 27.

For a pair $i<j$ the differences are $A_{r,j}-A_{r,i}$ as $r$ ranges over the rows. Fewer than 26 values cannot cover the group. At 26 rows every pair must give every residue once. If $s_i$ is the sum in column $i$, then $s_j-s_i=13$ modulo 26 for every $i<j$, since $\sum_{d=0}^{25}d=325$. Adding this congruence for $(1,2)$ and $(2,3)$ yields $s_3-s_1=0$, contradicting the congruence for $(1,3)$.

The 27-row witness is given below and in [the verifier](verify.py). For each of the ten column pairs the program forms the 27 differences and counts them. Every residue occurs once except 13, which occurs twice. This finite calculation proves the upper bound directly.

The array was found with the symmetry $A=(0,a,p,Up,U^2p)$, where $(Uf)_r=9f_{T(r)}$ and $T=(1\,2\,3)(4\,5\,6)\cdots(22\,23\,24)$ fixes rows 25 through 27 in one-based indexing. Here $Ua=a$ and $U^3=1$. Multiplication by 9 and negation permute the residue classes and fix 13, so they preserve the target multiset. Consequently it is enough in a search to impose the target multiset on $a,p,p-a,Up-p$. The supplied witness is checked directly and does not depend on the completeness of the search.

Run `python3 verify.py`. All ten column pairs passed during publication preparation. The published lower and upper bounds were 27 and 28. The displayed 27-row construction meets the lower bound. [Castoldi et al., Theorem 29(ii)](https://doi.org/10.1002/jcd.70037)

## Witness

The rows of A are listed below.

```text
 0  1 24 14  7
 0  3 16 21 20
 0  9 11  8 22
 0  2  2  9 25
 0  6  1 23  6
 0 18 17 18  3
 0  4 18 13 18
 0 12 13  2  2
 0 10  6  6 13
 0  5  8  7 10
 0 15 21  4 24
 0 19 12 20 11
 0  7 20 11  0
 0 21  7  0  8
 0 11  0 24 21
 0  8 25  3 16
 0 24  9 22 23
 0 20 14 17  1
 0 14 19 25 12
 0 16 23 10  5
 0 22  4 15 17
 0 17 15  1 13
 0 25  3 13 19
 0 23 13  5  9
 0  0 10 12  4
 0 13  5 19 15
 0 13 22 16 14
```
