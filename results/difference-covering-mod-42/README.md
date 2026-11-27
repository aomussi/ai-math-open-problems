# A five-column difference covering modulo 42 with the minimum number of rows

**Theorem.** The smallest number of rows of a five-column array over $\mathbb Z/42\mathbb Z$ for which rowwise differences in every column pair cover the group is 43.

At least 42 rows are needed by counting. At 42 rows every pair gives each residue exactly once, so for the column sums $s_i$ one would have $s_j-s_i=861=21$ modulo 42 for every $i<j$. The equations for pairs $(1,2)$ and $(2,3)$ contradict the equation for $(1,3)$. Thus at least 43 rows are required.

The witness is the vertical concatenation of $F,B,13B$ modulo 42, with five rows in $F$ and nineteen in $B$. The first column is zero. The two seed arrays are printed below and included in [the verifier](verify.py).

Multiplication by 13 is an involution modulo 42 with fixed set $H=\{0,7,14,21,28,35\}$ and eighteen two-element orbits. For each pair of columns, the nineteen differences in $B$ consist of 21 and exactly one element of each two-element orbit. The corresponding differences in $B$ and $13B$ therefore cover every residue outside $H$ once and 21 twice. The differences in $F$ are $H\setminus\{21\}$ for every pair. This gives the upper bound.

Run `python3 verify.py`. All ten pairs passed an exact count during publication preparation. The published lower and upper bounds were 43 and 44. The displayed construction meets the lower bound. [Castoldi et al., Theorem 29(i)](https://doi.org/10.1002/jcd.70037)

## Witness

The rows of F are listed below.

```text
 0  0  7 14 14
 0  7 35  7 35
 0 14 14  0  7
 0 28  0 35 28
 0 35 28 28  0
```

The rows of B are listed below.

```text
 0  6  4 10  8
 0 12 34 29  9
 0 18 31 20 30
 0  1 21 37 22
 0 19 15 11 23
 0 25 13 34 16
 0  8 37 38 39
 0  2 20 23 25
 0 32 23 33 38
 0 15 36  2 10
 0  9 24  6  1
 0  3 29 40 19
 0 22 39 27 21
 0 16 26 31  6
 0  4  9 24 15
 0 29 32 12 11
 0  5 30 21 18
 0 11 17  1 26
 0 21 16  3 41
```
