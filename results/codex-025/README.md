# Two induced-C12-saturated graphs on 24 vertices

**Theorem.** There exist two $C_{12}$-induced-saturated graphs on 24 vertices, with 45 and 56 edges respectively. A graph is $C_{12}$-induced-saturated if it contains no induced $C_{12}$ and changing the adjacency of any single pair produces one. This gives existence on 24 vertices, improving the cited 25-vertex construction.

## The graphs

For the 45-edge graph use $A_i,B_i,C_i,D_i$ with indices modulo six. Its edges are exactly $A_iB_{i+3}$, $A_iC_{i\pm1}$, $A_iD_{i+3}$, $B_iD_{i+d}$ for $d\in\{2,3,5\}$, and the three edges $C_iC_{i+3}$ for $0\le i<3$.

For the 56-edge graph use $a_i,b_i,c_i,d_i,e_i,f_i$ with indices modulo four. The $a$ vertices and $b$ vertices each form a $K_4$. For each $i$ add exactly the remaining edges
$$
c_id_i,\ b_ic_i,\ b_id_i,\ a_ic_i,\ a_{i-1}c_i,\ a_id_i,\ a_{i+1}d_i,\
c_ie_i,\ d_if_i,\ e_if_{i+1},\ e_if_{i+2}.
$$

## Exact finite proof

A 12-vertex induced graph is a $C_{12}$ exactly when it is connected and every vertex has degree two. Exhaust all $\binom{24}{12}=2{,}704{,}156$ sets in each graph. In the 45-edge graph the only 2-regular induced subgraphs on 12 vertices are 24 of type $C_5\sqcup C_7$ and six of type $C_6\sqcup C_6$. In the other graph there are four of type $C_6\sqcup C_6$. Thus neither contains an induced $C_{12}$.

Any newly created cycle must contain both endpoints of the toggled pair. Before adding a nonedge the endpoints must both have degree one in the subgraph induced by its witness set, and before deleting an edge they must both have degree three. All other degrees must already be two. At each visited set, check the relevant pair and test connectivity after the toggle. Record the pair when the test succeeds. Exhausting the sets this way finds a witness for each of the 276 pairs in each graph, namely 45 deletions and 231 additions for the first and 56 deletions and 220 additions for the second. The degree filters are necessary conditions, and the connectivity test on a 2-regular graph certifies each witness.

Run `python3 verify-45.py` and `python3 verify-56.py` with Python 3.10 or later. The scripts rebuild the graphs from the formulas and check the absence and toggle claims by enumeration. [Choi's existence theorem](https://arxiv.org/abs/2608.24202) · [Previously published 25-vertex construction](https://github.com/Twilight-Dream-Of-Magic/c12-induced-saturation)
