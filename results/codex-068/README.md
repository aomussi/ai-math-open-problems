# A polynomial-time algorithm for 2-annihilation games

On a finite directed graph, a legal move chooses a vertex $i$ with a token, removes it, and toggles exactly $\min(2,d_i)$ distinct out-neighbors, where $d_i$ is its out-degree. A sink permits removing its token without any toggles, so the empty position is the only terminal one. If a self-loop is selected, the token at the starting vertex reappears. Play is normal, and infinite play is a draw. The win, loss, or draw of an explicit position is computable in $O(n^{14})$ bit operations. The same argument covers move lists with polynomially many types, each gated by an occupied coordinate, with at least one type per vertex. [Nowakowski, Problem D4](https://library.slmath.org/books/Book71/files/GONC6-04.pdf)

Fraenkel and Yesha gave a polynomial-time outcome algorithm for the classical game in which a move sends a token to a single neighbor and annihilates a pair when the target is occupied. [Theory of annihilation games—I](https://doi.org/10.1016/0095-8956(82)90058-2)

## The invariant

Work over $V=\mathbb F_2^n$ with a list $M$ of moves $(i,m)$ taking $x$ to $x+m$ when $x_i=1$. There are $T=O(n^3)$ such moves. Let $N(L)$ be the one-move predecessors of a subspace $L$, $C(L)$ the positions with every legal successor in $N(L)$, and $Z=N(\{0\})=\{m:(i,m)\in M,\ m_i=1\}$.

Maintain an ordered basis $b_0,\ldots,b_{d-1}$ of $L$ with two properties. First, for every $p\in L$ and every legal move from $p$, a reply reaches a point in $L$ with strictly smaller rank $\rho(\sum_j a_jb_j)=\sum_j a_j2^j$. Second, $N(L)=Z+L$. These hold at $L=\{0\}$. The rank establishes finite loss for every position in $L$, and $N(L)$ consists of finite wins because each position in it can move into $L$. In particular $L\cap N(L)=\varnothing$ at every stage.

## Extension

For any $b\in C(L)\setminus L$, put $L'=L+\langle b\rangle$ with $b$ last in the basis. Write $N=N(L)$. We have $N(L')=N\cup(b+N)$. For $y\in N$ with move $(i,m)$ to $p\in L$, if $b_i=0$ then $y+b$ can make the same move to $L'$. If $b_i=1$, then $b+m\in N$ and $y+b=p+(b+m)\in N$ by translation invariance under $L$. Conversely, if a move takes $y$ to $b+p$ for $p\in L$, its gate either has $b_i=0$, so $y+b$ moves to $p$, or $b_i=1$, so $y=p+(b+m)\in N$. This proves the second invariant for $L'$.

For rank descent at $b+p$, let $(i,a)$ be the opponent's move. If $b_i=1$, the resulting position lies in $p+N=N$ and the reply returns to $L$. If $b_i=0$, then $p_i=1$ and the opponent’s move is legal at $p$. The old reply $(j,c)$ to $p+a$ would lead to $p'\in L$ of lower old rank. If that reply is legal at $b+p+a$, it reaches $b+p'$ and decreases rank. Otherwise $b_j=1$, so $b+c\in N$ and $b+p+a=(b+c)+p'\in N$, allowing a reply into $L$. Ranks there are smaller than any rank in $b+L$, establishing the first invariant.

## Search and the classification

Compute a linear remainder map $r$ modulo $L$ by Gaussian elimination and set $A=r(Z)$. A nonzero position has a move. Therefore any $x\in C(L)\setminus L$ has remainder $c=r(m)+r(z)\ne0$ for some move mask $m$ and $z\in Z$. There are at most $T^2$ candidates. For each $c$, impose $x_i=0$ whenever some move $(i,m)$ has $c+r(m)\notin A$, and $r(x)=c$. This linear system is exactly the requirement that all legal successors belong to $N$. A solution gives the next basis vector. After at most $n$ extensions no candidate remains, and $C(L)=L$ by the invariant. The losing and winning sets are $L$ and $Z+L$. In the complement every position has a successor in the complement and no successor in $L$. Both players can stay there, which gives the draw set.

For each round and candidate, constructing the forbidden coordinate set by simple list scans costs $O(T^2n)$, and solving the system costs $O(n^3)$. There are $O(nT^2)$ candidate visits. With $T=O(n^3)$ the bound follows.

Run `python3 verify.py` to compare the algorithm with full retrograde analysis on every directed graph on at most four vertices, including graphs with self-loops. It also checks every required rank-decreasing reply in those cases. The proof establishes the general result.
