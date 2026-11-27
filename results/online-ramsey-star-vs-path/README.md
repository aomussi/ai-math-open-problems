# The online Ramsey constant for a red four-leaf star versus a blue path

On an unlimited vertex set, Builder queries a previously unqueried pair of vertices each turn and Painter colors it red or blue. Let $r_n$ be the least number of queries with which Builder can guarantee a red $K_{1,4}$ or a blue path on $n$ vertices. For $n\ge2$,
$$
\left\lceil\frac{9n-8}{5}\right\rceil\le r_n\le
\left\lfloor\frac{9(n-1)}5\right\rfloor+27.
$$
Thus $\lim_{n\to\infty}r_n/n=9/5$. [Beilis, Curbelo and Koizumi](https://arxiv.org/abs/2608.27405)

## Painter's lower bound

Paint a query $uv$ blue if, before the query, an endpoint has red degree 3 or both endpoints have blue degree zero and positive red degree. Paint it red otherwise. There is no red four-leaf star. When a blue $P_n$ exists let $p=n-1$ and let $w$ be the number of other blue edges. Let $S$ be the set of vertices of final red degree 3 and $U$ the other vertices. Set $s=|S|$ and let $d$ be the sum of red degrees on $U$. Then $2R=3s+d$, with $R$ the red edge count. Let $A\subset S$ be the $a$ vertices that receive a blue edge before reaching red degree 3. The red graph on $S\setminus A$ is a forest since each red edge within it was added with at least one endpoint of red degree zero. Counting incidences on this forest gives $s\le4a+d-2$. If the forest is empty the same inequality follows from $2R\ge2$.

The blue edges queried when both blue degrees were zero and both red degrees positive form a matching $J$. Let $h$ count its $S$–$U$ edges. The first blue edge of each vertex in $A$ is either an $S$–$S$ edge or belongs to those $h$ edges. Thus $a\le2(x+w)+h$, where $x$ counts $S$–$S$ edges on the selected path. Let $y$ count $U$–$U$ edges there. They are in $J$, and disjointness of their endpoints from the $U$-endpoints counted by $h$ gives $d\ge h+2y$. The path has $p\le2s-x+y$ by counting degrees on $S$. Combining yields $s\le8x+8w+5d-8y-2$, hence $p\le5R/4+w-1/4$. Therefore the query count $p+w+R$ is at least $(9p+1)/5$.

## Builder's certified strategy

Maintain at most four disjoint blue paths, counting isolated vertices. A state records the path endpoints, path memberships, total red degrees of endpoints and all red edges between endpoints of distinct paths. Internal vertices never receive additional queries, and paths never split. Thus a missing recorded edge between distinct paths is unqueried. States are taken up to order and orientation of paths.

The actions are to add a new isolated vertex for zero cost, query an unqueried edge between endpoints of distinct paths, or join two red-degree-three endpoints through a fresh vertex using two queries. In the last action either red response wins immediately, while two blue responses join the paths. Let $c,\delta$ be the cost and increase in total managed vertices. The [strategy table](certificate/strategy.json) assigns an integer potential $\Phi\in[0,34]$, initialized at 0, with $5c-9\delta\le\Phi(q)-\Phi(q')$ for every nonterminal response. The [checker](certificate/verify.py) regenerates the legal actions and responses, verifies state equivalence, and tests this inequality on all 1,408 branches in the 1,063 reachable states.

Starting with one isolated vertex, telescoping gives $5T\le9(L-1)$ at completed operations, with $L$ managed vertices. If a red star ends an operation early, the cost is at most that of its hypothetical nonterminal blue completion. An endless run with $L<n$ would have bounded queries and bounded isolated additions, which is impossible. Thus within $\lfloor9(n-1)/5\rfloor$ queries there is a red star or the paths cover $n$ managed vertices.

To join two paths, query an edge between their endpoints $a,b$ if necessary. If it is red, query from $a$ to five fresh vertices. As long as there is no red star, at least three are blue. Query from $b$ to three such neighbors. Either the red edge $ab$ and those three queries form a red four-leaf star, or there is a blue two-edge connection. This costs at most nine queries and preserves all path vertices. At most three joins suffice. The upper and lower bounds have the same asymptotic coefficient.

Run `python3 verify.py` in `certificate/` with assertions enabled. The report gives `verified: true`, 1,063 reachable states and 1,408 nonterminal Painter branches. The potential inequality telescopes, so this finite check bounds the cost for every $n$.
