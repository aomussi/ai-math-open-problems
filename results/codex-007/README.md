# Kotzig Nim with moves 3 and 5

On the directed cycle $\mathbb Z/n\mathbb Z$, start from vertex 0 with 0 marked visited. A move adds 3 or 5 modulo $n$, landing on an unvisited vertex. Normal play applies. The second player wins exactly when $n$ is odd and $n\notin\{9,11,17\}$. [Tan and Ward, Conjecture 4.3](https://math.colgate.edu/~integers/og6/og6.pdf)

The general eventual-periodicity theorem for Kotzig Nim is due to Liang. Liang's reported explicit computations cover smaller move sets. This note determines the outcome for every positive order for the move set $\{3,5\}$. [Liang, Theorem 4.3 and Section 4.5](https://arxiv.org/abs/2608.13273)

## Even orders and the small cases

For even $n$, the first player always adds 3. Their moves start at even vertices and land at odd ones. The starting vertex of each such move is new, and addition by 3 is injective. Thus the destination is distinct from all earlier first-player destinations, and it cannot be a second-player destination. The first player always has this move. Play terminates because vertices cannot be revisited.

The [exact recurrence](verify_small.py) for $n\le33$ tests at most two moves from every pair of current vertex and visited set. A state wins if some legal successor loses. It gives the odd first-player wins $9,11,17$, and covers all odd orders outside the four families below.

## Fixed second-player policies

At vertex $v$ form a mask $p$ from the vertices visited before the current move at offsets $(-3,-5,1,-1,2,-2)$ modulo $n$, with the first offset the low bit. The phase is $v\bmod8$, and $k\ge0$ in each family below. At a second-player turn the policy chooses the preferred legal move, falling back to the other if required.

- For $n=41+8k$ the masks in [strategy_masks.hpp](strategy_masks.hpp) give the preference. At vertices $v<16$ use the left table indexed by $v$. For $1\le n-v\le16$ use the right table indexed by $n-v-1$. Otherwise use the interior table indexed by $v\bmod8$. Bit $p$ set means prefer 5.
- For $n=19+8k$ prefer 5 at interior vertices $2\le v\le n-3$ of phase $0,1,2$ modulo 8.
- For $n=13+8k$ prefer 5 in the same interior at phase 3 or 4, or at phase 5 if $v-3$ was visited.
- For $n=23+8k$, at $v=1,2,n-4$ prefer 5 for mask values $\{13,63\},\{38\},\{2\}$, respectively. For $4\le v<n-4$, prefer 5 according to the following table. All unspecified moves prefer 3.

| Phase | Masks that prefer 5 |
| --- | --- |
| 0 | 39 |
| 1 | 55 |
| 2 | 5, 25, 37 |
| 3 | 1, 2 |
| 4 | 9, 10, 25, 26, 37 |
| 5 | 1, 2, 47, 63 |
| 6 | 9, 10 |
| 7 | 55, 61, 62, 63 |

## A finite test for policy failure

Lift an actual play to the increasing cumulative sums of its moves, starting at zero. A play has at most $n-1$ moves, so an occurrence of a physical vertex $v$ has lift $v+\ell n$, $0\le\ell\le4$. Store each physical vertex as unvisited or as its lap $\ell$ and next step 3, next step 5, or terminal. In odd order the parity of $v+\ell$ equals the parity of the number of preceding moves. The terminal vertex of a second-player loss has odd parity.

Scan these symbols in physical order. A vertex other than 0 is unvisited if it has no incoming step from its predecessors at offsets $-3,-5$, and has the incoming lap if the step is unique. Taking two such steps into the same physical vertex would be a revisit. For $v+1,v+2$ all possible incoming steps also start within the preceding five symbols. Their already-visited tests compare their lifted positions to the current lifted position. In coordinates relative to the scan, an earlier lap is always earlier in the play, and an equal lap is earlier for a negative offset. The symbol for vertex 0 is initialized with lap zero. The last five physical symbols are guessed before scanning, with laps increased by one when represented at negative coordinates. These shifted copies can have relative lap five. A forward copy of vertex 0 at coordinate $n$ has relative lap $-1$.

A second-player move of 5 despite preference for 3 requires the $+3$ target to have been visited. Away from vertex 0 that earlier visit must have arrived by a step 5 from $v-2$, because the current vertex has yet to emit its step. This is available in the preceding window. A move of 3 despite preference for 5 requires the $+5$ target to have been visited. Away from vertex 0 its earlier visit must be via a step 3 from $v+2$. The lap of $v+2$ can be tested at the current vertex, and the direction requirement is recorded to be enforced at $v+2$, including across the boundary. A terminal symbol requires both blockages. Two bits suffice to carry these pending direction requirements.

The verifier filters full windows by necessary conditions. Visits of the same lap within five consecutive vertices must be separated by 3 with a step 3 connecting them. Steps landing within the window have matching laps. Steps crossing the cut at the window's right edge cannot have duplicate targets. The crossing laps are exactly an initial interval of laps starting at zero, since each completed lap crosses the cut once and the current lap crosses it only if the play extends past it. A terminal symbol in the window has lap equal to the number of crossings. These filters leave 1,842 histories. Of these, 541 have no final-window step landing at vertex 0. Each of the 541 is paired with the four possible pending-bit pairs, giving 2,164 boundary signatures.

For the four families the verifier scans a left boundary of lengths $16,5,5,5$, respectively, followed by $9,9,3,13$ internal positions. It then takes the full reachable closure on the graph of internal states. The state carries the window, pending bits and phase modulo 8, so the extra path lengths that connect to the required right boundary phase are multiples of eight. The program scans an equally long right boundary and tests equality with the guessed final window and pending bits. Every real losing play for the fixed policy would furnish such an accepting path. No accepting path exists in any of the four families. The game is finite, so the policy wins at each covered order.

## Reproduction

Compile and run the [finite-state verifier](verify.cpp) with a C++17 compiler. The code reconstructs the coverage from the policy tables and local rules. Run the small-case checker with Python assertions enabled.

```sh
c++ -O3 -std=c++17 -Wall -Wextra -Wpedantic verify.cpp -o verify
./verify
python3 verify_small.py
```

The four runs reach 224,081, 80,856, 92,160 and 163,395 state–signature pairs, respectively, without accepting. The verifier rebuilds the automaton from the strategy and window rules. The two implementations prune their boundary scans differently and visit different numbers of states in the first family. Both report zero accepting paths in each family.

The [original verifier](certificate/verify_all_odd.cpp) is retained byte for byte and has SHA-256 `90599c7a77b4a8b8e232c54514873b12d83577a2cfbfdd53cfddc2b072fc0a6b`. It reproduces the original counts 228,110, 80,856, 92,160 and 163,395, and the full small-case classification. Run from `certificate/`. The compatibility header provides standard headers for Clang.

```sh
c++ -O3 -std=c++17 -isystem compat verify_all_odd.cpp -o verify-original
./verify-original
python3 check_exception_words.py
```
