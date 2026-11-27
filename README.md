# AI-assisted investigations of open problems in mathematics

This collection presents 20 mathematical results developed through an experiment with AI reasoning systems. The project maintainer selected the problems, initiated and directed the attempts, collected the resulting materials, and prepared the collection. AI systems generated the proof arguments and much of the verification code. The folder prefixes identify the problem lists compiled with Codex and Claude. The numerical suffixes give the original ranks in those lists. The result pages state the claims, cite the source questions and prior inputs, and describe the evidence.

The result pages distinguish mathematical arguments from the computational checks used to establish them. Several results address a stated part of a broader question. The collection is offered for independent scrutiny and reproduction, with no claim of publication priority or peer review.

## Results

| Result | Main deliverable |
| --- | --- |
| [Three-heap Wythoff Nim](results/codex-001/README.md) | Exact minimum-heap-11 slice and an eventual special Wythoff sequence |
| [Ghafari–Wanless Latin squares](results/codex-003/README.md) | Empty common intersection of transversals for the specified even orders |
| [Difference coverings modulo 26](results/codex-004/README.md) | Exact five-column minimum of 27 rows |
| [Zarankiewicz number](results/codex-005/README.md) | Exact value 132 for the 16-by-17 instance forbidding an all-one 3-by-3 submatrix |
| [Kotzig Nim](results/codex-007/README.md) | Complete classification for moves 3 and 5 |
| [Three-move subtraction games](results/codex-008/README.md) | Positive Grundy preperiod for moves $2\le a<b<2a$ and $c>b$ when $0<c\bmod(a+b)<b-a$ |
| [Path–path partition](results/codex-011/README.md) | NP-completeness with both quotient and bags constrained to paths |
| [Difference coverings modulo 42](results/codex-012/README.md) | Exact five-column minimum of 43 rows |
| [Four-heap Gale's Nim](results/codex-014/README.md) | A finite-state classification of losing positions |
| [Dawson's Kayles](results/codex-020/README.md) | Countably infinite misère quotient for the universe generated through heap size 34 |
| [Induced cycle saturation](results/codex-025/README.md) | Two 24-vertex induced-C₁₂-saturated graphs |
| [Online Ramsey numbers](results/codex-027/README.md) | Asymptotic coefficient 9/5 for a red four-leaf star versus a blue path |
| [Binary projective coloring](results/codex-029/README.md) | Six colors to avoid monochromatic lines in PG(7,2), with a separate computational certificate |
| [Three point charges](results/codex-045/README.md) | Uniqueness of equilibrium for noncollinear, nonzero charges of total charge zero |
| [Log-concave maximum likelihood](results/codex-057/README.md) | Realization by distinct, equally weighted observations |
| [Real rank of ternary quartics](results/codex-058/README.md) | Counterexample to Michałek et al.'s description of the algebraic boundary for real rank six |
| [2-annihilation games](results/codex-068/README.md) | A polynomial-time win, loss and draw classification |
| [Geodesic convexity in orthant spaces](results/codex-077/README.md) | A nonclosed three-point geodesic convex hull |
| [Green's Problem 88](results/green-problem-88/README.md) | A fixed power saving for 2-comparable triples and the exact modular maximum. [Lean 4 proofs](results/green-problem-88/lean/README.md) and [extensions](results/green-problem-88/extensions.md) |
| [Butson Hadamard matrices](results/claude-001/README.md) | An explicit BH(46,6) construction |

## Reproduction

Use the commands from the relevant result page. Unless the result page lists another requirement, the Python checkers use Python 3.10 or later and the standard library. Run them with assertions enabled by omitting the `-O` and `-OO` flags. For PG(7,2), download `pg72-chromatic6-certificate.zip` and `SHA256SUMS.txt` from the GitHub release assets. The [PG(7,2) verification guide](results/codex-029/verification.md) gives the commands to check the archive hash, replay the certificate, and audit the recorded reports.
