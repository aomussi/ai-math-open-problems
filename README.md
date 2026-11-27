# AI-assisted investigations of open problems in mathematics

This collection presents 20 mathematical results developed through an experiment with AI reasoning systems. The project maintainer selected the problems, initiated and directed the attempts, collected the resulting materials, and prepared the collection. AI systems generated the proof arguments and much of the verification code. The results table records the original ranks in the Codex and Claude problem lists. The result pages state the claims, cite the source questions and prior inputs, and describe the evidence.

The result pages distinguish mathematical arguments from the computational checks used to establish them. Several results address a stated part of a broader question. The collection is offered for independent scrutiny and reproduction, with no claim of publication priority or peer review.

## Results

| Result | Main deliverable | Original list rank |
| --- | --- | --- |
| [Three-heap Wythoff Nim](results/three-heap-wythoff-nim/README.md) | Exact minimum-heap-11 slice and an eventual special Wythoff sequence | Codex #1 |
| [Ghafari–Wanless Latin squares](results/ghafari-wanless-latin-squares/README.md) | Empty common intersection of transversals for the specified even orders | Codex #3 |
| [Difference coverings modulo 26](results/difference-covering-mod-26/README.md) | Exact five-column minimum of 27 rows | Codex #4 |
| [Zarankiewicz number](results/zarankiewicz-16x17-3x3/README.md) | Exact value 132 for the 16-by-17 instance forbidding an all-one 3-by-3 submatrix | Codex #5 |
| [Kotzig Nim](results/kotzig-nim-3-5/README.md) | Complete classification for moves 3 and 5 | Codex #7 |
| [Three-move subtraction games](results/three-move-subtraction-games/README.md) | Positive Grundy preperiod for moves $2\le a<b<2a$ and $c>b$ when $0<c\bmod(a+b)<b-a$ | Codex #8 |
| [Path–path partition](results/path-path-partition/README.md) | NP-completeness with both quotient and bags constrained to paths | Codex #11 |
| [Difference coverings modulo 42](results/difference-covering-mod-42/README.md) | Exact five-column minimum of 43 rows | Codex #12 |
| [Four-heap Gale's Nim](results/four-heap-gales-nim/README.md) | A finite-state classification of losing positions | Codex #14 |
| [Dawson's Kayles](results/dawsons-kayles/README.md) | Countably infinite misère quotient for the universe generated through heap size 34 | Codex #20 |
| [Induced cycle saturation](results/induced-c12-saturation/README.md) | Two 24-vertex induced-C₁₂-saturated graphs | Codex #25 |
| [Online Ramsey numbers](results/online-ramsey-star-vs-path/README.md) | Asymptotic coefficient 9/5 for a red four-leaf star versus a blue path | Codex #27 |
| [Binary projective coloring](results/pg-7-2-chromatic-number/README.md) | Six colors to avoid monochromatic lines in PG(7,2), with a separate computational certificate | Codex #29 |
| [Three point charges](results/three-point-charge-equilibrium/README.md) | Uniqueness of equilibrium for noncollinear, nonzero charges of total charge zero | Codex #45 |
| [Log-concave maximum likelihood](results/log-concave-maximum-likelihood/README.md) | Realization by distinct, equally weighted observations | Codex #57 |
| [Real rank of ternary quartics](results/ternary-quartic-rank/README.md) | Counterexample to Michałek et al.'s description of the algebraic boundary for real rank six | Codex #58 |
| [2-annihilation games](results/two-annihilation-games/README.md) | A polynomial-time win, loss and draw classification | Codex #68 |
| [Geodesic convexity in orthant spaces](results/geodesic-convexity-orthant-spaces/README.md) | A nonclosed three-point geodesic convex hull | Codex #77 |
| [Green's Problem 88](results/green-problem-88/README.md) | A fixed power saving for 2-comparable triples and the exact modular maximum. [Lean 4 proofs](results/green-problem-88/lean/README.md) and [extensions](results/green-problem-88/extensions.md) | Codex #84 |
| [Butson Hadamard matrices](results/butson-hadamard-46-6/README.md) | An explicit BH(46,6) construction | Claude #1 |

## Reproduction

Use the commands from the relevant result page. Unless the result page lists another requirement, the Python checkers use Python 3.10 or later and the standard library. Run them with assertions enabled by omitting the `-O` and `-OO` flags. For PG(7,2), download `pg72-chromatic6-certificate.zip` and `SHA256SUMS.txt` from the GitHub release assets. The [PG(7,2) verification guide](results/pg-7-2-chromatic-number/verification.md) gives the commands to check the archive hash, replay the certificate, and audit the recorded reports.
