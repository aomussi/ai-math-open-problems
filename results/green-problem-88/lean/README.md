# Green’s Problem 88 in Lean 4

The theorem `Green88.green_88` proves that there is a real constant
$\delta>0$ such that every pairwise 2-comparable set
$S\subseteq [N]^3$ satisfies $|S|\le N^{2-\delta}$.

In the Lean statement, `Fin N` indexes the $N$ coordinate values, and
`Green88.Comparable` means that two distinct coordinates strictly increase
in the same direction. This is the relation used in the problem statement
and in the Formal Conjectures entry.

The modular theorem `Green88.modular_prime_exact` gives the exact maximum
$p^2$ for each odd prime $p$, under Green's forbidden difference condition
in $\mathbb F_p^3$. The theorem `Green88.modular_exact` holds for every
positive odd modulus. Each theorem includes the upper bound and an
attaining set of size $p^2$. The [companion note](../extensions.md) gives
the mathematical proofs and their relation to the original problem.

The project also formalizes these extensions.

| Theorem | Statement |
| --- | --- |
| [`Green88.rectangular_exponent`](Green88/Theorem.lean) | A comparable set in a box of volume $V$ has size at most $V^\theta$ for a uniform $\theta<2/3$. |
| [`Green88.higher_dimensional_reduction`](Green88/HigherDimension.lean) | Any bound $C$ for comparable triples gives the bound $N^{q-r-1}C$ for $r$-comparable sets in $[N]^q$ when $2\le r<q$. |
| [`Green88.higher_dimensional_power`](Green88/HigherDimension.lean) | The same exponent saving gives $N^{q-r+1-\delta}$ for those parameters. |
| [`Green88.ColoredTournament.grid_equivalence`](Green88/ColorAvoiding.lean) | When one color deletion is acyclic, the feasible tournament orders for three path caps agree exactly with the feasible sizes of comparable sets in the corresponding box. |
| [`Green88.ColoredTournament.rectangular_path_power`](Green88/ColorAvoiding.lean) | In this class, a tournament on $m$ vertices with longest path lengths $L_i$ in the three color deletions satisfies $m\le (L_0L_1L_2)^\theta$. |
| [`Green88.ColoredTournament.color_avoiding_power`](Green88/ColorAvoiding.lean) | In the same class, $\max_i L_i\ge m^{1/(2-\delta)}$. |
| [`Green88.ColoredTournament.partition_path_power`](Green88/ColorAvoiding.lean) | If one color deletion admits a partition into $b$ induced acyclic parts, $m\le b(\max_i L_i)^{2-\delta}$. |

Paths are simple and their lengths count vertices. The three colors are
indexed by `Fin 3`. The rectangular bounds use zero-based coordinates with
the same number of values on each axis as the written proof.

## Verification

This project pins Lean 4.19.0 and Mathlib v4.19.0. With Elan and Git
installed, run the following from the repository root.

```sh
cd results/green-problem-88/lean
lake build Green88
lake env lean Green88/Theorem.lean
lake env lean Green88/Modular.lean
lake env lean Green88/HigherDimension.lean
lake env lean Green88/ColorAvoiding.lean
```

The four `lake env lean` commands print the axiom dependencies.

```text
'Green88.rectangular_exponent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Green88.green_88' depends on axioms: [propext, Classical.choice, Quot.sound]
'Green88.modular_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Green88.modular_prime_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Green88.higher_dimensional_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Green88.higher_dimensional_power' depends on axioms: [propext, Classical.choice, Quot.sound]
'Green88.ColoredTournament.grid_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Green88.ColoredTournament.rectangular_path_power' depends on axioms: [propext, Classical.choice, Quot.sound]
'Green88.ColoredTournament.color_avoiding_power' depends on axioms: [propext, Classical.choice, Quot.sound]
'Green88.ColoredTournament.partition_path_power' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's standard axioms. The grid proof uses Mathlib's triangle
removal lemma and derives the qualitative upper bound for 2-comparable
sets within this project.

A first build can use prebuilt Mathlib artifacts. Run the following
before `lake build Green88` to download the required portion of the cache.

```sh
lake exe cache get \
  Mathlib.Combinatorics.SimpleGraph.Triangle.Removal \
  Mathlib.Analysis.MeanInequalities \
  Mathlib.Tactic.FinCases Mathlib.Tactic.Ring Mathlib.Tactic.Linarith \
  Mathlib.Tactic.FieldSimp Mathlib.Order.Interval.Finset.Nat \
  Mathlib.Data.Nat.Prime.Basic Mathlib.Data.ZMod.Basic \
  Mathlib.Data.Fintype.Order Mathlib.Data.Fin.VecNotation \
  Mathlib.Data.List.Chain Mathlib.Algebra.Order.BigOperators.Group.Finset
```

If the native cache executable fails to launch on macOS, use Lake's
Lean interpreter with the same cache arguments.

```sh
lake build cache
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get \
  Mathlib.Combinatorics.SimpleGraph.Triangle.Removal \
  Mathlib.Analysis.MeanInequalities \
  Mathlib.Tactic.FinCases Mathlib.Tactic.Ring Mathlib.Tactic.Linarith \
  Mathlib.Tactic.FieldSimp Mathlib.Order.Interval.Finset.Nat \
  Mathlib.Data.Nat.Prime.Basic Mathlib.Data.ZMod.Basic \
  Mathlib.Data.Fintype.Order Mathlib.Data.Fin.VecNotation \
  Mathlib.Data.List.Chain Mathlib.Algebra.Order.BigOperators.Group.Finset
```

## Reading the proof

| File | Contents |
| --- | --- |
| [Basic.lean](Green88/Basic.lean) | 2-comparability, injectivity of two-coordinate projections, strict chains in sections, and completion of triangles |
| [Qualitative.lean](Green88/Qualitative.lean) | The uniform $o(N^2)$ bound via triangle removal |
| [Rectangle.lean](Green88/Rectangle.lean) | Rank compression and bounds for rectangular boxes |
| [Coarse.lean](Green88/Coarse.lean) | Interval decomposition, projection counts, and groups of boxes on a coarse line |
| [Selection.lean](Green88/Selection.lean) | Transfer of comparability across one shared coarse coordinate and greedy selection |
| [Sampling.lean](Green88/Sampling.lean) | Exact finite counting of independent coordinate choices and marked boxes |
| [Budget.lean](Green88/Budget.lean) | Removal of groups on long lines and the arithmetic–geometric mean inequality for projection ratios |
| [Power.lean](Green88/Power.lean), [Induction.lean](Green88/Induction.lean) | The numerical inequalities and strong induction on rectangular volume |
| [Tensor.lean](Green88/Tensor.lean) | Lexicographic products and removal of the factor 2 |
| [Theorem.lean](Green88/Theorem.lean) | The cubical and rectangular grid bounds |
| [HigherDimension.lean](Green88/HigherDimension.lean) | Fixed-coordinate fibers and projection onto three coordinates |
| [DirectedPaths.lean](Green88/DirectedPaths.lean) | Longest simple paths, acyclic extensions, and directed Hamilton paths in tournaments |
| [ColorAvoiding.lean](Green88/ColorAvoiding.lean) | The height embedding, the converse grid construction, and the bounds for color-avoiding paths |
| [Modular.lean](Green88/Modular.lean) | The forbidden difference condition, injective projection, and attaining plane for the modular theorem |

The proof follows the manuscript's rectangular induction and tensor
argument. Each axis uses blocks of width $\lfloor r/k\rfloor+1$,
truncated at the boundary of the rectangle. The sampling space includes
the padded offsets in the last block. An offset marks a box only when it
occurs in the corresponding projection. Finite cardinality identities
therefore give the marking probabilities directly. The
arithmetic–geometric mean inequality bounds the sum of the cube roots
of the projection products.

## References

- Ben Green, [100 open problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf), Problem 88.
- W. T. Gowers and J. Long, [The length of an $s$-increasing sequence of $r$-tuples](https://arxiv.org/abs/1609.08688).
- [Research note from the project release](https://github.com/aomussi/ai-math-open-problems/tree/v1.0.0/results/codex-084).
