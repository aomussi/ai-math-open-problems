import Green88.Theorem
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Green88

/-- At least r coordinates increase from x to y. -/
def ManyLess {q N : ℕ} (r : ℕ) (x y : Fin q → Fin N) : Prop :=
  r ≤ (Finset.univ.filter fun i => x i < y i).card

/-- Any pair has at least r strict comparisons in one common direction. -/
def PairwiseManyComparable {q N : ℕ} (r : ℕ) (S : Finset (Fin q → Fin N)) : Prop :=
  (S : Set (Fin q → Fin N)).Pairwise fun x y => ManyLess r x y ∨ ManyLess r y x

private def tailCoordinates {q r N : ℕ} (x : Fin q → Fin N) :
    Fin (q - r - 1) → Fin N := fun i => x ⟨r + 1 + i.val, by have := i.isLt; omega⟩

private def firstThree {q N : ℕ} (hq : 3 ≤ q) (x : Fin q → Fin N) :
    Fin 3 → Fin N := fun i => x (Fin.castLE hq i)

private theorem fiber_twoLess {q r N : ℕ} (hr : 2 ≤ r) (hq : r < q)
    {x y : Fin q → Fin N} (ht : tailCoordinates (r := r) x = tailCoordinates (r := r) y)
    (h : ManyLess r x y) :
    TwoLess (firstThree (by omega) x) (firstThree (by omega) y) := by
  classical
  let good := Finset.univ.filter fun i => x i < y i
  have hlt (i : good) : i.val.val < r + 1 := by
    by_contra! hi
    let j : Fin (q - r - 1) := ⟨i.val.val - (r + 1), by have := i.val.isLt; omega⟩
    have he : x i.val = y i.val := by
      have hj : (⟨r + 1 + j.val, by have := j.isLt; omega⟩ : Fin q) = i.val :=
        Fin.ext (by dsimp [j]; omega)
      simpa only [tailCoordinates, hj] using congrFun ht j
    have hg := (Finset.mem_filter.mp i.property).2
    exact (ne_of_lt hg) he
  let emb : good ↪ Fin (r + 1) := ⟨fun i => ⟨i.val.val, hlt i⟩, by
    intro i j he
    exact Subtype.ext (Fin.ext (congrArg (fun k : Fin (r + 1) => k.val) he))⟩
  let used := (Finset.univ : Finset good).map emb
  have hcard : r ≤ used.card := by simpa [used, good, ManyLess] using h
  let X := firstThree (q := q) (by omega) x
  let Y := firstThree (q := q) (by omega) y
  change TwoLess X Y
  apply Classical.byContradiction
  intro htwo
  have bad : ∃ i j : Fin 3, i ≠ j ∧ ¬ X i < Y i ∧ ¬ X j < Y j := by
    by_cases h0 : X 0 < Y 0 <;> by_cases h1 : X 1 < Y 1 <;> by_cases h2 : X 2 < Y 2
    all_goals first
      | exact ⟨0, 1, by decide, h0, h1⟩
      | exact ⟨0, 2, by decide, h0, h2⟩
      | exact ⟨1, 2, by decide, h1, h2⟩
      | exact (htwo ⟨0, 1, by decide, h0, h1⟩).elim
      | exact (htwo ⟨0, 2, by decide, h0, h2⟩).elim
      | exact (htwo ⟨1, 2, by decide, h1, h2⟩).elim
  let cast : Fin 3 ↪ Fin (r + 1) := Fin.castLEEmb (by omega)
  have absent (i : Fin 3) (hi : ¬ X i < Y i) : cast i ∉ used := by
    intro hmem
    obtain ⟨j, -, hj⟩ := Finset.mem_map.mp hmem
    have he : j.val = Fin.castLE (by omega : 3 ≤ q) i := Fin.ext (congrArg (fun k : Fin (r + 1) => k.val) hj)
    change ¬ x (Fin.castLE _ i) < y (Fin.castLE _ i) at hi
    rw [← he] at hi
    exact hi (Finset.mem_filter.mp j.property).2
  obtain ⟨i, j, hne, hi, hj⟩ := bad
  have hc : (insert (cast i) (insert (cast j) used)).card ≤ r + 1 := by
    simpa using Finset.card_le_univ (insert (cast i) (insert (cast j) used))
  rw [Finset.card_insert_of_not_mem (by simp [cast.injective.ne hne, absent i hi]),
    Finset.card_insert_of_not_mem (absent j hj)] at hc
  omega

/-- The exact fiber reduction for higher-dimensional comparable sets.
Any bound C on the size of comparable triples yields N^(q-r-1) C in dimension q. -/
theorem higher_dimensional_reduction {q r N C : ℕ} (hr : 2 ≤ r) (hq : r < q)
    {S : Finset (Fin q → Fin N)} (hS : PairwiseManyComparable r S)
    (hC : ∀ T : Finset (Fin 3 → Fin N), PairwiseComparable T → T.card ≤ C) :
    S.card ≤ N ^ (q - r - 1) * C := by
  classical
  let tail := tailCoordinates (q := q) (r := r) (N := N)
  let head := firstThree (q := q) (N := N) (by omega)
  have fiber_bound (a : Fin (q - r - 1) → Fin N) :
      (S.filter fun x => tail x = a).card ≤ C := by
    let F := S.filter fun x => tail x = a
    have pair (x y : Fin q → Fin N) (hx : x ∈ F) (hy : y ∈ F) (hne : x ≠ y) :
        Comparable (head x) (head y) := by
      obtain ⟨hxS, hxa⟩ := Finset.mem_filter.mp hx
      obtain ⟨hyS, hya⟩ := Finset.mem_filter.mp hy
      have ht := hxa.trans hya.symm
      exact (hS hxS hyS hne).imp (fiber_twoLess hr hq ht) (fiber_twoLess hr hq ht.symm)
    have inj : Set.InjOn head (F : Set (Fin q → Fin N)) := by
      intro x hx y hy he
      by_contra hn
      have hc := pair x y hx hy hn
      rw [he] at hc
      rcases hc with ⟨i, _, _, hi, _⟩ | ⟨i, _, _, hi, _⟩ <;> exact (lt_irrefl _) hi
    rw [← Finset.card_image_of_injOn inj]
    apply hC
    intro x hx y hy hne
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact pair _ _ hu hv (fun e => hne (congrArg head e))
  have hbound := Finset.card_le_mul_card_image_of_maps_to (s := S) (f := tail)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _) C (fun a _ => fiber_bound a)
  simpa [Fintype.card_fun, mul_comm] using hbound

/-- The grid theorem's single exponent saving works for all 2 ≤ r < q. -/
theorem higher_dimensional_power :
    ∃ δ > (0 : ℝ), ∀ (q r N : ℕ), 2 ≤ r → r < q →
      ∀ S : Finset (Fin q → Fin N), PairwiseManyComparable r S →
        (S.card : ℝ) ≤ (N : ℝ) ^ ((q - r - 1 : ℕ) + (2 - δ)) := by
  obtain ⟨δ, hδ, hgrid⟩ := green_88
  refine ⟨δ, hδ, ?_⟩
  intro q r N hr hq S hS
  by_cases hN : N = 0
  · subst N
    have hS0 : S = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨x, _⟩
      exact Fin.elim0 (x ⟨0, by omega⟩)
    simp only [hS0, Finset.card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg le_rfl _
  let C : ℕ := ⌊(N : ℝ) ^ (2 - δ)⌋₊
  have hC (T : Finset (Fin 3 → Fin N)) (hT : PairwiseComparable T) : T.card ≤ C :=
    Nat.le_floor (hgrid _ _ hT)
  have hp : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  calc
    (S.card : ℝ) ≤ (N : ℝ) ^ (q - r - 1 : ℕ) * C := by
      exact_mod_cast higher_dimensional_reduction hr hq hS hC
    _ ≤ (N : ℝ) ^ (q - r - 1 : ℕ) * (N : ℝ) ^ (2 - δ) :=
      mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by positivity)
    _ = _ := by rw [Real.rpow_add hp, Real.rpow_natCast]

#print axioms higher_dimensional_reduction
#print axioms higher_dimensional_power

end Green88
