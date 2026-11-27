import Green88.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset

namespace Green88

open scoped BigOperators

/-- The points agreeing with `x` away from coordinate `i`. -/
def line {α : Type*} [DecidableEq α] (E : Finset (Fin 3 → α)) (x : Fin 3 → α)
    (i : Fin 3) : Finset (Fin 3 → α) :=
  E.filter fun y => ∀ j : Fin 3, j ≠ i → x j = y j

theorem mem_line {α : Type*} [DecidableEq α] {E : Finset (Fin 3 → α)}
    {x y : Fin 3 → α} {i : Fin 3} :
    y ∈ line E x i ↔ y ∈ E ∧ ∀ j : Fin 3, j ≠ i → x j = y j :=
  Finset.mem_filter

theorem comparable_of_no_equal {α : Type*} [LinearOrder α] {x y : Fin 3 → α}
    (hne : ∀ i, x i ≠ y i) : Comparable x y := by
  have cmp (i : Fin 3) := (lt_or_gt_of_ne (hne i))
  rcases cmp 0 with a | a <;> rcases cmp 1 with b | b
  · exact Or.inl ⟨0, 1, by decide, a, b⟩
  · exact (cmp 2).elim (fun c => Or.inl ⟨0, 2, by decide, a, c⟩)
      (fun c => Or.inr ⟨1, 2, by decide, b, c⟩)
  · exact (cmp 2).elim (fun c => Or.inl ⟨1, 2, by decide, b, c⟩)
      (fun c => Or.inr ⟨0, 2, by decide, a, c⟩)
  · exact Or.inr ⟨0, 1, by decide, a, b⟩

/-- Thin a set with short axis-parallel lines by selecting points greedily. -/
theorem select_comparable {α : Type*} [LinearOrder α] [DecidableEq α] (L : ℕ)
    (E : Finset (Fin 3 → α))
    (hline : ∀ x ∈ E, ∀ i, (line E x i).card ≤ L)
    (hone : ∀ x ∈ E, ∀ y ∈ E, ∀ i : Fin 3, x i = y i →
      (∀ j : Fin 3, j ≠ i → x j ≠ y j) → Comparable x y) :
    ∃ T ⊆ E, PairwiseComparable T ∧ E.card ≤ 3 * L * T.card := by
  classical
  induction E using Finset.strongInductionOn with
  | _ E ih =>
      obtain rfl | ⟨x, hx⟩ := E.eq_empty_or_nonempty
      · exact ⟨∅, Finset.Subset.rfl, by simp [PairwiseComparable], by simp⟩
      let B := (Finset.univ : Finset (Fin 3)).biUnion (line E x)
      have hB : B ⊆ E := by
        intro y hy
        obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hy
        exact (mem_line.mp hi).1
      have hxB : x ∈ B :=
        Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, mem_line.mpr ⟨hx, fun _ _ => rfl⟩⟩
      have hBc : B.card ≤ 3 * L := by
        calc
          B.card ≤ ∑ i : Fin 3, (line E x i).card := Finset.card_biUnion_le
          _ ≤ ∑ _i : Fin 3, L := Finset.sum_le_sum fun i _ => hline x hx i
          _ = 3 * L := by simp
      let D := E \ B
      have hD : D ⊆ E := Finset.sdiff_subset
      have hxD : x ∉ D := fun h => (Finset.mem_sdiff.mp h).2 hxB
      have hD' : D ⊂ E := Finset.ssubset_iff_subset_ne.mpr
        ⟨hD, fun e => hxD (e.symm ▸ hx)⟩
      have hlineD (y : Fin 3 → α) (hy : y ∈ D) (i : Fin 3) :
          (line D y i).card ≤ L :=
        (Finset.card_le_card fun _ hz => mem_line.mpr
          ⟨hD (mem_line.mp hz).1, (mem_line.mp hz).2⟩).trans (hline y (hD hy) i)
      obtain ⟨T, hT, hcomp, ht⟩ := ih D hD' hlineD
        (fun y hy z hz i he hne => hone y (hD hy) z (hD hz) i he hne)
      have hTx : x ∉ T := fun h => hxD (hT h)
      refine ⟨insert x T, Finset.insert_subset hx (hT.trans hD), ?_, ?_⟩
      · have hxy (y : Fin 3 → α) (hy : y ∈ T) : Comparable x y := by
          have hyD := Finset.mem_sdiff.mp (hT hy)
          by_cases he : ∃ i, x i = y i
          · obtain ⟨i, hi⟩ := he
            apply hone x hx y hyD.1 i hi
            intro j hji hj
            obtain ⟨k, hk⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
              fin_cases i <;> fin_cases j <;> first | contradiction | decide
            apply hyD.2
            refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _,
              mem_line.mpr ⟨hyD.1, ?_⟩⟩
            intro l hlk
            by_cases hli : l = i
            · simpa [hli] using hi
            by_cases hlj : l = j
            · simpa [hlj] using hj
            exact False.elim (hlk (fin3_eq_of_ne hji.symm hli hlj hk.1 hk.2))
          · exact comparable_of_no_equal (fun i eq => he ⟨i, eq⟩)
        intro a ha b hb hne
        change a ∈ insert x T at ha
        change b ∈ insert x T at hb
        rcases Finset.mem_insert.mp ha with ea | ha
        · subst a
          rcases Finset.mem_insert.mp hb with eb | hb
          · exact False.elim (hne eb.symm)
          · exact hxy _ hb
        · rcases Finset.mem_insert.mp hb with eb | hb
          · subst b
            exact comparable_symm (hxy _ ha)
          · exact hcomp ha hb hne
      · rw [Finset.card_insert_of_not_mem hTx, Nat.mul_succ]
        rw [← Finset.card_sdiff_add_card_eq_card hB]
        exact Nat.add_le_add ht hBc

/-- Boxes hit in all three one-dimensional projections by a shared choice of coordinates. -/
def IsMarked {α β : Type*} (S : Finset (Fin 3 → α))
    (bin : Fin 3 → α → β) (sample : Fin 3 → β → α) (e : Fin 3 → β) : Prop :=
  ∀ i : Fin 3, ∃ p ∈ S, (∀ j : Fin 3, bin j (p j) = e j) ∧ p i = sample i (e i)

/-- After fixing a fine coordinate, the other two coarse coordinates form a weak chain. -/
def SectionChains {α β : Type*} [LE β] (S : Finset (Fin 3 → α))
    (bin : Fin 3 → α → β) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ i j k : Fin 3, j ≠ k → i ≠ j → i ≠ k → x i = y i →
    (bin j (x j) ≤ bin j (y j) ∧ bin k (x k) ≤ bin k (y k)) ∨
    (bin j (y j) ≤ bin j (x j) ∧ bin k (y k) ≤ bin k (x k))

theorem sectionChains_of_comparable {α β : Type*} [LinearOrder α] [LinearOrder β]
    {S : Finset (Fin 3 → α)} (hS : PairwiseComparable S)
    {bin : Fin 3 → α → β} (hbin : ∀ i, Monotone (bin i)) : SectionChains S bin := by
  intro x hx y hy i j k hjk hij hik hi
  by_cases he : x = y
  · subst y
    exact Or.inl ⟨le_rfl, le_rfl⟩
  exact (section_chain hjk hij hik hi (hS hx hy he)).imp
    (fun h => ⟨hbin j h.1.le, hbin k h.2.le⟩) (fun h => ⟨hbin j h.1.le, hbin k h.2.le⟩)

/-- Marked boxes sharing just one coarse coordinate inherit comparability. -/
theorem marked_comparable_of_sections {α β : Type*} [LinearOrder α] [LinearOrder β]
    {S : Finset (Fin 3 → α)} {bin : Fin 3 → α → β} (hS : SectionChains S bin)
    {sample : Fin 3 → β → α} {e f : Fin 3 → β}
    (he : IsMarked S bin sample e) (hf : IsMarked S bin sample f)
    (i : Fin 3) (hi : e i = f i)
    (hne : ∀ j : Fin 3, j ≠ i → e j ≠ f j) : Comparable e f := by
  classical
  obtain ⟨p, hp, hpe, hpi⟩ := he i
  obtain ⟨q, hq, hqf, hqi⟩ := hf i
  have heq : p i = q i := hpi.trans ((congrArg (sample i) hi).trans hqi.symm)
  obtain ⟨j, k, hjk, hij, hik⟩ : ∃ j k : Fin 3, j ≠ k ∧ i ≠ j ∧ i ≠ k := by
    fin_cases i <;> decide
  have h := hS p hp q hq i j k hjk hij hik heq
  simp only [hpe, hqf] at h
  rcases h with h | h
  · exact Or.inl ⟨j, k, hjk, lt_of_le_of_ne h.1 (hne j hij.symm),
      lt_of_le_of_ne h.2 (hne k hik.symm)⟩
  · exact Or.inr ⟨j, k, hjk, lt_of_le_of_ne h.1 (hne j hij.symm).symm,
      lt_of_le_of_ne h.2 (hne k hik.symm).symm⟩

theorem marked_comparable {α β : Type*} [LinearOrder α] [LinearOrder β]
    {S : Finset (Fin 3 → α)} (hS : PairwiseComparable S)
    {bin : Fin 3 → α → β} (hbin : ∀ i, Monotone (bin i))
    {sample : Fin 3 → β → α} {e f : Fin 3 → β}
    (he : IsMarked S bin sample e) (hf : IsMarked S bin sample f)
    (i : Fin 3) (hi : e i = f i)
    (hne : ∀ j : Fin 3, j ≠ i → e j ≠ f j) : Comparable e f :=
  marked_comparable_of_sections (sectionChains_of_comparable hS hbin) he hf i hi hne

/-- Each sample marks at most three times the line bound times the coarse extremal bound. -/
theorem marked_card_bound_of_sections {α β : Type*} [LinearOrder α] [LinearOrder β] [DecidableEq β] {L C : ℕ}
    {S : Finset (Fin 3 → α)} {bin : Fin 3 → α → β} (hS : SectionChains S bin)
    {E R : Finset (Fin 3 → β)} (hsub : E ⊆ R)
    (hR : ∀ x ∈ R, ∀ i, (line R x i).card ≤ L)
    (hC : ∀ T : Finset (Fin 3 → β), PairwiseComparable T → T.card ≤ C)
    {sample : Fin 3 → β → α} (hmark : ∀ x ∈ E, IsMarked S bin sample x) :
    E.card ≤ 3 * L * C := by
  have hline (x : Fin 3 → β) (hx : x ∈ E) (i : Fin 3) : (line E x i).card ≤ L := by
    have hsubset : line E x i ⊆ line R x i := by
      intro y hy
      rw [mem_line] at hy ⊢
      exact ⟨hsub hy.1, hy.2⟩
    exact (Finset.card_le_card hsubset).trans (hR x (hsub hx) i)
  have hone (x : Fin 3 → β) (hx : x ∈ E) (y : Fin 3 → β) (hy : y ∈ E)
      (i : Fin 3) (he : x i = y i) (hn : ∀ j : Fin 3, j ≠ i → x j ≠ y j) :
      Comparable x y :=
    marked_comparable_of_sections hS (hmark x hx) (hmark y hy) i he hn
  obtain ⟨T, -, hT, hcard⟩ := select_comparable L E hline hone
  exact hcard.trans (Nat.mul_le_mul_left _ (hC T hT))


theorem marked_card_bound {α β : Type*} [LinearOrder α] [LinearOrder β] [DecidableEq β] {L C : ℕ}
    {S : Finset (Fin 3 → α)} (hS : PairwiseComparable S)
    {bin : Fin 3 → α → β} (hbin : ∀ i, Monotone (bin i))
    {E R : Finset (Fin 3 → β)} (hsub : E ⊆ R)
    (hR : ∀ x ∈ R, ∀ i, (line R x i).card ≤ L)
    (hC : ∀ T : Finset (Fin 3 → β), PairwiseComparable T → T.card ≤ C)
    {sample : Fin 3 → β → α} (hmark : ∀ x ∈ E, IsMarked S bin sample x) :
    E.card ≤ 3 * L * C :=
  marked_card_bound_of_sections (sectionChains_of_comparable hS hbin) hsub hR hC hmark

end Green88
