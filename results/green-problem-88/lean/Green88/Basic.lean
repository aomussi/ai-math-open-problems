import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

namespace Green88

/-- Two distinct coordinates strictly increase from `x` to `y`. -/
def TwoLess {α : Type*} [LT α] (x y : Fin 3 → α) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧ x i < y i ∧ x j < y j

/-- Two triples are comparable in at least two coordinates in the same direction. -/
def Comparable {α : Type*} [LT α] (x y : Fin 3 → α) : Prop :=
  TwoLess x y ∨ TwoLess y x

def PairwiseComparable {α : Type*} [LT α] (S : Finset (Fin 3 → α)) : Prop :=
  (S : Set (Fin 3 → α)).Pairwise Comparable

theorem comparable_symm {α : Type*} [LT α] {x y : Fin 3 → α}
    (h : Comparable x y) : Comparable y x :=
  h.symm

theorem fin3_eq_of_ne {i j k t : Fin 3} (hij : i ≠ j) (hki : k ≠ i)
    (hkj : k ≠ j) (hti : t ≠ i) (htj : t ≠ j) : k = t := by
  apply Fin.ext
  omega

theorem twoLess_coords {α : Type*} [Preorder α] {x y : Fin 3 → α}
    {i j k : Fin 3} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hk : y k ≤ x k) (h : TwoLess x y) : x i < y i ∧ x j < y j := by
  obtain ⟨a, b, hab, ha, hb⟩ := h
  have hak : a ≠ k := fun eq => (not_lt_of_ge hk) (eq ▸ ha)
  have hbk : b ≠ k := fun eq => (not_lt_of_ge hk) (eq ▸ hb)
  have e : (a = i ∧ b = j) ∨ (a = j ∧ b = i) := by
    by_cases hai : a = i
    · exact Or.inl ⟨hai, fin3_eq_of_ne hki hbk ((fun e => hab (hai.trans e.symm))) hkj.symm hij.symm⟩
    · have haj : a = j := fin3_eq_of_ne hki hak hai hkj.symm hij.symm
      exact Or.inr ⟨haj, fin3_eq_of_ne hkj hbk ((fun e => hab (haj.trans e.symm))) hki.symm hij⟩
  rcases e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨ha, hb⟩
  · exact ⟨hb, ha⟩

/-- On a section with one coordinate fixed, the other two coordinates form a strict chain. -/
theorem section_chain {α : Type*} [Preorder α] {x y : Fin 3 → α} {i j k : Fin 3}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (hk : x k = y k)
    (h : Comparable x y) : (x i < y i ∧ x j < y j) ∨ (y i < x i ∧ y j < x j) := by
  rcases h with h | h
  · exact Or.inl (twoLess_coords hij hki hkj (le_of_eq hk.symm) h)
  · exact Or.inr (twoLess_coords hij hki hkj (le_of_eq hk) h)

/-- A comparable pair cannot agree in two distinct coordinates. -/
theorem not_two_equal {α : Type*} [Preorder α] {x y : Fin 3 → α} {i j : Fin 3}
    (hij : i ≠ j) (hi : x i = y i) (hj : x j = y j) (h : Comparable x y) : False := by
  have aux : ∀ {a b : Fin 3 → α}, a i = b i → a j = b j → TwoLess a b → False := by
    intro a b ei ej ⟨k, l, hkl, hk, hl⟩
    have hki : k ≠ i := fun e => (not_lt_of_ge (le_of_eq ei.symm)) (e ▸ hk)
    have hkj : k ≠ j := fun e => (not_lt_of_ge (le_of_eq ej.symm)) (e ▸ hk)
    have hli : l ≠ i := fun e => (not_lt_of_ge (le_of_eq ei.symm)) (e ▸ hl)
    have hlj : l ≠ j := fun e => (not_lt_of_ge (le_of_eq ej.symm)) (e ▸ hl)
    exact hkl (fin3_eq_of_ne hij hki hkj hli hlj)
  exact h.elim (aux hi hj) (aux hi.symm hj.symm)

/-- Every two-coordinate projection is injective on a pairwise 2-comparable set. -/
theorem projection_inj {α : Type*} [Preorder α] {S : Finset (Fin 3 → α)}
    (hS : PairwiseComparable S) {i j : Fin 3} (hij : i ≠ j) :
    Set.InjOn (fun x : Fin 3 → α => (x i, x j)) (S : Set (Fin 3 → α)) := by
  intro x hx y hy he
  by_contra hne
  exact not_two_equal hij (congrArg Prod.fst he) (congrArg Prod.snd he) (hS hx hy hne)

theorem card_le_square {n : ℕ} {S : Finset (Fin 3 → Fin n)}
    (hS : PairwiseComparable S) : S.card ≤ n ^ 2 := by
  classical
  have hp := projection_inj hS (show (0 : Fin 3) ≠ 1 by decide)
  calc
    S.card = (S.image fun x => (x 0, x 1)).card :=
      (Finset.card_image_of_injOn hp).symm
    _ ≤ Fintype.card (Fin n × Fin n) := Finset.card_le_univ _
    _ = n ^ 2 := by simp [pow_two]

/-- If three triples supply the three edges of a triangle, the triangle's triple is in the set. -/
theorem triangle_completion {α : Type*} [LinearOrder α] {S : Finset (Fin 3 → α)}
    (hS : PairwiseComparable S) {p q r : Fin 3 → α}
    (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S)
    (hpq : p 2 = q 2) (hpr : p 1 = r 1) (hqr : q 0 = r 0) :
    ∃ x ∈ S, x 0 = q 0 ∧ x 1 = p 1 ∧ x 2 = p 2 := by
  by_cases e : p 0 = q 0
  · exact ⟨p, hp, e, rfl, rfl⟩
  have comp (x y : Fin 3 → α) (hx : x ∈ S) (hy : y ∈ S)
      (i : Fin 3) (hi : x i ≠ y i) : Comparable x y :=
    hS hx hy (fun he => hi (congrFun he i))
  have cpq := section_chain (i := 0) (j := 1) (k := 2)
    (by decide) (by decide) (by decide) hpq (comp p q hp hq 0 e)
  have hq1 : q 1 ≠ r 1 := by
    rw [← hpr]
    exact cpq.elim (fun h => ne_of_gt h.2) (fun h => ne_of_lt h.2)
  have cqr := section_chain (i := 1) (j := 2) (k := 0)
    (by decide) (by decide) (by decide) hqr (comp q r hq hr 1 hq1)
  have hr0 : p 0 ≠ r 0 := by rwa [← hqr]
  have cpr := section_chain (i := 0) (j := 2) (k := 1)
    (by decide) (by decide) (by decide) hpr (comp p r hp hr 0 hr0)
  simp only [← hpq, ← hpr, ← hqr] at cqr cpr
  exfalso
  rcases cpq with a | a <;> rcases cqr with b | b <;> rcases cpr with c | c
  all_goals first
    | exact (lt_asymm a.1) c.1
    | exact (lt_asymm a.2) b.1
    | exact (lt_asymm b.2) c.2

end Green88
