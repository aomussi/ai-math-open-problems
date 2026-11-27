import Green88.Selection
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Fin

namespace Green88

open scoped BigOperators

/-- Remove groups of exactly `L` from long lines, charging the same cost per group. -/
theorem charge_lines {α : Type*} [DecidableEq α] (L : ℕ) (hL : 0 < L)
    (E : Finset (Fin 3 → α)) (weight : (Fin 3 → α) → ℝ) (cost : ℝ)
    (hcost : ∀ B ⊆ E, ∀ x : Fin 3 → α, ∀ i : Fin 3,
      B.card = L → (∀ e ∈ B, ∀ j : Fin 3, j ≠ i → x j = e j) →
      ∑ e ∈ B, weight e ≤ cost * L) :
    ∃ R ⊆ E, (∀ x ∈ R, ∀ i, (line R x i).card ≤ L) ∧
      (∑ e ∈ E, weight e) ≤ (∑ e ∈ R, weight e) + cost * (E.card - R.card : ℕ) := by
  classical
  induction E using Finset.strongInductionOn with
  | _ E ih =>
    by_cases hf : ∀ x ∈ E, ∀ i, (line E x i).card ≤ L
    · exact ⟨E, Finset.Subset.rfl, hf, by simp⟩
    push_neg at hf
    obtain ⟨x, _, i, hx⟩ := hf
    obtain ⟨B, hB, hBc⟩ := Finset.exists_subset_card_eq hx.le
    have hBsub : B ⊆ E := fun _ he => (mem_line.mp (hB he)).1
    have hcardgroup := hcost B hBsub x i hBc (fun _ he => (mem_line.mp (hB he)).2)
    let D := E \ B
    have hD : D ⊆ E := Finset.sdiff_subset
    have hDc : D.card + L = E.card := by
      simpa only [hBc] using Finset.card_sdiff_add_card_eq_card hBsub
    have hss : D ⊂ E := Finset.ssubset_iff_subset_ne.mpr ⟨hD, by
      intro he
      have he' := congrArg Finset.card he
      omega⟩
    obtain ⟨R, hR, hline, hweight⟩ := ih D hss (fun A hA => hcost A (hA.trans hD))
    refine ⟨R, hR.trans hD, hline, ?_⟩
    have hrCard := Finset.card_le_card hR
    have hdiff : E.card - R.card = L + (D.card - R.card) := by omega
    have hsum : (∑ e ∈ D, weight e) + ∑ e ∈ B, weight e = ∑ e ∈ E, weight e :=
      Finset.sum_sdiff hBsub
    rw [← hsum, hdiff, Nat.cast_add, mul_add]
    linarith

/-- Arithmetic-geometric mean in the form used for the three projection ratios. -/
theorem cube_root_prod_le (u : Fin 3 → ℝ) (hu : ∀ i, 0 ≤ u i) :
    (∏ i, u i) ^ (1 / 3 : ℝ) ≤ (∑ i, u i) / 3 := by
  have h := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := 1 / 3) (w₂ := 1 / 3) (w₃ := 1 / 3)
    (by norm_num) (by norm_num) (by norm_num)
    (hu 0) (hu 1) (hu 2) (by norm_num)
  rw [Fin.prod_univ_three, Fin.sum_univ_three, Real.mul_rpow (mul_nonneg (hu 0) (hu 1)) (hu 2),
    Real.mul_rpow (hu 0) (hu 1)]
  convert h using 1; ring

end Green88
