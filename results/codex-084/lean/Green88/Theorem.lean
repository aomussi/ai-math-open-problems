import Green88.Induction
import Green88.Qualitative
import Green88.Tensor
import Mathlib.Algebra.Order.Floor.Semiring

namespace Green88

open scoped BigOperators

private def castTriple (n : ℕ) : (Fin 3 → Fin n) ↪ (Fin 3 → ℕ) where
  toFun x i := (x i).val
  inj' := fun _ _ e => funext fun i => Fin.ext (congrFun e i)

private theorem mapped_comparable {n : ℕ} {S : Finset (Fin 3 → Fin n)}
    (hS : PairwiseComparable S) : PairwiseComparable (S.map (castTriple n)) := by
  intro x hx y hy hne
  change x ∈ S.map (castTriple n) at hx
  change y ∈ S.map (castTriple n) at hy
  obtain ⟨p, hp, ep⟩ := Finset.mem_map.mp hx
  obtain ⟨q, hq, eq⟩ := Finset.mem_map.mp hy
  subst x
  subst y
  have hne' : p ≠ q := fun e => hne (congrArg (castTriple n) e)
  rcases hS hp hq hne' with ⟨i, j, hij, hi, hj⟩ | ⟨i, j, hij, hi, hj⟩
  · exact Or.inl ⟨i, j, hij, hi, hj⟩
  · exact Or.inr ⟨i, j, hij, hi, hj⟩

/-- Ben Green's Problem 88. The exponent saving is uniform over all sizes and sets. -/
theorem green_88 :
    ∃ δ > (0 : ℝ), ∀ (N : ℕ) (S : Finset (Fin 3 → Fin N)),
      PairwiseComparable S → (S.card : ℝ) ≤ (N : ℝ) ^ (2 - δ) := by
  classical
  let μ : ℝ := eta / (96 * (groupSize : ℝ))
  have hL : (0 : ℝ) < groupSize := by exact_mod_cast groupSize_pos
  have hμ : 0 < μ := div_pos eta_pos (by positivity)
  obtain ⟨K, hK⟩ := qualitative μ hμ
  let k := max K groupSize
  have hKk : K ≤ k := le_max_left _ _
  have hLk : groupSize ≤ k := le_max_right _ _
  have hk : 2 ≤ k := (by decide : 2 ≤ groupSize).trans hLk
  let C : ℕ := ⌊μ * (k : ℝ) ^ 2⌋₊
  have hC (S : Finset (Fin 3 → Fin k)) (hS : PairwiseComparable S) : S.card ≤ C :=
    Nat.le_floor (hK k hKk S hS)
  have hCsmall : 3 * (groupSize : ℝ) * C ≤ eta * ((k : ℝ) ^ 2 / 32) := by
    have hLf : (groupSize : ℝ) ≠ 0 := hL.ne'
    calc
      _ ≤ 3 * (groupSize : ℝ) * (μ * (k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by positivity)
      _ = _ := by dsimp [μ]; field_simp; ring
  obtain ⟨θ, hθ, hθ', hpow⟩ := exists_exponent hLk
  refine ⟨2 - 3 * θ, by linarith, remove_prefactor (C := 2) ?_⟩
  intro n S hS
  let T := S.map (castTriple n)
  have hRect : InRectangle (fun _ => n) T := by
    intro x hx i
    obtain ⟨z, _, rfl⟩ := Finset.mem_map.mp hx
    exact (z i).isLt
  have h := rectangular hk hθ hθ' hpow hC hCsmall _ T (mapped_comparable hS) hRect
  change ((S.map (castTriple n)).card : ℝ) ≤ 2 * (volume (fun _ => n) : ℝ) ^ θ at h
  rw [Finset.card_map, volume_cast, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.rpow_natCast_mul (Nat.cast_nonneg n), Nat.cast_ofNat] at h
  simpa only [show 2 - (2 - 3 * θ) = 3 * θ by ring] using h

#print axioms green_88

end Green88
