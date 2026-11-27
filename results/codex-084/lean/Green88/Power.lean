import Green88.Budget
import Green88.Rectangle
import Mathlib.Tactic.GCongr

namespace Green88

open scoped BigOperators

noncomputable def eta : ℝ := (2 : ℝ) ^ (-36 : ℝ)
def groupSize : ℕ := 2 ^ 54

theorem eta_pos : 0 < eta := by unfold eta; positivity
theorem eta_le_one : eta ≤ 1 := by
  unfold eta
  simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (by norm_num : (-36 : ℝ) ≤ 0)

theorem groupSize_pos : 0 < groupSize := by unfold groupSize; positivity

theorem light_constant {θ : ℝ} (hθ : 1 / 2 ≤ θ) :
    2 * eta ^ (θ - 1 / 3) ≤ 1 / 32 := by
  rw [eta, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (show -36 * (θ - 1 / 3) ≤ (-6 : ℝ) by linarith)
  have e : (2 : ℝ) ^ (-6 : ℝ) = 1 / 64 := by
    rw [show (-6 : ℝ) = -(6 : ℝ) by norm_num, Real.rpow_neg (by norm_num)]
    have e : (2 : ℝ) ^ (6 : ℝ) = (2 : ℝ) ^ (6 : ℕ) := Real.rpow_natCast 2 6
    rw [e]
    norm_num
  rw [e] at h
  linarith

theorem line_constant {θ : ℝ} (hθ : θ ≤ 2 / 3) :
    2 * eta ^ (-(1 / 3 : ℝ)) * (groupSize : ℝ) ^ (θ - 1) ≤ 1 / 32 := by
  have he : eta ^ (-(1 / 3 : ℝ)) = 2 ^ (12 : ℕ) := by
    rw [eta, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      show (-36 : ℝ) * -(1 / 3) = 12 by norm_num]
    exact Real.rpow_natCast 2 12
  have hg : (groupSize : ℝ) = (2 : ℝ) ^ (54 : ℝ) := by
    rw [groupSize, Nat.cast_pow]
    exact (Real.rpow_natCast 2 54).symm
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (show 54 * (θ - 1) ≤ (-18 : ℝ) by linarith)
  have e : (2 : ℝ) ^ (-18 : ℝ) = 1 / 262144 := by
    rw [show (-18 : ℝ) = -(18 : ℝ) by norm_num, Real.rpow_neg (by norm_num)]
    have e : (2 : ℝ) ^ (18 : ℝ) = (2 : ℝ) ^ (18 : ℕ) := Real.rpow_natCast 2 18
    rw [e]
    norm_num
  rw [e] at h
  rw [he, hg, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num at *
  linarith

theorem exists_exponent {k : ℕ} (hk : groupSize ≤ k) :
    ∃ θ : ℝ, 1 / 2 ≤ θ ∧ θ < 2 / 3 ∧ (k : ℝ) ^ (2 - 3 * θ) = 2 := by
  have hk2 : (2 : ℝ) ^ (2 : ℕ) ≤ k := by
    have h : 4 ≤ k := (by decide : 4 ≤ groupSize).trans hk
    exact_mod_cast h
  have hk1 : (1 : ℝ) < k := (by norm_num : (1 : ℝ) < 2 ^ (2 : ℕ)).trans_le hk2
  have hl := Real.log_pos hk1
  let d := Real.log 2 / Real.log k
  have hd : 0 < d := div_pos (Real.log_pos (by norm_num)) hl
  have hd' : d ≤ 1 / 2 := by
    apply (div_le_iff₀ hl).2
    have h := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ (2 : ℕ)) hk2
    rw [Real.log_pow] at h
    norm_num at h
    linarith
  refine ⟨(2 - d) / 3, by linarith, by linarith, ?_⟩
  rw [show 2 - 3 * ((2 - d) / 3) = d by ring,
    Real.rpow_def_of_pos (zero_lt_one.trans hk1)]
  have h : Real.log (k : ℝ) * d = Real.log 2 := by
    dsimp [d]
    field_simp
  rw [h, Real.exp_log (by norm_num)]

/-- A sorted box with a short side satisfies the bound using two-coordinate injectivity. -/
theorem small_sorted {a b c k : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hak : a ≤ k) {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ' : θ ≤ 2 / 3)
    (hk : k ^ (2 - 3 * θ) = 2) : a * b ≤ 2 * (a * b * c) ^ θ := by
  have hb := ha.trans_le hab
  have hc := hb.trans_le hbc
  have h₁ : a ^ (2 - 3 * θ) ≤ 2 := by
    exact (Real.rpow_le_rpow ha.le hak (show 0 ≤ 2 - 3 * θ by linarith)).trans_eq hk
  have h₂ := Real.rpow_le_rpow ha.le hab (show 0 ≤ 2 * θ - 1 by linarith)
  have h₃ := Real.rpow_le_rpow hb.le hbc (show 0 ≤ θ by linarith)
  rw [Real.mul_rpow (by positivity) hc.le, Real.mul_rpow ha.le hb.le]
  calc
    a * b = (a ^ (2 - 3 * θ) * a ^ θ * a ^ (2 * θ - 1)) * b := by
      rw [← Real.rpow_add ha, ← Real.rpow_add ha,
        show 2 - 3 * θ + θ + (2 * θ - 1) = 1 by ring, Real.rpow_one]
    _ ≤ (2 * a ^ θ * b ^ (2 * θ - 1)) * b := by gcongr
    _ = 2 * a ^ θ * b ^ θ * b ^ θ := by
      calc
        _ = 2 * a ^ θ * (b ^ (2 * θ - 1) * b ^ (1 : ℝ)) := by
          rw [Real.rpow_one]; ring
        _ = 2 * a ^ θ * (b ^ θ * b ^ θ) := by
          rw [← Real.rpow_add hb, ← Real.rpow_add hb]
          congr 2
          ring
        _ = _ := by ring
    _ ≤ 2 * (a ^ θ * b ^ θ * c ^ θ) := by
      rw [← mul_assoc, ← mul_assoc]
      gcongr

/-- The loss from rounding all three interval widths up is absorbed by the slack. -/
theorem rounded_volume {k V W θ : ℝ} (hk : 0 < k) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 2 / 3) (hwidth : V * k ^ 3 ≤ 8 * W)
    (hpow : k ^ (2 - 3 * θ) = 2) :
    V ^ θ * k ^ 2 ≤ 8 * W ^ θ := by
  have h := Real.rpow_le_rpow (show 0 ≤ V * k ^ (3 : ℕ) by positivity) hwidth hθ
  rw [Real.mul_rpow hV (by positivity), Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hW,
    ← Real.rpow_natCast_mul hk.le, Nat.cast_ofNat] at h
  have h8 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 8) hθ'
  have h84 : (8 : ℝ) ^ (2 / 3 : ℝ) = 4 := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by
      have e : (2 : ℝ) ^ (3 : ℝ) = (2 : ℝ) ^ (3 : ℕ) := Real.rpow_natCast 2 3
      rw [e]
      norm_num,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      show (3 : ℝ) * (2 / 3) = 2 by norm_num]
    have e : (2 : ℝ) ^ (2 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := Real.rpow_natCast 2 2
    rw [e]
    norm_num
  rw [h84] at h8
  have h' : V ^ θ * k ^ (3 * θ) ≤ 4 * W ^ θ :=
    h.trans (mul_le_mul_of_nonneg_right h8 (Real.rpow_nonneg hW _))
  calc
    V ^ θ * k ^ 2 = (V ^ θ * k ^ (3 * θ)) * k ^ (2 - 3 * θ) := by
      rw [mul_assoc, ← Real.rpow_add hk, show 3 * θ + (2 - 3 * θ) = 2 by ring]
      exact congrArg (V ^ θ * ·) (Real.rpow_natCast k 2).symm
    _ ≤ 8 * W ^ θ := by rw [hpow]; linarith

end Green88
