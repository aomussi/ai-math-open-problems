import Green88.GridCleaning
import Mathlib.Algebra.Order.Floor.Semiring

namespace Green88

private theorem floor_bounds {x : ℝ} (h : 1 ≤ x) :
    0 < ⌊x⌋₊ ∧ (⌊x⌋₊ : ℝ) ≤ x ∧ x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hle : (1 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast h)
  have hR : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hle
  exact ⟨hle, Nat.floor_le (by linarith), by linarith [Nat.lt_floor_add_one x]⟩

private theorem ceil_bounds {x : ℝ} (h : 1 ≤ x) :
    0 < ⌈x⌉₊ ∧ x ≤ (⌈x⌉₊ : ℝ) ∧ (⌈x⌉₊ : ℝ) ≤ 2 * x := by
  have hx := Nat.le_ceil x
  have hp : (0 : ℝ) < (⌈x⌉₊ : ℝ) := by linarith
  exact ⟨by exact_mod_cast hp, hx, by linarith [Nat.ceil_lt_add_one (show 0 ≤ x by linarith)]⟩

set_option maxHeartbeats 600000 in
/-- A sparse set of defects suffices for a power bound on the grid. -/
theorem sparse_grid_power {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hgrid : ∀ (k : ℕ) (S : Finset (Fin 3 → Fin k)), PairwiseComparable S →
      (S.card : ℝ) ≤ (k : ℝ) ^ (2 - δ)) {n : ℕ} (hn : 0 < n)
    {S : Finset (Fin 3 → ℕ)} (hr : InRectangle (fun _ => n) S)
    (hp : PairProjections S) (hB : ((badPairs S).card : ℝ) ≤ 72 * (n : ℝ) ^ (3 - δ)) :
    (S.card : ℝ) ≤ 2110 * (n : ℝ) ^ (2 - δ ^ 2 / 96) := by
  let N := (n : ℝ)
  have N1 : 1 ≤ N := by dsimp [N]; exact_mod_cast hn
  have Np : 0 < N := by linarith
  let k : ℕ := ⌊N ^ (δ / 16)⌋₊
  let K := (k : ℝ)
  have ⟨hk, kUpper, kLower⟩ : 0 < k ∧ K ≤ N ^ (δ / 16) ∧ N ^ (δ / 16) / 2 ≤ K :=
    floor_bounds (Real.one_le_rpow N1 (by linarith))
  have K1 : 1 ≤ K := by dsimp [K]; exact_mod_cast hk
  have Kp : 0 < K := by linarith
  have K_le_N : K ≤ N := kUpper.trans (by
    nth_rw 2 [← Real.rpow_one N]
    exact Real.rpow_le_rpow_of_exponent_le N1 (by linarith))
  let s : ℕ := ⌈N / K⌉₊
  have ⟨hs, sLower, sUpper⟩ : 0 < s ∧ N / K ≤ (s : ℝ) ∧ (s : ℝ) ≤ 2 * (N / K) :=
    ceil_bounds ((le_div_iff₀ Kp).mpr (by simpa using K_le_N))
  have hsCover : n ≤ k * s := by
    have := (div_le_iff₀ Kp).mp sLower
    dsimp [N, K] at this
    exact_mod_cast (by simpa [mul_comm] using this : (n : ℝ) ≤ (k : ℝ) * s)
  let u : ℕ := ⌈K ^ (δ / 3)⌉₊
  have ⟨hu, uLower, uUpper⟩ : 0 < u ∧ K ^ (δ / 3) ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * K ^ (δ / 3) :=
    ceil_bounds (Real.one_le_rpow K1 (by linarith))
  let t : ℕ := ⌈N ^ (1 - δ / 4)⌉₊
  have ⟨ht, tLower, tUpper⟩ :
      0 < t ∧ N ^ (1 - δ / 4) ≤ (t : ℝ) ∧ (t : ℝ) ≤ 2 * N ^ (1 - δ / 4) :=
    ceil_bounds (Real.one_le_rpow N1 (by linarith))
  let η : ℝ := K ^ (-(δ / 2))
  have ηp : 0 < η := Real.rpow_pos_of_pos Kp _
  let C : ℕ := ⌊K ^ (2 - δ)⌋₊
  have CUpper : (C : ℝ) ≤ K ^ (2 - δ) := Nat.floor_le (by positivity)
  have hC (W : Finset (Fin 3 → Fin k)) (hw : PairwiseComparable W) : W.card ≤ C :=
    Nat.le_floor (hgrid k W hw)
  obtain ⟨W, hsub, hchains, hLoss⟩ := clean_grid (s := s) hk ht hr hp
  have hW := coarse_grid_bound hk hs hsCover hu ηp hC
    (fun p hm => hr p (hsub hm)) (hp.mono hsub) hchains
  change (W.card : ℝ) ≤ (s : ℝ) ^ 2 *
    (6 * K ^ 2 * η ^ (1 / 3 : ℝ) + 2 * K ^ 2 / (η ^ (1 / 3 : ℝ) * u) + (3 * (u : ℝ) * C) / η) at hW
  have hroot : η ^ (1 / 3 : ℝ) = K ^ (-(δ / 6)) := by
    dsimp only [η]
    rw [← Real.rpow_mul Kp.le]
    congr 1
    ring
  have divLower : K ^ (δ / 6) ≤ η ^ (1 / 3 : ℝ) * u := by
    rw [hroot]
    calc
      _ = K ^ (-(δ / 6)) * K ^ (δ / 3) := by
        rw [← Real.rpow_add Kp]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left uLower (by positivity)
  have eLight : 6 * K ^ 2 * η ^ (1 / 3 : ℝ) = 6 * K ^ (2 - δ / 6) := by
    rw [hroot, mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add Kp]
    push_cast
    congr 2
  have eGroups : 2 * K ^ 2 / (η ^ (1 / 3 : ℝ) * u) ≤ 2 * K ^ (2 - δ / 6) := by
    calc
      _ ≤ 2 * K ^ 2 / K ^ (δ / 6) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) divLower
      _ = _ := by
        rw [mul_div_assoc, ← Real.rpow_natCast, ← Real.rpow_sub Kp]
        norm_num
  have eRemain : (3 * (u : ℝ) * C) / η ≤ 6 * K ^ (2 - δ / 6) := by
    calc
      _ ≤ (3 * (2 * K ^ (δ / 3)) * K ^ (2 - δ)) / η := by gcongr
      _ = 6 * ((K ^ (δ / 3) * K ^ (2 - δ)) / η) := by ring
      _ = _ := by
        dsimp only [η]
        rw [← Real.rpow_add Kp, ← Real.rpow_sub Kp]
        congr 2
        ring
  have hW' : (W.card : ℝ) ≤ 56 * N ^ 2 * K ^ (-(δ / 6)) := by
    have hc :
        6 * K ^ 2 * η ^ (1 / 3 : ℝ) + 2 * K ^ 2 / (η ^ (1 / 3 : ℝ) * u) +
          (3 * (u : ℝ) * C) / η ≤ 14 * K ^ (2 - δ / 6) := by linarith only [eLight, eGroups, eRemain]
    calc
      _ ≤ (s : ℝ) ^ 2 * (14 * K ^ (2 - δ / 6)) :=
        hW.trans (mul_le_mul_of_nonneg_left hc (by positivity))
      _ ≤ (2 * (N / K)) ^ 2 * (14 * K ^ (2 - δ / 6)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) sUpper _) (by positivity)
      _ = _ := by
        rw [show 2 - δ / 6 = 2 + -(δ / 6) by ring, Real.rpow_add Kp, Real.rpow_two]
        field_simp
        ring
  let γ := δ ^ 2 / 96
  have hγ : 0 < γ := div_pos (sq_pos_of_pos hδ) (by norm_num)
  have hkNeg : K ^ (-(δ / 6)) ≤ 2 * N ^ (-γ) := by
    have low : 0 < N ^ (δ / 16) / 2 := by positivity
    have h2 : (2 : ℝ) ^ (δ / 6) ≤ 2 := by
      calc
        _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = _ := Real.rpow_one _
    calc
      _ ≤ (N ^ (δ / 16) / 2) ^ (-(δ / 6)) :=
        Real.rpow_le_rpow_of_nonpos low kLower (by linarith)
      _ = N ^ (-γ) * (2 : ℝ) ^ (δ / 6) := by
        rw [Real.div_rpow (by positivity) (by norm_num : 0 ≤ (2 : ℝ)),
          ← Real.rpow_mul Np.le, Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ)), div_inv_eq_mul]
        congr 2
        dsimp [γ]
        ring
      _ ≤ _ := by rw [mul_comm 2]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hWfinal : (W.card : ℝ) ≤ 112 * N ^ (2 - γ) := by
    calc
      _ ≤ 56 * N ^ 2 * K ^ (-(δ / 6)) := hW'
      _ ≤ 56 * N ^ 2 * (2 * N ^ (-γ)) := mul_le_mul_of_nonneg_left hkNeg (by positivity)
      _ = 112 * (N ^ (2 : ℝ) * N ^ (-γ)) := by rw [Real.rpow_two]; ring
      _ = _ := by rw [← Real.rpow_add Np]; rfl
  have hThin : N * K ^ 2 * t ≤ 2 * N ^ (2 - δ / 8) := by
    calc
      _ ≤ N * (N ^ (δ / 16)) ^ (2 : ℕ) * (2 * N ^ (1 - δ / 4)) := by gcongr
      _ = 2 * (N ^ (1 : ℝ) * (N ^ (δ / 16)) ^ (2 : ℕ) * N ^ (1 - δ / 4)) := by
        rw [Real.rpow_one]; ring
      _ = _ := by
        rw [← Real.rpow_natCast (x := N ^ (δ / 16)), ← Real.rpow_mul Np.le,
          ← Real.rpow_add Np, ← Real.rpow_add Np]
        congr 2
        push_cast
        ring
  have hBad : N * (badPairs S).card / (t : ℝ) ^ 2 ≤ 72 * N ^ (2 - δ / 2) := by
    calc
      _ ≤ N * (72 * N ^ (3 - δ)) / (N ^ (1 - δ / 4)) ^ (2 : ℕ) := by
        have hN : N * ((badPairs S).card : ℝ) ≤ N * (72 * N ^ (3 - δ)) :=
          mul_le_mul_of_nonneg_left hB Np.le
        apply div_le_div_of_nonneg_left (show 0 ≤ N * ((badPairs S).card : ℝ) by positivity)
          (show 0 < (N ^ (1 - δ / 4)) ^ (2 : ℕ) by positivity)
          (pow_le_pow_left₀ (by positivity) tLower _) |>.trans
        exact div_le_div_of_nonneg_right hN (by positivity)
      _ = 72 * (N ^ (1 : ℝ) * N ^ (3 - δ) / (N ^ (1 - δ / 4)) ^ (2 : ℕ)) := by
        rw [Real.rpow_one]; ring
      _ = _ := by
        rw [← Real.rpow_natCast (x := N ^ (1 - δ / 4)), ← Real.rpow_mul Np.le,
          ← Real.rpow_add Np, ← Real.rpow_sub Np]
        congr 2
        push_cast
        ring
  have γle : γ ≤ δ / 8 := by
    dsimp [γ]
    nlinarith only [mul_nonneg hδ.le (sub_nonneg.mpr hδ'), hδ]
  have hThin' : N * K ^ 2 * t ≤ 2 * N ^ (2 - γ) :=
    hThin.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le N1 (by linarith)) (by norm_num))
  have hBad' : N * (badPairs S).card / (t : ℝ) ^ 2 ≤ 72 * N ^ (2 - γ) :=
    hBad.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le N1 (by linarith)) (by norm_num))
  dsimp only [N, K] at hThin' hBad' hWfinal
  change (S.card : ℝ) ≤ 2110 * (n : ℝ) ^ (2 - γ)
  linarith only [hLoss, hThin', hBad', hWfinal]

end Green88
