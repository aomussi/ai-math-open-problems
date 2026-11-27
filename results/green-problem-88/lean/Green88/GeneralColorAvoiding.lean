import Green88.GridPower
import Green88.TournamentGrid
import Green88.TournamentStrict

namespace Green88
namespace ColoredTournament

open DirectedPath

/-- Uniform power saving on the order in terms of the longest color-avoiding path. -/
theorem general_path_bound :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧
      ∀ (m : ℕ) (T : ColoredTournament (Fin m)), 0 < m →
        (m : ℝ) ≤ 3000 * (T.maxPathLength : ℝ) ^ (2 - γ) := by
  obtain ⟨θ, hθ, hθ', rect⟩ := rectangular_exponent
  let δ := 2 - 3 * θ
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ' : δ ≤ 1 / 2 := by dsimp [δ]; linarith
  let γ := δ ^ 2 / 96
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγ' : γ < 1 := by dsimp [γ]; nlinarith
  refine ⟨γ, hγ, hγ', ?_⟩
  intro m T hm
  let n := T.maxPathLength
  have hn : 0 < n := T.maxPathLength_pos hm
  have grid (k : ℕ) (S : Finset (Fin 3 → Fin k)) (hS : PairwiseComparable S) :
      (S.card : ℝ) ≤ (k : ℝ) ^ (2 - δ) := by
    have he : 2 - δ = 3 * θ := by dsimp [δ]; ring
    rw [he]
    exact cube_power_of_rectangle rect k S hS
  let C : ℕ := ⌊(n : ℝ) ^ (2 - δ)⌋₊
  have C_le : (C : ℝ) ≤ (n : ℝ) ^ (2 - δ) := Nat.floor_le (by positivity)
  have gridCap (U : Finset (Fin 3 → ℕ)) (hU : PairwiseComparable U)
      (hr : InRectangle (fun _ => n) U) : U.card ≤ C := by
    apply Nat.le_floor
    have h := rect _ U hU hr
    rw [volume, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow,
      ← Real.rpow_natCast_mul (Nat.cast_nonneg n), Nat.cast_ofNat] at h
    simpa only [show 2 - δ = 3 * θ by dsimp [δ]; ring] using h
  have cap (i : Fin 3) : PathBound (T.avoid i) n :=
    fun l hl => (longest_bound _ _ hl).trans (T.pathLength_le_max i)
  obtain ⟨S, hS, hp, hcard, hB⟩ := T.sparse_grid hn cap gridCap
  have hBR : ((badPairs S).card : ℝ) ≤ 72 * (n : ℝ) ^ (3 - δ) := by
    calc
      _ ≤ 72 * (n : ℝ) * C := by exact_mod_cast hB
      _ ≤ 72 * (n : ℝ) * (n : ℝ) ^ (2 - δ) :=
        mul_le_mul_of_nonneg_left C_le (by positivity)
      _ = _ := by
        nth_rw 1 [← Real.rpow_one (n : ℝ)]
        rw [mul_assoc, ← Real.rpow_add (show (0 : ℝ) < n by exact_mod_cast hn)]
        congr 2
        ring
  have h := sparse_grid_power hδ hδ' grid hn hS hp hBR
  have hcardR : 3 * (m : ℝ) ≤ 4 * S.card := by exact_mod_cast hcard
  have termNonneg : 0 ≤ (n : ℝ) ^ (2 - γ) := by positivity
  dsimp only [n] at h hcardR termNonneg
  linarith

private theorem absorb_prefactor {γ : ℝ} (hγ : 0 < γ) (hγ' : γ < 1) :
    ∃ d : ℝ, 0 < d ∧ d < 1 ∧ ∀ m L : ℕ, 0 < L →
      (1 < m → m < L ^ 2) → (m : ℝ) ≤ 3000 * (L : ℝ) ^ (2 - γ) →
      (m : ℝ) ≤ (L : ℝ) ^ (2 - d) := by
  let M : ℝ := (3000 : ℝ) ^ ((γ / 2)⁻¹) + 2
  have hM : 1 < M := by
    dsimp only [M]
    linarith [Real.rpow_nonneg (show (0 : ℝ) ≤ 3000 by norm_num) ((γ / 2)⁻¹)]
  have hMp : 0 < M := by linarith
  let R : ℝ := 1 + (M ^ 2)⁻¹
  have hR : 1 < R := by
    dsimp only [R]
    exact lt_add_of_pos_right _ (inv_pos.mpr (sq_pos_of_pos hMp))
  let β : ℝ := Real.log R / Real.log M
  have βpos : 0 < β := div_pos (Real.log_pos hR) (Real.log_pos hM)
  have hβ : M ^ β = R := by
    have he : Real.log M * (Real.log R / Real.log M) = Real.log R := by
      field_simp [(Real.log_pos hM).ne']
    rw [Real.rpow_def_of_pos hMp]
    dsimp only [β]
    rw [he, Real.exp_log (by linarith : 0 < R)]
  let d := min (γ / 2) β
  have hd : 0 < d := lt_min (by linarith) βpos
  have hdγ : d ≤ γ / 2 := min_le_left _ _
  have hdβ : d ≤ β := min_le_right _ _
  refine ⟨d, hd, by linarith, ?_⟩
  intro m L hL hstrict hbound
  let x := (L : ℝ)
  have x1 : 1 ≤ x := by dsimp [x]; exact_mod_cast hL
  have xp : 0 < x := by linarith
  by_cases hm : m ≤ 1
  · exact (show (m : ℝ) ≤ 1 by exact_mod_cast hm).trans (Real.one_le_rpow x1 (by linarith))
  by_cases big : M ≤ x
  · have hlarge : (3000 : ℝ) ≤ x ^ (γ / 2) := by
      calc
        _ = ((3000 : ℝ) ^ ((γ / 2)⁻¹)) ^ (γ / 2) := by
          rw [Real.rpow_inv_rpow (by norm_num) (by linarith : γ / 2 ≠ 0)]
        _ ≤ x ^ (γ / 2) := Real.rpow_le_rpow (by positivity) (by dsimp [M] at big; linarith)
          (by linarith)
    calc
      _ ≤ 3000 * x ^ (2 - γ) := hbound
      _ ≤ x ^ (γ / 2) * x ^ (2 - γ) := mul_le_mul_of_nonneg_right hlarge (by positivity)
      _ = x ^ (2 - γ / 2) := by rw [← Real.rpow_add xp]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le x1 (by linarith)
  · have small : x ≤ M := le_of_not_ge big
    have hpow : x ^ d ≤ R :=
      (Real.rpow_le_rpow xp.le small hd.le).trans
        ((Real.rpow_le_rpow_of_exponent_le hM.le hdβ).trans_eq hβ)
    have hstrictNat : m + 1 ≤ L ^ 2 := hstrict (by omega)
    have hstrictReal : (m : ℝ) + 1 ≤ x ^ 2 := by dsimp [x]; exact_mod_cast hstrictNat
    have hx2 : x ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ xp.le small _
    have hmr : (m : ℝ) ≤ M ^ 2 := by linarith
    have hρ : (m : ℝ) * (M ^ 2)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv]
      exact (div_le_one (sq_pos_of_pos hMp)).mpr hmr
    have hmMul : (m : ℝ) * x ^ d ≤ x ^ 2 := calc
      _ ≤ (m : ℝ) * R := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (m : ℝ) + (m : ℝ) * (M ^ 2)⁻¹ := by dsimp [R]; ring
      _ ≤ _ := by linarith
    have hdiv := (le_div_iff₀ (Real.rpow_pos_of_pos xp d)).mpr hmMul
    rw [← Real.rpow_two x, ← Real.rpow_sub xp] at hdiv
    exact hdiv

/-- The fixed power saving over the square-root bound holds for every three-colored
tournament, and the path consists of distinct vertices. -/
theorem general_color_avoiding_power :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (m : ℕ) (T : ColoredTournament (Fin m)), 0 < m →
      ∃ (i : Fin 3) (l : List (Fin m)), DirectedPath (T.avoid i) l ∧
        (m : ℝ) ^ (1 / 2 + ε) ≤ (l.length : ℝ) := by
  obtain ⟨γ, hγ, hγ', hbound⟩ := general_path_bound
  obtain ⟨d, hd, hd', remove⟩ := absorb_prefactor hγ hγ'
  refine ⟨1 / (2 - d) - 1 / 2, ?_, ?_⟩
  · have hp : 0 < 2 - d := by linarith
    have h : (1 / 2 : ℝ) < 1 / (2 - d) := (lt_div_iff₀ hp).mpr (by linarith)
    linarith
  intro m T hm
  let L := T.maxPathLength
  have Lpos : 0 < L := T.maxPathLength_pos hm
  have strict (h : 1 < m) : m < L ^ 2 :=
    T.card_lt_path_square (T.two_le_maxPathLength h)
      (fun i l hl => (longest_bound _ _ hl).trans (T.pathLength_le_max i))
  have h := remove m L Lpos strict (hbound m T hm)
  have xR : (0 : ℝ) ≤ L := by positivity
  have dpos : 0 < (2 : ℝ) - d := by linarith
  have root : (m : ℝ) ^ (1 / (2 - d)) ≤ (L : ℝ) := by
    calc
      _ ≤ ((L : ℝ) ^ (2 - d)) ^ (1 / (2 - d)) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
      _ = _ := by rw [one_div, Real.rpow_rpow_inv xR dpos.ne']
  obtain ⟨i, hi, hi'⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3)) T.pathLength
    ⟨0, Finset.mem_univ _⟩
  have hiL : L ≤ T.pathLength i := Finset.sup_le fun j hj => hi' j hj
  obtain ⟨l, hl, eq⟩ := longest_attained (T.avoid i)
  refine ⟨i, l, hl, ?_⟩
  rw [show (1/2 : ℝ) + (1 / (2 - d) - 1/2) = 1 / (2 - d) by ring]
  exact root.trans (by exact_mod_cast (show L ≤ l.length from hiL.trans_eq eq.symm))

#print axioms general_path_bound
#print axioms general_color_avoiding_power

end ColoredTournament
end Green88
