import Green88.Coarse
import Green88.Power

namespace Green88

open scoped BigOperators

def volume (r : Fin 3 → ℕ) : ℕ := ∏ i, r i

theorem volume_cast (r : Fin 3 → ℕ) : (volume r : ℝ) = ∏ i, (r i : ℝ) := by
  simp [volume]

private theorem sorted_axes (r : Fin 3 → ℕ) :
    ∃ i j l : Fin 3, i ≠ j ∧ r i ≤ r j ∧ r j ≤ r l ∧
      (∀ t, r i ≤ r t) ∧ volume r = r i * r j * r l := by
  have ordered (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
      (h₁ : r i ≤ r j) (h₂ : r j ≤ r l) : ∀ t, r i ≤ r t := by
    intro t
    by_cases e : t = i
    · simp [e]
    by_cases e' : t = j
    · simpa [e'] using h₁
    rw [fin3_eq_of_ne hij e e' hil.symm hjl.symm]
    exact h₁.trans h₂
  have a := le_total (r 0) (r 1)
  have b := le_total (r 0) (r 2)
  have c := le_total (r 1) (r 2)
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c
  all_goals first
    | exact ⟨0, 1, 2, by decide, a, c, ordered 0 1 2 (by decide) (by decide) (by decide) a c,
        by simp [volume, Fin.prod_univ_three]⟩
    | exact ⟨0, 2, 1, by decide, b, c, ordered 0 2 1 (by decide) (by decide) (by decide) b c,
        by simp only [volume, Fin.prod_univ_three]; ac_rfl⟩
    | exact ⟨1, 0, 2, by decide, a, b, ordered 1 0 2 (by decide) (by decide) (by decide) a b,
        by simp only [volume, Fin.prod_univ_three]; ac_rfl⟩
    | exact ⟨1, 2, 0, by decide, c, b, ordered 1 2 0 (by decide) (by decide) (by decide) c b,
        by simp only [volume, Fin.prod_univ_three]; ac_rfl⟩
    | exact ⟨2, 0, 1, by decide, b, a, ordered 2 0 1 (by decide) (by decide) (by decide) b a,
        by simp only [volume, Fin.prod_univ_three]; ac_rfl⟩
    | exact ⟨2, 1, 0, by decide, c, a, ordered 2 1 0 (by decide) (by decide) (by decide) c a,
        by simp only [volume, Fin.prod_univ_three]; ac_rfl⟩

private theorem width_bounds {k n : ℕ} (hk : 2 ≤ k) (hn : k < n) :
    n ≤ k * (n / k + 1) ∧ n / k + 1 < n ∧ (n / k + 1) * k ≤ 2 * n := by
  have hk0 : 0 < k := by omega
  have hm := Nat.mod_lt n hk0
  have hd := Nat.mod_add_div n k
  have hle := Nat.div_mul_le_self n k
  have hh : n / k ≤ n / 2 := Nat.div_le_div_left hk (by decide)
  refine ⟨?_, by omega, ?_⟩
  · rw [Nat.mul_add, Nat.mul_one]
    omega
  · rw [Nat.add_mul, Nat.one_mul]
    omega

private theorem group_volume {k : ℕ} {hk : 0 < k} {w r : Fin 3 → ℕ}
    (hw : ∀ i, 0 < w i) (hrw : ∀ i, r i ≤ k * w i)
    {S : Finset (Fin 3 → ℕ)} (hr : InRectangle r S)
    {B : Finset (Fin 3 → Fin k)} {x : Fin 3 → Fin k} {i : Fin 3}
    (hB : ∀ e ∈ B, ∀ j : Fin 3, j ≠ i → x j = e j) :
    volume (fun j => (projection (bunch hk w S B) j).card) ≤ B.card * volume w := by
  unfold volume
  calc
    _ ≤ ∏ j : Fin 3, (if j = i then B.card * w j else w j) :=
      Finset.prod_le_prod' fun j _ => bunch_projection_le hw hrw hr hB j
    _ = _ := by
      have he (j : Fin 3) : (if j = i then B.card * w j else w j) =
          (if j = i then B.card else 1) * w j := by split_ifs <;> simp
      simp_rw [he, Finset.prod_mul_distrib]
      congr 1
      simpa only [Finset.mem_univ, if_true] using
        Finset.prod_ite_eq' Finset.univ i (fun _ => B.card)

private theorem sum_light {α : Type*} (E : Finset α) (p q : α → ℝ) {A K θ : ℝ}
    (hA : 0 ≤ A) (hθ : 1 / 2 ≤ θ) (hp : ∀ e, 0 ≤ p e)
    (hq : ∀ e, q e ≤ A * (p e) ^ θ)
    (hsmall : ∀ e ∈ E, p e ≤ eta) (hsum : (∑ e ∈ E, (p e) ^ (1 / 3 : ℝ)) ≤ 2 * K) :
    (∑ e ∈ E, q e) ≤ A * (K / 32) := by
  have he : 0 ≤ θ - 1 / 3 := by linarith
  calc
    _ ≤ ∑ e ∈ E, (A * eta ^ (θ - 1 / 3)) * (p e) ^ (1 / 3 : ℝ) := by
      apply Finset.sum_le_sum
      intro e h
      refine (hq e).trans ?_
      have hf := Real.rpow_of_add_eq (hp e) (show θ ≠ 0 by linarith)
        (show (θ - 1 / 3) + 1 / 3 = θ by ring)
      rw [hf, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hp e) (hsmall e h) he)
          (Real.rpow_nonneg (hp e) _)) hA
    _ ≤ (A * eta ^ (θ - 1 / 3)) * (2 * K) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hsum (mul_nonneg hA (Real.rpow_nonneg eta_pos.le _))
    _ = (A * K) * (2 * eta ^ (θ - 1 / 3)) := by ring
    _ ≤ A * (K / 32) := by
      have hK : 0 ≤ K := by
        have hnn : 0 ≤ ∑ e ∈ E, (p e) ^ (1 / 3 : ℝ) :=
          Finset.sum_nonneg fun e _ => Real.rpow_nonneg (hp e) _
        linarith
      calc
        _ ≤ (A * K) * (1 / 32) :=
          mul_le_mul_of_nonneg_left (light_constant hθ) (mul_nonneg hA hK)
        _ = _ := by ring

private theorem heavy_card {α : Type*} (E : Finset α) (p : α → ℝ) {K : ℝ}
    (hsum : (∑ e ∈ E, (p e) ^ (1 / 3 : ℝ)) ≤ 2 * K)
    (hheavy : ∀ e ∈ E, eta ≤ p e) :
    (E.card : ℝ) ≤ 2 * eta ^ (-(1 / 3 : ℝ)) * K := by
  have he : 0 < eta ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos eta_pos _
  have h : (E.card : ℝ) * eta ^ (1 / 3 : ℝ) ≤ 2 * K := by
    calc
      _ = ∑ _e ∈ E, eta ^ (1 / 3 : ℝ) := by simp [nsmul_eq_mul]
      _ ≤ ∑ e ∈ E, (p e) ^ (1 / 3 : ℝ) :=
        Finset.sum_le_sum fun e h => Real.rpow_le_rpow eta_pos.le (hheavy e h) (by norm_num)
      _ ≤ _ := hsum
  have h' := (le_div_iff₀ he).mpr h
  convert h' using 1
  rw [Real.rpow_neg eta_pos.le, div_eq_mul_inv]
  ring

private theorem rectangular_step {k C : ℕ} {r : Fin 3 → ℕ}
    (hk : 2 ≤ k) (hrk : ∀ i, k < r i) {θ : ℝ}
    (hθ : 1 / 2 ≤ θ) (hθ' : θ < 2 / 3) (hpow : (k : ℝ) ^ (2 - 3 * θ) = 2)
    (hC : ∀ T : Finset (Fin 3 → Fin k), PairwiseComparable T → T.card ≤ C)
    (hCsmall : (3 * (groupSize : ℝ) * C) ≤ eta * ((k : ℝ) ^ 2 / 32))
    {S : Finset (Fin 3 → ℕ)} (hS : PairwiseComparable S) (hr : InRectangle r S)
    (ih : ∀ (t : Fin 3 → ℕ) (T : Finset (Fin 3 → ℕ)), volume t < volume r →
      PairwiseComparable T → InRectangle t T → (T.card : ℝ) ≤ 2 * (volume t : ℝ) ^ θ) :
    (S.card : ℝ) ≤ 2 * (volume r : ℝ) ^ θ := by
  classical
  have hk0 : 0 < k := by omega
  have hθ0 : 0 ≤ θ := by linarith
  let w (i : Fin 3) := r i / k + 1
  have hw (i : Fin 3) : 0 < w i := Nat.zero_lt_succ _
  have hrw (i : Fin 3) : r i ≤ k * w i := (width_bounds hk (hrk i)).1
  have hwr (i : Fin 3) : w i < r i := (width_bounds hk (hrk i)).2.1
  have hwk (i : Fin 3) : w i * k ≤ 2 * r i := (width_bounds hk (hrk i)).2.2
  let V : ℝ := volume w
  have hV : 0 < V := by
    rw [show V = (volume w : ℝ) by rfl, volume_cast]
    exact Finset.prod_pos fun i _ => by exact_mod_cast hw i
  let X := Fin 3 → Fin k
  let box (e : X) := cell hk0 w S e
  let weight (e : X) : ℝ := (box e).card
  let u (e : X) (i : Fin 3) : ℝ := ((projection (box e) i).card : ℝ) / (w i : ℝ)
  let p (e : X) := ∏ i, u e i
  let A : ℝ := 2 * V ^ θ
  let K : ℝ := (k : ℝ) ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hu (e : X) (i : Fin 3) : 0 ≤ u e i := by dsimp [u]; positivity
  have hu1 (e : X) (i : Fin 3) : u e i ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hw i)).2
    exact_mod_cast cell_projection_le hw hrw hr e i
  have hp (e : X) : 0 ≤ p e := Finset.prod_nonneg fun i _ => hu e i
  have hp1 (e : X) : p e ≤ 1 := Finset.prod_le_one (fun i _ => hu e i) (fun i _ => hu1 e i)
  have hind (T : Finset (Fin 3 → ℕ)) (hTS : T ⊆ S)
      (hle : ∀ i, (projection T i).card ≤ r i)
      (hs : ∃ i, (projection T i).card < r i) :
      (T.card : ℝ) ≤ 2 * (volume fun i => (projection T i).card : ℝ) ^ θ := by
    obtain rfl | ⟨x, hx⟩ := T.eq_empty_or_nonempty
    · simpa only [Finset.card_empty, Nat.cast_zero] using
        (show 0 ≤ 2 * (volume fun i => (projection (∅ : Finset (Fin 3 → ℕ)) i).card : ℝ) ^ θ by positivity)
    have htpos (i : Fin 3) : 0 < (projection T i).card :=
      Finset.card_pos.mpr ⟨x i, mem_projection.mpr ⟨x, hx, rfl⟩⟩
    have hvlt : volume (fun i => (projection T i).card) < volume r :=
      Finset.prod_lt_prod (fun i _ => htpos i) (fun i _ => hle i)
        (by obtain ⟨i, hi⟩ := hs; exact ⟨i, Finset.mem_univ _, hi⟩)
    obtain ⟨U, hU, hUr, hUc⟩ := compress (comparable_subset hTS hS)
    simpa only [hUc] using ih _ U hvlt hU hUr
  have hweight (e : X) : weight e ≤ A * (p e) ^ θ := by
    have hpr (i : Fin 3) : (projection (box e) i).card < r i :=
      (cell_projection_le hw hrw hr e i).trans_lt (hwr i)
    have h := hind (box e) (cell_subset hk0 w S e) (fun i => (hpr i).le) ⟨0, hpr 0⟩
    have hpV : (volume fun i => (projection (box e) i).card : ℝ) = V * p e := by
      dsimp [V, p, u]
      rw [volume_cast, volume_cast, Finset.prod_div_distrib]
      field_simp
    rw [hpV, Real.mul_rpow hV.le (hp e), ← mul_assoc] at h
    exact h
  have weight_le (e : X) : weight e ≤ A := by
    have h := Real.rpow_le_rpow (hp e) (hp1 e) hθ0
    rw [Real.one_rpow] at h
    exact (hweight e).trans (by simpa using mul_le_mul_of_nonneg_left h hA)
  have hsum_axis (i : Fin 3) : (∑ e : X, u e i) ≤ 2 * K := by
    dsimp [u]
    rw [← Finset.sum_div]
    apply (div_le_iff₀ (show (0 : ℝ) < w i by exact_mod_cast hw i)).mpr
    have hu := sum_projection_bound hk0 w hS hr i
    have hwr' : (r i : ℝ) ≤ (k : ℝ) * w i := by exact_mod_cast hrw i
    calc
      _ ≤ (r i : ℝ) * (2 * k) := hu
      _ ≤ ((k : ℝ) * w i) * (2 * k) :=
        mul_le_mul_of_nonneg_right hwr' (by positivity)
      _ = 2 * K * (w i : ℝ) := by dsimp [K]; ring
  have hpsum : (∑ e : X, (p e) ^ (1 / 3 : ℝ)) ≤ 2 * K := by
    calc
      _ ≤ ∑ e : X, (∑ i, u e i) / 3 := Finset.sum_le_sum fun e _ => cube_root_prod_le _ (hu e)
      _ = (∑ i, ∑ e : X, u e i) / 3 := by rw [← Finset.sum_div, Finset.sum_comm]
      _ ≤ (∑ _i : Fin 3, 2 * K) / 3 :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => hsum_axis i) (by norm_num)
      _ = _ := by simp [nsmul_eq_mul]
  let H : Finset X := Finset.univ.filter fun e => eta < p e
  let J : Finset X := Finset.univ \ H
  have hpH (e : X) (he : e ∈ H) : eta ≤ p e := (Finset.mem_filter.mp he).2.le
  have hpJ (e : X) (he : e ∈ J) : p e ≤ eta :=
    le_of_not_gt fun hh => (Finset.mem_sdiff.mp he).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
  have subSum (B : Finset X) : (∑ e ∈ B, (p e) ^ (1 / 3 : ℝ)) ≤ 2 * K :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
      (fun e _ _ => Real.rpow_nonneg (hp e) _)).trans hpsum
  have hJ := sum_light J p weight hA hθ hp hweight hpJ (subSum J)
  have hH := heavy_card H p (subSum H) hpH
  let cost : ℝ := A * (groupSize : ℝ) ^ (θ - 1)
  have hcost : 0 ≤ cost := mul_nonneg hA (Real.rpow_nonneg (by positivity) _)
  have group (B : Finset X) (_hB : B ⊆ H) (x : X) (i : Fin 3) (hBc : B.card = groupSize)
      (hline : ∀ e ∈ B, ∀ j : Fin 3, j ≠ i → x j = e j) :
      ∑ e ∈ B, weight e ≤ cost * groupSize := by
    let T := bunch hk0 w S B
    have hT := bunch_subset hk0 w S B
    have hTle (j : Fin 3) : (projection T j).card ≤ r j :=
      projection_card_le (fun y hy t => hr y (hT hy) t) j
    obtain ⟨j, hj⟩ : ∃ j : Fin 3, j ≠ i := by fin_cases i <;> decide
    have hTlt : (projection T j).card < r j := by
      have h := bunch_projection_le (hk := hk0) hw hrw hr hline j
      rw [if_neg hj] at h
      exact h.trans_lt (hwr j)
    have hvol : (volume fun j => (projection T j).card : ℝ) ≤ (groupSize : ℝ) * V := by
      have h := group_volume (hk := hk0) hw hrw hr hline
      rw [hBc] at h
      dsimp only [T, V]
      exact_mod_cast h
    have h := (hind T hT hTle ⟨j, hTlt⟩).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hvol hθ0) (by norm_num))
    have hsumT : (T.card : ℝ) = ∑ e ∈ B, weight e := by
      dsimp [T, weight, box]
      rw [card_bunch, Nat.cast_sum]
    rw [← hsumT]
    refine h.trans_eq ?_
    have hL : (0 : ℝ) < groupSize := by exact_mod_cast groupSize_pos
    rw [Real.mul_rpow hL.le hV.le]
    dsimp [cost, A]
    have he : (groupSize : ℝ) ^ θ = (groupSize : ℝ) ^ (θ - 1) * groupSize := by
      calc
        _ = (groupSize : ℝ) ^ (θ - 1 + 1) := by rw [sub_add_cancel]
        _ = _ := by rw [Real.rpow_add hL, Real.rpow_one]
    rw [he]
    ring
  obtain ⟨R, hR, hRline, hHR⟩ := charge_lines groupSize groupSize_pos H weight cost group
  have hRcard : (R.card : ℝ) ≤ K / 32 := by
    let E (f : Samples k w) := R.filter fun e => ∀ i, f i (e i) ∈ offsets hk0 w S e i
    have hmark (f : Samples k w) : (E f).card ≤ 3 * groupSize * C := by
      let sample (i : Fin 3) (b : Fin k) : ℕ := b.val * w i + (f i b).val
      have hl (e : X) (he : e ∈ E f) :
          IsMarked S (fun i => index hk0 (w i)) sample e := by
        intro i
        have he' : f i (e i) ∈ offsets hk0 w S e i := (Finset.mem_filter.mp he).2 i
        obtain ⟨y, hy, hye⟩ := mem_projection.mp (Finset.mem_filter.mp he').2
        exact ⟨y, (mem_cell.mp hy).1, (mem_cell.mp hy).2, hye⟩
      exact marked_card_bound hS (fun i => index_mono hk0 (w i))
        (Finset.filter_subset _ _) hRline hC hl
    have hRs := sampling_bound hw R (offsets hk0 w S) eta (3 * groupSize * C)
      (fun e he => by
        simp_rw [card_offsets hw hrw hr]
        rw [← Finset.prod_div_distrib]
        exact hpH e (hR he)) hmark
    have hRs' : eta * R.card ≤ eta * (K / 32) := hRs.trans (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hCsmall)
    exact (mul_le_mul_left eta_pos).mp hRs'
  have hRsum : (∑ e ∈ R, weight e) ≤ A * (K / 32) := by
    calc
      _ ≤ ∑ _e ∈ R, A := Finset.sum_le_sum fun e _ => weight_le e
      _ = A * R.card := by simp [nsmul_eq_mul, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hRcard hA
  have hlineTotal : cost * (H.card - R.card : ℕ) ≤ A * (K / 32) := by
    calc
      _ ≤ cost * (H.card : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le ..) hcost
      _ ≤ cost * (2 * eta ^ (-(1 / 3 : ℝ)) * K) := mul_le_mul_of_nonneg_left hH hcost
      _ = (A * K) * (2 * eta ^ (-(1 / 3 : ℝ)) * (groupSize : ℝ) ^ (θ - 1)) := by dsimp [cost]; ring
      _ ≤ (A * K) * (1 / 32) :=
        mul_le_mul_of_nonneg_left (line_constant hθ'.le) (mul_nonneg hA (sq_nonneg _))
      _ = _ := by ring
  have hsum := Finset.sum_sdiff (f := weight) (Finset.subset_univ H)
  have hcard : (S.card : ℝ) = (∑ e ∈ J, weight e) + ∑ e ∈ H, weight e :=
    (sum_cell_card hk0 w S).symm.trans hsum.symm
  have ht : (S.card : ℝ) ≤ 3 * (A * (K / 32)) := by rw [hcard]; linarith
  have hwidth : V * (k : ℝ) ^ 3 ≤ 8 * (volume r : ℝ) := by
    have h (i : Fin 3) : (w i : ℝ) * k ≤ 2 * (r i : ℝ) := by exact_mod_cast hwk i
    have hp := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 3)))
      (f := fun i => (w i : ℝ) * k) (g := fun i => 2 * (r i : ℝ))
      (fun _ _ => by positivity) (fun i _ => h i)
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hp
    norm_num [Finset.prod_const, ← volume_cast, V] at hp ⊢
    exact hp
  have hv := rounded_volume (show (0 : ℝ) < k by exact_mod_cast hk0)
    hV.le (Nat.cast_nonneg _) hθ0 hθ'.le hwidth hpow
  dsimp [A, K] at ht
  nlinarith [Real.rpow_nonneg (Nat.cast_nonneg (volume r)) θ]

theorem rectangular {k C : ℕ} (hk : 2 ≤ k) {θ : ℝ}
    (hθ : 1 / 2 ≤ θ) (hθ' : θ < 2 / 3) (hpow : (k : ℝ) ^ (2 - 3 * θ) = 2)
    (hC : ∀ T : Finset (Fin 3 → Fin k), PairwiseComparable T → T.card ≤ C)
    (hCsmall : 3 * (groupSize : ℝ) * C ≤ eta * ((k : ℝ) ^ 2 / 32))
    (r : Fin 3 → ℕ) (S : Finset (Fin 3 → ℕ)) (hS : PairwiseComparable S) (hr : InRectangle r S) :
    (S.card : ℝ) ≤ 2 * (volume r : ℝ) ^ θ := by
  suffices h : ∀ m (t : Fin 3 → ℕ), volume t = m → ∀ T : Finset (Fin 3 → ℕ),
      PairwiseComparable T → InRectangle t T → (T.card : ℝ) ≤ 2 * (volume t : ℝ) ^ θ from
    h _ r rfl S hS hr
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro t hvol T hT ht
    obtain rfl | ⟨x, hx⟩ := T.eq_empty_or_nonempty
    · simp only [Finset.card_empty, Nat.cast_zero]; positivity
    by_cases hlarge : ∀ i, k < t i
    · exact rectangular_step hk hlarge hθ hθ' hpow hC hCsmall hT ht
        (fun u U hlt hU hu => ih (volume u) (hvol ▸ hlt) u rfl U hU hu)
    · push_neg at hlarge
      obtain ⟨q, hq⟩ := hlarge
      obtain ⟨i, j, l, hij, hij', hjl', hmin, hvol'⟩ := sorted_axes t
      have hc : (T.card : ℝ) ≤ (t i : ℝ) * t j := by exact_mod_cast card_le_two_sides hT ht hij
      rw [hvol', Nat.cast_mul, Nat.cast_mul]
      have hipos : 0 < t i := (Nat.zero_le _).trans_lt (ht x hx i)
      exact hc.trans (small_sorted (by exact_mod_cast hipos) (by exact_mod_cast hij')
        (by exact_mod_cast hjl') (by exact_mod_cast (hmin q).trans hq) hθ hθ'.le hpow)

end Green88
