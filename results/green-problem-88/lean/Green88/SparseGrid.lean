import Green88.Coarse
import Green88.Budget

namespace Green88

open scoped BigOperators

/-- Knowing any two coordinates determines the point. -/
def PairProjections (S : Finset (Fin 3 → ℕ)) : Prop :=
  ∀ i j : Fin 3, i ≠ j → Set.InjOn (fun p : Fin 3 → ℕ => (p i, p j)) S

theorem PairProjections.mono {S T : Finset (Fin 3 → ℕ)} (h : PairProjections S) (hTS : T ⊆ S) :
    PairProjections T := fun i j hij _ ha _ hb he => h i j hij (hTS ha) (hTS hb) he

theorem PairProjections.card_le {S : Finset (Fin 3 → ℕ)} (h : PairProjections S)
    {i j : Fin 3} (hij : i ≠ j) :
    S.card ≤ (projection S i).card * (projection S j).card := by
  let f (p : Fin 3 → ℕ) := (p i, p j)
  have hsub : S.image f ⊆ (projection S i) ×ˢ (projection S j) := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨mem_projection.mpr ⟨x, hx, rfl⟩,
      mem_projection.mpr ⟨x, hx, rfl⟩⟩
  have hi : Set.InjOn f S := h i j hij
  simpa only [Finset.card_product, Finset.card_image_of_injOn hi] using Finset.card_le_card hsub

/-- Counting for point sets with coarse section chains. Fine-scale pairs may be incomparable. -/
theorem coarse_grid_bound {n k s u C : ℕ} (hk : 0 < k) (hs : 0 < s) (hn : n ≤ k * s)
    (hu : 0 < u) {η : ℝ} (hη : 0 < η)
    (hC : ∀ T : Finset (Fin 3 → Fin k), PairwiseComparable T → T.card ≤ C)
    {S : Finset (Fin 3 → ℕ)} (hr : InRectangle (fun _ => n) S) (hp : PairProjections S)
    (hchain : SectionChains S (fun _ => index hk s)) :
    (S.card : ℝ) ≤ (s : ℝ) ^ 2 *
      (6 * (k : ℝ) ^ 2 * η ^ (1 / 3 : ℝ) +
       2 * (k : ℝ) ^ 2 / (η ^ (1 / 3 : ℝ) * u) + (3 * (u : ℝ) * C) / η) := by
  classical
  let w : Fin 3 → ℕ := fun _ => s
  let X := Fin 3 → Fin k
  let box (e : X) := cell hk w S e
  let weight (e : X) : ℝ := (box e).card
  let density (e : X) (i : Fin 3) : ℝ := ((projection (box e) i).card : ℝ) / s
  let p (e : X) := ∏ i, density e i
  let A : ℝ := (s : ℝ) ^ 2
  let K : ℝ := (k : ℝ) ^ 2
  let α : ℝ := η ^ (1 / 3 : ℝ)
  have hα : 0 < α := Real.rpow_pos_of_pos hη _
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have width (e : X) (i : Fin 3) : (projection (box e) i).card ≤ s :=
    cell_projection_le (fun _ => hs) (fun _ => hn) hr e i
  have dens_nonneg (e : X) (i : Fin 3) : 0 ≤ density e i := by dsimp [density]; positivity
  have dens_le (e : X) (i : Fin 3) : density e i ≤ 1 :=
    (div_le_one hsR).mpr (by exact_mod_cast width e i)
  have weight_pair (e : X) {i j : Fin 3} (hij : i ≠ j) :
      weight e ≤ A * density e i * density e j := by
    have hc := (hp.mono (cell_subset hk w S e)).card_le hij
    have hcR : weight e ≤
        ((projection (box e) i).card : ℝ) * ((projection (box e) j).card : ℝ) := by
      change ((box e).card : ℝ) ≤ _
      exact_mod_cast hc
    refine hcR.trans_eq ?_
    dsimp [A, density]
    field_simp
    ring
  have weight_le (e : X) : weight e ≤ A := by
    calc
      _ ≤ A * density e 0 * density e 1 := weight_pair e (by decide)
      _ ≤ A * 1 * 1 := by gcongr <;> exact dens_le e _
      _ = A := by ring
  have sum_axis (i : Fin 3) : (∑ e : X, density e i) ≤ 2 * K := by
    dsimp [density]
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hsR).mpr
    have h := sum_projection_bound_of_sections hk w hchain hr i
    have hns : (n : ℝ) ≤ (k : ℝ) * s := by exact_mod_cast hn
    calc
      _ ≤ (n : ℝ) * (2 * k) := h
      _ ≤ ((k : ℝ) * s) * (2 * k) := mul_le_mul_of_nonneg_right hns (by positivity)
      _ = 2 * K * s := by dsimp [K]; ring
  have sum_dens : (∑ e : X, ∑ i, density e i) ≤ 6 * K := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _i : Fin 3, 2 * K := Finset.sum_le_sum fun i _ => sum_axis i
      _ = _ := by simp [nsmul_eq_mul]; ring
  have sum_root : (∑ e : X, (p e) ^ (1 / 3 : ℝ)) ≤ 2 * K := by
    calc
      _ ≤ ∑ e : X, (∑ i, density e i) / 3 :=
        Finset.sum_le_sum fun e _ => cube_root_prod_le _ (dens_nonneg e)
      _ ≤ _ := by
        rw [← Finset.sum_div]
        exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr (by linarith only [sum_dens])
  let heavy : Finset X := Finset.univ.filter fun e => η < p e
  let light : Finset X := Finset.univ \ heavy
  have point_light (e : X) (he : e ∈ light) : weight e ≤ A * α * (∑ i, density e i) := by
    have hlight : p e ≤ η := le_of_not_gt fun h =>
      (Finset.mem_sdiff.mp he).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have hsmall : ∃ i, density e i ≤ α := by
      apply Classical.byContradiction
      intro hall'
      have hall (i : Fin 3) : α < density e i := lt_of_not_ge fun h => hall' ⟨i, h⟩
      have hprod : ∏ _i : Fin 3, α < p e :=
        Finset.prod_lt_prod (fun _ _ => hα) (fun i _ => (hall i).le)
          ⟨0, Finset.mem_univ _, hall 0⟩
      have hpow : (∏ _i : Fin 3, α) = η := by
        rw [Fin.prod_univ_three]
        calc
          _ = (η ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by dsimp [α]; ring
          _ = η := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]
            norm_num
      exact (not_lt_of_ge hlight) (hpow ▸ hprod)
    obtain ⟨i, hi⟩ := hsmall
    obtain ⟨j, hij⟩ : ∃ j : Fin 3, i ≠ j := by fin_cases i <;> decide
    calc
      _ ≤ A * density e i * density e j := weight_pair e hij
      _ ≤ A * α * (∑ t : Fin 3, density e t) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hi (by dsimp [A]; positivity))
          (Finset.single_le_sum (fun t _ => dens_nonneg e t) (Finset.mem_univ j))
          (dens_nonneg e j) (by dsimp [A]; positivity)
  have sum_light : (∑ e ∈ light, weight e) ≤ A * α * (6 * K) := by
    calc
      _ ≤ ∑ e ∈ light, A * α * ∑ i, density e i := Finset.sum_le_sum point_light
      _ = _ := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ light)
          (fun e _ _ => Finset.sum_nonneg fun i _ => dens_nonneg e i)).trans sum_dens)
        (by dsimp [A]; positivity)
  have heavy_size : (heavy.card : ℝ) ≤ 2 * K / α := by
    apply (le_div_iff₀ hα).mpr
    calc
      _ = ∑ _e ∈ heavy, α := by simp [nsmul_eq_mul]
      _ ≤ ∑ e ∈ heavy, (p e) ^ (1 / 3 : ℝ) := Finset.sum_le_sum fun e he =>
        Real.rpow_le_rpow hη.le (Finset.mem_filter.mp he).2.le (by norm_num)
      _ ≤ _ := (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ heavy)
        (fun e _ _ => Real.rpow_nonneg (Finset.prod_nonneg fun i _ => dens_nonneg e i) _)).trans sum_root
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hgroup (B : Finset X) (_hB : B ⊆ heavy) (x : X) (i : Fin 3) (_hcard : B.card = u)
      (hline : ∀ e ∈ B, ∀ j : Fin 3, j ≠ i → x j = e j) :
      ∑ e ∈ B, weight e ≤ A / u * u := by
    let U := bunch hk w S B
    obtain ⟨j, l, hjl, hij, hil⟩ : ∃ j l : Fin 3, j ≠ l ∧ i ≠ j ∧ i ≠ l := by
      fin_cases i <;> decide
    have bound (a : Fin 3) (ha : a ≠ i) : (projection U a).card ≤ s := by
      have h := bunch_projection_le (hk := hk) (w := w) (fun _ => hs) (fun _ => hn) hr hline a
      simpa only [if_neg ha] using h
    have hc := ((hp.mono (bunch_subset hk w S B)).card_le hjl).trans
      (Nat.mul_le_mul (bound j hij.symm) (bound l hil.symm))
    have hsum : (U.card : ℝ) = ∑ e ∈ B, weight e := by
      dsimp [U, weight, box]
      rw [card_bunch, Nat.cast_sum]
    rw [← hsum, div_mul_cancel₀ _ huR.ne']
    dsimp [A]
    exact_mod_cast (by simpa [pow_two] using hc : U.card ≤ s ^ 2)
  obtain ⟨R, hR, hlines, hcharged⟩ := charge_lines u hu heavy weight (A / u) hgroup
  have hsample (f : Samples k w) :
      (R.filter fun e => ∀ i, f i (e i) ∈ offsets hk w S e i).card ≤ 3 * u * C := by
    let sample (i : Fin 3) (b : Fin k) : ℕ := b.val * w i + (f i b).val
    apply marked_card_bound_of_sections hchain (sample := sample) (Finset.filter_subset _ _)
      hlines hC
    intro e he i
    have hmem : f i (e i) ∈ offsets hk w S e i := (Finset.mem_filter.mp he).2 i
    obtain ⟨y, hy, hye⟩ := mem_projection.mp (Finset.mem_filter.mp hmem).2
    exact ⟨y, (mem_cell.mp hy).1, (mem_cell.mp hy).2, hye⟩
  have hRcount := sampling_bound (fun _ => hs) R (offsets hk w S) η (3 * u * C)
    (fun e he => by
      simp_rw [card_offsets (w := w) (fun _ => hs) (fun _ => hn) hr]
      rw [← Finset.prod_div_distrib]
      exact (Finset.mem_filter.mp (hR he)).2.le) hsample
  have hremain : (∑ e ∈ R, weight e) ≤ A * ((3 * (u : ℝ) * C) / η) := by
    calc
      _ ≤ ∑ _e ∈ R, A := Finset.sum_le_sum fun e _ => weight_le e
      _ = A * R.card := by simp [nsmul_eq_mul, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left ((le_div_iff₀ hη).mpr (by
        simpa [Nat.cast_mul, mul_comm] using hRcount)) (by dsimp [A]; positivity)
  have hcost : (A / u) * (heavy.card - R.card : ℕ) ≤ A * (2 * K / (α * u)) := by
    calc
      _ ≤ (A / u) * (heavy.card : ℝ) := mul_le_mul_of_nonneg_left
        (by exact_mod_cast Nat.sub_le heavy.card R.card) (by dsimp [A]; positivity)
      _ ≤ (A / u) * (2 * K / α) := mul_le_mul_of_nonneg_left heavy_size (by dsimp [A]; positivity)
      _ = _ := by ring
  have hsum : (S.card : ℝ) = (∑ e ∈ light, weight e) + ∑ e ∈ heavy, weight e :=
    (sum_cell_card hk w S).symm.trans (Finset.sum_sdiff (f := weight) (Finset.subset_univ heavy)).symm
  rw [hsum]
  dsimp [A, K, α] at *
  linarith only [sum_light, hcharged, hremain, hcost]

end Green88
