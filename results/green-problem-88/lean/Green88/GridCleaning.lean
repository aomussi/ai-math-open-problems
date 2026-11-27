import Green88.SparseGrid

namespace Green88

open scoped BigOperators

/-- Ordered pairs of distinct points that are not 2-comparable. -/
noncomputable def badPairs (S : Finset (Fin 3 → ℕ)) : Finset ((Fin 3 → ℕ) × (Fin 3 → ℕ)) := by
  classical
  exact (S ×ˢ S).filter fun p => p.1 ≠ p.2 ∧ ¬ Comparable p.1 p.2

theorem mem_badPairs {S : Finset (Fin 3 → ℕ)} {x y : Fin 3 → ℕ} :
    (x, y) ∈ badPairs S ↔ x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ ¬ Comparable x y := by
  classical
  simp [badPairs, and_assoc]

private theorem clean_axis {n k s t : ℕ} (hk : 0 < k) (ht : 0 < t)
    {S : Finset (Fin 3 → ℕ)} (hr : InRectangle (fun _ => n) S) (hp : PairProjections S)
    (i j l : Fin 3) (hjl : j ≠ l) (hij : i ≠ j) (hil : i ≠ l) :
    ∃ D ⊆ S, (D.card : ℝ) ≤ (n : ℝ) * (k : ℝ) ^ 2 * t +
        (n : ℝ) * (badPairs S).card / (t : ℝ) ^ 2 ∧
      ∀ a ∈ S \ D, ∀ b ∈ S \ D, a i = b i →
        (index hk s (a j) ≤ index hk s (b j) ∧ index hk s (a l) ≤ index hk s (b l)) ∨
        (index hk s (b j) ≤ index hk s (a j) ∧ index hk s (b l) ≤ index hk s (a l)) := by
  classical
  let key (p : Fin 3 → ℕ) := (p i, index hk s (p j), index hk s (p l))
  let fiber (a : ℕ) (e : Fin k × Fin k) := S.filter fun p => key p = (a, e)
  let domain : Finset (ℕ × (Fin k × Fin k)) := Finset.range n ×ˢ Finset.univ
  let small := S.filter fun p => (fiber (p i) ((key p).2)).card < t
  have small_bound : small.card ≤ n * k ^ 2 * t := by
    have dom (p : Fin 3 → ℕ) (hp : p ∈ small) : key p ∈ domain :=
      Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (hr p (Finset.mem_filter.mp hp).1 i), Finset.mem_univ _⟩
    have h := Finset.card_le_mul_card_image_of_maps_to (f := key) (s := small) (t := domain) dom t
      (fun ⟨a, e⟩ _ => by
        let U := small.filter fun x => key x = (a, e)
        rcases U.eq_empty_or_nonempty with h | ⟨p, hm⟩
        · change U.card ≤ t
          simp [h]
        · obtain ⟨hps, hkey⟩ := Finset.mem_filter.mp hm
          have hlt := (Finset.mem_filter.mp hps).2
          change (fiber (key p).1 (key p).2).card < t at hlt
          rw [hkey] at hlt
          exact (Finset.card_le_card (show U ⊆ fiber a e from
            fun q hq => Finset.mem_filter.mpr
              ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1, (Finset.mem_filter.mp hq).2⟩)).trans hlt.le)
    simpa [domain, Finset.card_product, Fintype.card_prod, pow_two,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  let inverted (a : ℕ) : Prop :=
    ∃ e f : Fin k × Fin k, e.1 < f.1 ∧ f.2 < e.2 ∧
      t ≤ (fiber a e).card ∧ t ≤ (fiber a f).card
  let badSlices := (Finset.range n).filter inverted
  let badIn (a : ℕ) := (badPairs S).filter fun p => p.1 i = a
  have slice_cost (a : ℕ) (ha : a ∈ badSlices) : t ^ 2 ≤ (badIn a).card := by
    obtain ⟨e, f, hfst, hsnd, he, hf⟩ := (Finset.mem_filter.mp ha).2
    have hsub : fiber a e ×ˢ fiber a f ⊆ badIn a := by
      rintro ⟨p, q⟩ hmem
      obtain ⟨hmp, hmq⟩ := Finset.mem_product.mp hmem
      obtain ⟨hps, hpkey⟩ := Finset.mem_filter.mp hmp
      obtain ⟨hqs, hqkey⟩ := Finset.mem_filter.mp hmq
      have hp0 : p i = a := congrArg Prod.fst hpkey
      have hq0 : q i = a := congrArg Prod.fst hqkey
      have hpj : index hk s (p j) = e.1 := congrArg (fun x => x.2.1) hpkey
      have hql : index hk s (q l) = f.2 := congrArg (fun x => x.2.2) hqkey
      have hqj : index hk s (q j) = f.1 := congrArg (fun x => x.2.1) hqkey
      have hpl : index hk s (p l) = e.2 := congrArg (fun x => x.2.2) hpkey
      have nij : p ≠ q := fun heq => by
        have this : index hk s (p j) = index hk s (q j) := congrArg (fun p : Fin 3 → ℕ => index hk s (p j)) heq
        rw [hpj, hqj] at this
        exact hfst.ne this
      refine Finset.mem_filter.mpr ⟨mem_badPairs.mpr ⟨hps, hqs, nij, ?_⟩, hp0⟩
      intro hc
      rcases section_chain hjl hij hil (hp0.trans hq0.symm) hc with h | h
      · have hb := index_mono hk s h.2.le
        rw [hpl, hql] at hb
        exact (not_lt_of_ge hb) hsnd
      · have hb := index_mono hk s h.1.le
        rw [hpj, hqj] at hb
        exact (not_lt_of_ge hb) hfst
    simpa only [pow_two, Finset.card_product] using
      (Nat.mul_le_mul he hf).trans (by simpa only [Finset.card_product] using Finset.card_le_card hsub)
  have slices_bound : badSlices.card * t ^ 2 ≤ (badPairs S).card := by
    calc
      _ = ∑ _a ∈ badSlices, t ^ 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ a ∈ badSlices, (badIn a).card := Finset.sum_le_sum slice_cost
      _ = ((badPairs S).filter fun p => p.1 i ∈ badSlices).card :=
        Finset.sum_card_fiberwise_eq_card_filter _ _ _
      _ ≤ _ := Finset.card_filter_le _ _
  let removed := S.filter fun p => p i ∈ badSlices
  have removed_bound : removed.card ≤ n * badSlices.card := by
    apply Finset.card_le_mul_card_image_of_maps_to (f := fun p : Fin 3 → ℕ => p i)
      (fun p hp => (Finset.mem_filter.mp hp).2) n
    intro a _
    let F := removed.filter fun p => p i = a
    have hmap (p : Fin 3 → ℕ) (hm : p ∈ F) : p j ∈ Finset.range n :=
      Finset.mem_range.mpr (hr p (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1 j)
    have hinj : Set.InjOn (fun p : Fin 3 → ℕ => p j) F := by
      intro p hmp q hmq heq
      obtain ⟨hmp', ep⟩ := Finset.mem_filter.mp hmp
      obtain ⟨hmq', eq⟩ := Finset.mem_filter.mp hmq
      exact hp i j hij (Finset.mem_filter.mp hmp').1 (Finset.mem_filter.mp hmq').1
        (Prod.ext (ep.trans eq.symm) heq)
    simpa using Finset.card_le_card_of_injOn (s := F) (t := Finset.range n)
      (fun p : Fin 3 → ℕ => p j) hmap hinj
  refine ⟨small ∪ removed, Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _), ?_, ?_⟩
  · have hsmall : (small.card : ℝ) ≤ (n : ℝ) * (k : ℝ) ^ 2 * t := by
      exact_mod_cast small_bound
    have hremoved : (removed.card : ℝ) ≤ (n : ℝ) * badSlices.card := by exact_mod_cast removed_bound
    have hbound : (badSlices.card : ℝ) * (t : ℝ) ^ 2 ≤ (badPairs S).card := by exact_mod_cast slices_bound
    have htR : (0 : ℝ) < t := by exact_mod_cast ht
    have h := mul_le_mul_of_nonneg_left ((le_div_iff₀ (sq_pos_of_pos htR)).mpr hbound)
      (show (0 : ℝ) ≤ n by positivity)
    have hsum : ((small ∪ removed).card : ℝ) ≤ (small.card : ℝ) + removed.card := by
      exact_mod_cast Finset.card_union_le (s := small) (t := removed)
    rw [← mul_div_assoc] at h
    linarith
  · intro a ha b hb hEq
    obtain ⟨has, hna⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨hbs, hnb⟩ := Finset.mem_sdiff.mp hb
    have haCard : t ≤ (fiber (a i) (key a).2).card :=
      le_of_not_gt fun ht => hna (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨has, ht⟩)))
    have hbCard : t ≤ (fiber (a i) (key b).2).card := by
      rw [hEq]
      exact le_of_not_gt fun ht => hnb (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hbs, ht⟩)))
    have no_inversion : ¬ inverted (a i) := fun he =>
      hna (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨has, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hr a has i), he⟩⟩)))
    by_cases ej : index hk s (a j) ≤ index hk s (b j)
    · by_cases el : index hk s (a l) ≤ index hk s (b l)
      · exact Or.inl ⟨ej, el⟩
      · by_cases ex : index hk s (b j) ≤ index hk s (a j)
        · exact Or.inr ⟨ex, (lt_of_not_ge el).le⟩
        · exact (no_inversion ⟨(key a).2, (key b).2, lt_of_not_ge ex, lt_of_not_ge el,
            haCard, hbCard⟩).elim
    · by_cases el : index hk s (b l) ≤ index hk s (a l)
      · exact Or.inr ⟨(lt_of_not_ge ej).le, el⟩
      · exact (no_inversion ⟨(key b).2, (key a).2, lt_of_not_ge ej, lt_of_not_ge el,
          hbCard, haCard⟩).elim

/-- Discard sparse cells and slices containing an inversion between dense cells. -/
theorem clean_grid {n k s t : ℕ} (hk : 0 < k) (ht : 0 < t)
    {S : Finset (Fin 3 → ℕ)} (hr : InRectangle (fun _ => n) S) (hp : PairProjections S) :
    ∃ W ⊆ S, SectionChains W (fun _ => index hk s) ∧
      (S.card : ℝ) ≤ (W.card : ℝ) +
        27 * ((n : ℝ) * (k : ℝ) ^ 2 * t + (n : ℝ) * (badPairs S).card / (t : ℝ) ^ 2) := by
  classical
  let I := Fin 3 × Fin 3 × Fin 3
  let B := (n : ℝ) * (k : ℝ) ^ 2 * t + (n : ℝ) * (badPairs S).card / (t : ℝ) ^ 2
  have chooseD (d : I) : ∃ D ⊆ S, (D.card : ℝ) ≤ B ∧
      (d.2.1 ≠ d.2.2 → d.1 ≠ d.2.1 → d.1 ≠ d.2.2 →
        ∀ a ∈ S \ D, ∀ b ∈ S \ D, a d.1 = b d.1 →
          (index hk s (a d.2.1) ≤ index hk s (b d.2.1) ∧
            index hk s (a d.2.2) ≤ index hk s (b d.2.2)) ∨
          (index hk s (b d.2.1) ≤ index hk s (a d.2.1) ∧
            index hk s (b d.2.2) ≤ index hk s (a d.2.2))) := by
    by_cases h : d.2.1 ≠ d.2.2 ∧ d.1 ≠ d.2.1 ∧ d.1 ≠ d.2.2
    · obtain ⟨D, hd, hb, hc⟩ := clean_axis hk ht hr hp d.1 d.2.1 d.2.2 h.1 h.2.1 h.2.2
      exact ⟨D, hd, hb, fun _ _ _ => hc⟩
    · exact ⟨∅, Finset.empty_subset _, by dsimp [B]; simp only [Finset.card_empty, Nat.cast_zero]; positivity,
        fun h1 h2 h3 => (h ⟨h1, h2, h3⟩).elim⟩
  choose D hs hb hc using chooseD
  let removed := (Finset.univ : Finset I).biUnion D
  have hsub : removed ⊆ S := fun x hx => by
    obtain ⟨j, _, hx⟩ := Finset.mem_biUnion.mp hx
    exact hs j hx
  refine ⟨S \ removed, Finset.sdiff_subset, ?_, ?_⟩
  · intro a ha b hb i j l hjl hij hil hEq
    let d : I := (i,j,l)
    have member (x : Fin 3 → ℕ) (hx : x ∈ S \ removed) : x ∈ S \ D d := by
      obtain ⟨hs, hn⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨hs, fun he =>
        hn (Finset.mem_biUnion.mpr ⟨d, Finset.mem_univ _, he⟩)⟩
    exact hc d hjl hij hil a (member a ha) b (member b hb) hEq
  · have hcard : (S.card : ℝ) = ((S \ removed).card : ℝ) + (removed.card : ℝ) := by
      exact_mod_cast (Finset.card_sdiff_add_card_eq_card hsub).symm
    have hremoved : (removed.card : ℝ) ≤ ∑ d : I, ((D d).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have hsum : (∑ d : I, ((D d).card : ℝ)) ≤ 27 * B := calc
      _ ≤ ∑ _d : I, B := Finset.sum_le_sum fun d _ => hb d
      _ = _ := by simp [I, Fintype.card_prod, nsmul_eq_mul]
    rw [hcard]
    exact add_le_add_left (hremoved.trans hsum) _

end Green88
