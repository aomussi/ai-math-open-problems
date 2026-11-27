import Green88.ColorAvoiding

namespace Green88

open Relation DirectedPath

namespace ColoredTournament

variable {V : Type*} [Fintype V] (T : ColoredTournament V)

theorem equal_height_color {H : V → V → Prop} {i : Fin 3}
    (ha : Acyclic H) (hmax : ∀ a b, T.avoid i a b → TransGen H a b ∨ TransGen H b a)
    {a b : V} (he : T.edge a b) (hh : height H a = height H b) : T.color a b = i := by
  apply Classical.byContradiction
  intro hne
  have inc (a b : V) (h : H a b) : height H a < height H b := height_lt ha h
  rcases hmax a b ⟨he, hne⟩ with hp | hp
  · exact ne_of_lt (reach_lt inc hp) hh
  · exact ne_of_gt (reach_lt inc hp) hh

theorem rectangle_of_heights {H : Fin 3 → V → V → Prop} {L : ℕ}
    (hbound : ∀ i, PathBound (H i) L)
    (hcomp : ∀ a b, a ≠ b → Comparable (fun i => height (H i) a) (fun i => height (H i) b)) :
    ∃ S : Finset (Fin 3 → ℕ), PairwiseComparable S ∧ InRectangle (fun _ => L) S ∧
      S.card = Fintype.card V := by
  let f (a : V) (i : Fin 3) := height (H i) a - 1
  have compare (a b : V) (hne : a ≠ b) : Comparable (f a) (f b) := by
    have down (i : Fin 3) (a b : V) (h : height (H i) a < height (H i) b) :
        f a i < f b i := by
      dsimp [f]
      have := height_pos (H i) a
      omega
    rcases hcomp a b hne with ⟨i, j, hij, hi, hj⟩ | ⟨i, j, hij, hi, hj⟩
    · exact Or.inl ⟨i, j, hij, down i a b hi, down j a b hj⟩
    · exact Or.inr ⟨i, j, hij, down i b a hi, down j b a hj⟩
  let emb : V ↪ (Fin 3 → ℕ) := ⟨f, by
    intro a b he
    by_contra hne
    have h := compare a b hne
    rw [he] at h
    rcases h with ⟨i, _, _, hi, _⟩ | ⟨i, _, _, hi, _⟩ <;> exact lt_irrefl _ hi⟩
  refine ⟨Finset.univ.map emb, ?_, ?_, by simp⟩
  · intro x hx y hy hne
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hy
    exact compare a b (fun e => hne (congrArg emb e))
  · intro x hx i
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    change height (H i) a - 1 < L
    have hb := height_le (fun _ _ h => h) (hbound i) a
    have hp := height_pos (H i) a
    omega

private theorem monochromatic_blocks_zero (block : V → ℕ) {L : ℕ}
    (hb : ∀ i, PathBound (T.avoid i) L)
    (ordered : ∀ a b, T.avoid 0 a b → block b ≤ block a)
    (mono : ∀ a b, T.edge a b → block a = block b → T.color a b = 1) :
    ∃ S : Finset (Fin 3 → ℕ), PairwiseComparable S ∧ InRectangle (fun _ => L) S ∧
      S.card = Fintype.card V := by
  obtain ⟨P, hPa, hPedge, hPtotal⟩ := T.level_paths block
  have pColor {a b : V} (h : P a b) : T.color a b = 1 :=
    mono a b (hPedge a b h).1 (hPedge a b h).2
  let cross (a b : V) := T.avoid 0 a b ∧ block a ≠ block b
  let H0 (a b : V) := P a b ∨ cross a b
  have sub0 : H0 ≤ T.avoid 0 := by
    intro a b h
    exact h.elim (fun h => ⟨(hPedge a b h).1, (pColor h).trans_ne (by decide)⟩) And.left
  have ha0 : Acyclic H0 := by
    exact acyclic_across_levels (f := fun a => OrderDual.toDual (block a)) hPa
      (fun a b h => (hPedge a b h).2)
      (fun a b h => lt_of_le_of_ne (ordered a b h.1) h.2)
  let x0 := height H0
  have inc0 (a b : V) (h : H0 a b) : x0 a < x0 b := height_lt ha0 h
  have h0color {a b : V} (ne : a ≠ b) (hh : x0 a = x0 b) (he : T.edge a b) : T.color a b = 0 := by
    by_cases hblock : block a = block b
    · rcases hPtotal a b ne hblock with h | h
      · exact (ne_of_lt (reach_lt inc0 (h.mono fun _ _ => Or.inl))) hh |>.elim
      · exact (ne_of_gt (reach_lt inc0 (h.mono fun _ _ => Or.inl))) hh |>.elim
    · apply Classical.byContradiction
      intro hn
      exact (ne_of_lt (inc0 a b (Or.inr ⟨⟨he, hn⟩, hblock⟩))) hh
  obtain ⟨Q, hQa, hQedge, hQtotal⟩ := T.level_paths x0
  have qColor {a b : V} (h : Q a b) : T.color a b = 0 :=
    h0color (fun e => T.loopless b (e ▸ (hQedge a b h).1))
      (hQedge a b h).2 (hQedge a b h).1
  have color2cross {a b : V} (he : T.edge a b) (hc : T.color a b = 2) : cross a b :=
    ⟨⟨he, hc.trans_ne (by decide)⟩, fun e => (show (2 : Fin 3) ≠ 1 by decide) (hc.symm.trans (mono a b he e))⟩
  let seed1 (a b : V) := Q a b ∨ T.edge a b ∧ T.color a b = 2
  have sub1 : seed1 ≤ T.avoid 1 := by
    intro a b h
    rcases h with h | ⟨he, hc⟩
    · exact ⟨(hQedge a b h).1, (qColor h).trans_ne (by decide)⟩
    · exact ⟨he, hc.trans_ne (by decide)⟩
  have ac1 : Acyclic seed1 :=
    acyclic_across_levels (f := x0) hQa (fun a b h => (hQedge a b h).2)
      (fun a b h => inc0 a b (Or.inr (color2cross h.1 h.2)))
  obtain ⟨H1, into1, hsub1, ha1, hmax1⟩ :=
    extend_acyclic sub1 ac1 (fun a h => T.loopless a h.1)
  let seed2 (a b : V) :=
    Q a b ∨ P a b ∨ (T.edge a b ∧ T.color a b = 1 ∧ block a ≠ block b)
  have sub2 : seed2 ≤ T.avoid 2 := by
    intro a b h
    rcases h with h | h | ⟨he, hc, _⟩
    · exact ⟨(hQedge a b h).1, (qColor h).trans_ne (by decide)⟩
    · exact ⟨(hPedge a b h).1, (pColor h).trans_ne (by decide)⟩
    · exact ⟨he, hc.trans_ne (by decide)⟩
  have oneCross {a b : V} (he : T.edge a b) (hc : T.color a b = 1) (hd : block a ≠ block b) :
      cross a b := ⟨⟨he, hc.trans_ne (by decide)⟩, hd⟩
  have ac2 : Acyclic seed2 := by
    apply acyclic_across_levels (f := x0) hQa (fun a b h => (hQedge a b h).2)
    intro a b h
    rcases h with h | ⟨he, hc, hd⟩
    · exact inc0 a b (Or.inl h)
    · exact inc0 a b (Or.inr (oneCross he hc hd))
  obtain ⟨H2, into2, hsub2, ha2, hmax2⟩ :=
    extend_acyclic sub2 ac2 (fun a h => T.loopless a h.1)
  have inc1 (a b : V) (h : H1 a b) : height H1 a < height H1 b := height_lt ha1 h
  have inc2 (a b : V) (h : H2 a b) : height H2 a < height H2 b := height_lt ha2 h
  let H : Fin 3 → V → V → Prop := ![H0, H1, H2]
  apply rectangle_of_heights (H := H)
  · intro i
    fin_cases i
    · exact bound_mono sub0 (hb 0)
    · exact bound_mono hsub1 (hb 1)
    · exact bound_mono hsub2 (hb 2)
  intro a b hab
  apply comparable_from_sections
  · intro hh
    have up {a b : V} (h : TransGen Q a b) : height H1 a < height H1 b ∧ height H2 a < height H2 b :=
      ⟨reach_lt inc1 (h.mono fun a b h => into1 a b (Or.inl h)),
        reach_lt inc2 (h.mono fun a b h => into2 a b (Or.inl h))⟩
    exact (hQtotal a b hab hh).imp up up
  · intro hh
    by_cases same : block a = block b
    · have up {a b : V} (h : TransGen P a b) : x0 a < x0 b ∧ height H2 a < height H2 b :=
        ⟨reach_lt inc0 (h.mono fun _ _ => Or.inl),
          reach_lt inc2 (h.mono fun a b h => into2 a b (Or.inr (Or.inl h)))⟩
      exact (hPtotal a b hab same).imp up up
    · have up {a b : V} (he : T.edge a b) (hf : height H1 a = height H1 b)
          (hd : block a ≠ block b) : x0 a < x0 b ∧ height H2 a < height H2 b := by
        have hc := T.equal_height_color ha1 hmax1 he hf
        exact ⟨inc0 a b (Or.inr (oneCross he hc hd)), inc2 a b (into2 a b (Or.inr (Or.inr ⟨he, hc, hd⟩)))⟩
      exact (T.total a b hab).imp (fun h => up h hh same) (fun h => up h hh.symm (Ne.symm same))
  · intro hh
    have up {a b : V} (he : T.edge a b) (hf : height H2 a = height H2 b) :
        x0 a < x0 b ∧ height H1 a < height H1 b := by
      have hc := T.equal_height_color ha2 hmax2 he hf
      exact ⟨inc0 a b (Or.inr (color2cross he hc)), inc1 a b (into1 a b (Or.inr ⟨he, hc⟩))⟩
    exact (T.total a b hab).imp (fun h => up h hh) (fun h => up h hh.symm)

/-- Monochromatic blocks of color i embedded using the order across blocks
provided by the digraph avoiding a different color j. -/
theorem monochromatic_blocks (block : V → ℕ) {L : ℕ} {i j : Fin 3} (hij : i ≠ j)
    (hb : ∀ i, PathBound (T.avoid i) L)
    (ordered : ∀ a b, T.avoid j a b → block b ≤ block a)
    (mono : ∀ a b, T.edge a b → block a = block b → T.color a b = i) :
    ∃ S : Finset (Fin 3 → ℕ), PairwiseComparable S ∧ InRectangle (fun _ => L) S ∧
      S.card = Fintype.card V := by
  let e1 := Equiv.swap j (0 : Fin 3)
  let e2 := Equiv.swap (e1 i) (1 : Fin 3)
  let e := e1.trans e2
  have h0 : e1 j = 0 := by simp [e1]
  have he0 : e j = 0 := by
    change e2 (e1 j) = 0
    rw [h0]
    have hd : (0 : Fin 3) ≠ e1 i := fun h => hij (e1.injective (h.symm.trans h0.symm))
    exact Equiv.swap_apply_of_ne_of_ne hd (by decide)
  have he1 : e i = 1 := by simp [e, e2]
  have he' : e.symm 0 = j := e.symm_apply_eq.mpr he0.symm
  apply (T.recolor e).monochromatic_blocks_zero block
  · intro a
    rw [avoid_recolor]
    exact hb _
  · intro a b h
    rw [avoid_recolor, he'] at h
    exact ordered a b h
  · intro a b he h
    change e (T.color a b) = 1
    rw [mono a b he h, he1]

end ColoredTournament
end Green88
