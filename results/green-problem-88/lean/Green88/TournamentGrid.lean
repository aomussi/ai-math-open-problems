import Green88.BlockCliques
import Green88.DepthFirst
import Green88.GridCleaning

namespace Green88

open scoped BigOperators
open Relation DirectedPath

namespace ColoredTournament

private theorem common_blocks {m L : ℕ} (T : ColoredTournament (Fin m)) (hL : 0 < L)
    (hb : ∀ i, PathBound (T.avoid i) L) :
    ∃ (w : Finset (Fin m)) (block : Fin 3 → Fin m → ℕ), 3 * m ≤ 4 * w.card ∧
      (∀ i a, (w.filter fun v => block i v = a).card ≤ 12 * L) ∧
      ∀ i, ∀ a ∈ w, ∀ b ∈ w, T.avoid i a b → block i b ≤ block i a := by
  classical
  have each (i : Fin 3) := ordered_blocks (hb i) (k := 12 * L) (by omega)
    (Finset.univ : Finset (Fin m))
  choose keep block _ hbudget hcapacity hordered using each
  let removed := (Finset.univ : Finset (Fin 3)).biUnion fun i => Finset.univ \ keep i
  let w : Finset (Fin m) := Finset.univ \ removed
  have hkeep (x : Fin m) (hx : x ∈ w) (i : Fin 3) : x ∈ keep i := by
    by_contra hm
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hm⟩⟩)
  have hcost (i : Fin 3) : 12 * ((Finset.univ : Finset (Fin m)) \ keep i).card ≤ m := by
    have h := hbudget i
    rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    simp only [Finset.card_univ, Fintype.card_fin] at h
    refine Nat.le_of_mul_le_mul_right (c := L) ?_ hL
    simpa only [Nat.mul_assoc, Nat.mul_comm 12] using h
  have hremoved : 12 * removed.card ≤ 3 * m := by
    calc
      _ ≤ 12 * ∑ i : Fin 3, ((Finset.univ : Finset (Fin m)) \ keep i).card :=
        Nat.mul_le_mul_left _ Finset.card_biUnion_le
      _ = ∑ i : Fin 3, 12 * ((Finset.univ : Finset (Fin m)) \ keep i).card := Finset.mul_sum ..
      _ ≤ ∑ _i : Fin 3, m := Finset.sum_le_sum fun i _ => hcost i
      _ = _ := by simp
  have hcard : w.card + removed.card = m := by
    simpa [w] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ removed)
  refine ⟨w, block, by omega, ?_, ?_⟩
  · intro i a
    have sub : (w.filter fun v => block i v = a) ⊆ (keep i).filter (fun v => block i v = a) :=
      fun v hv => Finset.mem_filter.mpr ⟨hkeep v (Finset.mem_filter.mp hv).1 i, (Finset.mem_filter.mp hv).2⟩
    exact (Finset.card_le_card sub).trans (hcapacity i a)
  · exact fun i a ha b hb he => hordered i a (hkeep a ha i) b (hkeep b hb i) he

private theorem pairs_in_blocks {V : Type*} [Fintype V] [DecidableEq V]
    (T : ColoredTournament V) {L C : ℕ} (hL : 0 < L)
    (gridCap : ∀ S : Finset (Fin 3 → ℕ), PairwiseComparable S →
      InRectangle (fun _ => L) S → S.card ≤ C)
    (hb : ∀ h, PathBound (T.avoid h) L)
    {i j : Fin 3} (hij : i ≠ j) (block label : V → ℕ)
    (hcap : ∀ b, (Finset.univ.filter fun v => block v = b).card ≤ 12 * L)
    (horder : ∀ v w, T.avoid j v w → block w ≤ block v) (hlabel : ∀ v, label v < L)
    (hmono : ∀ v w, T.edge v w → label v = label w → T.color v w = i) :
    ((Finset.univ : Finset (V × V)).filter
      fun p => block p.1 = block p.2 ∧ label p.1 = label p.2).card ≤ 12 * L * C := by
  classical
  let part (b : ℕ) := Finset.univ.filter fun v => block v = b
  let flat (b a : ℕ) := (part b).filter fun v => label v = a
  have maxes (b : ℕ) : ∃ a, a < L ∧ ∀ r < L, (flat b r).card ≤ (flat b a).card := by
    obtain ⟨a, ha, ha'⟩ := Finset.exists_max_image (Finset.range L) (fun a => (flat b a).card)
      ⟨0, Finset.mem_range.mpr hL⟩
    exact ⟨a, Finset.mem_range.mp ha, fun r hr => ha' r (Finset.mem_range.mpr hr)⟩
  choose best _ hbest using maxes
  let chosen := Finset.univ.filter fun v => label v = best (block v)
  let T' := T.induced chosen
  have chosen_bound : chosen.card ≤ C := by
    obtain ⟨S, hS, hbox, he⟩ := T'.monochromatic_blocks (fun v => block v.val) hij
      (fun h => T.induced_path_bound chosen h (hb h)) (fun v w h => horder v.val w.val h)
      (fun v w he hd => by
        change T.color v.val w.val = i
        have hv : label v.val = best (block v.val) := (Finset.mem_filter.mp v.prop).2
        have hw : label w.val = best (block w.val) := (Finset.mem_filter.mp w.prop).2
        exact hmono v.val w.val he (hv.trans ((congrArg best hd).trans hw.symm)))
    have hh := gridCap S hS hbox
    simpa only [he, Fintype.card_coe] using hh
  let blocks := (Finset.univ : Finset V).image block
  have hsum : (∑ b ∈ blocks, (flat b (best b)).card) = chosen.card := by
    have efiber (b : ℕ) : (chosen.filter fun v => block v = b) = flat b (best b) := by
      ext v
      simp only [chosen, flat, part, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h, eq⟩
        exact ⟨eq, eq ▸ h⟩
      · rintro ⟨eq, h⟩
        exact ⟨eq.symm ▸ h, eq⟩
    simp_rw [← efiber]
    exact (Finset.card_eq_sum_card_fiberwise (f := block) (s := chosen) (t := blocks)
      fun v _ => Finset.mem_image_of_mem _ (Finset.mem_univ v)).symm
  let pairs := (Finset.univ : Finset (V × V)).filter
    fun p => block p.1 = block p.2 ∧ label p.1 = label p.2
  let inBlock (b : ℕ) := pairs.filter fun p => block p.1 = b
  have part_bound (b : ℕ) : (inBlock b).card ≤ 12 * L * (flat b (best b)).card := by
    have h := Finset.card_le_mul_card_image_of_maps_to (f := fun p : V × V => p.1) (s := inBlock b) (t := part b)
      (fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩)
      (flat b (best b)).card (fun a ha => by
        let U := (inBlock b).filter fun p => p.1 = a
        have map (p : V × V) (hp : p ∈ U) : p.2 ∈ flat b (label a) := by
          obtain ⟨hp, ep⟩ := Finset.mem_filter.mp hp
          obtain ⟨hp, eb⟩ := Finset.mem_filter.mp hp
          obtain ⟨_, eb', el⟩ := Finset.mem_filter.mp hp
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, eb'.symm.trans eb⟩,
            el.symm.trans (congrArg label ep)⟩
        have inj : Set.InjOn (fun p : V × V => p.2) U := by
          intro p hp q hq he
          exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) he
        exact (Finset.card_le_card_of_injOn (s := U) (fun p : V × V => p.2) map inj).trans (hbest b (label a) (hlabel a)))
    exact h.trans (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_le_mul_left (flat b (best b)).card (hcap b))
  change pairs.card ≤ _
  calc
    _ = ∑ b ∈ blocks, (inBlock b).card :=
      Finset.card_eq_sum_card_fiberwise (f := fun v : V × V => block v.1)
        fun v _ => Finset.mem_image_of_mem _ (Finset.mem_univ v.1)
    _ ≤ ∑ b ∈ blocks, 12 * L * (flat b (best b)).card := Finset.sum_le_sum fun b _ => part_bound b
    _ = 12 * L * chosen.card := by rw [← Finset.mul_sum, hsum]
    _ ≤ _ := Nat.mul_le_mul_left _ chosen_bound

/-- Convert an arbitrary colored tournament to an almost-comparable point set.
The defect count is for ordered pairs, hence twice the unordered-pair constant. -/
theorem sparse_grid {m L C : ℕ} (T : ColoredTournament (Fin m)) (hL : 0 < L)
    (hb : ∀ i, PathBound (T.avoid i) L)
    (gridCap : ∀ S : Finset (Fin 3 → ℕ), PairwiseComparable S →
      InRectangle (fun _ => L) S → S.card ≤ C) :
    ∃ S : Finset (Fin 3 → ℕ), InRectangle (fun _ => L) S ∧ PairProjections S ∧
      3 * m ≤ 4 * S.card ∧ (badPairs S).card ≤ 72 * L * C := by
  classical
  obtain ⟨W, blocks, hkeep, hcapacity, hforward⟩ := common_blocks T hL hb
  let G := T.induced W
  let V := (↑W : Type)
  let block (j : Fin 3) (v : V) := blocks j v.val
  have ordered (i : Fin 3) (a b : V) (h : G.avoid i a b) : block i b ≤ block i a :=
    hforward i a.val a.prop b.val b.prop h
  have capacity (i : Fin 3) (k : ℕ) : ((Finset.univ : Finset V).filter fun v => block i v = k).card ≤ 12 * L := by
    have he : ((Finset.univ : Finset V).filter fun v => block i v = k).card =
        (W.filter fun v => blocks i v = k).card := by
      apply Finset.card_nbij Subtype.val
      · intro a ha
        exact Finset.mem_filter.mpr ⟨a.prop, (Finset.mem_filter.mp ha).2⟩
      · exact fun _ _ _ _ he => Subtype.ext he
      · intro a ha
        obtain ⟨hw, hh⟩ := Finset.mem_filter.mp ha
        exact ⟨⟨a, hw⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩, rfl⟩
    exact he ▸ hcapacity i k
  let seed (i : Fin 3) (a b : V) := G.avoid i a b ∧ block i a ≠ block i b
  have ext (i : Fin 3) : ∃ H : V → V → Prop, seed i ≤ H ∧ H ≤ G.avoid i ∧ Acyclic H ∧
      ∀ a b, G.avoid i a b → TransGen H a b ∨ TransGen H b a :=
    extend_acyclic (fun _ _ h => h.1)
      (acyclic_of_increasing (f := fun a => OrderDual.toDual (block i a))
        fun a b h => lt_of_le_of_ne (ordered i a b h.1) h.2)
      (fun a h => G.loopless a h.1)
  choose H hseed hsub ha hmax using ext
  let lab (a : V) (i : Fin 3) := height (H i) a - 1
  have cap (a : V) (i : Fin 3) : lab a i < L := by
    have hpos := height_pos (H i) a
    have hle := height_le (hsub i) (T.induced_path_bound W i (hb i)) a
    dsimp [lab]
    omega
  have strict {a b : V} (i : Fin 3) (h : H i a b) : lab a i < lab b i := by
    have hlt := height_lt (ha i) h
    have hpos := height_pos (H i) a
    dsimp [lab]
    omega
  have mono (i : Fin 3) (a b : V) (he : G.edge a b) (heq : lab a i = lab b i) : G.color a b = i := by
    apply G.equal_height_color (ha i) (hmax i) he
    have hp := height_pos (H i) a
    have hq := height_pos (H i) b
    dsimp [lab] at heq
    omega
  have inj_two {a b : V} {i j : Fin 3} (hij : i ≠ j)
      (hi : lab a i = lab b i) (hj : lab a j = lab b j) : a = b := by
    apply Classical.byContradiction
    intro hn
    rcases G.total a b hn with he | he
    · exact hij ((mono i a b he hi).symm.trans (mono j a b he hj))
    · exact hij ((mono i b a he hi.symm).symm.trans (mono j b a he hj.symm))
  let emb : V ↪ (Fin 3 → ℕ) := ⟨lab, by
    intro a b he
    exact inj_two (by decide : (0 : Fin 3) ≠ 1) (congrFun he 0) (congrFun he 1)⟩
  let S := (Finset.univ : Finset V).map emb
  have cardS : S.card = W.card := by
    simp only [S, Finset.card_map, Finset.card_univ]
    exact Fintype.card_coe W
  refine ⟨S, ?_, ?_, by rwa [cardS], ?_⟩
  · intro a ha i
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp ha
    exact cap v i
  · intro i j hij a ha b hb he
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp hb
    exact congrArg emb (inj_two hij (congrArg Prod.fst he) (congrArg Prod.snd he))
  · let IJ := {p : Fin 3 × Fin 3 // p.1 ≠ p.2}
    let pairs (ij : IJ) := (Finset.univ : Finset (V × V)).filter
      fun p => block ij.val.2 p.1 = block ij.val.2 p.2 ∧ lab p.1 ij.val.1 = lab p.2 ij.val.1
    have each (ij : IJ) : (pairs ij).card ≤ 12 * L * C :=
      pairs_in_blocks G hL gridCap (fun i => T.induced_path_bound W i (hb i))
        ij.prop (block ij.val.2) (fun a => lab a ij.val.1) (capacity _) (ordered _)
        (fun v => cap v _) (mono _)
    have identify (a b : V) (hne : ¬ Comparable (lab a) (lab b)) :
        ∃ ij : IJ, (a, b) ∈ pairs ij := by
      have equal : ∃ i : Fin 3, lab a i = lab b i := by
        apply Classical.byContradiction
        intro hh
        exact hne (comparable_of_no_equal (fun i h => hh ⟨i, h⟩))
      obtain ⟨i, hi⟩ := equal
      obtain ⟨j, l, hjl, hij, hil⟩ : ∃ j l : Fin 3, j ≠ l ∧ i ≠ j ∧ i ≠ l := by
        fin_cases i <;> decide
      by_cases ej : block j a = block j b
      · exact ⟨⟨(i, j), hij⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ej, hi⟩⟩
      by_cases el : block l a = block l b
      · exact ⟨⟨(i, l), hil⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, el, hi⟩⟩
      -- This branch is only used for distinct vertices, as the two block inequalities force.
      have hneq : a ≠ b := fun h => ej (congrArg (block j) h)
      have up {a b : V} (he : G.edge a b) (eh : lab a i = lab b i)
          (dj : block j a ≠ block j b) (dl : block l a ≠ block l b) : TwoLess (lab a) (lab b) :=
        ⟨j, l, hjl, strict j (hseed j a b ⟨⟨he, (mono i a b he eh).trans_ne hij⟩, dj⟩),
          strict l (hseed l a b ⟨⟨he, (mono i a b he eh).trans_ne hil⟩, dl⟩)⟩
      exact (hne ((G.total a b hneq).imp (fun e => up e hi ej el)
        (fun e => up e hi.symm (Ne.symm ej) (Ne.symm el)))).elim
    let U := (Finset.univ : Finset IJ).biUnion pairs
    have sub : badPairs S ⊆ U.image (fun p => (lab p.1, lab p.2)) := by
      rintro ⟨x, y⟩ hp
      obtain ⟨hx, hy, _, hn⟩ := mem_badPairs.mp hp
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hy
      obtain ⟨ij, hpair⟩ := identify a b hn
      exact Finset.mem_image.mpr ⟨(a, b),
        Finset.mem_biUnion.mpr ⟨ij, Finset.mem_univ _, hpair⟩, rfl⟩
    have hIJ : Fintype.card IJ = 6 := by decide
    calc
      _ ≤ (U.image (fun p => (lab p.1, lab p.2))).card := Finset.card_le_card sub
      _ ≤ U.card := Finset.card_image_le
      _ ≤ ∑ ij : IJ, (pairs ij).card := Finset.card_biUnion_le
      _ ≤ ∑ _ij : IJ, 12 * L * C := Finset.sum_le_sum fun ij _ => each ij
      _ = _ := by norm_num [hIJ, nsmul_eq_mul, ← Nat.mul_assoc]

end ColoredTournament
end Green88
