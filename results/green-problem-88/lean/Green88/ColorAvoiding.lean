import Green88.DirectedPaths
import Green88.Theorem
import Mathlib.Data.Fin.VecNotation

namespace Green88

open Relation DirectedPath

/-- A tournament with each directed edge assigned one of three colors. -/
structure ColoredTournament (V : Type*) where
  edge : V → V → Prop
  color : V → V → Fin 3
  total : ∀ a b, a ≠ b → edge a b ∨ edge b a
  asymm : ∀ a b, edge a b → ¬ edge b a

namespace ColoredTournament

variable {V : Type*} (T : ColoredTournament V)

/-- The spanning digraph obtained by deleting color i. -/
def avoid (i : Fin 3) (a b : V) : Prop :=
  T.edge a b ∧ T.color a b ≠ i

theorem loopless (a : V) : ¬ T.edge a a := fun h => T.asymm a a h h

/-- Longest simple color-avoiding path, counted in vertices. -/
noncomputable def pathLength [Fintype V] (i : Fin 3) : ℕ := DirectedPath.longest (T.avoid i)

def recolor (e : Fin 3 ≃ Fin 3) : ColoredTournament V :=
  ⟨T.edge, fun a b => e (T.color a b), T.total, T.asymm⟩

theorem avoid_recolor (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    (T.recolor e).avoid i = T.avoid (e.symm i) := by
  funext a b
  apply propext
  have h : e (T.color a b) = i ↔ T.color a b = e.symm i := e.apply_eq_iff_eq_symm_apply
  exact and_congr_right fun _ => not_congr h

private theorem pairwise_direction {R : V → V → Prop} {l : List V}
    (hl : l.Pairwise R) {a b : V} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    R a b ∨ R b a := by
  induction l with
  | nil => simp at ha
  | cons v l ih =>
      obtain ⟨hv, hl⟩ := List.pairwise_cons.mp hl
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inl (hv _ ((List.mem_cons.mp hb).resolve_left (fun h => hne h.symm)))
      · have haTail : a ∈ l := ha
        rcases List.mem_cons.mp hb with he | hbTail
        · rw [he]
          exact Or.inr (hv _ haTail)
        · exact ih hl haTail hbTail

theorem comparable_from_sections (x y : Fin 3 → ℕ)
    (h0 : x 0 = y 0 → (x 1 < y 1 ∧ x 2 < y 2) ∨ (y 1 < x 1 ∧ y 2 < x 2))
    (h1 : x 1 = y 1 → (x 0 < y 0 ∧ x 2 < y 2) ∨ (y 0 < x 0 ∧ y 2 < x 2))
    (h2 : x 2 = y 2 → (x 0 < y 0 ∧ x 1 < y 1) ∨ (y 0 < x 0 ∧ y 1 < x 1)) :
    Comparable x y := by
  by_cases e0 : x 0 = y 0
  · exact (h0 e0).imp (fun h => ⟨1, 2, by decide, h.1, h.2⟩)
      (fun h => ⟨1, 2, by decide, h.1, h.2⟩)
  by_cases e1 : x 1 = y 1
  · exact (h1 e1).imp (fun h => ⟨0, 2, by decide, h.1, h.2⟩)
      (fun h => ⟨0, 2, by decide, h.1, h.2⟩)
  by_cases e2 : x 2 = y 2
  · exact (h2 e2).imp (fun h => ⟨0, 1, by decide, h.1, h.2⟩)
      (fun h => ⟨0, 1, by decide, h.1, h.2⟩)
  rcases lt_or_gt_of_ne e0 with e0 | e0 <;> rcases lt_or_gt_of_ne e1 with e1 | e1 <;>
    rcases lt_or_gt_of_ne e2 with e2 | e2
  all_goals first
    | exact Or.inl ⟨0, 1, by decide, e0, e1⟩
    | exact Or.inl ⟨0, 2, by decide, e0, e2⟩
    | exact Or.inl ⟨1, 2, by decide, e1, e2⟩
    | exact Or.inr ⟨0, 1, by decide, e0, e1⟩
    | exact Or.inr ⟨0, 2, by decide, e0, e2⟩
    | exact Or.inr ⟨1, 2, by decide, e1, e2⟩

/-- The edges of one directed Hamilton path per level. -/
theorem level_paths [Fintype V] (f : V → ℕ) :
    ∃ P : V → V → Prop, Acyclic P ∧
      (∀ a b, P a b → T.edge a b ∧ f a = f b) ∧
      ∀ a b, a ≠ b → f a = f b → TransGen P a b ∨ TransGen P b a := by
  classical
  let level (k : ℕ) := Finset.univ.filter fun v : V => f v = k
  have pathsExist (k : ℕ) : ∃ l : List V, DirectedPath T.edge l ∧ ∀ v, v ∈ l ↔ f v = k := by
    obtain ⟨l, hl, hm⟩ := hamilton_path (level k) (fun a _ b _ => T.total a b)
    exact ⟨l, hl, fun a => (hm a).trans (by simp [level])⟩
  choose paths hp using pathsExist
  let P (a b : V) : Prop := ∃ (k j : ℕ) (hj : j < (paths k).length - 1),
    (paths k).get ⟨j, by omega⟩ = a ∧ (paths k).get ⟨j + 1, by omega⟩ = b
  let rank (a : V) := (paths (f a)).idxOf a
  have edgeData (a b : V) (h : P a b) : T.edge a b ∧ f a = f b ∧ rank a < rank b := by
    obtain ⟨k, j, hj, ea, eb⟩ := h
    have fa := (hp k).2 a |>.mp (ea ▸ List.get_mem ..)
    have fb := (hp k).2 b |>.mp (eb ▸ List.get_mem ..)
    have edge := List.chain'_iff_get.mp (hp k).1.2 j hj
    rw [ea, eb] at edge
    refine ⟨edge, fa.trans fb.symm, ?_⟩
    change (paths (f a)).idxOf a < (paths (f b)).idxOf b
    rw [fa, fb, ← ea, ← eb]
    simp only [List.get_eq_getElem, List.idxOf_getElem (hp k).1.1]
    omega
  refine ⟨P, acyclic_of_increasing (f := rank) fun a b h => (edgeData a b h).2.2,
    fun a b h => ⟨(edgeData a b h).1, (edgeData a b h).2.1⟩, ?_⟩
  intro a b hne he
  have chain : (paths (f a)).Chain' P :=
    List.chain'_iff_get.mpr fun j hj => ⟨f a, j, hj, rfl, rfl⟩
  have pairs := List.chain'_iff_pairwise.mp (chain.imp fun _ _ h => TransGen.single h)
  exact pairwise_direction pairs ((hp _).2 a |>.mpr rfl) ((hp _).2 b |>.mpr he.symm) hne

theorem acyclic_across_levels {α : Type*} [Preorder α] {f : V → α} {P Q : V → V → Prop}
    (hP : Acyclic P) (hflat : ∀ a b, P a b → f a = f b)
    (hup : ∀ a b, Q a b → f a < f b) : Acyclic (fun a b => P a b ∨ Q a b) := by
  have reduce {a b : V} (hr : TransGen (fun a b => P a b ∨ Q a b) a b) :
      (TransGen P a b ∧ f a = f b) ∨ f a < f b := by
    induction hr with
    | single h =>
      rcases h with h | h
      · exact Or.inl ⟨TransGen.single h, hflat _ _ h⟩
      · exact Or.inr (hup _ _ h)
    | tail _ h ih =>
      rcases ih with ⟨hp, he⟩ | hlt <;> rcases h with h | h
      · exact Or.inl ⟨hp.tail h, he.trans (hflat _ _ h)⟩
      · exact Or.inr (he.le.trans_lt (hup _ _ h))
      · exact Or.inr (hlt.trans_le (hflat _ _ h).le)
      · exact Or.inr (hlt.trans (hup _ _ h))
  intro a h
  exact (reduce h).elim (fun h => hP a h.1) (lt_irrefl _)

private theorem label_zero [Fintype V] (ha : Acyclic (T.avoid 0)) {n : Fin 3 → ℕ}
    (hb : ∀ i, PathBound (T.avoid i) (n i)) :
    ∃ f : V → Fin 3 → ℕ, (∀ a b, a ≠ b → Comparable (f a) (f b)) ∧
      ∀ a i, f a i < n i := by
  classical
  let h0 := height (T.avoid 0)
  have inc0 (a b : V) (h : T.avoid 0 a b) : h0 a < h0 b := height_lt ha h
  have color0 {a b : V} (he : T.edge a b) (hh : h0 a = h0 b) : T.color a b = 0 := by
    apply Classical.byContradiction
    intro hn
    exact (ne_of_lt (inc0 a b ⟨he, hn⟩)) hh
  obtain ⟨P, hPacyclic, hPedge, hPtotal⟩ := T.level_paths h0
  have path_levels {a b : V} (h : P a b) : h0 a = h0 b := (hPedge a b h).2
  have path_edge {a b : V} (h : P a b) : T.edge a b ∧ T.color a b = 0 :=
    ⟨(hPedge a b h).1, color0 (hPedge a b h).1 (path_levels h)⟩
  let first (a b : V) := P a b ∨ T.edge a b ∧ T.color a b = 2
  have first_sub : first ≤ T.avoid 1 := by
    intro a b h
    rcases h with h | ⟨he, hc⟩
    · obtain ⟨he, hc⟩ := path_edge h
      exact ⟨he, hc.trans_ne (by decide)⟩
    · exact ⟨he, hc.trans_ne (by decide)⟩
  have first_acyclic : Acyclic first :=
    acyclic_across_levels (f := h0) hPacyclic (fun a b h => path_levels h)
      (fun a b h => inc0 a b ⟨h.1, h.2.trans_ne (by decide)⟩)
  obtain ⟨H1, first_H1, H1_sub, H1_acyclic, H1_max⟩ :=
    extend_acyclic first_sub first_acyclic (fun v h => T.loopless v h.1)
  let h1 := height H1
  have inc1 (a b : V) (he : H1 a b) : h1 a < h1 b := height_lt H1_acyclic he
  have P_H1 : P ≤ H1 := fun a b h => first_H1 a b (Or.inl h)
  have color1 {a b : V} (he : T.edge a b) (hh : h1 a = h1 b) :
      T.color a b = 1 := by
    apply Classical.byContradiction
    intro hn
    rcases H1_max a b ⟨he, hn⟩ with h | h
    · exact ne_of_lt (reach_lt inc1 h) hh
    · exact ne_of_gt (reach_lt inc1 h) hh
  let Q (a b : V) := T.edge a b ∧ h1 a = h1 b
  let second (a b : V) := P a b ∨ Q a b
  have second_sub : second ≤ T.avoid 2 := by
    intro a b h
    rcases h with h | ⟨he, hh⟩
    · obtain ⟨he, hc⟩ := path_edge h
      exact ⟨he, hc.trans_ne (by decide)⟩
    · exact ⟨he, (color1 he hh).trans_ne (by decide)⟩
  have second_acyclic : Acyclic second := by
    apply acyclic_of_increasing (f := fun v => h0 v + h1 v)
    intro a b h
    rcases h with h | ⟨he, hh⟩
    · rw [path_levels h]
      exact Nat.add_lt_add_left (inc1 a b (P_H1 a b h)) _
    · rw [hh]
      exact Nat.add_lt_add_right (inc0 a b ⟨he, (color1 he hh).trans_ne (by decide)⟩) _
  obtain ⟨H2, second_H2, H2_sub, H2_acyclic, H2_max⟩ :=
    extend_acyclic second_sub second_acyclic (fun v h => T.loopless v h.1)
  let h2 := height H2
  have inc2 (a b : V) (he : H2 a b) : h2 a < h2 b := height_lt H2_acyclic he
  have P_H2 : P ≤ H2 := fun a b h => second_H2 a b (Or.inl h)
  have color2 {a b : V} (he : T.edge a b) (hh : h2 a = h2 b) :
      T.color a b = 2 := by
    apply Classical.byContradiction
    intro hn
    rcases H2_max a b ⟨he, hn⟩ with h | h
    · exact ne_of_lt (reach_lt inc2 h) hh
    · exact ne_of_gt (reach_lt inc2 h) hh
  let heights (a : V) : Fin 3 → ℕ := ![h0 a, h1 a, h2 a]
  have pos (a : V) (i : Fin 3) : 0 < heights a i := by
    fin_cases i
    · exact height_pos _ _
    · exact height_pos _ _
    · exact height_pos _ _
  have cap (a : V) (i : Fin 3) : heights a i ≤ n i := by
    fin_cases i
    · exact height_le (fun _ _ h => h) (hb 0) a
    · exact height_le H1_sub (hb 1) a
    · exact height_le H2_sub (hb 2) a
  have comp (a b : V) (hne : a ≠ b) : Comparable (heights a) (heights b) := by
    apply comparable_from_sections
    · intro hh
      rcases hPtotal a b hne hh with h | h
      · exact Or.inl ⟨reach_lt inc1 (h.mono P_H1), reach_lt inc2 (h.mono P_H2)⟩
      · exact Or.inr ⟨reach_lt inc1 (h.mono P_H1), reach_lt inc2 (h.mono P_H2)⟩
    · intro hh
      have increase {a b : V} (he : T.edge a b) (e : h1 a = h1 b) :
          h0 a < h0 b ∧ h2 a < h2 b :=
        ⟨inc0 _ _ ⟨he, (color1 he e).trans_ne (by decide)⟩,
          inc2 _ _ (second_H2 _ _ (Or.inr ⟨he, e⟩))⟩
      exact (T.total a b hne).imp (fun h => increase h hh) (fun h => increase h hh.symm)
    · intro hh
      have increase {a b : V} (he : T.edge a b) (e : h2 a = h2 b) :
          h0 a < h0 b ∧ h1 a < h1 b :=
        ⟨inc0 _ _ ⟨he, (color2 he e).trans_ne (by decide)⟩,
          inc1 _ _ (first_H1 _ _ (Or.inr ⟨he, color2 he e⟩))⟩
      exact (T.total a b hne).imp (fun h => increase h hh) (fun h => increase h hh.symm)
  have sub_lt (a b : V) (i : Fin 3) (hi : heights a i < heights b i) :
      heights a i - 1 < heights b i - 1 := by
    have := pos a i
    omega
  refine ⟨fun a i => heights a i - 1, ?_, ?_⟩
  · intro a b hne
    rcases comp a b hne with ⟨i, j, hij, hi, hj⟩ | ⟨i, j, hij, hi, hj⟩
    · exact Or.inl ⟨i, j, hij, sub_lt a b i hi, sub_lt a b j hj⟩
    · exact Or.inr ⟨i, j, hij, sub_lt b a i hi, sub_lt b a j hj⟩
  · intro a i
    change heights a i - 1 < n i
    have h := cap a i
    have hpos := pos a i
    omega

/-- If one color deletion is acyclic, the vertex set embeds as a comparable
set in the rectangle whose side lengths are any valid path bounds. -/
theorem comparable_rectangle [Fintype V] (ha : ∃ i, Acyclic (T.avoid i)) {n : Fin 3 → ℕ}
    (hn : ∀ i, PathBound (T.avoid i) (n i)) :
    ∃ S : Finset (Fin 3 → ℕ), PairwiseComparable S ∧ InRectangle n S ∧
      S.card = Fintype.card V := by
  classical
  obtain ⟨c, hc⟩ := ha
  let e := Equiv.swap c (0 : Fin 3)
  have e0 : e.symm 0 = c := by simp [e]
  have h0 : Acyclic ((T.recolor e).avoid 0) := by simpa only [avoid_recolor, e0] using hc
  obtain ⟨f, hf, hb⟩ := label_zero (T.recolor e) h0
    (n := fun i => n (e.symm i)) (fun i => by simpa only [avoid_recolor] using hn (e.symm i))
  let g (x : V) (i : Fin 3) := f x (e i)
  have comp (a b : V) (hne : a ≠ b) : Comparable (g a) (g b) := by
    have reindex {a b : V} (h : TwoLess (f a) (f b)) : TwoLess (g a) (g b) := by
      obtain ⟨i, j, hij, hi, hj⟩ := h
      exact ⟨e.symm i, e.symm j, e.symm.injective.ne hij, by simpa [g] using hi,
        by simpa [g] using hj⟩
    exact (hf a b hne).imp reindex reindex
  have inj : Function.Injective g := by
    intro a b h
    by_contra hab
    have hcomp := comp a b hab
    rw [h] at hcomp
    rcases hcomp with ⟨i, _, _, hi, _⟩ | ⟨i, _, _, hi, _⟩ <;> exact lt_irrefl _ hi
  let emb : V ↪ (Fin 3 → ℕ) := ⟨g, inj⟩
  refine ⟨Finset.univ.map emb, ?_, ?_, by simp⟩
  · intro x hx y hy hne
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hy
    exact comp a b (fun e => hne (congrArg emb e))
  · intro x hx i
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    change g a i < n i
    simpa [g] using hb a (e i)

private theorem twoLess_asymm {x y : Fin 3 → ℕ} (h : TwoLess x y) :
    ¬ TwoLess y x := by
  obtain ⟨i, j, hij, hi, hj⟩ := h
  rintro ⟨k, l, hkl, hk, hl⟩
  have disjoint {t : Fin 3} (ht : y t < x t) : t ≠ i ∧ t ≠ j :=
    ⟨fun e => lt_asymm hi (e ▸ ht), fun e => lt_asymm hj (e ▸ ht)⟩
  exact hkl (fin3_eq_of_ne hij (disjoint hk).1 (disjoint hk).2
    (disjoint hl).1 (disjoint hl).2)

private def gridColor (x y : Fin 3 → ℕ) : Fin 3 :=
  if x 0 < y 0 then if x 1 < y 1 then 2 else 1 else 0

private theorem increases_avoiding {x y : Fin 3 → ℕ} (h : TwoLess x y)
    (i : Fin 3) (hc : gridColor x y ≠ i) : x i < y i := by
  fin_cases i
  · change x 0 < y 0
    change gridColor x y ≠ 0 at hc
    apply lt_of_not_ge
    intro he
    exact hc (by simp [gridColor, not_lt_of_ge he])
  · change x 1 < y 1
    change gridColor x y ≠ 1 at hc
    apply lt_of_not_ge
    intro he
    have h0 := (twoLess_coords (i := 0) (j := 2) (k := 1)
      (by decide) (by decide) (by decide) he h).1
    exact hc (by simp [gridColor, h0, not_lt_of_ge he])
  · change x 2 < y 2
    change gridColor x y ≠ 2 at hc
    apply lt_of_not_ge
    intro he
    obtain ⟨h0, h1⟩ := twoLess_coords (i := 0) (j := 1) (k := 2)
      (by decide) (by decide) (by decide) he h
    exact hc (by simp [gridColor, h0, h1])

/-- The extremal equivalence holds at every order m and for every triple of caps.
The converse construction has all three color deletions acyclic. -/
theorem grid_equivalence (m : ℕ) (n : Fin 3 → ℕ) :
    (∃ G : ColoredTournament (Fin m), (∃ i, Acyclic (G.avoid i)) ∧
      ∀ i, PathBound (G.avoid i) (n i)) ↔
    ∃ S : Finset (Fin 3 → ℕ), PairwiseComparable S ∧ InRectangle n S ∧ S.card = m := by
  classical
  constructor
  · rintro ⟨G, ha, hb⟩
    simpa using G.comparable_rectangle ha hb
  · rintro ⟨S, hS, hr, hm⟩
    let equiv := (Finset.equivFinOfCardEq hm).symm
    let x (a : Fin m) := (equiv a).val
    let G : ColoredTournament (Fin m) :=
      ⟨fun a b => TwoLess (x a) (x b), fun a b => gridColor (x a) (x b),
        fun a b hne => hS (equiv a).prop (equiv b).prop
          (fun he => hne (equiv.injective (Subtype.ext he))),
        fun _ _ => twoLess_asymm⟩
    have inc (i : Fin 3) (a b : Fin m) (h : G.avoid i a b) : x a i < x b i :=
      increases_avoiding h.1 i h.2
    have ha (i : Fin 3) : Acyclic (G.avoid i) := acyclic_of_increasing (inc i)
    exact ⟨G, ⟨0, ha 0⟩, fun i => bound_of_increasing
      (fun a => hr (x a) (equiv a).prop i) (inc i)⟩

/-- Maximum of the three longest color-avoiding path lengths. -/
noncomputable def maxPathLength [Fintype V] : ℕ := Finset.univ.sup T.pathLength

theorem pathLength_le_max [Fintype V] (i : Fin 3) : T.pathLength i ≤ T.maxPathLength :=
  Finset.le_sup (Finset.mem_univ i)

open scoped BigOperators

/-- The rectangular power bound applies to the individual longest path lengths. -/
theorem rectangular_path_power :
    ∃ θ : ℝ, 1 / 2 ≤ θ ∧ θ < 2 / 3 ∧
      ∀ (m : ℕ) (G : ColoredTournament (Fin m)), (∃ i, Acyclic (G.avoid i)) →
        (m : ℝ) ≤ (volume G.pathLength : ℝ) ^ θ := by
  obtain ⟨θ, hθ, hθ', hrect⟩ := rectangular_exponent
  refine ⟨θ, hθ, hθ', ?_⟩
  intro m G ha
  obtain ⟨S, hS, hr, hc⟩ := G.comparable_rectangle ha
    (fun i => longest_bound (G.avoid i))
  simpa [hc] using hrect _ S hS hr

/-- One color can be avoided on a path with a power saving over the square-root bound. -/
theorem color_avoiding_power :
    ∃ δ : ℝ, 0 < δ ∧ δ < 2 ∧
      ∀ (m : ℕ) (G : ColoredTournament (Fin m)), (∃ i, Acyclic (G.avoid i)) →
        (m : ℝ) ^ (1 / (2 - δ)) ≤ (G.maxPathLength : ℝ) := by
  obtain ⟨θ, hθ, hθ', hbound⟩ := rectangular_path_power
  refine ⟨2 - 3 * θ, by linarith, by linarith, ?_⟩
  intro m G ha
  let L := G.maxPathLength
  have hθ0 : 0 < θ := by linarith
  have hθ3 : 0 < 3 * θ := by positivity
  have hv : volume G.pathLength ≤ L ^ 3 := by
    have hp : volume G.pathLength ≤ volume (fun _ => L) :=
      Finset.prod_le_prod' fun i _ => G.pathLength_le_max i
    simpa [volume, Finset.prod_const] using hp
  have hv' : (volume G.pathLength : ℝ) ≤ (L : ℝ) ^ (3 : ℕ) := by exact_mod_cast hv
  have hm : (m : ℝ) ≤ (L : ℝ) ^ (3 * θ) := calc
    _ ≤ (volume G.pathLength : ℝ) ^ θ := hbound m G ha
    _ ≤ ((L : ℝ) ^ (3 : ℕ)) ^ θ := Real.rpow_le_rpow (by positivity) hv' hθ0.le
    _ = _ := (Real.rpow_natCast_mul (by positivity) _ _).symm
  change (m : ℝ) ^ (1 / (2 - (2 - 3 * θ))) ≤ (L : ℝ)
  rw [show 2 - (2 - 3 * θ) = 3 * θ by ring]
  calc
    _ ≤ ((L : ℝ) ^ (3 * θ)) ^ (1 / (3 * θ)) :=
      Real.rpow_le_rpow (by positivity) hm (by positivity)
    _ = _ := by rw [← Real.rpow_mul (by positivity), one_div, mul_inv_cancel₀ hθ3.ne',
      Real.rpow_one]

/-- The tournament induced by a set of vertices. -/
def induced (s : Finset V) : ColoredTournament s :=
  ⟨fun a b => T.edge a.val b.val, fun a b => T.color a.val b.val,
    fun a b hne => T.total a.val b.val (fun h => hne (Subtype.ext h)),
    fun a b => T.asymm a.val b.val⟩

theorem induced_path_bound (s : Finset V) (i : Fin 3) {n : ℕ}
    (hb : PathBound (T.avoid i) n) : PathBound ((T.induced s).avoid i) n := by
  intro l hl
  have hmap : DirectedPath (T.avoid i) (l.map Subtype.val) :=
    ⟨hl.1.map Subtype.val_injective, (List.chain'_map Subtype.val).mpr hl.2⟩
  simpa only [List.length_map] using hb _ hmap

/-- The exponent saving with a factor b if one color deletion's vertex set
can be partitioned into b induced acyclic parts. -/
theorem partition_path_power :
    ∃ δ : ℝ, 0 < δ ∧ δ < 2 ∧
      ∀ (m b : ℕ) (G : ColoredTournament (Fin m)) (f : Fin m → Fin b) (i : Fin 3),
        (∀ j, Acyclic ((G.induced (Finset.univ.filter fun v => f v = j)).avoid i)) →
        (m : ℝ) ≤ (b : ℝ) * (G.maxPathLength : ℝ) ^ (2 - δ) := by
  classical
  obtain ⟨θ, hθ, hθ', hrect⟩ := rectangular_exponent
  refine ⟨2 - 3 * θ, by linarith, by linarith, ?_⟩
  intro m b G f i ha
  let L := G.maxPathLength
  let level (j : Fin b) : Finset (Fin m) := Finset.univ.filter fun v => f v = j
  have each (j : Fin b) : ((level j).card : ℝ) ≤ (L : ℝ) ^ (3 * θ) := by
    let H := G.induced (level j)
    have hb (c : Fin 3) : PathBound (H.avoid c) L := by
      apply G.induced_path_bound
      intro l hl
      exact (longest_bound (G.avoid c) l hl).trans (G.pathLength_le_max c)
    obtain ⟨S, hS, hr, hcard⟩ := H.comparable_rectangle ⟨i, ha j⟩ hb
    have h := hrect _ S hS hr
    rwa [hcard, Fintype.card_coe, volume, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity), Nat.cast_ofNat] at h
  have hcard : m = ∑ j : Fin b, (level j).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
        fun _ _ => Finset.mem_univ _)
  change (m : ℝ) ≤ (b : ℝ) * (L : ℝ) ^ (2 - (2 - 3 * θ))
  rw [show 2 - (2 - 3 * θ) = 3 * θ by ring]
  calc
    _ = ∑ j : Fin b, ((level j).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _j : Fin b, (L : ℝ) ^ (3 * θ) := Finset.sum_le_sum fun j _ => each j
    _ = _ := by simp

#print axioms grid_equivalence
#print axioms rectangular_path_power
#print axioms color_avoiding_power
#print axioms partition_path_power

end ColoredTournament
end Green88
