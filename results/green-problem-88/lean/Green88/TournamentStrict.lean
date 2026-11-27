import Green88.BlockCliques
import Mathlib.Data.Fintype.Option

namespace Green88

open Relation DirectedPath

namespace ColoredTournament

theorem maxPathLength_pos {m : ℕ} (T : ColoredTournament (Fin m)) (hm : 0 < m) :
    0 < T.maxPathLength := by
  have h := longest_bound (T.avoid 0) [⟨0, hm⟩] (by simp [DirectedPath])
  exact h.trans (T.pathLength_le_max 0)

theorem two_le_maxPathLength {m : ℕ} (T : ColoredTournament (Fin m)) (hm : 1 < m) :
    2 ≤ T.maxPathLength := by
  let a : Fin m := ⟨0, by omega⟩
  let b : Fin m := ⟨1, hm⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; contradiction
  have path {a b : Fin m} (hne : a ≠ b) (he : T.edge a b) : 2 ≤ T.maxPathLength := by
    obtain ⟨i, hi⟩ : ∃ i : Fin 3, T.color a b ≠ i := by
      generalize T.color a b = c
      fin_cases c <;> decide
    have hp : DirectedPath (T.avoid i) [a, b] :=
      ⟨by simp [hne], List.chain'_pair.mpr ⟨he, hi⟩⟩
    exact (longest_bound _ _ hp).trans (T.pathLength_le_max i)
  exact (T.total a b hab).elim (path hab) (path hab.symm)

/-- Strict improvement on the elementary square-root bound, including small orders. -/
theorem card_lt_path_square {m L : ℕ} (T : ColoredTournament (Fin m)) (hL : 1 < L)
    (hb : ∀ i, PathBound (T.avoid i) L) : m < L ^ 2 := by
  classical
  obtain ⟨H0, _, sub0, ac0, sat0⟩ :=
    extend_acyclic (E := fun _ _ : Fin m => False) (F := T.avoid 0)
      (fun _ _ h => h.elim) (fun _ h => by
        have hn := h.mono (p := fun a b : Fin m => (a : ℕ) < b) fun _ _ h => h.elim
        exact (lt_irrefl _) (reach_lt (f := fun a : Fin m => a.val) (fun _ _ h => h) hn))
      (fun a h => T.loopless a h.1)
  let h0 := height H0
  obtain ⟨P, acP, heP, totalP⟩ := T.level_paths h0
  have no0 {a b : Fin m} (h : P a b) : T.color a b = 0 :=
    T.equal_height_color ac0 sat0 (heP a b h).1 (heP a b h).2
  obtain ⟨H1, into1, sub1, ac1, sat1⟩ := extend_acyclic
    (E := P) (F := T.avoid 1)
    (fun a b h => ⟨(heP a b h).1, (no0 h).trans_ne (by decide)⟩)
    acP (fun a h => T.loopless a h.1)
  obtain ⟨H2, into2, sub2, ac2, sat2⟩ := extend_acyclic
    (E := P) (F := T.avoid 2)
    (fun a b h => ⟨(heP a b h).1, (no0 h).trans_ne (by decide)⟩)
    acP (fun a h => T.loopless a h.1)
  let rank (H : Fin m → Fin m → Prop) (hcap : ∀ v, height H v ≤ L) (v : Fin m) : Fin L :=
    ⟨height H v - 1, by have := height_pos H v; have := hcap v; omega⟩
  have bnd0 := height_le sub0 (hb 0)
  have bnd1 := height_le sub1 (hb 1)
  have bnd2 := height_le sub2 (hb 2)
  let f0 := rank H0 bnd0
  let f1 := rank H1 bnd1
  let f2 := rank H2 bnd2
  have rank_eq (H : Fin m → Fin m → Prop) (bound : ∀ v, height H v ≤ L)
      {a b : Fin m} (he : rank H bound a = rank H bound b) : height H a = height H b := by
    have ea := height_pos H a
    have eb := height_pos H b
    have hh := congrArg Fin.val he
    dsimp [rank] at hh
    omega
  have rank_lt (H : Fin m → Fin m → Prop) (bound : ∀ v, height H v ≤ L)
      {a b : Fin m} (h : height H a < height H b) : rank H bound a < rank H bound b := by
    change height H a - 1 < height H b - 1
    have := height_pos H a
    omega
  let pair (v : Fin m) := (f1 v, f2 v)
  have pair_inj : Function.Injective pair := by
    intro a b he
    apply Classical.byContradiction
    intro ne
    have e1 : height H1 a = height H1 b := rank_eq H1 bnd1 (congrArg Prod.fst he)
    have e2 : height H2 a = height H2 b := rank_eq H2 bnd2 (congrArg Prod.snd he)
    have clash {a b : Fin m} (e1 : height H1 a = height H1 b) (e2 : height H2 a = height H2 b)
        (he : T.edge a b) : False := by
      have c1 := T.equal_height_color ac1 sat1 he e1
      have c2 := T.equal_height_color ac2 sat2 he e2
      exact (show (1 : Fin 3) ≠ 2 by decide) (c1.symm.trans c2)
    exact (T.total a b ne).elim (clash e1 e2) (clash e1.symm e2.symm)
  have leSq : m ≤ L ^ 2 := by simpa [pow_two] using Fintype.card_le_of_injective pair pair_inj
  apply lt_of_le_of_ne leSq
  intro he
  have hsurj : Function.Surjective pair := ((Fintype.bijective_iff_injective_and_card pair).mpr
    ⟨pair_inj, by simpa [pow_two] using he⟩).2
  let last : Fin L := ⟨L - 1, by omega⟩
  let first : Fin L := ⟨0, by omega⟩
  have last_ne_first : last ≠ first := by
    intro he
    have eq : L - 1 = 0 := congrArg Fin.val he
    omega
  let tail : Option (Fin L) → Fin L × Fin L
    | none => (first, last)
    | some x => (last, x)
  have tail_inj : Function.Injective tail := by
    intro a b he
    cases a <;> cases b <;> simp_all [tail]
  have never {a b : Option (Fin L)} (h1 : (tail a).1 < (tail b).1)
      (h2 : (tail a).2 < (tail b).2) : False := by
    cases a with
    | none =>
      change L - 1 < (tail b).2.val at h2
      have := (tail b).2.isLt
      omega
    | some a =>
      change L - 1 < (tail b).1.val at h1
      have := (tail b).1.isLt
      omega
  choose vertex hvertex using fun o : Option (Fin L) => hsurj (tail o)
  have impossible : Function.Injective (fun a => f0 (vertex a)) := by
    intro a b he
    apply Classical.byContradiction
    intro hn
    have hne : vertex a ≠ vertex b := fun h => hn (tail_inj ((hvertex a).symm.trans
      ((congrArg pair h).trans (hvertex b))))
    have same : h0 (vertex a) = h0 (vertex b) := rank_eq H0 bnd0 he
    have upwards {a b : Option (Fin L)} (hr : TransGen P (vertex a) (vertex b)) : False := by
      have inc1 (a b : Fin m) (he : H1 a b) : height H1 a < height H1 b := height_lt ac1 he
      have inc2 (a b : Fin m) (he : H2 a b) : height H2 a < height H2 b := height_lt ac2 he
      have lt1 : (pair (vertex a)).1 < (pair (vertex b)).1 :=
        rank_lt H1 bnd1 (reach_lt inc1 (hr.mono into1))
      have lt2 : (pair (vertex a)).2 < (pair (vertex b)).2 :=
        rank_lt H2 bnd2 (reach_lt inc2 (hr.mono into2))
      rw [hvertex a, hvertex b] at lt1 lt2
      exact never lt1 lt2
    exact (totalP _ _ hne same).elim upwards upwards
  have : L + 1 ≤ L := by
    simpa [Nat.add_comm] using Fintype.card_le_of_injective _ impossible
  omega

end ColoredTournament
end Green88
