import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Relation

namespace Green88

open Relation

/-- A directed graph has no nonempty closed directed walk. -/
def Acyclic {V : Type*} (E : V → V → Prop) : Prop :=
  ∀ v, ¬ TransGen E v v

/-- A simple directed path, with vertices listed from first to last. -/
def DirectedPath {V : Type*} (E : V → V → Prop) (l : List V) : Prop :=
  l.Nodup ∧ l.Chain' E

/-- Every simple directed path has at most n vertices. -/
def PathBound {V : Type*} (E : V → V → Prop) (n : ℕ) : Prop :=
  ∀ l, DirectedPath E l → l.length ≤ n

namespace DirectedPath

variable {V : Type*} {E F : V → V → Prop}

theorem mono (hEF : E ≤ F) {l : List V} (hl : DirectedPath E l) : DirectedPath F l :=
  ⟨hl.1, hl.2.imp hEF⟩

theorem bound_mono (hEF : E ≤ F) {n : ℕ} (hF : PathBound F n) : PathBound E n :=
  fun l hl => hF l (mono hEF hl)

theorem reach_lt {α : Type*} [Preorder α] {f : V → α}
    (h : ∀ a b, E a b → f a < f b) {a b : V} (hab : TransGen E a b) : f a < f b := by
  induction hab with
  | single e => exact h _ _ e
  | tail _ e ih => exact ih.trans (h _ _ e)

theorem acyclic_of_increasing {α : Type*} [Preorder α] {f : V → α}
    (h : ∀ a b, E a b → f a < f b) : Acyclic E := fun v hv => (lt_irrefl (f v)) (reach_lt h hv)

theorem bound_of_increasing {f : V → ℕ} {n : ℕ}
    (hb : ∀ v, f v < n) (h : ∀ a b, E a b → f a < f b) : PathBound E n := by
  intro l hl
  let g (v : V) : Fin n := ⟨f v, hb v⟩
  have hs : (l.map g).Chain' (· < ·) := (List.chain'_map g).mpr (hl.2.imp h)
  have hn : (l.map g).Nodup := (List.chain'_iff_pairwise.mp hs).imp fun hlt => ne_of_lt hlt
  simpa using hn.length_le_card

private theorem acyclic_nodup (hE : Acyclic E) {l : List V} (hl : l.Chain' E) : l.Nodup := by
  have hh : l.Chain' (TransGen E) := hl.imp fun _ _ h => TransGen.single h
  rw [List.Nodup]
  apply (List.chain'_iff_pairwise.mp hh).imp
  intro a b hab he
  subst b
  exact hE a hab

/-- Maximum number of vertices in a simple directed path, including the empty path. -/
noncomputable def longest [Fintype V] (E : V → V → Prop) : ℕ := by
  classical
  exact Nat.findGreatest (fun k => ∃ l : List V, DirectedPath E l ∧ l.length = k) (Fintype.card V)

theorem longest_bound [Fintype V] (E : V → V → Prop) : PathBound E (longest E) := by
  classical
  intro l hl
  exact Nat.le_findGreatest hl.1.length_le_card ⟨l, hl, rfl⟩

theorem longest_attained [Fintype V] (E : V → V → Prop) :
    ∃ l : List V, DirectedPath E l ∧ l.length = longest E := by
  classical
  let P (k : ℕ) := ∃ l : List V, DirectedPath E l ∧ l.length = k
  have hzero : P 0 := ⟨[], by simp [DirectedPath], rfl⟩
  exact Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) hzero

theorem longest_le [Fintype V] {n : ℕ} (h : PathBound E n) : longest E ≤ n := by
  obtain ⟨l, hl, he⟩ := longest_attained E
  exact he ▸ h l hl

private def EndsWith (E : V → V → Prop) (v : V) (k : ℕ) : Prop :=
  ∃ l : List V, DirectedPath (flip E) (v :: l) ∧ (v :: l).length = k

/-- The largest size of a directed path ending at v. -/
noncomputable def height [Fintype V] (E : V → V → Prop) (v : V) : ℕ := by
  classical
  exact Nat.findGreatest (EndsWith E v) (Fintype.card V)

private theorem height_spec [Fintype V] (v : V) : EndsWith E v (height E v) := by
  classical
  have hs : DirectedPath (flip E) [v] := by simp [DirectedPath]
  exact Nat.findGreatest_spec hs.1.length_le_card ⟨[], hs, rfl⟩

theorem height_pos [Fintype V] (E : V → V → Prop) (v : V) : 0 < height E v := by
  obtain ⟨l, _, he⟩ := height_spec (E := E) v
  rw [← he]
  simp

theorem height_le [Fintype V] {n : ℕ} (hEF : E ≤ F) (hF : PathBound F n) (v : V) :
    height E v ≤ n := by
  obtain ⟨l, hl, he⟩ := height_spec (E := E) v
  have hb := hF (v :: l).reverse
    (mono hEF ⟨List.nodup_reverse.mpr hl.1, List.chain'_reverse.mpr hl.2⟩)
  simpa only [List.length_reverse, he] using hb

theorem height_lt [Fintype V] (hE : Acyclic E) {a b : V} (hab : E a b) :
    height E a < height E b := by
  classical
  obtain ⟨l, hl, he⟩ := height_spec (E := E) a
  have ha : Acyclic (flip E) := fun v hv => hE v hv.swap
  have hc : (b :: a :: l).Chain' (flip E) := hl.2.cons hab
  have hn := acyclic_nodup ha hc
  have hm : (b :: a :: l).length ≤ height E b :=
    Nat.le_findGreatest hn.length_le_card ⟨a :: l, ⟨hn, hc⟩, rfl⟩
  simp only [List.length_cons] at hm he
  omega

private theorem acyclic_add_edge (hE : Acyclic E) {a b : V} (hne : a ≠ b)
    (hback : ¬ TransGen E b a) : Acyclic (fun x y => E x y ∨ x = a ∧ y = b) := by
  have reduce {x y : V} (h : TransGen (fun x y => E x y ∨ x = a ∧ y = b) x y) :
      TransGen E x y ∨ ReflTransGen E x a ∧ ReflTransGen E b y := by
    induction h with
    | single h =>
        rcases h with h | ⟨rfl, rfl⟩
        · exact Or.inl (TransGen.single h)
        · exact Or.inr ⟨ReflTransGen.refl, ReflTransGen.refl⟩
    | tail _ he ih =>
        rcases ih with hold | ⟨hp, hs⟩
        · rcases he with he | ⟨rfl, rfl⟩
          · exact Or.inl (hold.tail he)
          · exact Or.inr ⟨hold.to_reflTransGen, ReflTransGen.refl⟩
        · rcases he with he | ⟨_, rfl⟩
          · exact Or.inr ⟨hp, hs.tail he⟩
          · exact Or.inr ⟨hp, ReflTransGen.refl⟩
  intro v hv
  rcases reduce hv with h | ⟨hp, hs⟩
  · exact hE v h
  · exact (reflTransGen_iff_eq_or_transGen.mp (hs.trans hp)).elim hne hback

/-- Extend a DAG inside a finite directed graph until each available edge's ends
are comparable by reachability. -/
theorem extend_acyclic [Finite V] (hEF : E ≤ F) (hE : Acyclic E)
    (loopless : ∀ v, ¬ F v v) :
    ∃ H : V → V → Prop, E ≤ H ∧ H ≤ F ∧ Acyclic H ∧
      ∀ a b, F a b → TransGen H a b ∨ TransGen H b a := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype Prop := Fintype.ofFinite Prop
  obtain ⟨H, hEH, hmax⟩ := Finite.exists_le_maximal (p := fun G => G ≤ F ∧ Acyclic G)
    ⟨hEF, hE⟩
  refine ⟨H, hEH, hmax.1.1, hmax.1.2, ?_⟩
  intro a b hab
  by_cases hback : TransGen H b a
  · exact Or.inr hback
  have hne : a ≠ b := fun e => loopless b (e ▸ hab)
  let G (x y : V) := H x y ∨ x = a ∧ y = b
  have hGF : G ≤ F := by
    intro x y h
    rcases h with h | ⟨rfl, rfl⟩
    · exact hmax.1.1 x y h
    · exact hab
  have hGH : G ≤ H := hmax.2 ⟨hGF, acyclic_add_edge hmax.1.2 hne hback⟩
    (fun _ _ => Or.inl)
  exact Or.inl (TransGen.single (hGH a b (Or.inr ⟨rfl, rfl⟩)))

private theorem insert_path (total : ∀ a b : V, a ≠ b → E a b ∨ E b a) (v : V) :
    ∀ l : List V, v ∉ l → l.Chain' E →
      ∃ w, (v :: l).Perm w ∧ w.Chain' E ∧ (w.head? = some v ∨ w.head? = l.head?) := by
  classical
  intro l
  induction l with
  | nil => exact fun _ _ => ⟨[v], List.Perm.refl _, List.chain'_singleton _, Or.inl rfl⟩
  | cons x l ih =>
      intro hv hl
      rcases total v x (fun h => hv (by simp [h])) with h | h
      · exact ⟨v :: x :: l, List.Perm.refl _, hl.cons h, Or.inl rfl⟩
      · obtain ⟨w, hw, hc, hh⟩ := ih (fun hm => hv (List.mem_cons_of_mem _ hm)) hl.tail
        have hchain : (x :: w).Chain' E := by
          apply hc.cons'
          intro y hy
          rcases hh with hh | hh
          · rw [hh] at hy
            simpa only [Option.mem_some_iff.mp hy] using h
          · exact hl.rel_head? (hh ▸ hy)
        exact ⟨x :: w, (List.Perm.swap x v l).trans (hw.cons x), hchain, Or.inr rfl⟩

/-- Rédei's theorem in each finite induced tournament. -/
theorem hamilton_path [DecidableEq V] (s : Finset V)
    (total : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → E a b ∨ E b a) :
    ∃ l : List V, DirectedPath E l ∧ ∀ v, v ∈ l ↔ v ∈ s := by
  classical
  let W := {v // v ∈ s}
  have localTotal (a b : W) (hne : a ≠ b) : E a.val b.val ∨ E b.val a.val :=
    total a.val a.prop b.val b.prop (fun h => hne (Subtype.ext h))
  have orderPath : ∀ l : List W, l.Nodup →
      ∃ w, l.Perm w ∧ w.Chain' (fun a b : W => E a.val b.val) := by
    intro l hl
    induction l with
    | nil => exact ⟨[], List.Perm.refl _, List.chain'_nil⟩
    | cons x l ih =>
        obtain ⟨w, hperm, hchain⟩ := ih (List.nodup_cons.mp hl).2
        have hn : x ∉ w := fun hw => (List.nodup_cons.mp hl).1 (hperm.mem_iff.mpr hw)
        obtain ⟨z, hz, hk, _⟩ := insert_path localTotal x w hn hchain
        exact ⟨z, (hperm.cons x).trans hz, hk⟩
  let all := (Finset.univ : Finset W).toList
  have hn : all.Nodup := Finset.nodup_toList _
  obtain ⟨w, hw, hc⟩ := orderPath all hn
  refine ⟨w.map Subtype.val, ⟨(hw.nodup hn).map Subtype.val_injective,
    (List.chain'_map Subtype.val).mpr hc⟩, ?_⟩
  intro v
  simp only [List.mem_map]
  refine ⟨fun ⟨a, _, h⟩ => h ▸ a.prop, fun hv => ?_⟩
  exact ⟨⟨v, hv⟩, hw.mem_iff.mp (by simp [all]), rfl⟩

end DirectedPath
end Green88
