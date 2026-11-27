import Green88.DirectedPaths
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega
import Aesop

namespace Green88
namespace DirectedPath

variable {V : Type*} [DecidableEq V]

/-- A depth-first search frontier, read from the newest active vertex back to its root. -/
private structure Frontier (E : V → V → Prop) (s done : Finset V)
    (stack : List V) (unseen : Finset V) : Prop where
  path : DirectedPath (flip E) stack
  cover : ∀ v, v ∈ s ↔ v ∈ done ∨ v ∈ stack ∨ v ∈ unseen
  done_stack : ∀ v ∈ done, v ∉ stack
  done_unseen : ∀ v ∈ done, v ∉ unseen
  stack_unseen : ∀ v ∈ stack, v ∉ unseen
  size : done.card + stack.length + unseen.card = s.card
  closed : ∀ a ∈ done, ∀ b ∈ unseen, ¬ E a b

private theorem Frontier.push {E : V → V → Prop} {s done unseen : Finset V} {stack : List V}
    (h : Frontier E s done stack unseen) {v : V} (hv : v ∈ unseen)
    (next : ∀ a ∈ stack.head?, E a v) :
    Frontier E s done (v :: stack) (unseen.erase v) := by
  have hvStack : v ∉ stack := fun hm => h.stack_unseen v hm hv
  have hvDone : v ∉ done := fun hm => h.done_unseen v hm hv
  refine ⟨⟨List.nodup_cons.mpr ⟨hvStack, h.path.1⟩, h.path.2.cons' next⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [h.cover x, List.mem_cons, Finset.mem_erase]
    by_cases hx : x = v
    · simp [hx, hv]
    · simp [hx]
  · intro x hx
    simp only [List.mem_cons, not_or]
    exact ⟨fun he => hvDone (he ▸ hx), h.done_stack x hx⟩
  · exact fun x hx hm => h.done_unseen x hx (Finset.mem_erase.mp hm).2
  · intro x hx hm
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (Finset.mem_erase.mp hm).1 rfl
    · exact h.stack_unseen x hx (Finset.mem_erase.mp hm).2
  · have hs := h.size
    have hp := Finset.card_pos.mpr ⟨v, hv⟩
    rw [List.length_cons, Finset.card_erase_of_mem hv]
    omega
  · exact fun a ha b hb => h.closed a ha b (Finset.mem_erase.mp hb).2

private theorem Frontier.pop {E : V → V → Prop} {s done unseen : Finset V} {v : V} {stack : List V}
    (h : Frontier E s done (v :: stack) unseen) (next : ∀ b ∈ unseen, ¬ E v b) :
    Frontier E s (insert v done) stack unseen := by
  have hv : v ∉ done := fun hm => h.done_stack v hm (List.mem_cons_self ..)
  refine ⟨⟨(List.nodup_cons.mp h.path.1).2, h.path.2.tail⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [h.cover x, Finset.mem_insert, List.mem_cons]
    tauto
  · intro x hx hh
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (List.nodup_cons.mp h.path.1).1 hh
    · exact h.done_stack x hx (List.mem_cons_of_mem _ hh)
  · intro x hx hh
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact h.stack_unseen x (List.mem_cons_self ..) hh
    · exact h.done_unseen x hx hh
  · exact fun x hx => h.stack_unseen x (List.mem_cons_of_mem _ hx)
  · have hs := h.size
    rw [Finset.card_insert_of_not_mem hv]
    simp only [List.length_cons] at hs
    omega
  · intro a ha b hb
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact next b hb
    · exact h.closed a ha b hb

private theorem finish_cut {E : V → V → Prop} {s : Finset V} {k : ℕ} (hk : k ≤ s.card) :
    ∃ done stack unseen, Frontier E s done stack unseen ∧ done.card = k := by
  classical
  have advance : ∀ fuel (done : Finset V) (stack : List V) (unseen : Finset V),
      2 * unseen.card + stack.length = fuel → Frontier E s done stack unseen →
      done.card ≤ k →
      ∃ f p u, Frontier E s f p u ∧ f.card = k := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
      intro done stack unseen hFuel state hDone
      by_cases hEq : done.card = k
      · exact ⟨done, stack, unseen, state, hEq⟩
      have push (v : V) (hv : v ∈ unseen) (next : ∀ a ∈ stack.head?, E a v) :
          ∃ f p u, Frontier E s f p u ∧ f.card = k := by
        apply ih (2 * (unseen.erase v).card + (v :: stack).length) _ done (v :: stack)
          (unseen.erase v) rfl (state.push hv next) hDone
        have hp := Finset.card_pos.mpr ⟨v, hv⟩
        rw [Finset.card_erase_of_mem hv, List.length_cons]
        omega
      cases stack with
      | nil =>
        obtain ⟨v, hv⟩ : unseen.Nonempty := by
          apply Finset.card_pos.mp
          have hs := state.size
          simp only [List.length_nil, Nat.add_zero] at hs
          omega
        exact push v hv (by simp)
      | cons v stack =>
        by_cases hNext : ∃ w ∈ unseen, E v w
        · obtain ⟨w, hw, he⟩ := hNext
          exact push w hw (by simpa)
        · have hclosed : ∀ w ∈ unseen, ¬ E v w := fun w hw he => hNext ⟨w, hw, he⟩
          refine ih (2 * unseen.card + stack.length) ?_ (insert v done) stack unseen
            rfl (state.pop hclosed) ?_
          · simp only [List.length_cons] at hFuel
            omega
          · have hv : v ∉ done := fun hm => state.done_stack v hm (List.mem_cons_self ..)
            rw [Finset.card_insert_of_not_mem hv]
            omega
  exact advance _ ∅ [] s rfl
    ⟨by simp [DirectedPath], by simp, by simp, by simp, by simp, by simp, by simp⟩ (by simp)

omit [DecidableEq V] in
private theorem reverse_path {E : V → V → Prop} {l : List V}
    (h : DirectedPath (flip E) l) : DirectedPath E l.reverse :=
  ⟨List.nodup_reverse.mpr h.1, List.chain'_reverse.mpr h.2⟩

/-- Keep an ordered partition into blocks of size at most k. Edges between the kept
blocks all point towards smaller block numbers. Each full block costs at most L
deleted vertices, where L bounds the number of vertices on a simple directed path. -/
theorem ordered_blocks {E : V → V → Prop} {L k : ℕ} (hL : PathBound E L) (hk : 0 < k)
    (s : Finset V) :
    ∃ (w : Finset V) (block : V → ℕ), w ⊆ s ∧
      (s.card - w.card) * k ≤ s.card * L ∧
      (∀ a : ℕ, (w.filter fun v => block v = a).card ≤ k) ∧
      ∀ a ∈ w, ∀ b ∈ w, E a b → block b ≤ block a := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s.card ≤ k
    · exact ⟨s, fun _ => 0, fun _ h => h, by simp,
        fun _ => (Finset.card_filter_le ..).trans hs, fun _ _ _ _ _ => le_rfl⟩
    obtain ⟨f, p, u, h, hf⟩ := finish_cut (E := E) (by omega : k ≤ s.card)
    have hfs : f ⊆ s := fun v hv => (h.cover v).mpr (Or.inl hv)
    have hus : u ⊆ s := fun v hv => (h.cover v).mpr (Or.inr (Or.inr hv))
    have hp : p.length ≤ L := by simpa using hL p.reverse (reverse_path h.path)
    have hsize := h.size
    have huCard : u.card < s.card := by omega
    have hproper : u ⊂ s := Finset.ssubset_iff_subset_ne.mpr
      ⟨hus, fun he => huCard.ne (congrArg Finset.card he)⟩
    obtain ⟨v, b, hvu, hvbudget, hvblock, hvedge⟩ := ih u hproper
    have hdis : Disjoint f v := Finset.disjoint_left.mpr fun x hx hxv =>
      h.done_unseen x hx (hvu hxv)
    let label (x : V) := if x ∈ f then 0 else b x + 1
    have hcard : (f ∪ v).card = k + v.card := by rw [Finset.card_union_of_disjoint hdis, hf]
    have hvCard : v.card ≤ u.card := Finset.card_le_card hvu
    refine ⟨f ∪ v, label, Finset.union_subset hfs (hvu.trans hus), ?_, ?_, ?_⟩
    · rw [hcard, show s.card - (k + v.card) = p.length + (u.card - v.card) by omega, Nat.add_mul]
      calc
        _ ≤ L * k + u.card * L := Nat.add_le_add (Nat.mul_le_mul_right k hp) hvbudget
        _ = (k + u.card) * L := by rw [Nat.add_mul, Nat.mul_comm L k]
        _ ≤ _ := Nat.mul_le_mul_right L (by omega)
    · intro a
      cases a with
      | zero =>
        have hsub : ((f ∪ v).filter fun x => label x = 0) ⊆ f := by
          intro x hx
          simpa [label] using (Finset.mem_filter.mp hx).2
        exact (Finset.card_le_card hsub).trans hf.le
      | succ a =>
        have hsub : ((f ∪ v).filter fun x => label x = a + 1) ⊆ v.filter (fun x => b x = a) := by
          intro x hx
          obtain ⟨hx, hl⟩ := Finset.mem_filter.mp hx
          rcases Finset.mem_union.mp hx with hx | hx
          · simp [label, hx] at hl
          · have hn : x ∉ f := fun hxf => Finset.disjoint_left.mp hdis hxf hx
            exact Finset.mem_filter.mpr ⟨hx, by simpa [label, hn] using hl⟩
        exact (Finset.card_le_card hsub).trans (hvblock a)
    · intro x hx y hy he
      rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
      · simp [label, hx, hy]
      · exact (h.closed x hx y (hvu hy) he).elim
      · simp [label, hy]
      · have hn : x ∉ f := fun he => Finset.disjoint_left.mp hdis he hx
        have hm : y ∉ f := fun he => Finset.disjoint_left.mp hdis he hy
        simpa [label, hn, hm] using hvedge x hx y hy he

end DirectedPath
end Green88
