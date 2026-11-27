import Green88.Selection
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace Green88

open scoped BigOperators

/-- One local offset for each coarse interval on each axis. -/
abbrev Samples (k : ℕ) (w : Fin 3 → ℕ) :=
  ∀ i : Fin 3, Fin k → Fin (w i)

private theorem card_split (k : ℕ) (w : Fin 3 → ℕ) (e : Fin 3 → Fin k)
    (A : ∀ i, Finset (Fin (w i))) :
    ((Finset.univ : Finset (Samples k w)).filter
      (fun f => ∀ i, f i (e i) ∈ A i)).card * (∏ i, w i) =
      (∏ i, (A i).card) * Fintype.card (Samples k w) := by
  classical
  let B (i : Fin 3) := {j : Fin k // j ≠ e i} → Fin (w i)
  let F (i : Fin 3) := (Equiv.funSplitAt (e i) (Fin (w i)))
  let T := {f : Samples k w // ∀ i, f i (e i) ∈ A i}
  let E : T ≃ (∀ i, (A i : Finset (Fin (w i)))) × (∀ i, B i) :=
    { toFun := fun f => (fun i => ⟨(F i (f.val i)).1, f.prop i⟩,
        fun i => (F i (f.val i)).2)
      invFun := fun f => ⟨fun i => (F i).symm ((f.1 i).val, f.2 i), by
        intro i
        have h := congrArg Prod.fst ((F i).apply_symm_apply ((f.1 i).val, f.2 i))
        change ((F i).symm ((f.1 i).val, f.2 i)) (e i) ∈ A i
        change ((F i).symm ((f.1 i).val, f.2 i)) (e i) = (f.1 i).val at h
        rw [h]
        exact (f.1 i).prop⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext i
        exact (F i).symm_apply_apply (f.val i)
      right_inv := by
        intro f
        apply Prod.ext <;> funext i
        · apply Subtype.ext
          exact congrArg Prod.fst ((F i).apply_symm_apply ((f.1 i).val, f.2 i))
        · exact congrArg Prod.snd ((F i).apply_symm_apply ((f.1 i).val, f.2 i)) }
  let E' : Samples k w ≃ (∀ i, Fin (w i)) × (∀ i, B i) :=
    { toFun := fun f => (fun i => (F i (f i)).1, fun i => (F i (f i)).2)
      invFun := fun f i => (F i).symm (f.1 i, f.2 i)
      left_inv := fun f => funext fun i => (F i).symm_apply_apply (f i)
      right_inv := fun f => Prod.ext
        (funext fun i => congrArg Prod.fst ((F i).apply_symm_apply (f.1 i, f.2 i)))
        (funext fun i => congrArg Prod.snd ((F i).apply_symm_apply (f.1 i, f.2 i))) }
  have hT := Fintype.card_congr E
  have hT' := Fintype.card_congr E'
  have hfilter : Fintype.card T = ((Finset.univ : Finset (Samples k w)).filter
      (fun f => ∀ i, f i (e i) ∈ A i)).card := Fintype.card_subtype _
  rw [← hfilter, hT, hT']
  simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_coe, Fintype.card_fin]
  ac_rfl

/-- Double count a finite relation by its rows and its columns. -/
theorem sum_filter_card_comm {α β : Type*} (s : Finset α) (t : Finset β)
    (P : α → β → Prop) [DecidableRel P] :
    (∑ x ∈ s, ((t.filter (P x)).card : ℝ)) =
    (∑ y ∈ t, ((s.filter (fun x => P x y)).card : ℝ)) := by
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  exact Finset.sum_comm

/-- Count the average number of marked boxes using independent coordinate offsets. -/
theorem sampling_bound {k : ℕ} {w : Fin 3 → ℕ} (hw : ∀ i, 0 < w i)
    (R : Finset (Fin 3 → Fin k)) (A : (Fin 3 → Fin k) → ∀ i, Finset (Fin (w i)))
    (η : ℝ) (C : ℕ)
    (hheavy : ∀ e ∈ R, η ≤ (∏ i, ((A e i).card : ℝ)) / (∏ i, (w i : ℝ)))
    (hmark : ∀ f : Samples k w, (R.filter (fun e => ∀ i, f i (e i) ∈ A e i)).card ≤ C) :
    η * R.card ≤ (C : ℝ) := by
  classical
  let T : Finset (Samples k w) := Finset.univ
  have hw' : 0 < ∏ i, (w i : ℝ) := Finset.prod_pos (fun i _ => by exact_mod_cast hw i)
  have hT : 0 < (T.card : ℝ) := by
    have hnonempty : T.Nonempty := ⟨fun i _ => ⟨0, hw i⟩, Finset.mem_univ _⟩
    exact_mod_cast Finset.card_pos.mpr hnonempty
  have hp (e : Fin 3 → Fin k) :
      ((T.filter (fun f => ∀ i, f i (e i) ∈ A e i)).card : ℝ) =
        ((∏ i, ((A e i).card : ℝ)) / (∏ i, (w i : ℝ))) * T.card := by
    have h := card_split k w e (A e)
    have h' : ((T.filter (fun f => ∀ i, f i (e i) ∈ A e i)).card : ℝ) *
      (∏ i, (w i : ℝ)) = (∏ i, ((A e i).card : ℝ)) * T.card := by
      exact_mod_cast h
    have h'' := (eq_div_iff hw'.ne').mpr h'
    simpa only [div_mul_eq_mul_div] using h''
  apply (mul_le_mul_right hT).mp
  calc
    η * (R.card : ℝ) * T.card = ∑ _e ∈ R, η * (T.card : ℝ) := by simp; ring
    _ ≤ ∑ e ∈ R, ((T.filter (fun f => ∀ i, f i (e i) ∈ A e i)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      rw [hp]
      exact mul_le_mul_of_nonneg_right (hheavy e he) hT.le
    _ = ∑ f ∈ T, ((R.filter (fun e => ∀ i, f i (e i) ∈ A e i)).card : ℝ) :=
      sum_filter_card_comm R T _
    _ ≤ ∑ _f ∈ T, (C : ℝ) := Finset.sum_le_sum fun f _ => by exact_mod_cast hmark f
    _ = (C : ℝ) * T.card := by simp [mul_comm]

end Green88
