import Green88.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Logic.Equiv.Fin.Basic

namespace Green88

private def digitPair {n m : ℕ} :
    ((Fin 3 → Fin n) × (Fin 3 → Fin m)) ↪ (Fin 3 → Fin (n * m)) where
  toFun p i := finProdFinEquiv (p.1 i, p.2 i)
  inj' := by
    intro p q h
    have h' (i : Fin 3) := finProdFinEquiv.injective (congrFun h i)
    exact Prod.ext (funext fun i => congrArg Prod.fst (h' i))
      (funext fun i => congrArg Prod.snd (h' i))

private theorem digit_lt_left {n m : ℕ} {a b : Fin n} {c d : Fin m} (h : a < b) :
    finProdFinEquiv (a, c) < finProdFinEquiv (b, d) := by
  change c.val + m * a.val < d.val + m * b.val
  have h' : a.val + 1 ≤ b.val := h
  calc
    c.val + m * a.val < m + m * a.val := Nat.add_lt_add_right c.isLt _
    _ = m * (a.val + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    _ ≤ m * b.val := Nat.mul_le_mul_left _ h'
    _ ≤ d.val + m * b.val := Nat.le_add_left _ _

private theorem digit_lt_right {n m : ℕ} {a : Fin n} {c d : Fin m} (h : c < d) :
    finProdFinEquiv (a, c) < finProdFinEquiv (a, d) :=
  Nat.add_lt_add_right h _

/-- The two-factor lexicographic product of pairwise comparable sets. -/
theorem tensor {n m : ℕ} {S : Finset (Fin 3 → Fin n)} {T : Finset (Fin 3 → Fin m)}
    (hS : PairwiseComparable S) (hT : PairwiseComparable T) :
    ∃ U : Finset (Fin 3 → Fin (n * m)), PairwiseComparable U ∧ U.card = S.card * T.card := by
  refine ⟨(S ×ˢ T).map digitPair, ?_, by rw [Finset.card_map, Finset.card_product]⟩
  intro x hx y hy hxy
  change x ∈ (S ×ˢ T).map digitPair at hx
  change y ∈ (S ×ˢ T).map digitPair at hy
  obtain ⟨⟨p, r⟩, hp, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨⟨q, s⟩, hq, rfl⟩ := Finset.mem_map.mp hy
  obtain ⟨hp, hr⟩ := Finset.mem_product.mp hp
  obtain ⟨hq, hs⟩ := Finset.mem_product.mp hq
  by_cases e : p = q
  · subst q
    have hne : r ≠ s := fun er => hxy (er ▸ rfl)
    rcases hT hr hs hne with ⟨i, j, hij, hi, hj⟩ | ⟨i, j, hij, hi, hj⟩
    · exact Or.inl ⟨i, j, hij, digit_lt_right hi, digit_lt_right hj⟩
    · exact Or.inr ⟨i, j, hij, digit_lt_right hi, digit_lt_right hj⟩
  · rcases hS hp hq e with ⟨i, j, hij, hi, hj⟩ | ⟨i, j, hij, hi, hj⟩
    · exact Or.inl ⟨i, j, hij, digit_lt_left hi, digit_lt_left hj⟩
    · exact Or.inr ⟨i, j, hij, digit_lt_left hi, digit_lt_left hj⟩

theorem tensor_power {n : ℕ} {S : Finset (Fin 3 → Fin n)} (hS : PairwiseComparable S)
    (t : ℕ) : ∃ U : Finset (Fin 3 → Fin (n ^ t)), PairwiseComparable U ∧ U.card = S.card ^ t := by
  induction t with
  | zero =>
      let u : Fin 3 → Fin (n ^ 0) := fun _ => ⟨0, by simp⟩
      exact ⟨{u}, by simp [PairwiseComparable], by simp⟩
  | succ t ih =>
      rw [pow_succ, pow_succ]
      obtain ⟨U, hU, hcard⟩ := ih
      simpa only [hcard] using tensor hU hS

/-- A uniform positive prefactor can be removed by tensoring. -/
theorem remove_prefactor {q C : ℝ}
    (bound : ∀ (n : ℕ) (S : Finset (Fin 3 → Fin n)),
      PairwiseComparable S → (S.card : ℝ) ≤ C * (n : ℝ) ^ q)
    (n : ℕ) (S : Finset (Fin 3 → Fin n)) (hS : PairwiseComparable S) :
    (S.card : ℝ) ≤ (n : ℝ) ^ q := by
  by_cases hn : n = 0
  · subst n
    have hc : S.card = 0 := Nat.eq_zero_of_le_zero (by simpa using card_le_square hS)
    simpa only [hc, Nat.cast_zero] using Real.rpow_nonneg (x := 0) le_rfl q
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  let z := (n : ℝ) ^ q
  have hz : 0 < z := Real.rpow_pos_of_pos hn' _
  by_contra! h
  have hratio : 1 < (S.card : ℝ) / z := (lt_div_iff₀ hz).2 (by simpa [z] using h)
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt C hratio
  obtain ⟨U, hU, hcard⟩ := tensor_power hS t
  have hbound := bound (n ^ t) U hU
  rw [hcard, Nat.cast_pow, Nat.cast_pow, ← Real.rpow_natCast_mul hn'.le,
    mul_comm (t : ℝ) q, Real.rpow_mul hn'.le, Real.rpow_natCast] at hbound
  rw [div_pow] at ht
  exact (not_lt_of_ge hbound) ((lt_div_iff₀ (pow_pos hz _)).1 ht)

end Green88
