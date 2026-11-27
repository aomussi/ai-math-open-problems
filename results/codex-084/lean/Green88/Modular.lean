import Green88.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic

namespace Green88

/-- The residues represented by the integers from 1 to `p / 2`.
For odd `p` this is Green's half-interval `{1, …, (p - 1) / 2}`. -/
def InPositiveHalf {p : ℕ} (x : ZMod p) : Prop :=
  0 < x.val ∧ x.val ≤ p / 2

/-- The six coordinate permutations of Green's forbidden differences. -/
def ForbiddenModularDifference {p : ℕ} (x : Fin 3 → ZMod p) : Prop :=
  ∃ i j k : Fin 3, i ≠ j ∧ j ≠ k ∧ k ≠ i ∧
    x i = 0 ∧ InPositiveHalf (x j) ∧ InPositiveHalf (-x k)

/-- The difference set of `A` is disjoint from the forbidden differences. -/
def ModularAdmissible {p : ℕ} (A : Finset (Fin 3 → ZMod p)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ¬ ForbiddenModularDifference (fun i => x i - y i)

private theorem half_of_nonzero {p : ℕ} [NeZero p] {a : ZMod p} (ha : a ≠ 0) :
    InPositiveHalf a ∨ InPositiveHalf (-a) := by
  have hval := a.val_lt
  have hpos : 0 < a.val := Nat.pos_of_ne_zero fun h => ha ((ZMod.val_eq_zero a).mp h)
  rw [InPositiveHalf, InPositiveHalf, ZMod.neg_val, if_neg ha]
  by_cases h : a.val ≤ p / 2
  · exact Or.inl ⟨hpos, h⟩
  · exact Or.inr ⟨by omega, by omega⟩

private theorem not_both_halves {p : ℕ} [NeZero p] (hp : Odd p) (a : ZMod p) :
    ¬ (InPositiveHalf a ∧ InPositiveHalf (-a)) := by
  rintro ⟨⟨hpos, hle⟩, ⟨_, hneg⟩⟩
  have hval := a.val_lt
  have ha : a ≠ 0 := by
    intro h
    simp [h] at hpos
  rw [ZMod.neg_val, if_neg ha] at hneg
  obtain ⟨k, hk⟩ := hp
  omega

private def planePoint {p : ℕ} (a b : ZMod p) (i : Fin 3) : ZMod p :=
  if i = 1 then b else a

@[simp] private theorem planePoint_zero {p : ℕ} (a b : ZMod p) : planePoint a b 0 = a := by
  simp [planePoint]

@[simp] private theorem planePoint_one {p : ℕ} (a b : ZMod p) : planePoint a b 1 = b := by
  simp [planePoint]

@[simp] private theorem planePoint_two {p : ℕ} (a b : ZMod p) : planePoint a b 2 = a := by
  simp [planePoint]

private theorem plane_avoids {p : ℕ} [NeZero p] (hp : Odd p) (a b : ZMod p) :
    ¬ ForbiddenModularDifference (planePoint a b) := by
  rintro ⟨i, j, k, hij, hjk, hki, hi, hj, hk⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [planePoint, InPositiveHalf] <;> exact not_both_halves hp a ⟨hj, hk⟩

private def planeEmbedding (p : ℕ) : (ZMod p × ZMod p) ↪ (Fin 3 → ZMod p) where
  toFun u := planePoint u.1 u.2
  inj' := by
    intro x y h
    exact Prod.ext (by simpa using congrFun h 0) (by simpa using congrFun h 1)

private theorem plane_attains {p : ℕ} [NeZero p] (hp : Odd p) :
    ∃ A : Finset (Fin 3 → ZMod p), ModularAdmissible A ∧ A.card = p ^ 2 := by
  classical
  refine ⟨Finset.univ.map (planeEmbedding p), ?_, by simp [ZMod.card, pow_two]⟩
  intro x hx y hy
  obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp hy
  have hd : (fun i => planeEmbedding p a i - planeEmbedding p b i) =
      planePoint (a.1 - b.1) (a.2 - b.2) := by
    funext i
    by_cases hi : i = 1 <;> simp [planeEmbedding, planePoint, hi]
  rw [hd]
  exact plane_avoids hp _ _

private theorem modular_projection_injective {p : ℕ} [NeZero p]
    {A : Finset (Fin 3 → ZMod p)} (hA : ModularAdmissible A) :
    Set.InjOn (fun x : Fin 3 → ZMod p => (x 0, x 1 + x 2)) A := by
  intro x hx y hy he
  have h0 : x 0 = y 0 := congrArg Prod.fst he
  have hs : x 1 + x 2 = y 1 + y 2 := congrArg Prod.snd he
  let d := x 1 - y 1
  have hsum : d + (x 2 - y 2) = 0 := by
    dsimp [d]
    rw [← add_sub_add_comm, hs, sub_self]
  have h2 : x 2 - y 2 = -d := (eq_neg_of_add_eq_zero_right hsum)
  by_cases hd : d = 0
  · have h1 : x 1 = y 1 := sub_eq_zero.mp hd
    have h2' : x 2 = y 2 := sub_eq_zero.mp (by simpa [hd] using h2)
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2'
  · exfalso
    apply hA x hx y hy
    have z : x 0 - y 0 = 0 := sub_eq_zero.mpr h0
    rcases half_of_nonzero hd with hp | hn
    · refine ⟨0, 1, 2, by decide, by decide, by decide, z, hp, ?_⟩
      simpa only [h2, neg_neg] using hp
    · refine ⟨0, 2, 1, by decide, by decide, by decide, z, ?_, hn⟩
      change InPositiveHalf (x 2 - y 2)
      rw [h2]
      exact hn

/-- Every admissible set has at most `p²` elements for a positive modulus `p`. -/
theorem modular_upper_bound {p : ℕ} [NeZero p] {A : Finset (Fin 3 → ZMod p)}
    (hA : ModularAdmissible A) : A.card ≤ p ^ 2 := by
  classical
  calc
    A.card = (A.image (fun x => (x 0, x 1 + x 2))).card :=
      (Finset.card_image_of_injOn (modular_projection_injective hA)).symm
    _ ≤ Fintype.card (ZMod p × ZMod p) := Finset.card_le_univ _
    _ = p ^ 2 := by simp [ZMod.card, pow_two]

/-- Green's modular problem has extremal value `p²` for every odd modulus. -/
theorem modular_exact {p : ℕ} (hp : Odd p) :
    (∀ A : Finset (Fin 3 → ZMod p), ModularAdmissible A → A.card ≤ p ^ 2) ∧
    ∃ A : Finset (Fin 3 → ZMod p), ModularAdmissible A ∧ A.card = p ^ 2 := by
  letI : NeZero p := ⟨by obtain ⟨k, hk⟩ := hp; omega⟩
  exact ⟨fun _ => modular_upper_bound, plane_attains hp⟩

/-- The finite-field formulation in the comments to Green's Problem 88. -/
theorem modular_prime_exact {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    (∀ A : Finset (Fin 3 → ZMod p), ModularAdmissible A → A.card ≤ p ^ 2) ∧
    ∃ A : Finset (Fin 3 → ZMod p), ModularAdmissible A ∧ A.card = p ^ 2 :=
  modular_exact (hp.eq_two_or_odd'.resolve_left hodd)

#print axioms modular_exact
#print axioms modular_prime_exact

end Green88
