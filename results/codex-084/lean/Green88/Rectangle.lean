import Green88.Basic
import Mathlib.Data.Finset.Sort

namespace Green88

/-- Points in the zero-based rectangular box with side lengths `r`. -/
def InRectangle (r : Fin 3 → ℕ) (S : Finset (Fin 3 → ℕ)) : Prop :=
  ∀ x ∈ S, ∀ i, x i < r i

/-- The set of values used on axis `i`. -/
def projection (S : Finset (Fin 3 → ℕ)) (i : Fin 3) : Finset ℕ :=
  S.image fun p => p i

theorem mem_projection {S : Finset (Fin 3 → ℕ)} {i : Fin 3} {v : ℕ} :
    v ∈ projection S i ↔ ∃ p ∈ S, p i = v :=
  Finset.mem_image

theorem comparable_subset {α : Type*} [LT α] {S T : Finset (Fin 3 → α)}
    (h : S ⊆ T) (hT : PairwiseComparable T) : PairwiseComparable S :=
  fun _ hx _ hy hne => hT (h hx) (h hy) hne

theorem projection_mono {S T : Finset (Fin 3 → ℕ)} (h : S ⊆ T) (i : Fin 3) :
    projection S i ⊆ projection T i :=
  Finset.image_subset_image h

theorem projection_card_le {S : Finset (Fin 3 → ℕ)} {r : Fin 3 → ℕ}
    (h : InRectangle r S) (i : Fin 3) : (projection S i).card ≤ r i := by
  have hs : projection S i ⊆ Finset.range (r i) := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := mem_projection.mp hv
    exact Finset.mem_range.mpr (h p hp i)
  simpa using Finset.card_le_card hs

theorem card_le_two_sides {S : Finset (Fin 3 → ℕ)} {r : Fin 3 → ℕ}
    (hS : PairwiseComparable S) (hr : InRectangle r S)
    {i j : Fin 3} (hij : i ≠ j) : S.card ≤ r i * r j := by
  let s := S.image fun p => (p i, p j)
  have hs : s ⊆ (Finset.range (r i)) ×ˢ (Finset.range (r j)) := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (hr p hp i), Finset.mem_range.mpr (hr p hp j)⟩
  rw [← Finset.card_image_of_injOn (projection_inj hS hij)]
  simpa only [Finset.card_product, Finset.card_range] using Finset.card_le_card hs

private def rankCoordinate (S : Finset (Fin 3 → ℕ)) (i : Fin 3) :
    (projection S i : Set ℕ) ≃o Fin (projection S i).card :=
  (Finset.orderIsoOfFin (projection S i) rfl).symm

/-- Replace each coordinate by its rank among values used on its own axis. -/
theorem compress {S : Finset (Fin 3 → ℕ)} (hS : PairwiseComparable S) :
    ∃ T : Finset (Fin 3 → ℕ), PairwiseComparable T ∧
      InRectangle (fun i => (projection S i).card) T ∧ T.card = S.card := by
  let rank (p : S) (i : Fin 3) : ℕ :=
    (rankCoordinate S i ⟨p.val i, mem_projection.mpr ⟨p.val, p.prop, rfl⟩⟩).val
  have hrank (p q : S) (i : Fin 3) (h : p.val i < q.val i) : rank p i < rank q i :=
    (rankCoordinate S i).strictMono h
  let emb : S ↪ (Fin 3 → ℕ) := ⟨rank, by
    intro p q h
    apply Subtype.ext
    funext i
    have hh := congrFun h i
    exact congrArg Subtype.val ((rankCoordinate S i).injective (Fin.ext hh))⟩
  let T := S.attach.map emb
  refine ⟨T, ?_, ?_, by simp [T]⟩
  · intro x hx y hy hne
    change x ∈ T at hx
    change y ∈ T at hy
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp hy
    have hne' : p.val ≠ q.val := fun e => hne (congrArg emb (Subtype.ext e))
    rcases hS p.prop q.prop hne' with ⟨i, j, hij, hi, hj⟩ | ⟨i, j, hij, hi, hj⟩
    · exact Or.inl ⟨i, j, hij, hrank p q i hi, hrank p q j hj⟩
    · exact Or.inr ⟨i, j, hij, hrank q p i hi, hrank q p j hj⟩
  · intro x hx i
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hx
    exact (rankCoordinate S i ⟨p.val i, mem_projection.mpr ⟨p.val, p.prop, rfl⟩⟩).isLt

end Green88
