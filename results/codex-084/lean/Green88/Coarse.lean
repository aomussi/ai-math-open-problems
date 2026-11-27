import Green88.Rectangle
import Green88.Selection
import Green88.Sampling
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.GCongr

namespace Green88

open scoped BigOperators

/-- The coarse index of a coordinate, extended monotonically beyond the box. -/
def index {k : ℕ} (hk : 0 < k) (width x : ℕ) : Fin k :=
  ⟨min (x / width) (k - 1), lt_of_le_of_lt (min_le_right _ _) (by omega)⟩

theorem index_mono {k : ℕ} (hk : 0 < k) (w : ℕ) : Monotone (index hk w) := by
  intro x y h
  exact min_le_min (Nat.div_le_div_right h) le_rfl

theorem index_val {k w x : ℕ} (hk : 0 < k) (hw : 0 < w) (hx : x < k * w) :
    (index hk w x).val = x / w :=
  min_eq_left (by have h := (Nat.div_lt_iff_lt_mul hw).mpr hx; omega)

/-- The fiber of the point-set over one tuple of coarse indices. -/
def cell {k : ℕ} (hk : 0 < k) (w : Fin 3 → ℕ)
    (S : Finset (Fin 3 → ℕ)) (e : Fin 3 → Fin k) : Finset (Fin 3 → ℕ) :=
  S.filter fun p => ∀ i, index hk (w i) (p i) = e i

theorem mem_cell {k : ℕ} {hk : 0 < k} {w : Fin 3 → ℕ}
    {S : Finset (Fin 3 → ℕ)} {e : Fin 3 → Fin k} {p : Fin 3 → ℕ} :
    p ∈ cell hk w S e ↔ p ∈ S ∧ ∀ i, index hk (w i) (p i) = e i :=
  Finset.mem_filter

theorem cell_subset {k : ℕ} (hk : 0 < k) (w : Fin 3 → ℕ)
    (S : Finset (Fin 3 → ℕ)) (e : Fin 3 → Fin k) : cell hk w S e ⊆ S :=
  Finset.filter_subset _ _

theorem sum_cell_card {k : ℕ} (hk : 0 < k) (w : Fin 3 → ℕ)
    (S : Finset (Fin 3 → ℕ)) :
    (∑ e : Fin 3 → Fin k, ((cell hk w S e).card : ℝ)) = S.card := by
  have h : (∑ e : Fin 3 → Fin k, (S.filter fun p =>
      (fun i => index hk (w i) (p i)) = e).card) = S.card := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter S
      (Finset.univ : Finset (Fin 3 → Fin k)) (fun p i => index hk (w i) (p i))
  exact_mod_cast (by simpa only [funext_iff, cell] using h :
    (∑ e : Fin 3 → Fin k, (cell hk w S e).card) = S.card)

theorem cell_interval {k : ℕ} {hk : 0 < k} {w r : Fin 3 → ℕ}
    (hw : ∀ i, 0 < w i) (hrw : ∀ i, r i ≤ k * w i)
    {S : Finset (Fin 3 → ℕ)} (hr : InRectangle r S)
    {e : Fin 3 → Fin k} {p : Fin 3 → ℕ} (hp : p ∈ cell hk w S e) (i : Fin 3) :
    (e i).val * w i ≤ p i ∧ p i < (e i).val * w i + w i := by
  have h := index_val hk (hw i) ((hr p (mem_cell.mp hp).1 i).trans_le (hrw i))
  rw [(mem_cell.mp hp).2 i] at h
  have he : p i % w i + (e i).val * w i = p i := by
    rw [h, Nat.mul_comm (p i / w i)]
    exact Nat.mod_add_div _ _
  have hmod := Nat.mod_lt (p i) (hw i)
  omega

/-- Every projection of a single box uses at most the corresponding interval width. -/
theorem cell_projection_le {k : ℕ} {hk : 0 < k} {w r : Fin 3 → ℕ}
    (hw : ∀ i, 0 < w i) (hrw : ∀ i, r i ≤ k * w i)
    {S : Finset (Fin 3 → ℕ)} (hr : InRectangle r S) (e : Fin 3 → Fin k) (i : Fin 3) :
    (projection (cell hk w S e) i).card ≤ w i := by
  have sub : projection (cell hk w S e) i ⊆
      Finset.Ico ((e i).val * w i) ((e i).val * w i + w i) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_projection.mp hx
    exact Finset.mem_Ico.mpr (cell_interval hw hrw hr hp i)
  simpa using Finset.card_le_card sub

/-- Local offsets which appear in the projection of a box. -/
def offsets {k : ℕ} (hk : 0 < k) (w : Fin 3 → ℕ)
    (S : Finset (Fin 3 → ℕ)) (e : Fin 3 → Fin k) (i : Fin 3) : Finset (Fin (w i)) :=
  Finset.univ.filter fun x => (e i).val * w i + x.val ∈ projection (cell hk w S e) i

theorem card_offsets {k : ℕ} {hk : 0 < k} {w r : Fin 3 → ℕ}
    (hw : ∀ i, 0 < w i) (hrw : ∀ i, r i ≤ k * w i)
    {S : Finset (Fin 3 → ℕ)} (hr : InRectangle r S) (e : Fin 3 → Fin k) (i : Fin 3) :
    (offsets hk w S e i).card = (projection (cell hk w S e) i).card := by
  apply Finset.card_nbij (fun x : Fin (w i) => (e i).val * w i + x.val)
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x _ y _ eq
    apply Fin.ext
    exact Nat.add_left_cancel eq
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_projection.mp hx
    obtain ⟨hle, hlt⟩ := cell_interval hw hrw hr hp i
    exact ⟨⟨p i - (e i).val * w i, by omega⟩, by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa only [Nat.add_sub_of_le hle] using hx⟩,
      Nat.add_sub_of_le hle⟩

theorem occurs_bound {k : ℕ} (hk : 0 < k) (w : Fin 3 → ℕ)
    {S : Finset (Fin 3 → ℕ)} (hS : PairwiseComparable S) (i : Fin 3) (x : ℕ) :
    ((Finset.univ : Finset (Fin 3 → Fin k)).filter
      (fun e => x ∈ projection (cell hk w S e) i)).card ≤ 2 * k := by
  classical
  let E := (Finset.univ : Finset (Fin 3 → Fin k)).filter
    (fun e => x ∈ projection (cell hk w S e) i)
  obtain ⟨j, l, hjl, hij, hil⟩ : ∃ j l : Fin 3, j ≠ l ∧ i ≠ j ∧ i ≠ l := by
    fin_cases i <;> decide
  have hc := Finset.card_le_card_of_injOn
    (s := E) (t := Finset.range (2 * k)) (fun e => (e j).val + (e l).val)
    (fun e _ => Finset.mem_range.mpr (by
      change (e j).val + (e l).val < 2 * k
      have hj := (e j).isLt
      have hl := (e l).isLt
      omega))
    ?_
  · simpa using hc
  · intro e he f hf heq
    have he' : e ∈ E := he
    have hf' : f ∈ E := hf
    obtain ⟨p, hp, hpx⟩ := mem_projection.mp (Finset.mem_filter.mp he').2
    obtain ⟨q, hq, hqx⟩ := mem_projection.mp (Finset.mem_filter.mp hf').2
    have hpe := (mem_cell.mp hp).2
    have hqf := (mem_cell.mp hq).2
    have hi : e i = f i := by rw [← hpe i, ← hqf i, hpx, hqx]
    by_cases hpq : p = q
    · subst q
      exact funext fun t => (hpe t).symm.trans (hqf t)
    have chain := section_chain hjl hij hil (hpx.trans hqx.symm)
      (hS (mem_cell.mp hp).1 (mem_cell.mp hq).1 hpq)
    have mono (t : Fin 3) : p t ≤ q t → e t ≤ f t := by
      intro h
      simpa [hpe, hqf] using index_mono hk (w t) h
    have mono' (t : Fin 3) : q t ≤ p t → f t ≤ e t := by
      intro h
      simpa [hpe, hqf] using index_mono hk (w t) h
    change (e j).val + (e l).val = (f j).val + (f l).val at heq
    have direction : ((e j).val ≤ (f j).val ∧ (e l).val ≤ (f l).val) ∨
        ((f j).val ≤ (e j).val ∧ (f l).val ≤ (e l).val) :=
      chain.elim (fun h => Or.inl ⟨mono j h.1.le, mono l h.2.le⟩)
        (fun h => Or.inr ⟨mono' j h.1.le, mono' l h.2.le⟩)
    have hje : e j = f j := Fin.ext (by omega)
    have hle : e l = f l := Fin.ext (by omega)
    funext t
    by_cases hti : t = i
    · simpa [hti] using hi
    by_cases htj : t = j
    · simpa [htj] using hje
    have htl := fin3_eq_of_ne hij hti htj hil.symm hjl.symm
    simpa [htl] using hle

/-- Bound the total size of the projections along any one axis. -/
theorem sum_projection_bound {k : ℕ} (hk : 0 < k) (w : Fin 3 → ℕ)
    {r : Fin 3 → ℕ} {S : Finset (Fin 3 → ℕ)} (hS : PairwiseComparable S)
    (hr : InRectangle r S) (i : Fin 3) :
    (∑ e : Fin 3 → Fin k, ((projection (cell hk w S e) i).card : ℝ)) ≤
      (r i : ℝ) * (2 * k) := by
  let P (e : Fin 3 → Fin k) (x : ℕ) := x ∈ projection (cell hk w S e) i
  have hproj (e : Fin 3 → Fin k) :
      (Finset.range (r i)).filter (P e) = projection (cell hk w S e) i := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).2
    · intro hx
      obtain ⟨p, hp, rfl⟩ := mem_projection.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hr p (mem_cell.mp hp).1 i), hx⟩
  simp_rw [← hproj]
  rw [sum_filter_card_comm _ _ P]
  calc
    _ ≤ ∑ _x ∈ Finset.range (r i), ((2 * k : ℕ) : ℝ) :=
      Finset.sum_le_sum fun x _ => by exact_mod_cast occurs_bound hk w hS i x
    _ = _ := by simp [nsmul_eq_mul]

/-- All points in a specified collection of coarse boxes. -/
def bunch {k : ℕ} (hk : 0 < k) (w : Fin 3 → ℕ)
    (S : Finset (Fin 3 → ℕ)) (B : Finset (Fin 3 → Fin k)) : Finset (Fin 3 → ℕ) :=
  B.biUnion (cell hk w S)

theorem bunch_subset {k : ℕ} (hk : 0 < k) (w : Fin 3 → ℕ)
    (S : Finset (Fin 3 → ℕ)) (B : Finset (Fin 3 → Fin k)) : bunch hk w S B ⊆ S := by
  intro x hx
  obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hx
  exact cell_subset hk w S e he

theorem card_bunch {k : ℕ} (hk : 0 < k) (w : Fin 3 → ℕ)
    (S : Finset (Fin 3 → ℕ)) (B : Finset (Fin 3 → Fin k)) :
    (bunch hk w S B).card = ∑ e ∈ B, (cell hk w S e).card := by
  apply Finset.card_biUnion
  intro e _ f _ hne
  refine Finset.disjoint_left.mpr fun p he hf => ?_
  exact hne (funext fun i => ((mem_cell.mp he).2 i).symm.trans ((mem_cell.mp hf).2 i))

/-- Projections of a group aligned along an axis stay within a single bin on the other axes. -/
theorem bunch_projection_le {k : ℕ} {hk : 0 < k} {w r : Fin 3 → ℕ}
    (hw : ∀ i, 0 < w i) (hrw : ∀ i, r i ≤ k * w i)
    {S : Finset (Fin 3 → ℕ)} (hr : InRectangle r S)
    {B : Finset (Fin 3 → Fin k)} {x : Fin 3 → Fin k} {i : Fin 3}
    (hB : ∀ e ∈ B, ∀ j : Fin 3, j ≠ i → x j = e j) (j : Fin 3) :
    (projection (bunch hk w S B) j).card ≤ (if j = i then B.card * w j else w j) := by
  by_cases h : j = i
  · rw [if_pos h]
    have hsub : projection (bunch hk w S B) j ⊆
        B.biUnion (fun e => projection (cell hk w S e) j) := by
      intro y hy
      obtain ⟨p, hp, rfl⟩ := mem_projection.mp hy
      obtain ⟨e, he, hep⟩ := Finset.mem_biUnion.mp hp
      exact Finset.mem_biUnion.mpr ⟨e, he, mem_projection.mpr ⟨p, hep, rfl⟩⟩
    calc
      _ ≤ (B.biUnion (fun e => projection (cell hk w S e) j)).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ e ∈ B, (projection (cell hk w S e) j).card := Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ B, w j := Finset.sum_le_sum fun e _ => cell_projection_le hw hrw hr e j
      _ = _ := by simp
  · rw [if_neg h]
    have hsub : projection (bunch hk w S B) j ⊆
        Finset.Ico ((x j).val * w j) ((x j).val * w j + w j) := by
      intro y hy
      obtain ⟨p, hp, rfl⟩ := mem_projection.mp hy
      obtain ⟨e, he, hep⟩ := Finset.mem_biUnion.mp hp
      rw [hB e he j h]
      exact Finset.mem_Ico.mpr (cell_interval hw hrw hr hep j)
    simpa using Finset.card_le_card hsub

end Green88
