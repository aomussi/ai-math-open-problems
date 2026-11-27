import Green88.Basic
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.Linarith

namespace Green88

open SimpleGraph

private def supportGraph {α : Type*} (S : Finset (Fin 3 → α)) : SimpleGraph (Fin 3 × α) where
  Adj u v := u.1 ≠ v.1 ∧ ∃ p ∈ S, p u.1 = u.2 ∧ p v.1 = v.2
  symm := by
    rintro u v ⟨hne, p, hp, hu, hv⟩
    exact ⟨hne.symm, p, hp, hv, hu⟩
  loopless u hu := hu.1 rfl

private def tripleVertices {α : Type*} (p : Fin 3 → α) : Fin 3 ↪ (Fin 3 × α) :=
  ⟨fun i => (i, p i), fun _ _ h => congrArg Prod.fst h⟩

private def triangle {α : Type*} (p : Fin 3 → α) : Finset (Fin 3 × α) :=
  Finset.univ.map (tripleVertices p)

private theorem mem_triangle {α : Type*} {p : Fin 3 → α} {v : Fin 3 × α} :
    v ∈ triangle p ↔ p v.1 = v.2 := by
  rcases v with ⟨i, x⟩
  simp [triangle, tripleVertices, Finset.mem_map]

private theorem triangle_inj {α : Type*} :
    Function.Injective (triangle : (Fin 3 → α) → Finset (Fin 3 × α)) := by
  intro p q h
  funext i
  have hm : (i, p i) ∈ triangle p := mem_triangle.mpr rfl
  rw [h] at hm
  exact (mem_triangle.mp hm).symm

private theorem isClique_triangle {α : Type*} {S : Finset (Fin 3 → α)}
    {p : Fin 3 → α} (hp : p ∈ S) :
    (supportGraph S).IsNClique 3 (triangle p) := by
  rw [isNClique_iff]
  refine ⟨?_, by simp [triangle, Finset.card_map]⟩
  intro u hu v hv hne
  have hu' := mem_triangle.mp hu
  have hv' := mem_triangle.mp hv
  refine ⟨?_, p, hp, hu', hv'⟩
  intro e
  exact hne (Prod.ext e (hu'.symm.trans ((congrArg p e).trans hv')))

private theorem clique_eq_triangle {α : Type*} [LinearOrder α]
    {S : Finset (Fin 3 → α)} (hS : PairwiseComparable S)
    {t : Finset (Fin 3 × α)} (ht : (supportGraph S).IsNClique 3 t) :
    ∃ p ∈ S, triangle p = t := by
  have hcolor : Set.InjOn Prod.fst (t : Set (Fin 3 × α)) := by
    intro u hu v hv he
    by_contra hne
    exact (ht.isClique hu hv hne).1 he
  have hfull : t.image Prod.fst = (Finset.univ : Finset (Fin 3)) :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      (by simp [Finset.card_image_of_injOn hcolor, ht.card_eq])
  have hmem (i : Fin 3) : ∃ x, (i, x) ∈ t := by
    have h : i ∈ t.image Prod.fst := hfull ▸ Finset.mem_univ i
    obtain ⟨⟨j, x⟩, hx, rfl⟩ := Finset.mem_image.mp h
    exact ⟨x, hx⟩
  obtain ⟨a, ha⟩ := hmem 0
  obtain ⟨b, hb⟩ := hmem 1
  obtain ⟨c, hc⟩ := hmem 2
  have hab := ht.isClique ha hb (by simp)
  have hac := ht.isClique ha hc (by simp)
  have hbc := ht.isClique hb hc (by simp)
  obtain ⟨_, r, hr, hr0, hr1⟩ := hab
  obtain ⟨_, q, hq, hq0, hq2⟩ := hac
  obtain ⟨_, p, hp, hp1, hp2⟩ := hbc
  obtain ⟨x, hx, hx0, hx1, hx2⟩ := triangle_completion hS hp hq hr
    (hp2.trans hq2.symm) (hp1.trans hr1.symm) (hq0.trans hr0.symm)
  have h0 : x 0 = a := hx0.trans hq0
  have h1 : x 1 = b := hx1.trans hp1
  have h2 : x 2 = c := hx2.trans hp2
  refine ⟨x, hx, Finset.eq_of_subset_of_card_le ?_ (by simp [triangle, ht.card_eq])⟩
  rintro ⟨i, y⟩ hy
  have hy' : x i = y := mem_triangle.mp hy
  subst y
  fin_cases i
  · change ((0 : Fin 3), x 0) ∈ t
    rwa [h0]
  · change ((1 : Fin 3), x 1) ∈ t
    rwa [h1]
  · change ((2 : Fin 3), x 2) ∈ t
    rwa [h2]

private theorem card_triangles {n : ℕ} {S : Finset (Fin 3 → Fin n)}
    (hS : PairwiseComparable S) [DecidableRel (supportGraph S).Adj] :
    ((supportGraph S).cliqueFinset 3).card = S.card := by
  have heq : (supportGraph S).cliqueFinset 3 = S.map ⟨triangle, triangle_inj⟩ := by
    ext t
    simp only [mem_cliqueFinset_iff, Finset.mem_map, Function.Embedding.coeFn_mk]
    exact ⟨clique_eq_triangle hS, by rintro ⟨p, hp, rfl⟩; exact isClique_triangle hp⟩
  rw [heq, Finset.card_map]

private theorem deletions_bound {n : ℕ} {S : Finset (Fin 3 → Fin n)}
    (hS : PairwiseComparable S)
    {H : SimpleGraph (Fin 3 × Fin n)} [DecidableRel H.Adj]
    [DecidableRel (supportGraph S).Adj] (hH : H.CliqueFree 3) :
    S.card ≤ ((supportGraph S).edgeFinset \ H.edgeFinset).card := by
  classical
  let G := supportGraph S
  have broken (p : Fin 3 → Fin n) (hp : p ∈ S) :
      ∃ i j : Fin 3, i ≠ j ∧ ¬H.Adj (i, p i) (j, p j) := by
    by_contra! intact
    apply hH (triangle p)
    rw [isNClique_iff]
    refine ⟨?_, by simp [triangle]⟩
    rintro ⟨i, x⟩ hu ⟨j, y⟩ hv hne
    have hu' : p i = x := mem_triangle.mp hu
    have hv' : p j = y := mem_triangle.mp hv
    subst x
    subst y
    exact intact i j (fun he => hne (by subst j; rfl))
  choose left right hne hbroken using broken
  let E (p : Fin 3 → Fin n) : Sym2 (Fin 3 × Fin n) :=
    if hp : p ∈ S then s((left p hp, p (left p hp)), (right p hp, p (right p hp)))
    else s((0, p 0), (0, p 0))
  refine Finset.card_le_card_of_injOn E ?_ ?_
  · intro p hp
    simp only [E, dif_pos hp, Finset.mem_sdiff, mem_edgeFinset, mem_edgeSet]
    exact ⟨⟨hne p hp, p, hp, rfl, rfl⟩, hbroken p hp⟩
  · intro p hp q hq he
    change p ∈ S at hp
    change q ∈ S at hq
    simp only [E, dif_pos hp, dif_pos hq, Sym2.mk_eq_mk_iff] at he
    rcases he with h | h
    · have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      have f₁ := congrArg Prod.fst h₁
      have f₂ := congrArg Prod.fst h₂
      have e₁ := congrArg Prod.snd h₁
      have e₂ := congrArg Prod.snd h₂
      exact projection_inj hS (hne p hp) hp hq
        (Prod.ext (e₁.trans (congrArg q f₁).symm) (e₂.trans (congrArg q f₂).symm))
    · have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      have f₁ := congrArg Prod.fst h₁
      have f₂ := congrArg Prod.fst h₂
      have e₁ := congrArg Prod.snd h₁
      have e₂ := congrArg Prod.snd h₂
      exact projection_inj hS (hne p hp) hp hq
        (Prod.ext (e₁.trans (congrArg q f₁).symm) (e₂.trans (congrArg q f₂).symm))

/-- The uniform qualitative bound used by the rectangular induction. -/
theorem qualitative (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n → ∀ S : Finset (Fin 3 → Fin n),
      PairwiseComparable S → (S.card : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
  classical
  let d : ℝ := min 1 (ε / 9)
  have hd : 0 < d := lt_min (by norm_num) (by positivity)
  have hd' : d ≤ 1 := min_le_left _ _
  have hdε : d * 9 ≤ ε := (le_div_iff₀ (by norm_num : (0 : ℝ) < 9)).1 (min_le_right _ _)
  let c : ℝ := triangleRemovalBound d
  have hc : 0 < c := triangleRemovalBound_pos hd hd'
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / c)
  refine ⟨K, ?_⟩
  intro n hKn S hS
  have hn : (1 / c) < n := hK.trans_le (by exact_mod_cast hKn)
  have hnpos : (0 : ℝ) < n := (by positivity : 0 < 1 / c).trans hn
  have hcn : 1 < c * (n : ℝ) := by
    rw [mul_comm]
    exact (div_lt_iff₀ hc).1 hn
  let G := supportGraph S
  have hcS : (S.card : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast card_le_square hS
  have hsmall : ((G.cliqueFinset 3).card : ℝ) <
      c * (Fintype.card (Fin 3 × Fin n) : ℝ) ^ 3 := by
    change (((supportGraph S).cliqueFinset 3).card : ℝ) < _
    rw [card_triangles hS, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul]
    norm_num
    have hp : 0 < (n : ℝ) ^ 2 := by positivity
    calc
      (S.card : ℝ) ≤ (n : ℝ) ^ 2 := hcS
      _ < (c * n) * (n : ℝ) ^ 2 := by simpa using mul_lt_mul_of_pos_right hcn hp
      _ ≤ c * (3 * (n : ℝ)) ^ 3 := by nlinarith [mul_nonneg hc.le (pow_nonneg hnpos.le 3)]
  obtain ⟨H, hHG, hdec, hcount, hH⟩ := triangle_removal (ε := d) hsmall
  letI : DecidableRel H.Adj := hdec
  have hcount' : (S.card : ℝ) ≤
      (G.edgeFinset.card : ℝ) - (H.edgeFinset.card : ℝ) := by
    have hsub := edgeFinset_mono hHG
    have hcard := deletions_bound hS hH
    rw [Finset.card_sdiff hsub] at hcard
    rw [← Nat.cast_sub (Finset.card_le_card hsub)]
    exact_mod_cast hcard
  have hconst : d * (↑(Fintype.card (Fin 3 × Fin n) ^ 2) : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow, Nat.cast_mul]
    norm_num
    calc
      d * (3 * (n : ℝ)) ^ 2 = (d * 9) * (n : ℝ) ^ 2 := by ring
      _ ≤ ε * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hdε (sq_nonneg _)
  exact (hcount'.trans (le_of_lt hcount)).trans hconst

end Green88
