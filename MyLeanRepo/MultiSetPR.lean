module

/-
# Multi-set Plünnecke-Ruzsa Inequality

Proves the k=2 case and a general k case (via union bound) of the multi-set
Plünnecke-Ruzsa inequality for dyadic covering numbers.

## Main results

1. `discretized_multiset_pr_two`: If N(X+Y_i) ≤ α_i N(X) for i=1,2, then
   N(Y_1+Y_2) ≤ 8 α_1 α_2 N(X).
2. `discretized_multiset_pr_general`: If N(X+Y_i) ≤ α_i N(X) for all i : Fin k,
   then N(Y_0+...+Y_{k-1}) ≤ k · (2·∑ α_i)^k · N(X).
3. `discretized_multiset_pr_product`: Under α_i ≥ 1, the bound becomes
   k · (2k)^k · (∏ α_i)^k · N(X).

## Proof route for k=2

1. Convert covering number hypotheses to finset cardinality bounds.
2. Use `sum_index_inclusion`: |I(X)+I(Y)| ≤ 2 |I(X+Y)|.
3. Apply Mathlib's `Finset.ruzsa_triangle_inequality_add_add_add`.
4. Use `sum_index_inclusion_rev`: N(Y_1+Y_2) ≤ 2 |I(Y_1)+I(Y_2)|.
5. Combine: constant 2 × 2 × 2 = 8.

## Proof route for general k (union bound)

1. Let B = ⋃ Y_i. Then X+B = ⋃ (X+Y_i).
2. Union bound: N(X+B) ≤ ∑ N(X+Y_i) ≤ (∑ α_i) N(X).
3. familySum Y ⊆ nfoldSum k B.
4. Apply single-set iterated Plünnecke-Ruzsa to B:
   N(nfoldSum k B) ≤ k · (2K)^k · N(X), where K = ∑ α_i.
5. Monotonicity gives the result.

## Whiteprint node
`WeakTwoEnds/OSW/MultiSetPR`
-/

public import MyLeanRepo.DiscretizedPluenneckeFull
public import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence

open ProductLikeIncidence (realCubeIndexSet realCubeIndexSet_finite
  realCoveringNumber_eq_card sum_index_inclusion sum_index_inclusion_rev
  bounded_image2_add finset_pointwise_add_card_le)

/-! ## k=2 case -/

/-- **Two-set multi-set Plünnecke-Ruzsa** (dyadic covering numbers). -/
lemma discretized_multiset_pr_two
    {δ : ℝ} (hδ : 0 < δ) {X Y1 Y2 : Set ℝ}
    (hX : Bornology.IsBounded X)
    (hY1 : Bornology.IsBounded Y1)
    (hY2 : Bornology.IsBounded Y2)
    (hX_nonempty : X.Nonempty)
    {α1 α2 : ℝ} (hα1_nonneg : 0 ≤ α1) (hα2_nonneg : 0 ≤ α2)
    (h1 : Nreal' δ (Set.image2 (· + ·) X Y1) ≤ ENNReal.ofReal α1 * Nreal' δ X)
    (h2 : Nreal' δ (Set.image2 (· + ·) X Y2) ≤ ENNReal.ofReal α2 * Nreal' δ X) :
    Nreal' δ (Set.image2 (· + ·) Y1 Y2) ≤
      ENNReal.ofReal (8 * α1 * α2) * Nreal' δ X := by
  let IA := (realCubeIndexSet_finite hδ hX).toFinset
  let IY1 := (realCubeIndexSet_finite hδ hY1).toFinset
  let IY2 := (realCubeIndexSet_finite hδ hY2).toFinset
  let IXY1 := (realCubeIndexSet_finite hδ (bounded_image2_add hX hY1)).toFinset
  let IXY2 := (realCubeIndexSet_finite hδ (bounded_image2_add hX hY2)).toFinset
  let IY1Y2 := (realCubeIndexSet_finite hδ (bounded_image2_add hY1 hY2)).toFinset

  have hIA_nonempty : IA.Nonempty := cube_index_nonempty hδ hX hX_nonempty
  have hIA : (IA : Set ℤ) = realCubeIndexSet δ X := Set.Finite.coe_toFinset _
  have hIY1 : (IY1 : Set ℤ) = realCubeIndexSet δ Y1 := Set.Finite.coe_toFinset _
  have hIY2 : (IY2 : Set ℤ) = realCubeIndexSet δ Y2 := Set.Finite.coe_toFinset _
  have hIXY1 : (IXY1 : Set ℤ) = realCubeIndexSet δ (Set.image2 (· + ·) X Y1) :=
    Set.Finite.coe_toFinset _
  have hIXY2 : (IXY2 : Set ℤ) = realCubeIndexSet δ (Set.image2 (· + ·) X Y2) :=
    Set.Finite.coe_toFinset _
  have hIY1Y2 : (IY1Y2 : Set ℤ) = realCubeIndexSet δ (Set.image2 (· + ·) Y1 Y2) :=
    Set.Finite.coe_toFinset _

  have h_card1 : IXY1.card ≤ α1 * IA.card :=
    covering_hyp_to_card hδ hX hY1 hα1_nonneg h1
  have h_card2 : IXY2.card ≤ α2 * IA.card :=
    covering_hyp_to_card hδ hX hY2 hα2_nonneg h2

  have h_sum1 : (IA + IY1).card ≤ 2 * IXY1.card := by
    have h2 : ((IA + IY1 : Finset ℤ) : Set ℤ) ⊆
        ((IXY1 + ({-1, 0} : Finset ℤ)) : Set ℤ) := by
      calc ((IA + IY1 : Finset ℤ) : Set ℤ)
          = realCubeIndexSet δ X + realCubeIndexSet δ Y1 := by simp [hIA, hIY1] <;> rfl
        _ ⊆ realCubeIndexSet δ (Set.image2 (· + ·) X Y1) + ({-1, 0} : Set ℤ) :=
          sum_index_inclusion hδ
        _ = (IXY1 : Set ℤ) + ({-1, 0} : Set ℤ) := by rw [←hIXY1]
        _ = ((IXY1 + ({-1, 0} : Finset ℤ)) : Set ℤ) := by simp
    have h_incl : (IA + IY1 : Finset ℤ) ⊆ IXY1 + ({-1, 0} : Finset ℤ) := by exact_mod_cast h2
    have h7 : (IXY1 + ({-1, 0} : Finset ℤ)).card ≤ IXY1.card * 2 := by
      have h8 := finset_pointwise_add_card_le (A := IXY1) (B := ({-1, 0} : Finset ℤ))
      simpa using h8
    calc (IA + IY1).card
        ≤ (IXY1 + ({-1, 0} : Finset ℤ)).card := Finset.card_le_card h_incl
      _ ≤ IXY1.card * 2 := h7
      _ = 2 * IXY1.card := by ring

  have h_sum2 : (IA + IY2).card ≤ 2 * IXY2.card := by
    have h2 : ((IA + IY2 : Finset ℤ) : Set ℤ) ⊆
        ((IXY2 + ({-1, 0} : Finset ℤ)) : Set ℤ) := by
      calc ((IA + IY2 : Finset ℤ) : Set ℤ)
          = realCubeIndexSet δ X + realCubeIndexSet δ Y2 := by simp [hIA, hIY2] <;> rfl
        _ ⊆ realCubeIndexSet δ (Set.image2 (· + ·) X Y2) + ({-1, 0} : Set ℤ) :=
          sum_index_inclusion hδ
        _ = (IXY2 : Set ℤ) + ({-1, 0} : Set ℤ) := by rw [←hIXY2]
        _ = ((IXY2 + ({-1, 0} : Finset ℤ)) : Set ℤ) := by simp
    have h_incl : (IA + IY2 : Finset ℤ) ⊆ IXY2 + ({-1, 0} : Finset ℤ) := by exact_mod_cast h2
    have h7 : (IXY2 + ({-1, 0} : Finset ℤ)).card ≤ IXY2.card * 2 := by
      have h8 := finset_pointwise_add_card_le (A := IXY2) (B := ({-1, 0} : Finset ℤ))
      simpa using h8
    calc (IA + IY2).card
        ≤ (IXY2 + ({-1, 0} : Finset ℤ)).card := Finset.card_le_card h_incl
      _ ≤ IXY2.card * 2 := h7
      _ = 2 * IXY2.card := by ring

  have h_ruzsa : (IY1 + IY2).card * IA.card ≤ (IY1 + IA).card * (IA + IY2).card :=
    Finset.ruzsa_triangle_inequality_add_add_add IY1 IA IY2

  have h_comm1 : (IY1 + IA).card = (IA + IY1).card := by
    rw [add_comm]

  have h_pos : (0 : ℝ) < (IA.card : ℝ) := by exact_mod_cast hIA_nonempty.card_pos

  have h_main : (IY1 + IY2).card ≤ 4 * α1 * α2 * (IA.card : ℝ) := by
    have h10 : ((IY1 + IY2).card : ℝ) * (IA.card : ℝ) ≤
        ((IY1 + IA).card : ℝ) * ((IA + IY2).card : ℝ) := by exact_mod_cast h_ruzsa
    have h11 : (IA.card : ℝ) ≠ 0 := h_pos.ne'
    have h9 : ((IY1 + IY2).card : ℝ) ≤
        ((IY1 + IA).card : ℝ) * ((IA + IY2).card : ℝ) / (IA.card : ℝ) := by
      have h_calc : ((IY1 + IY2).card : ℝ) * (IA.card : ℝ) ≤ ((IY1 + IA).card : ℝ) * ((IA + IY2).card : ℝ) := h10
      have h_pos' : 0 ≤ (IA.card : ℝ) := by positivity
      have h_div : ((IY1 + IY2).card : ℝ) * (IA.card : ℝ) / (IA.card : ℝ) ≤
          ((IY1 + IA).card : ℝ) * ((IA + IY2).card : ℝ) / (IA.card : ℝ) :=
        div_le_div_of_nonneg_right h_calc h_pos'
      have h_eq : ((IY1 + IY2).card : ℝ) * (IA.card : ℝ) / (IA.card : ℝ) = ((IY1 + IY2).card : ℝ) := by
        field_simp [h_pos.ne'] <;> ring
      rw [h_eq] at h_div
      exact h_div
    have h9' : ((IY1 + IY2).card : ℝ) ≤
        ((IA + IY1).card : ℝ) * ((IA + IY2).card : ℝ) / (IA.card : ℝ) := by
      rw [h_comm1] at h9; exact h9
    have h12 : ((IA + IY1).card : ℝ) ≤ 2 * (IXY1.card : ℝ) := by exact_mod_cast h_sum1
    have h13 : ((IA + IY2).card : ℝ) ≤ 2 * (IXY2.card : ℝ) := by exact_mod_cast h_sum2
    have h14 : (IXY1.card : ℝ) ≤ α1 * (IA.card : ℝ) := by exact_mod_cast h_card1
    have h15 : (IXY2.card : ℝ) ≤ α2 * (IA.card : ℝ) := by exact_mod_cast h_card2
    calc ((IY1 + IY2).card : ℝ)
        ≤ ((IA + IY1).card : ℝ) * ((IA + IY2).card : ℝ) / (IA.card : ℝ) := h9'
      _ ≤ (2 * (IXY1.card : ℝ)) * (2 * (IXY2.card : ℝ)) / (IA.card : ℝ) := by
          gcongr
      _ ≤ (2 * (α1 * (IA.card : ℝ))) * (2 * (α2 * (IA.card : ℝ))) / (IA.card : ℝ) := by
          gcongr
      _ = 4 * α1 * α2 * (IA.card : ℝ) := by
          field_simp [h_pos.ne'] <;> ring

  have h_rev : IY1Y2.card ≤ 2 * (IY1 + IY2).card := by
    have h2 : (IY1Y2 : Set ℤ) ⊆
        ((IY1 + IY2) + ({0, 1} : Finset ℤ) : Set ℤ) := by
      calc (IY1Y2 : Set ℤ)
          = realCubeIndexSet δ (Set.image2 (· + ·) Y1 Y2) := hIY1Y2
        _ ⊆ realCubeIndexSet δ Y1 + realCubeIndexSet δ Y2 + ({0, 1} : Set ℤ) :=
          sum_index_inclusion_rev hδ
        _ = (IY1 : Set ℤ) + (IY2 : Set ℤ) + ({0, 1} : Set ℤ) := by rw [←hIY1, ←hIY2]
        _ = ((IY1 + IY2) + ({0, 1} : Finset ℤ) : Set ℤ) := by simp
    have h_incl : IY1Y2 ⊆ (IY1 + IY2) + ({0, 1} : Finset ℤ) := by exact_mod_cast h2
    have h7 : ((IY1 + IY2) + ({0, 1} : Finset ℤ)).card ≤ (IY1 + IY2).card * 2 := by
      have h8 := finset_pointwise_add_card_le (A := (IY1 + IY2)) (B := ({0, 1} : Finset ℤ))
      simpa using h8
    calc IY1Y2.card
        ≤ ((IY1 + IY2) + ({0, 1} : Finset ℤ)).card := Finset.card_le_card h_incl
      _ ≤ (IY1 + IY2).card * 2 := h7
      _ = 2 * (IY1 + IY2).card := by ring

  have h_final : (IY1Y2.card : ℝ) ≤ 8 * α1 * α2 * (IA.card : ℝ) := by
    calc (IY1Y2.card : ℝ)
        ≤ 2 * ((IY1 + IY2).card : ℝ) := by exact_mod_cast h_rev
      _ ≤ 2 * (4 * α1 * α2 * (IA.card : ℝ)) := by gcongr
      _ = 8 * α1 * α2 * (IA.card : ℝ) := by ring

  have hN := realCoveringNumber_eq_card hδ (bounded_image2_add hY1 hY2)
  have hNX := realCoveringNumber_eq_card hδ hX
  have h_encard : (realCubeIndexSet δ (Set.image2 (· + ·) Y1 Y2)).encard = IY1Y2.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ (bounded_image2_add hY1 hY2))] <;> rfl
  have h_encardX : (realCubeIndexSet δ X).encard = IA.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ hX)] <;> rfl
  have h_ofReal_card : ∀ (c : ℕ), ENNReal.ofReal (c : ℝ) = (c : ENNReal) := by
    intro c; simp
  have h_ennreal : (IY1Y2.card : ENNReal) ≤
      ENNReal.ofReal (8 * α1 * α2) * (IA.card : ENNReal) := by
    have h_mul : ENNReal.ofReal (8 * α1 * α2 * (IA.card : ℝ)) =
        ENNReal.ofReal (8 * α1 * α2) * (IA.card : ENNReal) := by
      rw [ENNReal.ofReal_mul (by positivity), h_ofReal_card IA.card] <;> ring_nf <;> positivity
    have h5 : (IY1Y2.card : ENNReal) = ENNReal.ofReal (IY1Y2.card : ℝ) := by
      rw [h_ofReal_card]
    rw [h5, ←h_mul]
    exact ENNReal.ofReal_le_ofReal h_final
  dsimp only [Nreal']
  have h1' : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (Set.image2 (· + ·) Y1 Y2))) =
      (IY1Y2.card : ENNReal) := by
    rw [hN, h_encard] <;> simp
  have h2' : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy X)) =
      (IA.card : ENNReal) := by
    rw [hNX, h_encardX] <;> simp
  rw [h1', h2']
  exact h_ennreal

/-! ## Iterated sumset machinery -/

-- nfoldSum, nfoldSum_bounded, nfoldSum_one, rangeInt, rangeInt_card,
-- finset_coe_nsmul, nfold_sum_index_inclusion_aux, nfold_sum_index_inclusion,
-- finite_pluennecke_nsmul are all imported from DiscretizedPluenneckeFull.

/-! ## Union bound for covering numbers -/

/-- Covering numbers are subadditive over binary union. -/
lemma covering_union_two {δ : ℝ} {A B : Set ℝ} :
    Nreal' δ (A ∪ B) ≤ Nreal' δ A + Nreal' δ B := by
  dsimp only [Nreal']
  let A' := productLikeRealLineCopy A
  let B' := productLikeRealLineCopy B
  have h1 : productLikeRealLineCopy (A ∪ B) = A' ∪ B' := by
    ext x
    simp [productLikeRealLineCopy, A', B']
    <;> rfl
  rw [h1]
  have h_inter : ∀ (Q : Set (EuclideanSpace ℝ (Fin 1))),
      (Q ∩ (A' ∪ B')).Nonempty ↔ (Q ∩ A').Nonempty ∨ (Q ∩ B').Nonempty := by
    intro Q
    have h_eq : Q ∩ (A' ∪ B') = (Q ∩ A') ∪ (Q ∩ B') := by
      rw [Set.inter_union_distrib_left]
    rw [h_eq]
    constructor
    · rintro ⟨x, hx | hx⟩
      · exact Or.inl ⟨x, hx⟩
      · exact Or.inr ⟨x, hx⟩
    · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
      · exact ⟨x, Or.inl hx⟩
      · exact ⟨x, Or.inr hx⟩
  have h2 : dyadicCubesMeeting (d := 1) δ (A' ∪ B') =
      dyadicCubesMeeting (d := 1) δ A' ∪ dyadicCubesMeeting (d := 1) δ B' := by
    ext Q
    simp only [dyadicCubesMeeting, Set.mem_union, Set.mem_setOf_eq]
    rw [h_inter Q]
    constructor
    · rintro ⟨hQ1, hQ2 | hQ3⟩
      · exact Or.inl ⟨hQ1, hQ2⟩
      · exact Or.inr ⟨hQ1, hQ3⟩
    · rintro (⟨hQ1, hQ2⟩ | ⟨hQ1, hQ3⟩)
      · exact ⟨hQ1, Or.inl hQ2⟩
      · exact ⟨hQ1, Or.inr hQ3⟩
  dsimp only [dyadicCoveringNumber]
  rw [h2]
  have h3 := Set.encard_union_le
    (dyadicCubesMeeting (d := 1) δ A')
    (dyadicCubesMeeting (d := 1) δ B')
  exact_mod_cast h3

/-- Covering number of empty set is zero. -/
lemma covering_empty {δ : ℝ} : Nreal' δ (∅ : Set ℝ) = 0 := by
  dsimp only [Nreal']
  have h1 : productLikeRealLineCopy (∅ : Set ℝ) = (∅ : Set (EuclideanSpace ℝ (Fin 1))) := by
    ext x
    simp [productLikeRealLineCopy, Set.mem_empty_iff_false]
    <;> tauto
  rw [h1]
  have h2 : dyadicCubesMeeting (d := 1) δ (∅ : Set (EuclideanSpace ℝ (Fin 1))) = ∅ := by
    ext Q
    simp [dyadicCubesMeeting, Set.inter_empty]
    <;> tauto
  dsimp only [dyadicCoveringNumber]
  rw [h2]
  <;> simp

/-- Covering numbers are subadditive over finite unions. -/
lemma covering_union_bound {δ : ℝ} {k : ℕ} {S : Fin k → Set ℝ} :
    Nreal' δ (⋃ i : Fin k, S i) ≤ ∑ i : Fin k, Nreal' δ (S i) := by
  have h_main : ∀ (s : Finset (Fin k)),
      Nreal' δ (⋃ i ∈ s, S i) ≤ ∑ i ∈ s, Nreal' δ (S i) := by
    intro s
    induction s using Finset.induction with
    | empty =>
      have h_empty1 : (⋃ i ∈ (∅ : Finset (Fin k)), S i) = (∅ : Set ℝ) := by simp
      rw [h_empty1, covering_empty]
      <;> simp
    | @insert a s ha ih =>
      have h1 : (⋃ i ∈ (insert a s), S i) = (S a) ∪ (⋃ i ∈ s, S i) := by
        ext x
        simp only [Finset.mem_insert, Set.mem_iUnion, Set.mem_union]
        constructor
        · rintro ⟨i, (rfl | hi), hx⟩
          · exact Or.inl hx
          · exact Or.inr ⟨i, hi, hx⟩
        · rintro (hx | ⟨i, hi, hx⟩)
          · exact ⟨a, by simp, hx⟩
          · exact ⟨i, Or.inr hi, hx⟩
      rw [h1, Finset.sum_insert ha]
      exact le_trans covering_union_two (add_le_add_right ih _)
  have h_eq : (⋃ i : Fin k, S i) = (⋃ i ∈ (Finset.univ : Finset (Fin k)), S i) := by
    ext x
    simp only [Set.mem_iUnion, Finset.mem_univ]
    constructor
    · rintro ⟨i, hx⟩
      exact ⟨i, by trivial, hx⟩
    · rintro ⟨i, _, hx⟩
      exact ⟨i, hx⟩
  rw [h_eq]
  exact h_main Finset.univ

/-! ## familySum subset nfoldSum -/

/-- Helper: k-fold sum of a family of sets. -/
def familySum {k : ℕ} (Y : Fin k → Set ℝ) : Set ℝ :=
  match k with
  | 0 => {0}
  | k + 1 => Set.image2 (· + ·) (Y 0) (familySum (fun i => Y i.succ))

lemma familySum_subset_nfoldSum {k : ℕ} {Y : Fin k → Set ℝ} {B : Set ℝ}
    (hB : ∀ i, Y i ⊆ B) : familySum Y ⊆ nfoldSum k B := by
  induction k with
  | zero =>
    simp [familySum, nfoldSum]
  | succ k ih =>
    simp only [familySum]
    intro x hx
    rcases hx with ⟨y, hy, z, hz, rfl⟩
    have hy' : y ∈ B := hB 0 hy
    have hz' : z ∈ nfoldSum k B := ih (fun i => hB i.succ) hz
    exact ⟨y, hy', z, hz', rfl⟩

/-! ## General k case (union bound approach) -/

/-- **General multi-set Plünnecke-Ruzsa** via union bound (dyadic covering numbers).

If `N(X+Y_i, δ) ≤ α_i · N(X, δ)` for all `i : Fin k`, then
`N(Y_0 + ... + Y_{k-1}, δ) ≤ k · (2·∑ α_i)^k · N(X, δ)`.

The constant is not optimal (the optimal bound requires generalized Plünnecke),
but it is explicit and sufficient for applications where α_i ≥ 1. -/
lemma discretized_multiset_pr_general
    {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : 0 < k)
    {X : Set ℝ} {Y : Fin k → Set ℝ}
    (hX : Bornology.IsBounded X)
    (hY : ∀ i, Bornology.IsBounded (Y i))
    (hX_nonempty : X.Nonempty)
    {α : Fin k → ℝ} (hα_nonneg : ∀ i, 0 ≤ α i)
    (h : ∀ i, Nreal' δ (Set.image2 (· + ·) X (Y i)) ≤ ENNReal.ofReal (α i) * Nreal' δ X) :
    Nreal' δ (familySum Y) ≤
      ENNReal.ofReal ((k : ℝ) * (2 * ∑ i : Fin k, α i) ^ k) * Nreal' δ X := by
  let B : Set ℝ := ⋃ i : Fin k, Y i
  have hB_bounded : Bornology.IsBounded B := by
    have h : B = ⋃ i ∈ (Finset.univ : Finset (Fin k)), Y i := by
      simp [B]
      <;> rfl
    rw [h]
    have h' : ∀ (i : Fin k), Bornology.IsBounded (Y i) := hY
    exact (Bornology.isBounded_biUnion_finset Finset.univ).mpr fun i a => hY i
  have hXY_sum : Set.image2 (· + ·) X B = ⋃ i : Fin k, Set.image2 (· + ·) X (Y i) := by
    ext x
    simp only [B, Set.mem_image2, Set.mem_iUnion]
    constructor
    · rintro ⟨y, hy, z, ⟨i, hzi⟩, rfl⟩
      exact ⟨i, y, hy, z, hzi, rfl⟩
    · rintro ⟨i, y, hy, z, hzi, rfl⟩
      exact ⟨y, hy, z, ⟨i, hzi⟩, rfl⟩
  have h_union : Nreal' δ (Set.image2 (· + ·) X B) ≤ ∑ i : Fin k, Nreal' δ (Set.image2 (· + ·) X (Y i)) := by
    rw [hXY_sum]
    exact covering_union_bound
  have hK_nonneg : 0 ≤ ∑ i : Fin k, α i :=
    Finset.sum_nonneg (fun i _ => hα_nonneg i)
  have h_sum_bound : Nreal' δ (Set.image2 (· + ·) X B) ≤
      ENNReal.ofReal (∑ i : Fin k, α i) * Nreal' δ X := by
    calc Nreal' δ (Set.image2 (· + ·) X B)
        ≤ ∑ i : Fin k, Nreal' δ (Set.image2 (· + ·) X (Y i)) := h_union
      _ ≤ ∑ i : Fin k, (ENNReal.ofReal (α i) * Nreal' δ X) := by
        apply Finset.sum_le_sum
        intro i _
        exact h i
      _ = (∑ i : Fin k, ENNReal.ofReal (α i)) * Nreal' δ X := by
          rw [Finset.sum_mul]
      _ = ENNReal.ofReal (∑ i : Fin k, α i) * Nreal' δ X := by
          have h4 : (∑ i : Fin k, ENNReal.ofReal (α i)) = ENNReal.ofReal (∑ i : Fin k, α i) := by
            have h5 : ∀ (s : Finset (Fin k)), (∑ i ∈ s, ENNReal.ofReal (α i)) = ENNReal.ofReal (∑ i ∈ s, α i) := by
              intro s
              induction s using Finset.induction with
              | empty => simp
              | @insert a s ha ih =>
                rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
                have h6 : 0 ≤ α a := hα_nonneg a
                have h7 : 0 ≤ ∑ i ∈ s, α i := Finset.sum_nonneg (fun i _ => hα_nonneg i)
                rw [ENNReal.ofReal_add h6 h7]
            exact h5 Finset.univ
          rw [h4]
  let K : ℝ := ∑ i : Fin k, α i
  let IA := (realCubeIndexSet_finite hδ hX).toFinset
  let IB := (realCubeIndexSet_finite hδ hB_bounded).toFinset
  let IAB := (realCubeIndexSet_finite hδ (bounded_image2_add hX hB_bounded)).toFinset
  have hIA_nonempty : IA.Nonempty := cube_index_nonempty hδ hX hX_nonempty
  have h_card_hyp : IAB.card ≤ K * IA.card :=
    covering_hyp_to_card hδ hX hB_bounded hK_nonneg h_sum_bound
  have h_card_sum : (IA + IB).card ≤ 2 * IAB.card := by
    have h2 : ((IA + IB : Finset ℤ) : Set ℤ) ⊆
        ((IAB + ({-1, 0} : Finset ℤ)) : Set ℤ) := by
      have hIA : (IA : Set ℤ) = realCubeIndexSet δ X := Set.Finite.coe_toFinset _
      have hIB : (IB : Set ℤ) = realCubeIndexSet δ B := Set.Finite.coe_toFinset _
      have hIAB : (IAB : Set ℤ) = realCubeIndexSet δ (Set.image2 (· + ·) X B) :=
        Set.Finite.coe_toFinset _
      calc ((IA + IB : Finset ℤ) : Set ℤ)
          = realCubeIndexSet δ X + realCubeIndexSet δ B := by simp [hIA, hIB] <;> rfl
        _ ⊆ realCubeIndexSet δ (Set.image2 (· + ·) X B) + ({-1, 0} : Set ℤ) :=
          sum_index_inclusion hδ
        _ = (IAB : Set ℤ) + ({-1, 0} : Set ℤ) := by rw [←hIAB]
        _ = ((IAB + ({-1, 0} : Finset ℤ)) : Set ℤ) := by simp
    have h_incl : (IA + IB : Finset ℤ) ⊆ IAB + ({-1, 0} : Finset ℤ) := by exact_mod_cast h2
    have h7 : (IAB + ({-1, 0} : Finset ℤ)).card ≤ IAB.card * 2 := by
      have h8 := finset_pointwise_add_card_le (A := IAB) (B := ({-1, 0} : Finset ℤ))
      simpa using h8
    calc (IA + IB).card
        ≤ (IAB + ({-1, 0} : Finset ℤ)).card := Finset.card_le_card h_incl
      _ ≤ IAB.card * 2 := h7
      _ = 2 * IAB.card := by ring
  have h_card_sum2 : ((IA + IB).card : ℝ) ≤ 2 * K * (IA.card : ℝ) := by
    calc ((IA + IB).card : ℝ)
        ≤ 2 * (IAB.card : ℝ) := by exact_mod_cast h_card_sum
      _ ≤ 2 * (K * (IA.card : ℝ)) := by gcongr
      _ = 2 * K * (IA.card : ℝ) := by ring
  let r : ℚ≥0 := ((IA + IB).card : ℚ≥0) / (IA.card : ℚ≥0)
  have h_pos : (0 : ℚ≥0) < (IA.card : ℚ≥0) := by exact_mod_cast hIA_nonempty.card_pos
  have hr : (IA + IB).card ≤ r * IA.card := by
    have h_pos' : (IA.card : ℚ≥0) ≠ 0 := h_pos.ne'
    have h_pos'' : (IA.card : ℚ) ≠ 0 := by exact_mod_cast h_pos'
    have h_eq : r * (IA.card : ℚ≥0) = ((IA + IB).card : ℚ≥0) := by
      apply NNRat.coe_injective
      simp [r, NNRat.coe_mul, NNRat.coe_div, h_pos''] <;> field_simp [h_pos''] <;> ring
    exact_mod_cast h_eq.symm.le
  have hr_le : (r : ℝ) ≤ 2 * K := by
    have h_pos' : (0 : ℝ) < (IA.card : ℝ) := by exact_mod_cast hIA_nonempty.card_pos
    have h1 : (r : ℝ) = ((IA + IB).card : ℝ) / (IA.card : ℝ) := by
      simp [r, NNRat.cast_div, NNRat.cast_mul] <;> field_simp [h_pos'.ne'] <;> ring
    rw [h1]
    have h2 : ((IA + IB).card : ℝ) ≤ 2 * K * (IA.card : ℝ) := by exact_mod_cast h_card_sum2
    calc ((IA + IB).card : ℝ) / (IA.card : ℝ)
        ≤ (2 * K * (IA.card : ℝ)) / (IA.card : ℝ) := by gcongr
      _ = 2 * K := by field_simp [h_pos'.ne'] <;> ring
  have h_pluennecke : (k • IB).card ≤ r ^ k * IA.card :=
    finite_pluennecke_nsmul hIA_nonempty r hr k
  have hInB_finite : (realCubeIndexSet δ (nfoldSum k B)).Finite :=
    realCubeIndexSet_finite hδ (nfoldSum_bounded hB_bounded)
  let InB := hInB_finite.toFinset
  have hInB : (InB : Set ℤ) = realCubeIndexSet δ (nfoldSum k B) := Set.Finite.coe_toFinset _
  have h_incl : InB ⊆ (k • IB) + rangeInt k := by
    apply Finset.coe_subset.mp
    have h6 : (↑((k • IB) + rangeInt k) : Set ℤ) = (↑(k • IB) + rangeInt k : Set ℤ) := by
      rw [Finset.coe_add] <;> rfl
    rw [h6, hInB]
    exact nfold_sum_index_inclusion hδ hB_bounded k hk
  have h_card_nB : InB.card ≤ k * (k • IB).card := by
    have h6 : InB.card ≤ ((k • IB) + rangeInt k).card := Finset.card_le_card h_incl
    have h7 : ((k • IB) + rangeInt k).card ≤ (k • IB).card * (rangeInt k).card :=
      finset_pointwise_add_card_le
    have h8 : (rangeInt k).card = k := rangeInt_card k
    calc InB.card ≤ ((k • IB) + rangeInt k).card := h6
      _ ≤ (k • IB).card * (rangeInt k).card := h7
      _ = (k • IB).card * k := by rw [h8] <;> ring
      _ = k * (k • IB).card := by ring
  have h_final_card : (InB.card : ℝ) ≤ (k : ℝ) * (2 * K) ^ k * (IA.card : ℝ) := by
    have h9 : (InB.card : ℝ) ≤ (k : ℝ) * ((k • IB).card : ℝ) := by exact_mod_cast h_card_nB
    have h10 : ((k • IB).card : ℝ) ≤ (r : ℝ) ^ k * (IA.card : ℝ) := by exact_mod_cast h_pluennecke
    have h11 : (r : ℝ) ^ k ≤ (2 * K) ^ k := by gcongr <;> linarith
    calc (InB.card : ℝ)
        ≤ (k : ℝ) * ((k • IB).card : ℝ) := h9
      _ ≤ (k : ℝ) * ((r : ℝ) ^ k * (IA.card : ℝ)) := by gcongr
      _ ≤ (k : ℝ) * ((2 * K) ^ k * (IA.card : ℝ)) := by gcongr
      _ = (k : ℝ) * (2 * K) ^ k * (IA.card : ℝ) := by ring
  have h_subset : familySum Y ⊆ nfoldSum k B := familySum_subset_nfoldSum (fun i => Set.subset_iUnion Y i)
  have h_plc_subset : productLikeRealLineCopy (familySum Y) ⊆ productLikeRealLineCopy (nfoldSum k B) := by
    intro z hz
    exact h_subset hz
  have h_cubes_mono : dyadicCubesMeeting (d := 1) δ (productLikeRealLineCopy (familySum Y)) ⊆
      dyadicCubesMeeting (d := 1) δ (productLikeRealLineCopy (nfoldSum k B)) := by
    intro Q hQ
    have hQ' : Q ∈ dyadicCubes 1 δ ∧ (Q ∩ productLikeRealLineCopy (familySum Y)).Nonempty := by
      simpa [dyadicCubesMeeting] using hQ
    have h_inter_subset : Q ∩ productLikeRealLineCopy (familySum Y) ⊆ Q ∩ productLikeRealLineCopy (nfoldSum k B) :=
      Set.inter_subset_inter_right _ h_plc_subset
    exact ⟨hQ'.1, Set.Nonempty.mono h_inter_subset hQ'.2⟩
  have h_mono : Nreal' δ (familySum Y) ≤ Nreal' δ (nfoldSum k B) := by
    dsimp only [Nreal']
    apply ENat.toENNReal_mono
    apply Set.encard_mono
    exact h_cubes_mono
  have hNnB := realCoveringNumber_eq_card (S := nfoldSum k B) hδ (nfoldSum_bounded hB_bounded)
  have hNA := realCoveringNumber_eq_card hδ hX
  have h_encard_InB : (realCubeIndexSet δ (nfoldSum k B)).encard = InB.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite (S := nfoldSum k B) hδ (nfoldSum_bounded hB_bounded))] <;> rfl
  have h_encard_IA : (realCubeIndexSet δ X).encard = IA.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ hX)] <;> rfl
  have h_ofReal_card : ∀ (c : ℕ), ENNReal.ofReal (c : ℝ) = (c : ENNReal) := by
    intro c; simp
  have h_ennreal : (InB.card : ENNReal) ≤
      ENNReal.ofReal ((k : ℝ) * (2 * K) ^ k) * (IA.card : ENNReal) := by
    have h_mul : ENNReal.ofReal ((k : ℝ) * (2 * K) ^ k * (IA.card : ℝ)) =
        ENNReal.ofReal ((k : ℝ) * (2 * K) ^ k) * (IA.card : ENNReal) := by
      rw [ENNReal.ofReal_mul, h_ofReal_card IA.card] <;> ring_nf <;> positivity
    have h5 : (InB.card : ENNReal) = ENNReal.ofReal (InB.card : ℝ) := by
      rw [h_ofReal_card]
    rw [h5, ←h_mul]
    exact ENNReal.ofReal_le_ofReal h_final_card
  have h_goal : Nreal' δ (nfoldSum k B) ≤
      ENNReal.ofReal ((k : ℝ) * (2 * K) ^ k) * Nreal' δ X := by
    dsimp only [Nreal']
    have h1 : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (nfoldSum k B))) =
        (InB.card : ENNReal) := by
      rw [hNnB, h_encard_InB] <;> simp
    have h2 : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy X)) =
        (IA.card : ENNReal) := by
      rw [hNA, h_encard_IA] <;> simp
    rw [h1, h2]
    exact h_ennreal
  calc Nreal' δ (familySum Y)
      ≤ Nreal' δ (nfoldSum k B) := h_mono
    _ ≤ ENNReal.ofReal ((k : ℝ) * (2 * K) ^ k) * Nreal' δ X := h_goal

/-- Product-form corollary: when all α_i ≥ 1,
`N(Y_0+...+Y_{k-1}) ≤ k · (2k)^k · (∏ α_i)^k · N(X)`. -/
lemma discretized_multiset_pr_product
    {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : 0 < k)
    {X : Set ℝ} {Y : Fin k → Set ℝ}
    (hX : Bornology.IsBounded X)
    (hY : ∀ i, Bornology.IsBounded (Y i))
    (hX_nonempty : X.Nonempty)
    {α : Fin k → ℝ} (hα_nonneg : ∀ i, 0 ≤ α i) (hα_ge_one : ∀ i, 1 ≤ α i)
    (h : ∀ i, Nreal' δ (Set.image2 (· + ·) X (Y i)) ≤ ENNReal.ofReal (α i) * Nreal' δ X) :
    Nreal' δ (familySum Y) ≤
      ENNReal.ofReal ((k : ℝ) * (2 * (k : ℝ)) ^ k * (∏ i : Fin k, α i) ^ k) * Nreal' δ X := by
  have h_sum_le : ∑ i : Fin k, α i ≤ (k : ℝ) * ∏ i : Fin k, α i := by
    have h1 : ∀ i : Fin k, α i ≤ ∏ j : Fin k, α j := by
      intro i
      have h_i_in : i ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ i
      have h2 : ∏ j : Fin k, α j = α i * ∏ j ∈ (Finset.univ : Finset (Fin k)).erase i, α j := by
        have h_i_in : i ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ i
        have h_eq : α i * ∏ j ∈ (Finset.univ : Finset (Fin k)).erase i, α j = ∏ j : Fin k, α j := by
          (expose_names; exact Finset.mul_prod_erase Finset.univ α h_i_in_1)
        exact h_eq.symm
      rw [h2]
      have h4 : 1 ≤ ∏ j ∈ (Finset.univ : Finset (Fin k)).erase i, α j := by
        apply Finset.one_le_prod
        intro j _
        exact hα_ge_one j
      have h5 : 0 ≤ α i := hα_nonneg i
      have h6 : α i ≤ α i * (∏ j ∈ (Finset.univ : Finset (Fin k)).erase i, α j) := by
        have h7 : 1 * α i ≤ (∏ j ∈ (Finset.univ : Finset (Fin k)).erase i, α j) * α i :=
          mul_le_mul_of_nonneg_right h4 h5
        have h8 : 1 * α i = α i := by ring
        have h9 : (∏ j ∈ (Finset.univ : Finset (Fin k)).erase i, α j) * α i =
            α i * (∏ j ∈ (Finset.univ : Finset (Fin k)).erase i, α j) := by ring
        rw [h8, h9] at h7
        exact h7
      exact h6
    have h_sum : ∑ i : Fin k, α i ≤ ∑ i : Fin k, (∏ j : Fin k, α j) :=
      Finset.sum_le_sum (fun i _ => h1 i)
    calc ∑ i : Fin k, α i
        ≤ ∑ i : Fin k, (∏ j : Fin k, α j) := h_sum
      _ = (k : ℝ) * ∏ j : Fin k, α j := by
        simp [Finset.sum_const] <;> ring
  have h_main := discretized_multiset_pr_general hδ hk hX hY hX_nonempty hα_nonneg h
  have h5 : (2 * ∑ i : Fin k, α i) ^ k ≤ (2 * ((k : ℝ) * ∏ i : Fin k, α i)) ^ k := by
    have h_prod_nonneg : 0 ≤ ∏ i : Fin k, α i := Finset.prod_nonneg (fun i _ => hα_nonneg i)
    have h_a_nonneg : 0 ≤ 2 * ∑ i : Fin k, α i := by
      have h : 0 ≤ ∑ i : Fin k, α i := Finset.sum_nonneg (fun i _ => hα_nonneg i)
      linarith
    have h_b_nonneg : 0 ≤ 2 * ((k : ℝ) * ∏ i : Fin k, α i) := by
      have h_k_nonneg : 0 ≤ (k : ℝ) := by positivity
      positivity
    have h_le : 2 * ∑ i : Fin k, α i ≤ 2 * ((k : ℝ) * ∏ i : Fin k, α i) := by
      gcongr
      <;> exact h_sum_le
    have h_ind : ∀ n : ℕ, (2 * ∑ i : Fin k, α i) ^ n ≤ (2 * ((k : ℝ) * ∏ i : Fin k, α i)) ^ n := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
        calc (2 * ∑ i : Fin k, α i) ^ (n + 1)
          = (2 * ∑ i : Fin k, α i) * (2 * ∑ i : Fin k, α i) ^ n := by ring
        _ ≤ (2 * ((k : ℝ) * ∏ i : Fin k, α i)) * (2 * ∑ i : Fin k, α i) ^ n := by
          gcongr <;> linarith
        _ ≤ (2 * ((k : ℝ) * ∏ i : Fin k, α i)) * (2 * ((k : ℝ) * ∏ i : Fin k, α i)) ^ n := by
          gcongr <;> linarith
        _ = (2 * ((k : ℝ) * ∏ i : Fin k, α i)) ^ (n + 1) := by ring
    exact h_ind k
  have h6 : (k : ℝ) * (2 * ∑ i : Fin k, α i) ^ k ≤
      (k : ℝ) * (2 * (k : ℝ)) ^ k * (∏ i : Fin k, α i) ^ k := by
    have h_k_nonneg : 0 ≤ (k : ℝ) := by positivity
    calc (k : ℝ) * (2 * ∑ i : Fin k, α i) ^ k
        ≤ (k : ℝ) * (2 * ((k : ℝ) * ∏ i : Fin k, α i)) ^ k := mul_le_mul_of_nonneg_left h5 h_k_nonneg
      _ = (k : ℝ) * (2 * (k : ℝ)) ^ k * (∏ i : Fin k, α i) ^ k := by ring
  have h7 : ENNReal.ofReal ((k : ℝ) * (2 * ∑ i : Fin k, α i) ^ k) ≤
      ENNReal.ofReal ((k : ℝ) * (2 * (k : ℝ)) ^ k * (∏ i : Fin k, α i) ^ k) := by
    exact ENNReal.ofReal_le_ofReal h6
  calc Nreal' δ (familySum Y)
      ≤ ENNReal.ofReal ((k : ℝ) * (2 * ∑ i : Fin k, α i) ^ k) * Nreal' δ X := h_main
    _ ≤ ENNReal.ofReal ((k : ℝ) * (2 * (k : ℝ)) ^ k * (∏ i : Fin k, α i) ^ k) * Nreal' δ X := by
        gcongr

end ProductLikeIncidence
