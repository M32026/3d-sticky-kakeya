module

/-
  Prop73 Inductive Step Bridge Lemmas

  Interface lemmas for constructing `hcfg_fine : CombiningConfig` in the
  inductive step of Proposition 7.3 (InductiveStep.lean:1218).

  Four bridge gaps:
  1. Scale normalization: Δ' i = Δ(i+1)/Δ1 algebraic properties
  2. Index set extraction: MainSquare finset → (ℤ×ℤ) finset
  3. Fine point set geometric containment: finePointSet ⊆ P_Q
  4. Covering density from cardinality: card ratio → EC density

  Whiteprint node: combining_theorem_genuine / inductive_step_bridge
  Status: Bridge lemmas proved. Good-scale transfer uses per-square density.

  Key lemmas:
  - `scale_normalization_properties`
  - `mainSquare_finset_to_indices`
  - `fine_point_set_subset_full`
  - `global_covering_density_from_cardinality`
  - `between_scales_transfer_with_density`
  - `fine_between_scales_from_tail_consumer` (density-based h_normal/h_good wrapper)

  Key dependencies:
  - `squareHomothety_toSet` (FormatConversionLemmas.lean:745)
  - `dyadic_union_cover_upper` / `_lower` (GoodTransfer.lean:860/893)
  - `between_scales_transfer_all` (BetweenScalesTransfer.lean:43)
  - `IsSetBetweenScales.subset_with_density` (GoodTransfer.lean:686)
  - `IsRegularBetweenScales.subset_with_density` (GoodTransfer.lean:733)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.GoodTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.BetweenScalesTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.GeometricIntersection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FormatConversionLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.BasicUniformization
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformisationLemma_Bridge
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.InductionConfigurations
open DiscretisedFurstenbergEstimate.BasicUniformization
open DiscretisedFurstenbergEstimate.InductionOnScales
open DirecretisedFurstenbergEstimate.FormatConversion.M5

/-! ========================================================================
   Gap 1: Scale normalization

   Given Δ : Fin (n_fine+2) → ℝ with CombiningConfig properties, define
   Δ' : Fin (n_fine+1) → ℝ by Δ' i = Δ (Fin.succ i) / Δ 1.
   Prove Δ' is positive, dyadic, strictly decreasing, starts at 1,
   and the scale-ratio bound transfers (with δbar^τ replacing δ^τ).

   Using n_fine as the base avoids Fin (n-1) arithmetic issues.
   ======================================================================== -/

/-- Scale normalization: all algebraic properties of Δ' needed by
    `CombiningConfig` for the fine configuration.

    The original has `n_fine + 1` levels (`n_fine + 2` scales); the normalized
    fine config has `n_fine` levels (`n_fine + 1` scales). -/
lemma scale_normalization_properties
    {n_fine : ℕ}
    (Δ : Fin (n_fine + 2) → ℝ)
    (hΔ_pos : ∀ i, 0 < Δ i)
    (hΔ_dyadic : ∀ i, Δ i ∈ dyadicScales)
    (hΔ_strict : ∀ j : Fin (n_fine + 1), Δ (Fin.succ j) < Δ j.castSucc)
    (hΔ_start : Δ 0 = 1)
    (δ : ℝ)
    (hΔ_end : Δ (Fin.last (n_fine + 1)) = δ)
    (δbar : ℝ)
    (hδbar_eq : δbar = Δ (Fin.last (n_fine + 1)) / Δ 1)
    (τ : ℝ) (hτ_pos : 0 < τ)
    (scaleClass : Fin (n_fine + 1) → ScaleClass)
    (h_scale_ratio : ∀ j : Fin (n_fine + 1), ¬(scaleClass j).isBad →
      Δ (Fin.succ j) / Δ j.castSucc ≤ Real.rpow δ τ) :
    let Δ' : Fin (n_fine + 1) → ℝ := fun i => Δ (Fin.succ i) / Δ 1
    (∀ i : Fin (n_fine + 1), 0 < Δ' i) ∧
    (∀ i : Fin (n_fine + 1), Δ' i ∈ dyadicScales) ∧
    (∀ j : Fin n_fine, Δ' (Fin.succ j) < Δ' j.castSucc) ∧
    Δ' 0 = 1 ∧
    (∀ j : Fin n_fine,
      ¬(scaleClass (Fin.succ j)).isBad →
        Δ' (Fin.succ j) / Δ' j.castSucc ≤ Real.rpow δbar τ) := by
  let Δ' : Fin (n_fine + 1) → ℝ := fun i => Δ (Fin.succ i) / Δ 1
  let i1 : Fin (n_fine + 2) := 1
  have hΔ1_pos : 0 < Δ i1 := hΔ_pos i1
  have hΔ1_le_one : Δ i1 ≤ 1 := by
    have h : Δ i1 ≤ Δ 0 := (hΔ_strict 0).le
    rw [hΔ_start] at h <;> exact h
  have hδ_pos : 0 < δ := by
    have h_eq : δ = Δ (Fin.last (n_fine + 1)) := hΔ_end.symm
    rw [h_eq]
    exact hΔ_pos (Fin.last (n_fine + 1))
  have hδbar_ge_δ : δ ≤ δbar := by
    have h_eq : δbar = δ / Δ i1 := by
      rw [hδbar_eq, hΔ_end]
    rw [h_eq]
    have hδ_nonneg : 0 ≤ δ := by
      have h_eq2 : δ = Δ (Fin.last (n_fine + 1)) := hΔ_end.symm
      rw [h_eq2] <;> exact (hΔ_pos (Fin.last (n_fine + 1))).le
    calc
      δ / Δ i1 ≥ δ / 1 := by gcongr <;> linarith
      _ = δ := by ring
  -- Chain: Δ (Fin.succ i) ≤ Δ i1 for all i : Fin (n_fine + 1)
  have h_chain : ∀ (i : Fin (n_fine + 1)), Δ (Fin.succ i) ≤ Δ i1 := by
    have h_main : ∀ (m : ℕ), m ≤ n_fine →
        ∀ (i : Fin (n_fine + 1)), i.val = m → Δ (Fin.succ i) ≤ Δ i1 := by
      intro m hm
      induction m with
      | zero =>
        intro i hi
        have h_i0 : i = 0 := by
          apply Fin.ext
          simpa using hi
        rw [h_i0]
        have h_eq : (Fin.succ (0 : Fin (n_fine + 1)) : Fin (n_fine + 2)) = i1 := by
          apply Fin.ext <;> simp [i1]
        rw [h_eq]
      | succ m ih =>
        intro i hi
        let i_pred : Fin (n_fine + 1) := ⟨i.val - 1, by omega⟩
        have h_pred_val : i_pred.val = m := by
          simp [i_pred, hi] <;> omega
        have h_ih : Δ (Fin.succ i_pred) ≤ Δ i1 := ih (by omega) i_pred h_pred_val
        have h_cast_eq : (i.castSucc : Fin (n_fine + 2)) = Fin.succ i_pred := by
          apply Fin.ext
          simp [i_pred] <;> omega
        have h_strict : Δ (Fin.succ i) < Δ i.castSucc := hΔ_strict i
        rw [h_cast_eq] at h_strict
        exact h_strict.le.trans h_ih
    intro i
    exact h_main i.val (by omega) i rfl
  -- Positivity
  have h_pos : ∀ i : Fin (n_fine + 1), 0 < Δ' i := by
    intro i
    exact div_pos (hΔ_pos (Fin.succ i)) hΔ1_pos
  -- Dyadic
  have h_dyadic : ∀ i : Fin (n_fine + 1), Δ' i ∈ dyadicScales := by
    intro i
    have h_le : Δ (Fin.succ i) ≤ Δ i1 := h_chain i
    exact dyadic_quotient (hΔ_dyadic (Fin.succ i)) (hΔ_dyadic i1) h_le (hΔ_pos (Fin.succ i))
  -- Strict decreasing
  have h_strict : ∀ j : Fin n_fine, Δ' (Fin.succ j) < Δ' j.castSucc := by
    intro j
    let j' : Fin (n_fine + 1) := Fin.succ j
    have h_succ_eq : (Fin.succ (j.castSucc) : Fin (n_fine + 2)) = j'.castSucc := by
      apply Fin.ext
      simp [j'] <;> omega
    have h : Δ (Fin.succ j') < Δ j'.castSucc := hΔ_strict j'
    have h4 : Δ' (Fin.succ j) = Δ (Fin.succ j') / Δ i1 := by rfl
    have h5 : Δ' j.castSucc = Δ j'.castSucc / Δ i1 := by
      dsimp only [Δ']
      rw [h_succ_eq]
    rw [h4, h5]
    gcongr
  -- Start at 1
  have h_start : Δ' 0 = 1 := by
    dsimp only [Δ']
    have h_eq : (Fin.succ (0 : Fin (n_fine + 1)) : Fin (n_fine + 2)) = i1 := by
      apply Fin.ext
      simp [i1]
    rw [h_eq]
    exact div_self hΔ1_pos.ne'
  -- Scale ratio transfer
  have h_ratio : ∀ j : Fin n_fine,
      ¬(scaleClass (Fin.succ j)).isBad →
        Δ' (Fin.succ j) / Δ' j.castSucc ≤ Real.rpow δbar τ := by
    intro j hnotbad
    let j' : Fin (n_fine + 1) := Fin.succ j
    have h_succ_eq : (Fin.succ (j.castSucc) : Fin (n_fine + 2)) = j'.castSucc := by
      apply Fin.ext
      simp [j'] <;> omega
    have h_ratio_eq : Δ' (Fin.succ j) / Δ' j.castSucc =
        Δ (Fin.succ j') / Δ j'.castSucc := by
      dsimp only [Δ']
      have h_succ_eq : (Fin.succ (j.castSucc) : Fin (n_fine + 2)) = j'.castSucc := by
        apply Fin.ext <;> simp [j'] <;> omega
      calc
        (Δ (Fin.succ j') / Δ i1) / (Δ (Fin.succ (j.castSucc)) / Δ i1)
          = (Δ (Fin.succ j') / Δ i1) / (Δ j'.castSucc / Δ i1) := by
            rw [h_succ_eq]
        _ = Δ (Fin.succ j') / Δ j'.castSucc := by
            field_simp [hΔ1_pos.ne'] <;> ring
    rw [h_ratio_eq]
    have h6 : Δ (Fin.succ j') / Δ j'.castSucc ≤ Real.rpow δ τ :=
      h_scale_ratio j' hnotbad
    have h7 : Real.rpow δ τ ≤ Real.rpow δbar τ :=
      Real.rpow_le_rpow (by linarith) hδbar_ge_δ (by linarith)
    exact le_trans h6 h7
  exact ⟨h_pos, h_dyadic, h_strict, h_start, h_ratio⟩

/-! ========================================================================
   Gap 2: Index set extraction

   Convert Finset (MainSquare n) to Finset (ℤ × ℤ) via p ↦ (p.i, p.j).
   Card and subset are preserved because the map is injective.
   ======================================================================== -/

/-- Map a DyadicSquare to its index pair. -/
def mainSquareToIndices {n : ℕ} (p : DyadicSquare n) : ℤ × ℤ := (p.i, p.j)

/-- The map p ↦ (p.i, p.j) is injective. -/
lemma mainSquareToIndices_injective {n : ℕ} :
    Function.Injective (mainSquareToIndices (n := n)) := by
  intro p q h
  have hi : p.i = q.i := by simpa [mainSquareToIndices] using congr_arg Prod.fst h
  have hj : p.j = q.j := by simpa [mainSquareToIndices] using congr_arg Prod.snd h
  exact Bridge.dyadicSquare_eq hi hj

/-- Convert a finset of DyadicSquares to a finset of index pairs.
    Card is preserved and subset is reflected. -/
lemma mainSquare_finset_to_indices {n : ℕ} (P : Finset (DyadicSquare n)) :
    ∃ (S : Finset (ℤ × ℤ)),
      S.card = P.card ∧
      ∀ (P' : Finset (DyadicSquare n)), P' ⊆ P →
        (P'.image mainSquareToIndices) ⊆ S := by
  let S := P.image mainSquareToIndices
  have h_card : S.card = P.card :=
    Finset.card_image_of_injective _ mainSquareToIndices_injective
  have h_sub : ∀ (P' : Finset (DyadicSquare n)), P' ⊆ P →
      (P'.image mainSquareToIndices) ⊆ S := by
    intro P' hP'
    exact Finset.image_subset_image hP'
  exact ⟨S, h_card, h_sub⟩

/-- Compatibility with parentBy: the index of a square's parent at the
    B1 refinement level equals the containing square's indices.
    The compatible refinement factor is `n - m`, because `containingSquare hnm`
    divides indices by `2^(n-m)`, which is exactly what `parentBy (n-m)` does. -/
lemma mainSquareToIndices_parentBy {n m : ℕ} (hnm : m ≤ n)
    (p : DyadicSquare n) :
    parentBy (n - m) (mainSquareToIndices p) =
      mainSquareToIndices (InductionConfigurations.containingSquare hnm p) := by
  dsimp only [mainSquareToIndices, parentBy, InductionConfigurations.containingSquare,
    InductionConfigurations.refinementFactor]
  <;> rfl

/-! ========================================================================
   Gap 3: Fine point set geometric containment

   The fine config point set is exactly the homothety image of the thinned
   point set intersected with Q. This follows from squareHomothety_toSet.
   ======================================================================== -/

/-- The point set of a fine config is the homothety image of the thinned
    point set within the coarse square Q.

    Given P_thin : Finset (DyadicSquare n) with all squares contained in Q,
    the union of (squareHomothety hnm Q p).toSet for p ∈ P_thin equals
    homothetyS (dyadicDelta m) Q.i Q.j '' (⋃ p ∈ P_thin, p.toSet). -/
lemma fine_point_set_homothety_image
    {n m : ℕ} (hnm : m ≤ n) (Q : DyadicSquare m)
    (P_thin : Finset (DyadicSquare n))
    (h_contained : ∀ p ∈ P_thin, squareContained hnm p Q) :
    (⋃ p ∈ P_thin, ((InductionConfigurations.squareHomothety hnm Q p).toSet : Set Plane)) =
    homothetyS (dyadicDelta m) Q.i Q.j ''
      (⋃ p ∈ P_thin, (p.toSet : Set Plane)) := by
  have h_eq1 : (⋃ p ∈ P_thin, ((squareHomothety hnm Q p).toSet : Set Plane)) =
      ⋃ p ∈ P_thin, (homothetyS (dyadicDelta m) Q.i Q.j '' p.toSet) := by
    ext x
    simp only [Set.mem_iUnion₂]
    <;> constructor <;> rintro ⟨p, hp, hxp⟩ <;> refine ⟨p, hp, ?_⟩
    · exact (squareHomothety_toSet hnm Q p).symm ▸ hxp
    · exact (squareHomothety_toSet hnm Q p) ▸ hxp
  rw [h_eq1]
  have h_eq2 : (⋃ p ∈ P_thin, (homothetyS (dyadicDelta m) Q.i Q.j '' p.toSet)) =
      homothetyS (dyadicDelta m) Q.i Q.j '' (⋃ p ∈ P_thin, (p.toSet : Set Plane)) := by
    ext x
    simp only [Set.mem_iUnion₂, Set.mem_image]
    constructor
    · rintro ⟨p, hp, y, hyp, rfl⟩
      exact ⟨y, ⟨p, hp, hyp⟩, rfl⟩
    · rintro ⟨y, ⟨p, hp, hyp⟩, rfl⟩
      exact ⟨p, hp, y, hyp, rfl⟩
  exact h_eq2

/-- The fine point set is a subset of the homothety image of the FULL
    original point set intersected with Q. -/
lemma fine_point_set_subset_full
    {n m : ℕ} (hnm : m ≤ n) (Q : DyadicSquare m)
    (P_full P_thin : Finset (DyadicSquare n))
    (hP_thin_sub : P_thin ⊆ P_full)
    (h_contained : ∀ p ∈ P_thin, squareContained hnm p Q) :
    (⋃ p ∈ P_thin, ((squareHomothety hnm Q p).toSet : Set Plane)) ⊆
    homothetyS (dyadicDelta m) Q.i Q.j ''
      ((⋃ p ∈ P_full, (p.toSet : Set Plane)) ∩
        BasicUniformization.dyadicSquare (dyadicDelta m) Q.i Q.j) := by
  have h1 : (⋃ p ∈ P_thin, (p.toSet : Set Plane)) ⊆
      (⋃ p ∈ P_full, (p.toSet : Set Plane)) := by
    intro x hx
    have h_exists : ∃ (p : DyadicSquare n), p ∈ P_thin ∧ x ∈ (p.toSet : Set Plane) := by
      simpa [Finset.mem_biUnion] using hx
    rcases h_exists with ⟨p, hp, hxp⟩
    have h_in_full : p ∈ P_full := hP_thin_sub hp
    have : x ∈ (⋃ p ∈ P_full, (p.toSet : Set Plane)) := by
      simpa [Finset.mem_biUnion] using ⟨p, h_in_full, hxp⟩
    exact this
  have hQ_toSet_eq : (Q.toSet : Set Plane) =
      BasicUniformization.dyadicSquare (dyadicDelta m) Q.i Q.j := by
    ext y
    simp only [DyadicSquare.toSet, BasicUniformization.dyadicSquare, Set.mem_setOf_eq, Set.mem_Ico]
    <;> constructor
    · intro h
      exact ⟨⟨h.1, h.2.1⟩, ⟨h.2.2.1, h.2.2.2⟩⟩
    · intro h
      exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
  have h2 : ∀ p ∈ P_thin, (p.toSet : Set Plane) ⊆
      BasicUniformization.dyadicSquare (dyadicDelta m) Q.i Q.j := by
    intro p hp
    have h_cont : squareContained hnm p Q := h_contained p hp
    have h_sub : (p.toSet : Set Plane) ⊆ (Q.toSet : Set Plane) :=
      squareContained_toSet_subset hnm h_cont
    rw [hQ_toSet_eq] at h_sub
    exact h_sub
  have h3 : (⋃ p ∈ P_thin, (p.toSet : Set Plane)) ⊆
      BasicUniformization.dyadicSquare (dyadicDelta m) Q.i Q.j := by
    intro x hx
    have h_exists : ∃ (p : DyadicSquare n), p ∈ P_thin ∧ x ∈ (p.toSet : Set Plane) := by
      simpa [Finset.mem_biUnion] using hx
    rcases h_exists with ⟨p, hp, hxp⟩
    exact h2 p hp hxp
  rw [fine_point_set_homothety_image hnm Q P_thin h_contained]
  have h4 : (⋃ p ∈ P_thin, (p.toSet : Set Plane)) ⊆
      (⋃ p ∈ P_full, (p.toSet : Set Plane)) ∩
        BasicUniformization.dyadicSquare (dyadicDelta m) Q.i Q.j := by
    intro x hx
    exact ⟨h1 hx, h3 hx⟩
  exact Set.image_mono h4

/-! ========================================================================
   Gap 4: Covering density from cardinality

   For unions of dyadic squares at scale ε:
     cover_ε(A) ≤ |S|          (upper)
     cover_ε(A) ≥ |S| / 9      (lower)
   So if |S_full| ≤ K * |S_thin|, then
     cover(S_full) ≤ 9 * K * cover(S_thin)
   i.e. c = 1/(9*K) gives covering density.
   ======================================================================== -/

/-- Global covering density from cardinality ratio.

    Given two finsets of dyadic squares at the same scale, with
    `card_full ≤ K * card_thin`, derive
    `(1/(9*K)) * EC(fullSet) ≤ EC(thinSet)`.

    NOTE: This is a GLOBAL bound. For `IsSetBetweenScales.subset_with_density`,
    a per-coarse-square bound is required. See module documentation for the
    remaining architectural gap.
-/
lemma global_covering_density_from_cardinality
    {n : ℕ} (P_full P_thin : Finset (DyadicSquare n))
    (K : ℝ) (hK_pos : 0 < K)
    (h_card : (P_full.card : ℝ) ≤ K * (P_thin.card : ℝ)) :
    ENNReal.ofReal (1 / (9 * K)) *
      Metric.externalCoveringNumber (dyadicDelta n).toNNReal
        (⋃ p ∈ P_full, (p.toSet : Set Plane)) ≤
    Metric.externalCoveringNumber (dyadicDelta n).toNNReal
      (⋃ p ∈ P_thin, (p.toSet : Set Plane)) := by
  set ε := (dyadicDelta n).toNNReal with hε
  let A_full := (⋃ p ∈ P_full, (p.toSet : Set Plane))
  let A_thin := (⋃ p ∈ P_thin, (p.toSet : Set Plane))
  have h_upper_full : Metric.externalCoveringNumber ε A_full ≤ (P_full.card : ℕ∞) :=
    dyadic_union_cover_upper P_full
  have h_lower_thin : (P_thin.card : ENNReal) / (9 : ENNReal) ≤
      Metric.externalCoveringNumber ε A_thin :=
    dyadic_union_cover_lower P_thin
  have h_card' : (P_full.card : ENNReal) ≤ ENNReal.ofReal K * (P_thin.card : ENNReal) := by
    have h1 : (P_full.card : ℝ) ≤ K * (P_thin.card : ℝ) := h_card
    have h2 : ENNReal.ofReal (P_full.card : ℝ) ≤ ENNReal.ofReal (K * (P_thin.card : ℝ)) :=
      ENNReal.ofReal_le_ofReal h1
    have h3 : ENNReal.ofReal (K * (P_thin.card : ℝ)) = ENNReal.ofReal K * (P_thin.card : ENNReal) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      <;> norm_cast
    have h4 : (P_full.card : ENNReal) = ENNReal.ofReal (P_full.card : ℝ) := by norm_cast
    have h5 : ENNReal.ofReal (P_full.card : ℝ) ≤ ENNReal.ofReal K * (P_thin.card : ENNReal) := by
      rw [h3] at h2
      exact h2
    rw [h4]
    exact h5
  have h_algebra : ENNReal.ofReal (1 / (9 * K)) * (ENNReal.ofReal K * (P_thin.card : ENNReal)) =
      (P_thin.card : ENNReal) / (9 : ENNReal) := by
    have h1 : ENNReal.ofReal (1 / (9 * K)) * ENNReal.ofReal K = ENNReal.ofReal (1 / 9 : ℝ) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      <;> congr 1 <;> field_simp [hK_pos.ne'] <;> ring
    have h4 : ENNReal.ofReal (1 / 9 : ℝ) = (1 : ENNReal) / (9 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 9 by norm_num)]
      <;> norm_cast
    calc
      ENNReal.ofReal (1 / (9 * K)) * (ENNReal.ofReal K * (P_thin.card : ENNReal))
        = (ENNReal.ofReal (1 / (9 * K)) * ENNReal.ofReal K) * (P_thin.card : ENNReal) := by rw [mul_assoc]
      _ = ENNReal.ofReal (1 / 9 : ℝ) * (P_thin.card : ENNReal) := by rw [h1]
      _ = (P_thin.card : ENNReal) * ENNReal.ofReal (1 / 9 : ℝ) := by rw [mul_comm]
      _ = (P_thin.card : ENNReal) * ((1 : ENNReal) / (9 : ENNReal)) := by rw [h4]
      _ = (P_thin.card : ENNReal) / (9 : ENNReal) := by
        simp [div_eq_mul_inv] <;> rfl
  calc
    ENNReal.ofReal (1 / (9 * K)) * Metric.externalCoveringNumber ε A_full
      ≤ ENNReal.ofReal (1 / (9 * K)) * (P_full.card : ENNReal) := by
        gcongr <;> exact_mod_cast h_upper_full
    _ ≤ ENNReal.ofReal (1 / (9 * K)) * (ENNReal.ofReal K * (P_thin.card : ENNReal)) := by
        gcongr
    _ = (P_thin.card : ENNReal) / (9 : ENNReal) := h_algebra
    _ ≤ Metric.externalCoveringNumber ε A_thin := h_lower_thin

/-! ========================================================================
   Between-scales transfer via per-square covering density

   `between_scales_transfer_with_density` wraps
   `IsRegularBetweenScales.subset_with_density` for a single level.

   `fine_between_scales_from_tail_consumer` applies this at each good level,
   while normal levels pass through the tail consumer output directly.
   ======================================================================== -/

/-- IF per-square covering density holds, then between-scales properties
    transfer from P_Q to the fine point set with amplified constant 9*K*C.

    The density hypothesis `hdensity` is exactly what
    `IsSetBetweenScales.subset_with_density` requires. -/
lemma between_scales_transfer_with_density
    {P_Q P_fine : Set Plane} {δ Δ s C K c : ℝ}
    (h_reg : IsRegularBetweenScales P_Q δ Δ s C K)
    (hsub : P_fine ⊆ P_Q)
    (hc_pos : 0 < c)
    (hdensity : ∀ (i j : ℤ), (P_Q ∩ CombiningTheorem.dyadicSquare Δ i j).Nonempty →
      ENNReal.ofReal c *
        Metric.externalCoveringNumber (δ / Δ).toNNReal
          (homothetyS Δ i j '' (P_Q ∩ CombiningTheorem.dyadicSquare Δ i j)) ≤
      Metric.externalCoveringNumber (δ / Δ).toNNReal
          (homothetyS Δ i j '' (P_fine ∩ CombiningTheorem.dyadicSquare Δ i j))) :
    IsRegularBetweenScales P_fine δ Δ s (C / c) K :=
  IsRegularBetweenScales.subset_with_density h_reg hsub hc_pos hdensity

/-- Inverse of mainSquareToIndices: build a DyadicSquare from an index pair. -/
def indicesToMainSquare {n : ℕ} (idx : ℤ × ℤ) : DyadicSquare n :=
  ⟨idx.1, idx.2⟩

/-- indicesToMainSquare is the inverse of mainSquareToIndices. -/
lemma indicesToMainSquare_left_inv {n : ℕ} (p : DyadicSquare n) :
    indicesToMainSquare (mainSquareToIndices p) = p := by
  cases p <;> simp [indicesToMainSquare, mainSquareToIndices] <;> rfl

/-- mainSquareToIndices is the inverse of indicesToMainSquare. -/
lemma indicesToMainSquare_right_inv {n : ℕ} (idx : ℤ × ℤ) :
    mainSquareToIndices (indicesToMainSquare (n := n) idx) = idx := by
  simp [indicesToMainSquare, mainSquareToIndices] <;> rfl

/-- Convert a finset of index pairs to a finset of DyadicSquares.
    Card is preserved and the point sets match. -/
lemma indices_finset_to_mainSquare {n : ℕ} [DecidableEq (DyadicSquare n)] (S : Finset (ℤ × ℤ)) :
    (S.image (indicesToMainSquare (n := n))).card = S.card ∧
    (⋃ p ∈ (S.image (indicesToMainSquare (n := n))), (p.toSet : Set Plane)) =
      setFromIndices (dyadicDelta n) S := by
  classical
  let f := indicesToMainSquare (n := n)
  let P := S.image f
  have h_inj : Function.Injective f := by
    intro a b h
    have h1 : mainSquareToIndices (f a) = mainSquareToIndices (f b) := by rw [h]
    have h2 : mainSquareToIndices (f a) = a := indicesToMainSquare_right_inv a
    have h3 : mainSquareToIndices (f b) = b := indicesToMainSquare_right_inv b
    rw [h2, h3] at h1
    exact h1
  have h_card : P.card = S.card :=
    Finset.card_image_of_injective _ h_inj
  have h1 : (⋃ p ∈ P, (p.toSet : Set Plane)) =
      ⋃ idx ∈ S, ((f idx).toSet : Set Plane) := by
    ext x
    simp [P, Finset.mem_image, Set.mem_iUnion₂]
    <;> aesop
  have h_eq1 : ∀ idx : ℤ × ℤ, (f idx).toSet =
      BasicUniformization.dyadicSquare (dyadicDelta n) idx.1 idx.2 := by
    intro idx
    ext y
    simp only [f, indicesToMainSquare, DyadicSquare.toSet, BasicUniformization.dyadicSquare,
      Set.mem_setOf_eq, Set.mem_Ico]
    <;> constructor
    · intro h
      exact ⟨⟨h.1, h.2.1⟩, ⟨h.2.2.1, h.2.2.2⟩⟩
    · intro h
      exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
  have h2 : (⋃ idx ∈ S, ((f idx).toSet : Set Plane)) =
      ⋃ idx ∈ S, BasicUniformization.dyadicSquare (dyadicDelta n) idx.1 idx.2 := by
    ext x
    simp only [Set.mem_iUnion₂]
    <;> constructor <;> rintro ⟨idx, hidx, hxp⟩ <;> refine ⟨idx, hidx, ?_⟩
    · exact (h_eq1 idx) ▸ hxp
    · exact (h_eq1 idx).symm ▸ hxp
  have h3 : (⋃ idx ∈ S, BasicUniformization.dyadicSquare (dyadicDelta n) idx.1 idx.2) =
      setFromIndices (dyadicDelta n) S := by rfl
  have h_toSet : (⋃ p ∈ P, (p.toSet : Set Plane)) = setFromIndices (dyadicDelta n) S := by
    rw [h1, h2, h3]
  exact ⟨h_card, h_toSet⟩

/-- The point set of config.P₀ equals setFromIndices of its index image. -/
lemma config_pointSet_eq_setFromIndices {k : ℕ} {s C : ℝ} {M : ℕ}
    (config : CombiningTheorem.NiceConfiguration k s C M) :
    config.pointSet = setFromIndices (dyadicDelta k)
        (config.P₀.image (fun p : DyadicSquare k => (p.i, p.j))) := by
  dsimp only [CombiningTheorem.NiceConfiguration.pointSet]
  have h_eq2 : ∀ (p : DyadicSquare k), (p.toSet : Set Plane) =
      BasicUniformization.dyadicSquare (dyadicDelta k) p.i p.j := by
    intro p
    ext x
    simp only [DyadicSquare.toSet, BasicUniformization.dyadicSquare, Set.mem_setOf_eq, Set.mem_Ico]
    <;> constructor
    · intro h
      exact ⟨⟨h.1, h.2.1⟩, ⟨h.2.2.1, h.2.2.2⟩⟩
    · intro h
      exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
  have hfg2 : (fun p : DyadicSquare k => (p.toSet : Set Plane)) =
      (fun p => BasicUniformization.dyadicSquare (dyadicDelta k) p.i p.j) := by
    funext p
    exact h_eq2 p
  have h_main : (⋃ p ∈ config.P₀, (p.toSet : Set Plane)) =
      setFromIndices (dyadicDelta k) (config.P₀.image (fun p : DyadicSquare k => (p.i, p.j))) := by
    ext z
    simp only [NiceConfiguration.pointSet, Set.mem_iUnion₂, Finset.mem_coe, Finset.mem_image,
      setFromIndices]
    constructor
    · rintro ⟨p, hp, hz⟩
      refine ⟨(p.i, p.j), ⟨p, hp, rfl⟩, ?_⟩
      have h := h_eq2 p
      rw [h] at hz
      exact hz
    · rintro ⟨_, ⟨p, hp, rfl⟩, hz⟩
      have hz' : z ∈ BasicUniformization.dyadicSquare (dyadicDelta k) p.i p.j := by
        simpa using hz
      exact ⟨p, hp, (h_eq2 p).symm ▸ hz'⟩
  exact h_main

/-- Per-level wrapper: produce h_normal and h_good for the fine config.

    For normal scales: pass through the tail consumer's IsSetBetweenScales
    at exponent s directly.

    For good scales: transfer IsRegularBetweenScales from P_Q to P_fine at
    the original exponent t_j using per-square covering density.
    `IsRegularBetweenScales.subset_with_density` amplifies the S-set constant
    by 1/c; the half-scale covering constant K is unchanged by monotonicity.

    No exponent strengthening is used. -/
lemma fine_between_scales_from_tail_consumer
    {n_fine : ℕ}
    (Δ' : Fin (n_fine + 1) → ℝ)
    (scaleClass' : Fin n_fine → ScaleClass)
    (P_Q P_fine : Set Plane)
    (s : ℝ)
    (C_s C_reg K_reg : Fin n_fine → ℝ)
    (c : ℝ)
    (h_sub : P_fine ⊆ P_Q)
    (hc_pos : 0 < c)
    -- Tail consumer output: IsSetBetweenScales at exponent s at normal levels
    (h_set_fine : ∀ (j : Fin n_fine),
      scaleClass' j = ScaleClass.normal →
        IsSetBetweenScales P_fine
          (Δ' (Fin.succ j)) (Δ' j.castSucc) s (C_s j))
    -- Regularity on P_Q at good levels (transferred from original)
    (h_reg_Q : ∀ (j : Fin n_fine) (t_j : ℝ),
      scaleClass' j = ScaleClass.good t_j →
        IsRegularBetweenScales P_Q
          (Δ' (Fin.succ j)) (Δ' j.castSucc) t_j
          (C_reg j) (K_reg j))
    -- Per-square covering density at good levels
    (h_density_good : ∀ (j : Fin n_fine) (t_j : ℝ),
      scaleClass' j = ScaleClass.good t_j →
        ∀ (i k : ℤ), (P_Q ∩ CombiningTheorem.dyadicSquare (Δ' j.castSucc) i k).Nonempty →
          ENNReal.ofReal c *
            Metric.externalCoveringNumber ((Δ' (Fin.succ j)) / (Δ' j.castSucc)).toNNReal
              (homothetyS (Δ' j.castSucc) i k '' (P_Q ∩ CombiningTheorem.dyadicSquare (Δ' j.castSucc) i k)) ≤
          Metric.externalCoveringNumber ((Δ' (Fin.succ j)) / (Δ' j.castSucc)).toNNReal
              (homothetyS (Δ' j.castSucc) i k '' (P_fine ∩ CombiningTheorem.dyadicSquare (Δ' j.castSucc) i k))) :
    (∀ (j : Fin n_fine),
      scaleClass' j = ScaleClass.normal →
        IsSetBetweenScales P_fine
          (Δ' (Fin.succ j)) (Δ' j.castSucc) s (C_s j)) ∧
    (∀ (j : Fin n_fine) (t_j : ℝ),
      scaleClass' j = ScaleClass.good t_j →
        IsRegularBetweenScales P_fine
          (Δ' (Fin.succ j)) (Δ' j.castSucc) t_j
          (C_reg j / c) (K_reg j)) := by
  have h1 : ∀ (j : Fin n_fine),
      scaleClass' j = ScaleClass.normal →
        IsSetBetweenScales P_fine
          (Δ' (Fin.succ j)) (Δ' j.castSucc) s (C_s j) :=
    h_set_fine
  have h2 : ∀ (j : Fin n_fine) (t_j : ℝ),
      scaleClass' j = ScaleClass.good t_j →
        IsRegularBetweenScales P_fine
          (Δ' (Fin.succ j)) (Δ' j.castSucc) t_j
          (C_reg j / c) (K_reg j) := by
    intro j t_j hgood
    have h_reg : IsRegularBetweenScales P_Q
        (Δ' (Fin.succ j)) (Δ' j.castSucc) t_j
        (C_reg j) (K_reg j) := h_reg_Q j t_j hgood
    have h_density : ∀ (i k : ℤ), (P_Q ∩ CombiningTheorem.dyadicSquare (Δ' j.castSucc) i k).Nonempty →
        ENNReal.ofReal c *
          Metric.externalCoveringNumber ((Δ' (Fin.succ j)) / (Δ' j.castSucc)).toNNReal
            (homothetyS (Δ' j.castSucc) i k '' (P_Q ∩ CombiningTheorem.dyadicSquare (Δ' j.castSucc) i k)) ≤
        Metric.externalCoveringNumber ((Δ' (Fin.succ j)) / (Δ' j.castSucc)).toNNReal
            (homothetyS (Δ' j.castSucc) i k '' (P_fine ∩ CombiningTheorem.dyadicSquare (Δ' j.castSucc) i k)) :=
      h_density_good j t_j hgood
    exact IsRegularBetweenScales.subset_with_density h_reg h_sub hc_pos h_density
  exact ⟨h1, h2⟩

/-! ========================================================================
   Uniformity bridge: RangeUniformityProp → IsUniformAtScales

   Uses `dyadicSquareCount_setFromIndices_inter` to identify the
   `dyadicSquareCount` with the filtered `parentBy` image cardinality
   that `RangeUniformityProp` bounds (0 or [N, 2N)).
   ======================================================================== -/

/-- Convert `RangeUniformityProp` on an index finset to the genuine
    `IsUniformAtScales` on the corresponding point set.

    For each scale block j and coarse square g, the `dyadicSquareCount`
    at the fine scale equals the filtered `parentBy` cardinality, which
    `RangeUniformityProp` guarantees is either 0 or in [N_j, 2*N_j). -/
lemma rangeUniformity_to_isUniformAtScales
    {n_fine : ℕ} {a : Fin (n_fine + 1) → ℕ}
    {S'' : Finset (ℤ × ℤ)} {N'' : Fin n_fine → ℕ}
    (h : RangeUniformityProp n_fine a S'' N'')
    {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_eq : δ = dyadicDelta (a (Fin.last n_fine)))
    {P : Set Plane} (hP_eq : P = setFromIndices δ S'')
    {Δ' : Fin (n_fine + 1) → ℝ}
    (hΔ'_dyadic : ∀ i, Δ' i = dyadicDelta (a i))
    (ha_mono : ∀ j : Fin n_fine, a j.castSucc ≤ a (Fin.succ j))
    (ha_last_max : ∀ i : Fin (n_fine + 1), a i ≤ a (Fin.last n_fine)) :
    IsUniformAtScales P n_fine Δ' N'' := by
  have hS_nonempty : S''.Nonempty := h.1
  have hN_pos : ∀ (j : Fin n_fine), 1 ≤ N'' j := h.2.1
  have h_set_nonempty : (setFromIndices δ S'').Nonempty := by
    rcases hS_nonempty with ⟨idx, hidx⟩
    let sq : Set Plane := BasicUniformization.dyadicSquare δ idx.1 idx.2
    have h_sq_nonempty : sq.Nonempty := by
      refine' ⟨WithLp.toLp (2 : ENNReal) fun k : Fin 2 =>
        if k = 0 then (idx.1 : ℝ) * δ else (idx.2 : ℝ) * δ, _⟩
      simp only [sq, BasicUniformization.dyadicSquare, Set.mem_setOf_eq]
      <;> constructor <;> simp [PiLp.toLp_apply, Set.mem_Ico] <;> linarith
    have h_sub : sq ⊆ setFromIndices δ S'' := by
      intro x hx
      exact Set.mem_iUnion₂.mpr ⟨idx, hidx, hx⟩
    exact Set.Nonempty.mono h_sub h_sq_nonempty
  have hP_nonempty : P.Nonempty := by
    rw [hP_eq]
    exact h_set_nonempty
  have h_range : ∀ (j : Fin n_fine) (gx gy : ℤ),
      let count := dyadicSquareCount (Δ' (Fin.succ j))
          (P ∩ CombiningTheorem.dyadicSquare (Δ' j.castSucc) gx gy)
      count = 0 ∨ (↑(N'' j) ≤ count ∧ count < ↑(2 * N'' j)) := by
    intro j gx gy
    let g : ℤ × ℤ := (gx, gy)
    set k : ℕ := a (Fin.last n_fine) with hk
    set a_fine : ℕ := a (Fin.succ j) with ha_fine
    set a_coarse : ℕ := a j.castSucc with ha_coarse
    let card_expr : ℕ :=
      ((S''.image (parentBy (k - a_fine))).filter
        (fun idx => parentBy (a_fine - a_coarse) idx = g)).card
    have h1 : a_coarse ≤ a_fine := ha_mono j
    have h2 : a_fine ≤ k := ha_last_max (Fin.succ j)
    have h_bridge : dyadicSquareCount (Δ' (Fin.succ j))
          (P ∩ CombiningTheorem.dyadicSquare (Δ' j.castSucc) gx gy) =
        ↑card_expr := by
      rw [hP_eq, hΔ'_dyadic (Fin.succ j), hΔ'_dyadic j.castSucc, hδ_eq]
      exact OSUniformisation.dyadicSquareCount_setFromIndices_inter
        k a_fine a_coarse h1 h2 S'' g
    rw [h_bridge]
    have h3 := h.2.2 j g
    rcases h3 with (h3 | h3)
    · exact Or.inl (Nat.cast_eq_zero.mpr h3)
    · exact Or.inr ⟨Nat.cast_le.mpr h3.1, Nat.cast_lt.mpr h3.2⟩
  exact ⟨hP_nonempty, hN_pos, h_range⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
