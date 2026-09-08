/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Section6PartBWiring
public import Kakeya.DimensionThree.Plank.PartBOuterFullness
public import Kakeya.DimensionThree.Plank.CollarPlankConflictDegree

/-!
# GWZ Proposition 6.6(B): the constructed Proposition-5.1 output, on one family

 The residue
`Kakeya.Prop66BPartBChainConstructed` (`Kakeya/DimensionThree/Plank/Prop66BChainResidue.lean`)
is the Part-(B) chain of GWZ Proposition 6.6(B) *without* the unconstructible presentation
contract `Kakeya.Section6PartBData.Remark53Prop51`.  Closing it means rebuilding the outer
package of the chain over the family GWZ Proposition 5.1 actually constructs for Part (B).

Three pieces of that construction were already in the tree, each behind its own existential and
therefore on its own copy of the constructed family:

* the plank-presented multiplicity split
  (`Kakeya.Section6PartBData.exists_collarPresentable_prop51_output`,
  `Kakeya/DimensionThree/Plank/Section6PartBPlankOutput.lean`);
* the outer fullness clause
  (`Kakeya.PartBLoss.exists_threshold_partB_outer_fullness`,
  `Kakeya/DimensionThree/Plank/PartBOuterFullness.lean`);
* the essentially distinct extraction
  (`Kakeya.exists_pairwise_ED_collarPlank_subfamily`,
  `Kakeya/DimensionThree/Plank/CollarPlankConflictDegree.lean`).

This file **unifies the first two on a single constructed family** `O`
(`Kakeya.PartBLoss.exists_threshold_constructedProp51Output`), records the clauses the inner
pipeline needs about the same `O` (its parent map, its inner carriers, its inner index set, and its
refinement of the fine family with a sub-polynomial constant), and shows the two constants the
assembly has to absorb — the split constant of the constructed output and the two window constants
of the collar presentation — are sub-polynomial.

## Design, adapted from `origin/numina/22`

The shape of the contract — a Proposition-5.1 contract stated over the *constructed* output rather
than over `Kakeya.Section6PartBData.fineOutput`, with a `δ`-dependent split constant — is the
design of `exists_remark53Prop51_of_datum` on `origin/numina/22`
(`Kakeya/DimensionThree/Plank/Section6PartBSubpolynomial.lean:779` there), read for strategy only
Nothing is imported from that ref; the construction here is the
tree's own (`Kakeya.Section6PartBData.prop51SelectScaleOfDatum`), and the sub-polynomial bounds are
the tree's own pipeline envelope (`Kakeya/Factoring/CoreLossEnvelope.lean`).

## The two window constants are polynomial in the comparability constant

In the residue the plank-dimension constant `K` of the cell bodies is *not* absolute: it is
`Kakeya.GlobalPlankFactorization.plankReadingConst Cw C₀ ^ 2`, bounded only by `δ ^ (-η)`.  The
envelope ratio `Kakeya.flatPrismEnvelopeVolumeRatio.C (windowConst R K)` and the collar conflict
constant `Kakeya.collarConflictConst R K Λ` both depend on `K`, so they cannot be absorbed by a
threshold fixed before the configuration.  `Kakeya.flatPrismEnvelopeVolumeRatio_windowConst_le`
and `Kakeya.collarConflictConst_eq` show both are an absolute constant times `K ^ 6`, which the
`δ ^ (-η)` budget on `K` absorbs.
-/

@[expose] public section

open MeasureTheory Metric Convexity Filter Topology
open scoped ENNReal NNReal

noncomputable section

universe u v

namespace Kakeya

/-! ### Two more pipeline-envelope absorptions -/

namespace PartBLoss

open ShadedBody

/-- **Proposition 5.1's uniform retained-mass coefficient is bounded below by any prescribed
positive power of the master scale.**

The `Rc`-half of `Kakeya.PartBLoss.exists_threshold_rpow_le_fullnessConstant`, exposed on its own:
`Rc = P⁻¹` with `P` the pipeline loss
(`ShadedBody.factoringCoreAtScaleUniformRefinementConstant_eq_inv`), and `P` is sub-polynomial by
`ShadedBody.eventually_factoringCoreAtScaleUniformPipelineLoss_le_rpow_neg`.  This is the constant
of the refinement clause `ShadedBody.FactoringAndMultPropCoreAtScale.refinement`, i.e. GWZ
Proposition 5.1 item 1's `⪆ 1`. -/
theorem exists_threshold_rpow_le_refinementConstant {e : ℝ} (he : 0 < e) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ (δ w : ℝ≥0) (M N : ℕ), 0 < δ → δ ≤ δ₀ → δ ≤ w → w ≤ 1 →
      0 < M → (M : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) →
      ((N + 1 : ℕ) : ENNReal) ≤ (δ : ENNReal) ^ (-(e / 4)) →
      0 < ShadedBody.factoringCoreAtScaleUniformRefinementConstant 3 M N w →
      (δ : ENNReal) ^ e
        ≤ ((ShadedBody.factoringCoreAtScaleUniformRefinementConstant 3 M N w : ℝ≥0) : ENNReal) := by
  obtain ⟨u, hu, hev⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (ShadedBody.eventually_factoringCoreAtScaleUniformPipelineLoss_le_rpow_neg he)
  refine ⟨u, hu, ?_⟩
  intro δ w M N hδ0 hδ hδw hw1 hM hMcard hN hRc
  have hP : (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 M N w : ENNReal)
      ≤ (δ : ENNReal) ^ (-e) := hev ⟨hδ0, hδ⟩ M N hM hMcard hN w hδw hw1
  set P : ℝ≥0 := ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 M N w with hPdef
  set Rc : ℝ≥0 := ShadedBody.factoringCoreAtScaleUniformRefinementConstant 3 M N w with hRcdef
  have hRcP : Rc = P⁻¹ := ShadedBody.factoringCoreAtScaleUniformRefinementConstant_eq_inv 3 M N w
  have hPne : P ≠ 0 := by
    intro h0
    rw [h0, inv_zero] at hRcP
    exact absurd hRcP (ne_of_gt hRc)
  rw [hRcP]
  exact rpow_le_inv_of_le_rpow_neg hPne hP

/-- **Proposition 5.1's uniform multiplicity-product coefficient is sub-polynomial.**

`prodC = 4 · P · C_n` with `P` the pipeline loss
(`ShadedBody.factoringCoreAtScaleUniformProductConstant_eq`); this is the constant of the split
clause `ShadedBody.FactoringAndMultPropCoreAtScale.multiplicity_product`, GWZ Proposition 5.1
item 5's `⪅`. -/
theorem exists_threshold_productConstant_le_rpow_neg {e : ℝ} (he : 0 < e) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ (δ w : ℝ≥0) (M N : ℕ), 0 < δ → δ ≤ δ₀ → δ ≤ w → w ≤ 1 →
      0 < M → (M : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) →
      ((N + 1 : ℕ) : ENNReal) ≤ (δ : ENNReal) ^ (-(e / 8)) →
      ((ShadedBody.factoringCoreAtScaleUniformProductConstant 3 M N w : ℝ≥0) : ENNReal)
        ≤ (δ : ENNReal) ^ (-e) := by
  have he2 : (0 : ℝ) < e / 2 := by positivity
  set A : ℝ≥0 := max 1 (4 * ShadedBody.outerMultiplicityFromLocalBalls.C 3) with hA
  have hA1 : (1 : ENNReal) ≤ (A : ENNReal) := by
    exact_mod_cast (le_max_left _ _ : (1 : ℝ≥0) ≤ A)
  obtain ⟨u₁, hu₁, hev₁⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (ShadedBody.eventually_const_le_coe_rpow_neg hA1 ENNReal.coe_ne_top he2)
  obtain ⟨u₂, hu₂, hev₂⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (ShadedBody.eventually_factoringCoreAtScaleUniformPipelineLoss_le_rpow_neg he2)
  refine ⟨min u₁ u₂, lt_min hu₁ hu₂, ?_⟩
  intro δ w M N hδ0 hδ hδw hw1 hM hMcard hN
  have h1 := hev₁ ⟨hδ0, hδ.trans (min_le_left _ _)⟩
  have hN' : ((N + 1 : ℕ) : ENNReal) ≤ (δ : ENNReal) ^ (-((e / 2) / 4)) := by
    have : -((e / 2) / 4) = -(e / 8) := by ring
    rw [this]; exact hN
  have hP : (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 M N w : ENNReal)
      ≤ (δ : ENNReal) ^ (-(e / 2)) :=
    hev₂ ⟨hδ0, hδ.trans (min_le_right _ _)⟩ M N hM hMcard hN' w hδw hw1
  rw [ShadedBody.factoringCoreAtScaleUniformProductConstant_eq]
  have hδE0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδEtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsplit : (δ : ENNReal) ^ (-e)
      = (δ : ENNReal) ^ (-(e / 2)) * (δ : ENNReal) ^ (-(e / 2)) := by
    rw [← ENNReal.rpow_add _ _ hδE0 hδEtop]; congr 1; ring
  rw [hsplit]
  calc ((4 * ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 M N w
          * ShadedBody.outerMultiplicityFromLocalBalls.C 3 : ℝ≥0) : ENNReal)
      = ((4 * ShadedBody.outerMultiplicityFromLocalBalls.C 3 : ℝ≥0) : ENNReal)
          * (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 M N w : ENNReal) := by
        push_cast; ring
    _ ≤ (A : ENNReal) * (δ : ENNReal) ^ (-(e / 2)) := by
        gcongr
        exact_mod_cast (le_max_right _ _ : 4 * ShadedBody.outerMultiplicityFromLocalBalls.C 3 ≤ A)
    _ ≤ (δ : ENNReal) ^ (-(e / 2)) * (δ : ENNReal) ^ (-(e / 2)) := by
        gcongr
        exact h1.2.2
end PartBLoss

/-! ### The two window constants are polynomial in the comparability constant -/

/-- The absolute part of the envelope ratio
`Kakeya.flatPrismEnvelopeVolumeRatio.C (windowConst R Cw)` at window radius `R`; the
`Cw`-dependence is exactly `Cw ^ 6`. -/
def envelopeWindowPoly (R : ℝ≥0) : ℝ≥0 :=
  max 1 (8 * (8 * (4 * R)) ^ 3 * (4 * R) ^ 3 * (Metric.lt_volume_convexHull.c 3)⁻¹)

theorem one_le_envelopeWindowPoly (R : ℝ≥0) : 1 ≤ envelopeWindowPoly R := le_max_left _ _

/-- **The envelope ratio is at most `envelopeWindowPoly R · Cw ^ 6`.**  Unfolding
`Kakeya.comparablePlankEnvelope.shrink` and `Kakeya.windowPlankEnvelope.windowConst`. -/
theorem flatPrismEnvelopeVolumeRatio_windowConst_le {R Cw : ℝ≥0} (hCw : 1 ≤ Cw) :
    flatPrismEnvelopeVolumeRatio.C (windowPlankEnvelope.windowConst R Cw)
      ≤ envelopeWindowPoly R * Cw ^ 6 := by
  unfold flatPrismEnvelopeVolumeRatio.C
  have hA1 : 1 ≤ envelopeWindowPoly R := one_le_envelopeWindowPoly R
  have hCw6 : 1 ≤ Cw ^ 6 := one_le_pow₀ hCw
  refine max_le ?_ ?_
  · calc (1 : ℝ≥0) ≤ envelopeWindowPoly R := hA1
      _ = envelopeWindowPoly R * 1 := (mul_one _).symm
      _ ≤ envelopeWindowPoly R * Cw ^ 6 := by gcongr
  · have hshr : ((comparablePlankEnvelope.shrink (windowPlankEnvelope.windowConst R Cw)) ^ 3)⁻¹
        = (8 * (4 * R * Cw)) ^ 3 := by
      simp only [comparablePlankEnvelope.shrink, windowPlankEnvelope.windowConst, inv_pow, inv_inv]
    rw [hshr]
    calc 8 * (8 * (4 * R * Cw)) ^ 3 * (4 * R * Cw) ^ 3 * (Metric.lt_volume_convexHull.c 3)⁻¹
        = (8 * (8 * (4 * R)) ^ 3 * (4 * R) ^ 3 * (Metric.lt_volume_convexHull.c 3)⁻¹) * Cw ^ 6 := by
          ring
      _ ≤ envelopeWindowPoly R * Cw ^ 6 := by
          gcongr
          exact le_max_right _ _

/-- The absolute part of the collar conflict constant `Kakeya.collarConflictConst R Cw Λ` at
window radius `R` and dilation `Λ`; the `Cw`-dependence is exactly `Cw ^ 6`. -/
def collarConflictPoly (R Λ : ℝ≥0) : ℝ≥0 :=
  8 * (8 * (4 * R) * Λ) ^ 3 * (Metric.lt_volume_convexHull.c 3)⁻¹

/-- **The collar conflict constant is `collarConflictPoly R Λ · Cw ^ 6`.** -/
theorem collarConflictConst_eq (R Cw Λ : ℝ≥0) :
    collarConflictConst R Cw Λ = collarConflictPoly R Λ * Cw ^ 6 := by
  unfold collarConflictConst collarConflictPoly
  have hshr : (comparablePlankEnvelope.shrink (windowPlankEnvelope.windowConst R Cw))⁻¹
      = 8 * (4 * R * Cw) := by
    simp only [comparablePlankEnvelope.shrink, windowPlankEnvelope.windowConst, inv_inv]
  rw [hshr]
  ring

/-! ### The constructed output, on one family -/

namespace Section6PartBData

open _root_.ShadedBody

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {m Cfib CF C₀ : ℝ≥0}

/-- **The constructed Proposition-5.1 output of a Part-(B) datum, with every clause the 6.6(B)
assembly consumes, on one family `O`.**

`O` is `ShadedBody.outerThickFamilyAtScale` over the outer scale selected by shading mass
(`Kakeya.Section6PartBData.prop51SelectScaleOfDatum`).  The fields are:

* the outer clauses of `Kakeya.Section6PartBData.OuterPackage` on the plank presentation
  `Kakeya.collarPlank` — nonempty outer set inside the cells, collar-presentability (which gives
  the window and the Katz--Tao clause through `Kakeya.collarPlank_carrier_subset_window` and
  `Kakeya.isKatzTao_collarPlank`), and the fullness `δ ^ ηₒ ≤ λ(𝒲, Y_𝒲)`;
* the inner clauses the pipeline `Kakeya.exists_partB_selected_inner_ED_package` needs to be run
  on `O` through `Kakeya.Section6PartBData.withShades`: the parent map is the datum's cell map, the
  inner carriers are the fine tubes, the inner set is exactly the fine tubes over retained cells,
  and the refinement of the fine family has constant `cref`;
* the multiplicity split at constant `Cs`, on every retained cell.

`Cs` and `cref` are **not** absolute (GWZ's `⪅`/`⪆`): the producer bounds them by `δ ^ (∓e)`. -/
structure ConstructedProp51Output
    (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)
    {Cw : ℝ≥0} (hCw : 1 ≤ Cw)
    (O : ShadedBody.ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) ι D.factor.Cell)
    (Cs cref : ℝ≥0) (ηₒ : ℝ) : Prop where
  outerSet_subset : O.outerSet ⊆ D.factor.cells
  outerSet_nonempty : O.outerSet.Nonempty
  presentable : ∀ j ∈ O.outerSet,
    IsCollarPresentable plankWindowRadius Cw a b (D.factor.body j) (O.outerBody j)
  parent_eq : ∀ i, O.parent i = D.cellOfFine i
  inner_carrier : ∀ i, (O.innerBody i).toConvexSpaceBody = (T i).toConvexSpaceBody
  mem_innerSet_iff : ∀ i, i ∈ O.innerSet ↔ i ∈ q ∧ D.cellOfFine i ∈ O.outerSet
  refinement : ShadedBody.IsCRefinement O.innerSet O.innerBody q
    (fun i => (T i).toShadedBody) cref
  outer_fullness : (δ : ℝ≥0) ^ ηₒ ≤ ShadedBody.fullness O.outerSet
    (fun j => (collarPlank one_le_plankWindowRadius hCw hab hb1 (D.factor.body j)
      (O.outerBody j)).toShadedBody)
  split : ∀ j ∈ O.outerSet,
    ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
      ≤ (Cs : ENNReal) * ShadedBody.multiplicity O.outerSet O.outerBody
          * ShadedBody.multiplicity (O.fiber j) O.innerBody

end Section6PartBData

namespace PartBLoss

open _root_.ShadedBody

set_option maxHeartbeats 2000000 in
-- one construction, two long proofs (presentation and fullness) elaborated together
/-- **The constructed Proposition-5.1 output, with outer fullness, sub-polynomial split constant
and sub-polynomial refinement constant, on one family.**

The proofs of `Kakeya.Section6PartBData.exists_collarPresentable_prop51_output` and
`Kakeya.PartBLoss.exists_threshold_partB_outer_fullness`, run once on one construction, plus the
bounds on the split and refinement constants.  Every hypothesis is one of the residue's, and the
plank-dimension constant `Cw` is allowed to be configuration-dependent (`Cw ≤ δ ^ (-η)`); the
envelope ratio it enters is absorbed through `Kakeya.flatPrismEnvelopeVolumeRatio_windowConst_le`.
The produced fine exponent is `η = ηₒ / 48`: the binding constraints are the Remark-5.3 thick
constant (`ηₒ / 24`), the selection bound (`ηₒ / 32`) and the envelope ratio (`ηₒ / 48`). -/
theorem exists_threshold_constructedProp51Output {ηₒ e : ℝ} (hηₒ : 0 < ηₒ) (he : 0 < e) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∃ η > (0 : ℝ),
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type u} {q : Finset ι} {δ : ℝ≥0}
        {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
        {κ : Type v} {coarseSet : Finset κ} {ρ : ℝ≥0}
        {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))} {m Cfib CF C₀ : ℝ≥0}
        (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)
        {Cw : ℝ≥0} (hCw : 1 ≤ Cw),
        0 < δ → δ ≤ δ₀ → (δ : ℝ) ≤ 1 / 2 → 0 < ρ → ρ ≤ 1 → δ ≤ a → 0 < b →
        (∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ Metric.closedBall 0 1) →
        0 < ∑ i ∈ q, volume (T i).shade →
        δ + 2 * a ≤ 1 →
        (∀ x ∈ D.factor.cells, (D.factor.coarseFibre x).Nonempty) →
        (∀ x ∈ D.factor.cells, IsPlankOfDimensions Cw a b (D.factor.body x)) →
        (q : Set ι).Pairwise (fun i j =>
          _root_.IsEssentiallyDistinct ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            ((T j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        Cw ≤ δ ^ (-η) → Cfib ≤ δ ^ (-η) → CF ≤ δ ^ (-η) →
        (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
        ∃ (O : ShadedBody.ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) ι D.factor.Cell)
          (Cs cref : ℝ≥0),
          D.ConstructedProp51Output hCw O Cs cref ηₒ ∧
          Cs ≤ δ ^ (-e) ∧ (δ : ℝ≥0) ^ e ≤ cref := by
  classical
  have he4 : (0 : ℝ) < ηₒ / 4 := by positivity
  have he2 : (0 : ℝ) < e / 2 := by positivity
  obtain ⟨d1, hd1, hFC⟩ := exists_threshold_rpow_le_fullnessConstant he4
  obtain ⟨d2, hd2, hNb⟩ :=
    exists_threshold_fineVolumeRatio_exponent_succ_le_rpow_neg.{u, v}
      (show (0 : ℝ) < (ηₒ / 4) / 12 by positivity)
  obtain ⟨d3, hd3, hMb⟩ := exists_threshold_card_le_rpow_neg_seven.{u}
  obtain ⟨d4, hd4, hCb⟩ := exists_threshold_rpow_le_inv_remark53ThickConst he4
  obtain ⟨d5, hd5, hEb⟩ :=
    Kakeya.exists_threshold_le_rpow_neg (envelopeWindowPoly plankWindowRadius)
      (one_le_envelopeWindowPoly _) (show (0 : ℝ) < ηₒ / 8 by positivity)
  obtain ⟨d6, hd6, hSb⟩ :=
    exists_threshold_outerScaleSelectionConstant_le_rpow_neg
      (show (0 : ℝ) < ηₒ / 16 by positivity)
  -- the `e`-thresholds
  obtain ⟨d7, hd7, hNb'⟩ :=
    exists_threshold_fineVolumeRatio_exponent_succ_le_rpow_neg.{u, v}
      (show (0 : ℝ) < e / 16 by positivity)
  obtain ⟨d8, hd8, hSb'⟩ := exists_threshold_outerScaleSelectionConstant_le_rpow_neg he2
  obtain ⟨d9, hd9, hPb⟩ := exists_threshold_productConstant_le_rpow_neg he2
  obtain ⟨d10, hd10, hRb⟩ := exists_threshold_rpow_le_refinementConstant he2
  refine ⟨min (min (min d1 d2) (min d3 d4))
      (min (min (min d5 d6) (min d7 d8)) (min (min d9 d10) 1)),
    lt_min (lt_min (lt_min hd1 hd2) (lt_min hd3 hd4))
      (lt_min (lt_min (lt_min hd5 hd6) (lt_min hd7 hd8)) (lt_min (lt_min hd9 hd10) one_pos)),
    ηₒ / 48, by positivity, ?_⟩
  intro a b hab hb1 ι q δ T κ coarseSet ρ R m Cfib CF C₀ D Cw hCw
    hδ0 hδ hδhalf hρ0 hρ1 hδa hb0 hball hmass hsmall hcfne hdimK hEDq hCwδ hCfib hCF hfull
  -- unwind the threshold
  have hδ1 : δ ≤ 1 :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδd1 : δ ≤ d1 :=
    hδ.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hδd2 : δ ≤ d2 :=
    hδ.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hδd3 : δ ≤ d3 :=
    hδ.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hδd4 : δ ≤ d4 :=
    hδ.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _))
  have hδd5 : δ ≤ d5 :=
    hδ.trans ((min_le_right _ _).trans ((min_le_left _ _).trans
      ((min_le_left _ _).trans (min_le_left _ _))))
  have hδd6 : δ ≤ d6 :=
    hδ.trans ((min_le_right _ _).trans ((min_le_left _ _).trans
      ((min_le_left _ _).trans (min_le_right _ _))))
  have hδd7 : δ ≤ d7 :=
    hδ.trans ((min_le_right _ _).trans ((min_le_left _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hδd8 : δ ≤ d8 :=
    hδ.trans ((min_le_right _ _).trans ((min_le_left _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  have hδd9 : δ ≤ d9 :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_left _ _).trans (min_le_left _ _))))
  have hδd10 : δ ≤ d10 :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_left _ _).trans (min_le_right _ _))))
  have ha0 : 0 < a := lt_of_lt_of_le hδ0 hδa
  have ha1 : a ≤ 1 := hab.trans hb1
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hδE0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδEtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hR : (1 : ℝ≥0) ≤ plankWindowRadius := Kakeya.Section6PartBData.one_le_plankWindowRadius
  set Menv : ℝ≥0 :=
    flatPrismEnvelopeVolumeRatio.C (windowPlankEnvelope.windowConst plankWindowRadius Cw)
    with hMenvdef
  have hMenv1 : 1 ≤ Menv := flatPrismEnvelopeVolumeRatio.one_le _
  -- the Proposition-5.1 input and output
  set input := D.section6SelectScaleInput hδ0 hδhalf hδa le_rfl hball hmass with hinput
  have Q : ShadedBody.FactoringAndMultPropCoreSelectScaleResult
      (C := ((Kakeya.Section6PartBData.remark53ThickConst Cfib CF : ℝ≥0) : ENNReal))
      D.toFineProp51Family input.hδ input.hdisc input.volumeRatio input.hδB input.hupper
        input.hmass :=
    D.prop51SelectScaleOfDatum input hδ0 hρ0 hρ1 hsmall hcfne
  have hcore := Q.core
  have href1 := Q.selection_refinement D.toFineProp51Family input.hδ input.hdisc
    input.volumeRatio input.hδB input.hupper input.hmass
  set F' := ShadedBody.selectedOuterScaleFamily D.toFineProp51Family input.hδ input.hdisc
    input.hδB input.hupper input.hmass with hF'
  set Dvr := input.volumeRatio.restrictOuter _
    ((ShadedBody.outerScaleSelection D.toFineProp51Family input.hδ input.hdisc
      input.hδB input.hupper input.hmass).selected_subset.trans
        D.toFineProp51Family.innerSet_image_parent_subset_outerSet) with hDvr
  set w := ShadedBody.selectedOuterScale D.toFineProp51Family input.hδ input.hdisc
    input.hδB input.hupper input.hmass with hwdef
  set O := ShadedBody.outerThickFamilyAtScale F' input.hδ (input.hdisc.restrictOuter _) Dvr w
    Q.scale_pos with hO
  -- the selected outer cells are cells of the datum
  have hsubSelected : F'.outerSet ⊆ D.factor.cells := by
    rw [hF']
    simpa [ShadedBody.selectedOuterScaleFamily,
      ShadedBody.FactorFamily.restrictOuter_outerSet] using
      ((ShadedBody.outerScaleSelection D.toFineProp51Family input.hδ input.hdisc
        input.hδB input.hupper input.hmass).selected_subset.trans
          D.toFineProp51Family.innerSet_image_parent_subset_outerSet)
  have hwin : ∀ j ∈ F'.outerSet,
      ((F'.outerBody j).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ Metric.closedBall 0 ((plankWindowRadius : ℝ≥0) : ℝ) := by
    intro j hj
    exact D.body_carrier_subset_window (hsubSelected hj)
  have hdimSel : ∀ j ∈ F'.outerSet, IsPlankOfDimensions Cw a b (F'.outerBody j) := by
    intro j hj
    exact hdimK j (hsubSelected hj)
  have hpres := isCollarPresentable_outerThickFamilyAtScale F' input.hδ
    (input.hdisc.restrictOuter _) Dvr w Q.scale_pos hcore hwin hdimSel
  have houtsub := hcore.outerSet_subset
  -- the selected family carries positive shading mass, hence a nonempty productive output
  have hselpos : 0 < (ShadedBody.outerScaleSelectionConstant δ a : ENNReal)
      * ∑ i ∈ F'.innerSet, volume (F'.innerBody i).shade :=
    input.hmass.trans_le Q.selection_mass
  have hselmass : 0 < ∑ i ∈ F'.innerSet, volume (F'.innerBody i).shade :=
    pos_of_mul_pos_right hselpos bot_le
  have htsne : O.outerSet.Nonempty := hcore.outerSet_nonempty_of_input_mass_pos hselmass
  -- the outer-scale selection constant
  set selC : ℝ≥0 := ShadedBody.outerScaleSelectionConstant δ a with hselC
  have hsel0 : (selC : ENNReal) ≠ 0 := (pos_of_mul_pos_left hselpos (by positivity)).ne'
  have hsel0' : selC ≠ 0 := by
    intro h
    exact hsel0 (by rw [h]; simp)
  have hseltop : (selC : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- the pipeline constants of the selected family
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  set Mn : ℕ := F'.innerSet.card with hMn
  set Nn : ℕ := Dvr.exponent with hNn
  set prodC : ℝ≥0 := ShadedBody.factoringCoreAtScaleUniformProductConstant
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) Mn Nn w with hprodC
  set Rc : ℝ≥0 := ShadedBody.factoringCoreAtScaleUniformRefinementConstant
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) Mn Nn w with hRcdef
  -- pipeline-envelope inputs
  have hδw : δ ≤ w := ShadedBody.le_selectedOuterScale D.toFineProp51Family input.hδ
    input.hdisc input.hδB input.hupper input.hmass
  have hw1 : w ≤ 1 := by
    refine le_trans ?_ ha1
    exact selectedOuterScale_le D.toFineProp51Family input.hδ input.hdisc input.hδB
      input.hupper input.hmass
  have hMpos : 0 < Mn := by
    rw [hMn, Finset.card_pos]
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at hselmass
    simp at hselmass
  have hqinner : Mn ≤ q.card := by
    have h := selectedOuterScaleFamily_innerSet_card_le D.toFineProp51Family input.hδ
      input.hdisc input.hδB input.hupper input.hmass
    simpa [hF', D.toFineProp51Family_innerSet] using h
  have hMcard : (Mn : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) :=
    hMb q hδ0 hδd3 T hball hEDq Mn hqinner
  have hNbound : ((Nn + 1 : ℕ) : ENNReal) ≤ (δ : ENNReal) ^ (-((ηₒ / 4) / 12)) :=
    hNb D hδ0 hball hδd2
  have hNbound' : ((Nn + 1 : ℕ) : ENNReal) ≤ (δ : ENNReal) ^ (-(e / 16)) :=
    hNb' D hδ0 hball hδd7
  have hRcpos : 0 < ShadedBody.factoringCoreAtScaleUniformRefinementConstant 3 Mn Nn w := by
    have h := ShadedBody.factoringCoreAtScaleUniformRefinementConstant_pos input.hδ
      (input.hdisc.restrictOuter _) Dvr w Q.scale_pos htsne
    rwa [hfr] at h
  -- Cs
  set Cs : ℝ≥0 := max 1 (selC * prodC) with hCs
  -- cref
  set cref : ℝ≥0 := selC⁻¹ * Rc with hcref
  -- the family
  refine ⟨O, Cs, cref, ?_, ?_, ?_⟩
  · refine {
      outerSet_subset := houtsub.trans hsubSelected
      outerSet_nonempty := htsne
      presentable := hpres
      parent_eq := ?_
      inner_carrier := ?_
      mem_innerSet_iff := ?_
      refinement := ?_
      outer_fullness := ?_
      split := ?_ }
    · intro i
      have h := congrFun hcore.parent_eq i
      exact h
    · intro i
      exact hcore.inner_carrier i
    · intro i
      rw [hcore.innerSet_eq]
      simp only [Finset.mem_filter, ShadedBody.selectedOuterScaleFamily,
        ShadedBody.FactorFamily.restrictOuter_innerSet,
        ShadedBody.FactorFamily.restrictOuter_parent,
        D.toFineProp51Family_innerSet, D.toFineProp51Family_parent]
      constructor
      · rintro ⟨⟨hq, -⟩, hout⟩
        exact ⟨hq, hout⟩
      · rintro ⟨hq, hout⟩
        refine ⟨⟨hq, ?_⟩, hout⟩
        have hsub' := houtsub hout
        simpa [hF', ShadedBody.selectedOuterScaleFamily,
          ShadedBody.FactorFamily.restrictOuter_outerSet] using hsub'
    · exact hcore.refinement.trans href1
    · -- the fullness clause, as in `exists_threshold_partB_outer_fullness`
      set lam' : ℝ≥0 := ShadedBody.fullness F'.innerSet F'.innerBody with hlam'
      set cfull : ℝ≥0 := ShadedBody.factoringCoreAtScaleUniformFullnessConstant 3
        Mn Nn w with hcfull
      set Cth : ℝ≥0 := Kakeya.Section6PartBData.remark53ThickConst Cfib CF with hCth
      have hCthne : Cth ≠ 0 := by
        rw [hCth, Kakeya.Section6PartBData.remark53ThickConst]
        have h1 : (0 : ℝ≥0) < Cfib := lt_of_lt_of_le zero_lt_one D.decomp.one_le_Cfib
        have h2 : (0 : ℝ≥0) < CF := lt_of_lt_of_le zero_lt_one D.factor.one_le_CF
        have h3 : (0 : ℝ≥0) < Kakeya.coarseTubeVolumeRatio :=
          lt_of_lt_of_le zero_lt_one Kakeya.one_le_coarseTubeVolumeRatio
        have h4 : (0 : ℝ≥0) < Metric.volume_comparison.C 3 := Metric.volume_comparison.C_pos 3
        exact ne_of_gt (mul_pos (mul_pos (mul_pos (pow_pos h1 2) (pow_pos h3 2)) h2) (pow_pos h4 2))
      have hthick := hcore.thick_fullness
      rw [hfr] at hthick
      have hsum : (((cfull * Cth⁻¹ * lam' ^ 2 : ℝ≥0)) : ENNReal)
          * (∑ x ∈ O.outerSet, volume (O.outerBody x).carrier)
          ≤ ∑ x ∈ O.outerSet, volume (O.outerBody x).shade := by
        refine le_trans (le_of_eq ?_) hthick
        rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_inv hCthne, ENNReal.coe_pow]
      have hbridge := le_fullness_collarPlank_of_sum_le hR hCw hab hb1
        ha0 hb0 htsne F'.outerBody O.outerBody hpres
        (fun x hx => hdimSel x (houtsub hx)) hsum
      refine le_trans ?_ hbridge
      have hη24 : ηₒ / 48 ≤ ηₒ / 24 := by linarith
      have hη32 : ηₒ / 48 ≤ ηₒ / 32 := by linarith
      have hselC0 : ShadedBody.outerScaleSelectionConstant δ a ≠ 0 := hsel0'
      -- B: the Remark-5.3 thick constant
      have hCfibb : Cfib ≤ δ ^ (-((ηₒ / 4) / 6)) := by
        refine hCfib.trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 ?_)
        have : (ηₒ / 4) / 6 = ηₒ / 24 := by ring
        rw [this]
        linarith [hη24]
      have hCFb : CF ≤ δ ^ (-((ηₒ / 4) / 6)) := by
        refine hCF.trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 ?_)
        have : (ηₒ / 4) / 6 = ηₒ / 24 := by ring
        rw [this]
        linarith [hη24]
      have hB : (δ : ENNReal) ^ (ηₒ / 4) ≤ ((Cth⁻¹ : ℝ≥0) : ENNReal) := by
        rw [hCth]
        exact hCb δ Cfib CF hδ0 hδd4 hδ1 D.decomp.one_le_Cfib D.factor.one_le_CF hCfibb hCFb
      -- D: the envelope ratio, polynomial in `Cw`
      have hD : (δ : ENNReal) ^ (ηₒ / 4) ≤ ((Menv⁻¹ : ℝ≥0) : ENNReal) := by
        have hMenv0 : Menv ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hMenv1)
        refine rpow_le_inv_of_le_rpow_neg hMenv0 ?_
        have hpoly : Menv ≤ envelopeWindowPoly plankWindowRadius * Cw ^ 6 :=
          flatPrismEnvelopeVolumeRatio_windowConst_le hCw
        have hE : envelopeWindowPoly plankWindowRadius ≤ δ ^ (-(ηₒ / 8)) := hEb δ hδ0 hδd5
        have hCw6 : Cw ^ 6 ≤ δ ^ (-(ηₒ / 8)) := by
          calc Cw ^ 6 ≤ (δ ^ (-(ηₒ / 48))) ^ 6 := pow_le_pow_left' hCwδ 6
            _ = δ ^ (-(ηₒ / 8)) := by
              rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]; congr 1; push_cast; ring
        have hNN : Menv ≤ δ ^ (-(ηₒ / 4)) := by
          calc Menv ≤ envelopeWindowPoly plankWindowRadius * Cw ^ 6 := hpoly
            _ ≤ δ ^ (-(ηₒ / 8)) * δ ^ (-(ηₒ / 8)) := mul_le_mul' hE hCw6
            _ = δ ^ (-(ηₒ / 4)) := by
              rw [← NNReal.rpow_add hδ0.ne']; congr 1; ring
        calc (Menv : ENNReal) ≤ ((δ ^ (-(ηₒ / 4)) : ℝ≥0) : ENNReal) := by exact_mod_cast hNN
          _ = (δ : ENNReal) ^ (-(ηₒ / 4)) := ENNReal.coe_rpow_of_ne_zero hδ0.ne' _
      -- C: the selected family's fullness, squared
      have hC : (δ : ENNReal) ^ (ηₒ / 4) ≤ ((lam' ^ 2 : ℝ≥0) : ENNReal) := by
        refine rpow_le_sq_of_selection (η := ηₒ / 48) (η' := ηₒ / 16)
          hδ0 hδE1 hselC0 (hSb δ a hδ0 hδa ha1 hδd6) hfull ?_ ?_
        · have hib : D.toFineProp51Family.innerBody = fun i => (T i).toShadedBody := rfl
          have h := Q.selection_fullness D.toFineProp51Family input.hδ input.hdisc
            input.volumeRatio input.hδB input.hupper input.hmass
          simpa [hlam', hF', D.toFineProp51Family_innerSet, hib] using h
        · linarith [hη32]
      -- A: Proposition 5.1's own fullness constant
      have hA : (δ : ENNReal) ^ (ηₒ / 4) ≤ (cfull : ENNReal) := by
        rw [hcfull]
        exact hFC δ w Mn Nn hδ0 hδd1 hδw hw1 hMpos hMcard hNbound hRcpos
      -- collect
      have hall := rpow_le_mul_four (e := ηₒ) hδ0 hA hB hC hD
      refine rpow_le_of_coe_rpow_le hδ0 ?_
      rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_mul]
      exact hall
    · -- the split, as in `exists_collarPresentable_prop51_output`
      intro j hj
      have hstep1 : ((selC : ENNReal))⁻¹ * ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
          ≤ ShadedBody.multiplicity F'.innerSet F'.innerBody := by
        have h := href1.mul_multiplicity_le
        rwa [ENNReal.coe_inv hsel0'] at h
      have hstep2 := hcore.multiplicity_product j hj
      have hcancel : (selC : ENNReal) * ((selC : ENNReal))⁻¹ = 1 :=
        ENNReal.mul_inv_cancel hsel0 hseltop
      calc ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
          = (selC : ENNReal) * (((selC : ENNReal))⁻¹
              * ShadedBody.multiplicity q (fun i => (T i).toShadedBody)) := by
            rw [← mul_assoc, hcancel, one_mul]
        _ ≤ (selC : ENNReal) * ((prodC : ENNReal)
              * ShadedBody.multiplicity O.outerSet O.outerBody
              * ShadedBody.multiplicity (O.fiber j) O.innerBody) := by
            exact mul_le_mul' le_rfl (le_trans hstep1 hstep2)
        _ = ((selC : ENNReal) * (prodC : ENNReal))
              * ShadedBody.multiplicity O.outerSet O.outerBody
              * ShadedBody.multiplicity (O.fiber j) O.innerBody := by ring
        _ ≤ (Cs : ENNReal)
              * ShadedBody.multiplicity O.outerSet O.outerBody
              * ShadedBody.multiplicity (O.fiber j) O.innerBody := by
            gcongr
            rw [← ENNReal.coe_mul]
            exact ENNReal.coe_le_coe.mpr (le_max_right _ _)
  · -- Cs ≤ δ^{-e}
    have hone : (1 : ℝ≥0) ≤ δ ^ (-e) := by
      have := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (show -e ≤ (0 : ℝ) by linarith)
      simpa using this
    have hselE : (selC : ENNReal) ≤ (δ : ENNReal) ^ (-(e / 2)) := hSb' δ a hδ0 hδa ha1 hδd8
    have hprodE : (prodC : ENNReal) ≤ (δ : ENNReal) ^ (-(e / 2)) := by
      have hN8 : ((Nn + 1 : ℕ) : ENNReal) ≤ (δ : ENNReal) ^ (-((e / 2) / 8)) := by
        have : -((e / 2) / 8) = -(e / 16) := by ring
        rw [this]; exact hNbound'
      have h := hPb δ w Mn Nn hδ0 hδd9 hδw hw1 hMpos hMcard hN8
      rw [hprodC, hfr]
      exact h
    have hprodNN : selC * prodC ≤ δ ^ (-e) := by
      have hE : ((selC * prodC : ℝ≥0) : ENNReal) ≤ ((δ ^ (-e) : ℝ≥0) : ENNReal) := by
        rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδ0.ne']
        calc (selC : ENNReal) * (prodC : ENNReal)
            ≤ (δ : ENNReal) ^ (-(e / 2)) * (δ : ENNReal) ^ (-(e / 2)) := mul_le_mul' hselE hprodE
          _ = (δ : ENNReal) ^ (-e) := by
            rw [← ENNReal.rpow_add _ _ hδE0 hδEtop]; congr 1; ring
      exact ENNReal.coe_le_coe.mp hE
    exact max_le hone hprodNN
  · -- δ^e ≤ cref
    have hselE : (selC : ENNReal) ≤ (δ : ENNReal) ^ (-(e / 2)) := hSb' δ a hδ0 hδa ha1 hδd8
    have hinv : (δ : ENNReal) ^ (e / 2) ≤ ((selC⁻¹ : ℝ≥0) : ENNReal) :=
      rpow_le_inv_of_le_rpow_neg hsel0' hselE
    have hRcE : (δ : ENNReal) ^ (e / 2) ≤ (Rc : ENNReal) := by
      have hN4 : ((Nn + 1 : ℕ) : ENNReal) ≤ (δ : ENNReal) ^ (-((e / 2) / 4)) := by
        have h8 : -((e / 2) / 4) = -(e / 8) := by ring
        rw [h8]
        refine hNbound'.trans (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 ?_)
        linarith
      have h := hRb δ w Mn Nn hδ0 hδd10 hδw hw1 hMpos hMcard hN4 hRcpos
      rw [hRcdef, hfr]
      exact h
    refine rpow_le_of_coe_rpow_le hδ0 ?_
    rw [hcref, ENNReal.coe_mul]
    calc (δ : ENNReal) ^ e = (δ : ENNReal) ^ (e / 2) * (δ : ENNReal) ^ (e / 2) := by
          rw [← ENNReal.rpow_add _ _ hδE0 hδEtop]; congr 1; ring
      _ ≤ ((selC⁻¹ : ℝ≥0) : ENNReal) * (Rc : ENNReal) := mul_le_mul' hinv hRcE

end PartBLoss

end Kakeya

end
