import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallNestedPointCover

/-!
# Scalar receipt for the concrete four-call pullback

The pullback produced by `proposition63_four_call_pullback_of_runtime_witnesses`
uses two copies of the same refinement fraction.  Between them, the current
re-entry contributes its regularization loss and normalization weight.  This
module records that construction-specific scalar formula without adding a
field to either the generic pullback data or the four-call runtime.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- Closed scalar formula for the retention factor built by the concrete
four-call pullback producer. -/
noncomputable def proposition63FourCallPullbackRetentionFormula
    (fraction regularizationLoss normalizationWeight
      ancestorRetentionFactor : ENNReal) : ENNReal :=
  (fraction *
    ((regularizationLoss⁻¹ * ((73 / 100 : ENNReal) * normalizationWeight)) *
      (fraction * ancestorRetentionFactor⁻¹)))⁻¹

/-- The retention factor of the concrete current-shading re-entry is
definitionally the inverse of its trace coefficient times the incoming
retention coefficient.  This theorem lets the four-call producer expose its
local `p2` scalar without exposing `p2` itself. -/
theorem proposition63_dependent_coarse_reentry_retentionFactor_eq
    {delta sigma outerLoss coarseInputLoss coarseNormalizationLoss
      reentryLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {outerLogExponent normalizationExponent : ℕ}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent)
    {coarseSource :
      PureWZ2ExtremalConfiguration sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      normalizationExponent)
    (current : WZ1PaperTubeShading coarseNormalized.croppedFamily)
    (currentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) coarseNormalized current)
    (ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      coarseNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index))
    (current_sub_outer : ∀ index, current.carrier index ⊆
      outer.croppedCoarseShading.carrier (ancestorEmbedding index))
    (ancestorRetentionFactor : ENNReal)
    (ancestorRetentionFactor_pos : 0 < ancestorRetentionFactor)
    (ancestorRetentionFactor_ne_top : ancestorRetentionFactor ≠ ⊤)
    (current_retained_mass :
      ancestorRetentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
        current.mass) :
    (proposition63DependentCoarseReentryOfCurrent outer coarseNormalized
      current currentReentry ancestorEmbedding ancestor_tube_eq
      current_sub_outer ancestorRetentionFactor ancestorRetentionFactor_pos
      ancestorRetentionFactor_ne_top current_retained_mass).retentionFactor =
      ((currentReentry.regularized.regularizationLoss⁻¹ *
          ((73 / 100 : ENNReal) * currentReentry.normalizationWeight)) *
        ancestorRetentionFactor⁻¹)⁻¹ := by
  rfl

/-- A light companion receipt for a construction-specific pullback factor.
It contains only the equality which is lost when the producer is exposed as
an abstract `Proposition63FourCallPullbackData`. -/
structure Proposition63FourCallPullbackRetentionReceipt
    (actual fraction regularizationLoss normalizationWeight
      ancestorRetentionFactor : ENNReal) : Prop where
  retentionFactor_eq : actual =
    proposition63FourCallPullbackRetentionFormula fraction regularizationLoss
      normalizationWeight ancestorRetentionFactor

/-- Expand the two local intermediate factors used by the concrete producer.
This is suitable for use immediately before its final structure literal. -/
theorem proposition63_four_call_pullback_retention_formula_of_intermediates
    {actual fraction regularizationLoss normalizationWeight
      ancestorRetentionFactor call2Factor traceCoefficient p2Factor : ENNReal}
    (hcall2 : call2Factor = (fraction * ancestorRetentionFactor⁻¹)⁻¹)
    (htrace : traceCoefficient =
      regularizationLoss⁻¹ * ((73 / 100 : ENNReal) * normalizationWeight))
    (hp2 : p2Factor = (traceCoefficient * call2Factor⁻¹)⁻¹)
    (hactual : actual = (fraction * p2Factor⁻¹)⁻¹) :
    actual = proposition63FourCallPullbackRetentionFormula fraction
      regularizationLoss normalizationWeight ancestorRetentionFactor := by
  rw [hactual, hp2, inv_inv, htrace, hcall2, inv_inv]
  rfl

/-- Short form used after rewriting the locally constructed `p2` with
`proposition63_dependent_coarse_reentry_retentionFactor_eq`. -/
theorem proposition63_four_call_pullback_retention_formula_of_reentry_factor
    {actual fraction regularizationLoss normalizationWeight
      ancestorRetentionFactor p2Factor : ENNReal}
    (hp2 : p2Factor =
      ((regularizationLoss⁻¹ *
          ((73 / 100 : ENNReal) * normalizationWeight)) *
        (fraction * ancestorRetentionFactor⁻¹))⁻¹)
    (hactual : actual = (fraction * p2Factor⁻¹)⁻¹) :
    actual = proposition63FourCallPullbackRetentionFormula fraction
      regularizationLoss normalizationWeight ancestorRetentionFactor := by
  rw [hactual, hp2, inv_inv]
  rfl

/-- Package the local construction equalities as the lightweight scalar
receipt. -/
theorem proposition63_four_call_pullback_retention_receipt_of_intermediates
    {actual fraction regularizationLoss normalizationWeight
      ancestorRetentionFactor call2Factor traceCoefficient p2Factor : ENNReal}
    (hcall2 : call2Factor = (fraction * ancestorRetentionFactor⁻¹)⁻¹)
    (htrace : traceCoefficient =
      regularizationLoss⁻¹ * ((73 / 100 : ENNReal) * normalizationWeight))
    (hp2 : p2Factor = (traceCoefficient * call2Factor⁻¹)⁻¹)
    (hactual : actual = (fraction * p2Factor⁻¹)⁻¹) :
    Proposition63FourCallPullbackRetentionReceipt actual fraction
      regularizationLoss normalizationWeight ancestorRetentionFactor :=
  ⟨proposition63_four_call_pullback_retention_formula_of_intermediates
    hcall2 htrace hp2 hactual⟩

/-- The closed formula is increasing in the regularization loss and ancestor
retention cost, and decreasing in each refinement fraction and in the
normalization weight.  Thus lower bounds for the latter two and upper bounds
for the former two give a pre-runtime upper bound. -/
theorem proposition63_four_call_pullback_retention_formula_le
    {fractionLower fraction regularizationLoss regularizationUpper
      weightLower normalizationWeight ancestorRetentionFactor
      ancestorRetentionUpper : ENNReal}
    (hfraction : fractionLower ≤ fraction)
    (hregularization : regularizationLoss ≤ regularizationUpper)
    (hweight : weightLower ≤ normalizationWeight)
    (hancestor : ancestorRetentionFactor ≤ ancestorRetentionUpper) :
    proposition63FourCallPullbackRetentionFormula fraction regularizationLoss
        normalizationWeight ancestorRetentionFactor ≤
      proposition63FourCallPullbackRetentionFormula fractionLower
        regularizationUpper weightLower ancestorRetentionUpper := by
  unfold proposition63FourCallPullbackRetentionFormula
  apply ENNReal.inv_le_inv.mpr
  gcongr

/-- Minimal upper-bound interface for the closed formula.  Instead of four
separate monotonicity hypotheses, a caller may discharge the single lower
bound on the concrete retained coefficient which its scalar budget actually
provides. -/
theorem proposition63_four_call_pullback_retention_formula_le_upper
    {fraction regularizationLoss normalizationWeight ancestorRetentionFactor
      ancestorRetentionUpper : ENNReal}
    (hcoefficient : ancestorRetentionUpper⁻¹ ≤
      fraction *
        ((regularizationLoss⁻¹ *
            ((73 / 100 : ENNReal) * normalizationWeight)) *
          (fraction * ancestorRetentionFactor⁻¹))) :
    proposition63FourCallPullbackRetentionFormula fraction regularizationLoss
      normalizationWeight ancestorRetentionFactor ≤ ancestorRetentionUpper := by
  unfold proposition63FourCallPullbackRetentionFormula
  simpa only [inv_inv] using ENNReal.inv_le_inv.mpr hcoefficient

/-- Producer-facing scalar bridge.  The producer only needs to return the
equality for its freshly constructed pullback; the unique caller can consume
that equality immediately with one pre-runtime coefficient budget. -/
theorem proposition63_four_call_pullback_retention_le_upper_of_formula_eq
    {actual fraction regularizationLoss normalizationWeight
      ancestorRetentionFactor ancestorRetentionUpper : ENNReal}
    (hactual : actual =
      proposition63FourCallPullbackRetentionFormula fraction regularizationLoss
        normalizationWeight ancestorRetentionFactor)
    (hcoefficient : ancestorRetentionUpper⁻¹ ≤
      fraction *
        ((regularizationLoss⁻¹ *
            ((73 / 100 : ENNReal) * normalizationWeight)) *
          (fraction * ancestorRetentionFactor⁻¹))) :
    actual ≤ ancestorRetentionUpper := by
  rw [hactual]
  exact proposition63_four_call_pullback_retention_formula_le_upper hcoefficient

/-- Consume a construction receipt and pre-runtime scalar bounds. -/
theorem Proposition63FourCallPullbackRetentionReceipt.le_formula
    {actual fraction regularizationLoss normalizationWeight
      ancestorRetentionFactor fractionLower regularizationUpper weightLower
      ancestorRetentionUpper : ENNReal}
    (receipt : Proposition63FourCallPullbackRetentionReceipt actual fraction
      regularizationLoss normalizationWeight ancestorRetentionFactor)
    (hfraction : fractionLower ≤ fraction)
    (hregularization : regularizationLoss ≤ regularizationUpper)
    (hweight : weightLower ≤ normalizationWeight)
    (hancestor : ancestorRetentionFactor ≤ ancestorRetentionUpper) :
    actual ≤ proposition63FourCallPullbackRetentionFormula fractionLower
      regularizationUpper weightLower ancestorRetentionUpper := by
  rw [receipt.retentionFactor_eq]
  exact proposition63_four_call_pullback_retention_formula_le hfraction
    hregularization hweight hancestor

/-- Final bridge to an externally fixed ancestor-retention budget. -/
theorem Proposition63FourCallPullbackRetentionReceipt.le_upper
    {actual fraction regularizationLoss normalizationWeight
      ancestorRetentionFactor fractionLower regularizationUpper weightLower
      ancestorUpper ancestorRetentionUpper : ENNReal}
    (receipt : Proposition63FourCallPullbackRetentionReceipt actual fraction
      regularizationLoss normalizationWeight ancestorRetentionFactor)
    (hfraction : fractionLower ≤ fraction)
    (hregularization : regularizationLoss ≤ regularizationUpper)
    (hweight : weightLower ≤ normalizationWeight)
    (hancestor : ancestorRetentionFactor ≤ ancestorUpper)
    (hformula : proposition63FourCallPullbackRetentionFormula fractionLower
      regularizationUpper weightLower ancestorUpper ≤ ancestorRetentionUpper) :
    actual ≤ ancestorRetentionUpper :=
  (receipt.le_formula hfraction hregularization hweight hancestor).trans hformula

end Kakeya.Assouad.PureWZ2
