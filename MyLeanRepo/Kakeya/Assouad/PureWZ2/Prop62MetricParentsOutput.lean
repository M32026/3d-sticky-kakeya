import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricFiberRescaling

/-!
# Proposition 6.2: metric parents at the prescribed scale

This is the paper-facing output of Lemma `prop62-metric-parents`.  All fields
refer to one final augmented-tree core:

* the Section 6 parent relation is the genuine metric relation;
* each fiber is exactly the corresponding auxiliary node restricted to the
  core;
* the parent family and every public unit-rescaled fiber have nearby-scale
  pure CWA;
* final fiber cardinalities are uniformly comparable;
* the preliminary structural, dyadic, and one-pass tree losses are recorded
  by one explicit mass inequality.

The record deliberately does not assert that a Section 6 metric fiber is an
ordinary Definition 2.12 strict carrier fiber.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62MetricParentsOutput
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (oldData : WZ2PaperPureScaleCoverData fine scale C)
    (sourceWeight : Fin fine.card → ENNReal)
    (logExponent : ℕ) where
  width : ℝ
  M : ℝ
  metric :
    PureWZ2Prop62MetricPacketOutput
      (rho := rho) oldData width M
  coreIndices : Finset (Fin metric.selectedFine.card)
  core_nonempty : coreIndices.Nonempty
  restriction :
    PureWZ2Prop62MetricCoreRestrictionData
      metric.section6Cover coreIndices
  metric_fiber_image_eq :
    ∀ parent,
      Finset.image restriction.fineSelected.embedding
          (wz2PaperFullFiberIndices
            restriction.fineSelected.family
            restriction.coarseSelected.family parent) =
        coreIndices ∩
          wz2PaperFullFiberIndices
            metric.selectedFine metric.metricParents
              (restriction.coarseSelected.embedding parent)
  parentConstant : ENNReal
  sourceFiberConstant : ENNReal
  fiberConstant : ENNReal
  fiberConstant_eq :
    fiberConstant =
      (81000000 : ENNReal) * sourceFiberConstant
  parent_cwa :
    WZ2PaperPureCWAAtNearbyScales
      restriction.coarseSelected.family parentConstant
  parent_schedule :
    PureWZ2Prop62PureSchedule
      restriction.coarseSelected.family
      parentConstant parentConstant
  fiber_rescaling :
    ∀ parent : Fin restriction.coarseSelected.family.card,
      PureWZ2Prop62MetricFiberRescalingInput
        restriction.section6Cover parent sourceFiberConstant
  fiber_public_cwa :
    ∀ parent : Fin restriction.coarseSelected.family.card,
      WZ2PaperPureCWAAtNearbyScales
        (fiber_rescaling parent).certificate.publicFamily
        fiberConstant
  fiberUniformConstant : ENNReal
  full_fiber_uniform :
    ∀ first second,
      ((wz2PaperFullFiberIndices
        restriction.fineSelected.family
        restriction.coarseSelected.family first).card : ENNReal) ≤
        fiberUniformConstant *
          ((wz2PaperFullFiberIndices
            restriction.fineSelected.family
            restriction.coarseSelected.family second).card : ENNReal)
  sourceWeightLevel : ENNReal
  sourceWeightLevel_pos : 0 < sourceWeightLevel
  core_weight_retention :
    wz2PaperPureRefinementFraction delta logExponent *
        (∑ source : Fin fine.card, sourceWeight source) ≤
      ∑ source : Fin restriction.fineSelected.family.card,
        sourceWeight
          (metric.mesh.complete.selectedFine.embedding
            (restriction.fineSelected.embedding source))

end Kakeya.Assouad

end
