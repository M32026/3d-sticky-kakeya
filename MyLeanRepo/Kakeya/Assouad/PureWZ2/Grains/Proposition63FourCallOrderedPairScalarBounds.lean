import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallReentryReceipts

/-!
# Pre-runtime scalar bounds for one four-call ordered pair

These transparent definitions fix the four scalar choices used by the actual
ordered-pair callback.  They depend only on the root family and numerical
schedule data; in particular, no callback-local shading, re-entry, nested
cover, or pullback object occurs in their types.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- Root-family envelope for the retention entering the first pullback. -/
noncomputable def proposition63FourCallIncomingRetentionUpper
    {rootDelta : ℝ}
    (rootFamily : Kakeya.Streamlined.TubeFamily rootDelta)
    (rho sigma firstOutputLoss : ℝ) : ENNReal :=
  Kakeya.realRpowENN rho (2 - sigma - firstOutputLoss) * rootFamily.enncard

/-- Full pre-runtime envelope for the ancestor retention paid by the second
pullback. -/
noncomputable def proposition63FourCallAncestorRetentionUpper
    {rootDelta : ℝ}
    (rootFamily : Kakeya.Streamlined.TubeFamily rootDelta)
    (rho sigma firstOutputLoss secondNormalizationLoss secondSourceLoss
      rhoWeightLoss firstStageWeightLoss : ℝ) : ENNReal :=
  proposition63FourCallPullbackRetentionFormula
    (wz2PaperPureRefinementFraction rho 61)
    (proposition63UniformReentryRegularizationLoss rootFamily
      (proposition63CanonicalNearbyLevelCount secondNormalizationLoss))
    (proposition63CanonicalReentryWeight rho firstStageWeightLoss)
    (proposition63FourCallReentryRetentionFormula
      (proposition63UniformReentryRegularizationLoss rootFamily
        (proposition63CanonicalNearbyLevelCount (secondSourceLoss / 4)))
      (proposition63CanonicalReentryWeight rho rhoWeightLoss)
      (proposition63FourCallIncomingRetentionUpper rootFamily rho sigma
        firstOutputLoss))

/-- Frozen numerical base contributed by the critical cell-volume floor and
the interval-cover budget. -/
noncomputable def proposition63FourCallFrozenLineCoverBase
    (cellVolumeFloor sqrtScale : ℝ) (coverBudget : ℕ) : ENNReal :=
  ENNReal.ofReal ((cellVolumeFloor / 2) / (4 * (2 * sqrtScale) ^ 2)) *
    (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal)))

/-- Exact spatial variation scale attached to the fixed ambient extension. -/
noncomputable def proposition63FourCallVariationScale
    (sourceCoefficient : NNReal) (spatialScale : ℝ) : ℝ :=
  (((4 : NNReal) *
      (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ) *
    spatialScale

end Kakeya.Assouad.PureWZ2
