import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScalePreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.StickyRefinementData
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26DeltaBudget

/-!
# Nested prop-sticky schedule for the Pure WZ2 one-scale argument

The two applications of `prop: sticky` cannot be assembled after their
losses have been chosen independently.  The outer application first chooses
the loss of the actual coarse extremizer.  The inner application then chooses
the admissible loss of the original source.  This file records that quantifier
order together with the exact same-configuration provenance.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Two nested, provenance-preserving applications of `prop: sticky`.

The first output is a cover of the given pure grain source at scale `rho`.
The second output is a cover at scale `sqrt rho` of the *actual cropped coarse
extremizer selected by the first output*.
-/
structure PureWZ2OneScaleTwoScaleStickyData
    {sigma inputLoss delta : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (rho middleLoss outputLoss : ℝ)
    (logExponent : ℕ) where
  coarseLoss : ℝ
  rhoRequested : WZ2PaperRequestedScale delta
  rhoRequested_eq : rhoRequested.1 = rho
  coarse :
    PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested logExponent
  coarseGrains :
    PureWZ2GrainRefinementData
      coarse.croppedCoarseShading sigma middleLoss
  coarse_slope_eq :
    coarseGrains.globalGrains.slope = source.globalGrains.slope
  sqrtRequested : WZ2PaperRequestedScale rhoRequested.1
  sqrtRequested_eq : sqrtRequested.1 = Real.sqrt rho
  fine :
    PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := outputLoss)
      coarseGrains.shading sqrtRequested logExponent

namespace PureWZ2OneScaleTwoScaleStickyData

/-- The intermediate grain call retains the literal Proposition 6.3 slope,
so its chart bound is inherited from the exact quantitative source. -/
theorem coarseGrains_slope_bound
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent)
    (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    |data.coarseGrains.globalGrains.slope z| ≤ 3 := by
  rw [data.coarse_slope_eq]
  exact source.globalGrains.slope_bound z hz

end PureWZ2OneScaleTwoScaleStickyData

end Kakeya.Assouad
