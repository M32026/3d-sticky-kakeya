import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ExactMultiplicityPostRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleTwoScaleSticky

/-!
# Exact-multiplicity wiring for the two Node-5 calls

This module only records the dependent provenance needed to feed two exact
post-refinement Node-5 outputs into the existing one-scale/two-scale sticky
interface.  In particular, the second call is made on the actual grain
refinement of the first call's cropped coarse shading.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Two exact-multiplicity Node-5 calls with the grain refinement between them.

The seed losses and seed exponents are retained explicitly because they are
implicit indices of `PureWZ2Node05ExactMultiplicityPostRefinementData`.
-/
structure PureWZ2Node05TwoCallExactMultiplicityWiring
    {sigma inputLoss delta : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (rho middleLoss outputLoss : ℝ)
    (logExponent : ℕ) where
  coarseLoss : ℝ
  coarseSeedLoss : ℝ
  coarseSeedNormalizationExponent : ℕ
  coarseSeedLogExponent : ℕ
  rhoRequested : WZ2PaperRequestedScale delta
  rhoRequested_eq : rhoRequested.1 = rho
  coarse :
    PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := coarseSeedLoss)
      (outputLoss := coarseLoss) source.shading rhoRequested
      coarseSeedNormalizationExponent coarseSeedLogExponent logExponent
  coarseGrains :
    PureWZ2GrainRefinementData
      coarse.toNode5StickyData.croppedCoarseShading sigma middleLoss
  coarse_slope_eq :
    coarseGrains.globalGrains.slope = source.globalGrains.slope
  sqrtRequested : WZ2PaperRequestedScale rhoRequested.1
  sqrtRequested_eq : sqrtRequested.1 = Real.sqrt rho
  fineSeedLoss : ℝ
  fineSeedNormalizationExponent : ℕ
  fineSeedLogExponent : ℕ
  fine :
    PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := fineSeedLoss)
      (outputLoss := outputLoss) coarseGrains.shading sqrtRequested
      fineSeedNormalizationExponent fineSeedLogExponent logExponent

namespace PureWZ2Node05TwoCallExactMultiplicityWiring

variable
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {logExponent : ℕ}

/-- Forget the exact-multiplicity wrappers while preserving both calls and
their shared intermediate grain refinement. -/
noncomputable def toOneScaleTwoScaleStickyData
    (data : PureWZ2Node05TwoCallExactMultiplicityWiring
      source rho middleLoss outputLoss logExponent) :
    PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent where
  coarseLoss := data.coarseLoss
  rhoRequested := data.rhoRequested
  rhoRequested_eq := data.rhoRequested_eq
  coarse := data.coarse.toNode5StickyData
  coarseGrains := data.coarseGrains
  coarse_slope_eq := data.coarse_slope_eq
  sqrtRequested := data.sqrtRequested
  sqrtRequested_eq := data.sqrtRequested_eq
  fine := data.fine.toNode5StickyData

@[simp] theorem toOneScaleTwoScaleStickyData_coarse
    (data : PureWZ2Node05TwoCallExactMultiplicityWiring
      source rho middleLoss outputLoss logExponent) :
    data.toOneScaleTwoScaleStickyData.coarse =
      data.coarse.toNode5StickyData := rfl

@[simp] theorem toOneScaleTwoScaleStickyData_coarseGrains
    (data : PureWZ2Node05TwoCallExactMultiplicityWiring
      source rho middleLoss outputLoss logExponent) :
    data.toOneScaleTwoScaleStickyData.coarseGrains = data.coarseGrains := rfl

@[simp] theorem toOneScaleTwoScaleStickyData_fine
    (data : PureWZ2Node05TwoCallExactMultiplicityWiring
      source rho middleLoss outputLoss logExponent) :
    data.toOneScaleTwoScaleStickyData.fine =
      data.fine.toNode5StickyData := rfl

end PureWZ2Node05TwoCallExactMultiplicityWiring

end Kakeya.Assouad
