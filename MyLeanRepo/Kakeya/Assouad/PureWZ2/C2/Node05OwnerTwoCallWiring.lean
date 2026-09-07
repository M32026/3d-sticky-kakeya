import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05OwnerConcreteCall
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05TwoCallExactMultiplicityWiring

/-!
# Wiring two concrete owner calls through the actual grain refinement

This module provides only a thin constructor for the dependent two-call
Node-5 package.  Both exact post-refinement calls and the intermediate grain
refinement are supplied by the caller; no producer or provenance is inferred.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2Node05TwoCallExactMultiplicityWiring

/--
Package two already constructed owner exact post-refinement calls around the
actual grain refinement of the first call's cropped coarse shading.  The
requested-scale equalities and every seed/log index remain explicit inputs.
-/
noncomputable def ofOwnerExactCalls
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {logExponent : ℕ}
    (coarseLoss coarseSeedLoss : ℝ)
    (coarseSeedNormalizationExponent coarseSeedLogExponent : ℕ)
    (rhoRequested : WZ2PaperRequestedScale delta)
    (rhoRequested_eq : rhoRequested.1 = rho)
    (coarse :
      PureWZ2Node05ExactMultiplicityPostRefinementData
        (sigma := sigma) (seedLoss := coarseSeedLoss)
        (outputLoss := coarseLoss) source.shading rhoRequested
        coarseSeedNormalizationExponent coarseSeedLogExponent logExponent)
    (coarseGrains :
      PureWZ2GrainRefinementData
        coarse.toNode5StickyData.croppedCoarseShading sigma middleLoss)
    (coarse_slope_eq :
      coarseGrains.globalGrains.slope = source.globalGrains.slope)
    (sqrtRequested : WZ2PaperRequestedScale rhoRequested.1)
    (sqrtRequested_eq : sqrtRequested.1 = Real.sqrt rho)
    (fineSeedLoss : ℝ)
    (fineSeedNormalizationExponent fineSeedLogExponent : ℕ)
    (fine :
      PureWZ2Node05ExactMultiplicityPostRefinementData
        (sigma := sigma) (seedLoss := fineSeedLoss)
        (outputLoss := outputLoss) coarseGrains.shading sqrtRequested
        fineSeedNormalizationExponent fineSeedLogExponent logExponent) :
    PureWZ2Node05TwoCallExactMultiplicityWiring
      source rho middleLoss outputLoss logExponent where
  coarseLoss := coarseLoss
  coarseSeedLoss := coarseSeedLoss
  coarseSeedNormalizationExponent := coarseSeedNormalizationExponent
  coarseSeedLogExponent := coarseSeedLogExponent
  rhoRequested := rhoRequested
  rhoRequested_eq := rhoRequested_eq
  coarse := coarse
  coarseGrains := coarseGrains
  coarse_slope_eq := coarse_slope_eq
  sqrtRequested := sqrtRequested
  sqrtRequested_eq := sqrtRequested_eq
  fineSeedLoss := fineSeedLoss
  fineSeedNormalizationExponent := fineSeedNormalizationExponent
  fineSeedLogExponent := fineSeedLogExponent
  fine := fine

end PureWZ2Node05TwoCallExactMultiplicityWiring

end Kakeya.Assouad

end
