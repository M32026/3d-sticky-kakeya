import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7CubicalGlobalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SmallTwistedProjectionVolumeBound

/-!
# Node 7 projection-volume upper bound

The exact affine-image paper shading satisfies the global-AD Fubini bound.
This module leaves its final numerical absorption as one explicit scalar
budget and transfers the resulting union-volume estimate to the synchronized
ordinary retubing.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

namespace PureWZ2Node7AffineDiagonalPreparationData

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}

/-- The globally extended analysis slope is two-Lipschitz on the paper
height interval. -/
theorem analysisSlope_lipschitzOn_two
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    LipschitzOnWith 2 data.analysisSlope (Set.Icc (-1 : ℝ) 1) := by
  have hdifferentiable : Differentiable ℝ data.analysisSlope :=
    data.analysisSlope.contDiff.differentiable (by norm_num)
  apply (convex_Icc (-1 : ℝ) 1).lipschitzOnWith_of_nnnorm_deriv_le
  · intro z _hz
    exact hdifferentiable.differentiableAt
  · intro z hz
    apply NNReal.coe_le_coe.mp
    simpa [Real.norm_eq_abs] using
      (data.analysisSlope_nonsingular z hz).2.1

/-- Since the extended slope vanishes at zero, the derivative bound gives
the fixed value bound used in the paper Fubini estimate. -/
theorem analysisSlope_abs_le_two
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    |data.analysisSlope z| ≤ 2 := by
  have hlip := data.analysisSlope_lipschitzOn_two.dist_le_mul
    z hz 0 (by norm_num)
  rw [data.analysisSlope_zero] at hlip
  have hslope : |data.analysisSlope z| ≤ 2 * |z| := by
    simpa [Real.dist_eq] using hlip
  exact hslope.trans (by
    have hzAbs : |z| ≤ 1 := abs_le.mpr hz
    nlinarith)

/-- The sole scalar receipt needed after applying the exact-slice paper
global-AD volume theorem with slope bound two. -/
def Node7ProjectionScalarBudget
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (C : ENNReal) (outputLoss : ℝ) : Prop :=
  8 *
      (C *
        Kakeya.realRpowENN
          ((2 * (1 + (2 : ℝ))) / data.affineScale.targetDelta)
          (1 - sigma) *
        ENNReal.ofReal (2 * data.affineScale.targetDelta)) ≤
    Kakeya.realRpowENN data.affineScale.targetDelta
      (sigma - outputLoss)

/-- The final ordinary shading is the synchronized cubical saturation, so
the cubical global-AD estimate applies directly. -/
theorem ordinaryShading_projection_upper_of_budget
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (C : ENNReal) (outputLoss : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCtop : C ≠ ⊤)
    (cubicalGlobalAD : ∀ z : ℝ, ∀ _hz : z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (data.analysisSlope z))
          (horizontalSlice data.selected.localizedShading.union z))
        data.affineScale.targetDelta (1 - sigma)
        C)
    (budget : Node7ProjectionScalarBudget data C outputLoss) :
    volume (twistedUnion data.ordinaryShading data.analysisSlope) ≤
      Kakeya.realRpowENN data.affineScale.targetDelta
        (sigma - outputLoss) := by
  unfold twistedUnion
  rw [data.ordinaryShading_union]
  exact pure_wz2_small_twisted_projection_of_global_ad_scalar_budget
      data.selected.localizedShading data.analysisSlope
      data.affineScale.targetDelta_pos data.affineScale.targetDelta_le_one
      hsigma hsigmaOne hCtop data.selected.localized_cubical
      (show (0 : ℝ) ≤ 2 by norm_num)
      (fun _z hz => data.analysisSlope_abs_le_two hz)
      cubicalGlobalAD budget

/-- At the final ordinary radius `12 * targetDelta`, the cubical budget
and one scalar comparison are the complete projection input. -/
def Node7FinalProjectionScalarBudget
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (C : ENNReal) (intermediateLoss outputLoss : ℝ) : Prop :=
  Node7ProjectionScalarBudget data C intermediateLoss ∧
    Kakeya.realRpowENN data.affineScale.targetDelta
        (sigma - intermediateLoss) ≤
      Kakeya.realRpowENN (12 * data.affineScale.targetDelta)
        (sigma - outputLoss)

theorem ordinaryShading_final_projection_upper_of_budget
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (C : ENNReal) (intermediateLoss outputLoss : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCtop : C ≠ ⊤)
    (cubicalGlobalAD : ∀ z : ℝ, ∀ _hz : z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (data.analysisSlope z))
          (horizontalSlice data.selected.localizedShading.union z))
        data.affineScale.targetDelta (1 - sigma)
        C)
    (budget : Node7FinalProjectionScalarBudget data
      C intermediateLoss outputLoss) :
    volume (twistedUnion data.ordinaryShading data.analysisSlope) ≤
      Kakeya.realRpowENN (12 * data.affineScale.targetDelta)
        (sigma - outputLoss) :=
  (data.ordinaryShading_projection_upper_of_budget
    C intermediateLoss hsigma hsigmaOne hCtop cubicalGlobalAD budget.1).trans budget.2

end PureWZ2Node7AffineDiagonalPreparationData

end Kakeya.Assouad

end
