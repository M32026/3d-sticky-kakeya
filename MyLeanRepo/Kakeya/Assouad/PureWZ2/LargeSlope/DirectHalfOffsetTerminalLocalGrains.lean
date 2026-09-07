import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalLargeLocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.SaturationLocalADCore

/-!
# Local grains on the actual direct half-offset terminal

The chart-preserving saturation plane map and the exact local-AD theorem are
assembled here on the same terminal geometry and shading.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

namespace TerminalPlaneData

/-- Lightweight packaging boundary: given exact enlarged-ball AD on the same
terminal geometry, construct local grains using the existing chart-preserving
saturation core. -/
def toLocalGrainDataOfExactAD
    (data : commonSource.TerminalPlaneData)
    {Ctarget : ENNReal}
    (hexactAD : ∀ rho : ℝ, data.geometry.targetDelta ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ data.shading.union},
        PureWZ2PaperADSet1
          (scalarProjection
            (TerminalGeometry.exactPlaneMap commonSource data.geometry
              (data.core.sourcePoint point))
            (data.geometry.exactShading.union ∩
              Metric.closedBall (data.core.sourcePoint point : Point3)
                (Real.sqrt rho + 2 *
                  (data.geometry.targetDelta * Real.sqrt 3))))
          rho (1 - sigma) Ctarget) :
    PureWZ2LocalGrainData data.shading sigma (15 * Ctarget) := by
  let witnessRadius := data.geometry.targetDelta * Real.sqrt 3
  let error := (51 / 100 : ℝ) * witnessRadius
  let pointBound : ℝ := 1 / 25
  have hwitnessRadius : 0 ≤ witnessRadius := by
    dsimp only [witnessRadius]
    positivity [commonSource.halfOffsetLineClassTargetDelta_pos]
  have herror : 0 ≤ error := by
    dsimp only [error]
    positivity
  have hpointBound : 0 ≤ pointBound := by norm_num [pointBound]
  have hexactBound : ∀ source : {point : Point3 // point ∈
      data.geometry.exactShading.union}, ‖(source : Point3)‖ ≤ pointBound := by
    intro source
    exact TerminalGeometry.exact_point_norm_le_one_div_twentyFive
      commonSource data.geometry source
  have hprojectionBudget : witnessRadius + pointBound * error ≤
      2 * data.geometry.targetDelta := by
    have hsqrt : Real.sqrt 3 ≤ 26 / 15 := by
      have hsqrtNonneg := Real.sqrt_nonneg 3
      have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
      nlinarith
    have htargetNonneg := commonSource.halfOffsetLineClassTargetDelta_pos.le
    dsimp only [witnessRadius, error, pointBound]
    nlinarith [mul_le_mul_of_nonneg_left hsqrt htargetNonneg]
  apply data.core.toLocalGrainDataTwo
    hwitnessRadius herror hpointBound hexactBound
  · exact TerminalGeometry.saturationPlaneMap_incidence
      commonSource data.geometry data.core
  · exact hprojectionBudget
  · intro rho hrhoLower hrhoOne point
    exact hexactAD rho hrhoLower hrhoOne point

/-- The same actual terminal output carries public local grains once the
finite-cover constants have been absorbed into `Ctarget`. -/
def toLocalGrainData
    (data : commonSource.TerminalPlaneData)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    {Ctarget : ENNReal}
    (hCtargetOne : 1 ≤ Ctarget) (hCtargetTop : Ctarget ≠ ⊤)
    (hlarge : (338 : ENNReal) ≤ Ctarget)
    (hsmall : ∀ (rho : ℝ) (n : ℕ),
      0 < rho → rho ≤ 1 / 6400 →
      (n : ℝ) ≤ 9 *
        (commonSource.halfOffsetAssembly.horizontalSource.m *
          (commonSource.halfOffsetAssembly.horizontalSource.d -
            commonSource.halfOffsetAssembly.horizontalSource.c) / 2)⁻¹ →
      (n : ENNReal) *
          ((2 * (Nat.ceil ((5 * rho) / rho) + 1) : ENNReal) ^ 3 *
            Kakeya.realRpowENN delta
              (-commonSource.halfOffsetAssembly.technicalLoss)) ≤ Ctarget) :
    PureWZ2LocalGrainData data.shading sigma (15 * Ctarget) := by
  apply toLocalGrainDataOfExactAD commonSource data
  intro rho hrhoLower hrhoOne point
  have hAD := TerminalGeometry.exact_local_ad_all_scales
      commonSource data.geometry hsigma hsigmaOne hCtargetOne hCtargetTop
      hlarge hsmall rho hrhoLower hrhoOne (data.core.sourcePoint point)
  simpa only [TerminalGeometry.exactLocalSet,
    pureWZ2DirectHalfOffsetTerminalLocalADR] using hAD

end TerminalPlaneData

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
