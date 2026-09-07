import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalExactLocalAD

/-!
# Numerical bounds for the direct half-offset terminal local AD argument

The structural local-AD theorem uses a source-cover radius `R`, an occupied
terminal reanchoring radius `R0`, and an error budget `epsilon`.  This file
contains only the scalar estimates needed to instantiate those parameters.
-/

noncomputable section

namespace Kakeya.Assouad

open Real

/-- The source-cover radius used for an occupied exact terminal ball. -/
def pureWZ2DirectHalfOffsetTerminalLocalADR
    (rho targetDelta : ℝ) : ℝ :=
  Real.sqrt rho + 2 * (targetDelta * Real.sqrt 3)

/-- At the terminal small-scale cutoff, the reanchored occupied-source balls
fit into the radius `sqrt (25 rho) = 5 sqrt rho`. -/
theorem pureWZ2DirectHalfOffsetTerminalLocalAD_reanchor_radius_le
    {rho targetDelta : ℝ}
    (hrho : 0 < rho)
    (hrhoTiny : rho ≤ 1 / 6400)
    (htarget : targetDelta ≤ rho) :
    7 * pureWZ2DirectHalfOffsetTerminalLocalADR rho targetDelta / 2 ≤
      Real.sqrt (25 * rho) := by
  have hrhoNonneg : 0 ≤ rho := hrho.le
  have hsqrtRhoNonneg : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
  have hsqrtRhoSq : (Real.sqrt rho) ^ 2 = rho := by
    rw [Real.sq_sqrt hrhoNonneg]
  have hsqrtThreeNonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hsqrtThreeSq : (Real.sqrt 3) ^ 2 = 3 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hsqrtThree : Real.sqrt 3 ≤ 2 := by
    nlinarith
  have hrhoLeSqrt : rho ≤ Real.sqrt rho := by
    nlinarith
  have hsmall : 28 * Real.sqrt rho ≤ 3 := by
    nlinarith
  have hsqrtTwentyFive : Real.sqrt (25 * rho) = 5 * Real.sqrt rho := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 25)]
    norm_num
  rw [hsqrtTwentyFive]
  unfold pureWZ2DirectHalfOffsetTerminalLocalADR
  nlinarith

/-- The product of the source-cover radius with the occupied terminal radius
is at most the local-AD error budget `5 rho`. -/
theorem pureWZ2DirectHalfOffsetTerminalLocalAD_radius_mul_sqrt_le
    {rho targetDelta : ℝ}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (htarget : targetDelta ≤ rho) :
    pureWZ2DirectHalfOffsetTerminalLocalADR rho targetDelta *
        Real.sqrt rho ≤ 5 * rho := by
  have hrhoNonneg : 0 ≤ rho := hrho.le
  have hsqrtRhoNonneg : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
  have hsqrtRhoSq : (Real.sqrt rho) ^ 2 = rho := by
    rw [Real.sq_sqrt hrhoNonneg]
  have hsqrtRhoLeOne : Real.sqrt rho ≤ 1 := by
    nlinarith
  have hsqrtThreeNonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hsqrtThreeSq : (Real.sqrt 3) ^ 2 = 3 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hsqrtThree : Real.sqrt 3 ≤ 2 := by
    nlinarith
  have herror : targetDelta * Real.sqrt 3 * Real.sqrt rho ≤ 2 * rho := by
    by_cases htargetNonneg : 0 ≤ targetDelta
    · have hfirst : targetDelta * Real.sqrt 3 ≤ rho * 2 := by
        calc
          targetDelta * Real.sqrt 3 ≤ rho * Real.sqrt 3 :=
            mul_le_mul_of_nonneg_right htarget hsqrtThreeNonneg
          _ ≤ rho * 2 := mul_le_mul_of_nonneg_left hsqrtThree hrhoNonneg
      calc
        targetDelta * Real.sqrt 3 * Real.sqrt rho ≤
            (rho * 2) * Real.sqrt rho :=
          mul_le_mul_of_nonneg_right hfirst hsqrtRhoNonneg
        _ ≤ rho * 2 := by nlinarith
        _ = 2 * rho := by ring
    · have htargetNonpos : targetDelta ≤ 0 := le_of_not_ge htargetNonneg
      have hprodNonpos : targetDelta * Real.sqrt 3 * Real.sqrt rho ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg htargetNonpos hsqrtThreeNonneg)
          hsqrtRhoNonneg
      linarith
  unfold pureWZ2DirectHalfOffsetTerminalLocalADR
  nlinarith [herror]

/-- The target-side diameter of an occupied piece times the enclosing local
radius fits the centered-normal error budget. -/
theorem pureWZ2DirectHalfOffsetTerminalLocalAD_twice_radius_sq_le
    {rho targetDelta : ℝ}
    (hrho : 0 < rho)
    (hrhoTiny : rho ≤ 1 / 6400)
    (htargetNonneg : 0 ≤ targetDelta)
    (htarget : targetDelta ≤ rho) :
    (2 * pureWZ2DirectHalfOffsetTerminalLocalADR rho targetDelta) *
        pureWZ2DirectHalfOffsetTerminalLocalADR rho targetDelta ≤ 5 * rho := by
  have hrhoNonneg : 0 ≤ rho := hrho.le
  have hsqrtRhoNonneg : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
  have hsqrtRhoSq : (Real.sqrt rho) ^ 2 = rho :=
    Real.sq_sqrt hrhoNonneg
  have hsqrtThreeNonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hsqrtThreeSq : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtThree : Real.sqrt 3 ≤ 2 := by nlinarith
  have hrhoLeSqrtOverEighty : 80 * rho ≤ Real.sqrt rho := by
    nlinarith
  have hR : pureWZ2DirectHalfOffsetTerminalLocalADR rho targetDelta ≤
      (21 / 20 : ℝ) * Real.sqrt rho := by
    unfold pureWZ2DirectHalfOffsetTerminalLocalADR
    have hterm : 2 * (targetDelta * Real.sqrt 3) ≤ 4 * rho := by
      calc
        2 * (targetDelta * Real.sqrt 3) ≤ 2 * (rho * Real.sqrt 3) := by
          gcongr
        _ ≤ 4 * rho := by nlinarith
    nlinarith
  have hRNonneg : 0 ≤
      pureWZ2DirectHalfOffsetTerminalLocalADR rho targetDelta := by
    unfold pureWZ2DirectHalfOffsetTerminalLocalADR
    positivity
  have hrightNonneg : 0 ≤ (21 / 20 : ℝ) * Real.sqrt rho := by positivity
  have hRsq :
      pureWZ2DirectHalfOffsetTerminalLocalADR rho targetDelta ^ 2 ≤
        ((21 / 20 : ℝ) * Real.sqrt rho) ^ 2 :=
    (sq_le_sq₀ hRNonneg hrightNonneg).2 hR
  nlinarith

/-- The signed scalar in the exact projective covariance is tiny.  The total
normal has norm at least one, the projective chart denominator is bounded
away from zero, and the selected source interval is much shorter than the
ambient unit interval. -/
theorem PureWZ2DirectCommonYSourceAssembly.halfOffsetTerminal_projectionScale_abs_le
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)
    (sourcePoint : {point : Point3 // point ∈
      commonSource.halfOffsetAssembly.horizontalSource.sourceShading.union}) :
    let source := commonSource.halfOffsetAssembly.horizontalSource
    |pureWZ2OffsetProjectiveProjectionScale
        (PureWZ2HalfOffsetHorizontalSourceData.offset source)
        (source.m * (source.d - source.c) / 2)
        (2 / (source.d - source.c))
        pureWZ2DirectHalfOffsetTerminalLambda
        (source.sourceLocalGrains.planeMap sourcePoint)| ≤ 1 / 200 := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let normal := source.sourceLocalGrains.planeMap sourcePoint
  let projectiveNormal := pureWZ2OffsetShearProjectiveNormal
    (PureWZ2HalfOffsetHorizontalSourceData.offset source) normal
  let totalNormal := pureWZ2OffsetProjectiveTotalNormal
    (source.m * (source.d - source.c) / 2)
    (2 / (source.d - source.c))
    pureWZ2DirectHalfOffsetTerminalLambda projectiveNormal
  have hlengthPos : 0 < source.d - source.c := sub_pos.mpr source.ordered
  have hlengthUpper : source.d - source.c ≤ 1 / 640000 := by
    rw [source.length_eq, commonSource.halfOffsetAssembly.horizontalSource_scale]
    have hrhoTiny := commonSource.halfOffsetAssembly.rho_tiny
    nlinarith
  have hbNonneg : 0 ≤ source.m * (source.d - source.c) / 2 := by
    exact div_nonneg (mul_nonneg source.slopeScale_pos.le hlengthPos.le)
      (by norm_num)
  have hbUpper : source.m * (source.d - source.c) / 2 ≤ 1 / 10000 := by
    have hproduct := mul_le_mul_of_nonneg_right source.slopeScale_le_one
      hlengthPos.le
    nlinarith
  have hnorm : 1 ≤ ‖totalNormal‖ := by
    exact pureWZ2OffsetProjectiveTotalNormal_norm_lower _ _ _ _
  have hinvNorm : |‖totalNormal‖⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg totalNormal))]
    exact inv_le_one_of_one_le₀ hnorm
  have hchart : (1 / 50 : ℝ) ≤
      |pureWZ2OffsetShearNormal
        (PureWZ2HalfOffsetHorizontalSourceData.offset source) normal 1| :=
    PureWZ2HalfOffsetHorizontalSourceData.offsetShearNormal_coord_one_lower_restrict
      source commonSource.halfOffsetAssembly_compatibility sourcePoint
  have hchartPos : 0 <
      |pureWZ2OffsetShearNormal
        (PureWZ2HalfOffsetHorizontalSourceData.offset source) normal 1| := by
    linarith [hchart]
  have hdiv :
      |(source.m * (source.d - source.c) / 2) /
        pureWZ2OffsetShearNormal
          (PureWZ2HalfOffsetHorizontalSourceData.offset source) normal 1| ≤
        1 / 200 := by
    rw [abs_div, abs_of_nonneg hbNonneg]
    apply (div_le_iff₀ hchartPos).2
    nlinarith
  change |‖totalNormal‖⁻¹ *
    ((source.m * (source.d - source.c) / 2) /
      pureWZ2OffsetShearNormal
        (PureWZ2HalfOffsetHorizontalSourceData.offset source) normal 1)| ≤
      1 / 200
  rw [abs_mul]
  calc
    |‖totalNormal‖⁻¹| *
        |(source.m * (source.d - source.c) / 2) /
          pureWZ2OffsetShearNormal
            (PureWZ2HalfOffsetHorizontalSourceData.offset source) normal 1| ≤
        1 * (1 / 200 : ℝ) := by gcongr
    _ = 1 / 200 := by norm_num

/-- Consequently the source local-AD scale `25 * rho` transports below the
target base scale `rho`. -/
theorem PureWZ2DirectCommonYSourceAssembly.halfOffsetTerminal_projectionScale_mul_twentyFive_le
    {logExponent : ℕ}
    {sigma epsilon delta rho : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)
    (sourcePoint : {point : Point3 // point ∈
      commonSource.halfOffsetAssembly.horizontalSource.sourceShading.union})
    (hrho : 0 ≤ rho) :
    let source := commonSource.halfOffsetAssembly.horizontalSource
    |pureWZ2OffsetProjectiveProjectionScale
        (PureWZ2HalfOffsetHorizontalSourceData.offset source)
        (source.m * (source.d - source.c) / 2)
        (2 / (source.d - source.c))
        pureWZ2DirectHalfOffsetTerminalLambda
        (source.sourceLocalGrains.planeMap sourcePoint)| * (25 * rho) ≤ rho := by
  have hscale := commonSource.halfOffsetTerminal_projectionScale_abs_le
    sourcePoint
  calc
    _ = (25 * |pureWZ2OffsetProjectiveProjectionScale
        (PureWZ2HalfOffsetHorizontalSourceData.offset
          commonSource.halfOffsetAssembly.horizontalSource)
        (commonSource.halfOffsetAssembly.horizontalSource.m *
          (commonSource.halfOffsetAssembly.horizontalSource.d -
            commonSource.halfOffsetAssembly.horizontalSource.c) / 2)
        (2 / (commonSource.halfOffsetAssembly.horizontalSource.d -
          commonSource.halfOffsetAssembly.horizontalSource.c))
        pureWZ2DirectHalfOffsetTerminalLambda
        (commonSource.halfOffsetAssembly.horizontalSource.sourceLocalGrains
          |>.planeMap sourcePoint)|) * rho := by ring
    _ ≤ (25 * (1 / 200 : ℝ)) * rho := by gcongr
    _ ≤ rho := by nlinarith

end Kakeya.Assouad
