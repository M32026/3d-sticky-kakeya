import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalScaleData

/-!
# The margin-preserving affine-diagonal scale for Node 7

This is the parameter choice in `node07.tex`, expressed in the existing
affine-diagonal backend.  The horizontal frame is the genuine slope value at
the selected height.  We choose a slightly smaller diagonal slope scale than
the older tangent construction, leaving a fixed first-derivative margin for
the exact Mobius slope.  The same affine map carries the full fixed
normalization constant, so no second retubing step is introduced.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- The Node-7 normalization scale after rotating the value at the selected
height to zero.  The factor `4 / 5` is the fixed derivative margin and keeps
the transformed active interval inside `[0, 1/2]`. -/
def pureWZ2Node7RotatedSlopeScale
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) : ℝ :=
  (4 / 5 : ℝ) * band.slopeScale /
    (1 + band.lemma31.data.globalSlope subband.left ^ 2)

/-- The affine scale together with the exact choices prescribed by
`node07.tex`. -/
structure PureWZ2Node7AffineDiagonalScaleData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) where
  affineScale : PureWZ2AffineDiagonalScaleData subband
  anchor_left : affineScale.slopeData.anchor = subband.left
  frame_at_left : affineScale.slopeData.frameSlope =
    band.lemma31.data.globalSlope subband.left
  rotated_scale_eq : affineScale.slopeData.rotatedSlopeScale =
    pureWZ2Node7RotatedSlopeScale subband
  normalization_thousand :
    affineScale.slopeData.normalizationConstant = 1000
  height_upper_2500 : affineScale.slopeData.heightScale ≤
    2500 / band.lemma31.data.rho.1
  targetDelta_le_source_power : affineScale.targetDelta ≤
    5000 * Real.rpow delta (1 - epsilon)

/-- Construct the existing affine-diagonal geometry record with the genuine
horizontal rotation and the margin-preserving Node-7 scale. -/
theorem PureWZ2MassPopularSubbandData.toNode7AffineDiagonalScaleData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    Nonempty (PureWZ2Node7AffineDiagonalScaleData subband) := by
  let source := band.lemma31.data.globalSlope
  let anchor := subband.left
  let frameSlope := source anchor
  let rotatedSlopeScale := pureWZ2Node7RotatedSlopeScale subband
  let normalizationConstant : ℝ := 1000
  let heightScale := normalizationConstant / rotatedSlopeScale
  let transverseScale := rotatedSlopeScale ^ 2 / normalizationConstant
  let publicSlope :=
    pureWZ2FixedRotationLinearSlope source anchor band.slopeScale
  let exactSlope :=
    pureWZ2AffineDiagonalExactSlope source frameSlope anchor heightScale
      transverseScale
  have hdelta : 0 < delta := band.lemma31.data.cfg.extremal.delta_pos
  let rho := band.lemma31.data.rho.1
  have hrho : 0 < rho := hdelta.trans_le band.lemma31.data.rho.2.1
  have hframe : |frameSlope| ≤ 1 := by
    dsimp only [frameSlope, source]
    exact (band.lemma31.data.globalSlope_normalized anchor <| by
      exact ⟨band.lemma31.data.scaleData.slabLeft_mem.trans
          (band.left_mem.trans subband.left_mem),
        subband.ordered.le.trans <|
          subband.right_mem.trans <| band.right_mem.trans
          band.lemma31.data.scaleData.slabRight_mem⟩).1
  have hdenomPos : 0 < 1 + frameSlope ^ 2 := by positivity
  have hdenomUpper : 1 + frameSlope ^ 2 ≤ 2 := by
    nlinarith [sq_nonneg (frameSlope - 1), sq_nonneg (frameSlope + 1),
      abs_le.mp hframe]
  have hrotated : 0 < rotatedSlopeScale := by
    dsimp only [rotatedSlopeScale, pureWZ2Node7RotatedSlopeScale]
    exact div_pos (mul_pos (by norm_num) band.slopeScale_pos) hdenomPos
  have hrotatedLower : rho / 3 ≤ rotatedSlopeScale := by
    dsimp only [rotatedSlopeScale, pureWZ2Node7RotatedSlopeScale]
    apply (le_div_iff₀ hdenomPos).2
    have hslope := band.slopeScale_lower
    nlinarith
  have hrotatedUpper : rotatedSlopeScale ≤ 1 := by
    dsimp only [rotatedSlopeScale, pureWZ2Node7RotatedSlopeScale]
    apply (div_le_iff₀ hdenomPos).2
    have hdenomLower : 1 ≤ 1 + frameSlope ^ 2 := by
      nlinarith [sq_nonneg frameSlope]
    nlinarith [band.slopeScale_le_one]
  have hpublic : publicSlope.IsNonsingular := by
    dsimp only [publicSlope, source, anchor]
    exact pureWZ2FixedRotationLinearSlope_nonsingular _
      band.slopeScale_pos
      (band.derivative_band subband.left
        ⟨subband.left_mem, subband.ordered.le.trans subband.right_mem⟩).1
      (band.derivative_tight_upper subband.left
        ⟨subband.left_mem, subband.ordered.le.trans subband.right_mem⟩)
      band.slopeScale_lower
  let slopeData : PureWZ2FixedRotationLinearSlopeData band :=
    { anchor := anchor
      anchor_mem := ⟨subband.left_mem,
        subband.ordered.le.trans subband.right_mem⟩
      frameSlope := frameSlope
      frameSlope_bound := hframe
      rotatedSlopeScale := rotatedSlopeScale
      rotatedSlopeScale_pos := hrotated
      normalizationConstant := normalizationConstant
      normalizationConstant_pos := by norm_num
      heightScale := heightScale
      heightScale_eq := rfl
      transverseScale := transverseScale
      transverseScale_eq := rfl
      publicSlope := publicSlope
      publicSlope_eq := rfl
      publicSlope_nonsingular := hpublic
      publicSlope_zero := by simp [publicSlope]
      exactSlope := exactSlope
      exactSlope_eq := rfl }
  have hheightLower : 100 ≤ heightScale := by
    dsimp only [heightScale]
    exact (le_div_iff₀ hrotated).2 <| by nlinarith
  have hheightUpper : heightScale ≤ 2500 / rho := by
    dsimp only [heightScale]
    apply (div_le_iff₀ hrotated).2
    have hrotatedTwoFifths : 2 * rho / 5 ≤ rotatedSlopeScale := by
      dsimp only [rotatedSlopeScale, pureWZ2Node7RotatedSlopeScale]
      apply (le_div_iff₀ hdenomPos).2
      nlinarith [band.slopeScale_lower]
    have hratio : 1000 ≤ (2500 / rho) * (2 * rho / 5) := by
      field_simp [hrho.ne']
      norm_num
    exact hratio.trans (by gcongr)
  have htransverse : 0 < transverseScale := by
    dsimp only [transverseScale]
    positivity
  have htransverseUpper : transverseScale ≤ 1 / 100 := by
    dsimp only [transverseScale]
    nlinarith [sq_nonneg rotatedSlopeScale]
  let targetDelta := 2 * heightScale * delta
  have htarget : 0 < targetDelta := by
    dsimp only [targetDelta]
    positivity
  have hsourceTarget : delta ≤ targetDelta := by
    dsimp only [targetDelta]
    have hone : 1 ≤ 2 * heightScale := by linarith
    nlinarith
  have htargetUpper : targetDelta ≤ 1 / 10 := by
    calc
      targetDelta = 2 * heightScale * delta := rfl
      _ ≤ 2 * (2500 / rho) * delta := by gcongr
      _ ≤ 5000 * rho := by
        have hdeltaRho := band.lemma31.delta_le_rho_sq
        dsimp only [rho]
        rw [show 2 * (2500 / band.lemma31.data.rho.1) * delta =
            5000 * delta / band.lemma31.data.rho.1 by ring]
        exact (div_le_iff₀ hrho).2 <| by
          nlinarith [sq_nonneg band.lemma31.data.rho.1]
      _ ≤ 1 / 10 := by
        dsimp only [rho]
        linarith [band.lemma31.rho_tiny]
  have htargetSourcePower :
      targetDelta ≤ 5000 * Real.rpow delta (1 - epsilon) := by
    calc
      targetDelta = 2 * heightScale * delta := rfl
      _ ≤ 2 * (2500 / rho) * delta := by gcongr
      _ = 5000 * (delta / rho) := by ring
      _ = 5000 * Real.rpow delta (1 - epsilon) := by
        dsimp only [rho]
        rw [band.lemma31.data.rho_eq_power]
        congr 1
        simpa using (Real.rpow_sub hdelta 1 epsilon).symm
  let affineScale : PureWZ2AffineDiagonalScaleData subband :=
    { slopeData := slopeData
      slope_anchor_mem := ⟨le_rfl, subband.ordered.le⟩
      rho := rho
      rho_eq := rfl
      rho_pos := hrho
      normalization_ge_hundred := by norm_num
      normalization_le_thousand := by norm_num
      rotated_lower := hrotatedLower
      rotated_le_one := hrotatedUpper
      height_lower := hheightLower
      height_upper := hheightUpper.trans (by gcongr; norm_num)
      transverse_pos := htransverse
      transverse_le := htransverseUpper
      targetDelta := targetDelta
      targetDelta_eq := rfl
      targetDelta_pos := htarget
      source_le_target := hsourceTarget
      targetDelta_le_tenth := htargetUpper
      targetDelta_le_one := htargetUpper.trans (by norm_num) }
  exact ⟨{
    affineScale := affineScale
    anchor_left := rfl
    frame_at_left := rfl
    rotated_scale_eq := rfl
    normalization_thousand := rfl
    height_upper_2500 := hheightUpper
    targetDelta_le_source_power := htargetSourcePower
  }⟩

end Kakeya.Assouad

end
