import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FixedRotationLinearSlope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.MassPopularSubband

/-!
# Numerical scale certificate for the affine diagonal target
-/

noncomputable section

namespace Kakeya.Assouad

open Set

structure PureWZ2AffineDiagonalScaleData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) where
  slopeData : PureWZ2FixedRotationLinearSlopeData band
  slope_anchor_mem : slopeData.anchor ∈ Set.Icc subband.left subband.right
  rho : ℝ
  rho_eq : rho = band.lemma31.data.rho.1
  rho_pos : 0 < rho
  normalization_ge_hundred : 100 ≤ slopeData.normalizationConstant
  normalization_le_thousand : slopeData.normalizationConstant ≤ 1000
  /-- The lower bound needed by the geometric backend.  The factor `1 / 3`
  leaves room for the Node-7 derivative-margin choice after the genuine
  horizontal rotation. -/
  rotated_lower : rho / 3 ≤ slopeData.rotatedSlopeScale
  rotated_le_one : slopeData.rotatedSlopeScale ≤ 1
  height_lower : 100 ≤ slopeData.heightScale
  height_upper : slopeData.heightScale ≤ 3000 / rho
  transverse_pos : 0 < slopeData.transverseScale
  transverse_le : slopeData.transverseScale ≤ 1 / 100
  targetDelta : ℝ
  targetDelta_eq : targetDelta = 2 * slopeData.heightScale * delta
  targetDelta_pos : 0 < targetDelta
  source_le_target : delta ≤ targetDelta
  targetDelta_le_tenth : targetDelta ≤ 1 / 10
  targetDelta_le_one : targetDelta ≤ 1

theorem PureWZ2MassPopularSubbandData.toAffineDiagonalScaleData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    Nonempty (PureWZ2AffineDiagonalScaleData subband) := by
  rcases band.toFixedRotationLinearSlopeAt
      subband.anchor subband.anchor_mem with
    ⟨slopeData, hslopeAnchor, _hframeSlope, hrotatedSlopeScale,
      hnormalization⟩
  let rho := band.lemma31.data.rho.1
  have hdelta : 0 < delta := band.lemma31.data.cfg.extremal.delta_pos
  have hrho : 0 < rho := hdelta.trans_le band.lemma31.data.rho.2.1
  have hframe : |slopeData.frameSlope| ≤ 1 := by
    exact slopeData.frameSlope_bound
  have hdenomLower : 1 ≤ 1 + slopeData.frameSlope ^ 2 := by
    nlinarith [sq_nonneg slopeData.frameSlope]
  have hdenomUpper : 1 + slopeData.frameSlope ^ 2 ≤ 2 := by
    nlinarith [sq_nonneg (slopeData.frameSlope - 1),
      sq_nonneg (slopeData.frameSlope + 1), abs_le.mp hframe]
  have hrotatedLower : rho / 3 ≤ slopeData.rotatedSlopeScale := by
    rw [hrotatedSlopeScale]
    have hslope := band.slopeScale_lower
    apply (le_div_iff₀ (by positivity : 0 < 1 + slopeData.frameSlope ^ 2)).2
    dsimp only [rho]
    nlinarith
  have hrotatedUpper : slopeData.rotatedSlopeScale ≤ 1 := by
    rw [hrotatedSlopeScale]
    exact (div_le_iff₀ (by positivity : 0 < 1 + slopeData.frameSlope ^ 2)).2 <|
      by nlinarith [band.slopeScale_le_one]
  have hheightLower : 100 ≤ slopeData.heightScale := by
    rw [slopeData.heightScale_eq, hnormalization]
    exact (le_div_iff₀ slopeData.rotatedSlopeScale_pos).2 <| by
      nlinarith [slopeData.normalizationConstant_pos]
  have hheightUpper : slopeData.heightScale ≤ 3000 / rho := by
    rw [slopeData.heightScale_eq, hnormalization]
    apply (div_le_iff₀ slopeData.rotatedSlopeScale_pos).2
    have hratio : 1000 ≤ (3000 / rho) * (rho / 3) := by
      field_simp [hrho.ne'] <;> norm_num
    exact (show (100 : ℝ) ≤ 1000 by norm_num) |>.trans
      (hratio.trans (by gcongr))
  have htransverse : 0 < slopeData.transverseScale := by
    rw [slopeData.transverseScale_eq, hnormalization]
    exact div_pos (sq_pos_of_pos slopeData.rotatedSlopeScale_pos) (by norm_num)
  have htransverseUpper : slopeData.transverseScale ≤ 1 / 100 := by
    rw [slopeData.transverseScale_eq, hnormalization]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 100)).2
    nlinarith [sq_nonneg slopeData.rotatedSlopeScale, hrotatedUpper]
  let targetDelta := 2 * slopeData.heightScale * delta
  have htarget : 0 < targetDelta := by
    dsimp only [targetDelta]
    positivity
  have hsourceTarget : delta ≤ targetDelta := by
    dsimp only [targetDelta]
    have : 1 ≤ 2 * slopeData.heightScale := by linarith
    nlinarith
  have htargetUpper : targetDelta ≤ 1 / 10 := by
    calc
      targetDelta = 2 * slopeData.heightScale * delta := rfl
      _ ≤ 2 * (3000 / rho) * delta := by gcongr
      _ ≤ 6000 * rho := by
        have hdeltaRho := band.lemma31.delta_le_rho_sq
        dsimp only [rho]
        rw [show 2 * (3000 / band.lemma31.data.rho.1) * delta =
            6000 * delta / band.lemma31.data.rho.1 by ring]
        exact (div_le_iff₀ hrho).2 <| by
          nlinarith [sq_nonneg band.lemma31.data.rho.1]
      _ ≤ 1 / 10 := by
        dsimp only [rho]
        linarith [band.lemma31.rho_tiny]
  exact ⟨{
    slopeData := slopeData
    slope_anchor_mem := by
      rw [hslopeAnchor, subband.anchor_eq]
      constructor <;> linarith [subband.ordered]
    rho := rho
    rho_eq := rfl
    rho_pos := hrho
    normalization_ge_hundred := by rw [hnormalization]
    normalization_le_thousand := by rw [hnormalization]; norm_num
    rotated_lower := hrotatedLower
    rotated_le_one := hrotatedUpper
    height_lower := hheightLower
    height_upper := hheightUpper
    transverse_pos := htransverse
    transverse_le := htransverseUpper
    targetDelta := targetDelta
    targetDelta_eq := rfl
    targetDelta_pos := htarget
    source_le_target := hsourceTarget
    targetDelta_le_tenth := htargetUpper
    targetDelta_le_one := htargetUpper.trans (by norm_num)
  }⟩

end Kakeya.Assouad

end
