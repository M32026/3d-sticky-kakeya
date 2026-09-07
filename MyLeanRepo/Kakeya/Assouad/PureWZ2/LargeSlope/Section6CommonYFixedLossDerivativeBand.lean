import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6CommonYDerivativeBand

/-!
# Fixed-loss common-y derivative band for the Node-6 terminal schedule

The historical common-y wrapper pays the fixed factor `1 / 4` with one full
copy of the Section-6 scale exponent.  That is harmless for its original
callers but too expensive after conversion to the final radius.  This module
keeps the same geometric common-y data and charges that fixed factor to an
independently preselected positive loss.
-/

noncomputable section
namespace Kakeya.Assouad

open Set

/-- Run the derivative selection on the common-y shading while charging its
fixed quarter loss to `fixedLoss`. -/
theorem PureWZ2Lemma31DerivativeAssembly.toLemma32DerivativeBandAfterCommonYWithFixedLoss
    {sigma epsilon delta fixedLoss : ℝ}
    (data : PureWZ2Lemma31DerivativeAssembly sigma epsilon delta)
    (popular : PureWZ2WeightedPopularGlobalGrainData data.data.cfg data.data.rho
      data.data.scaleData)
    (frameSlope : ℝ)
    (common : PureWZ2RotatedWeightedCommonYCore data.data.cfg data.data.rho
      data.data.scaleData popular frameSlope)
    (hquarter : Kakeya.realRpowENN delta fixedLoss ≤ (1 / 4 : ENNReal)) :
    ∃ band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta,
      band.lemma31 = data ∧ band.sourceShading.union = common.F2.union ∧
        band.massLoss =
          data.data.targetLoss + 4 * common.badYLoss + fixedLoss := by
  let massLoss := data.data.targetLoss + 4 * common.badYLoss + fixedLoss
  have hretained :
      (1 / 4 : ENNReal) *
          Kakeya.realRpowENN delta (4 * common.badYLoss) *
          (ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta (data.data.targetLoss + 2) *
            data.data.cfg.family.enncard *
            ENNReal.ofReal data.data.rho.1) ≤
        common.F2.mass := by
    calc
      (1 / 4 : ENNReal) *
            Kakeya.realRpowENN delta (4 * common.badYLoss) *
            (ENNReal.ofReal (Real.pi / 4) *
              Kakeya.realRpowENN delta (data.data.targetLoss + 2) *
              data.data.cfg.family.enncard *
              ENNReal.ofReal data.data.rho.1) ≤
          (1 / 4 : ENNReal) *
            Kakeya.realRpowENN delta (4 * common.badYLoss) *
            data.data.scaleData.slabShading.mass := by
              gcongr
              exact data.data.scaleData.slab_mass
      _ ≤ common.F2.mass := common.F2_mass_retention
  have hpowerCard :
      Kakeya.realRpowENN delta (massLoss + 2) ≤
        (1 / 4 : ENNReal) *
          Kakeya.realRpowENN delta (4 * common.badYLoss) *
          Kakeya.realRpowENN delta (data.data.targetLoss + 2) := by
    calc
      Kakeya.realRpowENN delta (massLoss + 2) =
          Kakeya.realRpowENN delta fixedLoss *
            (Kakeya.realRpowENN delta (4 * common.badYLoss) *
              Kakeya.realRpowENN delta (data.data.targetLoss + 2)) := by
        rw [← realRpowENN_add data.data.cfg.extremal.delta_pos,
          ← realRpowENN_add data.data.cfg.extremal.delta_pos]
        congr 1
        dsimp only [massLoss]
        ring
      _ ≤ (1 / 4 : ENNReal) *
          (Kakeya.realRpowENN delta (4 * common.badYLoss) *
            Kakeya.realRpowENN delta (data.data.targetLoss + 2)) := by
        gcongr
      _ = (1 / 4 : ENNReal) *
          Kakeya.realRpowENN delta (4 * common.badYLoss) *
          Kakeya.realRpowENN delta (data.data.targetLoss + 2) := by ring
  have hmassCard :
      ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta (massLoss + 2) *
          data.data.cfg.family.enncard * ENNReal.ofReal data.data.rho.1 ≤
        common.F2.mass := by
    calc
      ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta (massLoss + 2) *
            data.data.cfg.family.enncard * ENNReal.ofReal data.data.rho.1 ≤
          ENNReal.ofReal (Real.pi / 4) *
            ((1 / 4 : ENNReal) *
              Kakeya.realRpowENN delta (4 * common.badYLoss) *
              Kakeya.realRpowENN delta (data.data.targetLoss + 2)) *
            data.data.cfg.family.enncard * ENNReal.ofReal data.data.rho.1 := by
              gcongr
      _ = (1 / 4 : ENNReal) *
          Kakeya.realRpowENN delta (4 * common.badYLoss) *
          (ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta (data.data.targetLoss + 2) *
            data.data.cfg.family.enncard *
            ENNReal.ofReal data.data.rho.1) := by ring
      _ ≤ common.F2.mass := hretained
  have hfamilyOne : (1 : ENNReal) ≤ data.data.cfg.family.enncard := by
    change (1 : ENNReal) ≤ (data.data.cfg.family.card : ENNReal)
    exact_mod_cast data.data.cfg.extremal.nonempty
  have hdeltaPi : Kakeya.realRpowENN delta 1 ≤
      ENNReal.ofReal (Real.pi / 4) := by
    have hreal : delta ≤ Real.pi / 4 :=
      data.delta_small.trans (by linarith [Real.pi_gt_three])
    calc
      Kakeya.realRpowENN delta 1 = ENNReal.ofReal delta := by
        simp [Kakeya.realRpowENN]
      _ ≤ ENNReal.ofReal (Real.pi / 4) := ENNReal.ofReal_mono hreal
  have hcoefficient : Kakeya.realRpowENN delta 1 ≤
      ENNReal.ofReal (Real.pi / 4) * data.data.cfg.family.enncard := by
    calc
      Kakeya.realRpowENN delta 1 ≤
          ENNReal.ofReal (Real.pi / 4) := hdeltaPi
      _ = ENNReal.ofReal (Real.pi / 4) * 1 := by simp
      _ ≤ ENNReal.ofReal (Real.pi / 4) *
          data.data.cfg.family.enncard := by gcongr
  have hmass :
      Kakeya.realRpowENN delta (massLoss + 3) *
          ENNReal.ofReal data.data.rho.1 ≤ common.F2.mass := by
    calc
      Kakeya.realRpowENN delta (massLoss + 3) *
            ENNReal.ofReal data.data.rho.1 =
          Kakeya.realRpowENN delta (massLoss + 2) *
            Kakeya.realRpowENN delta 1 *
            ENNReal.ofReal data.data.rho.1 := by
              rw [← realRpowENN_add data.data.cfg.extremal.delta_pos]
              congr 2 <;> ring
      _ ≤ Kakeya.realRpowENN delta (massLoss + 2) *
          (ENNReal.ofReal (Real.pi / 4) *
            data.data.cfg.family.enncard) *
          ENNReal.ofReal data.data.rho.1 := by gcongr
      _ = ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta (massLoss + 2) *
          data.data.cfg.family.enncard *
          ENNReal.ofReal data.data.rho.1 := by ring
      _ ≤ common.F2.mass := hmassCard
  apply data.toLemma32DerivativeBandOn common.F2 massLoss
  · intro index
    rw [common.F2_eq]
    exact (wz2RefinedShading_subshading index).trans
      (data.data.scaleData.slab_subshading index)
  · exact common.F2_in_slab
  · exact hmassCard
  · exact hmass

/-- The existing common-y geometry paired with a sharper fixed-loss
derivative band. -/
structure PureWZ2CoupledCommonYFixedLossDerivativeBandData
    {sigma epsilon delta : ℝ}
    (data : PureWZ2Lemma31DerivativeAssembly sigma epsilon delta)
    (fixedLoss : ℝ) where
  commonData : PureWZ2CoupledCommonYDerivativeBandData data
  band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta
  band_lemma31 : band.lemma31 = data
  band_source_union : band.sourceShading.union = commonData.common.F2.union
  band_massLoss : band.massLoss =
    data.data.targetLoss + 4 * commonData.common.badYLoss + fixedLoss
  fixed_loss_pos : 0 < fixedLoss
  frame_close_on_band : ∀ z ∈ Set.Icc band.left band.right,
    |commonData.frameSlope - data.data.globalSlope z| ≤ 1 / 4

/-- Construct the fixed-loss band without changing the historical common-y
record or its direct-backend callers. -/
theorem PureWZ2Lemma31DerivativeAssembly.toCoupledCommonYFixedLossDerivativeBand
    {sigma epsilon delta fixedLoss : ℝ}
    (data : PureWZ2Lemma31DerivativeAssembly sigma epsilon delta)
    (hfixedLoss : 0 < fixedLoss)
    (hquarter : Kakeya.realRpowENN delta fixedLoss ≤ (1 / 4 : ENNReal)) :
    Nonempty (PureWZ2CoupledCommonYFixedLossDerivativeBandData
      data fixedLoss) := by
  let commonData := Classical.choice data.toCoupledCommonYDerivativeBand
  rcases data.toLemma32DerivativeBandAfterCommonYWithFixedLoss
      commonData.popular commonData.frameSlope commonData.common hquarter with
    ⟨band, hbandData, hbandSource, hbandLoss⟩
  have hframeClose : ∀ z ∈ Set.Icc band.left band.right,
      |commonData.frameSlope - data.data.globalSlope z| ≤ 1 / 4 := by
    intro z hz
    let midpoint := data.data.scaleData.slabLeft +
      (data.data.scaleData.slabRight - data.data.scaleData.slabLeft) / 2
    have hmidpoint : midpoint ∈ Set.Icc data.data.scaleData.slabLeft
        data.data.scaleData.slabRight := by
      dsimp only [midpoint]
      constructor <;> linarith [data.data.scaleData.slab_ordered]
    have hmidpointAmbient : midpoint ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨data.data.scaleData.slabLeft_mem.trans hmidpoint.1,
        hmidpoint.2.trans data.data.scaleData.slabRight_mem⟩
    have hzSlab : z ∈ Set.Icc data.data.scaleData.slabLeft
        data.data.scaleData.slabRight := by
      rw [← hbandData]
      exact ⟨band.left_mem.trans hz.1, hz.2.trans band.right_mem⟩
    have hzAmbient : z ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨data.data.scaleData.slabLeft_mem.trans hzSlab.1,
        hzSlab.2.trans data.data.scaleData.slabRight_mem⟩
    have hlip := data.data.cfg.globalGrains.slope_lipschitzOn.dist_le_mul
      midpoint hmidpointAmbient z hzAmbient
    have hspan : |midpoint - z| ≤
        data.data.scaleData.slabRight - data.data.scaleData.slabLeft := by
      rw [abs_le]
      constructor <;> linarith [hmidpoint.1, hmidpoint.2,
        hzSlab.1, hzSlab.2]
    have hcloseCfg : |commonData.frameSlope -
        data.data.cfg.globalGrains.slope z| ≤ data.data.rho.1 := by
      rw [commonData.frameSlope_eq]
      calc
        |data.data.cfg.globalGrains.slope midpoint -
            data.data.cfg.globalGrains.slope z| ≤ |midpoint - z| := by
          norm_num [Real.dist_eq] at hlip ⊢
          exact hlip
        _ ≤ data.data.scaleData.slabRight -
            data.data.scaleData.slabLeft := hspan
        _ = data.data.rho.1 := data.data.scaleData.slab_width
    rw [data.data.globalSlope_eq_on z hzAmbient]
    exact hcloseCfg.trans (data.rho_tiny.trans (by norm_num))
  exact ⟨{
    commonData := commonData
    band := band
    band_lemma31 := hbandData
    band_source_union := hbandSource
    band_massLoss := hbandLoss
    fixed_loss_pos := hfixedLoss
    frame_close_on_band := hframeClose }⟩

end Kakeya.Assouad
end
