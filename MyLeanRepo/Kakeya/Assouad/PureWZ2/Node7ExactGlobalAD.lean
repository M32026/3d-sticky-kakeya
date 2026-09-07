import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7AffineExactShading
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7ExactSlopeCertificate
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7OrdinaryRetubing
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicADTransfer

/-!
# Exact-slice global AD for the Node 7 Mobius normalization

The target shading is the literal affine image of its synchronized source
shading.  On each target height the general-frame projection covariance is a
positive affine scalar map; the scalar is allowed to depend on the slice.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

namespace PureWZ2Node7AffineDiagonalPreparationData

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}

theorem exactShading_horizontalSlice_empty_of_not_active
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    {t : ℝ} (ht : t ∉ Set.Icc data.activeLeft data.activeRight) :
    horizontalSlice data.exactShading.union t = ∅ := by
  ext point
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hpoint
  have hheight : t ∈ Set.Icc data.activeLeft data.activeRight := by
    have hactive := data.exactShading_union_height_mem_active hpoint.1
    rw [hpoint.2] at hactive
    exact hactive
  exact ht hheight

/-- Exact projection identity on a target slice.  The coefficient is the
reciprocal of the height-dependent factor `lambda` from `node07.tex`. -/
theorem exactShading_slice_projection_eq
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    {t : ℝ} (ht : t ∈ Set.Icc data.activeLeft data.activeRight) :
    let sourceHeight := data.affineScale.slopeData.anchor +
      t / data.affineScale.slopeData.heightScale
    let sourceSlope :=
      commonSource.commonBand.band.lemma31.data.globalSlope sourceHeight
    let coefficient := pureWZ2HorizontalNorm
        data.affineScale.slopeData.frameSlope /
      (1 + data.affineScale.slopeData.frameSlope * sourceSlope)
    scalarProjection
        (globalGrainDirection (data.analysisSlope t))
        (horizontalSlice data.exactShading.union t) =
      (fun value : ℝ => coefficient * value - coefficient *
        inner ℝ data.selected.center
          (globalGrainDirection sourceSlope)) ''
        scalarProjection (globalGrainDirection sourceSlope)
          (horizontalSlice data.sourceExactShading.union sourceHeight) := by
  dsimp only
  let source := commonSource.commonBand.band.lemma31.data.globalSlope
  let q := data.affineScale.slopeData.frameSlope
  let sourceHeight := data.affineScale.slopeData.anchor +
    t / data.affineScale.slopeData.heightScale
  let sourceSlope := source sourceHeight
  let coefficient := pureWZ2HorizontalNorm q / (1 + q * sourceSlope)
  have hdenom := data.denominator_bounds ht
  have hdenomPos : 0 < 1 + q * sourceSlope := by
    have hB : 0 < 1 + q ^ 2 := by positivity
    exact (mul_pos (by norm_num) hB).trans_le hdenom.1
  have hslopeEq : data.analysisSlope t =
      pureWZ2RotatedSlopeValue q sourceSlope /
        data.affineScale.slopeData.transverseScale := by
    rw [data.analysisSlope_eq_on_active ht]
    rfl
  rw [data.exactShading_union, hslopeEq]
  ext value
  constructor
  · rintro ⟨target, ⟨⟨sourcePoint, hsourcePoint, hmap⟩, hheight⟩, rfl⟩
    have hsourceHeightEq : sourcePoint 2 = sourceHeight := by
      rw [← hmap] at hheight
      rw [pureWZ2AffineDiagonalMapCentered_coord_two] at hheight
      have hcenterHeight : data.selected.center 2 =
          data.affineScale.slopeData.anchor := by
        rw [data.selected.center_eq]
        simp [pureWZ2AffineDiagonalCommonCenter, point3]
      rw [hcenterHeight] at hheight
      simp only [one_mul] at hheight
      dsimp only [sourceHeight]
      have hheightScale : data.affineScale.slopeData.heightScale ≠ 0 :=
        (lt_of_lt_of_le (by norm_num) data.affineScale.height_lower).ne'
      field_simp [hheightScale] at hheight ⊢
      linarith
    refine ⟨inner ℝ sourcePoint (globalGrainDirection sourceSlope),
      ⟨sourcePoint, ⟨hsourcePoint, hsourceHeightEq⟩, rfl⟩, ?_⟩
    rw [← hmap]
    have hprojection := pureWZ2AffineDiagonalCentered_projection_identity
      q data.selected.center data.affineScale.slopeData.heightScale
      data.affineScale.slopeData.transverseScale 1 sourceSlope sourcePoint
      data.affineScale.transverse_pos.ne' hdenomPos.ne'
    rw [one_mul] at hprojection
    change inner ℝ
        (pureWZ2AffineDiagonalMapCentered q data.selected.center
          data.affineScale.slopeData.heightScale
          data.affineScale.slopeData.transverseScale 1 sourcePoint)
        (globalGrainDirection
          (pureWZ2RotatedSlopeValue q sourceSlope /
            data.affineScale.slopeData.transverseScale)) =
      coefficient * inner ℝ (sourcePoint - data.selected.center)
        (globalGrainDirection sourceSlope) at hprojection
    rw [inner_sub_left] at hprojection
    have hprojection' :
        coefficient * inner ℝ sourcePoint (globalGrainDirection sourceSlope) -
            coefficient * inner ℝ data.selected.center
              (globalGrainDirection sourceSlope) =
          inner ℝ
            (pureWZ2AffineDiagonalMapCentered q data.selected.center
              data.affineScale.slopeData.heightScale
              data.affineScale.slopeData.transverseScale 1 sourcePoint)
            (globalGrainDirection
              (pureWZ2RotatedSlopeValue q sourceSlope /
                data.affineScale.slopeData.transverseScale)) := by
      calc
        coefficient * inner ℝ sourcePoint (globalGrainDirection sourceSlope) -
              coefficient * inner ℝ data.selected.center
                (globalGrainDirection sourceSlope) =
            coefficient *
              (inner ℝ sourcePoint (globalGrainDirection sourceSlope) -
                inner ℝ data.selected.center
                  (globalGrainDirection sourceSlope)) := by ring
        _ = inner ℝ
            (pureWZ2AffineDiagonalMapCentered q data.selected.center
              data.affineScale.slopeData.heightScale
              data.affineScale.slopeData.transverseScale 1 sourcePoint)
            (globalGrainDirection
              (pureWZ2RotatedSlopeValue q sourceSlope /
                data.affineScale.slopeData.transverseScale)) := by
          exact hprojection.symm
    exact hprojection'
  · rintro ⟨sourceValue,
      ⟨sourcePoint, ⟨hsourcePoint, hsourceHeightEq⟩, rfl⟩, rfl⟩
    let targetPoint := pureWZ2AffineDiagonalMapCentered q
      data.selected.center data.affineScale.slopeData.heightScale
      data.affineScale.slopeData.transverseScale 1 sourcePoint
    have htargetHeight : targetPoint 2 = t := by
      dsimp only [targetPoint]
      rw [pureWZ2AffineDiagonalMapCentered_coord_two]
      have hcenterHeight : data.selected.center 2 =
          data.affineScale.slopeData.anchor := by
        rw [data.selected.center_eq]
        simp [pureWZ2AffineDiagonalCommonCenter, point3]
      rw [hcenterHeight, hsourceHeightEq]
      simp only [one_mul]
      have hheightScale : data.affineScale.slopeData.heightScale ≠ 0 :=
        (lt_of_lt_of_le (by norm_num) data.affineScale.height_lower).ne'
      change sourcePoint 2 = data.affineScale.slopeData.anchor +
        t / data.affineScale.slopeData.heightScale at hsourceHeightEq
      field_simp [hheightScale]
      ring
    refine ⟨targetPoint, ⟨⟨sourcePoint, hsourcePoint, rfl⟩, htargetHeight⟩, ?_⟩
    have hprojection := pureWZ2AffineDiagonalCentered_projection_identity
      q data.selected.center data.affineScale.slopeData.heightScale
      data.affineScale.slopeData.transverseScale 1 sourceSlope sourcePoint
      data.affineScale.transverse_pos.ne' hdenomPos.ne'
    rw [one_mul] at hprojection
    change inner ℝ targetPoint
        (globalGrainDirection
          (pureWZ2RotatedSlopeValue q sourceSlope /
            data.affineScale.slopeData.transverseScale)) =
      coefficient * inner ℝ (sourcePoint - data.selected.center)
        (globalGrainDirection sourceSlope) at hprojection
    change inner ℝ targetPoint
        (globalGrainDirection
          (pureWZ2RotatedSlopeValue q sourceSlope /
            data.affineScale.slopeData.transverseScale)) = _
    rw [show inner ℝ targetPoint
          (globalGrainDirection
            (pureWZ2RotatedSlopeValue q sourceSlope /
              data.affineScale.slopeData.transverseScale)) =
        coefficient * inner ℝ (sourcePoint - data.selected.center)
          (globalGrainDirection sourceSlope) by
      exact hprojection]
    rw [inner_sub_left]
    ring

theorem exactShading_global_ad
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (data.analysisSlope t))
          (horizontalSlice data.exactShading.union t))
        data.affineScale.targetDelta (1 - sigma)
          commonSource.commonBand.band.sourceConstant := by
  intro t _ht
  by_cases hactive : t ∈ Set.Icc data.activeLeft data.activeRight
  · let sourceHeight := data.affineScale.slopeData.anchor +
      t / data.affineScale.slopeData.heightScale
    let sourceSlope :=
      commonSource.commonBand.band.lemma31.data.globalSlope sourceHeight
    let coefficient := pureWZ2HorizontalNorm
        data.affineScale.slopeData.frameSlope /
      (1 + data.affineScale.slopeData.frameSlope * sourceSlope)
    have hsourceSubband := data.sourceHeight_mem_subband hactive
    have hsourcePaper : sourceHeight ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨commonSource.commonBand.band.lemma31.data.scaleData.slabLeft_mem.trans
          (commonSource.commonBand.band.left_mem.trans <|
            commonSource.subband.left_mem.trans hsourceSubband.1),
        hsourceSubband.2.trans <| commonSource.subband.right_mem.trans <|
          commonSource.commonBand.band.right_mem.trans
            commonSource.commonBand.band.lemma31.data.scaleData.slabRight_mem⟩
    have hsourceAD : PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection sourceSlope)
          (horizontalSlice data.sourceExactShading.union sourceHeight))
        delta (1 - sigma) commonSource.commonBand.band.sourceConstant := by
      have hambient :=
        commonSource.commonBand.band.lemma31.data.cfg.globalGrains.global_ad_slope
          sourceHeight hsourcePaper
      have hslope :
          commonSource.commonBand.band.lemma31.data.cfg.globalGrains.slope
              sourceHeight = sourceSlope := by
        exact (commonSource.commonBand.band.lemma31.data.globalSlope_eq_on
          sourceHeight hsourcePaper).symm
      rw [hslope] at hambient
      exact hambient.weaken_subset <| by
        apply Set.image_mono
        rintro point ⟨hpoint, hheight⟩
        have hsubband := data.sourceExactShading_union_subset_subband hpoint
        rcases hsubband with ⟨index, hindex⟩
        rw [commonSource.subband.carrier_eq] at hindex
        exact ⟨⟨index, commonSource.commonBand.band.source_subshading index
          hindex.1⟩, hheight⟩
    have hdenom := data.denominator_bounds hactive
    let B : ℝ := 1 + data.affineScale.slopeData.frameSlope ^ 2
    have hBPos : 0 < B := by dsimp only [B]; positivity
    have hdenomPos : 0 < 1 + data.affineScale.slopeData.frameSlope *
        sourceSlope :=
      (mul_pos (by norm_num) hBPos).trans_le hdenom.1
    have hcoefficientPos : 0 < coefficient := by
      dsimp only [coefficient]
      exact div_pos (pureWZ2HorizontalNorm_pos _) hdenomPos
    have haffine := hsourceAD.affine_transfer
      (a := coefficient)
      (b := -coefficient * inner ℝ data.selected.center
        (globalGrainDirection sourceSlope)) hcoefficientPos
    rw [data.exactShading_slice_projection_eq hactive]
    have hbase : coefficient * delta ≤ data.affineScale.targetDelta := by
      have hcoeff : coefficient ≤ 2 := by
        dsimp only [coefficient]
        have hnormSq := pureWZ2HorizontalNorm_sq
          data.affineScale.slopeData.frameSlope
        have hnormUpperSq : pureWZ2HorizontalNorm
              data.affineScale.slopeData.frameSlope ^ 2 ≤ 2 := by
          rw [hnormSq]
          rcases abs_le.mp data.affineScale.slopeData.frameSlope_bound with
            ⟨hqLower, hqUpper⟩
          nlinarith [sq_nonneg
            (data.affineScale.slopeData.frameSlope - 1),
            sq_nonneg (data.affineScale.slopeData.frameSlope + 1)]
        have hnormUpper : pureWZ2HorizontalNorm
            data.affineScale.slopeData.frameSlope ≤ 3 / 2 := by
          nlinarith [pureWZ2HorizontalNorm_pos
            data.affineScale.slopeData.frameSlope]
        have hdenomLower : (99 / 100 : ℝ) * B ≤
            1 + data.affineScale.slopeData.frameSlope * sourceSlope :=
          by simpa [B, sourceSlope, sourceHeight] using hdenom.1
        have hBOne : 1 ≤ B := by
          dsimp only [B]
          nlinarith [sq_nonneg data.affineScale.slopeData.frameSlope]
        apply (div_le_iff₀ hdenomPos).2
        calc
          pureWZ2HorizontalNorm data.affineScale.slopeData.frameSlope ≤
              3 / 2 := hnormUpper
          _ ≤ 2 * ((99 / 100 : ℝ) * B) := by nlinarith
          _ ≤ 2 * (1 + data.affineScale.slopeData.frameSlope * sourceSlope) :=
            by gcongr
      calc
        coefficient * delta ≤ 2 * delta := by
          exact mul_le_mul_of_nonneg_right hcoeff
            commonSource.commonBand.band.lemma31.data.cfg.extremal.delta_pos.le
        _ ≤ data.affineScale.targetDelta := by
          rw [data.affineScale.targetDelta_eq]
          have htwo : (2 : ℝ) ≤
              2 * data.affineScale.slopeData.heightScale := by
            nlinarith [data.affineScale.height_lower]
          exact mul_le_mul_of_nonneg_right htwo
            commonSource.commonBand.band.lemma31.data.cfg.extremal.delta_pos.le
    simpa [coefficient, sourceSlope, sourceHeight, sub_eq_add_neg] using
      haffine.weaken_scale data.affineScale.targetDelta_pos hbase
  · rw [data.exactShading_horizontalSlice_empty_of_not_active hactive]
    simp only [scalarProjection, Set.image_empty]
    have hseed :=
      commonSource.commonBand.band.lemma31.data.cfg.globalGrains.global_ad_slope
        0 (by norm_num)
    refine ⟨data.affineScale.targetDelta_pos, by linarith, by linarith,
      hseed.2.2.2.1, hseed.2.2.2.2.1, ?_⟩
    intro rho hrho _hrhoLower left length _hlength
    simp

/-- The intermediate exact-image ordinary shading uses the same carrier sets,
so it inherits exact-slice global AD without any covering-number loss. -/
theorem exactOrdinaryShading_global_ad
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (data.analysisSlope t))
          (horizontalSlice data.exactOrdinaryShading.union t))
        data.affineScale.targetDelta (1 - sigma)
          commonSource.commonBand.band.sourceConstant := by
  intro t ht
  change PureWZ2PaperADSet1
    (scalarProjection
      (globalGrainDirection (data.analysisSlope t))
      (horizontalSlice data.exactShading.union t))
    data.affineScale.targetDelta (1 - sigma)
      commonSource.commonBand.band.sourceConstant
  exact data.exactShading_global_ad hsigma hsigmaOne t ht

end PureWZ2Node7AffineDiagonalPreparationData

end Kakeya.Assouad

end
