import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ExactDiagonalSlope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalJointFamily

/-!
# Exact global AD for the centered pure-diagonal joint family

The affine-diagonal quotient keeps source and target indices synchronized.
This file records the corresponding union-level image identity and transports
the Node-5 global AD through the same centered pure-diagonal map that produces
the public slope.  No tangent replacement or additional spatial localization
is used.
-/

noncomputable section

namespace Kakeya.Assouad

open Set
open PureWZ2ExternalWeightRegularizationData

namespace PureWZ2AffineDiagonalCleanupQuotientAssemblyData

/-- The Node-5 global grain field restricted to the exact source shading
paired with the final affine-diagonal joint family. -/
def finalSourceGlobalGrains
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    PureWZ2C2GlobalGrainData assembly.finalSourceShading sigma
      band.sourceConstant := by
  let popularGlobal : PureWZ2C2GlobalGrainData
      popular.popular.restricted sigma band.sourceConstant :=
    band.lemma31.data.cfg.globalGrains.restrict_same_constant
      (fun index point hpoint => by
      have hsubband : point ∈ subband.shading.carrier index :=
        popular.popular.restricted_subshading index hpoint
      rw [subband.carrier_eq] at hsubband
      exact band.source_subshading index hsubband.1)
  exact ((popularGlobal.subfamily regularized.selected).subfamily
    data.selected).subfamily assembly.finalSourceSubfamily

/-- The final exact target shading is literally the centered affine-diagonal
image of the synchronized final source shading. -/
theorem finalExactShading_union_eq_affine_image
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    assembly.finalExactShading.union =
      pureWZ2AffineDiagonalMapCentered affineScale.slopeData.frameSlope
        cleanup.raw.center affineScale.slopeData.heightScale
          affineScale.slopeData.transverseScale 1 ''
        assembly.finalSourceShading.union := by
  ext point
  constructor
  · rintro ⟨index, hpoint⟩
    change point ∈
      (cleanupTargetExactShading (regularized := regularized)
        (cleanup := cleanup) data).carrier
          (assembly.joint.finalTargetIndex index) at hpoint
    rw [cleanupTargetExactShading_carrier] at hpoint
    rcases hpoint.1 with ⟨source, hsource, rfl⟩
    refine ⟨source, ⟨index, ?_⟩, rfl⟩
    exact hsource
  · rintro ⟨source, ⟨index, hsource⟩, rfl⟩
    refine ⟨index, ?_⟩
    change pureWZ2AffineDiagonalMapCentered
        affineScale.slopeData.frameSlope cleanup.raw.center
          affineScale.slopeData.heightScale
            affineScale.slopeData.transverseScale 1 source ∈
      (cleanupTargetExactShading (regularized := regularized)
        (cleanup := cleanup) data).carrier
          (assembly.joint.finalTargetIndex index)
    rw [cleanupTargetExactShading_carrier]
    refine ⟨⟨source, hsource, rfl⟩, ?_⟩
    rw [cleanupTargetShading_carrier_eq_saturation
      (regularized := regularized) (cleanup := cleanup) data]
    exact ⟨_, ⟨source, hsource, rfl⟩, rfl⟩

/-- The synchronized final source shading is still a genuine restriction of
the selected derivative subband. -/
theorem finalSourceShading_union_subset_subband
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    assembly.finalSourceShading.union ⊆ subband.shading.union := by
  intro point hpoint
  have hcleanup : point ∈
      (cleanupTargetSourceShading (regularized := regularized)
        (cleanup := cleanup) data).union :=
    assembly.joint.finalSourceShading_union_subset
      (cleanupTargetSourceShading (regularized := regularized)
        (cleanup := cleanup) data) hpoint
  have hselected : point ∈
      (restrictPaperShading regularized.selected
        popular.popular.restricted).union :=
    restrictPaperShading_union_subset data.selected
      (restrictPaperShading regularized.selected
        popular.popular.restricted) hcleanup
  have hpopular : point ∈ popular.popular.restricted.union :=
    restrictPaperShading_union_subset regularized.selected
      popular.popular.restricted hselected
  exact paperSubshading_union_subset
    popular.popular.restricted_subshading hpopular

/-- The synchronized final source shading remains inside the original
fixed-width popular box selected before every affine-diagonal operation. -/
theorem finalSourceShading_union_subset_popular
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    assembly.finalSourceShading.union ⊆
      popular.popular.restricted.union := by
  intro point hpoint
  have hcleanup : point ∈
      (cleanupTargetSourceShading (regularized := regularized)
        (cleanup := cleanup) data).union :=
    assembly.joint.finalSourceShading_union_subset
      (cleanupTargetSourceShading (regularized := regularized)
        (cleanup := cleanup) data) hpoint
  have hselected : point ∈
      (restrictPaperShading regularized.selected
        popular.popular.restricted).union :=
    restrictPaperShading_union_subset data.selected
      (restrictPaperShading regularized.selected
        popular.popular.restricted) hcleanup
  exact restrictPaperShading_union_subset regularized.selected
    popular.popular.restricted hselected

/-- The fixed popular-box provenance gives an absolute diameter bound for the
synchronized final source set, without any new terminal localization. -/
theorem finalSourceShading_diameter
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    ∀ first ∈ assembly.finalSourceShading.union,
      ∀ second ∈ assembly.finalSourceShading.union,
        dist first second ≤ Real.sqrt 3 / 8 := by
  intro first hfirst second hsecond
  have hball := popular.popular.restricted_union_subset_ball
    (show (0 : ℝ) ≤ 1 / 8 by norm_num)
  have hfirstBall := hball
    (assembly.finalSourceShading_union_subset_popular hfirst)
  have hsecondBall := hball
    (assembly.finalSourceShading_union_subset_popular hsecond)
  rw [Metric.mem_closedBall] at hfirstBall hsecondBall
  calc
    dist first second ≤ dist first popular.popular.center +
        dist popular.popular.center second := dist_triangle _ _ _
    _ ≤ Real.sqrt 3 * ((1 / 8 : ℝ) / 2) +
        Real.sqrt 3 * ((1 / 8 : ℝ) / 2) :=
      add_le_add hfirstBall (by simpa [dist_comm] using hsecondBall)
    _ = Real.sqrt 3 / 8 := by ring

/-- Every point of the final exact pure-diagonal image has target height in
the active core on which the extended public slope is the transported slope. -/
theorem PureWZ2ExactDiagonalAffineScaleData.finalExactShading_height_mem_core
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (exactScale : PureWZ2ExactDiagonalAffineScaleData subband)
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular exactScale.affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    {point : Point3} (hpoint : point ∈ assembly.finalExactShading.union) :
    point 2 ∈ Set.Icc (pureWZ2ExactDiagonalCoreLeft subband)
      (pureWZ2ExactDiagonalCoreRight subband) := by
  rw [assembly.finalExactShading_union_eq_affine_image] at hpoint
  rcases hpoint with ⟨source, hsource, rfl⟩
  have hsubband := finalSourceShading_union_subset_subband assembly hsource
  rcases hsubband with ⟨index, hcarrier⟩
  rw [subband.carrier_eq] at hcarrier
  have hheight : source 2 ∈ Set.Icc subband.left subband.right := hcarrier.2
  have hm := pureWZ2ExactDiagonalScale_pos band
  have hfactor : 0 < 100 / pureWZ2ExactDiagonalScale band := by positivity
  rw [show
      pureWZ2AffineDiagonalMapCentered
          exactScale.affineScale.slopeData.frameSlope cleanup.raw.center
          exactScale.affineScale.slopeData.heightScale
          exactScale.affineScale.slopeData.transverseScale 1 source 2 =
        (100 / pureWZ2ExactDiagonalScale band) *
          (source 2 - subband.anchor) by
    simp [pureWZ2AffineDiagonalMapCentered, exactScale.frame_zero,
      cleanup.raw.center_eq, pureWZ2AffineDiagonalCommonCenter,
      exactScale.affineScale.slopeData.heightScale_eq,
      exactScale.diagonal_scale, exactScale.normalization_hundred,
      exactScale.anchor_midpoint, point3]]
  constructor
  · unfold pureWZ2ExactDiagonalCoreLeft
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hheight.1 _) hfactor.le
  · unfold pureWZ2ExactDiagonalCoreRight
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hheight.2 _) hfactor.le

/-- Exact global AD on the active target-height core of the final joint
pure-diagonal image.  The slope in the conclusion is the globally extended
public witness, but the preceding height certificate identifies it with the
literal transported slope everywhere the exact shading can meet the slice. -/
theorem PureWZ2ExactDiagonalAffineScaleData.finalExactShading_global_ad_on_core
    {sigma epsilon delta targetDelta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (exactScale : PureWZ2ExactDiagonalAffineScaleData subband)
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular exactScale.affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (htargetDelta : 0 < targetDelta)
    (hbase : delta ≤ targetDelta) :
    ∀ t ∈ Set.Icc (pureWZ2ExactDiagonalCoreLeft subband)
        (pureWZ2ExactDiagonalCoreRight subband),
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (pureWZ2ExactDiagonalSlope subband t))
          (horizontalSlice assembly.finalExactShading.union t))
        targetDelta (1 - sigma) band.sourceConstant := by
  intro t ht
  let sourceGlobal := assembly.finalSourceGlobalGrains
  let sourceHeight := subband.anchor +
    pureWZ2ExactDiagonalScale band / 100 * t
  have hsourceHeightSubband :=
    pureWZ2ExactDiagonal_sourceHeight_mem subband ht
  have hsourceHeight : sourceHeight ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · exact band.lemma31.data.scaleData.slabLeft_mem.trans
        (band.left_mem.trans <| subband.left_mem.trans
          hsourceHeightSubband.1)
    · exact hsourceHeightSubband.2.trans <| subband.right_mem.trans <|
        band.right_mem.trans band.lemma31.data.scaleData.slabRight_mem
  have hsourceAD : PureWZ2PaperADSet1
      (scalarProjection
        (globalGrainDirection (band.lemma31.data.globalSlope sourceHeight))
        (horizontalSlice assembly.finalSourceShading.union sourceHeight))
      delta (1 - sigma) band.sourceConstant := by
    have h := sourceGlobal.global_ad_slope sourceHeight hsourceHeight
    have hsourceSlope : sourceGlobal.slope =
        band.lemma31.data.cfg.globalGrains.slope := rfl
    rw [hsourceSlope, ← band.lemma31.data.globalSlope_eq_on sourceHeight
      hsourceHeight] at h
    exact h
  have haffine := PureWZ2PaperADSet1.affine_transfer
    (a := 1)
    (b := -inner ℝ cleanup.raw.center
        (globalGrainDirection (band.lemma31.data.globalSlope sourceHeight)))
    hsourceAD (by norm_num)
  have hprojection :
      scalarProjection
          (globalGrainDirection (pureWZ2ExactDiagonalSlope subband t))
          (horizontalSlice assembly.finalExactShading.union t) =
        (fun value : ℝ =>
          value - inner ℝ cleanup.raw.center
                (globalGrainDirection
                  (band.lemma31.data.globalSlope sourceHeight))) ''
          scalarProjection
            (globalGrainDirection
              (band.lemma31.data.globalSlope sourceHeight))
            (horizontalSlice assembly.finalSourceShading.union
              sourceHeight) := by
    rw [assembly.finalExactShading_union_eq_affine_image]
    rw [pureWZ2ExactDiagonalSlope_eq_on_core subband ht]
    rw [show exactScale.affineScale.slopeData.frameSlope = 0 from
      exactScale.frame_zero]
    rw [show exactScale.affineScale.slopeData.heightScale =
        100 / pureWZ2ExactDiagonalScale band by
      rw [exactScale.affineScale.slopeData.heightScale_eq,
        exactScale.diagonal_scale, exactScale.normalization_hundred]]
    rw [show exactScale.affineScale.slopeData.transverseScale =
        pureWZ2ExactDiagonalScale band ^ 2 / 100 by
      rw [exactScale.affineScale.slopeData.transverseScale_eq,
        exactScale.diagonal_scale, exactScale.normalization_hundred]]
    ext value
    constructor
    · rintro ⟨target, ⟨⟨source, hsource, hmap⟩, hheight⟩, rfl⟩
      have hsourceHeightEq : source 2 = sourceHeight := by
        rw [← hmap] at hheight
        rw [pureWZ2AffineDiagonalMapCentered_coord_two] at hheight
        have hcenterHeight : cleanup.raw.center 2 = subband.anchor := by
          rw [cleanup.raw.center_eq]
          simp [pureWZ2AffineDiagonalCommonCenter, point3,
            exactScale.anchor_midpoint]
        rw [hcenterHeight] at hheight
        simp only [one_mul] at hheight
        dsimp only [sourceHeight] at hheight ⊢
        have hm := pureWZ2ExactDiagonalScale_pos band
        field_simp [hm.ne'] at hheight ⊢
        linarith
      have hslopeValue :
          pureWZ2RotatedSlopeValue 0
                (band.lemma31.data.globalSlope sourceHeight) /
              (pureWZ2ExactDiagonalScale band ^ 2 / 100) =
            100 / pureWZ2ExactDiagonalScale band ^ 2 *
              band.lemma31.data.globalSlope
                (subband.anchor + pureWZ2ExactDiagonalScale band / 100 * t) := by
        rw [show sourceHeight = subband.anchor +
          pureWZ2ExactDiagonalScale band / 100 * t by rfl]
        unfold pureWZ2RotatedSlopeValue
        have hm := pureWZ2ExactDiagonalScale_pos band
        field_simp [hm.ne']
        ring
      refine ⟨inner ℝ source
          (globalGrainDirection (band.lemma31.data.globalSlope sourceHeight)),
        ⟨source, ⟨hsource, hsourceHeightEq⟩, rfl⟩, ?_⟩
      rw [← hmap]
      have hprojectionPoint :=
        pureWZ2AffineDiagonalCentered_projection_identity
          0 cleanup.raw.center (100 / pureWZ2ExactDiagonalScale band)
          (pureWZ2ExactDiagonalScale band ^ 2 / 100) 1
          (band.lemma31.data.globalSlope sourceHeight) source
          (div_ne_zero (pow_ne_zero 2
            (pureWZ2ExactDiagonalScale_pos band).ne') (by norm_num)) (by simp)
      rw [hslopeValue] at hprojectionPoint
      calc
        inner ℝ source
              (globalGrainDirection
                (band.lemma31.data.globalSlope sourceHeight)) -
            inner ℝ cleanup.raw.center
              (globalGrainDirection
                (band.lemma31.data.globalSlope sourceHeight)) =
          inner ℝ (source - cleanup.raw.center)
            (globalGrainDirection
              (band.lemma31.data.globalSlope sourceHeight)) := by
                rw [inner_sub_left]
        _ = inner ℝ
            (pureWZ2AffineDiagonalMapCentered 0 cleanup.raw.center
              (100 / pureWZ2ExactDiagonalScale band)
              (pureWZ2ExactDiagonalScale band ^ 2 / 100) 1 source)
            (globalGrainDirection
              (100 / pureWZ2ExactDiagonalScale band ^ 2 *
                band.lemma31.data.globalSlope
                  (subband.anchor +
                    pureWZ2ExactDiagonalScale band / 100 * t))) := by
              simpa [pureWZ2HorizontalNorm] using hprojectionPoint.symm
    · rintro ⟨sourceValue,
        ⟨source, ⟨hsource, hsourceHeightEq⟩, rfl⟩, rfl⟩
      have htargetHeight :
          pureWZ2AffineDiagonalMapCentered 0 cleanup.raw.center
              (100 / pureWZ2ExactDiagonalScale band)
              (pureWZ2ExactDiagonalScale band ^ 2 / 100) 1 source 2 = t := by
        simp only [pureWZ2AffineDiagonalMapCentered_coord_two]
        have hcenterHeight : cleanup.raw.center 2 = subband.anchor := by
          rw [cleanup.raw.center_eq]
          simp [pureWZ2AffineDiagonalCommonCenter, point3,
            exactScale.anchor_midpoint]
        rw [hcenterHeight]
        dsimp only [sourceHeight] at hsourceHeightEq
        have hm := pureWZ2ExactDiagonalScale_pos band
        field_simp [hm.ne'] at hsourceHeightEq ⊢
        linarith
      refine ⟨pureWZ2AffineDiagonalMapCentered 0 cleanup.raw.center
          (100 / pureWZ2ExactDiagonalScale band)
          (pureWZ2ExactDiagonalScale band ^ 2 / 100) 1 source,
        ⟨?_, htargetHeight⟩, ?_⟩
      · exact ⟨source, hsource, rfl⟩
      · have hprojectionPoint :=
          pureWZ2AffineDiagonalCentered_projection_identity
            0 cleanup.raw.center (100 / pureWZ2ExactDiagonalScale band)
            (pureWZ2ExactDiagonalScale band ^ 2 / 100) 1
            (band.lemma31.data.globalSlope sourceHeight) source
            (div_ne_zero (pow_ne_zero 2
              (pureWZ2ExactDiagonalScale_pos band).ne') (by norm_num)) (by simp)
        have hslopeValue :
            pureWZ2RotatedSlopeValue 0
                  (band.lemma31.data.globalSlope sourceHeight) /
                (pureWZ2ExactDiagonalScale band ^ 2 / 100) =
              100 / pureWZ2ExactDiagonalScale band ^ 2 *
                band.lemma31.data.globalSlope
                  (subband.anchor + pureWZ2ExactDiagonalScale band / 100 * t) := by
          rw [show sourceHeight = subband.anchor +
            pureWZ2ExactDiagonalScale band / 100 * t by rfl]
          unfold pureWZ2RotatedSlopeValue
          have hm := pureWZ2ExactDiagonalScale_pos band
          field_simp [hm.ne']
          ring
        change inner ℝ
            (pureWZ2AffineDiagonalMapCentered 0 cleanup.raw.center
              (100 / pureWZ2ExactDiagonalScale band)
              (pureWZ2ExactDiagonalScale band ^ 2 / 100) 1 source)
            (globalGrainDirection
              (100 / pureWZ2ExactDiagonalScale band ^ 2 *
                band.lemma31.data.globalSlope
                  (subband.anchor +
                    pureWZ2ExactDiagonalScale band / 100 * t))) = _
        rw [← hslopeValue]
        calc
          inner ℝ
              (pureWZ2AffineDiagonalMapCentered 0 cleanup.raw.center
                (100 / pureWZ2ExactDiagonalScale band)
                (pureWZ2ExactDiagonalScale band ^ 2 / 100) 1 source)
              (globalGrainDirection
                (pureWZ2RotatedSlopeValue 0
                    (band.lemma31.data.globalSlope sourceHeight) /
                  (pureWZ2ExactDiagonalScale band ^ 2 / 100))) =
            1 * (pureWZ2HorizontalNorm 0 /
                (1 + 0 * band.lemma31.data.globalSlope sourceHeight)) *
              inner ℝ (source - cleanup.raw.center)
                (globalGrainDirection
                  (band.lemma31.data.globalSlope sourceHeight)) :=
              hprojectionPoint
          _ = inner ℝ source
                (globalGrainDirection
                  (band.lemma31.data.globalSlope sourceHeight)) -
              inner ℝ cleanup.raw.center
                (globalGrainDirection
                  (band.lemma31.data.globalSlope sourceHeight)) := by
                simp only [pureWZ2HorizontalNorm, one_mul, one_div,
                  inner_sub_left]
                ring
  rw [hprojection]
  have hbase' : 1 * delta ≤ targetDelta := by simpa using hbase
  simpa only [one_mul, sub_eq_add_neg] using
    haffine.weaken_scale htargetDelta hbase'

/-- The exact final shading has no points on a target-height slice outside
the transported derivative-band core. -/
theorem PureWZ2ExactDiagonalAffineScaleData.finalExactShading_horizontalSlice_empty
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (exactScale : PureWZ2ExactDiagonalAffineScaleData subband)
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular exactScale.affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    {t : ℝ}
    (ht : t ∉ Set.Icc (pureWZ2ExactDiagonalCoreLeft subband)
      (pureWZ2ExactDiagonalCoreRight subband)) :
    horizontalSlice assembly.finalExactShading.union t = ∅ := by
  ext point
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hpoint
  have hheight :=
    PureWZ2ExactDiagonalAffineScaleData.finalExactShading_height_mem_core
      exactScale assembly hpoint.1
  rw [hpoint.2] at hheight
  exact ht hheight

/-- Global AD for the centered pure-diagonal exact image on the entire public
height interval.  Outside the active core the target slice is empty; inside
the core exact affine covariance applies. -/
theorem PureWZ2ExactDiagonalAffineScaleData.finalExactShading_global_ad
    {sigma epsilon delta targetDelta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (exactScale : PureWZ2ExactDiagonalAffineScaleData subband)
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular exactScale.affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (htargetDelta : 0 < targetDelta) (hbase : delta ≤ targetDelta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (pureWZ2ExactDiagonalSlope subband t))
          (horizontalSlice assembly.finalExactShading.union t))
        targetDelta (1 - sigma) band.sourceConstant := by
  intro t _ht
  by_cases hcore : t ∈ Set.Icc (pureWZ2ExactDiagonalCoreLeft subband)
      (pureWZ2ExactDiagonalCoreRight subband)
  · exact
      PureWZ2ExactDiagonalAffineScaleData.finalExactShading_global_ad_on_core
        exactScale assembly htargetDelta hbase t hcore
  · rw [PureWZ2ExactDiagonalAffineScaleData.finalExactShading_horizontalSlice_empty
      exactScale assembly hcore]
    simp only [scalarProjection, Set.image_empty]
    have hseed :=
      PureWZ2ExactDiagonalAffineScaleData.finalExactShading_global_ad_on_core
        exactScale assembly htargetDelta hbase 0
          (pureWZ2ExactDiagonalCore_zero_mem subband)
    refine ⟨htargetDelta, by linarith, by linarith, hseed.2.2.2.1,
      hseed.2.2.2.2.1, ?_⟩
    intro rho hrho _hrhoLower left length _hlength
    simp

/-- The synchronized exact shading is supported on the transported core, so
the same global-AD statement is valid at every ambient height.  This form is
used by later centered normalizations whose inverse height can leave the
public interval while the corresponding source slice is empty. -/
theorem PureWZ2ExactDiagonalAffineScaleData.finalExactShading_global_ad_all
    {sigma epsilon delta targetDelta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (exactScale : PureWZ2ExactDiagonalAffineScaleData subband)
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular exactScale.affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (htargetDelta : 0 < targetDelta) (hbase : delta ≤ targetDelta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    ∀ t : ℝ,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (pureWZ2ExactDiagonalSlope subband t))
          (horizontalSlice assembly.finalExactShading.union t))
        targetDelta (1 - sigma) band.sourceConstant := by
  intro t
  by_cases hcore : t ∈ Set.Icc (pureWZ2ExactDiagonalCoreLeft subband)
      (pureWZ2ExactDiagonalCoreRight subband)
  · exact
      PureWZ2ExactDiagonalAffineScaleData.finalExactShading_global_ad_on_core
        exactScale assembly htargetDelta hbase t hcore
  · rw [PureWZ2ExactDiagonalAffineScaleData.finalExactShading_horizontalSlice_empty
      exactScale assembly hcore]
    simp only [scalarProjection, Set.image_empty]
    have hseed :=
      PureWZ2ExactDiagonalAffineScaleData.finalExactShading_global_ad_on_core
        exactScale assembly htargetDelta hbase 0
          (pureWZ2ExactDiagonalCore_zero_mem subband)
    refine ⟨htargetDelta, by linarith, by linarith, hseed.2.2.2.1,
      hseed.2.2.2.2.1, ?_⟩
    intro rho hrho _hrhoLower left length _hlength
    simp

end PureWZ2AffineDiagonalCleanupQuotientAssemblyData

end Kakeya.Assouad

end
