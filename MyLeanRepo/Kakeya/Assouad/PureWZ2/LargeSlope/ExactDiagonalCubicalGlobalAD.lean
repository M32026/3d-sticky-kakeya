import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ExactDiagonalSaturationWitness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CubicalHeightCells
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FinalQuotientGlobalAD

/-!
# Cubical global AD for the exact centered diagonal slope

The synchronized exact image already carries global AD for the literal
transported public slope.  The final target shading is its target-grid
saturation.  This file transfers the estimate to that cubical carrier by
returning every target point to its genuine source point, moving that source
point to the lower face of its original source grid cell, and applying the
finite-slice bridge.  No second coordinate transform is introduced.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set
open PureWZ2ExternalWeightRegularizationData

/-- A paper shading has empty horizontal slices outside `[-1,1]`, because
every carrier lies in the fixed paper axis box. -/
theorem WZ1PaperTubeShading.horizontalSlice_empty_of_not_mem_unit
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) {height : ℝ}
    (hheight : height ∉ Set.Icc (-1 : ℝ) 1) :
    horizontalSlice shading.union height = ∅ := by
  ext point
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨index, hpoint⟩, hpointHeight⟩
  have hbox := (shading.subset_body index hpoint).2
  have hpointUnit : point 2 ∈ Set.Icc (-1 : ℝ) 1 :=
    abs_le.mp <| by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
  rw [hpointHeight] at hpointUnit
  exact hheight hpointUnit

/-- Extend the chosen ambient global-grain AD statement to all heights.  No
new slope extension is introduced: outside the paper window the slice is
empty. -/
theorem PureWZ2C2GlobalGrainData.global_ad_slope_all
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family} {C : ENNReal}
    (data : PureWZ2C2GlobalGrainData shading sigma C)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    ∀ height : ℝ,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (data.slope height))
          (horizontalSlice shading.union height))
        delta (1 - sigma) C := by
  intro height
  by_cases hheight : height ∈ Set.Icc (-1 : ℝ) 1
  · exact data.global_ad_slope height hheight
  · rw [shading.horizontalSlice_empty_of_not_mem_unit hheight]
    simp only [scalarProjection, Set.image_empty]
    have hseed := data.global_ad_slope 0 (by norm_num)
    refine ⟨hseed.1, by linarith, by linarith, hseed.2.2.2.1,
      hseed.2.2.2.2.1, ?_⟩
    intro rho hrho _hrhoLower left length _hlength
    simp

/-- A globally smooth normalized slope is one-Lipschitz on the paper height
window. -/
theorem SlopeFunction.lipschitzOn_unit_of_normalized
    (slope : SlopeFunction) (hnormalized : slope.IsNormalized) :
    LipschitzOnWith 1 slope (Set.Icc (-1 : ℝ) 1) := by
  have hdifferentiable : Differentiable ℝ slope :=
    slope.contDiff.differentiable (by norm_num)
  apply (convex_Icc (-1 : ℝ) 1).lipschitzOnWith_of_nnnorm_deriv_le
  · intro t _ht
    exact hdifferentiable.differentiableAt
  · intro t ht
    apply NNReal.coe_le_coe.mp
    simpa [Real.norm_eq_abs] using (hnormalized t ht).2.1

/-- The globally smooth slope stored by the Lemma-31 assembly gives the
ambient configuration's AD estimate at every height. -/
theorem PureWZ2Lemma32DerivativeBandAssembly.configuration_global_ad_all
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    ∀ height : ℝ,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (band.lemma31.data.globalSlope height))
          (horizontalSlice band.lemma31.data.cfg.shading.union height))
        delta (1 - sigma) band.sourceConstant := by
  intro height
  by_cases hheight : height ∈ Set.Icc (-1 : ℝ) 1
  · have h := band.lemma31.data.cfg.globalGrains.global_ad_slope_all
      hsigma hsigmaOne height
    rw [← band.lemma31.data.globalSlope_eq_on height hheight] at h
    exact h
  · rw [band.lemma31.data.cfg.shading.horizontalSlice_empty_of_not_mem_unit
      hheight]
    simp only [scalarProjection, Set.image_empty]
    have hseed := band.lemma31.data.cfg.globalGrains.global_ad_slope
      0 (by norm_num)
    refine ⟨hseed.1, by linarith, by linarith, hseed.2.2.2.1,
      hseed.2.2.2.2.1, ?_⟩
    intro rho hrho _hrhoLower left length _hlength
    simp

/-- Spatial error, in units of the final target grid scale, after returning a
cubical target point to an exact image and then moving its source preimage to
the lower face of one source cell. -/
def pureWZ2ExactDiagonalCubicalRadiusFactor : ℝ :=
  Real.sqrt 3 + 1 / 2

/-- Slope error, in units of the final target grid scale.  The first term
moves the target height to the exact witness height; the second moves the
source witness to its lower cell face. -/
def pureWZ2ExactDiagonalCubicalSlopeErrorFactor
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta) : ℝ :=
  2 * Real.sqrt 3 + 1 / (2 * pureWZ2ExactDiagonalScale band)

/-- Explicit public-slope bound used by the cubical projection comparison.
The transported value at zero is retained rather than normalized away. -/
def pureWZ2ExactDiagonalCubicalSlopeBound
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta) : ℝ :=
  100 / pureWZ2ExactDiagonalScale band ^ 2 + 2

/-- Dimensionless projection radius absorbed by the one-dimensional AD
thickening. -/
def pureWZ2ExactDiagonalCubicalProjectionFactor
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta) : ℝ :=
  (1 + pureWZ2ExactDiagonalCubicalSlopeBound band) *
      pureWZ2ExactDiagonalCubicalRadiusFactor +
    (1 / 1600) *
      pureWZ2ExactDiagonalCubicalSlopeErrorFactor band

theorem pureWZ2ExactDiagonalCubicalProjectionFactor_pos
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta) :
    0 < pureWZ2ExactDiagonalCubicalProjectionFactor band := by
  have hm := pureWZ2ExactDiagonalScale_pos band
  unfold pureWZ2ExactDiagonalCubicalProjectionFactor
    pureWZ2ExactDiagonalCubicalSlopeBound
    pureWZ2ExactDiagonalCubicalRadiusFactor
    pureWZ2ExactDiagonalCubicalSlopeErrorFactor
  positivity

/-- Under the pure diagonal map, changing only source height changes only
target height, by the exact height dilation. -/
theorem pureWZ2ExactDiagonalMap_replaceHeight_dist
    {sigma epsilon delta height : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (exactScale : PureWZ2ExactDiagonalAffineScaleData subband)
    (center point : Point3) :
    dist
        (pureWZ2AffineDiagonalMapCentered
          exactScale.affineScale.slopeData.frameSlope center
          exactScale.affineScale.slopeData.heightScale
          exactScale.affineScale.slopeData.transverseScale 1 point)
        (pureWZ2AffineDiagonalMapCentered
          exactScale.affineScale.slopeData.frameSlope center
          exactScale.affineScale.slopeData.heightScale
          exactScale.affineScale.slopeData.transverseScale 1
          (pureWZ2ReplaceHeight point height)) =
      (100 / pureWZ2ExactDiagonalScale band) * |point 2 - height| := by
  rw [show exactScale.affineScale.slopeData.frameSlope = 0 from
    exactScale.frame_zero]
  rw [show exactScale.affineScale.slopeData.heightScale =
      100 / pureWZ2ExactDiagonalScale band by
    rw [exactScale.affineScale.slopeData.heightScale_eq,
      exactScale.diagonal_scale, exactScale.normalization_hundred]]
  rw [dist_eq_norm]
  have hdifference :
      pureWZ2AffineDiagonalMapCentered 0 center
          (100 / pureWZ2ExactDiagonalScale band)
          exactScale.affineScale.slopeData.transverseScale 1 point -
        pureWZ2AffineDiagonalMapCentered 0 center
          (100 / pureWZ2ExactDiagonalScale band)
          exactScale.affineScale.slopeData.transverseScale 1
          (pureWZ2ReplaceHeight point height) =
      point3 0 0
        ((100 / pureWZ2ExactDiagonalScale band) * (point 2 - height)) := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2AffineDiagonalMapCentered, pureWZ2ReplaceHeight, point3] <;>
      ring
  rw [hdifference]
  have hfactor : 0 ≤ 100 / pureWZ2ExactDiagonalScale band :=
    (div_nonneg (by norm_num)
      (pureWZ2ExactDiagonalScale_pos band).le)
  rw [show point3 0 0
        ((100 / pureWZ2ExactDiagonalScale band) * (point 2 - height)) =
      ((100 / pureWZ2ExactDiagonalScale band) * (point 2 - height)) •
        EuclideanSpace.single (2 : Fin 3) (1 : ℝ) by simp [point3]]
  rw [norm_smul, Real.norm_eq_abs]
  rw [PiLp.norm_single]
  simp only [norm_one, mul_one, abs_mul, abs_of_nonneg hfactor]

/-- Exact projection covariance at an arbitrary source height.  The public
slope need not agree with this expression away from the transported core; the
later error estimate compares the two values explicitly. -/
theorem pureWZ2ExactDiagonalMap_projection_replaceHeight
    {sigma epsilon delta height : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (exactScale : PureWZ2ExactDiagonalAffineScaleData subband)
    (center point : Point3) :
    inner ℝ
        (pureWZ2AffineDiagonalMapCentered
          exactScale.affineScale.slopeData.frameSlope center
          exactScale.affineScale.slopeData.heightScale
          exactScale.affineScale.slopeData.transverseScale 1
          (pureWZ2ReplaceHeight point height))
        (globalGrainDirection
          ((100 / pureWZ2ExactDiagonalScale band ^ 2) *
            band.lemma31.data.globalSlope height)) =
      inner ℝ (pureWZ2ReplaceHeight point height)
          (globalGrainDirection (band.lemma31.data.globalSlope height)) -
        inner ℝ center
          (globalGrainDirection (band.lemma31.data.globalSlope height)) := by
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
  have hm := pureWZ2ExactDiagonalScale_pos band
  simp [pureWZ2AffineDiagonalMapCentered, pureWZ2ReplaceHeight,
    pureWZ2HorizontalNorm, globalGrainDirection, PiLp.inner_apply,
    Fin.sum_univ_succ, point3]
  field_simp [hm.ne']
  ring

namespace PureWZ2AffineDiagonalCleanupQuotientAssemblyData

/-- The source side synchronized with the final target remains inside the
actual Node-5 configuration. -/
theorem finalSourceShading_union_subset_configuration
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
      band.lemma31.data.cfg.shading.union := by
  intro point hpoint
  have hsubband := assembly.finalSourceShading_union_subset_subband hpoint
  rcases hsubband with ⟨index, hcarrier⟩
  rw [subband.carrier_eq] at hcarrier
  exact ⟨index, band.source_subshading index hcarrier.1⟩

/-- Cubical global AD on the final synchronized target shading.  The only
losses are the fixed seventeen source-height cells and the explicit
dimensionless projection-thickening factor. -/
theorem PureWZ2ExactDiagonalAffineScaleData.finalTargetShading_global_ad
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
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (pureWZ2ExactDiagonalSlope subband z))
          (horizontalSlice assembly.finalTargetShading.union z))
        exactScale.affineScale.targetDelta (1 - sigma)
        ((2 * (Nat.ceil
            (pureWZ2ExactDiagonalCubicalProjectionFactor band) + 1) :
              ENNReal) ^ 3 *
          (17 * band.sourceConstant)) := by
  have hdelta : 0 < delta :=
    band.lemma31.data.cfg.extremal.delta_pos
  have hm : 0 < pureWZ2ExactDiagonalScale band :=
    pureWZ2ExactDiagonalScale_pos band
  have hsqrt : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_nonneg 3]
  have hslopeLipschitz :=
    pureWZ2ExactDiagonalSlope_lipschitzOn_two subband
  have hsourceLipschitz :=
    SlopeFunction.lipschitzOn_unit_of_normalized
      band.lemma31.data.globalSlope
      band.lemma31.data.globalSlope_normalized
  intro z hz
  let sourceCenter := subband.anchor +
    pureWZ2ExactDiagonalScale band / 100 * z
  let heightCells := pureWZ2CenteredHeightCells delta sourceCenter
  let offset : ℤ → ℝ := fun cell =>
    -inner ℝ cleanup.raw.center
      (globalGrainDirection
        (band.lemma31.data.globalSlope ((cell : ℝ) * delta)))
  let D := exactScale.affineScale.targetDelta *
    pureWZ2ExactDiagonalCubicalProjectionFactor band
  have hheightCells : heightCells.Nonempty := by
    apply Finset.card_pos.mp
    rw [show heightCells.card = 17 by
      simpa only [heightCells] using
        pureWZ2CenteredHeightCells_card delta sourceCenter]
    norm_num
  have hraw :=
    band.lemma31.data.cfg.cubical
      |>.targetProjection_ad_of_source_witness_indexed_all
        hdelta exactScale.affineScale.targetDelta_pos
        band.lemma31.data.globalSlope heightCells hheightCells
        (band.configuration_global_ad_all hsigma hsigmaOne)
        (a := 1) (offset := offset)
        (target := scalarProjection
          (globalGrainDirection (pureWZ2ExactDiagonalSlope subband z))
          (horizontalSlice assembly.finalTargetShading.union z))
        (D := D) (by norm_num) (by
          simpa using exactScale.affineScale.source_le_target)
        (by
          rintro value ⟨point, ⟨hpoint, hpointHeight⟩, rfl⟩
          rcases assembly.finalTargetShading_exactWitness ⟨point, hpoint⟩ with
            ⟨exactPoint, hexactDistance⟩
          have hexactImage : (exactPoint : Point3) ∈
              pureWZ2AffineDiagonalMapCentered
                  exactScale.affineScale.slopeData.frameSlope
                  cleanup.raw.center
                  exactScale.affineScale.slopeData.heightScale
                  exactScale.affineScale.slopeData.transverseScale 1 ''
                assembly.finalSourceShading.union := by
            rw [← assembly.finalExactShading_union_eq_affine_image]
            exact exactPoint.property
          rcases hexactImage with ⟨source, hsource, hsourceMap⟩
          have hsourceConfiguration :=
            assembly.finalSourceShading_union_subset_configuration hsource
          let height := pureWZ2PaperCellLowerHeight delta source
          let lowerSource := pureWZ2ReplaceHeight source height
          let lowerImage := pureWZ2AffineDiagonalMapCentered
            exactScale.affineScale.slopeData.frameSlope cleanup.raw.center
            exactScale.affineScale.slopeData.heightScale
            exactScale.affineScale.slopeData.transverseScale 1 lowerSource
          have hsourceHeight : source 2 ∈ Set.Icc (-1 : ℝ) 1 := by
            rcases hsourceConfiguration with ⟨index, hcarrier⟩
            have hbox :=
              (band.lemma31.data.cfg.shading.subset_body index hcarrier).2
            exact abs_le.mp <| by
              simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
          have hlowerConfiguration : lowerSource ∈
              band.lemma31.data.cfg.shading.union := by
            rcases hsourceConfiguration with ⟨index, hcarrier⟩
            exact ⟨index, band.lemma31.data.cfg.cubical.replaceHeight_lower_mem
              hdelta hcarrier⟩
          have hlowerHeight : height ∈ Set.Icc (-1 : ℝ) 1 := by
            rcases hlowerConfiguration with ⟨index, hcarrier⟩
            have hbox :=
              (band.lemma31.data.cfg.shading.subset_body index hcarrier).2
            exact abs_le.mp <| by
              simpa [lowerSource, height, Kakeya.Streamlined.axisBox] using
                hbox.2.2
          have hexactHeight : (exactPoint : Point3) 2 ∈
              Set.Icc (-1 : ℝ) 1 := by
            rcases exactPoint.property with ⟨index, hcarrier⟩
            have hbox := (assembly.finalExactShading.subset_body index hcarrier).2
            exact abs_le.mp <| by
              simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
          have hexactHeightTwo : (exactPoint : Point3) 2 ∈
              Set.Icc (-2 : ℝ) 2 :=
            ⟨by linarith [hexactHeight.1], by linarith [hexactHeight.2]⟩
          have hzTwo : z ∈ Set.Icc (-2 : ℝ) 2 :=
            ⟨by linarith [hz.1], by linarith [hz.2]⟩
          have hexactHeightDistance :
              |(exactPoint : Point3) 2 - z| ≤
                exactScale.affineScale.targetDelta * Real.sqrt 3 := by
            have hcoordinate :=
              (PiLp.norm_apply_le
                (point - (exactPoint : Point3)) (2 : Fin 3)).trans <| by
                simpa [dist_eq_norm] using hexactDistance
            simpa [PiLp.sub_apply, hpointHeight, abs_sub_comm] using hcoordinate
          have hcenterHeight : cleanup.raw.center 2 = subband.anchor := by
            rw [cleanup.raw.center_eq]
            simp [pureWZ2AffineDiagonalCommonCenter, point3,
              exactScale.anchor_midpoint]
          have hsourceDifference :
              source 2 - sourceCenter =
                pureWZ2ExactDiagonalScale band / 100 *
                  ((exactPoint : Point3) 2 - z) := by
            dsimp only [sourceCenter]
            rw [← hsourceMap]
            simp only [pureWZ2AffineDiagonalMapCentered_coord_two]
            rw [show exactScale.affineScale.slopeData.heightScale =
                100 / pureWZ2ExactDiagonalScale band by
              rw [exactScale.affineScale.slopeData.heightScale_eq,
                exactScale.diagonal_scale, exactScale.normalization_hundred],
                hcenterHeight]
            field_simp [hm.ne']
            ring
          have hsourceCenterClose : |source 2 - sourceCenter| ≤ 8 * delta := by
            rw [hsourceDifference, abs_mul,
              abs_of_pos (div_pos hm (by norm_num))]
            calc
              pureWZ2ExactDiagonalScale band / 100 *
                  |(exactPoint : Point3) 2 - z| ≤
                pureWZ2ExactDiagonalScale band / 100 *
                  (exactScale.affineScale.targetDelta * Real.sqrt 3) := by
                    gcongr
              _ = 2 * delta * Real.sqrt 3 := by
                rw [exactScale.affineScale.targetDelta_eq]
                rw [exactScale.affineScale.slopeData.heightScale_eq,
                  exactScale.diagonal_scale, exactScale.normalization_hundred]
                field_simp [hm.ne']
              _ ≤ 8 * delta := by nlinarith
          have hcell : Int.floor (source 2 / delta) ∈ heightCells :=
            pureWZ2_heightCell_mem_centered hdelta hsourceCenterClose
          refine ⟨source, hsourceConfiguration, hcell, ?_⟩
          have hlowerDistance : dist point lowerImage ≤
              exactScale.affineScale.targetDelta *
                pureWZ2ExactDiagonalCubicalRadiusFactor := by
            have himageLower : dist
                (pureWZ2AffineDiagonalMapCentered
                  exactScale.affineScale.slopeData.frameSlope
                  cleanup.raw.center
                  exactScale.affineScale.slopeData.heightScale
                  exactScale.affineScale.slopeData.transverseScale 1 source)
                lowerImage ≤ exactScale.affineScale.targetDelta / 2 := by
              rw [pureWZ2ExactDiagonalMap_replaceHeight_dist
                exactScale cleanup.raw.center source]
              have hheightClose :=
                pureWZ2PaperCellLowerHeight_close hdelta source
              calc
                100 / pureWZ2ExactDiagonalScale band *
                    |source 2 - height| ≤
                  100 / pureWZ2ExactDiagonalScale band * delta := by gcongr
                _ = exactScale.affineScale.targetDelta / 2 := by
                  rw [exactScale.affineScale.targetDelta_eq,
                    exactScale.affineScale.slopeData.heightScale_eq,
                    exactScale.diagonal_scale, exactScale.normalization_hundred]
                  ring
            calc
              dist point lowerImage ≤ dist point (exactPoint : Point3) +
                  dist (exactPoint : Point3) lowerImage := dist_triangle _ _ _
              _ ≤ exactScale.affineScale.targetDelta * Real.sqrt 3 +
                  exactScale.affineScale.targetDelta / 2 := by
                    gcongr
                    simpa [← hsourceMap] using himageLower
              _ = exactScale.affineScale.targetDelta *
                  pureWZ2ExactDiagonalCubicalRadiusFactor := by
                    unfold pureWZ2ExactDiagonalCubicalRadiusFactor
                    ring
          have htargetSlope :
              |pureWZ2ExactDiagonalSlope subband z| ≤
                pureWZ2ExactDiagonalCubicalSlopeBound band :=
            pureWZ2ExactDiagonalSlope_abs_le subband hz
          have hsourceFromTarget : source 2 =
              subband.anchor + pureWZ2ExactDiagonalScale band / 100 *
                (exactPoint : Point3) 2 := by
            rw [← hsourceMap]
            simp only [pureWZ2AffineDiagonalMapCentered_coord_two]
            rw [show exactScale.affineScale.slopeData.heightScale =
                100 / pureWZ2ExactDiagonalScale band by
              rw [exactScale.affineScale.slopeData.heightScale_eq,
                exactScale.diagonal_scale, exactScale.normalization_hundred],
                hcenterHeight]
            field_simp [hm.ne']
            ring
          have hexactSlope :
              pureWZ2ExactDiagonalSlope subband ((exactPoint : Point3) 2) =
                (100 / pureWZ2ExactDiagonalScale band ^ 2) *
                  band.lemma31.data.globalSlope (source 2) := by
            rw [pureWZ2ExactDiagonalSlope_eq_on_core subband
              (PureWZ2ExactDiagonalAffineScaleData.finalExactShading_height_mem_core
                exactScale
                assembly exactPoint.property), ← hsourceFromTarget]
          have hfirstSlope :
              |pureWZ2ExactDiagonalSlope subband z -
                  pureWZ2ExactDiagonalSlope subband ((exactPoint : Point3) 2)| ≤
                2 * exactScale.affineScale.targetDelta * Real.sqrt 3 := by
            have hlip := hslopeLipschitz.dist_le_mul
              z hzTwo ((exactPoint : Point3) 2) hexactHeightTwo
            calc
              |pureWZ2ExactDiagonalSlope subband z -
                  pureWZ2ExactDiagonalSlope subband ((exactPoint : Point3) 2)| ≤
                2 * |z - (exactPoint : Point3) 2| := by
                  simpa [Real.dist_eq] using hlip
              _ ≤ 2 *
                  (exactScale.affineScale.targetDelta * Real.sqrt 3) := by
                    gcongr
                    simpa [abs_sub_comm] using hexactHeightDistance
              _ = 2 * exactScale.affineScale.targetDelta * Real.sqrt 3 := by ring
          have hsourceSlope :
              |band.lemma31.data.globalSlope (source 2) -
                  band.lemma31.data.globalSlope height| ≤ delta := by
            have hlip := hsourceLipschitz.dist_le_mul
              (source 2) hsourceHeight height hlowerHeight
            calc
              |band.lemma31.data.globalSlope (source 2) -
                  band.lemma31.data.globalSlope height| ≤
                |source 2 - height| := by
                  simpa [Real.dist_eq] using hlip
              _ ≤ delta :=
                pureWZ2PaperCellLowerHeight_close hdelta source
          have hsecondSlope :
              |pureWZ2ExactDiagonalSlope subband ((exactPoint : Point3) 2) -
                  (100 / pureWZ2ExactDiagonalScale band ^ 2) *
                    band.lemma31.data.globalSlope height| ≤
                exactScale.affineScale.targetDelta *
                  (1 / (2 * pureWZ2ExactDiagonalScale band)) := by
            rw [hexactSlope, ← mul_sub, abs_mul,
              abs_of_pos (by positivity :
                0 < 100 / pureWZ2ExactDiagonalScale band ^ 2)]
            calc
              100 / pureWZ2ExactDiagonalScale band ^ 2 *
                  |band.lemma31.data.globalSlope (source 2) -
                    band.lemma31.data.globalSlope height| ≤
                100 / pureWZ2ExactDiagonalScale band ^ 2 * delta := by gcongr
              _ = exactScale.affineScale.targetDelta *
                  (1 / (2 * pureWZ2ExactDiagonalScale band)) := by
                rw [exactScale.affineScale.targetDelta_eq,
                  exactScale.affineScale.slopeData.heightScale_eq,
                  exactScale.diagonal_scale, exactScale.normalization_hundred]
                field_simp [hm.ne']
          have hslopeError :
              |pureWZ2ExactDiagonalSlope subband z -
                  (100 / pureWZ2ExactDiagonalScale band ^ 2) *
                    band.lemma31.data.globalSlope height| ≤
                exactScale.affineScale.targetDelta *
                  pureWZ2ExactDiagonalCubicalSlopeErrorFactor band := by
            calc
              _ ≤ |pureWZ2ExactDiagonalSlope subband z -
                    pureWZ2ExactDiagonalSlope subband
                      ((exactPoint : Point3) 2)| +
                  |pureWZ2ExactDiagonalSlope subband
                      ((exactPoint : Point3) 2) -
                    (100 / pureWZ2ExactDiagonalScale band ^ 2) *
                      band.lemma31.data.globalSlope height| :=
                abs_sub_le _ _ _
              _ ≤ 2 * exactScale.affineScale.targetDelta * Real.sqrt 3 +
                  exactScale.affineScale.targetDelta *
                    (1 / (2 * pureWZ2ExactDiagonalScale band)) :=
                add_le_add hfirstSlope hsecondSlope
              _ = exactScale.affineScale.targetDelta *
                  pureWZ2ExactDiagonalCubicalSlopeErrorFactor band := by
                unfold pureWZ2ExactDiagonalCubicalSlopeErrorFactor
                ring
          have hsourcePopular :=
            assembly.finalSourceShading_union_subset_popular hsource
          rcases hsourcePopular with ⟨sourceIndex, hsourcePopular⟩
          rw [popular.popular.restricted_carrier, popular.popular.box_eq]
              at hsourcePopular
          have hsourceY :
              |source 1 - cleanup.raw.center 1| ≤ 1 / 16 := by
            have hy := hsourcePopular.2.1 (1 : Fin 3)
            have hy' : |source 1 - popular.popular.center 1| ≤ 1 / 16 := by
              have hcoord :
                  (point3 (1 / 8 / 2) (1 / 8 / 2) (1 / 8 / 2) : Point3)
                      (1 : Fin 3) = 1 / 16 := by
                simp [point3]
                norm_num
              rw [hcoord] at hy
              exact hy
            rw [cleanup.raw.center_eq]
            simpa [pureWZ2AffineDiagonalCommonCenter, point3, wz1AxisBox]
              using hy'
          have hlowerY : |lowerImage 1| ≤ 1 / 1600 := by
            have htransverse := exactScale.affineScale.transverse_le
            have htransverseNonneg := exactScale.affineScale.transverse_pos.le
            have heq : lowerImage 1 =
                exactScale.affineScale.slopeData.transverseScale *
                  (source 1 - cleanup.raw.center 1) := by
              dsimp only [lowerImage, lowerSource]
              rw [show exactScale.affineScale.slopeData.frameSlope = 0 from
                exactScale.frame_zero]
              simp [pureWZ2AffineDiagonalMapCentered, pureWZ2ReplaceHeight,
                pureWZ2HorizontalNorm, point3]
            rw [heq, abs_mul, abs_of_nonneg htransverseNonneg]
            calc
              exactScale.affineScale.slopeData.transverseScale *
                  |source 1 - cleanup.raw.center 1| ≤
                exactScale.affineScale.slopeData.transverseScale *
                  (1 / 16) := by gcongr
              _ ≤ (1 / 100 : ℝ) * (1 / 16) := by gcongr
              _ = 1 / 1600 := by norm_num
          have hexactProjection :=
            pureWZ2ExactDiagonalMap_projection_replaceHeight
              (height := height) exactScale cleanup.raw.center source
          have hprojection := pureWZ2_globalProjection_dist_le_of_point_slope_error
            point lowerImage
            (pureWZ2ExactDiagonalSlope subband z)
            ((100 / pureWZ2ExactDiagonalScale band ^ 2) *
              band.lemma31.data.globalSlope height)
            (exactScale.affineScale.targetDelta *
              pureWZ2ExactDiagonalCubicalRadiusFactor)
            (exactScale.affineScale.targetDelta *
              pureWZ2ExactDiagonalCubicalSlopeErrorFactor band)
            (pureWZ2ExactDiagonalCubicalSlopeBound band) (1 / 1600)
            (mul_nonneg exactScale.affineScale.targetDelta_pos.le (by
              unfold pureWZ2ExactDiagonalCubicalRadiusFactor
              positivity))
            (mul_nonneg exactScale.affineScale.targetDelta_pos.le (by
              unfold pureWZ2ExactDiagonalCubicalSlopeErrorFactor
              positivity))
            (by unfold pureWZ2ExactDiagonalCubicalSlopeBound; positivity)
            (by norm_num) hlowerDistance htargetSlope hslopeError hlowerY
          rw [hexactProjection] at hprojection
          have hprojectionD :
              dist
                  (inner ℝ point
                    (globalGrainDirection
                      (pureWZ2ExactDiagonalSlope subband z)))
                  (inner ℝ lowerSource
                      (globalGrainDirection
                        (band.lemma31.data.globalSlope height)) -
                    inner ℝ cleanup.raw.center
                      (globalGrainDirection
                        (band.lemma31.data.globalSlope height))) ≤ D := by
            exact hprojection.trans_eq <| by
              dsimp only [D]
              unfold pureWZ2ExactDiagonalCubicalProjectionFactor
              ring
          simpa [offset, height, lowerSource,
            pureWZ2PaperCellLowerHeight, one_mul, sub_eq_add_neg]
            using hprojectionD)
        (by
          dsimp only [D]
          exact mul_pos exactScale.affineScale.targetDelta_pos
            (pureWZ2ExactDiagonalCubicalProjectionFactor_pos band))
  have hratio : D / exactScale.affineScale.targetDelta =
      pureWZ2ExactDiagonalCubicalProjectionFactor band := by
    dsimp only [D]
    field_simp [exactScale.affineScale.targetDelta_pos.ne']
  rw [hratio] at hraw
  simpa [heightCells, pureWZ2CenteredHeightCells_card] using hraw

end PureWZ2AffineDiagonalCleanupQuotientAssemblyData

end Kakeya.Assouad

end
