import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CubicalHeightCells
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicJointLocalGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CoupledIsotropicProjection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CoupledScaleGeometry

/-!
# Global AD on the final isotropic quotient family

This module connects the literal cubical witness of the second quotient to
the finite-slice AD bridge.  Every final point is first returned to the exact
isotropic image by `final_tubeWitness`, then through the exact triangular map
to the original cubical source shading.  The only remaining geometric input
is a pointwise projection-error estimate for that coupled map.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

/-- A Euclidean witness controls the global-grain projection after separating
the spatial displacement from the slope displacement. -/
theorem pureWZ2_globalProjection_dist_le_of_point_slope_error
    (point exactPoint : Point3) (targetSlope exactSlope radius slopeError
      slopeBound pointBound : ℝ)
    (hradius : 0 ≤ radius) (hslopeError : 0 ≤ slopeError)
    (hslopeBound : 0 ≤ slopeBound) (hpointBound : 0 ≤ pointBound)
    (hdist : dist point exactPoint ≤ radius)
    (htargetSlope : |targetSlope| ≤ slopeBound)
    (hslope : |targetSlope - exactSlope| ≤ slopeError)
    (hexactY : |exactPoint 1| ≤ pointBound) :
    dist (inner ℝ point (globalGrainDirection targetSlope))
        (inner ℝ exactPoint (globalGrainDirection exactSlope)) ≤
      (1 + slopeBound) * radius + pointBound * slopeError := by
  have hzero : |point 0 - exactPoint 0| ≤ radius := by
    exact (PiLp.norm_apply_le (point - exactPoint) 0).trans <| by
      simpa [dist_eq_norm] using hdist
  have hone : |point 1 - exactPoint 1| ≤ radius := by
    exact (PiLp.norm_apply_le (point - exactPoint) 1).trans <| by
      simpa [dist_eq_norm] using hdist
  rw [Real.dist_eq]
  have hidentity :
      inner ℝ point (globalGrainDirection targetSlope) -
          inner ℝ exactPoint (globalGrainDirection exactSlope) =
        (point 0 - exactPoint 0) +
          targetSlope * (point 1 - exactPoint 1) +
            (targetSlope - exactSlope) * exactPoint 1 := by
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    ring
  rw [hidentity]
  have hmiddle : |targetSlope| * |point 1 - exactPoint 1| ≤
      slopeBound * radius :=
    mul_le_mul htargetSlope hone (abs_nonneg _) hslopeBound
  have hlast : |targetSlope - exactSlope| * |exactPoint 1| ≤
      slopeError * pointBound :=
    mul_le_mul hslope hexactY (abs_nonneg _) hslopeError
  calc
    |(point 0 - exactPoint 0) +
          targetSlope * (point 1 - exactPoint 1) +
            (targetSlope - exactSlope) * exactPoint 1| ≤
        |point 0 - exactPoint 0| +
          |targetSlope| * |point 1 - exactPoint 1| +
            |targetSlope - exactSlope| * |exactPoint 1| := by
      calc
        _ ≤ |(point 0 - exactPoint 0) +
              targetSlope * (point 1 - exactPoint 1)| +
            |(targetSlope - exactSlope) * exactPoint 1| :=
          abs_add_le _ _
        _ ≤ (|point 0 - exactPoint 0| +
              |targetSlope * (point 1 - exactPoint 1)|) +
            |(targetSlope - exactSlope) * exactPoint 1| :=
          add_le_add_left (abs_add_le _ _) _
        _ = _ := by rw [abs_mul, abs_mul]
    _ ≤ radius + slopeBound * radius + slopeError * pointBound :=
      add_le_add (add_le_add hzero hmiddle) hlast
    _ = (1 + slopeBound) * radius + pointBound * slopeError := by ring

/-- The original source point underlying an exact final-isotropic witness. -/
def PureWZ2FinalIsotropicPreparationData.finalAmbientSourcePoint
    {sourceDelta preDelta finalDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (preparation : PureWZ2FinalIsotropicPreparationData
      (targetDelta := finalDelta) raw.exactShading sourceConstant
      boxScheduleConstant cleanupScheduleConstant boxLevelCount
      cleanupLevelCount scale)
    (point : {point : Point3 // point ∈
      pureWZ2IsotropicMap preparation.box.popular.center scale ''
        preparation.exactRestricted}) :
    {point : Point3 // point ∈ sourceShading.union} :=
  raw.exactSourcePoint
    ⟨pureWZ2IsotropicInverse preparation.box.popular.center scale point,
      preparation.exactRestricted_subset <|
        (pureWZ2IsotropicExactSourcePoint preparation.box.popular.center
          (lt_of_lt_of_le (by norm_num) preparation.scale_one) point).property⟩

/-- The exact final-isotropic witness is literally the coupled image of its
canonical ambient source point. -/
theorem PureWZ2FinalIsotropicPreparationData.coupledMap_finalAmbientSourcePoint
    {sourceDelta preDelta finalDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (preparation : PureWZ2FinalIsotropicPreparationData
      (targetDelta := finalDelta) raw.exactShading sourceConstant
      boxScheduleConstant cleanupScheduleConstant boxLevelCount
      cleanupLevelCount scale)
    (point : {point : Point3 // point ∈
      pureWZ2IsotropicMap preparation.box.popular.center scale ''
        preparation.exactRestricted}) :
    pureWZ2CoupledIsotropicMap g c d m anisotropicCenter
        preparation.box.popular.center scale
        (preparation.finalAmbientSourcePoint point) = point := by
  unfold pureWZ2CoupledIsotropicMap
  change pureWZ2IsotropicMap preparation.box.popular.center scale
      (anisotropicCenteredRescalingMap g c d m anisotropicCenter
        (raw.exactSourcePoint _)) = point
  rw [raw.map_exactSourcePoint]
  exact pureWZ2IsotropicMap_inverse preparation.box.popular.center
    (lt_of_lt_of_le (by norm_num) preparation.scale_one) point

/-- The final source box meets only a fixed number of original height cells.
The pre-isotropic box has width at most one pre-isotropic grid scale, while
the reciprocal-grid triangular scale converts that width back to at most
eight original grid scales. -/
theorem PureWZ2FinalIsotropicPreparationData.finalAmbientSourcePoint_height_close
    {sigma epsilon delta finalDelta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {anisotropicCenter : Point3}
    {m : ℝ} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := anisotropicPaperAlignedScale delta
        subband.left subband.right) sourceFamily sourceShading
        band.lemma31.data.globalSlope anisotropicCenter subband.ordered hm}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (preparation : PureWZ2FinalIsotropicPreparationData
      (targetDelta := finalDelta) raw.exactShading sourceConstant
      boxScheduleConstant cleanupScheduleConstant boxLevelCount
      cleanupLevelCount scale)
    (point : {point : Point3 // point ∈
      pureWZ2IsotropicMap preparation.box.popular.center scale ''
        preparation.exactRestricted}) :
    |(preparation.finalAmbientSourcePoint point : Point3) 2 -
        pureWZ2CoupledSourceHeight subband
          (preparation.box.popular.center 2)| ≤ 8 * delta := by
  let prePoint := pureWZ2IsotropicExactSourcePoint
    preparation.box.popular.center
      (lt_of_lt_of_le (by norm_num) preparation.scale_one) point
  have hpreSelected : (prePoint : Point3) ∈
      preparation.box.selectedShading.union :=
    restrictPaperShading_union_subset preparation.cleanupRegularized.selected
      preparation.box.selectedShading prePoint.property
  have hpreClose :
      |(prePoint : Point3) 2 - preparation.box.popular.center 2| ≤
        anisotropicPaperAlignedScale delta subband.left subband.right / 2 :=
    preparation.box.selectedShading_height_close hpreSelected
  let ambientPre : {point : Point3 // point ∈ raw.exactShading.union} :=
    ⟨prePoint, preparation.exactRestricted_subset prePoint.property⟩
  have hmap := congrArg (fun target : Point3 => target 2)
    (raw.map_exactSourcePoint ambientPre)
  have hsourceFormula :
      (preparation.finalAmbientSourcePoint point : Point3) 2 =
        subband.left + (subband.right - subband.left) / 2 *
          ((prePoint : Point3) 2 + 1) := by
    have heq : (preparation.finalAmbientSourcePoint point : Point3) =
        raw.exactSourcePoint ambientPre := by
      rfl
    rw [heq]
    simp only [anisotropicCenteredRescalingMap, PiLp.sub_apply, point3_coord2]
      at hmap
    rw [(anisotropicRescalingMap_coord
      band.lemma31.data.globalSlope subband.left subband.right m
        (raw.exactSourcePoint ambientPre : Point3)).2.2] at hmap
    change (preparation.finalAmbientSourcePoint point : Point3) 2 = _
    rw [heq]
    have hlength : subband.right - subband.left ≠ 0 :=
      sub_ne_zero.mpr subband.ordered.ne'
    field_simp [hlength] at hmap ⊢
    linarith
  have hcenterFormula :
      pureWZ2CoupledSourceHeight subband
          (preparation.box.popular.center 2) =
        subband.left + (subband.right - subband.left) / 2 *
          (preparation.box.popular.center 2 + 1) := rfl
  rw [hsourceFormula, hcenterFormula]
  have hlengthPos : 0 < subband.right - subband.left :=
    sub_pos.mpr subband.ordered
  have hfactorNonnegative : 0 ≤ (subband.right - subband.left) / 2 :=
    (div_pos hlengthPos (by norm_num)).le
  rw [show
      subband.left + (subband.right - subband.left) / 2 *
            ((prePoint : Point3) 2 + 1) -
          (subband.left + (subband.right - subband.left) / 2 *
            (preparation.box.popular.center 2 + 1)) =
        (subband.right - subband.left) / 2 *
          ((prePoint : Point3) 2 - preparation.box.popular.center 2) by ring,
    abs_mul, abs_of_nonneg hfactorNonnegative]
  calc
    (subband.right - subband.left) / 2 *
          |(prePoint : Point3) 2 - preparation.box.popular.center 2| ≤
        (subband.right - subband.left) / 2 *
          (anisotropicPaperAlignedScale delta subband.left subband.right / 2) := by
      gcongr
    _ ≤ (subband.right - subband.left) / 2 *
          ((2 * anisotropicPaperRawScale delta
            subband.left subband.right) / 2) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right
          ((anisotropicPaperAlignedScale_lt_two_mul_raw
            subband.anisotropic_rawScale_pos
              subband.anisotropic_rawScale_le_half).le) (by norm_num))
        hfactorNonnegative
    _ = 8 * delta := by
      unfold anisotropicPaperRawScale
      field_simp [sub_ne_zero.mpr subband.ordered.ne']
      ring
    _ ≤ 8 * delta := le_rfl

/-- The exact source points underlying the final quotient occupy a nonempty
set of at most seventeen legal original height cells. -/
theorem PureWZ2IsotropicCleanupQuotientAssemblyData.final_source_height_cells
    {sigma epsilon delta finalDelta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {anisotropicCenter : Point3}
    {m : ℝ} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := anisotropicPaperAlignedScale delta
        subband.left subband.right) sourceFamily sourceShading
        band.lemma31.data.globalSlope anisotropicCenter subband.ordered hm}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant
      sourceScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount parentLevelCount : ℕ} {scale : ℝ}
    {preparation : PureWZ2FinalIsotropicPreparationData
      (targetDelta := finalDelta) raw.exactShading sourceConstant
      boxScheduleConstant cleanupScheduleConstant boxLevelCount
      cleanupLevelCount scale}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData
      preparation.cleanupRegularized sourceScheduleConstant parentLevelCount)
    (hsourceCubical : WZ1PaperIsCubicalShading ambientShading)
    (hrawSource : sourceShading.union ⊆ ambientShading.union) :
    let cells := pureWZ2LocalPaperHeightCells delta
      (pureWZ2CoupledSourceHeight subband
        (preparation.box.popular.center 2))
    cells.Nonempty ∧ cells.card ≤ 17 ∧
      (∀ cell ∈ cells,
        (cell : ℝ) * delta ∈ Set.Icc (-1 : ℝ) 1) ∧
      ∀ exactPoint : {point : Point3 // point ∈
          pureWZ2IsotropicMap preparation.box.popular.center scale ''
            preparation.exactRestricted},
        Int.floor
          (((preparation.finalAmbientSourcePoint exactPoint : Point3) 2) /
            delta) ∈ cells := by
  dsimp only
  have hdelta : 0 < delta := band.lemma31.data.cfg.extremal.delta_pos
  have hcell : ∀ exactPoint : {point : Point3 // point ∈
        pureWZ2IsotropicMap preparation.box.popular.center scale ''
          preparation.exactRestricted},
      Int.floor
        (((preparation.finalAmbientSourcePoint exactPoint : Point3) 2) /
          delta) ∈
        pureWZ2LocalPaperHeightCells delta
          (pureWZ2CoupledSourceHeight subband
            (preparation.box.popular.center 2)) := by
    intro exactPoint
    exact hsourceCubical.heightCell_mem_local hdelta
      (hrawSource (preparation.finalAmbientSourcePoint exactPoint).property)
      (preparation.finalAmbientSourcePoint_height_close subband exactPoint)
  have hunion : assembly.finalShading.union.Nonempty := by
    let index : Fin (assembly.quotient.jointlyRegularizedFine
        (pureWZ2IsotropicCleanupJointWeight preparation.cleanupRegularized)
        assembly.selection assembly.joint.selected).family.card :=
      ⟨0, assembly.final_family_nonempty⟩
    have hpositive : 0 < MeasureTheory.volume
        (assembly.finalShading.carrier index) := by
      rw [assembly.finalShading_carrier, ←
        preparation.cleanupRegularized.selected_sourceWeight_eq_finalShading_volume]
      exact preparation.cleanupRegularized.selected_weight_pos _
    rcases nonempty_of_measure_ne_zero hpositive.ne' with ⟨point, hpoint⟩
    exact ⟨point, index, hpoint⟩
  rcases hunion with ⟨point, index, hpoint⟩
  rcases assembly.final_tubeWitness index point hpoint with
    ⟨exactPoint, _hexactDistance, _hexactCarrier⟩
  exact ⟨⟨_, hcell exactPoint⟩,
    pureWZ2LocalPaperHeightCells_card_le _ _,
    fun _ hmem => pureWZ2LocalPaperHeightCells_height_mem hdelta hmem, hcell⟩

/-- In particular the exact coupled witness has uniformly tiny target
horizontal coordinates. -/
theorem PureWZ2FinalIsotropicPreparationData.exactWitness_y_abs_le
    {sourceDelta preDelta finalDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (preparation : PureWZ2FinalIsotropicPreparationData
      (targetDelta := finalDelta) raw.exactShading sourceConstant
      boxScheduleConstant cleanupScheduleConstant boxLevelCount
      cleanupLevelCount scale)
    (point : {point : Point3 // point ∈
      pureWZ2IsotropicMap preparation.box.popular.center scale ''
        preparation.exactRestricted}) :
    |(point : Point3) 1| ≤ Real.sqrt 3 / 200 := by
  have hrestrictedSelected : preparation.exactRestricted ⊆
      preparation.box.selectedShading.union :=
    restrictPaperShading_union_subset preparation.cleanupRegularized.selected
      preparation.box.selectedShading
  exact (PiLp.norm_apply_le (point : Point3) 1).trans <|
    preparation.box.isotropicSelectedImage_norm_le preparation.scale_one
      preparation.scale_source_small
      ⟨point, Set.image_mono hrestrictedSelected point.property⟩

/-- The exact coupled witness and the image of the lower face of its ambient
source height cell are separated only in the vertical coordinate. -/
theorem PureWZ2FinalIsotropicPreparationData.exactWitness_lowerCell_dist
    {sourceDelta preDelta finalDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (preparation : PureWZ2FinalIsotropicPreparationData
      (targetDelta := finalDelta) raw.exactShading sourceConstant
      boxScheduleConstant cleanupScheduleConstant boxLevelCount
      cleanupLevelCount scale)
    (hsourceDelta : 0 < sourceDelta)
    (point : {point : Point3 // point ∈
      pureWZ2IsotropicMap preparation.box.popular.center scale ''
        preparation.exactRestricted}) :
    dist (point : Point3)
        (pureWZ2CoupledIsotropicMap g c d m anisotropicCenter
          preparation.box.popular.center scale
          (pureWZ2ReplaceHeight (preparation.finalAmbientSourcePoint point)
            (pureWZ2PaperCellLowerHeight sourceDelta
              (preparation.finalAmbientSourcePoint point)))) ≤
      scale * (2 / (d - c)) * sourceDelta := by
  rw [← preparation.coupledMap_finalAmbientSourcePoint point]
  rw [pureWZ2CoupledIsotropicMap_replaceHeight_dist g hcd
    (lt_of_lt_of_le (by norm_num) preparation.scale_one)]
  exact mul_le_mul_of_nonneg_left
    (pureWZ2PaperCellLowerHeight_close hsourceDelta _)
    (mul_nonneg
      (lt_of_lt_of_le (by norm_num) preparation.scale_one).le
      (by positivity))

/-- With the canonical coupled parameter `m = slopeScale / scale`, the
projection formula's combined exact slope is definitionally the exact
coupled slope at the same target height. -/
theorem pureWZ2CombinedExactSlope_eq_coupled
    {sigma epsilon delta t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (isotropicCenter : Point3) :
    pureWZ2CombinedExactSlope band.lemma31.data.globalSlope
        subband.left subband.right
        (pureWZ2CoupledFinalSlopeScale subband)
        isotropicCenter (pureWZ2CoupledFinalScale subband) t =
      pureWZ2CoupledExactSlope subband (isotropicCenter 2)
        (pureWZ2CoupledFinalScale subband) t := by
  simp only [pureWZ2CombinedExactSlope, pureWZ2CoupledExactSlope,
    pureWZ2CoupledFinalSlopeScale]

/-- Canonical pointwise slope comparison for the final quotient.  Cubical
movement, lowering the original source point to its height-cell face, and
the global Taylor remainder together cost at most five final radii. -/
theorem PureWZ2FinalIsotropicPreparationData.canonical_coupled_slope_error
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (scaleData : PureWZ2CoupledScaleData subband)
    {sourceFamily ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {anisotropicCenter : Point3}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := anisotropicPaperAlignedScale delta
        subband.left subband.right) sourceFamily sourceShading
        band.lemma31.data.globalSlope anisotropicCenter subband.ordered
          scaleData.m_pos}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ}
    (preparation : PureWZ2FinalIsotropicPreparationData
      (targetDelta := pureWZ2CoupledFinalDelta subband) raw.exactShading
      sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount (pureWZ2CoupledFinalScale subband))
    (hsourceCubical : WZ1PaperIsCubicalShading ambientShading)
    (hrawSource : sourceShading.union ⊆ ambientShading.union)
    (point : Point3) (index)
    (_hpoint : point ∈
      preparation.cleanupRegularized.isotropicCleanupFinalShading.carrier
        index)
    (exactPoint : {point : Point3 // point ∈
      pureWZ2IsotropicMap preparation.box.popular.center
          (pureWZ2CoupledFinalScale subband) ''
        preparation.exactRestricted})
    (hexactDistance : dist point (exactPoint : Point3) ≤
      pureWZ2CoupledFinalDelta subband * Real.sqrt 3) :
    let source := preparation.finalAmbientSourcePoint exactPoint
    let height := pureWZ2PaperCellLowerHeight delta source
    let targetHeight := pureWZ2CoupledTargetHeight subband.left subband.right
      preparation.box.popular.center (pureWZ2CoupledFinalScale subband) height
    |pureWZ2CoupledAffineSlope subband
          (preparation.box.popular.center 2)
          (pureWZ2CoupledFinalScale subband) (point 2) -
        pureWZ2CombinedExactSlope band.lemma31.data.globalSlope
          subband.left subband.right (pureWZ2CoupledFinalSlopeScale subband)
          preparation.box.popular.center
          (pureWZ2CoupledFinalScale subband) targetHeight| ≤
      5 * pureWZ2CoupledFinalDelta subband := by
  dsimp only
  let source := preparation.finalAmbientSourcePoint exactPoint
  let height := pureWZ2PaperCellLowerHeight delta source
  let targetHeight := pureWZ2CoupledTargetHeight subband.left subband.right
    preparation.box.popular.center (pureWZ2CoupledFinalScale subband) height
  let lowerImage := pureWZ2CoupledIsotropicMap
    band.lemma31.data.globalSlope subband.left subband.right
      (pureWZ2CoupledFinalSlopeScale subband) anisotropicCenter
      preparation.box.popular.center (pureWZ2CoupledFinalScale subband)
      (pureWZ2ReplaceHeight source height)
  have hcenterSubband : pureWZ2CoupledSourceHeight subband
      (preparation.box.popular.center 2) ∈
        Set.Icc subband.left subband.right :=
    pureWZ2CoupledSourceHeight_mem subband
      (abs_le.mp preparation.center_height_bound)
  have hcenterUnit : pureWZ2CoupledSourceHeight subband
      (preparation.box.popular.center 2) ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ⟨band.lemma31.data.scaleData.slabLeft_mem.trans
        (band.left_mem.trans (subband.left_mem.trans hcenterSubband.1)),
      (hcenterSubband.2.trans subband.right_mem).trans
        (band.right_mem.trans band.lemma31.data.scaleData.slabRight_mem)⟩
  have hheightUnit : height ∈ Set.Icc (-1 : ℝ) 1 := by
    have hcell := hsourceCubical.heightCell_mem
      band.lemma31.data.cfg.extremal.delta_pos (hrawSource source.property)
    exact pureWZ2PaperHeightCells_height_mem
      band.lemma31.data.cfg.extremal.delta_pos hcell
  have htargetSource : pureWZ2CoupledSourceHeight subband
      (preparation.box.popular.center 2 +
        targetHeight / pureWZ2CoupledFinalScale subband) = height := by
    dsimp only [targetHeight, pureWZ2CoupledTargetHeight,
      pureWZ2CoupledSourceHeight]
    field_simp [scaleData.lambda_pos.ne',
      sub_ne_zero.mpr subband.ordered.ne']
    ring
  have htargetUnit : pureWZ2CoupledSourceHeight subband
      (preparation.box.popular.center 2 +
        targetHeight / pureWZ2CoupledFinalScale subband) ∈
        Set.Icc (-1 : ℝ) 1 := by
    rwa [htargetSource]
  have hrestrictedSelected : preparation.exactRestricted ⊆
      preparation.box.selectedShading.union :=
    restrictPaperShading_union_subset preparation.cleanupRegularized.selected
      preparation.box.selectedShading
  have hexactHeightRaw :=
    preparation.box.isotropicSelectedImage_height_abs_le
      preparation.scale_one
      ⟨exactPoint, Set.image_mono hrestrictedSelected exactPoint.property⟩
  have hexactHeight : |(exactPoint : Point3) 2| ≤
      pureWZ2CoupledFinalDelta subband / 32 :=
    hexactHeightRaw.trans scaleData.isotropic_exact_height_budget
  have hlowerDistance : dist (exactPoint : Point3) lowerImage ≤
      pureWZ2CoupledFinalDelta subband / 128 := by
    exact (preparation.exactWitness_lowerCell_dist
      band.lemma31.data.cfg.extremal.delta_pos exactPoint).trans
        scaleData.lower_cell_image_budget
  have hlowerCoordinate :
      |(exactPoint : Point3) 2 - lowerImage 2| ≤
        pureWZ2CoupledFinalDelta subband / 128 := by
    exact (PiLp.norm_apply_le ((exactPoint : Point3) - lowerImage) 2).trans <| by
      simpa [dist_eq_norm] using hlowerDistance
  have hlowerHeight : lowerImage 2 = targetHeight := by
    exact pureWZ2CoupledIsotropicMap_replaceHeight_coord_two
      band.lemma31.data.globalSlope subband.left subband.right
      (pureWZ2CoupledFinalSlopeScale subband) anisotropicCenter
      preparation.box.popular.center source
      (pureWZ2CoupledFinalScale subband) height
  rw [hlowerHeight] at hlowerCoordinate
  have htargetAbs : |targetHeight| ≤
      (5 / 128 : ℝ) * pureWZ2CoupledFinalDelta subband := by
    calc
      |targetHeight| = |(exactPoint : Point3) 2 +
          (targetHeight - (exactPoint : Point3) 2)| := by ring_nf
      _ ≤ |(exactPoint : Point3) 2| +
          |targetHeight - (exactPoint : Point3) 2| := abs_add_le _ _
      _ ≤ pureWZ2CoupledFinalDelta subband / 32 +
          pureWZ2CoupledFinalDelta subband / 128 := by
        gcongr
        simpa [abs_sub_comm] using hlowerCoordinate
      _ = (5 / 128 : ℝ) * pureWZ2CoupledFinalDelta subband := by ring
  have hpointCoordinate :
      |point 2 - (exactPoint : Point3) 2| ≤
        pureWZ2CoupledFinalDelta subband * Real.sqrt 3 := by
    exact (PiLp.norm_apply_le (point - (exactPoint : Point3)) 2).trans <| by
      simpa [dist_eq_norm] using hexactDistance
  have hpointTarget : |point 2 - targetHeight| ≤
      pureWZ2CoupledFinalDelta subband * Real.sqrt 3 +
        pureWZ2CoupledFinalDelta subband / 128 := by
    exact (abs_sub_le (point 2) ((exactPoint : Point3) 2) targetHeight).trans
      (add_le_add hpointCoordinate hlowerCoordinate)
  have haffine := pureWZ2CoupledAffineSlope_sub_le
    (lambda := pureWZ2CoupledFinalScale subband) subband hcenterSubband
    (s := point 2) (t := targetHeight)
  have haffineBound :
      |pureWZ2CoupledAffineSlope subband
            (preparation.box.popular.center 2)
            (pureWZ2CoupledFinalScale subband) (point 2) -
          pureWZ2CoupledAffineSlope subband
            (preparation.box.popular.center 2)
            (pureWZ2CoupledFinalScale subband) targetHeight| ≤
        2 * (pureWZ2CoupledFinalDelta subband * Real.sqrt 3 +
          pureWZ2CoupledFinalDelta subband / 128) :=
    haffine.trans (mul_le_mul_of_nonneg_left hpointTarget (by norm_num))
  have htaylor := pureWZ2CoupledExactSlope_close_affine_on_unit
    subband scaleData.lambda_pos hcenterUnit htargetUnit
  have htargetSq : targetHeight ^ 2 ≤
      ((5 / 128 : ℝ) * pureWZ2CoupledFinalDelta subband) ^ 2 := by
    rw [← sq_abs targetHeight]
    nlinarith [abs_nonneg targetHeight, htargetAbs]
  have htaylorSmall : targetHeight ^ 2 /
        (18000 * pureWZ2CoupledFinalScale subband) ≤
      pureWZ2CoupledFinalDelta subband / 1000 := by
    have hdenominator : (18000 : ℝ) ≤
        18000 * pureWZ2CoupledFinalScale subband := by
      nlinarith [scaleData.lambda_one]
    calc
      targetHeight ^ 2 / (18000 * pureWZ2CoupledFinalScale subband) ≤
          targetHeight ^ 2 / 18000 := by
            exact div_le_div_of_nonneg_left (sq_nonneg targetHeight)
              (by norm_num) hdenominator
      _ ≤ (((5 / 128 : ℝ) * pureWZ2CoupledFinalDelta subband) ^ 2) /
          18000 := by gcongr
      _ ≤ pureWZ2CoupledFinalDelta subband / 1000 := by
        have hdeltaSq : pureWZ2CoupledFinalDelta subband ^ 2 ≤
            pureWZ2CoupledFinalDelta subband / 24 := by
          nlinarith [scaleData.final_delta_pos,
            scaleData.final_delta_le_twenty_four]
        nlinarith
  have htaylorBound :
      |pureWZ2CoupledAffineSlope subband
            (preparation.box.popular.center 2)
            (pureWZ2CoupledFinalScale subband) targetHeight -
          pureWZ2CoupledExactSlope subband
            (preparation.box.popular.center 2)
            (pureWZ2CoupledFinalScale subband) targetHeight| ≤
        pureWZ2CoupledFinalDelta subband / 1000 := by
    simpa [abs_sub_comm] using htaylor.trans htaylorSmall
  rw [pureWZ2CombinedExactSlope_eq_coupled subband
    preparation.box.popular.center]
  have htriangle := abs_sub_le
    (pureWZ2CoupledAffineSlope subband
      (preparation.box.popular.center 2)
      (pureWZ2CoupledFinalScale subband) (point 2))
    (pureWZ2CoupledAffineSlope subband
      (preparation.box.popular.center 2)
      (pureWZ2CoupledFinalScale subband) targetHeight)
    (pureWZ2CoupledExactSlope subband
      (preparation.box.popular.center 2)
      (pureWZ2CoupledFinalScale subband) targetHeight)
  calc
    _ ≤ 2 * (pureWZ2CoupledFinalDelta subband * Real.sqrt 3 +
          pureWZ2CoupledFinalDelta subband / 128) +
        pureWZ2CoupledFinalDelta subband / 1000 :=
      htriangle.trans (add_le_add haffineBound htaylorBound)
    _ ≤ 5 * pureWZ2CoupledFinalDelta subband := by
      have hsqrt : Real.sqrt 3 ≤ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
          Real.sqrt_nonneg 3]
      nlinarith [scaleData.final_delta_pos]

/-- Concrete projection comparison for the canonical coupled slope.  It
combines final cubical witness error, movement to the lower source-cell face,
and the exact affine projection identity at that face. -/
theorem PureWZ2FinalIsotropicPreparationData.coupledProjection_lowerCell_bound
    {sourceDelta preDelta finalDelta sigma epsilon delta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading
        band.lemma31.data.globalSlope anisotropicCenter hcd hm}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ}
    {scale slopeBound slopeError : ℝ}
    (preparation : PureWZ2FinalIsotropicPreparationData
      (targetDelta := finalDelta) raw.exactShading sourceConstant
      boxScheduleConstant cleanupScheduleConstant boxLevelCount
      cleanupLevelCount scale)
    (hsourceDelta : 0 < sourceDelta)
    (hslopeBound : 0 ≤ slopeBound)
    (hslopeErrorNonnegative : 0 ≤ slopeError)
    (htargetSlope : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |pureWZ2CoupledAffineSlope subband (preparation.box.popular.center 2)
        scale z| ≤ slopeBound)
    (hslopeError : ∀ point : Point3, ∀ index,
      point ∈
          preparation.cleanupRegularized.isotropicCleanupFinalShading.carrier
            index →
      ∀ exactPoint : {point : Point3 // point ∈
        pureWZ2IsotropicMap preparation.box.popular.center scale ''
          preparation.exactRestricted},
      dist point (exactPoint : Point3) ≤ finalDelta * Real.sqrt 3 →
      let source := preparation.finalAmbientSourcePoint exactPoint
      let height := pureWZ2PaperCellLowerHeight sourceDelta source
      let targetHeight := pureWZ2CoupledTargetHeight c d
        preparation.box.popular.center scale height
      |pureWZ2CoupledAffineSlope subband (preparation.box.popular.center 2)
          scale (point 2) -
        pureWZ2CombinedExactSlope band.lemma31.data.globalSlope c d m
          preparation.box.popular.center scale targetHeight| ≤
        slopeError)
    (index) (point : Point3)
    (hpoint : point ∈
      (preparation.cleanupRegularized.isotropicCleanupFinalShading).carrier
        index)
    (exactPoint : {point : Point3 // point ∈
      pureWZ2IsotropicMap preparation.box.popular.center scale ''
        preparation.exactRestricted})
    (hexactDistance : dist point (exactPoint : Point3) ≤
      finalDelta * Real.sqrt 3) :
    let source := preparation.finalAmbientSourcePoint exactPoint
    let height := pureWZ2PaperCellLowerHeight sourceDelta source
    let targetHeight := pureWZ2CoupledTargetHeight c d
      preparation.box.popular.center scale height
    dist
      (inner ℝ point
        (globalGrainDirection
          (pureWZ2CoupledAffineSlope subband
            (preparation.box.popular.center 2) scale (point 2))))
      (scale * inner ℝ (pureWZ2ReplaceHeight source height)
          (globalGrainDirection (band.lemma31.data.globalSlope height)) +
        pureWZ2CoupledProjectionOffset band.lemma31.data.globalSlope
          c d m anisotropicCenter preparation.box.popular.center
          scale targetHeight) ≤
      (1 + slopeBound) *
          (finalDelta * Real.sqrt 3 +
            scale * (2 / (d - c)) * sourceDelta) +
        (Real.sqrt 3 / 200) * slopeError := by
  dsimp only
  let source := preparation.finalAmbientSourcePoint exactPoint
  let height := pureWZ2PaperCellLowerHeight sourceDelta source
  let targetHeight := pureWZ2CoupledTargetHeight c d
    preparation.box.popular.center scale height
  let lowerImage := pureWZ2CoupledIsotropicMap
    band.lemma31.data.globalSlope c d m anisotropicCenter
      preparation.box.popular.center scale
      (pureWZ2ReplaceHeight source height)
  have hlowerDistance : dist point lowerImage ≤
      finalDelta * Real.sqrt 3 + scale * (2 / (d - c)) * sourceDelta := by
    calc
      dist point lowerImage ≤ dist point (exactPoint : Point3) +
          dist (exactPoint : Point3) lowerImage := dist_triangle _ _ _
      _ ≤ finalDelta * Real.sqrt 3 +
          scale * (2 / (d - c)) * sourceDelta := by
        gcongr
        exact preparation.exactWitness_lowerCell_dist hsourceDelta exactPoint
  have hlowerY : lowerImage 1 = (exactPoint : Point3) 1 := by
    rw [← preparation.coupledMap_finalAmbientSourcePoint exactPoint]
    simp [lowerImage, pureWZ2CoupledIsotropicMap, pureWZ2IsotropicMap,
      anisotropicCenteredRescalingMap, anisotropicRescalingMap,
      pureWZ2ReplaceHeight, point3, source, height]
  have hexactProjection :=
    pureWZ2CoupledIsotropic_projection_replaceHeight
      band.lemma31.data.globalSlope hcd hm
      (lt_of_lt_of_le (by norm_num) preparation.scale_one)
      anisotropicCenter preparation.box.popular.center source height
  have hbound := pureWZ2_globalProjection_dist_le_of_point_slope_error
    point lowerImage
      (pureWZ2CoupledAffineSlope subband (preparation.box.popular.center 2)
        scale (point 2))
      (pureWZ2CombinedExactSlope band.lemma31.data.globalSlope c d m
        preparation.box.popular.center scale targetHeight)
      (finalDelta * Real.sqrt 3 +
        scale * (2 / (d - c)) * sourceDelta)
      slopeError slopeBound (Real.sqrt 3 / 200)
      (add_nonneg
        (mul_nonneg preparation.target_delta_pos.le (Real.sqrt_nonneg 3))
        (mul_nonneg
          (mul_nonneg
            (lt_of_lt_of_le (by norm_num) preparation.scale_one).le
            (by positivity)) hsourceDelta.le))
      hslopeErrorNonnegative hslopeBound (by positivity)
      hlowerDistance (by
        apply htargetSlope
        have hbox := preparation.cleanupRegularized.isotropicCleanupFinalShading
          |>.subset_body index hpoint |>.2
        exact abs_le.mp <| by
          simpa [Kakeya.Streamlined.axisBox] using hbox.2.2)
      (hslopeError point index hpoint exactPoint hexactDistance)
      (by rw [hlowerY]; exact preparation.exactWitness_y_abs_le exactPoint)
  rw [hexactProjection] at hbound
  simpa [lowerImage, source, height, targetHeight] using hbound

/-- Fully concrete finite-slice global-AD transfer for the coupled affine
slope.  The source cubicality and AD may come from a larger ambient shading;
only the actual raw source points need to lie in that ambient union. -/
theorem PureWZ2IsotropicCleanupQuotientAssemblyData.toCoupledAffineGlobalAD
    {sourceDelta preDelta finalDelta sigma epsilon delta c d m : ℝ}
    {rawSourceFamily ambientFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {rawSourceShading : WZ1PaperTubeShading rawSourceFamily}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) rawSourceFamily rawSourceShading
        band.lemma31.data.globalSlope anisotropicCenter hcd hm}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant
      sourceScheduleConstant C targetConstant : ENNReal}
    {boxLevelCount cleanupLevelCount parentLevelCount : ℕ}
    {scale slopeBound slopeError D : ℝ}
    {preparation : PureWZ2FinalIsotropicPreparationData
      (targetDelta := finalDelta) raw.exactShading sourceConstant
      boxScheduleConstant cleanupScheduleConstant boxLevelCount
      cleanupLevelCount scale}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData
      preparation.cleanupRegularized sourceScheduleConstant parentLevelCount)
    (sourceGlobal : PureWZ2C2GlobalGrainData ambientShading sigma C)
    (hsourceCubical : WZ1PaperIsCubicalShading ambientShading)
    (hrawSource : rawSourceShading.union ⊆ ambientShading.union)
    (heightCells : Finset ℤ)
    (hheightCells : heightCells.Nonempty)
    (hcellHeight : ∀ cell ∈ heightCells,
      (cell : ℝ) * sourceDelta ∈ Set.Icc (-1 : ℝ) 1)
    (hsourceCell : ∀ exactPoint : {point : Point3 // point ∈
        pureWZ2IsotropicMap preparation.box.popular.center scale ''
          preparation.exactRestricted},
      Int.floor (((preparation.finalAmbientSourcePoint exactPoint : Point3) 2) /
        sourceDelta) ∈ heightCells)
    (hsourceSlope : (band.lemma31.data.globalSlope : ℝ → ℝ) =
      sourceGlobal.slope)
    (hscaleSource : scale * sourceDelta ≤ finalDelta)
    (hslopeBound : 0 ≤ slopeBound)
    (htargetSlope : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |pureWZ2CoupledAffineSlope subband (preparation.box.popular.center 2)
        scale z| ≤ slopeBound)
    (hslopeErrorNonnegative : 0 ≤ slopeError)
    (hslopeError : ∀ point : Point3, ∀ index,
      point ∈
          preparation.cleanupRegularized.isotropicCleanupFinalShading.carrier
            index →
      ∀ exactPoint : {point : Point3 // point ∈
          pureWZ2IsotropicMap preparation.box.popular.center scale ''
            preparation.exactRestricted},
      dist point (exactPoint : Point3) ≤ finalDelta * Real.sqrt 3 →
      let source := preparation.finalAmbientSourcePoint exactPoint
      let height := pureWZ2PaperCellLowerHeight sourceDelta source
      let targetHeight := pureWZ2CoupledTargetHeight c d
        preparation.box.popular.center scale height
      |pureWZ2CoupledAffineSlope subband (preparation.box.popular.center 2)
          scale (point 2) -
        pureWZ2CombinedExactSlope band.lemma31.data.globalSlope c d m
          preparation.box.popular.center scale targetHeight| ≤ slopeError)
    (hD :
      (1 + slopeBound) *
          (finalDelta * Real.sqrt 3 +
            scale * (2 / (d - c)) * sourceDelta) +
        (Real.sqrt 3 / 200) * slopeError ≤ D)
    (hDPos : 0 < D)
    (hconstant :
      (2 * (Nat.ceil (D / finalDelta) + 1) : ENNReal) ^ 3 *
          ((heightCells.card : ENNReal) * C) ≤
        targetConstant)
    (htargetOne : 1 ≤ targetConstant) (htargetTop : targetConstant ≠ ⊤) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection
            (pureWZ2CoupledAffineSlope subband
              (preparation.box.popular.center 2) scale z))
          (horizontalSlice assembly.finalShading.union z))
        finalDelta (1 - sigma) targetConstant := by
  have hsourceDelta : 0 < sourceDelta :=
    (sourceGlobal.global_ad_slope 0 (by constructor <;> norm_num)).1
  let offset : ℤ → ℝ := fun cell =>
    pureWZ2CoupledProjectionOffset band.lemma31.data.globalSlope c d m
      anisotropicCenter preparation.box.popular.center scale
        (pureWZ2CoupledTargetHeight c d preparation.box.popular.center scale
          ((cell : ℝ) * sourceDelta))
  intro z _hz
  have hrawAD : PureWZ2PaperADSet1
      (scalarProjection
        (globalGrainDirection
          (pureWZ2CoupledAffineSlope subband
            (preparation.box.popular.center 2) scale z))
        (horizontalSlice assembly.finalShading.union z))
      finalDelta (1 - sigma)
        ((2 * (Nat.ceil (D / finalDelta) + 1) : ENNReal) ^ 3 *
          ((heightCells.card : ENNReal) * C)) := by
    apply hsourceCubical.targetProjection_ad_of_source_witness_indexed
      hsourceDelta preparation.target_delta_pos sourceGlobal.slope
      heightCells hheightCells hcellHeight
      sourceGlobal.global_ad_slope (a := scale) (offset := offset)
        (target := scalarProjection
          (globalGrainDirection
            (pureWZ2CoupledAffineSlope subband
              (preparation.box.popular.center 2) scale z))
          (horizontalSlice assembly.finalShading.union z))
    · exact lt_of_lt_of_le (by norm_num) preparation.scale_one
    · exact hscaleSource
    · rintro value ⟨point, ⟨⟨index, hpoint⟩, hpointHeight⟩, rfl⟩
      rcases assembly.final_tubeWitness index point hpoint with
        ⟨exactPoint, hexactDistance, _hexactCarrier⟩
      let source := preparation.finalAmbientSourcePoint exactPoint
      refine ⟨(source : Point3), hrawSource source.property, ?_, ?_⟩
      · exact hsourceCell exactPoint
      · have hpointAmbient : point ∈
            preparation.cleanupRegularized.isotropicCleanupFinalShading.carrier
              (assembly.joint.finalTargetIndex index) := by
          simpa only [assembly.finalShading_carrier] using hpoint
        have hbound := preparation.coupledProjection_lowerCell_bound
          subband hsourceDelta hslopeBound hslopeErrorNonnegative htargetSlope
          hslopeError (assembly.joint.finalTargetIndex index) point
          hpointAmbient exactPoint hexactDistance
        have hboundD := hbound.trans hD
        simpa [offset, source, hpointHeight, pureWZ2PaperCellLowerHeight,
          ← hsourceSlope] using hboundD
    · exact hDPos
  exact hrawAD.weaken_constant hconstant htargetOne htargetTop

/-- Canonical final-quotient specialization of the preceding transfer.  The
source-height family is the fixed local window furnished by the narrow final
box, so the former `sourceDelta⁻¹` loss is replaced by the absolute constant
seventeen. -/
theorem PureWZ2IsotropicCleanupQuotientAssemblyData.toCoupledAffineGlobalAD_localHeightCells
    {sigma epsilon delta finalDelta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    {sourceFamily ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {anisotropicCenter : Point3}
    {m : ℝ} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := anisotropicPaperAlignedScale delta
        subband.left subband.right) sourceFamily sourceShading
        band.lemma31.data.globalSlope anisotropicCenter subband.ordered hm}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant
      sourceScheduleConstant C targetConstant : ENNReal}
    {boxLevelCount cleanupLevelCount parentLevelCount : ℕ}
    {scale slopeBound slopeError D : ℝ}
    {preparation : PureWZ2FinalIsotropicPreparationData
      (targetDelta := finalDelta) raw.exactShading sourceConstant
      boxScheduleConstant cleanupScheduleConstant boxLevelCount
      cleanupLevelCount scale}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData
      preparation.cleanupRegularized sourceScheduleConstant parentLevelCount)
    (sourceGlobal : PureWZ2C2GlobalGrainData ambientShading sigma C)
    (hsourceCubical : WZ1PaperIsCubicalShading ambientShading)
    (hrawSource : sourceShading.union ⊆ ambientShading.union)
    (hsourceSlope : (band.lemma31.data.globalSlope : ℝ → ℝ) =
      sourceGlobal.slope)
    (hscaleSource : scale * delta ≤ finalDelta)
    (hslopeBound : 0 ≤ slopeBound)
    (htargetSlope : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |pureWZ2CoupledAffineSlope subband (preparation.box.popular.center 2)
        scale z| ≤ slopeBound)
    (hslopeErrorNonnegative : 0 ≤ slopeError)
    (hslopeError : ∀ point : Point3, ∀ index,
      point ∈
          preparation.cleanupRegularized.isotropicCleanupFinalShading.carrier
            index →
      ∀ exactPoint : {point : Point3 // point ∈
          pureWZ2IsotropicMap preparation.box.popular.center scale ''
            preparation.exactRestricted},
      dist point (exactPoint : Point3) ≤ finalDelta * Real.sqrt 3 →
      let source := preparation.finalAmbientSourcePoint exactPoint
      let height := pureWZ2PaperCellLowerHeight delta source
      let targetHeight := pureWZ2CoupledTargetHeight subband.left subband.right
        preparation.box.popular.center scale height
      |pureWZ2CoupledAffineSlope subband (preparation.box.popular.center 2)
          scale (point 2) -
        pureWZ2CombinedExactSlope band.lemma31.data.globalSlope
          subband.left subband.right m preparation.box.popular.center scale
            targetHeight| ≤ slopeError)
    (hD :
      (1 + slopeBound) *
          (finalDelta * Real.sqrt 3 +
            scale * (2 / (subband.right - subband.left)) * delta) +
        (Real.sqrt 3 / 200) * slopeError ≤ D)
    (hDPos : 0 < D)
    (hconstant :
      (2 * (Nat.ceil (D / finalDelta) + 1) : ENNReal) ^ 3 *
          (17 * C) ≤ targetConstant)
    (htargetOne : 1 ≤ targetConstant) (htargetTop : targetConstant ≠ ⊤) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection
            (pureWZ2CoupledAffineSlope subband
              (preparation.box.popular.center 2) scale z))
          (horizontalSlice assembly.finalShading.union z))
        finalDelta (1 - sigma) targetConstant := by
  let cells := pureWZ2LocalPaperHeightCells delta
    (pureWZ2CoupledSourceHeight subband
      (preparation.box.popular.center 2))
  have hcells := assembly.final_source_height_cells subband
    hsourceCubical hrawSource
  apply assembly.toCoupledAffineGlobalAD subband sourceGlobal hsourceCubical
    hrawSource cells hcells.1 hcells.2.2.1 hcells.2.2.2 hsourceSlope
    hscaleSource hslopeBound htargetSlope hslopeErrorNonnegative hslopeError
    hD hDPos ?_ htargetOne htargetTop
  have hcardProduct : (cells.card : ENNReal) * C ≤ 17 * C := by
    exact mul_le_mul_right'
      (by exact_mod_cast hcells.2.1 : (cells.card : ENNReal) ≤ 17) C
  exact (mul_le_mul_left' hcardProduct
    ((2 * (Nat.ceil (D / finalDelta) + 1) : ENNReal) ^ 3)).trans hconstant

/-- Fully canonical global-AD transfer for the coupled final quotient.  All
geometric losses are bounded by fixed numerical constants: seventeen source
height cells and a projection thickening of at most `10 * finalDelta`. -/
theorem PureWZ2IsotropicCleanupQuotientAssemblyData.toCanonicalCoupledAffineGlobalAD
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (scaleData : PureWZ2CoupledScaleData subband)
    {sourceFamily ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {anisotropicCenter : Point3}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := anisotropicPaperAlignedScale delta
        subband.left subband.right) sourceFamily sourceShading
        band.lemma31.data.globalSlope anisotropicCenter subband.ordered
          scaleData.m_pos}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant
      sourceScheduleConstant C targetConstant : ENNReal}
    {boxLevelCount cleanupLevelCount parentLevelCount : ℕ}
    {preparation : PureWZ2FinalIsotropicPreparationData
      (targetDelta := pureWZ2CoupledFinalDelta subband) raw.exactShading
      sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount (pureWZ2CoupledFinalScale subband)}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData
      preparation.cleanupRegularized sourceScheduleConstant parentLevelCount)
    (sourceGlobal : PureWZ2C2GlobalGrainData ambientShading sigma C)
    (hsourceCubical : WZ1PaperIsCubicalShading ambientShading)
    (hrawSource : sourceShading.union ⊆ ambientShading.union)
    (hsourceSlope : (band.lemma31.data.globalSlope : ℝ → ℝ) =
      sourceGlobal.slope)
    (hconstant :
      (2 * (Nat.ceil (7 * pureWZ2CoupledFinalScale subband + 10) + 1) :
          ENNReal) ^ 3 * (17 * C) ≤ targetConstant)
    (htargetOne : 1 ≤ targetConstant) (htargetTop : targetConstant ≠ ⊤) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection
            (pureWZ2CoupledAffineSlope subband
              (preparation.box.popular.center 2)
              (pureWZ2CoupledFinalScale subband) z))
          (horizontalSlice assembly.finalShading.union z))
        (pureWZ2CoupledFinalDelta subband) (1 - sigma) targetConstant := by
  let slopeBound : ℝ := 3 * pureWZ2CoupledFinalScale subband + 2
  let slopeError : ℝ := 5 * pureWZ2CoupledFinalDelta subband
  let D : ℝ := (7 * pureWZ2CoupledFinalScale subband + 10) *
    pureWZ2CoupledFinalDelta subband
  have htargetSlope : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |pureWZ2CoupledAffineSlope subband (preparation.box.popular.center 2)
        (pureWZ2CoupledFinalScale subband) z| ≤ slopeBound := by
    exact pureWZ2CoupledAffineSlope_abs_le subband scaleData.lambda_pos
      (abs_le.mp preparation.center_height_bound)
  have hD :
      (1 + slopeBound) *
          (pureWZ2CoupledFinalDelta subband * Real.sqrt 3 +
            pureWZ2CoupledFinalScale subband *
              (2 / (subband.right - subband.left)) * delta) +
        (Real.sqrt 3 / 200) * slopeError ≤ D := by
    have hsqrt : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    have hmovement := scaleData.lower_cell_image_budget
    dsimp only [slopeBound, slopeError, D]
    have hdelta := scaleData.final_delta_pos
    have hinner : pureWZ2CoupledFinalDelta subband * Real.sqrt 3 +
          pureWZ2CoupledFinalScale subband *
            (2 / (subband.right - subband.left)) * delta ≤
        (257 / 128 : ℝ) * pureWZ2CoupledFinalDelta subband := by
      nlinarith
    have hcoefficient : 0 ≤
        1 + (3 * pureWZ2CoupledFinalScale subband + 2) := by
      nlinarith [scaleData.lambda_pos]
    have hmain := mul_le_mul_of_nonneg_left hinner hcoefficient
    nlinarith [mul_pos scaleData.lambda_pos hdelta]
  have hratio : D / pureWZ2CoupledFinalDelta subband =
      7 * pureWZ2CoupledFinalScale subband + 10 := by
    dsimp only [D]
    field_simp [scaleData.final_delta_pos.ne']
  have hconstant' :
      (2 * (Nat.ceil (D / pureWZ2CoupledFinalDelta subband) + 1) : ENNReal) ^ 3 *
          (17 * C) ≤ targetConstant := by
    rw [hratio]
    exact hconstant
  have hslopeBoundNonnegative : 0 ≤ slopeBound := by
    dsimp only [slopeBound]
    nlinarith [scaleData.lambda_pos]
  have hslopeErrorNonnegative : 0 ≤ slopeError := by
    dsimp only [slopeError]
    nlinarith [scaleData.final_delta_pos]
  exact assembly.toCoupledAffineGlobalAD_localHeightCells subband sourceGlobal
    hsourceCubical hrawSource hsourceSlope
    scaleData.lambda_mul_source_delta_le_final hslopeBoundNonnegative
    htargetSlope hslopeErrorNonnegative
    (preparation.canonical_coupled_slope_error subband scaleData
      hsourceCubical hrawSource) hD (by
        dsimp only [D]
        exact mul_pos (by nlinarith [scaleData.lambda_pos])
          scaleData.final_delta_pos) hconstant'
    htargetOne htargetTop

/-- Paper-faithful exact-slope form of the canonical final global-AD transfer.
The affine tangent is used only as an internal comparison estimate.  On every
nonempty final slice its quadratic error is at most one final radius, and the
visible factor six is the standard nearby-projection loss. -/
theorem PureWZ2IsotropicCleanupQuotientAssemblyData.toCanonicalCoupledExactGlobalAD
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (scaleData : PureWZ2CoupledScaleData subband)
    {sourceFamily ambientFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {anisotropicCenter : Point3}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := anisotropicPaperAlignedScale delta
        subband.left subband.right) sourceFamily sourceShading
        band.lemma31.data.globalSlope anisotropicCenter subband.ordered
          scaleData.m_pos}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant
      sourceScheduleConstant C targetConstant : ENNReal}
    {boxLevelCount cleanupLevelCount parentLevelCount : ℕ}
    {preparation : PureWZ2FinalIsotropicPreparationData
      (targetDelta := pureWZ2CoupledFinalDelta subband) raw.exactShading
      sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount (pureWZ2CoupledFinalScale subband)}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData
      preparation.cleanupRegularized sourceScheduleConstant parentLevelCount)
    (sourceGlobal : PureWZ2C2GlobalGrainData ambientShading sigma C)
    (hsourceCubical : WZ1PaperIsCubicalShading ambientShading)
    (hrawSource : sourceShading.union ⊆ ambientShading.union)
    (hsourceSlope : (band.lemma31.data.globalSlope : ℝ → ℝ) =
      sourceGlobal.slope)
    (hconstant :
      6 * ((2 *
          (Nat.ceil (7 * pureWZ2CoupledFinalScale subband + 10) + 1) :
            ENNReal) ^ 3 * (17 * C)) ≤ targetConstant)
    (htargetOne : 1 ≤ targetConstant) (htargetTop : targetConstant ≠ ⊤) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection
            (pureWZ2CoupledPublicExactSlopeFunction subband
              (preparation.box.popular.center 2)
              (pureWZ2CoupledFinalScale subband) z))
          (horizontalSlice assembly.finalShading.union z))
        (pureWZ2CoupledFinalDelta subband) (1 - sigma) targetConstant := by
  let rawConstant : ENNReal :=
    (2 * (Nat.ceil (7 * pureWZ2CoupledFinalScale subband + 10) + 1) :
      ENNReal) ^ 3 * (17 * C)
  have hsourceAD := sourceGlobal.global_ad (⟨0, by norm_num⟩ : PureWZ2UnitInterval)
  have hCOne : 1 ≤ C := hsourceAD.2.2.2.1
  have hCTop : C ≠ ⊤ := hsourceAD.2.2.2.2.1
  have hrawOne : 1 ≤ rawConstant := by
    dsimp only [rawConstant]
    have hfactor : (1 : ENNReal) ≤
        (2 * (Nat.ceil
          (7 * pureWZ2CoupledFinalScale subband + 10) + 1) : ENNReal) := by
      have hnat : 1 ≤ 2 * (Nat.ceil
          (7 * pureWZ2CoupledFinalScale subband + 10) + 1) := by omega
      exact_mod_cast hnat
    calc
      1 ≤ 1 ^ 3 * (1 * C) := by simpa using hCOne
      _ ≤ (2 * (Nat.ceil
            (7 * pureWZ2CoupledFinalScale subband + 10) + 1) : ENNReal) ^ 3 *
          (17 * C) := by gcongr <;> norm_num
  have hrawTop : rawConstant ≠ ⊤ := by
    dsimp only [rawConstant]
    have hfactorTop :
        (2 * (Nat.ceil
          (7 * pureWZ2CoupledFinalScale subband + 10) + 1) : ENNReal) ≠ ⊤ := by
      exact ENNReal.mul_ne_top (by norm_num) (by simp)
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top hfactorTop)
      (ENNReal.mul_ne_top (by norm_num) hCTop)
  have haffine := assembly.toCanonicalCoupledAffineGlobalAD subband scaleData
    sourceGlobal hsourceCubical hrawSource hsourceSlope
    (targetConstant := rawConstant) le_rfl hrawOne hrawTop
  intro z hz
  have hcenter : preparation.box.popular.center 2 ∈ Set.Icc (-1 : ℝ) 1 :=
    abs_le.mp preparation.center_height_bound
  have hclose := pureWZ2CoupledPublicExactSlope_close_affine subband
    scaleData.lambda_one hcenter hz
  have hnear := (haffine z hz).nearby_projection_transfer
    (w := globalGrainDirection
      (pureWZ2CoupledPublicExactSlopeFunction subband
        (preparation.box.popular.center 2)
        (pureWZ2CoupledFinalScale subband) z))
    (D := pureWZ2CoupledFinalDelta subband)
  have htransferred : PureWZ2PaperADSet1
      (scalarProjection
        (globalGrainDirection
          (pureWZ2CoupledPublicExactSlopeFunction subband
            (preparation.box.popular.center 2)
            (pureWZ2CoupledFinalScale subband) z))
        (horizontalSlice assembly.finalShading.union z))
      (pureWZ2CoupledFinalDelta subband) (1 - sigma) (6 * rawConstant) := by
    apply hnear
    · intro point hpoint
      rcases hpoint.1 with ⟨index, hpointCarrier⟩
      rcases assembly.final_tubeWitness index point hpointCarrier with
        ⟨exactPoint, hexactDistance, _hexactCarrier⟩
      have hrestrictedSelected : preparation.exactRestricted ⊆
          preparation.box.selectedShading.union :=
        restrictPaperShading_union_subset preparation.cleanupRegularized.selected
          preparation.box.selectedShading
      have hexactHeightRaw :=
        preparation.box.isotropicSelectedImage_height_abs_le
          preparation.scale_one
          ⟨exactPoint, Set.image_mono hrestrictedSelected exactPoint.property⟩
      have hexactHeight : |(exactPoint : Point3) 2| ≤
          pureWZ2CoupledFinalDelta subband / 32 :=
        hexactHeightRaw.trans scaleData.isotropic_exact_height_budget
      have hpointCoordinate :
          |point 2 - (exactPoint : Point3) 2| ≤
            pureWZ2CoupledFinalDelta subband * Real.sqrt 3 := by
        exact (PiLp.norm_apply_le (point - (exactPoint : Point3)) 2).trans <| by
          simpa [dist_eq_norm] using hexactDistance
      have hzAbs : |z| ≤ 3 * pureWZ2CoupledFinalDelta subband := by
        have hpointHeight : point 2 = z := hpoint.2
        rw [← hpointHeight]
        calc
          |point 2| = |(point 2 - (exactPoint : Point3) 2) +
              (exactPoint : Point3) 2| := by congr 1 <;> ring
          _ ≤ |point 2 - (exactPoint : Point3) 2| +
              |(exactPoint : Point3) 2| := abs_add_le _ _
          _ ≤ pureWZ2CoupledFinalDelta subband * Real.sqrt 3 +
              pureWZ2CoupledFinalDelta subband / 32 :=
            add_le_add hpointCoordinate hexactHeight
          _ ≤ 3 * pureWZ2CoupledFinalDelta subband := by
            have hsqrt : Real.sqrt 3 ≤ 2 := by
              nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
                Real.sqrt_nonneg 3]
            nlinarith [scaleData.final_delta_pos]
      have hzSq : z ^ 2 ≤
          9 * pureWZ2CoupledFinalDelta subband ^ 2 := by
        rw [← sq_abs z]
        nlinarith [abs_nonneg z, scaleData.final_delta_pos]
      have hy : |point 1| ≤ 2 := by
        have hbody := (assembly.finalShading.subset_body index hpointCarrier).2
        have hone : |point 1| ≤ 1 := by
          simpa [Kakeya.Streamlined.axisBox] using hbody.2.1
        exact hone.trans (by norm_num)
      have hidentity :
          inner ℝ point
              (globalGrainDirection
                (pureWZ2CoupledPublicExactSlopeFunction subband
                  (preparation.box.popular.center 2)
                  (pureWZ2CoupledFinalScale subband) z)) -
            inner ℝ point
              (globalGrainDirection
                (pureWZ2CoupledAffineSlope subband
                  (preparation.box.popular.center 2)
                  (pureWZ2CoupledFinalScale subband) z)) =
          (pureWZ2CoupledPublicExactSlopeFunction subband
                (preparation.box.popular.center 2)
                (pureWZ2CoupledFinalScale subband) z -
            pureWZ2CoupledAffineSlope subband
                (preparation.box.popular.center 2)
                (pureWZ2CoupledFinalScale subband) z) * point 1 := by
        simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
        ring
      rw [hidentity, abs_mul]
      calc
        _ ≤ (z ^ 2 / 18000) * 2 :=
          mul_le_mul hclose hy (abs_nonneg _) (by positivity)
        _ ≤ pureWZ2CoupledFinalDelta subband := by
          have hdeltaSq : pureWZ2CoupledFinalDelta subband ^ 2 ≤
              pureWZ2CoupledFinalDelta subband / 24 := by
            nlinarith [scaleData.final_delta_pos,
              scaleData.final_delta_le_twenty_four]
          nlinarith
    · exact scaleData.final_delta_pos.le
    · exact le_rfl
  exact htransferred.weaken_constant hconstant htargetOne htargetTop

/-- The second quotient inherits global AD from an ambient cubical source
shading once the concrete coupled projection error has been bounded.  The
height-cell count and the arbitrary positive thickening radius remain visible
so their finite loss can be absorbed by the caller's exponent budget. -/
theorem PureWZ2IsotropicCleanupQuotientAssemblyData.toFinalGlobalADOfCoupledWitness
    {sourceDelta preDelta finalDelta sigma c d m : ℝ}
    {rawSourceFamily ambientFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {rawSourceShading : WZ1PaperTubeShading rawSourceFamily}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) rawSourceFamily rawSourceShading
        g anisotropicCenter hcd hm}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant
      sourceScheduleConstant C : ENNReal}
    {boxLevelCount cleanupLevelCount parentLevelCount : ℕ}
    {scale D : ℝ}
    {preparation : PureWZ2FinalIsotropicPreparationData
      (targetDelta := finalDelta) raw.exactShading sourceConstant
      boxScheduleConstant cleanupScheduleConstant boxLevelCount
      cleanupLevelCount scale}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData
      preparation.cleanupRegularized sourceScheduleConstant parentLevelCount)
    (sourceGlobal : PureWZ2C2GlobalGrainData ambientShading sigma C)
    (hsourceCubical : WZ1PaperIsCubicalShading ambientShading)
    (hrawSource : rawSourceShading.union ⊆ ambientShading.union)
    (targetSlope : SlopeFunction)
    (offset : ℤ → ℝ)
    (hscaleSource : scale * sourceDelta ≤ finalDelta)
    (hprojection : ∀ index point,
      ∀ hpoint : point ∈ assembly.finalShading.carrier index,
      ∀ exactPoint : {point : Point3 // point ∈
          pureWZ2IsotropicMap preparation.box.popular.center scale ''
            preparation.exactRestricted},
        dist point (exactPoint : Point3) ≤ finalDelta * Real.sqrt 3 →
        let source := preparation.finalAmbientSourcePoint exactPoint
        let cell := Int.floor ((source : Point3) 2 / sourceDelta)
        dist
          (inner ℝ point
            (globalGrainDirection (targetSlope (point 2))))
          (scale * inner ℝ
              (pureWZ2ReplaceHeight source
                (pureWZ2PaperCellLowerHeight sourceDelta source))
              (globalGrainDirection
                (sourceGlobal.slope
                  (pureWZ2PaperCellLowerHeight sourceDelta source))) +
            offset cell) ≤ D)
    (hD : 0 < D) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (targetSlope z))
          (horizontalSlice assembly.finalShading.union z))
        finalDelta (1 - sigma)
          ((2 * (Nat.ceil (D / finalDelta) + 1) : ENNReal) ^ 3 *
            (((pureWZ2PaperHeightCells sourceDelta).card : ENNReal) * C)) := by
  have hsourceDelta : 0 < sourceDelta :=
    (sourceGlobal.global_ad_slope 0 (by constructor <;> norm_num)).1
  intro z _hz
  apply hsourceCubical.targetProjection_ad_of_source_witness_indexed
    hsourceDelta preparation.target_delta_pos sourceGlobal.slope
    (pureWZ2PaperHeightCells sourceDelta)
    (pureWZ2PaperHeightCells_nonempty hsourceDelta)
    (fun _ hcell => pureWZ2PaperHeightCells_height_mem
      hsourceDelta hcell)
    sourceGlobal.global_ad_slope (a := scale) (offset := offset)
      (target := scalarProjection (globalGrainDirection (targetSlope z))
        (horizontalSlice assembly.finalShading.union z))
  · exact lt_of_lt_of_le (by norm_num) preparation.scale_one
  · exact hscaleSource
  · rintro value ⟨point, ⟨⟨index, hpoint⟩, hpointHeight⟩, rfl⟩
    rcases assembly.final_tubeWitness index point hpoint with
      ⟨exactPoint, hexactDistance, _hexactCarrier⟩
    let source := preparation.finalAmbientSourcePoint exactPoint
    refine ⟨(source : Point3), hrawSource source.property, ?_, ?_⟩
    · exact hsourceCubical.heightCell_mem
        hsourceDelta (hrawSource source.property)
    · have hbound := hprojection index point hpoint exactPoint hexactDistance
      simpa [source, hpointHeight] using hbound
  · exact hD

/-- Absorb the explicit finite height-cell and thickening losses into any
larger terminal constant chosen by the caller. -/
theorem PureWZ2IsotropicCleanupQuotientAssemblyData.toFinalGlobalADOfCoupledWitnessWithConstant
    {sourceDelta preDelta finalDelta sigma c d m : ℝ}
    {rawSourceFamily ambientFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {rawSourceShading : WZ1PaperTubeShading rawSourceFamily}
    {ambientShading : WZ1PaperTubeShading ambientFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) rawSourceFamily rawSourceShading
        g anisotropicCenter hcd hm}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant
      sourceScheduleConstant C targetConstant : ENNReal}
    {boxLevelCount cleanupLevelCount parentLevelCount : ℕ}
    {scale D : ℝ}
    {preparation : PureWZ2FinalIsotropicPreparationData
      (targetDelta := finalDelta) raw.exactShading sourceConstant
      boxScheduleConstant cleanupScheduleConstant boxLevelCount
      cleanupLevelCount scale}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData
      preparation.cleanupRegularized sourceScheduleConstant parentLevelCount)
    (sourceGlobal : PureWZ2C2GlobalGrainData ambientShading sigma C)
    (hsourceCubical : WZ1PaperIsCubicalShading ambientShading)
    (hrawSource : rawSourceShading.union ⊆ ambientShading.union)
    (targetSlope : SlopeFunction) (offset : ℤ → ℝ)
    (hscaleSource : scale * sourceDelta ≤ finalDelta)
    (hprojection : ∀ index point,
      ∀ hpoint : point ∈ assembly.finalShading.carrier index,
      ∀ exactPoint : {point : Point3 // point ∈
          pureWZ2IsotropicMap preparation.box.popular.center scale ''
            preparation.exactRestricted},
        dist point (exactPoint : Point3) ≤ finalDelta * Real.sqrt 3 →
        let source := preparation.finalAmbientSourcePoint exactPoint
        let cell := Int.floor ((source : Point3) 2 / sourceDelta)
        dist
          (inner ℝ point
            (globalGrainDirection (targetSlope (point 2))))
          (scale * inner ℝ
              (pureWZ2ReplaceHeight source
                (pureWZ2PaperCellLowerHeight sourceDelta source))
              (globalGrainDirection
                (sourceGlobal.slope
                  (pureWZ2PaperCellLowerHeight sourceDelta source))) +
            offset cell) ≤ D)
    (hD : 0 < D)
    (hconstant :
      (2 * (Nat.ceil (D / finalDelta) + 1) : ENNReal) ^ 3 *
          (((pureWZ2PaperHeightCells sourceDelta).card : ENNReal) * C) ≤
        targetConstant)
    (htargetOne : 1 ≤ targetConstant) (htargetTop : targetConstant ≠ ⊤) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (targetSlope z))
          (horizontalSlice assembly.finalShading.union z))
        finalDelta (1 - sigma) targetConstant := by
  intro z hz
  exact (assembly.toFinalGlobalADOfCoupledWitness sourceGlobal
    hsourceCubical hrawSource targetSlope offset hscaleSource hprojection hD z hz)
      |>.weaken_constant hconstant htargetOne htargetTop

end Kakeya.Assouad

end
