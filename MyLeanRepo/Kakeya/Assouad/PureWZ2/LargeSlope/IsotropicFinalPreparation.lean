import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicBoxPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicCleanupSourceRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicCleanupQuotientAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FiniteScheduleParameters

/-!
# Final-isotropic source, shading, and cleanup preparation

This packages the two source-side CWA-compatible selections surrounding the
final isotropic distinctness cleanup.  The intermediate target shading is the
literal cubical saturation of the selected exact source shading and retains
the explicit `scale^3` Jacobian factor.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Per-source normalization furnished by the target mass surviving the
final-isotropic distinctness cleanup. -/
def pureWZ2IsotropicCleanupNormalization
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    (cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading) : ENNReal :=
  cleanup.restrictedShading.mass / sourceFamily.enncard

/-- Complete preparation immediately before the final quotient schedule. -/
structure PureWZ2FinalIsotropicPreparationData
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal)
    (boxLevelCount cleanupLevelCount : ℕ) (scale : ℝ) where
  box : PureWZ2FinalIsotropicBoxPreparationData sourceShading
    sourceConstant boxScheduleConstant boxLevelCount scale
  target_delta_pos : 0 < targetDelta
  target_delta_small : targetDelta ≤ 1 / 4
  scale_one : 1 ≤ scale
  radius_budget : scale * (6 * sourceDelta) +
      targetDelta * Real.sqrt 3 ≤ 6 * targetDelta
  scale_source_small : scale * sourceDelta ≤ 1 / 1000
  source_line : WZ1PaperIsLineClass sourceFamily
  source_direction : ∀ index,
    (sourceFamily.tube index).direction =
      wz1PaperDirection (sourceFamily.tube index)
  source_base : ∀ index, ‖(sourceFamily.tube index).base‖ ≤ 5
  cleanup : PureWZ2IsotropicDistinctCleanupData
    box.regularized.selected.family box.popular.center scale
    (pureWZ2IsotropicCenteredPaperShading box.selectedShading
      box.popular.center scale box.regularized.cwa_nearby.1
      target_delta_pos target_delta_small scale_one radius_budget
      (box.selectedShading_union_subset_ball scale_one scale_source_small))
  cleanup_mass_lower :
    (pureWZ2IsotropicCenteredPaperShading box.selectedShading
        box.popular.center scale box.regularized.cwa_nearby.1
        target_delta_pos target_delta_small scale_one radius_budget
        (box.selectedShading_union_subset_ball scale_one
          scale_source_small)).mass ≤
      (pureWZ2IsotropicCenteredConflictDegree sourceDelta targetDelta + 1 :
        ENNReal) * cleanup.restrictedShading.mass
  cleanupRegularized : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
    box.regularized.outputConstant cleanupScheduleConstant
    (pureWZ2IsotropicCleanupNormalization cleanup) cleanupLevelCount

/-- Assemble the final-isotropic preparation from one already selected source
box.  Keeping the box explicit is the dependency-safe interface for automatic
selection of the second finite schedule. -/
theorem pureWZ2_final_isotropic_preparation_of_box
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    (ambientCWA : WZ2PaperPureCWAAtNearbyScales sourceFamily sourceConstant)
    (hfamily : sourceFamily.Nonempty)
    (hsourceDeltaOne : sourceDelta ≤ 1)
    (hsourceMass : 0 < sourceShading.mass)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hsourceDirection : ∀ index,
      (sourceFamily.tube index).direction =
        wz1PaperDirection (sourceFamily.tube index))
    (hsourceBase : ∀ index, ‖(sourceFamily.tube index).base‖ ≤ 5)
    (hsourcePackingDistinct : WZ1PaperIsEssentiallyDistinct
      (pureWZ2CenteredPackingFamily sourceFamily))
    (scale : ℝ) (hscale : 1 ≤ scale)
    (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hradius : scale * (6 * sourceDelta) +
      targetDelta * Real.sqrt 3 ≤ 6 * targetDelta)
    (hscaleSourceSmall : scale * sourceDelta ≤ 1 / 1000)
    (boxLevelCount : ℕ)
    (hsourceTwo : 2 < sourceConstant)
    (hboxLevels : ENNReal.ofReal (1 / sourceDelta) ≤
      sourceConstant ^ boxLevelCount)
    (hboxScheduleFinite : WZ2PaperFiniteErrorConstant boxScheduleConstant)
    (hboxSchedule : sourceConstant * sourceConstant ≤ boxScheduleConstant)
    (box : PureWZ2FinalIsotropicBoxPreparationData sourceShading
      sourceConstant boxScheduleConstant boxLevelCount scale)
    (cleanupLevelCount : ℕ)
    (hboxTwo : 2 < box.regularized.outputConstant)
    (hcleanupLevels : ENNReal.ofReal (1 / sourceDelta) ≤
      box.regularized.outputConstant ^ cleanupLevelCount)
    (hcleanupScheduleFinite :
      WZ2PaperFiniteErrorConstant cleanupScheduleConstant)
    (hcleanupSchedule :
      box.regularized.outputConstant ^ 2 ≤
        cleanupScheduleConstant) :
    ∃ data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
        sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
        boxLevelCount cleanupLevelCount scale,
      data.box = box := by
  let targetShading := pureWZ2IsotropicCenteredPaperShading
    box.selectedShading box.popular.center scale box.regularized.cwa_nearby.1
    htargetDelta htargetDeltaSmall hscale hradius
    (box.selectedShading_union_subset_ball hscale hscaleSourceSmall)
  have hselectedLine : WZ1PaperIsLineClass box.regularized.selected.family :=
    hsourceLine.subfamily box.regularized.selected
  have hzero := box.isotropic_zeroPoint_bound
    ambientCWA.1 hscale hscaleSourceSmall hsourceLine
  have hisotropicLine : WZ1PaperIsLineClass
      (pureWZ2IsotropicPaperFamily
        (targetDelta := targetDelta) box.regularized.selected.family
        box.popular.center scale) := by
    intro index
    exact pureWZ2IsotropicPaperTube_lineClass box.popular.center
      (lt_of_lt_of_le (by norm_num) hscale)
      (box.regularized.selected.family.tube index) (hselectedLine index)
      (hzero index)
  let selectedPacking : Kakeya.Streamlined.TubeSubfamily
      (pureWZ2CenteredPackingFamily sourceFamily) :=
    { family := pureWZ2CenteredPackingFamily box.regularized.selected.family
      embedding := box.regularized.selected.embedding
      tube_eq := by
        intro index
        change wz2PaperRelabelTube
            (pureWZ2PaperCenteredTube
              (box.regularized.selected.family.tube index)) =
          wz2PaperRelabelTube
            (pureWZ2PaperCenteredTube
              (sourceFamily.tube
                (box.regularized.selected.embedding index)))
        rw [box.regularized.selected.tube_eq] }
  have hselectedPacking : WZ1PaperIsEssentiallyDistinct
      (pureWZ2CenteredPackingFamily box.regularized.selected.family) :=
    hsourcePackingDistinct.subfamily selectedPacking
  rcases pureWZ2_isotropic_distinct_cleanup
      box.regularized.selected.family box.popular.center hscale
      (by
        have hcenter := box.popular.center_mem
        exact hcenter (2 : Fin 3))
      ambientCWA.1 htargetDelta hselectedPacking hselectedLine
      hisotropicLine targetShading with
    ⟨cleanup⟩
  have htargetMass : 0 < targetShading.mass := by
    have hjacobian : 0 < ENNReal.ofReal (scale ^ 3) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    have hlower := pureWZ2IsotropicCenteredPaperShading_mass_lower
      box.selectedShading box.popular.center scale box.regularized.cwa_nearby.1
      htargetDelta htargetDeltaSmall hscale hradius
      (box.selectedShading_union_subset_ball hscale hscaleSourceSmall)
    exact (ENNReal.mul_pos hjacobian.ne'
      box.selectedShading_mass_pos.ne').trans_le hlower
  have hcleanupMass : 0 < cleanup.restrictedShading.mass := by
    have hproduct : 0 <
        (pureWZ2IsotropicCenteredConflictDegree sourceDelta targetDelta + 1 :
          ENNReal) * cleanup.restrictedShading.mass :=
      htargetMass.trans_le cleanup.mass_lower
    exact pos_of_mul_pos_right hproduct bot_le
  have hcardZero : box.regularized.selected.family.enncard ≠ 0 := by
    change (box.regularized.selected.family.card : ENNReal) ≠ 0
    exact_mod_cast box.regularized.selected_nonempty.ne'
  have hcardTop : box.regularized.selected.family.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hnormalizationZero : pureWZ2IsotropicCleanupNormalization cleanup ≠ 0 := by
    unfold pureWZ2IsotropicCleanupNormalization
    exact (ENNReal.div_pos hcleanupMass.ne' hcardTop).ne'
  have hnormalizationTop : pureWZ2IsotropicCleanupNormalization cleanup ≠ ⊤ := by
    have hmassTop : cleanup.restrictedShading.mass ≠ ⊤ := by
      change (∑ index, volume (cleanup.restrictedShading.carrier index)) ≠ ⊤
      apply ENNReal.sum_ne_top.mpr
      intro index _
      have hsubset : cleanup.restrictedShading.carrier index ⊆
          Kakeya.Streamlined.axisBox 2 2 2 := fun point hpoint =>
        (cleanup.restrictedShading.subset_body index hpoint).2
      apply ne_top_of_le_ne_top (b := volume
        (Kakeya.Streamlined.axisBox 2 2 2))
      · rw [Kakeya.Streamlined.volume_axisBox 2 2 2] <;> norm_num
      · exact measure_mono hsubset
    exact ENNReal.div_ne_top hmassTop hcardZero
  have hnormalizationMass :
      pureWZ2IsotropicCleanupNormalization cleanup *
          box.regularized.selected.family.enncard ≤
        cleanup.restrictedShading.mass := by
    unfold pureWZ2IsotropicCleanupNormalization
    rw [ENNReal.div_mul_cancel hcardZero hcardTop]
  rcases pureWZ2_isotropic_cleanup_source_regularization
      box.regularized.cwa_nearby box.regularized.selected_nonempty
      hsourceDeltaOne cleanup hnormalizationZero hnormalizationTop
      hnormalizationMass cleanupLevelCount hboxTwo hcleanupLevels
      hcleanupScheduleFinite (by simpa [pow_two] using hcleanupSchedule) with
    ⟨cleanupRegularized⟩
  exact ⟨{
    box := box
    target_delta_pos := htargetDelta
    target_delta_small := htargetDeltaSmall
    scale_one := hscale
    radius_budget := hradius
    scale_source_small := hscaleSourceSmall
    source_line := hsourceLine
    source_direction := hsourceDirection
    source_base := hsourceBase
    cleanup := cleanup
    cleanup_mass_lower := cleanup.mass_lower
    cleanupRegularized := cleanupRegularized
  }, rfl⟩

/-- Compatibility wrapper retaining the original dependent-choice interface. -/
theorem pureWZ2_final_isotropic_preparation
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    (ambientCWA : WZ2PaperPureCWAAtNearbyScales sourceFamily sourceConstant)
    (hfamily : sourceFamily.Nonempty)
    (hsourceDeltaOne : sourceDelta ≤ 1)
    (hsourceMass : 0 < sourceShading.mass)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hsourceDirection : ∀ index,
      (sourceFamily.tube index).direction =
        wz1PaperDirection (sourceFamily.tube index))
    (hsourceBase : ∀ index, ‖(sourceFamily.tube index).base‖ ≤ 5)
    (hsourcePackingDistinct : WZ1PaperIsEssentiallyDistinct
      (pureWZ2CenteredPackingFamily sourceFamily))
    (scale : ℝ) (hscale : 1 ≤ scale)
    (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hradius : scale * (6 * sourceDelta) +
      targetDelta * Real.sqrt 3 ≤ 6 * targetDelta)
    (hscaleSourceSmall : scale * sourceDelta ≤ 1 / 1000)
    (boxLevelCount : ℕ)
    (hsourceTwo : 2 < sourceConstant)
    (hboxLevels : ENNReal.ofReal (1 / sourceDelta) ≤
      sourceConstant ^ boxLevelCount)
    (hboxScheduleFinite : WZ2PaperFiniteErrorConstant boxScheduleConstant)
    (hboxSchedule : sourceConstant * sourceConstant ≤ boxScheduleConstant)
    (cleanupLevelCount : ℕ)
    (hboxTwo : 2 <
      (Classical.choice (pureWZ2_final_isotropic_box_preparation
        sourceShading ambientCWA hfamily hsourceDeltaOne hsourceMass scale
        hscale hscaleSourceSmall boxLevelCount hsourceTwo hboxLevels
        hboxScheduleFinite
        hboxSchedule)).regularized.outputConstant)
    (hcleanupLevels : ENNReal.ofReal (1 / sourceDelta) ≤
      (Classical.choice (pureWZ2_final_isotropic_box_preparation
        sourceShading ambientCWA hfamily hsourceDeltaOne hsourceMass scale
        hscale hscaleSourceSmall boxLevelCount hsourceTwo hboxLevels
        hboxScheduleFinite
        hboxSchedule)).regularized.outputConstant ^ cleanupLevelCount)
    (hcleanupScheduleFinite :
      WZ2PaperFiniteErrorConstant cleanupScheduleConstant)
    (hcleanupSchedule :
      (Classical.choice (pureWZ2_final_isotropic_box_preparation
        sourceShading ambientCWA hfamily hsourceDeltaOne hsourceMass scale
        hscale hscaleSourceSmall boxLevelCount hsourceTwo hboxLevels
        hboxScheduleFinite
        hboxSchedule)).regularized.outputConstant ^ 2 ≤
        cleanupScheduleConstant) :
    Nonempty (PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale) := by
  let box := Classical.choice (pureWZ2_final_isotropic_box_preparation
    sourceShading ambientCWA hfamily hsourceDeltaOne hsourceMass scale hscale
    hscaleSourceSmall boxLevelCount hsourceTwo hboxLevels hboxScheduleFinite
      hboxSchedule)
  have hboxTwo' : 2 < box.regularized.outputConstant := by
    simpa only [box] using hboxTwo
  have hcleanupLevels' : ENNReal.ofReal (1 / sourceDelta) ≤
      box.regularized.outputConstant ^ cleanupLevelCount := by
    simpa only [box] using hcleanupLevels
  have hcleanupSchedule' : box.regularized.outputConstant ^ 2 ≤
      cleanupScheduleConstant := by
    simpa only [box] using hcleanupSchedule
  rcases pureWZ2_final_isotropic_preparation_of_box sourceShading ambientCWA
      hfamily hsourceDeltaOne hsourceMass hsourceLine hsourceDirection hsourceBase
      hsourcePackingDistinct scale hscale htargetDelta htargetDeltaSmall hradius
      hscaleSourceSmall boxLevelCount hsourceTwo hboxLevels hboxScheduleFinite
      hboxSchedule box cleanupLevelCount hboxTwo' hcleanupLevels'
      hcleanupScheduleFinite hcleanupSchedule' with
    ⟨data, _⟩
  exact ⟨data⟩

/-- Final-isotropic preparation with both finite regularization schedules
selected internally and retained as explicit certificates. -/
structure PureWZ2AutoFinalIsotropicPreparationData
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (sourceConstant : ENNReal) (scale : ℝ) where
  boxParameters : PureWZ2FiniteScheduleParameters sourceConstant
    (ENNReal.ofReal (1 / sourceDelta))
  box : PureWZ2FinalIsotropicBoxPreparationData sourceShading
    sourceConstant boxParameters.scheduleConstant boxParameters.levelCount scale
  cleanupParameters :
    PureWZ2FiniteScheduleParameters box.regularized.outputConstant
      (ENNReal.ofReal (1 / sourceDelta))
  preparation : PureWZ2FinalIsotropicPreparationData
    (targetDelta := targetDelta) sourceShading sourceConstant
    boxParameters.scheduleConstant cleanupParameters.scheduleConstant
    boxParameters.levelCount cleanupParameters.levelCount scale
  preparation_box : preparation.box = box

/-- Choose both final-isotropic finite schedules without exposing their
constants or level counts to the geometric caller. -/
theorem pureWZ2_final_isotropic_preparation_auto
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    {sourceConstant : ENNReal}
    (ambientCWA : WZ2PaperPureCWAAtNearbyScales sourceFamily sourceConstant)
    (hfamily : sourceFamily.Nonempty)
    (hsourceDeltaOne : sourceDelta ≤ 1)
    (hsourceMass : 0 < sourceShading.mass)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hsourceDirection : ∀ index,
      (sourceFamily.tube index).direction =
        wz1PaperDirection (sourceFamily.tube index))
    (hsourceBase : ∀ index, ‖(sourceFamily.tube index).base‖ ≤ 5)
    (hsourcePackingDistinct : WZ1PaperIsEssentiallyDistinct
      (pureWZ2CenteredPackingFamily sourceFamily))
    (scale : ℝ) (hscale : 1 ≤ scale)
    (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hradius : scale * (6 * sourceDelta) +
      targetDelta * Real.sqrt 3 ≤ 6 * targetDelta)
    (hscaleSourceSmall : scale * sourceDelta ≤ 1 / 1000)
    (hsourceTwo : 2 < sourceConstant) :
    Nonempty (PureWZ2AutoFinalIsotropicPreparationData
      (targetDelta := targetDelta) sourceShading sourceConstant scale) := by
  let target : ENNReal := ENNReal.ofReal (1 / sourceDelta)
  let boxParameters := Classical.choice <|
    exists_finite_schedule_parameters (target := target) hsourceTwo
      ambientCWA.2.1.2 ENNReal.ofReal_ne_top
  let box := Classical.choice <|
    pureWZ2_final_isotropic_box_preparation sourceShading ambientCWA hfamily
      hsourceDeltaOne hsourceMass scale hscale hscaleSourceSmall
      boxParameters.levelCount hsourceTwo boxParameters.target_le_power
      boxParameters.schedule_finite boxParameters.square_le_schedule
  have hboxTwo : 2 < box.regularized.outputConstant :=
    box.regularized.outputConstant_gt_two
      hsourceTwo boxParameters.square_le_schedule
  let cleanupParameters := Classical.choice <|
    exists_finite_schedule_parameters (target := target) hboxTwo
      box.regularized.cwa_nearby.2.1.2 ENNReal.ofReal_ne_top
  rcases pureWZ2_final_isotropic_preparation_of_box sourceShading ambientCWA
      hfamily hsourceDeltaOne hsourceMass hsourceLine hsourceDirection
      hsourceBase hsourcePackingDistinct scale hscale htargetDelta
      htargetDeltaSmall hradius hscaleSourceSmall boxParameters.levelCount
      hsourceTwo boxParameters.target_le_power boxParameters.schedule_finite
      boxParameters.square_le_schedule box cleanupParameters.levelCount
      hboxTwo cleanupParameters.target_le_power
      cleanupParameters.schedule_finite (by
        simpa [pow_two] using cleanupParameters.square_le_schedule) with
    ⟨preparation, hpreparationBox⟩
  exact ⟨{ boxParameters := boxParameters
           box := box
           cleanupParameters := cleanupParameters
           preparation := preparation
           preparation_box := hpreparationBox }⟩

/-- Uniform final-isotropic preparation.  Both schedule depths are fixed by
one positive loss before the runtime source scale. -/
structure PureWZ2FixedFinalIsotropicPreparationData
    {sourceDelta targetDelta scheduleLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (sourceConstant : ENNReal) (scale : ℝ) where
  boxParameters : PureWZ2FiniteScheduleParameters sourceConstant
    (ENNReal.ofReal (1 / sourceDelta))
  boxLevelCount_eq :
    boxParameters.levelCount = pureWZ2FixedScheduleLevelCount scheduleLoss
  box : PureWZ2FinalIsotropicBoxPreparationData sourceShading
    sourceConstant boxParameters.scheduleConstant boxParameters.levelCount scale
  cleanupParameters :
    PureWZ2FiniteScheduleParameters box.regularized.outputConstant
      (ENNReal.ofReal (1 / sourceDelta))
  cleanupLevelCount_eq :
    cleanupParameters.levelCount = pureWZ2FixedScheduleLevelCount scheduleLoss
  preparation : PureWZ2FinalIsotropicPreparationData
    (targetDelta := targetDelta) sourceShading sourceConstant
    boxParameters.scheduleConstant cleanupParameters.scheduleConstant
    boxParameters.levelCount cleanupParameters.levelCount scale
  preparation_box : preparation.box = box
  sourcePower_le_boxOutput :
    Kakeya.realRpowENN sourceDelta (-scheduleLoss) ≤
      box.regularized.outputConstant
  sourcePower_le_cleanupOutput :
    Kakeya.realRpowENN sourceDelta (-scheduleLoss) ≤
      preparation.cleanupRegularized.outputConstant

/-- Construct the uniform final-isotropic preparation from one preselected
schedule loss and its lower bound in the incoming nearby-CWA constant. -/
theorem pureWZ2_final_isotropic_preparation_fixed
    {sourceDelta targetDelta scheduleLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    {sourceConstant : ENNReal}
    (ambientCWA : WZ2PaperPureCWAAtNearbyScales sourceFamily sourceConstant)
    (hfamily : sourceFamily.Nonempty)
    (hsourceDeltaOne : sourceDelta ≤ 1)
    (hsourceMass : 0 < sourceShading.mass)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hsourceDirection : ∀ index,
      (sourceFamily.tube index).direction =
        wz1PaperDirection (sourceFamily.tube index))
    (hsourceBase : ∀ index, ‖(sourceFamily.tube index).base‖ ≤ 5)
    (hsourcePackingDistinct : WZ1PaperIsEssentiallyDistinct
      (pureWZ2CenteredPackingFamily sourceFamily))
    (scale : ℝ) (hscale : 1 ≤ scale)
    (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hradius : scale * (6 * sourceDelta) +
      targetDelta * Real.sqrt 3 ≤ 6 * targetDelta)
    (hscaleSourceSmall : scale * sourceDelta ≤ 1 / 1000)
    (hscheduleLoss : 0 < scheduleLoss)
    (hsourcePower : Kakeya.realRpowENN sourceDelta (-scheduleLoss) ≤
      sourceConstant)
    (hsourceTwo : 2 < sourceConstant) :
    Nonempty (PureWZ2FixedFinalIsotropicPreparationData
      (targetDelta := targetDelta) (scheduleLoss := scheduleLoss)
      sourceShading sourceConstant scale) := by
  let boxParameters := fixedFiniteScheduleParameters ambientCWA.1
    hsourceDeltaOne hscheduleLoss hsourcePower hsourceTwo ambientCWA.2.1.2
  let box := Classical.choice <|
    pureWZ2_final_isotropic_box_preparation sourceShading ambientCWA hfamily
      hsourceDeltaOne hsourceMass scale hscale hscaleSourceSmall
      boxParameters.levelCount hsourceTwo boxParameters.target_le_power
      boxParameters.schedule_finite boxParameters.square_le_schedule
  have hsourceOne : (1 : ENNReal) ≤ sourceConstant :=
    (by norm_num : (1 : ENNReal) ≤ 2).trans hsourceTwo.le
  have hsourcePowerBox : Kakeya.realRpowENN sourceDelta (-scheduleLoss) ≤
      box.regularized.outputConstant :=
    hsourcePower.trans <| box.regularized.ambientConstant_le_outputConstant
      hsourceOne boxParameters.square_le_schedule
  have hboxTwo : 2 < box.regularized.outputConstant :=
    box.regularized.outputConstant_gt_two
      hsourceTwo boxParameters.square_le_schedule
  let cleanupParameters := fixedFiniteScheduleParameters ambientCWA.1
    hsourceDeltaOne hscheduleLoss hsourcePowerBox hboxTwo
    box.regularized.cwa_nearby.2.1.2
  rcases pureWZ2_final_isotropic_preparation_of_box sourceShading ambientCWA
      hfamily hsourceDeltaOne hsourceMass hsourceLine hsourceDirection
      hsourceBase hsourcePackingDistinct scale hscale htargetDelta
      htargetDeltaSmall hradius hscaleSourceSmall boxParameters.levelCount
      hsourceTwo boxParameters.target_le_power boxParameters.schedule_finite
      boxParameters.square_le_schedule box cleanupParameters.levelCount
      hboxTwo cleanupParameters.target_le_power cleanupParameters.schedule_finite
      (by simpa [pow_two] using cleanupParameters.square_le_schedule) with
    ⟨preparation, hpreparationBox⟩
  have hpreparationBoxOne :
      (1 : ENNReal) ≤ preparation.box.regularized.outputConstant := by
    rw [hpreparationBox]
    exact (by norm_num : (1 : ENNReal) ≤ 2).trans hboxTwo.le
  have hcleanupSchedule :
      preparation.box.regularized.outputConstant *
          preparation.box.regularized.outputConstant ≤
        cleanupParameters.scheduleConstant := by
    rw [hpreparationBox]
    exact cleanupParameters.square_le_schedule
  have hboxToCleanup : preparation.box.regularized.outputConstant ≤
      preparation.cleanupRegularized.outputConstant :=
    preparation.cleanupRegularized.ambientConstant_le_outputConstant
      hpreparationBoxOne hcleanupSchedule
  have hsourcePowerCleanup :
      Kakeya.realRpowENN sourceDelta (-scheduleLoss) ≤
        preparation.cleanupRegularized.outputConstant := by
    calc
      Kakeya.realRpowENN sourceDelta (-scheduleLoss) ≤
          box.regularized.outputConstant := hsourcePowerBox
      _ = preparation.box.regularized.outputConstant := by
        rw [hpreparationBox]
      _ ≤ preparation.cleanupRegularized.outputConstant := hboxToCleanup
  exact ⟨{ boxParameters := boxParameters
           boxLevelCount_eq := rfl
           box := box
           cleanupParameters := cleanupParameters
           cleanupLevelCount_eq := rfl
           preparation := preparation
           preparation_box := hpreparationBox
           sourcePower_le_boxOutput := hsourcePowerBox
           sourcePower_le_cleanupOutput := hsourcePowerCleanup }⟩

namespace PureWZ2FinalIsotropicPreparationData

/-- The canonical midpoint-centered isotropic saturation used throughout the
final preparation and quotient stages. -/
def targetShading
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale) :
    WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) data.box.regularized.selected.family
        data.box.popular.center scale) :=
  pureWZ2IsotropicCenteredPaperShading data.box.selectedShading
    data.box.popular.center scale data.box.regularized.cwa_nearby.1
    data.target_delta_pos data.target_delta_small data.scale_one
    data.radius_budget
    (data.box.selectedShading_union_subset_ball data.scale_one
      data.scale_source_small)

/-- The exact pre-isotropic shading restricted to the source indices retained
after the target distinctness cleanup. -/
def finalSourceShading
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale) :
    WZ1PaperTubeShading data.cleanupRegularized.selected.family :=
  restrictPaperShading data.cleanupRegularized.selected
    data.box.selectedShading

@[simp] theorem finalSourceShading_carrier
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale)
    (index : Fin data.cleanupRegularized.selected.family.card) :
    data.finalSourceShading.carrier index =
      data.box.selectedShading.carrier
        (data.cleanupRegularized.selected.embedding index) := rfl

theorem finalSourceShading_union_subset_ball
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale) :
    data.finalSourceShading.union ⊆
      Metric.closedBall data.box.popular.center (1 / (2 * scale)) :=
  (restrictPaperShading_union_subset data.cleanupRegularized.selected
    data.box.selectedShading).trans
      (data.box.selectedShading_union_subset_ball data.scale_one
        data.scale_source_small)

/-- The second final-isotropic dyadic level retains an explicit fraction of
the exact target normalization. -/
theorem cleanupSelectedWeightLevel_lower
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale) :
    pureWZ2IsotropicCleanupNormalization data.cleanup / 4 ≤
      data.cleanupRegularized.selectedWeightLevel := by
  apply data.cleanupRegularized.normalization_div_four_le_selectedWeightLevel
  rw [data.cleanup.sourceWeight_sum]
  unfold pureWZ2IsotropicCleanupNormalization
  have hcardZero : data.box.regularized.selected.family.enncard ≠ 0 := by
    change (data.box.regularized.selected.family.card : ENNReal) ≠ 0
    exact_mod_cast data.box.regularized.selected_nonempty.ne'
  have hcardTop : data.box.regularized.selected.family.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  rw [ENNReal.div_mul_cancel hcardZero hcardTop]

/-- The exact-image Jacobian and the first selected dyadic level give a
denominator-free lower bound for the normalization used by the second
final-isotropic source regularization. -/
theorem cleanupNormalization_lower_of_boxLevel
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale) :
    (ENNReal.ofReal (scale ^ 3) *
        data.box.regularized.selectedWeightLevel) /
      (pureWZ2IsotropicCenteredConflictDegree sourceDelta targetDelta + 1 :
        ENNReal) ≤
      pureWZ2IsotropicCleanupNormalization data.cleanup := by
  let card := data.box.regularized.selected.family.enncard
  let degree : ENNReal :=
    pureWZ2IsotropicCenteredConflictDegree sourceDelta targetDelta + 1
  have hcardZero : card ≠ 0 := by
    dsimp only [card]
    change (data.box.regularized.selected.family.card : ENNReal) ≠ 0
    exact_mod_cast data.box.regularized.selected_nonempty.ne'
  have hcardTop : card ≠ ⊤ := by
    dsimp only [card]
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hboxMass : data.box.regularized.selectedWeightLevel * card ≤
      data.box.selectedShading.mass := by
    rw [data.box.selectedShading_mass_eq_selectedWeight]
    exact data.box.regularized
      |>.selectedWeightLevel_mul_selectedCard_le_selectedWeight
  let exactTarget := pureWZ2IsotropicCenteredPaperShading
    data.box.selectedShading data.box.popular.center scale
    data.box.regularized.cwa_nearby.1 data.target_delta_pos
    data.target_delta_small data.scale_one data.radius_budget
    (data.box.selectedShading_union_subset_ball
      data.scale_one data.scale_source_small)
  have htargetMass : ENNReal.ofReal (scale ^ 3) *
        data.box.selectedShading.mass ≤ exactTarget.mass := by
    exact pureWZ2IsotropicCenteredPaperShading_mass_lower
      data.box.selectedShading data.box.popular.center scale
      data.box.regularized.cwa_nearby.1 data.target_delta_pos
      data.target_delta_small data.scale_one data.radius_budget
      (data.box.selectedShading_union_subset_ball
        data.scale_one data.scale_source_small)
  have hbeforeCleanup :
      (ENNReal.ofReal (scale ^ 3) *
        data.box.regularized.selectedWeightLevel) * card ≤
      degree * data.cleanup.restrictedShading.mass := by
    calc
      (ENNReal.ofReal (scale ^ 3) *
          data.box.regularized.selectedWeightLevel) * card =
        ENNReal.ofReal (scale ^ 3) *
          (data.box.regularized.selectedWeightLevel * card) := by ring
      _ ≤ ENNReal.ofReal (scale ^ 3) *
          data.box.selectedShading.mass := by gcongr
      _ ≤ exactTarget.mass := htargetMass
      _ ≤ degree * data.cleanup.restrictedShading.mass := by
        simpa only [degree, exactTarget] using data.cleanup_mass_lower
  have hdivDegree :
      ((ENNReal.ofReal (scale ^ 3) *
        data.box.regularized.selectedWeightLevel) * card) / degree ≤
      data.cleanup.restrictedShading.mass := by
    exact ENNReal.div_le_of_le_mul <| by
      simpa [mul_comm] using hbeforeCleanup
  unfold pureWZ2IsotropicCleanupNormalization
  apply (ENNReal.le_div_iff_mul_le (Or.inl hcardZero)
    (Or.inl hcardTop)).2
  simpa [card, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    hdivDegree

/-- The two final-isotropic selections retain a denominator-free density
floor.  The selected family cardinality appears in both the exact-image mass
and the cleanup normalization and cancels completely. -/
theorem cleanupSelectedWeightLevel_lower_of_boxLevel
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale) :
    ((ENNReal.ofReal (scale ^ 3) *
        data.box.regularized.selectedWeightLevel) /
      (pureWZ2IsotropicCenteredConflictDegree sourceDelta targetDelta + 1 :
        ENNReal)) / 4 ≤
      data.cleanupRegularized.selectedWeightLevel := by
  let card := data.box.regularized.selected.family.enncard
  let degree : ENNReal :=
    pureWZ2IsotropicCenteredConflictDegree sourceDelta targetDelta + 1
  have hcardZero : card ≠ 0 := by
    dsimp only [card]
    change (data.box.regularized.selected.family.card : ENNReal) ≠ 0
    exact_mod_cast data.box.regularized.selected_nonempty.ne'
  have hcardTop : card ≠ ⊤ := by
    dsimp only [card]
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hdegreeZero : degree ≠ 0 := by
    dsimp only [degree]
    positivity
  have hdegreeTop : degree ≠ ⊤ := by
    dsimp only [degree]
    simp
  have hboxMass : data.box.regularized.selectedWeightLevel * card ≤
      data.box.selectedShading.mass := by
    rw [data.box.selectedShading_mass_eq_selectedWeight]
    exact data.box.regularized
      |>.selectedWeightLevel_mul_selectedCard_le_selectedWeight
  let exactTarget := pureWZ2IsotropicCenteredPaperShading
    data.box.selectedShading data.box.popular.center scale
    data.box.regularized.cwa_nearby.1 data.target_delta_pos
    data.target_delta_small data.scale_one data.radius_budget
    (data.box.selectedShading_union_subset_ball
      data.scale_one data.scale_source_small)
  have htargetMass : ENNReal.ofReal (scale ^ 3) *
        data.box.selectedShading.mass ≤
      exactTarget.mass := by
    exact pureWZ2IsotropicCenteredPaperShading_mass_lower
      data.box.selectedShading data.box.popular.center scale
      data.box.regularized.cwa_nearby.1 data.target_delta_pos
      data.target_delta_small data.scale_one data.radius_budget
      (data.box.selectedShading_union_subset_ball
        data.scale_one data.scale_source_small)
  have hbeforeCleanup :
      (ENNReal.ofReal (scale ^ 3) *
        data.box.regularized.selectedWeightLevel) * card ≤
      degree * data.cleanup.restrictedShading.mass := by
    calc
      (ENNReal.ofReal (scale ^ 3) *
          data.box.regularized.selectedWeightLevel) * card =
        ENNReal.ofReal (scale ^ 3) *
          (data.box.regularized.selectedWeightLevel * card) := by ring
      _ ≤ ENNReal.ofReal (scale ^ 3) *
          data.box.selectedShading.mass := by gcongr
      _ ≤ exactTarget.mass := htargetMass
      _ ≤ degree * data.cleanup.restrictedShading.mass := by
        simpa only [degree, exactTarget] using data.cleanup_mass_lower
  have hdivDegree :
      ((ENNReal.ofReal (scale ^ 3) *
        data.box.regularized.selectedWeightLevel) * card) / degree ≤
      data.cleanup.restrictedShading.mass := by
    exact ENNReal.div_le_of_le_mul <| by
      simpa [mul_comm] using hbeforeCleanup
  have hnormalization :
      (ENNReal.ofReal (scale ^ 3) *
        data.box.regularized.selectedWeightLevel) / degree ≤
      pureWZ2IsotropicCleanupNormalization data.cleanup := by
    unfold pureWZ2IsotropicCleanupNormalization
    apply (ENNReal.le_div_iff_mul_le (Or.inl hcardZero)
      (Or.inl hcardTop)).2
    simpa [card, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hdivDegree
  exact (ENNReal.div_le_div_right hnormalization 4).trans
    data.cleanupSelectedWeightLevel_lower

/-- Ratio-aware output envelope for the cleanup-supported regularization in
the final-isotropic stage.  The explicit lower floor keeps the exact-image
Jacobian and centered-conflict loss together when controlling the inverse
normalization. -/
theorem cleanupOutputConstant_le_ratioEnvelope_of_boxLevel
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant
      ambientBound scheduleBound ratioBound logEnvelope : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale)
    (hambient : data.box.regularized.outputConstant ≤ ambientBound)
    (hschedule : cleanupScheduleConstant ≤ scheduleBound)
    (hratioFloor :
      ((ENNReal.ofReal (scale ^ 3) *
          data.box.regularized.selectedWeightLevel) /
        (pureWZ2IsotropicCenteredConflictDegree sourceDelta targetDelta + 1 :
          ENNReal))⁻¹ * 8 ≤ ratioBound)
    (hlog :
      (Nat.log 2
        (2 * data.box.regularized.selected.family.card) + 1 : ENNReal) ≤
          logEnvelope)
    (hlogOne : 1 ≤ logEnvelope) :
    data.cleanupRegularized.outputConstant ≤
      PureWZ2ExternalWeightRegularizationData.pureWZ2ExternalWeightRatioOutputEnvelope
        ambientBound scheduleBound ratioBound logEnvelope
          cleanupLevelCount := by
  apply data.cleanupRegularized
    |>.outputConstant_le_externalWeightRatioOutputEnvelope
      hambient hschedule
  · exact (mul_le_mul_right' ((ENNReal.inv_le_inv).2
      data.cleanupNormalization_lower_of_boxLevel) 8).trans hratioFloor
  · exact hlog
  · exact hlogOne

@[simp] theorem isotropicFinalShading_carrier
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale)
    (index : Fin data.cleanupRegularized.selected.family.card) :
    data.cleanupRegularized.isotropicCleanupFinalShading.carrier index =
      wz1PaperCubicalSaturation targetDelta
        (pureWZ2IsotropicMap data.box.popular.center scale ''
          data.finalSourceShading.carrier index) := by
  rw [data.cleanupRegularized.isotropicCleanupFinalShading_carrier,
    pureWZ2IsotropicCenteredPaperShading_carrier,
    pureWZ2IsotropicPaperShading_carrier]
  rfl

@[simp] theorem isotropicFinalShading_carrier_eq_source
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale)
    (index : Fin data.cleanupRegularized.selected.family.card) :
    data.cleanupRegularized.isotropicCleanupFinalShading.carrier index =
      (pureWZ2IsotropicCenteredPaperShading data.finalSourceShading
        data.box.popular.center scale data.box.regularized.cwa_nearby.1
        data.target_delta_pos data.target_delta_small data.scale_one
        data.radius_budget
        data.finalSourceShading_union_subset_ball).carrier
          index := by
  exact data.isotropicFinalShading_carrier index

theorem finalSource_line_class
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale) :
    WZ1PaperIsLineClass data.cleanupRegularized.selected.family :=
  (data.source_line.subfamily data.box.regularized.selected).subfamily
    data.cleanupRegularized.selected

theorem finalSource_direction
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale)
    (index : Fin data.cleanupRegularized.selected.family.card) :
    (data.cleanupRegularized.selected.family.tube index).direction =
      wz1PaperDirection
        (data.cleanupRegularized.selected.family.tube index) := by
  rw [data.cleanupRegularized.selected.tube_eq,
    data.box.regularized.selected.tube_eq]
  exact data.source_direction _

theorem finalSource_base_le_five
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale)
    (index : Fin data.cleanupRegularized.selected.family.card) :
    ‖(data.cleanupRegularized.selected.family.tube index).base‖ ≤ 5 := by
  rw [data.cleanupRegularized.selected.tube_eq,
    data.box.regularized.selected.tube_eq]
  exact data.source_base _

theorem center_height_bound
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale) :
    |data.box.popular.center 2| ≤ 1 :=
  data.box.popular.center_mem (2 : Fin 3)

theorem scale_source_le_target
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale) :
    scale * sourceDelta ≤ targetDelta := by
  have hsqrt : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  nlinarith [data.radius_budget, data.target_delta_pos]

theorem finalSource_zeroPoint_bound
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale)
    (index : Fin data.cleanupRegularized.selected.family.card)
    (coordinate : Fin 2) :
    |(pureWZ2IsotropicMap data.box.popular.center scale
      (wz1PaperAxisPointAtHeight
        (data.cleanupRegularized.selected.family.tube index)
        (data.box.popular.center 2))) coordinate.castSucc| ≤ 1 / 3 := by
  rw [data.cleanupRegularized.selected.tube_eq]
  exact data.box.isotropic_zeroPoint_bound
    data.box.regularized.cwa_nearby.1 data.scale_one data.scale_source_small
    data.source_line (data.cleanupRegularized.selected.embedding index)
    coordinate

/-- Build the final quotient schedule with all geometric side conditions
discharged by the preparation data. -/
theorem toQuotientAssembly
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant
      sourceScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale)
    (parentLevelCount : ℕ)
    (hsourceTwo : 2 < data.cleanupRegularized.outputConstant)
    (hsourceDeltaOne : sourceDelta ≤ 1)
    (hlevels : ENNReal.ofReal (1 / sourceDelta) ≤
      data.cleanupRegularized.outputConstant ^ parentLevelCount)
    (hsourceScheduleConstant :
      data.cleanupRegularized.outputConstant ^ 2 ≤ sourceScheduleConstant) :
    Nonempty (PureWZ2IsotropicCleanupQuotientAssemblyData
      data.cleanupRegularized sourceScheduleConstant parentLevelCount) := by
  apply pureWZ2_isotropic_cleanup_quotient_assembly
    data.cleanupRegularized sourceScheduleConstant parentLevelCount hsourceTwo
    hsourceDeltaOne hlevels (by simpa [pow_two] using hsourceScheduleConstant)
    data.scale_one data.center_height_bound data.target_delta_pos
    data.finalSource_line_class data.finalSource_base_le_five
    data.finalSource_zeroPoint_bound

end PureWZ2FinalIsotropicPreparationData

/-- The final quotient assembly with its internally selected parent schedule. -/
structure PureWZ2AutoFinalQuotientAssemblyData
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant : ENNReal} {scale : ℝ}
    (auto : PureWZ2AutoFinalIsotropicPreparationData
      (targetDelta := targetDelta) sourceShading sourceConstant scale) where
  parentParameters :
    PureWZ2FiniteScheduleParameters
      auto.preparation.cleanupRegularized.outputConstant
      (ENNReal.ofReal (1 / sourceDelta))
  assembly : PureWZ2IsotropicCleanupQuotientAssemblyData
    auto.preparation.cleanupRegularized parentParameters.scheduleConstant
    parentParameters.levelCount

namespace PureWZ2AutoFinalQuotientAssemblyData

/-- Produce final nearby CWA with a canonical finite target constant. -/
theorem toNearbyCWAAuto
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant : ENNReal} {scale : ℝ}
    {auto : PureWZ2AutoFinalIsotropicPreparationData
      (targetDelta := targetDelta) sourceShading sourceConstant scale}
    (quotient : PureWZ2AutoFinalQuotientAssemblyData auto) :
    Nonempty
      (PureWZ2IsotropicCleanupQuotientAssemblyData.PureWZ2AutoIsotropicNearbyCWAData
        quotient.assembly) := by
  have hsourceDelta : 0 < sourceDelta :=
    auto.preparation.box.regularized.cwa_nearby.1
  have hsourceTarget : sourceDelta ≤ targetDelta := by
    have hscaleSource : sourceDelta ≤ scale * sourceDelta := by
      simpa using mul_le_mul_of_nonneg_right
        auto.preparation.scale_one hsourceDelta.le
    exact hscaleSource.trans auto.preparation.scale_source_le_target
  exact quotient.assembly.toNearbyCWAAuto
    auto.preparation.scale_one auto.preparation.center_height_bound
    hsourceDelta hsourceTarget auto.preparation.scale_source_le_target
    auto.preparation.finalSource_line_class
    auto.preparation.finalSource_base_le_five
    quotient.parentParameters.schedule_finite.2

end PureWZ2AutoFinalQuotientAssemblyData

namespace PureWZ2AutoFinalIsotropicPreparationData

/-- The output constant after the final-isotropic cleanup regularization is
still strictly larger than two. -/
theorem cleanupOutputConstant_gt_two
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant : ENNReal} {scale : ℝ}
    (auto : PureWZ2AutoFinalIsotropicPreparationData
      (targetDelta := targetDelta) sourceShading sourceConstant scale)
    (hsourceTwo : 2 < sourceConstant) :
    2 < auto.preparation.cleanupRegularized.outputConstant := by
  have hboxTwo : 2 < auto.box.regularized.outputConstant :=
    auto.box.regularized.outputConstant_gt_two
      hsourceTwo auto.boxParameters.square_le_schedule
  have hpreparationBoxTwo :
      2 < auto.preparation.box.regularized.outputConstant := by
    rw [auto.preparation_box]
    exact hboxTwo
  apply auto.preparation.cleanupRegularized.outputConstant_gt_two
    hpreparationBoxTwo
  rw [auto.preparation_box]
  exact auto.cleanupParameters.square_le_schedule

/-- Automatically choose the last finite parent schedule and build the final
isotropic quotient assembly. -/
theorem toQuotientAssemblyAuto
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant : ENNReal} {scale : ℝ}
    (auto : PureWZ2AutoFinalIsotropicPreparationData
      (targetDelta := targetDelta) sourceShading sourceConstant scale)
    (hsourceDeltaOne : sourceDelta ≤ 1)
    (hsourceTwo : 2 < sourceConstant) :
    Nonempty (PureWZ2AutoFinalQuotientAssemblyData auto) := by
  have hcleanupTwo := auto.cleanupOutputConstant_gt_two hsourceTwo
  let parentParameters := Classical.choice <|
    exists_finite_schedule_parameters
      (target := ENNReal.ofReal (1 / sourceDelta)) hcleanupTwo
      auto.preparation.cleanupRegularized.cwa_nearby.2.1.2
      ENNReal.ofReal_ne_top
  let assembly := Classical.choice <|
    auto.preparation.toQuotientAssembly parentParameters.levelCount
      hcleanupTwo hsourceDeltaOne parentParameters.target_le_power
      (by simpa [pow_two] using parentParameters.square_le_schedule)
  exact ⟨{ parentParameters := parentParameters, assembly := assembly }⟩

end PureWZ2AutoFinalIsotropicPreparationData

/-- Final quotient assembly whose parent schedule depth is fixed by the same
pre-runtime loss used in the two final-isotropic regularizations. -/
structure PureWZ2FixedFinalQuotientAssemblyData
    {sourceDelta targetDelta scheduleLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant : ENNReal} {scale : ℝ}
    (fixed : PureWZ2FixedFinalIsotropicPreparationData
      (targetDelta := targetDelta) (scheduleLoss := scheduleLoss)
      sourceShading sourceConstant scale) where
  parentParameters : PureWZ2FiniteScheduleParameters
    fixed.preparation.cleanupRegularized.outputConstant
    (ENNReal.ofReal (1 / sourceDelta))
  parentLevelCount_eq :
    parentParameters.levelCount = pureWZ2FixedScheduleLevelCount scheduleLoss
  assembly : PureWZ2IsotropicCleanupQuotientAssemblyData
    fixed.preparation.cleanupRegularized parentParameters.scheduleConstant
    parentParameters.levelCount
  sourcePower_le_output :
    Kakeya.realRpowENN sourceDelta (-scheduleLoss) ≤
      fixed.preparation.cleanupRegularized.outputConstant

namespace PureWZ2FixedFinalIsotropicPreparationData

theorem cleanupOutputConstant_gt_two
    {sourceDelta targetDelta scheduleLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant : ENNReal} {scale : ℝ}
    (fixed : PureWZ2FixedFinalIsotropicPreparationData
      (targetDelta := targetDelta) (scheduleLoss := scheduleLoss)
      sourceShading sourceConstant scale)
    (hsourceTwo : 2 < sourceConstant) :
    2 < fixed.preparation.cleanupRegularized.outputConstant := by
  have hboxTwo : 2 < fixed.box.regularized.outputConstant :=
    fixed.box.regularized.outputConstant_gt_two
      hsourceTwo fixed.boxParameters.square_le_schedule
  have hpreparationBoxTwo :
      2 < fixed.preparation.box.regularized.outputConstant := by
    rw [fixed.preparation_box]
    exact hboxTwo
  apply fixed.preparation.cleanupRegularized.outputConstant_gt_two
    hpreparationBoxTwo
  rw [fixed.preparation_box]
  exact fixed.cleanupParameters.square_le_schedule

/-- Build the last parent schedule with fixed pre-runtime depth. -/
theorem toQuotientAssemblyFixed
    {sourceDelta targetDelta scheduleLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant : ENNReal} {scale : ℝ}
    (fixed : PureWZ2FixedFinalIsotropicPreparationData
      (targetDelta := targetDelta) (scheduleLoss := scheduleLoss)
      sourceShading sourceConstant scale)
    (hscheduleLoss : 0 < scheduleLoss)
    (hsourceDeltaOne : sourceDelta ≤ 1)
    (hsourceTwo : 2 < sourceConstant) :
    Nonempty (PureWZ2FixedFinalQuotientAssemblyData fixed) := by
  have hcleanupTwo := fixed.cleanupOutputConstant_gt_two hsourceTwo
  let parentParameters := fixedFiniteScheduleParameters
    fixed.preparation.cleanupRegularized.cwa_nearby.1 hsourceDeltaOne
    hscheduleLoss fixed.sourcePower_le_cleanupOutput hcleanupTwo
    fixed.preparation.cleanupRegularized.cwa_nearby.2.1.2
  let assembly := Classical.choice <|
    fixed.preparation.toQuotientAssembly parentParameters.levelCount
      hcleanupTwo hsourceDeltaOne parentParameters.target_le_power
      (by simpa [pow_two] using parentParameters.square_le_schedule)
  exact ⟨{ parentParameters := parentParameters
           parentLevelCount_eq := rfl
           assembly := assembly
           sourcePower_le_output := fixed.sourcePower_le_cleanupOutput }⟩

end PureWZ2FixedFinalIsotropicPreparationData

namespace PureWZ2FixedFinalQuotientAssemblyData

/-- Produce the final nearby-CWA certificate at the prescribed power
constant.  Unlike `toNearbyCWAAuto`, this theorem does not choose a runtime
finite maximum: every scale-window and coordinate cost must already have
been absorbed into `targetDelta ^ (-nearbyLoss)`. -/
theorem toNearbyCWAFixed
    {sourceDelta targetDelta scheduleLoss nearbyLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant : ENNReal} {scale : ℝ}
    {fixed : PureWZ2FixedFinalIsotropicPreparationData
      (targetDelta := targetDelta) (scheduleLoss := scheduleLoss)
      sourceShading sourceConstant scale}
    (quotient : PureWZ2FixedFinalQuotientAssemblyData fixed)
    (hnearbyLoss : 0 < nearbyLoss)
    (hscaleBudget : isotropicQuotientScaleWindowConstant
      scale quotient.parentParameters.scheduleConstant ≤
        Kakeya.realRpowENN targetDelta (-nearbyLoss))
    (hcoordinateBudget : ∀ coordinate,
      quotient.assembly.nearbyCWACoordinateBudget coordinate ≤
        Kakeya.realRpowENN targetDelta (-nearbyLoss)) :
    WZ2PaperPureCWAAtNearbyScales
      (quotient.assembly.quotient.jointlyRegularizedFine
        (pureWZ2IsotropicCleanupJointWeight
          fixed.preparation.cleanupRegularized)
        quotient.assembly.selection
        quotient.assembly.joint.selected).family
      (Kakeya.realRpowENN targetDelta (-nearbyLoss)) := by
  have hsourceDelta : 0 < sourceDelta :=
    fixed.preparation.box.regularized.cwa_nearby.1
  have hsourceTarget : sourceDelta ≤ targetDelta := by
    have hscaleSource : sourceDelta ≤ scale * sourceDelta := by
      simpa using mul_le_mul_of_nonneg_right
        fixed.preparation.scale_one hsourceDelta.le
    exact hscaleSource.trans fixed.preparation.scale_source_le_target
  have htargetFinite : WZ2PaperFiniteErrorConstant
      (Kakeya.realRpowENN targetDelta (-nearbyLoss)) := by
    constructor
    · rw [Kakeya.realRpowENN, ENNReal.one_le_ofReal]
      have hpow := Real.rpow_le_rpow_of_exponent_ge
        fixed.preparation.target_delta_pos
        (fixed.preparation.target_delta_small.trans (by norm_num))
        (show -nearbyLoss ≤ (0 : ℝ) by linarith)
      simpa using hpow
    · simp [Kakeya.realRpowENN]
  exact quotient.assembly.toNearbyCWA
    fixed.preparation.scale_one fixed.preparation.center_height_bound
    hsourceDelta hsourceTarget fixed.preparation.scale_source_le_target
    fixed.preparation.finalSource_line_class
    fixed.preparation.finalSource_base_le_five htargetFinite hscaleBudget
    (by
      intro coordinate
      simpa [PureWZ2IsotropicCleanupQuotientAssemblyData.nearbyCWACoordinateBudget]
        using hcoordinateBudget coordinate)

end PureWZ2FixedFinalQuotientAssemblyData

end Kakeya.Assouad

end
