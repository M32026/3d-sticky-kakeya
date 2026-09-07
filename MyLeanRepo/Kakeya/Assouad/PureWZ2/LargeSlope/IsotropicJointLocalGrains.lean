import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicFinalPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicRestrictedSaturationLocalGrains

/-!
# Local grains on the final isotropic quotient family

This module restricts the genuine inverse-transpose exact normal to the two
source selections made before the final similarity, and then extends it over
the cubical shading restricted to the final quotient family.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- The exact pre-isotropic target index underlying one final isotropic
quotient index. -/
def PureWZ2IsotropicCleanupQuotientAssemblyData.preIsotropicIndex
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant
      sourceScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount parentLevelCount : ℕ} {scale : ℝ}
    {preparation : PureWZ2FinalIsotropicPreparationData
      (targetDelta := targetDelta) sourceShading sourceConstant
      boxScheduleConstant cleanupScheduleConstant boxLevelCount
      cleanupLevelCount scale}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData
      preparation.cleanupRegularized sourceScheduleConstant parentLevelCount) :
    Fin (assembly.quotient.jointlyRegularizedFine
      (pureWZ2IsotropicCleanupJointWeight preparation.cleanupRegularized)
      assembly.selection assembly.joint.selected).family.card →
      Fin sourceFamily.card :=
  fun index => preparation.box.regularized.selected.embedding
    (preparation.cleanupRegularized.selected.embedding
      (assembly.joint.finalSourceIndex index))

/-- The exact source region used for the final isotropic normal. -/
def PureWZ2FinalIsotropicPreparationData.exactRestricted
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale) : Set Point3 :=
  data.finalSourceShading.union

theorem PureWZ2FinalIsotropicPreparationData.exactRestricted_subset
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount : ℕ} {scale : ℝ}
    (data : PureWZ2FinalIsotropicPreparationData (targetDelta := targetDelta)
      sourceShading sourceConstant boxScheduleConstant cleanupScheduleConstant
      boxLevelCount cleanupLevelCount scale) :
    data.exactRestricted ⊆ sourceShading.union := by
  exact (restrictPaperShading_union_subset data.cleanupRegularized.selected
    data.box.selectedShading).trans <|
      (restrictPaperShading_union_subset data.box.regularized.selected
        data.box.popular.restricted).trans <|
        paperSubshading_union_subset data.box.popular.restricted_subshading

/-- The cubical witness for the final joint shading stays in the exact source
carrier carrying the same pre-isotropic tube index. -/
theorem PureWZ2IsotropicCleanupQuotientAssemblyData.final_tubeWitness
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant
      sourceScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount parentLevelCount : ℕ} {scale : ℝ}
    {preparation : PureWZ2FinalIsotropicPreparationData
      (targetDelta := targetDelta) sourceShading sourceConstant
      boxScheduleConstant cleanupScheduleConstant boxLevelCount
      cleanupLevelCount scale}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData
      preparation.cleanupRegularized sourceScheduleConstant parentLevelCount)
    (index : Fin (assembly.quotient.jointlyRegularizedFine
      (pureWZ2IsotropicCleanupJointWeight preparation.cleanupRegularized)
      assembly.selection assembly.joint.selected).family.card)
    (point : Point3) (hpoint : point ∈ assembly.finalShading.carrier index) :
    ∃ source : {point : Point3 // point ∈
        pureWZ2IsotropicMap preparation.box.popular.center scale ''
          preparation.exactRestricted},
      dist point (source : Point3) ≤ targetDelta * Real.sqrt 3 ∧
      (pureWZ2IsotropicInverse preparation.box.popular.center scale source :
        Point3) ∈ sourceShading.carrier (assembly.preIsotropicIndex index) := by
  have hambient : point ∈
      preparation.cleanupRegularized.isotropicCleanupFinalShading.carrier
        (assembly.joint.finalTargetIndex index) := by
    simpa only [assembly.finalShading_carrier] using hpoint
  have hcanonical : point ∈
      (pureWZ2IsotropicCenteredPaperShading preparation.finalSourceShading
        preparation.box.popular.center scale
        preparation.box.regularized.cwa_nearby.1
        preparation.target_delta_pos preparation.target_delta_small
        preparation.scale_one preparation.radius_budget
        preparation.finalSourceShading_union_subset_ball).carrier
          (assembly.joint.finalTargetIndex index) := by
    rw [← preparation.isotropicFinalShading_carrier_eq_source]
    exact hambient
  rcases pureWZ2IsotropicCenteredPaperShading_tubeWitness
      preparation.finalSourceShading preparation.box.popular.center scale
      preparation.box.regularized.cwa_nearby.1
      preparation.target_delta_pos preparation.target_delta_small
      preparation.scale_one preparation.radius_budget
      preparation.finalSourceShading_union_subset_ball
      (assembly.joint.finalTargetIndex index) point hcanonical with
    ⟨source, hdist, hsource⟩
  refine ⟨source, hdist, ?_⟩
  change (pureWZ2IsotropicInverse preparation.box.popular.center scale source :
    Point3) ∈ preparation.box.selectedShading.carrier
      (preparation.cleanupRegularized.selected.embedding
        (assembly.joint.finalSourceIndex index)) at hsource
  exact preparation.box.popular.restricted_subshading _ hsource

/-- The final isotropic quotient tube has the direction of its exact
pre-isotropic source tube. -/
theorem PureWZ2IsotropicCleanupQuotientAssemblyData.final_direction
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceConstant boxScheduleConstant cleanupScheduleConstant
      sourceScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount parentLevelCount : ℕ} {scale : ℝ}
    {preparation : PureWZ2FinalIsotropicPreparationData
      (targetDelta := targetDelta) sourceShading sourceConstant
      boxScheduleConstant cleanupScheduleConstant boxLevelCount
      cleanupLevelCount scale}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData
      preparation.cleanupRegularized sourceScheduleConstant parentLevelCount)
    (index : Fin (assembly.quotient.jointlyRegularizedFine
      (pureWZ2IsotropicCleanupJointWeight preparation.cleanupRegularized)
      assembly.selection assembly.joint.selected).family.card) :
    ((assembly.quotient.jointlyRegularizedFine
      (pureWZ2IsotropicCleanupJointWeight preparation.cleanupRegularized)
      assembly.selection assembly.joint.selected).family.tube index).direction =
      (sourceFamily.tube (assembly.preIsotropicIndex index)).direction := by
  change (pureWZ2PaperCenteredTube
      (pureWZ2IsotropicPaperTube preparation.box.popular.center scale
        (preparation.cleanupRegularized.selected.family.tube
          (assembly.joint.finalSourceIndex index)))).direction = _
  rw [pureWZ2PaperCenteredTube_direction,
    pureWZ2IsotropicPaperTube_paperDirection]
  rw [preparation.cleanupRegularized.selected.tube_eq,
    preparation.box.regularized.selected.tube_eq]
  change wz1PaperDirection
      (sourceFamily.tube (assembly.preIsotropicIndex index)) =
    (sourceFamily.tube (assembly.preIsotropicIndex index)).direction
  exact (preparation.source_direction (assembly.preIsotropicIndex index)).symm

/-- Transport the genuine anisotropic inverse-transpose normal to the final
isotropic quotient family.  The exact region, cubical shading, tube direction,
and nearby-CWA family all use the same final joint indices. -/
theorem PureWZ2IsotropicCleanupQuotientAssemblyData.toFinalLocalGrains
    {sourceDelta preDelta finalDelta c d m sigma : ℝ}
    {C sourceConstant boxScheduleConstant cleanupScheduleConstant
      sourceScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount parentLevelCount : ℕ}
    {ambientSource : Kakeya.Streamlined.TubeFamily sourceDelta}
    {ambientShading : WZ1PaperTubeShading ambientSource}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) ambientSource ambientShading
        g anisotropicCenter hcd hm}
    {sourceLocal : PureWZ2LocalGrainData ambientShading sigma C}
    (exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal)
    {scale : ℝ}
    (preparation : PureWZ2FinalIsotropicPreparationData
      (targetDelta := finalDelta) raw.exactShading sourceConstant
      boxScheduleConstant cleanupScheduleConstant boxLevelCount
      cleanupLevelCount scale)
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData
      preparation.cleanupRegularized sourceScheduleConstant parentLevelCount)
    {targetK : NNReal}
    (hK : (exact.K : ℝ) ≤ (targetK : ℝ) * scale)
    (hsmall :
      ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        (finalDelta * Real.sqrt 3) ≤ 1 / 2)
    (hone :
      4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) ≤ 1)
    (hincidenceBudget :
      3 * sourceDelta +
          4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
            (finalDelta * Real.sqrt 3) ≤ finalDelta)
    (hprojectionBudget :
      finalDelta * Real.sqrt 3 +
          (Real.sqrt 3 / 200) *
            (4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
              (finalDelta * Real.sqrt 3)) ≤
        2 * finalDelta)
    (sourceRho : ∀ rho : ℝ, finalDelta ≤ rho → rho ≤ 1 → ℝ)
    (hsourceRhoLower : ∀ rho hrhoLower hrhoOne,
      sourceDelta ≤ sourceRho rho hrhoLower hrhoOne)
    (hsourceRhoOne : ∀ rho hrhoLower hrhoOne,
      sourceRho rho hrhoLower hrhoOne ≤ 1)
    (hball : ∀ rho hrhoLower hrhoOne,
      ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          ((Real.sqrt rho + 2 * (finalDelta * Real.sqrt 3)) / scale) ≤
        Real.sqrt (sourceRho rho hrhoLower hrhoOne))
    (hbase : ∀ rho hrhoLower hrhoOne,
      ∀ exactPoint : {point : Point3 //
        point ∈ pureWZ2IsotropicMap preparation.box.popular.center scale ''
          preparation.exactRestricted},
      (scale /
          ‖dPhiInvT g c d m
            (sourceLocal.planeMap
              (raw.exactSourcePoint
                (pureWZ2IsotropicExactSourcePoint
                  preparation.box.popular.center
                  (lt_of_lt_of_le (by norm_num) preparation.scale_one)
                  ⟨exactPoint, Set.image_mono
                    preparation.exactRestricted_subset
                    exactPoint.property⟩)))‖) *
        sourceRho rho hrhoLower hrhoOne ≤ rho) :
    Nonempty (PureWZ2LocalGrainData assembly.finalShading sigma (15 * C)) := by
  have hscalePos : 0 < scale :=
    lt_of_lt_of_le (by norm_num) preparation.scale_one
  have hrestrictedSelected : preparation.exactRestricted ⊆
      preparation.box.selectedShading.union :=
    restrictPaperShading_union_subset preparation.cleanupRegularized.selected
      preparation.box.selectedShading
  refine exact.toRestrictedIsotropicLocalGrains
    (exactRestricted := preparation.exactRestricted)
    preparation.exactRestricted_subset preparation.box.popular.center
    hscalePos assembly.finalShading preparation.target_delta_pos hK
    (mul_nonneg preparation.target_delta_pos.le (Real.sqrt_nonneg 3)) ?_
    hsmall hone rfl
    (div_nonneg (Real.sqrt_nonneg 3) (by norm_num)) ?_
    assembly.preIsotropicIndex assembly.final_direction ?_
    hincidenceBudget hprojectionBudget sourceRho hsourceRhoLower
    hsourceRhoOne hball hbase
  · rintro ⟨point, index, hpoint⟩
    rcases assembly.final_tubeWitness index point hpoint with
      ⟨source, hdist, _⟩
    exact ⟨source, hdist⟩
  · intro source
    exact preparation.box.isotropicSelectedImage_norm_le
      preparation.scale_one preparation.scale_source_small
      ⟨source, Set.image_mono hrestrictedSelected source.property⟩
  · intro index point hpoint
    exact assembly.final_tubeWitness index point hpoint

end Kakeya.Assouad

end
