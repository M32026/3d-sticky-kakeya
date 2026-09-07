import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RootPlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63Lemma412OuterSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PreliminaryLocalGrain

/-!
# Stateful Lemma-4.12 terminal from a provenance-complete root plane map

This is the family-generic terminal used after the paper's plane-map
coarsening step.  The M7 binding is indexed by the canonical re-entry obtained
from the exact normalization stored in `rootMap`; an unrelated re-entry cannot
be supplied.  Every coordinate of the outer iteration restores extremality
and CWA before the next coordinate.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

/-- Run the stateful M7/M8 grain-structure iteration from any exact root plane
map.  The output is indexed by that same root normalization and carries the
same plane map restricted through the finite iteration. -/
theorem proposition63_preliminary_local_grain_of_root_map_outer_inputs_with_receipts
    {delta sigma initialInputLoss normalizationLoss currentReentryLoss
      densityLoss incidence gridLoss midLoss localLoss terminalReentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent N : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := currentReentryLoss) initialNormalized current)
    {coefficient : NNReal}
    (rootMap : Proposition63RootPlaneMapData
      (densityLoss := densityLoss) (incidence := incidence) reentry coefficient)
    (hrootSourceLoss : 0 < currentReentryLoss)
    (hrootNormalizationLoss : 0 < reentry.reentryNormalizationLoss)
    (ambientAxialEighth : ∀ tube point,
      point ∈ rootMap.root.normalization.frame ''
          rootMap.root.normalization.ordinaryRefined.carrier tube →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (schedule : Proposition63Lemma412ScheduleData
      sigma gridLoss delta midLoss N)
    (K : ℝ)
    (hgridLossMid : gridLoss ≤ midLoss)
    (inputs : Proposition63Lemma411OuterBindingInputs
      (incidence := incidence) schedule.central schedule.outer
      (rootMap.root.normalization.toPropStickyReentryData
        hrootSourceLoss hrootNormalizationLoss)
      K coefficient hgridLossMid)
    (hrootInput :
      reentry.reentryNormalizationLoss ≤ schedule.outer.loss 0)
    (hgridReentry : gridLoss ≤ terminalReentryLoss)
    (hrootReentry :
      reentry.reentryNormalizationLoss ≤ terminalReentryLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hincidenceNonnegative : 0 ≤ incidence)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (habsorbInterpolation :
      (100 : ℝ) * Real.rpow delta
          (-gridLoss - midLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-localLoss))
    (habsorbFine :
      (100 : ℝ) * Real.rpow delta
          (-midLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-localLoss)) :
    ∃ output : Proposition63PreliminaryLocalGrainData
        (localLoss := localLoss) (reentryLoss := terminalReentryLoss)
        rootMap.root.normalization,
      output.incidence = incidence ∧ output.lipschitz = coefficient := by
  let ambientReentry :=
    rootMap.root.normalization.toPropStickyReentryData
      hrootSourceLoss hrootNormalizationLoss
  rcases proposition63_lemma411_central_binding schedule.central
      schedule.outer ambientReentry K coefficient hgridLossMid inputs with
    ⟨binding⟩
  have currentExtremal : WZ2PaperCroppedIsExtremal sigma
      (schedule.outer.loss 0) rootMap.root.normalization.croppedFamily
      rootMap.root.normalization.croppedRefined :=
    rootMap.root.normalization.final_extremal.mono_loss hrootInput
  have currentCWA : WZ2PaperConvexWolffBound
      rootMap.root.normalization.croppedFamily
      (Kakeya.realRpowENN delta (-(schedule.outer.loss 0))) := by
    apply weaken_convex_wolff_bound
      rootMap.root.normalization.cropped_top_level_cwa
    exact realRpowENN_antitone
      rootMap.root.normalization.final_extremal.delta_pos
      rootMap.root.normalization.final_extremal.delta_le_one
      (by linarith [hrootInput])
  have currentMassPos :
      0 < rootMap.root.normalization.croppedRefined.mass :=
    cropped_extremal_shading_mass_pos
      rootMap.root.normalization.final_extremal
      rootMap.root.normalization.line_class hdeltaSmall
  let identitySub : PaperIsSubshading
      rootMap.root.normalization.croppedRefined
      rootMap.root.normalization.croppedRefined := fun _ => Set.Subset.rfl
  rcases binding.binding.run ambientAxialEighth rootMap.planeMap
      rootMap.lipschitz identitySub identitySub currentExtremal currentCWA
      currentMassPos (fun _ => 0) (fun _ => 0) (by simp) with
    ⟨finite⟩
  let finalMap := finite.planeMap
  let finalFn : {point : Point3 // point ∈ finite.shading.union} → Point3 :=
    fun point => finalMap.planeMap point
  have finalLipschitz : LipschitzWith coefficient finalFn := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    have firstSource : (first : Point3) ∈
        rootMap.root.normalization.croppedRefined.union :=
      paperSubshading_union finite.subshading first.prop
    have secondSource : (second : Point3) ∈
        rootMap.root.normalization.croppedRefined.union :=
      paperSubshading_union finite.subshading second.prop
    change dist (finalMap.planeMap first) (finalMap.planeMap second) ≤
      (coefficient : ℝ) * dist first second
    rw [finite.same_plane_map]
    exact rootMap.lipschitz.dist_le_mul
      ⟨first, firstSource⟩ ⟨second, secondSource⟩
  have finalUnit : ∀ point, ‖finalFn point‖ = 1 := by
    intro point
    exact finalMap.unit point point.prop
  let localGrains : Proposition63InitialWeakLocalGrainData
      (incidence := incidence) finite.shading sigma
      (Kakeya.realRpowENN delta (-localLoss)) coefficient := {
    planeMap := finalFn
    planeMap_lipschitz := finalLipschitz
    planeMap_unit := finalUnit
    planeMap_incidence := by
      intro index point hpoint
      exact finalMap.incidence index point hpoint
    local_ad := finite_grid_isAD_every_scale_local_ad finalFn finalLipschitz
      finalUnit rootMap.root.normalization.final_extremal.delta_pos
      rootMap.root.normalization.final_extremal.delta_le_one hsigma hsigmaOne
      (by
        rw [← schedule.outer.final_loss]
        exact schedule.outer.loss_pos schedule.central.count le_rfl)
      schedule.central.midLoss_pos schedule.central.N_pos
      schedule.central.kMin_eq schedule.central.kMin_le_kMax
      schedule.central.kMax_lower schedule.central.admissible
      (by
        intro index indexRange point
        have sourceAD := finite.local_ad
          (index - schedule.central.kMin) (by
            dsimp [Proposition63Lemma412CentralGridData.count]
            omega) (point : Point3) point.prop
        have globalIndex : schedule.central.globalIndex
            (index - schedule.central.kMin) = index := by
          dsimp [Proposition63Lemma412CentralGridData.globalIndex]
          omega
        rw [binding.query_eq (index - schedule.central.kMin) (by
          dsimp [Proposition63Lemma412CentralGridData.count]
          omega), globalIndex, schedule.outer.final_loss] at sourceAD
        simpa only [finalFn] using sourceAD)
      habsorbInterpolation habsorbFine
  }
  exact ⟨{
    shading := finite.shading
    subshading := finite.subshading
    cubical := finite.cubical
    extremal := by
      have finalExtremal := finite.extremal
      rw [schedule.outer.final_loss] at finalExtremal
      exact finalExtremal.mono_loss hgridReentry
    topLevelCWA := by
      apply weaken_convex_wolff_bound
        rootMap.root.normalization.cropped_top_level_cwa
      exact realRpowENN_antitone
        rootMap.root.normalization.final_extremal.delta_pos
        rootMap.root.normalization.final_extremal.delta_le_one
        (neg_le_neg hrootReentry)
    incidence := incidence
    lipschitz := coefficient
    incidence_nonnegative := hincidenceNonnegative
    localGrains := localGrains
  }, rfl, rfl⟩

/-- Compatibility projection of the provenance-complete terminal. -/
theorem proposition63_preliminary_local_grain_of_root_map_outer_inputs
    {delta sigma initialInputLoss normalizationLoss currentReentryLoss
      densityLoss incidence gridLoss midLoss localLoss terminalReentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent N : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := currentReentryLoss) initialNormalized current)
    {coefficient : NNReal}
    (rootMap : Proposition63RootPlaneMapData
      (densityLoss := densityLoss) (incidence := incidence) reentry coefficient)
    (hrootSourceLoss : 0 < currentReentryLoss)
    (hrootNormalizationLoss : 0 < reentry.reentryNormalizationLoss)
    (ambientAxialEighth : ∀ tube point,
      point ∈ rootMap.root.normalization.frame ''
          rootMap.root.normalization.ordinaryRefined.carrier tube →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (schedule : Proposition63Lemma412ScheduleData
      sigma gridLoss delta midLoss N)
    (K : ℝ)
    (hgridLossMid : gridLoss ≤ midLoss)
    (inputs : Proposition63Lemma411OuterBindingInputs
      (incidence := incidence) schedule.central schedule.outer
      (rootMap.root.normalization.toPropStickyReentryData
        hrootSourceLoss hrootNormalizationLoss)
      K coefficient hgridLossMid)
    (hrootInput :
      reentry.reentryNormalizationLoss ≤ schedule.outer.loss 0)
    (hgridReentry : gridLoss ≤ terminalReentryLoss)
    (hrootReentry :
      reentry.reentryNormalizationLoss ≤ terminalReentryLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hincidenceNonnegative : 0 ≤ incidence)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (habsorbInterpolation :
      (100 : ℝ) * Real.rpow delta
          (-gridLoss - midLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-localLoss))
    (habsorbFine :
      (100 : ℝ) * Real.rpow delta
          (-midLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-localLoss)) :
    Nonempty (Proposition63PreliminaryLocalGrainData
      (localLoss := localLoss) (reentryLoss := terminalReentryLoss)
      rootMap.root.normalization) := by
  rcases proposition63_preliminary_local_grain_of_root_map_outer_inputs_with_receipts
      reentry rootMap hrootSourceLoss hrootNormalizationLoss
      ambientAxialEighth schedule K hgridLossMid inputs hrootInput
      hgridReentry hrootReentry hdeltaSmall hincidenceNonnegative hsigma
      hsigmaOne habsorbInterpolation habsorbFine with ⟨output, _, _⟩
  exact ⟨output⟩

end Kakeya.Assouad.PureWZ2

end
