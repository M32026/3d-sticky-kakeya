import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9PreliminaryPlaninessRuntime
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63Lemma412OuterSchedule

/-!
# Stateful preliminary Lemma-4.12 terminal

The preliminary finite planiness refinement already carries the one ambient
plane map needed by Lemma 4.12.  This adapter starts the existing stateful
Lemma-4.11 outer iteration on that actual refinement, so every coordinate
restores extremality before the next one.  The terminal local-grain package
is nevertheless indexed by the original normalization: no re-entry-selected
tube family is substituted for the preliminary root.

This is a conditional terminal adapter.  The M9 caller must still construct
the canonical ambient re-entry, its strict axial certificate, and every
pre-runtime outer-binding scalar receipt.  The zero spatial/variation
functions below intentionally discard the outer iterator's auxiliary
variation conclusion; only its stateful local-AD output is consumed here.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

/-- Convert a stateful M7 outer run on the genuine preliminary planiness
shading into the all-scale local-grain package used by the first rich call.
The map is only required on the actual planiness shading; its restriction is
preserved definitionally through the finite iteration. -/
theorem Proposition63M9PreliminaryPlaninessRuntimeData.preliminaryLocalGrainOfOuterInputs
    {delta sigma initialInputLoss normalizationLoss producerLoss coefficient
      incidence gridLoss midLoss localLoss reentryLoss ambientSourceLoss
      ambientNormalizationLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent N : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {source : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63M9PreliminaryPlaninessRuntimeData
      (producerLoss := producerLoss) (coefficient := coefficient)
      (incidence := incidence) initialNormalized source)
    (ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) initialNormalized.croppedRefined normalizationExponent
        ambientSourceLoss ambientNormalizationLoss)
    (ambientAxialEighth : ∀ tube point,
      point ∈ ambientReentry.geometry.frame ''
          ambientReentry.geometry.ordinaryRefined.carrier tube →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (schedule : Proposition63Lemma412ScheduleData
      sigma gridLoss delta midLoss N)
    (K : ℝ)
    (hgridLossMid : gridLoss ≤ midLoss)
    (inputs : Proposition63Lemma411OuterBindingInputs
      (incidence := incidence) schedule.central schedule.outer
      ambientReentry K (Real.toNNReal coefficient) hgridLossMid)
    (hproducerInput : producerLoss ≤ schedule.outer.loss 0)
    (hgridReentry : gridLoss ≤ reentryLoss)
    (hproducerReentry : producerLoss ≤ reentryLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
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
      (localLoss := localLoss) (reentryLoss := reentryLoss)
      initialNormalized) := by
  rcases proposition63_lemma411_central_binding schedule.central
      schedule.outer ambientReentry K (Real.toNNReal coefficient)
      hgridLossMid inputs with ⟨binding⟩
  have currentExtremal : WZ2PaperCroppedIsExtremal sigma
      (schedule.outer.loss 0) initialNormalized.croppedFamily
      data.planiness.data.refinement.shading :=
    data.extremal.mono_loss hproducerInput
  have currentCWA : WZ2PaperConvexWolffBound
      initialNormalized.croppedFamily
      (Kakeya.realRpowENN delta (-(schedule.outer.loss 0))) := by
    apply weaken_convex_wolff_bound data.topLevelCWA
    exact realRpowENN_antitone data.extremal.delta_pos
      data.extremal.delta_le_one (by linarith [hproducerInput])
  have currentMassPos : 0 < data.planiness.data.refinement.shading.mass :=
    cropped_extremal_shading_mass_pos data.extremal
      initialNormalized.line_class hdeltaSmall
  let identitySub : PaperIsSubshading
      data.planiness.data.refinement.shading
      data.planiness.data.refinement.shading := fun _ => Set.Subset.rfl
  rcases binding.binding.run ambientAxialEighth data.currentMap
      data.planiness.data.refinement.lipschitz identitySub data.subshading
      currentExtremal currentCWA currentMassPos (fun _ => 0) (fun _ => 0)
      (by simp) with ⟨finite⟩
  let finalMap := finite.planeMap
  let finalFn : {point : Point3 // point ∈ finite.shading.union} → Point3 :=
    fun point => finalMap.planeMap point
  have finalLipschitz : LipschitzWith (Real.toNNReal coefficient) finalFn := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    have firstSource : (first : Point3) ∈
        data.planiness.data.refinement.shading.union :=
      paperSubshading_union finite.subshading first.prop
    have secondSource : (second : Point3) ∈
        data.planiness.data.refinement.shading.union :=
      paperSubshading_union finite.subshading second.prop
    change dist (finalMap.planeMap first) (finalMap.planeMap second) ≤
      (Real.toNNReal coefficient : ℝ) * dist first second
    rw [finite.same_plane_map]
    exact data.planiness.data.refinement.lipschitz.dist_le_mul
      ⟨first, firstSource⟩ ⟨second, secondSource⟩
  have finalUnit : ∀ point, ‖finalFn point‖ = 1 := by
    intro point
    exact finalMap.unit point point.prop
  let localGrains : Proposition63InitialWeakLocalGrainData
      (incidence := incidence) finite.shading sigma
      (Kakeya.realRpowENN delta (-localLoss))
      (Real.toNNReal coefficient) := {
    planeMap := finalFn
    planeMap_lipschitz := finalLipschitz
    planeMap_unit := finalUnit
    planeMap_incidence := by
      intro index point hpoint
      exact finalMap.incidence index point hpoint
    local_ad := finite_grid_isAD_every_scale_local_ad finalFn finalLipschitz
      finalUnit data.extremal.delta_pos data.extremal.delta_le_one
      hsigma hsigmaOne
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
  have finalSubRoot : PaperIsSubshading finite.shading
      initialNormalized.croppedRefined := fun index point pointMem =>
    data.subshading index (finite.subshading index pointMem)
  exact ⟨{
    shading := finite.shading
    subshading := finalSubRoot
    cubical := finite.cubical
    extremal := by
      have finalExtremal := finite.extremal
      rw [schedule.outer.final_loss] at finalExtremal
      exact finalExtremal.mono_loss hgridReentry
    topLevelCWA := by
      apply weaken_convex_wolff_bound data.topLevelCWA
      exact realRpowENN_antitone data.extremal.delta_pos
        data.extremal.delta_le_one (by linarith [hproducerReentry])
    incidence := incidence
    lipschitz := Real.toNNReal coefficient
    incidence_nonnegative := data.incidence_nonnegative
    localGrains := localGrains
  }⟩

end Kakeya.Assouad.PureWZ2

end
