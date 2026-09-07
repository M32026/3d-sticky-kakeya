import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantOneScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ReentryTraceFloorSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyRegularizedNearbyCWA

/-!
# One scheduled transition of the re-entry-preserving hierarchy

The raw ordinary one-scale output and the synchronized next source are kept as
different losses.  One local trace-floor schedule supplies the critical floor
on the exact selected family; no global cropped-floor conversion or unrelated
source is introduced.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Construct one dependent hierarchy transition from the current exact
re-entry, a raw ordinary one-scale output, and the genuinely non-hereditary
selection receipts. -/
theorem exists_pureWZ2ReentrantOneScaleStep_of_traceSchedule
    {sigma inputLoss delta grainLoss outputLoss rho outputEta
      structuralBudget : ℝ}
    {normalizationExponent : ℕ}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    (oneScale : PureWZ2LocallyLinearOneScaleData
      current.grain grainLoss rho)
    (hinputGrain : inputLoss ≤ grainLoss)
    (schedule : PureWZ2ReentryTraceFloorSchedule
      sigma outputLoss structuralBudget)
    (hdeltaSchedule : delta ≤ schedule.delta₀)
    (inputEta : ℝ)
    (croppedMassFraction : ENNReal)
    (densitySeparation :
      Kakeya.realRpowENN delta outputEta ≤
        (1 / 2 : ENNReal) * Kakeya.realRpowENN delta inputEta)
    (inputDensityAbsorption :
      Kakeya.realRpowENN delta inputEta ≤
        (100 : ENNReal)⁻¹ * current.reentry.geometry.ordinaryDensity *
          Kakeya.realRpowENN delta grainLoss)
    (croppedMassAbsorption :
      croppedMassFraction ≤
        (100 : ENNReal)⁻¹ * current.reentry.geometry.ordinaryDensity)
    (cwaNormalizationLoss : ℝ)
    (input_loss_le_cwa : inputLoss ≤ cwaNormalizationLoss)
    (cwa_epsilon_pos :
      0 < schedule.densityLoss - cwaNormalizationLoss)
    (cwaRestrictionAbsorption :
      wz2PaperPureNearbyRestrictionConstant
          (Kakeya.realRpowENN delta (-cwaNormalizationLoss))
          (Kakeya.realRpowENN delta inputEta *
            Kakeya.deltaTubeVolume delta)
          (pureWZ2SpatialCellDegreeConstant
            (schedule.densityLoss - cwaNormalizationLoss)
              current.grain.family.card)
          (pureWZ2SpatialCellRegularizationLoss
              (schedule.densityLoss - cwaNormalizationLoss)
                current.grain.family.card *
            Kakeya.deltaTubeVolume delta) ≤
        Kakeya.realRpowENN delta (-schedule.densityLoss))
    (cwaCardinalityAbsorption :
      Kakeya.realRpowENN delta outputEta *
          pureWZ2SpatialCellRegularizationLoss
            (schedule.densityLoss - cwaNormalizationLoss)
              current.grain.family.card ≤
        Kakeya.realRpowENN delta inputEta)
    (grainLoss_le_density : grainLoss ≤ schedule.densityLoss)
    (densityAbsorption :
      (13824 : ENNReal) *
          Kakeya.realRpowENN delta schedule.densityLoss ≤
        Kakeya.realRpowENN delta outputEta)
    (topLevelAbsorption :
      ((Kakeya.realRpowENN delta outputEta)⁻¹ * 1) *
          Kakeya.realRpowENN delta (-grainLoss) ≤
        Kakeya.realRpowENN delta (-outputLoss))
    (densityLoss_le_half : schedule.densityLoss ≤ outputLoss / 2)
    (outputEta_le_structural :
      outputEta ≤ schedule.criticalFloor.structuralLoss) :
    Nonempty (PureWZ2ReentrantOneScaleStepData current grainLoss outputLoss
      rho outputEta croppedMassFraction) := by
  let grainRefinement := oneScale.toGrainRefinementData hinputGrain
  let identity := pureWZ2Node05PostGrainIdentityRefinement current.grain.shading
  have ambient : WZ2PaperPureCWAAtNearbyScales current.grain.family
      (Kakeya.realRpowENN delta (-cwaNormalizationLoss)) :=
    current.grain.extremal.cwa_nearby_scales.mono_loss
      current.grain.extremal.delta_pos current.grain.extremal.delta_le_one
      input_loss_le_cwa
  have roundingAbsorption :
      ENNReal.ofReal
          (Real.rpow delta
            (-(schedule.densityLoss - cwaNormalizationLoss))) *
          Kakeya.realRpowENN delta (-cwaNormalizationLoss) ≤
        Kakeya.realRpowENN delta (-schedule.densityLoss) := by
    change Kakeya.realRpowENN delta
          (-(schedule.densityLoss - cwaNormalizationLoss)) *
        Kakeya.realRpowENN delta (-cwaNormalizationLoss) ≤
      Kakeya.realRpowENN delta (-schedule.densityLoss)
    rw [← realRpowENN_add current.grain.extremal.delta_pos]
    apply le_of_eq
    congr 2
    ring
  rcases exists_pureWZ2Node05RegularizedPostGrainCore
      identity current.reentry grainRefinement croppedMassFraction
      (Kakeya.realRpowENN delta (-schedule.densityLoss)) ambient
      (hdeltaSchedule.trans schedule.delta₀_le_twelve) densitySeparation
      inputDensityAbsorption croppedMassAbsorption cwa_epsilon_pos
      (lt_of_le_of_lt hdeltaSchedule <|
        schedule.delta₀_le_twelve.trans_lt (by norm_num))
      (by simp [Kakeya.realRpowENN]) roundingAbsorption
      cwaRestrictionAbsorption cwaCardinalityAbsorption with
    ⟨regularized⟩
  let core := regularized.core
  have selectedNearby : WZ2PaperPureCWAAtNearbyScales
      (pureWZ2Node05PostGrainSelectedSubfamily
        current.grain.family core.retained).family
      (Kakeya.realRpowENN delta (-outputLoss)) :=
    regularized.nearby.mono_loss current.grain.extremal.delta_pos
      current.grain.extremal.delta_le_one schedule.densityLoss_le_floor
  have selectedDensity :
      (13824 : ENNReal) * Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta outputEta := by
    calc
      (13824 : ENNReal) * Kakeya.realRpowENN delta outputLoss ≤
          13824 * Kakeya.realRpowENN delta schedule.densityLoss := by
        gcongr
        exact pure_wz2_rpowENN_antitone current.grain.extremal.delta_pos
          current.grain.extremal.delta_le_one
          schedule.densityLoss_le_floor
      _ ≤ Kakeya.realRpowENN delta outputEta := densityAbsorption
  have selectedVolume :=
    core.selectedCropped_volume_lower_of_refreshedOrdinary
      schedule.criticalFloor
      (hdeltaSchedule.trans schedule.delta₀_le_floor)
      (by
        rw [schedule.densityLoss_eq]
        linarith [schedule.criticalFloor.structuralLoss_pos])
      outputEta_le_structural
      regularized.nearby
  let receipt : PureWZ2Node05SelectedGrainReceipt core outputLoss :=
    PureWZ2Node05SelectedGrainReceipt.ofNearbyAndDensity
      selectedNearby selectedDensity
      (grainLoss_le_density.trans schedule.densityLoss_le_floor)
      topLevelAbsorption selectedVolume
  have densityPower :
      Kakeya.realRpowENN delta schedule.densityLoss ≤
        Kakeya.realRpowENN delta outputEta := by
    exact (by
      calc
        Kakeya.realRpowENN delta schedule.densityLoss =
            1 * Kakeya.realRpowENN delta schedule.densityLoss := by simp
        _ ≤ 13824 * Kakeya.realRpowENN delta schedule.densityLoss := by
          gcongr
          norm_num
        _ ≤ Kakeya.realRpowENN delta outputEta := densityAbsorption)
  let refreshed := core.refreshedReentry receipt schedule.densityLoss_pos
    densityLoss_le_half grainLoss_le_density densityPower
    (wz2PaperPureRefinementFraction_le_one_of_le_one_twelfth
      current.grain.extremal.delta_pos
      (hdeltaSchedule.trans schedule.delta₀_le_twelve) normalizationExponent)
    regularized.nearby
  exact ⟨{
    oneScale := oneScale
    input_loss_le := hinputGrain
    grain_loss_le := grainLoss_le_density.trans schedule.densityLoss_le_floor
    core := core
    receipt := receipt
    nextOrdinaryLoss := schedule.densityLoss
    refreshedReentry := refreshed
    refreshed_axial_window_eighth := by
      intro index point pointMem
      change point ∈ current.reentry.geometry.frame ''
        core.refreshedOrdinaryShading.carrier index at pointMem
      rw [core.refreshedOrdinaryShading_frame_image index] at pointMem
      exact current.ordinary_axial_window_eighth _ point pointMem.1
  }⟩

end Kakeya.Assouad

end
