import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FromCritical
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RootNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63InitialLocalGrainReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PreliminaryLocalGrain
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WeakLipschitzPlaneMapRefinement

/-! # Generic first rich boundary assembly

This module runs the first rich call from an arbitrary root normalization and
current preliminary local-grain output.  It does not depend on the sampled M9
hierarchy or on any first-chart scalar data.
-/

noncomputable section
namespace Kakeya.Assouad.PureWZ2

/-- Prepare an arbitrary preliminary local-grain shading for its first rich
call, using only the root normalization and the frozen re-entry absorption. -/
theorem Proposition63RootNormalizationData.prepareGenericFirstRich
    {delta sigma inputLoss normalizationLoss densityLoss currentLoss
      localLoss weightLoss reentryLoss reentryNormalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
      densityLoss)
    (preliminary : Proposition63PreliminaryLocalGrainData
      (localLoss := localLoss) (reentryLoss := currentLoss)
      root.normalization)
    (absorption : Proposition63CurrentReentryAbsorptionData
      inputLoss normalizationLoss densityLoss currentLoss weightLoss
      reentryLoss
      (proposition63CanonicalNearbyLevelCount normalizationLoss))
    (hdeltaLe : delta ≤ absorption.delta₀)
    (hnormalizationLoss : 0 < normalizationLoss)
    (htwoNormalization : 2 * normalizationLoss ≤ reentryLoss)
    (hcurrentReentry : currentLoss ≤ reentryLoss)
    (hcurrentLoss : 0 < currentLoss)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2) :
    ∃ current : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) root.normalization preliminary.shading,
      current.normalizationWeight =
          proposition63CanonicalReentryWeight delta weightLoss ∧
        current.levelCount =
          proposition63CanonicalNearbyLevelCount normalizationLoss ∧
        current.reentryNormalizationLoss = reentryNormalizationLoss := by
  have deltaPos := root.normalization.final_extremal.delta_pos
  have ambientTwo := absorption.ambient_two deltaPos hdeltaLe
  rcases root.finiteNearbySchedule hnormalizationLoss ambientTwo
      htwoNormalization with ⟨nearby⟩
  have regularizationAbsorb := absorption.regularization_absorb
    root.normalization rfl nearby rfl rfl deltaPos hdeltaLe
  rcases root.currentShadingReentryFromExtremal preliminary.shading nearby
      ambientTwo preliminary.extremal hcurrentReentry hcurrentLoss
      reentryNormalizationLoss hreentryNormalizationLoss hreentryHalf
      (absorption.canonical_weight_absorb deltaPos hdeltaLe)
      (absorption.trace_fixed_absorb deltaPos hdeltaLe)
      (absorption.paper_fixed_absorb deltaPos hdeltaLe)
      regularizationAbsorb preliminary.subshading preliminary.cubical
      (hdeltaLe.trans absorption.delta₀_le_tiny |>.trans (by norm_num)) with
    ⟨current, weight, _weightUpper, levelCount, normalization⟩
  exact ⟨current, weight, levelCount, normalization⟩

/-- Output of a generic first rich call.  It retains the exact current
re-entry, the distinguished power scale, the original rich terminal package,
and the preliminary local-grain map restricted to the normalized shading. -/
structure Proposition63GenericFirstRichBoundaryData
    {delta sigma inputLoss normalizationLoss densityLoss currentLoss localLoss
      reentryLoss stickyLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
      densityLoss)
    (preliminary : Proposition63PreliminaryLocalGrainData
      (localLoss := localLoss) (reentryLoss := currentLoss)
      root.normalization)
    (schedule : Proposition63RichStickyKernelScheduleData sigma stickyLoss) where
  current : Proposition63CurrentShadingReentryData
    (reentryLoss := reentryLoss) root.normalization preliminary.shading
  reentry_loss_eq : reentryLoss = schedule.sourceLoss
  current_normalization_loss : current.reentryNormalizationLoss =
    schedule.normalizationLoss
  power : Proposition63PowerScale delta sigma
  terminal : Proposition63RichTerminalStickyData
    (sigma := sigma) (outputLoss := stickyLoss)
    current.normalization.croppedRefined
    (current.normalization.toPropStickyReentryData
      (by rw [reentry_loss_eq]; exact schedule.sourceLoss_pos)
      current.reentry_normalization_loss_pos)
    power.requested
  localGrains : Proposition63InitialWeakLocalGrainData
    (incidence := preliminary.incidence)
    current.normalization.croppedRefined sigma
    (Kakeya.realRpowENN delta (-localLoss)) preliminary.lipschitz
  localGrains_eq : localGrains = current.normalizedLocalGrains
    (localGrains := preliminary.localGrains)

namespace Proposition63GenericFirstRichBoundaryData

variable
    {delta sigma inputLoss normalizationLoss densityLoss currentLoss localLoss
      reentryLoss stickyLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
      densityLoss}
    {preliminary : Proposition63PreliminaryLocalGrainData
      (localLoss := localLoss) (reentryLoss := currentLoss)
      root.normalization}
    {schedule : Proposition63RichStickyKernelScheduleData sigma stickyLoss}
    (first : Proposition63GenericFirstRichBoundaryData
      (reentryLoss := reentryLoss) root preliminary schedule)

/-- The normalized shading is contained in the preliminary shading from
which the current re-entry was constructed. -/
theorem normalized_union_subset_preliminary :
    first.current.normalization.croppedRefined.union ⊆
      preliminary.shading.union :=
  first.current.normalization_croppedRefined_union_subset_current

/-- Restrict an arbitrary weak map on the preliminary shading along the
selected current family and then to the exact normalized dense shading. -/
noncomputable def normalizedPreliminaryMap
    (sourceMap : PaperWZ1WeakPlaneMapData
      preliminary.shading preliminary.incidence) :
    PaperWZ1WeakPlaneMapData
      first.current.normalization.croppedRefined preliminary.incidence :=
  paperWeakPlaneMapRestrict
    (PaperWZ1WeakPlaneMapData.restrictSubfamily sourceMap
      first.current.regularized.selected)
    first.current.denseSubshading

/-- Restriction preserves the source weak map pointwise. -/
theorem normalizedPreliminaryMap_eq_source
    (sourceMap : PaperWZ1WeakPlaneMapData
      preliminary.shading preliminary.incidence)
    (point : {point : Point3 //
      point ∈ first.current.normalization.croppedRefined.union}) :
    (first.normalizedPreliminaryMap sourceMap).planeMap point =
      sourceMap.planeMap point := by
  rfl

/-- Delta-grid cellwise constancy transfers through both normalization
restrictions.  The source certificate is deliberately supplied by the caller. -/
theorem normalizedPreliminaryMap_cellwise
    (sourceMap : PaperWZ1WeakPlaneMapData
      preliminary.shading preliminary.incidence)
    (sourceCellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        sourceMap.planeMap first = sourceMap.planeMap second) :
    ∀ firstPoint secondPoint,
      wz1PaperGridIndex delta firstPoint =
          wz1PaperGridIndex delta secondPoint →
        (first.normalizedPreliminaryMap sourceMap).planeMap firstPoint =
          (first.normalizedPreliminaryMap sourceMap).planeMap secondPoint := by
  intro firstPoint secondPoint sameCell
  exact sourceCellwise firstPoint secondPoint sameCell

/-- The stored normalized local-grain map agrees with the normalized weak map
when the caller records its construction from the preliminary local grains
and identifies that preliminary point function with the source weak map. -/
theorem localGrains_planeMap_eq_normalizedPreliminaryMap
    (sourceMap : PaperWZ1WeakPlaneMapData
      preliminary.shading preliminary.incidence)
    (localGrains_eq : first.localGrains =
      first.current.normalizedLocalGrains
        (localGrains := preliminary.localGrains))
    (sourceAgreement : ∀ point,
      preliminary.localGrains.planeMap point = sourceMap.planeMap point)
    (point : {point : Point3 //
      point ∈ first.current.normalization.croppedRefined.union}) :
    first.localGrains.planeMap point =
      (first.normalizedPreliminaryMap sourceMap).planeMap point := by
  rw [localGrains_eq]
  exact sourceAgreement
    ⟨point, first.normalized_union_subset_preliminary point.prop⟩

end Proposition63GenericFirstRichBoundaryData

/-- Execute the first rich call from arbitrary root and preliminary data at
the distinguished `Proposition63PowerScale delta sigma` request. -/
theorem Proposition63RootNormalizationData.runGenericFirstRich
    {delta sigma inputLoss normalizationLoss densityLoss currentLoss
      localLoss weightLoss reentryLoss stickyLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
      densityLoss)
    (preliminary : Proposition63PreliminaryLocalGrainData
      (localLoss := localLoss) (reentryLoss := currentLoss)
      root.normalization)
    (absorption : Proposition63CurrentReentryAbsorptionData
      inputLoss normalizationLoss densityLoss currentLoss weightLoss
      reentryLoss
      (proposition63CanonicalNearbyLevelCount normalizationLoss))
    (schedule : Proposition63RichStickyKernelScheduleData sigma stickyLoss)
    (hdeltaLe : delta ≤ absorption.delta₀)
    (hdeltaSchedule : delta ≤ schedule.delta₀)
    (hdeltaOne : delta < 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hnormalizationLoss : 0 < normalizationLoss)
    (htwoNormalization : 2 * normalizationLoss ≤ reentryLoss)
    (hcurrentReentry : currentLoss ≤ reentryLoss)
    (hcurrentLoss : 0 < currentLoss)
    (hreentryLoss : reentryLoss = schedule.sourceLoss)
    (hreentryNormalizationLoss : 0 < schedule.normalizationLoss)
    (hreentryHalf : reentryLoss ≤ schedule.normalizationLoss / 2)
    (hstickyLower : stickyLoss ≤ sigma / (2 + sigma))
    (hstickyUpper : sigma / (2 + sigma) ≤ 1 - stickyLoss) :
    Nonempty (Proposition63GenericFirstRichBoundaryData
      (reentryLoss := reentryLoss) root preliminary schedule) := by
  rcases root.prepareGenericFirstRich preliminary absorption hdeltaLe
      hnormalizationLoss htwoNormalization hcurrentReentry hcurrentLoss
      hreentryNormalizationLoss hreentryHalf with
    ⟨current, _weight, _levelCount, normalizationLossEq⟩
  rcases proposition63_power_scale root.normalization.final_extremal.delta_pos
      hdeltaOne hsigma hsigmaOne with ⟨power⟩
  have window := power.first_sticky_window
    root.normalization.final_extremal.delta_pos hdeltaOne.le
    hstickyLower hstickyUpper
  rcases proposition63CurrentShadingReentry_richTerminalSticky current
      schedule hreentryLoss normalizationLossEq hdeltaSchedule
      power.requested window.1 window.2 with ⟨terminal⟩
  exact ⟨{
    current := current
    reentry_loss_eq := hreentryLoss
    current_normalization_loss := normalizationLossEq
    power := power
    terminal := terminal
    localGrains := current.normalizedLocalGrains
      (localGrains := preliminary.localGrains)
    localGrains_eq := rfl
  }⟩

end Kakeya.Assouad.PureWZ2
end
