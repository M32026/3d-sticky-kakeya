import MyLeanRepo.Kakeya.Assouad.PureWZ2.FiniteCallerCenterNearbyAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SelectedCallerCompletePullback

/-!
# Same-family caller nearby-scale assembly

Apply the finite caller-center H1 selection to the shaded masses of the
already regularized merged caller fibers.  Pull the selected callers back by
complete WZ fibers.  The output therefore has one fine family, one caller
coarse family, one Section 6 cover, coarse pure CWA, and pure CWA on every
complete caller fiber.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

structure PureWZ2SameFamilyCallerNearbyAssemblyData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (support : PureWZ2PositiveCallerSupportData quotient)
    (coordinateCount : ℕ)
    (regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount)
    (merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized)
    (scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant) where
  selectedCoarse :
    WZ2PaperPureTubeSubfamily
      (quotient.callerCover.hitParentSubfamily
        quotient.positiveCallerFine).family
  selectedCoarse_nonempty : selectedCoarse.family.Nonempty
  retentionConstant : ENNReal
  parentMassLevel : ENNReal
  parentMassLevel_pos : 0 < parentMassLevel
  pullback :
    PureWZ2SelectedCallerCompletePullbackData
      merged selectedCoarse
  coarse_pure_cwa :
    WZ2PaperPureCWAAtNearbyScales
      selectedCoarse.family coarseConstant
  selected_mass_retention :
    merged.mergedShading.mass ≤
      retentionConstant *
        pullback.selectedFineShading.mass
  parent_mass_band :
    ∀ parent : Fin selectedCoarse.family.card,
      parentMassLevel ≤
          ∑ source ∈
            wz2PaperFullFiberIndices
              pullback.selectedFine.family selectedCoarse.family parent,
            volume (pullback.selectedFineShading.carrier source) ∧
        (∑ source ∈
            wz2PaperFullFiberIndices
              pullback.selectedFine.family selectedCoarse.family parent,
            volume (pullback.selectedFineShading.carrier source)) ≤
          2 * parentMassLevel
  source_mass_retention :
    shading.mass ≤
      ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
        pureWZ2CompleteParentRegularizationLoss
          actualNearby.scaleData.coarse.card coordinateCount *
        retentionConstant) *
          pullback.selectedFineShading.mass

/--
Select the H1 caller family with the actual merged caller-fiber shaded masses
as weights, then pull it back by complete caller fibers.
-/
theorem pureWZ2_same_family_caller_nearby_assembly
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (support : PureWZ2PositiveCallerSupportData quotient)
    (coordinateCount : ℕ)
    (coordinateCountPos : 0 < coordinateCount)
    (regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount)
    (merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized)
    (fineNonempty : fine.Nonempty)
    (fineBoundedBase : HasBoundedBase fine 4)
    (shadingMassPos : 0 < shading.mass)
    (scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (callerScheduled :
      ∀ coordinate,
        callerRequested.1 ≤ (scheduled coordinate).rho)
    (coarseOne : 1 ≤ coarseConstant)
    (coarseTop : coarseConstant ≠ ⊤)
    (scaleAbsorption :
      ∀ coordinate,
        max
            (pureWZ2FiniteCallerCenterDegreeConstant
              coordinateCount
              (quotient.callerCover.hitParentSubfamily
                quotient.positiveCallerFine).family.card)
            ((27 : ENNReal) *
              Kakeya.deltaTubeVolume
                (19 * (scheduled coordinate).rho) *
              (Kakeya.deltaTubeVolume callerRequested.1)⁻¹) ≤
          coarseConstant)
    (rounding :
      ∀ requested :
          WZ2PaperRequestedScale callerRequested.1,
        ∃ coordinate : Fin coordinateCount,
          requested.1 ≤ 19 * (scheduled coordinate).rho ∧
          ENNReal.ofReal (19 * (scheduled coordinate).rho) <
            coarseConstant * ENNReal.ofReal requested.1) :
    Nonempty
      (PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled) := by
  let ambientCoarse :=
    (quotient.callerCover.hitParentSubfamily
      quotient.positiveCallerFine).family
  let callerBase :=
    {
      family := ambientCoarse
      embedding :=
        (quotient.callerCover.hitParentSubfamily
          quotient.positiveCallerFine).embedding
      tube_eq :=
        (quotient.callerCover.hitParentSubfamily
          quotient.positiveCallerFine).tube_eq
    : WZ2PaperPureTubeSubfamily quotient.callerCoarse }
  let callerWeight : Fin callerBase.family.card → ENNReal :=
    fun parent =>
      ∑ source ∈
        wz2PaperFullFiberIndices
          merged.merged.family ambientCoarse
          parent,
        volume (merged.mergedShading.carrier source)
  have totalWeight :
      (∑ parent : Fin callerBase.family.card,
          callerWeight parent) =
        merged.mergedShading.mass := by
    change
      (∑ parent : Fin ambientCoarse.card,
          ∑ source ∈
            wz2PaperFullFiberIndices
              merged.merged.family ambientCoarse parent,
            volume (merged.mergedShading.carrier source)) =
        merged.mergedShading.mass
    have fiberIndices :
        ∀ parent : Fin ambientCoarse.card,
          wz2PaperFullFiberIndices
              merged.merged.family ambientCoarse parent =
            merged.callerCover.fiberIndices parent := by
      intro parent
      ext source
      simp only [WZ1PaperTubeCover.fiberIndices,
        Finset.mem_filter, Finset.mem_univ, true_and]
      rw [mem_wz2PaperFullFiberIndices_iff]
      constructor
      · intro hcovered
        exact
          (merged.callerCover.parent_unique
            source parent hcovered).symm
      · intro hparent
        rw [← hparent]
        exact merged.callerCover.parent_covers source
    simp_rw [fiberIndices]
    change
      (∑ parent : Fin ambientCoarse.card,
          ∑ source ∈ Finset.univ with
              merged.callerCover.parent source = parent,
            volume (merged.mergedShading.carrier source)) =
        ∑ source : Fin merged.merged.family.card,
          volume (merged.mergedShading.carrier source)
    exact
      Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ) (t := Finset.univ)
        (g := merged.callerCover.parent)
        (fun _ _ => Finset.mem_univ _)
        (fun source =>
          volume (merged.mergedShading.carrier source))
  have mergedMassPos : 0 < merged.mergedShading.mass := by
    have hretained := merged.source_mass_retention
    by_contra hzero
    have hmzero : merged.mergedShading.mass = 0 := by
      exact nonpos_iff_eq_zero.mp (not_lt.mp hzero)
    rw [hmzero, mul_zero] at hretained
    exact (not_le_of_gt shadingMassPos) hretained
  have totalWeightPos :
      0 < ∑ parent : Fin callerBase.family.card,
        callerWeight parent := by
    rw [totalWeight]
    exact mergedMassPos
  let nearby :
      PureWZ2FiniteCallerCenterNearbyAssemblyData
        quotient callerBase coordinateCount scales scheduled
        callerWeight coarseConstant :=
    Classical.choice <|
      pureWZ2_finite_caller_center_nearby_assembly
        quotient callerBase fineNonempty fineBoundedBase coordinateCount
        coordinateCountPos scales scheduled callerScheduled
        callerWeight totalWeightPos coarseConstant
        coarseOne coarseTop
        (by
          intro coordinate
          simpa [callerBase] using scaleAbsorption coordinate)
        rounding
  letI colorFintype :
      ∀ coordinate, Fintype (nearby.Color coordinate) :=
    nearby.colorFintype
  letI colorDecidableEq :
      ∀ coordinate, DecidableEq (nearby.Color coordinate) :=
    nearby.colorDecidableEq
  letI colorNonempty :
      ∀ coordinate, Nonempty (nearby.Color coordinate) :=
    nearby.colorNonempty
  let selectedCoarse :=
    nearby.selection.selected
  have selectedCoarseNonempty : selectedCoarse.family.Nonempty :=
    nearby.selected_nonempty
  let pullback :
      PureWZ2SelectedCallerCompletePullbackData
        merged selectedCoarse :=
    Classical.choice <|
      pureWZ2_selected_caller_complete_pullback
        merged selectedCoarse selectedCoarseNonempty
  have coarsePureCWA :
      WZ2PaperPureCWAAtNearbyScales
        selectedCoarse.family coarseConstant :=
    nearby.literal_cwa
  have selectedWeightSum :
      (∑ index : Fin nearby.selection.selected.family.card,
          callerWeight
            (nearby.selection.selected.embedding index)) =
        pullback.selectedFineShading.mass := by
    rw [pullback.selectedFineShading_mass_eq]
  have selectedRetention :
      merged.mergedShading.mass ≤
        nearby.selection.retentionConstant *
          pullback.selectedFineShading.mass := by
    rw [← totalWeight, ← selectedWeightSum]
    exact nearby.selection.retained_weight
  have sourceRetention :
      shading.mass ≤
        ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          pureWZ2CompleteParentRegularizationLoss
            actualNearby.scaleData.coarse.card coordinateCount *
          nearby.selection.retentionConstant) *
            pullback.selectedFineShading.mass := by
    calc
      shading.mass ≤
          (pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            pureWZ2CompleteParentRegularizationLoss
              actualNearby.scaleData.coarse.card coordinateCount *
            merged.mergedShading.mass :=
        merged.source_mass_retention
      _ ≤
          (pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            pureWZ2CompleteParentRegularizationLoss
              actualNearby.scaleData.coarse.card coordinateCount *
            (nearby.selection.retentionConstant *
              pullback.selectedFineShading.mass) := by
        gcongr
      _ =
          ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            pureWZ2CompleteParentRegularizationLoss
              actualNearby.scaleData.coarse.card coordinateCount *
            nearby.selection.retentionConstant) *
              pullback.selectedFineShading.mass := by
        ring
  exact
    ⟨{
      selectedCoarse := selectedCoarse
      selectedCoarse_nonempty := selectedCoarseNonempty
      retentionConstant := nearby.selection.retentionConstant
      parentMassLevel := nearby.selection.weightLevel
      parentMassLevel_pos := nearby.selection.weightLevel_pos
      pullback := pullback
      coarse_pure_cwa := coarsePureCWA
      selected_mass_retention := selectedRetention
      parent_mass_band := by
        intro parent
        rw [pullback.full_fiber_mass_eq parent]
        exact nearby.selection.weight_band parent
      source_mass_retention := sourceRetention
    }⟩

end Kakeya.Assouad

end
