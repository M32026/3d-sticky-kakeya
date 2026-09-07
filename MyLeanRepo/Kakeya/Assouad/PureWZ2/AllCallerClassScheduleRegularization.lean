import MyLeanRepo.Kakeya.Assouad.PureWZ2.PositiveCallerSupport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PostDeletionCallerWeightPreselection
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureFiberRestriction

/-!
# Simultaneous complete-parent regularization in every positive caller class

The quotient caller support is finite.  Apply the one-class complete-parent
regularizer independently to every positive caller and retain the resulting
dependent data.  Each local output remains a union of complete actual
Definition 2.12 fibers and satisfies pure CWA at every nearby scale.

This file does not yet merge the local families.  Its output is the exact
input for the subsequent fiberwise union: one local selected family for each
positive caller, together with its provenance and quantitative retention.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem PureWZ2CompleteParentRestrictionData.restrictedShading_mass_eq
    {delta actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualCoarse :
      Kakeya.Streamlined.TubeFamily actual}
    {actualCover :
      WZ2PaperPurePartitioningCover fine actualCoarse}
    {selectedActualParents :
      Finset (Fin actualCoarse.card)}
    (data :
      PureWZ2CompleteParentRestrictionData
        actualCover selectedActualParents)
    (shading : WZ1PaperTubeShading fine)
    (actual_nonneg : 0 ≤ actual) :
    (restrictPaperShading
      data.selectedFine.toTubeSubfamily shading).mass =
      ∑ parent ∈ selectedActualParents,
        pureWZ2ActualFiberShadedMass shading parent := by
  rw [restrictPaperShading_mass]
  let selectedIndices := data.selectedFineIndices
  let equivalence :
      Fin data.selectedFine.family.card ≃ selectedIndices :=
    (selectedIndices.orderIsoOfFin rfl).toEquiv
  have selectedMass :
      (∑ source : Fin data.selectedFine.family.card,
          volume
            (shading.carrier
              (data.selectedFine.embedding source))) =
        ∑ source ∈ selectedIndices,
          volume (shading.carrier source) := by
    calc
      (∑ source : Fin data.selectedFine.family.card,
          volume
            (shading.carrier
              (data.selectedFine.embedding source))) =
          ∑ source : selectedIndices,
            volume (shading.carrier source.1) := by
        exact
          Fintype.sum_equiv equivalence
            (fun source : Fin data.selectedFine.family.card =>
              volume
                (shading.carrier
                  (data.selectedFine.embedding source)))
            (fun source : selectedIndices =>
              volume (shading.carrier source.1))
            (fun _ => rfl)
      _ =
          ∑ source ∈ selectedIndices,
            volume (shading.carrier source) := by
        exact
          Finset.sum_coe_sort selectedIndices
            (fun source => volume (shading.carrier source))
  change
    (∑ source : Fin data.selectedFine.family.card,
        volume
          (shading.carrier
            (data.selectedFine.embedding source))) =
      ∑ parent ∈ selectedActualParents,
        pureWZ2ActualFiberShadedMass shading parent
  rw [selectedMass]
  have fiberwise :
      ∑ parent ∈ selectedActualParents,
          ∑ source ∈ selectedIndices with
              actualCover.parent source = parent,
            volume (shading.carrier source) =
        ∑ source ∈ selectedIndices,
          volume (shading.carrier source) :=
    Finset.sum_fiberwise_of_maps_to
      (s := selectedIndices)
      (t := selectedActualParents)
      (g := actualCover.parent)
      (fun source hsource =>
        (Finset.mem_filter.mp hsource).2)
      (fun source => volume (shading.carrier source))
  rw [← fiberwise]
  apply Finset.sum_congr rfl
  intro parent hparent
  unfold pureWZ2ActualFiberShadedMass
  apply Finset.sum_congr
  · ext source
    rw [actualCover.mem_fullFiber_iff_parent_eq
      actual_nonneg parent source]
    simp only [selectedIndices,
      PureWZ2CompleteParentRestrictionData.selectedFineIndices,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun hsource => hsource.2
    · intro hsource
      exact ⟨hsource ▸ hparent, hsource⟩
  · intro _ _
    rfl

/-- The complete output of regularization inside one quotient caller class. -/
structure PureWZ2CallerClassRegularizationData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (callerParent : Fin quotient.callerCoarse.card)
    (coordinateCount : ℕ) where
  selectedActualParents :
    Finset (Fin actualNearby.scaleData.coarse.card)
  complete :
    PureWZ2CompleteParentRestrictionData
      actualNearby.scaleData.cover selectedActualParents
  regularizationLoss : ENNReal
  selectedWeightLevel : ENNReal
  selected_subset :
    selectedActualParents ⊆
      quotient.callerActualParents callerParent
  regularizationLoss_ne_top :
    regularizationLoss ≠ ⊤
  regularizationLoss_eq :
    regularizationLoss =
      pureWZ2CompleteParentRegularizationLoss
        actualNearby.scaleData.coarse.card coordinateCount
  selectedWeightLevel_pos :
    0 < selectedWeightLevel
  selectedWeightLevel_ne_top :
    selectedWeightLevel ≠ ⊤
  selected_weight_pos :
    ∀ parent ∈ selectedActualParents,
      0 < pureWZ2ActualFiberShadedMass shading parent
  retained_weight :
    quotient.callerActualWeight callerParent ≤
      regularizationLoss *
        ∑ parent ∈ selectedActualParents,
          pureWZ2ActualFiberShadedMass shading parent
  pure_cwa :
    WZ2PaperPureCWAAtNearbyScales
      complete.selectedFine.family outputConstant

theorem PureWZ2CallerClassRegularizationData.selectedFine_nonempty
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {callerParent : Fin quotient.callerCoarse.card}
    {coordinateCount : ℕ}
    (data :
      PureWZ2CallerClassRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient callerParent coordinateCount)
    (fineNonempty : fine.Nonempty) :
    data.complete.selectedFine.family.Nonempty := by
  rcases data.complete.selectedActualParents_nonempty with
    ⟨actualParent, actualParentMem⟩
  have actualFiberNonempty :
      (wz2PaperOrdinaryFullFiberIndices
        fine actualNearby.scaleData.coarse actualParent).Nonempty :=
    actualNearby.scaleData.cover
      |>.fullFiber_nonempty_of_uniform
        fineNonempty actualNearby.scaleData.full_fiber_uniform
        actualParent
  rcases actualFiberNonempty with
    ⟨ambientSource, ambientSourceMem⟩
  have ambientSourceParent :
      actualNearby.scaleData.cover.parent ambientSource =
        actualParent :=
    (actualNearby.scaleData.cover.mem_fullFiber_iff_parent_eq
      actualNearby.scaleData.rho_pos.le
      actualParent ambientSource).mp ambientSourceMem
  have ambientSourceSelected :
      ambientSource ∈ data.complete.selectedFineIndices := by
    unfold PureWZ2CompleteParentRestrictionData.selectedFineIndices
    exact
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ ambientSource,
          ambientSourceParent.symm ▸ actualParentMem⟩
  rcases
      data.complete.selectedFine_ambient_surjective
        ambientSource ambientSourceSelected
    with
    ⟨selectedSource, _⟩
  exact Fin.pos_iff_nonempty.mpr ⟨selectedSource⟩

/-- Package the one-class regularization theorem as dependent data. -/
theorem caller_class_schedule_regularization_data
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant R : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (callerParent : Fin quotient.callerCoarse.card)
    (fineNonempty : fine.Nonempty)
    (classWeightPos :
      0 < quotient.callerActualWeight callerParent)
    (classWeight_ne_top :
      quotient.callerActualWeight callerParent ≠ ⊤)
    (weightUpper : ENNReal)
    (weightUpper_ne_top : weightUpper ≠ ⊤)
    (actualWeightUpper :
      ∀ actualParent,
        pureWZ2ActualFiberShadedMass
            shading actualParent ≤
          weightUpper *
            wz2PaperOrdinaryFullFiberCount
              fine actualNearby.scaleData.coarse
              actualParent)
    (coordinateCount : ℕ)
    (coordinateCountPos : 0 < coordinateCount)
    (scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate : Fin coordinateCount,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (scaleGap :
      ∀ coordinate : Fin coordinateCount,
        4 * ((scheduled coordinate).rho - delta) ≤
            actualNearby.rho ∨
          4 * (actualNearby.rho - delta) ≤
            (scheduled coordinate).rho)
    (R_pos : 0 < R)
    (R_ne_top : R ≠ ⊤)
    (R_one : 1 ≤ R)
    (rounding :
      ∀ requested : WZ2PaperRequestedScale delta,
        ∃ coordinate : Fin coordinateCount,
          requested.1 ≤ (scales coordinate).1 ∧
          ENNReal.ofReal (scales coordinate).1 <
            R * ENNReal.ofReal requested.1)
    (window_absorption :
      R * ambientConstant ≤ outputConstant)
    (output_ne_top : outputConstant ≠ ⊤)
    (restriction_absorption :
      wz2PaperPureNearbyRestrictionConstant
          ambientConstant
          (quotient.callerActualWeight callerParent *
            fine.enncard⁻¹)
          (max ambientConstant
            (ambientConstant *
              pureWZ2CompleteParentDegreeConstant
                actualNearby.scaleData.coarse.card coordinateCount))
          (pureWZ2CompleteParentRegularizationLoss
              actualNearby.scaleData.coarse.card coordinateCount *
            weightUpper) ≤
        outputConstant) :
    Nonempty
      (PureWZ2CallerClassRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient callerParent coordinateCount) := by
  rcases
      caller_class_schedule_regularization
        ambient actualNearby quotient callerParent
        fineNonempty classWeightPos classWeight_ne_top
        weightUpper weightUpper_ne_top actualWeightUpper
        coordinateCount coordinateCountPos
        scales scheduled scaleGap
        R_pos R_ne_top R_one rounding
        window_absorption output_ne_top
        restriction_absorption
    with
    ⟨selectedActualParents, complete,
      regularizationLoss, selectedWeightLevel,
      selectedSubset, regularizationTop,
      regularizationEq,
      selectedLevelPos, selectedLevelTop,
      selectedWeightPos, retainedWeight, selectedCWA⟩
  exact
    ⟨{
      selectedActualParents := selectedActualParents
      complete := complete
      regularizationLoss := regularizationLoss
      selectedWeightLevel := selectedWeightLevel
      selected_subset := selectedSubset
      regularizationLoss_ne_top := regularizationTop
      regularizationLoss_eq := regularizationEq
      selectedWeightLevel_pos := selectedLevelPos
      selectedWeightLevel_ne_top := selectedLevelTop
      selected_weight_pos := selectedWeightPos
      retained_weight := retainedWeight
      pure_cwa := selectedCWA
    }⟩

/--
One regularized complete-actual-fiber family for every positive quotient
caller.
-/
structure PureWZ2AllPositiveCallerRegularizationData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
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
    (coordinateCount : ℕ) where
  fiberData :
    ∀ parent :
        Fin (quotient.callerCover.hitParentSubfamily
          quotient.positiveCallerFine).family.card,
      PureWZ2CallerClassRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient
        ((quotient.callerCover.hitParentSubfamily
          quotient.positiveCallerFine).embedding parent)
        coordinateCount

/-- Apply the complete-parent schedule regularizer to every positive caller. -/
theorem all_positive_caller_schedule_regularization
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant R : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
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
    (fineNonempty : fine.Nonempty)
    (weightUpper : ENNReal)
    (weightUpper_ne_top : weightUpper ≠ ⊤)
    (actualWeightUpper :
      ∀ actualParent,
        pureWZ2ActualFiberShadedMass
            shading actualParent ≤
          weightUpper *
            wz2PaperOrdinaryFullFiberCount
              fine actualNearby.scaleData.coarse
              actualParent)
    (coordinateCount : ℕ)
    (coordinateCountPos : 0 < coordinateCount)
    (scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate : Fin coordinateCount,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (scaleGap :
      ∀ coordinate : Fin coordinateCount,
        4 * ((scheduled coordinate).rho - delta) ≤
            actualNearby.rho ∨
          4 * (actualNearby.rho - delta) ≤
            (scheduled coordinate).rho)
    (R_pos : 0 < R)
    (R_ne_top : R ≠ ⊤)
    (R_one : 1 ≤ R)
    (rounding :
      ∀ requested : WZ2PaperRequestedScale delta,
        ∃ coordinate : Fin coordinateCount,
          requested.1 ≤ (scales coordinate).1 ∧
          ENNReal.ofReal (scales coordinate).1 <
            R * ENNReal.ofReal requested.1)
    (window_absorption :
      R * ambientConstant ≤ outputConstant)
    (output_ne_top : outputConstant ≠ ⊤)
    (restriction_absorption :
      ∀ parent :
          Fin (quotient.callerCover.hitParentSubfamily
            quotient.positiveCallerFine).family.card,
        wz2PaperPureNearbyRestrictionConstant
            ambientConstant
            (quotient.callerActualWeight
                ((quotient.callerCover.hitParentSubfamily
                  quotient.positiveCallerFine).embedding parent) *
              fine.enncard⁻¹)
            (max ambientConstant
              (ambientConstant *
                pureWZ2CompleteParentDegreeConstant
                  actualNearby.scaleData.coarse.card coordinateCount))
            (pureWZ2CompleteParentRegularizationLoss
                actualNearby.scaleData.coarse.card coordinateCount *
              weightUpper) ≤
          outputConstant) :
    Nonempty
      (PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient support coordinateCount) := by
  let fiberData :
      ∀ parent :
          Fin (quotient.callerCover.hitParentSubfamily
            quotient.positiveCallerFine).family.card,
        PureWZ2CallerClassRegularizationData
          (outputConstant := outputConstant)
          actualNearby quotient
          ((quotient.callerCover.hitParentSubfamily
            quotient.positiveCallerFine).embedding parent)
          coordinateCount :=
    fun parent =>
      Classical.choice <|
        caller_class_schedule_regularization_data
          ambient actualNearby quotient
          ((quotient.callerCover.hitParentSubfamily
            quotient.positiveCallerFine).embedding parent)
          fineNonempty
          (pos_iff_ne_zero.mpr
            (support.hitParent_ambient_positive parent))
          (support.hitParent_weight_ne_top parent)
          weightUpper weightUpper_ne_top actualWeightUpper
          coordinateCount coordinateCountPos
          scales scheduled scaleGap
          R_pos R_ne_top R_one rounding
          window_absorption output_ne_top
          (restriction_absorption parent)
  exact ⟨{ fiberData := fiberData }⟩

/--
Complete-parent regularization only on the caller weight-band selected before
local regularization.  This is the honest post-deletion order: tiny positive
caller classes are discarded before their normalization weights are used.
-/
structure PureWZ2PreselectedCallerRegularizationData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (coordinateCount : ℕ)
    {scales : Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    (preselection :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled) where
  fiberData :
    ∀ parent : Fin preselection.selected.family.card,
      PureWZ2CallerClassRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient
        ((pureWZ2PostDeletionPositiveCallerBase quotient).embedding
          (preselection.selected.embedding parent))
        coordinateCount

/-- Run the local regularizer only after caller weight-band preselection. -/
theorem preselected_caller_schedule_regularization
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant R : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (fineNonempty : fine.Nonempty)
    (weightUpper : ENNReal)
    (weightUpper_ne_top : weightUpper ≠ ⊤)
    (actualWeightUpper :
      ∀ actualParent,
        pureWZ2ActualFiberShadedMass
            shading actualParent ≤
          weightUpper *
            wz2PaperOrdinaryFullFiberCount
              fine actualNearby.scaleData.coarse actualParent)
    (coordinateCount : ℕ)
    (coordinateCountPos : 0 < coordinateCount)
    (scales : Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate : Fin coordinateCount,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (preselection :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    (scaleGap :
      ∀ coordinate : Fin coordinateCount,
        4 * ((scheduled coordinate).rho - delta) ≤
            actualNearby.rho ∨
          4 * (actualNearby.rho - delta) ≤
            (scheduled coordinate).rho)
    (R_pos : 0 < R)
    (R_ne_top : R ≠ ⊤)
    (R_one : 1 ≤ R)
    (rounding :
      ∀ requested : WZ2PaperRequestedScale delta,
        ∃ coordinate : Fin coordinateCount,
          requested.1 ≤ (scales coordinate).1 ∧
          ENNReal.ofReal (scales coordinate).1 <
            R * ENNReal.ofReal requested.1)
    (window_absorption :
      R * ambientConstant ≤ outputConstant)
    (output_ne_top : outputConstant ≠ ⊤)
    (restriction_absorption :
      ∀ parent : Fin preselection.selected.family.card,
        wz2PaperPureNearbyRestrictionConstant
            ambientConstant
            (pureWZ2PostDeletionPositiveCallerWeight quotient
                (preselection.selected.embedding parent) *
              fine.enncard⁻¹)
            (max ambientConstant
              (ambientConstant *
                pureWZ2CompleteParentDegreeConstant
                  actualNearby.scaleData.coarse.card coordinateCount))
            (pureWZ2CompleteParentRegularizationLoss
                actualNearby.scaleData.coarse.card coordinateCount *
              weightUpper) ≤
          outputConstant) :
    Nonempty
      (PureWZ2PreselectedCallerRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient coordinateCount preselection) := by
  let fiberData :
      ∀ parent : Fin preselection.selected.family.card,
        PureWZ2CallerClassRegularizationData
          (outputConstant := outputConstant)
          actualNearby quotient
          ((pureWZ2PostDeletionPositiveCallerBase quotient).embedding
            (preselection.selected.embedding parent))
          coordinateCount :=
    fun parent =>
      Classical.choice <|
        caller_class_schedule_regularization_data
          ambient actualNearby quotient
          ((pureWZ2PostDeletionPositiveCallerBase quotient).embedding
            (preselection.selected.embedding parent))
          fineNonempty
          (preselection.weightLevel_pos.trans_le
            (preselection.weight_band parent).1)
          (quotient.callerActualWeight_ne_top _)
          weightUpper weightUpper_ne_top actualWeightUpper
          coordinateCount coordinateCountPos
          scales scheduled scaleGap
          R_pos R_ne_top R_one rounding
          window_absorption output_ne_top
          (restriction_absorption parent)
  exact ⟨{ fiberData := fiberData }⟩

/--
Callback-free selected-caller regularization.  The common local output
constant is computed from the preselected weight level; later power
bookkeeping only has to dominate this one finite runtime constant.
-/
theorem preselected_caller_schedule_regularization_localFiberConstant
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant R : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (fineNonempty : fine.Nonempty)
    (weightUpper : ENNReal)
    (weightUpper_ne_top : weightUpper ≠ ⊤)
    (actualWeightUpper :
      ∀ actualParent,
        pureWZ2ActualFiberShadedMass
            shading actualParent ≤
          weightUpper *
            wz2PaperOrdinaryFullFiberCount
              fine actualNearby.scaleData.coarse actualParent)
    (coordinateCount : ℕ)
    (coordinateCountPos : 0 < coordinateCount)
    (scales : Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate : Fin coordinateCount,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (preselection :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    (scaleGap :
      ∀ coordinate : Fin coordinateCount,
        4 * ((scheduled coordinate).rho - delta) ≤
            actualNearby.rho ∨
          4 * (actualNearby.rho - delta) ≤
            (scheduled coordinate).rho)
    (R_pos : 0 < R)
    (R_ne_top : R ≠ ⊤)
    (R_one : 1 ≤ R)
    (rounding :
      ∀ requested : WZ2PaperRequestedScale delta,
        ∃ coordinate : Fin coordinateCount,
          requested.1 ≤ (scales coordinate).1 ∧
          ENNReal.ofReal (scales coordinate).1 <
            R * ENNReal.ofReal requested.1) :
    Nonempty
      (PureWZ2PreselectedCallerRegularizationData
        (outputConstant :=
          preselection.localFiberConstant R weightUpper)
        actualNearby quotient coordinateCount preselection) := by
  exact
    preselected_caller_schedule_regularization
      ambient actualNearby quotient fineNonempty
      weightUpper weightUpper_ne_top actualWeightUpper
      coordinateCount coordinateCountPos scales scheduled preselection
      scaleGap R_pos R_ne_top R_one rounding
      (preselection.localFiber_window_absorption R weightUpper)
      (preselection.localFiberConstant_ne_top
        R_ne_top ambient.2.1.2 weightUpper_ne_top)
      (preselection.localFiber_restriction_absorption R weightUpper)

end Kakeya.Assouad

end
