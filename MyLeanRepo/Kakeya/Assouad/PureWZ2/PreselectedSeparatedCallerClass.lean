import MyLeanRepo.Kakeya.Assouad.PureWZ2.AllCallerClassScheduleRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinarySeparatedCWASelection

/-!
# Source-separated local fibers after caller preselection

The caller weight band is selected before any local regularization.  Inside
each selected caller, the complete-parent regularizer first produces a genuine
union of actual complete fibers with nearby CWA.  This module then performs
the paper's ordinary source-conflict refinement on that exact local family,
before any merge or whole-cell balancing.

The output keeps the original caller provenance, the full forward mass loss,
fresh nearby CWA on the selected family, and the strong source separation
needed after unit rescaling.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- One complete-parent caller class after the ordinary source-conflict
refinement and CWA rebuild. -/
structure PureWZ2SeparatedCallerClassRegularizationData
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
    (coordinateCount : ℕ)
    (base : PureWZ2CallerClassRegularizationData
      (outputConstant := outputConstant) actualNearby quotient callerParent
      coordinateCount) where
  separated :
    PureWZ2OrdinarySeparatedCWASelectionData
      (restrictPaperShading base.complete.selectedFine.toTubeSubfamily shading)

namespace PureWZ2SeparatedCallerClassRegularizationData

variable
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
    {base : PureWZ2CallerClassRegularizationData
      (outputConstant := outputConstant) actualNearby quotient callerParent
      coordinateCount}
    (data : PureWZ2SeparatedCallerClassRegularizationData
      actualNearby quotient callerParent coordinateCount base)

/-- The selected local family, embedded all the way back into the normalized
ambient fine family. -/
noncomputable def selected : WZ2PaperPureTubeSubfamily fine :=
  base.complete.selectedFine.comp data.separated.selected

/-- The literal selected local shading on the ambient source. -/
noncomputable def selectedShading : WZ1PaperTubeShading data.selected.family :=
  restrictPaperShading data.selected.toTubeSubfamily shading

theorem selectedShading_eq_separated :
    data.selectedShading = data.separated.selectedShading := by
  rw [data.separated.selectedShading_eq]
  rfl

theorem selected_nonempty : data.selected.family.Nonempty :=
  data.separated.selected_nonempty

/-- The exact original quotient caller remains the parent of every tube after
the local source-conflict refinement. -/
theorem selected_caller_covers
    (index : Fin data.selected.family.card) :
    WZ1PaperTubeCovers
      (data.selected.family.tube index)
      (quotient.callerCoarse.tube callerParent) := by
  let localIndex := data.separated.selected.embedding index
  let ambientIndex := base.complete.selectedFine.embedding localIndex
  let actualParent := actualNearby.scaleData.cover.parent ambientIndex
  have actualMem : actualParent ∈ base.selectedActualParents :=
    base.complete.selectedFine_parent_mem localIndex
  have classMem :
      actualParent ∈ quotient.callerActualParents callerParent :=
    base.selected_subset actualMem
  have centerEq :
      quotient.net.center actualParent = quotient.callerCenter callerParent :=
    (Finset.mem_filter.mp classMem).2
  have ambientCover :=
    quotient.caller_covers_of_actual_center
      ambientIndex actualParent callerParent rfl centerEq
  have sourceTubeEq :
      data.selected.family.tube index = fine.tube ambientIndex := by
    calc
      data.selected.family.tube index =
          data.separated.selected.family.tube index := rfl
      _ = base.complete.selectedFine.toTubeSubfamily.family.tube
          (data.separated.selected.embedding index) :=
        data.separated.selected.tube_eq index
      _ = fine.tube ambientIndex := by
        exact base.complete.selectedFine.tube_eq
          (data.separated.selected.embedding index)
  rw [sourceTubeEq]
  exact ambientCover

/-- The two finite local losses are both paid before the caller classes are
merged. -/
theorem caller_weight_retention :
    quotient.callerActualWeight callerParent ≤
      (base.regularizationLoss * data.separated.retentionLoss) *
        data.selectedShading.mass := by
  let completeShading :=
    restrictPaperShading base.complete.selectedFine.toTubeSubfamily shading
  have baseRetention :
      quotient.callerActualWeight callerParent ≤
        base.regularizationLoss * completeShading.mass := by
    calc
      quotient.callerActualWeight callerParent ≤
          base.regularizationLoss *
            ∑ parent ∈ base.selectedActualParents,
              pureWZ2ActualFiberShadedMass shading parent :=
        base.retained_weight
      _ = base.regularizationLoss * completeShading.mass := by
        rw [base.complete.restrictedShading_mass_eq
          shading actualNearby.scaleData.rho_pos.le]
  calc
    quotient.callerActualWeight callerParent ≤
        base.regularizationLoss * completeShading.mass := baseRetention
    _ ≤ base.regularizationLoss *
        (data.separated.retentionLoss *
          data.separated.selectedShading.mass) := by
      gcongr
      exact data.separated.retained_mass
    _ = (base.regularizationLoss * data.separated.retentionLoss) *
        data.selectedShading.mass := by
      rw [data.selectedShading_eq_separated]
      exact (mul_assoc _ _ _).symm

theorem pure_cwa :
    WZ2PaperPureCWAAtNearbyScales
      data.selected.family data.separated.outputConstant :=
  data.separated.pure_cwa

theorem strongly_separated :
    ∀ first second, first ≠ second →
      wz2PaperLiteralSourceSeparationFactor * delta <
        wz1PaperLineDistance
          (data.selected.family.tube first)
          (data.selected.family.tube second) :=
  data.separated.strongly_separated

/-- Turn the weighted separation into a fixed-exponent paper refinement once
its actual finite loss has been absorbed. -/
noncomputable def toPaperRefinement
    (logExponent : ℕ)
    (absorption :
      wz1PaperRefinementFraction delta logExponent *
          data.separated.retentionLoss ≤ 1) :
    WZ1PaperRefinement
      (restrictPaperShading base.complete.selectedFine.toTubeSubfamily shading)
      logExponent where
  selected := data.separated.selected.toTubeSubfamily
  refined := data.separated.selectedShading
  subshading := by
    intro index
    rw [data.separated.selectedShading_eq]
    exact Set.Subset.rfl
  retained_mass := by
    calc
      wz1PaperRefinementFraction delta logExponent *
            (restrictPaperShading
              base.complete.selectedFine.toTubeSubfamily shading).mass ≤
          wz1PaperRefinementFraction delta logExponent *
            (data.separated.retentionLoss *
              data.separated.selectedShading.mass) := by
        gcongr
        exact data.separated.retained_mass
      _ =
          (wz1PaperRefinementFraction delta logExponent *
            data.separated.retentionLoss) *
              data.separated.selectedShading.mass := by ring
      _ ≤ 1 * data.separated.selectedShading.mass := by
        gcongr
      _ = data.separated.selectedShading.mass := by simp

end PureWZ2SeparatedCallerClassRegularizationData

/-- Run the ordinary source-conflict refinement on one already-regularized
selected caller class. -/
theorem pureWZ2_separated_caller_class_regularization
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
    (coordinateCount : ℕ)
    (base : PureWZ2CallerClassRegularizationData
      (outputConstant := outputConstant) actualNearby quotient callerParent
      coordinateCount)
    (callerWeightPos : 0 < quotient.callerActualWeight callerParent)
    (boundedBase : HasBoundedBase fine 4)
    (deltaLtOne : delta < 1) :
    Nonempty
      (PureWZ2SeparatedCallerClassRegularizationData
        actualNearby quotient callerParent coordinateCount base) := by
  let completeShading :=
    restrictPaperShading base.complete.selectedFine.toTubeSubfamily shading
  have completeMassPos : 0 < completeShading.mass := by
    have productPos : 0 < base.regularizationLoss * completeShading.mass :=
      callerWeightPos.trans_le <| by
        calc
          quotient.callerActualWeight callerParent ≤
              base.regularizationLoss *
                ∑ parent ∈ base.selectedActualParents,
                  pureWZ2ActualFiberShadedMass shading parent :=
            base.retained_weight
          _ = base.regularizationLoss * completeShading.mass := by
            rw [base.complete.restrictedShading_mass_eq
              shading actualNearby.scaleData.rho_pos.le]
    exact (ENNReal.mul_pos_iff.mp productPos).2
  have completeLine : WZ1PaperIsLineClass
      base.complete.selectedFine.family :=
    quotient.ambient_fine_line_class.subfamily
      base.complete.selectedFine.toTubeSubfamily
  have completeBounded : HasBoundedBase
      base.complete.selectedFine.family 4 := by
    intro index
    rw [base.complete.selectedFine.tube_eq]
    exact boundedBase (base.complete.selectedFine.embedding index)
  rcases
      pureWZ2_ordinary_separated_cwa_selection
        completeShading outputConstant base.pure_cwa completeLine
        completeBounded completeMassPos deltaLtOne
    with
    ⟨separated⟩
  exact ⟨{ separated := separated }⟩

end Kakeya.Assouad

end
