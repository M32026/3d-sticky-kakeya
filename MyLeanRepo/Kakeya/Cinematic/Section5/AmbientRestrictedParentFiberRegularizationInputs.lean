import MyLeanRepo.Kakeya.Cinematic.Section5.IncidenceRectangleFiberRegularizationInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.RetainedHeavySupportSetupInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedCoarseIncidenceSubfamily

/-!
# Selected incidence fibers below each fixed-bin parent

For every selected heavy parent, regularize the selected incidence-fiber
cardinality across its active fine rectangles.  The output is the exact
`G'(R)` family required before applying the pointwise good-pair and fixed-pair
incidence estimates.
-/

noncomputable section

namespace Kakeya.Cinematic

local instance ambientRestrictedParentFiberRegularizationDecidableEq :
    DecidableEq C2Function := Classical.decEq _

structure AmbientRestrictedParentFiberRegularizationData
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
    (center : C2Function)
    (hE : MeasurableSet E)
    {C_R C_count C_shading C_volume : ℝ}
    (fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume)
    (coarseSetup : AmbientRestrictedCoarseSetupData
      data center hE fineSetup)
    {massExponent : ℝ}
    (refinement : AmbientRestrictedLargeBinRefinementData
      data center hE fineSetup coarseSetup massExponent)
    (degreeSetup : RetainedIncidenceDegreeSetupData
      data center hE fineSetup coarseSetup refinement)
    (q_fiber : ℕ)
    (fiberBound : ℝ)
    (heavySetup : RetainedHeavySupportSetupData
      data center hE fineSetup coarseSetup refinement
        degreeSetup q_fiber fiberBound) where
  pairLower :
    Fin
      (selectedCoarseSubfamily coarseSetup.coarseData
        heavySetup.selectedCoarse).card →
      ℕ
  selectedRectangles :
    Fin
      (selectedCoarseSubfamily coarseSetup.coarseData
        heavySetup.selectedCoarse).card →
      Finset (Fin fineSetup.fine.card)
  pairLower_eq : ∀ index,
    pairLower index =
      Nat.ceil
        ((q_fiber : ℝ) / (2 * heavySetup.heavyLogLoss))
  pairLower_pos : ∀ index, 0 < pairLower index
  selectedRectangles_eq : ∀ index,
    selectedRectangles index =
      (incidenceRectangleSupport degreeSetup.selectedEdges
        coarseSetup.coarseData.parent
        ((selectedCoarseSubfamily coarseSetup.coarseData
          heavySetup.selectedCoarse).embedding index)).filter
        (fun rectangle =>
          (q_fiber : ℝ) / (2 * heavySetup.heavyLogLoss) ≤
            ((incidenceRectangleFiber
              degreeSetup.selectedEdges rectangle).card : ℝ))
  selectedRectangles_nonempty : ∀ index,
    (selectedRectangles index).Nonempty
  selected_card_lower : ∀ index,
    (((incidenceParentEdges degreeSetup.selectedEdges
          coarseSetup.coarseData.parent
          ((selectedCoarseSubfamily coarseSetup.coarseData
            heavySetup.selectedCoarse).embedding index)).card : ℝ) / 2) /
        fiberBound ≤
      ((selectedRectangles index).card : ℝ)
  q_fiber_le_pairLower : ∀ index,
    (q_fiber : ℝ) ≤
      2 * heavySetup.heavyLogLoss * (pairLower index : ℝ)
  selected_fiber_lower : ∀ index, ∀ rectangle ∈ selectedRectangles index,
    pairLower index ≤
      (incidenceRectangleFiber
        degreeSetup.selectedEdges rectangle).card
  selectedRectangles_subset_retained : ∀ index,
    selectedRectangles index ⊆ degreeSetup.retained
  selected_fiber_subset_original : ∀ rectangle,
    incidenceRectangleFiber degreeSetup.selectedEdges rectangle ⊆
      (degreeSetup.fiber rectangle).toFinset

def AmbientRestrictedParentFiberRegularizationStatement : Prop :=
  IncidenceRectangleFiberRegularizationStatement.{0, 0, 0} →
    ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
      {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ},
      ∀ (data : DyadicFineAssignmentData
          family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
        (center : C2Function)
        (hE : MeasurableSet E)
        {C_R C_count C_shading C_volume : ℝ}
        (fineSetup : AmbientRestrictedFSVSetupData
          data center hE C_R C_count C_shading C_volume)
        (coarseSetup : AmbientRestrictedCoarseSetupData
          data center hE fineSetup)
        {massExponent : ℝ}
        (refinement : AmbientRestrictedLargeBinRefinementData
          data center hE fineSetup coarseSetup massExponent)
        (degreeSetup : RetainedIncidenceDegreeSetupData
          data center hE fineSetup coarseSetup refinement)
        (q_fiber : ℕ)
        (fiberBound : ℝ)
        (heavySetup : RetainedHeavySupportSetupData
          data center hE fineSetup coarseSetup refinement
            degreeSetup q_fiber fiberBound),
        0 < q_fiber →
        1 ≤ heavySetup.heavyLogLoss →
        0 < fiberBound →
        (∀ rectangle ∈ degreeSetup.retained,
          ((degreeSetup.fiber rectangle).card : ℝ) ≤ fiberBound) →
        Nonempty
          (AmbientRestrictedParentFiberRegularizationData
            data center hE fineSetup coarseSetup refinement
              degreeSetup q_fiber fiberBound heavySetup)

end Kakeya.Cinematic

end section
