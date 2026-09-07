import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedLargeBinRefinementInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.FineFiberIncidenceGraph
import MyLeanRepo.Kakeya.Cinematic.Section5.IncidenceDegreeRegularizationInputs

/-!
# Degree regularization on retained fine rectangles

Build the function--rectangle incidence graph only on the fine rectangles
retained by the piece-volume and coarse-parent pigeonholes, then select one
uniform positive incidence-degree class.
-/

noncomputable section

namespace Kakeya.Cinematic

local instance : DecidableEq C2Function := Classical.decEq _

structure RetainedIncidenceDegreeSetupData
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
      data center hE fineSetup coarseSetup massExponent) where
  retained : Finset (Fin fineSetup.fine.card) :=
    rectanglesOverParents refinement.selected
      coarseSetup.coarseData.parent refinement.selectedParents
  fiber : Fin fineSetup.fine.card → FiniteFunctionFamily :=
    fun i => fineSetup.pointData.fiber (fineSetup.source i)
  rawEdges : Finset (C2Function × Fin fineSetup.fine.card) :=
    fineFiberIncidenceEdgesOn retained fiber
  retained_eq :
    retained =
      rectanglesOverParents refinement.selected
        coarseSetup.coarseData.parent refinement.selectedParents
  fiber_eq :
    fiber =
      fun i => fineSetup.pointData.fiber (fineSetup.source i)
  rawEdges_eq :
    rawEdges = fineFiberIncidenceEdgesOn retained fiber
  rawEdges_nonempty : rawEdges.Nonempty
  degreeLevel : ℕ
  selectedEdges : Finset (C2Function × Fin fineSetup.fine.card)
  degreeLevel_bound :
    degreeLevel ≤ Nat.log2 (Fintype.card (Fin fineSetup.fine.card))
  selectedEdges_eq :
    selectedEdges =
      rawEdges.filter (fun edge =>
        2 ^ degreeLevel ≤
            incidenceDegree rawEdges coarseSetup.coarseData.parent
              edge.1 (coarseSetup.coarseData.parent edge.2) ∧
          incidenceDegree rawEdges coarseSetup.coarseData.parent
              edge.1 (coarseSetup.coarseData.parent edge.2) <
            2 ^ (degreeLevel + 1))
  degree_retention :
    rawEdges.card ≤
      (Nat.log2 (Fintype.card (Fin fineSetup.fine.card)) + 1) *
        selectedEdges.card
  degree_range :
    ∀ function coarse,
      incidenceDegree selectedEdges coarseSetup.coarseData.parent
          function coarse = 0 ∨
        (2 ^ degreeLevel ≤
            incidenceDegree selectedEdges coarseSetup.coarseData.parent
              function coarse ∧
          incidenceDegree selectedEdges coarseSetup.coarseData.parent
              function coarse < 2 ^ (degreeLevel + 1))
  selectedEdges_subset :
    selectedEdges ⊆ rawEdges
  selectedEdges_nonempty : selectedEdges.Nonempty

def RetainedIncidenceDegreeSetupStatement : Prop :=
  IncidenceDegreeRegularizationStatement.{0, 0, 0} →
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
          data center hE fineSetup coarseSetup massExponent),
        (∀ i ∈
          rectanglesOverParents refinement.selected
            coarseSetup.coarseData.parent refinement.selectedParents,
          (fineSetup.pointData.fiber (fineSetup.source i)).carrier.Nonempty) →
        Nonempty
          (RetainedIncidenceDegreeSetupData
            data center hE fineSetup coarseSetup refinement)

end Kakeya.Cinematic
