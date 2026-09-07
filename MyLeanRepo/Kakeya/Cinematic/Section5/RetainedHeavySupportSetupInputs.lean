import MyLeanRepo.Kakeya.Cinematic.Section5.IncidenceHeavySupportRegularization
import MyLeanRepo.Kakeya.Cinematic.Section5.RetainedIncidenceDegreeSetupInputs

/-!
# Heavy-parent and support regularization on retained incidences

Starting from the degree-regularized incidence graph on retained fine
rectangles, select quantitative heavy coarse parents and then one common
positive support-cardinality scale.  Every support remains inside the fixed
ambient family of the current bin.
-/

noncomputable section

namespace Kakeya.Cinematic

local instance : DecidableEq C2Function := Classical.decEq _

structure RetainedHeavySupportSetupData
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
    (fiberBound : ℝ) where
  M_parent : ℕ := 2 ^ refinement.parentLevel
  degreeLoss : ℕ :=
    Nat.log2 (Fintype.card (Fin fineSetup.fine.card)) + 1
  active : Finset (Fin coarseSetup.coarseData.coarse.card) :=
    incidenceParentSupport degreeSetup.selectedEdges
      coarseSetup.coarseData.parent
  rectangleBound : ℝ := 2 * M_parent
  heavyLogLoss : ℝ := 4 * degreeLoss
  heavyThreshold : ℝ :=
    rectangleBound * (q_fiber : ℝ) / heavyLogLoss
  heavy : Finset (Fin coarseSetup.coarseData.coarse.card) :=
    active.filter fun coarse =>
      heavyThreshold ≤
        ((incidenceParentEdges degreeSetup.selectedEdges
          coarseSetup.coarseData.parent coarse).card : ℝ)
  M_parent_eq :
    M_parent = 2 ^ refinement.parentLevel
  degreeLoss_eq :
    degreeLoss =
      Nat.log2 (Fintype.card (Fin fineSetup.fine.card)) + 1
  active_eq :
    active =
      incidenceParentSupport degreeSetup.selectedEdges
        coarseSetup.coarseData.parent
  rectangleBound_eq :
    rectangleBound = 2 * M_parent
  heavyLogLoss_eq :
    heavyLogLoss = 4 * degreeLoss
  heavyThreshold_eq :
    heavyThreshold =
      rectangleBound * (q_fiber : ℝ) / heavyLogLoss
  heavy_eq :
    heavy =
      active.filter fun coarse =>
        heavyThreshold ≤
          ((incidenceParentEdges degreeSetup.selectedEdges
            coarseSetup.coarseData.parent coarse).card : ℝ)
  heavy_lower :
    ((degreeSetup.selectedEdges.card : ℝ) / 2) /
        (rectangleBound * fiberBound) ≤
      (heavy.card : ℝ)
  heavy_nonempty : heavy.Nonempty
  heavy_aggregate :
    ∀ coarse ∈ heavy,
      ((incidenceRectangleSupport degreeSetup.selectedEdges
          coarseSetup.coarseData.parent coarse).card : ℝ) *
          (q_fiber : ℝ) ≤
        heavyLogLoss *
          (incidenceCountOverParent degreeSetup.selectedEdges
            coarseSetup.coarseData.parent coarse
            (incidenceFunctionSupport degreeSetup.selectedEdges
              coarseSetup.coarseData.parent coarse) : ℝ)
  ambient : Finset C2Function :=
    (data.ambientSource.cluster center (3 * tRep)).toFinset
  ambient_eq :
    ambient =
      (data.ambientSource.cluster center (3 * tRep)).toFinset
  supportLevel : ℕ
  selectedCoarse :
    Finset (Fin coarseSetup.coarseData.coarse.card)
  supportLevel_bound :
    supportLevel ≤ Nat.log2 ambient.card
  selectedCoarse_nonempty : selectedCoarse.Nonempty
  selectedCoarse_eq :
    selectedCoarse =
      heavy.filter (fun coarse =>
        2 ^ supportLevel ≤
            (incidenceFunctionSupport degreeSetup.selectedEdges
              coarseSetup.coarseData.parent coarse).card ∧
          (incidenceFunctionSupport degreeSetup.selectedEdges
            coarseSetup.coarseData.parent coarse).card <
              2 ^ (supportLevel + 1))
  support_retention :
    heavy.card ≤
      (Nat.log2 ambient.card + 1) * selectedCoarse.card
  selectedCoarse_subset : selectedCoarse ⊆ heavy
  support_range :
    ∀ coarse ∈ selectedCoarse,
      2 ^ supportLevel ≤
          (incidenceFunctionSupport degreeSetup.selectedEdges
            coarseSetup.coarseData.parent coarse).card ∧
        (incidenceFunctionSupport degreeSetup.selectedEdges
          coarseSetup.coarseData.parent coarse).card <
            2 ^ (supportLevel + 1)
  support_ambient :
    ∀ coarse ∈ heavy,
      incidenceFunctionSupport degreeSetup.selectedEdges
        coarseSetup.coarseData.parent coarse ⊆ ambient

def RetainedHeavySupportSetupStatement : Prop :=
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
      (fiberBound : ℝ),
      0 < q_fiber →
      0 < fiberBound →
      (∀ rectangle ∈ degreeSetup.retained,
        q_fiber ≤ (degreeSetup.fiber rectangle).card) →
      (∀ rectangle ∈ degreeSetup.retained,
        ((degreeSetup.fiber rectangle).card : ℝ) ≤ fiberBound) →
      Nonempty
        (RetainedHeavySupportSetupData
          data center hE fineSetup coarseSetup refinement
            degreeSetup q_fiber fiberBound)

end Kakeya.Cinematic
