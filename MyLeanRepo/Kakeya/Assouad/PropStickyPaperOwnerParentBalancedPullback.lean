import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCompleteCoarseSelectionPullback
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperOwnerParentNestedSelection

/-!
# Exact balanced pullback of the fixed-loss owner-parent selection

The selected coarse family is a subfamily of the dominant-owner parents.
Retain every fine tube in its complete parent fibers.  Since each retained
spatial cell has one dominant owner, a cell is kept exactly when that owner is
selected.  On every kept cell the complete-parent restriction agrees with the
ambient exactified shading, so the common balanced cell mass is unchanged.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

structure WZ2PaperOwnerParentBalancedPullbackData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover :
      WZ2PaperPartitioningCover
        fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) fineShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover fineShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover fineShading coarseCells availableFineCells
        balancing coarseData}
    (owner : WZ2PaperDirectOwnerPreparationData producer)
    (selectedPacked :
      Kakeya.Streamlined.TubeSubfamily
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          coarse
          owner.exactified.retainedParents).family) where
  pullback :
    WZ2PaperCompleteCoarseSelectionPullbackData
      owner.exactified.restrictedCover
      owner.exactified.refined
      owner.exactified.coarseShading
      selectedPacked
  selectedCells : Finset WZ2PaperCellIndex
  selectedCells_eq :
    selectedCells =
      owner.exactified.retainedCells.filter fun cell =>
        ∃ parent : Fin selectedPacked.family.card,
          owner.dominant.dominantParent cell =
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              coarse
              owner.exactified.retainedParents).embedding
                (selectedPacked.embedding parent)
  selectedCells_nonempty : selectedCells.Nonempty
  selected_coarse_carrier_eq :
    ∀ parent : Fin selectedPacked.family.card,
      pullback.selectedCoarseShading.carrier parent =
        ⋃ cell ∈ selectedCells,
          if
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                coarse
                owner.exactified.retainedParents).embedding
                  (selectedPacked.embedding parent) =
                owner.dominant.dominantParent cell
          then wz1PaperGridCube rho cell
          else ∅
  selected_fine_inter_cell_eq :
    ∀ cell ∈ selectedCells,
      pullback.selectedFineShading.union ∩
          wz1PaperGridCube rho cell =
        owner.exactified.refined.union ∩
          wz1PaperGridCube rho cell
  balanced :
    WZ1PaperBalancedCoverData
      pullback.restrictedCover.toWZ1PaperTubeCover
      pullback.selectedFineShading
      pullback.selectedCoarseShading
  balanced_activeCells_eq :
    balanced.activeCells = selectedCells
  balanced_cellMass_eq :
    balanced.cellMass = owner.exactified.balanced.cellMass
  parent_fiber_mass_floor :
    ∀ parent : Fin selectedPacked.family.card,
      owner.exactified.balanced_cellMass ≤
        (restrictPaperShading
          (pullback.restrictedCover.fullFiberSubfamily parent)
          pullback.selectedFineShading).mass

theorem wz2_paper_owner_subfamily_balanced_pullback
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover :
      WZ2PaperPartitioningCover
        fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) fineShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover fineShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover fineShading coarseCells availableFineCells
        balancing coarseData}
    (owner : WZ2PaperDirectOwnerPreparationData producer)
    (selectedPacked :
      Kakeya.Streamlined.TubeSubfamily
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          coarse
          owner.exactified.retainedParents).family)
    (selectedPackedNonempty : selectedPacked.family.Nonempty) :
    Nonempty
      (WZ2PaperOwnerParentBalancedPullbackData
        owner selectedPacked) := by
  let packed :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      coarse
      owner.exactified.retainedParents
  rcases
      wz2_paper_complete_coarse_selection_pullback
        owner.exactified.restrictedCover
        owner.exactified.refined
        owner.exactified.coarseShading
        owner.exactified.refined_cubical
        owner.exactified.balanced.coarse_cubical
        owner.exactified.balanced.point_compatibility
        selectedPacked
    with ⟨pullback⟩
  let selectedCells : Finset WZ2PaperCellIndex :=
    owner.exactified.retainedCells.filter fun cell =>
      ∃ parent : Fin selectedPacked.family.card,
        owner.dominant.dominantParent cell =
          packed.embedding (selectedPacked.embedding parent)
  have hSelectedCellsNonempty : selectedCells.Nonempty := by
    have hSelectedPackedCardPos : 0 < selectedPacked.family.card :=
      selectedPackedNonempty
    let parent : Fin selectedPacked.family.card :=
      ⟨0, hSelectedPackedCardPos⟩
    have hParentMem :
        packed.embedding (selectedPacked.embedding parent) ∈
          owner.exactified.retainedParents := by
      exact
        Finset.orderEmbOfFin_mem
          owner.exactified.retainedParents rfl
          (selectedPacked.embedding parent)
    rcases
        owner.exactified.owner_surjective
          (packed.embedding (selectedPacked.embedding parent))
          hParentMem
      with ⟨cell, hCell, hOwner⟩
    exact
      ⟨cell,
        Finset.mem_filter.mpr
          ⟨hCell, ⟨parent, hOwner⟩⟩⟩
  have hSelectedCoarseCarrier :
      ∀ parent : Fin selectedPacked.family.card,
        pullback.selectedCoarseShading.carrier parent =
          ⋃ cell ∈ selectedCells,
            if
                packed.embedding
                    (selectedPacked.embedding parent) =
                  owner.dominant.dominantParent cell
            then wz1PaperGridCube rho cell
            else ∅ := by
    intro parent
    rw [pullback.selectedCoarseShading_eq]
    change
      owner.exactified.coarseShading.carrier
          (selectedPacked.embedding parent) =
        _
    rw [owner.exactified.coarse_carrier_eq
      (selectedPacked.embedding parent)]
    ext point
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨cell, hCell, hPoint⟩
      by_cases hOwner :
          packed.embedding (selectedPacked.embedding parent) =
            owner.dominant.dominantParent cell
      · have hSelected : cell ∈ selectedCells := by
          apply Finset.mem_filter.mpr
          exact ⟨hCell, ⟨parent, hOwner.symm⟩⟩
        have hOwnerActual :
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              coarse
              owner.exactified.retainedParents).embedding
                (selectedPacked.embedding parent) =
              owner.dominant.dominantParent cell := by
          change
            packed.embedding
                (selectedPacked.embedding parent) =
              owner.dominant.dominantParent cell
          exact hOwner
        exact
          ⟨cell, hSelected, by
            rw [if_pos hOwner]
            rwa [if_pos hOwnerActual] at hPoint⟩
      · have hOwnerActual :
            ¬
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                coarse
                owner.exactified.retainedParents).embedding
                  (selectedPacked.embedding parent) =
                owner.dominant.dominantParent cell := by
          change
            ¬ packed.embedding
                (selectedPacked.embedding parent) =
              owner.dominant.dominantParent cell
          exact hOwner
        rw [if_neg hOwnerActual] at hPoint
        exact False.elim hPoint
    · rintro ⟨cell, hCell, hPoint⟩
      exact
        ⟨cell, (Finset.mem_filter.mp hCell).1, hPoint⟩
  have hCoarseUnion :
      pullback.selectedCoarseShading.union =
        ⋃ cell ∈ selectedCells,
          wz1PaperGridCube rho cell := by
    ext point
    change
      (∃ parent : Fin selectedPacked.family.card,
          point ∈ pullback.selectedCoarseShading.carrier parent) ↔
        point ∈
          ⋃ cell ∈ selectedCells,
            wz1PaperGridCube rho cell
    constructor
    · rintro ⟨parent, hPoint⟩
      rw [hSelectedCoarseCarrier parent] at hPoint
      rcases Set.mem_iUnion₂.mp hPoint with
        ⟨cell, hCell, hPoint⟩
      by_cases hOwner :
          packed.embedding (selectedPacked.embedding parent) =
            owner.dominant.dominantParent cell
      · rw [if_pos hOwner] at hPoint
        exact Set.mem_iUnion₂.mpr ⟨cell, hCell, hPoint⟩
      · rw [if_neg hOwner] at hPoint
        exact False.elim hPoint
    · intro hPoint
      rcases Set.mem_iUnion₂.mp hPoint with
        ⟨cell, hCell, hPoint⟩
      rcases (Finset.mem_filter.mp hCell).2 with
        ⟨parent, hOwner⟩
      refine ⟨parent, ?_⟩
      rw [hSelectedCoarseCarrier parent]
      exact
        Set.mem_iUnion₂.mpr
          ⟨cell, hCell, by
            rw [if_pos hOwner.symm]
            exact hPoint⟩
  have hSelectedFineSurjective :
      ∀ source,
        source ∈ pullback.selectedFineIndices →
          ∃ index : Fin pullback.selectedFine.family.card,
            pullback.selectedFine.embedding index = source := by
    rw [pullback.selectedFine_eq]
    intro source hSource
    let member : pullback.selectedFineIndices := ⟨source, hSource⟩
    let index :
        Fin
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            owner.exactified.selected.family
            pullback.selectedFineIndices).family.card :=
      (pullback.selectedFineIndices.orderIsoOfFin rfl).symm member
    exact
      ⟨index,
        congrArg Subtype.val
          (pullback.selectedFineIndices.orderIsoOfFin rfl
            |>.apply_symm_apply member)⟩
  have hSelectedFineCell :
      ∀ cell ∈ selectedCells,
        pullback.selectedFineShading.union ∩
            wz1PaperGridCube rho cell =
          owner.exactified.refined.union ∩
            wz1PaperGridCube rho cell := by
    intro cell hCell
    ext point
    change
      ((∃ index : Fin pullback.selectedFine.family.card,
          point ∈ pullback.selectedFineShading.carrier index) ∧
        point ∈ wz1PaperGridCube rho cell) ↔
      ((∃ sourceIndex : Fin owner.exactified.selected.family.card,
          point ∈ owner.exactified.refined.carrier sourceIndex) ∧
        point ∈ wz1PaperGridCube rho cell)
    constructor
    · rintro ⟨⟨index, hPoint⟩, hPointCell⟩
      refine ⟨?_, hPointCell⟩
      refine ⟨pullback.selectedFine.embedding index, ?_⟩
      rw [pullback.selectedFineShading_eq] at hPoint
      exact hPoint
    · rintro ⟨⟨sourceIndex, hPoint⟩, hPointCell⟩
      rcases
          owner.exactified.refined_owner
            sourceIndex point hPoint
        with ⟨ownerCell, hOwnerCell, hPointOwnerCell, hOwner⟩
      have hCellEq : ownerCell = cell := by
        by_contra hNe
        exact
          Set.disjoint_left.mp
            (wz1PaperGridCube_disjoint hNe)
            hPointOwnerCell hPointCell
      have hOwnerAtCell :
          packed.embedding
              (owner.exactified.restrictedCover.parent sourceIndex) =
            owner.dominant.dominantParent cell := by
        change
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
              coarse
              owner.exactified.retainedParents).embedding
                (owner.exactified.restrictedCover.parent sourceIndex) =
            owner.dominant.dominantParent cell
        rwa [hCellEq] at hOwner
      rcases (Finset.mem_filter.mp hCell).2 with
        ⟨selectedParent, hSelectedOwner⟩
      have hRestrictedParent :
          owner.exactified.restrictedCover.parent sourceIndex =
            selectedPacked.embedding selectedParent := by
        apply packed.embedding.injective
        calc
          packed.embedding
                (owner.exactified.restrictedCover.parent sourceIndex) =
              owner.dominant.dominantParent cell := by
            exact hOwnerAtCell
          _ =
              packed.embedding
                (selectedPacked.embedding selectedParent) :=
            hSelectedOwner
      have hSourceSelected :
          sourceIndex ∈ pullback.selectedFineIndices := by
        rw [pullback.selectedFineIndices_eq]
        apply Finset.mem_filter.mpr
        exact
          ⟨Finset.mem_univ _,
            ⟨selectedParent, hRestrictedParent⟩⟩
      rcases
          hSelectedFineSurjective sourceIndex hSourceSelected
        with ⟨selectedIndex, hSelectedIndex⟩
      refine ⟨⟨selectedIndex, ?_⟩, hPointCell⟩
      rw [pullback.selectedFineShading_eq]
      change
        point ∈
          owner.exactified.refined.carrier
            (pullback.selectedFine.embedding selectedIndex)
      rwa [hSelectedIndex]
  let balanced :
      WZ1PaperBalancedCoverData
        pullback.restrictedCover.toWZ1PaperTubeCover
        pullback.selectedFineShading
        pullback.selectedCoarseShading :=
    {
      point_compatibility := pullback.point_compatibility
      coarse_cubical := pullback.selectedCoarse_cubical
      activeCells := selectedCells
      coarse_union_eq := hCoarseUnion
      cellMass := owner.exactified.balanced.cellMass
      cellMass_pos := owner.exactified.balanced.cellMass_pos
      cellMass_ne_top := owner.exactified.balanced.cellMass_ne_top
      fine_cell_mass := by
        intro cell hCell
        rw [hSelectedFineCell cell hCell]
        apply owner.exactified.balanced.fine_cell_mass
        rw [owner.exactified.balanced_activeCells_eq]
        exact (Finset.mem_filter.mp hCell).1
    }
  have hParentFloor :
      ∀ parent : Fin selectedPacked.family.card,
        owner.exactified.balanced_cellMass ≤
          (restrictPaperShading
            (pullback.restrictedCover.fullFiberSubfamily parent)
            pullback.selectedFineShading).mass := by
    intro parent
    rw [pullback.full_fiber_mass_eq parent]
    exact
      owner.exactified.parent_fiber_mass_floor
        (selectedPacked.embedding parent)
  exact
    ⟨{
      pullback := pullback
      selectedCells := selectedCells
      selectedCells_eq := rfl
      selectedCells_nonempty := hSelectedCellsNonempty
      selected_coarse_carrier_eq := hSelectedCoarseCarrier
      selected_fine_inter_cell_eq := hSelectedFineCell
      balanced := balanced
      balanced_activeCells_eq := rfl
      balanced_cellMass_eq := rfl
      parent_fiber_mass_floor := hParentFloor
    }⟩

theorem wz2_paper_owner_parent_balanced_pullback
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {cover :
      WZ2PaperPartitioningCover
        fine prepared.callerStrict.coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := caller.1) fineShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover fineShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < caller.1}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover fineShading coarseCells availableFineCells
        balancing coarseData}
    (owner : WZ2PaperDirectOwnerPreparationData producer)
    {schedule :
      WZ2PaperCallerCoarsePrefixScheduleData prepared}
    (selection :
      WZ2PaperOwnerParentNestedSelectionData owner schedule) :
    Nonempty
      (WZ2PaperOwnerParentBalancedPullbackData
        owner selection.selectedPacked) :=
  wz2_paper_owner_subfamily_balanced_pullback
    owner selection.selectedPacked
    selection.selected_nonempty_family

end Kakeya.Assouad

end
