import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalBalancedCoverExactAdapterStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalInducedCoarseAdapter

/-! # Exact-cell adapter for the final multiplicity-banded cover -/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem wz2_paper_final_balanced_cover_exact_adapter :
    WZ2PaperFinalBalancedCoverExactAdapterStatement := by
  intro delta rho fine coarse cover sourceShading coarseCells
    availableFineCells balancing coarseData hdelta hrho producer
  let selectedCells := producer.coarseBand.selectedCells
  let selectedFineCells :=
    producer.finalFine.exact.selectedFineCells
  let retainedFineCells :=
    selectedCells.biUnion selectedFineCells
  let finalFine := producer.coarseBand.selectedFineShading
  let finalCoarse := producer.coarseBand.selectedCoarseShading
  have hSelectedFineDisjoint :
      ∀ first ∈ selectedCells, ∀ second ∈ selectedCells,
        first ≠ second →
          Disjoint
            (selectedFineCells first)
            (selectedFineCells second) := by
    intro first hfirst second hsecond hne
    rw [Finset.disjoint_left]
    intro fineCell hfirstFine hsecondFine
    let point : Point3 := cellCorner delta fineCell
    have hpointFine :
        point ∈ wz1PaperGridCube delta fineCell :=
      cellCorner_mem_gridCube hdelta fineCell
    have hpointFirst :
        point ∈ wz1PaperGridCube rho first :=
      producer.finalFine.exact.fine_cell_containment
        first (producer.coarseBand.selectedCells_subset hfirst)
        fineCell hfirstFine hpointFine
    have hpointSecond :
        point ∈ wz1PaperGridCube rho second :=
      producer.finalFine.exact.fine_cell_containment
        second (producer.coarseBand.selectedCells_subset hsecond)
        fineCell hsecondFine hpointFine
    exact
      Set.disjoint_left.mp
        (wz1PaperGridCube_disjoint hne)
        hpointFirst hpointSecond
  have hFinalFineUnion :
      finalFine.union =
        ⋃ fineCell ∈ retainedFineCells,
          wz1PaperGridCube delta fineCell := by
    rw [producer.coarseBand.selectedFine_union_eq]
    rw [producer.coarseBand.selectedRegion_eq]
    apply Set.Subset.antisymm
    · intro point hpoint
      rcases Set.mem_iUnion₂.mp hpoint.2 with
        ⟨cell, hcell, hpointCell⟩
      have hpointExact :
          point ∈
            producer.finalFine.exact.refined.union ∩
              wz1PaperGridCube rho cell :=
        ⟨hpoint.1, hpointCell⟩
      have hcellExact :
          cell ∈ producer.finalFine.exact.retainedCoarseCells :=
        producer.coarseBand.selectedCells_subset hcell
      have hIntersection :=
        wz2RefinedUnion_inter_coarseCube
          producer.finalFine.exact.retainedFineCells_eq
          producer.finalFine.exact.fine_cell_containment
          hcellExact
      have hIntersection' :
          producer.finalFine.exact.refined.union ∩
              wz1PaperGridCube rho cell =
            ⋃ fineCell ∈
                producer.finalFine.exact.selectedFineCells cell,
              wz1PaperGridCube delta fineCell := by
        rw [producer.finalFine.exact.refined_union_eq]
        exact hIntersection
      rw [hIntersection'] at hpointExact
      rcases Set.mem_iUnion₂.mp hpointExact with
        ⟨fineCell, hfine, hpointFine⟩
      exact Set.mem_iUnion₂.mpr
        ⟨fineCell,
          Finset.mem_biUnion.mpr ⟨cell, hcell, hfine⟩,
          hpointFine⟩
    · intro point hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨fineCell, hfine, hpointFine⟩
      rcases Finset.mem_biUnion.mp hfine with
        ⟨cell, hcell, hfineCell⟩
      have hcellExact :
          cell ∈ producer.finalFine.exact.retainedCoarseCells :=
        producer.coarseBand.selectedCells_subset hcell
      have hpointCoarse :
          point ∈ wz1PaperGridCube rho cell :=
        producer.finalFine.exact.fine_cell_containment
          cell hcellExact fineCell hfineCell hpointFine
      have hpointExact :
          point ∈ producer.finalFine.exact.refined.union := by
        rw [producer.finalFine.exact.refined_union_eq]
        exact Set.mem_iUnion₂.mpr
          ⟨fineCell,
            by
              rw [producer.finalFine.exact.retainedFineCells_eq]
              exact Finset.mem_biUnion.mpr
                ⟨cell, hcellExact, hfineCell⟩,
            hpointFine⟩
      exact
        ⟨hpointExact,
          Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCoarse⟩⟩
  have hFineMultiplicity :
      ∀ point ∈ finalFine.union,
        (2 ^ producer.finalFine.fineLevel : ENNReal) ≤
            (finalFine.pointMultiplicity point : ENNReal) ∧
          (finalFine.pointMultiplicity point : ENNReal) <
            (2 ^ (producer.finalFine.fineLevel + 1) : ENNReal) := by
    intro point hpoint
    have hpointExact :
        point ∈ producer.finalFine.exact.refined.union :=
      (by
        rw [producer.coarseBand.selectedFine_union_eq] at hpoint
        exact hpoint.1)
    have hEq :
        finalFine.pointMultiplicity point =
          producer.finalFine.exact.refined.pointMultiplicity point :=
      wholeCellRestriction_pointMultiplicity_eq
        producer.coarseBand.selectedFine_carrier_eq hpoint
    rw [hEq]
    exact producer.finalFine.exact_multiplicity_band
      point hpointExact
  let exact :
      WZ2PaperExactCellBalancingData
        (rho := rho) finalFine selectedCells selectedFineCells :=
    { level := producer.finalFine.exact.level
      retainedCoarseCells := selectedCells
      retainedCoarseCells_subset := fun _ h => h
      retainedCoarseCells_nonempty :=
        producer.coarseBand.selectedCells_nonempty
      selectedFineCells := selectedFineCells
      selectedFineCells_subset := by
        intro cell _ fineCell hfine
        exact hfine
      selectedFineCells_card := by
        intro cell hcell
        exact
          producer.finalFine.exact.selectedFineCells_card
            cell
            (producer.coarseBand.selectedCells_subset hcell)
      availableFineCells_band := by
        intro cell hcell
        have hcard :=
          producer.finalFine.exact.selectedFineCells_card
            cell
            (producer.coarseBand.selectedCells_subset hcell)
        rw [hcard]
        constructor
        · exact le_rfl
        · calc
            2 ^ producer.finalFine.exact.level <
                2 * 2 ^ producer.finalFine.exact.level := by
              have hpos :
                  0 < 2 ^ producer.finalFine.exact.level :=
                Nat.pow_pos (by norm_num)
              omega
            _ =
                2 ^ (producer.finalFine.exact.level + 1) := by
              rw [pow_succ]
              ring
      retainedFineCells := retainedFineCells
      retainedFineCells_eq := rfl
      retainedFineCells_count := by
        have hEq :
            (∑ cell ∈ selectedCells,
                (selectedFineCells cell).card) =
              retainedFineCells.card := by
          dsimp only [retainedFineCells]
          symm
          exact Finset.card_biUnion hSelectedFineDisjoint
        rw [hEq]
        exact Nat.le_mul_of_pos_left _ (by omega)
      refined := finalFine
      refined_carrier_eq := by
        intro index
        change
          finalFine.carrier index =
            finalFine.carrier index ∩
              wz2RetainedCellsUnion delta retainedFineCells
        apply Set.Subset.antisymm
        · intro point hpoint
          exact
            ⟨hpoint,
              by
                have hpointUnion :
                    point ∈ finalFine.union :=
                  ⟨index, hpoint⟩
                rw [hFinalFineUnion] at hpointUnion
                exact hpointUnion⟩
        · exact Set.inter_subset_left
      refined_subshading := fun _ => Set.Subset.rfl
      refined_cubical :=
        producer.coarseBand.selectedFine_cubical
      refined_union_eq := hFinalFineUnion
      cellMass := producer.finalFine.exact.cellMass
      cellMass_eq := producer.finalFine.exact.cellMass_eq
      cellMass_pos := producer.finalFine.exact.cellMass_pos
      cellMass_ne_top := producer.finalFine.exact.cellMass_ne_top
      fine_cell_mass := producer.coarseBand.selected_cell_mass
      fine_cell_containment := by
        intro cell hcell fineCell hfine
        exact
          producer.finalFine.exact.fine_cell_containment
            cell
            (producer.coarseBand.selectedCells_subset hcell)
            fineCell hfine }
  let finalCoarseData :
      WZ2PaperCoarseShadingData
        cover finalFine selectedCells selectedFineCells exact :=
    { parentCells := fun parent =>
        producer.induced.parentCells parent ∩ selectedCells
      parentCells_subset := by
        intro parent cell hcell
        exact (Finset.mem_inter.mp hcell).2
      parentCells_witness := by
        intro parent cell hcell
        rcases
            producer.induced.toCoarseShadingData.parentCells_witness
              parent cell (Finset.mem_inter.mp hcell).1
          with ⟨source, point, hparent, hpoint, hpointCell⟩
        exact
          ⟨source, point, hparent,
            by
              change point ∈ finalFine.carrier source
              rw [producer.coarseBand.selectedFine_carrier_eq]
              exact
                ⟨hpoint,
                  by
                    rw [producer.coarseBand.selectedRegion_eq]
                    exact Set.mem_iUnion₂.mpr
                      ⟨cell, (Finset.mem_inter.mp hcell).2,
                        hpointCell⟩⟩,
            hpointCell⟩
      retained_cell_owned := by
        intro cell hcell
        rcases producer.induced.retained_cell_owned
            cell
            (producer.coarseBand.selectedCells_subset hcell) with
          ⟨parent, hparent⟩
        exact
          ⟨parent, Finset.mem_inter.mpr ⟨hparent, hcell⟩⟩
      coarseShading := finalCoarse
      coarseShading_carrier_eq := by
        intro parent
        rw [producer.coarseBand.selectedCoarse_carrier_eq]
        rw [producer.induced.coarse_carrier_eq]
        rw [producer.coarseBand.selectedRegion_eq]
        ext point
        simp only [Set.mem_inter_iff, Set.mem_iUnion,
          Finset.mem_inter]
        constructor
        · rintro ⟨⟨cell, hparent, hpoint⟩,
            selectedCell, hselected, hpointSelected⟩
          have hcellEq : cell = selectedCell := by
            have hfirst :
                wz1PaperGridIndex rho point = cell :=
              (mem_wz1PaperGridCube rho cell point).mp hpoint
            have hsecond :
                wz1PaperGridIndex rho point = selectedCell :=
              (mem_wz1PaperGridCube rho selectedCell point).mp
                hpointSelected
            exact hfirst.symm.trans hsecond
          exact
            ⟨cell, ⟨hparent, by simpa [hcellEq] using hselected⟩,
              hpoint⟩
        · rintro ⟨cell, ⟨hparent, hselected⟩, hpoint⟩
          exact
            ⟨⟨cell, hparent, hpoint⟩,
              ⟨cell, hselected, hpoint⟩⟩
      balancedCover := producer.finalCover.balanced }
  exact
    ⟨{
      retainedFineCells := retainedFineCells
      retainedFineCells_eq := rfl
      exact := exact
      exact_refined_eq := rfl
      coarseData := finalCoarseData
      coarseData_coarseShading_eq := rfl
      fine_multiplicity_band := hFineMultiplicity
    }⟩

end Kakeya.Assouad

end
