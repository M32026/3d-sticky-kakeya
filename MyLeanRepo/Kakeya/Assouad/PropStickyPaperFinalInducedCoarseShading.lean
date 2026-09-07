import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalInducedCoarseShadingStatements

/-!
# Coarse shading induced from actual final fine incidences

Assign a final retained rho-cell to a coarse parent exactly when the parent's
actual final full fiber meets it.  Construct the literal coarse shading,
balanced cover, and exact active-parent incidence data with no ghost cells.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

theorem wz2_paper_final_induced_coarse_shading :
    WZ2PaperFinalInducedCoarseShadingStatement := by
  intro h_containment delta rho hdelta hrho h18 fine coarse cover
    hfine hcoarse sourceShading coarseCells availableFineCells
    balancing coarseData active fiberBand pairBand restriction
    finalFine hCrop
  let parentCells : Fin coarse.card → Finset WZ2PaperCellIndex :=
    fun parent =>
      finalFine.exact.retainedCoarseCells.filter fun cell =>
        ((restrictPaperShading
            (cover.fullFiberSubfamily parent)
            finalFine.exact.refined).union ∩
          wz1PaperGridCube rho cell).Nonempty
  have hparentCells_eq :
      ∀ parent,
        parentCells parent =
          finalFine.exact.retainedCoarseCells.filter fun cell =>
            ((restrictPaperShading
                (cover.fullFiberSubfamily parent)
                finalFine.exact.refined).union ∩
              wz1PaperGridCube rho cell).Nonempty := by
    intro parent
    rfl
  have hparentCells_subset :
      ∀ parent,
        parentCells parent ⊆ finalFine.exact.retainedCoarseCells := by
    intro parent
    exact Finset.filter_subset _ finalFine.exact.retainedCoarseCells
  have hretained_cell_owned :
      ∀ cell ∈ finalFine.exact.retainedCoarseCells,
        ∃ parent, cell ∈ parentCells parent := by
    intro cell hcell
    have hmass :
        volume
            (finalFine.exact.refined.union ∩
              wz1PaperGridCube rho cell) =
          finalFine.exact.cellMass :=
      finalFine.exact.fine_cell_mass cell hcell
    have hpositive :
        0 < volume
            (finalFine.exact.refined.union ∩
              wz1PaperGridCube rho cell) := by
      rw [hmass]
      exact finalFine.exact.cellMass_pos
    have hnonempty :
        (finalFine.exact.refined.union ∩
          wz1PaperGridCube rho cell).Nonempty := by
      by_contra hempty
      have hempty' :
          finalFine.exact.refined.union ∩
              wz1PaperGridCube rho cell =
            ∅ := by
        simpa [Set.not_nonempty_iff_eq_empty] using hempty
      rw [hempty'] at hpositive
      simp at hpositive
    rcases hnonempty with ⟨point, hpointUnion, hpointCube⟩
    rcases hpointUnion with ⟨source, hpointCarrier⟩
    let parent := cover.parent source
    let fiberIndices := wz2PaperFullFiberIndices fine coarse parent
    let fiberSubfamily := cover.fullFiberSubfamily parent
    have hpe : cover.parent source = parent := rfl
    have hiff : source ∈ fiberIndices ↔ cover.parent source = parent :=
      cover.mem_fullFiber_iff_parent parent source
    have hsource_in_fiber : source ∈ fiberIndices := hiff.mpr hpe
    let enumeration := fiberIndices.orderIsoOfFin rfl
    let i : Fin fiberSubfamily.family.card :=
      enumeration.symm ⟨source, hsource_in_fiber⟩
    have hembed : fiberSubfamily.embedding i = source :=
      congrArg Subtype.val
        (enumeration.apply_symm_apply ⟨source, hsource_in_fiber⟩)
    have hpoint_restricted :
        point ∈ (restrictPaperShading fiberSubfamily
            finalFine.exact.refined).carrier i := by
      simpa [restrictPaperShading, hembed] using hpointCarrier
    have hintersection :
        ((restrictPaperShading fiberSubfamily
            finalFine.exact.refined).union ∩
          wz1PaperGridCube rho cell).Nonempty :=
      ⟨point, ⟨i, hpoint_restricted⟩, hpointCube⟩
    have hmem : cell ∈ parentCells parent := by
      rw [Finset.mem_filter]
      exact ⟨hcell, hintersection⟩
    exact ⟨parent, hmem⟩
  have hparentCells_witness :
      ∀ parent cell, cell ∈ parentCells parent →
        ∃ source point,
          cover.parent source = parent ∧
          point ∈ finalFine.exact.refined.carrier source ∧
          point ∈ wz1PaperGridCube rho cell := by
    intro parent cell hcell
    have hintersection :
        ((restrictPaperShading
            (cover.fullFiberSubfamily parent)
            finalFine.exact.refined).union ∩
          wz1PaperGridCube rho cell).Nonempty :=
      (Finset.mem_filter.mp hcell).2
    rcases hintersection with ⟨point, hpointUnion, hpointCube⟩
    rcases hpointUnion with ⟨i, hpointCarrier⟩
    let source := (cover.fullFiberSubfamily parent).embedding i
    have hpointSource :
        point ∈ finalFine.exact.refined.carrier source := by
      simpa [restrictPaperShading] using hpointCarrier
    have hparent : cover.parent source = parent := by
      have hmem :
          source ∈ wz2PaperFullFiberIndices fine coarse parent :=
        cover.fullFiberSubfamily_mem parent i
      simpa [cover.mem_fullFiber_iff_parent] using hmem
    exact ⟨source, point, hparent, hpointSource, hpointCube⟩
  let coarseShading : WZ1PaperTubeShading coarse :=
    { carrier := fun parent =>
        ⋃ cell ∈ parentCells parent,
          wz1PaperGridCube rho cell
      measurable_carrier := fun parent => by
        apply MeasurableSet.iUnion
        intro cell
        apply MeasurableSet.iUnion
        intro _
        exact wz1PaperGridCube_measurable cell
      subset_body := fun parent => by
        apply iUnion_subset
        intro cell
        apply iUnion_subset
        intro hcell
        rcases hparentCells_witness parent cell hcell with
          ⟨source, point, hparent, hpointCarrier, hpointCube⟩
        have h1 : point ∈ finalFine.exact.refined.carrier source :=
          hpointCarrier
        have h2 : point ∈ finalFine.fineBand.carrier source :=
          finalFine.exact.refined_subshading source h1
        have h3 : point ∈ restriction.refined.carrier source := by
          have h4 : finalFine.fineBand.carrier source =
              restriction.refined.carrier source ∩ _ :=
            finalFine.fineBand_carrier_eq source
          rw [h4] at h2
          exact h2.1
        have h4 : point ∈ fiberBand.refined.carrier source :=
          restriction.refined_subshading source h3
        have h5 : point ∈ balancing.refined.carrier source :=
          fiberBand.refined_subshading source h4
        have h6 : point ∈ sourceShading.carrier source :=
          balancing.refined_subshading source h5
        have h7 : point ∈ wz1PaperTubeCarrier (fine.tube source) :=
          sourceShading.subset_body source h6
        have hintersection :
            (wz1PaperGridCube rho cell ∩
              wz1PaperTubeCarrier (fine.tube source)).Nonempty :=
          ⟨point, hpointCube, h7⟩
        have hfineLine :
            WZ1PaperTubeInLineClass (fine.tube source) :=
          hfine source
        have hcoarseLine :
            WZ1PaperTubeInLineClass (coarse.tube parent) :=
          hcoarse parent
        have hcovered :
            WZ1PaperTubeCovers
              (fine.tube source) (coarse.tube parent) := by
          have hparentCovered :=
            cover.toWZ1PaperTubeCover.parent_covers source
          simpa [hparent] using hparentCovered
        have hretained :
            cell ∈ finalFine.exact.retainedCoarseCells :=
          hparentCells_subset parent hcell
        have hcrop :
            wz1PaperGridCube rho cell ⊆
              Kakeya.Streamlined.axisBox 2 2 2 :=
          hCrop cell hretained
        exact
          h_containment hdelta hrho h18
            (fine.tube source) (coarse.tube parent)
            hfineLine hcoarseLine hcovered cell
            hintersection hcrop }
  have hcoarseShading_carrier_eq :
      ∀ parent,
        coarseShading.carrier parent =
          ⋃ cell ∈ parentCells parent,
            wz1PaperGridCube rho cell := by
    intro parent
    rfl
  have hpoint_compatibility :
      ∀ source point,
        point ∈ finalFine.exact.refined.carrier source →
          point ∈ coarseShading.carrier (cover.parent source) := by
    intro source point hpoint
    have hpointUnion :
        point ∈ finalFine.exact.refined.union :=
      ⟨source, hpoint⟩
    have hunion :
        finalFine.exact.refined.union =
          ⋃ fineCell ∈ finalFine.exact.retainedFineCells,
            wz1PaperGridCube delta fineCell :=
      finalFine.exact.refined_union_eq
    rw [hunion] at hpointUnion
    rcases mem_iUnion.mp hpointUnion with ⟨fineCell, hfineCell⟩
    rcases mem_iUnion.mp hfineCell with ⟨hfineRetained, hpointFineCube⟩
    have hfineMem :
        fineCell ∈ finalFine.exact.retainedFineCells :=
      hfineRetained
    have hfineUnion :
        finalFine.exact.retainedFineCells =
          finalFine.exact.retainedCoarseCells.biUnion
            finalFine.exact.selectedFineCells :=
      finalFine.exact.retainedFineCells_eq
    rw [hfineUnion] at hfineMem
    rcases Finset.mem_biUnion.mp hfineMem with
      ⟨coarseCell, hcoarseRetained, hselected⟩
    have hcoarseMem :
        coarseCell ∈ finalFine.exact.retainedCoarseCells :=
      hcoarseRetained
    have hselectedMem :
        fineCell ∈ finalFine.exact.selectedFineCells coarseCell :=
      hselected
    have hcontainment_fine :
        wz1PaperGridCube delta fineCell ⊆
          wz1PaperGridCube rho coarseCell :=
      finalFine.exact.fine_cell_containment
        coarseCell hcoarseMem fineCell hselectedMem
    have hpointCoarseCube :
        point ∈ wz1PaperGridCube rho coarseCell :=
      hcontainment_fine hpointFineCube
    let parent := cover.parent source
    let fiberIndices := wz2PaperFullFiberIndices fine coarse parent
    let fiberSubfamily := cover.fullFiberSubfamily parent
    have hpe : cover.parent source = parent := rfl
    have hiff : source ∈ fiberIndices ↔ cover.parent source = parent :=
      cover.mem_fullFiber_iff_parent parent source
    have hsource_in_fiber : source ∈ fiberIndices := hiff.mpr hpe
    let enumeration := fiberIndices.orderIsoOfFin rfl
    let i : Fin fiberSubfamily.family.card :=
      enumeration.symm ⟨source, hsource_in_fiber⟩
    have hembed : fiberSubfamily.embedding i = source :=
      congrArg Subtype.val
        (enumeration.apply_symm_apply ⟨source, hsource_in_fiber⟩)
    have hpoint_restricted :
        point ∈ (restrictPaperShading fiberSubfamily
            finalFine.exact.refined).carrier i := by
      simpa [restrictPaperShading, hembed] using hpoint
    have hintersection :
        ((restrictPaperShading fiberSubfamily
            finalFine.exact.refined).union ∩
          wz1PaperGridCube rho coarseCell).Nonempty :=
      ⟨point, ⟨i, hpoint_restricted⟩, hpointCoarseCube⟩
    have hparentCell :
        coarseCell ∈ parentCells parent := by
      rw [Finset.mem_filter]
      exact ⟨hcoarseMem, hintersection⟩
    have hpointParent :
        point ∈ coarseShading.carrier parent := by
      exact
        mem_iUnion.mpr
          ⟨coarseCell,
            mem_iUnion.mpr
              ⟨hparentCell, hpointCoarseCube⟩⟩
    exact hpointParent
  have hcoarse_cubical :
      WZ1PaperIsCubicalShading coarseShading := by
    intro parent point hpoint other hother
    rcases mem_iUnion.mp hpoint with ⟨cell, hpoint⟩
    rcases mem_iUnion.mp hpoint with ⟨hcell, hpointCell⟩
    have hindex :
        wz1PaperGridIndex rho point = cell :=
      (mem_wz1PaperGridCube rho cell point).mp hpointCell
    have hsame :
        other ∈ wz1PaperGridCube rho cell := by
      rw [hindex] at hother
      exact hother
    exact
      mem_iUnion.mpr
        ⟨cell, mem_iUnion.mpr ⟨hcell, hsame⟩⟩
  have hcoarse_union_eq :
      coarseShading.union =
        ⋃ cell ∈ finalFine.exact.retainedCoarseCells,
          wz1PaperGridCube rho cell := by
    ext point
    constructor
    · rintro ⟨parent, hpoint⟩
      rcases mem_iUnion.mp hpoint with ⟨cell, hpoint⟩
      rcases mem_iUnion.mp hpoint with ⟨hcell, hpointCell⟩
      have hretained :
          cell ∈ finalFine.exact.retainedCoarseCells :=
        hparentCells_subset parent hcell
      exact
        mem_iUnion.mpr
          ⟨cell, mem_iUnion.mpr ⟨hretained, hpointCell⟩⟩
    · intro hpoint
      rcases mem_iUnion.mp hpoint with ⟨cell, hpoint⟩
      rcases mem_iUnion.mp hpoint with ⟨hcell, hpointCell⟩
      rcases hretained_cell_owned cell hcell with
        ⟨parent, hparentCell⟩
      exact
        ⟨parent,
          mem_iUnion.mpr
            ⟨cell, mem_iUnion.mpr
              ⟨hparentCell, hpointCell⟩⟩⟩
  let balancedCover :
      WZ1PaperBalancedCoverData
        cover.toWZ1PaperTubeCover
        finalFine.exact.refined coarseShading :=
    { point_compatibility := hpoint_compatibility
      coarse_cubical := hcoarse_cubical
      activeCells := finalFine.exact.retainedCoarseCells
      coarse_union_eq := hcoarse_union_eq
      cellMass := finalFine.exact.cellMass
      cellMass_pos := finalFine.exact.cellMass_pos
      cellMass_ne_top := finalFine.exact.cellMass_ne_top
      fine_cell_mass := finalFine.exact.fine_cell_mass }
  let activeParents :
      WZ2PaperCellIndex → Finset (Fin coarse.card) :=
    fun cell =>
      Finset.univ.filter fun parent =>
        cell ∈ parentCells parent
  have hactiveParents_eq :
      ∀ cell,
        activeParents cell =
          Finset.univ.filter fun parent =>
            cell ∈ parentCells parent := by
    intro cell
    rfl
  have hactiveParents_nonempty :
      ∀ cell ∈ finalFine.exact.retainedCoarseCells,
        (activeParents cell).Nonempty := by
    intro cell hcell
    rcases hretained_cell_owned cell hcell with
      ⟨parent, hparentCell⟩
    have hmem : parent ∈ activeParents cell := by
      rw [hactiveParents_eq cell]
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ parent, hparentCell⟩
    exact ⟨parent, hmem⟩
  let representative : WZ2PaperCellIndex → Point3 :=
    active.representative
  have hrepresentative_mem :
      ∀ cell,
        representative cell ∈ wz1PaperGridCube rho cell :=
    active.representative_mem
  have hactiveParents_card_eq :
      ∀ cell ∈ finalFine.exact.retainedCoarseCells,
        (activeParents cell).card =
          coarseShading.pointMultiplicity (representative cell) := by
    intro cell hcell
    let point := representative cell
    have hpointCell : point ∈ wz1PaperGridCube rho cell :=
      hrepresentative_mem cell
    have h_iff :
        ∀ (parent : Fin coarse.card),
          parent ∈ activeParents cell ↔
            point ∈ coarseShading.carrier parent := by
      intro parent
      constructor
      · intro hparent
        have hmem : cell ∈ parentCells parent := by
          rw [hactiveParents_eq cell] at hparent
          exact (Finset.mem_filter.mp hparent).2
        have h :
            point ∈ coarseShading.carrier parent := by
          exact
            mem_iUnion.mpr
              ⟨cell, mem_iUnion.mpr ⟨hmem, hpointCell⟩⟩
        exact h
      · intro hpoint
        rcases mem_iUnion.mp hpoint with ⟨otherCell, hpoint⟩
        rcases mem_iUnion.mp hpoint with
          ⟨hotherCell, hpointOtherCube⟩
        have hindex1 :
            wz1PaperGridIndex rho point = otherCell :=
          (mem_wz1PaperGridCube rho otherCell point).mp
            hpointOtherCube
        have hindex2 :
            wz1PaperGridIndex rho point = cell :=
          (mem_wz1PaperGridCube rho cell point).mp hpointCell
        have heq : otherCell = cell :=
          hindex1.symm.trans hindex2
        rw [heq] at hotherCell
        have hmem : cell ∈ parentCells parent := hotherCell
        rw [hactiveParents_eq cell]
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ parent, hmem⟩
    have hset_eq :
        activeParents cell =
          Finset.univ.filter fun parent =>
            point ∈ coarseShading.carrier parent := by
      ext x
      constructor
      · intro h
        have h' : point ∈ coarseShading.carrier x := (h_iff x).mp h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, h'⟩
      · intro h
        have h' : point ∈ coarseShading.carrier x := (Finset.mem_filter.mp h).2
        exact (h_iff x).mpr h'
    rw [hset_eq]
    <;> rfl
  have hparent_cell_nonempty :
      ∀ cell ∈ finalFine.exact.retainedCoarseCells,
        ∀ parent ∈ activeParents cell,
          ((restrictPaperShading
              (cover.fullFiberSubfamily parent)
              finalFine.exact.refined).union ∩
            wz1PaperGridCube rho cell).Nonempty := by
    intro cell hcell parent hparent
    have hmem : cell ∈ parentCells parent := by
      rw [hactiveParents_eq cell] at hparent
      exact (Finset.mem_filter.mp hparent).2
    exact (Finset.mem_filter.mp hmem).2
  exact
    ⟨{
      parentCells := parentCells
      parentCells_eq := hparentCells_eq
      parentCells_subset := hparentCells_subset
      retained_cell_owned := hretained_cell_owned
      coarseShading := coarseShading
      coarse_carrier_eq := hcoarseShading_carrier_eq
      coarse_cubical := hcoarse_cubical
      coarse_union_eq := hcoarse_union_eq
      point_compatibility := hpoint_compatibility
      balanced := balancedCover
      balanced_activeCells_eq := rfl
      balanced_cellMass_eq := rfl
      activeParents := activeParents
      activeParents_eq := hactiveParents_eq
      activeParents_nonempty := hactiveParents_nonempty
      representative := representative
      representative_mem := hrepresentative_mem
      activeParents_card_eq := hactiveParents_card_eq
      parent_cell_nonempty := hparent_cell_nonempty
    }⟩

end Kakeya.Assouad

end
