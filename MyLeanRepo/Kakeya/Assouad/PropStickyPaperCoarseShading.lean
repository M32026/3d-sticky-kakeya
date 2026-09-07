import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoarseShadingStatements

/-!
# Exactly balanced coarse paper shading

Construct the coarse shading as the union of the retained whole `rho`-cells
owned by each parent.  The supplied coarse-cell containment theorem puts every
such cell in its parent paper tube, while positive balanced cell mass ensures
that every retained cell has an owner.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

theorem wz2_prop_sticky_paper_coarse_shading :
    WZ2PropStickyPaperCoarseShadingStatement := by
  intro h_containment delta rho hdelta hrho h18 fine coarse cover
    hfine hcoarse sourceShading hsourceCubical coarseCells
    hcoarseNonempty availableFineCells hAvailableNonempty
    hAvailableSubset balanced hCrop
  let parentCells : Fin coarse.card → Finset (ℤ × ℤ × ℤ) :=
    fun parent =>
      balanced.retainedCoarseCells.filter fun cell =>
        ∃ source : Fin fine.card,
          cover.toWZ1PaperTubeCover.parent source = parent ∧
          (balanced.refined.carrier source ∩
            wz1PaperGridCube rho cell).Nonempty
  have hparentCells_subset :
      ∀ parent,
        parentCells parent ⊆ balanced.retainedCoarseCells := by
    intro parent
    exact Finset.filter_subset _ balanced.retainedCoarseCells
  have hparentCells_witness :
      ∀ parent cell, cell ∈ parentCells parent →
        ∃ source point,
          cover.toWZ1PaperTubeCover.parent source = parent ∧
          point ∈ balanced.refined.carrier source ∧
          point ∈ wz1PaperGridCube rho cell := by
    intro parent cell hcell
    have hretained :
        cell ∈ balanced.retainedCoarseCells :=
      (Finset.mem_filter.mp hcell).1
    have hwitness :
        ∃ source : Fin fine.card,
          cover.toWZ1PaperTubeCover.parent source = parent ∧
          (balanced.refined.carrier source ∩
            wz1PaperGridCube rho cell).Nonempty :=
      (Finset.mem_filter.mp hcell).2
    rcases hwitness with
      ⟨source, hparent, hnonempty⟩
    rcases hnonempty with
      ⟨point, hpointCarrier, hpointCube⟩
    exact
      ⟨source, point, hparent, hpointCarrier, hpointCube⟩
  have hretained_cell_owned :
      ∀ cell ∈ balanced.retainedCoarseCells,
        ∃ parent, cell ∈ parentCells parent := by
    intro cell hcell
    have hmass :
        volume
            (balanced.refined.union ∩
              wz1PaperGridCube rho cell) =
          balanced.cellMass :=
      balanced.fine_cell_mass cell hcell
    have hpositive :
        0 <
          volume
            (balanced.refined.union ∩
              wz1PaperGridCube rho cell) := by
      rw [hmass]
      exact balanced.cellMass_pos
    have hnonempty :
        (balanced.refined.union ∩
          wz1PaperGridCube rho cell).Nonempty := by
      by_contra hempty
      have hempty' :
          balanced.refined.union ∩
              wz1PaperGridCube rho cell =
            ∅ := by
        simpa [Set.not_nonempty_iff_eq_empty] using hempty
      rw [hempty'] at hpositive
      simp at hpositive
    rcases hnonempty with
      ⟨point, hpointUnion, hpointCube⟩
    rcases hpointUnion with
      ⟨source, hpointCarrier⟩
    let parent :=
      cover.toWZ1PaperTubeCover.parent source
    have hintersection :
        (balanced.refined.carrier source ∩
          wz1PaperGridCube rho cell).Nonempty :=
      ⟨point, hpointCarrier, hpointCube⟩
    have hmem :
        cell ∈ parentCells parent := by
      rw [Finset.mem_filter]
      exact
        ⟨hcell, ⟨source, rfl, hintersection⟩⟩
    exact ⟨parent, hmem⟩
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
        have hrefined :
            point ∈ balanced.refined.carrier source :=
          hpointCarrier
        have hrefined_sub :
            balanced.refined.carrier source ⊆
              sourceShading.carrier source :=
          balanced.refined_subshading source
        have hsource :
            point ∈ sourceShading.carrier source :=
          hrefined_sub hrefined
        have hsource_sub :
            sourceShading.carrier source ⊆
              wz1PaperTubeCarrier (fine.tube source) :=
          sourceShading.subset_body source
        have hpointFine :
            point ∈ wz1PaperTubeCarrier (fine.tube source) :=
          hsource_sub hsource
        have hintersection :
            (wz1PaperGridCube rho cell ∩
              wz1PaperTubeCarrier (fine.tube source)).Nonempty :=
          ⟨point, hpointCube, hpointFine⟩
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
            cell ∈ balanced.retainedCoarseCells :=
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
        point ∈ balanced.refined.carrier source →
          point ∈
            coarseShading.carrier
              (cover.toWZ1PaperTubeCover.parent source) := by
    intro source point hpoint
    have hpointUnion :
        point ∈ balanced.refined.union :=
      ⟨source, hpoint⟩
    have hunion :
        balanced.refined.union =
          ⋃ fineCell ∈ balanced.retainedFineCells,
            wz1PaperGridCube delta fineCell :=
      balanced.refined_union_eq
    rw [hunion] at hpointUnion
    rcases mem_iUnion.mp hpointUnion with
      ⟨fineCell, hfineCell⟩
    rcases mem_iUnion.mp hfineCell with
      ⟨hfineRetained, hpointFineCube⟩
    have hfineMem :
        fineCell ∈ balanced.retainedFineCells :=
      hfineRetained
    have hfineUnion :
        balanced.retainedFineCells =
          balanced.retainedCoarseCells.biUnion
            balanced.selectedFineCells :=
      balanced.retainedFineCells_eq
    rw [hfineUnion] at hfineMem
    rcases Finset.mem_biUnion.mp hfineMem with
      ⟨coarseCell, hcoarseRetained, hselected⟩
    have hcoarseMem :
        coarseCell ∈ balanced.retainedCoarseCells :=
      hcoarseRetained
    have hselectedMem :
        fineCell ∈ balanced.selectedFineCells coarseCell :=
      hselected
    have havailable :
        fineCell ∈ availableFineCells coarseCell :=
      (balanced.selectedFineCells_subset
        coarseCell hcoarseMem) hselectedMem
    have hcoarseCell :
        coarseCell ∈ coarseCells :=
      balanced.retainedCoarseCells_subset hcoarseMem
    have hfineCube_sub :
        wz1PaperGridCube delta fineCell ⊆
          wz1PaperGridCube rho coarseCell :=
      (hAvailableSubset
        coarseCell hcoarseCell fineCell havailable).2
    have hpointCoarseCube :
        point ∈ wz1PaperGridCube rho coarseCell :=
      hfineCube_sub hpointFineCube
    have hintersection :
        (balanced.refined.carrier source ∩
          wz1PaperGridCube rho coarseCell).Nonempty :=
      ⟨point, hpoint, hpointCoarseCube⟩
    let parent :=
      cover.toWZ1PaperTubeCover.parent source
    have hparentCell :
        coarseCell ∈ parentCells parent := by
      rw [Finset.mem_filter]
      exact
        ⟨hcoarseMem, ⟨source, rfl, hintersection⟩⟩
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
    rcases mem_iUnion.mp hpoint with
      ⟨cell, hpoint⟩
    rcases mem_iUnion.mp hpoint with
      ⟨hcell, hpointCell⟩
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
        ⋃ cell ∈ balanced.retainedCoarseCells,
          wz1PaperGridCube rho cell := by
    ext point
    constructor
    · rintro ⟨parent, hpoint⟩
      rcases mem_iUnion.mp hpoint with
        ⟨cell, hpoint⟩
      rcases mem_iUnion.mp hpoint with
        ⟨hcell, hpointCell⟩
      have hretained :
          cell ∈ balanced.retainedCoarseCells :=
        hparentCells_subset parent hcell
      exact
        mem_iUnion.mpr
          ⟨cell, mem_iUnion.mpr
            ⟨hretained, hpointCell⟩⟩
    · intro hpoint
      rcases mem_iUnion.mp hpoint with
        ⟨cell, hpoint⟩
      rcases mem_iUnion.mp hpoint with
        ⟨hcell, hpointCell⟩
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
        balanced.refined coarseShading :=
    { point_compatibility := hpoint_compatibility
      coarse_cubical := hcoarse_cubical
      activeCells := balanced.retainedCoarseCells
      coarse_union_eq := hcoarse_union_eq
      cellMass := balanced.cellMass
      cellMass_pos := balanced.cellMass_pos
      cellMass_ne_top := balanced.cellMass_ne_top
      fine_cell_mass := balanced.fine_cell_mass }
  exact
    ⟨{
      parentCells := parentCells
      parentCells_subset := hparentCells_subset
      parentCells_witness := hparentCells_witness
      retained_cell_owned := hretained_cell_owned
      coarseShading := coarseShading
      coarseShading_carrier_eq :=
        hcoarseShading_carrier_eq
      balancedCover := balancedCover }⟩

end Kakeya.Assouad

end
