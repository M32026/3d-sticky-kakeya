import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedParentDeletionRestrictionStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantOwnerExactificationHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers

/-! # Restrict repaired parent deletion to complete retained fibers -/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem wz2_paper_balanced_parent_deletion_restriction :
    WZ2PaperBalancedParentDeletionRestrictionStatement := by
  intro delta rho fine coarse cover sourceShading coarseCells
    availableFineCells balancing coarseData hdelta hrho active
    degreeCap referenceFiberMass threshold deletion
  let selectedFineIndices : Finset (Fin fine.card) :=
    Finset.univ.filter fun source =>
      cover.parent source ∈ deletion.retainedParents
  let selected :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      fine selectedFineIndices
  let selectedFineShading :=
    restrictPaperShading selected deletion.refined
  let coarseSub :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      coarse deletion.retainedParents
  let restrictedCover :=
    cover.restrict deletion.retainedParents
      deletion.retainedParents_nonempty
  have hPointData :
      ∀ (source : Fin fine.card) point,
        point ∈ deletion.refined.carrier source →
          ∃ cell ∈ deletion.goodCells,
            point ∈ wz1PaperGridCube rho cell ∧
              cover.parent source ∈ active.activeParents cell := by
    intro source point hpoint
    have hpointUnion : point ∈ deletion.refined.union :=
      ⟨source, hpoint⟩
    rw [deletion.refined_union_eq] at hpointUnion
    rcases Set.mem_iUnion₂.mp hpointUnion with
      ⟨fineCell, hfineCell, hpointFine⟩
    rw [deletion.retainedFineCells_eq] at hfineCell
    rcases Finset.mem_biUnion.mp hfineCell with
      ⟨cell, hcell, hfineCellSelected⟩
    have hcellAmbient :
        cell ∈ balancing.retainedCoarseCells :=
      deletion.goodCells_subset hcell
    have hpointCoarse :
        point ∈ wz1PaperGridCube rho cell :=
      balancing.fine_cell_containment
        cell hcellAmbient fineCell hfineCellSelected hpointFine
    have hpointBalanced :
        point ∈ balancing.refined.carrier source :=
      deletion.refined_subshading source hpoint
    have hpointParent :
        point ∈
          coarseData.coarseShading.carrier (cover.parent source) :=
      coarseData.balancedCover.point_compatibility
        source point hpointBalanced
    rw [coarseData.coarseShading_carrier_eq] at hpointParent
    rcases Set.mem_iUnion₂.mp hpointParent with
      ⟨parentCell, hparentCell, hpointParentCell⟩
    have hcellEq : parentCell = cell := by
      have hfirst :
          wz1PaperGridIndex rho point = parentCell :=
        (mem_wz1PaperGridCube rho parentCell point).mp
          hpointParentCell
      have hsecond :
          wz1PaperGridIndex rho point = cell :=
        (mem_wz1PaperGridCube rho cell point).mp hpointCoarse
      exact hfirst.symm.trans hsecond
    have hactive :
        cover.parent source ∈ active.activeParents cell := by
      rw [active.activeParents_eq]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by simpa [hcellEq] using hparentCell⟩
    exact ⟨cell, hcell, hpointCoarse, hactive⟩
  have hSourceRetained :
      ∀ source : Fin fine.card,
        (deletion.refined.carrier source).Nonempty →
          source ∈ selectedFineIndices := by
    intro source hsource
    rcases hsource with ⟨point, hpoint⟩
    rcases hPointData source point hpoint with
      ⟨cell, hcell, _hpointCell, hactive⟩
    change
      source ∈
        Finset.univ.filter fun candidate : Fin fine.card =>
          cover.parent candidate ∈ deletion.retainedParents
    rw [Finset.mem_filter]
    exact
      ⟨Finset.mem_univ _,
        by
          rw [deletion.retainedParents_eq]
          exact Finset.mem_biUnion.mpr
            ⟨cell, hcell, hactive⟩⟩
  have hSelectedSurjective :
      ∀ source ∈ selectedFineIndices,
        ∃ index : Fin selected.family.card,
          selected.embedding index = source := by
    intro source hsource
    let sourceSubtype : selectedFineIndices :=
      ⟨source, hsource⟩
    let index : Fin selected.family.card :=
      (selectedFineIndices.orderIsoOfFin rfl).symm sourceSubtype
    exact
      ⟨index,
        congrArg Subtype.val
          (selectedFineIndices.orderIsoOfFin rfl
            |>.apply_symm_apply sourceSubtype)⟩
  have hSelectedFineUnion :
      selectedFineShading.union = deletion.refined.union := by
    apply Set.Subset.antisymm
    · rintro point ⟨index, hpoint⟩
      exact ⟨selected.embedding index, hpoint⟩
    · rintro point ⟨source, hpoint⟩
      have hsource :
          source ∈ selectedFineIndices :=
        hSourceRetained source ⟨point, hpoint⟩
      rcases hSelectedSurjective source hsource with
        ⟨index, hindex⟩
      refine ⟨index, ?_⟩
      change point ∈
        deletion.refined.carrier (selected.embedding index)
      rw [hindex]
      exact hpoint
  have hSelectedFineMass :
      selectedFineShading.mass = deletion.refined.mass := by
    change
      (∑ index : Fin selected.family.card,
        volume
          (deletion.refined.carrier
            (selected.embedding index))) =
        ∑ source : Fin fine.card,
          volume (deletion.refined.carrier source)
    calc
      (∑ index : Fin selected.family.card,
          volume
            (deletion.refined.carrier
              (selected.embedding index))) =
          ∑ source ∈ selectedFineIndices,
            volume (deletion.refined.carrier source) := by
        let enumeration : Fin selectedFineIndices.card ≃ selectedFineIndices :=
          (selectedFineIndices.orderIsoOfFin rfl).toEquiv
        exact
          Fintype.sum_equiv enumeration
            (fun index : Fin selected.family.card =>
              volume
                (deletion.refined.carrier
                  (selected.embedding index)))
            (fun source : selectedFineIndices =>
              volume (deletion.refined.carrier source.1))
            (fun _ => rfl) |>.trans
              (Finset.sum_coe_sort selectedFineIndices
                (fun source =>
                  volume (deletion.refined.carrier source)))
      _ =
          ∑ source : Fin fine.card,
            volume (deletion.refined.carrier source) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro source _ hsource
        have hEmpty :
            deletion.refined.carrier source = ∅ := by
          apply Set.not_nonempty_iff_eq_empty.mp
          intro hnonempty
          exact hsource (hSourceRetained source hnonempty)
        rw [hEmpty]
        simp
  have hSelectedFineCubical :
      WZ1PaperIsCubicalShading selectedFineShading :=
    restrictPaperShading_cubical
      selected deletion.refined_cubical
  have hSelectedFineCellsDisjoint :
      ∀ first ∈ deletion.goodCells,
        ∀ second ∈ deletion.goodCells,
          first ≠ second →
            Disjoint
              (balancing.selectedFineCells first)
              (balancing.selectedFineCells second) := by
    intro first hfirst second hsecond hne
    rw [Finset.disjoint_left]
    intro fineCell hfirstFine hsecondFine
    let point : Point3 := cellCorner delta fineCell
    have hpointFine :
        point ∈ wz1PaperGridCube delta fineCell :=
      cellCorner_mem_gridCube hdelta fineCell
    have hpointFirst :
        point ∈ wz1PaperGridCube rho first :=
      balancing.fine_cell_containment
        first (deletion.goodCells_subset hfirst)
        fineCell hfirstFine hpointFine
    have hpointSecond :
        point ∈ wz1PaperGridCube rho second :=
      balancing.fine_cell_containment
        second (deletion.goodCells_subset hsecond)
        fineCell hsecondFine hpointFine
    exact
      Set.disjoint_left.mp
        (wz1PaperGridCube_disjoint hne)
        hpointFirst hpointSecond
  let exact :
      WZ2PaperExactCellBalancingData
        (rho := rho)
        selectedFineShading deletion.goodCells
        balancing.selectedFineCells :=
    { level := balancing.level
      retainedCoarseCells := deletion.goodCells
      retainedCoarseCells_subset := fun _ h => h
      retainedCoarseCells_nonempty := deletion.goodCells_nonempty
      selectedFineCells := balancing.selectedFineCells
      selectedFineCells_subset := by
        intro cell _ fineCell hfine
        exact hfine
      selectedFineCells_card := by
        intro cell hcell
        exact balancing.selectedFineCells_card
          cell (deletion.goodCells_subset hcell)
      availableFineCells_band := by
        intro cell hcell
        have hcard :=
          balancing.selectedFineCells_card
            cell (deletion.goodCells_subset hcell)
        rw [hcard]
        constructor
        · exact le_rfl
        · calc
            2 ^ balancing.level <
                2 * 2 ^ balancing.level := by
              have hpos : 0 < 2 ^ balancing.level :=
                Nat.pow_pos (by norm_num)
              omega
            _ = 2 ^ (balancing.level + 1) := by
              rw [pow_succ]
              ring
      retainedFineCells := deletion.retainedFineCells
      retainedFineCells_eq := deletion.retainedFineCells_eq
      retainedFineCells_count := by
        have hEq :
            (∑ cell ∈ deletion.goodCells,
                (balancing.selectedFineCells cell).card) =
              deletion.retainedFineCells.card := by
          rw [deletion.retainedFineCells_eq]
          symm
          exact Finset.card_biUnion hSelectedFineCellsDisjoint
        rw [hEq]
        exact Nat.le_mul_of_pos_left _ (by omega)
      refined := selectedFineShading
      refined_carrier_eq := by
        intro index
        change
          selectedFineShading.carrier index =
            selectedFineShading.carrier index ∩
              wz2RetainedCellsUnion
                delta deletion.retainedFineCells
        apply Set.Subset.antisymm
        · intro point hpoint
          refine ⟨hpoint, ?_⟩
          have hpoint' :
              point ∈
                deletion.refined.carrier
                  (selected.embedding index) :=
            hpoint
          rw [deletion.refined_eq] at hpoint'
          exact hpoint'.2
        · exact Set.inter_subset_left
      refined_subshading := fun _ => Set.Subset.rfl
      refined_cubical := hSelectedFineCubical
      refined_union_eq := by
        rw [hSelectedFineUnion]
        exact deletion.refined_union_eq
      cellMass := balancing.cellMass
      cellMass_eq := balancing.cellMass_eq
      cellMass_pos := balancing.cellMass_pos
      cellMass_ne_top := balancing.cellMass_ne_top
      fine_cell_mass := by
        intro cell hcell
        rw [hSelectedFineUnion]
        exact deletion.retained_cell_mass cell hcell
      fine_cell_containment := by
        intro cell hcell fineCell hfine
        exact balancing.fine_cell_containment
          cell (deletion.goodCells_subset hcell)
          fineCell hfine }
  have hRestrictedParent :
      ∀ index,
        coarseSub.embedding (restrictedCover.parent index) =
          cover.parent (selected.embedding index) :=
    cover.restrict_parent_spec deletion.retainedParents
      deletion.retainedParents_nonempty
  have hFullFiberComplete :
      ∀ parent : Fin coarseSub.family.card,
        Finset.image selected.embedding
            (wz2PaperFullFiberIndices
              selected.family coarseSub.family parent) =
          wz2PaperFullFiberIndices fine coarse
            (coarseSub.embedding parent) := by
    intro parent
    ext source
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨index, hindex, rfl⟩
      have hparent :
          restrictedCover.parent index = parent :=
        (restrictedCover.mem_fullFiber_iff_parent parent index).mp
          hindex
      exact
        (cover.mem_fullFiber_iff_parent
          (coarseSub.embedding parent)
          (selected.embedding index)).mpr
          (by
            rw [← hRestrictedParent index, hparent])
    · intro hsource
      have hparent :
          cover.parent source = coarseSub.embedding parent :=
        (cover.mem_fullFiber_iff_parent
          (coarseSub.embedding parent) source).mp hsource
      have hsourceSelected : source ∈ selectedFineIndices := by
        change
          source ∈
            Finset.univ.filter fun candidate : Fin fine.card =>
              cover.parent candidate ∈ deletion.retainedParents
        rw [Finset.mem_filter]
        exact
          ⟨Finset.mem_univ _, by
            rw [hparent]
            exact Finset.orderEmbOfFin_mem
              deletion.retainedParents rfl parent⟩
      rcases hSelectedSurjective source hsourceSelected with
        ⟨index, hindex⟩
      have hrestrictedParent :
          restrictedCover.parent index = parent := by
        apply coarseSub.embedding.injective
        rw [hRestrictedParent index, hindex, hparent]
      exact
        ⟨index,
          (restrictedCover.mem_fullFiber_iff_parent
            parent index).mpr hrestrictedParent,
          hindex⟩
  let parentCells :
      Fin coarseSub.family.card → Finset WZ2PaperCellIndex :=
    fun parent =>
      deletion.goodCells.filter fun cell =>
        coarseSub.embedding parent ∈ active.activeParents cell
  let selectedCoarseShading : WZ1PaperTubeShading coarseSub.family :=
    { carrier := fun parent =>
        ⋃ cell ∈ parentCells parent,
          wz1PaperGridCube rho cell
      measurable_carrier := by
        intro parent
        apply MeasurableSet.iUnion
        intro cell
        apply MeasurableSet.iUnion
        intro _
        exact wz1PaperGridCube_measurable cell
      subset_body := by
        intro parent point hpoint
        rcases Set.mem_iUnion₂.mp hpoint with
          ⟨cell, hcell, hpointCell⟩
        have hactive :
            coarseSub.embedding parent ∈
              active.activeParents cell :=
          (Finset.mem_filter.mp hcell).2
        rw [active.activeParents_eq] at hactive
        have hparentCell :
            cell ∈
              coarseData.parentCells (coarseSub.embedding parent) :=
          (Finset.mem_filter.mp hactive).2
        have hcarrier :
            wz1PaperGridCube rho cell ⊆
              coarseData.coarseShading.carrier
                (coarseSub.embedding parent) := by
          rw [coarseData.coarseShading_carrier_eq]
          exact Set.subset_iUnion₂_of_subset
            cell hparentCell Set.Subset.rfl
        have hbody :=
          coarseData.coarseShading.subset_body
            (coarseSub.embedding parent)
            (hcarrier hpointCell)
        change point ∈
          wz1PaperTubeCarrier (coarseSub.family.tube parent)
        rw [coarseSub.tube_eq parent]
        exact hbody }
  have hPointCompatibility :
      ∀ index point,
        point ∈ selectedFineShading.carrier index →
          point ∈
            selectedCoarseShading.carrier
              (restrictedCover.parent index) := by
    intro index point hpoint
    have hpointAmbient :
        point ∈
          deletion.refined.carrier (selected.embedding index) :=
      hpoint
    rcases hPointData
        (selected.embedding index) point hpointAmbient with
      ⟨cell, hcell, hpointCell, hactive⟩
    have hparent :
        coarseSub.embedding (restrictedCover.parent index) =
          cover.parent (selected.embedding index) :=
      hRestrictedParent index
    have hcellParent :
        cell ∈ parentCells (restrictedCover.parent index) := by
      rw [Finset.mem_filter]
      exact ⟨hcell, by simpa [hparent] using hactive⟩
    exact Set.mem_iUnion₂.mpr
      ⟨cell, hcellParent, hpointCell⟩
  have hCoarseCubical :
      WZ1PaperIsCubicalShading selectedCoarseShading := by
    intro parent point hpoint other hother
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨cell, hcell, hpointCell⟩
    have hindex :
        wz1PaperGridIndex rho point = cell :=
      (mem_wz1PaperGridCube rho cell point).mp hpointCell
    exact Set.mem_iUnion₂.mpr
      ⟨cell, hcell, by simpa [hindex] using hother⟩
  have hCoarseUnion :
      selectedCoarseShading.union =
        ⋃ cell ∈ deletion.goodCells,
          wz1PaperGridCube rho cell := by
    ext point
    constructor
    · rintro ⟨parent, hpoint⟩
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨cell, hcell, hpointCell⟩
      exact Set.mem_iUnion₂.mpr
        ⟨cell, (Finset.mem_filter.mp hcell).1, hpointCell⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨cell, hcell, hpointCell⟩
      have hcellAmbient :
          cell ∈ balancing.retainedCoarseCells :=
        deletion.goodCells_subset hcell
      rcases active.activeParents_nonempty cell hcellAmbient with
        ⟨ambientParent, hactive⟩
      have hparentRetained :
          ambientParent ∈ deletion.retainedParents := by
        rw [deletion.retainedParents_eq]
        exact Finset.mem_biUnion.mpr
          ⟨cell, hcell, hactive⟩
      let ambientSubtype : deletion.retainedParents :=
        ⟨ambientParent, hparentRetained⟩
      let parent : Fin coarseSub.family.card :=
        (deletion.retainedParents.orderIsoOfFin rfl).symm
          ambientSubtype
      have hparentEmbedding :
          coarseSub.embedding parent = ambientParent :=
        congrArg Subtype.val
          (deletion.retainedParents.orderIsoOfFin rfl
            |>.apply_symm_apply ambientSubtype)
      have hcellParent : cell ∈ parentCells parent := by
        rw [Finset.mem_filter]
        exact ⟨hcell, by simpa [hparentEmbedding] using hactive⟩
      exact
        ⟨parent, Set.mem_iUnion₂.mpr
          ⟨cell, hcellParent, hpointCell⟩⟩
  let balanced :
      WZ1PaperBalancedCoverData
        restrictedCover.toWZ1PaperTubeCover
        selectedFineShading selectedCoarseShading :=
    { point_compatibility := hPointCompatibility
      coarse_cubical := hCoarseCubical
      activeCells := deletion.goodCells
      coarse_union_eq := hCoarseUnion
      cellMass := balancing.cellMass
      cellMass_pos := balancing.cellMass_pos
      cellMass_ne_top := balancing.cellMass_ne_top
      fine_cell_mass := by
        intro cell hcell
        rw [hSelectedFineUnion]
        exact deletion.retained_cell_mass cell hcell }
  let finalCoarseData :
      WZ2PaperCoarseShadingData
        restrictedCover selectedFineShading deletion.goodCells
        balancing.selectedFineCells exact :=
    { parentCells := parentCells
      parentCells_subset := by
        intro parent cell hcell
        exact (Finset.mem_filter.mp hcell).1
      parentCells_witness := by
        intro parent cell hcell
        have hactive :
            coarseSub.embedding parent ∈
              active.activeParents cell :=
          (Finset.mem_filter.mp hcell).2
        have hcellAmbient :
            cell ∈ balancing.retainedCoarseCells :=
          deletion.goodCells_subset
            (Finset.mem_filter.mp hcell).1
        rw [active.activeParents_eq] at hactive
        have hparentCell :
            cell ∈
              coarseData.parentCells (coarseSub.embedding parent) :=
          (Finset.mem_filter.mp hactive).2
        rcases
            coarseData.parentCells_witness
              (coarseSub.embedding parent) cell hparentCell
          with ⟨ambientSource, point, hparent, hpointBalanced,
            hpointCell⟩
        have hsourceSelected : ambientSource ∈ selectedFineIndices := by
          change
            ambientSource ∈
              Finset.univ.filter fun candidate : Fin fine.card =>
                cover.parent candidate ∈ deletion.retainedParents
          rw [Finset.mem_filter]
          exact
            ⟨Finset.mem_univ _, by
              rw [hparent]
              exact Finset.orderEmbOfFin_mem
                deletion.retainedParents rfl parent⟩
        rcases hSelectedSurjective ambientSource hsourceSelected with
          ⟨source, hsource⟩
        have hpointDeletion :
            point ∈ deletion.refined.carrier ambientSource := by
          rw [deletion.refined_eq]
          refine ⟨hpointBalanced, ?_⟩
          rw [deletion.retainedFineCells_eq]
          have hpointUnion :
              point ∈
                wz2RetainedCellsUnion
                  delta
                  (deletion.goodCells.biUnion
                    balancing.selectedFineCells) := by
            rw [show
              wz2RetainedCellsUnion delta
                  (deletion.goodCells.biUnion
                    balancing.selectedFineCells) =
                ⋃ fineCell ∈
                    deletion.goodCells.biUnion
                      balancing.selectedFineCells,
                  wz1PaperGridCube delta fineCell by rfl]
            have hpointRefined : point ∈ balancing.refined.union :=
              ⟨ambientSource, hpointBalanced⟩
            rw [balancing.refined_union_eq] at hpointRefined
            rcases Set.mem_iUnion₂.mp hpointRefined with
              ⟨fineCell, hfineRetained, hpointFine⟩
            rw [balancing.retainedFineCells_eq] at hfineRetained
            rcases Finset.mem_biUnion.mp hfineRetained with
              ⟨ambientCell, hambientCell, hfineCell⟩
            have hambientPoint :
                point ∈ wz1PaperGridCube rho ambientCell :=
              balancing.fine_cell_containment
                ambientCell hambientCell fineCell hfineCell hpointFine
            have hambientEq : ambientCell = cell := by
              have hfirst :
                  wz1PaperGridIndex rho point = ambientCell :=
                (mem_wz1PaperGridCube rho ambientCell point).mp
                  hambientPoint
              have hsecond :
                  wz1PaperGridIndex rho point = cell :=
                (mem_wz1PaperGridCube rho cell point).mp hpointCell
              exact hfirst.symm.trans hsecond
            exact Set.mem_iUnion₂.mpr
              ⟨fineCell,
                Finset.mem_biUnion.mpr
                  ⟨cell,
                    (Finset.mem_filter.mp hcell).1,
                    by simpa [hambientEq] using hfineCell⟩,
                hpointFine⟩
          exact hpointUnion
        have hpointSelected :
            point ∈ selectedFineShading.carrier source := by
          change
            point ∈
              deletion.refined.carrier (selected.embedding source)
          rw [hsource]
          exact hpointDeletion
        have hparentRestricted :
            restrictedCover.parent source = parent := by
          apply coarseSub.embedding.injective
          rw [hRestrictedParent source, hsource, hparent]
        exact
          ⟨source, point, hparentRestricted,
            hpointSelected, hpointCell⟩
      retained_cell_owned := by
        intro cell hcell
        rcases active.activeParents_nonempty
            cell (deletion.goodCells_subset hcell) with
          ⟨ambientParent, hactive⟩
        have hparentRetained :
            ambientParent ∈ deletion.retainedParents := by
          rw [deletion.retainedParents_eq]
          exact Finset.mem_biUnion.mpr
            ⟨cell, hcell, hactive⟩
        let ambientSubtype : deletion.retainedParents :=
          ⟨ambientParent, hparentRetained⟩
        let parent : Fin coarseSub.family.card :=
          (deletion.retainedParents.orderIsoOfFin rfl).symm
            ambientSubtype
        have hparentEmbedding :
            coarseSub.embedding parent = ambientParent :=
          congrArg Subtype.val
            (deletion.retainedParents.orderIsoOfFin rfl
              |>.apply_symm_apply ambientSubtype)
        exact
          ⟨parent,
            Finset.mem_filter.mpr
              ⟨hcell, by simpa [hparentEmbedding] using hactive⟩⟩
      coarseShading := selectedCoarseShading
      coarseShading_carrier_eq := fun _ => rfl
      balancedCover := balanced }
  have hParentFiberMassFloor :
      ∀ parent : Fin coarseSub.family.card,
        threshold *
            referenceFiberMass
              (coarseSub.embedding parent) ≤
          (restrictPaperShading
            (restrictedCover.fullFiberSubfamily parent)
            selectedFineShading).mass := by
    intro parent
    have hambientFloor :=
      deletion.parent_fiber_mass_floor
        (coarseSub.embedding parent)
        (Finset.orderEmbOfFin_mem
          deletion.retainedParents rfl parent)
    let finalFiber :=
      wz2PaperFullFiberIndices
        selected.family coarseSub.family parent
    let ambientFiber :=
      wz2PaperFullFiberIndices fine coarse
        (coarseSub.embedding parent)
    have hcomplete :
        Finset.image selected.embedding finalFiber = ambientFiber :=
      hFullFiberComplete parent
    have hMassEq :
        (restrictPaperShading
          (restrictedCover.fullFiberSubfamily parent)
          selectedFineShading).mass =
        (restrictPaperShading
          (cover.fullFiberSubfamily
            (coarseSub.embedding parent))
          deletion.refined).mass := by
      rw [restrictedCover.fullFiberShading_mass
        selectedFineShading parent]
      rw [cover.fullFiberShading_mass
        deletion.refined (coarseSub.embedding parent)]
      have hsum :
          ∑ source ∈ ambientFiber,
              volume (deletion.refined.carrier source) =
            ∑ source ∈ finalFiber,
              volume
                (deletion.refined.carrier
                  (selected.embedding source)) := by
        rw [← hcomplete]
        exact Finset.sum_image
          (Set.injOn_of_injective selected.embedding.injective)
      change
        (∑ source ∈ finalFiber,
          volume
            (deletion.refined.carrier
              (selected.embedding source))) =
          ∑ source ∈ ambientFiber,
            volume (deletion.refined.carrier source)
      exact hsum.symm
    exact hambientFloor.trans_eq hMassEq.symm
  exact
    ⟨{
      selectedFineIndices := selectedFineIndices
      selectedFineIndices_eq := rfl
      source_parent_retained := by
        intro source hsource
        have hmem := hSourceRetained source hsource
        exact (Finset.mem_filter.mp hmem).2
      selected := selected
      selected_eq := rfl
      selectedFineShading := selectedFineShading
      selectedFineShading_eq := rfl
      selectedFine_subshading := by
        intro index
        exact
          (deletion.refined_subshading
            (selected.embedding index))
      selectedFine_cubical :=
        restrictPaperShading_cubical
          selected deletion.refined_cubical
      selectedFine_union_eq := hSelectedFineUnion
      selectedFine_mass_eq := hSelectedFineMass
      restrictedCover := restrictedCover
      restricted_parent_spec := hRestrictedParent
      full_fiber_complete := hFullFiberComplete
      parentCells := parentCells
      parentCells_eq := fun _ => rfl
      selectedCoarseShading := selectedCoarseShading
      selectedCoarseShading_carrier_eq := fun _ => rfl
      selectedCoarseShading_union_eq := hCoarseUnion
      exact := exact
      exact_refined_eq := rfl
      coarseData := finalCoarseData
      coarseData_coarseShading_eq := rfl
      balanced := balanced
      parent_fiber_mass_floor := hParentFiberMassFloor
    }⟩

end Kakeya.Assouad

end
