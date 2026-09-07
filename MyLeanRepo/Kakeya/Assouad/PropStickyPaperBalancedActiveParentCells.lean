import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedActiveParentCellsStatements

/-! # Active parent fibers in balanced cells -/

noncomputable section

namespace Kakeya.Assouad

open Finset MeasureTheory Set

attribute [local instance] Classical.propDecidable

theorem wz2_paper_balanced_active_parent_cells :
    WZ2PaperBalancedActiveParentCellsStatement := by
  intro delta rho hdelta hrho fine coarse cover sourceShading
    coarseCells availableFineCells balancing coarseData
  let activeParents : WZ2PaperCellIndex → Finset (Fin coarse.card) :=
    fun cell => Finset.univ.filter fun parent =>
      cell ∈ coarseData.parentCells parent
  have hactiveParents_eq :
      ∀ cell, activeParents cell =
        Finset.univ.filter fun parent =>
          cell ∈ coarseData.parentCells parent := by
    intro cell; rfl
  have hactiveParents_nonempty :
      ∀ cell ∈ balancing.retainedCoarseCells,
        (activeParents cell).Nonempty := by
    intro cell hcell
    have h : ∃ parent, cell ∈ coarseData.parentCells parent :=
      coarseData.retained_cell_owned cell hcell
    rcases h with ⟨parent, hparent⟩
    have hmem : parent ∈ activeParents cell := by
      rw [hactiveParents_eq cell]
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ parent, hparent⟩
    exact ⟨parent, hmem⟩
  have hcube_nonempty : ∀ (cell : WZ2PaperCellIndex),
      (wz1PaperGridCube rho cell).Nonempty := by
    intro cell
    have hvol : 0 < volume (wz1PaperGridCube rho cell) :=
      wz1PaperGridCube_volume_pos hrho cell
    by_contra h
    have h' : wz1PaperGridCube rho cell = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using h
    rw [h'] at hvol
    simp at hvol
  let representative : WZ2PaperCellIndex → Point3 :=
    fun cell => Classical.choose (hcube_nonempty cell)
  have hrepresentative_mem :
      ∀ cell, representative cell ∈ wz1PaperGridCube rho cell := by
    intro cell
    exact Classical.choose_spec (hcube_nonempty cell)
  have hactiveParents_card_eq :
      ∀ cell ∈ balancing.retainedCoarseCells,
        (activeParents cell).card =
          coarseData.coarseShading.pointMultiplicity
            (representative cell) := by
    intro cell hcell
    let point := representative cell
    have hpointCell : point ∈ wz1PaperGridCube rho cell :=
      hrepresentative_mem cell
    have h_iff : ∀ (parent : Fin coarse.card),
        parent ∈ activeParents cell ↔
          point ∈ coarseData.coarseShading.carrier parent := by
      intro parent
      constructor
      · intro hparent
        have hmem : cell ∈ coarseData.parentCells parent := by
          rw [hactiveParents_eq cell] at hparent
          exact (Finset.mem_filter.mp hparent).2
        have h : point ∈ coarseData.coarseShading.carrier parent := by
          rw [coarseData.coarseShading_carrier_eq parent]
          have h_biunion :
              ∃ (c : WZ2PaperCellIndex),
                c ∈ coarseData.parentCells parent ∧
                  point ∈ wz1PaperGridCube rho c :=
            ⟨cell, hmem, hpointCell⟩
          simpa [Set.mem_biUnion] using h_biunion
        exact h
      · intro hpoint
        rw [coarseData.coarseShading_carrier_eq parent] at hpoint
        have h_exists :
            ∃ (otherCell : WZ2PaperCellIndex),
              otherCell ∈ coarseData.parentCells parent ∧
                point ∈ wz1PaperGridCube rho otherCell := by
          simpa [Set.mem_biUnion] using hpoint
        rcases h_exists with ⟨otherCell, hotherCell, hpointOtherCube⟩
        have hindex1 : wz1PaperGridIndex rho point = otherCell :=
          (mem_wz1PaperGridCube rho otherCell point).mp
            hpointOtherCube
        have hindex2 : wz1PaperGridIndex rho point = cell :=
          (mem_wz1PaperGridCube rho cell point).mp hpointCell
        have heq : otherCell = cell := hindex1.symm.trans hindex2
        rw [heq] at hotherCell
        rw [hactiveParents_eq cell]
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ parent, hotherCell⟩
    have hset_eq : activeParents cell =
        Finset.univ.filter fun parent =>
          point ∈ coarseData.coarseShading.carrier parent := by
      ext x
      constructor
      · intro h
        have h' : point ∈ coarseData.coarseShading.carrier x :=
          (h_iff x).mp h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, h'⟩
      · intro h
        have h' : point ∈ coarseData.coarseShading.carrier x :=
          (Finset.mem_filter.mp h).2
        exact (h_iff x).mpr h'
    rw [hset_eq]
    rfl
  let shading := balancing.refined
  have h_parentCellMass_eq :
      ∀ (cell : WZ2PaperCellIndex) (parent : Fin coarse.card),
        wz2PaperParentCellMass cover shading (cell, parent) =
          ∑ source ∈ cover.fiberIndices parent,
            volume
              (shading.carrier source ∩
                wz1PaperGridCube rho cell) := by
    intro cell parent
    dsimp only [wz2PaperParentCellMass, restrictPaperShading]
    let indices := wz2PaperFullFiberIndices fine coarse parent
    let equivalence : Fin indices.card ≃ indices :=
      (indices.orderIsoOfFin rfl).toEquiv
    calc
      ∑ index : Fin (cover.fullFiberSubfamily parent).family.card,
          volume
            (shading.carrier
                ((cover.fullFiberSubfamily parent).embedding index) ∩
              wz1PaperGridCube rho cell)
        = ∑ source : indices,
            volume
              (shading.carrier source.val ∩
                wz1PaperGridCube rho cell) := by
          exact Fintype.sum_equiv equivalence
            (fun index =>
              volume
                (shading.carrier
                    ((cover.fullFiberSubfamily parent).embedding index) ∩
                  wz1PaperGridCube rho cell))
            (fun source =>
              volume
                (shading.carrier source.val ∩
                  wz1PaperGridCube rho cell))
            (fun _ => rfl)
      _ = ∑ source ∈ indices,
          volume
            (shading.carrier source ∩
              wz1PaperGridCube rho cell) := by
          exact Finset.sum_coe_sort indices fun source =>
            volume
              (shading.carrier source ∩
                wz1PaperGridCube rho cell)
      _ = ∑ source ∈ cover.fiberIndices parent,
          volume
            (shading.carrier source ∩
              wz1PaperGridCube rho cell) := by
          exact Finset.sum_congr
            (cover.fullFiberIndices_eq parent) (fun _ _ => rfl)
  have h_inactive_zero :
      ∀ (cell : WZ2PaperCellIndex) (parent : Fin coarse.card),
        parent ∉ activeParents cell →
          wz2PaperParentCellMass cover shading (cell, parent) = 0 := by
    intro cell parent hnotactive
    have h_cell_not_in : cell ∉ coarseData.parentCells parent := by
      have h : activeParents cell =
          Finset.univ.filter
            (fun p => cell ∈ coarseData.parentCells p) :=
        hactiveParents_eq cell
      rw [h] at hnotactive
      simpa using hnotactive
    have h_each : ∀ source ∈ cover.fiberIndices parent,
        volume
            (shading.carrier source ∩
              wz1PaperGridCube rho cell) = 0 := by
      intro source hsource
      have h_parent : cover.parent source = parent := by
        simpa [WZ1PaperTubeCover.fiberIndices,
          Finset.mem_filter, Finset.mem_univ] using hsource
      have h_subset : shading.carrier source ⊆
          coarseData.coarseShading.carrier parent := by
        have h2 : shading.carrier source ⊆
            coarseData.coarseShading.carrier (cover.parent source) :=
          coarseData.balancedCover.point_compatibility source
        rw [h_parent] at h2
        exact h2
      have h_disjoint :
          Disjoint (coarseData.coarseShading.carrier parent)
            (wz1PaperGridCube rho cell) := by
        rw [coarseData.coarseShading_carrier_eq parent]
        rw [Set.disjoint_left]
        intro x hx1 hx2
        have h_exists :
            ∃ (c : WZ2PaperCellIndex),
              c ∈ coarseData.parentCells parent ∧
                x ∈ wz1PaperGridCube rho c := by
          simpa [Set.mem_biUnion] using hx1
        rcases h_exists with ⟨c, hc, hxc⟩
        have hne : c ≠ cell := by
          intro h
          rw [h] at hc
          exact h_cell_not_in hc
        have h_disj :
            Disjoint (wz1PaperGridCube rho c)
              (wz1PaperGridCube rho cell) :=
          wz1PaperGridCube_disjoint hne
        rw [Set.disjoint_left] at h_disj
        exact h_disj hxc hx2
      have h_disjoint2 :
          Disjoint (shading.carrier source)
            (wz1PaperGridCube rho cell) :=
        h_disjoint.mono_left h_subset
      have h_empty :
          shading.carrier source ∩ wz1PaperGridCube rho cell = ∅ :=
        Set.disjoint_iff_inter_eq_empty.mp h_disjoint2
      rw [h_empty]
      simp
    rw [h_parentCellMass_eq cell parent]
    rw [Finset.sum_congr rfl h_each]
    simp
  have h_sum_identity :
      ∀ cell ∈ balancing.retainedCoarseCells,
        (∑ parent ∈ activeParents cell,
            wz2PaperParentCellMass cover shading (cell, parent)) =
          wz2PaperCellIncidenceMass (rho := rho) shading cell := by
    intro cell hcell
    have h_all_parents :
        (∑ parent : Fin coarse.card,
            wz2PaperParentCellMass cover shading (cell, parent)) =
          wz2PaperCellIncidenceMass (rho := rho) shading cell := by
      have h1 : ∀ parent,
          wz2PaperParentCellMass cover shading (cell, parent) =
            ∑ source ∈ cover.fiberIndices parent,
              volume
                (shading.carrier source ∩
                  wz1PaperGridCube rho cell) :=
        fun parent => h_parentCellMass_eq cell parent
      simp_rw [h1]
      have h_fiber_eq : ∀ parent : Fin coarse.card,
          cover.fiberIndices parent =
            Finset.univ.filter
              (fun source => cover.parent source = parent) := by
        intro parent
        ext source
        simp [WZ1PaperTubeCover.fiberIndices,
          Finset.mem_filter, Finset.mem_univ]
      simp_rw [h_fiber_eq]
      rw [Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ) (t := Finset.univ)
        (g := cover.parent)
        (fun _ _ => Finset.mem_univ _)]
      rfl
    have h_sum_active :
        (∑ parent ∈ activeParents cell,
            wz2PaperParentCellMass cover shading (cell, parent)) =
          ∑ parent : Fin coarse.card,
            wz2PaperParentCellMass cover shading (cell, parent) := by
      rw [Finset.sum_subset
        (Finset.subset_univ (activeParents cell))]
      intro parent _ hnot
      exact h_inactive_zero cell parent hnot
    rw [h_sum_active, h_all_parents]
  have h_cell_mass_le :
      ∀ cell ∈ balancing.retainedCoarseCells,
        balancing.cellMass ≤
          ∑ parent ∈ activeParents cell,
            wz2PaperParentCellMass cover shading (cell, parent) := by
    intro cell hcell
    have h1 : balancing.cellMass =
        volume
          (balancing.refined.union ∩
            wz1PaperGridCube rho cell) :=
      (balancing.fine_cell_mass cell hcell).symm
    rw [h1]
    let A : Fin fine.card → Set Point3 :=
      fun source =>
        balancing.refined.carrier source ∩
          wz1PaperGridCube rho cell
    have h2 :
        balancing.refined.union ∩ wz1PaperGridCube rho cell =
          ⋃ source ∈ Finset.univ, A source := by
      ext x
      constructor
      · rintro ⟨hunion, hcube⟩
        rcases hunion with ⟨source, hcarrier⟩
        have h_biunion :
            ∃ (s : Fin fine.card), s ∈ Finset.univ ∧ x ∈ A s :=
          ⟨source, Finset.mem_univ source, ⟨hcarrier, hcube⟩⟩
        simpa [Set.mem_biUnion] using h_biunion
      · intro h
        have h_exists :
            ∃ (source : Fin fine.card),
              source ∈ Finset.univ ∧ x ∈ A source := by
          simpa [Set.mem_biUnion] using h
        rcases h_exists with ⟨source, _, ⟨hcarrier, hcube⟩⟩
        exact ⟨⟨source, hcarrier⟩, hcube⟩
    rw [h2]
    have h3 :
        volume (⋃ source ∈ Finset.univ, A source) ≤
          ∑ source ∈ Finset.univ, volume (A source) :=
      MeasureTheory.measure_biUnion_finset_le Finset.univ A
    have h4 :
        (∑ source ∈ Finset.univ, volume (A source)) =
          wz2PaperCellIncidenceMass
            (rho := rho) balancing.refined cell := by
      dsimp only [wz2PaperCellIncidenceMass, A]
    rw [h4] at h3
    have h5 :
        wz2PaperCellIncidenceMass
            (rho := rho) balancing.refined cell ≤
          ∑ parent ∈ activeParents cell,
            wz2PaperParentCellMass cover shading (cell, parent) := by
      exact (h_sum_identity cell hcell).symm ▸ le_refl _
    exact h3.trans h5
  let fiberCellMass : ENNReal :=
    volume (wz1PaperGridCube delta (0, 0, 0))
  have hfiberCellMass_pos : 0 < fiberCellMass :=
    wz1PaperGridCube_volume_pos hdelta (0, 0, 0)
  have hfiberCellMass_ne_top : fiberCellMass ≠ ⊤ :=
    wz1PaperGridCube_volume_ne_top hdelta (0, 0, 0)
  have h_fiber_cell_mass_lower :
      ∀ cell ∈ balancing.retainedCoarseCells,
        ∀ parent ∈ activeParents cell,
          fiberCellMass ≤
            volume
              ((restrictPaperShading
                  (cover.fullFiberSubfamily parent)
                  balancing.refined).union ∩
                wz1PaperGridCube rho cell) := by
    intro cell hcell parent hparent
    have hmem : cell ∈ coarseData.parentCells parent := by
      rw [hactiveParents_eq cell] at hparent
      exact (Finset.mem_filter.mp hparent).2
    rcases coarseData.parentCells_witness parent cell hmem with
      ⟨source, point, hparent_eq, hpoint_carrier, hpoint_cube⟩
    have hpoint_union : point ∈ balancing.refined.union :=
      ⟨source, hpoint_carrier⟩
    rw [balancing.refined_union_eq] at hpoint_union
    have h_exists :
        ∃ (fineCell : WZ2PaperCellIndex),
          fineCell ∈ balancing.retainedFineCells ∧
            point ∈ wz1PaperGridCube delta fineCell := by
      simpa [Set.mem_biUnion] using hpoint_union
    rcases h_exists with
      ⟨fineCell, hfineRetained, hpointFineCube⟩
    have hfineIndex : wz1PaperGridIndex delta point = fineCell :=
      (mem_wz1PaperGridCube delta fineCell point).mp hpointFineCube
    have hcube_in_carrier :
        wz1PaperGridCube delta fineCell ⊆
          balancing.refined.carrier source := by
      have h :
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            balancing.refined.carrier source :=
        balancing.refined_cubical source point hpoint_carrier
      rw [hfineIndex] at h
      exact h
    have hfineInBiUnion :
        fineCell ∈ balancing.retainedFineCells := hfineRetained
    rw [balancing.retainedFineCells_eq] at hfineInBiUnion
    simp only [Finset.mem_biUnion] at hfineInBiUnion
    rcases hfineInBiUnion with
      ⟨coarseCell, hcoarseRetained, hselected⟩
    have hcontainment :
        wz1PaperGridCube delta fineCell ⊆
          wz1PaperGridCube rho coarseCell :=
      balancing.fine_cell_containment
        coarseCell hcoarseRetained fineCell hselected
    have hpointInCoarse :
        point ∈ wz1PaperGridCube rho coarseCell :=
      hcontainment hpointFineCube
    have hcoarseEq : coarseCell = cell := by
      have hi : wz1PaperGridIndex rho point = coarseCell :=
        (mem_wz1PaperGridCube rho coarseCell point).mp hpointInCoarse
      have hj : wz1PaperGridIndex rho point = cell :=
        (mem_wz1PaperGridCube rho cell point).mp hpoint_cube
      exact hi.symm.trans hj
    have hcube_in_rho :
        wz1PaperGridCube delta fineCell ⊆
          wz1PaperGridCube rho cell := by
      rw [← hcoarseEq]
      exact hcontainment
    have hsource_in_fiber : source ∈ cover.fiberIndices parent := by
      simp [WZ1PaperTubeCover.fiberIndices, Finset.mem_filter,
        Finset.mem_univ, hparent_eq]
    let fiberSubfamily := cover.fullFiberSubfamily parent
    have hsource_in_fiber' :
        source ∈ wz2PaperFullFiberIndices fine coarse parent := by
      have h_eq :
          wz2PaperFullFiberIndices fine coarse parent =
            cover.fiberIndices parent :=
        cover.fullFiberIndices_eq parent
      rw [h_eq]
      exact hsource_in_fiber
    let indices := wz2PaperFullFiberIndices fine coarse parent
    let enumeration := indices.orderIsoOfFin rfl
    let i : Fin fiberSubfamily.family.card :=
      enumeration.symm ⟨source, hsource_in_fiber'⟩
    have hembed : fiberSubfamily.embedding i = source :=
      congrArg Subtype.val
        (enumeration.apply_symm_apply ⟨source, hsource_in_fiber'⟩)
    have hcube_in_restricted_carrier :
        wz1PaperGridCube delta fineCell ⊆
          (restrictPaperShading
            fiberSubfamily balancing.refined).carrier i := by
      simpa [restrictPaperShading, hembed] using hcube_in_carrier
    have hcube_in_restricted_union :
        wz1PaperGridCube delta fineCell ⊆
          (restrictPaperShading
            fiberSubfamily balancing.refined).union := by
      intro x hx
      exact ⟨i, hcube_in_restricted_carrier hx⟩
    have hcube_in_intersection :
        wz1PaperGridCube delta fineCell ⊆
          (restrictPaperShading
              fiberSubfamily balancing.refined).union ∩
            wz1PaperGridCube rho cell := by
      intro x hx
      exact ⟨hcube_in_restricted_union hx, hcube_in_rho hx⟩
    have hvol :
        volume (wz1PaperGridCube delta fineCell) ≤
          volume
            ((restrictPaperShading
                fiberSubfamily balancing.refined).union ∩
              wz1PaperGridCube rho cell) :=
      measure_mono hcube_in_intersection
    have hvol_eq :
        volume (wz1PaperGridCube delta fineCell) =
          volume (wz1PaperGridCube delta (0, 0, 0)) :=
      wz1PaperGridCube_volume_eq hdelta fineCell (0, 0, 0)
    rw [hvol_eq] at hvol
    exact hvol
  exact ⟨{
    activeParents := activeParents,
    activeParents_eq := hactiveParents_eq,
    activeParents_nonempty := hactiveParents_nonempty,
    representative := representative,
    representative_mem := hrepresentative_mem,
    activeParents_card_eq := hactiveParents_card_eq,
    sum_parent_mass_eq_cell_incidence := h_sum_identity,
    cell_mass_le_sum_parent := h_cell_mass_le,
    fiberCellMass := fiberCellMass,
    fiberCellMass_eq := rfl,
    fiberCellMass_pos := hfiberCellMass_pos,
    fiberCellMass_ne_top := hfiberCellMass_ne_top,
    fiber_cell_mass_lower := h_fiber_cell_mass_lower,
  }⟩

end Kakeya.Assouad

end
