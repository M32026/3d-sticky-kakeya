import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantParentFineCellsStatements

/-! # Whole fine cells occupied by each dominant complete parent fiber -/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

private lemma cubical_cube_subset_union
    {scale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily scale}
    {shading : WZ1PaperTubeShading family}
    (cubical : WZ1PaperIsCubicalShading shading)
    {cell : WZ2PaperCellIndex}
    (nonempty :
      (shading.union ∩ wz1PaperGridCube scale cell).Nonempty) :
    wz1PaperGridCube scale cell ⊆ shading.union := by
  rcases nonempty with
    ⟨point, point_union, point_cell⟩
  rcases point_union with ⟨index, point_carrier⟩
  have index_eq :
      wz1PaperGridIndex scale point = cell :=
    (mem_wz1PaperGridCube scale cell point).mp point_cell
  have cube_subset :
      wz1PaperGridCube scale
          (wz1PaperGridIndex scale point) ⊆
        shading.carrier index :=
    cubical index point point_carrier
  rw [index_eq] at cube_subset
  intro other other_cell
  exact ⟨index, cube_subset other_cell⟩

private lemma point_in_refined_union_and_rho_cell_implies_selected_fine
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    (balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells availableFineCells)
    {cell : WZ2PaperCellIndex}
    (_cell_mem : cell ∈ balancing.retainedCoarseCells)
    {point : Point3}
    (point_refined : point ∈ balancing.refined.union)
    (point_rho : point ∈ wz1PaperGridCube rho cell) :
    ∃ fineCell ∈ balancing.selectedFineCells cell,
      point ∈ wz1PaperGridCube delta fineCell := by
  rw [balancing.refined_union_eq] at point_refined
  have exists_fine :
      ∃ fineCell ∈ balancing.retainedFineCells,
        point ∈ wz1PaperGridCube delta fineCell := by
    simpa [Set.mem_iUnion] using point_refined
  rcases exists_fine with
    ⟨fineCell, fine_retained, point_fine⟩
  rw [balancing.retainedFineCells_eq] at fine_retained
  rcases Finset.mem_biUnion.mp fine_retained with
    ⟨coarseCell, coarse_retained, fine_selected⟩
  have containment :
      wz1PaperGridCube delta fineCell ⊆
        wz1PaperGridCube rho coarseCell :=
    balancing.fine_cell_containment
      coarseCell coarse_retained fineCell fine_selected
  have point_coarse :
      point ∈ wz1PaperGridCube rho coarseCell :=
    containment point_fine
  have coarse_eq : coarseCell = cell := by
    by_contra not_eq
    have disjoint :
        Disjoint
          (wz1PaperGridCube rho coarseCell)
          (wz1PaperGridCube rho cell) :=
      wz1PaperGridCube_disjoint not_eq
    exact Set.disjoint_left.mp disjoint point_coarse point_rho
  rw [coarse_eq] at fine_selected
  exact ⟨fineCell, fine_selected, point_fine⟩

theorem wz2_paper_dominant_parent_fine_cells :
    WZ2PaperDominantParentFineCellsStatement := by
  intro delta rho hdelta hrho fine coarse cover sourceShading coarseCells
    availableFineCells balancing coarseData active multiplicityLevel
    multiplicityUpper degree dominant

  let ownedFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex :=
    fun cell =>
      Finset.filter (fun fineCell =>
        (wz1PaperGridCube delta fineCell ∩
          (restrictPaperShading
            (cover.fullFiberSubfamily
              (dominant.dominantParent cell))
            balancing.refined).union).Nonempty)
        (balancing.selectedFineCells cell)

  have owned_eq :
      ∀ cell,
        ownedFineCells cell =
          Finset.filter (fun fineCell =>
            (wz1PaperGridCube delta fineCell ∩
              (restrictPaperShading
                (cover.fullFiberSubfamily
                  (dominant.dominantParent cell))
                balancing.refined).union).Nonempty)
            (balancing.selectedFineCells cell) := by
    intro cell
    rfl

  have owned_subset :
      ∀ cell ∈ dominant.selectedCells,
        ownedFineCells cell ⊆ balancing.selectedFineCells cell := by
    intro cell _
    exact Finset.filter_subset _ _

  have owned_nonempty :
      ∀ cell ∈ dominant.selectedCells,
        (ownedFineCells cell).Nonempty := by
    intro cell cell_mem
    have retained :
        cell ∈ balancing.retainedCoarseCells :=
      dominant.selectedCells_subset cell_mem
    let parent := dominant.dominantParent cell
    let fiberSubfamily := cover.fullFiberSubfamily parent
    let fiberShading :=
      restrictPaperShading fiberSubfamily balancing.refined
    have parent_active :
        parent ∈ active.activeParents cell :=
      dominant.dominantParent_mem cell retained
    have volume_lower :
        active.fiberCellMass ≤
          volume
            (fiberShading.union ∩
              wz1PaperGridCube rho cell) :=
      active.fiber_cell_mass_lower
        cell retained parent parent_active
    have volume_pos :
        0 <
          volume
            (fiberShading.union ∩
              wz1PaperGridCube rho cell) :=
      active.fiberCellMass_pos.trans_le volume_lower
    have intersection_nonempty :
        (fiberShading.union ∩
          wz1PaperGridCube rho cell).Nonempty := by
      by_contra empty
      have empty_eq :
          fiberShading.union ∩
              wz1PaperGridCube rho cell =
            ∅ := by
        simpa [Set.not_nonempty_iff_eq_empty] using empty
      rw [empty_eq] at volume_pos
      simp at volume_pos
    rcases intersection_nonempty with
      ⟨point, point_fiber, point_rho⟩
    have fiber_subset :
        fiberShading.union ⊆ balancing.refined.union := by
      intro other other_mem
      rcases other_mem with ⟨index, index_mem⟩
      exact ⟨fiberSubfamily.embedding index, index_mem⟩
    rcases
        point_in_refined_union_and_rho_cell_implies_selected_fine
          balancing retained (fiber_subset point_fiber) point_rho
      with ⟨fineCell, fine_selected, point_fine⟩
    have fine_owned :
        fineCell ∈ ownedFineCells cell := by
      simp only [ownedFineCells, Finset.mem_filter]
      exact
        ⟨fine_selected,
          ⟨point, point_fine, point_fiber⟩⟩
    exact ⟨fineCell, fine_owned⟩

  have owned_union_eq :
      ∀ cell ∈ dominant.selectedCells,
        ⋃ fineCell ∈ ownedFineCells cell,
            wz1PaperGridCube delta fineCell =
          (restrictPaperShading
              (cover.fullFiberSubfamily
                (dominant.dominantParent cell))
              balancing.refined).union ∩
            wz1PaperGridCube rho cell := by
    intro cell cell_mem
    let parent := dominant.dominantParent cell
    let fiberSubfamily := cover.fullFiberSubfamily parent
    let fiberShading :=
      restrictPaperShading fiberSubfamily balancing.refined
    have fiber_cubical :
        WZ1PaperIsCubicalShading fiberShading :=
      restrictPaperShading_cubical
        fiberSubfamily balancing.refined_cubical
    have retained :
        cell ∈ balancing.retainedCoarseCells :=
      dominant.selectedCells_subset cell_mem
    have fiber_subset :
        fiberShading.union ⊆ balancing.refined.union := by
      intro point point_mem
      rcases point_mem with ⟨index, index_mem⟩
      exact ⟨fiberSubfamily.embedding index, index_mem⟩
    ext point
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨fineCell, fine_mem, point_fine⟩
      have fine_selected :
          fineCell ∈ balancing.selectedFineCells cell := by
        exact (Finset.mem_filter.mp fine_mem).1
      have point_rho :
          point ∈ wz1PaperGridCube rho cell :=
        balancing.fine_cell_containment
          cell retained fineCell fine_selected point_fine
      have intersect_nonempty :
          (fiberShading.union ∩
            wz1PaperGridCube delta fineCell).Nonempty := by
        have owned_intersection :=
          (Finset.mem_filter.mp fine_mem).2
        simpa [Set.inter_comm] using owned_intersection
      have cube_subset :
          wz1PaperGridCube delta fineCell ⊆
            fiberShading.union :=
        cubical_cube_subset_union
          fiber_cubical intersect_nonempty
      exact ⟨cube_subset point_fine, point_rho⟩
    · rintro ⟨point_fiber, point_rho⟩
      rcases
          point_in_refined_union_and_rho_cell_implies_selected_fine
            balancing retained (fiber_subset point_fiber) point_rho
        with ⟨fineCell, fine_selected, point_fine⟩
      have fine_owned :
          fineCell ∈ ownedFineCells cell := by
        simp only [ownedFineCells, Finset.mem_filter]
        exact
          ⟨fine_selected,
            ⟨point, point_fine, point_fiber⟩⟩
      exact ⟨fineCell, fine_owned, point_fine⟩

  have cardinality_lower :
      ∀ cell ∈ dominant.selectedCells,
        dominant.dominantMass cell ≤
          (2 ^ (multiplicityLevel + 1) : ENNReal) *
            (ownedFineCells cell).card *
            active.fiberCellMass := by
    intro cell cell_mem
    let parent := dominant.dominantParent cell
    let fiberSubfamily := cover.fullFiberSubfamily parent
    let fiberShading :=
      restrictPaperShading fiberSubfamily balancing.refined
    let rhoCell := wz1PaperGridCube rho cell
    let intersection := fiberShading.union ∩ rhoCell
    have intersection_measurable :
        MeasurableSet intersection :=
      (measurableSet_shading_union fiberShading).inter
        (wz1PaperGridCube_measurable cell)
    have carrier_intersection :
        ∀ index,
          fiberShading.carrier index ∩ rhoCell =
            fiberShading.carrier index ∩ intersection := by
      intro index
      ext point
      simp only [intersection, Set.mem_inter_iff]
      constructor
      · rintro ⟨carrier_mem, rho_mem⟩
        exact
          ⟨carrier_mem, ⟨index, carrier_mem⟩, rho_mem⟩
      · rintro ⟨carrier_mem, _, rho_mem⟩
        exact ⟨carrier_mem, rho_mem⟩
    have fubini :
        dominant.dominantMass cell =
          ∫⁻ point in intersection,
            (fiberShading.pointMultiplicity point : ENNReal) := by
      rw [dominant.dominantMass_eq cell]
      dsimp only [wz2PaperParentCellMass]
      have sum_eq :
          ∑ source : Fin fiberSubfamily.family.card,
              volume (fiberShading.carrier source ∩ rhoCell) =
            ∑ source : Fin fiberSubfamily.family.card,
              volume
                (fiberShading.carrier source ∩ intersection) := by
        apply Finset.sum_congr rfl
        intro index _
        rw [carrier_intersection index]
      rw [sum_eq]
      exact
        sum_volume_inter_eq_setLIntegral_pointMultiplicity
          fiberShading intersection_measurable
    rw [fubini]
    let cap : ENNReal := 2 ^ (multiplicityLevel + 1)
    have fiber_subset :
        fiberShading.union ⊆ balancing.refined.union := by
      intro point point_mem
      rcases point_mem with ⟨index, index_mem⟩
      exact ⟨fiberSubfamily.embedding index, index_mem⟩
    have point_cap :
        ∀ point ∈ intersection,
          (fiberShading.pointMultiplicity point : ENNReal) ≤ cap := by
      intro point point_mem
      have restricted_le :
          (fiberShading.pointMultiplicity point : ENNReal) ≤
            (balancing.refined.pointMultiplicity point : ENNReal) := by
        exact_mod_cast
          restrictPaperShading_pointMultiplicity_le
            fiberSubfamily balancing.refined point
      exact
        restricted_le.trans
          (multiplicityUpper point
            (fiber_subset point_mem.1)).le
    have integral_bound :
        (∫⁻ point in intersection,
            (fiberShading.pointMultiplicity point : ENNReal)) ≤
          cap * volume intersection := by
      have bound :
          (∫⁻ point in intersection,
              (fiberShading.pointMultiplicity point : ENNReal)) ≤
            ∫⁻ _point in intersection, cap :=
        setLIntegral_mono' intersection_measurable point_cap
      rw [setLIntegral_const] at bound
      exact bound
    have intersection_volume :
        volume intersection =
          ((ownedFineCells cell).card : ENNReal) *
            active.fiberCellMass := by
      have set_eq :
          intersection =
            ⋃ fineCell ∈ ownedFineCells cell,
              wz1PaperGridCube delta fineCell :=
        (owned_union_eq cell cell_mem).symm
      rw [set_eq,
        wz1PaperGridCube_volume_biUnion
          hdelta (ownedFineCells cell),
        active.fiberCellMass_eq]
    rw [intersection_volume] at integral_bound
    simpa [cap, mul_assoc] using integral_bound

  exact
    ⟨{
      ownedFineCells := ownedFineCells
      ownedFineCells_eq := owned_eq
      ownedFineCells_subset := owned_subset
      ownedFineCells_nonempty := owned_nonempty
      owned_union_eq := owned_union_eq
      owned_cardinality_lower := cardinality_lower
    }⟩

end Kakeya.Assouad

end
