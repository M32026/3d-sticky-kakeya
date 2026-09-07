import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedActiveParentCellsStatements

/-!
# Total shaded mass as a sum of retained-cell incidence masses

An exactly balanced fine shading is supported on the disjoint union of its
retained literal `rho`-cells.  Finite additivity therefore decomposes its
total shaded incidence mass cell by cell.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem wz2_paper_cell_incidence_mass_sum
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    (balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells availableFineCells) :
    balancing.refined.mass =
      ∑ cell ∈ balancing.retainedCoarseCells,
        wz2PaperCellIncidenceMass
          (rho := rho) balancing.refined cell := by
  have carrier_partition :
      ∀ source : Fin fine.card,
        balancing.refined.carrier source =
          ⋃ cell ∈ balancing.retainedCoarseCells,
            balancing.refined.carrier source ∩
              wz1PaperGridCube rho cell := by
    intro source
    ext point
    constructor
    · intro point_carrier
      have point_union : point ∈ balancing.refined.union :=
        ⟨source, point_carrier⟩
      rw [balancing.refined_union_eq] at point_union
      rcases Set.mem_iUnion₂.mp point_union with
        ⟨fineCell, fineCell_mem, point_fine⟩
      rw [balancing.retainedFineCells_eq] at fineCell_mem
      rcases Finset.mem_biUnion.mp fineCell_mem with
        ⟨cell, cell_mem, fine_selected⟩
      have point_cell : point ∈ wz1PaperGridCube rho cell :=
        balancing.fine_cell_containment
          cell cell_mem fineCell fine_selected point_fine
      exact
        Set.mem_iUnion₂.mpr
          ⟨cell, cell_mem, point_carrier, point_cell⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨_cell, _cell_mem, point_carrier, _point_cell⟩
      exact point_carrier
  have carrier_volume :
      ∀ source : Fin fine.card,
        volume (balancing.refined.carrier source) =
          ∑ cell ∈ balancing.retainedCoarseCells,
            volume
              (balancing.refined.carrier source ∩
                wz1PaperGridCube rho cell) := by
    intro source
    have disjoint :
        Set.PairwiseDisjoint
          (↑balancing.retainedCoarseCells)
          (fun cell =>
            balancing.refined.carrier source ∩
              wz1PaperGridCube rho cell) := by
      intro first _ second _ hne
      exact
        (wz1PaperGridCube_disjoint hne).mono
          Set.inter_subset_right Set.inter_subset_right
    have measurable :
        ∀ cell ∈ balancing.retainedCoarseCells,
          MeasurableSet
            (balancing.refined.carrier source ∩
              wz1PaperGridCube rho cell) := by
      intro cell _
      exact
        (balancing.refined.measurable_carrier source).inter
          (wz1PaperGridCube_measurable cell)
    calc
      volume (balancing.refined.carrier source) =
          volume
            (⋃ cell ∈ balancing.retainedCoarseCells,
              balancing.refined.carrier source ∩
                wz1PaperGridCube rho cell) := by
        exact congrArg volume (carrier_partition source)
      _ =
          ∑ cell ∈ balancing.retainedCoarseCells,
            volume
              (balancing.refined.carrier source ∩
                wz1PaperGridCube rho cell) :=
        MeasureTheory.measure_biUnion_finset disjoint measurable
  calc
    balancing.refined.mass =
        ∑ source : Fin fine.card,
          ∑ cell ∈ balancing.retainedCoarseCells,
            volume
              (balancing.refined.carrier source ∩
                wz1PaperGridCube rho cell) := by
      apply Finset.sum_congr rfl
      intro source _
      exact carrier_volume source
    _ =
        ∑ cell ∈ balancing.retainedCoarseCells,
          ∑ source : Fin fine.card,
            volume
              (balancing.refined.carrier source ∩
                wz1PaperGridCube rho cell) := by
      rw [Finset.sum_comm]
    _ =
        ∑ cell ∈ balancing.retainedCoarseCells,
          wz2PaperCellIncidenceMass
            (rho := rho) balancing.refined cell := by
      rfl

end Kakeya.Assouad

end
