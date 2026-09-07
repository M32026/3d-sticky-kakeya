import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellMassConversion
import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers

/-!
# Family-independent balanced cells for Proposition 6.3

The fresh square-root cover in the finite Lemma 4.11/4.12 step is produced
on a selected tube family.  The subsequent common-spatial lift returns to the
ambient family but preserves the geometric union exactly.  It is therefore
incorrect to manufacture a Section-6 parent cover for the ambient family.

This file records precisely the spatial part of a genuine balanced cover that
the full-grain/Fubini argument uses.  The data can be transported only across
an equality of shaded unions; no unrelated cover or shading is accepted.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

/-- The spatial cell partition supplied by a genuine balanced cover.  Unlike
`PureWZ2BalancedCoverData`, this record does not claim a parent assignment for
the ambient tube family. -/
structure Proposition63BalancedCellData
    {delta scale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (fineShading : WZ1PaperTubeShading family) where
  scale_pos : 0 < scale
  activeCells : Finset (ℤ × ℤ × ℤ)
  cellMass : ENNReal
  cellMass_pos : 0 < cellMass
  cellMass_ne_top : cellMass ≠ ⊤
  fine_cell_mass :
    ∀ cell ∈ activeCells,
      volume (fineShading.union ∩ wz1PaperGridCube scale cell) = cellMass
  cellRep : ∀ cell, cell ∈ activeCells → Point3
  cellRep_in_union :
    ∀ cell (hcell : cell ∈ activeCells),
      cellRep cell hcell ∈ fineShading.union
  cellRep_in_cell :
    ∀ cell (hcell : cell ∈ activeCells),
      cellRep cell hcell ∈ wz1PaperGridCube scale cell
  fine_union_volume :
    volume fineShading.union = (activeCells.card : ENNReal) * cellMass
  activeCells_subset_gridWindow :
    activeCells ⊆ wz1PaperGridIndicesInWindow scale scale_pos

namespace Proposition63BalancedCellData

variable {delta scale : ℝ}
  {family : Kakeya.Streamlined.TubeFamily delta}
  {fineShading : WZ1PaperTubeShading family}

/-- A balanced cell has a genuine fine-shaded point because its common mass
is positive. -/
lemma cellIntersection_nonempty
    (data : Proposition63BalancedCellData (scale := scale) fineShading)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ data.activeCells) :
    (fineShading.union ∩ wz1PaperGridCube scale cell).Nonempty := by
  by_contra hempty
  have hemptyEq :
      fineShading.union ∩ wz1PaperGridCube scale cell = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hempty
  have hmass := data.fine_cell_mass cell hcell
  rw [hemptyEq, measure_empty] at hmass
  exact data.cellMass_pos.ne' hmass.symm

/-- Forget the tube-parent component of a genuine balanced cover while
retaining its exact spatial partition. -/
noncomputable def ofBalancedCover
    {coarse : Kakeya.Streamlined.TubeFamily scale}
    {cover : PureWZ2Section6Cover family coarse}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hscale : 0 < scale) :
    Proposition63BalancedCellData (scale := scale) fineShading where
  scale_pos := hscale
  activeCells := balanced.activeCells
  cellMass := balanced.cellMass
  cellMass_pos := balanced.cellMass_pos
  cellMass_ne_top := balanced.cellMass_ne_top
  fine_cell_mass := balanced.fine_cell_mass
  cellRep := balanced.cellRep
  cellRep_in_union := balanced.cellRep_in_union
  cellRep_in_cell := balanced.cellRep_in_cell
  fine_union_volume := balanced_cover_fine_union_volume balanced hscale
  activeCells_subset_gridWindow := by
    intro cell hcell
    let point : Point3 := cellCorner scale cell
    have hpointCell : point ∈ wz1PaperGridCube scale cell :=
      cellCorner_mem_gridCube hscale cell
    have hpointUnion : point ∈ coarseShading.union := by
      rw [balanced.coarse_union_eq]
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCell⟩
    rcases hpointUnion with ⟨index, hpointCarrier⟩
    have hpointBox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
      (coarseShading.subset_body index hpointCarrier).2
    have hwindow := paper_point_gridIndex_in_window hscale hpointBox
    have hindex : wz1PaperGridIndex scale point = cell :=
      (mem_wz1PaperGridCube scale cell point).mp hpointCell
    rwa [hindex] at hwindow

/-- Transport balanced spatial cells across an exact equality of shaded
unions.  This is the honest adapter from a selected-family sticky output to
its common-spatial ambient lift. -/
noncomputable def transportUnion
    (data : Proposition63BalancedCellData (scale := scale) fineShading)
    {targetFamily : Kakeya.Streamlined.TubeFamily delta}
    {target : WZ1PaperTubeShading targetFamily}
    (hunion : target.union = fineShading.union) :
    Proposition63BalancedCellData (scale := scale) target where
  scale_pos := data.scale_pos
  activeCells := data.activeCells
  cellMass := data.cellMass
  cellMass_pos := data.cellMass_pos
  cellMass_ne_top := data.cellMass_ne_top
  fine_cell_mass := by
    intro cell hcell
    rw [hunion]
    exact data.fine_cell_mass cell hcell
  cellRep := data.cellRep
  cellRep_in_union := by
    intro cell hcell
    rw [hunion]
    exact data.cellRep_in_union cell hcell
  cellRep_in_cell := data.cellRep_in_cell
  fine_union_volume := by
    rw [hunion]
    exact data.fine_union_volume
  activeCells_subset_gridWindow := data.activeCells_subset_gridWindow

/-- Exact whole-cell balancing itself supplies balanced spatial cells; no
coarse tube family is needed once the geometric pruning has been performed. -/
noncomputable def ofExactBalancing
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells : WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {source : WZ1PaperTubeShading family}
    (balancing : WZ2PaperExactCellBalancingData
      (rho := scale) source coarseCells availableFineCells)
    (hscale : 0 < scale) :
    Proposition63BalancedCellData (scale := scale) balancing.refined := by
  have hnonempty : ∀ cell, cell ∈ balancing.retainedCoarseCells →
      (balancing.refined.union ∩ wz1PaperGridCube scale cell).Nonempty := by
    intro cell hcell
    by_contra hempty
    have hemptyEq :
        balancing.refined.union ∩ wz1PaperGridCube scale cell = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hempty
    have hmass := balancing.fine_cell_mass cell hcell
    rw [hemptyEq, measure_empty] at hmass
    exact balancing.cellMass_pos.ne' hmass.symm
  let representative := fun cell hcell =>
    Classical.choose (hnonempty cell hcell)
  have hunion : balancing.refined.union =
      ⋃ cell ∈ balancing.retainedCoarseCells,
        balancing.refined.union ∩ wz1PaperGridCube scale cell := by
    apply Set.Subset.antisymm
    · intro point hpoint
      rw [balancing.refined_union_eq] at hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨fineCell, hfineCell, hpointFine⟩
      rw [balancing.retainedFineCells_eq] at hfineCell
      rcases Finset.mem_biUnion.mp hfineCell with
        ⟨cell, hcell, hfineSelected⟩
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, ⟨by
        rw [balancing.refined_union_eq]
        exact Set.mem_iUnion₂.mpr ⟨fineCell, by
          rw [balancing.retainedFineCells_eq]
          exact Finset.mem_biUnion.mpr ⟨cell, hcell, hfineSelected⟩,
          hpointFine⟩,
        balancing.fine_cell_containment cell hcell fineCell hfineSelected
          hpointFine⟩⟩
    · intro point hpoint
      rcases Set.mem_iUnion₂.mp hpoint with ⟨_cell, _hcell, hpointFine, _⟩
      exact hpointFine
  have hvolume : volume balancing.refined.union =
      (balancing.retainedCoarseCells.card : ENNReal) * balancing.cellMass := by
    rw [hunion]
    have hdisjoint : Set.PairwiseDisjoint
        (↑balancing.retainedCoarseCells)
        (fun cell => balancing.refined.union ∩
          wz1PaperGridCube scale cell) := by
      intro first _ second _ hne
      exact (wz1PaperGridCube_disjoint hne).mono
        Set.inter_subset_right Set.inter_subset_right
    have hmeasurable : ∀ cell ∈ balancing.retainedCoarseCells,
        MeasurableSet (balancing.refined.union ∩
          wz1PaperGridCube scale cell) := by
      intro cell _
      exact balancing.refined.union_measurable.inter
        (wz1PaperGridCube_measurable cell)
    rw [MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable]
    calc
      (∑ cell ∈ balancing.retainedCoarseCells,
          volume (balancing.refined.union ∩
            wz1PaperGridCube scale cell)) =
          ∑ _cell ∈ balancing.retainedCoarseCells, balancing.cellMass := by
        apply Finset.sum_congr rfl
        intro cell hcell
        exact balancing.fine_cell_mass cell hcell
      _ = (balancing.retainedCoarseCells.card : ENNReal) *
          balancing.cellMass := by simp [Finset.sum_const]
  refine
    { scale_pos := hscale
      activeCells := balancing.retainedCoarseCells
      cellMass := balancing.cellMass
      cellMass_pos := balancing.cellMass_pos
      cellMass_ne_top := balancing.cellMass_ne_top
      fine_cell_mass := balancing.fine_cell_mass
      cellRep := representative
      cellRep_in_union := ?_
      cellRep_in_cell := ?_
      fine_union_volume := hvolume
      activeCells_subset_gridWindow := ?_ }
  · intro cell hcell
    exact (Classical.choose_spec (hnonempty cell hcell)).1
  · intro cell hcell
    exact (Classical.choose_spec (hnonempty cell hcell)).2
  · intro cell hcell
    let point := representative cell hcell
    have hpointUnion : point ∈ balancing.refined.union :=
      (Classical.choose_spec (hnonempty cell hcell)).1
    rcases hpointUnion with ⟨index, hpointCarrier⟩
    have hpointBox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
      (balancing.refined.subset_body index hpointCarrier).2
    have hwindow := paper_point_gridIndex_in_window hscale hpointBox
    have hpointCell : point ∈ wz1PaperGridCube scale cell :=
      (Classical.choose_spec (hnonempty cell hcell)).2
    have hindex : wz1PaperGridIndex scale point = cell :=
      (mem_wz1PaperGridCube scale cell point).mp hpointCell
    rwa [hindex] at hwindow

end Proposition63BalancedCellData

/-- Provenance for a balanced spatial decomposition transported from a
genuine Section-6 cover.  The source and target tube families may differ, but
their shaded unions must be exactly equal. -/
structure Proposition63TransportedBalancedCoverData
    {delta scale : ℝ}
    {targetFamily : Kakeya.Streamlined.TubeFamily delta}
    (target : WZ1PaperTubeShading targetFamily) where
  sourceFamily : Kakeya.Streamlined.TubeFamily delta
  sourceShading : WZ1PaperTubeShading sourceFamily
  coarse : Kakeya.Streamlined.TubeFamily scale
  cover : PureWZ2Section6Cover sourceFamily coarse
  coarseShading : WZ1PaperTubeShading coarse
  balanced : PureWZ2BalancedCoverData cover sourceShading coarseShading
  scale_pos : 0 < scale
  target_union_eq : target.union = sourceShading.union

namespace Proposition63TransportedBalancedCoverData

/-- The family-independent cells carried by a provenance-preserving
transported balanced cover. -/
noncomputable def cells
    {delta scale : ℝ}
    {targetFamily : Kakeya.Streamlined.TubeFamily delta}
    {target : WZ1PaperTubeShading targetFamily}
    (data : Proposition63TransportedBalancedCoverData
      (scale := scale) target) :
    Proposition63BalancedCellData (scale := scale) target :=
  (Proposition63BalancedCellData.ofBalancedCover data.balanced
    data.scale_pos).transportUnion
      data.target_union_eq

end Proposition63TransportedBalancedCoverData

end Kakeya.Assouad.PureWZ2

end
