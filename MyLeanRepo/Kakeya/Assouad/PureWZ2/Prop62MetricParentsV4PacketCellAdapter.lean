import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsPacketCellInput
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperAudit.StatementsV4
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62SourceShadingMass

/-!
# V4 metric parents to the packet-cell input

The frozen metric-parent output already supplies the refined fine family,
its cubical shading, and the genuine Section 6 cover.  The subsequent
four-degree argument additionally needs only:

* a positive aggregate density certificate, used to prove that the active
  fine-cell set is nonempty;
* the paper's pointwise unique coarse-cell containment statement.

This module packages those local inputs into `PureWZ2Prop62PacketCellInput`.
It does not import an open target or use aligned-source provenance.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open MeasureTheory
open Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The exact post-metric inputs appearing in the Target 4 statement. -/
structure MetricParentsV4PacketCellLocalInput
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (metric :
      MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
          parentConstant fiberConstant) where
  delta_pos : 0 < delta
  delta_le_one_hundred : delta ≤ 1 / 100
  densityConstant : ENNReal
  densityConstant_pos : 0 < densityConstant
  refined_dense :
    metric.refinement.refined.IsLambdaDense densityConstant
  coarse_cell :
    ∀ sourceIndex cell,
      wz1PaperGridCube delta cell ⊆
          metric.refinement.refined.carrier sourceIndex →
        ∃! coarseCell,
          wz1PaperGridCube delta cell ⊆
              wz1PaperGridCube rho.1 coarseCell ∧
            wz1PaperGridCube rho.1 coarseCell ⊆
              wz1PaperTubeCarrier
                (metric.scaleData.coarse.tube
                  (metric.scaleData.cover.parent sourceIndex))

namespace MetricParentsV4PacketCellLocalInput

variable
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {metric :
      MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
          parentConstant fiberConstant}
    (input : MetricParentsV4PacketCellLocalInput metric)

include input

private theorem refined_body_mass_pos :
    0 < (wz1PaperBodyFamily metric.refinement.selected.family).mass := by
  exact
    pureWZ2_prop62_source_body_mass_pos
      input.delta_pos input.delta_le_one_hundred
      metric.refined_nonempty
      metric.scaleData.section6Cover.fine_line_class

private theorem refined_mass_pos :
    0 < metric.refinement.refined.mass := by
  have positiveProduct :
      0 <
        input.densityConstant *
          (wz1PaperBodyFamily metric.refinement.selected.family).mass :=
    ENNReal.mul_pos input.densityConstant_pos.ne'
      (input.refined_body_mass_pos).ne'
  exact positiveProduct.trans_le input.refined_dense

private theorem activeCells_nonempty :
    (wz1PaperActiveCells
      metric.refinement.refined
      input.delta_pos).Nonempty := by
  by_contra notNonempty
  have cellsEmpty :
      wz1PaperActiveCells metric.refinement.refined
          input.delta_pos =
        ∅ := by
    simpa [Finset.not_nonempty_iff_eq_empty] using notNonempty
  have unionEmpty : metric.refinement.refined.union = ∅ := by
    rw [metric.refined_cubical.union_eq_activeCells
      input.delta_pos, cellsEmpty]
    simp
  have massZero : metric.refinement.refined.mass = 0 := by
    change
      (∑ sourceIndex : Fin metric.refinement.selected.family.card,
        volume (metric.refinement.refined.carrier sourceIndex)) = 0
    apply Finset.sum_eq_zero
    intro sourceIndex _sourceMem
    have carrierEmpty :
        metric.refinement.refined.carrier sourceIndex = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro point pointMem
      have pointUnion : point ∈ metric.refinement.refined.union :=
        ⟨sourceIndex, pointMem⟩
      rw [unionEmpty] at pointUnion
      exact pointUnion
    rw [carrierEmpty]
    simp
  exact (not_lt_of_ge massZero.le) (input.refined_mass_pos)

private noncomputable def coarseCellOf
    (cell : WZ2PaperCellIndex) : WZ2PaperCellIndex :=
  if existsSource :
      ∃ sourceIndex,
        wz1PaperGridCube delta cell ⊆
          metric.refinement.refined.carrier sourceIndex then
    Classical.choose
      (input.coarse_cell
        (Classical.choose existsSource) cell
        (Classical.choose_spec existsSource))
  else
    0

private theorem coarseCellOf_spec
    {sourceIndex : Fin metric.refinement.selected.family.card}
    {cell : WZ2PaperCellIndex}
    (wholeCell :
      wz1PaperGridCube delta cell ⊆
        metric.refinement.refined.carrier sourceIndex) :
    wz1PaperGridCube delta cell ⊆
        wz1PaperGridCube rho.1 (input.coarseCellOf cell) ∧
      wz1PaperGridCube rho.1 (input.coarseCellOf cell) ⊆
        wz1PaperTubeCarrier
          (metric.scaleData.coarse.tube
            (metric.scaleData.cover.parent sourceIndex)) := by
  let existsSource :
      ∃ sourceIndex,
        wz1PaperGridCube delta cell ⊆
          metric.refinement.refined.carrier sourceIndex :=
    ⟨sourceIndex, wholeCell⟩
  let chosenSource := Classical.choose existsSource
  let chosenData :=
    input.coarse_cell chosenSource cell
      (Classical.choose_spec existsSource)
  have chosenSpec :=
    Classical.choose_spec chosenData
  have sourceSpec :=
    input.coarse_cell sourceIndex cell wholeCell
  let sourceCell := Classical.choose sourceSpec
  have sourceCellSpec := Classical.choose_spec sourceSpec
  have chosenEqSource :
      Classical.choose chosenData = sourceCell := by
    let point := cellCorner delta cell
    have pointFine :
        point ∈ wz1PaperGridCube delta cell :=
      cellCorner_mem_gridCube input.delta_pos cell
    have pointChosen :
        point ∈
          wz1PaperGridCube rho.1 (Classical.choose chosenData) :=
      chosenSpec.1.1 pointFine
    have pointSource :
        point ∈ wz1PaperGridCube rho.1 sourceCell :=
      sourceCellSpec.1.1 pointFine
    have chosenIndex :
        wz1PaperGridIndex rho.1 point =
          Classical.choose chosenData :=
      (mem_wz1PaperGridCube rho.1
        (Classical.choose chosenData) point).mp pointChosen
    have sourceIndexEq :
        wz1PaperGridIndex rho.1 point = sourceCell :=
      (mem_wz1PaperGridCube rho.1 sourceCell point).mp pointSource
    exact chosenIndex.symm.trans sourceIndexEq
  have coarseCellEq :
      input.coarseCellOf cell = sourceCell := by
    rw [coarseCellOf, dif_pos existsSource]
    exact chosenEqSource
  rw [coarseCellEq]
  exact sourceCellSpec.1

/-- Package the frozen V4 metric parents as the packet-cell input. -/
noncomputable def toPacketCellInput :
    PureWZ2Prop62PacketCellInput
      metric.scaleData.section6Cover
      metric.refinement.refined where
  delta_pos := input.delta_pos
  rho_pos := metric.rho_pos
  cubical := metric.refined_cubical
  fineCells :=
    wz1PaperActiveCells metric.refinement.refined
      input.delta_pos
  fineCells_eq := rfl
  fineCells_nonempty :=
    MetricParentsV4PacketCellLocalInput.activeCells_nonempty input
  coarseCellOf := input.coarseCellOf
  fine_cell_containment := by
    intro cell cellMem
    rcases
        ((mem_wz1PaperActiveCells metric.refinement.refined
          input.delta_pos cell).mp cellMem).2
      with ⟨point, pointUnion, pointCell⟩
    rcases pointUnion with ⟨sourceIndex, pointCarrier⟩
    have wholeCell :
        wz1PaperGridCube delta cell ⊆
          metric.refinement.refined.carrier sourceIndex :=
      by
        have cellEq :
            wz1PaperGridIndex delta point = cell :=
          (mem_wz1PaperGridCube delta cell point).mp pointCell
        rw [← cellEq]
        exact metric.refined_cubical sourceIndex point pointCarrier
    exact (input.coarseCellOf_spec wholeCell).1
  parent_cell_containment := by
    intro parent cell sourceIndex _cellMem sourceMem wholeCell
    have parentEq :
        metric.scaleData.cover.parent sourceIndex = parent := by
      exact
        (metric.scaleData.cover.parent_unique sourceIndex parent <| by
          exact
            (mem_wz2PaperFullFiberIndices_iff parent sourceIndex).mp
              sourceMem).symm
    rw [← parentEq]
    exact (input.coarseCellOf_spec wholeCell).2

end MetricParentsV4PacketCellLocalInput

end Kakeya.Assouad.Prop62PaperAudit.V4

end
