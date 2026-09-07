import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PacketCellMultiplicity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62SourceShadingMass
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers

/-!
# Statement-independent local packet-cell input

This module packages the local data needed to turn a genuine Section 6 cover
and a cubical shading into `PureWZ2Prop62PacketCellInput`.  It deliberately
does not import any frozen statement module.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/--
Local density and coarse-cell data for a fixed Section 6 cover and shading.

The nonemptiness and cubical hypotheses are included because neither follows
from the bare cover/shading pair, while both are needed to construct the
nonempty active-cell set in `toPacketCellInput`.
-/
structure PureWZ2Prop62PacketCellLocalInput
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (shading : WZ1PaperTubeShading fine) where
  delta_pos : 0 < delta
  delta_le_one_hundred : delta ≤ 1 / 100
  rho_pos : 0 < rho
  fine_nonempty : fine.Nonempty
  cubical : WZ1PaperIsCubicalShading shading
  densityConstant : ENNReal
  densityConstant_pos : 0 < densityConstant
  refined_dense : shading.IsLambdaDense densityConstant
  coarse_cell :
    ∀ sourceIndex cell,
      wz1PaperGridCube delta cell ⊆ shading.carrier sourceIndex →
        ∃! coarseCell,
          wz1PaperGridCube delta cell ⊆
              wz1PaperGridCube rho coarseCell ∧
            wz1PaperGridCube rho coarseCell ⊆
              wz1PaperTubeCarrier
                (coarse.tube
                  (cover.toWZ1PaperTubeCover.parent sourceIndex))

namespace PureWZ2Prop62PacketCellLocalInput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellLocalInput cover shading)

include input

private theorem body_mass_pos :
    0 < (wz1PaperBodyFamily fine).mass := by
  exact
    pureWZ2_prop62_source_body_mass_pos
      input.delta_pos input.delta_le_one_hundred
      input.fine_nonempty cover.fine_line_class

private theorem shading_mass_pos :
    0 < shading.mass := by
  have positiveProduct :
      0 <
        input.densityConstant *
          (wz1PaperBodyFamily fine).mass :=
    ENNReal.mul_pos input.densityConstant_pos.ne'
      input.body_mass_pos.ne'
  exact positiveProduct.trans_le input.refined_dense

private theorem activeCells_nonempty :
    (wz1PaperActiveCells shading input.delta_pos).Nonempty := by
  by_contra notNonempty
  have cellsEmpty :
      wz1PaperActiveCells shading input.delta_pos = ∅ := by
    simpa [Finset.not_nonempty_iff_eq_empty] using notNonempty
  have unionEmpty : shading.union = ∅ := by
    rw [input.cubical.union_eq_activeCells input.delta_pos, cellsEmpty]
    simp
  have massZero : shading.mass = 0 := by
    change
      (∑ sourceIndex : Fin fine.card,
        volume (shading.carrier sourceIndex)) = 0
    apply Finset.sum_eq_zero
    intro sourceIndex _sourceMem
    have carrierEmpty : shading.carrier sourceIndex = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro point pointMem
      have pointUnion : point ∈ shading.union :=
        ⟨sourceIndex, pointMem⟩
      rw [unionEmpty] at pointUnion
      exact pointUnion
    rw [carrierEmpty]
    simp
  exact (not_lt_of_ge massZero.le) input.shading_mass_pos

private noncomputable def coarseCellOf
    (cell : WZ2PaperCellIndex) : WZ2PaperCellIndex :=
  if existsSource :
      ∃ sourceIndex,
        wz1PaperGridCube delta cell ⊆
          shading.carrier sourceIndex then
    Classical.choose
      (input.coarse_cell
        (Classical.choose existsSource) cell
        (Classical.choose_spec existsSource))
  else
    0

private theorem coarseCellOf_spec
    {sourceIndex : Fin fine.card}
    {cell : WZ2PaperCellIndex}
    (wholeCell :
      wz1PaperGridCube delta cell ⊆ shading.carrier sourceIndex) :
    wz1PaperGridCube delta cell ⊆
        wz1PaperGridCube rho (input.coarseCellOf cell) ∧
      wz1PaperGridCube rho (input.coarseCellOf cell) ⊆
        wz1PaperTubeCarrier
          (coarse.tube
            (cover.toWZ1PaperTubeCover.parent sourceIndex)) := by
  let existsSource :
      ∃ sourceIndex,
        wz1PaperGridCube delta cell ⊆
          shading.carrier sourceIndex :=
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
          wz1PaperGridCube rho (Classical.choose chosenData) :=
      chosenSpec.1.1 pointFine
    have pointSource :
        point ∈ wz1PaperGridCube rho sourceCell :=
      sourceCellSpec.1.1 pointFine
    have chosenIndex :
        wz1PaperGridIndex rho point =
          Classical.choose chosenData :=
      (mem_wz1PaperGridCube rho
        (Classical.choose chosenData) point).mp pointChosen
    have sourceIndexEq :
        wz1PaperGridIndex rho point = sourceCell :=
      (mem_wz1PaperGridCube rho sourceCell point).mp pointSource
    exact chosenIndex.symm.trans sourceIndexEq
  have coarseCellEq :
      input.coarseCellOf cell = sourceCell := by
    rw [coarseCellOf, dif_pos existsSource]
    exact chosenEqSource
  rw [coarseCellEq]
  exact sourceCellSpec.1

/-- Convert the generic local data to the four-degree packet-cell input. -/
noncomputable def toPacketCellInput :
    PureWZ2Prop62PacketCellInput cover shading where
  delta_pos := input.delta_pos
  rho_pos := input.rho_pos
  cubical := input.cubical
  fineCells := wz1PaperActiveCells shading input.delta_pos
  fineCells_eq := rfl
  fineCells_nonempty := input.activeCells_nonempty
  coarseCellOf := input.coarseCellOf
  fine_cell_containment := by
    intro cell cellMem
    rcases
        ((mem_wz1PaperActiveCells shading
          input.delta_pos cell).mp cellMem).2
      with ⟨point, pointUnion, pointCell⟩
    rcases pointUnion with ⟨sourceIndex, pointCarrier⟩
    have wholeCell :
        wz1PaperGridCube delta cell ⊆
          shading.carrier sourceIndex := by
      have cellEq :
          wz1PaperGridIndex delta point = cell :=
        (mem_wz1PaperGridCube delta cell point).mp pointCell
      rw [← cellEq]
      exact input.cubical sourceIndex point pointCarrier
    exact (input.coarseCellOf_spec wholeCell).1
  parent_cell_containment := by
    intro parent cell sourceIndex _cellMem sourceMem wholeCell
    have parentEq :
        cover.toWZ1PaperTubeCover.parent sourceIndex = parent := by
      exact
        (cover.toWZ1PaperTubeCover.parent_unique sourceIndex parent <| by
          exact
            (mem_wz2PaperFullFiberIndices_iff parent sourceIndex).mp
              sourceMem).symm
    rw [← parentEq]
    exact (input.coarseCellOf_spec wholeCell).2

end PureWZ2Prop62PacketCellLocalInput

end Kakeya.Assouad

end
