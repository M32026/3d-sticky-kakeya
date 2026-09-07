import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleWindow
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment

/-!
# Actual `sqrt delta` parents met by the terminal fixed line

Each exact-slice representative is a genuine point of the terminal refined
paper shading.  Its complete side-`delta` paper cell is therefore nested in
one active side-`sqrt delta` balanced parent.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalFixedBinParentData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    (line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope) where
  sourceIndex : (ℤ × ℤ × ℤ) → Fin terminal.sticky.selected.family.card
  representative_mem_source :
    ∀ cell ∈ line.heavyCells,
      line.representative cell ∈
        terminalSource.shading.carrier (sourceIndex cell)
  paperCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
  paperCell_eq :
    ∀ cell ∈ line.heavyCells,
      paperCell cell = wz1PaperGridIndex delta (line.representative cell)
  representative_mem_paperCell :
    ∀ cell ∈ line.heavyCells,
      line.representative cell ∈ wz1PaperGridCube delta (paperCell cell)
  parentCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
  parent_active :
    ∀ cell ∈ line.heavyCells,
      parentCell cell ∈ terminal.sticky.balanced.activeCells
  paper_cell_nested :
    ∀ cell (hcell : cell ∈ line.heavyCells),
      wz1PaperGridCube delta (paperCell cell) ⊆
        wz1PaperGridCube terminal.sqrtRequested.1 (parentCell cell)
  representative_mem_parent :
    ∀ cell ∈ line.heavyCells,
      line.representative cell ∈
        wz1PaperGridCube terminal.sqrtRequested.1 (parentCell cell)
  parents : Finset (ℤ × ℤ × ℤ)
  parents_eq : parents = line.heavyCells.image parentCell
  parents_nonempty : parents.Nonempty
  parents_subset : parents ⊆ terminal.sticky.balanced.activeCells
  parent_hit :
    ∀ parent ∈ parents, ∃ cell ∈ line.heavyCells, parentCell cell = parent

/-- Backwards-compatible parent package on the largest global-bin core. -/
abbrev PureWZ2TerminalFixedLineParentData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    (line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope) :=
  PureWZ2TerminalFixedBinParentData
    line.toPureWZ2HorizontalFixedBinCore

theorem PureWZ2HorizontalFixedBinCore.toTerminalBinParents
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    (line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope) :
    Nonempty (PureWZ2TerminalFixedBinParentData line) := by
  have hrepresentativePaper :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        line.representative cell ∈ terminalSource.shading.union := by
    intro cell hcell
    have hwindow := line.representative_mem cell hcell
    have hshadow := window.subshading.union_subset hwindow
    rwa [prepared.shadow_union] at hshadow
  let sourceIndex : (ℤ × ℤ × ℤ) → Fin terminal.sticky.selected.family.card :=
    fun cell => if hcell : cell ∈ line.heavyCells then
      Classical.choose (hrepresentativePaper cell hcell) else
      ⟨0, terminalSource.nonempty⟩
  have hrepresentativeSource :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        line.representative cell ∈
          terminalSource.shading.carrier (sourceIndex cell) := by
    intro cell hcell
    simp only [sourceIndex, dif_pos hcell]
    exact Classical.choose_spec (hrepresentativePaper cell hcell)
  have hrepresentativeRefined :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        line.representative cell ∈
          terminal.sticky.refined.carrier (sourceIndex cell) := by
    intro cell hcell
    rw [← terminalSource.shading_eq]
    exact hrepresentativeSource cell hcell
  let paperCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun cell =>
    wz1PaperGridIndex delta (line.representative cell)
  have hrepresentativePaperCell :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        line.representative cell ∈ wz1PaperGridCube delta (paperCell cell) := by
    intro cell _
    exact (mem_wz1PaperGridCube delta _ _).mpr rfl
  have hparentExists :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        ∃ parent ∈ terminal.sticky.balanced.activeCells,
          wz1PaperGridCube delta (paperCell cell) ⊆
            wz1PaperGridCube terminal.sqrtRequested.1 parent := by
    intro cell hcell
    exact terminal.sticky.balanced.fine_cell_nested
      (sourceIndex cell) (line.representative cell)
      (hrepresentativeRefined cell hcell)
  let parentCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun cell =>
    if hcell : cell ∈ line.heavyCells then
      Classical.choose (hparentExists cell hcell) else (0, 0, 0)
  have hparentActive :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        parentCell cell ∈ terminal.sticky.balanced.activeCells := by
    intro cell hcell
    simp only [parentCell, dif_pos hcell]
    exact (Classical.choose_spec (hparentExists cell hcell)).1
  have hnested :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        wz1PaperGridCube delta (paperCell cell) ⊆
          wz1PaperGridCube terminal.sqrtRequested.1 (parentCell cell) := by
    intro cell hcell
    simp only [parentCell, dif_pos hcell]
    exact (Classical.choose_spec (hparentExists cell hcell)).2
  have hrepresentativeParent :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        line.representative cell ∈
          wz1PaperGridCube terminal.sqrtRequested.1 (parentCell cell) := by
    intro cell hcell
    exact hnested cell hcell (hrepresentativePaperCell cell hcell)
  let parents := line.heavyCells.image parentCell
  exact ⟨{
    sourceIndex := sourceIndex
    representative_mem_source := hrepresentativeSource
    paperCell := paperCell
    paperCell_eq := by intro cell hcell; rfl
    representative_mem_paperCell := hrepresentativePaperCell
    parentCell := parentCell
    parent_active := hparentActive
    paper_cell_nested := hnested
    representative_mem_parent := hrepresentativeParent
    parents := parents
    parents_eq := rfl
    parents_nonempty := line.heavyCells_nonempty.image parentCell
    parents_subset := by
      intro parent hparent
      rcases Finset.mem_image.mp hparent with ⟨cell, hcell, rfl⟩
      exact hparentActive cell hcell
    parent_hit := by
      intro parent hparent
      rcases Finset.mem_image.mp hparent with ⟨cell, hcell, heq⟩
      exact ⟨cell, hcell, heq⟩
  }⟩

/-- Compatibility wrapper for the former largest-bin terminal chain. -/
theorem PureWZ2HorizontalFixedLineCore.toTerminalParents
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    (line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope) :
    Nonempty (PureWZ2TerminalFixedLineParentData line) :=
  line.toPureWZ2HorizontalFixedBinCore.toTerminalBinParents

end Kakeya.Assouad
