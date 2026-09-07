import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularPreparedWindow
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalGlobalBinFamily
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment

/-!
# Sticky-parent provenance for the outer-popular terminal line

The old terminal parent package starts from a window on the full terminal
shading.  Here the fixed line instead lives on the partial-cell shadow of the
outer-popular carrier.  We recover the genuine selected tube and balanced
`sqrt delta` parent of every exact-slice representative without enlarging the
carrier or asserting a false per-parent mass identity.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Actual sticky-parent data for one global-bin fibre selected from the
outer-popular terminal carrier. -/
structure PureWZ2TerminalPopularFixedBinParentData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {popularPrepared : PureWZ2TerminalPopularPreparedWindowData carrier}
    (line : PureWZ2HorizontalFixedBinCore
      popularPrepared.windowed source.globalGrains.slope) where
  heavy_cell_count :
    line.sliceCells.card ≤ line.globalBins.card * line.heavyCells.card
  selectedIndex : (ℤ × ℤ × ℤ) →
    Fin terminal.sticky.selected.family.card
  representative_mem_selected :
    ∀ cell ∈ line.heavyCells,
      line.representative cell ∈
        terminalSource.shading.carrier (selectedIndex cell)
  representative_mem_popular :
    ∀ cell ∈ line.heavyCells,
      line.representative cell ∈ carrier.shading.union
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

/-- Recover the sticky parent of every representative on an outer-popular
global-bin fibre.  Membership in the selected tube family is obtained from
the exact zero-extension support, not from the full terminal window. -/
theorem PureWZ2TerminalPopularPreparedWindowData.toPopularTerminalBinParents
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    (popularPrepared : PureWZ2TerminalPopularPreparedWindowData carrier)
    (line : PureWZ2HorizontalFixedLineCore
      popularPrepared.windowed source.globalGrains.slope) :
    Nonempty (PureWZ2TerminalPopularFixedBinParentData
      line.toPureWZ2HorizontalFixedBinCore) := by
  have hselectedExists : ∀ cell (hcell : cell ∈ line.heavyCells),
      ∃ selectedIndex : Fin terminal.sticky.selected.family.card,
        line.representative cell ∈
          terminalSource.shading.carrier selectedIndex := by
    intro cell hcell
    have hpopular := popularPrepared.representative_mem_carrier
      line.toPureWZ2HorizontalFixedBinCore cell hcell
    rcases hpopular with ⟨sourceIndex, hsourceIndex⟩
    rw [carrier.carrier_eq] at hsourceIndex
    rcases carrier.zeroExtension.carrier_support sourceIndex
        (line.representative cell) hsourceIndex.1 with
      ⟨selectedIndex, heq, hselected⟩
    refine ⟨selectedIndex, ?_⟩
    rw [terminalSource.shading_eq]
    exact hselected
  let selectedIndex : (ℤ × ℤ × ℤ) →
      Fin terminal.sticky.selected.family.card := fun cell =>
    if hcell : cell ∈ line.heavyCells then
      Classical.choose (hselectedExists cell hcell)
    else ⟨0, terminalSource.nonempty⟩
  have hrepresentativeSelected :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        line.representative cell ∈
          terminalSource.shading.carrier (selectedIndex cell) := by
    intro cell hcell
    simp only [selectedIndex, dif_pos hcell]
    exact Classical.choose_spec (hselectedExists cell hcell)
  have hrepresentativeRefined :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        line.representative cell ∈
          terminal.sticky.refined.carrier (selectedIndex cell) := by
    intro cell hcell
    rw [← terminalSource.shading_eq]
    exact hrepresentativeSelected cell hcell
  let paperCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun cell =>
    wz1PaperGridIndex delta (line.representative cell)
  have hrepresentativePaperCell :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        line.representative cell ∈ wz1PaperGridCube delta (paperCell cell) := by
    intro cell _hcell
    exact (mem_wz1PaperGridCube delta _ _).mpr rfl
  have hparentExists :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        ∃ parent ∈ terminal.sticky.balanced.activeCells,
          wz1PaperGridCube delta (paperCell cell) ⊆
            wz1PaperGridCube terminal.sqrtRequested.1 parent := by
    intro cell hcell
    exact terminal.sticky.balanced.fine_cell_nested
      (selectedIndex cell) (line.representative cell)
      (hrepresentativeRefined cell hcell)
  let parentCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun cell =>
    if hcell : cell ∈ line.heavyCells then
      Classical.choose (hparentExists cell hcell)
    else (0, 0, 0)
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
    heavy_cell_count := line.heavy_cell_count
    selectedIndex := selectedIndex
    representative_mem_selected := hrepresentativeSelected
    representative_mem_popular :=
      popularPrepared.representative_mem_carrier
        line.toPureWZ2HorizontalFixedBinCore
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
      exact ⟨cell, hcell, heq⟩ }⟩

end Kakeya.Assouad

end
