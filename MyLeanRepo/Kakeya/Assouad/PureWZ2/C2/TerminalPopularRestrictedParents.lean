import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularParentRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment

/-!
# Sticky parents seen after outer-popular parent-weight regularization

The fixed line is selected on the already restricted outer-popular carrier.
Every resulting official sticky parent is therefore one of the parents in the
pre-line dyadic weight class.  This is proved from the uniqueness of the
literal paper-grid cube containing the representative point.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalPopularRestrictedFixedBinParentData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    (line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope) where
  heavy_cell_count :
    line.sliceCells.card ≤ line.globalBins.card * line.heavyCells.card
  selectedIndex : (ℤ × ℤ × ℤ) →
    Fin terminal.sticky.selected.family.card
  representative_mem_restricted :
    ∀ cell ∈ line.heavyCells,
      line.representative cell ∈ restricted.shading.union
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
  parent_selected :
    ∀ cell ∈ line.heavyCells, parentCell cell ∈ weightClass.selectedParents
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
  parents_subset_selected : parents ⊆ weightClass.selectedParents
  parents_subset_active : parents ⊆ terminal.sticky.balanced.activeCells
  parent_hit :
    ∀ parent ∈ parents, ∃ cell ∈ line.heavyCells, parentCell cell = parent

theorem PureWZ2TerminalPopularParentRestrictedPreparedData.toParents
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    (restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted)
    (line : PureWZ2HorizontalFixedLineCore
      restrictedPrepared.windowed source.globalGrains.slope) :
    Nonempty (PureWZ2TerminalPopularRestrictedFixedBinParentData
      line.toPureWZ2HorizontalFixedBinCore) := by
  let core := line.toPureWZ2HorizontalFixedBinCore
  have hrepresentativeRestricted :
      ∀ cell (hcell : cell ∈ core.heavyCells),
        core.representative cell ∈ restricted.shading.union := by
    intro cell hcell
    have hshadow := core.representative_mem cell hcell
    simpa [pureWZ2PartialActiveCellShading_union] using hshadow
  have hselectedExists : ∀ cell (hcell : cell ∈ core.heavyCells),
      ∃ selectedIndex : Fin terminal.sticky.selected.family.card,
        core.representative cell ∈
          terminalSource.shading.carrier selectedIndex := by
    intro cell hcell
    rcases hrepresentativeRestricted cell hcell with
      ⟨sourceIndex, hsourceIndex⟩
    rw [restricted.carrier_eq, carrier.carrier_eq] at hsourceIndex
    rcases carrier.zeroExtension.carrier_support sourceIndex
        (core.representative cell) hsourceIndex.1.1 with
      ⟨selectedIndex, heq, hselected⟩
    refine ⟨selectedIndex, ?_⟩
    rw [terminalSource.shading_eq]
    exact hselected
  let selectedIndex : (ℤ × ℤ × ℤ) →
      Fin terminal.sticky.selected.family.card := fun cell =>
    if hcell : cell ∈ core.heavyCells then
      Classical.choose (hselectedExists cell hcell)
    else ⟨0, terminalSource.nonempty⟩
  have hrepresentativeSelected :
      ∀ cell (hcell : cell ∈ core.heavyCells),
        core.representative cell ∈
          terminalSource.shading.carrier (selectedIndex cell) := by
    intro cell hcell
    simp only [selectedIndex, dif_pos hcell]
    exact Classical.choose_spec (hselectedExists cell hcell)
  have hrepresentativeRefined :
      ∀ cell (hcell : cell ∈ core.heavyCells),
        core.representative cell ∈
          terminal.sticky.refined.carrier (selectedIndex cell) := by
    intro cell hcell
    rw [← terminalSource.shading_eq]
    exact hrepresentativeSelected cell hcell
  let paperCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun cell =>
    wz1PaperGridIndex delta (core.representative cell)
  have hrepresentativePaperCell :
      ∀ cell (hcell : cell ∈ core.heavyCells),
        core.representative cell ∈ wz1PaperGridCube delta (paperCell cell) := by
    intro cell _
    exact (mem_wz1PaperGridCube delta _ _).mpr rfl
  have hparentExists :
      ∀ cell (hcell : cell ∈ core.heavyCells),
        ∃ parent ∈ terminal.sticky.balanced.activeCells,
          wz1PaperGridCube delta (paperCell cell) ⊆
            wz1PaperGridCube terminal.sqrtRequested.1 parent := by
    intro cell hcell
    exact terminal.sticky.balanced.fine_cell_nested
      (selectedIndex cell) (core.representative cell)
      (hrepresentativeRefined cell hcell)
  let parentCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun cell =>
    if hcell : cell ∈ core.heavyCells then
      Classical.choose (hparentExists cell hcell)
    else (0, 0, 0)
  have hparentActive :
      ∀ cell (hcell : cell ∈ core.heavyCells),
        parentCell cell ∈ terminal.sticky.balanced.activeCells := by
    intro cell hcell
    simp only [parentCell, dif_pos hcell]
    exact (Classical.choose_spec (hparentExists cell hcell)).1
  have hnested :
      ∀ cell (hcell : cell ∈ core.heavyCells),
        wz1PaperGridCube delta (paperCell cell) ⊆
          wz1PaperGridCube terminal.sqrtRequested.1 (parentCell cell) := by
    intro cell hcell
    simp only [parentCell, dif_pos hcell]
    exact (Classical.choose_spec (hparentExists cell hcell)).2
  have hrepresentativeParent :
      ∀ cell (hcell : cell ∈ core.heavyCells),
        core.representative cell ∈
          wz1PaperGridCube terminal.sqrtRequested.1 (parentCell cell) := by
    intro cell hcell
    exact hnested cell hcell (hrepresentativePaperCell cell hcell)
  have hparentSelected :
      ∀ cell (hcell : cell ∈ core.heavyCells),
        parentCell cell ∈ weightClass.selectedParents := by
    intro cell hcell
    have hrestricted := hrepresentativeRestricted cell hcell
    rw [restricted.union_eq] at hrestricted
    rw [weightClass.selectedRegion_eq] at hrestricted
    rcases Set.mem_iUnion₂.mp hrestricted.2 with
      ⟨selectedParent, hselectedParent, hrepresentativeSelectedParent⟩
    have hparentIndex :=
      (mem_wz1PaperGridCube terminal.sqrtRequested.1
        (parentCell cell) (core.representative cell)).mp
        (hrepresentativeParent cell hcell)
    have hselectedIndex :=
      (mem_wz1PaperGridCube terminal.sqrtRequested.1
        selectedParent (core.representative cell)).mp
        hrepresentativeSelectedParent
    have heq : parentCell cell = selectedParent :=
      hparentIndex.symm.trans hselectedIndex
    rwa [heq]
  let parents := core.heavyCells.image parentCell
  exact ⟨{
    heavy_cell_count := line.heavy_cell_count
    selectedIndex := selectedIndex
    representative_mem_restricted := hrepresentativeRestricted
    representative_mem_selected := hrepresentativeSelected
    representative_mem_popular := fun cell hcell =>
      restricted.subshading_carrier.union_subset
        (hrepresentativeRestricted cell hcell)
    paperCell := paperCell
    paperCell_eq := by intro cell hcell; rfl
    representative_mem_paperCell := hrepresentativePaperCell
    parentCell := parentCell
    parent_active := hparentActive
    parent_selected := hparentSelected
    paper_cell_nested := hnested
    representative_mem_parent := hrepresentativeParent
    parents := parents
    parents_eq := rfl
    parents_nonempty := core.heavyCells_nonempty.image parentCell
    parents_subset_selected := by
      intro parent hparent
      rcases Finset.mem_image.mp hparent with ⟨cell, hcell, rfl⟩
      exact hparentSelected cell hcell
    parents_subset_active := by
      intro parent hparent
      rcases Finset.mem_image.mp hparent with ⟨cell, hcell, rfl⟩
      exact hparentActive cell hcell
    parent_hit := by
      intro parent hparent
      rcases Finset.mem_image.mp hparent with ⟨cell, hcell, heq⟩
      exact ⟨cell, hcell, heq⟩
  }⟩

end Kakeya.Assouad

end
