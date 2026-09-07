import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalYResidue
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PaperCubeSliceArea

/-!
# Source-family shading on one separated horizontal residue
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2SourceHorizontalFixedBinResidueShadingData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    (residue : PureWZ2SourceHorizontalFixedBinYResidueData selection) where
  sliceCellFor : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
  sliceCellFor_mem : ∀ parent ∈ residue.selected,
    sliceCellFor parent ∈ line.heavyCells
  sliceCellFor_parent : ∀ parent ∈ residue.selected,
    parents.parentCell (sliceCellFor parent) = parent
  sliceCellFor_injective : Set.InjOn sliceCellFor residue.selected
  cellFor : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
  cellFor_mem : ∀ parent ∈ residue.selected,
    cellFor parent ∈ pullback.selectedCells
  sliceRepresentative_mem_cellFor : ∀ parent ∈ residue.selected,
    line.representative (sliceCellFor parent) ∈
      wz1PaperGridCube rho (cellFor parent)
  cellFor_parent : ∀ parent ∈ residue.selected,
    wz1PaperGridCube rho (cellFor parent) ⊆
      wz1PaperGridCube twoScale.sqrtRequested.1 parent
  cellFor_injective : Set.InjOn cellFor residue.selected
  cellParent : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
  cellParent_active : ∀ cell ∈ pullback.selectedCells,
    cellParent cell ∈ twoScale.fine.balanced.activeCells
  cell_parent : ∀ cell ∈ pullback.selectedCells,
    wz1PaperGridCube rho cell ⊆
      wz1PaperGridCube twoScale.sqrtRequested.1 (cellParent cell)
  cellParent_cellFor : ∀ parent ∈ residue.selected,
    cellParent (cellFor parent) = parent
  selectedCells : Finset (ℤ × ℤ × ℤ) :=
    pullback.selectedCells.filter fun cell => cellParent cell ∈ residue.selected
  selectedCells_eq : selectedCells =
    pullback.selectedCells.filter fun cell => cellParent cell ∈ residue.selected
  selectedCells_subset : selectedCells ⊆ pullback.selectedCells
  cellFor_selected : ∀ parent ∈ residue.selected, cellFor parent ∈ selectedCells
  selectedCells_card_lower : residue.selected.card ≤ selectedCells.card
  selectedCells_cube_volume :
    (selectedCells.card : ENNReal) *
        MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0)) =
      (residue.selected.card : ENNReal) *
        twoScale.fine.balanced.cellMass
  selectedRegion : Set Point3 :=
    ⋃ cell ∈ selectedCells, wz1PaperGridCube rho cell
  selectedRegion_eq : selectedRegion =
    ⋃ cell ∈ selectedCells, wz1PaperGridCube rho cell
  selectedRegion_measurable : MeasurableSet selectedRegion
  shading : WZ1PaperTubeShading source.family
  sliceRepresentative_mem : ∀ parent ∈ residue.selected,
    line.representative (sliceCellFor parent) ∈ shading.union
  carrier_eq : ∀ index, shading.carrier index =
    pullback.shading.carrier index ∩ selectedRegion
  subshading : PureWZ2PaperIsSubshading shading source.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  /-- The ordinary carrier used by the later finite graph.  It defaults to
  the whole-cell shadow, but may subsequently be restricted by the paper's
  pre-graph height-popularity step without changing the retained paper
  shading used for the final whole-cell lift. -/
  graphShadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily shading source.extremal.delta_pos) :=
      pureWZ2ActiveCellShading shading source.extremal.delta_pos
  graphShadow_sub : IsSubshading graphShadow
    (pureWZ2ActiveCellShading shading source.extremal.delta_pos)
  graphShadow_union_subset : graphShadow.union ⊆ shading.union
  union_eq : shading.union = pullback.shading.union ∩ selectedRegion
  volume_eq : MeasureTheory.volume shading.union =
    (selectedCells.card : ENNReal) * twoScale.coarse.balanced.cellMass
  volume_lower :
    (residue.selected.card : ENNReal) * twoScale.coarse.balanced.cellMass ≤
      MeasureTheory.volume shading.union
  volume_mul_cube :
    MeasureTheory.volume shading.union *
        MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0)) =
      ((residue.selected.card : ENNReal) *
        twoScale.fine.balanced.cellMass) *
        twoScale.coarse.balanced.cellMass
  commonParentHeight : ℤ
  parent_height_eq :
    ∀ parent ∈ residue.selected, parent.2.2 = commonParentHeight
  union_height :
    ∀ point ∈ shading.union,
      point (2 : Fin 3) ∈ Set.Ico
        ((commonParentHeight : ℝ) * twoScale.sqrtRequested.1)
        (((commonParentHeight : ℝ) + 1) * twoScale.sqrtRequested.1)

theorem PureWZ2SourceHorizontalFixedBinYResidueData.retainSourceShadingFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    (residue : PureWZ2SourceHorizontalFixedBinYResidueData selection) :
    ∃ retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue,
      retained.graphShadow.union = retained.shading.union := by
  have hrho : 0 < rho := line.rho_pos
  have hroot : 0 < twoScale.sqrtRequested.1 :=
    twoScale.fine.coarse_extremal.delta_pos
  have hhit : ∀ parent (hparent : parent ∈ residue.selected),
      ∃ cell ∈ line.heavyCells, parents.parentCell cell = parent := by
    intro parent hparent
    exact selection.selected_hit parent (residue.selected_subset hparent)
  let heavyFor : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun parent =>
    if hparent : parent ∈ residue.selected then
      Classical.choose (hhit parent hparent) else (0, 0, 0)
  have hheavyMem : ∀ parent (hparent : parent ∈ residue.selected),
      heavyFor parent ∈ line.heavyCells := by
    intro parent hparent
    simp only [heavyFor, dif_pos hparent]
    exact (Classical.choose_spec (hhit parent hparent)).1
  have hheavyParent : ∀ parent (hparent : parent ∈ residue.selected),
      parents.parentCell (heavyFor parent) = parent := by
    intro parent hparent
    simp only [heavyFor, dif_pos hparent]
    exact (Classical.choose_spec (hhit parent hparent)).2
  let cellFor : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun parent =>
    parents.rhoCell (heavyFor parent)
  have hcellMem : ∀ parent (hparent : parent ∈ residue.selected),
      cellFor parent ∈ pullback.selectedCells := by
    intro parent hparent
    exact parents.rhoCell_selected (heavyFor parent) (hheavyMem parent hparent)
  have hcellParent : ∀ parent (hparent : parent ∈ residue.selected),
      wz1PaperGridCube rho (cellFor parent) ⊆
        wz1PaperGridCube twoScale.sqrtRequested.1 parent := by
    intro parent hparent
    have h := parents.rho_cell_nested (heavyFor parent) (hheavyMem parent hparent)
    rwa [hheavyParent parent hparent] at h
  have hcellInjective : Set.InjOn cellFor residue.selected := by
    intro first hfirst second hsecond heq
    let point := line.representative (heavyFor first)
    have hpointCell : point ∈ wz1PaperGridCube rho (cellFor first) :=
      parents.representative_mem_rhoCell (heavyFor first) (hheavyMem first hfirst)
    have hpointFirst : point ∈
        wz1PaperGridCube twoScale.sqrtRequested.1 first :=
      hcellParent first hfirst hpointCell
    have hpointSecond : point ∈
        wz1PaperGridCube twoScale.sqrtRequested.1 second := by
      apply hcellParent second hsecond
      rwa [← heq]
    exact ((mem_wz1PaperGridCube twoScale.sqrtRequested.1 first point).mp
      hpointFirst).symm.trans
      ((mem_wz1PaperGridCube twoScale.sqrtRequested.1 second point).mp
        hpointSecond)
  have hfineExists :
      ∀ cell (hcell : cell ∈ pullback.selectedCells),
        ∃ point, point ∈ twoScale.fine.refined.union ∧
          point ∈ wz1PaperGridCube rho cell := by
    intro cell hcell
    have hactive : cell ∈ wz1PaperActiveCells
        twoScale.fine.refined
          twoScale.coarseGrains.extremal.delta_pos := by
      simpa [pullback.selectedCells_eq, twoScale.rhoRequested_eq] using hcell
    rcases ((mem_wz1PaperActiveCells twoScale.fine.refined
      twoScale.coarseGrains.extremal.delta_pos cell).mp hactive).2 with
      ⟨point, hpointUnion, hpointCell⟩
    exact ⟨point, hpointUnion, by
      simpa only [twoScale.rhoRequested_eq] using hpointCell⟩
  let finePoint : (ℤ × ℤ × ℤ) → Point3 := fun cell =>
    if hcell : cell ∈ pullback.selectedCells then
      Classical.choose (hfineExists cell hcell) else 0
  have hfinePoint :
      ∀ cell (hcell : cell ∈ pullback.selectedCells),
        finePoint cell ∈ twoScale.fine.refined.union ∧
          finePoint cell ∈ wz1PaperGridCube rho cell := by
    intro cell hcell
    simp only [finePoint, dif_pos hcell]
    exact Classical.choose_spec (hfineExists cell hcell)
  let fineIndex : (ℤ × ℤ × ℤ) →
      Fin twoScale.fine.selected.family.card := fun cell =>
    if hcell : cell ∈ pullback.selectedCells then
      Classical.choose (hfinePoint cell hcell).1
    else ⟨0, twoScale.fine.selected_nonempty⟩
  have hfineCarrier :
      ∀ cell (hcell : cell ∈ pullback.selectedCells),
        finePoint cell ∈ twoScale.fine.refined.carrier (fineIndex cell) := by
    intro cell hcell
    simp only [fineIndex, dif_pos hcell]
    exact Classical.choose_spec (hfinePoint cell hcell).1
  have hnestedExists :
      ∀ cell (hcell : cell ∈ pullback.selectedCells),
        ∃ parent ∈ twoScale.fine.balanced.activeCells,
          wz1PaperGridCube twoScale.rhoRequested.1
              (wz1PaperGridIndex twoScale.rhoRequested.1 (finePoint cell)) ⊆
            wz1PaperGridCube twoScale.sqrtRequested.1 parent := by
    intro cell hcell
    exact twoScale.fine.balanced.fine_cell_nested
      (fineIndex cell) (finePoint cell) (hfineCarrier cell hcell)
  let cellParent : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun cell =>
    if hcell : cell ∈ pullback.selectedCells then
      Classical.choose (hnestedExists cell hcell) else (0, 0, 0)
  have hcellParentActive :
      ∀ cell (hcell : cell ∈ pullback.selectedCells),
        cellParent cell ∈ twoScale.fine.balanced.activeCells := by
    intro cell hcell
    simp only [cellParent, dif_pos hcell]
    exact (Classical.choose_spec (hnestedExists cell hcell)).1
  have hcellIndex :
      ∀ cell (hcell : cell ∈ pullback.selectedCells),
        wz1PaperGridIndex twoScale.rhoRequested.1 (finePoint cell) = cell := by
    intro cell hcell
    rw [twoScale.rhoRequested_eq]
    exact (mem_wz1PaperGridCube rho cell (finePoint cell)).mp
      (hfinePoint cell hcell).2
  have hselectedCellParent :
      ∀ cell (hcell : cell ∈ pullback.selectedCells),
        wz1PaperGridCube rho cell ⊆
          wz1PaperGridCube twoScale.sqrtRequested.1 (cellParent cell) := by
    intro cell hcell
    have hraw := (Classical.choose_spec (hnestedExists cell hcell)).2
    simp only [cellParent, dif_pos hcell]
    have hsource :
        wz1PaperGridCube rho cell =
          wz1PaperGridCube twoScale.rhoRequested.1
            (wz1PaperGridIndex twoScale.rhoRequested.1 (finePoint cell)) := by
      rw [hcellIndex cell hcell]
      congr 1
      exact twoScale.rhoRequested_eq.symm
    rw [hsource]
    exact hraw
  have hcellParentCellFor :
      ∀ parent (hparent : parent ∈ residue.selected),
        cellParent (cellFor parent) = parent := by
    intro parent hparent
    let point := line.representative (heavyFor parent)
    have hpointCell : point ∈ wz1PaperGridCube rho (cellFor parent) :=
      parents.representative_mem_rhoCell
        (heavyFor parent) (hheavyMem parent hparent)
    have hpointSelectedParent :
        point ∈ wz1PaperGridCube twoScale.sqrtRequested.1
          (cellParent (cellFor parent)) :=
      hselectedCellParent (cellFor parent) (hcellMem parent hparent) hpointCell
    have hpointParent :
        point ∈ wz1PaperGridCube twoScale.sqrtRequested.1 parent :=
      hcellParent parent hparent hpointCell
    exact
      ((mem_wz1PaperGridCube twoScale.sqrtRequested.1
        (cellParent (cellFor parent)) point).mp hpointSelectedParent).symm.trans
      ((mem_wz1PaperGridCube twoScale.sqrtRequested.1 parent point).mp
        hpointParent)
  have hheavyInjective : Set.InjOn heavyFor residue.selected := by
    intro first hfirst second hsecond heq
    calc
      first = parents.parentCell (heavyFor first) :=
        (hheavyParent first hfirst).symm
      _ = parents.parentCell (heavyFor second) := by rw [heq]
      _ = second := hheavyParent second hsecond
  let selectedCells := pullback.selectedCells.filter fun cell =>
    cellParent cell ∈ residue.selected
  have hselectedSubset : selectedCells ⊆ pullback.selectedCells := by
    exact Finset.filter_subset _ _
  have hcellForSelected :
      ∀ parent (hparent : parent ∈ residue.selected),
        cellFor parent ∈ selectedCells := by
    intro parent hparent
    exact Finset.mem_filter.mpr
      ⟨hcellMem parent hparent, by rw [hcellParentCellFor parent hparent]; exact hparent⟩
  have himageSubset : residue.selected.image cellFor ⊆ selectedCells := by
    intro cell hcell
    rcases Finset.mem_image.mp hcell with ⟨parent, hparent, rfl⟩
    exact hcellForSelected parent hparent
  have hselectedCardLower : residue.selected.card ≤ selectedCells.card := by
    rw [← Finset.card_image_of_injOn hcellInjective]
    exact Finset.card_le_card himageSubset
  have hfineUnion :
      twoScale.fine.refined.union =
        ⋃ cell ∈ pullback.selectedCells, wz1PaperGridCube rho cell := by
    have hraw := twoScale.fine.refined_cubical.union_eq_activeCells
      twoScale.coarseGrains.extremal.delta_pos
    rw [pullback.selectedCells_eq]
    simpa only [twoScale.rhoRequested_eq] using hraw
  have hselectedRegionFine :
      twoScale.fine.refined.union ∩
          ⋃ parent ∈ residue.selected,
            wz1PaperGridCube twoScale.sqrtRequested.1 parent =
        ⋃ cell ∈ selectedCells, wz1PaperGridCube rho cell := by
    ext point
    constructor
    · rintro ⟨hpointFine, hpointParent⟩
      rw [hfineUnion] at hpointFine
      rcases Set.mem_iUnion₂.mp hpointFine with
        ⟨cell, hcell, hpointCell⟩
      rcases Set.mem_iUnion₂.mp hpointParent with
        ⟨parent, hparent, hpointParent⟩
      have hpointCellParent := hselectedCellParent cell hcell hpointCell
      have hparentEq : cellParent cell = parent :=
        ((mem_wz1PaperGridCube twoScale.sqrtRequested.1
          (cellParent cell) point).mp hpointCellParent).symm.trans
        ((mem_wz1PaperGridCube twoScale.sqrtRequested.1
          parent point).mp hpointParent)
      exact Set.mem_iUnion₂.mpr ⟨cell,
        Finset.mem_filter.mpr ⟨hcell, by rwa [hparentEq]⟩, hpointCell⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨cell, hcell, hpointCell⟩
      have hcellData := Finset.mem_filter.mp hcell
      refine ⟨?_, ?_⟩
      · rw [hfineUnion]
        exact Set.mem_iUnion₂.mpr ⟨cell, hcellData.1, hpointCell⟩
      · exact Set.mem_iUnion₂.mpr ⟨cellParent cell, hcellData.2,
          hselectedCellParent cell hcellData.1 hpointCell⟩
  have hselectedCubeVolume :
      (selectedCells.card : ENNReal) *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0)) =
        (residue.selected.card : ENNReal) *
          twoScale.fine.balanced.cellMass := by
    have hleft := wz1PaperGridCube_volume_biUnion line.rho_pos selectedCells
    have hright := twoScale.fine.balanced.selected_cells_volume
      residue.selected
      (residue.selected_subset.trans
        (selection.selected_subset.trans parents.parents_subset))
    rw [← hleft, ← hright, hselectedRegionFine]
  let selectedRegion : Set Point3 :=
    ⋃ cell ∈ selectedCells, wz1PaperGridCube rho cell
  have hregionMeas : MeasurableSet selectedRegion :=
    MeasurableSet.biUnion selectedCells.finite_toSet.countable
      (fun cell _ => wz1PaperGridCube_measurable cell)
  let shading : WZ1PaperTubeShading source.family :=
    { carrier := fun index => pullback.shading.carrier index ∩ selectedRegion
      measurable_carrier := fun index =>
        (pullback.shading.measurable_carrier index).inter hregionMeas
      subset_body := fun index => Set.inter_subset_left.trans
        (pullback.shading.subset_body index) }
  have hunion : shading.union = pullback.shading.union ∩ selectedRegion := by
    ext point
    constructor
    · rintro ⟨index, hsource, hregion⟩
      exact ⟨⟨index, hsource⟩, hregion⟩
    · rintro ⟨⟨index, hsource⟩, hregion⟩
      exact ⟨index, hsource, hregion⟩
  have hsub : PureWZ2PaperIsSubshading shading source.shading := by
    intro index point hpoint
    exact pullback.subshading index hpoint.1
  have hwhole : WZ1PaperIsCubicalShading shading := by
    intro index point hpoint other hother
    have hpullOther := pullback.whole_cells index point hpoint.1 hother
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨selectedCell, hselectedCell, hpointSelected⟩
    have hpointPullback : point ∈ pullback.shading.carrier index := hpoint.1
    rw [pullback.carrier_eq] at hpointPullback
    rcases pullback.zeroExtension.carrier_support index point hpointPullback.1 with
      ⟨selectedIndex, _heq, hselectedFine⟩
    rcases twoScale.coarse.balanced.fine_cell_nested
        selectedIndex point hselectedFine with
      ⟨nestedCell, _hnestedActive, hnested⟩
    have hpointNested : point ∈ wz1PaperGridCube rho nestedCell := by
      rw [← twoScale.rhoRequested_eq]
      exact hnested ((mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) point).mpr rfl)
    have hcellEq : nestedCell = selectedCell :=
      ((mem_wz1PaperGridCube rho nestedCell point).mp hpointNested).symm.trans
        ((mem_wz1PaperGridCube rho selectedCell point).mp hpointSelected)
    exact ⟨hpullOther, Set.mem_iUnion₂.mpr
      ⟨selectedCell, hselectedCell, by
        rw [← hcellEq, ← twoScale.rhoRequested_eq]
        exact hnested hother⟩⟩
  have hvolume : MeasureTheory.volume shading.union =
      (selectedCells.card : ENNReal) *
        twoScale.coarse.balanced.cellMass := by
    rw [hunion]
    have hpartition :
        pullback.shading.union ∩ selectedRegion =
          ⋃ cell ∈ selectedCells,
            pullback.shading.union ∩ wz1PaperGridCube rho cell := by
      ext point
      constructor
      · rintro ⟨hpull, hregion⟩
        rcases Set.mem_iUnion₂.mp hregion with ⟨cell, hcell, hpointCell⟩
        exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpull, hpointCell⟩
      · rintro hpoint
        rcases Set.mem_iUnion₂.mp hpoint with
          ⟨cell, hcell, hpull, hpointCell⟩
        exact ⟨hpull, Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCell⟩⟩
    rw [hpartition]
    have hdisjoint : (selectedCells : Set (ℤ × ℤ × ℤ)).PairwiseDisjoint
        (fun cell => pullback.shading.union ∩ wz1PaperGridCube rho cell) := by
      intro first _ second _ hne
      exact (wz1PaperGridCube_disjoint hne).mono
        Set.inter_subset_right Set.inter_subset_right
    have hmeas : ∀ cell ∈ selectedCells, MeasurableSet
        (pullback.shading.union ∩ wz1PaperGridCube rho cell) := by
      intro cell _
      exact (measurableSet_shading_union pullback.shading).inter
        (wz1PaperGridCube_measurable cell)
    rw [MeasureTheory.measure_biUnion_finset hdisjoint hmeas]
    calc
      (∑ cell ∈ selectedCells,
          volume (pullback.shading.union ∩ wz1PaperGridCube rho cell)) =
          ∑ _cell ∈ selectedCells, twoScale.coarse.balanced.cellMass := by
        apply Finset.sum_congr rfl
        intro cell hcell
        exact pullback.cell_mass cell (hselectedSubset hcell)
      _ = (selectedCells.card : ENNReal) *
          twoScale.coarse.balanced.cellMass := by simp [Finset.sum_const]
  have hvolumeLower :
      (residue.selected.card : ENNReal) *
          twoScale.coarse.balanced.cellMass ≤ volume shading.union := by
    rw [hvolume]
    gcongr
  have hvolumeMulCube :
      MeasureTheory.volume shading.union *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0)) =
        ((residue.selected.card : ENNReal) *
          twoScale.fine.balanced.cellMass) *
          twoScale.coarse.balanced.cellMass := by
    rw [hvolume]
    calc
      ((selectedCells.card : ENNReal) *
            twoScale.coarse.balanced.cellMass) *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0)) =
        ((selectedCells.card : ENNReal) *
            MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
          twoScale.coarse.balanced.cellMass := by ring
      _ = ((residue.selected.card : ENNReal) *
            twoScale.fine.balanced.cellMass) *
          twoScale.coarse.balanced.cellMass := by
        rw [hselectedCubeVolume]
  let firstParent := Classical.choose residue.selected_nonempty
  have hfirstParent : firstParent ∈ residue.selected :=
    Classical.choose_spec residue.selected_nonempty
  let commonParentHeight := firstParent.2.2
  have hparentHeight : ∀ parent ∈ residue.selected,
      parent.2.2 = commonParentHeight := by
    intro parent hparent
    have hparentSelected := residue.selected_subset hparent
    have hfirstSelected := residue.selected_subset hfirstParent
    rcases selection.selected_hit parent hparentSelected with
      ⟨cell, hcell, hcellParent⟩
    rcases selection.selected_hit firstParent hfirstSelected with
      ⟨firstCell, hfirstCell, hfirstCellParent⟩
    have hmem := parents.representative_mem_parent cell hcell
    have hfirstMem := parents.representative_mem_parent firstCell hfirstCell
    rw [hcellParent] at hmem
    rw [hfirstCellParent] at hfirstMem
    have hindex := (mem_wz1PaperGridCube twoScale.sqrtRequested.1 parent _).mp hmem
    have hfirstIndex :=
      (mem_wz1PaperGridCube twoScale.sqrtRequested.1 firstParent _).mp hfirstMem
    have hheight := line.representative_height cell hcell
    have hfirstHeight := line.representative_height firstCell hfirstCell
    have hz := congrArg (fun idx : ℤ × ℤ × ℤ => idx.2.2) hindex
    have hzFirst := congrArg (fun idx : ℤ × ℤ × ℤ => idx.2.2) hfirstIndex
    simp [wz1PaperGridIndex, gridIndex, hheight, hfirstHeight] at hz hzFirst
    exact hz.symm.trans hzFirst
  have hunionHeight : ∀ point ∈ shading.union,
      point (2 : Fin 3) ∈ Set.Ico
        ((commonParentHeight : ℝ) * twoScale.sqrtRequested.1)
        (((commonParentHeight : ℝ) + 1) * twoScale.sqrtRequested.1) := by
    intro point hpoint
    have hregion := (by rw [hunion] at hpoint; exact hpoint.2)
    rcases Set.mem_iUnion₂.mp hregion with ⟨cell, hcell, hpointCell⟩
    have hcellData := Finset.mem_filter.mp hcell
    let parent := cellParent cell
    have hparentMem : parent ∈ residue.selected := hcellData.2
    have hsubset := hselectedCellParent cell hcellData.1
    have hpointParent := hsubset hpointCell
    rw [wz1PaperGridCube_eq_Ico hroot parent] at hpointParent
    rw [← hparentHeight parent hparentMem]
    exact ⟨hpointParent.2.2.2.2.1, hpointParent.2.2.2.2.2⟩
  let retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue := {
    sliceCellFor := heavyFor
    sliceCellFor_mem := hheavyMem
    sliceCellFor_parent := hheavyParent
    sliceCellFor_injective := hheavyInjective
    sliceRepresentative_mem := by
      intro parent hparent
      have hpullback : line.representative (heavyFor parent) ∈
          pullback.shading.union := by
        have hwindow := line.representative_mem (heavyFor parent)
          (hheavyMem parent hparent)
        have hshadow : line.representative (heavyFor parent) ∈
            prepared.shadow.union := by
          rcases hwindow with ⟨index, hindex⟩
          exact ⟨index, window.subshading index hindex⟩
        rwa [prepared.shadow_union] at hshadow
      rw [hunion]
      refine ⟨hpullback, ?_⟩
      rw [show selectedRegion =
          ⋃ cell ∈ selectedCells, wz1PaperGridCube rho cell by rfl]
      exact Set.mem_iUnion₂.mpr
        ⟨cellFor parent, hcellForSelected parent hparent,
          parents.representative_mem_rhoCell
            (heavyFor parent) (hheavyMem parent hparent)⟩
    cellFor := cellFor
    cellFor_mem := hcellMem
    sliceRepresentative_mem_cellFor := by
      intro parent hparent
      exact parents.representative_mem_rhoCell
        (heavyFor parent) (hheavyMem parent hparent)
    cellFor_parent := hcellParent
    cellFor_injective := hcellInjective
    cellParent := cellParent
    cellParent_active := hcellParentActive
    cell_parent := hselectedCellParent
    cellParent_cellFor := hcellParentCellFor
    selectedCells := selectedCells
    selectedCells_eq := rfl
    selectedCells_subset := hselectedSubset
    cellFor_selected := hcellForSelected
    selectedCells_card_lower := hselectedCardLower
    selectedCells_cube_volume := hselectedCubeVolume
    selectedRegion := selectedRegion
    selectedRegion_eq := rfl
    selectedRegion_measurable := hregionMeas
    shading := shading
    carrier_eq := fun _ => rfl
    subshading := hsub
    whole_cells := hwhole
    graphShadow := pureWZ2ActiveCellShading shading source.extremal.delta_pos
    graphShadow_sub := fun _ _ h => h
    graphShadow_union_subset := by
      rw [pureWZ2ActiveCellShading_union shading source.extremal.delta_pos
        hwhole]
    union_eq := hunion
    volume_eq := hvolume
    volume_lower := hvolumeLower
    volume_mul_cube := hvolumeMulCube
    commonParentHeight := commonParentHeight
    parent_height_eq := hparentHeight
    union_height := hunionHeight
  }
  refine ⟨retained, ?_⟩
  exact pureWZ2ActiveCellShading_union shading source.extremal.delta_pos hwhole

/-- The source residue is obtained by two common spatial restrictions of the
first sticky refined shading, so its point-multiplicity band is unchanged. -/
theorem PureWZ2SourceHorizontalFixedBinResidueShadingData.constantMultiplicityFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue) :
    retained.shading.HasConstantMultiplicity
      twoScale.coarse.fineMultiplicity
      (2 * twoScale.coarse.fineMultiplicity) := by
  have hambient := pullback.zeroExtension.constantMultiplicity
    twoScale.coarse.refined_multiplicity_band
  intro point hpoint
  have hpull : point ∈ pullback.shading.union := by
    rcases hpoint with ⟨index, hpointCarrier⟩
    rw [retained.carrier_eq] at hpointCarrier
    exact ⟨index, hpointCarrier.1⟩
  have hfirst := wholeCellRestriction_pointMultiplicity_eq
    retained.carrier_eq hpoint
  have hsecond := wholeCellRestriction_pointMultiplicity_eq
    pullback.carrier_eq hpull
  rw [hfirst, hsecond]
  exact hambient point (by
    rcases hpull with ⟨index, hpointCarrier⟩
    rw [pullback.carrier_eq] at hpointCarrier
    exact ⟨index, hpointCarrier.1⟩)

/-- The first balanced cover gives the exact indexed source mass on every
union of retained side-`rho` cells.  This is the mass analogue of
`volume_eq`; no multiplicity or cell-volume estimate is used. -/
theorem PureWZ2SourceHorizontalFixedBinResidueShadingData.mass_eq_selectedCells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue) :
    retained.shading.mass =
      (retained.selectedCells.card : ENNReal) *
        twoScale.coarse.balanced.incidenceMass := by
  have hcarrierPartition : ∀ sourceIndex : Fin source.family.card,
      retained.shading.carrier sourceIndex =
        ⋃ cell ∈ retained.selectedCells,
          retained.shading.carrier sourceIndex ∩
            wz1PaperGridCube rho cell := by
    intro sourceIndex
    ext point
    constructor
    · intro hpoint
      rw [retained.carrier_eq] at hpoint
      rw [retained.selectedRegion_eq] at hpoint
      rcases Set.mem_iUnion₂.mp hpoint.2 with
        ⟨cell, hcell, hpointCell⟩
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, ⟨by
        rw [retained.carrier_eq, retained.selectedRegion_eq]
        exact hpoint, hpointCell⟩⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨_cell, _hcell, hsource, _hpointCell⟩
      exact hsource
  have hcellMass : ∀ cell ∈ retained.selectedCells,
      (∑ sourceIndex : Fin source.family.card,
        volume (retained.shading.carrier sourceIndex ∩
          wz1PaperGridCube rho cell)) =
        twoScale.coarse.balanced.incidenceMass := by
    intro cell hcell
    have hcellRegion : wz1PaperGridCube rho cell ⊆
        retained.selectedRegion := by
      intro point hpoint
      rw [retained.selectedRegion_eq]
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpoint⟩
    calc
      (∑ sourceIndex : Fin source.family.card,
          volume (retained.shading.carrier sourceIndex ∩
            wz1PaperGridCube rho cell)) =
        ∑ sourceIndex : Fin source.family.card,
          volume (pullback.shading.carrier sourceIndex ∩
            wz1PaperGridCube rho cell) := by
          apply Finset.sum_congr rfl
          intro sourceIndex _
          rw [retained.carrier_eq]
          congr 1
          ext point
          constructor
          · rintro ⟨⟨hsource, _hregion⟩, hpointCell⟩
            exact ⟨hsource, hpointCell⟩
          · rintro ⟨hsource, hpointCell⟩
            exact ⟨⟨hsource, hcellRegion hpointCell⟩, hpointCell⟩
      _ = twoScale.coarse.balanced.incidenceMass :=
        pullback.cell_incidence_mass cell
          (retained.selectedCells_subset hcell)
  have hcarrierVolume : ∀ sourceIndex : Fin source.family.card,
      volume (retained.shading.carrier sourceIndex) =
        ∑ cell ∈ retained.selectedCells,
          volume (retained.shading.carrier sourceIndex ∩
            wz1PaperGridCube rho cell) := by
    intro sourceIndex
    calc
      volume (retained.shading.carrier sourceIndex) =
          volume (⋃ cell ∈ retained.selectedCells,
            retained.shading.carrier sourceIndex ∩
              wz1PaperGridCube rho cell) :=
        congrArg volume (hcarrierPartition sourceIndex)
      _ = ∑ cell ∈ retained.selectedCells,
          volume (retained.shading.carrier sourceIndex ∩
            wz1PaperGridCube rho cell) := by
        apply MeasureTheory.measure_biUnion_finset
        · intro first _ second _ hne
          exact (wz1PaperGridCube_disjoint hne).mono
            Set.inter_subset_right Set.inter_subset_right
        · intro cell _
          exact (retained.shading.measurable_carrier sourceIndex).inter
            (wz1PaperGridCube_measurable cell)
  calc
    retained.shading.mass =
        ∑ sourceIndex : Fin source.family.card,
          ∑ cell ∈ retained.selectedCells,
            volume (retained.shading.carrier sourceIndex ∩
              wz1PaperGridCube rho cell) := by
        apply Finset.sum_congr rfl
        intro sourceIndex _
        exact hcarrierVolume sourceIndex
    _ = ∑ cell ∈ retained.selectedCells,
          ∑ sourceIndex : Fin source.family.card,
            volume (retained.shading.carrier sourceIndex ∩
              wz1PaperGridCube rho cell) := by
        rw [Finset.sum_comm]
    _ = ∑ _cell ∈ retained.selectedCells,
          twoScale.coarse.balanced.incidenceMass := by
        apply Finset.sum_congr rfl
        exact hcellMass
    _ = (retained.selectedCells.card : ENNReal) *
          twoScale.coarse.balanced.incidenceMass := by
        simp [Finset.sum_const]

/-- Exact two-cover cross identity for a selected family of second-stage
parents.  The physical side-`rho` cube is retained as a common factor; it is
not weakened to a power bound. -/
theorem PureWZ2SourceHorizontalFixedBinResidueShadingData.mass_mul_cube
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue) :
    retained.shading.mass *
        volume (wz1PaperGridCube rho (0, 0, 0)) =
      ((residue.selected.card : ENNReal) *
          twoScale.fine.balanced.cellMass) *
        twoScale.coarse.balanced.incidenceMass := by
  rw [retained.mass_eq_selectedCells]
  calc
    ((retained.selectedCells.card : ENNReal) *
          twoScale.coarse.balanced.incidenceMass) *
        volume (wz1PaperGridCube rho (0, 0, 0)) =
      ((retained.selectedCells.card : ENNReal) *
          volume (wz1PaperGridCube rho (0, 0, 0))) *
        twoScale.coarse.balanced.incidenceMass := by ring
    _ = ((residue.selected.card : ENNReal) *
          twoScale.fine.balanced.cellMass) *
        twoScale.coarse.balanced.incidenceMass := by
      rw [retained.selectedCells_cube_volume]

/-- Backwards-compatible retained shading on the maximal global bin. -/
abbrev PureWZ2SourceHorizontalResidueShadingData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    (residue : PureWZ2SourceHorizontalYResidueData selection) :=
  PureWZ2SourceHorizontalFixedBinResidueShadingData residue

/-- Compatibility wrapper for the former maximal-bin retention API. -/
theorem PureWZ2SourceHorizontalYResidueData.retainSourceShading
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    (residue : PureWZ2SourceHorizontalYResidueData selection) :
    ∃ retained : PureWZ2SourceHorizontalResidueShadingData residue,
      retained.graphShadow.union = retained.shading.union :=
  residue.retainSourceShadingFixedBin

/-- Compatibility name for the maximal-bin constant-multiplicity theorem. -/
theorem PureWZ2SourceHorizontalResidueShadingData.constantMultiplicity
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (retained : PureWZ2SourceHorizontalResidueShadingData residue) :
    retained.shading.HasConstantMultiplicity
      twoScale.coarse.fineMultiplicity
      (2 * twoScale.coarse.fineMultiplicity) :=
  retained.constantMultiplicityFixedBin

end Kakeya.Assouad
