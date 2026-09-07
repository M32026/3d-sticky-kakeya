import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleSourceFamily
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers

/-!
# Exact source cells meeting the genuine terminal coarse sources

For every selected side-`sqrt delta` parent, retain every side-`delta` paper
cell that meets its self-centered coarse source.  The resulting paper shading
uses the original source family, consists of whole `delta`-cells, and covers
all genuine coarse sources.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalSourceCellData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    {selection : PureWZ2TerminalParentYSelection parents}
    {residue : PureWZ2TerminalParentYResidueData selection}
    {retained : PureWZ2TerminalRetainedShadingData residue}
    (sources : PureWZ2TerminalSourceFamily retained) where
  cells : Finset (ℤ × ℤ × ℤ)
  cells_subset : cells ⊆
    wz1PaperActiveCells retained.shading source.extremal.delta_pos
  cells_nonempty : cells.Nonempty
  ownerParent : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
  owner_mem : ∀ cell ∈ cells, ownerParent cell ∈ residue.selected
  witness : (ℤ × ℤ × ℤ) → Point3
  witness_mem_coarse : ∀ cell (hcell : cell ∈ cells),
    witness cell ∈
      (sources.sourceFor (ownerParent cell) (owner_mem cell hcell)).coarseSource
  witness_mem_cell : ∀ cell ∈ cells,
    witness cell ∈ wz1PaperGridCube delta cell
  cell_subset_owner : ∀ cell (hcell : cell ∈ cells),
    wz1PaperGridCube delta cell ⊆
      wz1PaperGridCube terminal.sqrtRequested.1 (ownerParent cell)
  selectedRegion : Set Point3 :=
    ⋃ cell ∈ cells, wz1PaperGridCube delta cell
  selectedRegion_eq : selectedRegion =
    ⋃ cell ∈ cells, wz1PaperGridCube delta cell
  shading : WZ1PaperTubeShading source.family
  carrier_eq : ∀ index, shading.carrier index =
    retained.shading.carrier index ∩ selectedRegion
  subshading : PureWZ2PaperIsSubshading shading retained.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  union_eq : shading.union = selectedRegion
  coarse_source_subset : ∀ parent (hparent : parent ∈ residue.selected),
    (sources.sourceFor parent hparent).coarseSource ⊆ shading.union
  volume_fraction : volume retained.shading.union ≤ 512 * volume shading.union

theorem PureWZ2TerminalSourceFamily.sourceCells
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    {selection : PureWZ2TerminalParentYSelection parents}
    {residue : PureWZ2TerminalParentYResidueData selection}
    {retained : PureWZ2TerminalRetainedShadingData residue}
    (sources : PureWZ2TerminalSourceFamily retained) :
    Nonempty (PureWZ2TerminalSourceCellData sources) := by
  let ambientCells :=
    wz1PaperActiveCells retained.shading source.extremal.delta_pos
  let meetsSource (cell : ℤ × ℤ × ℤ) : Prop :=
    ∃ parent, ∃ hparent : parent ∈ residue.selected,
      ((sources.sourceFor parent hparent).coarseSource ∩
        wz1PaperGridCube delta cell).Nonempty
  let cells := ambientCells.filter meetsSource
  have hcellsSubset : cells ⊆ ambientCells := Finset.filter_subset _ _
  have hownerExists : ∀ cell (hcell : cell ∈ cells),
      ∃ parent, ∃ hparent : parent ∈ residue.selected,
        ((sources.sourceFor parent hparent).coarseSource ∩
          wz1PaperGridCube delta cell).Nonempty := by
    intro cell hcell
    exact (Finset.mem_filter.mp hcell).2
  let ownerParent (cell : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
    if hcell : cell ∈ cells then Classical.choose (hownerExists cell hcell)
    else Classical.choose residue.selected_nonempty
  have hownerMem : ∀ cell (hcell : cell ∈ cells),
      ownerParent cell ∈ residue.selected := by
    intro cell hcell
    simp only [ownerParent, dif_pos hcell]
    exact Classical.choose (Classical.choose_spec (hownerExists cell hcell))
  let ownerProof (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ cells) :
      ownerParent cell ∈ residue.selected := hownerMem cell hcell
  have hwitnessExists : ∀ cell (hcell : cell ∈ cells),
      ((sources.sourceFor (ownerParent cell) (ownerProof cell hcell)).coarseSource ∩
        wz1PaperGridCube delta cell).Nonempty := by
    intro cell hcell
    simp only [ownerParent, ownerProof, dif_pos hcell]
    exact Classical.choose_spec (Classical.choose_spec (hownerExists cell hcell))
  let witness (cell : ℤ × ℤ × ℤ) : Point3 :=
    if hcell : cell ∈ cells then Classical.choose (hwitnessExists cell hcell) else 0
  have hwitness : ∀ cell (hcell : cell ∈ cells),
      witness cell ∈
          (sources.sourceFor (ownerParent cell) (ownerProof cell hcell)).coarseSource ∩
        wz1PaperGridCube delta cell := by
    intro cell hcell
    simp only [witness, dif_pos hcell]
    exact Classical.choose_spec (hwitnessExists cell hcell)
  have hcellOwner : ∀ cell (hcell : cell ∈ cells),
      wz1PaperGridCube delta cell ⊆
        wz1PaperGridCube terminal.sqrtRequested.1 (ownerParent cell) := by
    intro cell hcell
    let parent := ownerParent cell
    let hparent := ownerProof cell hcell
    let point := witness cell
    have hpointCoarse := (hwitness cell hcell).1
    have hpointCell := (hwitness cell hcell).2
    have hpointSource : point ∈ terminalSource.shading.union :=
      ((sources.sourceFor parent hparent).coarseSource_subset hpointCoarse).1
    let sourceIndex : Fin terminal.sticky.selected.family.card :=
      Classical.choose hpointSource
    have hpointCarrier :
        point ∈ terminalSource.shading.carrier sourceIndex :=
      Classical.choose_spec hpointSource
    have hpointRefined :
        point ∈ terminal.sticky.refined.carrier sourceIndex := by
      rw [← terminalSource.shading_eq]
      exact hpointCarrier
    rcases terminal.sticky.balanced.fine_cell_nested
        sourceIndex point hpointRefined with
      ⟨nestedParent, _hnestedActive, hnested⟩
    have hcellIndex : wz1PaperGridIndex delta point = cell :=
      (mem_wz1PaperGridCube delta cell point).mp hpointCell
    have hnestedCell : wz1PaperGridCube delta cell ⊆
        wz1PaperGridCube terminal.sqrtRequested.1 nestedParent := by
      simpa [hcellIndex] using hnested
    have hpointNested : point ∈
        wz1PaperGridCube terminal.sqrtRequested.1 nestedParent :=
      hnestedCell hpointCell
    have hpointOwner : point ∈
        wz1PaperGridCube terminal.sqrtRequested.1 parent := by
      rw [(sources.sourceFor parent hparent).coarseSource_eq,
        (sources.sourceFor parent hparent).fullSource_eq] at hpointCoarse
      simpa only [parent, hparent,
        sources.sourceFor_cell parent hparent] using hpointCoarse.1.2
    have hparentEq : nestedParent = parent :=
      ((mem_wz1PaperGridCube terminal.sqrtRequested.1 nestedParent point).mp
        hpointNested).symm.trans
      ((mem_wz1PaperGridCube terminal.sqrtRequested.1 parent point).mp
        hpointOwner)
    rwa [hparentEq] at hnestedCell
  have hcellsNonempty : cells.Nonempty := by
    let parent := Classical.choose residue.selected_nonempty
    have hparent : parent ∈ residue.selected :=
      Classical.choose_spec residue.selected_nonempty
    let data := sources.sourceFor parent hparent
    rcases data.coarseSource_nonempty with ⟨point, hpoint⟩
    have hretained := sources.coarse_source_subset parent hparent hpoint
    have hunionCells := retained.whole_cells.union_eq_activeCells
      source.extremal.delta_pos
    rw [hunionCells] at hretained
    rcases Set.mem_iUnion₂.mp hretained.1 with ⟨cell, hcell, hpointCell⟩
    refine ⟨cell, Finset.mem_filter.mpr ⟨hcell, ?_⟩⟩
    exact ⟨parent, hparent, point, hpoint, hpointCell⟩
  let selectedRegion : Set Point3 :=
    ⋃ cell ∈ cells, wz1PaperGridCube delta cell
  have hregionMeas : MeasurableSet selectedRegion :=
    MeasurableSet.biUnion cells.finite_toSet.countable
      (fun cell _ => wz1PaperGridCube_measurable cell)
  let shading : WZ1PaperTubeShading source.family :=
    { carrier := fun index =>
        retained.shading.carrier index ∩ selectedRegion
      measurable_carrier := fun index =>
        (retained.shading.measurable_carrier index).inter hregionMeas
      subset_body := fun index => Set.inter_subset_left.trans
        (retained.shading.subset_body index) }
  have hsub : PureWZ2PaperIsSubshading shading retained.shading := by
    intro index point hpoint
    exact hpoint.1
  have hregionSubset : selectedRegion ⊆ retained.shading.union := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
    have hinter := retained.whole_cells.inter_activeCell_eq
      source.extremal.delta_pos (hcellsSubset hcell)
    have : point ∈ retained.shading.union ∩ wz1PaperGridCube delta cell := by
      rw [hinter]
      exact hpointCell
    exact this.1
  have hunion : shading.union = selectedRegion := by
    ext point
    constructor
    · rintro ⟨index, hsource, hregion⟩
      exact hregion
    · intro hregion
      rcases hregionSubset hregion with ⟨index, hsource⟩
      exact ⟨index, hsource, hregion⟩
  have hwhole : WZ1PaperIsCubicalShading shading := by
    intro index point hpoint other hother
    have hretainedOther := retained.whole_cells index point hpoint.1 hother
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨cell, hcell, hpointCell⟩
    have hcellEq : wz1PaperGridIndex delta point = cell :=
      (mem_wz1PaperGridCube delta cell point).mp hpointCell
    exact ⟨hretainedOther, Set.mem_iUnion₂.mpr
      ⟨cell, hcell, by
        apply (mem_wz1PaperGridCube delta cell other).mpr
        rw [← hcellEq]
        exact (mem_wz1PaperGridCube delta
          (wz1PaperGridIndex delta point) other).mp hother⟩⟩
  have hcoarseSubset : ∀ parent (hparent : parent ∈ residue.selected),
      (sources.sourceFor parent hparent).coarseSource ⊆ shading.union := by
    intro parent hparent point hpoint
    rw [hunion]
    have hretained := sources.coarse_source_subset parent hparent hpoint
    have hunionCells := retained.whole_cells.union_eq_activeCells
      source.extremal.delta_pos
    rw [hunionCells] at hretained
    rcases Set.mem_iUnion₂.mp hretained.1 with ⟨cell, hcell, hpointCell⟩
    refine Set.mem_iUnion₂.mpr ⟨cell, Finset.mem_filter.mpr ⟨hcell, ?_⟩, hpointCell⟩
    exact ⟨parent, hparent, point, hpoint, hpointCell⟩
  let selectedParents := residue.selected.attach
  let sourceSet
      (parent : {parent // parent ∈ residue.selected}) : Set Point3 :=
    (sources.sourceFor parent.1 parent.2).coarseSource
  let coarseUnion : Set Point3 :=
    ⋃ parent ∈ selectedParents, sourceSet parent
  have hcoarseUnionSubset : coarseUnion ⊆ shading.union := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨parent, hparent, hpointSource⟩
    exact hcoarseSubset parent.1 parent.2 hpointSource
  have hcoarseDisjoint :
      (selectedParents : Set {parent // parent ∈ residue.selected}).PairwiseDisjoint
        sourceSet := by
    intro first hfirst second hsecond hne
    have hvalNe : first.1 ≠ second.1 := by
      intro hval
      exact hne (Subtype.ext hval)
    apply (wz1PaperGridCube_disjoint
      (scale := terminal.sqrtRequested.1) hvalNe).mono
    · intro point hpoint
      change point ∈
        (sources.sourceFor first.1 first.2).coarseSource at hpoint
      rw [(sources.sourceFor first.1 first.2).coarseSource_eq,
        (sources.sourceFor first.1 first.2).fullSource_eq] at hpoint
      simpa only [sources.sourceFor_cell first.1 first.2] using hpoint.1.2
    · intro point hpoint
      change point ∈
        (sources.sourceFor second.1 second.2).coarseSource at hpoint
      rw [(sources.sourceFor second.1 second.2).coarseSource_eq,
        (sources.sourceFor second.1 second.2).fullSource_eq] at hpoint
      simpa only [sources.sourceFor_cell second.1 second.2] using hpoint.1.2
  have hcoarseMeas : ∀ parent ∈ selectedParents,
      MeasurableSet (sourceSet parent) := by
    intro parent _hparent
    exact (sources.sourceFor parent.1 parent.2).coarseSource_measurable
  have hcoarseVolume : volume coarseUnion =
      ∑ parent ∈ selectedParents, volume (sourceSet parent) := by
    dsimp only [coarseUnion]
    exact MeasureTheory.measure_biUnion_finset hcoarseDisjoint hcoarseMeas
  have hparentScaled : ∀ parent (hparent : parent ∈ residue.selected),
      terminal.sticky.balanced.cellMass ≤
        512 * volume (sources.sourceFor parent hparent).coarseSource := by
    intro parent hparent
    let data := sources.sourceFor parent hparent
    calc
      terminal.sticky.balanced.cellMass = volume data.fullSource :=
        data.fullSource_volume.symm
      _ ≤ (data.centers.card : ENNReal) * volume data.coarseSource :=
        data.volume_average
      _ ≤ 512 * volume data.coarseSource := by
        gcongr
        exact_mod_cast data.centers_card
  have hsumScaled :
      (residue.selected.card : ENNReal) *
          terminal.sticky.balanced.cellMass ≤
        512 * volume coarseUnion := by
    rw [hcoarseVolume]
    calc
      (residue.selected.card : ENNReal) *
          terminal.sticky.balanced.cellMass =
        ∑ _parent ∈ selectedParents,
          terminal.sticky.balanced.cellMass := by
            simp [selectedParents, Finset.sum_const]
      _ ≤ ∑ parent ∈ selectedParents,
          512 * volume (sourceSet parent) := by
            apply Finset.sum_le_sum
            intro parent _hparent
            exact hparentScaled parent.1 parent.2
      _ = 512 * ∑ parent ∈ selectedParents,
          volume (sourceSet parent) := by
            rw [Finset.mul_sum]
  have hvolumeFraction : volume retained.shading.union ≤
      512 * volume shading.union := by
    calc
      volume retained.shading.union =
          (residue.selected.card : ENNReal) *
            terminal.sticky.balanced.cellMass := retained.volume_eq
      _ ≤ 512 * volume coarseUnion := hsumScaled
      _ ≤ 512 * volume shading.union := by
        gcongr
  exact ⟨{
    cells := cells
    cells_subset := hcellsSubset
    cells_nonempty := hcellsNonempty
    ownerParent := ownerParent
    owner_mem := hownerMem
    witness := witness
    witness_mem_coarse := fun cell hcell => (hwitness cell hcell).1
    witness_mem_cell := fun cell hcell => (hwitness cell hcell).2
    cell_subset_owner := hcellOwner
    selectedRegion := selectedRegion
    selectedRegion_eq := rfl
    shading := shading
    carrier_eq := fun _ => rfl
    subshading := hsub
    whole_cells := hwhole
    union_eq := hunion
    coarse_source_subset := hcoarseSubset
    volume_fraction := hvolumeFraction
  }⟩

end Kakeya.Assouad
