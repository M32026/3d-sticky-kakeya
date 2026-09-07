import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalSourceBlockMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PaperCubeSliceArea
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperActiveCellLogBound

/-!
# Exact terminal block--parent pair weights

This file records the common refinement of the terminal `sqrt delta` block
partition and the official balanced-parent partition.  Every weight is the
volume of the actual terminal source carrier inside both regions; no complete
parent cube is substituted for that carrier.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Actual terminal-source volume in one block and one official balanced
parent. -/
def pureWZ2TerminalBlockParentWeight
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (block : ℤ) (parent : ℤ × ℤ × ℤ) : ENNReal :=
  volume ((terminalSourceBlockShading prepared block).union ∩
    wz1PaperGridCube terminal.sqrtRequested.1 parent)

/-- For one source block, its actual carrier is exactly partitioned by the
official balanced parents. -/
theorem pureWZ2TerminalBlockParentWeight_sum_parent
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (block : ℤ) :
    (∑ parent ∈ terminal.sticky.balanced.activeCells,
        pureWZ2TerminalBlockParentWeight prepared block parent) =
      volume (terminalSourceBlockShading prepared block).union := by
  let blockSet := (terminalSourceBlockShading prepared block).union
  have hsource : blockSet ⊆ terminalSource.shading.union := by
    intro point hpoint
    rcases hpoint with ⟨index, hcarrier⟩
    exact ⟨index, hcarrier.1⟩
  have hpartition : blockSet =
      ⋃ parent ∈ terminal.sticky.balanced.activeCells,
        blockSet ∩ wz1PaperGridCube terminal.sqrtRequested.1 parent := by
    apply Set.Subset.antisymm
    · intro point hpoint
      have hrefined : point ∈ terminal.sticky.refined.union := by
        rw [← terminalSource.shading_eq]
        exact hsource hpoint
      rw [terminal.sticky.balanced.toWZ1PaperBalancedCoverData.fine_cell_partition]
        at hrefined
      rcases Set.mem_iUnion₂.mp hrefined with
        ⟨parent, hparent, _hrefined, hpointParent⟩
      exact Set.mem_iUnion₂.mpr ⟨parent, hparent, hpoint, hpointParent⟩
    · intro point hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨_parent, _hparent, hpointBlock, _hpointParent⟩
      exact hpointBlock
  change (∑ parent ∈ terminal.sticky.balanced.activeCells,
      volume (blockSet ∩
        wz1PaperGridCube terminal.sqrtRequested.1 parent)) = volume blockSet
  have hdisjoint :
      (terminal.sticky.balanced.activeCells : Set (ℤ × ℤ × ℤ)).PairwiseDisjoint
        (fun parent => blockSet ∩
          wz1PaperGridCube terminal.sqrtRequested.1 parent) := by
    intro first _ second _ hne
    exact (wz1PaperGridCube_disjoint hne).mono
      Set.inter_subset_right Set.inter_subset_right
  have hmeasurable : ∀ parent ∈ terminal.sticky.balanced.activeCells,
      MeasurableSet (blockSet ∩
        wz1PaperGridCube terminal.sqrtRequested.1 parent) := by
    intro parent _
    exact (measurableSet_shading_union
      (terminalSourceBlockShading prepared block)).inter
        (wz1PaperGridCube_measurable parent)
  calc
    (∑ parent ∈ terminal.sticky.balanced.activeCells,
      volume (blockSet ∩
        wz1PaperGridCube terminal.sqrtRequested.1 parent)) =
        volume (⋃ parent ∈ terminal.sticky.balanced.activeCells,
          blockSet ∩ wz1PaperGridCube terminal.sqrtRequested.1 parent) :=
      (MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable).symm
    _ = volume blockSet := congrArg volume hpartition.symm

/-- Finite additivity over any selected official parent set inside one source
block. -/
theorem pureWZ2TerminalBlockParentWeight_sum_selected
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (block : ℤ) (selected : Finset (ℤ × ℤ × ℤ)) :
    (∑ parent ∈ selected,
        pureWZ2TerminalBlockParentWeight prepared block parent) =
      volume ((terminalSourceBlockShading prepared block).union ∩
        ⋃ parent ∈ selected,
          wz1PaperGridCube terminal.sqrtRequested.1 parent) := by
  let blockSet := (terminalSourceBlockShading prepared block).union
  let piece : (ℤ × ℤ × ℤ) → Set Point3 := fun parent =>
    blockSet ∩ wz1PaperGridCube terminal.sqrtRequested.1 parent
  have hdisjoint : (selected : Set (ℤ × ℤ × ℤ)).PairwiseDisjoint piece := by
    intro first _ second _ hne
    exact (wz1PaperGridCube_disjoint hne).mono
      Set.inter_subset_right Set.inter_subset_right
  have hmeas : ∀ parent ∈ selected, MeasurableSet (piece parent) := by
    intro parent _
    exact (measurableSet_shading_union
      (terminalSourceBlockShading prepared block)).inter
        (wz1PaperGridCube_measurable parent)
  have hunion : (⋃ parent ∈ selected, piece parent) =
      blockSet ∩ ⋃ parent ∈ selected,
        wz1PaperGridCube terminal.sqrtRequested.1 parent := by
    ext point
    simp [piece]
  rw [← hunion, MeasureTheory.measure_biUnion_finset hdisjoint hmeas]
  rfl

/-- For one official parent, summing over the disjoint terminal blocks
recovers its exact balanced fine mass. -/
theorem pureWZ2TerminalBlockParentWeight_sum_block
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (parent : ℤ × ℤ × ℤ)
    (hparent : parent ∈ terminal.sticky.balanced.activeCells) :
    (∑ block ∈ pureWZ2TerminalBlocks prepared,
        pureWZ2TerminalBlockParentWeight prepared block parent) =
      terminal.sticky.balanced.cellMass := by
  let parentCube := wz1PaperGridCube terminal.sqrtRequested.1 parent
  have hsourceBlocks : terminalSource.shading.union =
      ⋃ block ∈ pureWZ2TerminalBlocks prepared,
        (terminalSourceBlockShading prepared block).union := by
    calc
      terminalSource.shading.union = prepared.shadow.union :=
        prepared.shadow_union.symm
      _ = ⋃ block ∈ pureWZ2TerminalBlocks prepared,
          (pureWZ2TerminalBlockShading prepared block).union :=
        pureWZ2TerminalBlock_union_partition prepared
      _ = ⋃ block ∈ pureWZ2TerminalBlocks prepared,
          (terminalSourceBlockShading prepared block).union := by
        apply Set.iUnion_congr
        intro block
        apply Set.iUnion_congr
        intro _hblock
        exact terminalSourceBlockShading_union_eq prepared block |>.symm
  have hpartition : terminalSource.shading.union ∩ parentCube =
      ⋃ block ∈ pureWZ2TerminalBlocks prepared,
        (terminalSourceBlockShading prepared block).union ∩ parentCube := by
    apply Set.Subset.antisymm
    · rintro point ⟨hsource, hpointParent⟩
      rw [hsourceBlocks] at hsource
      rcases Set.mem_iUnion₂.mp hsource with
        ⟨block, hblock, hpointBlock⟩
      exact Set.mem_iUnion₂.mpr ⟨block, hblock, hpointBlock, hpointParent⟩
    · intro point hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨_block, _hblock, hpointBlock, hpointParent⟩
      exact ⟨by
        rcases hpointBlock with ⟨index, hcarrier⟩
        exact ⟨index, hcarrier.1⟩, hpointParent⟩
  have hsum :
      (∑ block ∈ pureWZ2TerminalBlocks prepared,
          pureWZ2TerminalBlockParentWeight prepared block parent) =
        volume (terminalSource.shading.union ∩ parentCube) := by
    rw [hpartition, MeasureTheory.measure_biUnion_finset]
    · rfl
    · intro first hfirst second hsecond hne
      change Disjoint
        ((terminalSourceBlockShading prepared first).union ∩ parentCube)
        ((terminalSourceBlockShading prepared second).union ∩ parentCube)
      have hd : Disjoint
          (pureWZ2TerminalBlockShading prepared first).union
          (pureWZ2TerminalBlockShading prepared second).union :=
        pureWZ2TerminalBlock_union_pairwise_disjoint prepared
          hfirst hsecond hne
      rw [terminalSourceBlockShading_union_eq prepared first,
        terminalSourceBlockShading_union_eq prepared second]
      exact hd.mono Set.inter_subset_left Set.inter_subset_left
    · intro block _
      exact (measurableSet_shading_union
        (terminalSourceBlockShading prepared block)).inter
          (wz1PaperGridCube_measurable parent)
  rw [hsum]
  change volume (terminalSource.shading.union ∩
      wz1PaperGridCube terminal.sqrtRequested.1 parent) = _
  rw [terminalSource.shading_eq]
  exact terminal.sticky.balanced.fine_cell_mass parent hparent

/-- The double sum of actual block--parent weights is the complete terminal
source volume. -/
theorem pureWZ2TerminalBlockParentWeight_sum
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) :
    (∑ block ∈ pureWZ2TerminalBlocks prepared,
      ∑ parent ∈ terminal.sticky.balanced.activeCells,
        pureWZ2TerminalBlockParentWeight prepared block parent) =
      volume terminalSource.shading.union := by
  calc
    (∑ block ∈ pureWZ2TerminalBlocks prepared,
      ∑ parent ∈ terminal.sticky.balanced.activeCells,
        pureWZ2TerminalBlockParentWeight prepared block parent) =
        ∑ block ∈ pureWZ2TerminalBlocks prepared,
          volume (terminalSourceBlockShading prepared block).union := by
      apply Finset.sum_congr rfl
      intro block _
      exact pureWZ2TerminalBlockParentWeight_sum_parent prepared block
    _ = ∑ block ∈ pureWZ2TerminalBlocks prepared,
          volume (pureWZ2TerminalBlockShading prepared block).union := by
      apply Finset.sum_congr rfl
      intro block _
      rw [terminalSourceBlockShading_union_eq prepared block]
    _ = volume prepared.shadow.union :=
      (pureWZ2TerminalBlock_volume_eq_sum prepared).symm
    _ = volume terminalSource.shading.union := by
      rw [prepared.shadow_union]

/-- A positive block--parent intersection can occur only in the parent's own
`sqrt delta` height block or one of its two neighbours. -/
theorem pureWZ2TerminalBlock_mem_parent_neighbours_of_weight_pos
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    {block : ℤ} {parent : ℤ × ℤ × ℤ}
    (hweight : 0 < pureWZ2TerminalBlockParentWeight prepared block parent) :
    block ∈ Finset.Icc (parent.2.2 - 1) (parent.2.2 + 1) := by
  have hset : ((terminalSourceBlockShading prepared block).union ∩
      wz1PaperGridCube terminal.sqrtRequested.1 parent).Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro hempty
    have hzero : pureWZ2TerminalBlockParentWeight prepared block parent = 0 := by
      simp [pureWZ2TerminalBlockParentWeight, hempty]
    exact hweight.ne' hzero
  rcases hset with ⟨point, hpointBlock, hpointParent⟩
  rcases hpointBlock with ⟨index, _hsource, hpointRegion⟩
  rcases Set.mem_iUnion₂.mp hpointRegion with
    ⟨cell, hcell, hpointCell⟩
  have hblockLabel : pureWZ2SourceCarrierBlockIndex delta cell = block :=
    (Finset.mem_filter.mp hcell).2
  have hcenterWindow :=
    pureWZ2SourceCarrierBlockIndex_spec source.extremal.delta_pos cell
  rw [hblockLabel] at hcenterWindow
  have hcenterWindow' :
      (block : ℝ) * Real.sqrt delta ≤
          (wz1Lemma23CellCenter delta cell) (2 : Fin 3) ∧
        (wz1Lemma23CellCenter delta cell) (2 : Fin 3) <
          ((block : ℝ) + 1) * Real.sqrt delta := by
    constructor
    · simpa [pureWZ2SourceCarrierBlockLeft, wz1Lemma23SnappedPoint]
        using hcenterWindow.1
    · have h := hcenterWindow.2
      simp only [pureWZ2SourceCarrierBlockLeft, wz1Lemma23SnappedPoint] at h
      nlinarith
  have hpointCenter :=
    ((wz1_lemma23_snapped_cell_geometry delta source.extremal.delta_pos
      source.extremal.delta_le_one).2.1 cell point hpointCell).1 (2 : Fin 3)
  rw [abs_le] at hpointCenter
  have hparentBounds := hpointParent
  rw [wz1PaperGridCube_eq_Ico terminal.sticky.coarse_extremal.delta_pos parent,
    terminal.sqrtRequested_eq] at hparentBounds
  have hparentLower : (parent.2.2 : ℝ) * Real.sqrt delta ≤
      point (2 : Fin 3) := hparentBounds.2.2.2.2.1
  have hparentUpper : point (2 : Fin 3) <
      ((parent.2.2 : ℝ) + 1) * Real.sqrt delta :=
    hparentBounds.2.2.2.2.2
  have hrootPos : 0 < Real.sqrt delta :=
    Real.sqrt_pos.mpr source.extremal.delta_pos
  have hdeltaRoot : delta ≤ Real.sqrt delta := by
    nlinarith [Real.sq_sqrt source.extremal.delta_pos.le,
      source.extremal.delta_le_one, Real.sqrt_nonneg delta]
  rw [Finset.mem_Icc]
  constructor
  · by_contra hnot
    have hblockInt : block ≤ parent.2.2 - 2 := by omega
    have hblockReal : (block : ℝ) ≤ (parent.2.2 : ℝ) - 2 := by
      exact_mod_cast hblockInt
    nlinarith [hcenterWindow'.2, hpointCenter.2, hparentLower]
  · by_contra hnot
    have hblockInt : parent.2.2 + 2 ≤ block := by omega
    have hblockReal : (parent.2.2 : ℝ) + 2 ≤ (block : ℝ) := by
      exact_mod_cast hblockInt
    nlinarith [hcenterWindow'.1, hpointCenter.1, hparentUpper]

/-- Positive block--parent pairs.  Filtering before dyadic binning avoids the
spurious `number of blocks` factor from zero entries. -/
def pureWZ2TerminalPositiveBlockParentPairs
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) :
    Finset (ℤ × (ℤ × ℤ × ℤ)) :=
  ((pureWZ2TerminalBlocks prepared).product
      terminal.sticky.balanced.activeCells).filter fun pair =>
    0 < pureWZ2TerminalBlockParentWeight prepared pair.1 pair.2

/-- Every official parent contributes positive mass to at most three terminal
blocks. -/
theorem pureWZ2TerminalPositiveBlockParentPairs_parent_fiber_card
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (parent : ℤ × ℤ × ℤ) :
    ((pureWZ2TerminalPositiveBlockParentPairs prepared).filter fun pair =>
        pair.2 = parent).card ≤ 3 := by
  let fiber := (pureWZ2TerminalPositiveBlockParentPairs prepared).filter
    fun pair => pair.2 = parent
  have hinjective : Set.InjOn
      (fun pair : ℤ × (ℤ × ℤ × ℤ) => pair.1)
      (↑fiber : Set (ℤ × (ℤ × ℤ × ℤ))) := by
    intro first hfirst second hsecond heq
    have hfirstParent : first.2 = parent := (Finset.mem_filter.mp hfirst).2
    have hsecondParent : second.2 = parent := (Finset.mem_filter.mp hsecond).2
    exact Prod.ext heq (hfirstParent.trans hsecondParent.symm)
  have hsubset : fiber.image Prod.fst ⊆
      Finset.Icc (parent.2.2 - 1) (parent.2.2 + 1) := by
    intro block hblock
    rcases Finset.mem_image.mp hblock with ⟨pair, hpair, rfl⟩
    have hparentEq : pair.2 = parent := (Finset.mem_filter.mp hpair).2
    have hpositive : 0 <
        pureWZ2TerminalBlockParentWeight prepared pair.1 pair.2 :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hpair).1).2
    simpa [hparentEq] using
      pureWZ2TerminalBlock_mem_parent_neighbours_of_weight_pos
        prepared hpositive
  calc
    fiber.card = (fiber.image Prod.fst).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ (Finset.Icc (parent.2.2 - 1) (parent.2.2 + 1)).card :=
      Finset.card_le_card hsubset
    _ = 3 := by simp [Int.card_Icc] <;> omega

/-- Removing zero block--parent pairs does not change the total weight. -/
theorem pureWZ2TerminalPositiveBlockParentPairs_sum
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) :
    (∑ pair ∈ pureWZ2TerminalPositiveBlockParentPairs prepared,
        pureWZ2TerminalBlockParentWeight prepared pair.1 pair.2) =
      volume terminalSource.shading.union := by
  let pairs := (pureWZ2TerminalBlocks prepared).product
    terminal.sticky.balanced.activeCells
  let weight : (ℤ × (ℤ × ℤ × ℤ)) → ENNReal := fun pair =>
    pureWZ2TerminalBlockParentWeight prepared pair.1 pair.2
  have hfilter : pairs.filter (fun pair => 0 < weight pair) =
      pairs.filter (fun pair => weight pair ≠ 0) := by
    ext pair
    simp [pos_iff_ne_zero]
  calc
    (∑ pair ∈ pureWZ2TerminalPositiveBlockParentPairs prepared,
        pureWZ2TerminalBlockParentWeight prepared pair.1 pair.2) =
        ∑ pair ∈ pairs.filter (fun pair => weight pair ≠ 0), weight pair := by
      rw [← hfilter]
      rfl
    _ = ∑ pair ∈ pairs, weight pair := Finset.sum_filter_ne_zero pairs
    _ = ∑ block ∈ pureWZ2TerminalBlocks prepared,
        ∑ parent ∈ terminal.sticky.balanced.activeCells,
          pureWZ2TerminalBlockParentWeight prepared block parent := by
      simpa [pairs, weight] using
        Finset.sum_product (pureWZ2TerminalBlocks prepared)
          terminal.sticky.balanced.activeCells
          (fun pair => pureWZ2TerminalBlockParentWeight prepared
            pair.1 pair.2)
    _ = volume terminalSource.shading.union :=
      pureWZ2TerminalBlockParentWeight_sum prepared

/-- The positive pair support is at most three times the number of official
balanced parents. -/
theorem pureWZ2TerminalPositiveBlockParentPairs_card
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) :
    (pureWZ2TerminalPositiveBlockParentPairs prepared).card ≤
      3 * terminal.sticky.balanced.activeCells.card := by
  apply Finset.card_le_mul_card_image_of_maps_to
    (f := fun pair : ℤ × (ℤ × ℤ × ℤ) => pair.2)
  · intro pair hpair
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hpair).1).2
  · intro parent _
    exact pureWZ2TerminalPositiveBlockParentPairs_parent_fiber_card
      prepared parent

/-- One global dyadic class of positive block--parent intersection masses.
The explicit `cellMass_le_pairFloor` field is the scale-sensitive gain missing
from parent regularization performed only after selecting one block. -/
structure PureWZ2TerminalBlockParentPairWeightClassData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) where
  bins : ℕ
  bins_eq : bins = Nat.log 2
    (2 * (pureWZ2TerminalPositiveBlockParentPairs prepared).card) + 1
  selectedPairs : Finset (ℤ × (ℤ × ℤ × ℤ))
  selectedPairs_nonempty : selectedPairs.Nonempty
  selectedPairs_subset : selectedPairs ⊆
    pureWZ2TerminalPositiveBlockParentPairs prepared
  pairFloor : ENNReal
  pairFloor_pos : 0 < pairFloor
  pairFloor_ne_top : pairFloor ≠ ⊤
  weight_band : ∀ pair ∈ selectedPairs,
    pairFloor ≤ pureWZ2TerminalBlockParentWeight prepared pair.1 pair.2 ∧
      pureWZ2TerminalBlockParentWeight prepared pair.1 pair.2 ≤ 2 * pairFloor
  selectedWeight : ENNReal :=
    ∑ pair ∈ selectedPairs,
      pureWZ2TerminalBlockParentWeight prepared pair.1 pair.2
  selectedWeight_eq : selectedWeight =
    ∑ pair ∈ selectedPairs,
      pureWZ2TerminalBlockParentWeight prepared pair.1 pair.2
  selectedWeight_pos : 0 < selectedWeight
  retained_volume : volume terminalSource.shading.union ≤
    2 * bins * selectedWeight
  cellMass_le_pairFloor :
    terminal.sticky.balanced.cellMass ≤ 12 * pairFloor

/-- The global block--parent dyadic class pays only one physical logarithm at
the terminal parent scale. -/
theorem PureWZ2TerminalBlockParentPairWeightClassData.bins_le_logEnvelope
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared) :
    (pairClass.bins : ENNReal) ≤
      4 * ENNReal.ofReal
        (wz2PaperBoundaryLogCoefficient *
          (1 + Real.log terminal.sqrtRequested.1⁻¹)) := by
  have hactive : terminal.sticky.balanced.activeCells ⊆
      wz1PaperActiveCells terminal.sticky.croppedCoarseShading
        terminal.sticky.coarse_extremal.delta_pos := by
    intro cell hcell
    let point : Point3 := cellCorner terminal.sqrtRequested.1 cell
    have hpointCell : point ∈
        wz1PaperGridCube terminal.sqrtRequested.1 cell :=
      cellCorner_mem_gridCube
        terminal.sticky.coarse_extremal.delta_pos cell
    have hpointUnion : point ∈
        terminal.sticky.croppedCoarseShading.union := by
      rw [terminal.sticky.balanced.coarse_union_eq]
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCell⟩
    rcases hpointUnion with ⟨index, hpointCarrier⟩
    have hpointBody := terminal.sticky.croppedCoarseShading.subset_body
      index hpointCarrier
    have hwindow : wz1PaperGridIndex terminal.sqrtRequested.1 point ∈
        wz1PaperGridIndicesInWindow terminal.sqrtRequested.1
          terminal.sticky.coarse_extremal.delta_pos :=
      paper_point_gridIndex_in_window
        terminal.sticky.coarse_extremal.delta_pos hpointBody.2
    have hindex : wz1PaperGridIndex terminal.sqrtRequested.1 point = cell :=
      (mem_wz1PaperGridCube terminal.sqrtRequested.1 cell point).mp
        hpointCell
    rw [hindex] at hwindow
    rw [mem_wz1PaperActiveCells]
    exact ⟨hwindow, ⟨point, ⟨index, hpointCarrier⟩, hpointCell⟩⟩
  have hactiveNonempty :
      terminal.sticky.balanced.activeCells.Nonempty := by
    rcases pairClass.selectedPairs_nonempty with ⟨pair, hpair⟩
    have hpositive := pairClass.selectedPairs_subset hpair
    exact ⟨pair.2,
      (Finset.mem_product.mp (Finset.mem_filter.mp hpositive).1).2⟩
  let activeCount := (wz1PaperActiveCells
    terminal.sticky.croppedCoarseShading
      terminal.sticky.coarse_extremal.delta_pos).card
  have hactiveCountNonempty : 0 < activeCount := by
    apply Finset.card_pos.mpr
    exact hactiveNonempty.mono hactive
  have hpairsCard :
      (pureWZ2TerminalPositiveBlockParentPairs prepared).card ≤
        3 * activeCount := by
    exact (pureWZ2TerminalPositiveBlockParentPairs_card prepared).trans
      (Nat.mul_le_mul_left 3 (Finset.card_le_card hactive))
  have harg :
      2 * (pureWZ2TerminalPositiveBlockParentPairs prepared).card ≤
        8 * activeCount := by omega
  have hlogNat : pairClass.bins ≤ Nat.log 2 activeCount + 4 := by
    rw [pairClass.bins_eq]
    calc
      Nat.log 2
            (2 * (pureWZ2TerminalPositiveBlockParentPairs prepared).card) + 1 ≤
          Nat.log 2 (8 * activeCount) + 1 := by
        exact Nat.add_le_add_right (Nat.log_mono_right harg) 1
      _ = Nat.log 2 activeCount + 4 := by
        rw [show 8 * activeCount = activeCount * 2 * 2 * 2 by omega]
        rw [Nat.log_mul_base (by omega)
          (Nat.mul_ne_zero
            (Nat.mul_ne_zero hactiveCountNonempty.ne' (by omega)) (by omega)),
          Nat.log_mul_base (by omega)
            (Nat.mul_ne_zero hactiveCountNonempty.ne' (by omega)),
          Nat.log_mul_base (by omega) hactiveCountNonempty.ne']
  let envelope := ENNReal.ofReal
    (wz2PaperBoundaryLogCoefficient *
      (1 + Real.log terminal.sqrtRequested.1⁻¹))
  have hphysical : ((Nat.log 2 activeCount + 1 : ℕ) : ENNReal) ≤
      envelope := by
    dsimp only [activeCount, envelope]
    exact wz2_paper_active_cell_log_bound_ennreal
      terminal.sticky.coarse_extremal.delta_pos
      terminal.sticky.coarse_extremal.delta_le_one
      terminal.sticky.croppedCoarseShading
  have hone : (1 : ENNReal) ≤ envelope := by
    exact (show (1 : ENNReal) ≤
      ((Nat.log 2 activeCount + 1 : ℕ) : ENNReal) by
        exact_mod_cast (show 1 ≤ Nat.log 2 activeCount + 1 by omega)).trans
          hphysical
  have hcast : (pairClass.bins : ENNReal) ≤
      ((Nat.log 2 activeCount + 1 : ℕ) : ENNReal) + 3 := by
    exact_mod_cast hlogNat
  calc
    (pairClass.bins : ENNReal) ≤
        ((Nat.log 2 activeCount + 1 : ℕ) : ENNReal) + 3 := hcast
    _ ≤ envelope + 3 * envelope := by
      apply add_le_add hphysical
      simpa using (mul_le_mul_left' hone (3 : ENNReal))
    _ = 4 * envelope := by ring

/-- Dyadically regularize only the positive block--parent support.  The
three-block incidence bound makes the selected pair floor comparable to the
balanced cell mass, without filling any parent cube. -/
theorem pureWZ2Terminal_regularizeBlockParentPairs
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) :
    Nonempty (PureWZ2TerminalBlockParentPairWeightClassData prepared) := by
  let pairs := pureWZ2TerminalPositiveBlockParentPairs prepared
  let pairType := {pair // pair ∈ pairs}
  let weight : pairType → ENNReal := fun pair =>
    pureWZ2TerminalBlockParentWeight prepared pair.1.1 pair.1.2
  let total := volume terminalSource.shading.union
  have htotal : total = ∑ pair : pairType, weight pair := by
    calc
      total = ∑ pair ∈ pairs,
          pureWZ2TerminalBlockParentWeight prepared pair.1 pair.2 :=
        (pureWZ2TerminalPositiveBlockParentPairs_sum prepared).symm
      _ = ∑ pair : pairType, weight pair := by
        simpa [pairType, weight] using
          (Finset.sum_attach pairs
            (fun pair => pureWZ2TerminalBlockParentWeight prepared
              pair.1 pair.2)).symm
  have htotalPos : 0 < total := by
    dsimp only [total]
    exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos source.extremal.delta_pos _)).trans_le
        terminalSource.volume_lower
  have htotalTop : total ≠ ⊤ := by
    have hball : terminalSource.shading.union ⊆
        Metric.closedBall (0 : Point3) 2 := by
      intro point hpoint
      have hnorm := norm_le_two_of_mem_paperShading hpoint
      simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
    exact ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
      (measure_mono hball)
  rcases ennreal_dyadic_bin weight total htotal htotalTop htotalPos with
    ⟨bins, selected, hbins, hselected, hretained, hthreshold,
      pairFloor, hpairFloor, hweightBand⟩
  let selectedPairs := selected.image Subtype.val
  have hselectedInjective : Set.InjOn
      (Subtype.val : pairType → (ℤ × (ℤ × ℤ × ℤ))) selected :=
    fun _ _ _ _ h => Subtype.ext h
  have hselectedSubset : selectedPairs ⊆ pairs := by
    intro pair hpair
    rcases Finset.mem_image.mp hpair with ⟨pairIndex, _hindex, rfl⟩
    exact pairIndex.property
  have hselectedSum :
      (∑ pair ∈ selectedPairs,
          pureWZ2TerminalBlockParentWeight prepared pair.1 pair.2) =
        ∑ pair ∈ selected, weight pair := by
    exact Finset.sum_image hselectedInjective
  have hretained' : total ≤ 2 * bins *
      ∑ pair ∈ selectedPairs,
        pureWZ2TerminalBlockParentWeight prepared pair.1 pair.2 := by
    rw [hselectedSum]
    have htwo : total ≤ 2 * ((∑ pair ∈ selected, weight pair) * bins) := by
      calc
        total = total / 2 + total / 2 := (ENNReal.add_halves total).symm
        _ ≤ (∑ pair ∈ selected, weight pair) * bins +
            (∑ pair ∈ selected, weight pair) * bins :=
          add_le_add hretained hretained
        _ = 2 * ((∑ pair ∈ selected, weight pair) * bins) := by ring
    simpa [mul_comm, mul_left_comm, mul_assoc] using htwo
  let selectedPair : pairType := Classical.choose hselected
  have hselectedPair : selectedPair ∈ selected :=
    Classical.choose_spec hselected
  have hselectedWeightPos : 0 <
      ∑ pair ∈ selectedPairs,
        pureWZ2TerminalBlockParentWeight prepared pair.1 pair.2 := by
    have hpositive : 0 < weight selectedPair :=
      hpairFloor.trans_le (hweightBand selectedPair hselectedPair).1
    rw [hselectedSum]
    exact hpositive.trans_le
      (Finset.single_le_sum (fun _ _ => bot_le) hselectedPair)
  have hpairsCard : pairs.card ≤
      3 * terminal.sticky.balanced.activeCells.card :=
    pureWZ2TerminalPositiveBlockParentPairs_card prepared
  have hpairsNonempty : pairs.Nonempty :=
    ⟨selectedPair.1, selectedPair.property⟩
  have hactivePos : 0 < terminal.sticky.balanced.activeCells.card := by
    apply Finset.card_pos.mpr
    have hproduct := (Finset.mem_filter.mp selectedPair.property).1
    exact ⟨selectedPair.1.2, (Finset.mem_product.mp hproduct).2⟩
  have hpairsPos : 0 < pairs.card := Finset.card_pos.mpr hpairsNonempty
  have hdenomZero : (2 * (pairs.card : ENNReal)) ≠ 0 := by
    norm_cast
    omega
  have hdenomTop : (2 * (pairs.card : ENNReal)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)
  have hfloorBound : terminal.sticky.balanced.cellMass ≤ 12 * pairFloor := by
    have hthresholdPair : total / (2 * (pairs.card : ENNReal)) ≤
        weight selectedPair := by
      simpa [pairType, Fintype.card_subtype] using
        hthreshold selectedPair hselectedPair
    have hpairUpper := (hweightBand selectedPair hselectedPair).2
    have htotalLe : total ≤ (2 * pairFloor) *
        (2 * (pairs.card : ENNReal)) :=
      (ENNReal.div_le_iff hdenomZero hdenomTop).mp
        (hthresholdPair.trans hpairUpper)
    have hpairsCardENN : (pairs.card : ENNReal) ≤
        3 * (terminal.sticky.balanced.activeCells.card : ENNReal) := by
      exact_mod_cast hpairsCard
    have hsourceVolume : total =
        (terminal.sticky.balanced.activeCells.card : ENNReal) *
          terminal.sticky.balanced.cellMass := by
      dsimp only [total]
      rw [terminalSource.shading_eq]
      exact terminal.sticky.balanced.toWZ1PaperBalancedCoverData.fine_union_volume
    have hscaled :
        (terminal.sticky.balanced.activeCells.card : ENNReal) *
            terminal.sticky.balanced.cellMass ≤
          (terminal.sticky.balanced.activeCells.card : ENNReal) *
            (12 * pairFloor) := by
      rw [← hsourceVolume]
      calc
        total ≤ (2 * pairFloor) * (2 * (pairs.card : ENNReal)) := htotalLe
        _ ≤ (2 * pairFloor) *
            (2 * (3 *
              (terminal.sticky.balanced.activeCells.card : ENNReal))) := by
          gcongr
        _ = (terminal.sticky.balanced.activeCells.card : ENNReal) *
            (12 * pairFloor) := by ring
    have hactiveZero :
        (terminal.sticky.balanced.activeCells.card : ENNReal) ≠ 0 := by
      exact_mod_cast hactivePos.ne'
    exact (ENNReal.mul_le_mul_iff_right hactiveZero
      (ENNReal.natCast_ne_top _)).mp hscaled
  have hpairFloorTop : pairFloor ≠ ⊤ := by
    have hweightTop : weight selectedPair ≠ ⊤ := by
      apply ne_top_of_le_ne_top htotalTop
      rw [htotal]
      exact Finset.single_le_sum (fun _ _ => bot_le)
        (Finset.mem_univ selectedPair)
    exact ne_top_of_le_ne_top hweightTop
      (hweightBand selectedPair hselectedPair).1
  exact ⟨{
    bins := bins
    bins_eq := by
      simpa [pairType, Fintype.card_subtype, pairs] using hbins
    selectedPairs := selectedPairs
    selectedPairs_nonempty := hselected.image _
    selectedPairs_subset := hselectedSubset
    pairFloor := pairFloor
    pairFloor_pos := hpairFloor
    pairFloor_ne_top := hpairFloorTop
    weight_band := by
      intro pair hpair
      rcases Finset.mem_image.mp hpair with
        ⟨pairIndex, hpairIndex, heq⟩
      subst pair
      simpa [weight] using hweightBand pairIndex hpairIndex
    selectedWeight := ∑ pair ∈ selectedPairs,
      pureWZ2TerminalBlockParentWeight prepared pair.1 pair.2
    selectedWeight_eq := rfl
    selectedWeight_pos := hselectedWeightPos
    retained_volume := by simpa [total] using hretained'
    cellMass_le_pairFloor := hfloorBound
  }⟩

end Kakeya.Assouad

end
