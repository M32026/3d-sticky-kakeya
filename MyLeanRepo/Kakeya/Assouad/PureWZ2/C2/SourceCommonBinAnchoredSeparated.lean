import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinAnchoredEligible
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CommonBinStandardParentWeightedSelection

/-!
# Anchored separated common-bin graph blocks
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

private theorem anchored_fixedCommonBinLabel_cellCenter_eq
    {side : ℝ} (hside : 0 < side) (slope : ℝ → ℝ)
    (referenceHeight : ℝ) (parent : CommonBinStandardParent) :
    pureWZ2FixedCommonBinLabel slope referenceHeight side
        (pureWZ2PaperCellCenter side parent) =
      parent.1 + Int.floor ((1 / 2 : ℝ) +
        slope referenceHeight * ((parent.2.1 : ℝ) + 1 / 2)) := by
  unfold pureWZ2FixedCommonBinLabel
  have hformula :
      inner ℝ (pureWZ2PaperCellCenter side parent)
          (globalGrainDirection (slope referenceHeight)) / side =
        (parent.1 : ℝ) + ((1 / 2 : ℝ) +
          slope referenceHeight * ((parent.2.1 : ℝ) + 1 / 2)) := by
    simp [pureWZ2PaperCellCenter, cellCorner,
      wz1PaperGridCubeTranslation, point3, globalGrainDirection,
      PiLp.inner_apply, Fin.sum_univ_succ]
    field_simp [hside.ne']
    ring
  rw [hformula, Int.floor_intCast_add]

namespace PureWZ2AnchoredIntegratedCommonBinReceipt

variable
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈
      selected.standardSqrtSlabIndices}}
    {data : PureWZ2AnchoredPreBinRhoHeightRegularizedData selected heightIndex}
    {B₀ threshold : ENNReal} {K : ℕ}
    (block : PureWZ2AnchoredIntegratedCommonBinReceipt data B₀ threshold K)

def cells : Finset (ℤ × ℤ × ℤ) := block.envelope.cells

def graphEnvelope : Set Point3 :=
  data.fixedBinWholeCellEnvelope block.referenceHeight block.bin

def graphSupply : ENNReal := volume block.graphEnvelope

def standardParents : Finset CommonBinStandardParent :=
  block.cells.image selected.standardSecondParent

def standardParentCells
    (parent : CommonBinStandardParent) : Finset (ℤ × ℤ × ℤ) :=
  block.cells.filter fun cell =>
    selected.standardSecondParent cell = parent

def standardParentWeight (parent : CommonBinStandardParent) : ENNReal :=
  (block.standardParentCells parent).card *
    volume (wz1PaperGridCube rhoRequested.1 (0, 0, 0))

theorem cells_nonempty (hK : 0 < K) : block.cells.Nonempty := by
  by_contra hempty
  have hzero : volume block.graphEnvelope = 0 := by
    rw [graphEnvelope, block.envelope.envelope_volume,
      show block.envelope.cells = block.cells by rfl,
      Finset.not_nonempty_iff_eq_empty.mp hempty]
    simp
  have hgraph := block.graph_lower
  change (K : ENNReal) * fine.balanced.cellMass ≤
    20 * (data.logarithmicCost : ENNReal) * volume block.graphEnvelope
    at hgraph
  rw [hzero] at hgraph
  simp only [mul_zero] at hgraph
  have hcellMassPos := fine.balanced.cellMass_pos
  have hKPos : 0 < (K : ENNReal) := by exact_mod_cast hK
  exact (not_le_of_gt (ENNReal.mul_pos hKPos.ne' hcellMassPos.ne'))
    hgraph

theorem standardParents_nonempty (hK : 0 < K) :
    block.standardParents.Nonempty :=
  (block.cells_nonempty hK).image selected.standardSecondParent

theorem cells_card_eq_sum_standardParentCells :
    block.cells.card =
      ∑ parent ∈ block.standardParents,
        (block.standardParentCells parent).card := by
  have hmaps : Set.MapsTo selected.standardSecondParent
      (block.cells : Set (ℤ × ℤ × ℤ))
      (block.standardParents : Set CommonBinStandardParent) := by
    intro cell hcell
    exact Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
  simpa [standardParentCells] using
    Finset.card_eq_sum_card_fiberwise hmaps

theorem sum_standardParentWeight_eq_graphSupply :
    (∑ parent ∈ block.standardParents,
      block.standardParentWeight parent) = block.graphSupply := by
  have hcount :
      (∑ parent ∈ block.standardParents,
        ((block.standardParentCells parent).card : ENNReal)) =
          (block.cells.card : ENNReal) := by
    exact_mod_cast block.cells_card_eq_sum_standardParentCells.symm
  unfold standardParentWeight graphSupply graphEnvelope
  rw [← Finset.sum_mul, hcount]
  simpa only [cells] using block.envelope.envelope_volume.symm

theorem standardParent_height
    {parent : CommonBinStandardParent}
    (hparent : parent ∈ block.standardParents) :
    parent.2.2 = heightIndex.1 := by
  rcases Finset.mem_image.mp hparent with ⟨cell, hcell, rfl⟩
  have hdataCell : cell ∈ data.cells :=
    block.envelope.cells_subset hcell
  have hslab := data.cells_subset_standard hdataCell
  exact (Finset.mem_filter.mp hslab).2

theorem standardParent_has_fixedBin_point
    {parent : CommonBinStandardParent}
    (hparent : parent ∈ block.standardParents) :
    ∃ point : Point3,
      point ∈ wz1PaperGridCube (Real.sqrt rhoRequested.1) parent ∧
      pureWZ2FixedCommonBinLabel source.globalGrains.slope
          block.referenceHeight (Real.sqrt rhoRequested.1) point =
        block.bin := by
  rcases Finset.mem_image.mp hparent with ⟨cell, hcell, rfl⟩
  rw [cells, block.envelope.cells_eq] at hcell
  have hcellData := Finset.mem_filter.mp hcell
  rcases hcellData.2 with ⟨point, hpointRegion, hpointCell⟩
  have hselected := data.cells_subset_selected hcellData.1
  have hpointParent := selected.standardSecondParent_cell_subset
    hselected hpointCell
  refine ⟨point, by simpa [data.sqrtRequested_eq] using hpointParent, ?_⟩
  exact hpointRegion.1.2

theorem standardParents_yFiber_card_le_five (y : ℤ) :
    (block.standardParents.filter fun parent =>
      commonBinStandardParentY parent = y).card ≤ 5 := by
  let fiber := block.standardParents.filter fun parent =>
    commonBinStandardParentY parent = y
  let centerLabel : CommonBinStandardParent → ℤ := fun parent =>
    pureWZ2FixedCommonBinLabel source.globalGrains.slope
      block.referenceHeight (Real.sqrt rhoRequested.1)
      (pureWZ2PaperCellCenter (Real.sqrt rhoRequested.1) parent)
  let labels := fiber.image centerLabel
  have hrho : 0 < rhoRequested.1 := coarse.coarse_extremal.delta_pos
  have hroot : 0 < Real.sqrt rhoRequested.1 := Real.sqrt_pos.mpr hrho
  have hslope : |source.globalGrains.slope block.referenceHeight| ≤ 3 :=
    source.globalGrains.slope_global_bound block.referenceHeight
  have hlabelsSubset : labels ⊆ Finset.Icc (block.bin - 2) (block.bin + 2) := by
    intro label hlabel
    rcases Finset.mem_image.mp hlabel with ⟨parent, hparentFiber, rfl⟩
    have hparent := (Finset.mem_filter.mp hparentFiber).1
    rcases block.standardParent_has_fixedBin_point hparent with
      ⟨point, hpointParent, hpointLabel⟩
    have hmeeting : block.bin ∈
        pureWZ2CommonBinsMeetingSpatialCell {block.bin}
          source.globalGrains.slope block.referenceHeight
          (Real.sqrt rhoRequested.1) parent := by
      rw [pureWZ2CommonBinsMeetingSpatialCell, Finset.mem_filter]
      exact ⟨by simp, point, hpointParent, hpointLabel⟩
    have hwindow := commonBinLabel_mem_center_window hroot {block.bin}
      source.globalGrains.slope block.referenceHeight hslope parent hmeeting
    rw [Finset.mem_Icc] at hwindow ⊢
    dsimp only [centerLabel]
    omega
  have hcenterInjective : Set.InjOn centerLabel fiber := by
    intro first hfirst second hsecond hlabel
    have hyFirst := (Finset.mem_filter.mp hfirst).2
    have hySecond := (Finset.mem_filter.mp hsecond).2
    have hzFirst := block.standardParent_height
      (Finset.mem_filter.mp hfirst).1
    have hzSecond := block.standardParent_height
      (Finset.mem_filter.mp hsecond).1
    dsimp only [centerLabel] at hlabel
    rw [anchored_fixedCommonBinLabel_cellCenter_eq hroot,
      anchored_fixedCommonBinLabel_cellCenter_eq hroot] at hlabel
    change first.2.1 = y at hyFirst
    change second.2.1 = y at hySecond
    rw [hyFirst, hySecond] at hlabel
    apply Prod.ext
    · omega
    · apply Prod.ext
      · exact hyFirst.trans hySecond.symm
      · exact hzFirst.trans hzSecond.symm
  have hcard : labels.card = fiber.card :=
    Finset.card_image_of_injOn hcenterInjective
  calc
    _ = fiber.card := rfl
    _ = labels.card := hcard.symm
    _ ≤ (Finset.Icc (block.bin - 2) (block.bin + 2)).card :=
      Finset.card_le_card hlabelsSubset
    _ = 5 := by rw [Int.card_Icc]; omega

end PureWZ2AnchoredIntegratedCommonBinReceipt

structure PureWZ2AnchoredWeightedParentData
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈
      selected.standardSqrtSlabIndices}}
    {data : PureWZ2AnchoredPreBinRhoHeightRegularizedData selected heightIndex}
    {B₀ threshold : ENNReal} {K : ℕ}
    (block : PureWZ2AnchoredIntegratedCommonBinReceipt data B₀ threshold K) where
  selection : CommonBinStandardParentWeightedSelectionData
    5 block.standardParents block.standardParentWeight

theorem PureWZ2AnchoredIntegratedCommonBinReceipt.selectWeightedParents
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices}}
    {data : PureWZ2AnchoredPreBinRhoHeightRegularizedData selected heightIndex}
    {B₀ threshold : ENNReal} {K : ℕ}
    (block : PureWZ2AnchoredIntegratedCommonBinReceipt data B₀ threshold K) :
    0 < K →
    Nonempty (PureWZ2AnchoredWeightedParentData
      (coarseLoss := coarseLoss) (fineLoss := fineLoss) block) := by
  intro hK
  rcases commonBin_selectStandardParentWeighted
    5 block.standardParents block.standardParentWeight
    (block.standardParents_nonempty hK)
    block.standardParents_yFiber_card_le_five with
    ⟨selection⟩
  exact ⟨{ selection := selection }⟩

namespace PureWZ2AnchoredWeightedParentData

variable
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices}}
    {data : PureWZ2AnchoredPreBinRhoHeightRegularizedData selected heightIndex}
    {B₀ threshold : ENNReal} {K : ℕ}
    {block : PureWZ2AnchoredIntegratedCommonBinReceipt data B₀ threshold K}
    (weighted : PureWZ2AnchoredWeightedParentData
      (coarseLoss := coarseLoss) (fineLoss := fineLoss) block)

def selectedParents : Finset CommonBinStandardParent :=
  weighted.selection.selected

def selectedCells : Finset (ℤ × ℤ × ℤ) :=
  weighted.selectedParents.biUnion block.standardParentCells

def selectedEnvelope : Set Point3 :=
  wz2RetainedCellsUnion rhoRequested.1 weighted.selectedCells

def selectedGraphSupply : ENNReal := volume weighted.selectedEnvelope

theorem selectedParents_nonempty : weighted.selectedParents.Nonempty :=
  weighted.selection.selected_nonempty

theorem selectedParents_subset :
    weighted.selectedParents ⊆ block.standardParents :=
  weighted.selection.selected_subset

theorem selectedParents_y_separated :
    ∀ first ∈ weighted.selectedParents,
      ∀ second ∈ weighted.selectedParents, first ≠ second →
        (512 : ℤ) ≤ |commonBinStandardParentY first -
          commonBinStandardParentY second| :=
  weighted.selection.selected_y_separated

theorem selectedCells_subset : weighted.selectedCells ⊆ block.cells := by
  intro cell hcell
  rcases Finset.mem_biUnion.mp hcell with ⟨parent, hparent, hcell⟩
  exact (Finset.mem_filter.mp hcell).1

theorem graphSupply_le_selectedParentWeight :
    block.graphSupply ≤ 5 * 512 *
      ∑ parent ∈ weighted.selectedParents,
        block.standardParentWeight parent := by
  rw [← block.sum_standardParentWeight_eq_graphSupply]
  exact weighted.selection.final_weight_le

theorem selectedGraphSupply_eq_parentWeight :
    weighted.selectedGraphSupply =
      ∑ parent ∈ weighted.selectedParents,
        block.standardParentWeight parent := by
  have hdisjoint : ∀ first ∈ weighted.selectedParents,
      ∀ second ∈ weighted.selectedParents, first ≠ second →
        Disjoint (block.standardParentCells first)
          (block.standardParentCells second) := by
    intro first _ second _ hne
    apply Finset.disjoint_left.mpr
    intro cell hfirstCell hsecondCell
    exact hne ((Finset.mem_filter.mp hfirstCell).2.symm.trans
      (Finset.mem_filter.mp hsecondCell).2)
  have hcountNat :
      weighted.selectedCells.card =
        ∑ parent ∈ weighted.selectedParents,
          (block.standardParentCells parent).card := by
    unfold selectedCells
    exact Finset.card_biUnion hdisjoint
  have hcount :
      (weighted.selectedCells.card : ENNReal) =
        ∑ parent ∈ weighted.selectedParents,
          ((block.standardParentCells parent).card : ENNReal) := by
    exact_mod_cast hcountNat
  unfold selectedGraphSupply selectedEnvelope wz2RetainedCellsUnion
  rw [wz1PaperGridCube_volume_biUnion coarse.coarse_extremal.delta_pos]
  rw [hcount, Finset.sum_mul]
  rfl

end PureWZ2AnchoredWeightedParentData

structure PureWZ2AnchoredSeparatedShadingData
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData coarse.croppedCoarseShading
      sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices}}
    {data : PureWZ2AnchoredPreBinRhoHeightRegularizedData selected heightIndex}
    {B₀ threshold : ENNReal} {K : ℕ}
    {block : PureWZ2AnchoredIntegratedCommonBinReceipt data B₀ threshold K}
    (weighted : PureWZ2AnchoredWeightedParentData
      (coarseLoss := coarseLoss) (fineLoss := fineLoss) block) where
  pullback : PureWZ2AnchoredSelectedCellSourcePullback
    selected weighted.selectedCells
  region_eq : pullback.region = weighted.selectedEnvelope
  graphSupply_le :
    block.graphSupply ≤ 5 * 512 * weighted.selectedGraphSupply

theorem PureWZ2AnchoredWeightedParentData.toSeparatedShading
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData coarse.croppedCoarseShading
      sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices}}
    {data : PureWZ2AnchoredPreBinRhoHeightRegularizedData selected heightIndex}
    {B₀ threshold : ENNReal} {K : ℕ}
    {block : PureWZ2AnchoredIntegratedCommonBinReceipt data B₀ threshold K}
    (weighted : PureWZ2AnchoredWeightedParentData
      (coarseLoss := coarseLoss) (fineLoss := fineLoss) block) :
    Nonempty (PureWZ2AnchoredSeparatedShadingData weighted) := by
  have hcells : weighted.selectedCells ⊆ selected.selectedCells :=
    weighted.selectedCells_subset.trans
      (block.envelope.cells_subset.trans data.cells_subset_selected)
  rcases selected.restrictCells weighted.selectedCells hcells with ⟨pullback⟩
  have hregion : pullback.region = weighted.selectedEnvelope := by
    rw [pullback.region_eq]
    rfl
  have hgraph : block.graphSupply ≤
      5 * 512 * weighted.selectedGraphSupply := by
    rw [weighted.selectedGraphSupply_eq_parentWeight]
    exact weighted.graphSupply_le_selectedParentWeight
  exact ⟨{
    pullback := pullback
    region_eq := hregion
    graphSupply_le := hgraph
  }⟩

structure PureWZ2AnchoredSeparatedAnchorData
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData coarse.croppedCoarseShading
      sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices}}
    {data : PureWZ2AnchoredPreBinRhoHeightRegularizedData selected heightIndex}
    {B₀ threshold : ENNReal} {K : ℕ}
    {block : PureWZ2AnchoredIntegratedCommonBinReceipt data B₀ threshold K}
    (weighted : PureWZ2AnchoredWeightedParentData
      (coarseLoss := coarseLoss) (fineLoss := fineLoss) block) where
  anchorFor : ∀ parent, parent ∈ weighted.selectedParents → Point3
  sourceIndexFor :
    ∀ parent, parent ∈ weighted.selectedParents → Fin source.family.card
  anchor_mem_source :
    ∀ parent (hparent : parent ∈ weighted.selectedParents),
      anchorFor parent hparent ∈
        selected.shading.carrier (sourceIndexFor parent hparent)
  anchor_mem_parent :
    ∀ parent (hparent : parent ∈ weighted.selectedParents),
      anchorFor parent hparent ∈
        wz1PaperGridCube (Real.sqrt rhoRequested.1) parent

theorem PureWZ2AnchoredWeightedParentData.selectAnchors
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData coarse.croppedCoarseShading
      sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices}}
    {data : PureWZ2AnchoredPreBinRhoHeightRegularizedData selected heightIndex}
    {B₀ threshold : ENNReal} {K : ℕ}
    {block : PureWZ2AnchoredIntegratedCommonBinReceipt data B₀ threshold K}
    (weighted : PureWZ2AnchoredWeightedParentData
      (coarseLoss := coarseLoss) (fineLoss := fineLoss) block) :
    Nonempty (PureWZ2AnchoredSeparatedAnchorData weighted) := by
  have hchoose : ∀ parent (hparent : parent ∈ weighted.selectedParents),
      ∃ sourceIndex : Fin source.family.card, ∃ point : Point3,
        point ∈ selected.shading.carrier sourceIndex ∧
        point ∈ wz1PaperGridCube (Real.sqrt rhoRequested.1) parent := by
    intro parent hparent
    have hparentBlock := weighted.selectedParents_subset hparent
    rcases Finset.mem_image.mp hparentBlock with ⟨cell, hcell, hparentEq⟩
    have hcellSelected : cell ∈ selected.selectedCells :=
      data.cells_subset_selected (block.envelope.cells_subset hcell)
    have hpositive : 0 < volume
        (selected.shading.union ∩
          wz1PaperGridCube rhoRequested.1 cell) := by
      rw [selected.cell_mass cell hcellSelected]
      exact coarse.balanced.cellMass_pos
    rcases nonempty_of_measure_ne_zero hpositive.ne' with ⟨point, hpoint⟩
    rcases hpoint.1 with ⟨sourceIndex, hsource⟩
    refine ⟨sourceIndex, point, hsource, ?_⟩
    have hparentCell := selected.standardSecondParent_cell_subset
      hcellSelected hpoint.2
    simpa [hparentEq, data.sqrtRequested_eq] using hparentCell
  let sourceIndexFor := fun parent hparent =>
    Classical.choose (hchoose parent hparent)
  let anchorFor := fun parent hparent =>
    Classical.choose (Classical.choose_spec (hchoose parent hparent))
  have hspec := fun parent hparent =>
    Classical.choose_spec (Classical.choose_spec (hchoose parent hparent))
  exact ⟨{
    anchorFor := anchorFor
    sourceIndexFor := sourceIndexFor
    anchor_mem_source := fun parent hparent => (hspec parent hparent).1
    anchor_mem_parent := fun parent hparent => (hspec parent hparent).2
  }⟩

structure PureWZ2AnchoredSeparatedGraphFamilyData
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {preBin : PureWZ2AnchoredPreBinRhoHeightFamilyData selected}
    {B₀ : ENNReal} {K : ℕ}
    {ledger : PureWZ2AnchoredEligibleBlockLedger preBin B₀ K}
    (family : PureWZ2AnchoredEligibleGraphFamilyData preBin B₀ K ledger) where
  weighted : ∀ heightIndex : {heightIndex // heightIndex ∈ ledger.eligible},
    PureWZ2AnchoredWeightedParentData
      (coarseLoss := coarseLoss) (fineLoss := fineLoss)
      (family.blockData heightIndex)
  shading : ∀ heightIndex : {heightIndex // heightIndex ∈ ledger.eligible},
    PureWZ2AnchoredSeparatedShadingData (weighted heightIndex)
  anchors : ∀ heightIndex : {heightIndex // heightIndex ∈ ledger.eligible},
    PureWZ2AnchoredSeparatedAnchorData (weighted heightIndex)

theorem PureWZ2AnchoredEligibleGraphFamilyData.separate
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {preBin : PureWZ2AnchoredPreBinRhoHeightFamilyData selected}
    {B₀ : ENNReal} {K : ℕ}
    {ledger : PureWZ2AnchoredEligibleBlockLedger preBin B₀ K}
    (family : PureWZ2AnchoredEligibleGraphFamilyData preBin B₀ K ledger)
    (hK : 0 < K) :
    Nonempty (PureWZ2AnchoredSeparatedGraphFamilyData
      (coarseLoss := coarseLoss) (fineLoss := fineLoss) family) := by
  have hweighted : ∀ heightIndex : {heightIndex // heightIndex ∈ ledger.eligible},
      Nonempty (PureWZ2AnchoredWeightedParentData
        (coarseLoss := coarseLoss) (fineLoss := fineLoss)
        (family.blockData heightIndex)) := fun heightIndex =>
    (family.blockData heightIndex).selectWeightedParents hK
  let weighted := fun heightIndex => Classical.choice (hweighted heightIndex)
  have hshading : ∀ heightIndex : {heightIndex // heightIndex ∈ ledger.eligible},
      Nonempty (PureWZ2AnchoredSeparatedShadingData (weighted heightIndex)) :=
    fun heightIndex => (weighted heightIndex).toSeparatedShading
  have hanchors : ∀ heightIndex : {heightIndex // heightIndex ∈ ledger.eligible},
      Nonempty (PureWZ2AnchoredSeparatedAnchorData (weighted heightIndex)) :=
    fun heightIndex => (weighted heightIndex).selectAnchors
  exact ⟨{
    weighted := weighted
    shading := fun heightIndex => Classical.choice (hshading heightIndex)
    anchors := fun heightIndex => Classical.choice (hanchors heightIndex)
  }⟩

namespace PureWZ2AnchoredSeparatedAnchorData

variable
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices}}
    {data : PureWZ2AnchoredPreBinRhoHeightRegularizedData selected heightIndex}
    {B₀ threshold : ENNReal} {K : ℕ}
    {block : PureWZ2AnchoredIntegratedCommonBinReceipt data B₀ threshold K}
    {weighted : PureWZ2AnchoredWeightedParentData
      (coarseLoss := coarseLoss) (fineLoss := fineLoss) block}
    (anchors : PureWZ2AnchoredSeparatedAnchorData weighted)

def sourceAnchor (parent : CommonBinStandardParent)
    (hparent : parent ∈ weighted.selectedParents) :
    {point : Point3 // point ∈ source.shading.union} :=
  ⟨anchors.anchorFor parent hparent,
    ⟨anchors.sourceIndexFor parent hparent,
      selected.subshading _ (anchors.anchor_mem_source parent hparent)⟩⟩

def normal (parent : CommonBinStandardParent)
    (hparent : parent ∈ weighted.selectedParents) : Point3 :=
  source.localGrains.planeMap (anchors.sourceAnchor parent hparent)

theorem normal_unit (parent : CommonBinStandardParent)
    (hparent : parent ∈ weighted.selectedParents) :
    ‖anchors.normal parent hparent‖ = 1 :=
  source.localGrains.planeMap_unit _

theorem normal_vertical (parent : CommonBinStandardParent)
    (hparent : parent ∈ weighted.selectedParents) :
    |anchors.normal parent hparent (2 : Fin 3)| ≤ 1 / 2 :=
  source.planeMap_vertical_bound _

theorem normal_dist_le_anchor_dist
    (first second : CommonBinStandardParent)
    (hfirst : first ∈ weighted.selectedParents)
    (hsecond : second ∈ weighted.selectedParents) :
    dist (anchors.normal first hfirst) (anchors.normal second hsecond) ≤
      dist (anchors.anchorFor first hfirst)
        (anchors.anchorFor second hsecond) := by
  have h := source.localGrains.planeMap_lipschitz.dist_le_mul
    (anchors.sourceAnchor first hfirst) (anchors.sourceAnchor second hsecond)
  change dist
      (source.localGrains.planeMap (anchors.sourceAnchor first hfirst))
      (source.localGrains.planeMap (anchors.sourceAnchor second hsecond)) ≤
    dist ((anchors.sourceAnchor first hfirst : _).1)
      ((anchors.sourceAnchor second hsecond : _).1)
  simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using h

end PureWZ2AnchoredSeparatedAnchorData

end Kakeya.Assouad

end
