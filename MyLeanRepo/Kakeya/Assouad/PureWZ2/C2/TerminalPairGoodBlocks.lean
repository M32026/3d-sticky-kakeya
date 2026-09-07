import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalBlockParentPairWeights
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalWindowHeightPopularity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularParentWeightClass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularExactMultiWindow
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalExactVolumeSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalGlobalBinGoodFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers

/-!
# Relative good blocks after block--parent pair regularization

The first dyadic selection is global in `(block, parent)`.  This file then
groups the selected pair mass by the original terminal block and keeps blocks
that are heavy relative to that already selected total.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

def PureWZ2TerminalBlockParentPairWeightClassData.blockPairs
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) : Finset (ℤ × (ℤ × ℤ × ℤ)) :=
  pairClass.selectedPairs.filter fun pair => pair.1 = block

def PureWZ2TerminalBlockParentPairWeightClassData.blockWeight
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) : ENNReal :=
  ∑ pair ∈ pairClass.blockPairs block,
    pureWZ2TerminalBlockParentWeight prepared pair.1 pair.2

def PureWZ2TerminalBlockParentPairWeightClassData.goodBlocks
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared) :
    Finset ℤ :=
  (pureWZ2TerminalBlocks prepared).filter fun block =>
    pairClass.selectedWeight /
        (2 * ((pureWZ2TerminalBlocks prepared).card : ENNReal)) ≤
      pairClass.blockWeight block

theorem PureWZ2TerminalBlockParentPairWeightClassData.sum_blockWeight
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared) :
    (∑ block ∈ pureWZ2TerminalBlocks prepared, pairClass.blockWeight block) =
      pairClass.selectedWeight := by
  have hmaps : Set.MapsTo
      (fun pair : ℤ × (ℤ × ℤ × ℤ) => pair.1)
      (pairClass.selectedPairs : Set (ℤ × (ℤ × ℤ × ℤ)))
      (pureWZ2TerminalBlocks prepared : Set ℤ) := by
    intro pair hpair
    have hpositive := pairClass.selectedPairs_subset hpair
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hpositive).1).1
  calc
    (∑ block ∈ pureWZ2TerminalBlocks prepared, pairClass.blockWeight block) =
        ∑ block ∈ pureWZ2TerminalBlocks prepared,
          ∑ pair ∈ pairClass.selectedPairs with pair.1 = block,
            pureWZ2TerminalBlockParentWeight prepared pair.1 pair.2 := by
      rfl
    _ = ∑ pair ∈ pairClass.selectedPairs,
          pureWZ2TerminalBlockParentWeight prepared pair.1 pair.2 :=
      Finset.sum_fiberwise_of_maps_to hmaps _
    _ = pairClass.selectedWeight := pairClass.selectedWeight_eq.symm

/-- The pair-relative good blocks retain at least half of the globally
selected pair mass. -/
theorem PureWZ2TerminalBlockParentPairWeightClassData.goodBlocks_retained
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared) :
    pairClass.selectedWeight ≤ 2 *
      ∑ block ∈ pairClass.goodBlocks, pairClass.blockWeight block := by
  let blocks := pureWZ2TerminalBlocks prepared
  let threshold := pairClass.selectedWeight /
    (2 * (blocks.card : ENNReal))
  have hblocksNonempty : blocks.Nonempty := by
    rcases pairClass.selectedPairs_nonempty with ⟨pair, hpair⟩
    have hpositive := pairClass.selectedPairs_subset hpair
    exact ⟨pair.1, (Finset.mem_product.mp
      (Finset.mem_filter.mp hpositive).1).1⟩
  have hdenomZero : (2 * (blocks.card : ENNReal)) ≠ 0 := by
    norm_cast
    exact mul_ne_zero (by norm_num) hblocksNonempty.card_ne_zero
  have hdenomTop : (2 * (blocks.card : ENNReal)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)
  have hselectedWeightTop : pairClass.selectedWeight ≠ ⊤ := by
    rw [pairClass.selectedWeight_eq]
    apply ENNReal.sum_ne_top.mpr
    intro pair hpair
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (by norm_num) pairClass.pairFloor_ne_top)
      (pairClass.weight_band pair hpair).2
  have hthresholdTop : threshold ≠ ⊤ :=
    ENNReal.div_ne_top hselectedWeightTop hdenomZero
  have hsmall : 2 * ((blocks.card : ENNReal) * threshold) ≤
      ∑ block ∈ blocks, pairClass.blockWeight block := by
    have hcancel : (2 * (blocks.card : ENNReal)) * threshold =
        pairClass.selectedWeight := by
      exact ENNReal.mul_div_cancel hdenomZero hdenomTop
    rw [pairClass.sum_blockWeight]
    rw [show 2 * ((blocks.card : ENNReal) * threshold) =
        (2 * (blocks.card : ENNReal)) * threshold by ring, hcancel]
  have hretained := finset_good_weighted_supply_retains_half
        blocks pairClass.blockWeight 1 threshold hthresholdTop
        (by simpa using hsmall)
  simp only [mul_one] at hretained
  change (∑ block ∈ pureWZ2TerminalBlocks prepared,
      pairClass.blockWeight block) ≤
    2 * ∑ block ∈ pairClass.goodBlocks, pairClass.blockWeight block at hretained
  rw [pairClass.sum_blockWeight] at hretained
  exact hretained

theorem PureWZ2TerminalBlockParentPairWeightClassData.goodBlocks_nonempty
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared) :
    pairClass.goodBlocks.Nonempty := by
  by_contra hempty
  have hzero : pairClass.goodBlocks = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hretained := pairClass.goodBlocks_retained
  rw [hzero] at hretained
  simp only [Finset.sum_empty, mul_zero] at hretained
  exact (not_le_of_gt pairClass.selectedWeight_pos) hretained

def PureWZ2TerminalBlockParentPairWeightClassData.blockParents
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (pairClass.blockPairs block).image Prod.snd

theorem PureWZ2TerminalBlockParentPairWeightClassData.good_blockWeight_pos
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    {block : ℤ} (hblock : block ∈ pairClass.goodBlocks) :
    0 < pairClass.blockWeight block := by
  have hblocksNonempty : (pureWZ2TerminalBlocks prepared).Nonempty := by
    rcases pairClass.selectedPairs_nonempty with ⟨pair, hpair⟩
    have hpositive := pairClass.selectedPairs_subset hpair
    exact ⟨pair.1, (Finset.mem_product.mp
      (Finset.mem_filter.mp hpositive).1).1⟩
  have hdenomTop : 2 *
      ((pureWZ2TerminalBlocks prepared).card : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)
  have hthresholdPos : 0 < pairClass.selectedWeight /
      (2 * ((pureWZ2TerminalBlocks prepared).card : ENNReal)) :=
    ENNReal.div_pos pairClass.selectedWeight_pos.ne' hdenomTop
  exact hthresholdPos.trans_le (Finset.mem_filter.mp hblock).2

theorem PureWZ2TerminalBlockParentPairWeightClassData.good_blockPairs_nonempty
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    {block : ℤ} (hblock : block ∈ pairClass.goodBlocks) :
    (pairClass.blockPairs block).Nonempty := by
  by_contra hempty
  have hzero : pairClass.blockPairs block = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hweightZero : pairClass.blockWeight block = 0 := by
    simp [PureWZ2TerminalBlockParentPairWeightClassData.blockWeight, hzero]
  exact (pairClass.good_blockWeight_pos hblock).ne' hweightZero

/-- The selected pair fibre over a fixed block has no duplicate parent. -/
theorem PureWZ2TerminalBlockParentPairWeightClassData.blockPairs_snd_injective
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) : Set.InjOn Prod.snd (↑(pairClass.blockPairs block) :
      Set (ℤ × (ℤ × ℤ × ℤ))) := by
  intro first hfirst second hsecond heq
  have hfirstBlock : first.1 = block := (Finset.mem_filter.mp hfirst).2
  have hsecondBlock : second.1 = block := (Finset.mem_filter.mp hsecond).2
  exact Prod.ext (hfirstBlock.trans hsecondBlock.symm) heq

theorem PureWZ2TerminalBlockParentPairWeightClassData.blockParents_nonempty
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    {block : ℤ} (hblock : block ∈ pairClass.goodBlocks) :
    (pairClass.blockParents block).Nonempty := by
  simpa [PureWZ2TerminalBlockParentPairWeightClassData.blockParents] using
    (pairClass.good_blockPairs_nonempty hblock).image Prod.snd

theorem PureWZ2TerminalBlockParentPairWeightClassData.blockParents_subset
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) : pairClass.blockParents block ⊆
      terminal.sticky.balanced.activeCells := by
  intro parent hparent
  rcases Finset.mem_image.mp hparent with ⟨pair, hpair, rfl⟩
  have hselected := (Finset.mem_filter.mp hpair).1
  have hpositive := pairClass.selectedPairs_subset hselected
  exact (Finset.mem_product.mp (Finset.mem_filter.mp hpositive).1).2

theorem PureWZ2TerminalBlockParentPairWeightClassData.blockWeight_eq_sum_parent
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) : pairClass.blockWeight block =
      ∑ parent ∈ pairClass.blockParents block,
        pureWZ2TerminalBlockParentWeight prepared block parent := by
  rw [show pairClass.blockWeight block =
      ∑ pair ∈ pairClass.blockPairs block,
        pureWZ2TerminalBlockParentWeight prepared pair.1 pair.2 by rfl]
  rw [show pairClass.blockParents block =
      (pairClass.blockPairs block).image Prod.snd by rfl,
    Finset.sum_image (pairClass.blockPairs_snd_injective block)]
  apply Finset.sum_congr rfl
  intro pair hpair
  rw [(Finset.mem_filter.mp hpair).2]

theorem PureWZ2TerminalBlockParentPairWeightClassData.block_support_card_mul_pairFloor_le
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) :
    (pairClass.blockParents block).card * pairClass.pairFloor ≤
      pairClass.blockWeight block := by
  rw [pairClass.blockWeight_eq_sum_parent block]
  calc
    (pairClass.blockParents block).card * pairClass.pairFloor =
        ∑ _parent ∈ pairClass.blockParents block, pairClass.pairFloor := by
      simp [Finset.sum_const]
    _ ≤ ∑ parent ∈ pairClass.blockParents block,
        pureWZ2TerminalBlockParentWeight prepared block parent := by
      apply Finset.sum_le_sum
      intro parent hparent
      rcases Finset.mem_image.mp hparent with ⟨pair, hpair, rfl⟩
      exact (pairClass.weight_band pair (Finset.mem_filter.mp hpair).1).1.trans_eq
        (congrArg (fun value =>
          pureWZ2TerminalBlockParentWeight prepared value pair.2)
          (Finset.mem_filter.mp hpair).2)

/-- The union of the official parents selected over one pair-good block. -/
def PureWZ2TerminalBlockParentPairWeightClassData.blockParentRegion
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) : Set Point3 :=
  ⋃ parent ∈ pairClass.blockParents block,
    wz1PaperGridCube terminal.sqrtRequested.1 parent

theorem PureWZ2TerminalBlockParentPairWeightClassData.blockParentRegion_measurable
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) : MeasurableSet (pairClass.blockParentRegion block) := by
  exact MeasurableSet.biUnion
    (pairClass.blockParents block).finite_toSet.countable
    (fun parent _ => wz1PaperGridCube_measurable parent)

/-- The genuine selected-family carrier in one block and its selected parent
support.  Both restrictions are spatial intersections of the original source. -/
def PureWZ2TerminalBlockParentPairWeightClassData.blockSourceShading
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) : WZ1PaperTubeShading terminal.sticky.selected.family where
  carrier index := (terminalSourceBlockShading prepared block).carrier index ∩
    pairClass.blockParentRegion block
  measurable_carrier index :=
    (terminalSourceBlockShading prepared block).measurable_carrier index |>.inter
      (pairClass.blockParentRegion_measurable block)
  subset_body index := Set.inter_subset_left.trans
    ((terminalSourceBlockShading prepared block).subset_body index)

theorem PureWZ2TerminalBlockParentPairWeightClassData.blockSourceShading_union_eq
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) :
    (pairClass.blockSourceShading block).union =
      (terminalSourceBlockShading prepared block).union ∩
        pairClass.blockParentRegion block := by
  ext point
  constructor
  · rintro ⟨index, hblock, hregion⟩
    exact ⟨⟨index, hblock⟩, hregion⟩
  · rintro ⟨⟨index, hblock⟩, hregion⟩
    exact ⟨index, hblock, hregion⟩

/-- The active-cell graph carrier cut by the identical block and parent
region as `blockSourceShading`. -/
def PureWZ2TerminalBlockParentPairWeightClassData.blockGraphShading
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily terminalSource.shading
        terminalSource.delta_pos) where
  carrier index := (pureWZ2TerminalBlockShading prepared block).carrier index ∩
    pairClass.blockParentRegion block
  measurable_carrier index :=
    (pureWZ2TerminalBlockShading prepared block).measurable_carrier index |>.inter
      (pairClass.blockParentRegion_measurable block)
  subset_body index := Set.inter_subset_left.trans
    ((pureWZ2TerminalBlockShading prepared block).subset_body index)

theorem PureWZ2TerminalBlockParentPairWeightClassData.blockGraphShading_union_eq
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) :
    (pairClass.blockGraphShading block).union =
      (pureWZ2TerminalBlockShading prepared block).union ∩
        pairClass.blockParentRegion block := by
  ext point
  constructor
  · rintro ⟨index, hblock, hregion⟩
    exact ⟨⟨index, hblock⟩, hregion⟩
  · rintro ⟨⟨index, hblock⟩, hregion⟩
    exact ⟨index, hblock, hregion⟩

theorem PureWZ2TerminalBlockParentPairWeightClassData.blockSourceGraph_union_eq
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) :
    (pairClass.blockSourceShading block).union =
      (pairClass.blockGraphShading block).union := by
  rw [pairClass.blockSourceShading_union_eq block,
    pairClass.blockGraphShading_union_eq block,
    terminalSourceBlockShading_union_eq prepared block]

theorem PureWZ2TerminalBlockParentPairWeightClassData.blockSourceShading_volume
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) :
    volume (pairClass.blockSourceShading block).union =
      pairClass.blockWeight block := by
  calc
    volume (pairClass.blockSourceShading block).union =
        volume ((terminalSourceBlockShading prepared block).union ∩
          ⋃ parent ∈ pairClass.blockParents block,
            wz1PaperGridCube terminal.sqrtRequested.1 parent) := by
      rw [pairClass.blockSourceShading_union_eq block]
      rfl
    _ = ∑ parent ∈ pairClass.blockParents block,
        pureWZ2TerminalBlockParentWeight prepared block parent :=
      (pureWZ2TerminalBlockParentWeight_sum_selected prepared block
        (pairClass.blockParents block)).symm
    _ = pairClass.blockWeight block :=
      (pairClass.blockWeight_eq_sum_parent block).symm

theorem PureWZ2TerminalBlockParentPairWeightClassData.blockSourceShading_subshading
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) :
    PureWZ2PaperIsSubshading (pairClass.blockSourceShading block)
      terminalSource.shading :=
  fun index => Set.inter_subset_left.trans Set.inter_subset_left

theorem PureWZ2TerminalBlockParentPairWeightClassData.blockSourceShading_constant_multiplicity
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) :
    (pairClass.blockSourceShading block).HasConstantMultiplicity
      terminalSource.multiplicity (2 * terminalSource.multiplicity) := by
  intro point hpoint
  have hmultiplicity : (pairClass.blockSourceShading block).pointMultiplicity
      point = terminalSource.shading.pointMultiplicity point := by
    unfold Kakeya.Streamlined.Shading.pointMultiplicity
    congr 1
    ext index
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.1.1
    · intro hsource
      rcases hpoint with ⟨_witness, _hblock, hparent⟩
      exact ⟨⟨hsource, _hblock.2⟩, hparent⟩
  rw [hmultiplicity]
  exact terminalSource.constant_multiplicity point
    (pairClass.blockSourceShading_subshading block |>.union_subset hpoint)

/-- The pair-relative good blocks retain the terminal indexed mass with only
the two factor-two volume/multiplicity conversions and the global pair-bin
loss. -/
theorem PureWZ2TerminalBlockParentPairWeightClassData.source_mass_control
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared) :
    terminalSource.shading.mass ≤
      (8 : ENNReal) * (pairClass.bins : ENNReal) *
        ∑ block ∈ pairClass.goodBlocks,
          (pairClass.blockSourceShading block).mass := by
  let multiplicity : ENNReal := terminalSource.multiplicity
  have hsourceUpper := (constant_multiplicity_mass_volume_generic
    terminalSource.constant_multiplicity).2
  have hblockLower : ∀ block : ℤ, multiplicity * pairClass.blockWeight block ≤
      (pairClass.blockSourceShading block).mass := by
    intro block
    rw [← pairClass.blockSourceShading_volume block]
    exact (constant_multiplicity_mass_volume_generic
      (pairClass.blockSourceShading_constant_multiplicity block)).1
  have hgoodMass :
      ∑ block ∈ pairClass.goodBlocks,
          multiplicity * pairClass.blockWeight block ≤
        ∑ block ∈ pairClass.goodBlocks,
          (pairClass.blockSourceShading block).mass :=
    Finset.sum_le_sum fun block _ => hblockLower block
  calc
    terminalSource.shading.mass ≤
        (2 * multiplicity) * volume terminalSource.shading.union := hsourceUpper
    _ ≤ (2 * multiplicity) * (2 * pairClass.bins *
        pairClass.selectedWeight) := by
      exact mul_le_mul_left' pairClass.retained_volume _
    _ ≤ (2 * multiplicity) * (2 * pairClass.bins *
        (2 * ∑ block ∈ pairClass.goodBlocks,
          pairClass.blockWeight block)) := by
      exact mul_le_mul_left'
        (mul_le_mul_left' pairClass.goodBlocks_retained _) _
    _ = (8 : ENNReal) * (pairClass.bins : ENNReal) *
        ∑ block ∈ pairClass.goodBlocks,
          (multiplicity * pairClass.blockWeight block) := by
      rw [← Finset.mul_sum]
      rw [show (8 : ENNReal) = 2 * 2 * 2 by norm_num]
      ac_rfl
    _ ≤ (8 : ENNReal) * (pairClass.bins : ENNReal) *
        ∑ block ∈ pairClass.goodBlocks,
          (pairClass.blockSourceShading block).mass := by gcongr

theorem PureWZ2TerminalBlockParentPairWeightClassData.blockGraphShading_volume
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) :
    volume (pairClass.blockGraphShading block).union =
      pairClass.blockWeight block := by
  rw [← pairClass.blockSourceGraph_union_eq block,
    pairClass.blockSourceShading_volume block]

theorem PureWZ2TerminalBlockParentPairWeightClassData.blockGraphShading_subshading
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) :
    IsSubshading (pairClass.blockGraphShading block) prepared.shadow :=
  fun index => Set.inter_subset_left.trans
    (pureWZ2TerminalBlockShading_subshading prepared block index)

theorem PureWZ2TerminalBlockParentPairWeightClassData.blockGraphShading_active_window
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) :
    ∀ cell ∈ wz1Lemma23ActiveCells
        (pairClass.blockGraphShading block) delta
        terminalSource.delta_pos,
      (wz1Lemma23SnappedPoint delta cell) (2 : Fin 3) ∈
        Set.Icc (pureWZ2SourceCarrierBlockLeft delta block)
          (pureWZ2SourceCarrierBlockLeft delta block + Real.sqrt delta) := by
  intro cell hcell
  apply pureWZ2TerminalBlockShading_active_window prepared block cell
  rw [wz1Lemma23_mem_active_iff] at hcell ⊢
  refine ⟨hcell.1, ?_⟩
  rcases hcell.2 with ⟨point, ⟨index, hblock, _hparent⟩, hpointCell⟩
  exact ⟨point, ⟨index, hblock⟩, hpointCell⟩

/-- A positive pair-good block packaged as the graph window consumed by the
terminal paper-order chain.  Its supply is the actual selected pair mass. -/
structure PureWZ2TerminalPairBlockWindowData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) where
  good_mem : block ∈ pairClass.goodBlocks
  window : PureWZ2TerminalWindow prepared
  left_eq : window.left = pureWZ2SourceCarrierBlockLeft delta block
  shading_eq : window.shading = pairClass.blockGraphShading block
  supply_eq : window.volumeSupply = pairClass.blockWeight block
  source_union_eq : (pairClass.blockSourceShading block).union =
    window.shading.union

theorem PureWZ2TerminalBlockParentPairWeightClassData.windowDataOfGoodBlock
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    {block : ℤ} (hblock : block ∈ pairClass.goodBlocks) :
    Nonempty (PureWZ2TerminalPairBlockWindowData pairClass block) := by
  rcases prepared.graphWindowOfSubshading
      (pureWZ2SourceCarrierBlockLeft delta block)
      (pairClass.blockGraphShading block)
      (pairClass.blockGraphShading_subshading block)
      (pairClass.blockGraphShading_active_window block)
      (pairClass.blockWeight block) (pairClass.good_blockWeight_pos hblock)
      (by rw [pairClass.blockGraphShading_volume block]) with
    ⟨window, hleft, hshading, hsupply⟩
  exact ⟨{
    good_mem := hblock
    window := window
    left_eq := hleft
    shading_eq := hshading
    supply_eq := hsupply
    source_union_eq := by
      rw [hshading]
      exact pairClass.blockSourceGraph_union_eq block
  }⟩

/-- The dependent outer-popular prefix on one pair-good block.  The second
parent regularization is performed only on the parents selected over this
same block. -/
structure PureWZ2TerminalPairBlockPopularData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (block : ℤ) where
  windowData : PureWZ2TerminalPairBlockWindowData pairClass block
  heightData : PureWZ2TerminalWindowHeightPopularData windowData.window
  carrier : PureWZ2TerminalPopularSourceCarrierData heightData
  weightClass : PureWZ2TerminalPopularParentWeightClassData carrier
  support_eq : weightClass.supportParents = pairClass.blockParents block
  pairFloor_le_weightFloor :
    pairClass.pairFloor ≤
      8 * (heightData.popular.bins : ENNReal) * weightClass.weightFloor

theorem PureWZ2TerminalBlockParentPairWeightClassData.popularDataOfGoodBlock
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    {block : ℤ} (hblock : block ∈ pairClass.goodBlocks) :
    Nonempty (PureWZ2TerminalPairBlockPopularData pairClass block) := by
  rcases pairClass.windowDataOfGoodBlock hblock with ⟨windowData⟩
  rcases windowData.window.heightPopularBeforeFixedLine with ⟨heightData⟩
  rcases heightData.toSourceCarrier with ⟨carrier⟩
  have hsupportSum :
      (∑ parent ∈ pairClass.blockParents block,
          pureWZ2TerminalPopularParentWeight carrier parent) =
        volume carrier.shading.union := by
    rw [pureWZ2TerminalPopularParentWeight_sum_eq]
    apply congrArg volume
    rw [Set.inter_eq_left]
    intro point hpoint
    have hgraph : point ∈ heightData.graphWindow.shading.union := by
      rwa [← carrier.union_eq]
    rw [heightData.graphWindow_shading] at hgraph
    have hwindow := heightData.popular.subshading.union_subset hgraph
    rw [windowData.shading_eq, pairClass.blockGraphShading_union_eq block]
      at hwindow
    exact hwindow.2
  rcases carrier.regularizeParentWeightsOnSupport
      (pairClass.blockParents block) (pairClass.blockParents_nonempty hblock)
      (pairClass.blockParents_subset block) hsupportSum with
    ⟨weightClass, hsupportEq⟩
  have hcardPos : 0 < (pairClass.blockParents block).card :=
    (pairClass.blockParents_nonempty hblock).card_pos
  have hcardZero :
      ((pairClass.blockParents block).card : ENNReal) ≠ 0 := by
    exact_mod_cast hcardPos.ne'
  have hcardTop :
      ((pairClass.blockParents block).card : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hcarrierUpper : volume carrier.shading.union ≤
      weightClass.weightFloor *
        (4 * ((pairClass.blockParents block).card : ENNReal)) := by
    have haverage := weightClass.average_le_weightFloor
    rw [hsupportEq] at haverage
    exact (ENNReal.div_le_iff
      (mul_ne_zero (by norm_num) hcardZero)
      (ENNReal.mul_ne_top (by norm_num) hcardTop)).mp haverage
  have hblockUpper : pairClass.blockWeight block ≤
      (2 * (heightData.popular.bins : ENNReal)) *
        volume carrier.shading.union := by
    calc
      pairClass.blockWeight block =
          volume windowData.window.shading.union := by
        rw [windowData.shading_eq, pairClass.blockGraphShading_volume block]
      _ ≤ (2 * heightData.popular.bins : ℕ) *
          heightData.graphWindow.volumeSupply :=
        heightData.source_volume_retention
      _ = (2 * (heightData.popular.bins : ENNReal)) *
          volume carrier.shading.union := by
        rw [heightData.graphWindow_supply, ← heightData.graphWindow_shading,
          ← carrier.volume_eq]
        norm_num
  have hscaled :
      ((pairClass.blockParents block).card : ENNReal) * pairClass.pairFloor ≤
        ((pairClass.blockParents block).card : ENNReal) *
          (8 * (heightData.popular.bins : ENNReal) *
            weightClass.weightFloor) := by
    calc
      ((pairClass.blockParents block).card : ENNReal) * pairClass.pairFloor ≤
          pairClass.blockWeight block := by
        simpa using pairClass.block_support_card_mul_pairFloor_le block
      _ ≤ (2 * (heightData.popular.bins : ENNReal)) *
          volume carrier.shading.union := hblockUpper
      _ ≤ (2 * (heightData.popular.bins : ENNReal)) *
          (weightClass.weightFloor *
            (4 * ((pairClass.blockParents block).card : ENNReal))) := by
        gcongr
      _ = ((pairClass.blockParents block).card : ENNReal) *
          (8 * (heightData.popular.bins : ENNReal) *
            weightClass.weightFloor) := by ring
  have hfloor := (ENNReal.mul_le_mul_iff_right hcardZero hcardTop).mp hscaled
  exact ⟨{
    windowData := windowData
    heightData := heightData
    carrier := carrier
    weightClass := weightClass
    support_eq := hsupportEq
    pairFloor_le_weightFloor := hfloor
  }⟩

/-- Runtime-independent logarithmic envelope for the three dyadic losses in
the weighted fixed-slice construction. -/
def pureWZ2TerminalPairWeightedSliceLogCost (delta : ℝ) : ENNReal :=
  (6144 * 4 * 23 ^ 2 * 2 : ENNReal) *
    ENNReal.ofReal wz2PaperBoundaryLogCoefficient ^ 2 *
    ENNReal.ofReal (1 + Real.log delta⁻¹) ^ 4

def pureWZ2TerminalPairSourceMassLogCost (delta : ℝ) : ENNReal :=
  (1024 : ENNReal) * ENNReal.ofReal wz2PaperBoundaryLogCoefficient *
    ENNReal.ofReal (1 + Real.log delta⁻¹)

/-- The terminal pair source-mass logarithm decreases when the scale grows. -/
theorem pureWZ2TerminalPairSourceMassLogCost_mono
    {delta rho : ℝ} (hdelta : 0 < delta) (hdeltaRho : delta ≤ rho) :
    pureWZ2TerminalPairSourceMassLogCost rho ≤
      pureWZ2TerminalPairSourceMassLogCost delta := by
  unfold pureWZ2TerminalPairSourceMassLogCost
  apply mul_le_mul_left'
  apply ENNReal.ofReal_mono
  have hinv : rho⁻¹ ≤ delta⁻¹ :=
    (inv_le_inv₀ (hdelta.trans_le hdeltaRho) hdelta).mpr hdeltaRho
  exact add_le_add_right
    (Real.log_le_log (inv_pos.mpr (hdelta.trans_le hdeltaRho)) hinv) 1

theorem PureWZ2TerminalBlockParentPairWeightClassData.sourceMassCost_le
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared) :
    (256 * pairClass.bins : ENNReal) ≤
      pureWZ2TerminalPairSourceMassLogCost delta := by
  let envelope := ENNReal.ofReal
    (wz2PaperBoundaryLogCoefficient *
      (1 + Real.log terminal.sqrtRequested.1⁻¹))
  let C := ENNReal.ofReal wz2PaperBoundaryLogCoefficient
  let L := ENNReal.ofReal (1 + Real.log delta⁻¹)
  have hdelta := source.extremal.delta_pos
  have hdeltaOne := source.extremal.delta_le_one
  have hrootPos : 0 < Real.sqrt delta := Real.sqrt_pos.mpr hdelta
  have hdeltaRoot : delta ≤ Real.sqrt delta := by
    nlinarith [Real.sq_sqrt hdelta.le, Real.sqrt_nonneg delta]
  have hinverse : (Real.sqrt delta)⁻¹ ≤ delta⁻¹ :=
    (inv_le_inv₀ hrootPos hdelta).mpr hdeltaRoot
  have hlogRoot : Real.log (Real.sqrt delta)⁻¹ ≤ Real.log delta⁻¹ :=
    Real.log_le_log (inv_pos.mpr hrootPos) hinverse
  have hcoefficient : 0 ≤ wz2PaperBoundaryLogCoefficient := by
    unfold wz2PaperBoundaryLogCoefficient
    exact le_trans (by positivity) (le_max_right _ _)
  have henvelope : envelope ≤ C * L := by
    dsimp only [envelope, C, L]
    rw [terminal.sqrtRequested_eq]
    calc
      ENNReal.ofReal (wz2PaperBoundaryLogCoefficient *
          (1 + Real.log (Real.sqrt delta)⁻¹)) ≤
        ENNReal.ofReal (wz2PaperBoundaryLogCoefficient *
          (1 + Real.log delta⁻¹)) := by
        apply ENNReal.ofReal_mono
        gcongr
      _ = ENNReal.ofReal wz2PaperBoundaryLogCoefficient *
          ENNReal.ofReal (1 + Real.log delta⁻¹) := by
        rw [← ENNReal.ofReal_mul hcoefficient]
  calc
    (256 * pairClass.bins : ENNReal) ≤ 256 * (4 * envelope) := by
      gcongr
      exact pairClass.bins_le_logEnvelope
    _ ≤ 256 * (4 * (C * L)) := by gcongr
    _ = pureWZ2TerminalPairSourceMassLogCost delta := by
      simp [pureWZ2TerminalPairSourceMassLogCost, C, L]
      ring

theorem pureWZ2_terminalPair_sourceMass_budget_schedule
    {stickyLoss localMassLoss workingLoss : ℝ}
    (hgap : stickyLoss + localMassLoss < workingLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sigma delta : ℝ}, 0 < delta → delta ≤ delta₀ →
        pureWZ2TerminalPairSourceMassLogCost delta *
            Kakeya.realRpowENN delta (sigma + workingLoss) ≤
          Kakeya.realRpowENN delta localMassLoss *
            Kakeya.realRpowENN delta (sigma + stickyLoss) := by
  let gap := workingLoss - (stickyLoss + localMassLoss)
  have hgapPos : 0 < gap := by dsimp only [gap]; linarith
  let coefficient : ENNReal :=
    (1024 : ENNReal) * ENNReal.ofReal wz2PaperBoundaryLogCoefficient
  have hcoefficientTop : coefficient ≠ ⊤ := by
    dsimp only [coefficient]
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  rcases exists_delta_log_absorbed_ennreal coefficient hcoefficientTop
      hgapPos (show 0 < (1 : ℕ) by omega) with
    ⟨delta₀, hdelta₀, hdelta₀One, habsorb⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro sigma delta hdelta hdeltaSmall
  have hcost : pureWZ2TerminalPairSourceMassLogCost delta ≤
      Kakeya.realRpowENN delta (-gap) := by
    simpa [pureWZ2TerminalPairSourceMassLogCost, coefficient, pow_one, mul_assoc]
      using habsorb delta hdelta hdeltaSmall
  have hcostAbsorb : pureWZ2TerminalPairSourceMassLogCost delta *
      Kakeya.realRpowENN delta gap ≤ 1 := by
    calc
      _ ≤ Kakeya.realRpowENN delta (-gap) *
          Kakeya.realRpowENN delta gap := by gcongr
      _ = Kakeya.realRpowENN delta ((-gap) + gap) :=
        (realRpowENN_add hdelta _ _).symm
      _ = 1 := by simp [Kakeya.realRpowENN]
  have hpower : Kakeya.realRpowENN delta (sigma + workingLoss) =
      (Kakeya.realRpowENN delta localMassLoss *
        Kakeya.realRpowENN delta (sigma + stickyLoss)) *
          Kakeya.realRpowENN delta gap := by
    rw [← realRpowENN_add hdelta, ← realRpowENN_add hdelta]
    congr 1
    dsimp only [gap]
    ring
  rw [hpower]
  calc
    pureWZ2TerminalPairSourceMassLogCost delta *
          ((Kakeya.realRpowENN delta localMassLoss *
            Kakeya.realRpowENN delta (sigma + stickyLoss)) *
              Kakeya.realRpowENN delta gap) =
        (Kakeya.realRpowENN delta localMassLoss *
          Kakeya.realRpowENN delta (sigma + stickyLoss)) *
            (pureWZ2TerminalPairSourceMassLogCost delta *
              Kakeya.realRpowENN delta gap) := by ring
    _ ≤ (Kakeya.realRpowENN delta localMassLoss *
          Kakeya.realRpowENN delta (sigma + stickyLoss)) * 1 := by gcongr
    _ = _ := by simp

/-- The ordinary three-loss adapter needs one additional factor two when the
pair-bin bound is converted to the source-mass cost.  Reserve half of the
available exponent gap and absorb that fixed factor uniformly before runtime. -/
theorem pureWZ2_terminalPair_doubleSourceMass_budget_schedule
    {stickyLoss localMassLoss workingLoss : ℝ}
    (hgap : stickyLoss + localMassLoss < workingLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sigma delta : ℝ}, 0 < delta → delta ≤ delta₀ →
        2 * pureWZ2TerminalPairSourceMassLogCost delta *
            Kakeya.realRpowENN delta (sigma + workingLoss) ≤
          Kakeya.realRpowENN delta localMassLoss *
            Kakeya.realRpowENN delta (sigma + stickyLoss) := by
  let middleLoss :=
    ((stickyLoss + localMassLoss) + workingLoss) / 2
  have hfirstGap : stickyLoss + localMassLoss < middleLoss := by
    dsimp only [middleLoss]
    linarith
  have hsecondGap : 0 < workingLoss - middleLoss := by
    dsimp only [middleLoss]
    linarith
  rcases pureWZ2_terminalPair_sourceMass_budget_schedule hfirstGap with
    ⟨sourceDelta₀, hsourceDelta₀, hsourceDelta₀One, hsource⟩
  rcases pure_wz2_exists_delta₀_constant_rpow_le_one
      (constant := 2) (gap := workingLoss - middleLoss) (by norm_num)
      hsecondGap with
    ⟨factorDelta₀, hfactorDelta₀, hfactorDelta₀One, hfactor⟩
  let delta₀ := min sourceDelta₀ factorDelta₀
  refine ⟨delta₀, lt_min hsourceDelta₀ hfactorDelta₀,
    (min_le_left _ _).trans hsourceDelta₀One, ?_⟩
  intro sigma delta hdelta hdeltaSmall
  have hsourceBound := hsource (sigma := sigma) hdelta
    (hdeltaSmall.trans (min_le_left _ _))
  have hfactorBound := hfactor delta hdelta
    (hdeltaSmall.trans (min_le_right _ _))
  norm_num at hfactorBound
  have hpower : Kakeya.realRpowENN delta (sigma + workingLoss) =
      Kakeya.realRpowENN delta (sigma + middleLoss) *
        Kakeya.realRpowENN delta (workingLoss - middleLoss) := by
    rw [← realRpowENN_add hdelta]
    congr 1
    ring
  rw [hpower]
  calc
    2 * pureWZ2TerminalPairSourceMassLogCost delta *
          (Kakeya.realRpowENN delta (sigma + middleLoss) *
            Kakeya.realRpowENN delta (workingLoss - middleLoss)) =
        (pureWZ2TerminalPairSourceMassLogCost delta *
          Kakeya.realRpowENN delta (sigma + middleLoss)) *
          (2 * Kakeya.realRpowENN delta
            (workingLoss - middleLoss)) := by ring
    _ ≤ (Kakeya.realRpowENN delta localMassLoss *
          Kakeya.realRpowENN delta (sigma + stickyLoss)) * 1 := by
      exact mul_le_mul hsourceBound hfactorBound (by positivity) (by positivity)
    _ = _ := by simp

/-- The strict terminal volume-loss gap absorbs all three dyadic factors in
the pair-good weighted-slice ledger. -/
theorem pureWZ2_terminalPair_weightedSlice_budget_schedule
    {inputLoss stickyLoss volumeLoss : ℝ}
    (hgap : inputLoss + 5 * stickyLoss / 2 < volumeLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sigma delta : ℝ}, 0 < delta → delta ≤ delta₀ →
        pureWZ2TerminalPairWeightedSliceLogCost delta *
            Kakeya.realRpowENN delta
              (1 + sigma / 2 + volumeLoss) *
            pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
          (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
            (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) := by
  let baseLoss := inputLoss + 5 * stickyLoss / 2
  let middleLoss := (baseLoss + volumeLoss) / 2
  let gap := volumeLoss - middleLoss
  have hmiddleGap : inputLoss + 5 * stickyLoss / 2 < middleLoss := by
    dsimp only [baseLoss, middleLoss]
    linarith
  have hgapPos : 0 < gap := by
    dsimp only [gap, middleLoss, baseLoss]
    linarith
  rcases pureWZ2_terminalExact_volume_budget_schedule hmiddleGap with
    ⟨volumeDelta₀, hvolumeDelta₀, hvolumeDelta₀One, hvolume⟩
  let coefficient : ENNReal :=
    (6144 * 4 * 23 ^ 2 * 2 : ENNReal) *
      ENNReal.ofReal wz2PaperBoundaryLogCoefficient ^ 2
  have hcoefficientTop : coefficient ≠ ⊤ := by
    dsimp only [coefficient]
    repeat' apply ENNReal.mul_ne_top
    all_goals simp
  rcases exists_delta_log_absorbed_ennreal coefficient hcoefficientTop
      hgapPos (show 0 < (4 : ℕ) by omega) with
    ⟨logDelta₀, hlogDelta₀, hlogDelta₀One, hlog⟩
  let delta₀ := min volumeDelta₀ logDelta₀
  refine ⟨delta₀, lt_min hvolumeDelta₀ hlogDelta₀,
    (min_le_left _ _).trans hvolumeDelta₀One, ?_⟩
  intro sigma delta hdelta hdeltaSmall
  have hvolumeBudget := hvolume (sigma := sigma) hdelta
    (hdeltaSmall.trans (min_le_left _ _))
  have hlogBound := hlog delta hdelta
    (hdeltaSmall.trans (min_le_right _ _))
  have hlogCost : pureWZ2TerminalPairWeightedSliceLogCost delta ≤
      Kakeya.realRpowENN delta (-gap) := by
    simpa [pureWZ2TerminalPairWeightedSliceLogCost, coefficient, mul_assoc]
      using hlogBound
  have hlogAbsorb : pureWZ2TerminalPairWeightedSliceLogCost delta *
      Kakeya.realRpowENN delta gap ≤ 1 := by
    calc
      _ ≤ Kakeya.realRpowENN delta (-gap) *
          Kakeya.realRpowENN delta gap := by gcongr
      _ = Kakeya.realRpowENN delta ((-gap) + gap) :=
        (realRpowENN_add hdelta _ _).symm
      _ = 1 := by simp [Kakeya.realRpowENN]
  have hpower : Kakeya.realRpowENN delta
      (1 + sigma / 2 + volumeLoss) =
      Kakeya.realRpowENN delta (1 + sigma / 2 + middleLoss) *
        Kakeya.realRpowENN delta gap := by
    rw [← realRpowENN_add hdelta]
    congr 1
    dsimp only [gap]
    ring
  rw [hpower]
  calc
    pureWZ2TerminalPairWeightedSliceLogCost delta *
          (Kakeya.realRpowENN delta (1 + sigma / 2 + middleLoss) *
            Kakeya.realRpowENN delta gap) *
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss =
        (Kakeya.realRpowENN delta (1 + sigma / 2 + middleLoss) *
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss) *
          (pureWZ2TerminalPairWeightedSliceLogCost delta *
            Kakeya.realRpowENN delta gap) := by ring
    _ ≤ ((16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2)) * 1 := by gcongr
    _ = _ := by simp

theorem PureWZ2TerminalPairBlockPopularData.bin_cost_le
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared}
    {block : ℤ}
    (pairData : PureWZ2TerminalPairBlockPopularData pairClass block) :
    (6144 * pairClass.bins * pairData.heightData.popular.bins ^ 2 *
        pairData.weightClass.bins : ENNReal) ≤
      pureWZ2TerminalPairWeightedSliceLogCost delta := by
  let L := ENNReal.ofReal (1 + Real.log delta⁻¹)
  let C := ENNReal.ofReal wz2PaperBoundaryLogCoefficient
  have hdelta := source.extremal.delta_pos
  have hdeltaOne := source.extremal.delta_le_one
  have hlogNonneg : 0 ≤ Real.log delta⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ hdelta).mpr hdeltaOne)
  have hrootPos : 0 < Real.sqrt delta := Real.sqrt_pos.mpr hdelta
  have hdeltaRoot : delta ≤ Real.sqrt delta := by
    nlinarith [Real.sq_sqrt hdelta.le, Real.sqrt_nonneg delta]
  have hinverse : (Real.sqrt delta)⁻¹ ≤ delta⁻¹ := by
    exact (inv_le_inv₀ hrootPos hdelta).mpr hdeltaRoot
  have hlogRoot : Real.log (Real.sqrt delta)⁻¹ ≤ Real.log delta⁻¹ :=
    Real.log_le_log (inv_pos.mpr hrootPos) hinverse
  have hcoefficient : 0 ≤ wz2PaperBoundaryLogCoefficient := by
    unfold wz2PaperBoundaryLogCoefficient
    exact le_trans (by positivity) (le_max_right _ _)
  have henvelope : ENNReal.ofReal
      (wz2PaperBoundaryLogCoefficient *
        (1 + Real.log terminal.sqrtRequested.1⁻¹)) ≤ C * L := by
    rw [terminal.sqrtRequested_eq]
    calc
      ENNReal.ofReal (wz2PaperBoundaryLogCoefficient *
          (1 + Real.log (Real.sqrt delta)⁻¹)) ≤
        ENNReal.ofReal (wz2PaperBoundaryLogCoefficient *
          (1 + Real.log delta⁻¹)) := by
        apply ENNReal.ofReal_mono
        gcongr
      _ = C * L := by
        rw [← ENNReal.ofReal_mul hcoefficient]
  have hpair : (pairClass.bins : ENNReal) ≤ 4 * C * L := by
    calc
      (pairClass.bins : ENNReal) ≤ 4 * ENNReal.ofReal
          (wz2PaperBoundaryLogCoefficient *
            (1 + Real.log terminal.sqrtRequested.1⁻¹)) :=
        pairClass.bins_le_logEnvelope
      _ ≤ 4 * (C * L) := mul_le_mul_left' henvelope 4
      _ = 4 * C * L := by ring
  have hweight : (pairData.weightClass.bins : ENNReal) ≤ 2 * C * L := by
    calc
      (pairData.weightClass.bins : ENNReal) ≤ 2 * ENNReal.ofReal
          (wz2PaperBoundaryLogCoefficient *
            (1 + Real.log terminal.sqrtRequested.1⁻¹)) :=
        pairData.weightClass.bins_le_logEnvelope
      _ ≤ 2 * (C * L) := mul_le_mul_left' henvelope 2
      _ = 2 * C * L := by ring
  have hheight : (pairData.heightData.popular.bins : ENNReal) ≤ 23 * L := by
    have hreal := pairData.heightData.bins_real_le_log
    calc
      (pairData.heightData.popular.bins : ENNReal) =
          ENNReal.ofReal (pairData.heightData.popular.bins : ℝ) := by simp
      _ ≤ ENNReal.ofReal (23 * (Real.log (1 / delta) + 1)) :=
        ENNReal.ofReal_mono hreal
      _ = 23 * L := by
        rw [show Real.log (1 / delta) = Real.log delta⁻¹ by
          congr 1 <;> field_simp [hdelta.ne'],
          ENNReal.ofReal_mul (by norm_num)]
        simp [L, add_comm]
  calc
    (6144 * pairClass.bins * pairData.heightData.popular.bins ^ 2 *
        pairData.weightClass.bins : ENNReal) ≤
      6144 * (4 * C * L) * (23 * L) ^ 2 * (2 * C * L) := by gcongr
    _ = pureWZ2TerminalPairWeightedSliceLogCost delta := by
      simp [pureWZ2TerminalPairWeightedSliceLogCost, C, L]
      ring

/-- The exact fixed-slice receipt on a pair-good block.  The global pair
regularization supplies the balanced-cell floor, source-height popularity
supplies the second logarithm, and the existing exact-volume budget pays the
geometric counting cost. -/
theorem PureWZ2TerminalPairBlockPopularData.weightedSlice
    {sigma inputLoss delta stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared}
    {block : ℤ}
    (pairData : PureWZ2TerminalPairBlockPopularData pairClass block)
    (habsorb :
      pureWZ2TerminalPairWeightedSliceLogCost delta *
          Kakeya.realRpowENN delta
            (1 + sigma / 2 + volumeLoss) *
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
        (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2))
    {restricted : PureWZ2TerminalPopularParentRestrictionData
      pairData.weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line}
    {selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents}
    {selectedCarrier :
      PureWZ2TerminalPopularSelectedParentCarrierData selection}
    {sources : PureWZ2TerminalPopularCoarseSourceFamily selection}
    (localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources) :
    pureWZ2TerminalPopularLocalizedPieceCost *
        Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) ≤
      (localized.selectedParents.card : ENNReal) *
        pairData.weightClass.weightFloor := by
  let power :=
    Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss)
  have hsourceFloor := pureWZ2_terminalExact_windowSupply_lower
    (prepared := prepared) source.extremal.delta_le_one
  have hblockThreshold : pairClass.selectedWeight ≤
      2 * (pureWZ2TerminalBlocks prepared).card *
        pairClass.blockWeight block := by
    have hmem := (Finset.mem_filter.mp pairData.windowData.good_mem).2
    have hdenomZero :
        2 * ((pureWZ2TerminalBlocks prepared).card : ENNReal) ≠ 0 := by
      norm_cast
      exact mul_ne_zero (by norm_num)
        (show (pureWZ2TerminalBlocks prepared).Nonempty from
          ⟨block, (Finset.mem_filter.mp pairData.windowData.good_mem).1⟩).card_ne_zero
    have hdenomTop :
        2 * ((pureWZ2TerminalBlocks prepared).card : ENNReal) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)
    simpa [mul_comm] using
      (ENNReal.div_le_iff hdenomZero hdenomTop).mp hmem
  let root := ENNReal.ofReal (Real.sqrt delta)
  let denom := ENNReal.ofReal (2 + delta + Real.sqrt delta)
  have hdenomPos : 0 < denom := by
    apply ENNReal.ofReal_pos.mpr
    nlinarith [source.extremal.delta_pos, Real.sqrt_nonneg delta]
  have hcardRoot :
      ((pureWZ2TerminalBlocks prepared).card : ENNReal) * root ≤
        2 * denom := by
    have hcard := pureWZ2TerminalBlocks_card_mul_sqrtENN_le prepared
    have hreal : 2 + delta + 2 * Real.sqrt delta ≤
        2 * (2 + delta + Real.sqrt delta) := by
      nlinarith [source.extremal.delta_pos, Real.sqrt_nonneg delta]
    calc
      ((pureWZ2TerminalBlocks prepared).card : ENNReal) * root ≤
          ENNReal.ofReal (2 + delta + 2 * Real.sqrt delta) := by
        simpa [root] using hcard
      _ ≤ ENNReal.ofReal (2 * (2 + delta + Real.sqrt delta)) :=
        ENNReal.ofReal_mono hreal
      _ = 2 * denom := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num [denom]
  have hwindowSupply :
      pureWZ2TerminalExactWindowSupply
          (volume prepared.shadow.union) delta ≤
        8 * (pairClass.bins : ENNReal) * pairClass.blockWeight block := by
    unfold pureWZ2TerminalExactWindowSupply
    apply (ENNReal.div_le_iff hdenomPos.ne' ENNReal.ofReal_ne_top).2
    change volume prepared.shadow.union * root ≤
      (8 * (pairClass.bins : ENNReal) * pairClass.blockWeight block) * denom
    rw [prepared.shadow_union]
    calc
      volume terminalSource.shading.union * root ≤
          (2 * (pairClass.bins : ENNReal) * pairClass.selectedWeight) *
            root := mul_le_mul_right' pairClass.retained_volume root
      _ ≤ (2 * (pairClass.bins : ENNReal) *
          (2 * (pureWZ2TerminalBlocks prepared).card *
            pairClass.blockWeight block)) * root := by gcongr
      _ = (4 * (pairClass.bins : ENNReal) *
          pairClass.blockWeight block) *
            ((pureWZ2TerminalBlocks prepared).card * root) := by ring
      _ ≤ (4 * (pairClass.bins : ENNReal) *
          pairClass.blockWeight block) * (2 * denom) := by gcongr
      _ = (8 * (pairClass.bins : ENNReal) *
          pairClass.blockWeight block) * denom := by ring
  have hvolumeFloor :
      (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) ≤
        96 * (pairClass.bins : ENNReal) *
          pairClass.blockWeight block * pairClass.pairFloor := by
    calc
      _ ≤ (4 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) := by gcongr <;> norm_num
      _ ≤ pureWZ2TerminalExactWindowSupply
            (volume prepared.shadow.union) delta *
          terminal.sticky.balanced.cellMass := hsourceFloor
      _ ≤ (8 * (pairClass.bins : ENNReal) *
          pairClass.blockWeight block) *
            (12 * pairClass.pairFloor) :=
        mul_le_mul hwindowSupply pairClass.cellMass_le_pairFloor bot_le bot_le
      _ = 96 * (pairClass.bins : ENNReal) *
          pairClass.blockWeight block * pairClass.pairFloor := by ring
  have hscheduled :
      (6144 * pairClass.bins * pairData.heightData.popular.bins ^ 2 *
          pairData.weightClass.bins : ENNReal) *
          power * pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
        96 * (pairClass.bins : ENNReal) *
          pairClass.blockWeight block * pairClass.pairFloor :=
    (show
      (6144 * pairClass.bins * pairData.heightData.popular.bins ^ 2 *
          pairData.weightClass.bins : ENNReal) * power *
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
        (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) from by
      calc
        (6144 * pairClass.bins * pairData.heightData.popular.bins ^ 2 *
            pairData.weightClass.bins : ENNReal) * power *
            pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
          pureWZ2TerminalPairWeightedSliceLogCost delta * power *
            pureWZ2TerminalExactVolumeCost delta sigma inputLoss := by
          gcongr
          exact pairData.bin_cost_le
        _ ≤ _ := habsorb).trans hvolumeFloor
  have hsourceToHeight : pairClass.blockWeight block ≤
      (2 * pairData.heightData.popular.bins : ENNReal) *
        pairData.heightData.graphWindow.volumeSupply := by
    rw [← pairData.windowData.supply_eq]
    exact pairData.windowData.window.volume_lower.trans (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        pairData.heightData.source_volume_retention)
  have hheightToRestricted :
      pairData.heightData.graphWindow.volumeSupply ≤
        (2 * pairData.weightClass.bins : ENNReal) *
          restrictedPrepared.volumeSupply := by
    calc
      pairData.heightData.graphWindow.volumeSupply ≤
          volume pairData.carrier.shading.union := by
        rw [pairData.carrier.volume_eq]
        exact pairData.heightData.graphWindow.volume_lower
      _ ≤ (2 * pairData.weightClass.bins : ENNReal) *
          volume restricted.shading.union :=
        restricted.retained_volume
      _ = (2 * pairData.weightClass.bins : ENNReal) *
          restrictedPrepared.volumeSupply := by
        rw [restrictedPrepared.volume_eq,
          pureWZ2PartialActiveCellShading_union]
  have hcount :=
    localized.volume_supply_mul_floor_le_selected_card
  have hlocalCost :
      96 * (pairClass.bins : ENNReal) *
          pairClass.blockWeight block * pairClass.pairFloor ≤
        (3072 * (pairClass.bins : ENNReal) *
          (pairData.heightData.popular.bins : ENNReal) ^ 2 *
          (pairData.weightClass.bins : ENNReal)) *
            (restrictedPrepared.volumeSupply *
              pairData.weightClass.weightFloor) := by
    calc
      96 * (pairClass.bins : ENNReal) *
          pairClass.blockWeight block * pairClass.pairFloor ≤
        96 * (pairClass.bins : ENNReal) *
          ((4 * (pairData.heightData.popular.bins : ENNReal) *
              pairData.weightClass.bins) * restrictedPrepared.volumeSupply) *
            (8 * (pairData.heightData.popular.bins : ENNReal) *
              pairData.weightClass.weightFloor) := by
        gcongr
        · exact hsourceToHeight.trans (by
            calc
              (2 * pairData.heightData.popular.bins : ENNReal) *
                  pairData.heightData.graphWindow.volumeSupply ≤
                (2 * pairData.heightData.popular.bins : ENNReal) *
                  ((2 * pairData.weightClass.bins : ENNReal) *
                    restrictedPrepared.volumeSupply) := by gcongr
              _ = (4 * (pairData.heightData.popular.bins : ENNReal) *
                  pairData.weightClass.bins) *
                    restrictedPrepared.volumeSupply := by ring)
        · exact pairData.pairFloor_le_weightFloor
      _ = (3072 * (pairClass.bins : ENNReal) *
          (pairData.heightData.popular.bins : ENNReal) ^ 2 *
          (pairData.weightClass.bins : ENNReal)) *
            (restrictedPrepared.volumeSupply *
              pairData.weightClass.weightFloor) := by ring
  have hscaled :
      (3072 * (pairClass.bins : ENNReal) *
          (pairData.heightData.popular.bins : ENNReal) ^ 2 *
          (pairData.weightClass.bins : ENNReal)) *
          (2 * power * pureWZ2TerminalExactVolumeCost
            delta sigma inputLoss) ≤
        (3072 * (pairClass.bins : ENNReal) *
          (pairData.heightData.popular.bins : ENNReal) ^ 2 *
          (pairData.weightClass.bins : ENNReal)) *
          (restrictedPrepared.volumeSupply *
            pairData.weightClass.weightFloor) := by
    calc
      _ = (6144 * pairClass.bins * pairData.heightData.popular.bins ^ 2 *
          pairData.weightClass.bins : ENNReal) * power *
            pureWZ2TerminalExactVolumeCost delta sigma inputLoss := by ring
      _ ≤ 96 * (pairClass.bins : ENNReal) *
          pairClass.blockWeight block * pairClass.pairFloor := hscheduled
      _ ≤ _ := hlocalCost
  let cancel : ENNReal :=
    3072 * (pairClass.bins : ENNReal) *
      (pairData.heightData.popular.bins : ENNReal) ^ 2 *
      (pairData.weightClass.bins : ENNReal)
  have hpositivePairBins : 0 < (pairClass.bins : ENNReal) := by
    exact_mod_cast (show 0 < pairClass.bins by rw [pairClass.bins_eq]; omega)
  have hpositiveHeightBins :
      0 < (pairData.heightData.popular.bins : ENNReal) := by
    exact_mod_cast (show 0 < pairData.heightData.popular.bins by
      rw [pairData.heightData.popular.bins_eq]; omega)
  have hpositiveWeightBins :
      0 < (pairData.weightClass.bins : ENNReal) := by
    exact_mod_cast (show 0 < pairData.weightClass.bins by
      rw [pairData.weightClass.bins_eq]; omega)
  have hcancelPos : 0 < cancel := by
    dsimp only [cancel]
    have hfirst : 0 < (3072 : ENNReal) * pairClass.bins :=
      ENNReal.mul_pos (by norm_num) hpositivePairBins.ne'
    have hsquare :
        0 < (pairData.heightData.popular.bins : ENNReal) ^ 2 :=
      by simpa [pow_two] using
        ENNReal.mul_pos hpositiveHeightBins.ne' hpositiveHeightBins.ne'
    have hthree : 0 < (3072 : ENNReal) * pairClass.bins *
        (pairData.heightData.popular.bins : ENNReal) ^ 2 :=
      ENNReal.mul_pos hfirst.ne' hsquare.ne'
    exact ENNReal.mul_pos hthree.ne' hpositiveWeightBins.ne'
  have hcancelTop : cancel ≠ ⊤ := by
    dsimp only [cancel]
    repeat' apply ENNReal.mul_ne_top
    all_goals simp
  have htwoPower :
      2 * power * pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
        restrictedPrepared.volumeSupply *
          pairData.weightClass.weightFloor :=
    (ENNReal.mul_le_mul_iff_left hcancelPos.ne' hcancelTop).mp
      (by simpa only [cancel, mul_comm, mul_left_comm, mul_assoc] using hscaled)
  let countCost :=
    pureWZ2TerminalPopularPrelocalizedCountCost delta sigma inputLoss
  have hcountCostPos : 0 < countCost := by
    have hthickness : 0 < ENNReal.ofReal (Real.sqrt delta + 2 * delta) :=
      ENNReal.ofReal_pos.mpr (by
        nlinarith [source.extremal.delta_pos, Real.sqrt_nonneg delta])
    have hdeltaENN : 0 < ENNReal.ofReal delta :=
      ENNReal.ofReal_pos.mpr source.extremal.delta_pos
    have hpi : 0 < ENNReal.ofReal Real.pi :=
      ENNReal.ofReal_pos.mpr Real.pi_pos
    have hglobalPower : 0 < Kakeya.realRpowENN delta (-inputLoss) := by
      exact ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos source.extremal.delta_pos _)
    have hinversePower :
        0 < Kakeya.realRpowENN (1 / delta) (1 - sigma) := by
      exact ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos (one_div_pos.mpr source.extremal.delta_pos) _)
    have hparentNat : 0 < pureWZ2FixedLineParentFiberBound delta := by
      unfold pureWZ2FixedLineParentFiberBound pureWZ2FixedLineParentYBound
      omega
    have hparent : 0 <
        (pureWZ2FixedLineParentFiberBound delta : ENNReal) := by
      exact_mod_cast hparentNat
    dsimp only [countCost, pureWZ2TerminalPopularPrelocalizedCountCost,
      pureWZ2TerminalPopularParentVolumeCost]
    positivity
  have hcountCostTop : countCost ≠ ⊤ := by
    dsimp only [countCost, pureWZ2TerminalPopularPrelocalizedCountCost,
      pureWZ2TerminalPopularParentVolumeCost]
    repeat' apply ENNReal.mul_ne_top
    all_goals simp [Kakeya.realRpowENN]
  have hfinalScaled :
      countCost * (pureWZ2TerminalPopularLocalizedPieceCost * power) ≤
        countCost * ((localized.selectedParents.card : ENNReal) *
          pairData.weightClass.weightFloor) := by
    calc
      countCost * (pureWZ2TerminalPopularLocalizedPieceCost * power) =
          (countCost * pureWZ2TerminalPopularLocalizedPieceCost) * power := by
        ring
      _ = (2 * pureWZ2TerminalExactVolumeCost delta sigma inputLoss) *
          power := by
        rw [show countCost * pureWZ2TerminalPopularLocalizedPieceCost =
            2 * pureWZ2TerminalExactVolumeCost delta sigma inputLoss by
          exact pureWZ2_terminalPopular_prelocalizedCountCost_mul_localizedPieceCost
            delta sigma inputLoss]
      _ =
        2 * power * pureWZ2TerminalExactVolumeCost delta sigma inputLoss := by
        ring
      _ ≤ restrictedPrepared.volumeSupply *
          pairData.weightClass.weightFloor := htwoPower
      _ ≤ countCost * ((localized.selectedParents.card : ENNReal) *
          pairData.weightClass.weightFloor) := by
        simpa [countCost] using hcount
  exact (ENNReal.mul_le_mul_iff_left hcountCostPos.ne' hcountCostTop).mp
    (by simpa only [mul_comm, mul_left_comm, mul_assoc] using hfinalScaled)

/-- Run the downstream paper-order output on every pair-relative good block
while preserving the exact block, source carrier, and parent-support witness. -/
theorem PureWZ2TerminalBlockParentPairWeightClassData.buildGoodBlockFamily
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss localMassLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared)
    (outputFor : ∀ {block : ℤ} (hblock : block ∈ pairClass.goodBlocks),
      ∀ pairData : PureWZ2TerminalPairBlockPopularData pairClass block,
        Nonempty (PureWZ2TerminalPopularExactWindowOutput
          (eta := eta) (theoremEta := theoremEta)
          (outputLoss := outputLoss) pairData.windowData.window))
    (volumeFor : ∀ {block : ℤ} (hblock : block ∈ pairClass.goodBlocks)
      (pairData : PureWZ2TerminalPairBlockPopularData pairClass block)
      (output : PureWZ2TerminalPopularExactWindowOutput
        (eta := eta) (theoremEta := theoremEta)
        (outputLoss := outputLoss) pairData.windowData.window),
      2 * Kakeya.realRpowENN delta localMassLoss *
          volume (pairClass.blockSourceShading block).union ≤
        volume output.chain.outerHeightLift.shading.union) :
    ∃ good : PureWZ2TerminalPopularGoodBlockFamilyData
        (eta := eta) (theoremEta := theoremEta)
        (outputLoss := outputLoss) (localMassLoss := localMassLoss) prepared,
      good.sourceMassCost = 8 * pairClass.bins := by
  let blocks := pairClass.goodBlocks
  let pairDataFor : ∀ {block : ℤ}, block ∈ blocks →
      PureWZ2TerminalPairBlockPopularData pairClass block := fun {_} hblock =>
    Classical.choice (pairClass.popularDataOfGoodBlock hblock)
  have hbinsPos : 0 < pairClass.bins := by
    rw [pairClass.bins_eq]
    omega
  rcases PureWZ2TerminalPopularGoodBlockFamilyData.buildFromSourcePiecesWithCost
      blocks pairClass.goodBlocks_nonempty
      (fun block => pairClass.blockSourceShading block)
      (fun hblock => pairClass.blockSourceShading_subshading _)
      (fun hblock => pairClass.blockSourceShading_constant_multiplicity _)
      (8 * pairClass.bins)
      (ENNReal.mul_pos (by norm_num) (by
        exact_mod_cast (Nat.ne_of_gt hbinsPos)))
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _))
      pairClass.source_mass_control
      (fun hblock => (pairDataFor hblock).windowData.window)
      (fun hblock => (pairDataFor hblock).windowData.left_eq)
      (fun hblock => (pairDataFor hblock).windowData.source_union_eq)
      (fun hblock => outputFor hblock (pairDataFor hblock))
      (fun hblock blockOutput =>
        volumeFor hblock (pairDataFor hblock) blockOutput) with ⟨good⟩
  exact ⟨good, by assumption⟩

end Kakeya.Assouad

end
