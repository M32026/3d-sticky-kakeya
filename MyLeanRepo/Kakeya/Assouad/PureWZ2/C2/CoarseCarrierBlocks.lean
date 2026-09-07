import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseGlobalPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCarrierBlocks

/-!
# Finite height blocks of the genuine coarse Lemma-24 carrier

The first sticky output, after the dependent Node-4 grain refinement and the
second sticky refinement, is the `rho`-scale carrier to which WZ Lemma 23 is
applied.  This file partitions its ordinary active-cell shadow by actual
Lemma-23 snapped cells in half-open `sqrt rho` height blocks.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

def pureWZ2CoarseCarrierBlockCells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale)
    (block : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (wz1Lemma23ActiveCells prepared.shadow twoScale.rhoRequested.1
    twoScale.coarseGrains.extremal.delta_pos).filter fun cell =>
      pureWZ2SourceCarrierBlockIndex twoScale.rhoRequested.1 cell = block

def pureWZ2CoarseCarrierBlocks
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale) : Finset ℤ :=
  (wz1Lemma23ActiveCells prepared.shadow twoScale.rhoRequested.1
    twoScale.coarseGrains.extremal.delta_pos).image
      (pureWZ2SourceCarrierBlockIndex twoScale.rhoRequested.1)

def pureWZ2CoarseCarrierBlockRegion
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale)
    (block : ℤ) : Set Point3 :=
  ⋃ cell ∈ pureWZ2CoarseCarrierBlockCells prepared block,
    wz1Lemma23Cell twoScale.rhoRequested.1 cell

def pureWZ2CoarseCarrierBlockShading
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale)
    (block : ℤ) : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily twoScale.fine.refined
        twoScale.coarseGrains.extremal.delta_pos) :=
  let region := pureWZ2CoarseCarrierBlockRegion prepared block
  { carrier := fun index => prepared.shadow.carrier index ∩ region
    measurable_carrier := fun index =>
      (prepared.shadow.measurable_carrier index).inter
        (MeasurableSet.biUnion
          (pureWZ2CoarseCarrierBlockCells prepared block).finite_toSet.countable
          (fun cell _ => wz1Lemma23Cell_measurable
            twoScale.coarseGrains.extremal.delta_pos cell))
    subset_body := fun index => Set.inter_subset_left.trans
      (prepared.shadow.subset_body index) }

theorem pureWZ2CoarseCarrierBlockShading_subshading
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale)
    (block : ℤ) :
    IsSubshading
      (pureWZ2CoarseCarrierBlockShading prepared block) prepared.shadow :=
  fun _ => Set.inter_subset_left

theorem pureWZ2CoarseCarrierBlock_carrier_partition
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale)
    (sourceIndex : Fin
      (pureWZ2ActiveCellFamily twoScale.fine.refined
        twoScale.coarseGrains.extremal.delta_pos).card) :
    prepared.shadow.carrier sourceIndex =
      ⋃ block ∈ pureWZ2CoarseCarrierBlocks prepared,
        (pureWZ2CoarseCarrierBlockShading prepared block).carrier
          sourceIndex := by
  let hrho := twoScale.coarseGrains.extremal.delta_pos
  have hball : prepared.shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hfine : point ∈ twoScale.fine.refined.union := by
      rwa [prepared.shadow_union] at hpoint
    rcases hfine with ⟨index, hindex⟩
    have hsource : point ∈ twoScale.coarseGrains.shading.union :=
      ⟨twoScale.fine.selected.embedding index,
        twoScale.fine.subshading index hindex⟩
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  ext point
  constructor
  · intro hpoint
    let cell := wz1Lemma23CellIndex twoScale.rhoRequested.1 point
    let block := pureWZ2SourceCarrierBlockIndex twoScale.rhoRequested.1 cell
    have hpointUnion : point ∈ prepared.shadow.union := ⟨sourceIndex, hpoint⟩
    have hcell : cell ∈ wz1Lemma23ActiveCells prepared.shadow
        twoScale.rhoRequested.1 hrho :=
      wz1Lemma23_index_mem_active_two hrho hball hpointUnion
    have hblock : block ∈ pureWZ2CoarseCarrierBlocks prepared :=
      Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
    exact Set.mem_iUnion₂.mpr
      ⟨block, hblock, hpoint, Set.mem_iUnion₂.mpr
        ⟨cell, Finset.mem_filter.mpr ⟨hcell, rfl⟩, rfl⟩⟩
  · intro hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨_block, _hblock, hpointBlock⟩
    exact hpointBlock.1

theorem pureWZ2CoarseCarrierBlockRegion_pairwise_disjoint
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale) :
    (pureWZ2CoarseCarrierBlocks prepared : Set ℤ).PairwiseDisjoint
      (pureWZ2CoarseCarrierBlockRegion prepared) := by
  intro first _ second _ hne
  change Disjoint
    (pureWZ2CoarseCarrierBlockRegion prepared first)
    (pureWZ2CoarseCarrierBlockRegion prepared second)
  rw [Set.disjoint_left]
  intro point hfirst hsecond
  rcases Set.mem_iUnion₂.mp hfirst with
    ⟨firstCell, hfirstCell, hpointFirst⟩
  rcases Set.mem_iUnion₂.mp hsecond with
    ⟨secondCell, hsecondCell, hpointSecond⟩
  have hcellEq : firstCell = secondCell := hpointFirst.symm.trans hpointSecond
  apply hne
  rw [← (Finset.mem_filter.mp hfirstCell).2, hcellEq,
    (Finset.mem_filter.mp hsecondCell).2]

theorem pureWZ2CoarseCarrierBlock_union_partition
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale) :
    prepared.shadow.union =
      ⋃ block ∈ pureWZ2CoarseCarrierBlocks prepared,
        (pureWZ2CoarseCarrierBlockShading prepared block).union := by
  ext point
  constructor
  · rintro ⟨sourceIndex, hpoint⟩
    have hpartition := congrArg (fun carrier : Set Point3 => point ∈ carrier)
      (pureWZ2CoarseCarrierBlock_carrier_partition prepared sourceIndex)
    rw [hpartition] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨block, hblock, hpointBlock⟩
    exact Set.mem_iUnion₂.mpr ⟨block, hblock, sourceIndex, hpointBlock⟩
  · intro hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨block, _hblock, sourceIndex, hpointBlock⟩
    exact ⟨sourceIndex,
      pureWZ2CoarseCarrierBlockShading_subshading prepared block
        sourceIndex hpointBlock⟩

theorem pureWZ2CoarseCarrierBlock_union_pairwise_disjoint
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale) :
    (pureWZ2CoarseCarrierBlocks prepared : Set ℤ).PairwiseDisjoint
      (fun block =>
        (pureWZ2CoarseCarrierBlockShading prepared block).union) := by
  intro first hfirst second hsecond hne
  exact (pureWZ2CoarseCarrierBlockRegion_pairwise_disjoint prepared
    hfirst hsecond hne).mono
      (by rintro point ⟨_index, _hcarrier, hregion⟩; exact hregion)
      (by rintro point ⟨_index, _hcarrier, hregion⟩; exact hregion)

theorem pureWZ2CoarseCarrierBlock_volume_eq_sum
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale) :
    MeasureTheory.volume prepared.shadow.union =
      ∑ block ∈ pureWZ2CoarseCarrierBlocks prepared,
        MeasureTheory.volume
          (pureWZ2CoarseCarrierBlockShading prepared block).union := by
  rw [pureWZ2CoarseCarrierBlock_union_partition prepared]
  exact MeasureTheory.measure_biUnion_finset
    (pureWZ2CoarseCarrierBlock_union_pairwise_disjoint prepared)
    (fun block _ => measurableSet_shading_union
      (pureWZ2CoarseCarrierBlockShading prepared block))

/-- The genuine coarse shadow meets only `O(1 / sqrt rho)` height blocks. -/
theorem pureWZ2CoarseCarrierBlocks_card_mul_sqrt_le
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale) :
    (pureWZ2CoarseCarrierBlocks prepared).card *
        Real.sqrt twoScale.rhoRequested.1 ≤
      2 + twoScale.rhoRequested.1 +
        2 * Real.sqrt twoScale.rhoRequested.1 := by
  let scale := twoScale.rhoRequested.1
  have hscale : 0 < scale := twoScale.coarseGrains.extremal.delta_pos
  have hscaleOne : scale ≤ 1 := twoScale.rhoRequested.property.2
  let root := Real.sqrt scale
  have hroot : 0 < root := Real.sqrt_pos.mpr hscale
  let lower : ℤ := Int.floor ((-1 - scale / 2) / root)
  let upper : ℤ := Int.floor ((1 + scale / 2) / root)
  have hcenter : ∀ cell ∈ wz1Lemma23ActiveCells prepared.shadow scale hscale,
      |(wz1Lemma23SnappedPoint scale cell) (2 : Fin 3)| ≤
        1 + scale / 2 := by
    intro cell hcell
    rcases (wz1Lemma23_mem_active_iff prepared.shadow hscale cell).mp hcell with
      ⟨_hbounded, point, hpoint, hpointCell⟩
    have hfine : point ∈ twoScale.fine.refined.union := by
      rw [← prepared.shadow_union]
      exact hpoint
    rcases hfine with ⟨index, hindex⟩
    have hsource : point ∈ twoScale.coarseGrains.shading.union :=
      ⟨twoScale.fine.selected.embedding index,
        twoScale.fine.subshading index hindex⟩
    have hbox := shading_union_subset_axisBox hsource
    have hpointHeight : |point (2 : Fin 3)| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
    have hclose :=
      ((wz1_lemma23_snapped_cell_geometry scale hscale hscaleOne).2.1
        cell point hpointCell).1 (2 : Fin 3)
    have htriangle :
        |(wz1Lemma23SnappedPoint scale cell) (2 : Fin 3)| ≤
          |point (2 : Fin 3)| +
            |point (2 : Fin 3) -
              (wz1Lemma23SnappedPoint scale cell) (2 : Fin 3)| := by
      have := abs_add_le (point (2 : Fin 3))
        (-(point (2 : Fin 3) -
          (wz1Lemma23SnappedPoint scale cell) (2 : Fin 3)))
      simpa [abs_neg, abs_sub_comm] using this
    exact htriangle.trans (by linarith)
  have hsubset : pureWZ2CoarseCarrierBlocks prepared ⊆
      Finset.Icc lower upper := by
    intro block hblock
    rcases Finset.mem_image.mp hblock with ⟨cell, hcell, rfl⟩
    have hc := abs_le.mp (hcenter cell hcell)
    rw [Finset.mem_Icc]
    constructor
    · apply Int.floor_mono
      apply div_le_div_of_nonneg_right _ hroot.le
      linarith [hc.1]
    · apply Int.floor_mono
      exact div_le_div_of_nonneg_right hc.2 hroot.le
  have hcardNat : (pureWZ2CoarseCarrierBlocks prepared).card ≤
      (Finset.Icc lower upper).card := Finset.card_le_card hsubset
  have hlowerUpper : lower ≤ upper + 1 := by
    have hreal : ((-1 - scale / 2) / root) ≤
        ((1 + scale / 2) / root) := by
      apply div_le_div_of_nonneg_right _ hroot.le
      linarith
    have hfloor : lower ≤ upper := Int.floor_mono hreal
    omega
  have hcardInt : ((Finset.Icc lower upper).card : ℤ) =
      upper + 1 - lower := Int.card_Icc_of_le lower upper hlowerUpper
  have hcardReal : ((pureWZ2CoarseCarrierBlocks prepared).card : ℝ) ≤
      (upper : ℝ) + 1 - lower := by
    have hcast : ((pureWZ2CoarseCarrierBlocks prepared).card : ℤ) ≤
        (Finset.Icc lower upper).card := by exact_mod_cast hcardNat
    rw [hcardInt] at hcast
    exact_mod_cast hcast
  have hupper : (upper : ℝ) ≤ (1 + scale / 2) / root :=
    Int.floor_le _
  have hlower : ((-1 - scale / 2) / root) < (lower : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hquotient :
      (1 + scale / 2) / root - ((-1 - scale / 2) / root) =
        (2 + scale) / root := by
    field_simp [hroot.ne']
    ring
  have hcardBound : ((pureWZ2CoarseCarrierBlocks prepared).card : ℝ) ≤
      (2 + scale) / root + 2 := by
    rw [← hquotient]
    linarith
  have hmul := mul_le_mul_of_nonneg_right hcardBound hroot.le
  have hcancel : (2 + scale) / root * root = 2 + scale := by
    field_simp [hroot.ne']
  rw [add_mul, hcancel] at hmul
  simpa [scale, root] using hmul

def pureWZ2PositiveCoarseCarrierBlocks
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale) : Finset ℤ :=
  (pureWZ2CoarseCarrierBlocks prepared).filter fun block =>
    0 < MeasureTheory.volume
      (pureWZ2CoarseCarrierBlockShading prepared block).union

theorem pureWZ2PositiveCoarseCarrierBlocks_card_mul_sqrtENN_le
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale) :
    ((pureWZ2PositiveCoarseCarrierBlocks prepared).card : ENNReal) *
        ENNReal.ofReal (Real.sqrt twoScale.rhoRequested.1) ≤
      ENNReal.ofReal
        (2 + twoScale.rhoRequested.1 +
          2 * Real.sqrt twoScale.rhoRequested.1) := by
  have hcard : (pureWZ2PositiveCoarseCarrierBlocks prepared).card ≤
      (pureWZ2CoarseCarrierBlocks prepared).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hreal : ((pureWZ2PositiveCoarseCarrierBlocks prepared).card : ℝ) *
        Real.sqrt twoScale.rhoRequested.1 ≤
      2 + twoScale.rhoRequested.1 +
        2 * Real.sqrt twoScale.rhoRequested.1 := by
    calc
      ((pureWZ2PositiveCoarseCarrierBlocks prepared).card : ℝ) *
            Real.sqrt twoScale.rhoRequested.1 ≤
          ((pureWZ2CoarseCarrierBlocks prepared).card : ℝ) *
            Real.sqrt twoScale.rhoRequested.1 := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast hcard) (Real.sqrt_nonneg _)
      _ ≤ _ := pureWZ2CoarseCarrierBlocks_card_mul_sqrt_le prepared
  have hrhs : 0 ≤ 2 + twoScale.rhoRequested.1 +
      2 * Real.sqrt twoScale.rhoRequested.1 := by
    have hscale : 0 < twoScale.rhoRequested.1 :=
      twoScale.coarseGrains.extremal.delta_pos
    positivity
  rw [← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff hrhs]
  exact hreal

theorem pureWZ2PositiveCoarseCarrierBlock_volume_pos
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {block : ℤ}
    (hblock : block ∈ pureWZ2PositiveCoarseCarrierBlocks prepared) :
    0 < MeasureTheory.volume
      (pureWZ2CoarseCarrierBlockShading prepared block).union := by
  exact (Finset.mem_filter.mp hblock).2

theorem pureWZ2PositiveCoarseCarrierBlocks_volume_eq_sum
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale) :
    MeasureTheory.volume prepared.shadow.union =
      ∑ block ∈ pureWZ2PositiveCoarseCarrierBlocks prepared,
        MeasureTheory.volume
          (pureWZ2CoarseCarrierBlockShading prepared block).union := by
  rw [pureWZ2CoarseCarrierBlock_volume_eq_sum prepared]
  rw [pureWZ2PositiveCoarseCarrierBlocks, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro block _
  by_cases hpositive : 0 < MeasureTheory.volume
      (pureWZ2CoarseCarrierBlockShading prepared block).union
  · simp [hpositive]
  · have hzero : MeasureTheory.volume
        (pureWZ2CoarseCarrierBlockShading prepared block).union = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp hpositive)
    simp [hpositive, hzero]

theorem pureWZ2CoarseCarrierBlockShading_active_window
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale)
    (block : ℤ) :
    ∀ cell ∈ wz1Lemma23ActiveCells
        (pureWZ2CoarseCarrierBlockShading prepared block)
        twoScale.rhoRequested.1
        twoScale.coarseGrains.extremal.delta_pos,
      (wz1Lemma23SnappedPoint twoScale.rhoRequested.1 cell)
          (2 : Fin 3) ∈
        Set.Icc
          (pureWZ2SourceCarrierBlockLeft twoScale.rhoRequested.1 block)
          (pureWZ2SourceCarrierBlockLeft twoScale.rhoRequested.1 block +
            Real.sqrt twoScale.rhoRequested.1) := by
  intro cell hcell
  rcases (wz1Lemma23_mem_active_iff
      (pureWZ2CoarseCarrierBlockShading prepared block)
      twoScale.coarseGrains.extremal.delta_pos cell).mp hcell with
    ⟨_hbounded, point, hpoint, hpointCell⟩
  rcases hpoint with ⟨_sourceIndex, hpointCarrier⟩
  rcases Set.mem_iUnion₂.mp hpointCarrier.2 with
    ⟨sourceCell, hsourceCell, hpointSourceCell⟩
  have hcellEq : sourceCell = cell := hpointSourceCell.symm.trans hpointCell
  have hblock : pureWZ2SourceCarrierBlockIndex
      twoScale.rhoRequested.1 cell = block := by
    rw [← hcellEq]
    exact (Finset.mem_filter.mp hsourceCell).2
  have hspec := pureWZ2SourceCarrierBlockIndex_spec
    twoScale.coarseGrains.extremal.delta_pos cell
  rw [hblock] at hspec
  exact ⟨hspec.1, hspec.2.le⟩

/-- One genuine coarse block obeys the exact-slice AD slab-volume cap. -/
theorem pureWZ2CoarseCarrierBlock_volume_upper
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (block : ℤ) :
    MeasureTheory.volume
        (pureWZ2CoarseCarrierBlockShading prepared block).union ≤
      (32 * (10 * Kakeya.realRpowENN rho (-middleLoss)) *
          Kakeya.realRpowENN rho sigma) *
        ENNReal.ofReal (Real.sqrt rho + 2 * rho) := by
  let shading := pureWZ2CoarseCarrierBlockShading prepared block
  have hsub : IsSubshading shading prepared.shadow :=
    pureWZ2CoarseCarrierBlockShading_subshading prepared block
  have hheight : shading.union ⊆ horizontalSlab
      (pureWZ2SourceCarrierBlockLeft rho block - rho)
      (pureWZ2SourceCarrierBlockLeft rho block + Real.sqrt rho + rho) := by
    intro point hpoint
    have hblockRegion : point ∈
        pureWZ2CoarseCarrierBlockRegion prepared block := by
      rcases hpoint with ⟨sourceIndex, _hsource, hregion⟩
      exact hregion
    rcases Set.mem_iUnion₂.mp hblockRegion with
      ⟨cell, hcell, hpointCell⟩
    have hblock : pureWZ2SourceCarrierBlockIndex
        twoScale.rhoRequested.1 cell = block :=
      (Finset.mem_filter.mp hcell).2
    have hrho : 0 < rho := by
      rw [← twoScale.rhoRequested_eq]
      exact twoScale.coarseGrains.extremal.delta_pos
    have hrhoOne : rho ≤ 1 := by
      rw [← twoScale.rhoRequested_eq]
      exact twoScale.rhoRequested.property.2
    have hcenter := pureWZ2SourceCarrierBlockIndex_spec
      twoScale.coarseGrains.extremal.delta_pos cell
    rw [hblock] at hcenter
    have hpointCenter :=
      ((wz1_lemma23_snapped_cell_geometry
        twoScale.rhoRequested.1
        twoScale.coarseGrains.extremal.delta_pos
        twoScale.rhoRequested.property.2).2.1
        cell point hpointCell).1 (2 : Fin 3)
    rw [abs_le] at hpointCenter
    change point (2 : Fin 3) ∈ Set.Icc _ _
    rw [← twoScale.rhoRequested_eq]
    exact ⟨by linarith [hcenter.1, hpointCenter.2],
      by linarith [hcenter.2, hpointCenter.1]⟩
  have haxis : ∀ point ∈ shading.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hprepared := hsub.union_subset hpoint
    have hfine : point ∈ twoScale.fine.refined.union := by
      rwa [prepared.shadow_union] at hprepared
    have hsource : point ∈ twoScale.coarseGrains.shading.union :=
      ⟨twoScale.fine.selected.embedding hfine.choose,
        twoScale.fine.subshading hfine.choose hfine.choose_spec⟩
    have hbox := shading_union_subset_axisBox hsource
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hslab := paper_exactSlice_slab_volume_le
    shading haxis twoScale.coarseGrains.globalGrains.slope
    (10 * Kakeya.realRpowENN
      twoScale.rhoRequested.1 (-middleLoss))
    twoScale.coarseGrains.extremal.delta_pos
    hsigma hsigmaOne
    (ENNReal.mul_ne_top (by norm_num) (by simp [Kakeya.realRpowENN]))
    (by
      intro z hz
      have hexact := prepared.exactAD z hz
      exact hexact.mono (by
        rintro value ⟨point, hpoint, rfl⟩
        exact ⟨point, ⟨hsub.union_subset hpoint.1, hpoint.2⟩, rfl⟩))
    (a := pureWZ2SourceCarrierBlockLeft rho block - rho)
    (b := pureWZ2SourceCarrierBlockLeft rho block + Real.sqrt rho + rho)
    (by
      have hrho : 0 < rho := by
        rw [← twoScale.rhoRequested_eq]
        exact twoScale.coarseGrains.extremal.delta_pos
      nlinarith [Real.sqrt_pos.mpr hrho])
  have hinter : shading.union ∩ horizontalSlab
      (pureWZ2SourceCarrierBlockLeft rho block - rho)
      (pureWZ2SourceCarrierBlockLeft rho block + Real.sqrt rho + rho) =
      shading.union := Set.inter_eq_left.mpr hheight
  rw [hinter] at hslab
  have hlength :
      pureWZ2SourceCarrierBlockLeft rho block + Real.sqrt rho + rho -
          (pureWZ2SourceCarrierBlockLeft rho block - rho) =
        Real.sqrt rho + 2 * rho := by ring
  rw [hlength] at hslab
  simpa only [twoScale.rhoRequested_eq] using hslab

structure PureWZ2CoarseCarrierBlockWindowData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale)
    (block : ℤ) where
  window : PureWZ2Lemma23WindowedCoarse prepared
  left_eq : window.left = pureWZ2SourceCarrierBlockLeft rho block
  shading_eq :
    window.shading = pureWZ2CoarseCarrierBlockShading prepared block
  volumeSupply_eq :
    window.volumeSupply = MeasureTheory.volume window.shading.union

theorem PureWZ2Lemma23PreparedCoarse.windowDataOfBlock
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale)
    (block : ℤ)
    (hvolume : 0 < MeasureTheory.volume
      (pureWZ2CoarseCarrierBlockShading prepared block).union) :
    Nonempty (PureWZ2CoarseCarrierBlockWindowData prepared block) := by
  let shading := pureWZ2CoarseCarrierBlockShading prepared block
  have hsub : IsSubshading shading prepared.shadow :=
    pureWZ2CoarseCarrierBlockShading_subshading prepared block
  have hball : shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hprepared := hsub.union_subset hpoint
    have hfine : point ∈ twoScale.fine.refined.union := by
      rwa [prepared.shadow_union] at hprepared
    rcases hfine with ⟨index, hindex⟩
    have hsource : point ∈ twoScale.coarseGrains.shading.union :=
      ⟨twoScale.fine.selected.embedding index,
        twoScale.fine.subshading index hindex⟩
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hfinite : MeasureTheory.volume shading.union ≠ ⊤ :=
    ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
      (MeasureTheory.measure_mono hball)
  rcases prepared.ofSubshading
      (pureWZ2SourceCarrierBlockLeft twoScale.rhoRequested.1 block) shading hsub
      (pureWZ2CoarseCarrierBlockShading_active_window prepared block)
      (MeasureTheory.volume shading.union) (by simpa [shading] using hvolume)
      hfinite le_rfl with ⟨window, hleft, hshading, hsupply⟩
  exact ⟨{
    window := window
    left_eq := by simpa [twoScale.rhoRequested_eq] using hleft
    shading_eq := hshading
    volumeSupply_eq := by rw [hsupply, hshading]
  }⟩

end Kakeya.Assouad
