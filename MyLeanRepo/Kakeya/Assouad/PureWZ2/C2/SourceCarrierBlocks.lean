import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCarrierPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PaperExactSliceSlabVolume

/-!
# Finite source-carrier height blocks

The multi-window Lemma-24 argument runs the local graph construction on
disjoint unions of actual graph cells.  Blocks are defined by the center
height of the side-`rho` Lemma-23 cell, using half-open intervals of width
`sqrt rho`; boundary cells therefore belong to exactly one block.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

def pureWZ2SourceCarrierBlockIndex
    (rho : ℝ) (cell : ℤ × ℤ × ℤ) : ℤ :=
  Int.floor
    ((wz1Lemma23SnappedPoint rho cell) (2 : Fin 3) / Real.sqrt rho)

def pureWZ2SourceCarrierBlockLeft (rho : ℝ) (block : ℤ) : ℝ :=
  (block : ℝ) * Real.sqrt rho

def pureWZ2SourceCarrierBlockCells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (block : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  let hrho : 0 < rho := source.extremal.delta_pos.trans_le (by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1)
  (wz1Lemma23ActiveCells prepared.shadow rho hrho).filter fun cell =>
    pureWZ2SourceCarrierBlockIndex rho cell = block

/-- The finite set of height blocks met by the prepared source shadow. -/
def pureWZ2SourceCarrierBlocks
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) : Finset ℤ :=
  let hrho : 0 < rho := source.extremal.delta_pos.trans_le (by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1)
  (wz1Lemma23ActiveCells prepared.shadow rho hrho).image
    (pureWZ2SourceCarrierBlockIndex rho)

def pureWZ2SourceCarrierBlockRegion
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (block : ℤ) : Set Point3 :=
  ⋃ cell ∈ pureWZ2SourceCarrierBlockCells prepared block,
    wz1Lemma23Cell rho cell

def pureWZ2SourceCarrierBlockShading
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (block : ℤ) : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily pullback.shading
        source.extremal.delta_pos) :=
  let region := pureWZ2SourceCarrierBlockRegion prepared block
  { carrier := fun index => prepared.shadow.carrier index ∩ region
    measurable_carrier := fun index =>
      (prepared.shadow.measurable_carrier index).inter
        (MeasurableSet.biUnion
          (pureWZ2SourceCarrierBlockCells prepared block).finite_toSet.countable
          (fun cell _ => wz1Lemma23Cell_measurable
            (source.extremal.delta_pos.trans_le (by
              rw [← twoScale.rhoRequested_eq]
              exact twoScale.rhoRequested.property.1)) cell))
    subset_body := fun index => Set.inter_subset_left.trans
      (prepared.shadow.subset_body index) }

theorem pureWZ2SourceCarrierBlockShading_subshading
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (block : ℤ) :
    IsSubshading
      (pureWZ2SourceCarrierBlockShading prepared block) prepared.shadow :=
  fun _ => Set.inter_subset_left

/-- The prepared carrier is the exact finite union of its height blocks,
tube by tube. -/
theorem pureWZ2SourceCarrierBlock_carrier_partition
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (sourceIndex : Fin
      (pureWZ2ActiveCellFamily pullback.shading
        source.extremal.delta_pos).card) :
    prepared.shadow.carrier sourceIndex =
      ⋃ block ∈ pureWZ2SourceCarrierBlocks prepared,
        (pureWZ2SourceCarrierBlockShading prepared block).carrier
          sourceIndex := by
  let hrho : 0 < rho := source.extremal.delta_pos.trans_le (by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1)
  have hball : prepared.shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hpull : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hpoint
    have hsource := pullback.subshading.union_subset hpull
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  ext point
  constructor
  · intro hpoint
    let cell := wz1Lemma23CellIndex rho point
    let block := pureWZ2SourceCarrierBlockIndex rho cell
    have hpointUnion : point ∈ prepared.shadow.union := ⟨sourceIndex, hpoint⟩
    have hcell : cell ∈ wz1Lemma23ActiveCells prepared.shadow rho hrho :=
      wz1Lemma23_index_mem_active_two hrho hball hpointUnion
    have hblock : block ∈ pureWZ2SourceCarrierBlocks prepared := by
      exact Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨block, hblock, hpoint, ?_⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨cell, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hcell, rfl⟩
  · intro hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨block, _hblock, hpointBlock⟩
    exact hpointBlock.1

/-- Distinct block regions are genuinely disjoint; the half-open block
index and the Lemma-23 cell index are both unique. -/
theorem pureWZ2SourceCarrierBlockRegion_pairwise_disjoint
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) :
    (pureWZ2SourceCarrierBlocks prepared : Set ℤ).PairwiseDisjoint
      (pureWZ2SourceCarrierBlockRegion prepared) := by
  intro first _hfirst second _hsecond hne
  change Disjoint
    (pureWZ2SourceCarrierBlockRegion prepared first)
    (pureWZ2SourceCarrierBlockRegion prepared second)
  rw [Set.disjoint_left]
  intro point hfirst hsecond
  rcases Set.mem_iUnion₂.mp hfirst with
    ⟨firstCell, hfirstCell, hpointFirst⟩
  rcases Set.mem_iUnion₂.mp hsecond with
    ⟨secondCell, hsecondCell, hpointSecond⟩
  have hcellEq : firstCell = secondCell := hpointFirst.symm.trans hpointSecond
  have hfirstBlock :
      pureWZ2SourceCarrierBlockIndex rho firstCell = first :=
    (Finset.mem_filter.mp hfirstCell).2
  have hsecondBlock :
      pureWZ2SourceCarrierBlockIndex rho secondCell = second :=
    (Finset.mem_filter.mp hsecondCell).2
  apply hne
  rw [← hfirstBlock, hcellEq, hsecondBlock]

/-- Distinct block shadings are disjoint tube by tube. -/
theorem pureWZ2SourceCarrierBlock_carrier_pairwise_disjoint
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (sourceIndex : Fin
      (pureWZ2ActiveCellFamily pullback.shading
        source.extremal.delta_pos).card) :
    (pureWZ2SourceCarrierBlocks prepared : Set ℤ).PairwiseDisjoint
      (fun block =>
        (pureWZ2SourceCarrierBlockShading prepared block).carrier
          sourceIndex) := by
  intro first hfirst second hsecond hne
  exact (pureWZ2SourceCarrierBlockRegion_pairwise_disjoint prepared
    hfirst hsecond hne).mono Set.inter_subset_right Set.inter_subset_right

/-- The shaded union is the exact finite union of the block unions. -/
theorem pureWZ2SourceCarrierBlock_union_partition
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) :
    prepared.shadow.union =
      ⋃ block ∈ pureWZ2SourceCarrierBlocks prepared,
        (pureWZ2SourceCarrierBlockShading prepared block).union := by
  ext point
  constructor
  · rintro ⟨sourceIndex, hpoint⟩
    have hpartition := congrArg (fun carrier : Set Point3 => point ∈ carrier)
      (pureWZ2SourceCarrierBlock_carrier_partition prepared sourceIndex)
    rw [hpartition] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨block, hblock, hpointBlock⟩
    exact Set.mem_iUnion₂.mpr ⟨block, hblock, sourceIndex, hpointBlock⟩
  · intro hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨block, _hblock, sourceIndex, hpointBlock⟩
    exact ⟨sourceIndex,
      pureWZ2SourceCarrierBlockShading_subshading prepared block
        sourceIndex hpointBlock⟩

/-- Distinct block unions are genuinely disjoint. -/
theorem pureWZ2SourceCarrierBlock_union_pairwise_disjoint
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) :
    (pureWZ2SourceCarrierBlocks prepared : Set ℤ).PairwiseDisjoint
      (fun block =>
        (pureWZ2SourceCarrierBlockShading prepared block).union) := by
  intro first hfirst second hsecond hne
  exact (pureWZ2SourceCarrierBlockRegion_pairwise_disjoint prepared
    hfirst hsecond hne).mono
      (by rintro point ⟨sourceIndex, _hcarrier, hregion⟩; exact hregion)
      (by rintro point ⟨sourceIndex, _hcarrier, hregion⟩; exact hregion)

/-- Source volume splits exactly across the finite height blocks. -/
theorem pureWZ2SourceCarrierBlock_volume_eq_sum
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) :
    MeasureTheory.volume prepared.shadow.union =
      ∑ block ∈ pureWZ2SourceCarrierBlocks prepared,
        MeasureTheory.volume
          (pureWZ2SourceCarrierBlockShading prepared block).union := by
  rw [pureWZ2SourceCarrierBlock_union_partition prepared]
  exact MeasureTheory.measure_biUnion_finset
    (pureWZ2SourceCarrierBlock_union_pairwise_disjoint prepared)
    (fun block _ =>
      measurableSet_shading_union
        (pureWZ2SourceCarrierBlockShading prepared block))

/-- Indexed shading mass splits exactly across the finite height blocks. -/
theorem pureWZ2SourceCarrierBlock_mass_eq_sum
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) :
    prepared.shadow.mass =
      ∑ block ∈ pureWZ2SourceCarrierBlocks prepared,
        (pureWZ2SourceCarrierBlockShading prepared block).mass := by
  calc
    prepared.shadow.mass =
        ∑ sourceIndex : Fin
            (pureWZ2ActiveCellFamily pullback.shading
              source.extremal.delta_pos).card,
          MeasureTheory.volume (⋃ block ∈
            pureWZ2SourceCarrierBlocks prepared,
              (pureWZ2SourceCarrierBlockShading prepared block).carrier
                sourceIndex) := by
      apply Finset.sum_congr rfl
      intro sourceIndex _
      rw [← pureWZ2SourceCarrierBlock_carrier_partition prepared sourceIndex]
    _ = ∑ sourceIndex : Fin
            (pureWZ2ActiveCellFamily pullback.shading
              source.extremal.delta_pos).card,
          ∑ block ∈ pureWZ2SourceCarrierBlocks prepared,
            MeasureTheory.volume
              ((pureWZ2SourceCarrierBlockShading prepared block).carrier
                sourceIndex) := by
      apply Finset.sum_congr rfl
      intro sourceIndex _
      rw [MeasureTheory.measure_biUnion_finset
        (pureWZ2SourceCarrierBlock_carrier_pairwise_disjoint
          prepared sourceIndex)]
      intro block _
      exact (pureWZ2SourceCarrierBlockShading prepared block).measurable_carrier
        sourceIndex
    _ = ∑ block ∈ pureWZ2SourceCarrierBlocks prepared,
          ∑ sourceIndex : Fin
              (pureWZ2ActiveCellFamily pullback.shading
                source.extremal.delta_pos).card,
            MeasureTheory.volume
              ((pureWZ2SourceCarrierBlockShading prepared block).carrier
                sourceIndex) := by
      rw [Finset.sum_comm]
    _ = ∑ block ∈ pureWZ2SourceCarrierBlocks prepared,
        (pureWZ2SourceCarrierBlockShading prepared block).mass := rfl

/-- The zero-origin block convention meets at most the expected
`O(1 / sqrt rho)` integer blocks.  The extra endpoint term compared with the
min-shifted height pigeonhole is kept explicit. -/
theorem pureWZ2SourceCarrierBlocks_card_mul_sqrt_le
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) :
    (pureWZ2SourceCarrierBlocks prepared).card * Real.sqrt rho ≤
      2 + rho + 2 * Real.sqrt rho := by
  let hrho : 0 < rho := source.extremal.delta_pos.trans_le (by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1)
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  let root := Real.sqrt rho
  have hroot : 0 < root := Real.sqrt_pos.mpr hrho
  let lower : ℤ := Int.floor ((-1 - rho / 2) / root)
  let upper : ℤ := Int.floor ((1 + rho / 2) / root)
  have hcenter : ∀ cell ∈ wz1Lemma23ActiveCells prepared.shadow rho hrho,
      |(wz1Lemma23SnappedPoint rho cell) (2 : Fin 3)| ≤ 1 + rho / 2 := by
    intro cell hcell
    rcases (wz1Lemma23_mem_active_iff prepared.shadow hrho cell).mp hcell with
      ⟨_hbounded, point, hpoint, hpointCell⟩
    have hpull : point ∈ pullback.shading.union := by
      rw [← prepared.shadow_union]
      exact hpoint
    have hbox := shading_union_subset_axisBox hpull
    have hpointHeight : |point (2 : Fin 3)| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
    have hindex : wz1Lemma23CellIndex rho point = cell := hpointCell
    have hclose :=
      ((wz1_lemma23_snapped_cell_geometry rho hrho hrhoOne).2.1
        cell point hindex).1 (2 : Fin 3)
    have htriangle :
        |(wz1Lemma23SnappedPoint rho cell) (2 : Fin 3)| ≤
          |point (2 : Fin 3)| +
            |point (2 : Fin 3) -
              (wz1Lemma23SnappedPoint rho cell) (2 : Fin 3)| := by
      have := abs_add_le (point (2 : Fin 3))
        (-(point (2 : Fin 3) -
          (wz1Lemma23SnappedPoint rho cell) (2 : Fin 3)))
      simpa [abs_neg, abs_sub_comm] using this
    exact htriangle.trans (by linarith)
  have hsubset : pureWZ2SourceCarrierBlocks prepared ⊆
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
  have hcardNat : (pureWZ2SourceCarrierBlocks prepared).card ≤
      (Finset.Icc lower upper).card := Finset.card_le_card hsubset
  have hlowerUpper : lower ≤ upper + 1 := by
    have hreal : ((-1 - rho / 2) / root) ≤
        ((1 + rho / 2) / root) := by
      apply div_le_div_of_nonneg_right _ hroot.le
      linarith
    have hfloor : lower ≤ upper := Int.floor_mono hreal
    omega
  have hcardInt : ((Finset.Icc lower upper).card : ℤ) =
      upper + 1 - lower := Int.card_Icc_of_le lower upper hlowerUpper
  have hcardReal : ((pureWZ2SourceCarrierBlocks prepared).card : ℝ) ≤
      (upper : ℝ) + 1 - lower := by
    have hcast : ((pureWZ2SourceCarrierBlocks prepared).card : ℤ) ≤
        (Finset.Icc lower upper).card := by exact_mod_cast hcardNat
    rw [hcardInt] at hcast
    exact_mod_cast hcast
  have hupper : (upper : ℝ) ≤ (1 + rho / 2) / root := Int.floor_le _
  have hlower : ((-1 - rho / 2) / root) < (lower : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hquotient :
      (1 + rho / 2) / root - ((-1 - rho / 2) / root) =
        (2 + rho) / root := by
    field_simp [hroot.ne']
    ring
  have hcardBound : ((pureWZ2SourceCarrierBlocks prepared).card : ℝ) ≤
      (2 + rho) / root + 2 := by
    rw [← hquotient]
    linarith
  have hmul := mul_le_mul_of_nonneg_right hcardBound hroot.le
  have hcancel : (2 + rho) / root * root = 2 + rho := by
    field_simp [hroot.ne']
  rw [add_mul, hcancel] at hmul
  simpa [root] using hmul

theorem pureWZ2SourceCarrierBlocks_card_mul_sqrtENN_le
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) :
    ((pureWZ2SourceCarrierBlocks prepared).card : ENNReal) *
        ENNReal.ofReal (Real.sqrt rho) ≤
      ENNReal.ofReal (2 + rho + 2 * Real.sqrt rho) := by
  have hreal := pureWZ2SourceCarrierBlocks_card_mul_sqrt_le prepared
  have hrho : 0 < rho := source.extremal.delta_pos.trans_le (by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1)
  have hnonneg : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg _
  have hcast : ((pureWZ2SourceCarrierBlocks prepared).card : ENNReal) =
      ENNReal.ofReal ((pureWZ2SourceCarrierBlocks prepared).card : ℝ) := by
    simp
  rw [hcast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)]
  exact hreal

/-- Blocks with positive source volume. -/
def pureWZ2PositiveSourceCarrierBlocks
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) : Finset ℤ :=
  (pureWZ2SourceCarrierBlocks prepared).filter fun block =>
    0 < MeasureTheory.volume
      (pureWZ2SourceCarrierBlockShading prepared block).union

theorem pureWZ2PositiveSourceCarrierBlock_volume_pos
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {block : ℤ}
    (hblock : block ∈ pureWZ2PositiveSourceCarrierBlocks prepared) :
    0 < MeasureTheory.volume
      (pureWZ2SourceCarrierBlockShading prepared block).union := by
  exact (Finset.mem_filter.mp hblock).2

/-- A zero-volume block has zero indexed shading mass. -/
theorem pureWZ2SourceCarrierBlock_mass_eq_zero_of_volume_eq_zero
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (block : ℤ)
    (hzero : MeasureTheory.volume
      (pureWZ2SourceCarrierBlockShading prepared block).union = 0) :
    (pureWZ2SourceCarrierBlockShading prepared block).mass = 0 := by
  apply Finset.sum_eq_zero
  intro sourceIndex _
  apply le_zero_iff.mp
  calc
    MeasureTheory.volume
        ((pureWZ2SourceCarrierBlockShading prepared block).carrier
          sourceIndex) ≤
      MeasureTheory.volume
        (pureWZ2SourceCarrierBlockShading prepared block).union :=
      MeasureTheory.measure_mono (fun point hpoint => ⟨sourceIndex, hpoint⟩)
    _ = 0 := hzero

/-- Removing zero-volume blocks changes neither the source volume nor its
indexed shading mass. -/
theorem pureWZ2PositiveSourceCarrierBlocks_volume_eq_sum
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) :
    MeasureTheory.volume prepared.shadow.union =
      ∑ block ∈ pureWZ2PositiveSourceCarrierBlocks prepared,
        MeasureTheory.volume
          (pureWZ2SourceCarrierBlockShading prepared block).union := by
  rw [pureWZ2SourceCarrierBlock_volume_eq_sum prepared]
  rw [pureWZ2PositiveSourceCarrierBlocks, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro block _
  by_cases hpositive : 0 < MeasureTheory.volume
      (pureWZ2SourceCarrierBlockShading prepared block).union
  · simp [hpositive]
  · have hzero : MeasureTheory.volume
        (pureWZ2SourceCarrierBlockShading prepared block).union = 0 :=
      not_lt.mp hpositive |> nonpos_iff_eq_zero.mp
    simp [hpositive, hzero]

theorem pureWZ2PositiveSourceCarrierBlocks_weightedSupply_eq
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) :
    (∑ block ∈ pureWZ2PositiveSourceCarrierBlocks prepared,
        MeasureTheory.volume
            (pureWZ2SourceCarrierBlockShading prepared block).union *
          twoScale.coarse.balanced.cellMass) =
      MeasureTheory.volume prepared.shadow.union *
        twoScale.coarse.balanced.cellMass := by
  rw [← Finset.sum_mul, ←
    pureWZ2PositiveSourceCarrierBlocks_volume_eq_sum prepared]

theorem pureWZ2PositiveSourceCarrierBlocks_mass_eq_sum
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) :
    prepared.shadow.mass =
      ∑ block ∈ pureWZ2PositiveSourceCarrierBlocks prepared,
        (pureWZ2SourceCarrierBlockShading prepared block).mass := by
  rw [pureWZ2SourceCarrierBlock_mass_eq_sum prepared]
  rw [pureWZ2PositiveSourceCarrierBlocks, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro block _
  by_cases hpositive : 0 < MeasureTheory.volume
      (pureWZ2SourceCarrierBlockShading prepared block).union
  · simp [hpositive]
  · have hzero : MeasureTheory.volume
        (pureWZ2SourceCarrierBlockShading prepared block).union = 0 :=
      not_lt.mp hpositive |> nonpos_iff_eq_zero.mp
    rw [pureWZ2SourceCarrierBlock_mass_eq_zero_of_volume_eq_zero
      prepared block hzero]
    simp [hpositive]

theorem pureWZ2SourceCarrierBlockIndex_spec
    {rho : ℝ} (hrho : 0 < rho) (cell : ℤ × ℤ × ℤ) :
    (wz1Lemma23SnappedPoint rho cell) (2 : Fin 3) ∈
      Set.Ico
        (pureWZ2SourceCarrierBlockLeft rho
          (pureWZ2SourceCarrierBlockIndex rho cell))
        (pureWZ2SourceCarrierBlockLeft rho
          (pureWZ2SourceCarrierBlockIndex rho cell) + Real.sqrt rho) := by
  let value := (wz1Lemma23SnappedPoint rho cell) (2 : Fin 3)
  let root := Real.sqrt rho
  let block := Int.floor (value / root)
  have hroot : 0 < root := Real.sqrt_pos.mpr hrho
  have hlower : (block : ℝ) ≤ value / root := Int.floor_le _
  have hupper : value / root < (block : ℝ) + 1 :=
    Int.lt_floor_add_one _
  constructor
  · dsimp only [pureWZ2SourceCarrierBlockLeft,
      pureWZ2SourceCarrierBlockIndex, value, root, block]
    have := mul_le_mul_of_nonneg_right hlower hroot.le
    simpa [div_mul_eq_mul_div, hroot.ne'] using this
  · dsimp only [pureWZ2SourceCarrierBlockLeft,
      pureWZ2SourceCarrierBlockIndex, value, root, block]
    have := mul_lt_mul_of_pos_right hupper hroot
    have hcancel : value / root * root = value := by
      field_simp [hroot.ne']
    rw [hcancel] at this
    nlinarith

theorem pureWZ2SourceCarrierBlockShading_active_window
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (block : ℤ) :
    ∀ cell ∈ wz1Lemma23ActiveCells
        (pureWZ2SourceCarrierBlockShading prepared block) rho
        (source.extremal.delta_pos.trans_le (by
          rw [← twoScale.rhoRequested_eq]
          exact twoScale.rhoRequested.property.1)),
      (wz1Lemma23SnappedPoint rho cell) (2 : Fin 3) ∈
        Set.Icc
          (pureWZ2SourceCarrierBlockLeft rho block)
          (pureWZ2SourceCarrierBlockLeft rho block + Real.sqrt rho) := by
  let hrho : 0 < rho := source.extremal.delta_pos.trans_le (by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1)
  intro cell hcell
  rcases (wz1Lemma23_mem_active_iff
      (pureWZ2SourceCarrierBlockShading prepared block) hrho cell).mp hcell with
    ⟨_hbounded, point, hpoint, hpointCell⟩
  rcases hpoint with ⟨sourceIndex, hpointCarrier⟩
  have hregion : point ∈ pureWZ2SourceCarrierBlockRegion prepared block :=
    hpointCarrier.2
  rcases Set.mem_iUnion₂.mp hregion with
    ⟨sourceCell, hsourceCell, hpointSourceCell⟩
  have hsourceIndex : wz1Lemma23CellIndex rho point = sourceCell :=
    hpointSourceCell
  have htargetIndex : wz1Lemma23CellIndex rho point = cell :=
    hpointCell
  have hcellEq : sourceCell = cell := hsourceIndex.symm.trans htargetIndex
  have hblock : pureWZ2SourceCarrierBlockIndex rho cell = block := by
    rw [← hcellEq]
    exact (Finset.mem_filter.mp hsourceCell).2
  have hspec := pureWZ2SourceCarrierBlockIndex_spec hrho cell
  rw [hblock] at hspec
  exact ⟨hspec.1, hspec.2.le⟩

/-- One source block has the exact-slice AD slab-volume upper bound at its
complete-cell height window. -/
theorem pureWZ2SourceCarrierBlock_volume_upper
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (block : ℤ) :
    MeasureTheory.volume
        (pureWZ2SourceCarrierBlockShading prepared block).union ≤
      (32 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
          Kakeya.realRpowENN delta sigma) *
        ENNReal.ofReal (Real.sqrt rho + 2 * rho) := by
  let shading := pureWZ2SourceCarrierBlockShading prepared block
  have hsub : IsSubshading shading prepared.shadow :=
    pureWZ2SourceCarrierBlockShading_subshading prepared block
  have hheight : shading.union ⊆ horizontalSlab
      (pureWZ2SourceCarrierBlockLeft rho block - rho)
      (pureWZ2SourceCarrierBlockLeft rho block + Real.sqrt rho + rho) := by
    intro point hpoint
    have hactive : point ∈ prepared.shadow.union := hsub.union_subset hpoint
    have hblockRegion : point ∈
        pureWZ2SourceCarrierBlockRegion prepared block := by
      rcases hpoint with ⟨sourceIndex, _hsource, hregion⟩
      exact hregion
    rcases Set.mem_iUnion₂.mp hblockRegion with
      ⟨cell, hcell, hpointCell⟩
    have hblock : pureWZ2SourceCarrierBlockIndex rho cell = block :=
      (Finset.mem_filter.mp hcell).2
    have hrho : 0 < rho := source.extremal.delta_pos.trans_le (by
      rw [← twoScale.rhoRequested_eq]
      exact twoScale.rhoRequested.property.1)
    have hrhoOne : rho ≤ 1 := by
      rw [← twoScale.rhoRequested_eq]
      exact twoScale.rhoRequested.property.2
    have hcenter := pureWZ2SourceCarrierBlockIndex_spec hrho cell
    rw [hblock] at hcenter
    have hpointCenter :=
      ((wz1_lemma23_snapped_cell_geometry rho hrho hrhoOne).2.1
        cell point hpointCell).1 (2 : Fin 3)
    rw [abs_le] at hpointCenter
    change point (2 : Fin 3) ∈ Set.Icc _ _
    exact ⟨by linarith [hcenter.1, hpointCenter.2],
      by linarith [hcenter.2, hpointCenter.1]⟩
  have haxis : ∀ point ∈ shading.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hprepared := hsub.union_subset hpoint
    have hpull : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    have hsource := pullback.subshading.union_subset hpull
    have hbox := shading_union_subset_axisBox hsource
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hslab := paper_exactSlice_slab_volume_le
    shading haxis source.globalGrains.slope
    (10 * Kakeya.realRpowENN delta (-inputLoss))
    source.extremal.delta_pos hsigma hsigmaOne
    (ENNReal.mul_ne_top (by norm_num) (by simp [Kakeya.realRpowENN]))
    (by
      intro z hz
      exact (prepared.exactAD_delta z hz).mono (by
        rintro value ⟨point, hpoint, rfl⟩
        exact ⟨point, ⟨hsub.union_subset hpoint.1, hpoint.2⟩, rfl⟩))
    (a := pureWZ2SourceCarrierBlockLeft rho block - rho)
    (b := pureWZ2SourceCarrierBlockLeft rho block + Real.sqrt rho + rho)
    (by
      have hrho : 0 < rho := source.extremal.delta_pos.trans_le (by
        rw [← twoScale.rhoRequested_eq]
        exact twoScale.rhoRequested.property.1)
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
  rwa [hlength] at hslab

/-- A block window together with the exact provenance needed by the
multi-window assembly. -/
structure PureWZ2SourceCarrierBlockWindowData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (block : ℤ) where
  window : PureWZ2SourceCarrierWindow prepared
  left_eq : window.left = pureWZ2SourceCarrierBlockLeft rho block
  shading_eq :
    window.shading = pureWZ2SourceCarrierBlockShading prepared block
  volumeSupply_eq : window.volumeSupply = MeasureTheory.volume window.shading.union

/-- Every occupied half-open block gives a standard local source window with
its exact local volume as supply and explicit block provenance. -/
theorem PureWZ2SourceCarrierPreparation.windowDataOfBlock
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (block : ℤ)
    (hvolume :
      0 < MeasureTheory.volume
        (pureWZ2SourceCarrierBlockShading prepared block).union) :
    Nonempty (PureWZ2SourceCarrierBlockWindowData prepared block) := by
  let shading := pureWZ2SourceCarrierBlockShading prepared block
  have hsub : IsSubshading shading prepared.shadow :=
    pureWZ2SourceCarrierBlockShading_subshading prepared block
  have hball : shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hprepared := hsub.union_subset hpoint
    have hpull : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    have hsource := pullback.subshading.union_subset hpull
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hfinite : MeasureTheory.volume shading.union ≠ ⊤ :=
    ne_top_of_le_ne_top
      Metric.isBounded_closedBall.measure_lt_top.ne
      (MeasureTheory.measure_mono hball)
  have hpositive : 0 < MeasureTheory.volume shading.union := by
    simpa [shading] using hvolume
  rcases PureWZ2SourceCarrierPreparation.ofSubshading
    (prepared := prepared)
    (pureWZ2SourceCarrierBlockLeft rho block) shading hsub
    (pureWZ2SourceCarrierBlockShading_active_window prepared block)
    (MeasureTheory.volume shading.union) hpositive hfinite le_rfl with
    ⟨window, hleft, hshading, hsupply⟩
  exact ⟨{
    window := window
    left_eq := hleft
    shading_eq := hshading
    volumeSupply_eq := by rw [hsupply, hshading]
  }⟩

/-- Compatibility view when the caller does not need block provenance. -/
theorem PureWZ2SourceCarrierPreparation.windowOfBlock
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (block : ℤ)
    (hvolume :
      0 < MeasureTheory.volume
        (pureWZ2SourceCarrierBlockShading prepared block).union) :
    Nonempty (PureWZ2SourceCarrierWindow prepared) := by
  rcases prepared.windowDataOfBlock block hvolume with ⟨data⟩
  exact ⟨data.window⟩

end Kakeya.Assouad
