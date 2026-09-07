import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleWindow
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalExactVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCarrierBlocks
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalGoodBlocks

/-!
# Finite terminal height blocks

The exact terminal active-cell shadow is partitioned by the zero-origin
`sqrt delta` height grid.  Blocks above one quarter of the canonical average
become genuine local terminal windows with their actual union volume as
`volumeSupply`.  The good blocks retain at least half of the source volume.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

def pureWZ2TerminalBlockCells
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (block : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (wz1Lemma23ActiveCells prepared.shadow delta
      terminalSource.delta_pos).filter fun cell =>
    pureWZ2SourceCarrierBlockIndex delta cell = block

def pureWZ2TerminalBlocks
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) : Finset ℤ :=
  (wz1Lemma23ActiveCells prepared.shadow delta
      terminalSource.delta_pos).image
    (pureWZ2SourceCarrierBlockIndex delta)

def pureWZ2TerminalBlockRegion
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (block : ℤ) : Set Point3 :=
  ⋃ cell ∈ pureWZ2TerminalBlockCells prepared block,
    wz1Lemma23Cell delta cell

def pureWZ2TerminalBlockShading
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (block : ℤ) : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily terminalSource.shading
        terminalSource.delta_pos) :=
  let region := pureWZ2TerminalBlockRegion prepared block
  { carrier := fun index => prepared.shadow.carrier index ∩ region
    measurable_carrier := fun index =>
      (prepared.shadow.measurable_carrier index).inter
        (MeasurableSet.biUnion
          (pureWZ2TerminalBlockCells prepared block).finite_toSet.countable
          (fun cell _ => wz1Lemma23Cell_measurable
            terminalSource.delta_pos cell))
    subset_body := fun index => Set.inter_subset_left.trans
      (prepared.shadow.subset_body index) }

theorem pureWZ2TerminalBlockShading_subshading
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (block : ℤ) :
    IsSubshading (pureWZ2TerminalBlockShading prepared block) prepared.shadow :=
  fun _ => Set.inter_subset_left

theorem pureWZ2TerminalBlock_carrier_partition
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (index : Fin (pureWZ2ActiveCellFamily terminalSource.shading
      terminalSource.delta_pos).card) :
    prepared.shadow.carrier index =
      ⋃ block ∈ pureWZ2TerminalBlocks prepared,
        (pureWZ2TerminalBlockShading prepared block).carrier index := by
  have hball : prepared.shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hpaper : point ∈ terminalSource.shading.union := by
      rwa [prepared.shadow_union] at hpoint
    have hnorm := norm_le_two_of_mem_paperShading hpaper
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  ext point
  constructor
  · intro hpoint
    let cell := wz1Lemma23CellIndex delta point
    let block := pureWZ2SourceCarrierBlockIndex delta cell
    have hpointUnion : point ∈ prepared.shadow.union := ⟨index, hpoint⟩
    have hcell : cell ∈ wz1Lemma23ActiveCells prepared.shadow delta
        terminalSource.delta_pos :=
      wz1Lemma23_index_mem_active_two terminalSource.delta_pos
        hball hpointUnion
    have hblock : block ∈ pureWZ2TerminalBlocks prepared :=
      Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
    exact Set.mem_iUnion₂.mpr ⟨block, hblock, hpoint,
      Set.mem_iUnion₂.mpr ⟨cell, Finset.mem_filter.mpr ⟨hcell, rfl⟩, rfl⟩⟩
  · intro hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨block, _hblock, hpointBlock⟩
    exact hpointBlock.1

theorem pureWZ2TerminalBlockRegion_pairwise_disjoint
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) :
    (pureWZ2TerminalBlocks prepared : Set ℤ).PairwiseDisjoint
      (pureWZ2TerminalBlockRegion prepared) := by
  intro first _ second _ hne
  change Disjoint
    (pureWZ2TerminalBlockRegion prepared first)
    (pureWZ2TerminalBlockRegion prepared second)
  rw [Set.disjoint_left]
  intro point hfirst hsecond
  rcases Set.mem_iUnion₂.mp hfirst with
    ⟨firstCell, hfirstCell, hpointFirst⟩
  rcases Set.mem_iUnion₂.mp hsecond with
    ⟨secondCell, hsecondCell, hpointSecond⟩
  have hcellEq : firstCell = secondCell := hpointFirst.symm.trans hpointSecond
  have hfirstBlock := (Finset.mem_filter.mp hfirstCell).2
  have hsecondBlock := (Finset.mem_filter.mp hsecondCell).2
  apply hne
  rw [← hfirstBlock, hcellEq, hsecondBlock]

theorem pureWZ2TerminalBlock_union_partition
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) :
    prepared.shadow.union =
      ⋃ block ∈ pureWZ2TerminalBlocks prepared,
        (pureWZ2TerminalBlockShading prepared block).union := by
  ext point
  constructor
  · rintro ⟨index, hpoint⟩
    have hpartition := congrArg (fun carrier : Set Point3 => point ∈ carrier)
      (pureWZ2TerminalBlock_carrier_partition prepared index)
    rw [hpartition] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨block, hblock, hpointBlock⟩
    exact Set.mem_iUnion₂.mpr ⟨block, hblock, index, hpointBlock⟩
  · intro hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨block, _hblock, index, hpointBlock⟩
    exact ⟨index, pureWZ2TerminalBlockShading_subshading
      prepared block index hpointBlock⟩

theorem pureWZ2TerminalBlock_union_pairwise_disjoint
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) :
    (pureWZ2TerminalBlocks prepared : Set ℤ).PairwiseDisjoint
      (fun block => (pureWZ2TerminalBlockShading prepared block).union) := by
  intro first hfirst second hsecond hne
  exact (pureWZ2TerminalBlockRegion_pairwise_disjoint prepared
    hfirst hsecond hne).mono
      (by rintro point ⟨_index, _hcarrier, hregion⟩; exact hregion)
      (by rintro point ⟨_index, _hcarrier, hregion⟩; exact hregion)

theorem pureWZ2TerminalBlock_volume_eq_sum
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) :
    volume prepared.shadow.union =
      ∑ block ∈ pureWZ2TerminalBlocks prepared,
        volume (pureWZ2TerminalBlockShading prepared block).union := by
  rw [pureWZ2TerminalBlock_union_partition prepared]
  exact MeasureTheory.measure_biUnion_finset
    (pureWZ2TerminalBlock_union_pairwise_disjoint prepared)
    (fun block _ => measurableSet_shading_union
      (pureWZ2TerminalBlockShading prepared block))

theorem pureWZ2TerminalBlocks_card_mul_sqrtENN_le
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) :
    ((pureWZ2TerminalBlocks prepared).card : ENNReal) *
        ENNReal.ofReal (Real.sqrt delta) ≤
      ENNReal.ofReal (2 + delta + 2 * Real.sqrt delta) := by
  -- The proof is carrier-independent; the source-block argument uses only the
  -- paper height bound and the zero-origin floor partition.
  let root := Real.sqrt delta
  have hdelta : 0 < delta := terminalSource.delta_pos
  have hdeltaOne : delta ≤ 1 := terminalSource.delta_le_one
  have hroot : 0 < root := Real.sqrt_pos.mpr hdelta
  let lower : ℤ := Int.floor ((-1 - delta / 2) / root)
  let upper : ℤ := Int.floor ((1 + delta / 2) / root)
  have hcenter : ∀ cell ∈ wz1Lemma23ActiveCells prepared.shadow delta hdelta,
      |(wz1Lemma23SnappedPoint delta cell) (2 : Fin 3)| ≤ 1 + delta / 2 := by
    intro cell hcell
    rcases (wz1Lemma23_mem_active_iff prepared.shadow hdelta cell).mp hcell with
      ⟨_hbounded, point, hpoint, hpointCell⟩
    have hpaper : point ∈ terminalSource.shading.union := by
      rw [← prepared.shadow_union]
      exact hpoint
    have hbox := shading_union_subset_axisBox hpaper
    have hp : |point (2 : Fin 3)| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
    have hclose := ((wz1_lemma23_snapped_cell_geometry delta hdelta hdeltaOne).2.1
      cell point hpointCell).1 (2 : Fin 3)
    rw [abs_le]
    constructor <;> nlinarith [abs_le.mp hp, abs_le.mp hclose]
  have hsubset : pureWZ2TerminalBlocks prepared ⊆ Finset.Icc lower upper := by
    intro block hblock
    rcases Finset.mem_image.mp hblock with ⟨cell, hcell, rfl⟩
    have hc := abs_le.mp (hcenter cell hcell)
    rw [Finset.mem_Icc]
    constructor
    · apply Int.floor_mono
      exact div_le_div_of_nonneg_right (by linarith [hc.1]) hroot.le
    · apply Int.floor_mono
      exact div_le_div_of_nonneg_right hc.2 hroot.le
  have hcardNat := Finset.card_le_card hsubset
  have hlowerUpper : lower ≤ upper + 1 := by
    have hreal : ((-1 - delta / 2) / root) ≤
        ((1 + delta / 2) / root) := by
      apply div_le_div_of_nonneg_right _ hroot.le
      linarith
    have := Int.floor_mono hreal
    omega
  have hcardInt : ((Finset.Icc lower upper).card : ℤ) =
      upper + 1 - lower := Int.card_Icc_of_le lower upper hlowerUpper
  have hcardReal : ((pureWZ2TerminalBlocks prepared).card : ℝ) ≤
      (upper : ℝ) + 1 - lower := by
    have hcast : ((pureWZ2TerminalBlocks prepared).card : ℤ) ≤
        (Finset.Icc lower upper).card := by exact_mod_cast hcardNat
    rw [hcardInt] at hcast
    exact_mod_cast hcast
  have hupper : (upper : ℝ) ≤ (1 + delta / 2) / root := Int.floor_le _
  have hlower : ((-1 - delta / 2) / root) < (lower : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hquotient : (1 + delta / 2) / root -
      ((-1 - delta / 2) / root) = (2 + delta) / root := by
    field_simp [hroot.ne']
    ring
  have hcardBound : ((pureWZ2TerminalBlocks prepared).card : ℝ) ≤
      (2 + delta) / root + 2 := by
    rw [← hquotient]
    linarith
  have hmul := mul_le_mul_of_nonneg_right hcardBound hroot.le
  have hcancel : (2 + delta) / root * root = 2 + delta := by
    field_simp [hroot.ne']
  rw [add_mul, hcancel] at hmul
  have hreal : ((pureWZ2TerminalBlocks prepared).card : ℝ) *
      Real.sqrt delta ≤ 2 + delta + 2 * Real.sqrt delta := by
    simpa [root] using hmul
  have hcast : ((pureWZ2TerminalBlocks prepared).card : ENNReal) =
      ENNReal.ofReal ((pureWZ2TerminalBlocks prepared).card : ℝ) := by simp
  rw [hcast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)]
  exact hreal

def pureWZ2GoodTerminalBlocks
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) : Finset ℤ :=
  let threshold := (4 : ENNReal)⁻¹ *
    pureWZ2TerminalExactWindowSupply (volume prepared.shadow.union) delta
  (pureWZ2TerminalBlocks prepared).filter fun block =>
    threshold ≤ volume (pureWZ2TerminalBlockShading prepared block).union

theorem pureWZ2GoodTerminalBlocks_half
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) :
    volume prepared.shadow.union ≤
      2 * ∑ block ∈ pureWZ2GoodTerminalBlocks prepared,
        volume (pureWZ2TerminalBlockShading prepared block).union := by
  let blocks := pureWZ2TerminalBlocks prepared
  let threshold := (4 : ENNReal)⁻¹ *
    pureWZ2TerminalExactWindowSupply (volume prepared.shadow.union) delta
  have hpreparedTop : volume prepared.shadow.union ≠ ⊤ := by
    have hball : prepared.shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
      intro point hpoint
      have hpaper : point ∈ terminalSource.shading.union := by
        rwa [prepared.shadow_union] at hpoint
      have hnorm := norm_le_two_of_mem_paperShading hpaper
      simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
    exact ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
      (measure_mono hball)
  have hthresholdTop : threshold ≠ ⊤ := by
    dsimp only [threshold, pureWZ2TerminalExactWindowSupply]
    exact ENNReal.mul_ne_top (by simp) <|
      ENNReal.div_ne_top
        (ENNReal.mul_ne_top hpreparedTop ENNReal.ofReal_ne_top)
        (ENNReal.ofReal_pos.mpr (by
          nlinarith [source.extremal.delta_pos, Real.sqrt_nonneg delta])).ne'
  have hsmall : 2 * ((blocks.card : ENNReal) * threshold) ≤
      volume prepared.shadow.union := by
    have hcard := pureWZ2TerminalBlocks_card_mul_sqrtENN_le prepared
    have hdenomReal : 2 + delta + 2 * Real.sqrt delta ≤
        2 * (2 + delta + Real.sqrt delta) := by
      nlinarith [source.extremal.delta_pos, Real.sqrt_nonneg delta]
    have hdenom : ENNReal.ofReal (2 + delta + 2 * Real.sqrt delta) ≤
        2 * ENNReal.ofReal (2 + delta + Real.sqrt delta) := by
      calc
        _ ≤ ENNReal.ofReal (2 * (2 + delta + Real.sqrt delta)) :=
          ENNReal.ofReal_mono hdenomReal
        _ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
    have hcardDenom : (blocks.card : ENNReal) *
        ENNReal.ofReal (Real.sqrt delta) ≤
          2 * ENNReal.ofReal (2 + delta + Real.sqrt delta) :=
      hcard.trans hdenom
    let V := volume prepared.shadow.union
    let root := ENNReal.ofReal (Real.sqrt delta)
    let denom := ENNReal.ofReal (2 + delta + Real.sqrt delta)
    have hrootZero : root ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr source.extremal.delta_pos)).ne'
    have hrootTop : root ≠ ⊤ := ENNReal.ofReal_ne_top
    have hdenomZero : denom ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (by
        nlinarith [source.extremal.delta_pos, Real.sqrt_nonneg delta])).ne'
    have hdenomTop : denom ≠ ⊤ := ENNReal.ofReal_ne_top
    have htwoQuarter : (2 : ENNReal) * (4 : ENNReal)⁻¹ =
        (2 : ENNReal)⁻¹ := by
      rw [show (4 : ENNReal) = 2 * 2 by norm_num]
      rw [ENNReal.mul_inv (by norm_num) (by norm_num)]
      calc
        (2 : ENNReal) * (2⁻¹ * 2⁻¹) = (2 * 2⁻¹) * 2⁻¹ := by ac_rfl
        _ = 2⁻¹ := by rw [ENNReal.mul_inv_cancel] <;> norm_num
    have hhalfCard : (2 : ENNReal)⁻¹ *
        ((blocks.card : ENNReal) * root) ≤ denom := by
      calc
        (2 : ENNReal)⁻¹ * ((blocks.card : ENNReal) * root) ≤
            (2 : ENNReal)⁻¹ * (2 * denom) := by gcongr
        _ = denom := by
          calc
            (2 : ENNReal)⁻¹ * (2 * denom) =
                ((2 : ENNReal)⁻¹ * 2) * denom := by ac_rfl
            _ = denom := by
              rw [ENNReal.inv_mul_cancel] <;> norm_num
    have hscaled :
        (2 * ((blocks.card : ENNReal) * threshold)) * denom ≤
          V * denom := by
      dsimp only [threshold, pureWZ2TerminalExactWindowSupply, V, root, denom]
      calc
        (2 * ((blocks.card : ENNReal) *
            ((4 : ENNReal)⁻¹ * (V * root / denom)))) * denom =
          ((2 * (4 : ENNReal)⁻¹) *
            ((blocks.card : ENNReal) * root) * V) *
              (denom⁻¹ * denom) := by
                rw [div_eq_mul_inv]
                simp only [mul_assoc, mul_comm, mul_left_comm]
        _ = ((2 : ENNReal)⁻¹ * ((blocks.card : ENNReal) * root)) * V := by
          rw [ENNReal.inv_mul_cancel hdenomZero hdenomTop, mul_one, htwoQuarter]
        _ ≤ denom * V := by gcongr
        _ = V * denom := mul_comm _ _
    have hscaled' : denom * (2 * ((blocks.card : ENNReal) * threshold)) ≤
        denom * V := by simpa [mul_comm] using hscaled
    exact (ENNReal.mul_le_mul_iff_right hdenomZero hdenomTop).mp hscaled'
  have hraw := finset_good_weighted_supply_retains_half
    blocks (fun block => volume
      (pureWZ2TerminalBlockShading prepared block).union) 1 threshold
    hthresholdTop
  have hsmallSum : 2 * ((blocks.card : ENNReal) * threshold) ≤
      ∑ block ∈ blocks,
        volume (pureWZ2TerminalBlockShading prepared block).union * 1 := by
    have hsum := pureWZ2TerminalBlock_volume_eq_sum prepared
    change 2 * ((blocks.card : ENNReal) * threshold) ≤ _
    simpa only [mul_one, blocks, ← hsum] using hsmall
  have hretained := hraw hsmallSum
  simp only [mul_one] at hretained
  change (∑ block ∈ pureWZ2TerminalBlocks prepared,
      volume (pureWZ2TerminalBlockShading prepared block).union) ≤ _ at hretained
  rw [← pureWZ2TerminalBlock_volume_eq_sum prepared] at hretained
  simpa [blocks, threshold, pureWZ2GoodTerminalBlocks] using hretained

/-- The good terminal block family is nonempty.  This is the direct positive-
volume consequence of the half-retention estimate above. -/
theorem pureWZ2GoodTerminalBlocks_nonempty
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) :
    (pureWZ2GoodTerminalBlocks prepared).Nonempty := by
  have hvolumePos : 0 < volume prepared.shadow.union := by
    rw [prepared.shadow_union]
    exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos terminalSource.delta_pos _)).trans_le
      terminalSource.volume_lower
  by_contra hempty
  have hgoodEmpty : pureWZ2GoodTerminalBlocks prepared = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hhalf := pureWZ2GoodTerminalBlocks_half prepared
  rw [hgoodEmpty] at hhalf
  simp only [Finset.sum_empty, mul_zero] at hhalf
  exact (not_le_of_gt hvolumePos) hhalf

/-- Every active cell of one terminal block has its snapped center in the
corresponding `sqrt delta` height interval.  This geometric fact is independent
of the old global-average good-block threshold. -/
theorem pureWZ2TerminalBlockShading_active_window
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (block : ℤ) :
    ∀ cell ∈ wz1Lemma23ActiveCells
        (pureWZ2TerminalBlockShading prepared block) delta
        terminalSource.delta_pos,
      (wz1Lemma23SnappedPoint delta cell) (2 : Fin 3) ∈
        Set.Icc (pureWZ2SourceCarrierBlockLeft delta block)
          (pureWZ2SourceCarrierBlockLeft delta block + Real.sqrt delta) := by
  intro cell hcell
  rcases (wz1Lemma23_mem_active_iff
    (pureWZ2TerminalBlockShading prepared block)
    terminalSource.delta_pos cell).mp hcell with
    ⟨_bounded, point, hpoint, hpointCell⟩
  rcases hpoint with ⟨index, hcarrier⟩
  rcases Set.mem_iUnion₂.mp hcarrier.2 with
    ⟨sourceCell, hsourceCell, hpointSourceCell⟩
  have hcellEq : sourceCell = cell := hpointSourceCell.symm.trans hpointCell
  have hlabel : pureWZ2SourceCarrierBlockIndex delta cell = block := by
    rw [← hcellEq]
    exact (Finset.mem_filter.mp hsourceCell).2
  have hspec := pureWZ2SourceCarrierBlockIndex_spec
    terminalSource.delta_pos cell
  rw [hlabel] at hspec
  exact ⟨hspec.1, hspec.2.le⟩

structure PureWZ2TerminalBlockWindowData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (block : ℤ) where
  window : PureWZ2TerminalWindow prepared
  left_eq : window.left = pureWZ2SourceCarrierBlockLeft delta block
  shading_eq : window.shading = pureWZ2TerminalBlockShading prepared block
  supply_eq : window.volumeSupply = volume window.shading.union
  minimum_supply :
    (4 : ENNReal)⁻¹ *
        (volume prepared.shadow.union * ENNReal.ofReal (Real.sqrt delta) /
          ENNReal.ofReal (2 + delta + Real.sqrt delta)) ≤
      window.volumeSupply

theorem PureWZ2TerminalLemma23Prepared.windowDataOfGoodBlock
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    {block : ℤ} (hblock : block ∈ pureWZ2GoodTerminalBlocks prepared) :
    Nonempty (PureWZ2TerminalBlockWindowData prepared block) := by
  let shading := pureWZ2TerminalBlockShading prepared block
  let supply := volume shading.union
  have hminimum : (4 : ENNReal)⁻¹ *
      pureWZ2TerminalExactWindowSupply (volume prepared.shadow.union) delta ≤
        supply := (Finset.mem_filter.mp hblock).2
  have hminimum' : (4 : ENNReal)⁻¹ *
        (volume prepared.shadow.union * ENNReal.ofReal (Real.sqrt delta) /
          ENNReal.ofReal (2 + delta + Real.sqrt delta)) ≤ supply := by
    simpa [pureWZ2TerminalExactWindowSupply] using hminimum
  have hsupplyPos : 0 < supply := by
    have hprepared : 0 < volume prepared.shadow.union := by
      rw [prepared.shadow_union]
      exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos terminalSource.delta_pos _)).trans_le
        terminalSource.volume_lower
    have hthresholdPos : 0 < (4 : ENNReal)⁻¹ *
        pureWZ2TerminalExactWindowSupply (volume prepared.shadow.union) delta := by
      dsimp only [pureWZ2TerminalExactWindowSupply]
      apply ENNReal.mul_pos
      · norm_num
      · exact (ENNReal.div_pos
          (ENNReal.mul_pos hprepared.ne'
            (ENNReal.ofReal_pos.mpr
              (Real.sqrt_pos.mpr source.extremal.delta_pos)).ne').ne'
          ENNReal.ofReal_ne_top).ne'
    exact hthresholdPos.trans_le hminimum
  have hsupplyTop : supply ≠ ⊤ := by
    have hball : shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
      intro point hpoint
      have hprepared := pureWZ2TerminalBlockShading_subshading
        prepared block |>.union_subset hpoint
      have hpaper : point ∈ terminalSource.shading.union := by
        rwa [prepared.shadow_union] at hprepared
      have hnorm := norm_le_two_of_mem_paperShading hpaper
      simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
    exact ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
      (measure_mono hball)
  have hactive := pureWZ2TerminalBlockShading_active_window prepared block
  rcases prepared.windowOfSubshading
      (pureWZ2SourceCarrierBlockLeft delta block) shading
      (pureWZ2TerminalBlockShading_subshading prepared block) hactive
      supply hsupplyPos hsupplyTop hminimum' le_rfl with
    ⟨window, hleft, hshading, hsupply⟩
  let graphWindow := window.toGraphWindow
  exact ⟨{
    window := graphWindow
    left_eq := hleft
    shading_eq := hshading
    supply_eq := by
      change window.volumeSupply = volume window.shading.union
      rw [hsupply, hshading]
    minimum_supply := by
      change (4 : ENNReal)⁻¹ *
          (volume prepared.shadow.union * ENNReal.ofReal (Real.sqrt delta) /
            ENNReal.ofReal (2 + delta + Real.sqrt delta)) ≤
        window.volumeSupply
      exact window.minimum_supply }⟩

end Kakeya.Assouad

end
