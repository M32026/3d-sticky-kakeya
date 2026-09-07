import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.BalancedSafeWindowPhases

/-!
# Finite block family on one safe balanced phase

The chosen phase is partitioned by its literal `sqrt rho` block index.  Each
fiber is definitionally the safe-cell set of one carrier-faithful balanced
window, and the fiber cardinalities sum to the full retained phase.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

def pureWZ2BalancedWindowPhaseLeftAt
    (rho : ℝ) (phase : Bool) (block : ℤ) : ℝ :=
  (block : ℝ) * Real.sqrt rho +
    pureWZ2BalancedWindowPhaseShift rho phase

def pureWZ2BalancedSafePhaseBlocks
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (phase : Bool) : Finset ℤ :=
  (pureWZ2BalancedSafePhaseCells
    (pullback := pullback) phase).image
      (pureWZ2BalancedWindowPhaseBlock rho phase)

def pureWZ2BalancedSafePhaseBlockCells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (phase : Bool) (block : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (pureWZ2BalancedSafePhaseCells
    (pullback := pullback) phase).filter fun cell =>
      pureWZ2BalancedWindowPhaseBlock rho phase cell = block

theorem pureWZ2BalancedSafePhaseBlockCells_eq_windowCells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (phase : Bool) (block : ℤ) :
    pureWZ2BalancedSafePhaseBlockCells
        (pullback := pullback) phase block =
      pureWZ2BalancedSafeWindowCells
        (pullback := pullback)
        (pureWZ2BalancedWindowPhaseLeftAt rho phase block) := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hroot : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  ext cell
  constructor
  · intro hcell
    have houter := Finset.mem_filter.mp hcell
    have hsafePhase := (Finset.mem_filter.mp houter.1).2
    have hselected := (Finset.mem_filter.mp houter.1).1
    apply Finset.mem_filter.mpr
    refine ⟨hselected, ?_⟩
    rw [pureWZ2BalancedCellSafeAtPhase] at hsafePhase
    simpa [pureWZ2BalancedWindowPhaseLeft,
      pureWZ2BalancedWindowPhaseLeftAt, houter.2] using hsafePhase
  · intro hcell
    have hdata := Finset.mem_filter.mp hcell
    let center := pureWZ2PaperCellCenterHeight rho cell
    let shift := pureWZ2BalancedWindowPhaseShift rho phase
    let root := Real.sqrt rho
    have hblock :
        pureWZ2BalancedWindowPhaseBlock rho phase cell = block := by
      apply Int.floor_eq_iff.mpr
      have hlower : (block : ℝ) ≤ (center - shift) / root := by
        apply (le_div_iff₀ hroot).2
        dsimp only [center, shift, root]
        have := hdata.2.1
        dsimp only [pureWZ2BalancedWindowPhaseLeftAt] at this
        linarith [hrho]
      have hupper : (center - shift) / root < (block : ℝ) + 1 := by
        apply (div_lt_iff₀ hroot).2
        dsimp only [center, shift, root]
        have := hdata.2.2
        dsimp only [pureWZ2BalancedWindowPhaseLeftAt] at this
        linarith [hrho]
      exact ⟨hlower, hupper⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hdata.1, ?_⟩, hblock⟩
    rw [pureWZ2BalancedCellSafeAtPhase]
    simpa [pureWZ2BalancedWindowPhaseLeft,
      pureWZ2BalancedWindowPhaseLeftAt, hblock] using hdata.2

theorem pureWZ2BalancedSafePhaseBlockCells_nonempty
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {phase : Bool} {block : ℤ}
    (hblock : block ∈ pureWZ2BalancedSafePhaseBlocks
      (pullback := pullback) phase) :
    (pureWZ2BalancedSafePhaseBlockCells
      (pullback := pullback) phase block).Nonempty := by
  rcases Finset.mem_image.mp hblock with ⟨cell, hcell, hlabel⟩
  exact ⟨cell, Finset.mem_filter.mpr ⟨hcell, hlabel⟩⟩

theorem pureWZ2BalancedSafePhase_card_eq_sum_blocks
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (phase : Bool) :
    (pureWZ2BalancedSafePhaseCells
        (pullback := pullback) phase).card =
      ∑ block ∈ pureWZ2BalancedSafePhaseBlocks
          (pullback := pullback) phase,
        (pureWZ2BalancedSafePhaseBlockCells
          (pullback := pullback) phase block).card := by
  let cells := pureWZ2BalancedSafePhaseCells
    (pullback := pullback) phase
  let label := pureWZ2BalancedWindowPhaseBlock rho phase
  have hmaps : Set.MapsTo label (cells : Set (ℤ × ℤ × ℤ))
      (cells.image label : Set ℤ) :=
    fun cell hcell => Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
  simpa [cells, label, pureWZ2BalancedSafePhaseBlocks,
    pureWZ2BalancedSafePhaseBlockCells] using
      Finset.card_eq_sum_card_fiberwise hmaps

structure PureWZ2BalancedSafeBlockFamilyData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) where
  phase : Bool
  selected_card : pullback.selectedCells.card ≤
    2 * (pureWZ2BalancedSafePhaseCells
      (pullback := pullback) phase).card
  blocks : Finset ℤ :=
    pureWZ2BalancedSafePhaseBlocks (pullback := pullback) phase
  blocks_eq : blocks =
    pureWZ2BalancedSafePhaseBlocks (pullback := pullback) phase
  blockWindow : ∀ block : {block // block ∈ blocks},
    PureWZ2BalancedSafeWindowData prepared
      (pureWZ2BalancedWindowPhaseLeftAt rho phase block.1)
  block_cells : ∀ block, (blockWindow block).cells =
    pureWZ2BalancedSafePhaseBlockCells
      (pullback := pullback) phase block.1
  phase_card_eq :
    (pureWZ2BalancedSafePhaseCells
      (pullback := pullback) phase).card =
      ∑ block : {block // block ∈ blocks},
        (blockWindow block).cells.card

theorem PureWZ2SourceCarrierPreparation.balancedSafeBlockFamily
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (hmargin : 4 * rho ≤ Real.sqrt rho) :
    Nonempty (PureWZ2BalancedSafeBlockFamilyData prepared) := by
  rcases pureWZ2_exists_balanced_safe_phase
      (pullback := pullback) hmargin with ⟨phase, hphaseCard⟩
  let blocks := pureWZ2BalancedSafePhaseBlocks
    (pullback := pullback) phase
  have hwindow : ∀ block : {block // block ∈ blocks},
      Nonempty (PureWZ2BalancedSafeWindowData prepared
        (pureWZ2BalancedWindowPhaseLeftAt rho phase block.1)) := by
    intro block
    apply prepared.balancedSafeWindow
    rw [← pureWZ2BalancedSafePhaseBlockCells_eq_windowCells]
    exact pureWZ2BalancedSafePhaseBlockCells_nonempty block.2
  let blockWindow : ∀ block : {block // block ∈ blocks},
      PureWZ2BalancedSafeWindowData prepared
        (pureWZ2BalancedWindowPhaseLeftAt rho phase block.1) :=
    fun block => Classical.choice (hwindow block)
  have hblockCells : ∀ block, (blockWindow block).cells =
      pureWZ2BalancedSafePhaseBlockCells
        (pullback := pullback) phase block.1 := by
    intro block
    rw [(blockWindow block).cells_eq,
      ← pureWZ2BalancedSafePhaseBlockCells_eq_windowCells]
  have hphaseSum :
      (pureWZ2BalancedSafePhaseCells
        (pullback := pullback) phase).card =
        ∑ block : {block // block ∈ blocks},
          (blockWindow block).cells.card := by
    calc
      (pureWZ2BalancedSafePhaseCells
          (pullback := pullback) phase).card =
          ∑ block ∈ blocks,
            (pureWZ2BalancedSafePhaseBlockCells
              (pullback := pullback) phase block).card := by
        simpa [blocks] using
          pureWZ2BalancedSafePhase_card_eq_sum_blocks
            (pullback := pullback) phase
      _ = ∑ block : {block // block ∈ blocks},
            (pureWZ2BalancedSafePhaseBlockCells
              (pullback := pullback) phase block.1).card :=
        Finset.sum_subtype blocks (fun _ => Iff.rfl) _
      _ = ∑ block : {block // block ∈ blocks},
            (blockWindow block).cells.card := by
        apply Finset.sum_congr rfl
        intro block _
        rw [hblockCells block]
  exact ⟨{
    phase := phase
    selected_card := hphaseCard
    blocks := blocks
    blocks_eq := rfl
    blockWindow := blockWindow
    block_cells := hblockCells
    phase_card_eq := hphaseSum
  }⟩

/-- The selected safe phase retains half of the exact pullback union volume. -/
theorem PureWZ2BalancedSafeBlockFamilyData.volume_half
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (data : PureWZ2BalancedSafeBlockFamilyData prepared) :
    MeasureTheory.volume prepared.shadow.union ≤
      2 * ∑ block : {block // block ∈ data.blocks},
        MeasureTheory.volume (data.blockWindow block).shading.union := by
  have hselected :
      (pullback.selectedCells.card : ENNReal) ≤
        2 * ((pureWZ2BalancedSafePhaseCells
          (pullback := pullback) data.phase).card : ENNReal) := by
    exact_mod_cast data.selected_card
  calc
    MeasureTheory.volume prepared.shadow.union =
        (pullback.selectedCells.card : ENNReal) *
          twoScale.coarse.balanced.cellMass := by
      rw [prepared.shadow_union, pullback.volume_eq]
    _ ≤ (2 * ((pureWZ2BalancedSafePhaseCells
          (pullback := pullback) data.phase).card : ENNReal)) *
          twoScale.coarse.balanced.cellMass := by
      gcongr
    _ = 2 * ∑ block : {block // block ∈ data.blocks},
          MeasureTheory.volume (data.blockWindow block).shading.union := by
      have hphase :
          ((pureWZ2BalancedSafePhaseCells
            (pullback := pullback) data.phase).card : ENNReal) =
            ∑ block : {block // block ∈ data.blocks},
              ((data.blockWindow block).cells.card : ENNReal) := by
        exact_mod_cast data.phase_card_eq
      rw [hphase]
      calc
        (2 * ∑ block : {block // block ∈ data.blocks},
              ((data.blockWindow block).cells.card : ENNReal)) *
            twoScale.coarse.balanced.cellMass =
          2 * ∑ block : {block // block ∈ data.blocks},
            ((data.blockWindow block).cells.card : ENNReal) *
              twoScale.coarse.balanced.cellMass := by
            rw [mul_assoc, Finset.sum_mul]
        _ = 2 * ∑ block : {block // block ∈ data.blocks},
              MeasureTheory.volume
                (data.blockWindow block).shading.union := by
            congr 1
            apply Finset.sum_congr rfl
            intro block _
            exact (data.blockWindow block).volume_eq.symm

theorem PureWZ2BalancedSafeBlockFamilyData.blocks_nonempty
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (data : PureWZ2BalancedSafeBlockFamilyData prepared) :
    data.blocks.Nonempty := by
  have hselectedNonempty : pullback.selectedCells.Nonempty := by
    by_contra hnone
    have hcells : pullback.selectedCells = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnone
    have hfinePos : 0 < MeasureTheory.volume twoScale.fine.refined.union :=
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos
        twoScale.coarseGrains.extremal.delta_pos _)).trans_le
        twoScale.fine.refined_volume_lower
    rw [← pullback.selected_count_mul_coarse_volume, hcells] at hfinePos
    simpa using hfinePos
  have hphaseNonempty :
      (pureWZ2BalancedSafePhaseCells
        (pullback := pullback) data.phase).Nonempty := by
    apply Finset.card_ne_zero.mp
    intro hzero
    have hselectedZero : pullback.selectedCells.card = 0 := by
      have h := data.selected_card
      rw [hzero] at h
      omega
    exact hselectedNonempty.card_ne_zero hselectedZero
  have himage := hphaseNonempty.image
    (pureWZ2BalancedWindowPhaseBlock rho data.phase)
  simpa [data.blocks_eq, pureWZ2BalancedSafePhaseBlocks] using himage

/-- The two shifted safe phases meet only `O(1 / sqrt rho)` height blocks.
The common phase shift changes the endpoints but not the length of the
containing interval. -/
theorem PureWZ2BalancedSafeBlockFamilyData.blocks_card_mul_sqrt_le
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (data : PureWZ2BalancedSafeBlockFamilyData prepared) :
    data.blocks.card * Real.sqrt rho ≤
      2 + rho + 2 * Real.sqrt rho := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hroot : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  let shift := pureWZ2BalancedWindowPhaseShift rho data.phase
  let lower : ℤ := Int.floor ((-1 - rho / 2 - shift) / Real.sqrt rho)
  let upper : ℤ := Int.floor ((1 + rho / 2 - shift) / Real.sqrt rho)
  have hcenter : ∀ cell ∈ pullback.selectedCells,
      |pureWZ2PaperCellCenterHeight rho cell| ≤ 1 + rho / 2 := by
    intro cell hcell
    have hactive : cell ∈ wz1PaperActiveCells twoScale.fine.refined
        twoScale.coarseGrains.extremal.delta_pos := by
      rwa [pullback.selectedCells_eq] at hcell
    rcases ((mem_wz1PaperActiveCells twoScale.fine.refined
      twoScale.coarseGrains.extremal.delta_pos cell).mp hactive).2 with
      ⟨point, hpointFine, hpointCell⟩
    have hbox := shading_union_subset_axisBox hpointFine
    have hpointHeight : |point (2 : Fin 3)| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
    have hpointCellRho : point ∈ wz1PaperGridCube rho cell := by
      simpa only [twoScale.rhoRequested_eq] using hpointCell
    have hcellBounds := hpointCellRho
    rw [wz1PaperGridCube_eq_Ico hrho cell] at hcellBounds
    have hcenterDistance :
        |pureWZ2PaperCellCenterHeight rho cell - point (2 : Fin 3)| ≤
          rho / 2 := by
      rw [abs_le]
      constructor
      · calc
          -(rho / 2) =
              pureWZ2PaperCellCenterHeight rho cell -
                ((cell.2.2 : ℝ) + 1) * rho := by
            dsimp only [pureWZ2PaperCellCenterHeight]
            ring
          _ ≤ pureWZ2PaperCellCenterHeight rho cell - point (2 : Fin 3) :=
            sub_le_sub_left hcellBounds.2.2.2.2.2.le _
      · calc
          pureWZ2PaperCellCenterHeight rho cell - point (2 : Fin 3) ≤
              pureWZ2PaperCellCenterHeight rho cell -
                (cell.2.2 : ℝ) * rho :=
            sub_le_sub_left hcellBounds.2.2.2.2.1 _
          _ = rho / 2 := by
            dsimp only [pureWZ2PaperCellCenterHeight]
            ring
    calc
      |pureWZ2PaperCellCenterHeight rho cell| ≤
          |pureWZ2PaperCellCenterHeight rho cell - point (2 : Fin 3)| +
            |point (2 : Fin 3)| := by
        calc
          |pureWZ2PaperCellCenterHeight rho cell| =
              |(pureWZ2PaperCellCenterHeight rho cell - point (2 : Fin 3)) +
                point (2 : Fin 3)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      _ ≤ rho / 2 + 1 := add_le_add hcenterDistance hpointHeight
      _ = 1 + rho / 2 := by ring
  have hsubset : data.blocks ⊆ Finset.Icc lower upper := by
    intro block hblock
    rw [data.blocks_eq, pureWZ2BalancedSafePhaseBlocks] at hblock
    rcases Finset.mem_image.mp hblock with ⟨cell, hcell, rfl⟩
    have hc := abs_le.mp (hcenter cell (Finset.mem_filter.mp hcell).1)
    rw [Finset.mem_Icc]
    constructor
    · change Int.floor ((-1 - rho / 2 - shift) / Real.sqrt rho) ≤
          Int.floor ((pureWZ2PaperCellCenterHeight rho cell - shift) /
            Real.sqrt rho)
      apply Int.floor_mono
      apply div_le_div_of_nonneg_right _ hroot.le
      linarith [hc.1]
    · change Int.floor ((pureWZ2PaperCellCenterHeight rho cell - shift) /
            Real.sqrt rho) ≤
          Int.floor ((1 + rho / 2 - shift) / Real.sqrt rho)
      apply Int.floor_mono
      exact div_le_div_of_nonneg_right (by linarith [hc.2]) hroot.le
  have hcardNat : data.blocks.card ≤ (Finset.Icc lower upper).card :=
    Finset.card_le_card hsubset
  have hlowerUpper : lower ≤ upper + 1 := by
    have hreal : ((-1 - rho / 2 - shift) / Real.sqrt rho) ≤
        ((1 + rho / 2 - shift) / Real.sqrt rho) := by
      apply div_le_div_of_nonneg_right _ hroot.le
      linarith
    have hfloor : lower ≤ upper := Int.floor_mono hreal
    omega
  have hcardInt : ((Finset.Icc lower upper).card : ℤ) =
      upper + 1 - lower := Int.card_Icc_of_le lower upper hlowerUpper
  have hcardReal : (data.blocks.card : ℝ) ≤
      (upper : ℝ) + 1 - lower := by
    have hcast : (data.blocks.card : ℤ) ≤
        (Finset.Icc lower upper).card := by exact_mod_cast hcardNat
    rw [hcardInt] at hcast
    exact_mod_cast hcast
  have hupper : (upper : ℝ) ≤
      (1 + rho / 2 - shift) / Real.sqrt rho := Int.floor_le _
  have hlower : ((-1 - rho / 2 - shift) / Real.sqrt rho) <
      (lower : ℝ) + 1 := Int.lt_floor_add_one _
  have hquotient :
      (1 + rho / 2 - shift) / Real.sqrt rho -
          ((-1 - rho / 2 - shift) / Real.sqrt rho) =
        (2 + rho) / Real.sqrt rho := by
    field_simp [hroot.ne']
    ring
  have hcardBound : (data.blocks.card : ℝ) ≤
      (2 + rho) / Real.sqrt rho + 2 := by
    rw [← hquotient]
    linarith
  have hmul := mul_le_mul_of_nonneg_right hcardBound hroot.le
  have hcancel : (2 + rho) / Real.sqrt rho * Real.sqrt rho =
      2 + rho := by
    field_simp [hroot.ne']
  rw [add_mul, hcancel] at hmul
  simpa using hmul

theorem PureWZ2BalancedSafeBlockFamilyData.blocks_card_mul_sqrtENN_le
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (data : PureWZ2BalancedSafeBlockFamilyData prepared) :
    (data.blocks.card : ENNReal) * ENNReal.ofReal (Real.sqrt rho) ≤
      ENNReal.ofReal (2 + rho + 2 * Real.sqrt rho) := by
  have hreal := data.blocks_card_mul_sqrt_le
  have hcast : (data.blocks.card : ENNReal) =
      ENNReal.ofReal (data.blocks.card : ℝ) := by simp
  rw [hcast, ← ENNReal.ofReal_mul (by exact_mod_cast
    (Nat.zero_le data.blocks.card))]
  exact ENNReal.ofReal_mono hreal

end Kakeya.Assouad
