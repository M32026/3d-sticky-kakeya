import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinAnchoredIntegrated

/-!
# Eligible anchored pre-bin blocks
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2AnchoredPreBinRhoHeightFamilyData

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
    (preBin : PureWZ2AnchoredPreBinRhoHeightFamilyData selected)

def localSourceMass
    (heightIndex :
      {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices}) :
    ENNReal :=
  volume (preBin.blockData heightIndex).sourceSet

def eligibleThreshold
    (_preBin : PureWZ2AnchoredPreBinRhoHeightFamilyData selected)
    (B₀ : ENNReal) (K : ℕ) : ENNReal :=
  4 * B₀ * K *
    PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
      sigma inputLoss delta rhoRequested.1 *
    ENNReal.ofReal (Real.sqrt rhoRequested.1)

def eligibleBlocks (B₀ : ENNReal) (K : ℕ) :
    Finset {heightIndex //
      heightIndex ∈ selected.standardSqrtSlabIndices} :=
  Finset.univ.filter fun heightIndex =>
    preBin.eligibleThreshold B₀ K ≤ preBin.localSourceMass heightIndex

theorem eligible_localPopularThreshold
    (B₀ : ENNReal) (K : ℕ)
    {heightIndex :
      {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices}}
    (heligible : heightIndex ∈ preBin.eligibleBlocks B₀ K) :
    2 * B₀ *
        ((K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rhoRequested.1) ≤
      pureWZ2SourceCommonBinPopularThreshold
        (preBin.blockData heightIndex).sourceSet
        (Real.sqrt rhoRequested.1) := by
  have hrho : 0 < rhoRequested.1 :=
    source.extremal.delta_pos.trans_le rhoRequested.property.1
  let root := ENNReal.ofReal (Real.sqrt rhoRequested.1)
  have hrootPos : 0 < root :=
    ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hrho)
  have hrootTop : root ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmass :
      4 * B₀ * K *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rhoRequested.1 * root ≤
        preBin.localSourceMass heightIndex := by
    simpa [eligibleBlocks, eligibleThreshold, root] using
      (Finset.mem_filter.mp heligible).2
  rw [pureWZ2SourceCommonBinPopularThreshold_eq]
  change 2 * B₀ * ((K : ENNReal) *
      PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
        sigma inputLoss delta rhoRequested.1) ≤
    preBin.localSourceMass heightIndex / (2 * root)
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.mul_pos (by norm_num) hrootPos.ne').ne')
    (Or.inl (ENNReal.mul_ne_top (by norm_num) hrootTop))).2
  simpa only [Nat.cast_ofNat] using (show
    (2 * B₀ * ((K : ENNReal) *
      PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
        sigma inputLoss delta rhoRequested.1)) * (2 * root) ≤
      preBin.localSourceMass heightIndex by
        calc
          _ = 4 * B₀ * K *
              PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
                sigma inputLoss delta rhoRequested.1 * root := by ring
          _ ≤ _ := hmass)

theorem logarithmicCost_le_heightCost
    (heightIndex :
      {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices}) :
    ((preBin.blockData heightIndex).logarithmicCost : ENNReal) ≤
      pureWZ2CommonBinPreBinHeightCost rhoRequested.1 := by
  let block := preBin.blockData heightIndex
  have hrho : 0 < rhoRequested.1 := coarse.coarse_extremal.delta_pos
  have hcard :
      (selected.standardSqrtSlabRhoCells heightIndex.1).card ≤
        (wz1PaperActiveCells fine.refined hrho).card := by
    apply Finset.card_le_card
    intro cell hcell
    rw [← selected.selectedCells_eq]
    exact selected.standardSqrtSlabRhoCells_subset heightIndex.1 hcell
  rw [block.logarithmicCost_eq]
  simpa [pureWZ2CommonBinPreBinHeightCost] using
    commonBin_rhoHeight_logarithmicCostBoundaryENN_le
      hrho rhoRequested.property.2 fine.refined
      (selected.standardSqrtSlabRhoCells heightIndex.1).card hcard

theorem sum_standardSqrtSlabRhoCells_card
    (_preBin : PureWZ2AnchoredPreBinRhoHeightFamilyData selected) :
    ∑ heightIndex :
        {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices},
      (selected.standardSqrtSlabRhoCells heightIndex.1).card =
      selected.selectedCells.card := by
  have hraw := Finset.sum_card_fiberwise_eq_card_filter
    selected.selectedCells selected.standardSqrtSlabIndices
      selected.standardSqrtSlabIndex
  have hfilter :
      selected.selectedCells.filter (fun cell =>
        selected.standardSqrtSlabIndex cell ∈
          selected.standardSqrtSlabIndices) =
        selected.selectedCells := by
    apply Finset.filter_true_of_mem
    intro cell hcell
    exact Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
  rw [hfilter] at hraw
  rw [← hraw]
  rw [Finset.sum_subtype selected.standardSqrtSlabIndices (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro heightIndex _
  rfl

theorem selected_volume_le_heightCost_mul_sum_localSourceMass :
    volume selected.shading.union ≤
      pureWZ2CommonBinPreBinHeightCost rhoRequested.1 *
        ∑ heightIndex, preBin.localSourceMass heightIndex := by
  rw [selected.volume_eq]
  have hcount :
      (selected.selectedCells.card : ENNReal) ≤
        ∑ heightIndex,
          ((preBin.blockData heightIndex).logarithmicCost : ENNReal) *
            ((preBin.blockData heightIndex).cells.card : ENNReal) := by
    have hn :
        selected.selectedCells.card ≤
          ∑ heightIndex,
            (preBin.blockData heightIndex).logarithmicCost *
              (preBin.blockData heightIndex).cells.card := by
      rw [← preBin.sum_standardSqrtSlabRhoCells_card]
      exact Finset.sum_le_sum fun heightIndex _ =>
        (preBin.blockData heightIndex).card_retention
    exact_mod_cast hn
  calc
    (selected.selectedCells.card : ENNReal) *
        coarse.balanced.cellMass ≤
      (∑ heightIndex,
        ((preBin.blockData heightIndex).logarithmicCost : ENNReal) *
          ((preBin.blockData heightIndex).cells.card : ENNReal)) *
        coarse.balanced.cellMass := by gcongr
    _ = ∑ heightIndex,
        ((preBin.blockData heightIndex).logarithmicCost : ENNReal) *
          preBin.localSourceMass heightIndex := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro heightIndex _
      rw [localSourceMass, show volume
          (preBin.blockData heightIndex).sourceSet =
            ((preBin.blockData heightIndex).cells.card : ENNReal) *
              coarse.balanced.cellMass by
        exact (preBin.blockData heightIndex).source_volume]
      ring
    _ ≤ ∑ heightIndex,
        pureWZ2CommonBinPreBinHeightCost rhoRequested.1 *
          preBin.localSourceMass heightIndex := by
      gcongr with heightIndex
      exact preBin.logarithmicCost_le_heightCost heightIndex
    _ = _ := by rw [← Finset.mul_sum]

theorem standardSqrtSlabIndices_card_mul_sqrtENN_le_five
    (preBin : PureWZ2AnchoredPreBinRhoHeightFamilyData selected) :
    (selected.standardSqrtSlabIndices.card : ENNReal) *
        ENNReal.ofReal (Real.sqrt rhoRequested.1) ≤ 5 := by
  have hrho : 0 < rhoRequested.1 := coarse.coarse_extremal.delta_pos
  let root := Real.sqrt rhoRequested.1
  have hroot : 0 < root := Real.sqrt_pos.mpr hrho
  let lower : ℤ := Int.floor ((-1 - root / 2) / root)
  let upper : ℤ := Int.floor ((1 + root / 2) / root)
  have hcenter :
      ∀ cell ∈ selected.selectedCells,
        |pureWZ2PaperCellCenterHeight root
            (selected.standardSecondParent cell)| ≤ 1 + root / 2 := by
    intro cell hcell
    have hactive : cell ∈ wz1PaperActiveCells fine.refined hrho := by
      simpa only [selected.selectedCells_eq] using hcell
    rcases ((mem_wz1PaperActiveCells fine.refined hrho cell).mp hactive).2 with
      ⟨point, hpointFine, hpointCell⟩
    have hbox := shading_union_subset_axisBox hpointFine
    have hpointHeight : |point (2 : Fin 3)| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
    have hpointParent :
        point ∈ wz1PaperGridCube root
          (selected.standardSecondParent cell) := by
      simpa [root, preBin.sqrtRequested_eq] using
        selected.standardSecondParent_cell_subset hcell hpointCell
    have hparentBounds := hpointParent
    rw [wz1PaperGridCube_eq_Ico hroot] at hparentBounds
    have hcenterDistance :
        |pureWZ2PaperCellCenterHeight root
              (selected.standardSecondParent cell) -
            point (2 : Fin 3)| ≤ root / 2 := by
      rw [abs_le]
      constructor
      · calc
          -(root / 2) =
              pureWZ2PaperCellCenterHeight root
                  (selected.standardSecondParent cell) -
                (((selected.standardSecondParent cell).2.2 : ℝ) + 1) *
                  root := by
                    dsimp only [pureWZ2PaperCellCenterHeight]
                    ring
          _ ≤ pureWZ2PaperCellCenterHeight root
                  (selected.standardSecondParent cell) -
                point (2 : Fin 3) :=
            sub_le_sub_left hparentBounds.2.2.2.2.2.le _
      · calc
          pureWZ2PaperCellCenterHeight root
                (selected.standardSecondParent cell) -
              point (2 : Fin 3) ≤
            pureWZ2PaperCellCenterHeight root
                (selected.standardSecondParent cell) -
              ((selected.standardSecondParent cell).2.2 : ℝ) * root :=
            sub_le_sub_left hparentBounds.2.2.2.2.1 _
          _ = root / 2 := by
            dsimp only [pureWZ2PaperCellCenterHeight]
            ring
    calc
      |pureWZ2PaperCellCenterHeight root
          (selected.standardSecondParent cell)| ≤
        |pureWZ2PaperCellCenterHeight root
              (selected.standardSecondParent cell) - point 2| +
          |point 2| := by
            simpa only [sub_add_cancel] using
              abs_add_le
                (pureWZ2PaperCellCenterHeight root
                  (selected.standardSecondParent cell) - point 2) (point 2)
      _ ≤ root / 2 + 1 := add_le_add hcenterDistance hpointHeight
      _ = 1 + root / 2 := by ring
  have hindexFloor : ∀ cell,
      Int.floor (pureWZ2PaperCellCenterHeight root
        (selected.standardSecondParent cell) / root) =
        selected.standardSqrtSlabIndex cell := by
    intro cell
    unfold PureWZ2AnchoredSourceRelativeFineSelection.standardSqrtSlabIndex
      pureWZ2PaperCellCenterHeight
    rw [mul_div_cancel_right₀ _ hroot.ne', Int.floor_eq_iff]
    constructor <;> norm_num
  have hsubset :
      selected.standardSqrtSlabIndices ⊆ Finset.Icc lower upper := by
    intro heightIndex hheightIndex
    rw [PureWZ2AnchoredSourceRelativeFineSelection.standardSqrtSlabIndices]
      at hheightIndex
    rcases Finset.mem_image.mp hheightIndex with ⟨cell, hcell, rfl⟩
    have hc := abs_le.mp (hcenter cell hcell)
    rw [Finset.mem_Icc, ← hindexFloor cell]
    constructor
    · apply Int.floor_mono
      apply div_le_div_of_nonneg_right _ hroot.le
      linarith [hc.1]
    · apply Int.floor_mono
      apply div_le_div_of_nonneg_right _ hroot.le
      linarith [hc.2]
  have hcardNat := Finset.card_le_card hsubset
  have hlowerUpper : lower ≤ upper + 1 := by
    have hfloor : lower ≤ upper := Int.floor_mono <| by
      apply div_le_div_of_nonneg_right _ hroot.le
      linarith
    omega
  have hcardInt :
      ((Finset.Icc lower upper).card : ℤ) = upper + 1 - lower :=
    Int.card_Icc_of_le lower upper hlowerUpper
  have hcardReal :
      (selected.standardSqrtSlabIndices.card : ℝ) ≤
        (upper : ℝ) + 1 - lower := by
    have hcast :
        (selected.standardSqrtSlabIndices.card : ℤ) ≤
          (Finset.Icc lower upper).card := by exact_mod_cast hcardNat
    rw [hcardInt] at hcast
    exact_mod_cast hcast
  have hupper : (upper : ℝ) ≤ (1 + root / 2) / root := Int.floor_le _
  have hlower : ((-1 - root / 2) / root) < (lower : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hcardBound :
      (selected.standardSqrtSlabIndices.card : ℝ) * root ≤ 5 := by
    have hquotient :
        (1 + root / 2) / root - ((-1 - root / 2) / root) =
          (2 + root) / root := by field_simp [hroot.ne']; ring
    have hcard :
        (selected.standardSqrtSlabIndices.card : ℝ) ≤
          (2 + root) / root + 2 := by rw [← hquotient]; linarith
    have hmul := mul_le_mul_of_nonneg_right hcard hroot.le
    have hcancel : (2 + root) / root * root = 2 + root := by
      field_simp [hroot.ne']
    rw [add_mul, hcancel] at hmul
    have hrootOne : root ≤ 1 := by
      exact Real.sqrt_le_one.mpr rhoRequested.property.2
    linarith
  have hcast :
      (selected.standardSqrtSlabIndices.card : ENNReal) =
        ENNReal.ofReal (selected.standardSqrtSlabIndices.card : ℝ) := by simp
  rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
  exact (ENNReal.ofReal_mono hcardBound).trans_eq (by norm_num)

theorem lightBudget_of_scalar
    {volumeLoss : ℝ} {B₀ : ENNReal}
    (scalar : PureWZ2AnchoredCommonBinScalarData
      (volumeLoss := volumeLoss) preBin B₀) :
    2 * (((Finset.univ :
        Finset {heightIndex //
          heightIndex ∈ selected.standardSqrtSlabIndices}).card : ENNReal) *
      preBin.eligibleThreshold B₀ scalar.K) ≤
    ∑ heightIndex, preBin.localSourceMass heightIndex := by
  let H := pureWZ2CommonBinPreBinHeightCost rhoRequested.1
  let cap :=
    PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
      sigma inputLoss delta rhoRequested.1
  let V := volume selected.shading.union
  have hrho : 0 < rhoRequested.1 := coarse.coarse_extremal.delta_pos
  have hHPos : 0 < H :=
    pureWZ2CommonBinPreBinHeightCost_pos hrho rhoRequested.property.2
  have hHTop : H ≠ ⊤ := by
    simp [H, pureWZ2CommonBinPreBinHeightCost]
  have hcount :=
    preBin.standardSqrtSlabIndices_card_mul_sqrtENN_le_five
  have hscaledCapacity :
      (20 * H) * (2 * B₀ * (scalar.X * cap)) ≤ V := by
    have hc := (ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.mul_pos (by norm_num) hHPos.ne').ne')
      (Or.inl (ENNReal.mul_ne_top (by norm_num) hHTop))).mp scalar.capacity
    simpa [H, cap, V, mul_comm, mul_left_comm, mul_assoc] using hc
  have hbeforeCancel :
      H * (2 * ((selected.standardSqrtSlabIndices.card : ENNReal) *
        preBin.eligibleThreshold B₀ scalar.K)) ≤
      H * ∑ heightIndex, preBin.localSourceMass heightIndex := by
    calc
      _ = H * (8 * B₀ * scalar.K * cap *
          ((selected.standardSqrtSlabIndices.card : ENNReal) *
            ENNReal.ofReal (Real.sqrt rhoRequested.1))) := by
        simp only [eligibleThreshold]
        ring
      _ ≤ H * (8 * B₀ * scalar.X * cap *
          ((selected.standardSqrtSlabIndices.card : ENNReal) *
            ENNReal.ofReal (Real.sqrt rhoRequested.1))) := by
        gcongr
        exact scalar.K_upper
      _ ≤ H * (8 * B₀ * scalar.X * cap * 5) := by gcongr
      _ = (20 * H) * (2 * B₀ * (scalar.X * cap)) := by ring
      _ ≤ V := hscaledCapacity
      _ ≤ H * ∑ heightIndex, preBin.localSourceMass heightIndex :=
        preBin.selected_volume_le_heightCost_mul_sum_localSourceMass
  have hreordered :
      (2 * ((selected.standardSqrtSlabIndices.card : ENNReal) *
        preBin.eligibleThreshold B₀ scalar.K)) * H ≤
      (∑ heightIndex, preBin.localSourceMass heightIndex) * H := by
    simpa [mul_comm] using hbeforeCancel
  simpa only [Finset.card_univ, Fintype.card_coe] using
    ((ENNReal.mul_le_mul_iff_left hHPos.ne' hHTop).mp hreordered)

end PureWZ2AnchoredPreBinRhoHeightFamilyData

structure PureWZ2AnchoredEligibleBlockLedger
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
    (preBin : PureWZ2AnchoredPreBinRhoHeightFamilyData selected)
    (B₀ : ENNReal) (K : ℕ) where
  eligible := preBin.eligibleBlocks B₀ K
  eligible_eq : eligible = preBin.eligibleBlocks B₀ K
  retained_source :
    volume selected.shading.union ≤
      2 * pureWZ2CommonBinPreBinHeightCost rhoRequested.1 *
        ∑ heightIndex ∈ eligible, preBin.localSourceMass heightIndex
  nonempty : eligible.Nonempty

theorem pureWZ2_anchoredEligibleBlockLedger_of_lightBudget
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
    (preBin : PureWZ2AnchoredPreBinRhoHeightFamilyData selected)
    (B₀ : ENNReal) (K : ℕ) (hB₀Top : B₀ ≠ ⊤)
    (hsource :
      volume selected.shading.union ≤
        pureWZ2CommonBinPreBinHeightCost rhoRequested.1 *
          ∑ heightIndex, preBin.localSourceMass heightIndex)
    (hlight :
      2 * (((Finset.univ :
          Finset {heightIndex //
            heightIndex ∈ selected.standardSqrtSlabIndices}).card : ENNReal) *
        preBin.eligibleThreshold B₀ K) ≤
      ∑ heightIndex, preBin.localSourceMass heightIndex) :
    Nonempty (PureWZ2AnchoredEligibleBlockLedger preBin B₀ K) := by
  let slabs : Finset {heightIndex //
      heightIndex ∈ selected.standardSqrtSlabIndices} := Finset.univ
  let threshold := preBin.eligibleThreshold B₀ K
  have hthresholdTop : threshold ≠ ⊤ := by
    unfold threshold PureWZ2AnchoredPreBinRhoHeightFamilyData.eligibleThreshold
      PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
      Kakeya.realRpowENN
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num) hB₀Top)
          (ENNReal.natCast_ne_top _))
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
            ENNReal.ofReal_ne_top)
          ENNReal.ofReal_ne_top))
      ENNReal.ofReal_ne_top
  have hhalf := finset_good_weighted_supply_retains_half
    slabs (fun heightIndex => preBin.localSourceMass heightIndex)
    1 threshold hthresholdTop (by simpa [slabs, threshold] using hlight)
  simp only [mul_one] at hhalf
  have hretained :
      volume selected.shading.union ≤
        2 * pureWZ2CommonBinPreBinHeightCost rhoRequested.1 *
          ∑ heightIndex ∈ preBin.eligibleBlocks B₀ K,
            preBin.localSourceMass heightIndex := by
    calc
      _ ≤ pureWZ2CommonBinPreBinHeightCost rhoRequested.1 *
          ∑ heightIndex, preBin.localSourceMass heightIndex := hsource
      _ ≤ pureWZ2CommonBinPreBinHeightCost rhoRequested.1 *
          (2 * ∑ heightIndex ∈ preBin.eligibleBlocks B₀ K,
            preBin.localSourceMass heightIndex) := by
        gcongr
        simpa [slabs, threshold,
          PureWZ2AnchoredPreBinRhoHeightFamilyData.eligibleBlocks] using hhalf
      _ = _ := by ring
  have heligible : (preBin.eligibleBlocks B₀ K).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hretained
    simp only [Finset.sum_empty, mul_zero] at hretained
    have hselectedPos : 0 < volume selected.shading.union := by
      have hrho : 0 < rhoRequested.1 :=
        source.extremal.delta_pos.trans_le rhoRequested.property.1
      exact (ENNReal.mul_pos
        (ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos source.extremal.delta_pos _)).ne'
        (ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos hrho _)).ne').trans_le
            selected.volume_relative_lower
    exact (not_le_of_gt hselectedPos) hretained
  exact ⟨{
    eligible := preBin.eligibleBlocks B₀ K
    eligible_eq := rfl
    retained_source := hretained
    nonempty := heligible
  }⟩

theorem PureWZ2AnchoredCommonBinScalarData.eligibleLedger
    {sigma inputLoss delta coarseLoss fineLoss volumeLoss : ℝ}
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
    {B₀ : ENNReal}
    (scalar : PureWZ2AnchoredCommonBinScalarData
      (volumeLoss := volumeLoss) preBin B₀)
    (hB₀Top : B₀ ≠ ⊤) :
    Nonempty (PureWZ2AnchoredEligibleBlockLedger
      preBin B₀ scalar.K) :=
  pureWZ2_anchoredEligibleBlockLedger_of_lightBudget
    preBin B₀ scalar.K hB₀Top
    preBin.selected_volume_le_heightCost_mul_sum_localSourceMass
    (preBin.lightBudget_of_scalar scalar)

structure PureWZ2AnchoredEligibleGraphFamilyData
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
    (preBin : PureWZ2AnchoredPreBinRhoHeightFamilyData selected)
    (B₀ : ENNReal) (K : ℕ)
    (ledger : PureWZ2AnchoredEligibleBlockLedger preBin B₀ K) where
  blockData : ∀ heightIndex : {heightIndex //
      heightIndex ∈ ledger.eligible},
    PureWZ2AnchoredIntegratedCommonBinReceipt
      (preBin.blockData heightIndex.1) B₀
      ((K : ENNReal) *
        PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
          sigma inputLoss delta rhoRequested.1) K

theorem PureWZ2AnchoredEligibleBlockLedger.graphFamily
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
    (ledger : PureWZ2AnchoredEligibleBlockLedger preBin B₀ K)
    (hB₀ : 264 * Kakeya.realRpowENN delta (-inputLoss) *
        Kakeya.realRpowENN (1 / Real.sqrt rhoRequested.1) (1 - sigma) ≤ B₀) :
    Nonempty (PureWZ2AnchoredEligibleGraphFamilyData
      preBin B₀ K ledger) := by
  let threshold :=
    (K : ENNReal) *
      PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
        sigma inputLoss delta rhoRequested.1
  have hblock : ∀ heightIndex : {heightIndex //
      heightIndex ∈ ledger.eligible},
      Nonempty (PureWZ2AnchoredIntegratedCommonBinReceipt
        (preBin.blockData heightIndex.1) B₀ threshold K) := by
    intro heightIndex
    apply (preBin.blockData heightIndex.1).integratedCommonBin
      B₀ threshold K hB₀
    · apply preBin.eligible_localPopularThreshold B₀ K
      rw [← ledger.eligible_eq]
      exact heightIndex.2
    · exact le_rfl
  exact ⟨{
    blockData := fun heightIndex => Classical.choice (hblock heightIndex)
  }⟩

theorem PureWZ2AnchoredCommonBinScalarData.eligibleGraphFamily
    {sigma inputLoss delta coarseLoss fineLoss volumeLoss : ℝ}
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
    {B₀ : ENNReal}
    (scalar : PureWZ2AnchoredCommonBinScalarData
      (volumeLoss := volumeLoss) preBin B₀)
    (hB₀Top : B₀ ≠ ⊤)
    (hB₀ : 264 * Kakeya.realRpowENN delta (-inputLoss) *
        Kakeya.realRpowENN (1 / Real.sqrt rhoRequested.1) (1 - sigma) ≤ B₀) :
    ∃ ledger : PureWZ2AnchoredEligibleBlockLedger preBin B₀ scalar.K,
      Nonempty (PureWZ2AnchoredEligibleGraphFamilyData
        preBin B₀ scalar.K ledger) := by
  rcases scalar.eligibleLedger hB₀Top with ⟨ledger⟩
  exact ⟨ledger, ledger.graphFamily hB₀⟩

end Kakeya.Assouad

end
