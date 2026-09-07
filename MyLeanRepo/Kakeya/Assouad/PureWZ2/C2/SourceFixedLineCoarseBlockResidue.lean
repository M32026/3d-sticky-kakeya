import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseAllBlocks
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalBlockSeparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderSelectedCoarseBins

/-!
# Mod-64 selection for genuine-coarse paper-order blocks

The weight of a block is the indexed mass of its exact original-family
pullback.  Thus the residue selection occurs only after the genuine coarse
`Z_lin` region has been pulled back through the first balanced cover.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2SourceFixedLineCoarseGoodBlockFamilyData

private lemma sourceFixedLineCoarseResidue_separated
    {first second : ℤ}
    (hne : first ≠ second)
    (hmod : first % (64 : ℤ) = second % (64 : ℤ)) :
    (64 : ℤ) ≤ |first - second| := by
  have hzero : (first - second) % (64 : ℤ) = 0 := by
    rw [Int.sub_emod, hmod]
    simp
  have hdiv : (64 : ℤ) ∣ first - second := by
    rwa [Int.dvd_iff_emod_eq_zero]
  exact Int.le_abs_of_dvd (sub_ne_zero.mpr hne) hdiv

/-- The exact source window underlying one retained rich block. -/
theorem sourceWindow_left_eq
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family}
    (data : PureWZ2SourceFixedLineCoarseGoodBlockFamilyData
      (finalLoss := finalLoss) (theoremEta := theoremEta)
      (volumeLoss := volumeLoss) all)
    (index : Fin data.indexCount) :
    (family.carrierData (data.safeBlock index)).outerPopular.popularWindow.left =
      pureWZ2SourceCarrierBlockLeft rho (data.safeBlock index).1 +
        pureWZ2BalancedWindowPhaseShift rho safe.phase := by
  calc
    _ = (family.carrierData (data.safeBlock index)).sourceWindow.left :=
      (family.carrierData (data.safeBlock index)).outerPopular.popularWindow_left
    _ = _ := by
      rw [family.carrierData_sourceWindow]
      rw [(safe.blockWindow (data.safeBlock index)).window_left]
      rfl

/-- Genuine-coarse rich trapezoid cores from same-phase source blocks at gap
at least 64 are separated at the public scale `1280 * rho`. -/
theorem rich_cores_separated_of_block_gap
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family}
    (data : PureWZ2SourceFixedLineCoarseGoodBlockFamilyData
      (finalLoss := finalLoss) (theoremEta := theoremEta)
      (volumeLoss := volumeLoss) all)
    (first second : Fin data.indexCount)
    (hblocks : (64 : ℤ) ≤
      |(data.safeBlock first).1 - (data.safeBlock second).1|) :
    ∀ z ∈ (data.rich first).richTrapezoid.trapezoid.core,
      ∀ w ∈ (data.rich second).richTrapezoid.trapezoid.core,
        Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) ≤ |z - w| := by
  have hrho : 0 < rho :=
    (family.carrierData (data.safeBlock first)).line.rho_pos
  let root := Real.sqrt rho
  have hroot : 0 < root := Real.sqrt_pos.mpr hrho
  have hscale := pureWZ2SourceHorizontalFinalScale_sqrt_le hrho
  intro z hz w hw
  have hzWindow := (data.rich first).richTrapezoid.core_height_window z hz
  have hwWindow := (data.rich second).richTrapezoid.core_height_window w hw
  rw [data.sourceWindow_left_eq first] at hzWindow
  rw [data.sourceWindow_left_eq second] at hwWindow
  simp only [pureWZ2SourceCarrierBlockLeft] at hzWindow hwWindow
  by_cases horder : (data.safeBlock first).1 < (data.safeBlock second).1
  · have hdiffInt : (64 : ℤ) ≤
        (data.safeBlock second).1 - (data.safeBlock first).1 := by
      rw [abs_of_nonpos (sub_nonpos.mpr horder.le)] at hblocks
      simpa using hblocks
    have hdiffReal : (64 : ℝ) ≤
        (data.safeBlock second).1 - (data.safeBlock first).1 := by
      exact_mod_cast hdiffInt
    have hwz : 59 * root ≤ w - z := by
      dsimp only [root] at hroot ⊢
      nlinarith [hzWindow.2, hwWindow.1]
    have hwzNonneg : 0 ≤ w - z :=
      (mul_pos (by norm_num) hroot).le.trans hwz
    rw [abs_sub_comm, abs_of_nonneg hwzNonneg]
    exact hscale.trans (by
      dsimp only [root] at hwz ⊢
      nlinarith [Real.sqrt_pos.mpr hrho])
  · have hreverse : (data.safeBlock second).1 <
        (data.safeBlock first).1 := by
      have hne : (data.safeBlock first).1 ≠
          (data.safeBlock second).1 := by
        intro heq
        rw [heq, sub_self, abs_zero] at hblocks
        norm_num at hblocks
      omega
    have hdiffInt : (64 : ℤ) ≤
        (data.safeBlock first).1 - (data.safeBlock second).1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hreverse.le)] at hblocks
      exact hblocks
    have hdiffReal : (64 : ℝ) ≤
        (data.safeBlock first).1 - (data.safeBlock second).1 := by
      exact_mod_cast hdiffInt
    have hzw : 59 * root ≤ z - w := by
      dsimp only [root] at hroot ⊢
      nlinarith [hzWindow.1, hwWindow.2]
    have hzwNonneg : 0 ≤ z - w :=
      (mul_pos (by norm_num) hroot).le.trans hzw
    rw [abs_of_nonneg hzwNonneg]
    exact hscale.trans (by
      dsimp only [root] at hzw ⊢
      nlinarith [Real.sqrt_pos.mpr hrho])

/-- A mass-heavy mod-64 subfamily of completed genuine-coarse blocks. -/
structure PureWZ2SourceFixedLineCoarseBlockResidueData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family}
    (data : PureWZ2SourceFixedLineCoarseGoodBlockFamilyData
      (finalLoss := finalLoss) (theoremEta := theoremEta)
      (volumeLoss := volumeLoss) all) where
  residue : Fin 64
  selected : Finset (Fin data.indexCount)
  selected_eq : selected = Finset.univ.filter fun index =>
    ((data.safeBlock index).1 % (64 : ℤ)).toNat = residue
  selected_nonempty : selected.Nonempty
  selectedIndex : Fin selected.card → Fin data.indexCount
  selectedIndex_mem : ∀ index, selectedIndex index ∈ selected
  selectedIndex_injective : Function.Injective selectedIndex
  selectedIndex_surjective : ∀ index ∈ selected,
    ∃ selectedIndexValue, selectedIndex selectedIndexValue = index
  total_mass_le :
    (∑ index : Fin data.indexCount,
        (data.rich index).sourcePullback.shading.mass) ≤
      64 * ∑ index : Fin selected.card,
        (data.rich (selectedIndex index)).sourcePullback.shading.mass
  separated_cores :
    ∀ first second : Fin selected.card, first ≠ second →
      ∀ z ∈ (data.rich
          (selectedIndex first)).richTrapezoid.trapezoid.core,
        ∀ w ∈ (data.rich
            (selectedIndex second)).richTrapezoid.trapezoid.core,
          Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) ≤ |z - w|

/-- Select the mass-heavy source-block residue after each block has completed
its genuine-coarse `Z_popular` and `Z_lin` construction and exact pullback. -/
theorem selectResidue
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family}
    (data : PureWZ2SourceFixedLineCoarseGoodBlockFamilyData
      (finalLoss := finalLoss) (theoremEta := theoremEta)
      (volumeLoss := volumeLoss) all) :
    Nonempty (PureWZ2SourceFixedLineCoarseBlockResidueData data) := by
  let label : Fin data.indexCount → Fin 64 := fun index =>
    ⟨((data.safeBlock index).1 % (64 : ℤ)).toNat, by
      have hnonneg : 0 ≤ (data.safeBlock index).1 % (64 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      have hlt : (data.safeBlock index).1 % (64 : ℤ) < (64 : ℤ) :=
        Int.emod_lt_of_pos _ (by norm_num)
      omega⟩
  let weight : Fin data.indexCount → ENNReal := fun index =>
    (data.rich index).sourcePullback.shading.mass
  rcases finset_ennreal_weighted_pigeonhole (n := 64) (by norm_num)
      Finset.univ weight label with ⟨residue, hretained⟩
  let selected := Finset.univ.filter fun index =>
    ((data.safeBlock index).1 % (64 : ℤ)).toNat = (residue : ℕ)
  have hretained' :
      (∑ index : Fin data.indexCount, weight index) ≤
        64 * ∑ index ∈ selected, weight index := by
    simpa [selected, label, Fin.ext_iff] using hretained
  have hweightPos : ∀ index : Fin data.indexCount, 0 < weight index := by
    intro index
    let rich := data.rich index
    have hselectedCells : rich.richCells.cells ⊆
        rich.sourcePullback.selectedCells := by
      intro cell hcell
      rw [rich.sourcePullback.selectedCells_eq, mem_wz1PaperActiveCells]
      have hactive := rich.richCells.cells_active_carrier hcell
      rw [mem_wz1PaperActiveCells] at hactive
      refine ⟨hactive.1, ?_⟩
      rcases hactive.2 with ⟨point, _hcarrier, hpointCell⟩
      have hpointCellRho : point ∈ wz1PaperGridCube rho cell := by
        simpa only [twoScale.rhoRequested_eq] using hpointCell
      refine ⟨point, ?_, hpointCell⟩
      rw [rich.richShading.union_eq, rich.richShading.region_eq]
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCellRho⟩
    have hselectedNonempty : rich.sourcePullback.selectedCells.Nonempty :=
      rich.richCells.cells_nonempty.mono hselectedCells
    have hselectedCard : 0 <
        (rich.sourcePullback.selectedCells.card : ENNReal) := by
      exact_mod_cast hselectedNonempty.card_pos
    dsimp only [weight]
    rw [rich.sourcePullback.mass_eq]
    exact ENNReal.mul_pos hselectedCard.ne'
      twoScale.coarse.balanced.incidenceMass_pos.ne'
  have htotalPos : 0 < ∑ index : Fin data.indexCount, weight index := by
    let first : Fin data.indexCount := ⟨0, data.indexCount_pos⟩
    exact (hweightPos first).trans_le
      (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ first))
  have hselectedNonempty : selected.Nonempty := by
    by_contra hempty
    have hselectedEmpty : selected = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hzero : ∑ index ∈ selected, weight index = 0 := by
      simp [hselectedEmpty]
    have hleZero : (∑ index : Fin data.indexCount, weight index) ≤ 0 := by
      simpa [hzero] using hretained'
    exact (not_le_of_gt htotalPos) hleZero
  let selectedEquiv := selected.equivFin
  let selectedIndex : Fin selected.card → Fin data.indexCount := fun index =>
    (selectedEquiv.symm index).1
  have hselectedIndexMem : ∀ index, selectedIndex index ∈ selected :=
    fun index => (selectedEquiv.symm index).2
  have hselectedIndexInjective : Function.Injective selectedIndex := by
    intro first second heq
    apply selectedEquiv.symm.injective
    exact Subtype.ext heq
  have hselectedIndexSurjective : ∀ index ∈ selected,
      ∃ selectedIndexValue, selectedIndex selectedIndexValue = index := by
    intro index hindex
    let selectedValue : {index // index ∈ selected} := ⟨index, hindex⟩
    exact ⟨selectedEquiv selectedValue, by
      change (selectedEquiv.symm (selectedEquiv selectedValue)).1 = index
      simp [selectedValue]⟩
  have hselectedSum :
      (∑ index ∈ selected, weight index) =
        ∑ index : Fin selected.card, weight (selectedIndex index) := by
    symm
    apply Finset.sum_bij (fun index _ => selectedIndex index)
    · exact fun index _ => hselectedIndexMem index
    · exact fun first _ second _ heq => hselectedIndexInjective heq
    · intro index hindex
      rcases hselectedIndexSurjective index hindex with ⟨value, hvalue⟩
      exact ⟨value, Finset.mem_univ value, hvalue⟩
    · intro _ _
      rfl
  have hmass :
      (∑ index : Fin data.indexCount,
          (data.rich index).sourcePullback.shading.mass) ≤
        64 * ∑ index : Fin selected.card,
          (data.rich (selectedIndex index)).sourcePullback.shading.mass := by
    change (∑ index : Fin data.indexCount, weight index) ≤
      64 * ∑ index : Fin selected.card, weight (selectedIndex index)
    rw [← hselectedSum]
    exact hretained'
  have hseparated :
      ∀ first second : Fin selected.card, first ≠ second →
        ∀ z ∈ (data.rich
            (selectedIndex first)).richTrapezoid.trapezoid.core,
          ∀ w ∈ (data.rich
              (selectedIndex second)).richTrapezoid.trapezoid.core,
            Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) ≤ |z - w| := by
    intro first second hne
    have hsourceNe : selectedIndex first ≠ selectedIndex second := by
      intro heq
      exact hne (hselectedIndexInjective heq)
    have hblockNe : (data.safeBlock (selectedIndex first)).1 ≠
        (data.safeBlock (selectedIndex second)).1 := by
      intro heq
      exact hsourceNe (data.safeBlock_injective (Subtype.ext heq))
    have hsameResidue :
        (data.safeBlock (selectedIndex first)).1 % (64 : ℤ) =
          (data.safeBlock (selectedIndex second)).1 % (64 : ℤ) := by
      have hfirst := (Finset.mem_filter.mp (hselectedIndexMem first)).2
      have hsecond := (Finset.mem_filter.mp (hselectedIndexMem second)).2
      have hfirstCast := congrArg (fun value : ℕ => (value : ℤ)) hfirst
      have hsecondCast := congrArg (fun value : ℕ => (value : ℤ)) hsecond
      have hfirstNonneg : 0 ≤
          (data.safeBlock (selectedIndex first)).1 % (64 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      have hsecondNonneg : 0 ≤
          (data.safeBlock (selectedIndex second)).1 % (64 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      simpa [label, Int.toNat_of_nonneg hfirstNonneg,
        Int.toNat_of_nonneg hsecondNonneg] using hfirstCast.trans hsecondCast.symm
    exact data.rich_cores_separated_of_block_gap
      (selectedIndex first) (selectedIndex second)
      (sourceFixedLineCoarseResidue_separated hblockNe hsameResidue)
  exact ⟨{
    residue := residue
    selected := selected
    selected_eq := rfl
    selected_nonempty := hselectedNonempty
    selectedIndex := selectedIndex
    selectedIndex_mem := hselectedIndexMem
    selectedIndex_injective := hselectedIndexInjective
    selectedIndex_surjective := hselectedIndexSurjective
    total_mass_le := hmass
    separated_cores := hseparated
  }⟩

end PureWZ2SourceFixedLineCoarseGoodBlockFamilyData

namespace PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData

private lemma selected_residue_separated
    {first second : ℤ} (hne : first ≠ second)
    (hmod : first % (64 : ℤ) = second % (64 : ℤ)) :
    (64 : ℤ) ≤ |first - second| := by
  have hzero : (first - second) % (64 : ℤ) = 0 := by
    rw [Int.sub_emod, hmod]
    simp
  have hdiv : (64 : ℤ) ∣ first - second := by
    rwa [Int.dvd_iff_emod_eq_zero]
  exact Int.le_abs_of_dvd (sub_ne_zero.mpr hne) hdiv

/-- A mod-64 subfamily of the exact chosen-bin rich pipelines.  The blocks
remain indexed by the selected-bin record, so no preparation is re-chosen. -/
structure SelectedBlockResidueData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta volumeLoss : ℝ}
    {logExponent : ℕ} {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale} {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {allBins : PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers}
    {coarseBins : PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins}
    {selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData (volumeLoss := volumeLoss) coarseBins}
    (rich : PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta) selected) where
  residue : Fin 64
  retained : Finset {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe}
  retained_eq : retained = (pureWZ2OrdinaryPaperOrderRegularizedBlocks safe).attach.filter
    fun block => (block.1.1 % (64 : ℤ)).toNat = residue
  retained_nonempty : retained.Nonempty
  selectedIndex : Fin retained.card → {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe}
  selectedIndex_mem : ∀ index, selectedIndex index ∈ retained
  selectedIndex_injective : Function.Injective selectedIndex
  selectedIndex_surjective : ∀ index ∈ retained, ∃ value, selectedIndex value = index
  total_mass_le :
    (∑ block : {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      (rich.rich block).sourcePullback.shading.mass) ≤
      64 * ∑ index : Fin retained.card,
        (rich.rich (selectedIndex index)).sourcePullback.shading.mass
  separated_cores : ∀ first second : Fin retained.card, first ≠ second →
    ∀ z ∈ (rich.rich (selectedIndex first)).richTrapezoid.trapezoid.core,
      ∀ w ∈ (rich.rich (selectedIndex second)).richTrapezoid.trapezoid.core,
        Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) ≤ |z - w|

private theorem selected_rich_cores_separated
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta volumeLoss : ℝ}
    {logExponent : ℕ} {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale} {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {allBins : PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers}
    {coarseBins : PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins}
    {selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData (volumeLoss := volumeLoss) coarseBins}
    (rich : PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta) selected)
    (first second : {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe})
    (hblocks : (64 : ℤ) ≤ |first.1.1 - second.1.1|) :
    ∀ z ∈ (rich.rich first).richTrapezoid.trapezoid.core,
      ∀ w ∈ (rich.rich second).richTrapezoid.trapezoid.core,
        Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) ≤ |z - w| := by
  have hrho : 0 < rho := (carriers.carrier first.1).line.rho_pos
  let root := Real.sqrt rho
  have hscale := pureWZ2SourceHorizontalFinalScale_sqrt_le hrho
  intro z hz w hw
  have hzWindow := (rich.rich first).richTrapezoid.core_height_window z hz
  have hwWindow := (rich.rich second).richTrapezoid.core_height_window w hw
  have hfirstLeft : (carriers.carrier first.1).outerPopular.windowed.left =
      pureWZ2SourceCarrierBlockLeft rho first.1.1 +
        pureWZ2BalancedWindowPhaseShift rho safe.phase := by
    calc
      _ = (safe.blockWindow first.1).window.left :=
        (carriers.carrier first.1).outerPopular.windowed_left
      _ = _ := by rw [(safe.blockWindow first.1).window_left]; rfl
  have hsecondLeft : (carriers.carrier second.1).outerPopular.windowed.left =
      pureWZ2SourceCarrierBlockLeft rho second.1.1 +
        pureWZ2BalancedWindowPhaseShift rho safe.phase := by
    calc
      _ = (safe.blockWindow second.1).window.left :=
        (carriers.carrier second.1).outerPopular.windowed_left
      _ = _ := by rw [(safe.blockWindow second.1).window_left]; rfl
  rw [hfirstLeft] at hzWindow
  rw [hsecondLeft] at hwWindow
  simp only [pureWZ2SourceCarrierBlockLeft] at hzWindow hwWindow
  by_cases horder : first.1.1 < second.1.1
  · have hd : (64 : ℝ) ≤ second.1.1 - first.1.1 := by
      exact_mod_cast (by rw [abs_of_nonpos (sub_nonpos.mpr horder.le)] at hblocks; simpa using hblocks)
    have hsep : 59 * root ≤ w - z := by
      dsimp [root]
      nlinarith [hzWindow.2, hwWindow.1, Real.sqrt_pos.mpr hrho]
    rw [abs_sub_comm, abs_of_nonneg ((mul_pos (by norm_num) (Real.sqrt_pos.mpr hrho)).le.trans hsep)]
    exact hscale.trans (by dsimp [root] at hsep ⊢; nlinarith [Real.sqrt_pos.mpr hrho])
  · have hreverse : second.1.1 < first.1.1 := by
      have hne : first.1.1 ≠ second.1.1 := by intro h; rw [h, sub_self, abs_zero] at hblocks; norm_num at hblocks
      omega
    have hd : (64 : ℝ) ≤ first.1.1 - second.1.1 := by
      exact_mod_cast (by rw [abs_of_nonneg (sub_nonneg.mpr hreverse.le)] at hblocks; exact hblocks)
    have hsep : 59 * root ≤ z - w := by
      dsimp [root]
      nlinarith [hzWindow.1, hwWindow.2, Real.sqrt_pos.mpr hrho]
    rw [abs_of_nonneg ((mul_pos (by norm_num) (Real.sqrt_pos.mpr hrho)).le.trans hsep)]
    exact hscale.trans (by dsimp [root] at hsep ⊢; nlinarith [Real.sqrt_pos.mpr hrho])

theorem selectSelectedResidue
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta volumeLoss : ℝ}
    {logExponent : ℕ} {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale} {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {allBins : PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers}
    {coarseBins : PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins}
    {selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData (volumeLoss := volumeLoss) coarseBins}
    (rich : PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta) selected) :
    Nonempty (SelectedBlockResidueData rich) := by
  let blocks := (pureWZ2OrdinaryPaperOrderRegularizedBlocks safe).attach
  let label : {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe} → Fin 64 :=
    fun block => ⟨(block.1.1 % (64 : ℤ)).toNat, by
      have hn := Int.emod_nonneg block.1.1 (by norm_num : (64 : ℤ) ≠ 0)
      have hl := Int.emod_lt_of_pos block.1.1 (by norm_num : (0 : ℤ) < 64)
      omega⟩
  let weight : {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe} → ENNReal :=
    fun block => (rich.rich block).sourcePullback.shading.mass
  rcases finset_ennreal_weighted_pigeonhole (n := 64) (by norm_num) blocks weight label with ⟨residue, hretained⟩
  let retained := blocks.filter fun block => (block.1.1 % (64 : ℤ)).toNat = (residue : ℕ)
  have hretained' : (∑ block, weight block) ≤ 64 * ∑ block ∈ retained, weight block := by
    simpa [blocks, retained, label, Fin.ext_iff] using hretained
  have hpositive : ∀ block, 0 < weight block := by
    intro block
    let output := rich.rich block
    have hsubset : output.richCells.cells ⊆ output.sourcePullback.selectedCells := by
      intro cell hcell
      rw [output.sourcePullback.selectedCells_eq, mem_wz1PaperActiveCells]
      have hactive := output.richCells.cells_active_carrier hcell
      rw [mem_wz1PaperActiveCells] at hactive
      refine ⟨hactive.1, ?_⟩
      rcases hactive.2 with ⟨point, _hcarrier, hpointCell⟩
      have hpointCellRho : point ∈ wz1PaperGridCube rho cell := by
        simpa only [twoScale.rhoRequested_eq] using hpointCell
      refine ⟨point, ?_, hpointCell⟩
      rw [output.richShading.union_eq, output.richShading.region_eq]
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCellRho⟩
    have hcard : 0 < (output.sourcePullback.selectedCells.card : ENNReal) := by
      exact_mod_cast output.richCells.cells_nonempty.mono hsubset |>.card_pos
    dsimp only [weight]
    rw [output.sourcePullback.mass_eq]
    exact ENNReal.mul_pos hcard.ne' twoScale.coarse.balanced.incidenceMass_pos.ne'
  have hnonempty : retained.Nonempty := by
    by_contra hempty
    have hzero : ∑ block ∈ retained, weight block = 0 := by simp [Finset.not_nonempty_iff_eq_empty.mp hempty]
    rcases safe.regularizedBlocks_nonempty with ⟨value, hvalue⟩
    let block : {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe} := ⟨value, hvalue⟩
    have htotal : 0 < ∑ block, weight block :=
      (hpositive block).trans_le (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ block))
    exact (not_le_of_gt htotal) (by simpa [hzero] using hretained')
  let equiv := retained.equivFin
  let selectedIndex : Fin retained.card → {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe} := fun i => (equiv.symm i).1
  have hmem : ∀ i, selectedIndex i ∈ retained := fun i => (equiv.symm i).2
  have hinj : Function.Injective selectedIndex := by intro a b h; apply equiv.symm.injective; exact Subtype.ext h
  have hsurj : ∀ i ∈ retained, ∃ j, selectedIndex j = i := by
    intro i hi; let x : {i // i ∈ retained} := ⟨i, hi⟩
    exact ⟨equiv x, by change (equiv.symm (equiv x)).1 = i; simp [x]⟩
  have hsum : (∑ i ∈ retained, weight i) = ∑ i : Fin retained.card, weight (selectedIndex i) := by
    symm; apply Finset.sum_bij (fun i _ => selectedIndex i)
    · exact fun i _ => hmem i
    · exact fun a _ b _ h => hinj h
    · intro i hi; rcases hsurj i hi with ⟨j, hj⟩; exact ⟨j, Finset.mem_univ _, hj⟩
    · intro _ _; rfl
  refine ⟨{
    residue := residue
    retained := retained
    retained_eq := rfl
    retained_nonempty := hnonempty
    selectedIndex := selectedIndex
    selectedIndex_mem := hmem
    selectedIndex_injective := hinj
    selectedIndex_surjective := hsurj
    total_mass_le := by rw [← hsum]; exact hretained'
    separated_cores := by
      intro first second hne
      have hblockNe : (selectedIndex first).1.1 ≠ (selectedIndex second).1.1 := by
        intro h
        apply hne
        apply hinj
        exact Subtype.ext (Subtype.ext h)
      have hmod : (selectedIndex first).1.1 % (64 : ℤ) =
          (selectedIndex second).1.1 % (64 : ℤ) := by
        have hfirst := (Finset.mem_filter.mp (hmem first)).2
        have hsecond := (Finset.mem_filter.mp (hmem second)).2
        have hn1 := Int.emod_nonneg (selectedIndex first).1.1 (by norm_num : (64 : ℤ) ≠ 0)
        have hn2 := Int.emod_nonneg (selectedIndex second).1.1 (by norm_num : (64 : ℤ) ≠ 0)
        have hcast := congrArg (fun value : ℕ => (value : ℤ))
          (hfirst.trans hsecond.symm)
        simpa [Int.toNat_of_nonneg hn1, Int.toNat_of_nonneg hn2] using hcast
      exact selected_rich_cores_separated rich _ _
        (selected_residue_separated hblockNe hmod)
  }⟩

end PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData

end Kakeya.Assouad

end
