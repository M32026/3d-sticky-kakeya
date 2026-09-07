import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarsePreGraphMassBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalBlockSeparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderSelectedCoarseBins

/-!
# Mod-64 selection weighted by fixed-bin source height lifts

This is parallel to the older exact coarse-pullback residue.  Its weight is
the mass of the height-only original-family shading, which is the carrier
needed by the paper-faithful `Z_lin` return.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData

private lemma heightLift_residue_separated
    {first second : ℤ} (hne : first ≠ second)
    (hmod : first % (64 : ℤ) = second % (64 : ℤ)) :
    (64 : ℤ) ≤ |first - second| := by
  have hzero : (first - second) % (64 : ℤ) = 0 := by
    rw [Int.sub_emod, hmod]
    simp
  have hdiv : (64 : ℤ) ∣ first - second := by
    rwa [Int.dvd_iff_emod_eq_zero]
  exact Int.le_abs_of_dvd (sub_ne_zero.mpr hne) hdiv

/-- A nonempty mod-64 block class selected using height-lift indexed mass. -/
structure SelectedHeightLiftResidueData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {allBins : PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers}
    {coarseBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins}
    {selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
      (volumeLoss := volumeLoss) coarseBins}
    (rich : PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) selected) where
  residue : Fin 64
  retained : Finset
    {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe}
  retained_eq : retained =
    (pureWZ2OrdinaryPaperOrderRegularizedBlocks safe).attach.filter
      fun block => (block.1.1 % (64 : ℤ)).toNat = residue
  retained_nonempty : retained.Nonempty
  selectedIndex : Fin retained.card →
    {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe}
  selectedIndex_mem : ∀ index, selectedIndex index ∈ retained
  selectedIndex_injective : Function.Injective selectedIndex
  selectedIndex_surjective :
    ∀ index ∈ retained, ∃ value, selectedIndex value = index
  total_mass_le :
    (∑ block :
        {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      (rich.rich block).heightLift.shading.mass) ≤
      64 * ∑ index : Fin retained.card,
        (rich.rich (selectedIndex index)).heightLift.shading.mass
  separated_cores : ∀ first second : Fin retained.card, first ≠ second →
    ∀ z ∈ (rich.rich (selectedIndex first)).richTrapezoid.trapezoid.core,
      ∀ w ∈ (rich.rich
          (selectedIndex second)).richTrapezoid.trapezoid.core,
        Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) ≤ |z - w|

private theorem heightLift_cores_separated
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {allBins : PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers}
    {coarseBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins}
    {selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
      (volumeLoss := volumeLoss) coarseBins}
    (rich : PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) selected)
    (first second :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe})
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
  have hfirstLeft :
      (carriers.carrier first.1).outerPopular.windowed.left =
        pureWZ2SourceCarrierBlockLeft rho first.1.1 +
          pureWZ2BalancedWindowPhaseShift rho safe.phase := by
    calc
      _ = (safe.blockWindow first.1).window.left :=
        (carriers.carrier first.1).outerPopular.windowed_left
      _ = _ := by rw [(safe.blockWindow first.1).window_left]; rfl
  have hsecondLeft :
      (carriers.carrier second.1).outerPopular.windowed.left =
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
      exact_mod_cast (by
        rw [abs_of_nonpos (sub_nonpos.mpr horder.le)] at hblocks
        simpa using hblocks)
    have hsep : 59 * root ≤ w - z := by
      dsimp only [root]
      nlinarith [hzWindow.2, hwWindow.1, Real.sqrt_pos.mpr hrho]
    rw [abs_sub_comm, abs_of_nonneg
      ((mul_pos (by norm_num) (Real.sqrt_pos.mpr hrho)).le.trans hsep)]
    exact hscale.trans (by
      dsimp only [root] at hsep ⊢
      nlinarith [Real.sqrt_pos.mpr hrho])
  · have hreverse : second.1.1 < first.1.1 := by
      have hne : first.1.1 ≠ second.1.1 := by
        intro h
        rw [h, sub_self, abs_zero] at hblocks
        norm_num at hblocks
      omega
    have hd : (64 : ℝ) ≤ first.1.1 - second.1.1 := by
      exact_mod_cast (by
        rw [abs_of_nonneg (sub_nonneg.mpr hreverse.le)] at hblocks
        exact hblocks)
    have hsep : 59 * root ≤ z - w := by
      dsimp only [root]
      nlinarith [hzWindow.1, hwWindow.2, Real.sqrt_pos.mpr hrho]
    rw [abs_of_nonneg
      ((mul_pos (by norm_num) (Real.sqrt_pos.mpr hrho)).le.trans hsep)]
    exact hscale.trans (by
      dsimp only [root] at hsep ⊢
      nlinarith [Real.sqrt_pos.mpr hrho])

theorem selectHeightLiftResidue
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {allBins : PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers}
    {coarseBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins}
    {selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
      (volumeLoss := volumeLoss) coarseBins}
    (rich : PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) selected) :
    Nonempty (SelectedHeightLiftResidueData rich) := by
  let blocks :=
    (pureWZ2OrdinaryPaperOrderRegularizedBlocks safe).attach
  let label :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe} →
        Fin 64 := fun block =>
    ⟨(block.1.1 % (64 : ℤ)).toNat, by
      have hn := Int.emod_nonneg block.1.1 (by norm_num : (64 : ℤ) ≠ 0)
      have hl := Int.emod_lt_of_pos block.1.1 (by norm_num : (0 : ℤ) < 64)
      omega⟩
  let weight :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe} →
        ENNReal := fun block => (rich.rich block).heightLift.shading.mass
  rcases finset_ennreal_weighted_pigeonhole (n := 64) (by norm_num)
      blocks weight label with ⟨residue, hretained⟩
  let retained := blocks.filter fun block =>
    (block.1.1 % (64 : ℤ)).toNat = residue
  have hretained' : (∑ block, weight block) ≤
      64 * ∑ block ∈ retained, weight block := by
    simpa [blocks, retained, label, Fin.ext_iff] using hretained
  have hpositive : ∀ block, 0 < weight block := by
    intro block
    let output := rich.rich block
    have hpullbackPos : 0 < output.sourcePullback.shading.mass := by
      rw [output.sourcePullback.mass_eq]
      have hselectedCells : output.richCells.cells ⊆
          output.sourcePullback.selectedCells := by
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
      have hselectedNonempty : output.sourcePullback.selectedCells.Nonempty :=
        output.richCells.cells_nonempty.mono hselectedCells
      have hselectedCard :
          0 < (output.sourcePullback.selectedCells.card : ENNReal) := by
        exact_mod_cast hselectedNonempty.card_pos
      exact ENNReal.mul_pos
        hselectedCard.ne'
        twoScale.coarse.balanced.incidenceMass_pos.ne'
    exact hpullbackPos.trans_le
      (output.heightLift.sourcePullback_mass_le output.sourcePullback)
  have htotalPos : 0 < ∑ block, weight block := by
    let first :
        {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe} :=
      ⟨Classical.choose safe.regularizedBlocks_nonempty,
        Classical.choose_spec safe.regularizedBlocks_nonempty⟩
    exact (hpositive first).trans_le
      (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ first))
  have hretainedNonempty : retained.Nonempty := by
    by_contra hempty
    have hzero : ∑ block ∈ retained, weight block = 0 := by
      simp [Finset.not_nonempty_iff_eq_empty.mp hempty]
    have hleZero : (∑ block, weight block) ≤ 0 := by
      simpa [hzero] using hretained'
    exact (not_le_of_gt htotalPos) hleZero
  have hmass : (∑ block, weight block) ≤
      64 * ∑ block ∈ retained, weight block := hretained'
  let equiv := retained.equivFin
  let selectedIndex : Fin retained.card →
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe} :=
    fun index => (equiv.symm index).1
  have hmem : ∀ index, selectedIndex index ∈ retained :=
    fun index => (equiv.symm index).2
  have hinj : Function.Injective selectedIndex := by
    intro first second heq
    apply equiv.symm.injective
    exact Subtype.ext heq
  have hsurj : ∀ index ∈ retained, ∃ value, selectedIndex value = index := by
    intro index hindex
    let selectedValue : {index // index ∈ retained} := ⟨index, hindex⟩
    exact ⟨equiv selectedValue, by
      change (equiv.symm (equiv selectedValue)).1 = index
      simp [selectedValue]⟩
  have hsum : (∑ block ∈ retained, weight block) =
      ∑ index : Fin retained.card, weight (selectedIndex index) := by
    symm
    apply Finset.sum_bij (fun index _ => selectedIndex index)
    · exact fun index _ => hmem index
    · exact fun first _ second _ heq => hinj heq
    · intro index hindex
      rcases hsurj index hindex with ⟨value, hvalue⟩
      exact ⟨value, Finset.mem_univ value, hvalue⟩
    · intro _ _
      rfl
  refine ⟨{
    residue := residue
    retained := retained
    retained_eq := rfl
    retained_nonempty := hretainedNonempty
    selectedIndex := selectedIndex
    selectedIndex_mem := hmem
    selectedIndex_injective := hinj
    selectedIndex_surjective := hsurj
    total_mass_le := by
      rw [← hsum]
      simpa only [weight] using hmass
    separated_cores := ?_
  }⟩
  intro first second hne
  have hsourceNe : selectedIndex first ≠ selectedIndex second := by
    intro heq
    exact hne (hinj heq)
  have hblockNe : (selectedIndex first).1.1 ≠
      (selectedIndex second).1.1 := by
    intro heq
    exact hsourceNe (Subtype.ext (Subtype.ext heq))
  have hsameResidue :
      (selectedIndex first).1.1 % (64 : ℤ) =
        (selectedIndex second).1.1 % (64 : ℤ) := by
    have hfirst := (Finset.mem_filter.mp (hmem first)).2
    have hsecond := (Finset.mem_filter.mp (hmem second)).2
    have hn1 := Int.emod_nonneg (selectedIndex first).1.1
      (by norm_num : (64 : ℤ) ≠ 0)
    have hn2 := Int.emod_nonneg (selectedIndex second).1.1
      (by norm_num : (64 : ℤ) ≠ 0)
    have hcast := congrArg (fun value : ℕ => (value : ℤ))
      (hfirst.trans hsecond.symm)
    simpa [Int.toNat_of_nonneg hn1, Int.toNat_of_nonneg hn2] using hcast
  exact heightLift_cores_separated rich _ _
    (heightLift_residue_separated hblockNe hsameResidue)

end PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData

end Kakeya.Assouad

end
