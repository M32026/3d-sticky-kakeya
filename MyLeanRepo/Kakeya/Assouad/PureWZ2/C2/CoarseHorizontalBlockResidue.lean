import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseHorizontalBlockSeparation

/-!
# Mass-weighted residue selection for genuine-coarse rich slabs
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2CoarseHorizontalBlockResidueData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta
      volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    (blocks : PureWZ2CoarseHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      prepared volumeLoss) where
  residue : Fin 64
  selected : Finset (Fin blocks.indexCount)
  selected_eq : selected = Finset.univ.filter fun index =>
    (blocks.block index % (64 : ℤ)).toNat = residue
  selected_nonempty : selected.Nonempty
  family : PureWZ2CoarseHorizontalWindowFamilyData
    (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
    twoScale
  total_mass_le :
    (∑ index : Fin blocks.indexCount,
        (blocks.rich index).richShading.shading.mass) ≤
      64 * family.shading.mass

private lemma coarseBlockResidue_separated
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

theorem PureWZ2CoarseHorizontalGoodBlockFamilyData.selectResidue
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta
      volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    (blocks : PureWZ2CoarseHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      prepared volumeLoss) :
    Nonempty (PureWZ2CoarseHorizontalBlockResidueData blocks) := by
  let label : Fin blocks.indexCount → Fin 64 := fun index =>
    ⟨(blocks.block index % (64 : ℤ)).toNat, by
      have hnonneg : 0 ≤ blocks.block index % (64 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      have hlt : blocks.block index % (64 : ℤ) < (64 : ℤ) :=
        Int.emod_lt_of_pos _ (by norm_num)
      omega⟩
  let weight : Fin blocks.indexCount → ENNReal := fun index =>
    (blocks.rich index).richShading.shading.mass
  rcases finset_ennreal_weighted_pigeonhole (n := 64) (by norm_num)
      Finset.univ weight label with ⟨residue, hretained⟩
  let selected := Finset.univ.filter fun index => label index = residue
  have hweightPos : ∀ index : Fin blocks.indexCount, 0 < weight index := by
    intro index
    have hmult : 0 < (twoScale.fine.fineMultiplicity : ENNReal) := by
      exact_mod_cast twoScale.fine.fineMultiplicity_pos
    have hrho : 0 < rho := by
      rw [← twoScale.rhoRequested_eq]
      exact twoScale.coarseGrains.extremal.delta_pos
    have hcube : 0 < MeasureTheory.volume
        (wz1PaperGridCube rho (0, 0, 0)) := by
      rw [wz1PaperGridCube_volume_exact hrho]
      positivity
    have hcells : 0 <
        (((blocks.rich index).richCells.cells.card : ℕ) : ENNReal) := by
      exact_mod_cast (blocks.rich index).richCells.cells_nonempty.card_pos
    have hunion : 0 < MeasureTheory.volume
        (blocks.rich index).richShading.shading.union := by
      rw [(blocks.rich index).richShading.volume_eq]
      exact ENNReal.mul_pos hcells.ne' hcube.ne'
    have hleft : 0 <
        (twoScale.fine.fineMultiplicity : ENNReal) *
          MeasureTheory.volume
            (blocks.rich index).richShading.shading.union :=
      ENNReal.mul_pos hmult.ne' hunion.ne'
    exact hleft.trans_le (blocks.rich index).richShading.mass_lower
  have htotalPos : 0 < ∑ index : Fin blocks.indexCount, weight index := by
    let first : Fin blocks.indexCount := ⟨0, blocks.indexCount_pos⟩
    exact (hweightPos first).trans_le
      (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ first))
  have hselectedNonempty : selected.Nonempty := by
    by_contra hempty
    have hselectedEmpty : selected = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hzero : ∑ index ∈ selected, weight index = 0 := by
      simp [hselectedEmpty]
    have hleZero : (∑ index : Fin blocks.indexCount, weight index) ≤ 0 := by
      simpa [selected, hzero] using hretained
    exact (not_le_of_gt htotalPos) hleZero
  let selectedEquiv := selected.equivFin
  let selectedIndex : Fin selected.card → Fin blocks.indexCount := fun index =>
    (selectedEquiv.symm index).1
  have hselectedIndexInjective : Function.Injective selectedIndex := by
    intro first second heq
    apply selectedEquiv.symm.injective
    exact Subtype.ext heq
  have hselectedMem : ∀ index, selectedIndex index ∈ selected := fun index =>
    (selectedEquiv.symm index).2
  have hsameResidue : ∀ index,
      blocks.block (selectedIndex index) % (64 : ℤ) = (residue : ℤ) := by
    intro index
    have hlabel := (Finset.mem_filter.mp (hselectedMem index)).2
    have hcast := congrArg (fun value : Fin 64 => (value : ℤ)) hlabel
    have hnonneg : 0 ≤
        blocks.block (selectedIndex index) % (64 : ℤ) :=
      Int.emod_nonneg _ (by norm_num)
    simpa [label, Int.toNat_of_nonneg hnonneg] using hcast
  let family : PureWZ2CoarseHorizontalWindowFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      twoScale := {
    windowCount := selected.card
    windowCount_pos := Finset.card_pos.mpr hselectedNonempty
    pipeline := fun index => blocks.pipeline (selectedIndex index)
    rich := fun index => blocks.rich (selectedIndex index)
    trapezoid_injective := by
      intro first second htrapezoid
      by_contra hne
      have hsourceNe : selectedIndex first ≠ selectedIndex second := by
        intro heq
        exact hne (hselectedIndexInjective heq)
      have hblockNe : blocks.block (selectedIndex first) ≠
          blocks.block (selectedIndex second) :=
        fun heq => hsourceNe (blocks.block_injective heq)
      have hmod : blocks.block (selectedIndex first) % (64 : ℤ) =
          blocks.block (selectedIndex second) % (64 : ℤ) := by
        rw [hsameResidue first, hsameResidue second]
      let z := (blocks.rich (selectedIndex first)).richTrapezoid.trapezoid.left
      have hzFirst : z ∈
          (blocks.rich (selectedIndex first)).richTrapezoid.trapezoid.core := by
        exact ⟨le_rfl,
          (blocks.rich (selectedIndex first)).richTrapezoid.trapezoid.left_lt_right.le⟩
      have hzSecond : z ∈
          (blocks.rich (selectedIndex second)).richTrapezoid.trapezoid.core := by
        change (blocks.rich (selectedIndex first)).richTrapezoid.trapezoid =
          (blocks.rich (selectedIndex second)).richTrapezoid.trapezoid at htrapezoid
        rw [← htrapezoid]
        exact hzFirst
      have hsep := pureWZ2CoarseHorizontalBlockCores_separated
        (blocks.rich (selectedIndex first))
        (blocks.rich (selectedIndex second))
        (blocks.block (selectedIndex first))
        (blocks.block (selectedIndex second))
        (blocks.left_eq (selectedIndex first))
        (blocks.left_eq (selectedIndex second))
        (coarseBlockResidue_separated hblockNe hmod) z hzFirst z hzSecond
      have hscalePos : 0 < pureWZ2CoarseHorizontalFinalScale rho := by
        unfold pureWZ2CoarseHorizontalFinalScale
        have hrho : 0 < rho := by
          rw [← twoScale.rhoRequested_eq]
          exact twoScale.coarseGrains.extremal.delta_pos
        positivity
      exact (not_le_of_gt (Real.sqrt_pos.mpr hscalePos)) (by simpa using hsep)
    separated_cores := by
      intro first second htrapezoidNe
      have hne : first ≠ second := by
        intro heq
        subst second
        exact htrapezoidNe rfl
      have hsourceNe : selectedIndex first ≠ selectedIndex second := by
        intro heq
        exact hne (hselectedIndexInjective heq)
      have hblockNe : blocks.block (selectedIndex first) ≠
          blocks.block (selectedIndex second) :=
        fun heq => hsourceNe (blocks.block_injective heq)
      have hmod : blocks.block (selectedIndex first) % (64 : ℤ) =
          blocks.block (selectedIndex second) % (64 : ℤ) := by
        rw [hsameResidue first, hsameResidue second]
      exact pureWZ2CoarseHorizontalBlockCores_separated
        (blocks.rich (selectedIndex first))
        (blocks.rich (selectedIndex second))
        (blocks.block (selectedIndex first))
        (blocks.block (selectedIndex second))
        (blocks.left_eq (selectedIndex first))
        (blocks.left_eq (selectedIndex second))
        (coarseBlockResidue_separated hblockNe hmod)
  }
  have hselectedMass :
      (∑ index ∈ selected, weight index) =
        ∑ index : Fin family.windowCount,
          (family.rich index).richShading.shading.mass := by
    calc
      (∑ index ∈ selected, weight index) =
          ∑ index : selected, weight index.1 :=
        Finset.sum_subtype selected (fun _ => Iff.rfl) weight
      _ = ∑ index : Fin selected.card,
          weight (selectedEquiv.symm index).1 := by
        exact (Equiv.sum_comp selectedEquiv.symm
          (fun index : selected => weight index.1)).symm
      _ = ∑ index : Fin family.windowCount,
          (family.rich index).richShading.shading.mass := rfl
  have htotal :
      (∑ index : Fin blocks.indexCount,
          (blocks.rich index).richShading.shading.mass) ≤
        64 * family.shading.mass := by
    rw [PureWZ2CoarseHorizontalWindowFamilyData.shading_mass_eq_sum family]
    simpa [weight, selected, hselectedMass] using hretained
  exact ⟨{
    residue := residue
    selected := selected
    selected_eq := by
      apply Finset.ext
      intro index
      simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact congrArg Fin.val h
      · intro h
        exact Fin.ext h
    selected_nonempty := hselectedNonempty
    family := family
    total_mass_le := htotal
  }⟩

theorem PureWZ2CoarseHorizontalGoodBlockFamilyData.selectResidue_mass_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta
      volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    (data : PureWZ2CoarseHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      prepared volumeLoss)
    (hsmall :
      2 * ((pureWZ2PositiveCoarseCarrierBlocks prepared).card : ENNReal) *
          pureWZ2CoarseHorizontalBlockThreshold
            rho sigma middleLoss volumeLoss ≤
        MeasureTheory.volume prepared.shadow.union *
          pureWZ2CoarseHorizontalBlockSupplyFactor
            rho sigma stickyLoss) :
    ∃ residueData : PureWZ2CoarseHorizontalBlockResidueData data,
      MeasureTheory.volume prepared.shadow.union *
          pureWZ2CoarseHorizontalBlockSupplyFactor
            rho sigma stickyLoss *
          PureWZ2CoarseHorizontalGoodBlockFamilyData.richFloor rho finalLoss *
          ((twoScale.fine.fineMultiplicity : ENNReal) *
            MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) ≤
        128 * pureWZ2HorizontalFixedLineVolumeCost
            rho sigma middleLoss *
          PureWZ2CoarseHorizontalGoodBlockFamilyData.graphCellCost
            rho data.extraLoss *
          (54 * PureWZ2CoarseHorizontalGoodBlockFamilyData.snappedHeightCap
            rho) *
          residueData.family.shading.mass := by
  rcases data.selectResidue with ⟨residueData⟩
  refine ⟨residueData,
    (data.aggregate_mass_bound hsmall).trans ?_⟩
  calc
    2 * pureWZ2HorizontalFixedLineVolumeCost rho sigma middleLoss *
          PureWZ2CoarseHorizontalGoodBlockFamilyData.graphCellCost
            rho data.extraLoss *
          (54 * PureWZ2CoarseHorizontalGoodBlockFamilyData.snappedHeightCap
            rho) *
          ∑ index : Fin data.indexCount,
            (data.rich index).richShading.shading.mass ≤
        2 * pureWZ2HorizontalFixedLineVolumeCost rho sigma middleLoss *
          PureWZ2CoarseHorizontalGoodBlockFamilyData.graphCellCost
            rho data.extraLoss *
          (54 * PureWZ2CoarseHorizontalGoodBlockFamilyData.snappedHeightCap
            rho) *
          (64 * residueData.family.shading.mass) := by
      gcongr
      exact residueData.total_mass_le
    _ = 128 * pureWZ2HorizontalFixedLineVolumeCost
          rho sigma middleLoss *
          PureWZ2CoarseHorizontalGoodBlockFamilyData.graphCellCost
            rho data.extraLoss *
          (54 * PureWZ2CoarseHorizontalGoodBlockFamilyData.snappedHeightCap
            rho) *
          residueData.family.shading.mass := by ring

/--
The second sticky refinement turns coarse-body density into true pointwise
multiplicity times the exact prepared volume.
-/
theorem PureWZ2OneScaleTwoScaleStickyData.coarseBody_mass_to_preparedVolume
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent)
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale) :
    wz2PaperPureRefinementFraction
          twoScale.rhoRequested.1 logExponent *
        (Kakeya.realRpowENN twoScale.rhoRequested.1 middleLoss *
          (wz1PaperBodyFamily twoScale.coarse.coarse).mass) ≤
      (2 * twoScale.fine.fineMultiplicity : ENNReal) *
        MeasureTheory.volume prepared.shadow.union := by
  have hmassVolume := constant_multiplicity_mass_volume_generic
    twoScale.fine.refined_multiplicity_band
  calc
    wz2PaperPureRefinementFraction
          twoScale.rhoRequested.1 logExponent *
        (Kakeya.realRpowENN twoScale.rhoRequested.1 middleLoss *
          (wz1PaperBodyFamily twoScale.coarse.coarse).mass) ≤
      wz2PaperPureRefinementFraction
          twoScale.rhoRequested.1 logExponent *
        twoScale.coarseGrains.shading.mass := by
      gcongr
      exact twoScale.coarseGrains.extremal.dense
    _ ≤ twoScale.fine.refined.mass := twoScale.fine.retained_mass
    _ ≤ (2 * twoScale.fine.fineMultiplicity : ENNReal) *
          MeasureTheory.volume twoScale.fine.refined.union :=
      hmassVolume.2
    _ = (2 * twoScale.fine.fineMultiplicity : ENNReal) *
          MeasureTheory.volume prepared.shadow.union := by
      rw [prepared.shadow_union]

/--
Paper-faithful Lemma-24 exit from the selected coarse residue.  The only
remaining analytic input is one explicit small-scale absorption inequality.
-/
theorem PureWZ2CoarseHorizontalBlockResidueData.toOneScaleOfGrainProducer
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta
      volumeLoss structuralLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {blocks : PureWZ2CoarseHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      prepared volumeLoss}
    (residueData : PureWZ2CoarseHorizontalBlockResidueData blocks)
    (hmiddleStructural : middleLoss ≤ structuralLoss)
    (hstructuralFinal : structuralLoss ≤ finalLoss)
    (grainProducer :
      ∀ targetFamily :
          Kakeya.Streamlined.TubeFamily twoScale.rhoRequested.1,
        ∀ targetShading : WZ1PaperTubeShading targetFamily,
          WZ1PaperIsLineClass targetFamily →
          WZ2PaperCroppedIsExtremal
              sigma structuralLoss targetFamily targetShading →
            Nonempty
              (PureWZ2GrainRefinementData
                targetShading sigma finalLoss))
    (haggregate :
      MeasureTheory.volume prepared.shadow.union *
          pureWZ2CoarseHorizontalBlockSupplyFactor
            rho sigma stickyLoss *
          PureWZ2CoarseHorizontalGoodBlockFamilyData.richFloor rho finalLoss *
          ((twoScale.fine.fineMultiplicity : ENNReal) *
            MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) ≤
        128 * pureWZ2HorizontalFixedLineVolumeCost rho sigma middleLoss *
          PureWZ2CoarseHorizontalGoodBlockFamilyData.graphCellCost
            rho blocks.extraLoss *
          (54 * PureWZ2CoarseHorizontalGoodBlockFamilyData.snappedHeightCap
            rho) *
          residueData.family.shading.mass)
    (habsorb :
      256 * pureWZ2HorizontalFixedLineVolumeCost rho sigma middleLoss *
          PureWZ2CoarseHorizontalGoodBlockFamilyData.graphCellCost
            rho blocks.extraLoss *
          (54 * PureWZ2CoarseHorizontalGoodBlockFamilyData.snappedHeightCap
            rho) *
          Kakeya.realRpowENN rho structuralLoss ≤
        wz2PaperPureRefinementFraction rho logExponent *
          Kakeya.realRpowENN rho middleLoss *
          pureWZ2CoarseHorizontalBlockSupplyFactor
            rho sigma stickyLoss *
          PureWZ2CoarseHorizontalGoodBlockFamilyData.richFloor rho finalLoss *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) :
    Nonempty (PureWZ2LocallyLinearOneScaleData
      (twoScale.coarseGrains.toQuantitativeGrainConfiguration
        twoScale.coarseGrains_slope_bound) finalLoss
      (pureWZ2CoarseHorizontalFinalScale rho)) := by
  let cost := pureWZ2HorizontalFixedLineVolumeCost rho sigma middleLoss
  let cellCost := PureWZ2CoarseHorizontalGoodBlockFamilyData.graphCellCost
    rho blocks.extraLoss
  let heightCap :=
    PureWZ2CoarseHorizontalGoodBlockFamilyData.snappedHeightCap rho
  let factor : ENNReal := 256 * cost * cellCost * (54 * heightCap)
  let bodyMass := (wz1PaperBodyFamily twoScale.coarse.coarse).mass
  let floor := PureWZ2CoarseHorizontalGoodBlockFamilyData.richFloor
    rho finalLoss
  let supplyFactor :=
    pureWZ2CoarseHorizontalBlockSupplyFactor rho sigma stickyLoss
  let cubeVolume := MeasureTheory.volume
    (wz1PaperGridCube rho (0, 0, 0))
  let multiplicity : ENNReal := twoScale.fine.fineMultiplicity
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hcostPos : 0 < cost := by
    dsimp only [cost, pureWZ2HorizontalFixedLineVolumeCost]
    have hthickness : 0 < ENNReal.ofReal
        (Real.sqrt rho + 2 * rho) := ENNReal.ofReal_pos.mpr (by positivity)
    have hrhoENN : 0 < ENNReal.ofReal rho :=
      ENNReal.ofReal_pos.mpr hrho
    have hpi : 0 < ENNReal.ofReal Real.pi :=
      ENNReal.ofReal_pos.mpr Real.pi_pos
    have hmiddle : 0 < Kakeya.realRpowENN rho (-middleLoss) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hrho _)
    have hinv : 0 < 1 / rho := by positivity
    have hglobal : 0 < Kakeya.realRpowENN (1 / rho) (1 - sigma) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hinv _)
    have hparent : 0 < (pureWZ2FixedLineParentFiberBound rho : ENNReal) := by
      simp [pureWZ2FixedLineParentFiberBound, pureWZ2FixedLineParentYBound]
    positivity
  have hcostTop : cost ≠ ⊤ := by
    dsimp only [cost]
    exact pureWZ2HorizontalFixedLineVolumeCost_ne_top _ _ _
  have hcellCostPos : 0 < cellCost := by
    dsimp only [cellCost,
      PureWZ2CoarseHorizontalGoodBlockFamilyData.graphCellCost]
    apply ENNReal.ofReal_pos.mpr
    have hscale : 0 < 256 * rho := by positivity
    have hfirst : 0 < Real.rpow (256 * rho) (-blocks.extraLoss) :=
      Real.rpow_pos_of_pos hscale _
    have hsecond : 0 < Real.rpow (256 * rho) (5 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hscale _
    positivity
  have hcellCostTop : cellCost ≠ ⊤ := by
    dsimp only [cellCost,
      PureWZ2CoarseHorizontalGoodBlockFamilyData.graphCellCost]
    exact ENNReal.ofReal_ne_top
  have hheightPos : 0 < heightCap := by
    dsimp only [heightCap,
      PureWZ2CoarseHorizontalGoodBlockFamilyData.snappedHeightCap]
    apply ENNReal.ofReal_pos.mpr
    have : 0 < Real.sqrt (256 * rho) := by positivity
    positivity
  have hheightTop : heightCap ≠ ⊤ := by
    dsimp only [heightCap,
      PureWZ2CoarseHorizontalGoodBlockFamilyData.snappedHeightCap]
    exact ENNReal.ofReal_ne_top
  have hfactorZero : factor ≠ 0 := by
    dsimp only [factor]
    positivity
  have hfactorTop : factor ≠ ⊤ := by
    dsimp only [factor]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) hcostTop) hcellCostTop)
      (ENNReal.mul_ne_top (by norm_num) hheightTop)
  have hcoarseMass :=
    twoScale.coarseBody_mass_to_preparedVolume prepared
  have hcoarseMassRho :
      wz2PaperPureRefinementFraction rho logExponent *
          (Kakeya.realRpowENN rho middleLoss * bodyMass) ≤
        (2 * multiplicity) *
          MeasureTheory.volume prepared.shadow.union := by
    simpa [bodyMass, multiplicity, twoScale.rhoRequested_eq] using hcoarseMass
  have hdense :
      Kakeya.realRpowENN rho structuralLoss * bodyMass ≤
        residueData.family.shading.mass := by
    apply (ENNReal.mul_le_mul_iff_right hfactorZero hfactorTop).mp
    calc
      factor * (Kakeya.realRpowENN rho structuralLoss * bodyMass) =
          (factor * Kakeya.realRpowENN rho structuralLoss) * bodyMass := by
        ring
      _ ≤ (wz2PaperPureRefinementFraction rho logExponent *
            Kakeya.realRpowENN rho middleLoss * supplyFactor * floor *
              cubeVolume) *
          bodyMass := by
        exact mul_le_mul_right'
          (by simpa [factor, cost, cellCost, heightCap, supplyFactor, floor,
              cubeVolume]
            using habsorb)
          bodyMass
      _ = (wz2PaperPureRefinementFraction rho logExponent *
            (Kakeya.realRpowENN rho middleLoss * bodyMass)) *
          supplyFactor * floor * cubeVolume := by ring
      _ ≤ ((2 * multiplicity) *
            MeasureTheory.volume prepared.shadow.union) *
          supplyFactor * floor * cubeVolume := by gcongr
      _ = 2 * (MeasureTheory.volume prepared.shadow.union * supplyFactor *
            floor *
            (multiplicity * cubeVolume)) := by ring
      _ ≤ 2 * (128 * cost * cellCost * (54 * heightCap) *
            residueData.family.shading.mass) := by
        exact mul_le_mul_left'
          (by simpa [floor, supplyFactor, multiplicity, cubeVolume, cost,
              cellCost, heightCap] using haggregate)
          2
      _ = factor * residueData.family.shading.mass := by
        simp [factor]
        ring
  have hdenseStored : residueData.family.shading.IsLambdaDense
      (Kakeya.realRpowENN twoScale.rhoRequested.1 structuralLoss) := by
    have hbudgetStored :
        Kakeya.realRpowENN twoScale.rhoRequested.1 structuralLoss *
            (wz1PaperBodyFamily twoScale.coarse.coarse).mass ≤
          residueData.family.shading.mass := by
      simpa [twoScale.rhoRequested_eq, bodyMass] using hdense
    exact residueData.family.dense_of_mass_budget hbudgetStored
  exact residueData.family.toOneScaleOfGrainProducer
    hmiddleStructural hstructuralFinal grainProducer hdenseStored

end Kakeya.Assouad
