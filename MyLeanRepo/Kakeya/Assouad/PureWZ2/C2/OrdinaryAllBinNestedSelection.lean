import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryAllBinNestedRegionalCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalBlockSeparation

/-!
# Finite selection for the nested ordinary regional construction

The concrete regional family has three dependent finite indices: source block,
source global bin, and nested coarse global bin.  This module compresses the
two inner indices one at a time.  No additivity is asserted between outputs
from the same source block.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

private theorem exists_finset_max_sum
    {α : Type*} [DecidableEq α] (indices : Finset α)
    (hindices : indices.Nonempty) (weight : {index // index ∈ indices} → ENNReal) :
    ∃ selected : {index // index ∈ indices},
      (∑ index : {index // index ∈ indices}, weight index) ≤
        (indices.card : ENNReal) * weight selected := by
  let first : {index // index ∈ indices} :=
    ⟨Classical.choose hindices, Classical.choose_spec hindices⟩
  rcases Finset.exists_max_image (Finset.univ :
      Finset {index // index ∈ indices}) weight
      ⟨first, Finset.mem_univ first⟩ with ⟨selected, _, hmax⟩
  refine ⟨selected, ?_⟩
  simpa [nsmul_eq_mul] using
    (Finset.sum_le_card_nsmul
      (Finset.univ : Finset {index // index ∈ indices}) weight
      (weight selected) (fun index hindex => hmax index hindex))

namespace PureWZ2OrdinaryAllBinNestedRegionalData

variable
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta finalLoss
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {companions : PureWZ2OrdinaryAllBinOuterPopularCompanionData carriers}

private def nestedMass
    (regional : PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions)
    (block : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe})
    (bin : {bin // bin ∈ (regional.sourceBins block).line.globalBins})
    (nestedBin : {nestedBin //
      nestedBin ∈ ((regional.family block).good bin).selected}) : ENNReal :=
  (((regional.family block).rich bin).rich nestedBin).heightLift.shading.mass

/-- The maximum-mass nested output in one source bin. -/
noncomputable def selectedNestedBin
    (regional : PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions)
    (block : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe})
    (bin : {bin // bin ∈ (regional.sourceBins block).line.globalBins}) :
    {nestedBin // nestedBin ∈ ((regional.family block).good bin).selected} :=
  Classical.choose (exists_finset_max_sum
    ((regional.family block).good bin).selected
    ((regional.family block).good bin).selected_nonempty
    (nestedMass regional block bin))

theorem nested_mass_le_selected
    (regional : PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions)
    (block : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe})
    (bin : {bin // bin ∈ (regional.sourceBins block).line.globalBins}) :
    (∑ nestedBin : {nestedBin //
        nestedBin ∈ ((regional.family block).good bin).selected},
      (((regional.family block).rich bin).rich
        nestedBin).heightLift.shading.mass) ≤
      (((regional.family block).good bin).selected.card : ENNReal) *
        (((regional.family block).rich bin).rich
          (regional.selectedNestedBin block bin)).heightLift.shading.mass := by
  exact Classical.choose_spec (exists_finset_max_sum
    ((regional.family block).good bin).selected
    ((regional.family block).good bin).selected_nonempty
    (nestedMass regional block bin))

private def sourceBinWeight
    (regional : PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions)
    (block : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe})
    (bin : {bin // bin ∈ (regional.sourceBins block).line.globalBins}) :
    ENNReal :=
  (((regional.family block).good bin).selected.card : ENNReal) *
    (((regional.family block).rich bin).rich
      (regional.selectedNestedBin block bin)).heightLift.shading.mass

/-- The maximum weighted source-bin output in one source block. -/
noncomputable def selectedSourceBin
    (regional : PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions)
    (block : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe}) :
    {bin // bin ∈ (regional.sourceBins block).line.globalBins} :=
  Classical.choose (exists_finset_max_sum
    (regional.sourceBins block).line.globalBins
    ⟨(regional.sourceBins block).line.lineBin,
      (regional.sourceBins block).line.lineBin_mem⟩
    (sourceBinWeight regional block))

theorem block_mass_le_selected
    (regional : PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions)
    (block : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe}) :
    (∑ bin : {bin // bin ∈ (regional.sourceBins block).line.globalBins},
        ∑ nestedBin : {nestedBin //
            nestedBin ∈ ((regional.family block).good bin).selected},
          (((regional.family block).rich bin).rich
            nestedBin).heightLift.shading.mass) ≤
      ((regional.sourceBins block).line.globalBins.card : ENNReal) *
        (((regional.family block).good
          (regional.selectedSourceBin block)).selected.card : ENNReal) *
        (((regional.family block).rich
          (regional.selectedSourceBin block)).rich
          (regional.selectedNestedBin block
            (regional.selectedSourceBin block))).heightLift.shading.mass := by
  calc
    _ ≤ ∑ bin : {bin //
        bin ∈ (regional.sourceBins block).line.globalBins},
      sourceBinWeight regional block bin := by
        exact Finset.sum_le_sum fun bin _ =>
          regional.nested_mass_le_selected block bin
    _ ≤ ((regional.sourceBins block).line.globalBins.card : ENNReal) *
        sourceBinWeight regional block (regional.selectedSourceBin block) :=
      Classical.choose_spec (exists_finset_max_sum
        (regional.sourceBins block).line.globalBins
        ⟨(regional.sourceBins block).line.lineBin,
          (regional.sourceBins block).line.lineBin_mem⟩
        (sourceBinWeight regional block))
    _ = _ := by
      unfold sourceBinWeight
      ring

/-- The single provenance-bearing rich output selected from one regularized
source block.  Naming it keeps the residue interface small enough to elaborate
under the repository's default proof budget. -/
def selectedRich
    (regional : PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions)
    (block : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe}) :=
  ((regional.family block).rich
    (regional.selectedSourceBin block)).rich
      (regional.selectedNestedBin block (regional.selectedSourceBin block))

def selectedMass
    (regional : PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions)
    (block : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe}) : ENNReal :=
  (selectedRich regional block).heightLift.shading.mass

def selectedShading
    (regional : PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions)
    (block : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe}) :
    WZ1PaperTubeShading source.family :=
  (selectedRich regional block).heightLift.shading

def selectedTrapezoid
    (regional : PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions)
    (block : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe}) :
    WZ1VerticalTrapezoid :=
  (selectedRich regional block).richTrapezoid.trapezoid

private theorem nested_selected_cores_separated
    (regional : PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions)
    (first second : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe})
    (hblocks : (64 : ℤ) ≤ |first.1.1 - second.1.1|) :
    let firstBin := regional.selectedSourceBin first
    let secondBin := regional.selectedSourceBin second
    let firstNested := regional.selectedNestedBin first firstBin
    let secondNested := regional.selectedNestedBin second secondBin
    ∀ z ∈ (((regional.family first).rich firstBin).rich
        firstNested).richTrapezoid.trapezoid.core,
      ∀ w ∈ (((regional.family second).rich secondBin).rich
          secondNested).richTrapezoid.trapezoid.core,
        Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) ≤ |z - w| := by
  dsimp only
  have hrho : 0 < rho :=
    (regional.sourceBins first).line.rho_pos
  let root := Real.sqrt rho
  have hscale := pureWZ2SourceHorizontalFinalScale_sqrt_le hrho
  intro z hz w hw
  have hzWindow := (((regional.family first).rich
    (regional.selectedSourceBin first)).rich
      (regional.selectedNestedBin first
        (regional.selectedSourceBin first))).richTrapezoid.core_height_window z hz
  have hwWindow := (((regional.family second).rich
    (regional.selectedSourceBin second)).rich
      (regional.selectedNestedBin second
        (regional.selectedSourceBin second))).richTrapezoid.core_height_window w hw
  have hfirstLeft : (regional.sourceWindow first).window.left =
      pureWZ2SourceCarrierBlockLeft rho first.1.1 +
        pureWZ2BalancedWindowPhaseShift rho safe.phase := by
    calc
      _ = (safe.blockWindow first.1).window.left :=
        (regional.sourceWindow first).window_left
      _ = _ := by rw [(safe.blockWindow first.1).window_left]; rfl
  have hsecondLeft : (regional.sourceWindow second).window.left =
      pureWZ2SourceCarrierBlockLeft rho second.1.1 +
        pureWZ2BalancedWindowPhaseShift rho safe.phase := by
    calc
      _ = (safe.blockWindow second.1).window.left :=
        (regional.sourceWindow second).window_left
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
        intro heq
        rw [heq, sub_self, abs_zero] at hblocks
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

/-- A mass-heavy mod-64 family after the two inner indices have been selected. -/
structure SelectedBlockResidueData
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta finalLoss
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {companions : PureWZ2OrdinaryAllBinOuterPopularCompanionData carriers}
    (regional : PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions) where
  residue : Fin 64
  retained : Finset {block //
    block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe}
  retained_eq : retained =
    (pureWZ2OrdinaryPaperOrderRegularizedBlocks safe).attach.filter
      fun block => (block.1.1 % (64 : ℤ)).toNat = residue
  retained_nonempty : retained.Nonempty
  selectedIndex : Fin retained.card →
    {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe}
  selectedIndex_mem : ∀ index, selectedIndex index ∈ retained
  selectedIndex_injective : Function.Injective selectedIndex
  selectedIndex_surjective : ∀ block ∈ retained,
    ∃ index, selectedIndex index = block
  total_mass_le :
    (∑ block : {block //
        block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      selectedMass regional block) ≤
      64 * ∑ index : Fin retained.card,
        selectedMass regional (selectedIndex index)

/-- Select the mass-heavy block residue for the concrete nested regional
family. -/
theorem selectBlockResidue
    (regional : PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions) :
    Nonempty (regional.SelectedBlockResidueData) := by
  let blocks :=
    (pureWZ2OrdinaryPaperOrderRegularizedBlocks safe).attach
  let label : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe} → Fin 64 :=
    fun block => ⟨(block.1.1 % (64 : ℤ)).toNat, by
      have hn := Int.emod_nonneg block.1.1 (by norm_num : (64 : ℤ) ≠ 0)
      have hl := Int.emod_lt_of_pos block.1.1 (by norm_num : (0 : ℤ) < 64)
      omega⟩
  let weight : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe} → ENNReal :=
    selectedMass regional
  rcases finset_ennreal_weighted_fiber_retention blocks weight label with
    ⟨residue, hretained⟩
  let retained := blocks.filter fun block =>
    (block.1.1 % (64 : ℤ)).toNat = residue
  have hretained' : (∑ block, weight block) ≤
      64 * ∑ block ∈ retained, weight block := by
    simpa [blocks, retained, label, Fin.ext_iff] using hretained
  have hweightPos : ∀ block, 0 < weight block := by
    intro block
    let selectedBin := regional.selectedSourceBin block
    let selectedNested := regional.selectedNestedBin block selectedBin
    let saturation :=
      (regional.family block).rich selectedBin |>.saturation selectedNested
    have hheightNonempty :
        (((regional.family block).rich selectedBin).rich
          selectedNested).rich.heightIndices.Nonempty := by
      rw [((regional.family block).rich selectedBin).rich
        selectedNested |>.rich.heightIndices_eq]
      exact (((regional.family block).rich selectedBin).rich
        selectedNested).rich.richF_nonempty.image _
    have hleftPos : 0 <
        ((((regional.family block).rich selectedBin).rich
          selectedNested).rich.heightIndices.card : ENNReal) *
          (((regional.family block).rich selectedBin).pipeline
            selectedNested).preparedGraph.heightPopular.layerMass *
          twoScale.coarse.balanced.incidenceMass := by
      have hcardPos : 0 <
          ((((regional.family block).rich selectedBin).rich
            selectedNested).rich.heightIndices.card : ENNReal) := by
        exact_mod_cast hheightNonempty.card_pos
      have hlayerPos : 0 <
          (((regional.family block).rich selectedBin).pipeline
            selectedNested).preparedGraph.heightPopular.layerMass :=
        (((regional.family block).rich selectedBin).pipeline
          selectedNested).preparedGraph.heightPopular.layerMass_pos
      have hpairPos : 0 <
          ((((regional.family block).rich selectedBin).rich
            selectedNested).rich.heightIndices.card : ENNReal) *
            (((regional.family block).rich selectedBin).pipeline
              selectedNested).preparedGraph.heightPopular.layerMass :=
        ENNReal.mul_pos_iff.mpr ⟨hcardPos, hlayerPos⟩
      exact ENNReal.mul_pos hpairPos.ne'
        twoScale.coarse.balanced.incidenceMass_pos.ne'
    have hrightPos : 0 <
        (((regional.family block).rich selectedBin).rich
          selectedNested).heightLift.shading.mass *
          volume (wz1PaperGridCube rho (0, 0, 0)) :=
      hleftPos.trans_le saturation.mass_cube_lower
    dsimp only [weight]
    exact (ENNReal.mul_pos_iff.mp hrightPos).1
  have htotalPos : 0 < ∑ block, weight block := by
    let first : {block //
        block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe} :=
      ⟨Classical.choose safe.regularizedBlocks_nonempty,
        Classical.choose_spec safe.regularizedBlocks_nonempty⟩
    exact (hweightPos first).trans_le
      (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ first))
  have hretainedNonempty : retained.Nonempty := by
    by_contra hempty
    have hzero : ∑ block ∈ retained, weight block = 0 := by
      simp [Finset.not_nonempty_iff_eq_empty.mp hempty]
    have hleZero : (∑ block, weight block) ≤ 0 := by
      simpa [hzero] using hretained'
    exact (not_le_of_gt htotalPos) hleZero
  let equiv := retained.equivFin
  let selectedIndex : Fin retained.card →
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe} :=
    fun index => (equiv.symm index).1
  have hmem : ∀ index, selectedIndex index ∈ retained :=
    fun index => (equiv.symm index).2
  have hinjective : Function.Injective selectedIndex := by
    intro first second heq
    apply equiv.symm.injective
    exact Subtype.ext heq
  have hsurjective : ∀ block ∈ retained,
      ∃ index, selectedIndex index = block := by
    intro block hblock
    let selectedBlock : {block // block ∈ retained} := ⟨block, hblock⟩
    exact ⟨equiv selectedBlock, by
      change (equiv.symm (equiv selectedBlock)).1 = block
      simp [selectedBlock]⟩
  have hsum : (∑ block ∈ retained, weight block) =
      ∑ index : Fin retained.card, weight (selectedIndex index) := by
    symm
    apply Finset.sum_bij (fun index _ => selectedIndex index)
    · exact fun index _ => hmem index
    · exact fun first _ second _ heq => hinjective heq
    · intro block hblock
      rcases hsurjective block hblock with ⟨index, hindex⟩
      exact ⟨index, Finset.mem_univ index, hindex⟩
    · intro _ _
      rfl
  refine ⟨{
    residue := residue
    retained := retained
    retained_eq := rfl
    retained_nonempty := hretainedNonempty
    selectedIndex := selectedIndex
    selectedIndex_mem := hmem
    selectedIndex_injective := hinjective
    selectedIndex_surjective := hsurjective
    total_mass_le := by rw [← hsum]; exact hretained'
  }⟩

/-- Distinct members of the selected residue have separated rich cores.  This
is derived from the retained indices instead of stored in the finite selector,
which keeps the selector's dependent record inexpensive to elaborate. -/
theorem SelectedBlockResidueData.separated_cores
    (regional : PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions)
    (residueData : regional.SelectedBlockResidueData)
    (first second : Fin residueData.retained.card) (hne : first ≠ second) :
    ∀ z ∈ (selectedTrapezoid regional
        (residueData.selectedIndex first)).core,
      ∀ w ∈ (selectedTrapezoid regional
          (residueData.selectedIndex second)).core,
        Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) ≤ |z - w| := by
  have hblockNe : (residueData.selectedIndex first).1.1 ≠
      (residueData.selectedIndex second).1.1 := by
    intro heq
    exact hne (residueData.selectedIndex_injective
      (Subtype.ext (Subtype.ext heq)))
  have hsameResidue :
      (residueData.selectedIndex first).1.1 % (64 : ℤ) =
        (residueData.selectedIndex second).1.1 % (64 : ℤ) := by
    have hfirst := residueData.selectedIndex_mem first
    have hsecond := residueData.selectedIndex_mem second
    rw [residueData.retained_eq] at hfirst hsecond
    have hfirst' := (Finset.mem_filter.mp hfirst).2
    have hsecond' := (Finset.mem_filter.mp hsecond).2
    have hn1 := Int.emod_nonneg (residueData.selectedIndex first).1.1
      (by norm_num : (64 : ℤ) ≠ 0)
    have hn2 := Int.emod_nonneg (residueData.selectedIndex second).1.1
      (by norm_num : (64 : ℤ) ≠ 0)
    have hcast := congrArg (fun value : ℕ => (value : ℤ))
      (hfirst'.trans hsecond'.symm)
    simpa [Int.toNat_of_nonneg hn1,
      Int.toNat_of_nonneg hn2] using hcast
  have hgap : (64 : ℤ) ≤
      |(residueData.selectedIndex first).1.1 -
        (residueData.selectedIndex second).1.1| := by
    have hzero : ((residueData.selectedIndex first).1.1 -
        (residueData.selectedIndex second).1.1) % (64 : ℤ) = 0 := by
      rw [Int.sub_emod, hsameResidue]
      simp
    exact Int.le_abs_of_dvd (sub_ne_zero.mpr hblockNe)
      (by rwa [Int.dvd_iff_emod_eq_zero])
  simpa [selectedTrapezoid, selectedRich] using
    nested_selected_cores_separated regional _ _ hgap

end PureWZ2OrdinaryAllBinNestedRegionalData

end Kakeya.Assouad

end
