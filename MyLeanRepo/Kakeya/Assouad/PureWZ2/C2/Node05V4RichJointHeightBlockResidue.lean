import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightBlockFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalBlockResidue

/-!
# Weighted separated residue of joint-height blocks

Heavy slabs are colored modulo 64 by their literal slab index and weighted by
the mass of their same-witness whole-cell lift.  The selected residue retains
a fixed fraction of that actual mass.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2Node05V4RichJointBlockResidueData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta finalLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {B₀ threshold : ENNReal}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (family : PureWZ2Node05V4RichJointBlockFamily
      (eta := eta) pullback B₀ threshold hbridge projection) where
  residue : Fin 64
  selectedBlocks : Finset {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback} :=
    Finset.univ.filter fun heightIndex =>
      (heightIndex.1.1 % (64 : ℤ)).toNat = residue
  selectedBlocks_eq :
    selectedBlocks = Finset.univ.filter fun heightIndex =>
      (heightIndex.1.1 % (64 : ℤ)).toNat = residue
  selectedBlocks_nonempty : selectedBlocks.Nonempty
  block_residue :
    ∀ heightIndex ∈ selectedBlocks,
      heightIndex.1.1 % (64 : ℤ) = (residue : ℤ)
  mass_retention :
    (∑ heightIndex, (family.lift heightIndex).shading.mass) ≤
      64 * ∑ heightIndex ∈ selectedBlocks,
        (family.lift heightIndex).shading.mass

namespace PureWZ2Node05V4RichJointBlockFamily

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta finalLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {B₀ threshold : ENNReal}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (family : PureWZ2Node05V4RichJointBlockFamily
      (eta := eta) pullback B₀ threshold hbridge projection)

theorem lift_mass_pos
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}) :
    0 < (family.lift heightIndex).shading.mass := by
  let data := family.theorem52 heightIndex
  have hfloorNat : 0 <
      twoScale.first.fourDegreeReceipts.fineDegreeFloor *
        twoScale.first.fourDegreeReceipts.muFine :=
    Nat.mul_pos twoScale.first.fourDegreeReceipts.fineDegreeFloor_pos
      twoScale.first.fourDegreeReceipts.muFine_pos
  have hfloor : 0 <
      (((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
        twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal)) := by
    exact_mod_cast hfloorNat
  have hheightCardNat : 0 < data.output.richHeightIndices.card := by
    rw [data.output.richHeightIndices_card]
    exact data.output.lineData.richF_nonempty.card_pos
  have hheightCard : 0 <
      (data.output.richHeightIndices.card : ENNReal) := by
    exact_mod_cast hheightCardNat
  have hleft :
      0 < (((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
            twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
        ((data.output.richHeightIndices.card : ENNReal) *
          (family.prepared heightIndex).volumePopular.popular.layerMass)) :=
    ENNReal.mul_pos hfloor.ne' <|
      (ENNReal.mul_pos hheightCard.ne'
        (family.prepared heightIndex).volumePopular.popular.layerMass_pos.ne').ne'
  have hcoreScaled :
      0 < 3 * data.sourceMass.shading.mass :=
    hleft.trans_le data.sourceMass.rich_mass_lower
  have hcore : 0 < data.sourceMass.shading.mass := by
    by_contra hnot
    have hzero : data.sourceMass.shading.mass = 0 :=
      bot_unique (not_lt.mp hnot)
    rw [hzero, mul_zero] at hcoreScaled
    exact (lt_irrefl 0 hcoreScaled)
  exact hcore.trans_le (family.lift heightIndex).sourceCore_mass_le

theorem selectBlockResidue :
    Nonempty (PureWZ2Node05V4RichJointBlockResidueData family) := by
  let Block := {heightIndex //
    heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}
  let weight : Block → ENNReal := fun heightIndex =>
    (family.lift heightIndex).shading.mass
  let color : Block → Fin 64 := fun heightIndex =>
    ⟨(heightIndex.1.1 % (64 : ℤ)).toNat, by
      have hnonneg : 0 ≤ heightIndex.1.1 % (64 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      have hlt : heightIndex.1.1 % (64 : ℤ) < (64 : ℤ) :=
        Int.emod_lt_of_pos _ (by norm_num)
      omega⟩
  rcases finset_ennreal_weighted_pigeonhole
      (n := 64) (by norm_num) Finset.univ weight color with
    ⟨residue, hretained⟩
  let selectedBlocks := Finset.univ.filter fun heightIndex : Block =>
    color heightIndex = residue
  have hallPos : 0 < ∑ heightIndex : Block, weight heightIndex := by
    rcases pullback.heavySlabs_nonempty with ⟨heightIndex, hheightIndex⟩
    let blockIndex : Block := ⟨heightIndex, hheightIndex⟩
    have hsingle :
        weight blockIndex ≤ ∑ heightIndex : Block, weight heightIndex :=
      Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ blockIndex)
    exact (family.lift_mass_pos blockIndex).trans_le hsingle
  have hselectedNonempty : selectedBlocks.Nonempty := by
    by_contra hempty
    have hempty' : selectedBlocks = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hzero : ∑ heightIndex ∈ selectedBlocks, weight heightIndex = 0 := by
      simp [hempty']
    have hallZero : ∑ heightIndex : Block, weight heightIndex = 0 := by
      have hle : (∑ heightIndex : Block, weight heightIndex) ≤ 0 := by
        simpa [selectedBlocks, hzero] using hretained
      exact le_zero_iff.mp hle
    exact (ne_of_gt hallPos) hallZero
  exact ⟨{
    residue := residue
    selectedBlocks := selectedBlocks
    selectedBlocks_eq := by
      apply Finset.ext
      intro heightIndex
      simp only [selectedBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hcolor
        exact congrArg Fin.val hcolor
      · intro hvalue
        exact Fin.ext hvalue
    selectedBlocks_nonempty := hselectedNonempty
    block_residue := by
      intro heightIndex hheightIndex
      have hcolor := (Finset.mem_filter.mp hheightIndex).2
      have hnonneg : 0 ≤ heightIndex.1.1 % (64 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      have hcast : ((color heightIndex : ℕ) : ℤ) =
          heightIndex.1.1 % (64 : ℤ) := by
        simp [color, Int.toNat_of_nonneg hnonneg]
      have hcastEq :=
        congrArg (fun value : Fin 64 => (value : ℤ)) hcolor
      rwa [hcast] at hcastEq
    mass_retention := by
      change (∑ heightIndex : Block, weight heightIndex) ≤
        64 * ∑ heightIndex ∈ selectedBlocks, weight heightIndex
      simpa [selectedBlocks] using hretained
  }⟩

end PureWZ2Node05V4RichJointBlockFamily

end Kakeya.Assouad

end
