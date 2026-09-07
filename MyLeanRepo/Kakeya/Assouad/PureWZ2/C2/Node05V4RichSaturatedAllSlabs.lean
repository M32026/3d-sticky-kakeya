import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSaturatedHeightLift
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichNeighborhoodDensity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalGoodBlocks

/-!
# Heavy standard slabs for the saturated Node-5 route

This module selects the source-volume-heavy standard side-`sqrt rho` slabs
before any common-bin or Theorem-5.2 choice.  The selected slabs retain half
of the exact source union volume.  Since every slab restriction inherits the
same first-V4 multiplicity band, the same selection retains indexed source
mass up to the single terminal regularity factor.

No old weighted-owner or fixed-line block record is used.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

def pureWZ2Node05V4RichHeavySlabThreshold
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale) : ENNReal :=
  (10 : ENNReal)⁻¹ * volume pullback.shading.union *
    ENNReal.ofReal (Real.sqrt rho)

def pureWZ2Node05V4RichHeavySlabs
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale) :
    Finset {heightIndex // heightIndex ∈ pullback.standardSqrtSlabIndices} :=
  Finset.univ.filter fun heightIndex =>
    pureWZ2Node05V4RichHeavySlabThreshold pullback ≤
      volume (pullback.standardSqrtSlabSourceRegion heightIndex.1)

namespace PureWZ2Node05V4RichTwoScaleCellPullbackData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)

def standardSqrtSlabSourceShading (heightIndex : ℤ) :
    WZ1PaperTubeShading current.grain.family :=
  pureWZ2Node05RestrictToCells (rho := rho) pullback.shading
    (pullback.standardSqrtSlabRhoCells heightIndex)

theorem standardSqrtSlabSourceShading_union (heightIndex : ℤ) :
    (pullback.standardSqrtSlabSourceShading heightIndex).union =
      pullback.standardSqrtSlabSourceRegion heightIndex := by
  exact pureWZ2Node05RestrictToCells_union pullback.shading _

theorem standardSqrtSlabSourceShading_sub_source (heightIndex : ℤ) :
    PureWZ2PaperIsSubshading
      (pullback.standardSqrtSlabSourceShading heightIndex)
      current.grain.shading := by
  intro source point hpoint
  exact pullback.subshading source hpoint.1

theorem standardSqrtSlabSourceShading_constantMultiplicity (heightIndex : ℤ) :
    (pullback.standardSqrtSlabSourceShading heightIndex).HasConstantMultiplicity
      (twoScale.first.fourDegreeReceipts.fineDegreeFloor *
        twoScale.first.fourDegreeReceipts.muFine)
      ((twoScale.first.fourDegreeReceipts.regularity *
        twoScale.first.fourDegreeReceipts.fineDegreeFloor) *
          twoScale.first.fourDegreeReceipts.muFine) :=
  pureWZ2Node05RestrictToCells_constantMultiplicity
    pullback.source_constantMultiplicity

theorem standardSqrtSlabSourceShading_mass_lower (heightIndex : ℤ) :
    ((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
          twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
        volume (pullback.standardSqrtSlabSourceRegion heightIndex) ≤
      (pullback.standardSqrtSlabSourceShading heightIndex).mass := by
  rw [← pullback.standardSqrtSlabSourceShading_union heightIndex]
  apply multiplicity_floor_le_mass
  intro point hpoint
  exact_mod_cast
    (pullback.standardSqrtSlabSourceShading_constantMultiplicity
      heightIndex point hpoint).1

theorem standardSqrtSlabSourceShading_mass_upper (heightIndex : ℤ) :
    (pullback.standardSqrtSlabSourceShading heightIndex).mass ≤
      (((twoScale.first.fourDegreeReceipts.regularity *
          twoScale.first.fourDegreeReceipts.fineDegreeFloor) *
            twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
        volume (pullback.standardSqrtSlabSourceRegion heightIndex) := by
  rw [← pullback.standardSqrtSlabSourceShading_union heightIndex]
  apply mass_le_of_pointMultiplicity_le
  intro point hpoint
  exact_mod_cast
    (pullback.standardSqrtSlabSourceShading_constantMultiplicity
      heightIndex point hpoint).2

theorem heavySlabThreshold_ne_top :
    pureWZ2Node05V4RichHeavySlabThreshold pullback ≠ ⊤ := by
  have hsourceTop : volume pullback.shading.union ≠ ⊤ := by
    rw [pullback.volume_eq]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      pullback.firstPostBalanced.cellMass_ne_top
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by norm_num) hsourceTop) ENNReal.ofReal_ne_top

theorem heavySlabs_retains_half_volume :
    volume pullback.shading.union ≤
      2 * ∑ heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback,
        volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) := by
  let slabs : Finset {heightIndex //
      heightIndex ∈ pullback.standardSqrtSlabIndices} := Finset.univ
  let sourceVolume := volume pullback.shading.union
  let root := ENNReal.ofReal (Real.sqrt rho)
  let threshold := pureWZ2Node05V4RichHeavySlabThreshold pullback
  have hrhoOne : rho ≤ 1 := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.2
  have hcardRoot : (slabs.card : ENNReal) * root ≤ 5 := by
    simpa [slabs, root] using
      pullback.standardSqrtSlabIndices_card_mul_sqrtENN_le_five hrhoOne
  have hsmall : 2 * ((slabs.card : ENNReal) * threshold) ≤ sourceVolume := by
    have hcoefficient : (2 : ENNReal) * (10 : ENNReal)⁻¹ * 5 = 1 := by
      rw [show (10 : ENNReal) = 2 * 5 by norm_num,
        ENNReal.mul_inv (by norm_num) (by norm_num)]
      calc
        (2 : ENNReal) * (2⁻¹ * 5⁻¹) * 5 =
            (2 * 2⁻¹) * (5⁻¹ * 5) := by ac_rfl
        _ = 1 := by
          rw [ENNReal.mul_inv_cancel, ENNReal.inv_mul_cancel] <;> norm_num
    calc
      2 * ((slabs.card : ENNReal) * threshold) =
          (2 * (10 : ENNReal)⁻¹) *
            ((slabs.card : ENNReal) * root) * sourceVolume := by
        simp only [threshold, pureWZ2Node05V4RichHeavySlabThreshold,
          sourceVolume, root]
        ring
      _ ≤ (2 * (10 : ENNReal)⁻¹) * 5 * sourceVolume := by gcongr
      _ = sourceVolume := by rw [hcoefficient, one_mul]
  have htotal :
      (∑ heightIndex ∈ slabs,
        volume (pullback.standardSqrtSlabSourceRegion heightIndex.1)) =
          sourceVolume := by
    simpa [slabs, sourceVolume] using
      pullback.sum_standardSqrtSlabSourceRegion_volume_subtype
  have hhalf := finset_good_weighted_supply_retains_half slabs
    (fun heightIndex =>
      volume (pullback.standardSqrtSlabSourceRegion heightIndex.1))
    1 threshold pullback.heavySlabThreshold_ne_top (by simpa [htotal] using hsmall)
  simp only [mul_one] at hhalf
  rw [htotal] at hhalf
  simpa [slabs, sourceVolume, threshold, pureWZ2Node05V4RichHeavySlabs] using hhalf

theorem heavySlabs_nonempty :
    (pureWZ2Node05V4RichHeavySlabs pullback).Nonempty := by
  have hselected : pullback.selectedCells.Nonempty := by
    rcases twoScale.second.terminal.packetCells_nonempty with ⟨edge, hedge⟩
    rw [twoScale.second.terminal.packetCells_eq] at hedge
    have hactive := (Finset.mem_product.mp (Finset.mem_filter.mp hedge).1).2
    rw [pullback.selectedCells_eq]
    exact ⟨edge.2, hactive⟩
  have hsourcePos : 0 < volume pullback.shading.union := by
    rw [pullback.volume_eq]
    exact ENNReal.mul_pos
      (by exact_mod_cast hselected.card_pos.ne')
      pullback.firstPostBalanced.cellMass_pos.ne'
  have hretained := pullback.heavySlabs_retains_half_volume
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hretained
  simp only [Finset.sum_empty, mul_zero] at hretained
  exact (not_le_of_gt hsourcePos) hretained

theorem heavySlabs_retains_mass :
    pullback.shading.mass ≤
      2 * (twoScale.first.fourDegreeReceipts.regularity : ENNReal) *
        ∑ heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback,
          (pullback.standardSqrtSlabSourceShading heightIndex.1).mass := by
  let floor : ENNReal :=
    (twoScale.first.fourDegreeReceipts.fineDegreeFloor *
      twoScale.first.fourDegreeReceipts.muFine : ℕ)
  let regularity : ENNReal := twoScale.first.fourDegreeReceipts.regularity
  have hsourceUpper : pullback.shading.mass ≤
      (regularity * floor) * volume pullback.shading.union := by
    apply mass_le_of_pointMultiplicity_le
    intro point hpoint
    have hband := pullback.source_constantMultiplicity point hpoint
    have hcast :
        (pullback.shading.pointMultiplicity point : ENNReal) ≤
          ((twoScale.first.fourDegreeReceipts.regularity *
            twoScale.first.fourDegreeReceipts.fineDegreeFloor) *
              twoScale.first.fourDegreeReceipts.muFine : ℕ) := by
      exact_mod_cast hband.2
    simpa [regularity, floor, Nat.cast_mul, mul_assoc] using hcast
  have hvolume := pullback.heavySlabs_retains_half_volume
  have hslabLower :
      floor * ∑ heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback,
          volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) ≤
        ∑ heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback,
          (pullback.standardSqrtSlabSourceShading heightIndex.1).mass := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun heightIndex _ => by
      simpa [floor] using
        pullback.standardSqrtSlabSourceShading_mass_lower heightIndex.1
  calc
    pullback.shading.mass ≤
        (regularity * floor) * volume pullback.shading.union := hsourceUpper
    _ ≤ (regularity * floor) *
        (2 * ∑ heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback,
          volume (pullback.standardSqrtSlabSourceRegion heightIndex.1)) := by
      gcongr
    _ = 2 * regularity *
        (floor * ∑ heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback,
          volume (pullback.standardSqrtSlabSourceRegion heightIndex.1)) := by ring
    _ ≤ 2 * regularity *
        ∑ heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback,
          (pullback.standardSqrtSlabSourceShading heightIndex.1).mass := by gcongr

end PureWZ2Node05V4RichTwoScaleCellPullbackData

/-- The paper-order global-grain neighborhood constructed on every source-
heavy standard slab. -/
structure PureWZ2Node05V4RichHeavySlabNeighborhoodFamily
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (neighborhoodLoss : ℝ) where
  block : ∀ heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback},
    PureWZ2PreCommonBinGlobalGrainNeighborhoodAtData
      pullback heightIndex.1 neighborhoodLoss

/-- The complete Theorem-5.2 tail on every source-heavy slab.  Every field is
indexed by the exact prescribed-slab neighborhood stored in `family`; no graph,
source cell, or complete-height witness is reselected. -/
structure PureWZ2Node05V4RichHeavySlabSaturatedTailFamily
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss neighborhoodLoss finalLoss eta : ℝ}
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
    (family : PureWZ2Node05V4RichHeavySlabNeighborhoodFamily
      pullback neighborhoodLoss)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (projection : PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss) where
  graphScale_le_one : ∀ heightIndex,
    (family.block heightIndex).neighborhood.saturatedGraphScale ≤ 1
  scheduled : ∀ heightIndex,
    PureWZ2Node05V4RichSaturatedScheduledTheorem52Data
      (eta := eta) (family.block heightIndex).neighborhood hbridge
        (graphScale_le_one heightIndex) projection
  sparse : ∀ heightIndex,
    PureWZ2Node05V4RichSaturatedSourceCellData (scheduled heightIndex)
  complete : ∀ heightIndex,
    PureWZ2Node05V4RichSaturatedCompleteHeightData (sparse heightIndex)

namespace PureWZ2Node05V4RichTwoScaleCellPullbackData

/-- Construct the exact prescribed-slab neighborhood independently at every
source-heavy slab, with one common family-free scalar budget. -/
theorem heavySlabNeighborhoodFamily
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss neighborhoodLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hbudget :
      pureWZ2PreCommonBinHeavySlabNeighborhoodCost
          sigma inputLoss delta rho *
        pureWZ2PreCommonBinRequiredCubeCount pullback neighborhoodLoss ≤
      volume pullback.shading.union) :
    Nonempty (PureWZ2Node05V4RichHeavySlabNeighborhoodFamily
      pullback neighborhoodLoss) := by
  have hblock : ∀ heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback},
      Nonempty (PureWZ2PreCommonBinGlobalGrainNeighborhoodAtData
        pullback heightIndex.1 neighborhoodLoss) := by
    intro heightIndex
    have hheavy := (Finset.mem_filter.mp heightIndex.property).2
    have hsourceSlab :
        volume pullback.shading.union * ENNReal.ofReal (Real.sqrt rho) ≤
          10 * volume
            (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) := by
      have hten : (10 : ENNReal) * 10⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      calc
        volume pullback.shading.union * ENNReal.ofReal (Real.sqrt rho) =
            1 * (volume pullback.shading.union *
              ENNReal.ofReal (Real.sqrt rho)) := by rw [one_mul]
        _ = (10 * (10 : ENNReal)⁻¹) *
            (volume pullback.shading.union *
              ENNReal.ofReal (Real.sqrt rho)) := by rw [hten]
        _ = 10 * ((10 : ENNReal)⁻¹ * volume pullback.shading.union *
              ENNReal.ofReal (Real.sqrt rho)) := by ring
        _ ≤ 10 * volume
            (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) :=
          mul_le_mul_right hheavy 10
    apply pullback.producePreCommonBinGlobalGrainNeighborhoodAt
      heightIndex.1 10 (by norm_num) (by norm_num) hsourceSlab hbridge
        neighborhoodLoss
    simpa [pureWZ2PreCommonBinHeavySlabNeighborhoodCost] using hbudget
  exact ⟨{ block := fun heightIndex => Classical.choice (hblock heightIndex) }⟩

/-- Construct every source-heavy prescribed-slab neighborhood directly from
the two-call cell-floor product.  The remaining hypothesis is a pre-runtime
scalar inequality; no runtime source-volume budget is exposed. -/
theorem heavySlabNeighborhoodFamilyOfCellFloorProduct
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss neighborhoodLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hpower :
      pureWZ2PreCommonBinHeavySlabNeighborhoodCost
            sigma inputLoss delta rho *
          pureWZ2PreCommonBinRequiredCubeCount pullback neighborhoodLoss *
          volume (wz1PaperGridCube rho (0, 0, 0)) ≤
        pureWZ2Node05V4RichP3CellFloorProduct twoScale) :
    Nonempty (PureWZ2Node05V4RichHeavySlabNeighborhoodFamily
      pullback neighborhoodLoss) := by
  exact pullback.heavySlabNeighborhoodFamily hbridge
    (pullback.heavySlabNeighborhood_budget_of_cellFloorProduct hpower)

/-- Production constructor for all paper-heavy slabs.  The exact parent count,
point density, two balanced-cell floors, and whole-refined-volume cancellation
are all discharged by the pre-runtime threshold on the same two-call witness. -/
theorem heavySlabNeighborhoodFamilyOfThreshold
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta stickyLoss sourceLossCeiling secondLossCeiling
      neighborhoodLoss scaleLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rhoRequested.1) twoScale)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (threshold :
      PureWZ2Node05V4RichSecondCallData.PureWZ2Node05V4RichNeighborhoodBudgetThreshold
      sigma sourceLossCeiling schedule.firstOutputLoss secondLossCeiling
        neighborhoodLoss scaleLoss)
    (hinputNonneg : 0 ≤ inputLoss)
    (hinputCeiling : inputLoss ≤ sourceLossCeiling)
    (hsecondCeiling : stickyLoss ≤ secondLossCeiling)
    (hdeltaSmall : delta ≤ threshold.delta₀)
    (hrhoSmall : rhoRequested.1 ≤ 1 / 12)
    (hrhoThreshold : rhoRequested.1 ≤ threshold.rho₀)
    (hrhoPower : rhoRequested.1 ≤ Real.rpow delta scaleLoss) :
    Nonempty (PureWZ2Node05V4RichHeavySlabNeighborhoodFamily
      pullback neighborhoodLoss) := by
  apply pullback.heavySlabNeighborhoodFamily hbridge
  exact twoScale.heavySlabNeighborhood_budget threshold pullback
    hinputNonneg hinputCeiling hsecondCeiling hdeltaSmall hrhoSmall
      hrhoThreshold hrhoPower

end PureWZ2Node05V4RichTwoScaleCellPullbackData

namespace PureWZ2Node05V4RichHeavySlabNeighborhoodFamily

/-- Run the saturated Theorem-5.2 graph, source-cell provenance, and complete
source-height lift on every exact neighborhood in a heavy-slab family. -/
theorem saturatedTail
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss neighborhoodLoss finalLoss eta
      sourceLossCeiling firstLossCeiling secondLossCeiling scaleLoss : ℝ}
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
    (family : PureWZ2Node05V4RichHeavySlabNeighborhoodFamily
      pullback neighborhoodLoss)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (projection : PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss)
    (analytic : PureWZ2SourceHorizontalAnalyticThreshold projection.theoremEta)
    (threshold : PureWZ2Node05V4RichSaturatedGraphThreshold
      sigma sourceLossCeiling firstLossCeiling secondLossCeiling eta
        neighborhoodLoss analytic.budget.volumeLoss
        analytic.budget.constantLoss projection.sourceCostLossCeiling
        scaleLoss)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb : 256 * rho + 2 * Real.sqrt rho ≤ 16 * Real.sqrt rho)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hcertificateOne : 4 * rhoRequested.1 ≤ 1)
    (hPlanarSmall : 32 * Real.rpow (4 * rhoRequested.1) eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rhoRequested.1) ≤ 1)
    (habsorb :
      Real.rpow (4 * rhoRequested.1) (1 - 4 * eta / sigma) ≤
        Real.sqrt (4 * rhoRequested.1) / 14)
    (hfinal : 0 < finalLoss) (hfinalOne : finalLoss < 1)
    (hfinalSigma : finalLoss / 2 < sigma)
    (hinputNonneg : 0 ≤ inputLoss)
    (hinputCeiling : inputLoss ≤ sourceLossCeiling)
    (hfirstCeiling : schedule.firstOutputLoss ≤ firstLossCeiling)
    (hsecondCeiling : stickyLoss ≤ secondLossCeiling)
    (hdeltaSmall : delta ≤ threshold.delta₀)
    (hrhoSmall : rho ≤ threshold.rho₀)
    (hrhoPower : rho ≤ Real.rpow delta scaleLoss)
    (hgraphAnalytic : 256 * rho ≤ analytic.rho0)
    (hrhoProjection : rho ≤ projection.rho₀)
    (hCOne : (1 : ENNReal) ≤
      160 * Kakeya.realRpowENN delta (-inputLoss)) :
    Nonempty (PureWZ2Node05V4RichHeavySlabSaturatedTailFamily
      (eta := eta) family hbridge projection) := by
  let graphOne : ∀ heightIndex,
      (family.block heightIndex).neighborhood.saturatedGraphScale ≤ 1 := by
    intro heightIndex
    simpa [PureWZ2PreCommonBinGlobalGrainNeighborhoodData.saturatedGraphScale]
      using hgraphOne
  have hscheduled : ∀ heightIndex, Nonempty
      (PureWZ2Node05V4RichSaturatedScheduledTheorem52Data
        (eta := eta) (family.block heightIndex).neighborhood hbridge
          (graphOne heightIndex) projection) := by
    intro heightIndex
    let block := family.block heightIndex
    let neighborhood := block.neighborhood
    have hthresholdAt : ∃ thresholdAt :
        PureWZ2Node05V4RichSaturatedGraphThreshold
          sigma sourceLossCeiling firstLossCeiling secondLossCeiling eta
            neighborhood.neighborhoodLoss analytic.budget.volumeLoss
            analytic.budget.constantLoss projection.sourceCostLossCeiling
            scaleLoss,
        thresholdAt.delta₀ = threshold.delta₀ ∧
          thresholdAt.rho₀ = threshold.rho₀ := by
      rw [block.neighborhoodLoss_eq]
      exact ⟨threshold, rfl, rfl⟩
    rcases hthresholdAt with ⟨thresholdAt, hdeltaCutoff, hrhoCutoff⟩
    have hdeltaSmallAt : delta ≤ thresholdAt.delta₀ := by
      rw [hdeltaCutoff]
      exact hdeltaSmall
    have hrhoSmallAt : rho ≤ thresholdAt.rho₀ := by
      rw [hrhoCutoff]
      exact hrhoSmall
    apply neighborhood.saturatedTheorem52OfThresholds hbridge projection analytic
      thresholdAt (graphOne heightIndex)
    · simpa [neighborhood,
        PureWZ2PreCommonBinGlobalGrainNeighborhoodData.saturatedGraphScale]
        using hheightAbsorb
    · exact hsigma
    · exact hsigmaOne
    · exact heta
    · exact hetaSigma
    · exact hcertificateOne
    · exact hPlanarSmall
    · exact hrootSmall20
    · exact habsorb
    · exact hfinal
    · exact hfinalOne
    · exact hfinalSigma
    · exact hinputNonneg
    · exact hinputCeiling
    · exact hfirstCeiling
    · exact hsecondCeiling
    · exact hdeltaSmallAt
    · exact hrhoSmallAt
    · exact hrhoPower
    · simpa [neighborhood,
        PureWZ2PreCommonBinGlobalGrainNeighborhoodData.graphScale,
        PureWZ2PreCommonBinGlobalGrainNeighborhoodData.saturatedGraphScale]
        using hgraphAnalytic
    · exact hrhoProjection
    · exact hCOne
  let scheduled : ∀ heightIndex,
      PureWZ2Node05V4RichSaturatedScheduledTheorem52Data
        (eta := eta) (family.block heightIndex).neighborhood hbridge
          (graphOne heightIndex) projection := fun heightIndex =>
    Classical.choice (hscheduled heightIndex)
  have hsparse : ∀ heightIndex, Nonempty
      (PureWZ2Node05V4RichSaturatedSourceCellData
        (scheduled heightIndex)) := fun heightIndex =>
    (scheduled heightIndex).sourceCells
  let sparse : ∀ heightIndex,
      PureWZ2Node05V4RichSaturatedSourceCellData
        (scheduled heightIndex) := fun heightIndex =>
    Classical.choice (hsparse heightIndex)
  have hcomplete : ∀ heightIndex, Nonempty
      (PureWZ2Node05V4RichSaturatedCompleteHeightData
        (sparse heightIndex)) := fun heightIndex =>
    (scheduled heightIndex).completeSourceHeights (sparse heightIndex)
  exact ⟨{
    graphScale_le_one := graphOne
    scheduled := scheduled
    sparse := sparse
    complete := fun heightIndex => Classical.choice (hcomplete heightIndex)
  }⟩

end PureWZ2Node05V4RichHeavySlabNeighborhoodFamily

end Kakeya.Assouad

end
