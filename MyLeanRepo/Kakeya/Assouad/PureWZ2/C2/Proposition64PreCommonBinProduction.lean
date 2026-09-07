import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64PreCommonBinGlobalGrainNeighborhoodProducer

/-!
# Direct-rich P3 pre-common-bin production

This module turns the two terminal rich V4 balanced-cell floors into the two
division-free budgets consumed by the paper-order global-neighborhood and
local-grain constructors.  Runtime geometry is not reselected here.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The product of the exact power floors retained by the two dependent rich
Proposition 6.2 calls. -/
def pureWZ2Node05V4RichP3CellFloorProduct
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    (twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested) : ENNReal :=
  (Kakeya.realRpowENN rhoRequested.1 3 *
      Kakeya.realRpowENN (delta / rhoRequested.1)
        (sigma + 2 * twoScale.first.rich.terminalLoss)) *
    (Kakeya.realRpowENN sqrtRequested.1 3 *
      Kakeya.realRpowENN (rhoRequested.1 / sqrtRequested.1)
        (sigma + 2 * twoScale.second.terminalLoss))

namespace PureWZ2Node05V4RichTwoScaleCellPullbackData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta rho : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
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

/-- Paper-sized global-neighborhood budget from the whole second refined
union, not from one second balanced cell, with the slab-to-slice factor kept
explicit.  This is the sharp cross-stage quantity in WZ Lemma 5.4: the second
refined union supplies the `rho^(sigma + loss)` factor, while the first
balanced cell pulls it back to the final source. -/
theorem globalNeighborhood_budget_withSlabFactor_of_secondRefinedVolume
    (slabFactor : ENNReal)
    (hrhoSmall : rhoRequested.1 ≤ 1 / 12)
    {neighborhoodLoss : ℝ}
    (hpower :
      (twoScale.first.fourDegreeReceipts.regularity : ENNReal) *
          ((pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
                slabFactor sigma inputLoss delta rho *
              pureWZ2PreCommonBinRequiredCubeCount
                pullback neighborhoodLoss) *
            volume (wz1PaperGridCube rho (0, 0, 0))) ≤
        (wz2PaperPureRefinementFraction rhoRequested.1 61 *
            Kakeya.realRpowENN rhoRequested.1
              (sigma + 2 * schedule.firstOutputLoss)) *
          (Kakeya.realRpowENN rhoRequested.1 3 *
            Kakeya.realRpowENN (delta / rhoRequested.1)
              (sigma + 2 * twoScale.first.rich.terminalLoss))) :
    pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
          slabFactor sigma inputLoss delta rho *
        pureWZ2PreCommonBinRequiredCubeCount pullback neighborhoodLoss ≤
      volume pullback.shading.union := by
  let regularity : ENNReal :=
    twoScale.first.fourDegreeReceipts.regularity
  let cubeVolume := volume (wz1PaperGridCube rho (0, 0, 0))
  let required :=
    pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
        slabFactor sigma inputLoss delta rho *
      pureWZ2PreCommonBinRequiredCubeCount pullback neighborhoodLoss
  let secondFloor :=
    wz2PaperPureRefinementFraction rhoRequested.1 61 *
      Kakeya.realRpowENN rhoRequested.1
        (sigma + 2 * schedule.firstOutputLoss)
  let firstCellFloor :=
    Kakeya.realRpowENN rhoRequested.1 3 *
      Kakeya.realRpowENN (delta / rhoRequested.1)
        (sigma + 2 * twoScale.first.rich.terminalLoss)
  have hsecond :
      secondFloor ≤ regularity *
        volume twoScale.secondRefinedFineShading.union := by
    simpa only [secondFloor, regularity] using
      twoScale.second_refined_volume_lower hrhoSmall
  have hfirst :
      firstCellFloor ≤ pullback.firstPostBalanced.cellMass := by
    dsimp only [firstCellFloor]
    rw [pullback.firstPost_cellMass_eq]
    exact twoScale.first_cellMass_power_lower
  have hscaled :
      regularity * (required * cubeVolume) ≤
        regularity * (volume pullback.shading.union * cubeVolume) := by
    calc
      regularity * (required * cubeVolume) ≤
          secondFloor * firstCellFloor := by
        simpa only [regularity, required, cubeVolume, secondFloor,
          firstCellFloor] using hpower
      _ ≤ (regularity * volume twoScale.secondRefinedFineShading.union) *
          pullback.firstPostBalanced.cellMass :=
        mul_le_mul hsecond hfirst (by positivity) (by positivity)
      _ = regularity *
          (volume pullback.shading.union * cubeVolume) := by
        rw [pullback.source_volume_mul_rho_cube_eq]
        ring
  have hregularityZero : regularity ≠ 0 := by
    dsimp only [regularity]
    exact_mod_cast twoScale.first.fourDegreeReceipts.regularity_pos.ne'
  have hregularityTop : regularity ≠ ⊤ := by
    simp [regularity]
  have hcubePos : 0 < cubeVolume := by
    dsimp only [cubeVolume]
    have hrho : 0 < rho := by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos
    exact wz1PaperGridCube_volume_pos hrho (0, 0, 0)
  have hcubeTop : cubeVolume ≠ ⊤ := by
    dsimp only [cubeVolume]
    have hrho : 0 < rho := by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_ne_top
  have hwithoutRegularity :
      required * cubeVolume ≤
        volume pullback.shading.union * cubeVolume :=
    (ENNReal.mul_le_mul_iff_right hregularityZero hregularityTop).mp hscaled
  exact (ENNReal.mul_le_mul_iff_left hcubePos.ne' hcubeTop).mp
    hwithoutRegularity

/-- Maximal-slab factor-`5` specialization retained for the existing
single-neighborhood producer. -/
theorem globalNeighborhood_budget_of_secondRefinedVolume
    (hrhoSmall : rhoRequested.1 ≤ 1 / 12)
    {neighborhoodLoss : ℝ}
    (hpower :
      (twoScale.first.fourDegreeReceipts.regularity : ENNReal) *
          ((pureWZ2PreCommonBinGlobalNeighborhoodCost
                sigma inputLoss delta rho *
              pureWZ2PreCommonBinRequiredCubeCount
                pullback neighborhoodLoss) *
            volume (wz1PaperGridCube rho (0, 0, 0))) ≤
        (wz2PaperPureRefinementFraction rhoRequested.1 61 *
            Kakeya.realRpowENN rhoRequested.1
              (sigma + 2 * schedule.firstOutputLoss)) *
          (Kakeya.realRpowENN rhoRequested.1 3 *
            Kakeya.realRpowENN (delta / rhoRequested.1)
              (sigma + 2 * twoScale.first.rich.terminalLoss))) :
    pureWZ2PreCommonBinGlobalNeighborhoodCost
          sigma inputLoss delta rho *
        pureWZ2PreCommonBinRequiredCubeCount pullback neighborhoodLoss ≤
      volume pullback.shading.union := by
  apply pullback.globalNeighborhood_budget_withSlabFactor_of_secondRefinedVolume
    5 hrhoSmall
  simpa only [pureWZ2PreCommonBinGlobalNeighborhoodCost] using hpower

/-- Source-heavy factor-`10` specialization.  Unlike the legacy
`heavySlabNeighborhood_budget_of_cellFloorProduct`, this uses the full second
refined volume and therefore retains the number of active second-cover cells
needed by the paper's line-neighborhood construction. -/
theorem heavySlabNeighborhood_budget_of_secondRefinedVolume
    (hrhoSmall : rhoRequested.1 ≤ 1 / 12)
    {neighborhoodLoss : ℝ}
    (hpower :
      (twoScale.first.fourDegreeReceipts.regularity : ENNReal) *
          ((pureWZ2PreCommonBinHeavySlabNeighborhoodCost
                sigma inputLoss delta rho *
              pureWZ2PreCommonBinRequiredCubeCount
                pullback neighborhoodLoss) *
            volume (wz1PaperGridCube rho (0, 0, 0))) ≤
        (wz2PaperPureRefinementFraction rhoRequested.1 61 *
            Kakeya.realRpowENN rhoRequested.1
              (sigma + 2 * schedule.firstOutputLoss)) *
          (Kakeya.realRpowENN rhoRequested.1 3 *
            Kakeya.realRpowENN (delta / rhoRequested.1)
              (sigma + 2 * twoScale.first.rich.terminalLoss))) :
    pureWZ2PreCommonBinHeavySlabNeighborhoodCost
          sigma inputLoss delta rho *
        pureWZ2PreCommonBinRequiredCubeCount pullback neighborhoodLoss ≤
      volume pullback.shading.union := by
  apply pullback.globalNeighborhood_budget_withSlabFactor_of_secondRefinedVolume
    10 hrhoSmall
  simpa only [pureWZ2PreCommonBinHeavySlabNeighborhoodCost] using hpower

/-- Cancel the positive side-`rho` cube volume in the exact pullback identity,
with an arbitrary preselected finite slab-to-slice factor. -/
theorem globalNeighborhood_budget_withSlabFactor_of_cellFloorProduct
    (slabFactor : ENNReal) {neighborhoodLoss : ℝ}
    (hpower :
      pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor slabFactor
            sigma inputLoss delta rho *
          pureWZ2PreCommonBinRequiredCubeCount pullback neighborhoodLoss *
          volume (wz1PaperGridCube rho (0, 0, 0)) ≤
        pureWZ2Node05V4RichP3CellFloorProduct twoScale) :
    pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor slabFactor
          sigma inputLoss delta rho *
        pureWZ2PreCommonBinRequiredCubeCount pullback neighborhoodLoss ≤
      volume pullback.shading.union := by
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  let cubeVolume := volume (wz1PaperGridCube rho (0, 0, 0))
  have hcubePos : 0 < cubeVolume :=
    wz1PaperGridCube_volume_pos hrho (0, 0, 0)
  have hcubeTop : cubeVolume ≠ ⊤ := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_ne_top
  apply (ENNReal.mul_le_mul_iff_right hcubePos.ne' hcubeTop).mp
  calc
    cubeVolume *
        (pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor slabFactor
          sigma inputLoss delta rho *
        pureWZ2PreCommonBinRequiredCubeCount pullback neighborhoodLoss) ≤
      pureWZ2Node05V4RichP3CellFloorProduct twoScale := by
        simpa only [cubeVolume, mul_comm, mul_left_comm, mul_assoc] using hpower
    _ ≤ cubeVolume * volume pullback.shading.union := by
      have h :=
        pullback.rich_cellMass_power_product_le_source_volume_mul_cube
      simpa only [cubeVolume, pureWZ2Node05V4RichP3CellFloorProduct,
        mul_comm] using h

/-- Maximal-slab factor-`5` specialization retained for the existing
single-neighborhood producer. -/
theorem globalNeighborhood_budget_of_cellFloorProduct
    {neighborhoodLoss : ℝ}
    (hpower :
      pureWZ2PreCommonBinGlobalNeighborhoodCost
            sigma inputLoss delta rho *
          pureWZ2PreCommonBinRequiredCubeCount pullback neighborhoodLoss *
          volume (wz1PaperGridCube rho (0, 0, 0)) ≤
        pureWZ2Node05V4RichP3CellFloorProduct twoScale) :
    pureWZ2PreCommonBinGlobalNeighborhoodCost
          sigma inputLoss delta rho *
        pureWZ2PreCommonBinRequiredCubeCount pullback neighborhoodLoss ≤
      volume pullback.shading.union := by
  apply pullback.globalNeighborhood_budget_withSlabFactor_of_cellFloorProduct 5
  simpa only [pureWZ2PreCommonBinGlobalNeighborhoodCost] using hpower

/-- Source-heavy factor-`10` specialization used to construct all retained
slab neighborhoods with one common budget. -/
theorem heavySlabNeighborhood_budget_of_cellFloorProduct
    {neighborhoodLoss : ℝ}
    (hpower :
      pureWZ2PreCommonBinHeavySlabNeighborhoodCost
            sigma inputLoss delta rho *
          pureWZ2PreCommonBinRequiredCubeCount pullback neighborhoodLoss *
          volume (wz1PaperGridCube rho (0, 0, 0)) ≤
        pureWZ2Node05V4RichP3CellFloorProduct twoScale) :
    pureWZ2PreCommonBinHeavySlabNeighborhoodCost
          sigma inputLoss delta rho *
        pureWZ2PreCommonBinRequiredCubeCount pullback neighborhoodLoss ≤
      volume pullback.shading.union := by
  apply pullback.globalNeighborhood_budget_withSlabFactor_of_cellFloorProduct 10
  simpa only [pureWZ2PreCommonBinHeavySlabNeighborhoodCost] using hpower

/-- The same two rich cell floors discharge the almost-full local-grain
budget once its scalar cost has been absorbed before runtime. -/
theorem localGrain_budget_of_cellFloorProduct
    {eta : ℝ}
    (hpower :
      Kakeya.realRpowENN rho (2 + 2 * eta) *
          (pureWZ2PreCommonBinLocalProjectionCost
            delta rho sigma inputLoss *
            volume (wz1PaperGridCube rho (0, 0, 0))) ≤
        pureWZ2Node05V4RichP3CellFloorProduct twoScale) :
    Kakeya.realRpowENN rho (2 + 2 * eta) *
          (pureWZ2PreCommonBinLocalProjectionCost
            delta rho sigma inputLoss *
            volume (wz1PaperGridCube rho (0, 0, 0))) ≤
      twoScale.second.terminal.balanced.cellMass *
        pullback.firstPostBalanced.cellMass := by
  calc
    _ ≤ pureWZ2Node05V4RichP3CellFloorProduct twoScale := hpower
    _ ≤ pullback.firstPostBalanced.cellMass *
          twoScale.secondBalancedCover.cellMass := by
      dsimp only [pureWZ2Node05V4RichP3CellFloorProduct]
      gcongr
      · rw [pullback.firstPost_cellMass_eq]
        exact twoScale.first_cellMass_power_lower
      · exact twoScale.second_cellMass_power_lower
    _ = twoScale.second.terminal.balanced.cellMass *
          pullback.firstPostBalanced.cellMass := by ring

/-- One paper-order P3 prefix: select the global-grain neighborhood and then
construct its almost-full local grains and auxiliary graph on the same source. -/
theorem producePreCommonBinLocalGrainFamily
    (hbridge : PureWZ2PaperADBridgeStatement)
    (neighborhoodLoss eta : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hconstantPower :
      10 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN rho (-eta))
    (hPlanarSmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt rho ≤ 1)
    (habsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤
        Real.sqrt rho / 14)
    (hglobalPower :
      pureWZ2PreCommonBinGlobalNeighborhoodCost
            sigma inputLoss delta rho *
          pureWZ2PreCommonBinRequiredCubeCount pullback neighborhoodLoss *
          volume (wz1PaperGridCube rho (0, 0, 0)) ≤
        pureWZ2Node05V4RichP3CellFloorProduct twoScale)
    (hlocalPower :
      Kakeya.realRpowENN rho (2 + 2 * eta) *
          (pureWZ2PreCommonBinLocalProjectionCost
            delta rho sigma inputLoss *
            volume (wz1PaperGridCube rho (0, 0, 0))) ≤
        pureWZ2Node05V4RichP3CellFloorProduct twoScale) :
    Nonempty
      (Σ neighborhood :
          PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback,
        PureWZ2PreCommonBinLocalGrainFamilyData
          (eta := eta) neighborhood) := by
  rcases pullback.producePreCommonBinGlobalGrainNeighborhood
      hbridge neighborhoodLoss
      (pullback.globalNeighborhood_budget_of_cellFloorProduct hglobalPower) with
    ⟨neighborhood⟩
  rcases neighborhood.localGrainFamily hbridge hsigma hsigmaOne heta hetaSigma
      hconstantPower hPlanarSmall hrootSmall20 habsorb
      (pullback.localGrain_budget_of_cellFloorProduct hlocalPower) with
    ⟨localGrains⟩
  exact ⟨⟨neighborhood, localGrains⟩⟩

end PureWZ2Node05V4RichTwoScaleCellPullbackData

end Kakeya.Assouad

end
