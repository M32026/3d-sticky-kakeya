import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyInternalPartitioningCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyCallerNearbyAssembly
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDirectGeometricBalanced
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperExactBalancingMassRetention

/-!
# Fixed-origin balancing on the same-family caller pullback

Run the closed whole-cell balancing pipeline on the internal cover derived
from the public caller cover.  The final fine shading, final coarse shading,
and public balanced-cover certificate all use the unchanged selected fine and
caller families.  The package also records the complete explicit finite loss
from the input selected shading to the final balanced shading.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The explicit finite loss paid by the closed direct balancing pipeline. -/
def pureWZ2SameFamilyFixedOriginBalancingLoss
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (balanced :
      WZ2PaperDirectBalancedData
        cover shading hdelta hrho 14) : ENNReal :=
  (((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) *
      (16 *
        ((Nat.log 2
            (∑ coarseCell ∈
              balanced.rebalancing.boundaryPruning.coarseCells,
              (balanced.rebalancing.boundaryPruning
                |>.availableFineCells coarseCell).card) + 1 : ℕ) :
          ENNReal))) *
    wz2PaperFinalBalancedCoverLoss balanced.finalData.producer

structure PureWZ2SameFamilyFixedOriginBalancingData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (support : PureWZ2PositiveCallerSupportData quotient)
    (coordinateCount : ℕ)
    (regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount)
    (merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized)
    (scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled)
    (scaleSeparation : 18 * delta ≤ callerRequested.1) where
  balanced :
    WZ2PaperDirectBalancedData
      (sameFamily.pullback.internalPartitioningCover scaleSeparation)
      sameFamily.pullback.selectedFineShading
      actualNearby.scaleData.delta_pos
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
      14
  publicBalanced :
    PureWZ2BalancedCoverData
      sameFamily.pullback.section6Cover
      balanced.finalData.producer.coarseBand.selectedFineShading
      balanced.finalData.producer.coarseBand.selectedCoarseShading
  finalFine_subshading :
    ∀ index,
      balanced.finalData.producer.coarseBand.selectedFineShading.carrier
          index ⊆
        sameFamily.pullback.selectedFineShading.carrier index
  finalFine_cubical :
    WZ1PaperIsCubicalShading
      balanced.finalData.producer.coarseBand.selectedFineShading
  selected_mass_retention :
    sameFamily.pullback.selectedFineShading.mass ≤
      pureWZ2SameFamilyFixedOriginBalancingLoss balanced *
        balanced.finalData.producer.coarseBand.selectedFineShading.mass
  source_mass_retention :
    shading.mass ≤
      (((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          pureWZ2CompleteParentRegularizationLoss
            actualNearby.scaleData.coarse.card coordinateCount *
          sameFamily.retentionConstant) *
        pureWZ2SameFamilyFixedOriginBalancingLoss balanced) *
        balanced.finalData.producer.coarseBand.selectedFineShading.mass

/--
Produce the fixed-origin balanced shading from the explicit geometric
absorption input.  No second tube-family selection occurs.
-/
theorem pureWZ2_same_family_fixed_origin_balancing
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (support : PureWZ2PositiveCallerSupportData quotient)
    (coordinateCount : ℕ)
    (regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount)
    (merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized)
    (scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled)
    (scaleSeparation : 18 * delta ≤ callerRequested.1)
    (input :
      WZ2PaperDirectGeometricInputData
        (sameFamily.pullback.internalPartitioningCover scaleSeparation)
        sameFamily.pullback.selectedFineShading
        actualNearby.scaleData.delta_pos
        (actualNearby.scaleData.delta_pos.trans_le
          callerRequested.2.1)) :
    Nonempty
      (PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation) := by
  let internalCover :=
    sameFamily.pullback.internalPartitioningCover scaleSeparation
  let callerPos : 0 < callerRequested.1 :=
    actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1
  let balanced :
      WZ2PaperDirectBalancedData
        internalCover sameFamily.pullback.selectedFineShading
        actualNearby.scaleData.delta_pos callerPos 14 :=
    Classical.choice <|
      wz2_paper_direct_balanced_from_geometric_input input
  let producer := balanced.finalData.producer
  let finalFine := producer.coarseBand.selectedFineShading
  let finalCoarse := producer.coarseBand.selectedCoarseShading
  let historicalBalanced := producer.finalCover.balanced
  have publicBalanced :
      PureWZ2BalancedCoverData
        sameFamily.pullback.section6Cover finalFine finalCoarse := by
    exact
      {
        point_compatibility := by
          intro source parent hcovered point hpoint
          have hparent :
              parent = sameFamily.pullback.callerCover.parent source :=
            sameFamily.pullback.callerCover.parent_unique
              source parent hcovered
          subst parent
          exact historicalBalanced.point_compatibility source point hpoint
        coarse_cubical := historicalBalanced.coarse_cubical
        activeCells := historicalBalanced.activeCells
        coarse_union_eq := historicalBalanced.coarse_union_eq
        cellMass := historicalBalanced.cellMass
        cellMass_pos := historicalBalanced.cellMass_pos
        cellMass_ne_top := historicalBalanced.cellMass_ne_top
        fine_cell_mass := historicalBalanced.fine_cell_mass
      }
  have finalFineSubshading :
      ∀ index,
        finalFine.carrier index ⊆
          sameFamily.pullback.selectedFineShading.carrier index := by
    intro index
    have hFinal :=
      balanced.finalData.finalRefinement.subshading index
    rw [
      balanced.rebalancing.cropPruning.croppedBalancing_refined_eq
    ] at hFinal
    exact
      hFinal
        |>.trans
          (balanced.rebalancing.cropPruning.refined_subshading index)
        |>.trans
          (balanced.rebalancing.initialBalancing.refined_subshading index)
        |>.trans
          (balanced.rebalancing.boundaryPruning.pruned_subshading index)
        |>.trans
          (by
            rw [balanced.bandData.band_eq]
            exact
              wz1PaperDyadicBandSubshading_isSubshading
                sameFamily.pullback.selectedFineShading
                balanced.bandData.level index)
  have finalFineCubical :
      WZ1PaperIsCubicalShading finalFine :=
    producer.coarseBand.selectedFine_cubical
  let fineLog : ENNReal :=
    ((Nat.log 2 sameFamily.pullback.selectedFine.family.card + 1 : ℕ) :
      ENNReal)
  let availableLog : ENNReal :=
    ((Nat.log 2
        (∑ coarseCell ∈
          balanced.rebalancing.boundaryPruning.coarseCells,
          (balanced.rebalancing.boundaryPruning
            |>.availableFineCells coarseCell).card) + 1 : ℕ) :
      ENNReal)
  have fineLogZero : fineLog ≠ 0 := by
    dsimp only [fineLog]
    positivity
  have fineLogTop : fineLog ≠ ⊤ := by
    dsimp only [fineLog]
    simp
  have sourceToBand :
      sameFamily.pullback.selectedFineShading.mass ≤
        fineLog * balanced.bandData.band.mass := by
    have h := balanced.bandData.band_mass_retention
    rw [ENNReal.div_le_iff fineLogZero fineLogTop] at h
    simpa [fineLog, mul_comm] using h
  let crossingMass : ENNReal :=
    ∑ index : Fin sameFamily.pullback.selectedFine.family.card,
      volume
        (balanced.bandData.band.carrier index ∩
          balanced.rebalancing.boundaryPruning.crossingRegion)
  have crossingHalf :
      2 * crossingMass < balanced.bandData.band.mass := by
    dsimp only [crossingMass]
    rw [balanced.rebalancing.boundaryPruning.crossingRegion_eq_source]
    exact input.geometric.crossing_absorption balanced.bandData
  have bandToInitial :
      balanced.bandData.band.mass ≤
        (8 * availableLog) *
          balanced.rebalancing.initialBalancing.refined.mass := by
    simpa [availableLog] using
      wz2_paper_direct_exact_balancing_scaled_floor
        actualNearby.scaleData.delta_pos balanced.bandData
        balanced.rebalancing.boundaryPruning
        balanced.rebalancing.initialBalancing crossingHalf
  let cropMass : ENNReal :=
    ∑ index : Fin sameFamily.pullback.selectedFine.family.card,
      volume
        (balanced.rebalancing.initialBalancing.refined.carrier index ∩
          wz2PaperCropBoundaryRegion callerRequested.1)
  have cropHalf :
      2 * cropMass <
        balanced.rebalancing.initialBalancing.refined.mass := by
    dsimp only [cropMass]
    exact
      input.geometric.crop_absorption balanced.bandData
        balanced.rebalancing.boundaryPruning
        balanced.rebalancing.initialBalancing
  have cropFinite : cropMass ≠ ⊤ := by
    apply ne_top_of_lt
    calc
      cropMass ≤ 2 * cropMass := by
        exact le_mul_of_one_le_left' (by norm_num)
      _ < balanced.rebalancing.initialBalancing.refined.mass := cropHalf
  have cropLtRefined :
      cropMass < balanced.rebalancing.cropPruning.refined.mass := by
    apply (ENNReal.add_lt_add_iff_right cropFinite).mp
    calc
      cropMass + cropMass = 2 * cropMass := by ring
      _ < balanced.rebalancing.initialBalancing.refined.mass := cropHalf
      _ ≤
          balanced.rebalancing.cropPruning.refined.mass +
            cropMass := by
        simpa [cropMass, add_comm] using
          balanced.rebalancing.cropPruning.source_mass_le_boundary
  have initialToCrop :
      balanced.rebalancing.initialBalancing.refined.mass ≤
        2 * balanced.rebalancing.cropPruning.refined.mass := by
    calc
      balanced.rebalancing.initialBalancing.refined.mass ≤
          balanced.rebalancing.cropPruning.refined.mass +
            cropMass := by
        simpa [cropMass] using
          balanced.rebalancing.cropPruning.source_mass_le_boundary
      _ ≤
          balanced.rebalancing.cropPruning.refined.mass +
            balanced.rebalancing.cropPruning.refined.mass := by
        gcongr
      _ = 2 * balanced.rebalancing.cropPruning.refined.mass := by ring
  have cropMassEq :
      balanced.rebalancing.cropPruning.refined.mass =
        balanced.rebalancing.cropPruning.croppedBalancing.refined.mass :=
    congrArg Kakeya.Streamlined.Shading.mass
      balanced.rebalancing.cropPruning.croppedBalancing_refined_eq.symm
  have selectedRetention :
      sameFamily.pullback.selectedFineShading.mass ≤
        pureWZ2SameFamilyFixedOriginBalancingLoss balanced *
          finalFine.mass := by
    calc
      sameFamily.pullback.selectedFineShading.mass ≤
          fineLog * balanced.bandData.band.mass := sourceToBand
      _ ≤
          fineLog *
            ((8 * availableLog) *
              balanced.rebalancing.initialBalancing.refined.mass) := by
        gcongr
      _ ≤
          fineLog *
            ((8 * availableLog) *
              (2 * balanced.rebalancing.cropPruning.refined.mass)) := by
        gcongr
      _ =
          (fineLog * (16 * availableLog)) *
            balanced.rebalancing.cropPruning.refined.mass := by ring
      _ =
          (fineLog * (16 * availableLog)) *
            balanced.rebalancing.cropPruning.croppedBalancing.refined.mass := by
        rw [cropMassEq]
      _ ≤
          (fineLog * (16 * availableLog)) *
            (wz2PaperFinalBalancedCoverLoss producer *
              finalFine.mass) := by
        gcongr
        exact balanced.finalData.finalRefinement.source_mass_le
      _ =
          pureWZ2SameFamilyFixedOriginBalancingLoss balanced *
            finalFine.mass := by
        simp only [pureWZ2SameFamilyFixedOriginBalancingLoss]
        ring
  have sourceRetention :
      shading.mass ≤
        (((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            pureWZ2CompleteParentRegularizationLoss
              actualNearby.scaleData.coarse.card coordinateCount *
            sameFamily.retentionConstant) *
          pureWZ2SameFamilyFixedOriginBalancingLoss balanced) *
          finalFine.mass := by
    calc
      shading.mass ≤
          ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            pureWZ2CompleteParentRegularizationLoss
              actualNearby.scaleData.coarse.card coordinateCount *
            sameFamily.retentionConstant) *
            sameFamily.pullback.selectedFineShading.mass :=
        sameFamily.source_mass_retention
      _ ≤
          ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            pureWZ2CompleteParentRegularizationLoss
              actualNearby.scaleData.coarse.card coordinateCount *
            sameFamily.retentionConstant) *
            (pureWZ2SameFamilyFixedOriginBalancingLoss balanced *
              finalFine.mass) := by
        gcongr
      _ =
          (((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
              pureWZ2CompleteParentRegularizationLoss
                actualNearby.scaleData.coarse.card coordinateCount *
              sameFamily.retentionConstant) *
            pureWZ2SameFamilyFixedOriginBalancingLoss balanced) *
            finalFine.mass := by ring
  exact
    ⟨{
      balanced := balanced
      publicBalanced := publicBalanced
      finalFine_subshading := finalFineSubshading
      finalFine_cubical := finalFineCubical
      selected_mass_retention := selectedRetention
      source_mass_retention := sourceRetention
    }⟩

end Kakeya.Assouad

end
