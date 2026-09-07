import MyLeanRepo.Kakeya.Assouad.PureWZ2.PreselectedSameFamilyCallerNearbyAssembly
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDirectGeometricBalanced
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDirectPositiveFinalComparison
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierVolumeLower
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Corrected selected-caller post-deletion assembly

This private Layer-1 package records the complete selected-only route:
weight-band preselection, local regularization, exact merged provenance,
same-family caller CWA, fixed-origin balancing, and positive whole-parent
deletion.  The true preselection retention factor remains visible in the
source-mass ledger.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The explicit finite loss paid by the selected-caller fixed-origin
balancing stage.  This is the construction-independent part of the old
same-family ledger: it depends only on the direct balanced output itself. -/
def pureWZ2PreselectedFixedOriginBalancingLoss
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

/-- Exact forward ledger retained from the selected-caller balancing
constructor.  The geometric input is consumed while constructing this
receipt; downstream owner code only sees the resulting same-witness facts. -/
structure PureWZ2PreselectedFixedOriginBalancingReceipt
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (balanced :
      WZ2PaperDirectBalancedData
        cover shading hdelta hrho 14) : Prop where
  finalFine_subshading :
    ∀ index,
      balanced.finalData.producer.coarseBand.selectedFineShading.carrier
          index ⊆
        shading.carrier index
  finalFine_cubical :
    WZ1PaperIsCubicalShading
      balanced.finalData.producer.coarseBand.selectedFineShading
  selected_mass_retention :
    shading.mass ≤
      pureWZ2PreselectedFixedOriginBalancingLoss balanced *
        balanced.finalData.producer.coarseBand.selectedFineShading.mass

/-- Build the forward finite-loss ledger from the very same geometric input
used to construct the direct balanced output. -/
theorem pureWZ2_preselected_fixed_origin_balancing_receipt
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (input : WZ2PaperDirectGeometricInputData
      cover shading hdelta hrho)
    (balanced : WZ2PaperDirectBalancedData
      cover shading hdelta hrho 14) :
    PureWZ2PreselectedFixedOriginBalancingReceipt balanced := by
  let finalFine :=
    balanced.finalData.producer.coarseBand.selectedFineShading
  let fineLog : ENNReal :=
    ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal)
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
      shading.mass ≤ fineLog * balanced.bandData.band.mass := by
    have h := balanced.bandData.band_mass_retention
    rw [ENNReal.div_le_iff fineLogZero fineLogTop] at h
    simpa [fineLog, mul_comm] using h
  let crossingMass : ENNReal :=
    ∑ index : Fin fine.card,
      MeasureTheory.volume
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
        hdelta balanced.bandData
        balanced.rebalancing.boundaryPruning
        balanced.rebalancing.initialBalancing crossingHalf
  let cropMass : ENNReal :=
    ∑ index : Fin fine.card,
      MeasureTheory.volume
        (balanced.rebalancing.initialBalancing.refined.carrier index ∩
          wz2PaperCropBoundaryRegion rho)
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
      cropMass ≤ 2 * cropMass := le_mul_of_one_le_left' (by norm_num)
      _ < balanced.rebalancing.initialBalancing.refined.mass := cropHalf
  have cropLtRefined :
      cropMass < balanced.rebalancing.cropPruning.refined.mass := by
    apply (ENNReal.add_lt_add_iff_right cropFinite).mp
    calc
      cropMass + cropMass = 2 * cropMass := by ring
      _ < balanced.rebalancing.initialBalancing.refined.mass := cropHalf
      _ ≤ balanced.rebalancing.cropPruning.refined.mass + cropMass := by
        simpa [cropMass, add_comm] using
          balanced.rebalancing.cropPruning.source_mass_le_boundary
  have initialToCrop :
      balanced.rebalancing.initialBalancing.refined.mass ≤
        2 * balanced.rebalancing.cropPruning.refined.mass := by
    calc
      balanced.rebalancing.initialBalancing.refined.mass ≤
          balanced.rebalancing.cropPruning.refined.mass + cropMass := by
        simpa [cropMass] using
          balanced.rebalancing.cropPruning.source_mass_le_boundary
      _ ≤ balanced.rebalancing.cropPruning.refined.mass +
          balanced.rebalancing.cropPruning.refined.mass := by
        gcongr
      _ = 2 * balanced.rebalancing.cropPruning.refined.mass := by ring
  have cropMassEq :
      balanced.rebalancing.cropPruning.refined.mass =
        balanced.rebalancing.cropPruning.croppedBalancing.refined.mass :=
    congrArg Kakeya.Streamlined.Shading.mass
      balanced.rebalancing.cropPruning.croppedBalancing_refined_eq.symm
  have finalFineSubshading :
      ∀ index, finalFine.carrier index ⊆ shading.carrier index := by
    intro index
    have finalSub := balanced.finalData.finalRefinement.subshading index
    rw [balanced.rebalancing.cropPruning.croppedBalancing_refined_eq]
      at finalSub
    exact
      finalSub
        |>.trans (balanced.rebalancing.cropPruning.refined_subshading index)
        |>.trans
          (balanced.rebalancing.initialBalancing.refined_subshading index)
        |>.trans
          (balanced.rebalancing.boundaryPruning.pruned_subshading index)
        |>.trans
          (by
            rw [balanced.bandData.band_eq]
            exact wz1PaperDyadicBandSubshading_isSubshading
              shading balanced.bandData.level index)
  have selectedRetention :
      shading.mass ≤
        pureWZ2PreselectedFixedOriginBalancingLoss balanced *
          finalFine.mass := by
    calc
      shading.mass ≤ fineLog * balanced.bandData.band.mass := sourceToBand
      _ ≤ fineLog *
          ((8 * availableLog) *
            balanced.rebalancing.initialBalancing.refined.mass) := by
        gcongr
      _ ≤ fineLog *
          ((8 * availableLog) *
            (2 * balanced.rebalancing.cropPruning.refined.mass)) := by
        gcongr
      _ = (fineLog * (16 * availableLog)) *
          balanced.rebalancing.cropPruning.refined.mass := by ring
      _ = (fineLog * (16 * availableLog)) *
          balanced.rebalancing.cropPruning.croppedBalancing.refined.mass := by
        rw [cropMassEq]
      _ ≤ (fineLog * (16 * availableLog)) *
          (wz2PaperFinalBalancedCoverLoss balanced.finalData.producer *
            finalFine.mass) := by
        gcongr
        exact balanced.finalData.finalRefinement.source_mass_le
      _ = pureWZ2PreselectedFixedOriginBalancingLoss balanced *
          finalFine.mass := by
        simp only [pureWZ2PreselectedFixedOriginBalancingLoss]
        ring
  exact
    { finalFine_subshading := finalFineSubshading
      finalFine_cubical :=
        balanced.finalData.producer.coarseBand.selectedFine_cubical
      selected_mass_retention := selectedRetention }

structure PureWZ2PreselectedPostDeletionUniversalInput
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
    (coordinateCount : ℕ)
    (scales : Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (preselection :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    (regularized :
      PureWZ2PreselectedCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient coordinateCount preselection)
    (merged :
      PureWZ2GenericMergedCallerClassRegularizationData
        actualNearby quotient
        preselection.selectedCallerBase.toTubeSubfamily
        coordinateCount regularized.toCallerSubfamily
        ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          preselection.retentionConstant))
    (nearby :
      PureWZ2PreselectedCallerNearbyAssemblyData
        quotient coordinateCount scales scheduled preselection
        coarseConstant)
    (sameFamily :
      PureWZ2PreselectedSameFamilyCallerNearbyAssemblyData
        actualNearby quotient coordinateCount scales scheduled
        preselection regularized merged nearby)
    (scaleSeparation : 18 * delta ≤ callerRequested.1)
    (deletionExponent : ℕ) where
  retained_weight_receipt :
    (∑ parent :
        Fin (pureWZ2PostDeletionPositiveCallerBase quotient).family.card,
      pureWZ2PostDeletionPositiveCallerWeight quotient parent) ≤
        preselection.retentionConstant *
          ∑ parent : Fin preselection.selected.family.card,
            pureWZ2PostDeletionPositiveCallerWeight quotient
              (preselection.selected.embedding parent)
  weight_band_receipt :
    ∀ parent : Fin preselection.selected.family.card,
      preselection.weightLevel ≤
          pureWZ2PostDeletionPositiveCallerWeight quotient
            (preselection.selected.embedding parent) ∧
        pureWZ2PostDeletionPositiveCallerWeight quotient
            (preselection.selected.embedding parent) ≤
          2 * preselection.weightLevel
  source_to_same_family :
    shading.mass ≤
      (((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          preselection.retentionConstant) *
        pureWZ2CompleteParentRegularizationLoss
          actualNearby.scaleData.coarse.card coordinateCount) *
        sameFamily.selectedFineShading.mass
  balanced :
    WZ2PaperDirectBalancedData
      (sameFamily.internalPartitioningCover scaleSeparation)
      sameFamily.selectedFineShading
      actualNearby.scaleData.delta_pos
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
      14
  balancingReceipt :
    PureWZ2PreselectedFixedOriginBalancingReceipt balanced
  post :
    WZ2PaperDirectPositiveFinalComparisonData
      balanced deletionExponent

theorem pureWZ2_preselected_post_deletion_universal_input
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
    (coordinateCount : ℕ)
    (scales : Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (preselection :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    (regularized :
      PureWZ2PreselectedCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient coordinateCount preselection)
    (merged :
      PureWZ2GenericMergedCallerClassRegularizationData
        actualNearby quotient
        preselection.selectedCallerBase.toTubeSubfamily
        coordinateCount regularized.toCallerSubfamily
        ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          preselection.retentionConstant))
    (nearby :
      PureWZ2PreselectedCallerNearbyAssemblyData
        quotient coordinateCount scales scheduled preselection
        coarseConstant)
    (sameFamily :
      PureWZ2PreselectedSameFamilyCallerNearbyAssemblyData
        actualNearby quotient coordinateCount scales scheduled
        preselection regularized merged nearby)
    (scaleSeparation : 18 * delta ≤ callerRequested.1)
    (geometricInput :
      WZ2PaperDirectGeometricInputData
        (sameFamily.internalPartitioningCover scaleSeparation)
        sameFamily.selectedFineShading
        actualNearby.scaleData.delta_pos
        (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1))
    (deletionExponent : ℕ)
    (fractionSmall :
      wz1PaperRefinementFraction delta deletionExponent ≤
        (1 / 2 : ENNReal)) :
    Nonempty
      (PureWZ2PreselectedPostDeletionUniversalInput
        actualNearby quotient coordinateCount scales scheduled
        preselection regularized merged nearby sameFamily
        scaleSeparation deletionExponent) := by
  let balanced :
      WZ2PaperDirectBalancedData
        (sameFamily.internalPartitioningCover scaleSeparation)
        sameFamily.selectedFineShading
        actualNearby.scaleData.delta_pos
        (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
        14 :=
    Classical.choice <|
      wz2_paper_direct_balanced_from_geometric_input geometricInput
  let post :
      WZ2PaperDirectPositiveFinalComparisonData
        balanced deletionExponent :=
    Classical.choice <|
      wz2_paper_direct_positive_final_comparison
        balanced deletionExponent fractionSmall
  let balancingReceipt :
      PureWZ2PreselectedFixedOriginBalancingReceipt balanced :=
    pureWZ2_preselected_fixed_origin_balancing_receipt
      geometricInput balanced
  exact
    ⟨{
      retained_weight_receipt := preselection.retained_weight
      weight_band_receipt := preselection.weight_band
      source_to_same_family := sameFamily.source_mass_retention
      balanced := balanced
      balancingReceipt := balancingReceipt
      post := post
    }⟩

/-- Existential private ABI for one corrected selected-caller post-deletion
construction.  All runtime families remain dependent fields, while the
caller request and normalized source stay fixed external indices. -/
structure PureWZ2PreselectedPostDeletionUniversalPackage
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent)
    (callerRequested : WZ2PaperRequestedScale delta)
    (deletionExponent : ℕ) where
  ambientConstant : ENNReal
  fiberConstant : ENNReal
  coarseConstant : ENNReal
  actualRequested : WZ2PaperRequestedScale delta
  actualNearby :
    WZ2PaperPureNearbyScaleCoverData
      normalized.croppedFamily actualRequested ambientConstant
  quotient :
    PureWZ2ParentQuotientNetSelectionData
      actualNearby callerRequested normalized.croppedRefined
  coordinateCount : ℕ
  scales : Fin coordinateCount → WZ2PaperRequestedScale delta
  scheduled :
    ∀ coordinate,
      WZ2PaperPureNearbyScaleCoverData
        normalized.croppedFamily (scales coordinate) ambientConstant
  preselection :
    PureWZ2PostDeletionCallerWeightPreselectionData
      quotient coordinateCount scales scheduled
  regularized :
    PureWZ2PreselectedCallerRegularizationData
      (outputConstant := fiberConstant)
      actualNearby quotient coordinateCount preselection
  merged :
    PureWZ2GenericMergedCallerClassRegularizationData
      actualNearby quotient
      preselection.selectedCallerBase.toTubeSubfamily
      coordinateCount regularized.toCallerSubfamily
      ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
        preselection.retentionConstant)
  nearby :
    PureWZ2PreselectedCallerNearbyAssemblyData
      quotient coordinateCount scales scheduled preselection coarseConstant
  sameFamily :
    PureWZ2PreselectedSameFamilyCallerNearbyAssemblyData
      actualNearby quotient coordinateCount scales scheduled
      preselection regularized merged nearby
  scaleSeparation : 18 * delta ≤ callerRequested.1
  post :
    PureWZ2PreselectedPostDeletionUniversalInput
      actualNearby quotient coordinateCount scales scheduled
      preselection regularized merged nearby sameFamily
      scaleSeparation deletionExponent
  localFiberR : ENNReal
  localFiberWeightUpper : ENNReal
  fiberConstant_eq :
    fiberConstant =
      preselection.localFiberConstant
        localFiberR localFiberWeightUpper
  localFiberR_ne_top : localFiberR ≠ ⊤
  localFiberWeightUpper_ne_top : localFiberWeightUpper ≠ ⊤

namespace PureWZ2PreselectedPostDeletionUniversalPackage

/-- Explicit forward power lower bound for the caller weight level. It is
obtained before local complete-parent regularization from normalized source
density, quotient retention, weighted preselection, and the hit-parent
cardinality cancellation. -/
theorem weightLevel_lower
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (package :
      PureWZ2PreselectedPostDeletionUniversalPackage
        normalized callerRequested deletionExponent)
    (delta_small : delta ≤ 1 / 24) :
    Kakeya.realRpowENN delta (normalizationLoss + 2) ≤
      ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
        package.preselection.retentionConstant * 2) *
        package.preselection.weightLevel := by
  have ambientDensity :
      (Kakeya.realRpowENN delta normalizationLoss *
          Kakeya.realRpowENN delta 2) *
          normalized.croppedFamily.enncard ≤
        normalized.croppedRefined.mass := by
    have bodyMass :
        Kakeya.realRpowENN delta 2 *
            normalized.croppedFamily.enncard ≤
          (wz1PaperBodyFamily normalized.croppedFamily).mass := by
      calc
        Kakeya.realRpowENN delta 2 *
              normalized.croppedFamily.enncard =
            ∑ _index : Fin normalized.croppedFamily.card,
              Kakeya.realRpowENN delta 2 := by
          simp [Kakeya.Streamlined.TubeFamily.enncard,
            Finset.sum_const, mul_comm]
        _ ≤
            ∑ index : Fin normalized.croppedFamily.card,
              MeasureTheory.volume
                (wz1PaperTubeCarrier
                  (normalized.croppedFamily.tube index)) := by
          apply Finset.sum_le_sum
          intro index _
          simpa [Kakeya.realRpowENN, Real.rpow_two] using
            (canonical_volume_lower package.actualNearby.scaleData.delta_pos).trans
              (wz2PaperTubeCarrier_volume_lower
                package.actualNearby.scaleData.delta_pos
                (delta_small.trans (by norm_num))
                (normalized.croppedFamily.tube index)
                (normalized.line_class index))
        _ = (wz1PaperBodyFamily normalized.croppedFamily).mass := rfl
    calc
      (Kakeya.realRpowENN delta normalizationLoss *
            Kakeya.realRpowENN delta 2) *
            normalized.croppedFamily.enncard =
          Kakeya.realRpowENN delta normalizationLoss *
            (Kakeya.realRpowENN delta 2 *
              normalized.croppedFamily.enncard) := by ring
      _ ≤
          Kakeya.realRpowENN delta normalizationLoss *
            (wz1PaperBodyFamily normalized.croppedFamily).mass := by
        gcongr
      _ ≤ normalized.croppedRefined.mass :=
        normalized.final_extremal.dense
  rw [realRpowENN_add package.actualNearby.scaleData.delta_pos]
  exact
    package.preselection.weightLevel_density_lower
      normalized.final_extremal.nonempty
      (Kakeya.realRpowENN delta normalizationLoss *
        Kakeya.realRpowENN delta 2)
      ambientDensity

/-- Once the exact preselection coefficient is absorbed by one fixed loss,
the selected caller level has the promised family-free power floor. The
exponent is exactly `normalizationLoss + selectionLoss + 2`. -/
theorem weightLevel_power_lower
    {delta sigma sourceLoss normalizationLoss selectionLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (package :
      PureWZ2PreselectedPostDeletionUniversalPackage
        normalized callerRequested deletionExponent)
    (delta_small : delta ≤ 1 / 24)
    (selection_absorption :
      Kakeya.realRpowENN delta selectionLoss *
          ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            package.preselection.retentionConstant * 2) ≤
        1) :
    Kakeya.realRpowENN delta
        (normalizationLoss + selectionLoss + 2) ≤
      package.preselection.weightLevel := by
  have lower := package.weightLevel_lower delta_small
  calc
    Kakeya.realRpowENN delta
          (normalizationLoss + selectionLoss + 2) =
        Kakeya.realRpowENN delta selectionLoss *
          Kakeya.realRpowENN delta (normalizationLoss + 2) := by
      rw [← realRpowENN_add package.actualNearby.scaleData.delta_pos]
      congr 1
      ring
    _ ≤
        Kakeya.realRpowENN delta selectionLoss *
          (((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            package.preselection.retentionConstant * 2) *
            package.preselection.weightLevel) := by
      gcongr
    _ =
        (Kakeya.realRpowENN delta selectionLoss *
          ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            package.preselection.retentionConstant * 2)) *
          package.preselection.weightLevel := by ring
    _ ≤ 1 * package.preselection.weightLevel := by
      gcongr
    _ = package.preselection.weightLevel := by simp

theorem source_mass_retention
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (package :
      PureWZ2PreselectedPostDeletionUniversalPackage
        normalized callerRequested deletionExponent) :
    normalized.croppedRefined.mass ≤
      (((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          package.preselection.retentionConstant) *
        pureWZ2CompleteParentRegularizationLoss
          package.actualNearby.scaleData.coarse.card
          package.coordinateCount) *
        package.sameFamily.selectedFineShading.mass :=
  package.post.source_to_same_family

theorem retained_weight
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (package :
      PureWZ2PreselectedPostDeletionUniversalPackage
        normalized callerRequested deletionExponent) :
    (∑ parent :
        Fin (pureWZ2PostDeletionPositiveCallerBase
          package.quotient).family.card,
      pureWZ2PostDeletionPositiveCallerWeight package.quotient parent) ≤
      package.preselection.retentionConstant *
        ∑ parent : Fin package.preselection.selected.family.card,
          pureWZ2PostDeletionPositiveCallerWeight package.quotient
            (package.preselection.selected.embedding parent) :=
  package.post.retained_weight_receipt

end PureWZ2PreselectedPostDeletionUniversalPackage

end Kakeya.Assouad

end
