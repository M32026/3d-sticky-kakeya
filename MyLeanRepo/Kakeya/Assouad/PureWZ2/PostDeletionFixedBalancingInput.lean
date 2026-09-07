import MyLeanRepo.Kakeya.Assouad.PureWZ2.PostDeletionUniversalInputAssembly
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalGeometricNumericalData
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalGeometricLossAbsorption
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCanonicalPostMassVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPreparedCoarseLogBound
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import MyLeanRepo.Kakeya.Assouad.ExtremalHelpers
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Fixed balancing input on the post-deletion route

The direct balancing constructor only uses top-level Convex--Wolff for an
ambient family.  Here that ambient family is always the complete normalized
cropped family, so no arbitrary subfamily CWA is assumed.

The same-family ABI records source-mass retention but does not retain the
construction formula for its finite selection constant.  The single
selection-loss absorption below is therefore the thinnest scalar premise
needed to obtain a source-uniform threshold.  The second scalar premise is
the ambient cardinality-log bound needed by the final finite balancing loss.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

def pureWZ2PostDeletionSelectionLoss
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {support : PureWZ2PositiveCallerSupportData quotient}
    {coordinateCount : ℕ}
    {regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount}
    {merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized}
    {scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    (sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled) : ENNReal :=
  (pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
    pureWZ2CompleteParentRegularizationLoss
      actualNearby.scaleData.coarse.card coordinateCount *
    sameFamily.retentionConstant

noncomputable def pureWZ2PostDeletionFinalBalancingScale : ℝ :=
  Classical.choose
    wz2_paper_final_geometric_balanced_cover_loss_absorption

theorem pureWZ2PostDeletionFinalBalancingScale_pos :
    0 < pureWZ2PostDeletionFinalBalancingScale :=
  (Classical.choose_spec
    wz2_paper_final_geometric_balanced_cover_loss_absorption).1

theorem pureWZ2PostDeletionFinalBalancingScale_le_one :
    pureWZ2PostDeletionFinalBalancingScale ≤ 1 :=
  (Classical.choose_spec
    wz2_paper_final_geometric_balanced_cover_loss_absorption).2.1

theorem pureWZ2_postDeletion_fixed_balancing_input_from_selected
    {delta sigma sourceLoss internalLoss publicLoss selectionLoss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := internalLoss) source normalizationExponent)
    (callerRequested : WZ2PaperRequestedScale delta)
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        normalized.croppedFamily actualRequested
        (Kakeya.realRpowENN delta (-internalLoss)))
    (selected :
      Kakeya.Streamlined.TubeSubfamily normalized.croppedFamily)
    (coarse : Kakeya.Streamlined.TubeFamily callerRequested.1)
    (cover : WZ2PaperPartitioningCover selected.family coarse)
    (fineShading : WZ1PaperTubeShading selected.family)
    (selectedNonempty : selected.family.Nonempty)
    (coarseNonempty : coarse.Nonempty)
    (fineLine : WZ1PaperIsLineClass selected.family)
    (coarseLine : WZ1PaperIsLineClass coarse)
    (coarseDistinct : WZ1PaperIsEssentiallyDistinct coarse)
    (fineCubical : WZ1PaperIsCubicalShading fineShading)
    (selectionCost : ENNReal)
    (sourceMassRetention :
      normalized.croppedRefined.mass ≤ selectionCost * fineShading.mass)
    (scaleSeparation : 18 * delta ≤ callerRequested.1)
    (internalLossPos : 0 < internalLoss)
    (selectionLossPos : 0 < selectionLoss)
    (sourcePublicGap :
      16 * (internalLoss + selectionLoss) < publicLoss)
    (callerLower :
      Real.rpow delta (1 - publicLoss) ≤ callerRequested.1)
    (callerUpper :
      callerRequested.1 ≤ Real.rpow delta publicLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (periodicScale : 50 * delta ≤ callerRequested.1)
    (selectionAbsorption :
      Kakeya.realRpowENN delta selectionLoss *
          selectionCost ≤
        1)
    (selectedLogBound :
      ((Nat.log 2 selected.family.card + 1 : ℕ) : ENNReal) ≤
        ENNReal.ofReal
          (wz2PaperBoundaryLogCoefficient *
            (1 + Real.log delta⁻¹)))
    (numerical :
      WZ2PaperFinalGeometricNumericalData
        (internalLoss + selectionLoss) publicLoss publicLoss 0 0)
    (hdeltaNumerical : delta ≤ numerical.delta₀)
    (hdeltaFinal :
      delta ≤ pureWZ2PostDeletionFinalBalancingScale) :
    WZ2PaperDirectGeometricInputData
      cover fineShading
      actualNearby.scaleData.delta_pos
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1) := by
  let ambient := normalized.croppedFamily
  let fine := selected.family
  let hdelta := actualNearby.scaleData.delta_pos
  let hrho := hdelta.trans_le callerRequested.2.1
  let envelope : ENNReal :=
    ENNReal.ofReal
      (wz2PaperBoundaryLogCoefficient *
        (1 + Real.log delta⁻¹))
  let fraction := wz1PaperRefinementFraction delta 20
  let fineLog : ENNReal :=
    ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal)
  let firstLoss := fraction
  let secondLoss : ENNReal := 1
  let bandFactor :=
    firstLoss * fraction⁻¹ * (secondLoss * fineLog)
  let scalarFloor :=
    wz1PaperRefinementFraction delta 4 *
      ((1 / 2 : ENNReal) *
        Kakeya.realRpowENN delta (internalLoss + selectionLoss))
  have hdeltaOne : delta ≤ 1 :=
    hdeltaSmall.trans (by norm_num)
  have hdeltaStrict : delta < 1 := by
    nlinarith
  have ambientNonempty : ambient.Nonempty :=
    normalized.final_extremal.nonempty
  have fineLogBound : fineLog ≤ envelope := selectedLogBound
  have fineLogOne : (1 : ENNReal) ≤ fineLog := by
    dsimp only [fineLog]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have envelopeOne : (1 : ENNReal) ≤ envelope :=
    fineLogOne.trans fineLogBound
  have fineLogPos : 0 < fineLog :=
    zero_lt_one.trans_le fineLogOne
  have fineLogZero : fineLog ≠ 0 := fineLogPos.ne'
  have fineLogTop : fineLog ≠ ⊤ := by
    dsimp only [fineLog]
    simp
  have fractionOne : fraction ≤ 1 := by
    dsimp only [fraction, wz1PaperRefinementFraction]
    have logOne : 1 ≤ Real.log (1 / delta) := by
      apply (Real.le_log_iff_exp_le (by positivity)).2
      have expThree : Real.exp 1 < 3 := Real.exp_one_lt_three
      have threeInv : (3 : ℝ) ≤ 1 / delta := by
        rw [le_div_iff₀ hdelta]
        nlinarith
      exact expThree.le.trans threeInv
    exact
      pow_le_one₀ (by positivity)
        (ENNReal.inv_le_one.mpr
          (ENNReal.one_le_ofReal.mpr logOne))
  have fractionZero : fraction ≠ 0 :=
    wz1PaperRefinementFraction_ne_zero hdelta hdeltaStrict 20
  have fractionTop : fraction ≠ ⊤ :=
    wz1PaperRefinementFraction_ne_top hdelta hdeltaStrict 20
  have bandFactorEq : bandFactor = fineLog := by
    dsimp only [bandFactor, firstLoss, secondLoss]
    rw [ENNReal.mul_inv_cancel fractionZero fractionTop]
    simp
  have firstLossBound :
      firstLoss ≤ 8 * envelope ^ (0 + 2) := by
    calc
      firstLoss ≤ 1 := fractionOne
      _ ≤ 8 * envelope ^ (0 + 2) := by
        have powerOne : (1 : ENNReal) ≤ envelope ^ (0 + 2) :=
          one_le_pow₀ envelopeOne
        exact
          (by norm_num : (1 : ENNReal) ≤ 8).trans <|
            (by simpa using
              mul_le_mul_left' powerOne (8 : ENNReal))
  have secondLossBound :
      secondLoss ≤ 8 * envelope ^ (0 + 2) := by
    dsimp only [secondLoss]
    have powerOne : (1 : ENNReal) ≤ envelope ^ (0 + 2) :=
      one_le_pow₀ envelopeOne
    exact
      (by norm_num : (1 : ENNReal) ≤ 8).trans <|
        (by simpa using
          mul_le_mul_left' powerOne (8 : ENNReal))
  have topLevelBound :
      Kakeya.realRpowENN delta (-internalLoss) ≤
        Kakeya.realRpowENN delta
          (-4 * (internalLoss + selectionLoss)) := by
    exact
      realRpowENN_antitone hdelta hdeltaOne <| by
        nlinarith
  have ambientMassLower :
      Kakeya.realRpowENN delta internalLoss *
            Kakeya.realRpowENN delta 2 * ambient.enncard ≤
        normalized.croppedRefined.mass := by
    have bodyMass :
        Kakeya.realRpowENN delta 2 * ambient.enncard ≤
          (wz1PaperBodyFamily ambient).mass := by
      calc
        Kakeya.realRpowENN delta 2 * ambient.enncard =
            ∑ _index : Fin ambient.card,
              Kakeya.realRpowENN delta 2 := by
          simp [Kakeya.Streamlined.TubeFamily.enncard,
            Finset.sum_const, mul_comm]
        _ ≤
            ∑ index : Fin ambient.card,
              volume (wz1PaperTubeCarrier (ambient.tube index)) := by
          apply Finset.sum_le_sum
          intro index _
          simpa [Kakeya.realRpowENN, Real.rpow_two] using
            (canonical_volume_lower hdelta).trans
              (wz2PaperTubeCarrier_volume_lower
                hdelta (hdeltaSmall.trans (by norm_num))
                (ambient.tube index) (normalized.line_class index))
        _ = (wz1PaperBodyFamily ambient).mass := rfl
    calc
      Kakeya.realRpowENN delta internalLoss *
            Kakeya.realRpowENN delta 2 * ambient.enncard =
          Kakeya.realRpowENN delta internalLoss *
            (Kakeya.realRpowENN delta 2 * ambient.enncard) := by
        ring
      _ ≤
          Kakeya.realRpowENN delta internalLoss *
            (wz1PaperBodyFamily ambient).mass := by
        gcongr
      _ ≤ normalized.croppedRefined.mass :=
        normalized.final_extremal.dense
  have selectedMassLower :
      Kakeya.realRpowENN delta (internalLoss + selectionLoss) *
            (Kakeya.realRpowENN delta 2 * ambient.enncard) ≤
        fineShading.mass := by
    let totalLoss := selectionCost
    have sourceRetention :
        normalized.croppedRefined.mass ≤
          totalLoss * fineShading.mass := by
      simpa [totalLoss, mul_assoc] using sourceMassRetention
    calc
      Kakeya.realRpowENN delta (internalLoss + selectionLoss) *
            (Kakeya.realRpowENN delta 2 * ambient.enncard) =
          Kakeya.realRpowENN delta selectionLoss *
            (Kakeya.realRpowENN delta internalLoss *
              Kakeya.realRpowENN delta 2 * ambient.enncard) := by
        rw [realRpowENN_add hdelta]
        ring
      _ ≤
          Kakeya.realRpowENN delta selectionLoss *
            normalized.croppedRefined.mass := by
        gcongr
      _ ≤
          Kakeya.realRpowENN delta selectionLoss *
            (totalLoss * fineShading.mass) := by
        gcongr
      _ =
          (Kakeya.realRpowENN delta selectionLoss * totalLoss) *
            fineShading.mass := by
        ring
      _ ≤ 1 * fineShading.mass := by
        gcongr
      _ = fineShading.mass := by simp
  have crossingScalar :
      2 * bandFactor * 24000000 *
            (Kakeya.realRpowENN delta (-internalLoss) *
                wz2PaperBoundaryGeometryConstant + 1) *
            ENNReal.ofReal
              (Real.sqrt (delta / callerRequested.1)) <
        scalarFloor := by
    simpa only [bandFactor, scalarFloor, firstLoss, secondLoss, fraction,
      fineLog, envelope] using
      numerical.crossing hdelta hdeltaNumerical hrho callerRequested.2.2
        callerLower envelope envelope fineLog firstLoss secondLoss
        (Kakeya.realRpowENN delta (-internalLoss))
        le_rfl le_rfl fineLogBound firstLossBound secondLossBound
        topLevelBound
  have bandFloor :
      ∀ bandData : WZ2PaperGlobalMultiplicityBandData fineShading,
        scalarFloor *
              (Kakeya.realRpowENN delta 2 * ambient.enncard) ≤
          bandFactor * bandData.band.mass := by
    intro bandData
    have bandSource :
        fineShading.mass ≤ fineLog * bandData.band.mass := by
      have retained := bandData.band_mass_retention
      rw [ENNReal.div_le_iff fineLogZero fineLogTop] at retained
      simpa [fineLog, mul_comm] using retained
    calc
      scalarFloor *
            (Kakeya.realRpowENN delta 2 * ambient.enncard) ≤
          Kakeya.realRpowENN delta
              (internalLoss + selectionLoss) *
            (Kakeya.realRpowENN delta 2 * ambient.enncard) := by
        dsimp only [scalarFloor]
        have fractionFour :
            wz1PaperRefinementFraction delta 4 ≤ 1 := by
          dsimp only [wz1PaperRefinementFraction]
          have logOne : 1 ≤ Real.log (1 / delta) := by
            apply (Real.le_log_iff_exp_le (by positivity)).2
            have expThree : Real.exp 1 < 3 := Real.exp_one_lt_three
            have threeInv : (3 : ℝ) ≤ 1 / delta := by
              rw [le_div_iff₀ hdelta]
              nlinarith
            exact expThree.le.trans threeInv
          exact
            pow_le_one₀ (by positivity)
              (ENNReal.inv_le_one.mpr
                (ENNReal.one_le_ofReal.mpr logOne))
        calc
          (wz1PaperRefinementFraction delta 4 *
              ((1 / 2 : ENNReal) *
                Kakeya.realRpowENN delta
                  (internalLoss + selectionLoss))) *
                (Kakeya.realRpowENN delta 2 * ambient.enncard) ≤
            (1 * (1 *
              Kakeya.realRpowENN delta
                (internalLoss + selectionLoss))) *
                (Kakeya.realRpowENN delta 2 * ambient.enncard) := by
              gcongr <;> norm_num
          _ =
              Kakeya.realRpowENN delta
                  (internalLoss + selectionLoss) *
                (Kakeya.realRpowENN delta 2 * ambient.enncard) := by
            ring
      _ ≤ fineShading.mass := selectedMassLower
      _ ≤ fineLog * bandData.band.mass := bandSource
      _ = bandFactor * bandData.band.mass := by
        rw [bandFactorEq]
  have bandFactorPos : 0 < bandFactor := by
    rw [bandFactorEq]
    exact fineLogPos
  have bandFactorTop : bandFactor ≠ ⊤ := by
    rw [bandFactorEq]
    exact fineLogTop
  have cropScalar :
      ∀ bandData : WZ2PaperGlobalMultiplicityBandData fineShading,
        ∀ {multiplicityCap : ENNReal},
          ∀ boundaryPruning :
              WZ2PaperBoundaryCellPruningData
                (rho := callerRequested.1)
                bandData.band hdelta multiplicityCap,
            let availableLog : ENNReal :=
              ((Nat.log 2
                  (∑ coarseCell ∈ boundaryPruning.coarseCells,
                    (boundaryPruning.availableFineCells coarseCell).card) +
                    1 : ℕ) : ENNReal)
            2 * (bandFactor * (8 * availableLog)) *
                  wz2PaperCropBoundaryMassConstant *
                  (Kakeya.realRpowENN delta (-internalLoss) + 1) *
                  ENNReal.ofReal (Real.sqrt callerRequested.1) <
              scalarFloor := by
    intro bandData multiplicityCap boundaryPruning
    let availableLog : ENNReal :=
      ((Nat.log 2
          (∑ coarseCell ∈ boundaryPruning.coarseCells,
            (boundaryPruning.availableFineCells coarseCell).card) + 1 :
        ℕ) : ENNReal)
    have availableLogBound : availableLog ≤ envelope := by
      dsimp only [availableLog, envelope]
      exact
        wz2_paper_available_cell_log_bound_ennreal
          hdelta hdeltaOne boundaryPruning
    simpa only [bandFactor, scalarFloor, firstLoss, secondLoss, fraction,
      fineLog, envelope, availableLog, mul_assoc] using
      numerical.crop hdelta hdeltaNumerical hrho callerRequested.2.2
        callerUpper envelope envelope fineLog availableLog
        firstLoss secondLoss
        (Kakeya.realRpowENN delta (-internalLoss))
        le_rfl le_rfl fineLogBound availableLogBound
        firstLossBound secondLossBound topLevelBound
  have postBalancing :
      ∀ bandData : WZ2PaperGlobalMultiplicityBandData fineShading,
        ∀ {multiplicityCap : ENNReal},
          ∀ boundaryPruning :
              WZ2PaperBoundaryCellPruningData
                (rho := callerRequested.1)
                bandData.band hdelta multiplicityCap,
            wz1PaperRefinementFraction delta 2 *
                wz2PaperPostBalancingLoss boundaryPruning ≤
              1 := by
    intro bandData multiplicityCap boundaryPruning
    exact
      numerical.post_balancing hdelta hdeltaNumerical boundaryPruning
  let geometric :=
    wz2_paper_direct_geometric_from_scaled_floors
      hdelta hdeltaSmall hrho callerRequested.2.2
      callerRequested.2.1 periodicScale ambientNonempty
      normalized.line_class selected cover fineShading
      normalized.cropped_top_level_cwa
      bandFactor scalarFloor crossingScalar bandFloor
      bandFactorPos bandFactorTop cropScalar postBalancing
  have finalAbsorption :
      ∀ bandData : WZ2PaperGlobalMultiplicityBandData fineShading,
        ∀ rebalancing :
            WZ2PaperWholeCellRebalancingRepairedData
              cover fineShading bandData hdelta hrho,
          ∀ producer :
              WZ2PaperFinalBalancedCoverProducerData
                (hdelta := hdelta) (hrho := hrho)
                cover rebalancing.cropPruning.refined
                rebalancing.cropPruning.retainedCoarseCells
                rebalancing.cropPruning.selectedFineCells
                rebalancing.cropPruning.croppedBalancing
                rebalancing.coarseData,
            wz1PaperRefinementFraction delta 14 *
                  wz2PaperFinalBalancedCoverLoss producer ≤
              1 := by
    intro bandData rebalancing producer
    have fineLogFinal :
        ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) ≤ envelope :=
      fineLogBound
    have coarseDouble :
        (Nat.log 2 (2 * coarse.card) + 1 : ENNReal) ≤ envelope := by
      dsimp only [envelope]
      exact
        wz2_paper_prepared_coarse_log_bound
          hdelta hrho callerRequested.2.1 callerRequested.2.2
          coarseLine coarseDistinct
    have coarseLog :
        ((Nat.log 2 coarse.card + 1 : ℕ) : ENNReal) ≤ envelope := by
      calc
        ((Nat.log 2 coarse.card + 1 : ℕ) : ENNReal) ≤
            (Nat.log 2 (2 * coarse.card) + 1 : ENNReal) := by
          exact_mod_cast
            Nat.add_le_add_right
              (Nat.log_mono_right <| by omega) 1
        _ ≤ envelope := coarseDouble
    have coarseCells :
        rebalancing.cropPruning.croppedBalancing.retainedCoarseCells ⊆
          wz1PaperActiveCells
            rebalancing.coarseData.coarseShading hrho :=
      wz2_paper_final_geometric_retained_coarse_cells_subset_active_cells
        rebalancing.coarseData hrho
    have coarseCellLog :
        ((Nat.log 2
          rebalancing.cropPruning.croppedBalancing.retainedCoarseCells.card +
          1 : ℕ) : ENNReal) ≤ envelope := by
      calc
        ((Nat.log 2
            rebalancing.cropPruning.croppedBalancing.retainedCoarseCells.card +
            1 : ℕ) : ENNReal) ≤
            ((Nat.log 2
                (wz1PaperActiveCells
                  rebalancing.coarseData.coarseShading hrho).card + 1 : ℕ) :
              ENNReal) := by
          exact_mod_cast
            Nat.add_le_add_right
              (Nat.log_mono_right <| Finset.card_le_card coarseCells) 1
        _ ≤
            ENNReal.ofReal
              (wz2PaperBoundaryLogCoefficient *
                (1 + Real.log callerRequested.1⁻¹)) :=
          wz2_paper_active_cell_log_bound_ennreal
            hrho callerRequested.2.2 rebalancing.coarseData.coarseShading
        _ ≤ envelope := by
          dsimp only [envelope]
          apply ENNReal.ofReal_mono
          have logMono :
              Real.log callerRequested.1⁻¹ ≤ Real.log delta⁻¹ := by
            apply Real.log_le_log
            · exact inv_pos.mpr hrho
            · exact
                (inv_le_inv₀ hrho hdelta).mpr callerRequested.2.1
          have coefficientNonnegative :
              0 ≤ wz2PaperBoundaryLogCoefficient := by
            dsimp only [wz2PaperBoundaryLogCoefficient]
            positivity
          exact
            mul_le_mul_of_nonneg_left
              (by linarith) coefficientNonnegative
    have pairCard :
        (wz2PaperPositiveParentCellPairs
            producer.active producer.fiberBand.refined).card ≤
          rebalancing.cropPruning.croppedBalancing.retainedCoarseCells.card *
            coarse.card :=
      wz2_paper_final_geometric_pair_card_le
        producer.active producer.fiberBand.refined
    let retainedCellCount :=
      rebalancing.cropPruning.croppedBalancing.retainedCoarseCells.card
    have pairLog :
        (Nat.log 2
            (2 *
              (wz2PaperPositiveParentCellPairs
                producer.active producer.fiberBand.refined).card) :
          ENNReal) + 1 ≤
          2 * envelope := by
      have natBound :
          Nat.log 2
                (2 *
                  (wz2PaperPositiveParentCellPairs
                    producer.active producer.fiberBand.refined).card) + 1 ≤
            (Nat.log 2
                (retainedCellCount) + 1) +
              (Nat.log 2 (2 * coarse.card) + 1) := by
        calc
          _ ≤
              Nat.log 2
                  (2 *
                    (retainedCellCount * coarse.card)) + 1 := by
            dsimp only [retainedCellCount]
            exact
              Nat.add_le_add_right
                (Nat.log_mono_right <|
                  Nat.mul_le_mul_left 2 pairCard) 1
          _ ≤ _ :=
            wz2_paper_final_geometric_nat_log_two_twice_mul_add_one_le _ _
      calc
        (Nat.log 2
              (2 *
                (wz2PaperPositiveParentCellPairs
                  producer.active producer.fiberBand.refined).card) :
            ENNReal) + 1 ≤
            ((Nat.log 2
                (retainedCellCount) + 1 : ℕ) : ENNReal) +
              ((Nat.log 2 (2 * coarse.card) + 1 : ℕ) : ENNReal) := by
          exact_mod_cast natBound
        _ ≤ envelope + envelope :=
          add_le_add coarseCellLog <| by
            simpa only [Nat.cast_add, Nat.cast_one] using coarseDouble
        _ = 2 * envelope := by ring
    have finalCount :
        (∑ cell ∈ producer.finalFine.finalCoarseCells,
            (producer.finalFine.availableFinalFineCells cell).card) =
          producer.finalFine.activeFineCells.card :=
      wz2_paper_final_geometric_available_cell_count_eq producer.finalFine
    have finalCellLog :
        ((Nat.log 2
            (∑ cell ∈ producer.finalFine.finalCoarseCells,
              (producer.finalFine.availableFinalFineCells cell).card) + 1 :
          ℕ) : ENNReal) ≤
          envelope := by
      rw [finalCount, producer.finalFine.activeFineCells_eq]
      exact
        wz2_paper_active_cell_log_bound_ennreal
          hdelta hdeltaOne producer.finalFine.fineBand
    exact
      (Classical.choose_spec
          wz2_paper_final_geometric_balanced_cover_loss_absorption).2.2
        hdelta hdeltaFinal producer envelope
        fineLogFinal pairLog finalCellLog coarseLog le_rfl
  change
    WZ2PaperDirectGeometricInputData
      cover fineShading hdelta hrho
  exact
    {
      rho_le_one := callerRequested.2.2
      scale_separation := scaleSeparation
      refined_cubical := fineCubical
      fine_line := fineLine
      coarse_line := coarseLine
      geometric := geometric
      final_absorption := finalAbsorption
    }

/-- Compatibility wrapper for the original same-family package. -/
theorem pureWZ2_postDeletion_fixed_balancing_input
    {delta sigma internalLoss publicLoss selectionLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma internalLoss delta}
    {normalizationExponent : ℕ}
    (normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := internalLoss) source normalizationExponent)
    (callerRequested : WZ2PaperRequestedScale delta)
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby : WZ2PaperPureNearbyScaleCoverData
      normalized.croppedFamily actualRequested
      (Kakeya.realRpowENN delta (-internalLoss)))
    (quotient : PureWZ2ParentQuotientNetSelectionData
      actualNearby callerRequested normalized.croppedRefined)
    (support : PureWZ2PositiveCallerSupportData quotient)
    (coordinateCount : ℕ)
    {fiberConstant : ENNReal}
    (regularized : PureWZ2AllPositiveCallerRegularizationData
      (outputConstant := fiberConstant)
      actualNearby quotient support coordinateCount)
    (merged : PureWZ2MergedCallerClassRegularizationData
      actualNearby quotient support coordinateCount regularized)
    (scales : Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled : ∀ coordinate, WZ2PaperPureNearbyScaleCoverData
      normalized.croppedFamily (scales coordinate)
      (Kakeya.realRpowENN delta (-internalLoss)))
    {coarseConstant : ENNReal}
    (sameFamily : PureWZ2SameFamilyCallerNearbyAssemblyData
      (coarseConstant := coarseConstant) actualNearby quotient support
      coordinateCount regularized merged scales scheduled)
    (scaleSeparation : 18 * delta ≤ callerRequested.1)
    (internalLossPos : 0 < internalLoss)
    (selectionLossPos : 0 < selectionLoss)
    (sourcePublicGap : 16 * (internalLoss + selectionLoss) < publicLoss)
    (callerLower : Real.rpow delta (1 - publicLoss) ≤ callerRequested.1)
    (callerUpper : callerRequested.1 ≤ Real.rpow delta publicLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (periodicScale : 50 * delta ≤ callerRequested.1)
    (selectionAbsorption :
      Kakeya.realRpowENN delta selectionLoss *
          pureWZ2PostDeletionSelectionLoss sameFamily ≤ 1)
    (ambientLogBound :
      (Nat.log 2 (2 * normalized.croppedFamily.card) + 1 : ENNReal) ≤
        ENNReal.ofReal
          (wz2PaperBoundaryLogCoefficient * (1 + Real.log delta⁻¹)))
    (numerical : WZ2PaperFinalGeometricNumericalData
      (internalLoss + selectionLoss) publicLoss publicLoss 0 0)
    (hdeltaNumerical : delta ≤ numerical.delta₀)
    (hdeltaFinal : delta ≤ pureWZ2PostDeletionFinalBalancingScale) :
    WZ2PaperDirectGeometricInputData
      (sameFamily.pullback.internalPartitioningCover scaleSeparation)
      sameFamily.pullback.selectedFineShading
      actualNearby.scaleData.delta_pos
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1) := by
  let selected := merged.merged.toTubeSubfamily.comp
    sameFamily.pullback.selectedFine
  have selectedNonempty : selected.family.Nonempty := by
    let parent : Fin sameFamily.selectedCoarse.family.card :=
      ⟨0, sameFamily.selectedCoarse_nonempty⟩
    rcases sameFamily.pullback.section6Cover.parent_hit parent with
      ⟨index, _⟩
    exact Fin.pos_iff_nonempty.mpr ⟨index⟩
  have fineCubical : WZ1PaperIsCubicalShading
      sameFamily.pullback.selectedFineShading := by
    rw [sameFamily.pullback.selectedFineShading_eq,
      merged.mergedShading_eq]
    exact restrictPaperShading_cubical sameFamily.pullback.selectedFine
      (restrictPaperShading_cubical merged.merged.toTubeSubfamily
        normalized.cropped_cubical)
  exact pureWZ2_postDeletion_fixed_balancing_input_from_selected
    normalized callerRequested actualNearby selected
    sameFamily.selectedCoarse.family
    (sameFamily.pullback.internalPartitioningCover scaleSeparation)
    sameFamily.pullback.selectedFineShading selectedNonempty
    sameFamily.selectedCoarse_nonempty
    sameFamily.pullback.section6Cover.fine_line_class
    sameFamily.pullback.section6Cover.coarse_line_class
    sameFamily.pullback.section6Cover.coarse_essentially_distinct
    fineCubical (pureWZ2PostDeletionSelectionLoss sameFamily)
    (by
      calc
        normalized.croppedRefined.mass ≤
            ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
              pureWZ2CompleteParentRegularizationLoss
                actualNearby.scaleData.coarse.card coordinateCount *
              sameFamily.retentionConstant) *
              sameFamily.pullback.selectedFineShading.mass :=
          sameFamily.source_mass_retention
        _ = pureWZ2PostDeletionSelectionLoss sameFamily *
              sameFamily.pullback.selectedFineShading.mass := by
          rfl)
    scaleSeparation internalLossPos selectionLossPos sourcePublicGap
    callerLower callerUpper hdeltaSmall periodicScale selectionAbsorption
    (by
      let fine := selected.family
      let ambient := normalized.croppedFamily
      have fineCardLeAmbient : fine.card ≤ ambient.card := by
        simpa only [Fintype.card_fin] using
          Fintype.card_le_of_injective
            selected.embedding selected.embedding.injective
      have cardBound : fine.card ≤ 2 * ambient.card := by omega
      have logCard :
          Nat.log 2 fine.card ≤ Nat.log 2 (2 * ambient.card) :=
        Nat.log_mono_right cardBound
      calc
        ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) ≤
            (Nat.log 2 (2 * ambient.card) + 1 : ENNReal) := by
          exact_mod_cast Nat.add_le_add_right logCard 1
        _ ≤ _ := by simpa only [ambient] using ambientLogBound)
    numerical hdeltaNumerical hdeltaFinal

theorem pureWZ2_postDeletion_fixed_balancing_input_uniform_scales
    (internalLoss selectionLoss publicLoss : ℝ)
    (internalLossPos : 0 < internalLoss)
    (selectionLossPos : 0 < selectionLoss)
    (publicLossPos : 0 < publicLoss)
    (sourcePublicGap :
      16 * (internalLoss + selectionLoss) < publicLoss) :
    ∃ numerical :
        WZ2PaperFinalGeometricNumericalData
          (internalLoss + selectionLoss) publicLoss publicLoss 0 0,
      ∃ delta₀ : ℝ,
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        delta₀ ≤ numerical.delta₀ ∧
        delta₀ ≤ pureWZ2PostDeletionFinalBalancingScale ∧
        delta₀ ≤ 1 / 24 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          50 * delta ≤ Real.rpow delta (1 - publicLoss) := by
  let numerical :=
    Classical.choice <|
      wz2_paper_final_geometric_numerical_data
        (internalLoss + selectionLoss) publicLoss publicLoss
        (by positivity) sourcePublicGap sourcePublicGap 0 0
  rcases
      exists_delta_mul_rpow_le_rpow
        50 (by norm_num)
        (alpha := 1) (beta := 1 - publicLoss)
        (by linarith)
    with
    ⟨periodicScale, periodicScalePos, periodicScaleOne,
      periodicAbsorption⟩
  let delta₀ :=
    min numerical.delta₀
      (min pureWZ2PostDeletionFinalBalancingScale
        (min periodicScale (1 / 24)))
  refine
    ⟨numerical, delta₀,
      lt_min numerical.delta₀_pos <|
        lt_min pureWZ2PostDeletionFinalBalancingScale_pos <|
          lt_min periodicScalePos (by norm_num),
      (min_le_left _ _).trans numerical.delta₀_le_one,
      min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _),
      ?_⟩
  intro delta deltaPos deltaSmall
  simpa using
    periodicAbsorption delta deltaPos
      (deltaSmall.trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _))

end Kakeya.Assouad

end
