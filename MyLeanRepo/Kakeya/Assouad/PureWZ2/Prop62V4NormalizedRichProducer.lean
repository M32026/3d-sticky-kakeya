import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4NormalizedFixedGrid
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4Pipeline
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4PureRefinementComposition
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4MetricCoarseCellAdapter
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4RichFourDegreeProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4ThreeLossRouting

/-!
# Rich Proposition 6.2 certificates from normalized sources

This module combines the normalized fixed-grid cleanup, the bounded-base
metric-parent pipeline, and the rich four-degree producer.  All thresholds
are selected before the runtime scale and normalized source.

The live constants are fixed to `A = 1`, metric CWA power `8`, input density
exponent `1`, packet density exponent `2`, rich CWA loss exponent `51`, and
polylogarithmic exponent `10`.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open Kakeya.Assouad
open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The fixed-grid cleanup is run at an intermediate loss, leaving a positive
gap which pays for the metric ten-log refinement. -/
def prop62V4NormalizedRichIntermediateLoss
    {sigma outputLoss : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData 10 8 2 51 sigma outputLoss}
    (three : Prop62V4ThreeLossRoutingData routing) : ℝ :=
  (three.normalizationLoss + three.workingEta) / 2

private theorem normalizedRich_bodyFamily_mass_subfamily_le
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily source) :
    (wz1PaperBodyFamily selected.family).mass ≤
      (wz1PaperBodyFamily source).mass := by
  change
    (∑ index : Fin selected.family.card,
      volume (wz1PaperTubeCarrier (selected.family.tube index))) ≤
    ∑ index : Fin source.card,
      volume (wz1PaperTubeCarrier (source.tube index))
  calc
    (∑ index : Fin selected.family.card,
        volume (wz1PaperTubeCarrier (selected.family.tube index))) =
      ∑ index : Fin selected.family.card,
        volume (wz1PaperTubeCarrier
          (source.tube (selected.embedding index))) := by
        apply Finset.sum_congr rfl
        intro index _
        rw [selected.tube_eq]
    _ =
        ∑ index ∈ Finset.univ.map selected.embedding,
          volume (wz1PaperTubeCarrier (source.tube index)) := by
      exact
        (Finset.sum_map Finset.univ selected.embedding
          (fun index =>
            volume (wz1PaperTubeCarrier (source.tube index)))).symm
    _ ≤
        ∑ index : Fin source.card,
          volume (wz1PaperTubeCarrier (source.tube index)) := by
      exact
        Finset.sum_le_sum_of_subset_of_nonneg
          (by simp) (fun _ _ _ => bot_le)

private theorem normalizedRich_exists_delta_power_le_refinementFraction
    (eta : ℝ)
    (etaPos : 0 < eta)
    (logExponent : ℕ)
    (logExponentPos : 0 < logExponent) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        Kakeya.realRpowENN delta eta ≤
          wz1PaperRefinementFraction delta logExponent := by
  rcases
      exists_delta_log_absorbed_ennreal
        (1 : ENNReal) (by norm_num) etaPos logExponentPos
    with ⟨delta₀, delta₀Pos, delta₀LeOne, absorb⟩
  refine ⟨delta₀, delta₀Pos, delta₀LeOne, ?_⟩
  intro delta deltaPos deltaLe
  let logTerm : ENNReal :=
    ENNReal.ofReal (Real.log (1 / delta))
  let envelope : ENNReal :=
    ENNReal.ofReal (1 + Real.log delta⁻¹)
  have deltaLeOne : delta ≤ 1 :=
    deltaLe.trans delta₀LeOne
  have logNonnegative : 0 ≤ Real.log delta⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ deltaPos).mpr deltaLeOne)
  have logLe : logTerm ≤ envelope := by
    dsimp only [logTerm, envelope]
    apply ENNReal.ofReal_mono
    rw [show 1 / delta = delta⁻¹ by simp]
    linarith
  have envelopeBound :
      envelope ^ logExponent ≤
        Kakeya.realRpowENN delta (-eta) := by
    simpa [envelope] using absorb delta deltaPos deltaLe
  have productBound :
      Kakeya.realRpowENN delta eta *
          logTerm ^ logExponent ≤
        1 := by
    calc
      Kakeya.realRpowENN delta eta *
            logTerm ^ logExponent ≤
          Kakeya.realRpowENN delta eta *
            envelope ^ logExponent := by
        gcongr
      _ ≤
          Kakeya.realRpowENN delta eta *
            Kakeya.realRpowENN delta (-eta) := by
        gcongr
      _ = 1 := by
        rw [← realRpowENN_add deltaPos]
        simp [Kakeya.realRpowENN]
  rw [wz1PaperRefinementFraction, ← ENNReal.inv_pow]
  exact ENNReal.le_inv_iff_mul_le.mpr productBound

private theorem WZ1PaperRefinement.dense_of_power_gap
    {delta sourceExponent targetExponent : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {logExponent : ℕ}
    (hdelta : 0 < delta)
    (sourceDense :
      shading.IsLambdaDense
        (Kakeya.realRpowENN delta sourceExponent))
    (refinement : WZ1PaperRefinement shading logExponent)
    (powerAbsorption :
      Kakeya.realRpowENN delta (targetExponent - sourceExponent) ≤
        wz1PaperRefinementFraction delta logExponent) :
    refinement.refined.IsLambdaDense
      (Kakeya.realRpowENN delta targetExponent) := by
  rw [Kakeya.Streamlined.Shading.IsLambdaDense]
  have selectedMass :=
    normalizedRich_bodyFamily_mass_subfamily_le refinement.selected
  calc
    Kakeya.realRpowENN delta targetExponent *
          (wz1PaperBodyFamily refinement.selected.family).mass =
        (Kakeya.realRpowENN delta
            (targetExponent - sourceExponent) *
          Kakeya.realRpowENN delta sourceExponent) *
          (wz1PaperBodyFamily refinement.selected.family).mass := by
      rw [← realRpowENN_add hdelta]
      congr 2
      ring
    _ ≤
        (wz1PaperRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta sourceExponent) *
          (wz1PaperBodyFamily source).mass := by
      gcongr
    _ =
        wz1PaperRefinementFraction delta logExponent *
          (Kakeya.realRpowENN delta sourceExponent *
            (wz1PaperBodyFamily source).mass) := by
      ring
    _ ≤
        wz1PaperRefinementFraction delta logExponent *
          shading.mass := by
      exact mul_le_mul_left' sourceDense _
    _ ≤ refinement.refined.mass :=
      refinement.retained_mass

private theorem
    PureWZ2Prop62MetricParentsV4Certificate.toMetricData_refined_dense
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant densityConstant : ENNReal}
    (certificate :
      PureWZ2Prop62MetricParentsV4Certificate
        shading rho fineParentDistanceConstant
          parentConstant fiberConstant)
    (dense :
      certificate.refinement.refined.IsLambdaDense densityConstant) :
    certificate.toMetricData.refinement.refined.IsLambdaDense
      densityConstant := by
  rcases certificate with
    ⟨rhoPos, distanceConstantPos, refinement, fine, fineEq,
      refinedNonempty, refinedCubical, coarse, _coarseCentered, section6Cover,
      cover, coverEq, fullFiberUniform, coarseCWA,
      coarseStronglySeparated, sourceFiberConstant,
      fiberConstantEq, fiberRescaling, fiberPublicCWA,
      metricFiber, fineParentClose⟩
  subst fine
  exact dense

/--
The exact fixed-grid preparation, metric certificate, and rich companion
produced from one normalized source.  The dependent fields ensure that the
rich companion uses the same fixed-grid cleanup and metric certificate.
-/
structure Prop62V4NormalizedRichProducerData
    {sigma outputLoss delta : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData 10 8 2 51 sigma outputLoss}
    (three : Prop62V4ThreeLossRoutingData routing)
    {source :
      PureWZ2ExtremalConfiguration sigma three.sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := three.normalizationLoss)
        source normalizationExponent)
    (rho : WZ2PaperRequestedScale delta)
    (hdelta : 0 < delta) where
  fixedGrid :
    Prop62V4NormalizedFixedGridData
      (workingEta := prop62V4NormalizedRichIntermediateLoss three)
      normalized rho
  metricCertificate :
    PureWZ2Prop62MetricParentsV4Certificate
      fixedGrid.preparation.cleanup.refined rho (1 / 100 : ℝ)
      (Kakeya.realRpowENN delta (-8 * three.workingEta))
      (Kakeya.realRpowENN delta (-8 * three.workingEta))
  rich :
    Prop62V4RichCertificateCompanionData
      (eta := three.workingEta)
      (packetDensityExponent := 2)
      (cwaLossExponent := 51)
      (polylogExponent := 10)
      hdelta
      (prop62V4FixedGridMetricCompanionOfCertificate
        normalized fixedGrid.preparation metricCertificate)

/--
A single threshold selected from the fixed routing data, fixed-grid theorem,
and cleanup oracle, before the runtime scale and normalized source.
-/
structure Prop62V4NormalizedRichProducerThresholdReceipt
    {sigma outputLoss : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData 10 8 2 51 sigma outputLoss}
    (three : Prop62V4ThreeLossRoutingData routing) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one_hundred : delta₀ ≤ 1 / 100
  produce :
    ∀ {delta : ℝ}, ∀ (hdelta : 0 < delta),
      delta ≤ delta₀ →
      ∀ {source :
          PureWZ2ExtremalConfiguration sigma three.sourceLoss delta},
        ∀ {normalizationExponent : ℕ},
          ∀ (normalized :
              PureWZ2CroppedCriticalNormalizationData
                (outputLoss := three.normalizationLoss)
                source normalizationExponent),
            ∀ rho : WZ2PaperRequestedScale delta,
              Real.rpow delta (1 - outputLoss) ≤ rho.1 →
              rho.1 ≤ Real.rpow delta outputLoss →
                Nonempty
                  (Prop62V4NormalizedRichProducerData
                    three normalized rho hdelta)

/--
Uniformly produce the exact rich Proposition 6.2 companion from an arbitrary
completed normalization.

The metric-parent stage uses the cleaned pure CWA and density supplied by the
fixed-grid preparation and uses `normalized.ordinary_bounded_base`; no
unit-ball hypothesis is introduced.
-/
theorem prop62V4_normalized_rich_producer
    {sigma outputLoss : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData 10 8 2 51 sigma outputLoss}
    (three : Prop62V4ThreeLossRoutingData routing)
    (hFixedGrid : FixedGridBoundaryRemovalStatement)
    (cleanupOracle : PureWZ2Prop62CleanupOracle) :
    Nonempty
      (Prop62V4NormalizedRichProducerThresholdReceipt three) := by
  have outputLossPos : 0 < outputLoss := by
    nlinarith [three.normalizationLoss_pos,
      three.normalizationLoss_output_budget]
  have normalizationToIntermediate :
      three.normalizationLoss <
        prop62V4NormalizedRichIntermediateLoss three := by
    unfold prop62V4NormalizedRichIntermediateLoss
    linarith [three.normalizationLoss_lt_workingEta]
  have intermediateToWorking :
      prop62V4NormalizedRichIntermediateLoss three <
        three.workingEta := by
    unfold prop62V4NormalizedRichIntermediateLoss
    linarith [three.normalizationLoss_lt_workingEta]
  rcases
      prop62V4NormalizedFixedGridThreshold
        normalizationToIntermediate
        three.normalizationLoss_output_budget hFixedGrid
    with ⟨fixedGridThreshold⟩
  have metricLoss :
      (pureWZ2Prop62MetricParentsV4CWAPower 1 : ℝ) *
          three.workingEta ≤
        outputLoss / 100 := by
    simpa [three.workingEta_eq] using routing.numerics.metric_loss
  let metricThreshold :=
    pureWZ2Prop62MetricParentsV4Threshold
      1 outputLoss three.workingEta (1 / 100 : ℝ)
      (by norm_num) outputLossPos
      three.workingEta_pos metricLoss (by norm_num)
  rcases
      exists_prop62V4RichCertificateCompanion
        cleanupOracle 1 8 three.workingEta three.workingEta_pos
        (by
          simpa [three.workingEta_eq,
            pureWZ2Prop62FourDegreePacketDensityExponent] using
              routing.numerics.packet_loss)
    with
    ⟨richThreshold, richThresholdPos, richThresholdLe, produceRich⟩
  rcases
      normalizedRich_exists_delta_power_le_refinementFraction
        (three.workingEta -
          prop62V4NormalizedRichIntermediateLoss three)
        (by linarith) 10 (by norm_num)
    with
    ⟨densityThreshold, densityThresholdPos, densityThresholdLe,
      absorbDensity⟩
  rcases
      exists_delta_mul_rpow_le_rpow
        18 (by norm_num)
        (alpha := 1) (beta := 1 - outputLoss)
        (by linarith)
    with
    ⟨separationThreshold, separationThresholdPos,
      separationThresholdLe, separate⟩
  let delta₀ :=
    min fixedGridThreshold.delta₀
      (min metricThreshold
        (min richThreshold
          (min densityThreshold separationThreshold)))
  have metricThresholdPos : 0 < metricThreshold := by
    dsimp only [metricThreshold]
    exact
      pureWZ2Prop62MetricParentsV4Threshold_pos
        1 outputLoss three.workingEta (1 / 100 : ℝ)
        (by norm_num) outputLossPos
        three.workingEta_pos metricLoss (by norm_num)
  have delta₀Pos : 0 < delta₀ := by
    dsimp only [delta₀]
    exact
      lt_min fixedGridThreshold.delta₀_pos <|
        lt_min metricThresholdPos <|
          lt_min richThresholdPos <|
            lt_min densityThresholdPos separationThresholdPos
  refine
    ⟨{
      delta₀ := delta₀
      delta₀_pos := delta₀Pos
      delta₀_le_one_hundred :=
        (min_le_left _ _).trans
          fixedGridThreshold.delta₀_le_one_hundred
      produce := ?_
    }⟩
  intro delta deltaPos deltaLe source normalizationExponent normalized
    rho rhoLower rhoUpper
  have deltaFixedGrid : delta ≤ fixedGridThreshold.delta₀ :=
    deltaLe.trans (min_le_left _ _)
  have deltaMetric : delta ≤ metricThreshold :=
    deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
  have deltaRich : delta ≤ richThreshold :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have deltaDensity : delta ≤ densityThreshold :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have deltaSeparation : delta ≤ separationThreshold :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
  rcases
      fixedGridThreshold.prepare deltaPos deltaFixedGrid
        normalized rho rhoLower rhoUpper
    with ⟨fixedGrid⟩
  let cleanedWorking :=
    fixedGrid.cleaned_extremal.mono_loss intermediateToWorking.le
  have cleanedCWA :
      WZ2PaperPureCWAAtNearbyScales normalized.croppedFamily
        (pureWZ2Prop62CallerCstar delta 1 three.workingEta) := by
    simpa [pureWZ2Prop62CallerCstar, pureWZ2Prop62CallerLoss] using
      cleanedWorking.cwa_nearby_scales
  have cleanedDense :
      fixedGrid.preparation.cleanup.refined.IsLambdaDense
        (Kakeya.realRpowENN delta three.workingEta) := by
    simpa using cleanedWorking.dense
  rcases
      pureWZ2_prop62_metric_parents_v4_pipeline_of_bounded_base
        1 outputLoss three.workingEta (1 / 100 : ℝ) delta
        normalized.croppedFamily fixedGrid.preparation.cleanup.refined rho
        (by norm_num) outputLossPos
        three.workingEta_pos metricLoss (by norm_num) deltaPos deltaMetric
        fixedGrid.cleaned_extremal.nonempty
        normalized.ordinary_bounded_base
        fixedGrid.line_class fixedGrid.cleaned_cubical
        cleanedCWA (by simpa using cleanedDense)
        rhoLower rhoUpper cleanupOracle
    with ⟨metricCertificate⟩
  have parentConstantLe :
      Kakeya.realRpowENN delta (-8 * three.workingEta) ≤
        Kakeya.realRpowENN delta (-(8 : ℝ) * three.workingEta) := by
    rfl
  have fiberConstantLe :
      Kakeya.realRpowENN delta (-8 * three.workingEta) ≤
        Kakeya.realRpowENN delta (-(8 : ℝ) * three.workingEta) := by
    rfl
  have refinedDense :
      (prop62V4FixedGridMetricCompanionOfCertificate
        normalized fixedGrid.preparation metricCertificate
      ).metric.refinement.refined.IsLambdaDense
        (Kakeya.realRpowENN delta three.workingEta) := by
    change
      metricCertificate.toMetricData.refinement.refined.IsLambdaDense
        (Kakeya.realRpowENN delta three.workingEta)
    apply
      PureWZ2Prop62MetricParentsV4Certificate.toMetricData_refined_dense
        metricCertificate
    exact
      have raw :
          metricCertificate.refinement.refined.IsLambdaDense
            (Kakeya.realRpowENN delta three.workingEta) :=
        WZ1PaperRefinement.dense_of_power_gap
          deltaPos fixedGrid.cleaned_extremal.dense
          metricCertificate.refinement
          (absorbDensity delta deltaPos deltaDensity)
      raw
  have scaleSeparation : 18 * delta ≤ rho.1 := by
    calc
      18 * delta = 18 * Real.rpow delta 1 := by simp
      _ ≤ Real.rpow delta (1 - outputLoss) :=
        separate delta deltaPos deltaSeparation
      _ ≤ rho.1 := rhoLower
  have coarseCell :=
    Prop62V4MetricParentsRichCompanionData.fixedGrid_coarse_cell
      fixedGrid.preparation.cleanup
      (prop62V4FixedGridMetricCompanionOfCertificate
        normalized fixedGrid.preparation metricCertificate)
      scaleSeparation
  rcases
      produceRich delta deltaPos deltaRich normalized.croppedFamily
        fixedGrid.preparation.cleanup.refined rho (1 / 100 : ℝ)
        (Kakeya.realRpowENN delta (-8 * three.workingEta))
        (Kakeya.realRpowENN delta (-8 * three.workingEta))
        (prop62V4FixedGridMetricCompanionOfCertificate
          normalized fixedGrid.preparation metricCertificate)
        parentConstantLe fiberConstantLe
        (by simpa only [Nat.cast_one, one_mul])
        coarseCell
    with ⟨rich⟩
  exact
    ⟨{
      fixedGrid := fixedGrid
      metricCertificate := metricCertificate
      rich := by
        simpa [pureWZ2Prop62FourDegreePacketDensityExponent,
          pureWZ2Prop62RichFourDegreeCWALossExponent,
          pureWZ2Prop62FourDegreePolylogExponent] using rich
    }⟩

end Kakeya.Assouad.Prop62PaperAudit.V4

end
