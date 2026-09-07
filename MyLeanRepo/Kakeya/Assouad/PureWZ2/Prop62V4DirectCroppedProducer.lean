import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4FixedGridBoundaryRemoval
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4OnePassTreeCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4TargetAdapter
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4Threshold
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4Pipeline
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4MetricCoarseCellAdapter
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4RichFourDegreeProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperFinalV4FixedGridPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ConfigurationWeakening
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# Direct cropped Proposition 6.2 V4 producer

This Node3-owned module keeps only the direct cropped runtime chain

`fixed-grid -> metric parents -> rich/four-degree`.

The runtime input is now a paper-facing
`PureWZ2C2GrainConfiguration`.  The fixed-grid cleanup, cleaned cropped
extremality, metric refinement density, and final rich witness are all
constructed internally from the fields already stored in that configuration.

No normalization, re-entry, exact-source bridge, or final/universal assembly
appears here.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open MeasureTheory
open Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The direct cropped fixed-grid step is run at an intermediate loss between
the source loss and the final working loss. -/
def prop62V4DirectCroppedIntermediateLoss
    (sourceLoss workingEta : ℝ) : ℝ :=
  (sourceLoss + workingEta) / 2

private theorem directCropped_directionLevelCount_le_logEnvelope
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1) :
    logarithmicLoss delta ≤
      2 * ENNReal.ofReal (1 + Real.log delta⁻¹) := by
  have logNonneg : 0 ≤ Real.log delta⁻¹ := by
    exact Real.log_nonneg ((one_le_inv₀ deltaPos).mpr deltaLeOne)
  have quotientNonneg :
      0 ≤ Real.log delta⁻¹ / Real.log 2 := by
    positivity
  have floorLe :
      (Nat.floor (Real.log delta⁻¹ / Real.log 2) : ℝ) ≤
        Real.log delta⁻¹ / Real.log 2 :=
    Nat.floor_le quotientNonneg
  have logTwoHalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have bound :
        Real.log (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have rewrite :
        Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num)]
      simp
    rw [rewrite] at bound
    linarith
  have quotientLe :
      Real.log delta⁻¹ / Real.log 2 ≤
        2 * Real.log delta⁻¹ := by
    rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    nlinarith
  have realBound :
      (pureWZ2Prop62DirectionLevelCount delta : ℝ) ≤
        2 * (1 + Real.log delta⁻¹) := by
    change
      ((Nat.floor (Real.log (1 / delta) / Real.log 2) + 1 : ℕ) : ℝ) ≤
        2 * (1 + Real.log delta⁻¹)
    rw [show 1 / delta = delta⁻¹ by simp]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have converted := ENNReal.ofReal_mono realBound
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at converted
  norm_num at converted ⊢
  simpa [logarithmicLoss] using converted

private theorem directCropped_refinementFraction_one_le_half
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaSmall : delta ≤ Real.exp (-2)) :
    wz1PaperRefinementFraction delta 1 ≤ (1 / 2 : ENNReal) := by
  have expNegPos : 0 < Real.exp (-2) := Real.exp_pos _
  have inverse : Real.exp 2 ≤ delta⁻¹ := by
    have bound := (inv_le_inv₀ expNegPos deltaPos).mpr deltaSmall
    simpa [Real.exp_neg] using bound
  have logBound : 2 ≤ Real.log delta⁻¹ := by
    rw [← Real.log_exp 2]
    exact Real.log_le_log (Real.exp_pos 2) inverse
  unfold wz1PaperRefinementFraction
  simp only [pow_one, one_div]
  rw [ENNReal.inv_le_inv]
  have two : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by
    norm_num
  rw [two]
  simpa [one_div] using ENNReal.ofReal_mono logBound

/-- Runtime data after the direct cropped fixed-grid step. -/
structure Prop62V4DirectCroppedFixedGridData
    {sigma sourceLoss workingEta delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta)
    (rho : WZ2PaperRequestedScale delta) where
  preparation :
    FixedGridPreparationData
      (rho := rho.1)
      cfg.shading
      cfg.extremal.delta_pos
  cleaned_extremal :
    WZ2PaperCroppedIsExtremal
      sigma workingEta cfg.family preparation.cleanup.refined
  line_class :
    WZ1PaperIsLineClass cfg.family
  cleaned_cubical :
    WZ1PaperIsCubicalShading preparation.cleanup.refined
  ordinary_bounded_base :
    HasBoundedBase cfg.family 4

/-- Package one direct metric-parent certificate as its canonical companion. -/
noncomputable def prop62V4DirectCroppedMetricCompanionOfCertificate
    {sigma sourceLoss fixedGridEta delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta}
    {rho : WZ2PaperRequestedScale delta}
    {parentConstant fiberConstant : ENNReal}
    (fixedGrid :
      Prop62V4DirectCroppedFixedGridData
        (workingEta := fixedGridEta) cfg rho)
    (certificate :
      PureWZ2Prop62MetricParentsV4Certificate
        fixedGrid.preparation.cleanup.refined
        rho
        (1 / 100 : ℝ)
        parentConstant fiberConstant) :
    Prop62V4MetricParentsRichCompanionData
      fixedGrid.preparation.cleanup.refined
      rho
      (1 / 100 : ℝ)
      parentConstant fiberConstant where
  certificate := certificate

/-- The direct cropped output keeps the fixed-grid, metric, and rich
witnesses on one common runtime instance. -/
structure Prop62V4DirectCroppedProducerData
    {sigma sourceLoss workingEta delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta)
    (rho : WZ2PaperRequestedScale delta)
    (hdelta : 0 < delta) where
  fixedGrid :
    Prop62V4DirectCroppedFixedGridData
      (workingEta := prop62V4DirectCroppedIntermediateLoss
        sourceLoss workingEta)
      cfg rho
  metricCertificate :
    PureWZ2Prop62MetricParentsV4Certificate
      fixedGrid.preparation.cleanup.refined
      rho
      (1 / 100 : ℝ)
      (pureWZ2Prop62MetricParentsV4Target delta 1 workingEta)
      (pureWZ2Prop62MetricParentsV4Target delta 1 workingEta)
  rich :
    Prop62V4RichCertificateCompanionData
      (eta := workingEta)
      (packetDensityExponent := 2)
      (cwaLossExponent := 51)
      (polylogExponent := 10)
      hdelta
      (prop62V4DirectCroppedMetricCompanionOfCertificate
        fixedGrid metricCertificate)

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

private theorem directCropped_bodyFamily_mass_subfamily_le
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

private theorem directCropped_exists_delta_power_le_refinementFraction
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

private theorem directCropped_dense_of_power_gap
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
    directCropped_bodyFamily_mass_subfamily_le refinement.selected
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

/-- Uniform threshold for the direct cropped fixed-grid cleanup. -/
structure Prop62V4DirectCroppedFixedGridThresholdReceipt
    (sourceLoss workingEta callerLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one_hundred : delta₀ ≤ 1 / 100
  prepare :
    ∀ {delta sigma : ℝ},
      0 < delta →
      delta ≤ delta₀ →
      ∀ (cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta),
        ∀ rho : WZ2PaperRequestedScale delta,
          Real.rpow delta (1 - callerLoss) ≤ rho.1 →
          rho.1 ≤ Real.rpow delta callerLoss →
            Nonempty
              (Prop62V4DirectCroppedFixedGridData
                (workingEta := workingEta) cfg rho)

/-- Threshold for constructing the direct fixed-grid cleanup directly from a
paper-facing grain configuration. -/
theorem prop62V4_direct_cropped_fixedGrid_threshold
    {sourceLoss workingEta callerLoss : ℝ}
    (sourceLossToWorking : sourceLoss < workingEta)
    (boundaryGap : 2 * sourceLoss < callerLoss)
    (hFixedGrid : FixedGridBoundaryRemovalStatement) :
    Nonempty
      (Prop62V4DirectCroppedFixedGridThresholdReceipt
        sourceLoss workingEta callerLoss) := by
  rcases hFixedGrid with
    ⟨gridConstant, outerConstant, gridConstantPos,
      gridConstantTop, outerConstantPos, outerConstantTop,
      fixedGrid⟩
  let absorptionConstant : ENNReal :=
    4 * (gridConstant + outerConstant)
  have absorptionConstantTop : absorptionConstant ≠ ⊤ := by
    dsimp only [absorptionConstant]
    exact ENNReal.mul_ne_top (by norm_num) <|
      ENNReal.add_ne_top.mpr ⟨gridConstantTop, outerConstantTop⟩
  have boundaryGapPos :
      0 < callerLoss - 2 * sourceLoss := by
    linarith
  rcases exists_delta_log_absorbed_ennreal
      absorptionConstant absorptionConstantTop boundaryGapPos
      (show 0 < (1 : ℕ) by norm_num) with
    ⟨boundaryDelta, boundaryDeltaPos, boundaryDeltaOne,
      absorbBoundary⟩
  rcases Subunit.exists_delta₀_mul_pow_le_one
      2 (by norm_num)
      (workingEta - sourceLoss)
      (by linarith) with
    ⟨densityDelta, densityDeltaPos, densityDeltaOne,
      absorbDensity⟩
  let delta₀ : ℝ :=
    min (1 / 100 : ℝ)
      (min (Real.exp (-2))
        (min boundaryDelta densityDelta))
  have delta₀Pos : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  refine
    ⟨{
      delta₀ := delta₀
      delta₀_pos := delta₀Pos
      delta₀_le_one_hundred := min_le_left _ _
      prepare := ?_
    }⟩
  intro delta sigma deltaPos deltaLe cfg rho rhoLower rhoUpper
  have deltaLeHundred : delta ≤ 1 / 100 :=
    deltaLe.trans (min_le_left _ _)
  have deltaLeOne : delta ≤ 1 :=
    deltaLeHundred.trans (by norm_num)
  have deltaLeExp : delta ≤ Real.exp (-2) :=
    deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeBoundary : delta ≤ boundaryDelta :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeDensity : delta ≤ densityDelta :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_right _ _)
  have rhoPos : 0 < rho.1 :=
    deltaPos.trans_le rho.2.1
  have ratioUpper :
      delta / rho.1 ≤ Real.rpow delta callerLoss := by
    rw [div_le_iff₀ rhoPos]
    calc
      delta = Real.rpow delta 1 := by simp
      _ =
          Real.rpow delta (1 - callerLoss) *
            Real.rpow delta callerLoss := by
        calc
          Real.rpow delta 1 =
              Real.rpow delta ((1 - callerLoss) + callerLoss) := by
            congr 1
            ring
          _ =
              Real.rpow delta (1 - callerLoss) *
                Real.rpow delta callerLoss :=
            Real.rpow_add deltaPos (1 - callerLoss) callerLoss
      _ ≤ rho.1 * Real.rpow delta callerLoss := by
        gcongr
        exact Real.rpow_nonneg deltaPos.le callerLoss
      _ = Real.rpow delta callerLoss * rho.1 := mul_comm _ _
  let sourceConstant : ENNReal :=
    Kakeya.realRpowENN delta (-sourceLoss)
  have sourceConstantFinite :
      finiteErrorConstant sourceConstant := by
    exact
      ⟨cfg.extremal.cwa_nearby_scales.2.1.1,
        cfg.extremal.cwa_nearby_scales.2.1.2⟩
  have levelBound :
      logarithmicLoss delta ≤
        2 * ENNReal.ofReal (1 + Real.log delta⁻¹) :=
    directCropped_directionLevelCount_le_logEnvelope
      deltaPos deltaLeOne
  have gridScale :
      ENNReal.ofReal (delta / rho.1) ≤
        Kakeya.realRpowENN delta callerLoss :=
    ENNReal.ofReal_mono ratioUpper
  have outerScale :
      ENNReal.ofReal rho.1 ≤
        Kakeya.realRpowENN delta callerLoss :=
    ENNReal.ofReal_mono rhoUpper
  have absorbedBoundary :
      absorptionConstant *
          ENNReal.ofReal (1 + Real.log delta⁻¹) ≤
        Kakeya.realRpowENN delta
          (-(callerLoss - 2 * sourceLoss)) := by
    simpa only [pow_one] using
      absorbBoundary delta deltaPos deltaLeBoundary
  have coefficientBound :
      gridConstant * sourceConstant *
            ENNReal.ofReal (delta / rho.1) *
            logarithmicLoss delta +
          outerConstant * sourceConstant *
            ENNReal.ofReal rho.1 *
            logarithmicLoss delta ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta sourceLoss := by
    let envelope : ENNReal :=
      ENNReal.ofReal (1 + Real.log delta⁻¹)
    let callerPower : ENNReal :=
      Kakeya.realRpowENN delta callerLoss
    let sourceInverse : ENNReal :=
      Kakeya.realRpowENN delta (-sourceLoss)
    let gapInverse : ENNReal :=
      Kakeya.realRpowENN delta
        (-(callerLoss - 2 * sourceLoss))
    have sourceCallerIdentity :
        sourceInverse * callerPower =
          Kakeya.realRpowENN delta
            (callerLoss - sourceLoss) := by
      dsimp only [sourceInverse, callerPower]
      rw [← realRpowENN_add deltaPos]
      congr 1
      ring
    have gapIdentity :
        gapInverse *
            Kakeya.realRpowENN delta
              (callerLoss - sourceLoss) =
          Kakeya.realRpowENN delta sourceLoss := by
      dsimp only [gapInverse]
      rw [← realRpowENN_add deltaPos]
      congr 1
      ring
    calc
      gridConstant * sourceConstant *
              ENNReal.ofReal (delta / rho.1) *
              logarithmicLoss delta +
            outerConstant * sourceConstant *
              ENNReal.ofReal rho.1 *
              logarithmicLoss delta ≤
          gridConstant * sourceConstant * callerPower *
              logarithmicLoss delta +
            outerConstant * sourceConstant * callerPower *
              logarithmicLoss delta := by
        gcongr
      _ =
          ((gridConstant + outerConstant) *
              logarithmicLoss delta) *
            (sourceInverse * callerPower) := by
        dsimp only [sourceConstant]
        ring
      _ ≤
          ((gridConstant + outerConstant) *
              (2 * envelope)) *
            (sourceInverse * callerPower) := by
        gcongr
      _ =
          ((1 / 2 : ENNReal) *
              (absorptionConstant * envelope)) *
            (sourceInverse * callerPower) := by
        have halfFour : (1 / 2 : ENNReal) * 4 = 2 := by
          rw [show (4 : ENNReal) = 2 * 2 by norm_num, one_div,
            ← mul_assoc,
            ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
            one_mul]
        dsimp only [absorptionConstant]
        calc
          ((gridConstant + outerConstant) * (2 * envelope)) *
                (sourceInverse * callerPower) =
              (2 * ((gridConstant + outerConstant) * envelope)) *
                (sourceInverse * callerPower) := by ring
          _ =
              (((1 / 2 : ENNReal) * 4) *
                  ((gridConstant + outerConstant) * envelope)) *
                (sourceInverse * callerPower) := by rw [halfFour]
          _ =
              ((1 / 2 : ENNReal) *
                  (4 * (gridConstant + outerConstant) * envelope)) *
                (sourceInverse * callerPower) := by ring
      _ ≤
          ((1 / 2 : ENNReal) * gapInverse) *
            (sourceInverse * callerPower) := by
        gcongr
      _ =
          (1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta sourceLoss := by
        rw [sourceCallerIdentity]
        calc
          ((1 / 2 : ENNReal) * gapInverse) *
                Kakeya.realRpowENN delta
                  (callerLoss - sourceLoss) =
              (1 / 2 : ENNReal) *
                (gapInverse *
                  Kakeya.realRpowENN delta
                    (callerLoss - sourceLoss)) := by ring
          _ =
              (1 / 2 : ENNReal) *
                Kakeya.realRpowENN delta sourceLoss := by
            rw [gapIdentity]
  have boundarySmall :
      gridConstant * sourceConstant *
              ENNReal.ofReal (delta / rho.1) *
              logarithmicLoss delta *
                (wz1PaperBodyFamily cfg.family).mass +
            outerConstant * sourceConstant *
              ENNReal.ofReal rho.1 *
              logarithmicLoss delta *
                (wz1PaperBodyFamily cfg.family).mass ≤
        cfg.shading.mass / 2 := by
    calc
      gridConstant * sourceConstant *
              ENNReal.ofReal (delta / rho.1) *
              logarithmicLoss delta *
                (wz1PaperBodyFamily cfg.family).mass +
            outerConstant * sourceConstant *
              ENNReal.ofReal rho.1 *
              logarithmicLoss delta *
                (wz1PaperBodyFamily cfg.family).mass =
          (gridConstant * sourceConstant *
                ENNReal.ofReal (delta / rho.1) *
                logarithmicLoss delta +
              outerConstant * sourceConstant *
                ENNReal.ofReal rho.1 *
                logarithmicLoss delta) *
            (wz1PaperBodyFamily cfg.family).mass := by
        ring
      _ ≤
          ((1 / 2 : ENNReal) *
              Kakeya.realRpowENN delta sourceLoss) *
            (wz1PaperBodyFamily cfg.family).mass := by
        gcongr
      _ =
          (1 / 2 : ENNReal) *
            (Kakeya.realRpowENN delta sourceLoss *
              (wz1PaperBodyFamily cfg.family).mass) := by
        ring
      _ ≤ (1 / 2 : ENNReal) * cfg.shading.mass := by
        gcongr
        exact cfg.extremal.dense
      _ = cfg.shading.mass / 2 := by
        simp only [ENNReal.div_eq_inv_mul, mul_one]
  have boundary :=
    fixedGrid delta rho.1 deltaPos deltaLeHundred rhoPos rho.2.2
      rho.2.1 cfg.family cfg.line_class cfg.shading cfg.cubical
      sourceConstant sourceConstantFinite cfg.top_level_cwa
  dsimp only at boundary
  rcases boundary.2.2 boundarySmall with ⟨cleanup⟩
  have refinementRetained :
      wz1PaperRefinementFraction delta 1 *
          cfg.shading.mass ≤
        cleanup.refined.mass := by
    calc
      wz1PaperRefinementFraction delta 1 *
            cfg.shading.mass ≤
          (1 / 2 : ENNReal) * cfg.shading.mass := by
        gcongr
        exact
          directCropped_refinementFraction_one_le_half
            deltaPos deltaLeExp
      _ = cfg.shading.mass / 2 := by
        simp only [ENNReal.div_eq_inv_mul, mul_one]
      _ ≤ cleanup.refined.mass :=
        cleanup.mass_retention
  let preparation :
      FixedGridPreparationData
        (rho := rho.1)
        cfg.shading
        cfg.extremal.delta_pos :=
    {
      cleanup := cleanup
      refinement_retained := refinementRetained
    }
  have densityPower :
      Kakeya.realRpowENN delta workingEta ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta sourceLoss := by
    apply pure_wz2_pruning_power_bound deltaPos
    exact
      absorbDensity delta deltaPos deltaLeDensity
  have cleanedDense :
      cleanup.refined.IsLambdaDense
        (Kakeya.realRpowENN delta workingEta) := by
    calc
      Kakeya.realRpowENN delta workingEta *
            (wz1PaperBodyFamily cfg.family).mass ≤
          ((1 / 2 : ENNReal) *
              Kakeya.realRpowENN delta sourceLoss) *
            (wz1PaperBodyFamily cfg.family).mass := by
        gcongr
      _ =
          (1 / 2 : ENNReal) *
            (Kakeya.realRpowENN delta sourceLoss *
              (wz1PaperBodyFamily cfg.family).mass) := by
        ring
      _ ≤ (1 / 2 : ENNReal) * cfg.shading.mass := by
        gcongr
        exact cfg.extremal.dense
      _ = cfg.shading.mass / 2 := by
        simp only [ENNReal.div_eq_inv_mul, mul_one]
      _ ≤ cleanup.refined.mass :=
        cleanup.mass_retention
  have cleanedUnionSubset :
      cleanup.refined.union ⊆ cfg.shading.union := by
    rintro point ⟨index, pointMem⟩
    exact ⟨index, cleanup.subshading index pointMem⟩
  let weakened :=
    cfg.extremal.mono_loss sourceLossToWorking.le
  let cleanedExtremal :
      WZ2PaperCroppedIsExtremal
        sigma workingEta
        cfg.family cleanup.refined :=
    {
      delta_pos := cfg.extremal.delta_pos
      delta_le_one := cfg.extremal.delta_le_one
      nonempty := cfg.extremal.nonempty
      cwa_nearby_scales := weakened.cwa_nearby_scales
      cubical := cleanup.cubical
      dense := cleanedDense
      volume_upper :=
        (measure_mono cleanedUnionSubset).trans weakened.volume_upper
    }
  exact
    ⟨{
      preparation := preparation
      cleaned_extremal := cleanedExtremal
      line_class := cfg.line_class
      cleaned_cubical := cleanup.cubical
      ordinary_bounded_base := cfg.bounded_base
    }⟩

/-- Uniform direct-cropped producer receipt from one paper-facing C2 grain
configuration. -/
structure Prop62V4DirectCroppedProducerThresholdReceipt
    {sigma outputLoss sourceLoss workingEta : ℝ} where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one_hundred : delta₀ ≤ 1 / 100
  produce :
    ∀ {delta : ℝ}, ∀ (hdelta : 0 < delta),
      delta ≤ delta₀ →
      ∀ (cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta),
        ∀ rho : WZ2PaperRequestedScale delta,
          Real.rpow delta (1 - outputLoss) ≤ rho.1 →
          rho.1 ≤ Real.rpow delta outputLoss →
            Nonempty
              (Prop62V4DirectCroppedProducerData
                (workingEta := workingEta) cfg rho hdelta)

/-- Direct cropped runtime producer from a paper-facing `PureWZ2C2GrainConfiguration`. -/
theorem prop62V4_direct_cropped_producer
    {sigma outputLoss sourceLoss workingEta : ℝ}
    (sourceLossPos : 0 < sourceLoss)
    (outputLossPos : 0 < outputLoss)
    (sourceLoss_output_budget : 2 * sourceLoss < outputLoss)
    (sourceLoss_lt_workingEta : sourceLoss < workingEta)
    (workingEtaPos : 0 < workingEta)
    (metricLoss :
      (pureWZ2Prop62MetricParentsV4CWAPower 1 : ℝ) * workingEta ≤
        outputLoss / 100)
    (packetExponentLtOne : ((2 : ℝ) * workingEta) < 1)
    (hFixedGrid : FixedGridBoundaryRemovalStatement)
    (hTreeCleanup : OnePassTreeCleanupStatement) :
    Nonempty
      (Prop62V4DirectCroppedProducerThresholdReceipt
        (sigma := sigma) (outputLoss := outputLoss)
        (sourceLoss := sourceLoss) (workingEta := workingEta)) := by
  let intermediateLoss :=
    prop62V4DirectCroppedIntermediateLoss sourceLoss workingEta
  have sourceLossToIntermediate : sourceLoss < intermediateLoss := by
    change sourceLoss < (sourceLoss + workingEta) / 2
    linarith
  have intermediateToWorking : intermediateLoss < workingEta := by
    change (sourceLoss + workingEta) / 2 < workingEta
    linarith
  rcases
      prop62V4_direct_cropped_fixedGrid_threshold
        sourceLossToIntermediate
        sourceLoss_output_budget
        hFixedGrid
    with ⟨fixedGridThreshold⟩
  let cleanupOracle :=
    onePassTreeCleanupStatement_to_pureWZ2Prop62CleanupOracle
      hTreeCleanup
  let metricThreshold :=
    pureWZ2Prop62MetricParentsV4Threshold
      1 outputLoss workingEta (1 / 100 : ℝ)
      (by norm_num) outputLossPos workingEtaPos metricLoss
      (by norm_num)
  rcases
      exists_prop62V4RichCertificateCompanion
        cleanupOracle 1 8 workingEta workingEtaPos packetExponentLtOne
    with
    ⟨richDelta, richDeltaPos, richDeltaLe, produceRich⟩
  rcases
      directCropped_exists_delta_power_le_refinementFraction
        (workingEta - intermediateLoss)
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
        (min richDelta
          (min densityThreshold separationThreshold)))
  have metricThresholdPos : 0 < metricThreshold := by
    dsimp only [metricThreshold]
    exact
      pureWZ2Prop62MetricParentsV4Threshold_pos
        1 outputLoss workingEta (1 / 100 : ℝ)
        (by norm_num) outputLossPos workingEtaPos metricLoss
        (by norm_num)
  have delta₀Pos : 0 < delta₀ := by
    dsimp only [delta₀]
    exact
      lt_min fixedGridThreshold.delta₀_pos <|
        lt_min metricThresholdPos <|
          lt_min richDeltaPos <|
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
  intro delta hdelta hdeltaLe cfg rho rhoLower rhoUpper
  have hFixedGridDelta : delta ≤ fixedGridThreshold.delta₀ :=
    hdeltaLe.trans (min_le_left _ _)
  have hMetricDelta : delta ≤ metricThreshold :=
    hdeltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
  have hRichDelta : delta ≤ richDelta :=
    hdeltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have hDensityDelta : delta ≤ densityThreshold :=
    hdeltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have hSeparationDelta : delta ≤ separationThreshold :=
    hdeltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
  rcases
      fixedGridThreshold.prepare hdelta hFixedGridDelta
        cfg rho rhoLower rhoUpper
    with
    ⟨fixedGrid⟩
  let cleanedWorking :=
    fixedGrid.cleaned_extremal.mono_loss intermediateToWorking.le
  have cleanedCWA :
      WZ2PaperPureCWAAtNearbyScales cfg.family
        (pureWZ2Prop62CallerCstar delta 1 workingEta) := by
    simpa [pureWZ2Prop62CallerCstar, pureWZ2Prop62CallerLoss] using
      cleanedWorking.cwa_nearby_scales
  have cleanedDense :
      fixedGrid.preparation.cleanup.refined.IsLambdaDense
        (Kakeya.realRpowENN delta workingEta) := by
    simpa using cleanedWorking.dense
  rcases
      pureWZ2_prop62_metric_parents_v4_pipeline_of_bounded_base
        1 outputLoss workingEta (1 / 100 : ℝ) delta
        cfg.family fixedGrid.preparation.cleanup.refined rho
        (by norm_num) outputLossPos workingEtaPos metricLoss (by norm_num)
        hdelta hMetricDelta
        fixedGrid.cleaned_extremal.nonempty
        fixedGrid.ordinary_bounded_base
        fixedGrid.line_class fixedGrid.cleaned_cubical
        cleanedCWA (by simpa using cleanedDense)
        rhoLower rhoUpper cleanupOracle
    with
    ⟨metricCertificate⟩
  have parentConstantLe :
      Kakeya.realRpowENN delta (-8 * workingEta) ≤
        Kakeya.realRpowENN delta (-(8 : ℝ) * workingEta) := by
    rfl
  have fiberConstantLe :
      Kakeya.realRpowENN delta (-8 * workingEta) ≤
        Kakeya.realRpowENN delta (-(8 : ℝ) * workingEta) := by
    rfl
  have refinedDense :
      (prop62V4DirectCroppedMetricCompanionOfCertificate
        fixedGrid metricCertificate
      ).metric.refinement.refined.IsLambdaDense
        (Kakeya.realRpowENN delta workingEta) := by
    change
      metricCertificate.toMetricData.refinement.refined.IsLambdaDense
        (Kakeya.realRpowENN delta workingEta)
    apply
      PureWZ2Prop62MetricParentsV4Certificate.toMetricData_refined_dense
        metricCertificate
    exact
      have raw :
          metricCertificate.refinement.refined.IsLambdaDense
            (Kakeya.realRpowENN delta workingEta) :=
        directCropped_dense_of_power_gap
          hdelta fixedGrid.cleaned_extremal.dense
          metricCertificate.refinement
          (absorbDensity delta hdelta hDensityDelta)
      raw
  have scaleSeparation : 18 * delta ≤ rho.1 := by
    calc
      18 * delta = 18 * Real.rpow delta 1 := by simp
      _ ≤ Real.rpow delta (1 - outputLoss) :=
        separate delta hdelta hSeparationDelta
      _ ≤ rho.1 := rhoLower
  let metricCompanion :=
    prop62V4DirectCroppedMetricCompanionOfCertificate
      fixedGrid metricCertificate
  have coarseCell :
      ∀ sourceIndex cell,
        wz1PaperGridCube delta cell ⊆
            metricCompanion.metric.refinement.refined.carrier sourceIndex →
          ∃! coarseCell,
            wz1PaperGridCube delta cell ⊆
                wz1PaperGridCube rho.1 coarseCell ∧
              wz1PaperGridCube rho.1 coarseCell ⊆
                wz1PaperTubeCarrier
                  (metricCompanion.metric.scaleData.coarse.tube
                    (metricCompanion.metric.scaleData.cover.parent
                      sourceIndex)) :=
    Prop62V4MetricParentsRichCompanionData.fixedGrid_coarse_cell
      fixedGrid.preparation.cleanup metricCompanion scaleSeparation
  rcases
      produceRich delta hdelta hRichDelta
        cfg.family fixedGrid.preparation.cleanup.refined rho
        (1 / 100 : ℝ)
        (pureWZ2Prop62MetricParentsV4Target delta 1 workingEta)
        (pureWZ2Prop62MetricParentsV4Target delta 1 workingEta)
        metricCompanion
        le_rfl le_rfl
        (by simpa only [Nat.cast_one, one_mul] using refinedDense)
        coarseCell with
    ⟨rich⟩
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
