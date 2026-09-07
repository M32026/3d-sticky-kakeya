import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63UniformFullGrainStepProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63Lemma43
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63AlignedPhase1Candidate
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentStepArithmetic
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ExtremalOneScalePlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63NestedPointCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RobustTauLocalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalGrainAmbientPlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SourceWitnessCoarseMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentPlaneIncidence

/-!
# Pre-runtime full-grain schedules

The scalar loss hierarchy and Phase-1 threshold are compiled independently
from the runtime full-grain assembly.  Editing the runtime proof therefore
reuses these relatively expensive, family-free arithmetic certificates.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

/-- One completed Lemma 4.12 scale on the current ambient family.  The plane
map is a restriction of the caller's map, and both the variation estimate and
the local AD estimate live on the same restored-extremal shading. -/
structure Proposition63ExtremalOneScaleFullGrainData
    {delta sigma incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (current : WZ1PaperTubeShading family)
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (outputLoss queryScale spatialScale variationScale : ℝ) where
  shading : WZ1PaperTubeShading family
  subshading : PaperIsSubshading shading current
  cubical : WZ1PaperIsCubicalShading shading
  planeMap : PaperWZ1WeakPlaneMapData shading incidence
  same_plane_map : planeMap.planeMap = currentMap.planeMap
  variation : ∀ first ∈ shading.union, ∀ second ∈ shading.union,
    dist first second ≤ spatialScale →
      dist (planeMap.planeMap first) (planeMap.planeMap second) ≤
        variationScale
  local_ad : ∀ point ∈ shading.union,
    IsADSet1
      (scalarProjection (planeMap.planeMap point)
        (shading.union ∩ Metric.closedBall point (Real.sqrt queryScale)))
      queryScale (1 - sigma)
      (Kakeya.realRpowENN delta (-outputLoss))
  massLoss : ENNReal
  massLoss_pos : 0 < massLoss
  massLoss_ne_top : massLoss ≠ ⊤
  mass_retention : massLoss⁻¹ * current.mass ≤ shading.mass
  extremal : WZ2PaperCroppedIsExtremal
    sigma outputLoss family shading

/-- Abstract pre-runtime contract for one restored Lemma 4.12 step.  The
input loss and scale threshold are fixed before the runtime family, shading,
map, and target coordinate.  The coordinate hypotheses record the genuine
positive, small, grid-compatible regime used by the full-grain construction. -/
structure Proposition63ExtremalOneScaleFullGrainScheduleData
    (sigma outputLoss : ℝ) where
  rootSourceLoss : ℝ
  rootNormalizationLoss : ℝ
  producerWindowLoss : ℝ
  phase1StickyLoss : ℝ
  inputLoss : ℝ
  delta₀ : ℝ
  rootSourceLoss_pos : 0 < rootSourceLoss
  rootNormalizationLoss_pos : 0 < rootNormalizationLoss
  rootSourceLoss_le_half : rootSourceLoss ≤ rootNormalizationLoss / 2
  producerWindowLoss_pos : 0 < producerWindowLoss
  producerWindowLoss_le_sticky : producerWindowLoss ≤ phase1StickyLoss
  phase1StickyLoss_le_output : phase1StickyLoss ≤ outputLoss
  inputLoss_pos : 0 < inputLoss
  inputLoss_le_output : inputLoss ≤ outputLoss
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  run : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    ∀ {ambientSourceLoss ambientNormalizationLoss : ℝ}
      {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
      {ambientShading : WZ1PaperTubeShading ambientFamily}
      {normalizationExponent : ℕ},
      ∀ (_ambientReentry : PureWZ2PropStickyReentryData
          (sigma := sigma) ambientShading normalizationExponent ambientSourceLoss
            ambientNormalizationLoss)
        (_ambientSource_le : ambientSourceLoss ≤ rootSourceLoss)
        (_ambientNormalization_le :
          ambientNormalizationLoss ≤ rootNormalizationLoss)
        (current : WZ1PaperTubeShading ambientFamily)
        (_currentExtremal : WZ2PaperCroppedIsExtremal
          sigma inputLoss ambientFamily current)
        (_currentSub : PaperIsSubshading current ambientShading)
        {incidence : ℝ}
        (currentMap : PaperWZ1WeakPlaneMapData current incidence)
        (coefficient : NNReal),
        LipschitzWith coefficient
          (fun point : {point : Point3 // point ∈ current.union} =>
            currentMap.planeMap point) →
        ∀ queryScale spatialScale variationScale : ℝ,
          0 < queryScale →
          queryScale ≤ 1 / 4 →
          48 * delta ^ 2 ≤ queryScale →
          Real.rpow delta (1 - producerWindowLoss) ≤
            alignedCoarseScale delta queryScale →
          Real.rpow delta phase1StickyLoss ≤
            alignedCoarseScale delta queryScale →
          alignedCoarseScale delta queryScale ≤
            Real.rpow delta producerWindowLoss →
          50 * delta ≤ Real.sqrt queryScale →
          Real.sqrt queryScale ≤ 1 →
          1 ≤ (coefficient : ℝ) →
          (coefficient : ℝ) * spatialScale ≤ variationScale →
          Nonempty (Proposition63ExtremalOneScaleFullGrainData
            (sigma := sigma) current currentMap outputLoss queryScale
              spatialScale variationScale)

/-- The concrete paper-order loss hierarchy for one full-grain coordinate.
All losses are fixed before the runtime extremizer.  The Node-3 source and
normalization losses are retained verbatim, while the remaining losses are
small rational multiples of one common budget. -/
structure Proposition63FullGrainOneScaleLossData
    (sigma outputLoss : ℝ) where
  producerWindowLoss : ℝ
  phase1StickyLoss : ℝ
  phase1Loss : ℝ
  sourceADLoss : ℝ
  criticalLoss : ℝ
  queryLoss : ℝ
  middleLoss : ℝ
  finalLoss : ℝ
  producer : Proposition63RichStickyKernelScheduleData
    sigma producerWindowLoss
  rootNormalizationLoss : ℝ
  rootSourceLoss : ℝ
  densityLoss : ℝ
  inputLoss : ℝ
  dyadicLoss : ℝ
  weightLoss : ℝ
  rootNormalizationLoss_eq :
    rootNormalizationLoss = producer.sourceLoss / 16
  rootSourceLoss_eq : rootSourceLoss = rootNormalizationLoss / 4
  densityLoss_eq : densityLoss = rootNormalizationLoss * 2
  inputLoss_eq : inputLoss = rootNormalizationLoss
  dyadicLoss_eq : dyadicLoss = rootNormalizationLoss * 2
  weightLoss_eq : weightLoss = producer.sourceLoss / 2
  sigma_pos : 0 < sigma
  sigma_lt_one : sigma < 1
  rootSourceLoss_pos : 0 < rootSourceLoss
  rootNormalizationLoss_pos : 0 < rootNormalizationLoss
  rootSourceLoss_le_half : rootSourceLoss ≤ rootNormalizationLoss / 2
  inputLoss_pos : 0 < inputLoss
  inputLoss_le_output : inputLoss ≤ outputLoss
  inputLoss_lt_dyadic : inputLoss < dyadicLoss
  producerWindowLoss_pos : 0 < producerWindowLoss
  producerWindowLoss_le_sticky : producerWindowLoss ≤ phase1StickyLoss
  phase1StickyLoss_le_output : phase1StickyLoss ≤ outputLoss
  rootSource_lt_density : rootSourceLoss < densityLoss
  density_add_dyadic_lt_weight : densityLoss + dyadicLoss < weightLoss
  weight_lt_reentry : weightLoss < producer.sourceLoss
  two_rootNormalization_le_reentry :
    2 * rootNormalizationLoss ≤ producer.sourceLoss
  input_le_dyadic : inputLoss ≤ dyadicLoss
  dyadic_pos : 0 < dyadicLoss
  dyadic_le_reentry : dyadicLoss ≤ producer.sourceLoss
  reentry_regularization_gap :
    0 < producer.sourceLoss - weightLoss - 2 * rootNormalizationLoss
  reentryNormalization_le_phase1 :
    producer.normalizationLoss ≤ phase1Loss
  reentryNormalization_lt_phase1 :
    producer.normalizationLoss < phase1Loss
  reentryNormalization_le_sticky :
    producer.normalizationLoss ≤ phase1StickyLoss
  reentryNormalization_lt_half_sigma :
    producer.normalizationLoss < sigma / 2
  phase1Loss_pos : 0 < phase1Loss
  sticky_small :
    6 * phase1StickyLoss < sigma + 2 * producer.normalizationLoss
  sourceADLoss_pos : 0 < sourceADLoss
  sticky_le_sourceAD : 3 * phase1StickyLoss ≤ sourceADLoss
  sourceAD_lt_critical : sourceADLoss < criticalLoss
  criticalLoss_pos : 0 < criticalLoss
  dyadic_le_critical : dyadicLoss ≤ criticalLoss
  rootNormalization_le_critical : rootNormalizationLoss ≤ criticalLoss
  density_gap :
    0 < criticalLoss - producer.normalizationLoss - weightLoss
  critical_lt_query : criticalLoss < queryLoss
  query_le_middle : queryLoss ≤ middleLoss
  query_lt_middle : queryLoss < middleLoss
  middle_pos : 0 < middleLoss
  middle_lt_final : middleLoss < finalLoss
  final_pos : 0 < finalLoss
  final_lt_output : finalLoss < outputLoss
  boundary_gap : 2 * middleLoss < (1 - phase1StickyLoss) / 2

/-- Select the complete loss hierarchy before the runtime scale and family. -/
theorem proposition63_full_grain_one_scale_losses
    (sigma : ℝ) (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ) (houtputLoss : 0 < outputLoss) :
    Nonempty (Proposition63FullGrainOneScaleLossData sigma outputLoss) := by
  let budget : ℝ := min outputLoss (min sigma 1)
  have budgetPos : 0 < budget := by
    dsimp only [budget]
    exact lt_min houtputLoss (lt_min critical.sigma_pos zero_lt_one)
  have budgetLeOutput : budget ≤ outputLoss := min_le_left _ _
  have budgetLeSigma : budget ≤ sigma :=
    (min_le_right _ _).trans (min_le_left _ _)
  have budgetLeOne : budget ≤ 1 :=
    (min_le_right _ _).trans (min_le_right _ _)
  let producerWindowLoss : ℝ := budget / 128
  let phase1StickyLoss : ℝ := 2 * budget / 128
  let phase1Loss : ℝ := 3 * budget / 128
  let sourceADLoss : ℝ := 6 * budget / 128
  let criticalLoss : ℝ := 7 * budget / 128
  let queryLoss : ℝ := 8 * budget / 128
  let middleLoss : ℝ := 9 * budget / 128
  let finalLoss : ℝ := 10 * budget / 128
  have producerPos : 0 < producerWindowLoss := by
    dsimp only [producerWindowLoss]
    positivity
  have producerOne : producerWindowLoss ≤ 1 := by
    dsimp only [producerWindowLoss]
    linarith
  rcases proposition63_rich_sticky_kernel sigma critical producerWindowLoss
      producerPos producerOne with ⟨producer⟩
  let rootNormalizationLoss : ℝ := producer.sourceLoss / 16
  let rootSourceLoss : ℝ := rootNormalizationLoss / 4
  let densityLoss : ℝ := rootNormalizationLoss * 2
  let inputLoss : ℝ := rootNormalizationLoss
  let dyadicLoss : ℝ := rootNormalizationLoss * 2
  let weightLoss : ℝ := producer.sourceLoss / 2
  have producerSourcePos : 0 < producer.sourceLoss :=
    producer.sourceLoss_pos
  have producerNormalizationLt :
      producer.normalizationLoss < producerWindowLoss :=
    producer.normalizationLoss_lt_output
  have producerNormalizationUpper :
      producer.normalizationLoss < budget / 128 := by
    simpa only [producerWindowLoss] using producerNormalizationLt
  have producerSourceLeNormalization :
      producer.sourceLoss ≤ producer.normalizationLoss / 2 :=
    producer.sourceLoss_le_half
  have rootNormalizationPos : 0 < rootNormalizationLoss := by
    dsimp only [rootNormalizationLoss]
    positivity
  have producerSourceUpper : producer.sourceLoss ≤ budget / 256 := by
    calc
      producer.sourceLoss ≤ producer.normalizationLoss / 2 :=
        producerSourceLeNormalization
      _ ≤ producerWindowLoss / 2 := by linarith
      _ = budget / 256 := by
        dsimp only [producerWindowLoss]
        ring
  refine ⟨{
    producerWindowLoss := producerWindowLoss
    phase1StickyLoss := phase1StickyLoss
    phase1Loss := phase1Loss
    sourceADLoss := sourceADLoss
    criticalLoss := criticalLoss
    queryLoss := queryLoss
    middleLoss := middleLoss
    finalLoss := finalLoss
    producer := producer
    rootNormalizationLoss := rootNormalizationLoss
    rootSourceLoss := rootSourceLoss
    densityLoss := densityLoss
    inputLoss := inputLoss
    dyadicLoss := dyadicLoss
    weightLoss := weightLoss
    rootNormalizationLoss_eq := rfl
    rootSourceLoss_eq := rfl
    densityLoss_eq := rfl
    inputLoss_eq := rfl
    dyadicLoss_eq := rfl
    weightLoss_eq := rfl
    sigma_pos := critical.sigma_pos
    sigma_lt_one := critical.sigma_lt_one
    rootSourceLoss_pos := by
      dsimp only [rootSourceLoss, rootNormalizationLoss]
      positivity
    rootNormalizationLoss_pos := rootNormalizationPos
    rootSourceLoss_le_half := by
      dsimp only [rootSourceLoss]
      linarith
    inputLoss_pos := by
      dsimp only [inputLoss, rootNormalizationLoss]
      positivity
    inputLoss_le_output := by
      dsimp only [inputLoss, rootNormalizationLoss]
      calc
        producer.sourceLoss / 16 ≤ budget / 256 / 16 :=
          div_le_div_of_nonneg_right producerSourceUpper (by norm_num)
        _ ≤ budget := by
          rw [div_div]
          apply div_le_self budgetPos.le
          norm_num
        _ ≤ outputLoss := budgetLeOutput
    inputLoss_lt_dyadic := by
      dsimp only [inputLoss, dyadicLoss]
      linarith [rootNormalizationPos]
    producerWindowLoss_pos := producerPos
    producerWindowLoss_le_sticky := by
      dsimp only [producerWindowLoss, phase1StickyLoss]
      linarith
    phase1StickyLoss_le_output := by
      dsimp only [phase1StickyLoss]
      linarith
    rootSource_lt_density := by
      dsimp only [rootSourceLoss, densityLoss, rootNormalizationLoss]
      linarith [producerSourcePos]
    density_add_dyadic_lt_weight := by
      dsimp only [densityLoss, dyadicLoss, weightLoss, rootNormalizationLoss]
      linarith
    weight_lt_reentry := by
      dsimp only [weightLoss]
      linarith
    two_rootNormalization_le_reentry := by
      dsimp only [rootNormalizationLoss]
      linarith
    input_le_dyadic := by
      dsimp only [inputLoss, dyadicLoss, rootNormalizationLoss]
      linarith [producerSourcePos]
    dyadic_pos := by
      dsimp only [dyadicLoss, rootNormalizationLoss]
      positivity
    dyadic_le_reentry := by
      dsimp only [dyadicLoss, rootNormalizationLoss]
      linarith
    reentry_regularization_gap := by
      dsimp only [weightLoss, rootNormalizationLoss]
      linarith
    reentryNormalization_le_phase1 := by
      calc
        producer.normalizationLoss ≤ producerWindowLoss :=
          producerNormalizationLt.le
        _ ≤ phase1Loss := by
          dsimp only [producerWindowLoss, phase1Loss]
          linarith
    reentryNormalization_lt_phase1 := by
      calc
        producer.normalizationLoss < producerWindowLoss :=
          producerNormalizationLt
        _ < phase1Loss := by
          dsimp only [producerWindowLoss, phase1Loss]
          linarith
    reentryNormalization_le_sticky := by
      calc
        producer.normalizationLoss ≤ producerWindowLoss :=
          producerNormalizationLt.le
        _ ≤ phase1StickyLoss := by
          dsimp only [producerWindowLoss, phase1StickyLoss]
          linarith
    reentryNormalization_lt_half_sigma := by
      calc
        producer.normalizationLoss < producerWindowLoss :=
          producerNormalizationLt
        _ = budget / 128 := rfl
        _ ≤ sigma / 128 :=
          div_le_div_of_nonneg_right budgetLeSigma (by norm_num)
        _ < sigma / 2 := by
          exact div_lt_div_of_pos_left critical.sigma_pos (by norm_num)
            (by norm_num)
    phase1Loss_pos := by dsimp only [phase1Loss]; positivity
    sticky_small := by
      dsimp only [phase1StickyLoss, producerWindowLoss]
      linarith
    sourceADLoss_pos := by dsimp only [sourceADLoss]; positivity
    sticky_le_sourceAD := by
      dsimp only [phase1StickyLoss, sourceADLoss]
      linarith
    sourceAD_lt_critical := by
      dsimp only [sourceADLoss, criticalLoss]
      linarith
    criticalLoss_pos := by dsimp only [criticalLoss]; positivity
    dyadic_le_critical := by
      dsimp only [dyadicLoss, rootNormalizationLoss, criticalLoss]
      calc
        producer.sourceLoss / 16 * 2 ≤ budget / 256 / 16 * 2 := by gcongr
        _ ≤ 7 * budget / 128 := by linarith
    rootNormalization_le_critical := by
      dsimp only [rootNormalizationLoss, criticalLoss]
      calc
        producer.sourceLoss / 16 ≤ budget / 256 / 16 :=
          div_le_div_of_nonneg_right producerSourceUpper (by norm_num)
        _ ≤ 7 * budget / 128 := by linarith
    density_gap := by
      dsimp only [criticalLoss, weightLoss]
      have combinedUpper : producer.normalizationLoss + producer.sourceLoss / 2 ≤
          budget / 128 + budget / 256 / 2 := by gcongr
      linarith
    critical_lt_query := by
      dsimp only [criticalLoss, queryLoss]
      linarith
    query_le_middle := by
      dsimp only [queryLoss, middleLoss]
      linarith
    query_lt_middle := by
      dsimp only [queryLoss, middleLoss]
      linarith
    middle_pos := by dsimp only [middleLoss]; positivity
    middle_lt_final := by
      dsimp only [middleLoss, finalLoss]
      linarith
    final_pos := by dsimp only [finalLoss]; positivity
    final_lt_output := by
      dsimp only [finalLoss]
      calc
        10 * budget / 128 ≤ 10 * outputLoss / 128 := by gcongr
        _ < outputLoss := by linarith
    boundary_gap := by
      dsimp only [middleLoss, phase1StickyLoss]
      have leftUpper : 2 * (9 * budget / 128) ≤ 18 / 128 := by
        calc
          2 * (9 * budget / 128) ≤ 2 * (9 * 1 / 128) := by gcongr
          _ = 18 / 128 := by ring
      have rightLower : (1 - 2 * budget / 128) / 2 ≥
          (1 - 2 * 1 / 128) / 2 := by gcongr
      linarith
  }⟩

/-- Uniform small-scale package for the scalar hypotheses internal to the
aligned Phase-1 call.  Only the upper Node-3 window is needed at runtime. -/
structure Proposition63FullGrainPhase1ThresholdData
    (sigma producerLoss stickyLoss reentryNormalizationLoss : ℝ) where
  logScale : ℝ
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  run : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    ∀ rho : WZ2PaperRequestedScale delta,
      rho.1 ≤ Real.rpow delta producerLoss →
      rho.1 ≤ 1 / 10000 ∧
      rho.1 ≤ (3 : ℝ) ^ (-(20 / sigma)) ∧
      (PureWZ2.h_avg_m_val sigma reentryNormalizationLoss rho.1 : ℝ) *
          rho.1 ^ (sigma - 3 * stickyLoss) < 1 / 8 ∧
      rho.1 ≤ logScale ∧
      (∀ epsilon₁ : ℝ, epsilon₁ =
          (sigma - 2 * reentryNormalizationLoss) / 20 →
        0 < epsilon₁ → ∀ scale : ℝ, 0 < scale → scale ≤ logScale →
        ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / scale ^ 3 →
          Real.rpow scale epsilon₁ *
            (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108) ∧
      rho.1 ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ)

theorem proposition63_full_grain_phase1_threshold
    (sigma producerLoss stickyLoss reentryNormalizationLoss : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hproducer : 0 < producerLoss)
    (hreentry : 0 < reentryNormalizationLoss)
    (hreentryHalf : reentryNormalizationLoss < sigma / 2)
    (hsticky : 0 ≤ stickyLoss)
    (haverageGap : 6 * stickyLoss <
      sigma + 2 * reentryNormalizationLoss) :
    Nonempty (Proposition63FullGrainPhase1ThresholdData
      sigma producerLoss stickyLoss reentryNormalizationLoss) := by
  rcases PureWZ2.h_avg_exponent_arithmetic sigma
      reentryNormalizationLoss stickyLoss hsigma hsigmaOne hreentry
      hreentryHalf hsticky (by linarith) with
    ⟨averageScale, averageScalePos, averageScaleOne, averageBound⟩
  have epsilonPos :
      0 < (sigma - 2 * reentryNormalizationLoss) / 20 := by
    linarith
  rcases cordoba_log_absorption_exists epsilonPos with
    ⟨logScale, logScalePos, logScaleOne, logBound⟩
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := (1 / 10000 : ℝ)) (s := producerLoss)
      (by norm_num) hproducer with
    ⟨smallDelta, smallDeltaPos, smallDeltaOne, smallBound⟩
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := (3 : ℝ) ^ (-(20 / sigma)))
      (s := producerLoss) (by positivity) hproducer with
    ⟨propertyDelta, propertyDeltaPos, propertyDeltaOne, propertyBound⟩
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := averageScale) (s := producerLoss) averageScalePos
      hproducer with
    ⟨averageDelta, averageDeltaPos, averageDeltaOne, averageScaleBound⟩
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := logScale) (s := producerLoss) logScalePos hproducer with
    ⟨logDelta, logDeltaPos, logDeltaOne, logScaleBound⟩
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
      (s := producerLoss) (by positivity) hproducer with
    ⟨inverseCubeDelta, inverseCubeDeltaPos, inverseCubeDeltaOne,
      inverseCubeBound⟩
  let delta₀ := min smallDelta <| min propertyDelta <| min averageDelta <|
    min logDelta inverseCubeDelta
  refine ⟨{
    logScale := logScale
    delta₀ := delta₀
    delta₀_pos := by
      dsimp only [delta₀]
      exact lt_min smallDeltaPos <| lt_min propertyDeltaPos <|
        lt_min averageDeltaPos <| lt_min logDeltaPos inverseCubeDeltaPos
    delta₀_le_one := (min_le_left _ _).trans smallDeltaOne
    run := ?_
  }⟩
  intro delta deltaPos deltaLe rho rhoUpper
  have deltaSmall : delta ≤ smallDelta :=
    deltaLe.trans (min_le_left _ _)
  have deltaProperty : delta ≤ propertyDelta :=
    deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
  have deltaAverage : delta ≤ averageDelta :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have deltaLog : delta ≤ logDelta :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have deltaInverseCube : delta ≤ inverseCubeDelta :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
  have rhoAverage : rho.1 ≤ averageScale :=
    rhoUpper.trans (averageScaleBound delta deltaPos deltaAverage)
  exact ⟨
    rhoUpper.trans (smallBound delta deltaPos deltaSmall),
    rhoUpper.trans (propertyBound delta deltaPos deltaProperty),
    averageBound rho.1 (deltaPos.trans_le rho.2.1) rhoAverage,
    rhoUpper.trans (logScaleBound delta deltaPos deltaLog),
    (fun epsilon epsilonEq epsilonPositive => by
      subst epsilon
      exact logBound),
    rhoUpper.trans (inverseCubeBound delta deltaPos deltaInverseCube)
  ⟩

end Kakeya.Assouad.PureWZ2
