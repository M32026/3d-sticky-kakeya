import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9GenericFirstChartDenseRoot
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9PreRuntimeHierarchy

/-! # Generic scalar bridge for the first-chart dense root

This module exposes the scalar receipts used by the dense-root construction
without referring to the sampled M9 hierarchy.  The geometric receipts come
from the exact generic whole-cell trace; schedule, cardinality, regularization,
and top-level absorption remain explicit inputs.
-/

noncomputable section
namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

private theorem genericDenseRootOutputFinite
    {q loss : ℝ} (qPos : 0 < q) (qOne : q ≤ 1) (lossPos : 0 < loss) :
    WZ2PaperFiniteErrorConstant (Kakeya.realRpowENN q (-loss)) := by
  constructor
  · simp only [Kakeya.realRpowENN]
    have hreal : Real.rpow q 0 ≤ Real.rpow q (-loss) :=
      Real.rpow_le_rpow_of_exponent_ge qPos qOne (by linarith)
    have henn := ENNReal.ofReal_le_ofReal hreal
    simpa using henn
  · simp [Kakeya.realRpowENN]

private theorem genericDenseRootSourceMass
    {q sigma sourceLoss weightLoss : ℝ}
    (source : PureWZ2ExtremalConfiguration sigma sourceLoss q)
    (qPos : 0 < q) (qOne : q ≤ 1)
    (sourceLossLe : sourceLoss ≤ weightLoss) :
    proposition63CanonicalReentryWeight q weightLoss *
        source.family.enncard ≤ source.shading.mass := by
  have bodyLower : Kakeya.realRpowENN q 2 * source.family.enncard ≤
      source.family.toBodyFamily.mass := by
    rw [tubeFamily_mass_eq_nominal]
    rw [mul_comm (Kakeya.realRpowENN q 2) source.family.enncard]
    apply mul_le_mul_left'
    calc
      Kakeya.realRpowENN q 2 = ENNReal.ofReal (q ^ 2) := by
        simp [Kakeya.realRpowENN, Real.rpow_two]
      _ ≤ ENNReal.ofReal (Real.pi * q ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [Real.pi_gt_three, sq_nonneg q]
      _ ≤ Kakeya.deltaTubeVolume q := deltaTubeVolume_lower_pi qPos
  calc
    proposition63CanonicalReentryWeight q weightLoss *
          source.family.enncard =
        Kakeya.realRpowENN q weightLoss *
          (Kakeya.realRpowENN q 2 * source.family.enncard) := by
      unfold proposition63CanonicalReentryWeight
      rw [Kakeya.Assouad.realRpowENN_add qPos]
      ring
    _ ≤ Kakeya.realRpowENN q weightLoss *
        source.family.toBodyFamily.mass := by gcongr
    _ ≤ Kakeya.realRpowENN q sourceLoss *
        source.family.toBodyFamily.mass := by
      gcongr
      exact ENNReal.ofReal_mono
        (Real.rpow_le_rpow_of_exponent_ge qPos qOne sourceLossLe)
    _ ≤ source.shading.mass := source.extremal.dense

private theorem genericDenseRootCarrierUpper
    {q sigma sourceLoss : ℝ}
    (source : PureWZ2ExtremalConfiguration sigma sourceLoss q)
    (ambient : WZ1PaperTubeShading source.family)
    (qPos : 0 < q) (qSmall : q ≤ 1 / 24)
    (sourceSub : ∀ index, source.shading.carrier index ⊆
      ambient.carrier index)
    (lineClass : WZ1PaperIsLineClass source.family) :
    ∀ index : Fin source.family.card,
      proposition63OrdinaryCarrierWeight source.shading index ≤
        55296 * Kakeya.deltaTubeVolume 1 * Kakeya.realRpowENN q 2 := by
  intro index
  calc
    proposition63OrdinaryCarrierWeight source.shading index ≤
        volume (wz1PaperTubeCarrier (source.family.tube index)) := by
      apply measure_mono
      intro point pointMem
      exact ambient.subset_body index (sourceSub index pointMem)
    _ ≤ 55296 * Kakeya.deltaTubeVolume 1 * Kakeya.realRpowENN q 2 :=
      (wz2PaperTubeCarrier_convex_and_volume_quadratic
        wz2_paper_tube_carrier_geometry qPos qSmall
        (source.family.tube index) (lineClass index)).2

private theorem genericDenseRootWeightUpperFinite {q : ℝ} :
    (55296 * Kakeya.deltaTubeVolume 1 * Kakeya.realRpowENN q 2 :
      ENNReal) ≠ ⊤ := by
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top)
    (by simp [Kakeya.realRpowENN])

structure GenericDenseRootRegularizationReceipt
    {delta q weightLoss targetLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := family)
      (Kakeya.realRpowENN q (-weightLoss))
      (Kakeya.realRpowENN q (-targetLoss)) levelCount) : Prop where
  bound :
    let degreeConstant :=
      16 * (schedule.scaleCount : ENNReal) *
        (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^ schedule.scaleCount
    let regularizationLoss :=
      8 * (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
        (schedule.scaleCount + 1)
    max degreeConstant
        (((proposition63CanonicalReentryWeight q weightLoss)⁻¹ *
          (Kakeya.realRpowENN q (-weightLoss) *
            (regularizationLoss *
              (55296 * Kakeya.deltaTubeVolume 1 * Kakeya.realRpowENN q 2)) *
              degreeConstant)) * Kakeya.realRpowENN q (-weightLoss)) ≤
      Kakeya.realRpowENN q (-targetLoss)

private theorem genericDenseRootRegularizationAbsorb
    {delta q weightLoss targetLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {levelCount : ℕ}
    (qPos : 0 < q)
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := family)
      (Kakeya.realRpowENN q (-weightLoss))
      (Kakeya.realRpowENN q (-targetLoss)) levelCount)
    (absorptionBound :
      let logTerm := (Nat.log 2 (2 * family.card) + 1 : ENNReal)
      let frozenDegree :=
        16 * ((levelCount + 1 : ℕ) : ENNReal) *
          logTerm ^ (levelCount + 1)
      let frozenLoss := 8 * logTerm ^ (levelCount + 2)
      max frozenDegree
          ((((1 / 2 : ENNReal) * Kakeya.realRpowENN q weightLoss)⁻¹ *
            (Kakeya.realRpowENN q (-weightLoss) *
              ((2 * frozenLoss) * (55296 * Kakeya.deltaTubeVolume 1) *
                frozenDegree))) *
            Kakeya.realRpowENN q (-weightLoss)) ≤
        Kakeya.realRpowENN q (-targetLoss)) :
    let degreeConstant :=
      16 * (schedule.scaleCount : ENNReal) *
        (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^ schedule.scaleCount
    let regularizationLoss :=
      8 * (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
        (schedule.scaleCount + 1)
    max degreeConstant
        (((proposition63CanonicalReentryWeight q weightLoss)⁻¹ *
          (Kakeya.realRpowENN q (-weightLoss) *
            (regularizationLoss *
              (55296 * Kakeya.deltaTubeVolume 1 *
                Kakeya.realRpowENN q 2)) * degreeConstant)) *
          Kakeya.realRpowENN q (-weightLoss)) ≤
      Kakeya.realRpowENN q (-targetLoss) := by
  let logTerm : ENNReal :=
    (Nat.log 2 (2 * family.card) + 1 : ENNReal)
  let actualDegree : ENNReal :=
    16 * (schedule.scaleCount : ENNReal) * logTerm ^ schedule.scaleCount
  let frozenDegree : ENNReal :=
    16 * ((levelCount + 1 : ℕ) : ENNReal) * logTerm ^ (levelCount + 1)
  let actualLoss : ENNReal := 8 * logTerm ^ (schedule.scaleCount + 1)
  let frozenLoss : ENNReal := 8 * logTerm ^ (levelCount + 2)
  have logOne : (1 : ENNReal) ≤ logTerm := by
    dsimp only [logTerm]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have degreeLe : actualDegree ≤ frozenDegree := by
    dsimp only [actualDegree, frozenDegree]
    calc
      16 * (schedule.scaleCount : ENNReal) * logTerm ^ schedule.scaleCount ≤
          16 * ((levelCount + 1 : ℕ) : ENNReal) *
            logTerm ^ schedule.scaleCount := by
        gcongr
        exact_mod_cast schedule.scaleCount_le
      _ ≤ frozenDegree := by
        dsimp only [frozenDegree]
        exact mul_le_mul_left'
          (pow_le_pow_right' logOne schedule.scaleCount_le) _
  have lossLe : actualLoss ≤ frozenLoss := by
    dsimp only [actualLoss, frozenLoss]
    exact mul_le_mul_left'
      (pow_le_pow_right' logOne
        (Nat.add_le_add_right schedule.scaleCount_le 1)) _
  have qTwoZero : Kakeya.realRpowENN q 2 ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos qPos _)).ne'
  have qTwoTop : Kakeya.realRpowENN q 2 ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have densityZero : Kakeya.realRpowENN q weightLoss ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos qPos _)).ne'
  have densityTop : Kakeya.realRpowENN q weightLoss ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have densityEq : Kakeya.realRpowENN q weightLoss *
        Kakeya.realRpowENN q 2 =
      proposition63CanonicalReentryWeight q weightLoss := by
    unfold proposition63CanonicalReentryWeight
    exact (Kakeya.Assouad.realRpowENN_add qPos _ _).symm
  have weightedLe :
      ((proposition63CanonicalReentryWeight q weightLoss)⁻¹ *
          (Kakeya.realRpowENN q (-weightLoss) *
            (actualLoss * (55296 * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN q 2)) * actualDegree)) *
        Kakeya.realRpowENN q (-weightLoss) ≤
      (((1 / 2 : ENNReal) * Kakeya.realRpowENN q weightLoss)⁻¹ *
          (Kakeya.realRpowENN q (-weightLoss) *
            ((2 * frozenLoss) * (55296 * Kakeya.deltaTubeVolume 1) *
              frozenDegree))) *
        Kakeya.realRpowENN q (-weightLoss) := by
    rw [← densityEq,
      ENNReal.mul_inv (Or.inl densityZero) (Or.inl densityTop)]
    rw [show ((1 / 2 : ENNReal) *
        Kakeya.realRpowENN q weightLoss)⁻¹ =
        2 * (Kakeya.realRpowENN q weightLoss)⁻¹ by
      rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num]
    have qCancel : (Kakeya.realRpowENN q 2)⁻¹ *
        Kakeya.realRpowENN q 2 = 1 :=
      ENNReal.inv_mul_cancel qTwoZero qTwoTop
    have leftEq :
        (Kakeya.realRpowENN q weightLoss)⁻¹ *
              (Kakeya.realRpowENN q 2)⁻¹ *
            (Kakeya.realRpowENN q (-weightLoss) *
              (actualLoss * (55296 * Kakeya.deltaTubeVolume 1 *
                Kakeya.realRpowENN q 2)) * actualDegree) *
            Kakeya.realRpowENN q (-weightLoss) =
          (Kakeya.realRpowENN q weightLoss)⁻¹ *
          (Kakeya.realRpowENN q (-weightLoss) *
            (actualLoss * (55296 * Kakeya.deltaTubeVolume 1)) *
              actualDegree) *
          Kakeya.realRpowENN q (-weightLoss) := by
      rw [show
        (Kakeya.realRpowENN q weightLoss)⁻¹ *
              (Kakeya.realRpowENN q 2)⁻¹ *
            (Kakeya.realRpowENN q (-weightLoss) *
              (actualLoss * (55296 * Kakeya.deltaTubeVolume 1 *
                Kakeya.realRpowENN q 2)) * actualDegree) *
            Kakeya.realRpowENN q (-weightLoss) =
          ((Kakeya.realRpowENN q 2)⁻¹ * Kakeya.realRpowENN q 2) *
            ((Kakeya.realRpowENN q weightLoss)⁻¹ *
              (Kakeya.realRpowENN q (-weightLoss) *
                (actualLoss * (55296 * Kakeya.deltaTubeVolume 1)) *
                  actualDegree) *
              Kakeya.realRpowENN q (-weightLoss)) by ring, qCancel, one_mul]
    have coreLe :
        actualLoss * (55296 * Kakeya.deltaTubeVolume 1) * actualDegree ≤
          (2 * frozenLoss) * (55296 * Kakeya.deltaTubeVolume 1) *
            frozenDegree := by
      calc
        actualLoss * (55296 * Kakeya.deltaTubeVolume 1) * actualDegree ≤
            frozenLoss * (55296 * Kakeya.deltaTubeVolume 1) *
              frozenDegree := by gcongr
        _ ≤ (2 * frozenLoss) * (55296 * Kakeya.deltaTubeVolume 1) *
              frozenDegree := by
          gcongr
          calc
            frozenLoss = 1 * frozenLoss := by rw [one_mul]
            _ ≤ 2 * frozenLoss := by gcongr <;> norm_num
    rw [leftEq]
    have invLe : (Kakeya.realRpowENN q weightLoss)⁻¹ ≤
        2 * (Kakeya.realRpowENN q weightLoss)⁻¹ := by
      calc
        (Kakeya.realRpowENN q weightLoss)⁻¹ =
            1 * (Kakeya.realRpowENN q weightLoss)⁻¹ := by rw [one_mul]
        _ ≤ 2 * (Kakeya.realRpowENN q weightLoss)⁻¹ := by gcongr <;> norm_num
    calc
      _ ≤ 2 * (Kakeya.realRpowENN q weightLoss)⁻¹ *
          (Kakeya.realRpowENN q (-weightLoss) *
            (actualLoss * (55296 * Kakeya.deltaTubeVolume 1)) *
              actualDegree) *
          Kakeya.realRpowENN q (-weightLoss) := by gcongr <;> norm_num
      _ ≤ _ := by
        apply mul_le_mul_right'
        apply mul_le_mul_left'
        have weightedCoreLe := mul_le_mul_left' coreLe
          (Kakeya.realRpowENN q (-weightLoss))
        simpa only [mul_assoc] using weightedCoreLe
  dsimp only
  exact (max_le_max degreeLe weightedLe).trans absorptionBound

private theorem genericDenseRootTopLevelAbsorb
    {delta q stickyLoss weightLoss targetLoss normalizationLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {levelCount : ℕ}
    (qPos : 0 < q) (qOne : q ≤ 1)
    (stickyLeWeight : stickyLoss ≤ weightLoss)
    (normalizationPos : 0 < normalizationLoss)
    (targetLeHalf : targetLoss ≤ normalizationLoss / 2)
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := family)
      (Kakeya.realRpowENN q (-weightLoss))
      (Kakeya.realRpowENN q (-targetLoss)) levelCount)
    (ambientTwo : (2 : ENNReal) < Kakeya.realRpowENN q (-weightLoss))
    (regularizationAbsorb : GenericDenseRootRegularizationReceipt schedule) :
    ((proposition63CanonicalReentryWeight q weightLoss)⁻¹ *
        (((8 : ENNReal) *
          (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
            (schedule.scaleCount + 1)) *
          (55296 * Kakeya.deltaTubeVolume 1 * Kakeya.realRpowENN q 2))) *
      ((4 : ENNReal) * Kakeya.realRpowENN q (-stickyLoss)) ≤
    Kakeya.realRpowENN q (-normalizationLoss) := by
  let ambientConstant := Kakeya.realRpowENN q (-weightLoss)
  let degreeConstant : ENNReal :=
    16 * (schedule.scaleCount : ENNReal) *
      (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^ schedule.scaleCount
  let regularizationLoss : ENNReal :=
    8 * (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
      (schedule.scaleCount + 1)
  have logOne : (1 : ENNReal) ≤
      (Nat.log 2 (2 * family.card) + 1 : ENNReal) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have countOne : (1 : ENNReal) ≤ schedule.scaleCount := by
    exact_mod_cast schedule.scaleCount_pos
  have degreeFour : (4 : ENNReal) ≤ degreeConstant := by
    dsimp only [degreeConstant]
    calc
      (4 : ENNReal) ≤ 16 * 1 * 1 := by norm_num
      _ ≤ 16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
            schedule.scaleCount := by
        gcongr
        exact one_le_pow₀ logOne
  have stickyPowerLe : Kakeya.realRpowENN q (-stickyLoss) ≤
      ambientConstant := by
    dsimp only [ambientConstant]
    exact ENNReal.ofReal_mono
      (Real.rpow_le_rpow_of_exponent_ge qPos qOne (by linarith))
  have ambientOne : (1 : ENNReal) ≤ ambientConstant :=
    (by norm_num : (1 : ENNReal) < 2).le.trans ambientTwo.le
  have topFactorLe :
      (4 : ENNReal) * Kakeya.realRpowENN q (-stickyLoss) ≤
        ambientConstant * degreeConstant * ambientConstant := by
    calc
      (4 : ENNReal) * Kakeya.realRpowENN q (-stickyLoss) ≤
          degreeConstant * ambientConstant := by gcongr
      _ = 1 * (degreeConstant * ambientConstant) := by rw [one_mul]
      _ ≤ ambientConstant * (degreeConstant * ambientConstant) := by gcongr
      _ = ambientConstant * degreeConstant * ambientConstant := by ring
  have topLeRegularization :
      ((proposition63CanonicalReentryWeight q weightLoss)⁻¹ *
          (regularizationLoss *
            (55296 * Kakeya.deltaTubeVolume 1 * Kakeya.realRpowENN q 2))) *
        ((4 : ENNReal) * Kakeya.realRpowENN q (-stickyLoss)) ≤
      ((proposition63CanonicalReentryWeight q weightLoss)⁻¹ *
          (ambientConstant *
            (regularizationLoss *
              (55296 * Kakeya.deltaTubeVolume 1 *
                Kakeya.realRpowENN q 2)) * degreeConstant)) *
        ambientConstant := by
    calc
      _ ≤ ((proposition63CanonicalReentryWeight q weightLoss)⁻¹ *
          (regularizationLoss *
            (55296 * Kakeya.deltaTubeVolume 1 * Kakeya.realRpowENN q 2))) *
          (ambientConstant * degreeConstant * ambientConstant) := by
            exact mul_le_mul_left' topFactorLe _
      _ = _ := by ring
  have targetBound : Kakeya.realRpowENN q (-targetLoss) ≤
      Kakeya.realRpowENN q (-normalizationLoss) := by
    simp only [Kakeya.realRpowENN]
    exact ENNReal.ofReal_mono (Real.rpow_le_rpow_of_exponent_ge
      qPos qOne (by linarith))
  dsimp only [regularizationLoss, ambientConstant, degreeConstant] at topLeRegularization
  have regularizationBound := regularizationAbsorb.bound
  dsimp only at regularizationBound
  exact (topLeRegularization.trans
    ((le_max_right _ _).trans regularizationBound)).trans targetBound

namespace Proposition63GenericFirstRichBoundaryData

variable
    {delta sigma inputLoss normalizationLoss densityLoss currentLoss localLoss
      reentryLoss stickyLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
      densityLoss}
    {preliminary : Proposition63PreliminaryLocalGrainData
      (localLoss := localLoss) (reentryLoss := currentLoss)
      root.normalization}
    {richSchedule : Proposition63RichStickyKernelScheduleData sigma stickyLoss}
    (first : Proposition63GenericFirstRichBoundaryData
      (reentryLoss := reentryLoss) root preliminary richSchedule)

abbrev GenericFirstChartCardinalityReceipt
    {commonSliceLoss chartLoss tau epsilon₁ epsilon₃ : ℝ}
    {coefficient : NNReal} {retainedFactor : ENNReal}
    (chart : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := (coefficient : ℝ))
      first.terminal.data first.power.Delta retainedFactor)
    (output : GenericFirstChartWholeCellOutput first chart) :=
  (output.rescalingCertificate.publicFamily.card : ℝ) ≤
    (259 : ℝ)^3 * (67 : ℝ)^3 * Real.rpow first.power.h (-9 : ℝ)

/-- Build the pre-Lemma-4.3 dense root on the exact generic whole-cell trace.
All numerical information formerly obtained from sampled cutoff records is
supplied explicitly.  The cardinality receipt is retained at this boundary so
callers can document the finite-family estimate used to prove the two
absorption hypotheses. -/
theorem firstChartDenseRootFromScalarReceipts
    {commonSliceLoss chartLoss targetLoss targetNormalizationLoss
      nearbyInputLoss tau epsilon₁ epsilon₃ : ℝ}
    {coefficient : NNReal} {retainedFactor : ENNReal}
    (chart : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := (coefficient : ℝ))
      first.terminal.data first.power.Delta retainedFactor)
    (denseNormalizationExponent levelCount : ℕ)
    (output : GenericFirstChartWholeCellOutput first chart)
    (massLower : GenericFirstChartTraceMassLower first chart output)
    (sourceLossLe : chartLoss ≤ targetLoss)
    (targetLossPos : 0 < targetLoss)
    (normalizationLossPos : 0 < targetNormalizationLoss)
    (targetLossLeHalf : targetLoss ≤ targetNormalizationLoss / 2)
    (qSmall : delta / first.power.requested.1 ≤ 1 / 24)
    (sigmaLeOne : sigma ≤ 1)
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := (chart.wholeCellTraceOrdinarySource
        first.current.normalization output massLower).family)
      (Kakeya.realRpowENN (delta / first.power.requested.1)
        (-nearbyInputLoss))
      (Kakeya.realRpowENN (delta / first.power.requested.1)
        (-targetLoss)) levelCount)
    (ambientCWA : WZ2PaperPureCWAAtNearbyScales
      (chart.wholeCellTraceOrdinarySource
        first.current.normalization output massLower).family
      (Kakeya.realRpowENN (delta / first.power.requested.1)
        (-nearbyInputLoss)))
    (normalizationWeight : ENNReal)
    (normalizationWeightNeZero : normalizationWeight ≠ 0)
    (normalizationWeightNeTop : normalizationWeight ≠ ⊤)
    (weightUpper : ENNReal)
    (weightUpperNeTop : weightUpper ≠ ⊤)
    (regularizationMassLower : normalizationWeight *
      (chart.wholeCellTraceOrdinarySource first.current.normalization
        output massLower).family.enncard ≤
      (chart.wholeCellTraceOrdinarySource first.current.normalization
        output massLower).shading.mass)
    (weightUpperReceipt : ∀ index : Fin
      (chart.wholeCellTraceOrdinarySource first.current.normalization
        output massLower).family.card,
      proposition63OrdinaryCarrierWeight
          (chart.wholeCellTraceOrdinarySource first.current.normalization
            output massLower).shading index ≤ weightUpper)
    (outputFinite : WZ2PaperFiniteErrorConstant
      (Kakeya.realRpowENN (delta / first.power.requested.1) (-targetLoss)))
    (regularizationAbsorb : GenericFirstChartCardinalityReceipt
        first chart output →
      let traceSource := chart.wholeCellTraceOrdinarySource
        first.current.normalization output massLower
      let ambientConstant := Kakeya.realRpowENN
        (delta / first.power.requested.1) (-nearbyInputLoss)
      let outputConstant := Kakeya.realRpowENN
        (delta / first.power.requested.1) (-targetLoss)
      let degreeConstant :=
        16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * traceSource.family.card) + 1 : ENNReal) ^
            schedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * traceSource.family.card) + 1 : ENNReal) ^
            (schedule.scaleCount + 1)
      max degreeConstant
          ((normalizationWeight⁻¹ *
              (ambientConstant * (regularizationLoss * weightUpper) *
                degreeConstant)) * ambientConstant) ≤ outputConstant)
    (traceScaleAbsorb :
      4 * (Kakeya.realRpowENN (delta / first.power.requested.1) targetLoss *
        Kakeya.deltaTubeVolume (delta / first.power.requested.1)) ≤
      normalizationWeight)
    (paperScaleAbsorb : ∀ index : Fin
      (chart.wholeCellTraceOrdinarySource first.current.normalization
        output massLower).family.card,
      4 * (Kakeya.realRpowENN (delta / first.power.requested.1) targetLoss *
          volume (wz1PaperTubeCarrier
            ((chart.wholeCellTraceOrdinarySource first.current.normalization
              output massLower).family.tube index))) ≤
        (73 / 100 : ENNReal) * normalizationWeight)
    (topCWA : WZ2PaperConvexWolffBound
      (chart.wholeCellTraceOrdinarySource
        first.current.normalization output massLower).family
      ((4 : ENNReal) *
        Kakeya.realRpowENN first.power.h (-stickyLoss)))
    (topLevelAbsorb :
      (normalizationWeight⁻¹ *
          (((8 : ENNReal) *
              (Nat.log 2 (2 *
                (chart.wholeCellTraceOrdinarySource
                  first.current.normalization output massLower).family.card) +
                1 : ENNReal) ^ (schedule.scaleCount + 1)) * weightUpper)) *
          ((4 : ENNReal) *
            Kakeya.realRpowENN first.power.h (-stickyLoss)) ≤
        Kakeya.realRpowENN (delta / first.power.requested.1)
          (-targetNormalizationLoss)) :
    Nonempty (Proposition63PreLemma43DenseRootData
      (chart.wholeCellTraceOrdinarySource first.current.normalization
        output massLower)
      (chart.wholeCellTraceAmbient first.current.normalization output massLower)
      targetLoss targetNormalizationLoss denseNormalizationExponent) := by
  let traceSource := chart.wholeCellTraceOrdinarySource
    first.current.normalization output massLower
  let traceAmbient := chart.wholeCellTraceAmbient
    first.current.normalization output massLower
  let traceRoot := proposition63_m9_wholeCellTraceRoot
    first.current.normalization chart output massLower
  have cardinalityReceipt : GenericFirstChartCardinalityReceipt
      first chart output :=
    first.firstChartPublicCardinalityNinthPower chart output sigmaLeOne
  exact proposition63_preLemma43_dense_root traceSource traceAmbient schedule
    ambientCWA sourceLossLe targetLossPos normalizationLossPos
    targetLossLeHalf normalizationWeightNeZero normalizationWeightNeTop
    weightUpperNeTop regularizationMassLower weightUpperReceipt outputFinite
    (regularizationAbsorb cardinalityReceipt) le_rfl traceScaleAbsorb
    paperScaleAbsorb
    traceRoot.source_sub_ambient traceRoot.ambient_cubical
    (traceRoot.ambient_extremal.mono_loss sourceLossLe)
    traceRoot.source_axial_window traceRoot.ambient_line_class
    traceRoot.ambient_direction_vertical qSmall
    ((4 : ENNReal) * Kakeya.realRpowENN first.power.h (-stickyLoss))
    topCWA topLevelAbsorb

/-- Package the scalar-constructed dense root together with the exact output
and mass receipt produced by `firstChartWholeCellTrace`. -/
theorem firstChartDenseRootOutputFromScalarReceipts
    {commonSliceLoss chartLoss targetLoss targetNormalizationLoss
      tau epsilon₁ epsilon₃ : ℝ}
    {coefficient : NNReal} {retainedFactor : ENNReal}
    (chart : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := (coefficient : ℝ))
      first.terminal.data first.power.Delta retainedFactor)
    (denseNormalizationExponent : ℕ)
    (output : GenericFirstChartWholeCellOutput first chart)
    (massLower : GenericFirstChartTraceMassLower first chart output)
    (denseRoot : Nonempty (Proposition63PreLemma43DenseRootData
      (chart.wholeCellTraceOrdinarySource first.current.normalization
        output massLower)
      (chart.wholeCellTraceAmbient first.current.normalization output massLower)
      targetLoss targetNormalizationLoss denseNormalizationExponent)) :
    Nonempty (GenericFirstChartDenseRootOutput
      (targetLoss := targetLoss)
      (targetNormalizationLoss := targetNormalizationLoss)
      first chart denseNormalizationExponent) :=
  first.firstChartDenseRootOfOutput chart denseNormalizationExponent output
    massLower denseRoot

private theorem firstChartDenseRootCanonicalFromSchedule
    {outputLoss tau epsilon₁ epsilon₃ : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    {canonicalPreliminary : Proposition63PreliminaryLocalGrainData
      (localLoss := cutoff.initial.localLoss)
      (reentryLoss := currentLoss) root.normalization}
    (first : Proposition63GenericFirstRichBoundaryData
      (localLoss := cutoff.initial.localLoss)
      (reentryLoss := cutoff.firstRichSchedule.sourceLoss)
      root canonicalPreliminary cutoff.firstRichSchedule)
    {coefficient : NNReal} {retainedFactor : ENNReal}
    (chart : Proposition63FirstChartData
      (localLoss := cutoff.initial.localLoss)
      (commonSliceLoss := cutoff.initial.localLoss)
      (chartLoss := cutoff.initial.lemma43SourceLoss)
      (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
      (coefficient := (coefficient : ℝ)) first.terminal.data
      first.power.Delta retainedFactor)
    (output : GenericFirstChartWholeCellOutput first chart)
    (massLower : GenericFirstChartTraceMassLower first chart output)
    (topCWA : WZ2PaperConvexWolffBound
      (chart.wholeCellTraceOrdinarySource first.current.normalization
        output massLower).family
      ((4 : ENNReal) * Kakeya.realRpowENN
        (delta / first.power.requested.1) (-cutoff.initial.stickyLoss)))
    (hdelta : delta ≤ cutoff.outerScaleCeiling)
    (firstLower : Real.rpow delta (1 - cutoff.initial.stickyLoss) ≤
      first.power.requested.1)
    (qSmall : first.power.h ≤ 1 / 24)
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := (chart.wholeCellTraceOrdinarySource
        first.current.normalization output massLower).family)
      (Kakeya.realRpowENN (delta / first.power.requested.1)
        (-cutoff.firstChartCutoff.nearbyInputLoss))
      (Kakeya.realRpowENN (delta / first.power.requested.1)
        (-cutoff.twoCall.schedule.first.sourceLoss))
      cutoff.firstChartCutoff.levelCount)
    (ambientTwo : (2 : ENNReal) < Kakeya.realRpowENN
      (delta / first.power.requested.1)
      (-cutoff.firstChartCutoff.nearbyInputLoss))
    (regularizationAbsorb : GenericDenseRootRegularizationReceipt
      (q := delta / first.power.requested.1)
      (weightLoss := cutoff.firstChartCutoff.nearbyInputLoss)
      (targetLoss := cutoff.twoCall.schedule.first.sourceLoss) schedule) :
    Nonempty (GenericFirstChartDenseRootOutput
      (targetLoss := cutoff.twoCall.schedule.first.sourceLoss)
      (targetNormalizationLoss :=
        cutoff.twoCall.schedule.first.normalizationLoss)
      first chart hierarchy.N) := by
  let traceSource := chart.wholeCellTraceOrdinarySource
    first.current.normalization output massLower
  let traceAmbient := chart.wholeCellTraceAmbient
    first.current.normalization output massLower
  let traceRoot := proposition63_m9_wholeCellTraceRoot
    first.current.normalization chart output massLower
  have qPos : 0 < first.power.h := first.power.h_pos
  have qOne : first.power.h ≤ 1 := qSmall.trans (by norm_num)
  have ratioEq : delta / first.power.requested.1 = first.power.h := by
    rw [first.power.requested_eq, first.power.h_eq]
  have qPosRatio : 0 < delta / first.power.requested.1 := by
    simpa only [ratioEq] using qPos
  have qOneRatio : delta / first.power.requested.1 ≤ 1 := by
    simpa only [ratioEq] using qOne
  have qSmallRatio : delta / first.power.requested.1 ≤ 1 / 24 := by
    simpa only [ratioEq] using qSmall
  have nearbyCWARatio : WZ2PaperPureCWAAtNearbyScales traceSource.family
      (Kakeya.realRpowENN (delta / first.power.requested.1)
        (-cutoff.firstChartCutoff.nearbyInputLoss)) :=
    traceSource.extremal.cwa_nearby_scales.mono_loss qPosRatio qOneRatio
      cutoff.initial_lemma43_lt_firstChartNearby.le
  have topAbsorb := genericDenseRootTopLevelAbsorb
    (stickyLoss := cutoff.initial.stickyLoss)
    (weightLoss := cutoff.firstChartCutoff.nearbyInputLoss)
    (targetLoss := cutoff.twoCall.schedule.first.sourceLoss)
    (normalizationLoss := cutoff.twoCall.schedule.first.normalizationLoss)
    qPosRatio qOneRatio
    (by
      have hnearby := cutoff.initial_lemma43_lt_firstChartNearby
      rw [cutoff.initial.lemma43SourceLoss_eq_three_sticky] at hnearby
      linarith [cutoff.initial.sticky_pos])
    cutoff.twoCall.schedule.first.normalizationLoss_pos
    cutoff.twoCall.schedule.first.sourceLoss_le_half schedule ambientTwo
    regularizationAbsorb
  have scaleAbsorb := cutoff.firstChartScaleAbsorption
    first.current.normalization.final_extremal.delta_pos hdelta
    first.power.requested firstLower
  have denseRoot := proposition63_preLemma43_dense_root
    (normalizationExponent := hierarchy.N) traceSource traceAmbient
    schedule nearbyCWARatio cutoff.initial_lemma43_lt_firstSource.le
    cutoff.twoCall.schedule.first.sourceLoss_pos
    cutoff.twoCall.schedule.first.normalizationLoss_pos
    cutoff.twoCall.schedule.first.sourceLoss_le_half
    (proposition63CanonicalReentryWeight_ne_zero qPosRatio)
    proposition63CanonicalReentryWeight_ne_top
    genericDenseRootWeightUpperFinite
    (genericDenseRootSourceMass traceSource qPosRatio qOneRatio
      cutoff.initial_lemma43_lt_firstChartNearby.le)
    (genericDenseRootCarrierUpper traceSource traceAmbient qPosRatio qSmallRatio
      traceRoot.source_sub_ambient traceRoot.ambient_line_class)
    (genericDenseRootOutputFinite qPosRatio qOneRatio
      cutoff.twoCall.schedule.first.sourceLoss_pos)
    regularizationAbsorb.bound le_rfl
    (proposition63CanonicalReentryWeight_trace_scale qPosRatio qOneRatio
      scaleAbsorb.1)
    (fun index => proposition63CanonicalReentryWeight_paper_scale qPosRatio
      qSmallRatio
      scaleAbsorb.2 traceRoot.ambient_line_class index)
    traceRoot.source_sub_ambient traceRoot.ambient_cubical
    (traceRoot.ambient_extremal.mono_loss
      cutoff.initial_lemma43_lt_firstSource.le)
    traceRoot.source_axial_window traceRoot.ambient_line_class
    traceRoot.ambient_direction_vertical qSmallRatio
    ((4 : ENNReal) * Kakeya.realRpowENN
      (delta / first.power.requested.1)
      (-cutoff.initial.stickyLoss)) (by simpa only [traceSource] using topCWA)
      topAbsorb
  exact first.firstChartDenseRootOutputFromScalarReceipts chart hierarchy.N
    output massLower denseRoot

private theorem firstChartDenseRootCanonicalOfOutput
    {outputLoss tau epsilon₁ epsilon₃ : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    {canonicalPreliminary : Proposition63PreliminaryLocalGrainData
      (localLoss := cutoff.initial.localLoss)
      (reentryLoss := currentLoss) root.normalization}
    (first : Proposition63GenericFirstRichBoundaryData
      (localLoss := cutoff.initial.localLoss)
      (reentryLoss := cutoff.firstRichSchedule.sourceLoss)
      root canonicalPreliminary cutoff.firstRichSchedule)
    {coefficient : NNReal} {retainedFactor : ENNReal}
    (chart : Proposition63FirstChartData
      (localLoss := cutoff.initial.localLoss)
      (commonSliceLoss := cutoff.initial.localLoss)
      (chartLoss := cutoff.initial.lemma43SourceLoss)
      (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
      (coefficient := (coefficient : ℝ)) first.terminal.data
      first.power.Delta retainedFactor)
    (output : GenericFirstChartWholeCellOutput first chart)
    (massLower : GenericFirstChartTraceMassLower first chart output)
    (topCWA : WZ2PaperConvexWolffBound
      (chart.wholeCellTraceOrdinarySource first.current.normalization
        output massLower).family
      ((4 : ENNReal) * Kakeya.realRpowENN
        (delta / first.power.requested.1) (-cutoff.initial.stickyLoss)))
    (hdelta : delta ≤ cutoff.outerScaleCeiling)
    (firstLower : Real.rpow delta (1 - cutoff.initial.stickyLoss) ≤
      first.power.requested.1)
    (qSmall : first.power.h ≤ 1 / 24)
    (hsigmaOne : sigma < 1) :
    Nonempty (GenericFirstChartDenseRootOutput
      (targetLoss := cutoff.twoCall.schedule.first.sourceLoss)
      (targetNormalizationLoss :=
        cutoff.twoCall.schedule.first.normalizationLoss)
      first chart hierarchy.N) := by
  let traceSource := chart.wholeCellTraceOrdinarySource
    first.current.normalization output massLower
  let traceAmbient := chart.wholeCellTraceAmbient
    first.current.normalization output massLower
  let traceRoot := proposition63_m9_wholeCellTraceRoot
    first.current.normalization chart output massLower
  have qPos : 0 < first.power.h := first.power.h_pos
  have ratioEq : delta / first.power.requested.1 = first.power.h := by
    rw [first.power.requested_eq, first.power.h_eq]
  have qPosRatio : 0 < delta / first.power.requested.1 := by
    simpa only [ratioEq] using qPos
  have qSmallRatio : delta / first.power.requested.1 ≤ 1 / 24 := by
    simpa only [ratioEq] using qSmall
  have nearbyCWARatio : WZ2PaperPureCWAAtNearbyScales traceSource.family
      (Kakeya.realRpowENN (delta / first.power.requested.1)
        (-cutoff.firstChartCutoff.nearbyInputLoss)) :=
    traceSource.extremal.cwa_nearby_scales.mono_loss qPosRatio
      (qSmallRatio.trans (by norm_num))
      cutoff.initial_lemma43_lt_firstChartNearby.le
  have cardBound := first.firstChartPublicCardinalityNinthPower chart output
    hsigmaOne.le
  rcases cutoff.firstChartCutoff.absorption_at_ratio
      first.current.normalization.final_extremal.delta_pos
      (hdelta.trans cutoff.outerScaleCeiling_le_firstChartRoot |>.trans
        cutoff.firstChartRootScale_le_cutoffRoot) first.power.requested firstLower
      output.rescalingCertificate.publicFamily.card (by
        simpa only [first.power.h_eq, ← first.power.requested_eq] using cardBound) with
    ⟨ambientTwo, ambientFinite, _, _, coverage, outputWindow, absorptionBound⟩
  rcases paper_pure_finite_nearby_schedule (fine := traceSource.family)
      cutoff.firstChartCutoff.levelCount qPosRatio
      (qSmallRatio.trans (by norm_num))
      ambientTwo ambientFinite coverage outputWindow nearbyCWARatio with ⟨nearby⟩
  have cardEq : traceSource.family.card =
      output.rescalingCertificate.publicFamily.card := rfl
  have absorptionReceipt :
      let logTerm := (Nat.log 2 (2 * traceSource.family.card) + 1 : ENNReal)
      let frozenDegree := 16 *
        ((cutoff.firstChartCutoff.levelCount + 1 : ℕ) : ENNReal) *
        logTerm ^ (cutoff.firstChartCutoff.levelCount + 1)
      let frozenLoss := 8 * logTerm ^ (cutoff.firstChartCutoff.levelCount + 2)
      max frozenDegree
          ((((1 / 2 : ENNReal) * Kakeya.realRpowENN
              (delta / first.power.requested.1)
              cutoff.firstChartCutoff.nearbyInputLoss)⁻¹ *
            (Kakeya.realRpowENN (delta / first.power.requested.1)
                (-cutoff.firstChartCutoff.nearbyInputLoss) *
              ((2 * frozenLoss) * (55296 * Kakeya.deltaTubeVolume 1) *
                frozenDegree))) *
            Kakeya.realRpowENN (delta / first.power.requested.1)
              (-cutoff.firstChartCutoff.nearbyInputLoss)) ≤
        Kakeya.realRpowENN (delta / first.power.requested.1)
          (-cutoff.twoCall.schedule.first.sourceLoss) := by
    rw [cardEq]
    simpa only [mul_assoc] using absorptionBound
  have regularizationAbsorb := genericDenseRootRegularizationAbsorb qPosRatio nearby
    absorptionReceipt
  exact firstChartDenseRootCanonicalFromSchedule cutoff first chart output
    massLower topCWA hdelta firstLower qSmall nearby
    ambientTwo ⟨regularizationAbsorb⟩

/-- Canonical generic first-chart wrapper.  The outer hierarchy supplies all
losses and cutoffs; the only runtime scalar hypotheses are the terminal-density
receipt and the root-scale bound. -/
theorem firstChartDenseRootCanonical
    {outputLoss tau epsilon₁ epsilon₃ : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    {canonicalPreliminary : Proposition63PreliminaryLocalGrainData
      (localLoss := cutoff.initial.localLoss)
      (reentryLoss := currentLoss) root.normalization}
    (first : Proposition63GenericFirstRichBoundaryData
      (localLoss := cutoff.initial.localLoss)
      (reentryLoss := cutoff.firstRichSchedule.sourceLoss)
      root canonicalPreliminary cutoff.firstRichSchedule)
    {coefficient : NNReal} {retainedFactor : ENNReal}
    (chart : Proposition63FirstChartData
      (localLoss := cutoff.initial.localLoss)
      (commonSliceLoss := cutoff.initial.localLoss)
      (chartLoss := cutoff.initial.lemma43SourceLoss)
      (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
      (coefficient := (coefficient : ℝ)) first.terminal.data
      first.power.Delta retainedFactor)
    (terminalDensity :
      proposition63FirstChartTerminalDensity first.power.requested.1
          cutoff.initial.stickyLoss ≤ chart.sliceDensity)
    (hdelta : delta ≤ cutoff.outerScaleCeiling)
    (hsigmaOne : sigma < 1) :
    Nonempty (GenericFirstChartDenseRootOutput
      (targetLoss := cutoff.twoCall.schedule.first.sourceLoss)
      (targetNormalizationLoss :=
        cutoff.twoCall.schedule.first.normalizationLoss)
      first chart hierarchy.N) := by
  have firstLower : Real.rpow delta (1 - cutoff.initial.stickyLoss) ≤
      first.power.requested.1 :=
    (first.power.first_sticky_window
      first.current.normalization.final_extremal.delta_pos
      (hdelta.trans cutoff.outerScaleCeiling_le_one)
      cutoff.initial.sticky_le_power
      cutoff.initial.power_le_one_sub_sticky).1
  have qPos : 0 < first.power.h := first.power.h_pos
  have qSmall : first.power.h ≤ 1 / 24 := by
    rw [first.power.h_eq, ← first.power.requested_eq]
    exact cutoff.firstChartRatio_le_nearbyCutoff
      first.current.normalization.final_extremal.delta_pos hdelta
      first.power.requested firstLower |>.trans
        cutoff.firstChartCutoff.ratioCutoff_le
  have ratioEq : delta / first.power.requested.1 = first.power.h := by
    rw [first.power.requested_eq, first.power.h_eq]
  have qPosRatio : 0 < delta / first.power.requested.1 := by
    simpa only [ratioEq] using qPos
  have qSmallRatio : delta / first.power.requested.1 ≤ 1 / 24 := by
    simpa only [ratioEq] using qSmall
  have traceDensity := cutoff.firstChartTraceDensity.trace_density qPos
    (by
      calc
        first.power.h ≤ first.power.Delta := by
          rw [first.power.h_eq]
          apply (div_le_iff₀ (by
            rw [← first.power.scale_identity]
            exact Real.rpow_pos_of_pos first.power.h_pos _)).2
          simpa [pow_two] using first.power.tau_le_Delta_sq
        _ ≤ cutoff.firstChartTraceDensity.delta₀ := by
          rw [first.power.Delta_eq]
          exact cutoff.firstChartPower_le_traceDensityCutoff
            first.current.normalization.final_extremal.delta_pos hdelta)
  have rootPower :
      Kakeya.realRpowENN delta cutoff.firstRichSchedule.sourceLoss =
        Kakeya.realRpowENN first.power.h
          ((1 + sigma / 2) * cutoff.firstRichSchedule.sourceLoss) :=
    first.power.root_power_eq_ratio_power
  have terminalPower :
      ((400000000 : ENNReal)⁻¹ * Kakeya.realRpowENN first.power.h
        (sigma * cutoff.initial.stickyLoss)) ≤ chart.sliceDensity := by
    simpa only [← first.terminalDensity_eq_ratio_power] using terminalDensity
  have traceAbsorb :
      Kakeya.realRpowENN first.power.h cutoff.initial.lemma43SourceLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ((100 : ENNReal)⁻¹ *
            (Kakeya.realRpowENN delta cutoff.firstRichSchedule.sourceLoss / 2) *
            (chart.sliceDensity / 2)) := by
    rw [rootPower]
    exact traceDensity.trans (by gcongr)
  have outputAbsorb :
      Kakeya.realRpowENN first.power.h cutoff.initial.lemma43SourceLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          (chart.sliceDensity / 2) := by
    have factorLe : (100 : ENNReal)⁻¹ *
        (Kakeya.realRpowENN delta cutoff.firstRichSchedule.sourceLoss / 2) ≤ 1 := by
      calc
        _ ≤ 1 * (1 / 2 : ENNReal) := by
          gcongr
          · norm_num
          · unfold Kakeya.realRpowENN
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_mono (Real.rpow_le_one
              first.current.normalization.final_extremal.delta_pos.le
              (hdelta.trans cutoff.outerScaleCeiling_le_one)
              cutoff.firstRichSchedule.sourceLoss_pos.le)
        _ ≤ 1 := by norm_num
    exact traceAbsorb.trans (by
      gcongr
      calc
        ((100 : ENNReal)⁻¹ *
            (Kakeya.realRpowENN delta cutoff.firstRichSchedule.sourceLoss / 2)) *
            (chart.sliceDensity / 2) ≤ 1 * (chart.sliceDensity / 2) := by
              gcongr
        _ = _ := one_mul _)
  rcases proposition63_literal_unit_rescaled_shading chart.metricFiber
      (chart.wholeCellShading first.current.normalization)
      first.power.requested.2.2 qSmallRatio with ⟨literalImage⟩
  have sourceSub : PaperIsSubshading
      (chart.wholeCellShading first.current.normalization)
      chart.metricFiber.sourceFiber := fun index =>
    (chart.chartSelection.saturated_sub_selectedFiber index).trans
      (chart.metricFiber.source_subshading index)
  have sourceMass :
      (chart.sliceDensity / 2) *
          chart.metricFiber.fiberFamily.family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        (chart.wholeCellShading first.current.normalization).mass :=
    chart.chartRescaled.source_mass.trans
      chart.chartSelection.sourceShading_mass_le_saturated_mass
  have outputExtremal := rescaledSubfiber_extremal_of_source_density
    chart.metricFiber.frozenRescaled sourceSub literalImage
    (chart.sliceDensity / 2) sourceMass
    (cutoff.initial.sticky_lt_local.le.trans
      cutoff.initial.local_lt_lemma43.le)
    (cutoff.initial.sticky_pos.trans
      (cutoff.initial.sticky_lt_local.trans cutoff.initial.local_lt_lemma43))
    qSmallRatio (by simpa only [ratioEq] using outputAbsorb)
  let output : GenericFirstChartWholeCellOutput first chart := {
    familyData := chart.metricFiber.frozenRescaled.familyData
    literalShading := literalImage
    jacobianConstant := chart.metricFiber.frozenRescaled.jacobianConstant
    jacobianConstant_one :=
      chart.metricFiber.frozenRescaled.jacobianConstant_one
    jacobianConstant_finite :=
      chart.metricFiber.frozenRescaled.jacobianConstant_finite
    rescalingCertificate :=
      chart.metricFiber.frozenRescaled.rescalingCertificate
    extremal := outputExtremal
    source_cardinality_eq :=
      chart.metricFiber.frozenRescaled.source_cardinality_eq
  }
  have massLower := chart.wholeCell_trace_massLower
    first.current.normalization output (qSmallRatio.trans (by norm_num))
    (by simpa only [ratioEq] using traceAbsorb)
  have canonicalTop := first.firstChartNormalizedTopLevelCWA chart qSmallRatio
  have topCWA : WZ2PaperConvexWolffBound
      (chart.wholeCellTraceOrdinarySource first.current.normalization
        output massLower).family
      ((4 : ENNReal) * Kakeya.realRpowENN
        (delta / first.power.requested.1) (-cutoff.initial.stickyLoss)) := by
    simpa only [ratioEq,
      Proposition63FirstChartData.wholeCellTraceOrdinarySource,
      Proposition63FirstChartData.wholeCellChartOrdinaryExtremalSourceOfTraceMass,
      proposition63ChartOrdinaryExtremalSourceOfTraceMass,
      proposition63TransportPureExtremal,
      WZ2PaperPureRescaledFullFiberOutput.withNormalizationFinalOrdinaryTraceOfMass,
      WZ2PaperPureRescaledFullFiberOutput.withNormalizationFinalOrdinaryTrace,
      WZ2PaperPureRescaledFullFiberOutput.withOrdinaryExactImage,
      criticalRescaledFiberToExtremalConfiguration,
      Proposition63ChartSelectionData.normalizedFamily] using canonicalTop
  exact firstChartDenseRootCanonicalOfOutput cutoff first chart output massLower
    topCWA hdelta firstLower qSmall hsigmaOne

end Proposition63GenericFirstRichBoundaryData
end Kakeya.Assouad.PureWZ2
end
