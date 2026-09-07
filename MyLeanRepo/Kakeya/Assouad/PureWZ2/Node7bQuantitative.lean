import MyLeanRepo.Kakeya.Assouad.PureWZ2.AnalyticCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PowerAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.BoundedDeltaMax
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Quantitative bookkeeping for pure WZ2 Node 7b

The lemmas here contain only fixed-scale `ENNReal` arithmetic.  In
particular, they do not add analytic conclusions to the Node-3 normalization
record or to the Node-6 large-slope configuration.
-/

noncomputable section

open MeasureTheory
open Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Assouad

/-- A uniform numerical majorant for the loss in the two analytic-cleanup
branches. -/
lemma pure_wz2_cleanup_loss_le
    {delta eta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (heta : 0 < eta) (net : TubeDensityTestNet delta)
    (hnet : net.lossFactor ≤ (10^7 : ENNReal)) :
    27000000000 *
          (net.lossFactor * 10 * Kakeya.realRpowENN delta (-eta)) + 1 ≤
      (2700000000000000001 : ENNReal) *
        Kakeya.realRpowENN delta (-eta) := by
  let target := Kakeya.realRpowENN delta (-eta)
  have htarget_one : (1 : ENNReal) ≤ target := by
    have hreal : 1 ≤ Real.rpow delta (-eta) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta_one
        (show -eta ≤ 0 by linarith)
    have henn := ENNReal.ofReal_mono hreal
    simpa [target, Kakeya.realRpowENN] using henn
  calc
    27000000000 * (net.lossFactor * 10 * target) + 1
        ≤ 27000000000 * ((10^7 : ENNReal) * 10 * target) + target := by
          gcongr
    _ = (2700000000000000001 : ENNReal) * target := by
          norm_num
          ring

/-- The cleanup loss is positive and finite. -/
lemma pure_wz2_cleanup_loss_ne_zero_top
    {delta eta : ℝ} (net : TubeDensityTestNet delta) :
    27000000000 *
          (net.lossFactor * 10 * Kakeya.realRpowENN delta (-eta)) + 1 ≠ 0 ∧
      27000000000 *
          (net.lossFactor * 10 * Kakeya.realRpowENN delta (-eta)) + 1 ≠ ⊤ := by
  constructor
  · positivity
  · exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top net.lossFactor_ne_top (by norm_num))
          ENNReal.ofReal_ne_top), ENNReal.one_ne_top⟩

/-- Inverse of the positive finite real power used throughout the assembly. -/
lemma pure_wz2_realRpowENN_inv
    {delta exponent : ℝ} (hdelta : 0 < delta) :
    (Kakeya.realRpowENN delta exponent)⁻¹ =
      Kakeya.realRpowENN delta (-exponent) := by
  simp only [Kakeya.realRpowENN]
  calc
    (ENNReal.ofReal (Real.rpow delta exponent))⁻¹ =
        ENNReal.ofReal ((Real.rpow delta exponent)⁻¹) :=
      (ENNReal.ofReal_inv_of_pos
        (Real.rpow_pos_of_pos hdelta exponent)).symm
    _ = ENNReal.ofReal (Real.rpow delta (-exponent)) :=
      congrArg ENNReal.ofReal
        (Real.rpow_neg hdelta.le exponent).symm

/-- Both cleanup branches have the same absolute cardinality upper bound.
The proof uses only the actual sampling rate, bounded support, and the
ambient `deltaMax` bound supplied to the cleanup. -/
lemma pure_wz2_cleanup_family_card_le
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (ambient : Kakeya.Streamlined.TubeFamily delta)
    (ambientShading : Kakeya.Streamlined.TubeShading ambient)
    (target D : ENNReal) (net : TubeDensityTestNet delta)
    (data : PureWZ2AnalyticCleanupData
      ambient ambientShading target D net)
    (hsupport : ∀ i, (ambient.tube i).carrier ⊆
      Metric.closedBall (0 : Point3) 6)
    (hdeltaMax : ambient.toBodyFamily.deltaMax ≤ D)
    (htarget_D : target ≤ D) (htarget_zero : target ≠ 0)
    (hD_top : D ≠ ⊤) :
    data.family.enncard ≤
      2400 * target * (Kakeya.deltaTubeVolume delta)⁻¹ := by
  have hballPos :
      0 < volume (Metric.closedBall (0 : Point3) 6) :=
    Metric.measure_closedBall_pos volume (0 : Point3) (by norm_num)
  have hballTop :
      volume (Metric.closedBall (0 : Point3) 6) ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num) volume_closedBall_six_le
  have hsample := tubeFamily_sampling_card_le_of_support
    hdelta hdelta_one ambient hsupport target D hdeltaMax
    htarget_D htarget_zero hD_top hballPos hballTop
  calc
    data.family.enncard
        ≤ 2 * data.samplingRate * ambient.enncard := data.family_card_le
    _ = 2 * ((target / D) * ambient.enncard) := by
          rw [data.samplingRate_eq]
          ring
    _ ≤ 2 * (target * volume (Metric.closedBall (0 : Point3) 6) *
          (Kakeya.deltaTubeVolume delta)⁻¹) := by gcongr
    _ ≤ 2 * (target * 1200 *
          (Kakeya.deltaTubeVolume delta)⁻¹) := by
            gcongr
            exact volume_closedBall_six_le
    _ = 2400 * target * (Kakeya.deltaTubeVolume delta)⁻¹ := by ring

/-- Replace inverse tube volume by the canonical `delta⁻²` power. -/
lemma pure_wz2_cleanup_family_card_power_le
    {delta eta : ℝ} (hdelta : 0 < delta)
    {card : ENNReal}
    (hcard : card ≤ 2400 * Kakeya.realRpowENN delta (-eta) *
      (Kakeya.deltaTubeVolume delta)⁻¹) :
    card ≤ 2400 * Kakeya.realRpowENN delta (-2 - eta) := by
  have hVinv : (Kakeya.deltaTubeVolume delta)⁻¹ ≤
      Kakeya.realRpowENN delta (-2) := by
    have hinv := ENNReal.inv_le_inv.mpr (canonical_volume_lower hdelta)
    have hpowTwo : ENNReal.ofReal (delta ^ 2) =
        Kakeya.realRpowENN delta 2 := by
      simp [Kakeya.realRpowENN, Real.rpow_two]
    rw [hpowTwo, pure_wz2_realRpowENN_inv hdelta] at hinv
    simpa using hinv
  calc
    card ≤ 2400 * Kakeya.realRpowENN delta (-eta) *
        (Kakeya.deltaTubeVolume delta)⁻¹ := hcard
    _ ≤ 2400 * Kakeya.realRpowENN delta (-eta) *
        Kakeya.realRpowENN delta (-2) := by gcongr
    _ = 2400 * Kakeya.realRpowENN delta (-2 - eta) := by
      rw [show -2 - eta = -eta + -2 by ring, realRpowENN_add hdelta]
      ring

/-- Fixed denominator in the paper-CWA sampling lower bound. -/
def pureWZ2SamplingConstant : ENNReal :=
  222264000 * Kakeya.deltaTubeVolume 1

lemma pureWZ2SamplingConstant_pos : 0 < pureWZ2SamplingConstant := by
  exact ENNReal.mul_pos (by norm_num)
    (tube_volume_scaling.2.1 1 (by norm_num) (by norm_num)).1.ne'

lemma pureWZ2SamplingConstant_ne_top : pureWZ2SamplingConstant ≠ ⊤ := by
  exact ENNReal.mul_ne_top (by norm_num)
    (tube_volume_scaling.2.1 1 (by norm_num) (by norm_num)).2

lemma pureWZ2SamplingConstant_toReal_pos :
    0 < pureWZ2SamplingConstant.toReal :=
  ENNReal.toReal_pos pureWZ2SamplingConstant_pos.ne'
    pureWZ2SamplingConstant_ne_top

lemma pureWZ2FinalFloorConstant_ne_zero :
    (2 * (2700000000000000001 : ENNReal) *
      pureWZ2SamplingConstant)⁻¹ ≠ 0 := by
  exact ENNReal.inv_ne_zero.mpr
    (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (by norm_num))
      pureWZ2SamplingConstant_ne_top)

lemma pureWZ2FinalFloorConstant_ne_top :
    (2 * (2700000000000000001 : ENNReal) *
      pureWZ2SamplingConstant)⁻¹ ≠ ⊤ := by
  exact ENNReal.inv_ne_top.mpr
    (mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num))
      pureWZ2SamplingConstant_pos.ne')

/-- A denominator upper bound gives the corresponding Bernoulli
`samplingRate * ambientCard` lower bound. -/
lemma pure_wz2_sampling_card_lower
    (target D A card : ENNReal)
    (htarget_zero : target ≠ 0) (htarget_D : target ≤ D)
    (hD_top : D ≠ ⊤)
    (hA_zero : A ≠ 0) (hA_top : A ≠ ⊤)
    (hD : D ≤ A * card) :
    A⁻¹ * target ≤ (target / D) * card := by
  have hDzero : D ≠ 0 := by
    intro hzero
    rw [hzero] at htarget_D
    exact htarget_zero (bot_unique htarget_D)
  apply (ENNReal.mul_le_mul_iff_left hA_zero hA_top).mp
  calc
    (A⁻¹ * target) * A = target := by
      rw [show A⁻¹ * target * A = target * (A⁻¹ * A) by ring]
      rw [ENNReal.inv_mul_cancel hA_zero hA_top, mul_one]
    _ = (target / D) * D := by
      rw [ENNReal.div_mul_cancel hDzero hD_top]
    _ ≤ (target / D) * (A * card) := by gcongr
    _ = ((target / D) * card) * A := by ring

/-- Generalized second Bernoulli failure estimate with an explicit positive
sampling denominator. -/
lemma pure_wz2_thinning_failure_bound
    {delta exponent z constant : ℝ}
    (hcoeff : 0 < 3 - Real.exp 1) (hconstant : 0 < constant)
    (hz : constant⁻¹ * Real.rpow delta exponent ≤ z)
    (hasym : ((3 - Real.exp 1) / constant) *
      Real.rpow delta exponent > Real.log 16) :
    Real.exp (-(3 - Real.exp 1) * z) < 1 / 16 := by
  have hlog : (3 - Real.exp 1) * z > Real.log 16 := by
    have hle : (3 - Real.exp 1) *
        (constant⁻¹ * Real.rpow delta exponent) ≤
        (3 - Real.exp 1) * z :=
      mul_le_mul_of_nonneg_left hz hcoeff.le
    have heq : (3 - Real.exp 1) *
        (constant⁻¹ * Real.rpow delta exponent) =
        ((3 - Real.exp 1) / constant) *
          Real.rpow delta exponent := by
      field_simp [hconstant.ne']
    rw [heq] at hle
    exact hasym.trans_le hle
  have hstrict : Real.exp (-((3 - Real.exp 1) * z)) <
      Real.exp (-Real.log 16) :=
    Real.exp_strictMono (neg_lt_neg hlog)
  have hexp : Real.exp (-Real.log 16) = 1 / 16 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
    field_simp
  rw [hexp] at hstrict
  have harg : -(3 - Real.exp 1) * z =
      -((3 - Real.exp 1) * z) := by ring
  rw [harg]
  exact hstrict

/-- The paper-CWA `deltaMax` upper bound and the quadratic tube-volume upper
bound imply a power lower bound for the sampled ambient cardinality. -/
lemma pure_wz2_high_sampling_card_power_lower
    {delta coreLoss thinEta : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (ambientCard D : ENNReal) (hcard_top : ambientCard ≠ ⊤)
    (hD_top : D ≠ ⊤)
    (hD : D ≤ 9261000 * Kakeya.realRpowENN delta (-coreLoss) *
      ambientCard * Kakeya.deltaTubeVolume delta)
    (htarget_D : Kakeya.realRpowENN delta (-thinEta) ≤ D) :
    pureWZ2SamplingConstant⁻¹ *
        Kakeya.realRpowENN delta (-2 + coreLoss - thinEta) ≤
      (Kakeya.realRpowENN delta (-thinEta) / D) * ambientCard := by
  let target := Kakeya.realRpowENN delta (-thinEta)
  let A := 9261000 * Kakeya.realRpowENN delta (-coreLoss) *
    Kakeya.deltaTubeVolume delta
  have htarget_zero : target ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)).ne'
  have hAzero : A ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num)
        (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)).ne')
      (tube_volume_scaling.2.1 delta hdelta hdelta_one).1.ne'
  have hAtop : A ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      (tube_volume_scaling.2.1 delta hdelta hdelta_one).2
  have hD' : D ≤ A * ambientCard := by
    simpa [A, mul_assoc, mul_comm, mul_left_comm] using hD
  have hsample := pure_wz2_sampling_card_lower
    target D A ambientCard htarget_zero htarget_D hD_top
    hAzero hAtop hD'
  have hVupper : Kakeya.deltaTubeVolume delta ≤
      24 * Kakeya.realRpowENN delta 2 * Kakeya.deltaTubeVolume 1 := by
    let canonical : Kakeya.DeltaTube delta :=
      { base := 0
        direction := EuclideanSpace.single (0 : Fin 3) 1
        direction_unit := by simp <;> norm_num }
    exact tube_volume_scaling.2.2 delta hdelta hdelta_one canonical
  have hpowerA : A ≤ pureWZ2SamplingConstant *
      Kakeya.realRpowENN delta (2 - coreLoss) := by
    calc
      A ≤ 9261000 * Kakeya.realRpowENN delta (-coreLoss) *
          (24 * Kakeya.realRpowENN delta 2 *
            Kakeya.deltaTubeVolume 1) := by
              dsimp only [A]
              gcongr
      _ = pureWZ2SamplingConstant *
          Kakeya.realRpowENN delta (2 - coreLoss) := by
            rw [show 2 - coreLoss = -coreLoss + 2 by ring,
              realRpowENN_add hdelta]
            simp [pureWZ2SamplingConstant]
            ring
  have hleftA :
      (pureWZ2SamplingConstant⁻¹ *
          Kakeya.realRpowENN delta (-2 + coreLoss - thinEta)) * A ≤
        target := by
    calc
      _ ≤ (pureWZ2SamplingConstant⁻¹ *
          Kakeya.realRpowENN delta (-2 + coreLoss - thinEta)) *
            (pureWZ2SamplingConstant *
              Kakeya.realRpowENN delta (2 - coreLoss)) := by gcongr
      _ = target := by
        rw [show pureWZ2SamplingConstant⁻¹ *
              Kakeya.realRpowENN delta (-2 + coreLoss - thinEta) *
              (pureWZ2SamplingConstant *
                Kakeya.realRpowENN delta (2 - coreLoss)) =
            (pureWZ2SamplingConstant⁻¹ * pureWZ2SamplingConstant) *
              (Kakeya.realRpowENN delta (-2 + coreLoss - thinEta) *
                Kakeya.realRpowENN delta (2 - coreLoss)) by ring]
        rw [ENNReal.inv_mul_cancel pureWZ2SamplingConstant_pos.ne'
          pureWZ2SamplingConstant_ne_top, one_mul]
        rw [← realRpowENN_add hdelta]
        change Kakeya.realRpowENN delta
            ((-2 + coreLoss - thinEta) + (2 - coreLoss)) =
          Kakeya.realRpowENN delta (-thinEta)
        congr 1 <;> ring
  have hAinv : pureWZ2SamplingConstant⁻¹ *
      Kakeya.realRpowENN delta (-2 + coreLoss - thinEta) ≤
        A⁻¹ * target := by
    have hmul :
        (pureWZ2SamplingConstant⁻¹ *
          Kakeya.realRpowENN delta (-2 + coreLoss - thinEta)) * A ≤
          target := hleftA
    apply (ENNReal.mul_le_mul_iff_left hAzero hAtop).mp
    calc
      (pureWZ2SamplingConstant⁻¹ *
          Kakeya.realRpowENN delta (-2 + coreLoss - thinEta)) * A
          ≤ target := hmul
      _ = (A⁻¹ * target) * A := by
        rw [show A⁻¹ * target * A = target * (A⁻¹ * A) by ring]
        rw [ENNReal.inv_mul_cancel hAzero hAtop, mul_one]
  exact hAinv.trans hsample

/-- Combine the sampled-cardinality lower bound, ambient density, and
weighted conflict cleanup into the final absolute cardinality floor. -/
lemma pure_wz2_cleanup_cardinality_floor
    {delta coreLoss thinEta : ℝ} (hdelta : 0 < delta)
    (net : TubeDensityTestNet delta)
    (loss sampleCard finalCard : ENNReal)
    (hLzero : loss ≠ 0) (hLtop : loss ≠ ⊤)
    (hloss : loss ≤ (2700000000000000001 : ENNReal) *
      Kakeya.realRpowENN delta (-thinEta))
    (hsample : pureWZ2SamplingConstant⁻¹ *
        Kakeya.realRpowENN delta (-2 + coreLoss - thinEta) ≤ sampleCard)
    (hretention : loss⁻¹ *
        ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta coreLoss * sampleCard) ≤
      finalCard) :
    ((2 : ENNReal) * 2700000000000000001 *
        pureWZ2SamplingConstant)⁻¹ *
      Kakeya.realRpowENN delta
        (-2 + 2 * coreLoss) ≤ finalCard := by
  have hconstantZero :
      (2 : ENNReal) * 2700000000000000001 *
          pureWZ2SamplingConstant ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num))
      pureWZ2SamplingConstant_pos.ne'
  have hconstantTop :
      (2 : ENNReal) * 2700000000000000001 *
          pureWZ2SamplingConstant ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (by norm_num))
      pureWZ2SamplingConstant_ne_top
  have hLinv :
      ((2700000000000000001 : ENNReal) *
          Kakeya.realRpowENN delta (-thinEta))⁻¹ ≤ loss⁻¹ :=
    ENNReal.inv_le_inv.mpr hloss
  calc
    ((2 : ENNReal) * 2700000000000000001 *
          pureWZ2SamplingConstant)⁻¹ *
        Kakeya.realRpowENN delta
          (-2 + 2 * coreLoss)
        = (((2700000000000000001 : ENNReal) *
              Kakeya.realRpowENN delta (-thinEta))⁻¹) *
            ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta coreLoss *
              (pureWZ2SamplingConstant⁻¹ *
                Kakeya.realRpowENN delta
                  (-2 + coreLoss - thinEta))) := by
            rw [ENNReal.mul_inv (Or.inl (by norm_num))
              (Or.inl (by norm_num))]
            have hsplit : ((2 : ENNReal) * 2700000000000000001)⁻¹ =
                (2 : ENNReal)⁻¹ * (2700000000000000001 : ENNReal)⁻¹ := by
              exact ENNReal.mul_inv (Or.inl (by norm_num))
                (Or.inl (by norm_num))
            rw [hsplit]
            have hrpowZero :
                Kakeya.realRpowENN delta (-thinEta) ≠ 0 :=
              (ENNReal.ofReal_pos.mpr
                (Real.rpow_pos_of_pos hdelta _)).ne'
            have hrpowTop :
                Kakeya.realRpowENN delta (-thinEta) ≠ ⊤ :=
              ENNReal.ofReal_ne_top
            have hlossSplit :
                ((2700000000000000001 : ENNReal) *
                    Kakeya.realRpowENN delta (-thinEta))⁻¹ =
                  (2700000000000000001 : ENNReal)⁻¹ *
                    (Kakeya.realRpowENN delta (-thinEta))⁻¹ :=
              ENNReal.mul_inv (Or.inl (by norm_num))
                (Or.inl (by norm_num))
            rw [hlossSplit]
            rw [pure_wz2_realRpowENN_inv hdelta]
            norm_num
            have hpow :
                Kakeya.realRpowENN delta thinEta *
                    Kakeya.realRpowENN delta coreLoss *
                    Kakeya.realRpowENN delta
                      (-2 + coreLoss - thinEta) =
                  Kakeya.realRpowENN delta (-2 + 2 * coreLoss) := by
              rw [← realRpowENN_add hdelta, ← realRpowENN_add hdelta]
              congr 1
              ring
            rw [show (2700000000000000001 : ENNReal)⁻¹ *
                  Kakeya.realRpowENN delta thinEta *
                  ((2 : ENNReal)⁻¹ *
                    Kakeya.realRpowENN delta coreLoss *
                    (pureWZ2SamplingConstant⁻¹ *
                      Kakeya.realRpowENN delta
                        (-2 + coreLoss - thinEta))) =
                (2 : ENNReal)⁻¹ *
                  (2700000000000000001 : ENNReal)⁻¹ *
                  pureWZ2SamplingConstant⁻¹ *
                  (Kakeya.realRpowENN delta thinEta *
                    Kakeya.realRpowENN delta coreLoss *
                    Kakeya.realRpowENN delta
                      (-2 + coreLoss - thinEta)) by ring]
            rw [hpow]
    _ ≤ loss⁻¹ *
          ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta coreLoss *
            sampleCard) := by gcongr
    _ ≤ finalCard := hretention

/-- Identity thinning in the low-`deltaMax` branch starts from the paper-CWA
cardinality floor. -/
lemma pure_wz2_cleanup_cardinality_floor_low
    {delta coreLoss thinEta : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (net : TubeDensityTestNet delta)
    (loss ambientCard finalCard : ENNReal)
    (hLzero : loss ≠ 0) (hLtop : loss ≠ ⊤)
    (hloss : loss ≤ (2700000000000000001 : ENNReal) *
      Kakeya.realRpowENN delta (-thinEta))
    (hambient : Kakeya.realRpowENN delta (-2 + 2 * coreLoss) ≤ ambientCard)
    (hretention : loss⁻¹ *
        ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta coreLoss * ambientCard) ≤
      finalCard) :
    ((2 : ENNReal) * 2700000000000000001 *
        pureWZ2SamplingConstant)⁻¹ *
      Kakeya.realRpowENN delta
        (-2 + 3 * coreLoss + thinEta) ≤ finalCard := by
  have hsampleConstantOne : (1 : ENNReal) ≤ pureWZ2SamplingConstant := by
    dsimp only [pureWZ2SamplingConstant]
    calc
      (1 : ENNReal) ≤ Kakeya.deltaTubeVolume 1 := one_le_deltaTubeVolume_one
      _ ≤ 222264000 * Kakeya.deltaTubeVolume 1 := by
        simpa using mul_le_mul_right'
          (show (1 : ENNReal) ≤ 222264000 by norm_num)
          (Kakeya.deltaTubeVolume 1)
  have hconstantInv :
      ((2 : ENNReal) * 2700000000000000001 *
          pureWZ2SamplingConstant)⁻¹ ≤
        ((2 : ENNReal) * 2700000000000000001)⁻¹ := by
    apply ENNReal.inv_le_inv.mpr
    calc
      (2 : ENNReal) * 2700000000000000001
          = (2 * 2700000000000000001) * 1 := by ring
      _ ≤ (2 * 2700000000000000001) * pureWZ2SamplingConstant := by gcongr
      _ = 2 * 2700000000000000001 * pureWZ2SamplingConstant := rfl
  have hLinv :
      ((2700000000000000001 : ENNReal) *
          Kakeya.realRpowENN delta (-thinEta))⁻¹ ≤ loss⁻¹ :=
    ENNReal.inv_le_inv.mpr hloss
  calc
    ((2 : ENNReal) * 2700000000000000001 *
          pureWZ2SamplingConstant)⁻¹ *
        Kakeya.realRpowENN delta (-2 + 3 * coreLoss + thinEta)
        ≤ ((2 : ENNReal) * 2700000000000000001)⁻¹ *
          Kakeya.realRpowENN delta (-2 + 3 * coreLoss + thinEta) := by
            gcongr
    _ = (((2700000000000000001 : ENNReal) *
            Kakeya.realRpowENN delta (-thinEta))⁻¹) *
          ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta coreLoss *
            Kakeya.realRpowENN delta (-2 + 2 * coreLoss)) := by
          have hsplit : ((2 : ENNReal) * 2700000000000000001)⁻¹ =
              (2 : ENNReal)⁻¹ * (2700000000000000001 : ENNReal)⁻¹ :=
            ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))
          rw [hsplit]
          have hlossSplit :
              ((2700000000000000001 : ENNReal) *
                  Kakeya.realRpowENN delta (-thinEta))⁻¹ =
                (2700000000000000001 : ENNReal)⁻¹ *
                  Kakeya.realRpowENN delta thinEta := by
            rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
              pure_wz2_realRpowENN_inv hdelta]
            congr 2 <;> ring
          rw [hlossSplit]
          norm_num
          rw [show (2700000000000000001 : ENNReal)⁻¹ *
                Kakeya.realRpowENN delta thinEta *
                ((2 : ENNReal)⁻¹ * Kakeya.realRpowENN delta coreLoss *
                  Kakeya.realRpowENN delta (-2 + 2 * coreLoss)) =
              (2 : ENNReal)⁻¹ *
                (2700000000000000001 : ENNReal)⁻¹ *
                (Kakeya.realRpowENN delta thinEta *
                  Kakeya.realRpowENN delta coreLoss *
                  Kakeya.realRpowENN delta (-2 + 2 * coreLoss)) by ring]
          rw [← realRpowENN_add hdelta, ← realRpowENN_add hdelta]
          congr 2 <;> ring
    _ ≤ loss⁻¹ *
          ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta coreLoss *
            ambientCard) := by gcongr
    _ ≤ finalCard := hretention

/-- Absorb the cleanup loss into the requested final lambda density. -/
lemma pure_wz2_cleanup_density_absorption
    {delta coreLoss thinEta analyticLoss : ℝ}
    (hdelta : 0 < delta)
    (target loss : ENNReal)
    (htarget : target = Kakeya.realRpowENN delta (-thinEta))
    (hloss : loss ≤ (2700000000000000001 : ENNReal) * target)
    (hconstant : 4 * (2700000000000000001 : ENNReal) ≤
      Kakeya.realRpowENN delta
        (-(analyticLoss - coreLoss - thinEta))) :
    Kakeya.realRpowENN delta analyticLoss * 2 * loss ≤
      (1 / 2 : ENNReal) * Kakeya.realRpowENN delta coreLoss := by
  calc
    Kakeya.realRpowENN delta analyticLoss * 2 * loss
        ≤ Kakeya.realRpowENN delta analyticLoss * 2 *
            ((2700000000000000001 : ENNReal) * target) := by gcongr
    _ = ((4 * (2700000000000000001 : ENNReal)) *
          Kakeya.realRpowENN delta
            (analyticLoss - coreLoss - thinEta)) *
        ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta coreLoss) := by
      rw [htarget]
      have hpow : Kakeya.realRpowENN delta analyticLoss *
            Kakeya.realRpowENN delta (-thinEta) =
          Kakeya.realRpowENN delta (analyticLoss - thinEta) := by
        rw [← realRpowENN_add hdelta]
        congr 1 <;> ring
      have hcoeff : Kakeya.realRpowENN delta analyticLoss * 2 *
            ((2700000000000000001 : ENNReal) *
              Kakeya.realRpowENN delta (-thinEta)) =
          (4 * (2700000000000000001 : ENNReal)) *
            (Kakeya.realRpowENN delta analyticLoss *
              Kakeya.realRpowENN delta (-thinEta)) * (1 / 2) := by
        have hfourHalf : (4 : ENNReal) * (1 / 2 : ENNReal) = 2 := by
          rw [show (4 : ENNReal) = 2 * 2 by norm_num,
            show (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ by
              simp [div_eq_mul_inv]]
          rw [mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
            mul_one]
        calc
          Kakeya.realRpowENN delta analyticLoss * 2 *
                ((2700000000000000001 : ENNReal) *
                  Kakeya.realRpowENN delta (-thinEta)) =
              (2700000000000000001 : ENNReal) *
                (Kakeya.realRpowENN delta analyticLoss *
                  Kakeya.realRpowENN delta (-thinEta)) * 2 := by ring
          _ = (2700000000000000001 : ENNReal) *
                (Kakeya.realRpowENN delta analyticLoss *
                  Kakeya.realRpowENN delta (-thinEta)) *
                    (4 * (1 / 2)) := by rw [hfourHalf]
          _ = (4 * (2700000000000000001 : ENNReal)) *
              (Kakeya.realRpowENN delta analyticLoss *
                Kakeya.realRpowENN delta (-thinEta)) * (1 / 2) := by ring
      rw [hcoeff, hpow]
      rw [show analyticLoss - thinEta =
          (analyticLoss - coreLoss - thinEta) + coreLoss by ring,
        realRpowENN_add hdelta]
      ring
    _ ≤ (1 / 2 : ENNReal) * Kakeya.realRpowENN delta coreLoss := by
      have hmul := mul_le_mul_right' hconstant
        (Kakeya.realRpowENN delta
          (analyticLoss - coreLoss - thinEta))
      rw [← realRpowENN_add hdelta] at hmul
      have hone : (4 * (2700000000000000001 : ENNReal)) *
          Kakeya.realRpowENN delta (analyticLoss - coreLoss - thinEta) ≤ 1 := by
        simpa [Kakeya.realRpowENN] using hmul
      simpa using mul_le_mul_right' hone
        ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta coreLoss)

/-- Absorb a fixed nonconcentration constant against the absolute cleanup
cardinality floor. -/
lemma pure_wz2_normalized_nonconcentration_absorption
    {delta analyticLoss coreLoss thinEta : ℝ}
    (hdelta : 0 < delta) (fixed : ENNReal)
    (hfixed :
      (2 * (2700000000000000001 : ENNReal) *
          pureWZ2SamplingConstant) * fixed ≤
        Kakeya.realRpowENN delta
          (-(analyticLoss - 3 * coreLoss - 2 * thinEta))) :
    fixed * Kakeya.realRpowENN delta (-thinEta) *
        Kakeya.realRpowENN delta (-2) ≤
      Kakeya.realRpowENN delta (-analyticLoss) *
        ((2 * (2700000000000000001 : ENNReal) *
            pureWZ2SamplingConstant)⁻¹ *
          Kakeya.realRpowENN delta (-2 + 3 * coreLoss + thinEta)) := by
  let L : ENNReal :=
    2 * (2700000000000000001 : ENNReal) * pureWZ2SamplingConstant
  have hLzero : L ≠ 0 := by
    dsimp only [L]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num))
      pureWZ2SamplingConstant_pos.ne'
  have hLtop : L ≠ ⊤ := by
    dsimp only [L]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (by norm_num))
      pureWZ2SamplingConstant_ne_top
  have hcancel : fixed ≤ L⁻¹ *
      Kakeya.realRpowENN delta
        (-(analyticLoss - 3 * coreLoss - 2 * thinEta)) := by
    have h := mul_le_mul_left' hfixed L⁻¹
    rw [show L⁻¹ * (L * fixed) = (L⁻¹ * L) * fixed by ring,
      ENNReal.inv_mul_cancel hLzero hLtop, one_mul] at h
    simpa [L] using h
  calc
    fixed * Kakeya.realRpowENN delta (-thinEta) *
          Kakeya.realRpowENN delta (-2)
        ≤ (L⁻¹ * Kakeya.realRpowENN delta
            (-(analyticLoss - 3 * coreLoss - 2 * thinEta))) *
          Kakeya.realRpowENN delta (-thinEta) *
            Kakeya.realRpowENN delta (-2) := by gcongr
    _ = Kakeya.realRpowENN delta (-analyticLoss) *
        (L⁻¹ * Kakeya.realRpowENN delta
          (-2 + 3 * coreLoss + thinEta)) := by
      have hpow : Kakeya.realRpowENN delta
            (-(analyticLoss - 3 * coreLoss - 2 * thinEta)) *
          Kakeya.realRpowENN delta (-thinEta) *
          Kakeya.realRpowENN delta (-2) =
        Kakeya.realRpowENN delta (-analyticLoss) *
          Kakeya.realRpowENN delta (-2 + 3 * coreLoss + thinEta) := by
        rw [← realRpowENN_add hdelta, ← realRpowENN_add hdelta,
          ← realRpowENN_add hdelta]
        congr 1
        ring
      rw [show L⁻¹ * Kakeya.realRpowENN delta
              (-(analyticLoss - 3 * coreLoss - 2 * thinEta)) *
            Kakeya.realRpowENN delta (-thinEta) *
            Kakeya.realRpowENN delta (-2) =
          L⁻¹ * (Kakeya.realRpowENN delta
              (-(analyticLoss - 3 * coreLoss - 2 * thinEta)) *
            Kakeya.realRpowENN delta (-thinEta) *
            Kakeya.realRpowENN delta (-2)) by ring, hpow]
      ring
    _ = Kakeya.realRpowENN delta (-analyticLoss) *
        ((2 * (2700000000000000001 : ENNReal) *
            pureWZ2SamplingConstant)⁻¹ *
          Kakeya.realRpowENN delta (-2 + 3 * coreLoss + thinEta)) := rfl

end Kakeya.Assouad

end
