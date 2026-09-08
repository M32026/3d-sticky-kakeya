import MyLeanRepo.Kakeya.Integration.CompetitorFullFiberStructure
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.AllScaleUniformityBound
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.AssemblyHelpers
import MyLeanRepo.Kakeya.Streamlined.TubePacking.UnitBall
import MyLeanRepo.Kakeya.Streamlined.PlankKatzTao.PowerAbsorptionAlgebra
import Kakeya.MultiScaleLoss

/-!
# Power absorption for the competitor all-real hierarchy

This module isolates the numerical estimates needed after the geometric
competitor-to-WZ2 construction.  All thresholds in the final theorem will be
chosen before the runtime scale, family, hierarchy, and selected survivor.
-/

noncomputable section

namespace Kakeya.Integration

open Kakeya.Streamlined
open Kakeya.Streamlined.RandomTranslation
open Kakeya.Streamlined.RandomTranslation.WithShading
open CompetitorStickyInput

/-- The competitor grid length exceeds every fixed real bound once the runtime
scale is sufficiently small.  Kept here to avoid importing the unrelated
cross-scale Katz--Tao geometry into the WZ2 producer closure. -/
theorem exists_threshold_le_competitor_ssfGridLen (K : ℝ) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ ∀ {delta : NNReal}, 0 < delta →
      (delta : ℝ) ≤ delta₀ → K ≤ (Tube.ssfGridLen delta : ℝ) := by
  let delta₀ : ℝ := min (Real.exp (-(Real.exp (max K 0)))) (1 / 2)
  refine ⟨delta₀, ?_, ?_⟩
  · exact lt_min (Real.exp_pos _) (by norm_num)
  · intro delta hdelta hdeltale
    have hdeltaR : (0 : ℝ) < (delta : ℝ) := by exact_mod_cast hdelta
    have hdelta1 : 0 < 1 / (delta : ℝ) := one_div_pos.mpr hdeltaR
    have hdeltale_eval :
        (delta : ℝ) ≤ Real.exp (-(Real.exp (max K 0))) :=
      hdeltale.trans (min_le_left _ _)
    have hE : Real.exp (Real.exp (max K 0)) ≤ 1 / (delta : ℝ) := by
      have hht : (delta : ℝ) ≤ (Real.exp (Real.exp (max K 0)))⁻¹ := by
        rw [← Real.exp_neg]
        exact hdeltale_eval
      have hEpos : 0 < Real.exp (Real.exp (max K 0)) := Real.exp_pos _
      have hmul :
          (delta : ℝ) * Real.exp (Real.exp (max K 0)) ≤ 1 := by
        calc
          (delta : ℝ) * Real.exp (Real.exp (max K 0)) ≤
              (Real.exp (Real.exp (max K 0)))⁻¹ *
                Real.exp (Real.exp (max K 0)) :=
            mul_le_mul_of_nonneg_right hht hEpos.le
          _ = 1 := inv_mul_cancel₀ hEpos.ne'
      exact (le_div_iff₀ hdeltaR).mpr (by simpa [mul_comm] using hmul)
    have hexp_le_log : Real.exp (max K 0) ≤ Real.log (1 / (delta : ℝ)) :=
      (Real.le_log_iff_exp_le hdelta1).mpr hE
    have hdeltalt1 : (delta : ℝ) < 1 := by
      have hle : (delta : ℝ) ≤ 1 / 2 := hdeltale.trans (min_le_right _ _)
      linarith
    have hlogpos : 0 < Real.log (1 / (delta : ℝ)) :=
      Real.log_pos (one_lt_one_div hdeltaR hdeltalt1)
    have hmax : max K 0 ≤ Real.log (Real.log (1 / (delta : ℝ))) :=
      (Real.le_log_iff_exp_le hlogpos).mpr hexp_le_log
    have hceil : Real.log (Real.log (1 / (delta : ℝ))) ≤
        (Tube.ssfGridLen delta : ℝ) := by
      dsimp [Tube.ssfGridLen]
      exact Nat.le_ceil (Real.log (Real.log (1 / (delta : ℝ))))
    exact (le_max_left K 0).trans (hmax.trans hceil)

/-- A single coarse envelope for both losses of the weighted simultaneous
coordinate selector. -/
def competitorFiniteQuotientProfileEnvelope
    (N sourceCard : ℕ) : ENNReal :=
  (64 *
    (weightedFiniteCoordinateFiberCoreBinCount sourceCard : ENNReal)) ^
      (5 * N + 5)

/-- Fixed coefficient in the supporting-line quotient conflict estimate. -/
def competitorQuotientConflictConstant : ENNReal :=
  ENNReal.ofReal (3000 * (202 : ℝ) ^ 4 * 3000 ^ 7)

lemma competitorQuotientConflictConstant_ne_top :
    competitorQuotientConflictConstant ≠ ⊤ :=
  ENNReal.ofReal_ne_top

lemma competitorAllRealOutputDilation_one :
    1 ≤ dominatingUpperFromDilatedCoverDilation
      competitorSupportingLineQuotientDilation := by
  norm_num [dominatingUpperFromDilatedCoverDilation,
    competitorSupportingLineQuotientDilation,
    competitorSupportingLineCellDilation, composedDilatedCoverDilation]

/-- Fixed coefficient left after extracting the `33/N` degree power and the
single selector-profile envelope from all-real full-fiber uniformity. -/
def competitorAllRealUniformityFixedConstant : ENNReal :=
  fullContainmentBranchingLoss
      (dominatingUpperFromDilatedCoverDilation
        competitorSupportingLineQuotientDilation)
      competitorAllRealOutputDilation_one *
    (competitorQuotientConflictConstant *
        ENNReal.ofReal (2 + Real.pi + 8 / 3 * Real.pi) ^ 11 + 1)

lemma competitorAllRealUniformityFixedConstant_ne_top :
    competitorAllRealUniformityFixedConstant ≠ ⊤ := by
  unfold competitorAllRealUniformityFixedConstant
  exact ENNReal.mul_ne_top
    (fullContainmentBranchingLoss_ne_top _ _)
    (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top competitorQuotientConflictConstant_ne_top
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top), by norm_num⟩)

/-- Fixed part of the nearby-scale assigned-Frostman transport. -/
def competitorAllRealTransportFixedConstant : ENNReal :=
  ENNReal.ofReal (2 + Real.pi + 8 / 3 * Real.pi) *
    dilatedCoverVolumeFactor
      (dominatingUpperFromDilatedCoverDilation
        competitorSupportingLineQuotientDilation)

lemma competitorAllRealTransportFixedConstant_ne_top :
    competitorAllRealTransportFixedConstant ≠ ⊤ := by
  unfold competitorAllRealTransportFixedConstant
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- One fixed finite constant dominating every absolute factor used by the
competitor quotient-to-all-real route. -/
def competitorAllRealFixedConstant : ENNReal :=
  max competitorAllRealUniformityFixedConstant
    (max competitorAllRealTransportFixedConstant
      (max 2 competitorSupportingLineQuotientFrostmanLoss))

lemma competitorAllRealFixedConstant_ne_top :
    competitorAllRealFixedConstant ≠ ⊤ := by
  unfold competitorAllRealFixedConstant
  exact max_ne_top competitorAllRealUniformityFixedConstant_ne_top <|
    max_ne_top competitorAllRealTransportFixedConstant_ne_top <|
      max_ne_top (by norm_num)
        competitorSupportingLineQuotientFrostmanLoss_ne_top

lemma competitorAllRealUniformityFixedConstant_le_fixedConstant :
    competitorAllRealUniformityFixedConstant ≤
      competitorAllRealFixedConstant :=
  le_max_left _ _

lemma competitorAllRealTransportFixedConstant_le_fixedConstant :
    competitorAllRealTransportFixedConstant ≤
      competitorAllRealFixedConstant :=
  (le_max_left _ _).trans (le_max_right _ _)

lemma two_le_competitorAllRealFixedConstant :
    (2 : ENNReal) ≤ competitorAllRealFixedConstant :=
  (le_max_left _ _).trans <|
    (le_max_right _ _).trans (le_max_right _ _)

lemma competitorSupportingLineQuotientFrostmanLoss_le_fixedConstant :
    competitorSupportingLineQuotientFrostmanLoss ≤
      competitorAllRealFixedConstant :=
  (le_max_right _ _).trans <|
    (le_max_right _ _).trans (le_max_right _ _)

lemma explicitConflictConstant_le_competitorQuotientConflictConstant_mul
    {K : ℝ} (hK : 0 ≤ K) :
    ENNReal.ofReal (explicitConflictConstant K) ≤
      competitorQuotientConflictConstant * (ENNReal.ofReal K) ^ 7 := by
  unfold explicitConflictConstant competitorQuotientConflictConstant
  rw [show 3000 * (202 : ℝ) ^ 4 * (3000 * K) ^ 7 =
      (3000 * (202 : ℝ) ^ 4 * 3000 ^ 7) * K ^ 7 by ring]
  rw [ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow hK]

private lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 ≤ 2 ^ n + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add_left Nat.one_le_two_pow _
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

private lemma selector_base_one_le (sourceCard : ℕ) :
    (1 : ENNReal) ≤
      64 * (weightedFiniteCoordinateFiberCoreBinCount sourceCard : ENNReal) := by
  have hbin : (1 : ENNReal) ≤
      (weightedFiniteCoordinateFiberCoreBinCount sourceCard : ENNReal) := by
    exact_mod_cast (by
      simp [weightedFiniteCoordinateFiberCoreBinCount] :
        1 ≤ weightedFiniteCoordinateFiberCoreBinCount sourceCard)
  exact one_le_mul (by norm_num) hbin

private lemma selector_base_two_le (sourceCard : ℕ) :
    (2 : ENNReal) ≤
      64 * (weightedFiniteCoordinateFiberCoreBinCount sourceCard : ENNReal) := by
  have hbin : (1 : ENNReal) ≤
      (weightedFiniteCoordinateFiberCoreBinCount sourceCard : ENNReal) := by
    exact_mod_cast (by
      simp [weightedFiniteCoordinateFiberCoreBinCount] :
        1 ≤ weightedFiniteCoordinateFiberCoreBinCount sourceCard)
  calc
    (2 : ENNReal) ≤ 64 := by norm_num
    _ = 64 * 1 := by simp
    _ ≤ 64 *
        (weightedFiniteCoordinateFiberCoreBinCount sourceCard : ENNReal) := by
      gcongr

lemma natSucc_le_competitorFiniteQuotientProfileEnvelope
    (N sourceCard : ℕ) :
    (N + 1 : ENNReal) ≤
      competitorFiniteQuotientProfileEnvelope N sourceCard := by
  let base : ENNReal :=
    64 * (weightedFiniteCoordinateFiberCoreBinCount sourceCard : ENNReal)
  have hbaseTwo : (2 : ENNReal) ≤ base := by
    simpa [base] using selector_base_two_le sourceCard
  have hbaseOne : (1 : ENNReal) ≤ base := one_le_two.trans hbaseTwo
  calc
    (N + 1 : ENNReal) ≤ ((2 ^ (N + 1) : ℕ) : ENNReal) := by
      exact_mod_cast nat_le_two_pow (N + 1)
    _ = (2 : ENNReal) ^ (N + 1) := by norm_cast
    _ ≤ base ^ (N + 1) := by gcongr
    _ ≤ base ^ (5 * N + 5) := by
      exact pow_le_pow_right₀ hbaseOne (by omega)
    _ = competitorFiniteQuotientProfileEnvelope N sourceCard := by
      rfl

lemma competitorFiniteQuotientUniformity_le_profileEnvelope
    (N sourceCard : ℕ) :
    competitorFiniteQuotientUniformity N sourceCard ≤
      competitorFiniteQuotientProfileEnvelope N sourceCard := by
  let B : ENNReal :=
    weightedFiniteCoordinateFiberCoreBinCount sourceCard
  let base : ENNReal := 64 * B
  have hB : 1 ≤ B := by
    dsimp only [B]
    exact_mod_cast (by
      simp [weightedFiniteCoordinateFiberCoreBinCount] :
        1 ≤ weightedFiniteCoordinateFiberCoreBinCount sourceCard)
  have hbase : 1 ≤ base := by
    simpa [base, B] using selector_base_one_le sourceCard
  have hN : (N : ENNReal) ≤ base ^ N := by
    calc
      (N : ENNReal) ≤ (2 ^ N : ℕ) := by exact_mod_cast nat_le_two_pow N
      _ = (2 : ENNReal) ^ N := by norm_cast
      _ ≤ base ^ N := by
        gcongr
        simpa [base, B] using selector_base_two_le sourceCard
  have hBpow : B ^ (4 * N) ≤ base ^ (4 * N) := by
    gcongr
    dsimp only [base]
    exact le_mul_of_one_le_left (by positivity) (by norm_num)
  unfold competitorFiniteQuotientUniformity
    weightedFiniteCoordinateFiberCoreUniformity
    parentComponentCoreDenominator
    parentComponentColorCount
    competitorFiniteQuotientProfileEnvelope
  push_cast
  change 4 * (16 * (N : ENNReal) * (B ^ 2) ^ (2 * N)) ≤
    base ^ (5 * N + 5)
  rw [show (B ^ 2) ^ (2 * N) = B ^ (4 * N) by
    rw [← pow_mul]
    congr 1 <;> omega]
  calc
    4 * (16 * (N : ENNReal) * B ^ (4 * N)) =
        64 * (N : ENNReal) * B ^ (4 * N) := by ring
    _ ≤ base * base ^ N * base ^ (4 * N) := by
      gcongr
      · dsimp only [base]
        exact le_mul_of_one_le_right (by norm_num) hB
    _ = base ^ (5 * N + 1) := by
      calc
        base * base ^ N * base ^ (4 * N) =
            base ^ (N + 1) * base ^ (4 * N) := by
          rw [pow_succ]
          ring
        _ = base ^ ((N + 1) + 4 * N) :=
          (pow_add base (N + 1) (4 * N)).symm
        _ = base ^ (5 * N + 1) := by congr 1 <;> omega
    _ ≤ base ^ (5 * N + 5) := by
      exact pow_le_pow_right₀ hbase (by omega)

lemma competitorFiniteQuotientWeightLoss_le_profileEnvelope
    (N sourceCard : ℕ) :
    competitorFiniteQuotientWeightLoss N sourceCard ≤
      competitorFiniteQuotientProfileEnvelope N sourceCard := by
  let B : ENNReal :=
    weightedFiniteCoordinateFiberCoreBinCount sourceCard
  let base : ENNReal := 64 * B
  have hB : 1 ≤ B := by
    dsimp only [B]
    exact_mod_cast (by
      simp [weightedFiniteCoordinateFiberCoreBinCount] :
        1 ≤ weightedFiniteCoordinateFiberCoreBinCount sourceCard)
  have hbase : 1 ≤ base := by
    simpa [base, B] using selector_base_one_le sourceCard
  have hBpow : B ^ (4 * N) ≤ base ^ (4 * N) := by
    gcongr
    dsimp only [base]
    exact le_mul_of_one_le_left (by positivity) (by norm_num)
  unfold competitorFiniteQuotientWeightLoss
    weightedFiniteCoordinateFiberCoreWeightLoss
    parentComponentColorCount
    competitorFiniteQuotientProfileEnvelope
  push_cast
  change 2 * B * (8 * (B ^ 2) ^ (2 * N)) ≤ base ^ (5 * N + 5)
  rw [show (B ^ 2) ^ (2 * N) = B ^ (4 * N) by
    rw [← pow_mul]
    congr 1 <;> omega]
  calc
    2 * B * (8 * B ^ (4 * N)) = 16 * B * B ^ (4 * N) := by ring
    _ ≤ base * base * base ^ (4 * N) := by
      gcongr
      · dsimp only [base]
        calc
          (16 : ENNReal) ≤ 64 := by norm_num
          _ = 64 * 1 := by simp
          _ ≤ 64 * B := by gcongr
      · dsimp only [base]
        exact le_mul_of_one_le_left (by positivity) (by norm_num)
    _ = base ^ (4 * N + 2) := by
      calc
        base * base * base ^ (4 * N) =
            base ^ 2 * base ^ (4 * N) := by rw [pow_two]
        _ = base ^ (2 + 4 * N) :=
          (pow_add base 2 (4 * N)).symm
        _ = base ^ (4 * N + 2) := by congr 1 <;> omega
    _ ≤ base ^ (5 * N + 5) := by
      exact pow_le_pow_right₀ hbase (by omega)

/-- At the competitor grid depth, the common selector envelope is
subpolynomial uniformly over every essentially-distinct source in the unit
ball.  The threshold depends only on the requested loss. -/
theorem exists_threshold_competitorFiniteQuotientProfileEnvelope_le
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta₀ : NNReal, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta : NNReal}, 0 < delta → delta ≤ delta₀ →
      ∀ source : Kakeya.Streamlined.TubeFamily (delta : ℝ),
        source.IsEssentiallyDistinct → source.IsInUnitBall →
        competitorFiniteQuotientProfileEnvelope
            (Tube.ssfGridLen delta) source.card ≤
          Kakeya.realRpowENN (delta : ℝ) (-epsilon) := by
  rcases unitBall_tube_cardinality_five with
    ⟨packingThreshold, hpackingThreshold,
      hpackingThresholdOne, hpacking⟩
  rcases Tube.exists_threshold_polylog_pow_ssfGridLen_le
      64 (by norm_num) 6 5 epsilon hepsilon with
    ⟨profileThreshold, hprofileThreshold,
      hprofileThresholdOne, hprofile⟩
  let packingThresholdNN : NNReal :=
    ⟨packingThreshold, hpackingThreshold.le⟩
  let half : NNReal := 1 / 2
  let delta₀ : NNReal :=
    min (min packingThresholdNN profileThreshold) half
  have hdelta₀ : 0 < delta₀ := by
    apply lt_min
    · apply lt_min
      · exact hpackingThreshold
      · exact hprofileThreshold
    · norm_num [half]
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans
      ((min_le_left _ _).trans hpackingThresholdOne)
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaSmall source hsourceED hsourceBall
  have hpackingSmall : (delta : ℝ) ≤ packingThreshold := by
    have hle : delta ≤ packingThresholdNN :=
      hdeltaSmall.trans ((min_le_left _ _).trans (min_le_left _ _))
    exact_mod_cast hle
  have hprofileSmall : delta ≤ profileThreshold :=
    hdeltaSmall.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hdeltaHalf : (delta : ℝ) ≤ 1 / 2 := by
    exact_mod_cast hdeltaSmall.trans (min_le_right _ _)
  have hsourceCard :
      (source.card : ℝ) ≤ (1 / (delta : ℝ)) ^ (5 : ℕ) :=
    hpacking (delta : ℝ) (by exact_mod_cast hdelta)
      hpackingSmall source hsourceED hsourceBall
  have hinverseTwo : (2 : ℝ) ≤ 1 / (delta : ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast hdelta : (0 : ℝ) < delta)]
    linarith
  have hdoubleCard :
      ((2 * source.card : ℕ) : ℝ) ≤
        (1 / (delta : ℝ)) ^ (6 : ℝ) := by
    calc
      ((2 * source.card : ℕ) : ℝ) =
          2 * (source.card : ℝ) := by norm_cast
      _ ≤ 2 * (1 / (delta : ℝ)) ^ (5 : ℕ) := by gcongr
      _ ≤ (1 / (delta : ℝ)) *
          (1 / (delta : ℝ)) ^ (5 : ℕ) := by gcongr
      _ = (1 / (delta : ℝ)) ^ (6 : ℝ) := by
        rw [show (6 : ℝ) = (6 : ℕ) by norm_num, Real.rpow_natCast]
        ring
  have hprofileBound :=
    (hprofile hdelta hprofileSmall).2.2
      ((2 * source.card : ℕ) : ℝ) (by positivity) (by
        calc
          ((2 * source.card : ℕ) : ℝ) ≤
              (1 / (delta : ℝ)) ^ (6 : ℝ) := hdoubleCard
          _ = (delta : ℝ) ^ (-(6 : ℝ)) := by
            rw [one_div, Real.inv_rpow
              (show (0 : ℝ) ≤ (delta : ℝ) by positivity)]
            exact (Real.rpow_neg
              (show (0 : ℝ) ≤ (delta : ℝ) by positivity) 6).symm)
  have hfloor :
      (⌊Real.logb 2 ((2 * source.card : ℕ) : ℝ)⌋₊ : ℕ) =
        Nat.log 2 (2 * source.card) := by
    exact_mod_cast Real.natFloor_logb_natCast 2 (2 * source.card)
  have hreal :
      (64 *
          (((Nat.log 2 (2 * source.card) + 1 : ℕ) : ℝ))) ^
            (5 * Tube.ssfGridLen delta + 5) ≤
        (delta : ℝ) ^ (-epsilon) := by
    rw [hfloor] at hprofileBound
    norm_num at hprofileBound ⊢
    exact hprofileBound
  unfold competitorFiniteQuotientProfileEnvelope
    weightedFiniteCoordinateFiberCoreBinCount
  rw [Kakeya.realRpowENN]
  let exponent := 5 * Tube.ssfGridLen delta + 5
  let baseReal : ℝ :=
    64 * (((Nat.log 2 (2 * source.card) + 1 : ℕ) : ℝ))
  have hbaseCast :
      (64 : ENNReal) *
          ((Nat.log 2 (2 * source.card) + 1 : ℕ) : ENNReal) =
        ENNReal.ofReal baseReal := by
    dsimp only [baseReal]
    norm_cast
  calc
    ((64 : ENNReal) *
          ((Nat.log 2 (2 * source.card) + 1 : ℕ) : ENNReal)) ^
          (5 * Tube.ssfGridLen delta + 5) =
        ENNReal.ofReal (baseReal ^ exponent) := by
          rw [hbaseCast]
          exact (ENNReal.ofReal_pow (by positivity) exponent).symm
    _ ≤ ENNReal.ofReal ((delta : ℝ) ^ (-epsilon)) := by
          apply ENNReal.ofReal_le_ofReal
          simpa [baseReal, exponent] using hreal

/-- All scalar prerequisites for the pointwise full-fiber budget can be
chosen before the runtime scale and family. -/
theorem exists_threshold_competitorAllRealPowerInputs
    (p : ℝ) (hp : 0 < p) :
    ∃ delta₀ : NNReal, 0 < delta₀ ∧ delta₀ ≤ 1 / 2 ∧
      ∀ {delta : NNReal}, 0 < delta → delta ≤ delta₀ →
      0 < Tube.ssfGridLen delta ∧ delta < 1 ∧
      (33 : ℝ) / (Tube.ssfGridLen delta : ℝ) ≤ p ∧
      (∀ source : Kakeya.Streamlined.TubeFamily (delta : ℝ),
        source.IsEssentiallyDistinct → source.IsInUnitBall →
        competitorFiniteQuotientProfileEnvelope
            (Tube.ssfGridLen delta) source.card ≤
          Kakeya.realRpowENN (delta : ℝ) (-p)) ∧
      competitorAllRealFixedConstant ≤
        Kakeya.realRpowENN (delta : ℝ) (-p) := by
  rcases exists_threshold_competitorFiniteQuotientProfileEnvelope_le
      p hp with
    ⟨profileThreshold, hprofileThreshold,
      hprofileThresholdOne, hprofile⟩
  rcases exists_threshold_le_competitor_ssfGridLen (33 / p) with
    ⟨gridThreshold, hgridThreshold, hgrid⟩
  rcases Kakeya.Streamlined.exists_delta_pow_bound competitorAllRealFixedConstant
      competitorAllRealFixedConstant_ne_top hp with
    ⟨fixedThreshold, hfixedThreshold, hfixed⟩
  let gridThresholdNN : NNReal :=
    ⟨gridThreshold, hgridThreshold.le⟩
  let fixedThresholdNN : NNReal :=
    ⟨fixedThreshold, hfixedThreshold.le⟩
  let half : NNReal := 1 / 2
  let delta₀ : NNReal :=
    min profileThreshold (min gridThresholdNN (min fixedThresholdNN half))
  have hdelta₀ : 0 < delta₀ := by
    apply lt_min
    · exact hprofileThreshold
    apply lt_min
    · exact hgridThreshold
    apply lt_min
    · exact hfixedThreshold
    · norm_num [half]
  have hdelta₀Half : delta₀ ≤ 1 / 2 :=
    (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨delta₀, hdelta₀, hdelta₀Half, ?_⟩
  intro delta hdelta hdeltaSmall
  have hprofileSmall : delta ≤ profileThreshold :=
    hdeltaSmall.trans (min_le_left _ _)
  have hgridSmall : (delta : ℝ) ≤ gridThreshold := by
    have hle : delta ≤ gridThresholdNN :=
      hdeltaSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
    exact_mod_cast hle
  have hfixedSmall : (delta : ℝ) ≤ fixedThreshold := by
    have hle : delta ≤ fixedThresholdNN :=
      hdeltaSmall.trans ((min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _))
    exact_mod_cast hle
  have hgridRaw :
      33 / p ≤ (Tube.ssfGridLen delta : ℝ) :=
    hgrid hdelta hgridSmall
  have hNpos : (0 : ℝ) < (Tube.ssfGridLen delta : ℝ) := by
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < 33 / p) hgridRaw
  have hgridFinal :
      (33 : ℝ) / (Tube.ssfGridLen delta : ℝ) ≤ p := by
    rw [div_le_iff₀ hNpos]
    have hmul := mul_le_mul_of_nonneg_right hgridRaw hp.le
    have hcancel : p * (33 / p) = 33 := by
      field_simp [hp.ne']
    nlinarith
  have hNposNat : 0 < Tube.ssfGridLen delta := by
    exact_mod_cast hNpos
  have hdeltaStrict : delta < 1 := by
    exact lt_of_le_of_lt
      (hdeltaSmall.trans hdelta₀Half) (by norm_num)
  exact ⟨hNposNat, hdeltaStrict, hgridFinal,
    fun source hsourceED hsourceBall =>
      hprofile hdelta hprofileSmall source hsourceED hsourceBall,
    hfixed (delta : ℝ) (by exact_mod_cast hdelta) hfixedSmall⟩

/-- Specialization of the generic all-scale degree estimate to the active
competitor supporting-line quotient construction. -/
theorem CompetitorStickyInput.FiniteQuotientSelectionPackage.allReal_uniformity_le
    {delta : NNReal} {ι : Type*} {N : ℕ} {C : NNReal}
    {lambda frostmanConstant : ENNReal} {supportRadius : ℝ}
    {input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius}
    {hN : 0 < N} {hdelta : 0 < delta} {hdeltaOne : delta ≤ 1}
    {hsourceBall : input.source.IsInUnitBall}
    (selection :
      input.FiniteQuotientSelectionPackage
        hN hdelta hdeltaOne hsourceBall)
    (hdeltaStrict : delta < 1)
    (package : selection.AllRealPackage)
    {eta₁ epsilon : ℝ}
    (heta₁ : 0 < eta₁) (hepsilon : 0 < epsilon)
    (hexp : (33 : ℝ) / (N : ℝ) + epsilon < eta₁)
    (hprofile :
      competitorFiniteQuotientUniformity N input.source.card ≤
        Kakeya.realRpowENN (delta : ℝ) (-epsilon))
    (habsorb :
      fullContainmentBranchingLoss
          (dominatingUpperFromDilatedCoverDilation
            competitorSupportingLineQuotientDilation)
          package.outputDilation_one *
        (competitorQuotientConflictConstant *
            ENNReal.ofReal
                (2 + Real.pi + 8 / 3 * Real.pi) ^ 11 *
            (N : ENNReal) + ((N : ENNReal) + 1)) ≤
        Kakeya.realRpowENN (delta : ℝ)
          (-(eta₁ - (33 / (N : ℝ)) - epsilon))) :
    package.uts.uniformity ≤
      Kakeya.realRpowENN (delta : ℝ) (-eta₁) := by
  let grid := canonicalFixedDepthPowerGrid N hN (delta : ℝ)
    (by exact_mod_cast hdelta) (by exact_mod_cast hdeltaStrict)
  apply allScaleUniformityBound
    (by exact_mod_cast hdelta) (by exact_mod_cast hdeltaOne) hN
    (grid := grid)
    (explicitConflictConstant
      (fixedDepthPowerGridKRatio (delta : ℝ) N))
    (by
      unfold explicitConflictConstant
      have hK : 0 < fixedDepthPowerGridKRatio (delta : ℝ) N :=
        lt_of_lt_of_le (by norm_num)
          (fixed_depth_power_grid_k_ratio_gate
            (by exact_mod_cast hdelta) (by exact_mod_cast hdeltaOne)
            hN grid).1
      positivity)
    (competitorFiniteQuotientDegree delta N hN hdelta hdeltaOne)
    (by
      intro cut
      unfold competitorFiniteQuotientDegree
      change
        Nat.ceil
            (explicitConflictConstant
                (fixedDepthPowerGridKRatio (delta : ℝ) N) *
              (((canonicalFixedDepthPowerGrid N hN (delta : ℝ)
                    (by exact_mod_cast hdelta)
                    (by exact_mod_cast hdeltaStrict)).increasingScale
                  (Fin.succ cut)).1 /
                ((canonicalFixedDepthPowerGrid N hN (delta : ℝ)
                    (by exact_mod_cast hdelta)
                    (by exact_mod_cast hdeltaStrict)).increasingScale
                  (Fin.castSucc cut)).1) ^ 4) = _
      rfl)
    package.uts.uniformity
    (competitorFiniteQuotientUniformity N input.source.card)
    (fullContainmentBranchingLoss
      (dominatingUpperFromDilatedCoverDilation
        competitorSupportingLineQuotientDilation)
      package.outputDilation_one)
    (allScaleBalancedFromDilatedCoverDegreeFactor
      (competitorFiniteQuotientDegree delta N hN hdelta hdeltaOne))
    package.uniformity_eq
    rfl eta₁ epsilon heta₁ hepsilon hexp
    competitorQuotientConflictConstant (by
      unfold competitorQuotientConflictConstant
      positivity)
    (explicitConflictConstant_le_competitorQuotientConflictConstant_mul
      (show 0 ≤ fixedDepthPowerGridKRatio (delta : ℝ) N by
        exact le_trans (by norm_num)
          (fixed_depth_power_grid_k_ratio_gate
            (by exact_mod_cast hdelta) (by exact_mod_cast hdeltaOne)
            hN grid).1))
    hprofile habsorb

/-- Pointwise all-real uniformity budget with all runtime dependence isolated
in `N`, the selector profile, and inverse powers of `delta`. -/
theorem CompetitorStickyInput.FiniteQuotientSelectionPackage.allReal_uniformity_le_of_profile
    {delta : NNReal} {ι : Type*} {N : ℕ} {C : NNReal}
    {lambda frostmanConstant : ENNReal} {supportRadius : ℝ}
    {input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius}
    {hN : 0 < N} {hdelta : 0 < delta} {hdeltaOne : delta ≤ 1}
    {hsourceBall : input.source.IsInUnitBall}
    (selection :
      input.FiniteQuotientSelectionPackage
        hN hdelta hdeltaOne hsourceBall)
    (hdeltaStrict : delta < 1)
    (package : selection.AllRealPackage)
    {p : ℝ} (hp : 0 < p)
    (hgrid : (33 : ℝ) / (N : ℝ) ≤ p)
    (hprofile :
      competitorFiniteQuotientProfileEnvelope N input.source.card ≤
        Kakeya.realRpowENN (delta : ℝ) (-p))
    (hfixed : competitorAllRealUniformityFixedConstant ≤
      Kakeya.realRpowENN (delta : ℝ) (-p)) :
    package.uts.uniformity ≤
      Kakeya.realRpowENN (delta : ℝ) (-(4 * p)) := by
  have hbase := competitorFiniteQuotientUniformity_le_profileEnvelope
    N input.source.card
  have hfiber :
      competitorFiniteQuotientUniformity N input.source.card ≤
        Kakeya.realRpowENN (delta : ℝ) (-p) :=
    hbase.trans hprofile
  have hNsucc :
      (N + 1 : ENNReal) ≤
        competitorFiniteQuotientProfileEnvelope N input.source.card :=
    natSucc_le_competitorFiniteQuotientProfileEnvelope N input.source.card
  have hNle :
      (N : ENNReal) ≤
        competitorFiniteQuotientProfileEnvelope N input.source.card := by
    exact (by exact_mod_cast Nat.le_succ N :
      (N : ENNReal) ≤ (N + 1 : ENNReal)) |>.trans hNsucc
  have hdegreeBracket :
      competitorQuotientConflictConstant *
            ENNReal.ofReal (2 + Real.pi + 8 / 3 * Real.pi) ^ 11 *
            (N : ENNReal) + ((N : ENNReal) + 1) ≤
        (competitorQuotientConflictConstant *
            ENNReal.ofReal (2 + Real.pi + 8 / 3 * Real.pi) ^ 11 + 1) *
          competitorFiniteQuotientProfileEnvelope N input.source.card := by
    calc
      competitorQuotientConflictConstant *
              ENNReal.ofReal (2 + Real.pi + 8 / 3 * Real.pi) ^ 11 *
              (N : ENNReal) + ((N : ENNReal) + 1)
          ≤ competitorQuotientConflictConstant *
              ENNReal.ofReal (2 + Real.pi + 8 / 3 * Real.pi) ^ 11 *
              competitorFiniteQuotientProfileEnvelope N input.source.card +
            competitorFiniteQuotientProfileEnvelope N input.source.card := by
              gcongr
      _ = (competitorQuotientConflictConstant *
              ENNReal.ofReal (2 + Real.pi + 8 / 3 * Real.pi) ^ 11 + 1) *
            competitorFiniteQuotientProfileEnvelope N input.source.card := by ring
  have habsorbTwo :
      competitorAllRealUniformityFixedConstant *
          competitorFiniteQuotientProfileEnvelope N input.source.card ≤
        Kakeya.realRpowENN (delta : ℝ) (-(2 * p)) := by
    simpa [show p + p = 2 * p by ring] using
      (absorption_upper_mul
        (by exact_mod_cast hdelta) hfixed hprofile)
  have habsorbRaw :
      fullContainmentBranchingLoss
          (dominatingUpperFromDilatedCoverDilation
            competitorSupportingLineQuotientDilation)
          package.outputDilation_one *
        (competitorQuotientConflictConstant *
            ENNReal.ofReal (2 + Real.pi + 8 / 3 * Real.pi) ^ 11 *
            (N : ENNReal) + ((N : ENNReal) + 1)) ≤
        Kakeya.realRpowENN (delta : ℝ) (-(2 * p)) := by
    calc
      fullContainmentBranchingLoss
            (dominatingUpperFromDilatedCoverDilation
              competitorSupportingLineQuotientDilation)
            package.outputDilation_one *
          (competitorQuotientConflictConstant *
              ENNReal.ofReal (2 + Real.pi + 8 / 3 * Real.pi) ^ 11 *
              (N : ENNReal) + ((N : ENNReal) + 1))
        ≤ fullContainmentBranchingLoss
            (dominatingUpperFromDilatedCoverDilation
              competitorSupportingLineQuotientDilation)
            package.outputDilation_one *
          ((competitorQuotientConflictConstant *
              ENNReal.ofReal (2 + Real.pi + 8 / 3 * Real.pi) ^ 11 + 1) *
            competitorFiniteQuotientProfileEnvelope N input.source.card) := by
              gcongr
      _ = competitorAllRealUniformityFixedConstant *
          competitorFiniteQuotientProfileEnvelope N input.source.card := by
            rw [show package.outputDilation_one =
              competitorAllRealOutputDilation_one from Subsingleton.elim _ _]
            unfold competitorAllRealUniformityFixedConstant
            ring
      _ ≤ Kakeya.realRpowENN (delta : ℝ) (-(2 * p)) := habsorbTwo
  have hslack :
      2 * p ≤ 4 * p - 33 / (N : ℝ) - p := by
    linarith
  have habsorb :
      fullContainmentBranchingLoss
          (dominatingUpperFromDilatedCoverDilation
            competitorSupportingLineQuotientDilation)
          package.outputDilation_one *
        (competitorQuotientConflictConstant *
            ENNReal.ofReal (2 + Real.pi + 8 / 3 * Real.pi) ^ 11 *
            (N : ENNReal) + ((N : ENNReal) + 1)) ≤
        Kakeya.realRpowENN (delta : ℝ)
          (-(4 * p - 33 / (N : ℝ) - p)) := by
    exact habsorbRaw.trans <|
      GeneralizedFrostman.realRpowENN_anti
        (by exact_mod_cast hdelta) (by exact_mod_cast hdeltaOne)
        (by linarith : -(4 * p - 33 / (N : ℝ) - p) ≤ -(2 * p))
  exact selection.allReal_uniformity_le hdeltaStrict package
    (eta₁ := 4 * p) (epsilon := p) (by positivity) hp
    (by linarith) hfiber habsorb

/-- Explicit pointwise power ledger for the common all-real complete-fiber
coefficient.  The two occurrences of `eta` are respectively the density
inverse in the one-shot restriction and the original node-Frostman bound. -/
theorem CompetitorStickyInput.FiniteQuotientSelectionPackage.allRealFullFiberCoefficient_le
    {delta : NNReal} {ι : Type*} {N : ℕ} {C : NNReal}
    {lambda frostmanConstant : ENNReal} {supportRadius : ℝ}
    {input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius}
    {hN : 0 < N} {hdelta : 0 < delta} {hdeltaOne : delta ≤ 1}
    {hsourceBall : input.source.IsInUnitBall}
    (selection :
      input.FiniteQuotientSelectionPackage
        hN hdelta hdeltaOne hsourceBall)
    (hdeltaStrict : delta < 1)
    (package : selection.AllRealPackage)
    {eta p : ℝ} (heta : 0 < eta) (hp : 0 < p)
    (hgrid : (33 : ℝ) / (N : ℝ) ≤ p)
    (hprofile :
      competitorFiniteQuotientProfileEnvelope N input.source.card ≤
        Kakeya.realRpowENN (delta : ℝ) (-p))
    (huniformFixed : competitorAllRealUniformityFixedConstant ≤
      Kakeya.realRpowENN (delta : ℝ) (-p))
    (htransportFixed : competitorAllRealTransportFixedConstant ≤
      Kakeya.realRpowENN (delta : ℝ) (-p))
    (htwo : (2 : ENNReal) ≤
      Kakeya.realRpowENN (delta : ℝ) (-p))
    (hquotient : competitorSupportingLineQuotientFrostmanLoss ≤
      Kakeya.realRpowENN (delta : ℝ) (-p))
    (hlambdaInv : lambda⁻¹ ≤
      Kakeya.realRpowENN (delta : ℝ) (-eta))
    (hfrostman : frostmanConstant ≤
      Kakeya.realRpowENN (delta : ℝ) (-eta)) :
    selection.allRealFullFiberCoefficient package ≤
      Kakeya.realRpowENN (delta : ℝ) (-(2 * eta + 10 * p)) := by
  have hdeltaReal : (0 : ℝ) < (delta : ℝ) := by exact_mod_cast hdelta
  have huniform : package.uts.uniformity ≤
      Kakeya.realRpowENN (delta : ℝ) (-(4 * p)) :=
    selection.allReal_uniformity_le_of_profile hdeltaStrict package hp
      hgrid hprofile huniformFixed
  let grid := canonicalFixedDepthPowerGrid N hN (delta : ℝ)
    hdeltaReal (by exact_mod_cast hdeltaStrict)
  have hK : reverseGridK delta N ≤
      ENNReal.ofReal (2 + Real.pi + 8 / 3 * Real.pi) *
        Kakeya.realRpowENN (delta : ℝ) (-(3 / (N : ℝ))) := by
    exact (fixed_depth_power_grid_k_ratio_gate
      hdeltaReal (by exact_mod_cast hdeltaOne) hN grid).2.1
  have hgridPower :
      Kakeya.realRpowENN (delta : ℝ) (-(3 / (N : ℝ))) ≤
        Kakeya.realRpowENN (delta : ℝ) (-p) := by
    have hthree : (3 : ℝ) / (N : ℝ) ≤ 33 / (N : ℝ) := by
      gcongr
      norm_num
    exact GeneralizedFrostman.realRpowENN_anti hdeltaReal
      (by exact_mod_cast hdeltaOne)
      (by linarith [hthree, hgrid] : -p ≤ -(3 / (N : ℝ)))
  have htransport :
      allScaleAssignedFrostmanTransportLoss
          competitorSupportingLineQuotientDilation
          (reverseGridK delta N) ≤
        Kakeya.realRpowENN (delta : ℝ) (-(2 * p)) := by
    have hraw :
        allScaleAssignedFrostmanTransportLoss
            competitorSupportingLineQuotientDilation
            (reverseGridK delta N) ≤
          competitorAllRealTransportFixedConstant *
            Kakeya.realRpowENN (delta : ℝ) (-p) := by
      unfold allScaleAssignedFrostmanTransportLoss
        competitorAllRealTransportFixedConstant
      calc
        reverseGridK delta N *
            dilatedCoverVolumeFactor
              (dominatingUpperFromDilatedCoverDilation
                competitorSupportingLineQuotientDilation)
          ≤ (ENNReal.ofReal (2 + Real.pi + 8 / 3 * Real.pi) *
                Kakeya.realRpowENN (delta : ℝ) (-(3 / (N : ℝ)))) *
              dilatedCoverVolumeFactor
                (dominatingUpperFromDilatedCoverDilation
                  competitorSupportingLineQuotientDilation) := by gcongr
        _ = competitorAllRealTransportFixedConstant *
              Kakeya.realRpowENN (delta : ℝ) (-(3 / (N : ℝ))) := by
                unfold competitorAllRealTransportFixedConstant
                ring
        _ ≤ competitorAllRealTransportFixedConstant *
              Kakeya.realRpowENN (delta : ℝ) (-p) := by gcongr
    exact hraw.trans <| by
      simpa [show p + p = 2 * p by ring] using
        (absorption_upper_mul (p := p) (q := p) hdeltaReal
          htransportFixed (le_refl _))
  have hweight : competitorFiniteQuotientWeightLoss
      N input.source.card ≤ Kakeya.realRpowENN (delta : ℝ) (-p) :=
    (competitorFiniteQuotientWeightLoss_le_profileEnvelope
      N input.source.card).trans hprofile
  have hselectorUniform : competitorFiniteQuotientUniformity
      N input.source.card ≤ Kakeya.realRpowENN (delta : ℝ) (-p) :=
    (competitorFiniteQuotientUniformity_le_profileEnvelope
      N input.source.card).trans hprofile
  have hlambdaWeight : lambda⁻¹ *
      competitorFiniteQuotientWeightLoss N input.source.card ≤
      Kakeya.realRpowENN (delta : ℝ) (-(eta + p)) :=
    absorption_upper_mul hdeltaReal hlambdaInv hweight
  have hlambdaWeightUniform :
      (lambda⁻¹ * competitorFiniteQuotientWeightLoss N input.source.card) *
          competitorFiniteQuotientUniformity N input.source.card ≤
        Kakeya.realRpowENN (delta : ℝ) (-(eta + 2 * p)) := by
    simpa [show (eta + p) + p = eta + 2 * p by ring] using
      (absorption_upper_mul hdeltaReal hlambdaWeight hselectorUniform)
  have hretention : competitorFiniteQuotientFiberRetentionLoss
      lambda N input.source.card ≤
      Kakeya.realRpowENN (delta : ℝ) (-(eta + 3 * p)) := by
    unfold competitorFiniteQuotientFiberRetentionLoss
    have h := absorption_upper_mul (p := p) (q := eta + 2 * p)
      hdeltaReal htwo hlambdaWeightUniform
    calc
      2 * (lambda⁻¹ *
            competitorFiniteQuotientWeightLoss N input.source.card) *
          competitorFiniteQuotientUniformity N input.source.card =
        2 * ((lambda⁻¹ *
            competitorFiniteQuotientWeightLoss N input.source.card) *
          competitorFiniteQuotientUniformity N input.source.card) := by ring
      _ ≤ Kakeya.realRpowENN (delta : ℝ)
          (-(p + (eta + 2 * p))) := h
      _ = Kakeya.realRpowENN (delta : ℝ) (-(eta + 3 * p)) := by
        congr 1
        ring
  have hfirst := absorption_upper_mul hdeltaReal huniform htransport
  have hsecond := absorption_upper_mul hdeltaReal hfirst hretention
  have hthird := absorption_upper_mul hdeltaReal hsecond hquotient
  have hfourth := absorption_upper_mul hdeltaReal hthird hfrostman
  have hcomplete :
      selection.allRealFullContainmentFrostmanCoefficient package ≤
        Kakeya.realRpowENN (delta : ℝ) (-(2 * eta + 10 * p)) := by
    rw [selection.allRealFullContainmentFrostmanCoefficient_eq package]
    simpa [show (((4 * p + 2 * p) + (eta + 3 * p)) + p) + eta =
        2 * eta + 10 * p by ring] using hfourth
  have huniformFinal : package.uts.uniformity ≤
      Kakeya.realRpowENN (delta : ℝ) (-(2 * eta + 10 * p)) := by
    exact huniform.trans <|
      GeneralizedFrostman.realRpowENN_anti hdeltaReal
        (by exact_mod_cast hdeltaOne)
        (by linarith : -(2 * eta + 10 * p) ≤ -(4 * p))
  exact max_le huniformFinal hcomplete

/-- Uniform threshold form of the complete competitor hierarchy budget.
Every parameter controlling the threshold is fixed before the runtime scale,
family, hierarchy, common selection, and all-real package are introduced. -/
theorem exists_threshold_competitorAllRealFullFiberCoefficient_le
    {eta p inputLoss : ℝ}
    (heta : 0 < eta) (hp : 0 < p)
    (hbudget : 2 * eta + 10 * p ≤ inputLoss) :
    ∃ delta₀ : NNReal, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta : NNReal},
      ∀ (hdelta : 0 < delta),
      ∀ (hdeltaSmall : delta ≤ delta₀),
      ∀ {ι : Type*} {C : NNReal}
        {lambda frostmanConstant : ENNReal} {supportRadius : ℝ}
        (input : CompetitorStickyInput delta ι (Tube.ssfGridLen delta) C
          lambda frostmanConstant supportRadius)
        (hsourceBall : input.source.IsInUnitBall)
        (hN : 0 < Tube.ssfGridLen delta)
        (hdeltaOne : delta ≤ 1)
        (hdeltaStrict : delta < 1)
        (selection : input.FiniteQuotientSelectionPackage
          hN hdelta hdeltaOne hsourceBall)
        (package : selection.AllRealPackage)
        (hlambdaInv : lambda⁻¹ ≤
          Kakeya.realRpowENN (delta : ℝ) (-eta))
        (hfrostman : frostmanConstant ≤
          Kakeya.realRpowENN (delta : ℝ) (-eta)),
        selection.allRealFullFiberCoefficient package ≤
          Kakeya.realRpowENN (delta : ℝ) (-inputLoss) := by
  rcases exists_threshold_competitorAllRealPowerInputs p hp with
    ⟨delta₀, hdelta₀, hdelta₀Half, hinputs⟩
  have hdelta₀One : delta₀ ≤ 1 := hdelta₀Half.trans (by norm_num)
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaSmall ι C lambda frostmanConstant
    supportRadius input hsourceBall hN hdeltaOne hdeltaStrict selection package
    hlambdaInv hfrostman
  rcases hinputs hdelta hdeltaSmall with
    ⟨_, _, hgrid, hprofileAll, hfixed⟩
  have hprofile := hprofileAll input.source
    ((competitorTubeFamily_isEssentiallyDistinct_iff input.s input.V).2
      input.leaf_separation) hsourceBall
  have hraw := selection.allRealFullFiberCoefficient_le
    hdeltaStrict package heta hp hgrid hprofile
    (competitorAllRealUniformityFixedConstant_le_fixedConstant.trans hfixed)
    (competitorAllRealTransportFixedConstant_le_fixedConstant.trans hfixed)
    (two_le_competitorAllRealFixedConstant.trans hfixed)
    (competitorSupportingLineQuotientFrostmanLoss_le_fixedConstant.trans hfixed)
    hlambdaInv hfrostman
  exact hraw.trans <|
    GeneralizedFrostman.realRpowENN_anti
      (by exact_mod_cast hdelta) (by exact_mod_cast hdeltaOne)
      (by linarith : -inputLoss ≤ -(2 * eta + 10 * p))

end Kakeya.Integration

end
