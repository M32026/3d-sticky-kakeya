import MyLeanRepo.Kakeya.Assouad.WZ1.KaufmanEnergyTotal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exponent arithmetic for the normalized Kaufman preparation
-/

namespace Kakeya.Assouad

/-- Positivity of the angular Kaufman constant in the one-dimensional case. -/
private lemma kaufman_K_ang_one_pos
    {gamma : ℝ} (hgamma_lt_one : gamma < 1) :
    0 < kaufman_K_ang 1 gamma := by
  dsimp only [kaufman_K_ang]
  have hdenominator :
      0 < (1 : ℝ) - (2 : ℝ) ^ (-(1 - gamma)) := by
    have hexponent : 0 < (1 : ℝ) - gamma := by
      linarith
    have hpower : 1 < (2 : ℝ) ^ (1 - gamma) :=
      Real.one_lt_rpow (by norm_num) hexponent
    have hinverse :
        (2 : ℝ) ^ (-(1 - gamma)) =
          ((2 : ℝ) ^ (1 - gamma))⁻¹ := by
      rw [Real.rpow_neg (by norm_num)]
    rw [hinverse]
    have hpowerPos : 0 < (2 : ℝ) ^ (1 - gamma) := by
      positivity
    have :
        ((2 : ℝ) ^ (1 - gamma))⁻¹ < 1 := by
      simpa [one_div] using (div_lt_one hpowerPos).2 hpower
    linarith
  positivity

/-- Positivity of the Frostman Kaufman constant in the one-dimensional case. -/
private lemma kaufman_K_frost0_one_pos
    {gamma : ℝ} (hgamma_lt_one : gamma < 1) :
    0 < kaufman_K_frost0 1 gamma := by
  dsimp only [kaufman_K_frost0]
  have hpower :
      0 < (2 : ℝ) ^ (1 - gamma) - 1 := by
    have hexponent : 0 < (1 : ℝ) - gamma := by
      linarith
    have : 1 < (2 : ℝ) ^ (1 - gamma) :=
      Real.one_lt_rpow (by norm_num) hexponent
    linarith
  positivity

/-- Positivity of the angular constant, exported for downstream arithmetic. -/
lemma kaufman_K_ang_one_positive
    {gamma : ℝ} (hgamma_lt_one : gamma < 1) :
    0 < kaufman_K_ang 1 gamma :=
  kaufman_K_ang_one_pos hgamma_lt_one

/-- Positivity of the Frostman constant, exported for downstream arithmetic. -/
lemma kaufman_K_frost0_one_positive
    {gamma : ℝ} (hgamma_lt_one : gamma < 1) :
    0 < kaufman_K_frost0 1 gamma :=
  kaufman_K_frost0_one_pos hgamma_lt_one

/-- The total one-dimensional Kaufman constant is positive. -/
lemma kaufman_total_const_one_pos
    {constant gamma : ℝ}
    (hconstant : 0 < constant)
    (hgamma_lt_one : gamma < 1) :
    0 < kaufman_total_const constant 1 1 gamma := by
  dsimp only [kaufman_total_const]
  have hangular : 0 < kaufman_K_ang 1 gamma :=
    kaufman_K_ang_one_pos hgamma_lt_one
  have hfrostman : 0 < kaufman_K_frost0 1 gamma :=
    kaufman_K_frost0_one_pos hgamma_lt_one
  positivity

/--
The Kaufman energy constant grows at most quadratically in its Frostman
constant when the dimensions are both one.
-/
lemma kaufman_total_const_quadratic_bound
    {constant gamma : ℝ}
    (hconstant : 1 ≤ constant)
    (_hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1) :
    kaufman_total_const constant 1 1 gamma ≤
      (1 +
          2 * kaufman_K_ang 1 gamma *
            kaufman_K_frost0 1 gamma +
          kaufman_K_ang 1 gamma) *
        constant ^ 2 := by
  dsimp only [kaufman_total_const]
  let angular := kaufman_K_ang 1 gamma
  let frostman := kaufman_K_frost0 1 gamma
  have hangular : 0 < angular :=
    kaufman_K_ang_one_pos hgamma_lt_one
  have hfrostman : 0 < frostman :=
    kaufman_K_frost0_one_pos hgamma_lt_one
  have hlinear : constant ≤ constant ^ 2 := by
    nlinarith
  have hnonnegative :
      0 ≤ angular * frostman + angular := by
    positivity
  calc
    (constant + angular * frostman * (1 + constant) + angular) *
          constant =
        constant ^ 2 * (1 + angular * frostman) +
          constant * (angular * frostman + angular) := by
      ring
    _ ≤
        constant ^ 2 * (1 + angular * frostman) +
          constant ^ 2 * (angular * frostman + angular) := by
      gcongr
    _ =
        (1 + 2 * angular * frostman + angular) *
          constant ^ 2 := by
      ring

/--
For the choice `eta = epsilon / 10`, the normalized Kaufman covering
inequality is absorbed by shrinking the scale.
-/
lemma kaufman_numerical_asymptotic
    {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (_hepsilon_lt_one : epsilon < 1)
    {leftConstant rightConstant : ℝ}
    (hleftConstant : 0 < leftConstant)
    (hrightConstant : 0 < rightConstant) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        leftConstant * (2 / delta) ^ (1 - epsilon) ≤
          rightConstant *
            delta ^ (4 * (epsilon / 10) - 1 + epsilon / 2) := by
  have htwo : 0 < (2 : ℝ) ^ (1 - epsilon) := by
    positivity
  let threshold :=
    (rightConstant /
        (leftConstant * (2 : ℝ) ^ (1 - epsilon))) ^
      (10 / epsilon)
  have hthreshold : 0 < threshold := by
    positivity
  let delta₀ := min threshold 1
  have hdelta₀ : 0 < delta₀ := by
    positivity
  refine ⟨delta₀, hdelta₀, min_le_right _ _, ?_⟩
  intro delta hdelta hdeltaThreshold
  have hdeltaThreshold' : delta ≤ threshold :=
    hdeltaThreshold.trans (min_le_left _ _)
  have hpositivePower :
      delta ^ (epsilon / 10) ≤
        rightConstant /
          (leftConstant * (2 : ℝ) ^ (1 - epsilon)) := by
    calc
      delta ^ (epsilon / 10)
          ≤ threshold ^ (epsilon / 10) :=
        Real.rpow_le_rpow hdelta.le hdeltaThreshold'
          (by positivity)
      _ =
          rightConstant /
            (leftConstant * (2 : ℝ) ^ (1 - epsilon)) := by
        dsimp only [threshold]
        rw [← Real.rpow_mul (by positivity)]
        have :
            (10 / epsilon) * (epsilon / 10) = 1 := by
          field_simp [hepsilon.ne']
        rw [this, Real.rpow_one]
  have hnegativePower :
      leftConstant * (2 : ℝ) ^ (1 - epsilon) /
            rightConstant ≤
        delta ^ (-epsilon / 10) := by
    have hinverse :
        delta ^ (-epsilon / 10) =
          (delta ^ (epsilon / 10))⁻¹ := by
      have : -epsilon / 10 = -(epsilon / 10) := by
        ring
      rw [this]
      exact Real.rpow_neg hdelta.le _
    rw [hinverse]
    calc
      leftConstant * (2 : ℝ) ^ (1 - epsilon) /
            rightConstant =
          (rightConstant /
            (leftConstant * (2 : ℝ) ^ (1 - epsilon)))⁻¹ := by
        field_simp
          [hleftConstant.ne', hrightConstant.ne', htwo.ne']
      _ ≤ (delta ^ (epsilon / 10))⁻¹ := by
        gcongr
  have hcoefficient :
      leftConstant * (2 : ℝ) ^ (1 - epsilon) ≤
        rightConstant * delta ^ (-epsilon / 10) := by
    calc
      leftConstant * (2 : ℝ) ^ (1 - epsilon) =
          rightConstant *
            (leftConstant * (2 : ℝ) ^ (1 - epsilon) /
              rightConstant) := by
        field_simp [hrightConstant.ne']
      _ ≤ rightConstant * delta ^ (-epsilon / 10) := by
        gcongr
  have hquotient :
      (2 / delta) ^ (1 - epsilon) =
        (2 : ℝ) ^ (1 - epsilon) *
          delta ^ (epsilon - 1) := by
    rw [show 2 / delta = (2 : ℝ) * delta⁻¹ by ring]
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    have hinversePower :
        (delta⁻¹) ^ (1 - epsilon) =
          delta ^ (-(1 - epsilon)) := by
      rw [Real.rpow_neg_eq_inv_rpow]
    rw [hinversePower]
    congr 2
    ring
  have hexponent :
      4 * (epsilon / 10) - 1 + epsilon / 2 =
        (epsilon - 1) + (-epsilon / 10) := by
    ring
  rw [hquotient, hexponent, Real.rpow_add hdelta]
  calc
    leftConstant *
          ((2 : ℝ) ^ (1 - epsilon) *
            delta ^ (epsilon - 1)) =
        (leftConstant * (2 : ℝ) ^ (1 - epsilon)) *
          delta ^ (epsilon - 1) := by
      ring
    _ ≤
        (rightConstant * delta ^ (-epsilon / 10)) *
          delta ^ (epsilon - 1) := by
      exact mul_le_mul_of_nonneg_right hcoefficient
        (Real.rpow_nonneg hdelta.le _)
    _ =
        rightConstant *
          (delta ^ (epsilon - 1) *
            delta ^ (-epsilon / 10)) := by
      ring

end Kakeya.Assouad
