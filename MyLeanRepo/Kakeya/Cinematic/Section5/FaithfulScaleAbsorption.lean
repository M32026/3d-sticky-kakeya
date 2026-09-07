import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulAssemblyInputs

/-!
# Scale absorption for the faithful short-curve assembly

The dyadic logarithmic loss is absorbed by shrinking the physical scale
before the family, level set, and multiplicity are chosen.
-/

namespace Kakeya.Cinematic

lemma fixed_constant_rpow_absorption
    (C exponent : ℝ)
    (hC : 0 < C)
    (hexponent : 0 < exponent) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ {delta : ℝ},
        0 < delta →
        delta ≤ delta₀ →
        C * Real.rpow delta exponent ≤ 1 := by
  let threshold := Real.rpow C (-1 / exponent)
  have hthreshold : 0 < threshold :=
    Real.rpow_pos_of_pos hC _
  let delta₀ := min 1 threshold
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀_one : delta₀ ≤ 1 := by
    dsimp only [delta₀]
    exact min_le_left _ _
  have hdelta₀_threshold : delta₀ ≤ threshold := by
    dsimp only [delta₀]
    exact min_le_right _ _
  refine ⟨delta₀, hdelta₀, hdelta₀_one, ?_⟩
  intro delta hdelta hdeltaBound
  have hdeltaThreshold : delta ≤ threshold :=
    hdeltaBound.trans hdelta₀_threshold
  have hpower :
      Real.rpow delta exponent ≤
        Real.rpow threshold exponent :=
    Real.rpow_le_rpow hdelta.le hdeltaThreshold hexponent.le
  have hthresholdPower :
      Real.rpow threshold exponent = C⁻¹ := by
    dsimp only [threshold]
    calc
      Real.rpow (Real.rpow C (-1 / exponent)) exponent =
          Real.rpow C ((-1 / exponent) * exponent) :=
        (Real.rpow_mul hC.le (-1 / exponent) exponent).symm
      _ = Real.rpow C (-1) := by
        congr 1
        field_simp [hexponent.ne']
      _ = C⁻¹ := Real.rpow_neg_one C
  calc
    C * Real.rpow delta exponent ≤
        C * Real.rpow threshold exponent := by
      gcongr
    _ = C * C⁻¹ := by rw [hthresholdPower]
    _ = 1 := mul_inv_cancel₀ hC.ne'

lemma choose_internal_metric_exponent
    (targetExponent lossBudget : ℝ)
    (htarget : 0 < targetExponent)
    (hloss : 8 ≤ lossBudget) :
    ∃ metricExponent : ℝ,
      metricExponent =
          min targetExponent 1 / lossBudget ∧
      0 < metricExponent ∧
      metricExponent ≤ 1 / 4 ∧
      8 * metricExponent ≤ targetExponent ∧
      4 * metricExponent ≤ targetExponent ∧
      2 * metricExponent ≤ targetExponent ∧
      metricExponent < targetExponent := by
  let metricExponent := min targetExponent 1 / lossBudget
  have hlossPos : 0 < lossBudget := lt_of_lt_of_le (by norm_num) hloss
  have hmetric : 0 < metricExponent := by
    dsimp only [metricExponent]
    positivity
  have hmetricLoss :
      metricExponent * lossBudget = min targetExponent 1 := by
    dsimp only [metricExponent]
    field_simp [hlossPos.ne']
  have height :
      8 * metricExponent ≤ targetExponent := by
    have hscaled :
        8 * metricExponent ≤ lossBudget * metricExponent :=
      mul_le_mul_of_nonneg_right hloss hmetric.le
    have hlossMul :
        lossBudget * metricExponent = min targetExponent 1 := by
      rw [mul_comm]
      exact hmetricLoss
    rw [hlossMul] at hscaled
    exact hscaled.trans (min_le_left _ _)
  have hquarter : metricExponent ≤ 1 / 4 := by
    have hscaled :
        8 * metricExponent ≤ 1 :=
      calc
        8 * metricExponent ≤ lossBudget * metricExponent :=
          mul_le_mul_of_nonneg_right hloss hmetric.le
        _ = min targetExponent 1 := by
          rw [mul_comm]
          exact hmetricLoss
        _ ≤ 1 := min_le_right _ _
    linarith
  refine
    ⟨metricExponent, rfl, hmetric, hquarter, height,
      by linarith, by linarith, ?_⟩
  linarith

lemma choose_internal_metric_exponent_for_loss
    (targetExponent lossBudget : ℝ)
    (htarget : 0 < targetExponent) :
    ∃ metricExponent : ℝ,
      metricExponent =
          min targetExponent 1 /
            (2 * max 8 lossBudget) ∧
      0 < metricExponent ∧
      metricExponent ≤ 1 / 16 ∧
      8 * metricExponent < targetExponent ∧
      lossBudget * metricExponent < targetExponent ∧
      (3 / 2 : ℝ) *
          (metricExponent + metricExponent ^ 2 +
            metricExponent ^ 2) <
        targetExponent := by
  let denominator : ℝ := 2 * max 8 lossBudget
  let metricExponent : ℝ :=
    min targetExponent 1 / denominator
  have hmaxEight : 8 ≤ max 8 lossBudget :=
    le_max_left _ _
  have hmaxLoss : lossBudget ≤ max 8 lossBudget :=
    le_max_right _ _
  have hmaxPos : 0 < max 8 lossBudget :=
    lt_of_lt_of_le (by norm_num) hmaxEight
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    positivity
  have hmetric : 0 < metricExponent := by
    dsimp only [metricExponent]
    positivity
  have hmetricDenominator :
      metricExponent * denominator =
        min targetExponent 1 := by
    dsimp only [metricExponent]
    field_simp [hdenominator.ne']
  have hhalfTarget :
      max 8 lossBudget * metricExponent ≤
        targetExponent / 2 := by
    have hrewrite :
        max 8 lossBudget * metricExponent =
          (metricExponent * denominator) / 2 := by
      dsimp only [denominator]
      ring
    rw [hrewrite, hmetricDenominator]
    exact div_le_div_of_nonneg_right
      (min_le_left targetExponent 1) (by norm_num)
  have hhalfOne :
      max 8 lossBudget * metricExponent ≤ 1 / 2 := by
    have hrewrite :
        max 8 lossBudget * metricExponent =
          (metricExponent * denominator) / 2 := by
      dsimp only [denominator]
      ring
    rw [hrewrite, hmetricDenominator]
    exact div_le_div_of_nonneg_right
      (min_le_right targetExponent 1) (by norm_num)
  have hmetricSixteenth : metricExponent ≤ 1 / 16 := by
    have hscaled :
        8 * metricExponent ≤
          max 8 lossBudget * metricExponent :=
      mul_le_mul_of_nonneg_right hmaxEight hmetric.le
    linarith
  have height :
      8 * metricExponent < targetExponent := by
    have hscaled :
        8 * metricExponent ≤
          max 8 lossBudget * metricExponent :=
      mul_le_mul_of_nonneg_right hmaxEight hmetric.le
    have hhalfStrict : targetExponent / 2 < targetExponent := by
      linarith
    exact (hscaled.trans hhalfTarget).trans_lt hhalfStrict
  have hlossTarget :
      lossBudget * metricExponent < targetExponent := by
    have hscaled :
        lossBudget * metricExponent ≤
          max 8 lossBudget * metricExponent :=
      mul_le_mul_of_nonneg_right hmaxLoss hmetric.le
    have hhalfStrict : targetExponent / 2 < targetExponent := by
      linarith
    exact (hscaled.trans hhalfTarget).trans_lt hhalfStrict
  have hsquare :
      metricExponent ^ 2 ≤
        metricExponent / 16 := by
    nlinarith
  have hsmallJoint :
      (3 / 2 : ℝ) *
          (metricExponent + metricExponent ^ 2 +
            metricExponent ^ 2) <
        targetExponent := by
    have hsum :
        (3 / 2 : ℝ) *
            (metricExponent + metricExponent ^ 2 +
              metricExponent ^ 2) ≤
          2 * metricExponent := by
      nlinarith
    have htwo : 2 * metricExponent < targetExponent := by
      linarith [height]
    exact hsum.trans_lt htwo
  exact
    ⟨metricExponent, rfl, hmetric, hmetricSixteenth,
      height, hlossTarget, hsmallJoint⟩

lemma polynomial_loss_absorption
    (constant loss metricExponent targetExponent : ℝ)
    (hconstant : 0 < constant)
    (hgap : loss * metricExponent < targetExponent) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ {delta : ℝ},
        0 < delta →
        delta ≤ delta₀ →
        constant *
            Real.rpow delta (-(loss * metricExponent)) ≤
          Real.rpow delta (-targetExponent) := by
  let gap := targetExponent - loss * metricExponent
  have hgapPos : 0 < gap := by
    dsimp only [gap]
    linarith
  rcases fixed_constant_rpow_absorption
      constant gap hconstant hgapPos with
    ⟨delta₀, hdelta₀, hdelta₀One, hmain⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaBound
  have hsmall :
      constant * Real.rpow delta gap ≤ 1 :=
    hmain hdelta hdeltaBound
  have htargetNonneg :
      0 ≤ Real.rpow delta (-targetExponent) :=
    Real.rpow_nonneg hdelta.le _
  have hmul :
      constant * Real.rpow delta gap *
          Real.rpow delta (-targetExponent) ≤
        Real.rpow delta (-targetExponent) :=
    (mul_le_mul_of_nonneg_right hsmall htargetNonneg).trans_eq
      (one_mul _)
  have hexponent :
      gap + (-targetExponent) =
        -(loss * metricExponent) := by
    dsimp only [gap]
    ring
  have hpower :
      Real.rpow delta gap *
          Real.rpow delta (-targetExponent) =
        Real.rpow delta (-(loss * metricExponent)) := by
    calc
      Real.rpow delta gap *
          Real.rpow delta (-targetExponent) =
        Real.rpow delta (gap + (-targetExponent)) :=
          (Real.rpow_add hdelta gap (-targetExponent)).symm
      _ = Real.rpow delta (-(loss * metricExponent)) := by
        rw [hexponent]
  calc
    constant *
          Real.rpow delta (-(loss * metricExponent)) =
        constant *
          (Real.rpow delta gap *
            Real.rpow delta (-targetExponent)) := by
      rw [hpower]
    _ =
        constant * Real.rpow delta gap *
          Real.rpow delta (-targetExponent) := by ring
    _ ≤ Real.rpow delta (-targetExponent) := hmul

lemma polynomial_local_coefficient_absorption
    (constant loss metricExponent targetExponent : ℝ)
    (hconstant : 0 < constant)
    (hgap : loss * metricExponent < targetExponent) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ {delta mu : ℝ},
        0 < delta →
        delta ≤ delta₀ →
        0 ≤ mu →
        constant *
              Real.rpow delta (-(loss * metricExponent)) *
              Real.rpow mu (-3 / 2 : ℝ) ≤
            Real.rpow delta (-targetExponent) *
              Real.rpow mu (-3 / 2 : ℝ) := by
  rcases polynomial_loss_absorption
      constant loss metricExponent targetExponent
      hconstant hgap with
    ⟨delta₀, hdelta₀, hdelta₀One, hmain⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta mu hdelta hdeltaBound hmu
  exact mul_le_mul_of_nonneg_right
    (hmain hdelta hdeltaBound)
    (Real.rpow_nonneg hmu _)

private lemma helper_log_sq_le (y c : ℝ) (hy : 1 ≤ y) (hc : 0 < c) :
    (Real.log y) ^ 2 ≤ y ^ (c / 2) / (c ^ 2 / 16) := by
  have h1 : Real.log y ≤ y ^ (c / 4) / (c / 4) :=
    Real.log_le_rpow_div (by linarith) (by positivity)
  have h2 : 0 ≤ Real.log y := Real.log_nonneg hy
  have h3 : (Real.log y) ^ 2 ≤ (y ^ (c / 4) / (c / 4)) ^ 2 := by
    gcongr
  have h4 :
      (y ^ (c / 4) / (c / 4)) ^ 2 =
        y ^ (c / 2) / (c ^ 2 / 16) := by
    have h5 : (y ^ (c / 4)) ^ 2 = y ^ (c / 2) := by
      have h6 : c / 4 + c / 4 = c / 2 := by ring
      calc
        (y ^ (c / 4)) ^ 2 = y ^ (c / 4) * y ^ (c / 4) := by ring
        _ = y ^ (c / 4 + c / 4) := by
          rw [← Real.rpow_add (by linarith)]
        _ = y ^ (c / 2) := by rw [h6]
    have h7 : (c / 4) ^ 2 = c ^ 2 / 16 := by ring
    have h8 :
        (y ^ (c / 4) / (c / 4)) ^ 2 =
          (y ^ (c / 4)) ^ 2 / (c / 4) ^ 2 := by
      field_simp
    rw [h8, h5, h7]
  rw [h4] at h3
  exact h3

private lemma helper_N2_le
    (y : ℝ) (hy : 2 ≤ y) (N : ℕ)
    (hN : (N : ℝ) = Nat.ceil (Real.logb 2 y)) :
    (N : ℝ) ^ 2 + 1 ≤
      (5 / (Real.log 2) ^ 2) * (Real.log y) ^ 2 := by
  set z : ℝ := Real.logb 2 y with hz_def
  have hz_ge1 : 1 ≤ z := by
    have h : Real.logb 2 2 ≤ Real.logb 2 y :=
      Real.logb_le_logb_of_le (by norm_num) (by norm_num) hy
    simpa using h
  have hN_le : (N : ℝ) ≤ z + 1 := by
    rw [hN]
    have hz_nonneg : 0 ≤ z := by linarith
    have h1 : (Nat.ceil z : ℝ) < z + 1 :=
      Nat.ceil_lt_add_one hz_nonneg
    linarith
  have h_alg : (z + 1) ^ 2 + 1 ≤ 5 * z ^ 2 := by
    have h1 : 0 ≤ z - 1 := by linarith
    nlinarith
  have hz2 : z ^ 2 = (Real.log y) ^ 2 / (Real.log 2) ^ 2 := by
    simp [hz_def, Real.logb]
    ring
  calc
    (N : ℝ) ^ 2 + 1 ≤ (z + 1) ^ 2 + 1 := by
      gcongr <;> linarith
    _ ≤ 5 * z ^ 2 := h_alg
    _ = (5 / (Real.log 2) ^ 2) * (Real.log y) ^ 2 := by
      rw [hz2]
      ring

private lemma helper_y2_cond
    (C_log b K x y : ℝ) (hK : 1 ≤ K) (hb_pos : 0 < b)
    (hC_log_pos : 0 < C_log) (hx_pos : 0 < x) (hy_pos : 0 < y)
    (hy2 : ℝ) (hy_ge_y2 : hy2 ≤ y)
    (hy2_def :
      hy2 = (C_log * 16 * (4 * K) ^ b / b ^ 2) ^ (2 / b))
    (hlog_sq_le :
      (Real.log y) ^ 2 ≤ y ^ (b / 2) / (b ^ 2 / 16))
    (h_yx : y * x = 4 * K) :
    C_log * (Real.log y) ^ 2 * x ^ b ≤ 1 := by
  have hK_pos : 0 < K := by linarith
  have h4K_pos : 0 < 4 * K := by positivity
  have hy2_pos : 0 < hy2 := by
    rw [hy2_def]
    positivity
  have h9 : hy2 ^ (b / 2) ≤ y ^ (b / 2) :=
    Real.rpow_le_rpow hy2_pos.le hy_ge_y2 (by positivity)
  have h10 :
      hy2 ^ (b / 2) = C_log * 16 * (4 * K) ^ b / b ^ 2 := by
    rw [hy2_def]
    have h_pos : 0 < C_log * 16 * (4 * K) ^ b / b ^ 2 := by
      positivity
    have h1 : (2 / b) * (b / 2) = 1 := by
      field_simp [hb_pos.ne']
    have h2 :
        ((C_log * 16 * (4 * K) ^ b / b ^ 2) ^ (2 / b)) ^
            (b / 2) =
          (C_log * 16 * (4 * K) ^ b / b ^ 2) ^
            ((2 / b) * (b / 2)) := by
      rw [← Real.rpow_mul (by positivity)]
    rw [h2, h1, Real.rpow_one]
  have h12 : x = (4 * K) / y := by
    rw [eq_div_iff hy_pos.ne']
    rw [mul_comm]
    exact h_yx
  have h11 :
      y ^ (b / 2) * x ^ b = (4 * K) ^ b / y ^ (b / 2) := by
    rw [h12]
    have h14 : ((4 * K) / y) ^ b = (4 * K) ^ b / y ^ b := by
      rw [Real.div_rpow h4K_pos.le hy_pos.le]
    rw [h14]
    have h16 : y ^ b = y ^ (b / 2) * y ^ (b / 2) := by
      have h_sum : b / 2 + b / 2 = b := by linarith
      rw [← Real.rpow_add hy_pos, h_sum]
    rw [h16]
    have h_y_b_pos : 0 < y ^ b :=
      Real.rpow_pos_of_pos hy_pos b
    have h_y_b2_pos : 0 < y ^ (b / 2) :=
      Real.rpow_pos_of_pos hy_pos (b / 2)
    field_simp [h_y_b_pos.ne', h_y_b2_pos.ne']
  have h_4K_b_pos : 0 < (4 * K) ^ b :=
    Real.rpow_pos_of_pos h4K_pos b
  have h_y_b2_pos : 0 < y ^ (b / 2) :=
    Real.rpow_pos_of_pos hy_pos (b / 2)
  calc
    C_log * (Real.log y) ^ 2 * x ^ b ≤
        C_log * (y ^ (b / 2) / (b ^ 2 / 16)) * x ^ b := by
      gcongr
    _ = (C_log * 16 / b ^ 2) * (y ^ (b / 2) * x ^ b) := by
      ring
    _ =
        (hy2 ^ (b / 2) / (4 * K) ^ b) *
          (y ^ (b / 2) * x ^ b) := by
      have h17 :
          C_log * 16 / b ^ 2 =
            hy2 ^ (b / 2) / (4 * K) ^ b := by
        have h171 :
            C_log * 16 / b ^ 2 =
              (C_log * 16 * (4 * K) ^ b / b ^ 2) /
                (4 * K) ^ b := by
          field_simp [h_4K_b_pos.ne']
        rw [h171, ← h10]
      rw [h17]
    _ =
        (hy2 ^ (b / 2) / (4 * K) ^ b) *
          ((4 * K) ^ b / y ^ (b / 2)) := by
      rw [h11]
    _ = hy2 ^ (b / 2) / y ^ (b / 2) := by
      field_simp [h_4K_b_pos.ne', h_y_b2_pos.ne']
    _ ≤ 1 := by
      exact (div_le_one h_y_b2_pos).mpr h9

lemma bounded_multiplicity_scale_absorption
    (m T B : ℝ)
    (hB : 0 < B)
    (hmargin : (3 / 2 : ℝ) * m < T) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ {delta : ℝ} {mu : ℕ},
        0 < delta →
        delta ≤ delta₀ →
        0 < mu →
        delta ^ m * (mu : ℝ) < B →
        1 ≤
          delta ^ (-T) *
            (mu : ℝ) ^ (-3 / 2 : ℝ) := by
  set gap : ℝ := T - 3 * m / 2 with hgap_def
  have hgap : 0 < gap := by
    linarith
  set delta₀ : ℝ := min 1 (B ^ (-3 / (2 * gap))) with hdelta₀_def
  have hdelta₀_pos : 0 < delta₀ := by
    rw [hdelta₀_def]
    exact lt_min (by norm_num) (Real.rpow_pos_of_pos hB _)
  have hdelta₀_one : delta₀ ≤ 1 := by
    rw [hdelta₀_def]
    exact min_le_left _ _
  have hdelta₀_bound : delta₀ ≤ B ^ (-3 / (2 * gap)) := by
    rw [hdelta₀_def]
    exact min_le_right _ _
  have habsorb : B ^ (3 / 2 : ℝ) * delta₀ ^ gap ≤ 1 := by
    have h1 :
        delta₀ ^ gap ≤ (B ^ (-3 / (2 * gap))) ^ gap := by
      gcongr
    have h2 :
        (B ^ (-3 / (2 * gap))) ^ gap = B ^ (-3 / 2 : ℝ) := by
      rw [← Real.rpow_mul hB.le]
      have hmul : (-3 / (2 * gap)) * gap = -3 / 2 := by
        field_simp [hgap.ne']
      rw [hmul]
    have hdeltaPower :
        delta₀ ^ gap ≤ B ^ (-3 / 2 : ℝ) := h1.trans_eq h2
    calc
      B ^ (3 / 2 : ℝ) * delta₀ ^ gap ≤
          B ^ (3 / 2 : ℝ) * B ^ (-3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hdeltaPower
          (Real.rpow_nonneg hB.le _)
      _ = 1 := by
        rw [← Real.rpow_add hB]
        norm_num
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta mu hdelta hdelta_le hmu hscale
  have hdeltaM : 0 < delta ^ m := by
    positivity
  have hmuReal : 0 < (mu : ℝ) := by
    exact_mod_cast hmu
  have hmuUpper : (mu : ℝ) < B * delta ^ (-m) := by
    have h1 : (mu : ℝ) < B / delta ^ m := by
      rw [lt_div_iff₀ hdeltaM]
      simpa [mul_comm] using hscale
    have hneg : delta ^ (-m) = (delta ^ m)⁻¹ :=
      Real.rpow_neg hdelta.le m
    rw [hneg]
    simpa [div_eq_mul_inv] using h1
  have h13 :
      (mu : ℝ) ^ (3 / 2 : ℝ) <
        (B * delta ^ (-m)) ^ (3 / 2 : ℝ) := by
    gcongr
  have h14 :
      (B * delta ^ (-m)) ^ (3 / 2 : ℝ) =
        B ^ (3 / 2 : ℝ) * delta ^ (-(3 * m / 2)) := by
    rw [Real.mul_rpow hB.le (Real.rpow_nonneg hdelta.le _)]
    have hpow :
        (delta ^ (-m)) ^ (3 / 2 : ℝ) =
          delta ^ ((-m) * (3 / 2 : ℝ)) := by
      rw [← Real.rpow_mul hdelta.le]
    rw [hpow]
    congr 2
    ring
  rw [h14] at h13
  have hdeltaFactor :
      delta ^ T * delta ^ (-(3 * m / 2)) = delta ^ gap := by
    rw [← Real.rpow_add hdelta]
    congr 2
  have h15 :
      delta ^ T * (mu : ℝ) ^ (3 / 2 : ℝ) <
        B ^ (3 / 2 : ℝ) * delta ^ gap := by
    have hmul :=
      mul_lt_mul_of_pos_left h13
        (Real.rpow_pos_of_pos hdelta T)
    calc
      delta ^ T * (mu : ℝ) ^ (3 / 2 : ℝ) <
          delta ^ T *
            (B ^ (3 / 2 : ℝ) * delta ^ (-(3 * m / 2))) :=
        hmul
      _ = B ^ (3 / 2 : ℝ) * delta ^ gap := by
        calc
          delta ^ T *
              (B ^ (3 / 2 : ℝ) * delta ^ (-(3 * m / 2))) =
            B ^ (3 / 2 : ℝ) *
              (delta ^ T * delta ^ (-(3 * m / 2))) := by
            ring
          _ = B ^ (3 / 2 : ℝ) * delta ^ gap := by
            rw [hdeltaFactor]
  have hdeltaGap : delta ^ gap ≤ delta₀ ^ gap := by
    gcongr
  have h17 :
      delta ^ T * (mu : ℝ) ^ (3 / 2 : ℝ) < 1 := by
    calc
      delta ^ T * (mu : ℝ) ^ (3 / 2 : ℝ) <
          B ^ (3 / 2 : ℝ) * delta ^ gap :=
        h15
      _ ≤ B ^ (3 / 2 : ℝ) * delta₀ ^ gap := by
        gcongr
      _ ≤ 1 := habsorb
  have h18 :
      0 < delta ^ T * (mu : ℝ) ^ (3 / 2 : ℝ) := by
    positivity
  have h19 :
      1 < (delta ^ T * (mu : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
    rw [one_lt_inv_iff₀]
    exact ⟨h18, h17⟩
  have h20 :
      (delta ^ T * (mu : ℝ) ^ (3 / 2 : ℝ))⁻¹ =
        delta ^ (-T) * (mu : ℝ) ^ (-3 / 2 : ℝ) := by
    have h21 :
        (delta ^ T * (mu : ℝ) ^ (3 / 2 : ℝ))⁻¹ =
          (delta ^ T)⁻¹ * ((mu : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
      rw [mul_inv_rev]
      ring
    rw [h21]
    have h22 : (delta ^ T)⁻¹ = delta ^ (-T) := by
      rw [← Real.rpow_neg hdelta.le]
    have h23 :
        ((mu : ℝ) ^ (3 / 2 : ℝ))⁻¹ =
          (mu : ℝ) ^ (-3 / 2 : ℝ) := by
      rw [← Real.rpow_neg hmuReal.le]
      congr 2
      norm_num
    rw [h22, h23]
  rw [h20] at h19
  exact h19.le

/--
Choose a scale threshold that simultaneously absorbs the dyadic logarithmic
loss, the fixed geometric constant, and the singleton-fiber exit.
-/
lemma wz2_absorption_lemma
    (K L lambda epsilon epsilon' C_abs delta₀_FSV
      delta₀_singleton : ℝ)
    (hK : 1 ≤ K) (hL_nonneg : 0 ≤ L) (hlambda : 1 ≤ lambda)
    (_hepsilon : 0 < epsilon) (hepsilon'_pos : 0 < epsilon')
    (hepsilon'_lt : epsilon' < epsilon) (hC_abs_pos : 0 < C_abs)
    (hdelta₀_FSV_pos : 0 < delta₀_FSV)
    (hdelta₀_singleton_pos : 0 < delta₀_singleton) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 / lambda ∧
      delta₀ ≤ K / ((1 + L) * lambda) ∧
      delta₀ ≤ delta₀_FSV ∧
      (1 + L) * lambda * delta₀ ≤ delta₀_FSV ∧
      (1 + L) * lambda * delta₀ ≤ 1 / 2 ∧
      delta₀ ≤ delta₀_singleton ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∃ N : ℕ,
          (2 : ℝ) ^ N * ((1 + L) * lambda * delta) ≥ 4 * K ∧
          ((N : ℝ) ^ 2 + 1) * C_abs ≤
            Real.rpow ((1 + L) * lambda * delta)
              (-(epsilon - epsilon')) ∧
          ((N : ℝ) ^ 2 + 1) *
              ((1 + L) * lambda) ^ epsilon' * delta ^ epsilon' ≤
            1 := by
  set a : ℝ := epsilon - epsilon' with ha_def
  set b : ℝ := epsilon' with hb_def
  have ha_pos : 0 < a := by linarith
  have hb_pos : 0 < b := by linarith
  set C_log : ℝ := 5 / (Real.log 2) ^ 2 with hC_log_def
  have hC_log_pos : 0 < C_log := by positivity
  set y1 : ℝ :=
    (C_log * 16 * C_abs * (4 * K) ^ a / a ^ 2) ^ (2 / a)
    with hy1_def
  set y2 : ℝ :=
    (C_log * 16 * (4 * K) ^ b / b ^ 2) ^ (2 / b)
    with hy2_def
  have hy1_pos : 0 < y1 := by positivity
  have hy2_pos : 0 < y2 := by positivity
  set y0 : ℝ := max 2 (max y1 y2) with hy0_def
  have hy0_pos : 0 < y0 := by positivity
  have hy0_ge2 : 2 ≤ y0 := by
    simp [hy0_def]
  have hy0_ge_y1 : y1 ≤ y0 := by
    simp [hy0_def]
  have hy0_ge_y2 : y2 ≤ y0 := by
    simp [hy0_def]
  set x0 : ℝ := (4 * K) / y0 with hx0_def
  have hx0_pos : 0 < x0 := by positivity
  set d0 : ℝ := x0 / ((1 + L) * lambda) with hd0_def
  have hpos1 : 0 < (1 + L) * lambda := by positivity
  have hd0_pos : 0 < d0 := by positivity
  set delta₀ : ℝ :=
    min
      (min
        (min
          (min
            (min
              (min d0 (1 / lambda))
              (K / ((1 + L) * lambda)))
            delta₀_FSV)
          (delta₀_FSV / ((1 + L) * lambda)))
        (1 / (2 * (1 + L) * lambda)))
      delta₀_singleton
    with hdelta₀_def
  have hdelta₀_pos : 0 < delta₀ := by
    rw [hdelta₀_def]
    positivity
  have hdelta₀_le_d0 : delta₀ ≤ d0 := by
    rw [hdelta₀_def]
    exact
      le_trans (min_le_left _ _)
        (le_trans (min_le_left _ _)
          (le_trans (min_le_left _ _)
            (le_trans (min_le_left _ _)
              (le_trans (min_le_left _ _) (min_le_left _ _)))))
  have hdelta₀_le_lambda : delta₀ ≤ 1 / lambda := by
    rw [hdelta₀_def]
    exact
      le_trans (min_le_left _ _)
        (le_trans (min_le_left _ _)
          (le_trans (min_le_left _ _)
            (le_trans (min_le_left _ _)
              (le_trans (min_le_left _ _) (min_le_right _ _)))))
  have hdelta₀_le_K :
      delta₀ ≤ K / ((1 + L) * lambda) := by
    rw [hdelta₀_def]
    exact
      le_trans (min_le_left _ _)
        (le_trans (min_le_left _ _)
          (le_trans (min_le_left _ _)
            (le_trans (min_le_left _ _) (min_le_right _ _))))
  have hdelta₀_le_FSV : delta₀ ≤ delta₀_FSV := by
    rw [hdelta₀_def]
    exact
      le_trans (min_le_left _ _)
        (le_trans (min_le_left _ _)
          (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hdelta₀_vert_FSV :
      (1 + L) * lambda * delta₀ ≤ delta₀_FSV := by
    have h :
        delta₀ ≤ delta₀_FSV / ((1 + L) * lambda) := by
      rw [hdelta₀_def]
      exact
        le_trans (min_le_left _ _)
          (le_trans (min_le_left _ _) (min_le_right _ _))
    calc
      (1 + L) * lambda * delta₀ ≤
          (1 + L) * lambda *
            (delta₀_FSV / ((1 + L) * lambda)) := by
        gcongr
      _ = delta₀_FSV := by
        field_simp [hpos1.ne']
  have hdelta₀_half :
      (1 + L) * lambda * delta₀ ≤ 1 / 2 := by
    have h :
        delta₀ ≤ 1 / (2 * (1 + L) * lambda) := by
      rw [hdelta₀_def]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    calc
      (1 + L) * lambda * delta₀ ≤
          (1 + L) * lambda *
            (1 / (2 * (1 + L) * lambda)) := by
        gcongr
      _ = 1 / 2 := by
        field_simp [hpos1.ne']
  have hdelta₀_le_singleton : delta₀ ≤ delta₀_singleton := by
    rw [hdelta₀_def]
    exact min_le_right _ _
  refine
    ⟨delta₀, hdelta₀_pos, hdelta₀_le_lambda, hdelta₀_le_K,
      hdelta₀_le_FSV, hdelta₀_vert_FSV, hdelta₀_half,
      hdelta₀_le_singleton, ?_⟩
  intro delta hdelta hdelta_le_delta₀
  set x : ℝ := (1 + L) * lambda * delta with hx_def
  have hx_pos : 0 < x := by positivity
  have hdelta_le_d0 : delta ≤ d0 := by
    exact hdelta_le_delta₀.trans hdelta₀_le_d0
  have hx_le_x0 : x ≤ x0 := by
    calc
      x = (1 + L) * lambda * delta := by rw [hx_def]
      _ ≤ (1 + L) * lambda * d0 := by gcongr
      _ = x0 := by
        rw [hd0_def, hx0_def]
        field_simp [hpos1.ne']
  set y : ℝ := (4 * K) / x with hy_def
  have hy_pos : 0 < y := by positivity
  have h_yx : y * x = 4 * K := by
    rw [hy_def]
    exact div_mul_cancel₀ (4 * K) hx_pos.ne'
  have hy_ge_y0 : y0 ≤ y := by
    have h7 : (4 * K) / x0 ≤ (4 * K) / x := by
      gcongr
    have h8 : (4 * K) / x0 = y0 := by
      rw [hx0_def]
      field_simp [hy0_pos.ne']
    rw [h8] at h7
    exact h7
  have hy_ge2 : 2 ≤ y := hy0_ge2.trans hy_ge_y0
  have hy_ge_y1 : y1 ≤ y := hy0_ge_y1.trans hy_ge_y0
  have hy_ge_y2 : y2 ≤ y := hy0_ge_y2.trans hy_ge_y0
  set N : ℕ := Nat.ceil (Real.logb 2 y) with hN_def
  have hN_ge : Real.logb 2 y ≤ (N : ℝ) :=
    Nat.le_ceil (Real.logb 2 y)
  have h_pow_eq : (2 : ℝ) ^ N ≥ y := by
    have h4 : (2 : ℝ) ^ (Real.logb 2 y) = y :=
      Real.rpow_logb (by norm_num) (by norm_num) hy_pos
    have h6 :
        Real.rpow (2 : ℝ) (Real.logb 2 y) ≤
          Real.rpow (2 : ℝ) (N : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hN_ge
    calc
      y = (2 : ℝ) ^ (Real.logb 2 y) := h4.symm
      _ ≤ Real.rpow (2 : ℝ) (N : ℝ) := h6
      _ = (2 : ℝ) ^ N := Real.rpow_natCast (2 : ℝ) N
  have hcond1 : (2 : ℝ) ^ N * x ≥ 4 * K := by
    calc
      (2 : ℝ) ^ N * x ≥ y * x := by gcongr
      _ = 4 * K := h_yx
  have hN2_le :
      (N : ℝ) ^ 2 + 1 ≤ C_log * (Real.log y) ^ 2 :=
    helper_N2_le y hy_ge2 N (by simp [hN_def, hC_log_def])
  have hlog_sq_le_a :
      (Real.log y) ^ 2 ≤ y ^ (a / 2) / (a ^ 2 / 16) :=
    helper_log_sq_le y a (by linarith) ha_pos
  have hlog_sq_le_b :
      (Real.log y) ^ 2 ≤ y ^ (b / 2) / (b ^ 2 / 16) :=
    helper_log_sq_le y b (by linarith) hb_pos
  have h_y1_cond :
      C_log * (Real.log y) ^ 2 * C_abs ≤
        y ^ a / (4 * K) ^ a := by
    have h7 :
        C_log * (Real.log y) ^ 2 * C_abs ≤
          C_log * (y ^ (a / 2) / (a ^ 2 / 16)) * C_abs := by
      gcongr
    have h9 : y1 ^ (a / 2) ≤ y ^ (a / 2) :=
      Real.rpow_le_rpow hy1_pos.le hy_ge_y1 (by positivity)
    have h10 :
        y1 ^ (a / 2) =
          C_log * 16 * C_abs * (4 * K) ^ a / a ^ 2 := by
      rw [hy1_def]
      have h_mul :
          ((C_log * 16 * C_abs * (4 * K) ^ a / a ^ 2) ^
              (2 / a)) ^ (a / 2) =
            C_log * 16 * C_abs * (4 * K) ^ a / a ^ 2 := by
        have h1 : (2 / a) * (a / 2) = 1 := by
          field_simp [ha_pos.ne']
        rw [← Real.rpow_mul (by positivity), h1, Real.rpow_one]
      exact h_mul
    have h13 :
        C_log * 16 * C_abs / a ^ 2 ≤
          y ^ (a / 2) / (4 * K) ^ a := by
      calc
        C_log * 16 * C_abs / a ^ 2 =
            (C_log * 16 * C_abs * (4 * K) ^ a / a ^ 2) /
              (4 * K) ^ a := by
          field_simp
        _ = y1 ^ (a / 2) / (4 * K) ^ a := by rw [← h10]
        _ ≤ y ^ (a / 2) / (4 * K) ^ a := by gcongr
    have h14 : y ^ a = y ^ (a / 2) * y ^ (a / 2) := by
      have h_sum : a / 2 + a / 2 = a := by linarith
      rw [← Real.rpow_add hy_pos, h_sum]
    calc
      C_log * (Real.log y) ^ 2 * C_abs ≤
          C_log * (y ^ (a / 2) / (a ^ 2 / 16)) * C_abs :=
        h7
      _ = (C_log * 16 * C_abs / a ^ 2) * y ^ (a / 2) := by
        ring_nf
      _ ≤
          (y ^ (a / 2) / (4 * K) ^ a) * y ^ (a / 2) := by
        gcongr
      _ = y ^ a / (4 * K) ^ a := by
        rw [h14]
        ring
  have hcond2 :
      ((N : ℝ) ^ 2 + 1) * C_abs ≤ Real.rpow x (-a) := by
    calc
      ((N : ℝ) ^ 2 + 1) * C_abs ≤
          C_log * (Real.log y) ^ 2 * C_abs := by
        gcongr
      _ ≤ y ^ a / (4 * K) ^ a := h_y1_cond
      _ = (y / (4 * K)) ^ a := by
        rw [← Real.div_rpow (by positivity) (by positivity) a]
      _ = (1 / x) ^ a := by
        have h16 : y / (4 * K) = 1 / x := by
          field_simp [hx_pos.ne', hy_pos.ne']
          linarith
        rw [h16]
      _ = Real.rpow x (-a) := by
        have h17 :
            (1 / x) ^ a = (1 : ℝ) ^ a / x ^ a :=
          Real.div_rpow (by norm_num) (by positivity) a
        have h17b : (1 : ℝ) ^ a = 1 := Real.one_rpow a
        have h18 :
            Real.rpow x (-a) = (x ^ a)⁻¹ :=
          Real.rpow_neg (by positivity) a
        have h19 : (x ^ a)⁻¹ = 1 / x ^ a := by simp
        rw [h17, h17b, h18, h19]
  have h_y2_cond :
      C_log * (Real.log y) ^ 2 * x ^ b ≤ 1 :=
    helper_y2_cond C_log b K x y hK hb_pos hC_log_pos
      hx_pos hy_pos y2 hy_ge_y2 hy2_def hlog_sq_le_b h_yx
  have hcond3 : ((N : ℝ) ^ 2 + 1) * x ^ b ≤ 1 := by
    calc
      ((N : ℝ) ^ 2 + 1) * x ^ b ≤
          C_log * (Real.log y) ^ 2 * x ^ b := by
        gcongr
      _ ≤ 1 := h_y2_cond
  have h_rpow_conv :
      Real.rpow x (-a) =
        Real.rpow ((1 + L) * lambda * delta)
          (-(epsilon - epsilon')) := by
    rw [hx_def, ha_def]
  have h_x_b_conv :
      x ^ b =
        ((1 + L) * lambda) ^ epsilon' * delta ^ epsilon' := by
    rw [hx_def, hb_def]
    rw [Real.mul_rpow (by positivity) (by positivity)]
  refine ⟨N, hcond1, ?_⟩
  rw [h_rpow_conv] at hcond2
  rw [h_x_b_conv] at hcond3
  have hcond3' :
      ((N : ℝ) ^ 2 + 1) * ((1 + L) * lambda) ^ b * delta ^ b ≤
        1 := by
    have hb : b = epsilon' := hb_def
    have h :
        ((N : ℝ) ^ 2 + 1) * ((1 + L) * lambda) ^ b * delta ^ b =
          ((N : ℝ) ^ 2 + 1) *
            (((1 + L) * lambda) ^ epsilon' * delta ^ epsilon') := by
      rw [hb]
      ring
    rw [h]
    exact hcond3
  exact ⟨hcond2, hcond3'⟩

end Kakeya.Cinematic
