import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulKaufmanArithmetic

/-!
# Fine-scale logarithmic loss absorption for WZ1 Lemma 8.13

The coarsening operates at `fineScale = delta / (2 * aspect)`, not at `delta`.
Its logarithmic loss is therefore bounded by `20 * (1 + log(fineScale⁻¹))`,
which is larger than `20 * (1 + log(delta⁻¹))`.

This module shows the extra factor can still be absorbed into the remaining
exponent gap `normalizedEta - fineExponent`.
-/

namespace Kakeya.Assouad

noncomputable section

/--
Absorption of the fine-scale logarithmic Frostman loss.

The coarsening runs at `fineScale = delta / (2 * aspect)` with
`1 ≤ aspect ≤ 3 * delta^(-epsilon₁)`, so its log loss is
`20 * (1 + log(fineScale⁻¹))` rather than `20 * (1 + log(delta⁻¹))`.

We bound `fineScale⁻¹ ≤ 6 * delta^(-(1+epsilon₁))`, hence
`log(fineScale⁻¹) ≤ log 6 + (1+epsilon₁) * log(delta⁻¹)`. Since
`epsilon₁ < log 6`, this is `≤ (1 + log 6) * (1 + log(delta⁻¹))`.
The extra constant `1 + log 6` is absorbed by `log_poly_decay_general`
into the positive exponent gap `normalizedEta - fineExponent`.
-/
theorem wz1Lemma8_13_fineScale_log_absorption :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
      ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ aspect logLoss fineConstant : ℝ,
            1 ≤ aspect →
            aspect ≤ 3 * Real.rpow delta (-wz1Lemma8_13FaithfulEpsilonOne epsilon) →
            0 ≤ logLoss →
            logLoss ≤ 20 * (1 + Real.log ((delta / (2 * aspect))⁻¹)) →
            0 ≤ fineConstant →
            fineConstant ≤ 96 * Real.rpow delta (-wz1Lemma8_13FaithfulFineExponent epsilon) →
            16200 * logLoss * fineConstant ≤
              Real.rpow delta (-wz1Lemma8_13FaithfulNormalizedEta epsilon) := by
  intro epsilon hepsilon hepsilonOne
  let epsilon1 := wz1Lemma8_13FaithfulEpsilonOne epsilon
  let fineExponent := wz1Lemma8_13FaithfulFineExponent epsilon
  let normalizedEta := wz1Lemma8_13FaithfulNormalizedEta epsilon
  let fineGap := normalizedEta - fineExponent
  have hfineGap : 0 < fineGap :=
    wz1Lemma8_13_fine_exponent_gap hepsilon
  have hepsilon1_small : epsilon1 < 1 := by
    dsimp only [epsilon1, wz1Lemma8_13FaithfulEpsilonOne]
    nlinarith [sq_pos_of_pos hepsilon]
  have hlog6_gt_one : 1 < Real.log 6 := by
    have h_exp : Real.exp 1 < (6 : ℝ) := by
      have h : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
      linarith
    have h : Real.log (Real.exp 1) < Real.log 6 :=
      Real.log_lt_log (by positivity) h_exp
    have h2 : Real.log (Real.exp 1) = 1 := by simp
    rw [h2] at h
    exact h
  have hepsilon1_le_log6 : epsilon1 ≤ Real.log 6 := by
    linarith [hepsilon1_small, hlog6_gt_one]
  let K : ℝ := 16200 * 20 * 96 * (1 + Real.log 6)
  have hK_pos : 0 < K := by positivity
  rcases log_poly_decay_general K fineGap hK_pos hfineGap with
    ⟨delta₀, hdelta₀_pos, hdelta₀_one, hlog⟩
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta hdelta hdelta_small aspect logLoss fineConstant
    haspect_one haspect_upper hlogLoss_nonneg hlogLoss_bound
    hfineConstant_nonneg hfineConstant_bound
  have hdelta_one : delta ≤ 1 := hdelta_small.trans hdelta₀_one
  have haspect_pos : 0 < aspect := by linarith
  have hfineScale_pos : 0 < delta / (2 * aspect) := by positivity
  -- fineScale⁻¹ ≤ 6 * delta^(-(1 + epsilon1))
  have hfineScale_inv_bound :
      (delta / (2 * aspect))⁻¹ ≤ 6 * Real.rpow delta (-(1 + epsilon1)) := by
    have h1 : (delta / (2 * aspect))⁻¹ = (2 * aspect) / delta := by
      field_simp [hdelta.ne', haspect_pos.ne']
    rw [h1]
    have h2 : 2 * aspect ≤ 6 * Real.rpow delta (-epsilon1) := by
      calc
        2 * aspect ≤ 2 * (3 * Real.rpow delta (-epsilon1)) := by gcongr
        _ = 6 * Real.rpow delta (-epsilon1) := by ring
    have h3 : (2 * aspect) / delta ≤ (6 * Real.rpow delta (-epsilon1)) / delta := by
      gcongr
    have h4 : (6 * Real.rpow delta (-epsilon1)) / delta =
        6 * Real.rpow delta (-(1 + epsilon1)) := by
      have h51 : Real.rpow delta (-1) = delta⁻¹ := by
        have h : (delta : ℝ) ^ (-1 : ℝ) = ((delta : ℝ) ^ (1 : ℝ))⁻¹ :=
          Real.rpow_neg hdelta.le (1 : ℝ)
        simpa [Real.rpow_one] using h
      have h5 : Real.rpow delta (-epsilon1) / delta =
          Real.rpow delta (-epsilon1) * Real.rpow delta (-1) := by
        rw [div_eq_mul_inv, ←h51]
      have h6 : Real.rpow delta (-epsilon1) * Real.rpow delta (-1) =
          Real.rpow delta ((-epsilon1) + (-1)) :=
        (Real.rpow_add hdelta _ _).symm
      have h7 : (-epsilon1) + (-1 : ℝ) = (-(1 + epsilon1)) := by ring
      calc
        (6 * Real.rpow delta (-epsilon1)) / delta
          = 6 * (Real.rpow delta (-epsilon1) / delta) := by ring
        _ = 6 * (Real.rpow delta (-epsilon1) * Real.rpow delta (-1)) := by rw [h5]
        _ = 6 * Real.rpow delta ((-epsilon1) + (-1)) := by rw [h6]
        _ = 6 * Real.rpow delta (-(1 + epsilon1)) := by rw [h7]
    rw [h4] at h3
    exact h3
  -- log(fineScale⁻¹) ≤ log 6 + (1 + epsilon1) * log(delta⁻¹)
  have hlog_fineScale :
      Real.log ((delta / (2 * aspect))⁻¹) ≤
        Real.log 6 + (1 + epsilon1) * Real.log delta⁻¹ := by
    have h_rpow_pos : 0 < Real.rpow delta (-(1 + epsilon1)) :=
      Real.rpow_pos_of_pos hdelta _
    have h_pos : 0 < 6 * Real.rpow delta (-(1 + epsilon1)) :=
      mul_pos (by norm_num) h_rpow_pos
    have h21 : Real.log (6 * Real.rpow delta (-(1 + epsilon1))) =
        Real.log 6 + Real.log (Real.rpow delta (-(1 + epsilon1))) :=
      Real.log_mul (by norm_num) h_rpow_pos.ne'
    have h22 : Real.log (Real.rpow delta (-(1 + epsilon1))) =
        (-(1 + epsilon1)) * Real.log delta :=
      Real.log_rpow hdelta _
    have h2 : Real.log (6 * Real.rpow delta (-(1 + epsilon1))) =
        Real.log 6 + (-(1 + epsilon1)) * Real.log delta := by
      rw [h21, h22]
    have h3 : Real.log delta⁻¹ = -Real.log delta := Real.log_inv delta
    have h4 : Real.log delta = -Real.log delta⁻¹ := by linarith [h3]
    calc
      Real.log ((delta / (2 * aspect))⁻¹)
        ≤ Real.log (6 * Real.rpow delta (-(1 + epsilon1))) :=
          Real.log_le_log (by positivity) hfineScale_inv_bound
      _ = Real.log 6 + (-(1 + epsilon1)) * Real.log delta := h2
      _ = Real.log 6 + (-(1 + epsilon1)) * (-Real.log delta⁻¹) := by rw [h4]
      _ = Real.log 6 + (1 + epsilon1) * Real.log delta⁻¹ := by ring
  have hlog_delta_nonneg : 0 ≤ Real.log delta⁻¹ := by
    have h : delta⁻¹ ≥ 1 := (one_le_inv₀ hdelta).mpr hdelta_one
    exact Real.log_nonneg h
  -- 1 + log(fineScale⁻¹) ≤ (1 + log 6) * (1 + log(delta⁻¹))
  have h_bound1 :
      1 + Real.log ((delta / (2 * aspect))⁻¹) ≤
        (1 + Real.log 6) * (1 + Real.log delta⁻¹) := by
    calc
      1 + Real.log ((delta / (2 * aspect))⁻¹)
        ≤ 1 + Real.log 6 + (1 + epsilon1) * Real.log delta⁻¹ := by
          linarith [hlog_fineScale]
      _ = (1 + Real.log 6) + (1 + epsilon1) * Real.log delta⁻¹ := by ring
      _ ≤ (1 + Real.log 6) + (1 + Real.log 6) * Real.log delta⁻¹ := by
          gcongr
      _ = (1 + Real.log 6) * (1 + Real.log delta⁻¹) := by ring
  have hlogLoss2 :
      logLoss ≤ 20 * (1 + Real.log 6) * (1 + Real.log delta⁻¹) := by
    calc
      logLoss ≤ 20 * (1 + Real.log ((delta / (2 * aspect))⁻¹)) := hlogLoss_bound
      _ ≤ 20 * ((1 + Real.log 6) * (1 + Real.log delta⁻¹)) := by gcongr
      _ = 20 * (1 + Real.log 6) * (1 + Real.log delta⁻¹) := by ring
  have h_main1 : K * (Real.log delta⁻¹ + 1) ≤ 1 / Real.rpow delta fineGap := by
    simpa [add_comm] using hlog delta hdelta hdelta_small
  have h_product :
      16200 * logLoss * fineConstant ≤
        K * (Real.log delta⁻¹ + 1) * Real.rpow delta (-fineExponent) := by
    have h_left : 16200 * logLoss ≤
        16200 * (20 * (1 + Real.log 6) * (1 + Real.log delta⁻¹)) := by
      gcongr
    have h_right : fineConstant ≤ 96 * Real.rpow delta (-fineExponent) :=
      hfineConstant_bound
    have h_nonneg1 : 0 ≤ fineConstant := hfineConstant_nonneg
    have h_nonneg2 : 0 ≤ 16200 * (20 * (1 + Real.log 6) * (1 + Real.log delta⁻¹)) := by
      positivity
    calc
      16200 * logLoss * fineConstant
        ≤ (16200 * (20 * (1 + Real.log 6) * (1 + Real.log delta⁻¹))) * fineConstant := by
          gcongr
      _ ≤ (16200 * (20 * (1 + Real.log 6) * (1 + Real.log delta⁻¹))) *
            (96 * Real.rpow delta (-fineExponent)) := by
          gcongr
      _ = K * (Real.log delta⁻¹ + 1) * Real.rpow delta (-fineExponent) := by
          dsimp only [K]; ring
  have h_final :
      K * (Real.log delta⁻¹ + 1) * Real.rpow delta (-fineExponent) ≤
        Real.rpow delta (-normalizedEta) := by
    calc
      K * (Real.log delta⁻¹ + 1) * Real.rpow delta (-fineExponent)
        ≤ (1 / Real.rpow delta fineGap) * Real.rpow delta (-fineExponent) := by
          exact mul_le_mul_of_nonneg_right h_main1
            (Real.rpow_nonneg hdelta.le _)
      _ = Real.rpow delta (-fineGap) * Real.rpow delta (-fineExponent) := by
          have h5 : 1 / Real.rpow delta fineGap = Real.rpow delta (-fineGap) := by
            rw [one_div]
            exact (Real.rpow_neg hdelta.le fineGap).symm
          rw [h5]
      _ = Real.rpow delta ((-fineGap) + (-fineExponent)) :=
          (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta (-normalizedEta) := by
          congr 1
          dsimp only [fineGap]; ring
  exact h_product.trans h_final

end

end Kakeya.Assouad
