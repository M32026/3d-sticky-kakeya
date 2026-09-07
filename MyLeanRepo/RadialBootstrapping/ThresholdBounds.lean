module

/-
  ThresholdBounds.lean

  Proves the two threshold bounds required by shrink_r2:
    hB_large : B > 8 / K'^(1/(σ+τ))
    hB_lt_Kinv : B < K^(-1/τ)

  for an explicitly constructed B.

  Key insight: every threshold has K/C exponent ratio ≤ 1/τ, while
  M/(σ+τ) ≫ 1/τ (since M > 400/τ²), so Q^(-1/τ) ≫ Q^(-M/(σ+τ)).
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Classical
open scoped ENNReal NNReal

set_option maxHeartbeats 500000

noncomputable section

namespace RadialBootstrapping

/-- General threshold bound: if a threshold has the form
    (c / (K^a * C^b))^(1/e) with (a+b)/e ≤ 1/τ, e ≥ τ/2, c ≥ Q^(-100),
    and Q, M are large enough, then the threshold exceeds 8 / Q^(M/(σ+τ)). -/
lemma general_threshold_bound
    (Q M σ τ : ℝ)
    (hQ_large : Q > 4000 / τ^2)
    (hM_large : M > 400 / τ^2)
    (hτ_pos : 0 < τ) (hτ_lt_one : τ < 1) (hτ_small : τ < 1 / 14)
    (hστ_pos : 0 < σ + τ) (hστ_lt_two : σ + τ < 2)
    (c a b e : ℝ)
    (hc_pos : 0 < c) (ha_nonneg : 0 ≤ a) (hb_nonneg : 0 ≤ b) (he_pos : 0 < e)
    (h_ratio : (a + b) / e ≤ 1 / τ)
    (h_ge_half : e ≥ τ / 2)
    (h_c_lower : c ≥ Real.rpow Q (-100))
    (K C : ℝ) (hK_one : 1 ≤ K) (hC_one : 1 ≤ C)
    (hK_le_Q : K ≤ Q) (hC_le_Q : C ≤ Q) :
    Real.rpow (c / (Real.rpow K a * Real.rpow C b)) (1 / e) >
    8 / Real.rpow Q (M / (σ + τ)) := by
  have hQ_pos : 0 < Q := by linarith
  have hτ2_lt_one : τ^2 < 1 := by nlinarith
  have hQ_gt_4000 : Q > 4000 := by
    have h1 : 1 / τ^2 > 1 := by
      have h2 : 0 < τ^2 := by positivity
      exact one_lt_one_div h2 hτ2_lt_one
    calc Q > 4000 / τ^2 := hQ_large
      _ = 4000 * (1 / τ^2) := by ring
      _ > 4000 * (1 : ℝ) := by gcongr
      _ = 4000 := by ring
  have hQ_gt_one : 1 < Q := by linarith
  have hK_pos : 0 < K := by linarith
  have hC_pos : 0 < C := by linarith
  have hK_nonneg : 0 ≤ K := by linarith
  have hC_nonneg : 0 ≤ C := by linarith

  -- Step 1: K^a * C^b ≤ Q^(a+b)
  have hKa_pos : 0 < Real.rpow K a := Real.rpow_pos_of_pos hK_pos a
  have hCb_pos : 0 < Real.rpow C b := Real.rpow_pos_of_pos hC_pos b
  have h1 : Real.rpow K a ≤ Real.rpow Q a :=
    Real.rpow_le_rpow hK_nonneg hK_le_Q ha_nonneg
  have h2 : Real.rpow C b ≤ Real.rpow Q b :=
    Real.rpow_le_rpow hC_nonneg hC_le_Q hb_nonneg
  have hQa_nonneg : 0 ≤ Real.rpow Q a := Real.rpow_nonneg hQ_pos.le a
  have h3 : Real.rpow K a * Real.rpow C b ≤ Real.rpow Q (a + b) := by
    have h4 : Real.rpow Q (a + b) = Real.rpow Q a * Real.rpow Q b :=
      Real.rpow_add hQ_pos a b
    rw [h4]
    exact mul_le_mul h1 h2 hCb_pos.le hQa_nonneg

  -- Step 2: c / (K^a * C^b) ≥ Q^(-(a+b+2))
  have h_prod_pos : 0 < Real.rpow K a * Real.rpow C b := mul_pos hKa_pos hCb_pos
  have hQab_pos : 0 < Real.rpow Q (a + b) := Real.rpow_pos_of_pos hQ_pos (a + b)
  have hQ_negk_pos : 0 < Real.rpow Q (-100) := Real.rpow_pos_of_pos hQ_pos (-100)
  have hQ_neg_abk : Real.rpow Q (-(a + b + 100)) = Real.rpow Q (-100) / Real.rpow Q (a + b) := by
    have h51 : (-(a + b + 100) : ℝ) = -100 - (a + b) := by ring
    rw [h51]
    have h52 : Real.rpow Q (-100 - (a + b)) = Real.rpow Q (-100) / Real.rpow Q (a + b) := by
      have h53 := Real.rpow_sub hQ_pos (-100) (a + b)
      exact h53
    exact h52
  have h5 : c / (Real.rpow K a * Real.rpow C b) ≥ Real.rpow Q (-(a + b + 100)) := by
    rw [hQ_neg_abk]
    have h_pos_a : 0 ≤ Real.rpow Q (-100) := by positivity
    have h53 : c / (Real.rpow K a * Real.rpow C b) ≥
        (Real.rpow Q (-100)) / (Real.rpow K a * Real.rpow C b) := by
      have h531 : c ≥ Real.rpow Q (-100) := h_c_lower
      have h532 : 0 < Real.rpow K a * Real.rpow C b := h_prod_pos
      exact div_le_div_of_nonneg_right h531 h532.le
    have h54 : (Real.rpow Q (-100)) / (Real.rpow K a * Real.rpow C b) ≥
        (Real.rpow Q (-100)) / Real.rpow Q (a + b) := by
      have h541 : 0 ≤ Real.rpow Q (-100) := h_pos_a
      have h542 : 0 < Real.rpow K a * Real.rpow C b := h_prod_pos
      have h543 : Real.rpow K a * Real.rpow C b ≤ Real.rpow Q (a + b) := h3
      have h544 : (Real.rpow Q (-100)) / Real.rpow Q (a + b) ≤
          (Real.rpow Q (-100)) / (Real.rpow K a * Real.rpow C b) :=
        div_le_div_of_nonneg_left h541 (by positivity) h543
      exact h544
    exact h54.trans h53

  -- Step 3: threshold ≥ Q^(-(a+b+2)/e)
  have hQ_neg_abk_pos2 : 0 < Real.rpow Q (-(a + b + 100)) := Real.rpow_pos_of_pos hQ_pos _
  have h_one_over_e_pos : 0 < 1 / e := by positivity
  have h10 : Real.rpow (c / (Real.rpow K a * Real.rpow C b)) (1 / e) ≥
      Real.rpow Q (-(a + b + 100) / e) := by
    have h11 : (Real.rpow Q (-(a + b + 100))) ^ (1 / e) =
        Real.rpow Q ((-(a + b + 100)) * (1 / e)) :=
      (Real.rpow_mul hQ_pos.le (-(a + b + 100)) (1 / e)).symm
    have h13 : (-(a + b + 100)) * (1 / e) = -(a + b + 100) / e := by ring
    have h12 : Real.rpow Q (-(a + b + 100) / e) =
        (Real.rpow Q (-(a + b + 100))) ^ (1 / e) := by
      have h14 : Real.rpow Q (-(a + b + 100) / e) = Real.rpow Q ((-(a + b + 100)) * (1 / e)) := by
        rw [h13]
      rw [h14]
      exact h11.symm
    rw [h12]
    have h15 : Real.rpow Q (-(a + b + 100)) ≤ c / (Real.rpow K a * Real.rpow C b) := h5
    exact Real.rpow_le_rpow hQ_neg_abk_pos2.le h15 (by positivity)

  -- Step 4: (a+b+100)/e ≤ 201/τ
  have h12 : (a + b + 100) / e ≤ 201 / τ := by
    have h13 : (a + b + 100) / e = (a + b) / e + 100 / e := by
      field_simp [he_pos.ne'] <;> ring
    rw [h13]
    have h14 : 100 / e ≤ 200 / τ := by
      have h15 : 0 < τ / 2 := by positivity
      have h16 : 1 / e ≤ 2 / τ := by
        calc 1 / e ≤ 1 / (τ / 2) := by gcongr
          _ = 2 / τ := by
            field_simp [h15.ne'] <;> ring
      calc 100 / e = 100 * (1 / e) := by ring
        _ ≤ 100 * (2 / τ) := by gcongr
        _ = 200 / τ := by ring
    have h17 : (a + b) / e ≤ 1 / τ := h_ratio
    have h18 : (a + b) / e + 100 / e ≤ 1 / τ + 200 / τ := by
      exact add_le_add h17 h14
    have h19 : 1 / τ + 200 / τ = 201 / τ := by ring
    rw [h19] at h18
    exact h18

  -- Step 5: Q^(-(a+b+100)/e) ≥ Q^(-201/τ)
  have h17 : -(a + b + 100) / e ≥ -201 / τ := by
    have h18 : (a + b + 100) / e ≤ 201 / τ := h12
    have h19 : -(a + b + 100) / e = -((a + b + 100) / e) := by ring
    rw [h19]
    have h20 : -((a + b + 100) / e) ≥ -(201 / τ) := neg_le_neg h18
    have h21 : -(201 / τ) = -201 / τ := by ring
    rw [h21] at h20
    exact h20
  have h18 : Real.rpow Q (-(a + b + 100) / e) ≥ Real.rpow Q (-201 / τ) :=
    Real.rpow_le_rpow_of_exponent_le hQ_gt_one.le h17

  -- Step 6: M/(σ+τ) - 201/τ > 1
  have h19 : M / (σ + τ) - 201 / τ > 1 := by
    have h20 : M / (σ + τ) > 200 / τ^2 := by
      have h21 : 0 < σ + τ := hστ_pos
      have h22 : σ + τ < 2 := hστ_lt_two
      calc M / (σ + τ) > (400 / τ^2) / (σ + τ) := by gcongr
        _ > (400 / τ^2) / 2 := by gcongr
        _ = 200 / τ^2 := by ring
    have h23 : 0 < τ^2 := by positivity
    have h24 : 201 / τ < 201 / τ^2 := by
      have h25 : τ^2 < τ := by nlinarith
      have h26 : 0 < τ := hτ_pos
      have h27 : 1 / τ < 1 / τ^2 := one_div_lt_one_div_of_lt (by positivity) h25
      calc 201 / τ = 201 * (1 / τ) := by ring
        _ < 201 * (1 / τ^2) := by gcongr
        _ = 201 / τ^2 := by ring
    have h31 : (200 : ℝ) / τ^2 - 201 / τ > 1 := by
      have h32 : 201 * τ < 201 / 14 := by
        have h33 : τ < 1 / 14 := hτ_small
        nlinarith
      have h34 : 200 - 201 * τ > 185 := by nlinarith
      have h35 : τ^2 < 1 / 196 := by nlinarith [hτ_small]
      have h36 : 1 / τ^2 > 196 := by
        have h37 : 0 < τ^2 := by positivity
        have h38 : τ^2 < 1 / 196 := h35
        have h39 : 1 / τ^2 > 1 / (1 / 196) := one_div_lt_one_div_of_lt h37 h38
        have h40 : 1 / (1 / 196 : ℝ) = 196 := by norm_num
        rw [h40] at h39
        exact h39
      have h41 : (200 - 201 * τ) / τ^2 > 185 / τ^2 := by
        apply div_lt_div_of_pos_right h34 (by positivity)
      have h42 : 185 / τ^2 > 185 * (196 : ℝ) := by
        have h43 : 1 / τ^2 > 196 := h36
        have h44 : 185 / τ^2 = 185 * (1 / τ^2) := by ring
        rw [h44]
        gcongr
      have h45 : 185 * (196 : ℝ) > 1 := by norm_num
      have h46 : (200 - 201 * τ) / τ^2 > 1 := by linarith
      have h47 : (200 : ℝ) / τ^2 - 201 / τ = (200 - 201 * τ) / τ^2 := by
        field_simp [h23.ne'] <;> ring
      rw [h47]
      exact h46
    have h_goal : M / (σ + τ) - 201 / τ > 1 := by
      have h41 : M / (σ + τ) > (200 : ℝ) / τ^2 := h20
      linarith [h31]
    exact h_goal

  -- Step 7: Q^(M/(σ+τ) - 201/τ) > 8
  have h28 : Real.rpow Q (M / (σ + τ) - 201 / τ) > 8 := by
    have h29 : 1 < M / (σ + τ) - 201 / τ := h19
    have h30 : Real.rpow Q (M / (σ + τ) - 201 / τ) > Real.rpow Q 1 :=
      Real.rpow_lt_rpow_of_exponent_lt hQ_gt_one h29
    have h31 : Real.rpow Q 1 = Q := Real.rpow_one Q
    rw [h31] at h30
    have h32 : Q > 8 := by linarith [hQ_gt_4000]
    linarith

  -- Step 8: Q^(-201/τ) > 8 * Q^(-M/(σ+τ))
  have h33 : 0 < Real.rpow Q (M / (σ + τ)) := Real.rpow_pos_of_pos hQ_pos _
  have h34 : Real.rpow Q (M / (σ + τ) - 201 / τ) * Real.rpow Q (-(M / (σ + τ))) =
      Real.rpow Q (-201 / τ) := by
    have h35 := Real.rpow_add hQ_pos (M / (σ + τ) - 201 / τ) (-(M / (σ + τ)))
    have h36 : (M / (σ + τ) - 201 / τ) + (-(M / (σ + τ))) = -201 / τ := by ring
    rw [h36] at h35
    exact h35.symm
  have h37 : 0 < Real.rpow Q (-(M / (σ + τ))) := Real.rpow_pos_of_pos hQ_pos _
  have h38 : Real.rpow Q (-201 / τ) > 8 * Real.rpow Q (-(M / (σ + τ))) := by
    have h39 : Real.rpow Q (M / (σ + τ) - 201 / τ) > 8 := h28
    have h40 : Real.rpow Q (M / (σ + τ) - 201 / τ) * Real.rpow Q (-(M / (σ + τ))) >
        8 * Real.rpow Q (-(M / (σ + τ))) :=
      mul_lt_mul_of_pos_right h39 h37
    rw [h34] at h40
    exact h40

  -- Conclusion
  have h41 : Real.rpow Q (-(M / (σ + τ))) = (Real.rpow Q (M / (σ + τ)))⁻¹ :=
    Real.rpow_neg hQ_pos.le (M / (σ + τ))
  calc Real.rpow (c / (Real.rpow K a * Real.rpow C b)) (1 / e)
    ≥ Real.rpow Q (-(a + b + 100) / e) := h10
  _ ≥ Real.rpow Q (-201 / τ) := h18
  _ > 8 * Real.rpow Q (-(M / (σ + τ))) := h38
  _ = 8 / Real.rpow Q (M / (σ + τ)) := by
    rw [h41]
    <;> field_simp [h33.ne'] <;> ring

end RadialBootstrapping
