module

/-
  Equation (89) logarithmic absorption for C_between bounds.

  Proves that the coarse logarithmic factor log(1/δ)^C_P is absorbed by
  the fine logarithmic factor log(1/δbar)^(C_P + 2*C_n) when:
  - δbar ≤ δ^τ (scale separation from non-bad scale ratio)
  - log(1/δbar) sufficiently large (δ smallness)

  Reference: OS paper, equation (89):
  [log(1/δ)]^{C_P + C_n} ≤ (1/τ)^{C_P + C_n} · [log(1/δbar)]^{C_P + C_n}
                        ≤ [log(1/δbar)]^{C_P + 2C_n}

  Whiteprint node: combining_theorem_genuine / inductive_step
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem

/-- Core equation-(89) logarithmic absorption.

    Given scale separation `δbar ≤ δ^τ` and sufficient smallness of δbar,
    the coarse logarithmic factor is bounded by the fine one with inflated exponent.

    This is the key inequality behind OS equation (89). -/
lemma equation89_log_absorption
    {δ δbar τ C_P C_n : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hδbar_pos : 0 < δbar)
    (hδbar_lt_one : δbar < 1)
    (hτ_pos : 0 < τ)
    (hτ_lt_one : τ < 1)
    (hCP : 1 ≤ C_P)
    (hCn_ge1 : 1 ≤ C_n)
    (h_scale_sep : δbar ≤ δ^τ)
    (h_small : Real.log (1 / δbar) ≥ τ ^ (-(C_P + C_n))) :
    (Real.log (1 / δ)) ^ C_P ≤ (Real.log (1 / δbar)) ^ (C_P + 2 * C_n) := by
  have h1 : 0 < Real.log (1 / δ) := by
    have h11 : 1 < 1 / δ := by
      apply one_lt_one_div hδ_pos
      exact hδ_lt_one
    exact Real.log_pos h11
  have h2 : 0 < Real.log (1 / δbar) := by
    have h21 : 1 < 1 / δbar := by
      apply one_lt_one_div hδbar_pos
      exact hδbar_lt_one
    exact Real.log_pos h21
  have h3 : 1 < Real.log (1 / δbar) := by
    have h4 : 0 < τ := hτ_pos
    have h5 : τ < 1 := hτ_lt_one
    have h6 : -(C_P + C_n) < 0 := by linarith [hCP, hCn_ge1]
    have h7 : τ ^ (-(C_P + C_n)) > 1 := by
      have h8 : τ ^ (-(C_P + C_n)) = (1 / τ) ^ (C_P + C_n) := by
        have h91 : τ ^ (-(C_P + C_n)) = (τ ^ (C_P + C_n)) ⁻¹ := by
          rw [Real.rpow_neg (by linarith)] <;> ring
        rw [h91]
        have h92 : (τ ^ (C_P + C_n)) ⁻¹ = (1 / τ) ^ (C_P + C_n) := by
          rw [← Real.inv_rpow (by linarith)] <;> ring_nf
        exact h92
      rw [h8]
      have h11 : 1 < 1 / τ := by
        apply one_lt_one_div h4
        exact h5
      have h12 : 0 < C_P + C_n := by linarith
      exact Real.one_lt_rpow h11 h12
    linarith [h_small]
  -- Step 1: δbar ≤ δ^τ implies log(1/δ) ≤ (1/τ) * log(1/δbar)
  have h_step1 : Real.log (1 / δ) ≤ (1 / τ) * Real.log (1 / δbar) := by
    have h9 : δbar ≤ δ ^ τ := h_scale_sep
    have h10 : (1 : ℝ) / δbar ≥ (1 / δ) ^ τ := by
      have h11 : 0 < δ := hδ_pos
      have h12 : 0 < δ ^ τ := by positivity
      have h13 : 1 / δbar ≥ 1 / δ ^ τ := by gcongr
      have h14 : 1 / δ ^ τ = (1 / δ) ^ τ := by
        have h141 : 1 / δ ^ τ = (δ ^ τ) ⁻¹ := by simp
        rw [h141]
        have h142 : (δ ^ τ) ⁻¹ = (1 / δ) ^ τ := by
          rw [← Real.inv_rpow (by linarith)] <;> ring_nf
        exact h142
      rw [h14] at h13
      exact h13
    have h15 : Real.log (1 / δbar) ≥ Real.log ((1 / δ) ^ τ) := Real.log_le_log (by positivity) h10
    have h16 : Real.log ((1 / δ) ^ τ) = τ * Real.log (1 / δ) := by
      rw [Real.log_rpow (by positivity)]
      <;> ring
    rw [h16] at h15
    have h17 : Real.log (1 / δbar) ≥ τ * Real.log (1 / δ) := h15
    have h18 : (1 / τ) * Real.log (1 / δbar) ≥ Real.log (1 / δ) := by
      calc (1 / τ) * Real.log (1 / δbar)
        ≥ (1 / τ) * (τ * Real.log (1 / δ)) := by gcongr
      _ = Real.log (1 / δ) := by
        field_simp [hτ_pos.ne'] <;> ring
    exact h18
  -- Step 2: (1/τ)^C_P ≤ log(1/δbar)^(2*C_n)
  have h_step2 : (1 / τ) ^ C_P ≤ (Real.log (1 / δbar)) ^ (2 * C_n) := by
    have h4 : Real.log (1 / δbar) ≥ τ ^ (-(C_P + C_n)) := h_small
    have h_pos1 : 0 < τ ^ (-(C_P + C_n)) := by positivity
    have h5 : Real.log (Real.log (1 / δbar)) ≥
        Real.log (τ ^ (-(C_P + C_n))) := Real.log_le_log (by linarith [h3, h_small]) h4
    have h6 : Real.log (τ ^ (-(C_P + C_n))) = (C_P + C_n) * Real.log (1 / τ) := by
      have h7 : Real.log (τ ^ (-(C_P + C_n))) = (-(C_P + C_n)) * Real.log τ := by
        rw [Real.log_rpow (by linarith)] <;> ring
      rw [h7]
      have h8 : Real.log τ = -Real.log (1 / τ) := by
        rw [Real.log_div (by norm_num) hτ_pos.ne'] <;> simp
      rw [h8] <;> ring
    rw [h6] at h5
    have h9 : Real.log (Real.log (1 / δbar)) ≥ (C_P + C_n) * Real.log (1 / τ) := h5
    have h10 : 2 * C_n * Real.log (Real.log (1 / δbar)) ≥ C_P * Real.log (1 / τ) := by
      have h11 : 2 * C_n * (C_P + C_n) ≥ C_P := by
        nlinarith [hCP, hCn_ge1]
      have h12 : 0 < Real.log (1 / τ) := by
        have h13 : 1 < 1 / τ := by
          apply one_lt_one_div hτ_pos
          exact hτ_lt_one
        exact Real.log_pos h13
      nlinarith [h9, h12]
    have h12 : (Real.log (1 / δbar)) ^ (2 * C_n) ≥ (1 / τ) ^ C_P := by
      have h13 : 0 < Real.log (1 / δbar) := by linarith
      have h14 : 0 < 1 / τ := by positivity
      have h15 : Real.log ((Real.log (1 / δbar)) ^ (2 * C_n)) =
          2 * C_n * Real.log (Real.log (1 / δbar)) := by
        rw [Real.log_rpow (by linarith [h3])] <;> ring
      have h16 : Real.log ((1 / τ) ^ C_P) = C_P * Real.log (1 / τ) := by
        rw [Real.log_rpow (by positivity)] <;> ring
      have h17 : Real.log ((Real.log (1 / δbar)) ^ (2 * C_n)) ≥
          Real.log ((1 / τ) ^ C_P) := by
        rw [h15, h16]
        exact h10
      by_contra h19
      have h20 : (Real.log (1 / δbar)) ^ (2 * C_n) < (1 / τ) ^ C_P := by linarith
      have h21 : 0 < (Real.log (1 / δbar)) ^ (2 * C_n) := by positivity
      have h22 : Real.log ((Real.log (1 / δbar)) ^ (2 * C_n)) <
          Real.log ((1 / τ) ^ C_P) := Real.log_lt_log h21 h20
      linarith
    exact h12
  -- Step 3: combine
  have h_step3 : (Real.log (1 / δ)) ^ C_P ≤
      (1 / τ) ^ C_P * (Real.log (1 / δbar)) ^ C_P := by
    have h19 : 0 ≤ Real.log (1 / δ) := by linarith
    have h20 : 0 ≤ Real.log (1 / δbar) := by linarith
    have h21 : Real.log (1 / δ) ≤ (1 / τ) * Real.log (1 / δbar) := h_step1
    have h22 : (Real.log (1 / δ)) ^ C_P ≤ ((1 / τ) * Real.log (1 / δbar)) ^ C_P := by
      gcongr <;> linarith
    have h23 : ((1 / τ) * Real.log (1 / δbar)) ^ C_P =
        (1 / τ) ^ C_P * (Real.log (1 / δbar)) ^ C_P := by
      rw [Real.mul_rpow] <;> positivity
    rw [h23] at h22
    exact h22
  calc (Real.log (1 / δ)) ^ C_P
    ≤ (1 / τ) ^ C_P * (Real.log (1 / δbar)) ^ C_P := h_step3
  _ = (Real.log (1 / δbar)) ^ C_P * (1 / τ) ^ C_P := by ring
  _ ≤ (Real.log (1 / δbar)) ^ C_P * (Real.log (1 / δbar)) ^ (2 * C_n) := by
    gcongr
    <;> linarith [h2, h3]
  _ = (Real.log (1 / δbar)) ^ (C_P + 2 * C_n) := by
    rw [← Real.rpow_add] <;> linarith [h2, h3]

/-- Full equation-(89) C_between bound transfer for normal scales.

    Given a coarse C_between bound with logarithmic factor log(1/δ)^C_P
    and ratio term ratio^ε_N, produces the fine bound with
    log(1/δbar)^(C_P + 2*C_n) and the same ratio term. -/
lemma equation89_cbetween_normal
    {δ δbar τ C_P C_n ε_N ratio : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hδbar_pos : 0 < δbar)
    (hδbar_lt_one : δbar < 1)
    (hτ_pos : 0 < τ)
    (hτ_lt_one : τ < 1)
    (hCP : 1 ≤ C_P)
    (hCn_ge1 : 1 ≤ C_n)
    (hεN : 0 < ε_N)
    (h_ratio_nonneg : 0 ≤ ratio)
    (h_scale_sep : δbar ≤ δ ^ τ)
    (h_small : Real.log (1 / δbar) ≥ τ ^ (-(C_P + C_n)))
    (C_between : ℝ)
    (h_coarse_bound : C_between ≤ (Real.log (1 / δ)) ^ C_P * ratio ^ ε_N) :
    C_between ≤ (Real.log (1 / δbar)) ^ (C_P + 2 * C_n) * ratio ^ ε_N := by
  have h_log : (Real.log (1 / δ)) ^ C_P ≤ (Real.log (1 / δbar)) ^ (C_P + 2 * C_n) :=
    equation89_log_absorption hδ_pos hδ_lt_one hδbar_pos hδbar_lt_one
      hτ_pos hτ_lt_one hCP hCn_ge1 h_scale_sep h_small
  calc C_between
    ≤ (Real.log (1 / δ)) ^ C_P * ratio ^ ε_N := h_coarse_bound
  _ ≤ (Real.log (1 / δbar)) ^ (C_P + 2 * C_n) * ratio ^ ε_N := by
    gcongr
    <;> exact h_log

/-- Full equation-(89) C_between bound transfer for good scales.

    Same as normal version but with ε_G instead of ε_N. -/
lemma equation89_cbetween_good
    {δ δbar τ C_P C_n ε_G ratio : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hδbar_pos : 0 < δbar)
    (hδbar_lt_one : δbar < 1)
    (hτ_pos : 0 < τ)
    (hτ_lt_one : τ < 1)
    (hCP : 1 ≤ C_P)
    (hCn_ge1 : 1 ≤ C_n)
    (hεG : 0 < ε_G)
    (h_ratio_nonneg : 0 ≤ ratio)
    (h_scale_sep : δbar ≤ δ ^ τ)
    (h_small : Real.log (1 / δbar) ≥ τ ^ (-(C_P + C_n)))
    (C_between : ℝ)
    (h_coarse_bound : C_between ≤ (Real.log (1 / δ)) ^ C_P * ratio ^ ε_G) :
    C_between ≤ (Real.log (1 / δbar)) ^ (C_P + 2 * C_n) * ratio ^ ε_G :=
  equation89_cbetween_normal hδ_pos hδ_lt_one hδbar_pos hδbar_lt_one
    hτ_pos hτ_lt_one hCP hCn_ge1 hεG h_ratio_nonneg h_scale_sep h_small C_between h_coarse_bound

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
