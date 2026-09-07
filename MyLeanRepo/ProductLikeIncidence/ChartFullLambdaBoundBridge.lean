module

/-
# ChartFullLambda Bound Bridge

Produces `h_chartFullLambda_bound` required by `glue_h5_to_h6`:
  `∀ (i : Fin 4) (y : ℝ), sectorPredicate i x y → |chartFullLambda i y θ1 θ3 θ2 x| ≤ 1`
-/

public import MyLeanRepo.ProductLikeIncidence.ChartFullLambda
public import MyLeanRepo.FourSectorSelection
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set ENNReal Bornology Classical

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

namespace ProductLikeIncidence.ProductReduction

/-! ========================================================================
   Sector 0: 0 ≤ x y ≤ 1  ⟹  θ1 ≤ y ≤ θ3  ⟹  0 < λ ≤ 1
   ======================================================================== -/

private lemma sector0_bound
    {θ1 θ3 θ2 y : ℝ} {x : ℝ → ℝ}
    (h13 : θ1 < θ3) (h32 : θ3 < θ2)
    (hx_formula : ∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y)))
    (h : 0 ≤ x y ∧ x y ≤ 1) :
    |chartFullLambda 0 y θ1 θ3 θ2 x| ≤ 1 := by
  have h_pos : 0 ≤ x y := h.1
  have h_le : x y ≤ 1 := h.2
  by_cases hy2 : y = θ2
  · simp [hy2, chartFullLambda]
  · have h_ne : θ2 - y ≠ 0 := by intro h'; exact hy2 (by linarith)
    have hdenom_pos : 0 < θ2 - y := by
      by_cases h' : 0 < θ2 - y; exact h'
      have h'' : θ2 - y < 0 := by by_contra h'''; exact h_ne (by linarith)
      have h_gt : θ2 < y := by linarith
      have h_a : 0 < (θ2 - θ3) * (y - θ1) := by nlinarith
      have h_b : (θ3 - θ1) * (θ2 - y) < 0 := by nlinarith
      have h_xneg : x y < 0 := by
        rw [hx_formula y]; exact div_neg_of_pos_of_neg h_a h_b
      linarith
    have hy1 : θ1 ≤ y := by
      by_cases h' : y < θ1
      · have h_a : (θ2 - θ3) * (y - θ1) < 0 := by nlinarith
        have h_b : 0 < (θ3 - θ1) * (θ2 - y) := by positivity
        have h_xneg : x y < 0 := by
          rw [hx_formula y]; exact div_neg_of_neg_of_pos h_a h_b
        linarith
      · linarith
    have h_ineq : (θ2 - θ3) * (y - θ1) ≤ (θ3 - θ1) * (θ2 - y) := by
      have h_form : x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y)) := hx_formula y
      rw [h_form] at h_le
      have h_bpos : 0 < (θ3 - θ1) * (θ2 - y) := by positivity
      exact (div_le_one h_bpos).mp h_le
    have hyle : y ≤ θ3 := by nlinarith
    have h_res : 0 < chartFullLambda 0 y θ1 θ3 θ2 x ∧ chartFullLambda 0 y θ1 θ3 θ2 x ≤ 1 :=
      chartFullLambda_bound_sector0 h13 h32 hy1 hyle x
    have h_nn : 0 ≤ chartFullLambda 0 y θ1 θ3 θ2 x := h_res.1.le
    rw [abs_of_nonneg h_nn]; exact h_res.2

/-! ========================================================================
   Sector 1: x y > 1  ⟹  θ3 < y < θ2  ⟹  0 < λ/x ≤ 1
   ======================================================================== -/

private lemma sector1_bound
    {θ1 θ3 θ2 y : ℝ} {x : ℝ → ℝ}
    (h13 : θ1 < θ3) (h32 : θ3 < θ2)
    (hx_formula : ∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y)))
    (h : 1 < x y) :
    |chartFullLambda 1 y θ1 θ3 θ2 x| ≤ 1 := by
  have h_ne : θ2 - y ≠ 0 := by
    intro h_eq
    have hy : y = θ2 := by linarith
    have h_x0 : x y = 0 := by
      rw [hy, hx_formula θ2] <;> simp
    rw [h_x0] at h; linarith
  have hdenom_pos : 0 < θ2 - y := by
    by_cases h' : 0 < θ2 - y; exact h'
    have h'' : θ2 - y < 0 := by by_contra h'''; exact h_ne (by linarith)
    have h_gt2 : θ2 < y := by linarith
    have h_a : 0 < (θ2 - θ3) * (y - θ1) := by nlinarith
    have h_b : (θ3 - θ1) * (θ2 - y) < 0 := by nlinarith
    have h_xneg : x y < 0 := by
      rw [hx_formula y]; exact div_neg_of_pos_of_neg h_a h_b
    linarith
  have h_ineq : (θ3 - θ1) * (θ2 - y) < (θ2 - θ3) * (y - θ1) := by
    have h_form : x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y)) := hx_formula y
    rw [h_form] at h
    have h_bpos : 0 < (θ3 - θ1) * (θ2 - y) := by positivity
    exact (one_lt_div h_bpos).mp h
  have h_y_gt3 : θ3 < y := by nlinarith
  have h_y_lt2 : y < θ2 := by linarith
  have h_res : 0 < chartFullLambda 1 y θ1 θ3 θ2 x ∧ chartFullLambda 1 y θ1 θ3 θ2 x ≤ 1 :=
    chartFullLambda_bound_sector1 h13 h32 (by linarith) h_y_lt2 x hx_formula
  have h_nn : 0 ≤ chartFullLambda 1 y θ1 θ3 θ2 x := h_res.1.le
  rw [abs_of_nonneg h_nn]; exact h_res.2

/-! ========================================================================
   Sector 2: -1 ≤ x y < 0
   - If y < θ1: use existing lemma (0 < λ < 1)
   - If y > θ2: derive y ≥ 2θ2-θ3, then |λ| = (θ2-θ3)/(y-θ2) ≤ 1
   ======================================================================== -/

private lemma sector2_bound
    {θ1 θ3 θ2 y : ℝ} {x : ℝ → ℝ}
    (h13 : θ1 < θ3) (h32 : θ3 < θ2)
    (hx_formula : ∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y)))
    (h : -1 ≤ x y ∧ x y < 0) :
    |chartFullLambda 2 y θ1 θ3 θ2 x| ≤ 1 := by
  have hneg : x y < 0 := h.2
  have hge : -1 ≤ x y := h.1
  by_cases h_y_lt1 : y < θ1
  · -- Case y < θ1: existing lemma
    have h_res : 0 < chartFullLambda 2 y θ1 θ3 θ2 x ∧ chartFullLambda 2 y θ1 θ3 θ2 x < 1 :=
      chartFullLambda_bound_sector2_below h13 h32 h_y_lt1 x
    have h_nn : 0 ≤ chartFullLambda 2 y θ1 θ3 θ2 x := h_res.1.le
    rw [abs_of_nonneg h_nn]; exact h_res.2.le
  · -- Case ¬(y < θ1), i.e. θ1 ≤ y
    -- Since x y < 0, we must have y > θ2 (if θ1 ≤ y ≤ θ2, x y ≥ 0)
    have h_y_gt2 : θ2 < y := by
      by_cases h' : y > θ2; exact h'
      have h4 : θ1 ≤ y := by linarith
      have h5 : y ≤ θ2 := by linarith
      by_cases h6 : y = θ1
      · rw [h6] at hneg; simp [hx_formula] at hneg <;> linarith
      · by_cases h7 : y = θ2
        · rw [h7] at hneg; simp [hx_formula] at hneg <;> linarith
        · have h8 : θ1 < y := by exact lt_of_le_of_ne h4 (Ne.symm h6)
          have h9 : y < θ2 := by exact lt_of_le_of_ne h5 h7
          have h10 : 0 < x y := by
            rw [hx_formula y]
            have h_a : 0 < (θ2 - θ3) * (y - θ1) := by positivity
            have h_b : 0 < (θ3 - θ1) * (θ2 - y) := by positivity
            exact div_pos h_a h_b
          linarith
    -- Now y > θ2
    set a : ℝ := θ2 - θ3 with ha_def
    set b : ℝ := θ3 - θ1 with hb_def
    set c : ℝ := y - θ2 with hc_def
    have ha_pos : 0 < a := by linarith
    have hb_pos : 0 < b := by linarith
    have hc_pos : 0 < c := by linarith
    have hy1_pos : 0 < y - θ1 := by linarith
    have hbc_pos : 0 < b * c := by positivity
    -- x y = -a * (y-θ1) / (b * c)
    have h1 : θ2 - y = -c := by simp [hc_def] <;> ring
    have h_form2 : x y = -(a * (y - θ1)) / (b * c) := by
      rw [hx_formula y, h1]
      field_simp [hb_pos.ne', hc_pos.ne'] <;> ring
    -- From -1 ≤ x y, get a * (y-θ1) ≤ b * c
    have h_eq_neg : -(a * (y - θ1)) / (b * c) = -(a * (y - θ1) / (b * c)) := by
      field_simp [hbc_pos.ne'] <;> ring
    have h_ineq : a * (y - θ1) ≤ b * c := by
      rw [h_form2, h_eq_neg] at hge
      have h9 : a * (y - θ1) / (b * c) ≤ 1 := by linarith
      exact (div_le_one hbc_pos).mp h9
    -- y - θ1 = c + a + b
    have h_sum : y - θ1 = c + a + b := by
      simp only [ha_def, hb_def, hc_def] <;> ring
    rw [h_sum] at h_ineq
    -- a * (c + a + b) ≤ b * c  ⟹  c ≥ a
    have h_c_ge_a : c ≥ a := by nlinarith
    -- chartFullLambda 2 = a / (θ2-y) = a / (-c) = -(a/c)
    have h_lambda_eq : chartFullLambda 2 y θ1 θ3 θ2 x = -(a / c) := by
      have h_expand : chartFullLambda 2 y θ1 θ3 θ2 x = (θ2 - θ3) / (θ2 - y) := by
        simp [chartFullLambda]
      rw [h_expand]
      have h4 : (θ2 - θ3) / (θ2 - y) = -(a / c) := by
        rw [h1]
        field_simp [hc_pos.ne'] <;> ring
      exact h4
    have h_lambda_neg : chartFullLambda 2 y θ1 θ3 θ2 x < 0 := by
      rw [h_lambda_eq]; exact neg_neg_of_pos (div_pos ha_pos hc_pos)
    have h_abs : |chartFullLambda 2 y θ1 θ3 θ2 x| = a / c := by
      rw [h_lambda_eq]
      rw [abs_neg, abs_of_pos (div_pos ha_pos hc_pos)]
    rw [h_abs]
    exact (div_le_one hc_pos).mpr h_c_ge_a

/-! ========================================================================
   Sector 3: x y < -1
   - If y > θ2: use existing lemma (0 < λ/x < 1)
   - If y < θ1: derive y ≤ 2θ1-θ3, then |λ/x| = (θ3-θ1)/(θ1-y) ≤ 1
   ======================================================================== -/

private lemma sector3_bound
    {θ1 θ3 θ2 y : ℝ} {x : ℝ → ℝ}
    (h13 : θ1 < θ3) (h32 : θ3 < θ2)
    (hx_formula : ∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y)))
    (h : x y < -1) :
    |chartFullLambda 3 y θ1 θ3 θ2 x| ≤ 1 := by
  have hneg' : x y < 0 := by linarith
  by_cases h_y_gt2 : θ2 < y
  · -- Case y > θ2: existing lemma
    have h_res : 0 < chartFullLambda 3 y θ1 θ3 θ2 x ∧ chartFullLambda 3 y θ1 θ3 θ2 x < 1 :=
      chartFullLambda_bound_sector3_above h13 h32 h_y_gt2 x hx_formula
    have h_nn : 0 ≤ chartFullLambda 3 y θ1 θ3 θ2 x := h_res.1.le
    rw [abs_of_nonneg h_nn]; exact h_res.2.le
  · -- Case ¬(θ2 < y), i.e. y ≤ θ2
    -- Since x y < 0, we must have y < θ1
    have h_y_lt1 : y < θ1 := by
      by_cases h' : y < θ1; exact h'
      have h4 : θ1 ≤ y := by linarith
      have h5 : y ≤ θ2 := by linarith
      by_cases h6 : y = θ1
      · rw [h6] at hneg'; simp [hx_formula] at hneg' <;> linarith
      · by_cases h7 : y = θ2
        · rw [h7] at hneg'; simp [hx_formula] at hneg' <;> linarith
        · have h8 : θ1 < y := by exact lt_of_le_of_ne h4 (Ne.symm h6)
          have h9 : y < θ2 := by exact lt_of_le_of_ne h5 h7
          have h10 : 0 < x y := by
            rw [hx_formula y]
            have h_a : 0 < (θ2 - θ3) * (y - θ1) := by positivity
            have h_b : 0 < (θ3 - θ1) * (θ2 - y) := by positivity
            exact div_pos h_a h_b
          linarith
    -- Now y < θ1
    set a : ℝ := θ2 - θ3 with ha_def
    set b : ℝ := θ3 - θ1 with hb_def
    set c : ℝ := θ1 - y with hc_def
    have ha_pos : 0 < a := by linarith
    have hb_pos : 0 < b := by linarith
    have hc_pos : 0 < c := by linarith
    have h2y_pos : 0 < θ2 - y := by linarith
    have h_sum_pos : 0 < a + b + c := by linarith
    -- θ2 - y = a + b + c
    have h2 : θ2 - y = a + b + c := by
      simp [ha_def, hb_def, hc_def] <;> ring
    -- y - θ1 = -c
    have h1 : y - θ1 = -c := by simp [hc_def] <;> ring
    -- x y = -a * c / (b * (a + b + c))
    have h_form3 : x y = -(a * c) / (b * (a + b + c)) := by
      rw [hx_formula y, h1, h2]
      field_simp [hb_pos.ne', h_sum_pos.ne'] <;> ring
    -- From x y < -1, get a * c > b * (a + b + c)
    have h_pos : 0 < b * (a + b + c) := by positivity
    have h_eq_neg : -(a * c) / (b * (a + b + c)) = -(a * c / (b * (a + b + c))) := by
      field_simp [h_pos.ne'] <;> ring
    have h_ineq : b * (a + b + c) < a * c := by
      rw [h_form3, h_eq_neg] at h
      have h9 : 1 < (a * c) / (b * (a + b + c)) := by linarith
      exact (one_lt_div h_pos).mp h9
    -- This implies c > b
    have h_c_gt_b : c > b := by nlinarith
    have h_c_ge_b : c ≥ b := by linarith
    -- chartFullLambda 3 = (a / (a+b+c)) / x y = -b / c
    have h_lambda_eq : chartFullLambda 3 y θ1 θ3 θ2 x = -b / c := by
      have h_expand : chartFullLambda 3 y θ1 θ3 θ2 x = ((θ2 - θ3) / (θ2 - y)) / x y := by
        simp [chartFullLambda]
      rw [h_expand]
      rw [h2, h_form3]
      field_simp [ha_pos.ne', hb_pos.ne', hc_pos.ne', h_sum_pos.ne'] <;> ring
    have h_lambda_neg : chartFullLambda 3 y θ1 θ3 θ2 x < 0 := by
      rw [h_lambda_eq]
      have h_neg_b : -b < 0 := by linarith
      exact div_neg_of_neg_of_pos h_neg_b hc_pos
    have h_abs : |chartFullLambda 3 y θ1 θ3 θ2 x| = b / c := by
      rw [h_lambda_eq]
      have h_eq : (-b / c) = -(b / c) := by field_simp [hc_pos.ne'] <;> ring
      rw [h_eq]
      rw [abs_neg, abs_of_pos (div_pos hb_pos hc_pos)]
    rw [h_abs]
    exact (div_le_one hc_pos).mpr h_c_ge_b

/-! ========================================================================
   Main bridge lemma
   ======================================================================== -/

lemma chart_full_lambda_bound_bridge
    {δ : ℝ} (hδ_pos : 0 < δ)
    {θ1 θ3 θ2 : ℝ}
    (hθ1_lt_θ3 : θ1 < θ3)
    (hθ3_lt_θ2 : θ3 < θ2)
    (hθ1_in_Icc : θ1 ∈ Set.Icc (0 : ℝ) 1)
    (hθ2_in_Icc : θ2 ∈ Set.Icc (0 : ℝ) 1)
    {x : ℝ → ℝ}
    (hx_formula : ∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y))) :
    ∀ (i : Fin 4) (y : ℝ), sectorPredicate i x y →
      |chartFullLambda i y θ1 θ3 θ2 x| ≤ 1 := by
  intro i y hsec
  fin_cases i
  · exact sector0_bound hθ1_lt_θ3 hθ3_lt_θ2 hx_formula hsec
  · exact sector1_bound hθ1_lt_θ3 hθ3_lt_θ2 hx_formula hsec
  · exact sector2_bound hθ1_lt_θ3 hθ3_lt_θ2 hx_formula hsec
  · exact sector3_bound hθ1_lt_θ3 hθ3_lt_θ2 hx_formula hsec

end ProductLikeIncidence.ProductReduction
