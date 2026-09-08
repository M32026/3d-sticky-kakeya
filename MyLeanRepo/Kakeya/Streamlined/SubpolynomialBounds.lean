import MyLeanRepo.Kakeya.Streamlined.UniformScaleGrid
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Subpolynomial bounds for the paper scale grid

Core estimate: `(log y)^2 = o(y)`, and consequences for `M = uniformScaleSteps δ`.
-/

noncomputable section

namespace Kakeya.Streamlined

/--
For any real `C` and `ε > 0`, there exists `y₀ > 0` such that for all `y ≥ y₀`:
`(Real.log y + 1) * (max C 0 + Real.log y) ≤ ε * y`.
-/
lemma log_sq_linear_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ y₀ : ℝ, 0 < y₀ ∧ ∀ y : ℝ, y ≥ y₀ →
      (Real.log y + 1) * (max C 0 + Real.log y) ≤ ε * y := by
  let C' : ℝ := max C 1
  have hC'_ge_one : 1 ≤ C' := le_max_right _ _
  have hC1 : max C 0 ≤ C' := by
    by_cases h : C ≥ 0
    · have h2 : max C 0 = C := by simp [h]
      rw [h2]; simp [C'] <;> linarith
    · have h2 : max C 0 = 0 := by simp [h] <;> linarith
      rw [h2]; linarith [hC'_ge_one]
  have hε3 : 0 < ε / 3 := by positivity
  have hC11_pos : 0 < C' + 1 := by linarith
  have h_asym2 : (fun y : ℝ => (Real.log y) ^ (2 : ℝ)) =o[Filter.atTop] (fun y : ℝ => y ^ (1 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop (s := 1) 2 (by norm_num)
  have h_asym1 : (fun y : ℝ => Real.log y) =o[Filter.atTop] (fun y : ℝ => y ^ (1 : ℝ)) :=
    isLittleO_log_rpow_atTop (r := 1) (by norm_num)
  have h_eventually1 : ∀ᶠ (y : ℝ) in Filter.atTop, 1 ≤ y :=
    Filter.eventually_ge_atTop 1
  have h_eventually2 : ∀ᶠ (y : ℝ) in Filter.atTop, (Real.log y) ^ 2 ≤ (ε / 3) * y := by
    have h := (Asymptotics.isLittleO_iff.mp h_asym2) hε3
    filter_upwards [h_eventually1, h] with y hy1 hy
    have hpos : 0 ≤ Real.log y := Real.log_nonneg hy1
    have h_eq : (Real.log y) ^ (2 : ℝ) = (Real.log y) ^ 2 := by norm_cast
    have h_norm1 : ‖(Real.log y) ^ (2 : ℝ)‖ = (Real.log y) ^ 2 := by
      rw [h_eq, Real.norm_eq_abs, abs_of_nonneg] <;> positivity
    have h_norm2 : ‖(y ^ (1 : ℝ))‖ = y := by
      have h_eq2 : y ^ (1 : ℝ) = y := by simp
      rw [h_eq2, Real.norm_eq_abs, abs_of_nonneg] <;> linarith
    rw [h_norm1, h_norm2] at hy; exact hy
  have h_eventually3 : ∀ᶠ (y : ℝ) in Filter.atTop, (C' + 1) * Real.log y ≤ (ε / 3) * y := by
    have hε' : 0 < (ε / 3) / (C' + 1) := by positivity
    have h := (Asymptotics.isLittleO_iff.mp h_asym1) hε'
    filter_upwards [h_eventually1, h] with y hy1 hy
    have hpos : 0 ≤ Real.log y := Real.log_nonneg hy1
    have h_norm1 : ‖Real.log y‖ = Real.log y := by
      rw [Real.norm_eq_abs, abs_of_nonneg] <;> positivity
    have h_norm2 : ‖(y ^ (1 : ℝ))‖ = y := by
      have h_eq2 : y ^ (1 : ℝ) = y := by simp
      rw [h_eq2, Real.norm_eq_abs, abs_of_nonneg] <;> linarith
    rw [h_norm1, h_norm2] at hy
    have h' : Real.log y ≤ ((ε / 3) / (C' + 1)) * y := hy
    have h : (C' + 1) * Real.log y ≤ (C' + 1) * (((ε / 3) / (C' + 1)) * y) := by gcongr
    have h2 : (C' + 1) * (((ε / 3) / (C' + 1)) * y) = (ε / 3) * y := by
      field_simp [hC11_pos.ne'] <;> ring
    rw [h2] at h; exact h
  have h_eventually4 : ∀ᶠ (y : ℝ) in Filter.atTop, C' ≤ (ε / 3) * y := by
    filter_upwards [Filter.eventually_ge_atTop (C' / (ε / 3))] with y hy
    have h : C' ≤ (ε / 3) * y := by
      calc C'
        = (ε / 3) * (C' / (ε / 3)) := by field_simp [hε3.ne'] <;> ring
      _ ≤ (ε / 3) * y := by gcongr
    exact h
  have h4 : ∀ᶠ (y : ℝ) in Filter.atTop,
      (Real.log y) ^ 2 + (C' + 1) * Real.log y + C' ≤ ε * y := by
    filter_upwards [h_eventually2, h_eventually3, h_eventually4] with y hy2 hy3 hy4
    have h : (Real.log y) ^ 2 + (C' + 1) * Real.log y + C' ≤
        (ε / 3) * y + (ε / 3) * y + (ε / 3) * y := by gcongr <;> linarith
    have h5 : (ε / 3) * y + (ε / 3) * y + (ε / 3) * y = ε * y := by ring
    rw [h5] at h; exact h
  rcases Filter.eventually_atTop.mp h4 with ⟨y₁, h⟩
  let y₀ : ℝ := max y₁ 1
  have hy₀_pos : 0 < y₀ := by positivity
  refine ⟨y₀, hy₀_pos, ?_⟩
  intro y hy
  have h_y1 : y ≥ y₁ := by
    have h6 : y ≥ y₀ := hy
    have h7 : y₀ ≥ y₁ := le_max_left _ _
    linarith
  have h5 : (Real.log y) ^ 2 + (C' + 1) * Real.log y + C' ≤ ε * y := h y h_y1
  have h_y_ge_one : 1 ≤ y := by
    have h6 : y ≥ y₀ := hy
    have h7 : y₀ ≥ 1 := le_max_right _ _
    linarith
  have h8 : 0 ≤ Real.log y + 1 := by linarith [Real.log_nonneg h_y_ge_one]
  have h9 : max C 0 + Real.log y ≤ C' + Real.log y := by linarith [hC1]
  have h7 : (Real.log y + 1) * (max C 0 + Real.log y) ≤
      (Real.log y + 1) * (C' + Real.log y) :=
    mul_le_mul_of_nonneg_left h9 h8
  have h10 : (Real.log y + 1) * (C' + Real.log y) =
      (Real.log y) ^ 2 + (C' + 1) * Real.log y + C' := by ring
  rw [h10] at h7
  exact h7.trans h5

/--
For any `C > 0` and `ε > 0`, there exists `x₀ > 1` such that for all `x ≥ x₀`:
`(C * Real.log x) ^ (Real.log (Real.log x) + 1) ≤ x ^ ε`.
-/
lemma subpoly_log_pow_loglog (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x ≥ x₀ →
      (C * Real.log x) ^ (Real.log (Real.log x) + 1) ≤ x ^ ε := by
  let D : ℝ := Real.log C
  have h_main := log_sq_linear_bound D ε hε
  rcases h_main with ⟨y₀, _hy₀_pos, h_bound⟩
  let y₁ : ℝ := max y₀ (max (Real.exp 1) (1 / C))
  let x₀ : ℝ := Real.exp y₁
  have hx₀_gt_one : 1 < x₀ := by
    have h₁ : 0 < y₁ := by positivity
    have h₂ : Real.exp y₁ > 1 := by
      have h₂₁ : 0 < y₁ := by positivity
      have h₂₂ : Real.exp y₁ > Real.exp 0 := Real.exp_strictMono (by linarith)
      simpa using h₂₂
    exact h₂
  have h_log_x_ge : ∀ x ≥ x₀, Real.log x ≥ y₁ := by
    intro x hx
    have h₃ : Real.log x ≥ Real.log x₀ := Real.log_le_log (by positivity) hx
    have h₄ : Real.log x₀ = y₁ := by simp [x₀, Real.log_exp]
    rw [h₄] at h₃; exact h₃
  refine ⟨x₀, hx₀_gt_one, ?_⟩
  intro x hx
  set y : ℝ := Real.log x with hy_def
  have hy_y0 : y ≥ y₀ := by
    have h : y₁ ≥ y₀ := le_max_left _ _
    have h' : y ≥ y₁ := h_log_x_ge x hx
    linarith
  have h_y_pos : 0 < y := by
    have h : y ≥ y₁ := h_log_x_ge x hx
    have h2 : y₁ ≥ Real.exp 1 := by
      have h3 : y₁ ≥ max (Real.exp 1) (1 / C) := le_max_right _ _
      have h4 : max (Real.exp 1) (1 / C) ≥ Real.exp 1 := le_max_left _ _
      linarith
    linarith [Real.exp_pos 1]
  have h_base_pos : 0 < C * y := by positivity
  have h_base_ge_one : 1 ≤ C * y := by
    have h1 : y ≥ 1 / C := by
      have h2 : y₁ ≥ max (Real.exp 1) (1 / C) := le_max_right _ _
      have h3 : max (Real.exp 1) (1 / C) ≥ 1 / C := le_max_right _ _
      have h4 : y ≥ y₁ := h_log_x_ge x hx
      linarith
    have h₄ : 0 < C := hC
    have h₅ : C * y ≥ C * (1 / C) := by gcongr
    have h₆ : C * (1 / C) = 1 := by field_simp [h₄.ne'] <;> ring
    rw [h₆] at h₅; exact h₅
  have h_key : (Real.log y + 1) * Real.log (C * y) ≤ ε * y := by
    have h₅ : Real.log (C * y) = Real.log C + Real.log y := by
      rw [Real.log_mul (by linarith) (by linarith)]
    rw [h₅]
    have h₆ : Real.log C ≤ max D 0 := by
      simp [D] <;> omega
    have h₇ : Real.log C + Real.log y ≤ max D 0 + Real.log y := by linarith
    have h_y_ge_one : 1 ≤ y := by
      have h : y ≥ y₁ := h_log_x_ge x hx
      have h2 : y₁ ≥ Real.exp 1 := by
        have h3 : y₁ ≥ max (Real.exp 1) (1 / C) := le_max_right _ _
        have h4 : max (Real.exp 1) (1 / C) ≥ Real.exp 1 := le_max_left _ _
        linarith
      have h5 : Real.exp 1 > 1 := by
        have h6 : Real.exp 1 > Real.exp 0 := Real.exp_strictMono (by norm_num)
        simpa using h6
      linarith
    have h₈ : 0 ≤ Real.log y + 1 := by linarith [Real.log_nonneg h_y_ge_one]
    have h₉ : (Real.log y + 1) * (Real.log C + Real.log y) ≤
        (Real.log y + 1) * (max D 0 + Real.log y) :=
      mul_le_mul_of_nonneg_left h₇ h₈
    exact h₉.trans (h_bound y hy_y0)
  have h_goal : Real.log ((C * y) ^ (Real.log y + 1)) ≤ Real.log (x ^ ε) := by
    have h₆ : Real.log ((C * y) ^ (Real.log y + 1)) =
        (Real.log y + 1) * Real.log (C * y) := by
      rw [Real.log_rpow (by positivity)] <;> ring
    have h₇ : Real.log (x ^ ε) = ε * Real.log x := by
      rw [Real.log_rpow (by linarith)] <;> ring
    rw [h₆, h₇, hy_def]
    exact h_key
  have h₈ : 0 < (C * y) ^ (Real.log y + 1) := Real.rpow_pos_of_pos h_base_pos _
  have h₉ : 0 < x ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  exact (Real.log_le_log_iff h₈ h₉).mp h_goal

/-! ### Bounds on M = uniformScaleSteps δ -/

/--
For sufficiently small `δ`, `(uniformScaleSteps δ : ℝ) ≤ Real.log (Real.log (1/δ)) + 1`.
-/
lemma M_le_log_log (δ : ℝ) (hδ_pos : 0 < δ)
    (hδ_small : δ < Real.exp (-Real.exp 1)) :
    (uniformScaleSteps δ : ℝ) ≤ Real.log (Real.log (1 / δ)) + 1 := by
  have h_exp_neg : 0 < Real.exp (-Real.exp 1) := by positivity
  have h1 : 1 / δ > Real.exp (Real.exp 1) := by
    have h2 : δ < Real.exp (-Real.exp 1) := hδ_small
    have h3 : 1 / δ > 1 / Real.exp (-Real.exp 1) := one_div_lt_one_div_of_lt hδ_pos h2
    have h4 : 1 / Real.exp (-Real.exp 1) = Real.exp (Real.exp 1) := by
      have h5 : Real.exp (-Real.exp 1) = (Real.exp (Real.exp 1))⁻¹ := by rw [Real.exp_neg]
      rw [h5]
      field_simp
    rw [h4] at h3; exact h3
  have h6 : 1 / δ > 1 := by
    have h7 : Real.exp (Real.exp 1) > 1 := by
      have h8 : Real.exp (Real.exp 1) > Real.exp 0 := Real.exp_strictMono (by positivity)
      simpa using h8
    linarith
  have h9 : Real.log (1 / δ) > 1 := by
    have h10 : Real.log (1 / δ) > Real.log (Real.exp (Real.exp 1)) :=
      Real.log_lt_log (by positivity) h1
    have h11 : Real.log (Real.exp (Real.exp 1)) = Real.exp 1 := by simp
    rw [h11] at h10
    have h12 : Real.exp 1 > 1 := by
      have h13 : Real.exp 1 > Real.exp 0 := Real.exp_strictMono (by norm_num)
      simpa using h13
    linarith
  have h13 : Real.log (Real.log (1 / δ)) > 1 := by
    have h14 : Real.log (1 / δ) > Real.exp 1 := by
      have h15 : Real.log (1 / δ) > Real.log (Real.exp (Real.exp 1)) :=
        Real.log_lt_log (by positivity) h1
      have h16 : Real.log (Real.exp (Real.exp 1)) = Real.exp 1 := by simp
      rw [h16] at h15; exact h15
    have h_pos_log : 0 < Real.log (1 / δ) := by
      have h : Real.log (1 / δ) > 1 := h9
      linarith
    have h17 : Real.log (Real.log (1 / δ)) > Real.log (Real.exp 1) :=
      Real.log_lt_log (by positivity) h14
    have h18 : Real.log (Real.exp 1) = 1 := by simp
    rw [h18] at h17; exact h17
  have h19 : max 1 (Real.log (1 / δ)) = Real.log (1 / δ) := by
    rw [max_eq_right] <;> linarith
  have h20 : max 1 (Real.log (max 1 (Real.log (1 / δ)))) =
      Real.log (Real.log (1 / δ)) := by
    rw [h19]
    rw [max_eq_right] <;> linarith
  have h21 : 1 ≤ Real.log (Real.log (1 / δ)) := by linarith
  have h22 : Real.log (max 1 (Real.log (1 / δ))) = Real.log (Real.log (1 / δ)) := by
    rw [h19]
  have h23 : Nat.ceil (Real.log (max 1 (Real.log (1 / δ)))) =
      Nat.ceil (Real.log (Real.log (1 / δ))) := by
    rw [h22]
  have h24 : (1 : ℝ) ≤ (Nat.ceil (Real.log (Real.log (1 / δ))) : ℝ) := by
    have h25 : (1 : ℝ) ≤ Real.log (Real.log (1 / δ)) := h21
    have h26 : Real.log (Real.log (1 / δ)) ≤ (Nat.ceil (Real.log (Real.log (1 / δ))) : ℝ) :=
      Nat.le_ceil _
    linarith
  have h24' : (1 : ℕ) ≤ Nat.ceil (Real.log (max 1 (Real.log (1 / δ)))) := by
    rw [h23]
    exact_mod_cast h24
  have h27 : max 1 (Nat.ceil (Real.log (max 1 (Real.log (1 / δ))))) =
      Nat.ceil (Real.log (max 1 (Real.log (1 / δ)))) := by
    rw [max_eq_right h24']
  have h28 : uniformScaleSteps δ = Nat.ceil (Real.log (Real.log (1 / δ))) := by
    rw [uniformScaleSteps, h27, h23]
  rw [h28]
  have h29 : (Nat.ceil (Real.log (Real.log (1 / δ))) : ℝ) ≤
      Real.log (Real.log (1 / δ)) + 1 := by
    have h30 : (Nat.ceil (Real.log (Real.log (1 / δ))) : ℝ) <
        Real.log (Real.log (1 / δ)) + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    linarith
  exact h29

/--
Helper: for any `C > 0` and `ε > 0`, `C * Real.log x ≤ x^ε` for sufficiently large `x`.
-/
lemma const_mul_log_le_rpow (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x ≥ x₀ → C * Real.log x ≤ x ^ ε := by
  set K : ℝ := 2 * C / ε with hK_def
  have hK_pos : 0 < K := by positivity
  have hε2 : 0 < ε / 2 := by positivity
  let x₁ : ℝ := K ^ (2 / ε)
  let x₀ : ℝ := max (Real.exp 1) x₁
  have hx₀_gt_one : 1 < x₀ := by
    have h : x₀ ≥ Real.exp 1 := le_max_left _ _
    have h2 : Real.exp 1 > 1 := by
      have h3 : Real.exp 1 > Real.exp 0 := Real.exp_strictMono (by norm_num)
      simpa using h3
    linarith
  have h_x1_nonneg : 0 ≤ x₁ := by positivity
  refine ⟨x₀, hx₀_gt_one, ?_⟩
  intro x hx
  have h_x_ge_two : Real.exp 1 ≤ x := by
    have h : x ≥ x₀ := hx
    have h2 : x₀ ≥ Real.exp 1 := le_max_left _ _
    linarith
  have h_x_ge_x1 : x ≥ x₁ := by
    have h : x ≥ x₀ := hx
    have h2 : x₀ ≥ x₁ := le_max_right _ _
    linarith
  have h6 : K ≤ x ^ (ε / 2) := by
    have h7 : x₁ ^ (ε / 2) ≤ x ^ (ε / 2) :=
      Real.rpow_le_rpow h_x1_nonneg h_x_ge_x1 (by positivity)
    have h8 : x₁ ^ (ε / 2) = K := by
      have h81 : x₁ = K ^ (2 / ε) := by rfl
      have h_pos : 0 ≤ K := by positivity
      have h : (K ^ (2 / ε)) ^ (ε / 2) = K := by
        have h_mul : (K ^ (2 / ε)) ^ (ε / 2) = K ^ ((2 / ε) * (ε / 2)) := by
          exact (Real.rpow_mul h_pos (2 / ε) (ε / 2)).symm
        rw [h_mul]
        have h_eq : (2 / ε) * (ε / 2) = 1 := by field_simp [hε.ne'] <;> ring
        rw [h_eq]
        simp
      rw [h81]
      exact h
    rw [h8] at h7
    exact h7
  have h9 : Real.log x ≤ x ^ (ε / 2) / (ε / 2) := Real.log_le_rpow_div (by linarith) hε2
  have h10 : C * Real.log x ≤ K * x ^ (ε / 2) := by
    have h11 : C * Real.log x ≤ C * (x ^ (ε / 2) / (ε / 2)) := by gcongr
    have h12 : C * (x ^ (ε / 2) / (ε / 2)) = K * x ^ (ε / 2) := by
      simp [hK_def] <;> ring
    rw [h12] at h11
    exact h11
  have h13 : K * x ^ (ε / 2) ≤ x ^ (ε / 2) * x ^ (ε / 2) := by
    have h_x_pos : 0 < x := by linarith [h_x_ge_two]
    have h14 : 0 ≤ x ^ (ε / 2) := Real.rpow_nonneg (by linarith) _
    have h15 : K ≤ x ^ (ε / 2) := h6
    exact mul_le_mul_of_nonneg_right h15 h14
  have h15 : x ^ (ε / 2) * x ^ (ε / 2) = x ^ ε := by
    rw [← Real.rpow_add (by linarith)] <;> ring
  calc
    C * Real.log x ≤ K * x ^ (ε / 2) := h10
    _ ≤ x ^ (ε / 2) * x ^ (ε / 2) := h13
    _ = x ^ ε := h15

/--
For any `ε > 0`, for sufficiently small `δ`,
`2^(uniformScaleSteps δ) ≤ δ^(-ε) = (1/δ)^ε`.
-/
lemma two_pow_M_subpoly (ε : ℝ) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      (2 : ℝ) ^ (uniformScaleSteps δ) ≤ (1 / δ) ^ ε := by
  rcases const_mul_log_le_rpow 2 ε (by norm_num) hε with ⟨x₀, hx₀_gt_one, h_log_bound⟩
  let δ₁ : ℝ := Real.exp (-Real.exp 1)
  let δ₀ : ℝ := min δ₁ (1 / x₀)
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro δ hδ_pos hδ_lt
  have hδ_small : δ < δ₁ := by
    have h : δ < δ₀ := hδ_lt
    have h2 : δ₀ ≤ δ₁ := min_le_left _ _
    linarith
  have h_x_ge : 1 / δ ≥ x₀ := by
    have h1 : δ < 1 / x₀ := by
      have h2 : δ < δ₀ := hδ_lt
      have h3 : δ₀ ≤ 1 / x₀ := min_le_right _ _
      linarith
    have h4 : 0 < 1 / x₀ := by positivity
    have h5 : 1 / δ > 1 / (1 / x₀) := one_div_lt_one_div_of_lt hδ_pos h1
    have h6 : 1 / (1 / x₀) = x₀ := by
      field_simp [hx₀_gt_one.ne']
    rw [h6] at h5; linarith
  set y : ℝ := Real.log (1 / δ) with hy_def
  have hM_le : (uniformScaleSteps δ : ℝ) ≤ Real.log y + 1 := by
    simpa [hy_def] using M_le_log_log δ hδ_pos hδ_small
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_log2_lt_one : Real.log 2 < 1 := by
    have h : (2 : ℝ) < Real.exp 1 := by
      have h2 : (1 : ℝ) + 1 < Real.exp 1 := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
      norm_num at h2 ⊢ <;> exact h2
    have h3 : Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by positivity) h
    have h4 : Real.log (Real.exp 1) = 1 := by simp
    rw [h4] at h3; exact h3
  have h_y_ge_one : 1 ≤ y := by
    have h7 : 1 / δ ≥ Real.exp 1 := by
      have h71 : δ < δ₁ := hδ_small
      have h72 : 1 / δ > 1 / δ₁ := one_div_lt_one_div_of_lt hδ_pos h71
      have h73 : 1 / δ₁ = Real.exp (Real.exp 1) := by
        simp [δ₁, Real.exp_neg] <;> field_simp
      rw [h73] at h72
      have h74 : Real.exp (Real.exp 1) > Real.exp 1 := by
        have h75 : (1 : ℝ) < Real.exp 1 := by
          have h76 : (1 : ℝ) + 1 < Real.exp 1 := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
          norm_num at h76 ⊢ <;> exact h76
        exact Real.exp_strictMono h75
      linarith
    have h8 : Real.log (1 / δ) ≥ Real.log (Real.exp 1) := Real.log_le_log (by positivity) h7
    have h9 : Real.log (Real.exp 1) = 1 := by simp
    have h10 : y = Real.log (1 / δ) := by simp [hy_def]
    rw [h10]
    linarith
  have h1 : (2 : ℝ) ^ (uniformScaleSteps δ) ≤ (2 : ℝ) ^ ((uniformScaleSteps δ : ℝ)) := by
    norm_cast
  have h2 : (2 : ℝ) ^ ((uniformScaleSteps δ : ℝ)) ≤ (2 : ℝ) ^ (Real.log y + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hM_le
  have h3 : (2 : ℝ) ^ (Real.log y + 1) = 2 * y ^ (Real.log 2) := by
    have h4 : (2 : ℝ) ^ (Real.log y + 1) = (2 : ℝ) * (2 : ℝ) ^ (Real.log y) := by
      rw [Real.rpow_add (by norm_num)] <;> ring
    rw [h4]
    have h5 : (2 : ℝ) ^ (Real.log y) = Real.exp (Real.log 2 * Real.log y) := by
      rw [Real.rpow_def_of_pos (by positivity)]
    have h6 : y ^ (Real.log 2) = Real.exp (Real.log y * Real.log 2) := by
      rw [Real.rpow_def_of_pos (by linarith [h_y_ge_one])]
    rw [h5, h6]
    have h7 : Real.log 2 * Real.log y = Real.log y * Real.log 2 := by ring
    rw [h7] <;> ring
  have h4 : y ^ (Real.log 2) ≤ y := by
    have h5 : Real.log 2 ≤ (1 : ℝ) := by linarith [h_log2_lt_one]
    have h6 : y ^ (Real.log 2) ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h_y_ge_one h5
    have h7 : y ^ (1 : ℝ) = y := by simp
    rw [h7] at h6
    exact h6
  have h5 : 2 * y ^ (Real.log 2) ≤ 2 * y := by gcongr
  have h6 : 2 * y ≤ (1 / δ) ^ ε := by
    have h7 : y = Real.log (1 / δ) := by simp [hy_def]
    rw [h7]
    exact h_log_bound (1 / δ) h_x_ge
  calc
    (2 : ℝ) ^ (uniformScaleSteps δ)
      ≤ (2 : ℝ) ^ ((uniformScaleSteps δ : ℝ)) := h1
    _ ≤ (2 : ℝ) ^ (Real.log y + 1) := h2
    _ = 2 * y ^ (Real.log 2) := h3
    _ ≤ 2 * y := h5
    _ ≤ (1 / δ) ^ ε := h6

/--
If `F.card ≤ (1/δ)^C`, then for sufficiently small `δ`,
`(Nat.log 2 F.card + 1)^(uniformScaleSteps δ) ≤ δ^(-ε) = (1/δ)^ε`.
-/
lemma log_pow_M_subpoly (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (δ : ℝ), 0 < δ → δ < δ₀ →
      ∀ (n : ℕ), (n : ℝ) ≤ (1 / δ) ^ C →
        ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ (uniformScaleSteps δ) ≤ (1 / δ) ^ ε := by
  rcases subpoly_log_pow_loglog (C / Real.log 2 + 1) ε (by positivity) hε with
    ⟨x₀, hx₀_gt_one, h_bound⟩
  let δ₁ : ℝ := Real.exp (-Real.exp 1)
  let δ₀ : ℝ := min δ₁ (1 / x₀)
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro δ hδ_pos hδ_lt n hn
  have hδ'_small : δ < δ₁ := by
    have h : δ < δ₀ := hδ_lt
    have h2 : δ₀ ≤ δ₁ := min_le_left _ _
    linarith
  have h_x_ge : 1 / δ ≥ x₀ := by
    have h1 : δ < 1 / x₀ := by
      have h2 : δ < δ₀ := hδ_lt
      have h3 : δ₀ ≤ 1 / x₀ := min_le_right _ _
      linarith
    have h4 : 0 < 1 / x₀ := by positivity
    have h5 : 1 / δ > 1 / (1 / x₀) := one_div_lt_one_div_of_lt hδ_pos h1
    have h6 : 1 / (1 / x₀) = x₀ := by
      field_simp [hx₀_gt_one.ne']
    rw [h6] at h5; linarith
  by_cases h_n0 : n = 0
  · -- n = 0 case: (Nat.log 2 0 + 1)^M = 1^M = 1 ≤ (1/δ)^ε
    have h_goal : ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ (uniformScaleSteps δ) ≤ (1 / δ) ^ ε := by
      rw [h_n0]
      have h1 : Nat.log 2 0 = 0 := by simp
      rw [h1]
      have h2 : ((1 : ℕ) : ℝ) ^ (uniformScaleSteps δ) = 1 := by simp
      rw [h2]
      have h4 : 1 < 1 / δ := by linarith [hx₀_gt_one]
      have h5 : (1 : ℝ) ≤ (1 / δ) ^ ε := by
        have h6 : 1 ≤ 1 / δ := by linarith
        have h7 : (1 / δ) ^ ε ≥ 1 ^ ε := by gcongr
        simpa using h7
      exact h5
    exact h_goal
  · -- n > 0 case
    have h_n_pos : 0 < n := Nat.pos_of_ne_zero h_n0
    set x : ℝ := 1 / δ with hx_def
    have hx_ge : x ≥ x₀ := h_x_ge
    have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h_log_x_gt_one : 1 < Real.log x := by
      have h1 : x > Real.exp (Real.exp 1) := by
        have h2 : δ < δ₁ := hδ'_small
        have h3 : 1 / δ > 1 / δ₁ := one_div_lt_one_div_of_lt hδ_pos h2
        have h4 : 1 / δ₁ = Real.exp (Real.exp 1) := by
          simp [δ₁, Real.exp_neg] <;> field_simp
        rw [h4] at h3
        simpa [hx_def] using h3
      have h5 : Real.log x > Real.log (Real.exp (Real.exp 1)) := Real.log_lt_log (by positivity) h1
      have h6 : Real.log (Real.exp (Real.exp 1)) = Real.exp 1 := by simp
      rw [h6] at h5
      have h7 : Real.exp 1 > 1 := by
        have h8 : Real.exp 1 > Real.exp 0 := Real.exp_strictMono (by norm_num)
        simpa using h8
      linarith
    have h_log_log_x_nonneg : 0 ≤ Real.log (Real.log x) :=
      Real.log_nonneg (by linarith)
    have h_log_nat : (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
      have h_pow : (2 : ℝ) ^ (Nat.log 2 n) ≤ (n : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have h1 : Real.log ((2 : ℝ) ^ (Nat.log 2 n)) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by positivity) h_pow
      have h2 : Real.log ((2 : ℝ) ^ (Nat.log 2 n)) =
          (Nat.log 2 n : ℝ) * Real.log 2 := by
        rw [Real.log_pow] <;> norm_num
      rw [h2] at h1
      have h3 : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := h1
      have h41 : ((Nat.log 2 n : ℝ) * Real.log 2) / Real.log 2 = (Nat.log 2 n : ℝ) := by
        field_simp [h_log2_pos.ne']
      have h4 : (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
        calc (Nat.log 2 n : ℝ)
          = ((Nat.log 2 n : ℝ) * Real.log 2) / Real.log 2 := h41.symm
        _ ≤ Real.log (n : ℝ) / Real.log 2 := by gcongr
      exact h4
    have h_log_n : Real.log (n : ℝ) ≤ C * Real.log x := by
      have h5 : (n : ℝ) ≤ x ^ C := by simpa [hx_def] using hn
      have h6 : Real.log (n : ℝ) ≤ Real.log (x ^ C) := Real.log_le_log (by positivity) h5
      have h7 : Real.log (x ^ C) = C * Real.log x := by
        rw [Real.log_rpow (by linarith)] <;> ring
      rw [h7] at h6; exact h6
    let C' : ℝ := C / Real.log 2 + 1
    have h_x_ge_one : 1 ≤ x := by linarith [hx₀_gt_one]
    have h_base : (Nat.log 2 n + 1 : ℝ) ≤ C' * Real.log x := by
      have h8 : (Nat.log 2 n + 1 : ℝ) = (Nat.log 2 n : ℝ) + 1 := by simp
      rw [h8]
      have h9 : (Nat.log 2 n : ℝ) ≤ (C / Real.log 2) * Real.log x := by
        calc (Nat.log 2 n : ℝ)
          ≤ Real.log (n : ℝ) / Real.log 2 := h_log_nat
        _ ≤ (C * Real.log x) / Real.log 2 := by gcongr
        _ = (C / Real.log 2) * Real.log x := by ring
      have h10 : (1 : ℝ) ≤ 1 * Real.log x := by
        have h11 : 1 ≤ Real.log x := by linarith [h_log_x_gt_one]
        simpa using h11
      linarith
    have hM_le : (uniformScaleSteps δ : ℝ) ≤ Real.log (Real.log x) + 1 := by
      simpa [hx_def] using M_le_log_log δ hδ_pos hδ'_small
    have h_main : (C' * Real.log x) ^ (Real.log (Real.log x) + 1) ≤ x ^ ε :=
      h_bound x hx_ge
    have h_base_ge_one : 1 ≤ (Nat.log 2 n + 1 : ℝ) := by
      have h : 1 ≤ Nat.log 2 n + 1 := by simp
      exact_mod_cast h
    have h_exp_nonneg : 0 ≤ Real.log (Real.log x) + 1 := by linarith [h_log_log_x_nonneg]
    have h11 : ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ (uniformScaleSteps δ) ≤
        ((Nat.log 2 n + 1 : ℝ)) ^ (Real.log (Real.log x) + 1) := by
      have h12 : ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ (uniformScaleSteps δ) =
          ((Nat.log 2 n + 1 : ℝ)) ^ ((uniformScaleSteps δ : ℝ)) := by norm_cast
      rw [h12]
      exact Real.rpow_le_rpow_of_exponent_le h_base_ge_one hM_le
    have h13 : ((Nat.log 2 n + 1 : ℝ)) ^ (Real.log (Real.log x) + 1) ≤
        (C' * Real.log x) ^ (Real.log (Real.log x) + 1) := by
      have h_pos1 : 0 ≤ (Nat.log 2 n + 1 : ℝ) := by positivity
      exact Real.rpow_le_rpow h_pos1 h_base h_exp_nonneg
    have h14 : x ^ ε = (1 / δ) ^ ε := by simp [hx_def]
    calc
      ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ (uniformScaleSteps δ)
        ≤ ((Nat.log 2 n + 1 : ℝ)) ^ (Real.log (Real.log x) + 1) := h11
      _ ≤ (C' * Real.log x) ^ (Real.log (Real.log x) + 1) := h13
      _ ≤ x ^ ε := h_main
      _ = (1 / δ) ^ ε := h14

end Kakeya.Streamlined
