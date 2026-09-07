module

public import MyLeanRepo.OSWPrelude
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

namespace Vendored.NumberTheory.Analytic.Sieve

open Filter Finset Nat BigOperators Topology

attribute [local instance] Classical.propDecidable

/-!
# Asymptotic inequalities for the Selberg sieve parameter choice

General principle: any power of log x grows slower than any positive power of x.
All lemmas below follow from `isLittleO_log_rpow_rpow_atTop` in Mathlib.
-/

/-- General asymptotic lemma: for any real exponents r > 0, s > 0,
    there exists x0 such that for all x ≥ x0, (log x)^r ≤ x^s.
    Proof: (log x)^r = o(x^s) as x → ∞ by `isLittleO_log_rpow_rpow_atTop`,
    so for c = 1, eventually |(log x)^r| ≤ |x^s|, which gives the result. -/
lemma general_log_pow_le_rpow (r s : ℝ) (_hr : 0 < r) (hs : 0 < s) :
    ∃ (x0 : ℝ), 1 < x0 ∧ ∀ (x : ℝ), x0 ≤ x → (Real.log x)^r ≤ x^s := by
  have h_littleO : (fun x : ℝ => (Real.log x)^r) =o[Filter.atTop] fun x : ℝ => x^s :=
    isLittleO_log_rpow_rpow_atTop r hs
  have h_eventually : ∀ᶠ (x : ℝ) in Filter.atTop, ‖(Real.log x)^r‖ ≤ ‖x^s‖ :=
    h_littleO.eventuallyLE
  have h_eventually' : ∀ᶠ (x : ℝ) in Filter.atTop, |(Real.log x)^r| ≤ |x^s| := by
    simpa [Real.norm_eq_abs] using h_eventually
  rcases Filter.eventually_atTop.mp h_eventually' with ⟨x1, hx1⟩
  let x0 := max x1 (Real.exp 1)
  have h_x0_gt_one : 1 < x0 := by
    have h1 : Real.exp 1 > 1 := by
      have h2 : Real.exp 1 > Real.exp 0 := Real.exp_strictMono (by norm_num)
      simp
    have h3 : x0 ≥ Real.exp 1 := le_max_right _ _
    linarith
  have h_main : ∀ (x : ℝ), x0 ≤ x → (Real.log x)^r ≤ x^s := by
    intro x hx
    have h_x_ge_x1 : x1 ≤ x := by
      have h4 : x0 ≥ x1 := le_max_left _ _
      linarith
    have h5 : |(Real.log x)^r| ≤ |x^s| := hx1 x h_x_ge_x1
    have h_x_gt_one : 1 < x := by
      have h6 : x0 ≥ Real.exp 1 := le_max_right _ _
      have h7 : Real.exp 1 > 1 := by
        have h8 : Real.exp 1 > Real.exp 0 := Real.exp_strictMono (by norm_num)
        simp
      linarith
    have h_log_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have h_log_r_pos : 0 < (Real.log x)^r := by
      apply Real.rpow_pos_of_pos h_log_pos
    have h_xs_pos : 0 < x^s := by
      apply Real.rpow_pos_of_pos
      linarith
    have h_abs1 : |(Real.log x)^r| = (Real.log x)^r := by
      rw [abs_of_pos h_log_r_pos]
    have h_abs2 : |x^s| = x^s := by
      rw [abs_of_pos h_xs_pos]
    rw [h_abs1, h_abs2] at h5
    exact h5
  exact ⟨x0, h_x0_gt_one, h_main⟩

/-- Asymptotic inequality 1: y^(1/4) ≤ y / (log y)^2 for sufficiently large y. -/
lemma y_one_fourth_le_y_over_log_sq :
    ∃ x0 : ℕ, 1000 ≤ x0 ∧ ∀ y : ℕ, x0 ≤ y →
      (y : ℝ)^(1 / 4 : ℝ) ≤ (y : ℝ) / (Real.log (y : ℝ))^2 := by
  rcases general_log_pow_le_rpow 2 (3 / 4 : ℝ) (by norm_num) (by norm_num) with ⟨x0_real, hx0_gt_one, h_bound⟩
  let x0 : ℕ := Nat.ceil (max x0_real 1000)
  have h_x0_ge : (x0 : ℝ) ≥ max x0_real 1000 := Nat.le_ceil _
  have h_x0_ge_x0_real : (x0 : ℝ) ≥ x0_real := by
    have h' : max x0_real 1000 ≥ x0_real := le_max_left _ _
    linarith
  have h_x0_ge_1000 : 1000 ≤ x0 := by
    have h' : max x0_real 1000 ≥ 1000 := le_max_right _ _
    have h'' : (x0 : ℝ) ≥ 1000 := by linarith
    exact_mod_cast h''
  have h_main : ∀ (y : ℕ), x0 ≤ y → (y : ℝ)^(1 / 4 : ℝ) ≤ (y : ℝ) / (Real.log (y : ℝ))^2 := by
    intro y hy
    have hy' : (x0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
    have h_y_ge_x0 : x0_real ≤ (y : ℝ) := by linarith
    have h_y_gt_one : 1 < (y : ℝ) := by
      have h1 : 1000 ≤ (y : ℝ) := by exact_mod_cast (show 1000 ≤ y from by linarith)
      linarith
    have h_log_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
    have h_log_sq_pos : 0 < (Real.log (y : ℝ))^2 := by positivity
    have h_bound2 : (Real.log (y : ℝ))^(2 : ℝ) ≤ (y : ℝ)^(3 / 4 : ℝ) := h_bound (y : ℝ) h_y_ge_x0
    have h_conv : (Real.log (y : ℝ))^2 = (Real.log (y : ℝ))^(2 : ℝ) := by
      have h : ∀ (x : ℝ), x ^ 2 = x ^ (2 : ℝ) := by
        intro x
        simp
      exact h (Real.log (y : ℝ))
    have h_bound3 : (Real.log (y : ℝ))^2 ≤ (y : ℝ)^(3 / 4 : ℝ) := by
      rw [h_conv]
      exact h_bound2
    have h_y_pos : 0 < (y : ℝ) := by positivity
    have h_y34_pos : 0 < (y : ℝ)^(3 / 4 : ℝ) := by positivity
    have h_y14_pos : 0 < (y : ℝ)^(1 / 4 : ℝ) := by positivity
    have h_eq : (y : ℝ)^(3 / 4 : ℝ) * (y : ℝ)^(1 / 4 : ℝ) = (y : ℝ) := by
      rw [← Real.rpow_add h_y_pos]
      ; ring_nf ; norm_num
    calc
      (y : ℝ)^(1 / 4 : ℝ)
        = ((y : ℝ)^(3 / 4 : ℝ) * (y : ℝ)^(1 / 4 : ℝ)) / (y : ℝ)^(3 / 4 : ℝ) := by
          field_simp [h_y34_pos.ne']
      _ = (y : ℝ) / (y : ℝ)^(3 / 4 : ℝ) := by rw [h_eq]
      _ ≤ (y : ℝ) / (Real.log (y : ℝ))^2 := by
        gcongr

  exact ⟨x0, h_x0_ge_1000, h_main⟩

/-- Asymptotic inequality 2: y^(1/8) ≤ y / (log y)^2 for sufficiently large y. -/
lemma y_one_eighth_le_y_over_log_sq :
    ∃ x0 : ℕ, 1000 ≤ x0 ∧ ∀ y : ℕ, x0 ≤ y →
      (y : ℝ)^(1 / 8 : ℝ) ≤ (y : ℝ) / (Real.log (y : ℝ))^2 := by
  rcases general_log_pow_le_rpow 2 (7 / 8 : ℝ) (by norm_num) (by norm_num) with ⟨x0_real, hx0_gt_one, h_bound⟩
  let x0 : ℕ := Nat.ceil (max x0_real 1000)
  have h_x0_ge : (x0 : ℝ) ≥ max x0_real 1000 := Nat.le_ceil _
  have h_x0_ge_x0_real : (x0 : ℝ) ≥ x0_real := by
    have h' : max x0_real 1000 ≥ x0_real := le_max_left _ _
    linarith
  have h_x0_ge_1000 : 1000 ≤ x0 := by
    have h' : max x0_real 1000 ≥ 1000 := le_max_right _ _
    have h'' : (x0 : ℝ) ≥ 1000 := by linarith
    exact_mod_cast h''
  have h_main : ∀ (y : ℕ), x0 ≤ y → (y : ℝ)^(1 / 8 : ℝ) ≤ (y : ℝ) / (Real.log (y : ℝ))^2 := by
    intro y hy
    have hy' : (x0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
    have h_y_ge_x0 : x0_real ≤ (y : ℝ) := by linarith
    have h_y_gt_one : 1 < (y : ℝ) := by
      have h1 : 1000 ≤ (y : ℝ) := by exact_mod_cast (show 1000 ≤ y from by linarith)
      linarith
    have h_log_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
    have h_log_sq_pos : 0 < (Real.log (y : ℝ))^2 := by positivity
    have h_bound2 : (Real.log (y : ℝ))^(2 : ℝ) ≤ (y : ℝ)^(7 / 8 : ℝ) := h_bound (y : ℝ) h_y_ge_x0
    have h_conv : (Real.log (y : ℝ))^2 = (Real.log (y : ℝ))^(2 : ℝ) := by
      have h : ∀ (x : ℝ), x ^ 2 = x ^ (2 : ℝ) := by
        intro x
        simp
      exact h (Real.log (y : ℝ))
    have h_bound3 : (Real.log (y : ℝ))^2 ≤ (y : ℝ)^(7 / 8 : ℝ) := by
      rw [h_conv]
      exact h_bound2
    have h_y_pos : 0 < (y : ℝ) := by positivity
    have h_y78_pos : 0 < (y : ℝ)^(7 / 8 : ℝ) := by positivity
    have h_y18_pos : 0 < (y : ℝ)^(1 / 8 : ℝ) := by positivity
    have h_eq : (y : ℝ)^(7 / 8 : ℝ) * (y : ℝ)^(1 / 8 : ℝ) = (y : ℝ) := by
      rw [← Real.rpow_add h_y_pos]
      ; ring_nf ; norm_num
    calc
      (y : ℝ)^(1 / 8 : ℝ)
        = ((y : ℝ)^(7 / 8 : ℝ) * (y : ℝ)^(1 / 8 : ℝ)) / (y : ℝ)^(7 / 8 : ℝ) := by
          field_simp [h_y78_pos.ne']
      _ = (y : ℝ) / (y : ℝ)^(7 / 8 : ℝ) := by rw [h_eq]
      _ ≤ (y : ℝ) / (Real.log (y : ℝ))^2 := by
        gcongr

  exact ⟨x0, h_x0_ge_1000, h_main⟩

/-- Bonus: y^(1/4) ≤ y * (log log y)^2 / (log y)^2 for sufficiently large y.
    Even easier than the above, since (log log y)^2 ≥ 1 for y ≥ e^e. -/
lemma y_one_fourth_le_y_times_loglog_sq_over_log_sq :
    ∃ x0 : ℕ, 1000 ≤ x0 ∧ ∀ y : ℕ, x0 ≤ y →
      (y : ℝ)^(1 / 4 : ℝ) ≤ (y : ℝ) * (Real.log (Real.log (y : ℝ)))^2 / (Real.log (y : ℝ))^2 := by
  rcases y_one_fourth_le_y_over_log_sq with ⟨x0, hx0_ge, h_main1⟩
  have h_main2 : ∀ y : ℕ, x0 ≤ y →
      (y : ℝ) / (Real.log (y : ℝ))^2 ≤ (y : ℝ) * (Real.log (Real.log (y : ℝ)))^2 / (Real.log (y : ℝ))^2 := by
    intro y hy
    have h_y_ge1000 : 1000 ≤ y := by linarith
    have h_y_gt_one : 1 < (y : ℝ) := by
      have h1 : 1000 ≤ (y : ℝ) := by exact_mod_cast h_y_ge1000
      linarith
    have h_log_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
    have h_log_gt_one : 1 < Real.log (y : ℝ) := by
      have h1 : Real.log 1000 ≤ Real.log (y : ℝ) := Real.log_le_log (by positivity) (by exact_mod_cast h_y_ge1000)
      have h2 : 1 < Real.log 1000 := by
        have h3 : Real.exp 1 < 1000 := by
          have h4 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
          linarith
        have h5 : Real.log (Real.exp 1) < Real.log (1000 : ℝ) := Real.log_lt_log (by positivity) h3
        rw [Real.log_exp] at h5
        linarith
      linarith
    have h_exp1_le_log1000 : Real.exp 1 ≤ Real.log (1000 : ℝ) := by
      have h1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have h2 : Real.exp 3 < 1000 := by
        have h21 : Real.exp 3 ≤ 27 := by
          have h22 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
          have h23 : Real.exp 3 = (Real.exp 1)^3 := by
            rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num]
            rw [Real.exp_add, Real.exp_add] ; ring
          rw [h23]
          have h24 : (Real.exp 1)^3 ≤ (3 : ℝ)^3 := by gcongr
          norm_num at h24 ⊢ ; exact h24
        linarith
      have h3 : Real.log (Real.exp 3) < Real.log (1000 : ℝ) := Real.log_lt_log (by positivity) h2
      have h4 : (3 : ℝ) < Real.log (1000 : ℝ) := by
        rw [Real.log_exp] at h3 ; linarith
      linarith
    have h_exp1_le_logy : Real.exp 1 ≤ Real.log (y : ℝ) := by
      have h4 : Real.log (1000 : ℝ) ≤ Real.log (y : ℝ) := Real.log_le_log (by positivity) (by exact_mod_cast h_y_ge1000)
      linarith [h_exp1_le_log1000]
    have h_loglog_pos : 0 < Real.log (Real.log (y : ℝ)) := Real.log_pos h_log_gt_one
    have h_loglog_sq_ge1 : 1 ≤ (Real.log (Real.log (y : ℝ)))^2 := by
      have h1 : 1 ≤ Real.log (Real.log (y : ℝ)) := by
        have h3 : Real.log (Real.exp 1) ≤ Real.log (Real.log (y : ℝ)) := Real.log_le_log (by positivity) h_exp1_le_logy
        rw [Real.log_exp] at h3
        linarith
      nlinarith
    have h_y_pos : 0 < (y : ℝ) := by positivity
    have h_log_sq_pos : 0 < (Real.log (y : ℝ))^2 := by positivity
    calc
      (y : ℝ) / (Real.log (y : ℝ))^2
        = 1 * ((y : ℝ) / (Real.log (y : ℝ))^2) := by ring
      _ ≤ (Real.log (Real.log (y : ℝ)))^2 * ((y : ℝ) / (Real.log (y : ℝ))^2) := by
        gcongr
      _ = (y : ℝ) * (Real.log (Real.log (y : ℝ)))^2 / (Real.log (y : ℝ))^2 := by ring
  have h_main : ∀ y : ℕ, x0 ≤ y →
      (y : ℝ)^(1 / 4 : ℝ) ≤ (y : ℝ) * (Real.log (Real.log (y : ℝ)))^2 / (Real.log (y : ℝ))^2 := by
    intro y hy
    have h1 : (y : ℝ)^(1 / 4 : ℝ) ≤ (y : ℝ) / (Real.log (y : ℝ))^2 := h_main1 y hy
    have h2 : (y : ℝ) / (Real.log (y : ℝ))^2 ≤ (y : ℝ) * (Real.log (Real.log (y : ℝ)))^2 / (Real.log (y : ℝ))^2 := h_main2 y hy
    exact le_trans h1 h2
  exact ⟨x0, hx0_ge, h_main⟩

/-- Bonus: z = y^(1/8) satisfies z ≤ y * (log log y)^2 / (log y)^2 for large y. -/
lemma y_one_eighth_le_y_times_loglog_sq_over_log_sq :
    ∃ x0 : ℕ, 1000 ≤ x0 ∧ ∀ y : ℕ, x0 ≤ y →
      (y : ℝ)^(1 / 8 : ℝ) ≤ (y : ℝ) * (Real.log (Real.log (y : ℝ)))^2 / (Real.log (y : ℝ))^2 := by
  rcases y_one_eighth_le_y_over_log_sq with ⟨x0, hx0_ge, h_main1⟩
  have h_main2 : ∀ y : ℕ, x0 ≤ y →
      (y : ℝ) / (Real.log (y : ℝ))^2 ≤ (y : ℝ) * (Real.log (Real.log (y : ℝ)))^2 / (Real.log (y : ℝ))^2 := by
    intro y hy
    have h_y_ge1000 : 1000 ≤ y := by linarith
    have h_y_gt_one : 1 < (y : ℝ) := by
      have h1 : 1000 ≤ (y : ℝ) := by exact_mod_cast h_y_ge1000
      linarith
    have h_log_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
    have h_log_gt_one : 1 < Real.log (y : ℝ) := by
      have h1 : Real.log 1000 ≤ Real.log (y : ℝ) := Real.log_le_log (by positivity) (by exact_mod_cast h_y_ge1000)
      have h2 : 1 < Real.log 1000 := by
        have h3 : Real.exp 1 < 1000 := by
          have h4 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
          linarith
        have h5 : Real.log (Real.exp 1) < Real.log (1000 : ℝ) := Real.log_lt_log (by positivity) h3
        rw [Real.log_exp] at h5
        linarith
      linarith
    have h_exp1_le_log1000 : Real.exp 1 ≤ Real.log (1000 : ℝ) := by
      have h1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have h2 : Real.exp 3 < 1000 := by
        have h21 : Real.exp 3 ≤ 27 := by
          have h22 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
          have h23 : Real.exp 3 = (Real.exp 1)^3 := by
            rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num]
            rw [Real.exp_add, Real.exp_add] ; ring
          rw [h23]
          have h24 : (Real.exp 1)^3 ≤ (3 : ℝ)^3 := by gcongr
          norm_num at h24 ⊢ ; exact h24
        linarith
      have h3 : Real.log (Real.exp 3) < Real.log (1000 : ℝ) := Real.log_lt_log (by positivity) h2
      have h4 : (3 : ℝ) < Real.log (1000 : ℝ) := by
        rw [Real.log_exp] at h3 ; linarith
      linarith
    have h_exp1_le_logy : Real.exp 1 ≤ Real.log (y : ℝ) := by
      have h4 : Real.log (1000 : ℝ) ≤ Real.log (y : ℝ) := Real.log_le_log (by positivity) (by exact_mod_cast h_y_ge1000)
      linarith [h_exp1_le_log1000]
    have h_loglog_pos : 0 < Real.log (Real.log (y : ℝ)) := Real.log_pos h_log_gt_one
    have h_loglog_sq_ge1 : 1 ≤ (Real.log (Real.log (y : ℝ)))^2 := by
      have h1 : 1 ≤ Real.log (Real.log (y : ℝ)) := by
        have h3 : Real.log (Real.exp 1) ≤ Real.log (Real.log (y : ℝ)) := Real.log_le_log (by positivity) h_exp1_le_logy
        rw [Real.log_exp] at h3
        linarith
      nlinarith
    have h_y_pos : 0 < (y : ℝ) := by positivity
    have h_log_sq_pos : 0 < (Real.log (y : ℝ))^2 := by positivity
    calc
      (y : ℝ) / (Real.log (y : ℝ))^2
        = 1 * ((y : ℝ) / (Real.log (y : ℝ))^2) := by ring
      _ ≤ (Real.log (Real.log (y : ℝ)))^2 * ((y : ℝ) / (Real.log (y : ℝ))^2) := by
        gcongr
      _ = (y : ℝ) * (Real.log (Real.log (y : ℝ)))^2 / (Real.log (y : ℝ))^2 := by ring
  have h_main : ∀ y : ℕ, x0 ≤ y →
      (y : ℝ)^(1 / 8 : ℝ) ≤ (y : ℝ) * (Real.log (Real.log (y : ℝ)))^2 / (Real.log (y : ℝ))^2 := by
    intro y hy
    have h1 : (y : ℝ)^(1 / 8 : ℝ) ≤ (y : ℝ) / (Real.log (y : ℝ))^2 := h_main1 y hy
    have h2 : (y : ℝ) / (Real.log (y : ℝ))^2 ≤ (y : ℝ) * (Real.log (Real.log (y : ℝ)))^2 / (Real.log (y : ℝ))^2 := h_main2 y hy
    exact le_trans h1 h2
  exact ⟨x0, hx0_ge, h_main⟩

end Vendored.NumberTheory.Analytic.Sieve
