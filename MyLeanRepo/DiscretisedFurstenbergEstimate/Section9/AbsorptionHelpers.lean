module

/-
  Helper lemmas for Section 9 exponent absorption.

  Provides:
  - `log_factor_absorption`: for any C ≥ 0 and ε > 0, there exists δ₀ > 0
    such that log(1/δ)^{-C} ≥ δ^ε for all 0 < δ ≤ δ₀.
  - `bad_product_reciprocation`: convert upper bound on product of ratios
    to lower bound on product of inverse ratios.

  These are used to instantiate the abstract `exponent_absorption` lemma
  with concrete bounds from the decomposition data.

  Whiteprint node: section9 / absorption_helpers
  Status: DRAFT
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9

/-- For any C ≥ 0 and ε > 0, there exists δ₀ > 0 such that for all
    0 < δ ≤ δ₀, `log(1/δ)^{-C} ≥ δ^ε`.

    This follows from the fact that any power of log grows slower than any
    positive power of 1/δ. -/
lemma log_factor_absorption (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
      (Real.log (1 / δ)) ^ (-C) ≥ δ ^ ε := by
  by_cases hC0 : C = 0
  · -- C = 0: log(1/δ)^0 = 1 ≥ δ^ε since δ ≤ 1
    refine ⟨1, by norm_num, fun δ hδ_pos hδ_le_one => ?_⟩
    have h1 : (Real.log (1 / δ)) ^ (-C) = 1 := by
      rw [hC0] <;> simp
    rw [h1]
    have h2 : δ ^ ε ≤ 1 := by
      have h3 : δ ≤ 1 := by linarith
      exact Real.rpow_le_one hδ_pos.le h3 hε.le
    linarith
  · -- C > 0
    have hC_pos : 0 < C := by
      exact lt_of_le_of_ne hC (Ne.symm hC0)
    -- Directly: (log x)^C = o(x^ε) as x → ∞
    have h_littleo : (fun x : ℝ => (Real.log x) ^ C) =o[Filter.atTop] (fun x : ℝ => x ^ ε) :=
      isLittleO_log_rpow_rpow_atTop C hε
    have h1 : ∀ᶠ (x : ℝ) in Filter.atTop, ‖(Real.log x) ^ C‖ ≤ ‖x ^ ε‖ :=
      h_littleo.eventuallyLE
    -- Restrict to x > 1 where both sides are positive, so norms drop
    have h2 : ∀ᶠ (x : ℝ) in Filter.atTop, (Real.log x) ^ C ≤ x ^ ε := by
      filter_upwards [h1, Filter.eventually_gt_atTop (1 : ℝ)] with x hx_norm hx_gt_one
      have hlog_pos : 0 < Real.log x := Real.log_pos hx_gt_one
      have hleft_pos : 0 < (Real.log x) ^ C := by positivity
      have hright_pos : 0 < x ^ ε := by positivity
      have hnorm_left : ‖(Real.log x) ^ C‖ = (Real.log x) ^ C := by
        simpa [abs_of_pos hleft_pos] using rfl
      have hnorm_right : ‖x ^ ε‖ = x ^ ε := by
        simpa [abs_of_pos hright_pos] using rfl
      rw [hnorm_left, hnorm_right] at hx_norm
      exact hx_norm
    rcases Filter.eventually_atTop.mp h2 with ⟨x₀, hx₀⟩
    let x₁ : ℝ := max x₀ 1 + 1
    have hx₁_gt_one : 1 < x₁ := by
      dsimp only [x₁]
      have h : max x₀ 1 ≥ 1 := le_max_right _ _
      linarith
    have hx₁_ge : x₁ ≥ x₀ := by
      dsimp only [x₁]
      have h : max x₀ 1 ≥ x₀ := le_max_left _ _
      linarith
    let δ₀ : ℝ := 1 / x₁
    have hδ₀_pos : 0 < δ₀ := by positivity
    refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_le => ?_⟩
    have h_x_ge_x1 : 1 / δ ≥ x₁ := by
      dsimp only [δ₀] at hδ_le
      have h1 : 1 / δ ≥ 1 / δ₀ := by gcongr <;> linarith
      simpa [δ₀] using h1
    have h_x_ge_x0 : 1 / δ ≥ x₀ := by linarith
    have h_x_gt_one : 1 < 1 / δ := by linarith [hx₁_gt_one]
    have h6 : (Real.log (1 / δ)) ^ C ≤ (1 / δ) ^ ε := hx₀ (1 / δ) h_x_ge_x0
    have hlog_pos' : 0 < Real.log (1 / δ) := Real.log_pos h_x_gt_one
    have h7 : 0 < (Real.log (1 / δ)) ^ C := Real.rpow_pos_of_pos hlog_pos' C
    have h8 : (Real.log (1 / δ)) ^ (-C) = ((Real.log (1 / δ)) ^ C)⁻¹ := by
      rw [Real.rpow_neg (by linarith [hlog_pos'])] <;> ring
    rw [h8]
    have h9 : (1 / δ) ^ ε = (δ ^ ε)⁻¹ := by
      have h10 : (1 / δ) = δ⁻¹ := by field_simp
      rw [h10]
      rw [Real.inv_rpow hδ_pos.le]
      <;> ring
    have h13 : ((Real.log (1 / δ)) ^ C)⁻¹ ≥ ((1 / δ) ^ ε)⁻¹ := by
      gcongr
    rw [h9] at h13
    have h14 : ((δ ^ ε)⁻¹)⁻¹ = δ ^ ε := by
      have h15 : 0 < δ ^ ε := by positivity
      field_simp [h15.ne'] <;> ring
    rw [h14] at h13
    exact h13

/-- Convert an upper bound on a product of positive ratios to a lower bound
    on the product of their inverses. -/
lemma bad_product_reciprocation
    {n : ℕ} {B : Finset (Fin n)} {δ : ℝ} {ε_bad : ℝ}
    {Δ : Fin (n + 1) → ℝ} (hΔ_pos : ∀ i, 0 < Δ i)
    (h : (∏ j ∈ B, (Δ j.castSucc / Δ (Fin.succ j))) ≤ δ ^ (-ε_bad))
    (hδ_pos : 0 < δ) (hε_bad : 0 ≤ ε_bad) :
    (∏ j ∈ B, Δ (Fin.succ j) / Δ j.castSucc) ≥ δ ^ ε_bad := by
  have h_pos : ∀ j ∈ B, 0 < Δ j.castSucc / Δ (Fin.succ j) := by
    intro j _
    exact div_pos (hΔ_pos _) (hΔ_pos _)
  have h_prod_pos : 0 < (∏ j ∈ B, (Δ j.castSucc / Δ (Fin.succ j))) :=
    Finset.prod_pos h_pos
  have h_inv : (∏ j ∈ B, Δ (Fin.succ j) / Δ j.castSucc) =
      ((∏ j ∈ B, (Δ j.castSucc / Δ (Fin.succ j)))⁻¹) := by
    have h1 : ∏ j ∈ B, Δ (Fin.succ j) / Δ j.castSucc =
        ∏ j ∈ B, (Δ j.castSucc / Δ (Fin.succ j))⁻¹ := by
      apply Finset.prod_congr rfl
      intro j _
      field_simp [(hΔ_pos _).ne', (hΔ_pos _).ne'] <;> ring
    rw [h1]
    rw [Finset.prod_inv_distrib]
  rw [h_inv]
  have h2 : 0 < δ ^ (-ε_bad) := by positivity
  have h3 : ((∏ j ∈ B, (Δ j.castSucc / Δ (Fin.succ j)))⁻¹) ≥ (δ ^ (-ε_bad))⁻¹ := by
    gcongr
  have h4 : (δ ^ (-ε_bad))⁻¹ = δ ^ ε_bad := by
    have h5 : 0 < δ ^ ε_bad := by positivity
    have h6 : δ ^ (-ε_bad) = (δ ^ ε_bad)⁻¹ := by
      rw [← Real.rpow_neg hδ_pos.le] <;> ring
    rw [h6]
    field_simp [h5.ne'] <;> ring
  rw [h4] at h3
  exact h3

end DirecretisedFurstenbergEstimate.Section9
