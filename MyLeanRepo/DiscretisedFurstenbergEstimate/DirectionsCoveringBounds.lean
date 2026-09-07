module

/-
  Helper lemmas for directions covering bounds in Phase2Assembly.

  1. Lower bound: from IsDeltaSSet at scale δ, Ncover δ P ≥ 1/(C * δ^s)
  2. Polylog absorption: K * log(2/√δ)^A * δ^(-ε) ≤ (√δ)^(-Aρ) for small δ

  Dependencies: Basics
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Phase2Ncover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Basics
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
open DirecretisedFurstenbergEstimate

noncomputable section

namespace DirecretisedFurstenbergEstimate.Phase2

/-! ### Lower covering bound from S-set property -/

/-- If P is a nonempty (δ,s,C)-set, then Ncover δ P ≥ 1/(C * δ^s). -/
lemma sset_lower_cover_bound
    {X : Type*} [PseudoMetricSpace X] {δ s C : ℝ} {P : Set X}
    (hδ_pos : 0 < δ) (hs_nonneg : 0 ≤ s) (hC_pos : 0 < C)
    (hP : IsDeltaSSet δ s C P) :
    ENNReal.ofReal (1 / (C * δ ^ s)) ≤ Ncover δ P := by
  rcases hP with ⟨hP_nonempty, _, _, _, h_main⟩
  rcases hP_nonempty with ⟨x, hx⟩
  have hδ_nonneg : 0 ≤ δ := by linarith
  have h1 : x ∈ P ∩ Metric.closedBall x δ := by
    exact ⟨hx, by simp [dist_self, hδ_nonneg]⟩
  have h_nonempty : (P ∩ Metric.closedBall x δ).Nonempty := ⟨x, h1⟩
  have h_pos : 0 < (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x δ)) :=
    Metric.externalCoveringNumber_pos_iff.mpr h_nonempty
  have h2' : (1 : ℝ≥0∞) ≤ (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x δ) : ℝ≥0∞) := by
    have h : (1 : ℕ∞) ≤ Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x δ) := by
      exact Order.one_le_iff_pos.mpr h_pos
    exact_mod_cast h
  have h3 := h_main x δ (by linarith)
  have h4 : (ENNReal.ofReal (δ : ℝ)) ^ s = ENNReal.ofReal (δ ^ s) := by
    exact ENNReal.ofReal_rpow_of_pos hδ_pos
  rw [h4] at h3
  set a : ENNReal := ENNReal.ofReal (C * δ ^ s) with ha_def
  have hCδ_pos : 0 < C * δ ^ s := by positivity
  have h_prod : ENNReal.ofReal C * ENNReal.ofReal (δ ^ s) = a := by
    rw [← ENNReal.ofReal_mul (by linarith), ha_def] <;> ring
  rw [h_prod] at h3
  have h5 : (1 : ℝ≥0∞) ≤ a * Ncover δ P := by
    simpa [Ncover] using le_trans h2' h3
  have ha_ne_zero : a ≠ 0 := by
    simp [ha_def, ENNReal.ofReal_eq_zero]
    <;> linarith
  have ha_ne_top : a ≠ ⊤ := by
    simp [ha_def, ENNReal.ofReal_ne_top]
  have h6 : a⁻¹ * a = 1 := ENNReal.inv_mul_cancel ha_ne_zero ha_ne_top
  have h7 : a⁻¹ = ENNReal.ofReal (1 / (C * δ ^ s)) := by
    have h_inv : (1 / (C * δ ^ s)) = (C * δ ^ s)⁻¹ := by
      field_simp [hCδ_pos.ne'] <;> ring
    have h8 : ENNReal.ofReal ((C * δ ^ s)⁻¹) = (ENNReal.ofReal (C * δ ^ s))⁻¹ :=
      ENNReal.ofReal_inv_of_pos hCδ_pos
    have h9 : ENNReal.ofReal (1 / (C * δ ^ s)) = (ENNReal.ofReal (C * δ ^ s))⁻¹ := by
      rw [h_inv]
      exact h8
    simpa [ha_def] using h9.symm
  calc
    ENNReal.ofReal (1 / (C * δ ^ s))
      = a⁻¹ := h7.symm
    _ = a⁻¹ * 1 := by simp
    _ ≤ a⁻¹ * (a * Ncover δ P) := by gcongr
    _ = (a⁻¹ * a) * Ncover δ P := by rw [mul_assoc]
    _ = 1 * Ncover δ P := by rw [h6]
    _ = Ncover δ P := by simp

/-! ### Polylog absorption -/

/-- For any α > 0, A, K > 0, there exists x₀ > 0 such that for all x ≥ x₀:
    K * Real.log x ^ A ≤ x ^ α.

    Uses Mathlib's `isLittleO_log_rpow_rpow_atTop`. -/
lemma polylog_beats_polynomial {α A K : ℝ} (hα_pos : 0 < α) (hK_pos : 0 < K) :
    ∃ (x₀ : ℝ), 0 < x₀ ∧ ∀ (x : ℝ), x ≥ x₀ → K * Real.log x ^ A ≤ x ^ α := by
  have h_main : (fun x : ℝ => Real.log x ^ A) =o[Filter.atTop] fun x : ℝ => x ^ α :=
    isLittleO_log_rpow_rpow_atTop A hα_pos
  have h1 : ∀ (c : ℝ), 0 < c → ∃ (x₀ : ℝ), ∀ (x : ℝ), x ≥ x₀ →
      |Real.log x ^ A| ≤ c * |x ^ α| := by
    intro c hc
    have h2 : (fun x : ℝ => Real.log x ^ A) =o[Filter.atTop] fun x : ℝ => x ^ α := h_main
    have h3 := (Asymptotics.isLittleO_iff).mp h2 hc
    rcases Filter.eventually_atTop.mp h3 with ⟨x₀, hx₀⟩
    exact ⟨x₀, fun x hx => hx₀ x hx⟩
  have hK_pos' : 0 < 1 / K := by positivity
  rcases h1 (1 / K) hK_pos' with ⟨x₀, hx₀⟩
  let x₁ := max x₀ 1
  have hx₁_pos : 0 < x₁ := by positivity
  refine' ⟨x₁, hx₁_pos, _⟩
  intro x hx
  have hx_ge_x0 : x ≥ x₀ := le_trans (le_max_left _ _) hx
  have hx_ge_one : x ≥ 1 := le_trans (le_max_right _ _) hx
  have h2 : |Real.log x ^ A| ≤ (1 / K) * |x ^ α| := hx₀ x hx_ge_x0
  have h3 : 0 ≤ Real.log x := by
    have h4 : Real.log x ≥ Real.log 1 := Real.log_le_log (by linarith) hx_ge_one
    simpa using h4
  have h4 : 0 ≤ x ^ α := by positivity
  have h5 : |Real.log x ^ A| = Real.log x ^ A := by
    rw [abs_of_nonneg] <;> positivity
  have h6 : |x ^ α| = x ^ α := by
    rw [abs_of_nonneg] <;> positivity
  rw [h5, h6] at h2
  have h7 : Real.log x ^ A ≤ (1 / K) * x ^ α := h2
  have h8 : K * Real.log x ^ A ≤ x ^ α := by
    calc
      K * Real.log x ^ A ≤ K * ((1 / K) * x ^ α) := by gcongr
      _ = x ^ α := by
        field_simp [hK_pos.ne'] <;> ring
  exact h8

/-- Directions constant absorption: for small δ,
    K * log(2/√δ)^A * δ^(-ε) ≤ (√δ)^(-Aρ)
    whenever Aρ > 2ε. -/
lemma directions_constant_absorption
    {Aρ ε K A : ℝ} (hAρ_pos : 0 < Aρ) (hε_pos : 0 < ε)
    (hK_pos : 0 < K) (h_ineq : 2 * ε < Aρ) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
      K * Real.log (2 / Real.sqrt δ) ^ A * δ ^ (-ε) ≤ (Real.sqrt δ) ^ (-(Aρ)) := by
  set α : ℝ := Aρ / 2 - ε with hα_def
  have hα_pos : 0 < α := by linarith
  -- Apply polylog with y = 2/√δ
  rcases polylog_beats_polynomial hα_pos hK_pos with ⟨y₀, hy₀_pos, hy₀_lemma⟩
  -- We need y = 2/√δ ≥ y₀, i.e. √δ ≤ 2/y₀, i.e. δ ≤ 4/y₀²
  let δ₁ : ℝ := 4 / y₀ ^ 2
  have hδ₁_pos : 0 < δ₁ := by positivity
  -- Also need (2/√δ)^α ≤ δ^(-α), i.e. 2^α * δ^(-α/2) ≤ δ^(-α), i.e. 2^α ≤ δ^(-α/2)
  -- This holds for δ ≤ 2^(-2) = 1/4 (since then δ^(-α/2) ≥ 2^α)
  let δ₀ : ℝ := min (1 / 4) δ₁
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine' ⟨δ₀, hδ₀_pos, _⟩
  intro δ hδ hδ₀
  have hδ_le_quarter : δ ≤ 1 / 4 := le_trans hδ₀ (min_le_left _ _)
  have hδ_le_δ1 : δ ≤ δ₁ := le_trans hδ₀ (min_le_right _ _)
  set y : ℝ := 2 / Real.sqrt δ with hy_def
  have h_sqrt_pos : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hy_pos : 0 < y := by positivity
  have hy_ge_y0 : y ≥ y₀ := by
    have h1 : δ ≤ 4 / y₀ ^ 2 := hδ_le_δ1
    have h2 : 0 < y₀ := hy₀_pos
    have h3 : Real.sqrt δ ≤ 2 / y₀ := by
      have h4 : Real.sqrt δ ≤ Real.sqrt (4 / y₀ ^ 2) := Real.sqrt_le_sqrt (by linarith)
      have h5 : Real.sqrt (4 / y₀ ^ 2) = 2 / y₀ := by
        have h6 : 0 < y₀ := h2
        rw [Real.sqrt_eq_cases] <;> field_simp [h6.ne'] <;> norm_num
      rw [h5] at h4 <;> exact h4
    have h7 : 2 / Real.sqrt δ ≥ 2 / (2 / y₀) := by
      gcongr
    have h8 : 2 / (2 / y₀) = y₀ := by
      field_simp [h2.ne'] <;> ring
    rw [h8] at h7
    exact h7
  have h9 : K * Real.log y ^ A ≤ y ^ α := hy₀_lemma y hy_ge_y0
  have h10 : y ^ α ≤ δ ^ (-α) := by
    have h11 : y = 2 / Real.sqrt δ := by simp [y]
    rw [h11]
    have h12 : (2 / Real.sqrt δ) ^ α = 2 ^ α * (Real.sqrt δ) ^ (-α) := by
      have h13 : 0 < Real.sqrt δ := h_sqrt_pos
      have h14 : (2 / Real.sqrt δ) ^ α = (2 : ℝ) ^ α * (Real.sqrt δ) ^ (-α) := by
        have h15 : (2 / Real.sqrt δ) = (2 : ℝ) * (Real.sqrt δ)⁻¹ := by
          field_simp [h13.ne'] <;> ring
        rw [h15]
        have h16 : ((2 : ℝ) * (Real.sqrt δ)⁻¹) ^ α = (2 : ℝ) ^ α * ((Real.sqrt δ)⁻¹) ^ α :=
          Real.mul_rpow (by positivity) (by positivity)
        rw [h16]
        have h17 : ((Real.sqrt δ)⁻¹) ^ α = (Real.sqrt δ) ^ (-α) := by
          have h_pos : 0 < Real.sqrt δ := h_sqrt_pos
          have h18 : (Real.sqrt δ)⁻¹ = (Real.sqrt δ) ^ (-1 : ℝ) := by
            have h19 : (Real.sqrt δ) ^ (-1 : ℝ) = (Real.sqrt δ)⁻¹ := by
              rw [Real.rpow_neg (by positivity) (1 : ℝ)]
              <;> simp
            exact h19.symm
          rw [h18]
          rw [← Real.rpow_mul (by linarith)]
          <;> ring_nf
        rw [h17]
      exact h14
    rw [h12]
    have h15 : (Real.sqrt δ) ^ (-α) = δ ^ (-α / 2) := by
      have h16 : Real.sqrt δ = δ ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
      rw [h16]
      rw [← Real.rpow_mul (by linarith)] <;> ring_nf
    rw [h15]
    have h17 : 2 ^ α * δ ^ (-α / 2) ≤ δ ^ (-α) := by
      have h18 : δ ≤ 1 / 4 := hδ_le_quarter
      have h19 : 0 < δ := hδ
      have h20 : δ ^ (-α / 2) > 0 := by positivity
      have h21 : 2 ^ α ≤ δ ^ (-α / 2) := by
        have h22 : δ ≤ 1 / 4 := h18
        have h23 : δ ^ (α / 2) ≤ (1 / 4) ^ (α / 2) := by gcongr <;> positivity
        have h24 : (1 / 4 : ℝ) ^ (α / 2) = (2 : ℝ) ^ (-α) := by
          have h25 : (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by norm_num
          rw [h25]
          rw [← Real.rpow_mul (by norm_num)] <;> ring_nf
        rw [h24] at h23
        have h26 : δ ^ (α / 2) ≤ 2 ^ (-α) := h23
        have h27 : 0 < δ ^ (α / 2) := by positivity
        have h28 : 0 < (2 : ℝ) ^ (-α) := by positivity
        have h29 : ((2 : ℝ) ^ (-α))⁻¹ ≤ (δ ^ (α / 2))⁻¹ := by gcongr
        have h30 : ((2 : ℝ) ^ (-α))⁻¹ = (2 : ℝ) ^ α := by
          have h31 : (2 : ℝ) ^ (-α) = ((2 : ℝ) ^ α)⁻¹ := Real.rpow_neg (by norm_num) α
          rw [h31]
          rw [inv_inv]
        have h32 : (δ ^ (α / 2))⁻¹ = δ ^ (-α / 2) := by
          have h_eq : -α / 2 = -(α / 2) := by ring
          have h33 : δ ^ (-(α / 2)) = (δ ^ (α / 2))⁻¹ := Real.rpow_neg hδ.le (α / 2)
          have h34 : δ ^ (-α / 2) = δ ^ (-(α / 2)) := by rw [h_eq]
          rw [h34]
          exact h33.symm
        rw [h30, h32] at h29
        exact h29
      calc
        2 ^ α * δ ^ (-α / 2) ≤ δ ^ (-α / 2) * δ ^ (-α / 2) := by gcongr
        _ = δ ^ (-α) := by
          rw [← Real.rpow_add (by linarith)] <;> ring_nf
    exact h17
  have h22 : K * Real.log y ^ A ≤ δ ^ (-α) := by linarith
  have h23 : K * Real.log (2 / Real.sqrt δ) ^ A * δ ^ (-ε) ≤ δ ^ (-α) * δ ^ (-ε) :=
    mul_le_mul_of_nonneg_right h22 (by positivity)
  have h24 : δ ^ (-α) * δ ^ (-ε) = δ ^ (-(Aρ / 2)) := by
    have h25 : -α + -ε = -(Aρ / 2) := by
      dsimp only [α] <;> ring
    rw [← Real.rpow_add (by linarith), h25]
  rw [h24] at h23
  have h26 : (Real.sqrt δ) ^ (-(Aρ)) = δ ^ (-(Aρ / 2)) := by
    have h27 : Real.sqrt δ = δ ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
    rw [h27]
    rw [← Real.rpow_mul (by linarith)] <;> ring_nf
  rw [h26]
  exact h23

end DirecretisedFurstenbergEstimate.Phase2

end
