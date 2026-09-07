module

/-
  Threshold existential lemmas for the five absorption ledgers.

  Each lemma provides ∃ δ₀ > 0 such that for all 0 < δ ≤ δ₀,
  the relevant constant/polylog factor is absorbed by δ^(-ε).

  Uses polylog_absorption from PolylogAbsorption for logarithmic growth terms.

  Whiteprint node: section9 / threshold_existentials
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.PolylogAbsorption
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9

/-- Generic constant absorption: for any C ≥ 0 and ε > 0, there exists
    δ₀ > 0 such that C ≤ δ^(-ε) for all 0 < δ ≤ δ₀. -/
lemma constant_absorption_threshold (C ε : ℝ) (hC_nonneg : 0 ≤ C) (hε_pos : 0 < ε) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ → C ≤ δ ^ (-ε) := by
  by_cases hC_le_one : C ≤ 1
  · -- C ≤ 1: choose δ₀ = 1, then δ^(-ε) ≥ 1 ≥ C for δ ≤ 1
    refine ⟨1, by norm_num, fun δ hδ_pos hδ_le => ?_⟩
    have h1 : δ ^ ε ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) (by linarith)
    have h2 : 0 < δ ^ ε := Real.rpow_pos_of_pos hδ_pos _
    have h3 : δ ^ (-ε) = (δ ^ ε)⁻¹ := by
      rw [Real.rpow_neg hδ_pos.le] <;> ring
    rw [h3]
    have h4 : 1 ≤ (δ ^ ε)⁻¹ := by
      have h41 : δ ^ ε ≤ 1 := h1
      have h42 : 0 < δ ^ ε := h2
      have h43 : (δ ^ ε) * (δ ^ ε)⁻¹ = 1 := by field_simp [h42.ne'] <;> ring
      nlinarith
    linarith
  · -- C > 1: choose δ₀ = C^(-1/ε)
    have hC_pos : 0 < C := by linarith
    have hC_gt_one : 1 < C := by linarith
    let δ₀ : ℝ := C ^ (-1 / ε)
    have hδ₀_pos : 0 < δ₀ := Real.rpow_pos_of_pos hC_pos _
    have hδ₀_pow : δ₀ ^ ε = C⁻¹ := by
      have hlog : Real.log (δ₀ ^ ε) = Real.log (C⁻¹) := by
        rw [Real.log_rpow hδ₀_pos, Real.log_rpow hC_pos]
        <;> simp [δ₀] <;> field_simp [hε_pos.ne'] <;> ring
      have hpos1 : 0 < δ₀ ^ ε := Real.rpow_pos_of_pos hδ₀_pos _
      have hpos2 : 0 < C⁻¹ := by positivity
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr hpos1) (Set.mem_Ioi.mpr hpos2) hlog
    refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_le => ?_⟩
    have h4 : δ ^ ε ≤ δ₀ ^ ε := Real.rpow_le_rpow (by linarith) hδ_le (by linarith)
    have h5 : δ ^ ε ≤ C⁻¹ := by rw [hδ₀_pow] at h4; exact h4
    have h6 : 0 < δ ^ ε := Real.rpow_pos_of_pos hδ_pos _
    have h7 : C * δ ^ ε ≤ 1 := by
      calc C * δ ^ ε ≤ C * C⁻¹ := by gcongr
           _ = 1 := by field_simp [hC_pos.ne'] <;> ring
    have h8 : δ ^ (-ε) = (δ ^ ε)⁻¹ := by
      rw [Real.rpow_neg hδ_pos.le] <;> ring
    rw [h8]
    have h9 : C ≤ (δ ^ ε)⁻¹ := by
      have h91 : C * δ ^ ε ≤ 1 := h7
      have h92 : 0 < δ ^ ε := h6
      have h93 : C ≤ (δ ^ ε)⁻¹ := by
        calc C = C * ((δ ^ ε) * (δ ^ ε)⁻¹) := by field_simp [h92.ne'] <;> ring
          _ = (C * δ ^ ε) * (δ ^ ε)⁻¹ := by ring
          _ ≤ 1 * (δ ^ ε)⁻¹ := by gcongr
          _ = (δ ^ ε)⁻¹ := by ring
      exact h93
    exact h9

/-- Generic polylog absorption: for any C ≥ 0, A > 0, ε > 0, there exists
    δ₀ > 0 such that C * log(1/δ)^A ≤ δ^(-ε) for all 0 < δ ≤ δ₀. -/
lemma polylog_absorption_threshold (C A ε : ℝ)
    (hA_pos : 0 < A) (hε_pos : 0 < ε) (hC_nonneg : 0 ≤ C) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
        C * (Real.log (1 / δ)) ^ A ≤ δ ^ (-ε) := by
  have h_main := PolylogAbsorption.polylog_absorption_with_const hA_pos hε_pos hC_nonneg
  rcases h_main with ⟨Δ₀, hΔ₀_pos, hΔ₀_le_one, h1⟩
  refine ⟨Δ₀, hΔ₀_pos, hΔ₀_le_one, fun δ hδ_pos hδ_le => ?_⟩
  have h2 : C * (Real.log (2 / δ)) ^ A ≤ δ ^ (-ε) := h1 δ hδ_pos hδ_le
  have h3 : 0 ≤ Real.log (1 / δ) := by
    have h4 : δ ≤ 1 := by linarith [hΔ₀_le_one]
    have h51 : 1 / 1 ≤ 1 / δ := one_div_le_one_div_of_le hδ_pos h4
    have h5 : 1 ≤ 1 / δ := by simpa using h51
    exact Real.log_nonneg h5
  have h4 : Real.log (1 / δ) ≤ Real.log (2 / δ) := by
    apply Real.log_le_log
    · positivity
    · have h5 : 1 / δ ≤ 2 / δ := by
        have h6 : 0 < δ := hδ_pos
        gcongr
        <;> norm_num
      exact h5
  have h5 : (Real.log (1 / δ)) ^ A ≤ (Real.log (2 / δ)) ^ A := by
    gcongr <;> linarith
  have h6 : C * (Real.log (1 / δ)) ^ A ≤ C * (Real.log (2 / δ)) ^ A := by
    gcongr <;> linarith
  exact h6.trans h2

/-- Ledger A: point-to-Root threshold (corrected: factors out ε_input).

    The point-side loss has the form:
      point_coeff(δ) * δ^(-ε_input) * δ^(-rho_Delta)
    where:
      - ε_input is the source S-set exponent
      - rho_Delta = log(48*log(1/Δ)) / log(1/Δ) is the uniformization log exponent
      - point_coeff(δ) is the remaining fixed/polylogarithmic coefficient

    Budget: ε_input + rho_Delta + ε_band < ε_Root.
    The residual gap ε_Root - ε_input - rho_Delta - ε_band absorbs point_coeff.
    Conclusion preserves +ε_band slack for the separate square-band factor.
    Use point_to_root_with_band to compose with square_band_threshold. -/
lemma point_to_root_threshold
    (point_coeff : ℝ → ℝ)
    (ε_input rho_Delta ε_band ε_Root : ℝ)
    (hε_input_nonneg : 0 ≤ ε_input) (hrho_Delta_nonneg : 0 ≤ rho_Delta)
    (hε_band_nonneg : 0 ≤ ε_band) (hε_Root_pos : 0 < ε_Root)
    (h_sum : ε_input + rho_Delta + ε_band < ε_Root)
    (C0 A : ℝ) (hC0_nonneg : 0 ≤ C0) (hA_pos : 0 < A)
    (h_coeff_bound : ∃ δ₁ > 0, ∀ δ, 0 < δ → δ ≤ δ₁ →
      point_coeff δ ≤ C0 * (Real.log (1 / δ)) ^ A) :
    ∃ (δ₀_point : ℝ), 0 < δ₀_point ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀_point →
        point_coeff δ * δ ^ (-ε_input) * δ ^ (-rho_Delta) ≤ δ ^ (-ε_Root + ε_band) := by
  rcases h_coeff_bound with ⟨δ₁, hδ₁_pos, h1⟩
  let ε_gap : ℝ := ε_Root - ε_input - rho_Delta - ε_band
  have hε_gap_pos : 0 < ε_gap := by linarith
  rcases polylog_absorption_threshold C0 A ε_gap hA_pos hε_gap_pos hC0_nonneg
    with ⟨δ₂, hδ₂_pos, hδ₂_le_one, h2⟩
  let δ₀_point := min δ₁ δ₂
  have hδ₀_pos : 0 < δ₀_point := by positivity
  refine ⟨δ₀_point, hδ₀_pos, fun δ hδ_pos hδ_le => ?_⟩
  have hδ_le_1 : δ ≤ δ₁ := le_trans hδ_le (min_le_left _ _)
  have hδ_le_2 : δ ≤ δ₂ := le_trans hδ_le (min_le_right _ _)
  have h3 : point_coeff δ ≤ C0 * (Real.log (1 / δ)) ^ A := h1 δ hδ_pos hδ_le_1
  have h4 : C0 * (Real.log (1 / δ)) ^ A ≤ δ ^ (-ε_gap) := h2 δ hδ_pos hδ_le_2
  have h5 : point_coeff δ * δ ^ (-ε_input) * δ ^ (-rho_Delta) ≤
      (C0 * (Real.log (1 / δ)) ^ A) * δ ^ (-ε_input) * δ ^ (-rho_Delta) := by gcongr
  have h6 : (C0 * (Real.log (1 / δ)) ^ A) * δ ^ (-ε_input) * δ ^ (-rho_Delta) ≤
      δ ^ (-ε_gap) * δ ^ (-ε_input) * δ ^ (-rho_Delta) := by gcongr
  have h7 : δ ^ (-ε_gap) * δ ^ (-ε_input) * δ ^ (-rho_Delta) = δ ^ (-ε_Root + ε_band) := by
    have h8 : δ ^ (-ε_gap) * δ ^ (-ε_input) = δ ^ (-ε_gap - ε_input) := by
      rw [← Real.rpow_add hδ_pos] <;> ring_nf
    have h9 : δ ^ (-ε_gap - ε_input) * δ ^ (-rho_Delta) = δ ^ (-ε_gap - ε_input - rho_Delta) := by
      rw [← Real.rpow_add hδ_pos] <;> ring_nf
    rw [h8, h9]
    have h10 : -ε_gap - ε_input - rho_Delta = -ε_Root + ε_band := by
      dsimp only [ε_gap] <;> ring
    rw [h10]
  have h8 : (C0 * (Real.log (1 / δ)) ^ A) * δ ^ (-ε_input) * δ ^ (-rho_Delta) ≤
      δ ^ (-ε_Root + ε_band) := by
    calc (C0 * (Real.log (1 / δ)) ^ A) * δ ^ (-ε_input) * δ ^ (-rho_Delta)
      ≤ δ ^ (-ε_gap) * δ ^ (-ε_input) * δ ^ (-rho_Delta) := h6
    _ = δ ^ (-ε_Root + ε_band) := h7
  exact h5.trans h8

/-- Ledger B: fibre-to-lambda threshold.

    Absorbs fibre-side constant factors into δ^(-(lam - ε_input)).
    If the total fibre loss constant C_fibre is fixed (independent of δ),
    this is just constant absorption. -/
lemma fibre_to_lambda_threshold
    (C_fibre : ℝ) (hC_fibre_nonneg : 0 ≤ C_fibre)
    (lam ε_input : ℝ) (hε_input_pos : 0 < ε_input) (hε_input_lt_lam : ε_input < lam) :
    ∃ (δ₀_fibre : ℝ), 0 < δ₀_fibre ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀_fibre →
        C_fibre ≤ δ ^ (-(lam - ε_input)) := by
  have hgap_pos : 0 < lam - ε_input := by linarith
  rcases constant_absorption_threshold C_fibre (lam - ε_input) hC_fibre_nonneg hgap_pos
    with ⟨δ₀, hδ₀_pos, h⟩
  exact ⟨δ₀, hδ₀_pos, h⟩

/-- Square band ledger threshold.

    Absorbs the 9*(K_band(δ)+1) factor into δ^(-ε_band).
    If K_band grows at most polylogarithmically, use polylog_absorption. -/
lemma square_band_threshold
    (ε_band : ℝ) (hε_band_pos : 0 < ε_band)
    (K_band : ℝ → ℕ)
    (C0 A : ℝ) (hC0_nonneg : 0 ≤ C0) (hA_pos : 0 < A)
    (h_growth : ∃ δ₁ > 0, ∀ δ, 0 < δ → δ ≤ δ₁ →
      (K_band δ : ℝ) ≤ C0 * (Real.log (1 / δ)) ^ A) :
    ∃ (δ₀_band : ℝ), 0 < δ₀_band ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀_band →
        9 * ((K_band δ : ℝ) + 1) ≤ δ ^ (-ε_band) := by
  rcases h_growth with ⟨δ₁, hδ₁_pos, h1⟩
  let C0' : ℝ := 9 * (C0 + 1)
  have hC0'_nonneg : 0 ≤ C0' := by positivity
  rcases polylog_absorption_threshold C0' A ε_band hA_pos hε_band_pos hC0'_nonneg
    with ⟨δ₂, hδ₂_pos, hδ₂_le_one, h2⟩
  let δ₃ : ℝ := Real.exp (-1)
  have hδ₃_pos : 0 < δ₃ := by positivity
  let δ₀_band := min (min δ₁ δ₂) δ₃
  have hδ₀_band_pos : 0 < δ₀_band := by positivity
  refine ⟨δ₀_band, hδ₀_band_pos, fun δ hδ_pos hδ_le => ?_⟩
  have hδ_le_1 : δ ≤ δ₁ := by
    exact le_trans hδ_le (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ_le_2 : δ ≤ δ₂ := by
    exact le_trans hδ_le (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ_le_3 : δ ≤ δ₃ := by
    exact le_trans hδ_le (min_le_right _ _)
  have h3 : (K_band δ : ℝ) ≤ C0 * (Real.log (1 / δ)) ^ A := h1 δ hδ_pos hδ_le_1
  have hlog_ge_one : 1 ≤ Real.log (1 / δ) := by
    have h4 : δ ≤ δ₃ := hδ_le_3
    have h5 : 1 / δ ≥ Real.exp 1 := by
      have h6 : δ ≤ Real.exp (-1) := h4
      have h7 : 0 < δ := hδ_pos
      have h8 : 1 / δ ≥ 1 / Real.exp (-1) := one_div_le_one_div_of_le h7 h6
      have h9 : 1 / Real.exp (-1) = Real.exp 1 := by
        simp [Real.exp_neg]
        <;> ring
      rw [h9] at h8
      exact h8
    have h10 : Real.log (1 / δ) ≥ Real.log (Real.exp 1) := Real.log_le_log (by positivity) h5
    have h11 : Real.log (Real.exp 1) = 1 := by simp
    linarith
  have h9 : (1 : ℝ) ≤ (Real.log (1 / δ)) ^ A := by
    have h10 : (1 : ℝ) ≤ Real.log (1 / δ) := hlog_ge_one
    have h11 : (Real.log (1 / δ)) ^ A ≥ (1 : ℝ) ^ A := by gcongr
    have h12 : (1 : ℝ) ^ A = 1 := by simp
    linarith
  have h4 : 9 * ((K_band δ : ℝ) + 1) ≤ C0' * (Real.log (1 / δ)) ^ A := by
    have h5 : 9 * ((K_band δ : ℝ) + 1) ≤ 9 * (C0 * (Real.log (1 / δ)) ^ A + 1) := by gcongr
    have h6 : 9 * (C0 * (Real.log (1 / δ)) ^ A + 1) ≤ 9 * (C0 + 1) * (Real.log (1 / δ)) ^ A := by
      have h7 : (1 : ℝ) ≤ (Real.log (1 / δ)) ^ A := h9
      nlinarith
    dsimp only [C0'] at *
    <;> linarith
  have h10 : C0' * (Real.log (1 / δ)) ^ A ≤ δ ^ (-ε_band) := h2 δ hδ_pos hδ_le_2
  exact h4.trans h10

/-- Composition: point ledger + square band → full δ^(-ε_Root) bound.

    Composes point_to_root_threshold (which preserves +ε_band slack)
    with square_band_threshold (which absorbs 9*(K_band+1) into δ^(-ε_band)).
    The product gives exactly δ^(-ε_Root) with no remaining slack. -/
lemma point_to_root_with_band
    (point_coeff : ℝ → ℝ)
    (K_band : ℝ → ℕ)
    (ε_input rho_Delta ε_band ε_Root : ℝ)
    (hε_input_nonneg : 0 ≤ ε_input) (hrho_Delta_nonneg : 0 ≤ rho_Delta)
    (hε_band_pos : 0 < ε_band) (hε_Root_pos : 0 < ε_Root)
    (h_sum : ε_input + rho_Delta + ε_band < ε_Root)
    (C0 A : ℝ) (hC0_nonneg : 0 ≤ C0) (hA_pos : 0 < A)
    (h_coeff_bound : ∃ δ₁ > 0, ∀ δ, 0 < δ → δ ≤ δ₁ →
      point_coeff δ ≤ C0 * (Real.log (1 / δ)) ^ A)
    (C0_band A_band : ℝ) (hC0_band_nonneg : 0 ≤ C0_band) (hA_band_pos : 0 < A_band)
    (h_growth : ∃ δ₂ > 0, ∀ δ, 0 < δ → δ ≤ δ₂ →
      (K_band δ : ℝ) ≤ C0_band * (Real.log (1 / δ)) ^ A_band) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
        point_coeff δ * δ ^ (-ε_input) * δ ^ (-rho_Delta) *
          (9 * ((K_band δ : ℝ) + 1)) ≤ δ ^ (-ε_Root) := by
  rcases point_to_root_threshold point_coeff ε_input rho_Delta ε_band ε_Root
      hε_input_nonneg hrho_Delta_nonneg hε_band_pos.le hε_Root_pos h_sum
      C0 A hC0_nonneg hA_pos h_coeff_bound
    with ⟨δ₁, hδ₁_pos, h_point⟩
  rcases square_band_threshold ε_band hε_band_pos K_band
      C0_band A_band hC0_band_nonneg hA_band_pos h_growth
    with ⟨δ₂, hδ₂_pos, h_band⟩
  let δ₀ := min δ₁ δ₂
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_le => ?_⟩
  have hδ_le_1 : δ ≤ δ₁ := le_trans hδ_le (min_le_left _ _)
  have hδ_le_2 : δ ≤ δ₂ := le_trans hδ_le (min_le_right _ _)
  have h1 : point_coeff δ * δ ^ (-ε_input) * δ ^ (-rho_Delta) ≤ δ ^ (-ε_Root + ε_band) :=
    h_point δ hδ_pos hδ_le_1
  have h2 : 9 * ((K_band δ : ℝ) + 1) ≤ δ ^ (-ε_band) := h_band δ hδ_pos hδ_le_2
  have h3 : point_coeff δ * δ ^ (-ε_input) * δ ^ (-rho_Delta) * (9 * ((K_band δ : ℝ) + 1)) ≤
      δ ^ (-ε_Root + ε_band) * δ ^ (-ε_band) := by gcongr
  have h4 : δ ^ (-ε_Root + ε_band) * δ ^ (-ε_band) = δ ^ (-ε_Root) := by
    rw [← Real.rpow_add hδ_pos] <;> ring_nf
  rw [h4] at h3
  exact h3

/-- Ambient ledger threshold.

    Absorbs a fixed ambient constant K_ambient into δ^(-ρ_T). -/
lemma ambient_threshold
    (K_ambient ρ_T : ℝ) (hK_ambient_nonneg : 0 ≤ K_ambient) (hρ_T_pos : 0 < ρ_T) :
    ∃ (δ₀_ambient : ℝ), 0 < δ₀_ambient ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀_ambient →
        K_ambient ≤ δ ^ (-ρ_T) := by
  rcases constant_absorption_threshold K_ambient ρ_T hK_ambient_nonneg hρ_T_pos
    with ⟨δ₀, hδ₀_pos, h⟩
  exact ⟨δ₀, hδ₀_pos, h⟩

/-- Final transfer threshold (CORRECTED direction).

    Gives δ₀ > 0 such that for all 0 < δ ≤ δ₀:
      δ^(ε_section9 - ε_target) ≤ C_fixed

    This ensures C_fixed * δ^(-(2s+ε_section9)) ≥ δ^(-(2s+ε_target)),
    which is the fixed-coefficient payment at the end of Section 9.

    Explicit threshold: δ₀ = C_fixed^(1/(ε_section9 - ε_target)). -/
lemma final_transfer_threshold
    (C_fixed ε_section9 ε_target : ℝ) (hC_fixed_pos : 0 < C_fixed)
    (hε_target_lt_section9 : ε_target < ε_section9) :
    ∃ (δ₀_final : ℝ), 0 < δ₀_final ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀_final →
        δ ^ (ε_section9 - ε_target) ≤ C_fixed := by
  have hgap_pos : 0 < ε_section9 - ε_target := by linarith
  let ε_gap : ℝ := ε_section9 - ε_target
  let δ₀_final : ℝ := C_fixed ^ (1 / ε_gap)
  have hδ₀_pos : 0 < δ₀_final := Real.rpow_pos_of_pos hC_fixed_pos _
  have h_main : δ₀_final ^ ε_gap = C_fixed := by
    have hlog1 : Real.log (δ₀_final ^ ε_gap) = ε_gap * Real.log δ₀_final :=
      Real.log_rpow hδ₀_pos ε_gap
    have hlog2 : Real.log δ₀_final = (1 / ε_gap) * Real.log C_fixed := by
      rw [Real.log_rpow hC_fixed_pos] <;> ring
    have hlog3 : Real.log (δ₀_final ^ ε_gap) = Real.log C_fixed := by
      rw [hlog1, hlog2]
      have h4 : ε_gap * ((1 / ε_gap) * Real.log C_fixed) = Real.log C_fixed := by
        have h5 : ε_gap ≠ 0 := hgap_pos.ne'
        field_simp [h5] <;> ring
      exact h4
    have hpos1 : 0 < δ₀_final ^ ε_gap := Real.rpow_pos_of_pos hδ₀_pos _
    have hpos2 : 0 < C_fixed := hC_fixed_pos
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr hpos1) (Set.mem_Ioi.mpr hpos2) hlog3
  refine ⟨δ₀_final, hδ₀_pos, fun δ hδ_pos hδ_le => ?_⟩
  have h1 : δ ^ ε_gap ≤ δ₀_final ^ ε_gap := Real.rpow_le_rpow (by linarith) hδ_le (by linarith)
  rw [h_main] at h1
  exact h1

/-- Pullback threshold conversion: if δ ≤ 4*Δ*θ_d and δ_d ≤ δ/(4*Δ), then δ_d ≤ θ_d.

    Used to derive the dyadic-scale threshold condition (dyadicDelta k ≤ δ₀)
    from a source-scale threshold δ ≤ θ_d, given the nearby-power relations
    δ/4 ≤ δ_d ≤ δ/(4*Δ). -/
lemma pullback_threshold
    (Δ : ℝ) (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (θ_d : ℝ) (hθ_d_pos : 0 < θ_d)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (hδ_le : δ ≤ 4 * Δ * θ_d)
    (δ_d : ℝ)
    (hδ_d_upper : δ_d ≤ δ / (4 * Δ))
    (hδ_d_lower : δ / 4 ≤ δ_d) :
    δ_d ≤ θ_d := by
  have h_pos : 0 < 4 * Δ := by positivity
  calc δ_d ≤ δ / (4 * Δ) := hδ_d_upper
       _ ≤ (4 * Δ * θ_d) / (4 * Δ) := by gcongr
       _ = θ_d := by
         field_simp [h_pos.ne'] <;> ring

end DirecretisedFurstenbergEstimate.Section9
