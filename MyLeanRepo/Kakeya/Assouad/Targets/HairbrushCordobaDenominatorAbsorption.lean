import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.Subunit.AsymptoticHelper

/-!
# Fixed-stem Córdoba denominator absorption

This is the asymptotic algebra recovering the homogeneous radius factor from
`farRadius = farFraction * sigma * radius` while absorbing the Katz--Tao and
logarithmic denominators into a prescribed strict delta-power loss.

Whiteprint node: `CordobaDenominatorAbsorption`.
-/

namespace Kakeya.Assouad

theorem hairbrush_cordoba_denominator_absorption :
    HairbrushCordobaDenominatorAbsorptionStatement := by
  intro katzExponent outputLoss farFraction densityFraction hkatz_nonneg hstrict hfar_pos hdens_pos
  set gap : ℝ := outputLoss - katzExponent with hgap_def
  have hgap_pos : 0 < gap := by linarith
  set ε : ℝ := gap / 2 with hε_def
  have hε_pos : 0 < ε := by linarith
  set C_katz : ℝ := 2000 * (3 : ℝ) * 32 * Real.pi with hC_katz_def
  have hC_katz_pos : 0 < C_katz := by positivity
  set C_far : ℝ := 100 * (1 / farFraction + 2) with hC_far_def
  have hC_far_pos : 0 < C_far := by positivity
  set C_log : ℝ := 1 + 1 / ε with hC_log_def
  have hC_log_pos : 0 < C_log := by positivity
  set C_total : ℝ := C_far * (1 + C_katz) * C_log with hC_total_def
  have hC_total_pos : 0 < C_total := by positivity
  set C_ratio : ℝ := C_total / densityFraction^2 with hC_ratio_def
  have hC_ratio_pos : 0 < C_ratio := by positivity

  -- Step 1: threshold from asymptotic helper
  obtain ⟨δ₁, hδ₁_pos, hδ₁_le_one, hδ₁_bound⟩ :=
    Subunit.exists_delta₀_mul_pow_le_one C_ratio hC_ratio_pos ε hε_pos

  set δ₀ : ℝ := min δ₁ (1 / 1000) with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_le_δ₁ : δ₀ ≤ δ₁ := min_le_left _ _
  have hδ₀_le_thousand : δ₀ ≤ 1 / 1000 := min_le_right _ _

  refine ⟨δ₀, hδ₀_pos, hδ₀_le_thousand, ?_⟩
  intro δ hδ_pos hδ_le katzTaoConstant hkt_nonneg hkt_bound
        sigma radius farRadius hsigma_pos hradius_ge hradius_le hfar_eq

  have hradius_pos : 0 < radius := by linarith
  have hδ_le_one : δ ≤ 1 := by linarith [hδ_le, hδ₀_le_thousand]
  have hδ_le_δ₁ : δ ≤ δ₁ := hδ_le.trans hδ₀_le_δ₁

  -- katzTaoConstant ≤ δ^(-katzExponent) in Real
  have hkt_real : katzTaoConstant ≤ Real.rpow δ (-katzExponent) := by
    have h : ENNReal.ofReal katzTaoConstant ≤ ENNReal.ofReal (Real.rpow δ (-katzExponent)) := by
      simpa [Kakeya.realRpowENN] using hkt_bound
    have h' : 0 ≤ Real.rpow δ (-katzExponent) := (Real.rpow_pos_of_pos hδ_pos _).le
    exact (ENNReal.ofReal_le_ofReal_iff h').mp h

  -- log(1/δ) > 0
  have hlog_pos : 0 < Real.log (1 / δ) := by
    have h1 : 1 < 1 / δ := by
      apply one_lt_one_div hδ_pos
      linarith
    exact Real.log_pos h1

  -- δ^(-katzExponent) ≥ 1
  have h_rpow_kt_ge_one : 1 ≤ Real.rpow δ (-katzExponent) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ_pos hδ_le_one (by linarith)

  -- δ^(-ε) ≥ 1
  have h_rpow_ε_ge_one : 1 ≤ Real.rpow δ (-ε) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ_pos hδ_le_one (by linarith)

  -- sigma / farRadius = 1 / (farFraction * radius)
  have h_simp : sigma / farRadius = 1 / (farFraction * radius) := by
    rw [hfar_eq]
    field_simp [hsigma_pos.ne', hfar_pos.ne', hradius_pos.ne']

  -- Step 2: radius * 100 * (sigma/farRadius + 1) ≤ C_far
  have h_far_bound : radius * (100 * (sigma / farRadius + 1)) ≤ C_far := by
    rw [h_simp]
    have h : radius * (100 * (1 / (farFraction * radius) + 1)) =
        100 * (1 / farFraction + radius) := by
      field_simp [hfar_pos.ne', hradius_pos.ne']
    rw [h]
    have h2 : 100 * (1 / farFraction + radius) ≤ C_far := by
      simp only [hC_far_def]
      gcongr
    exact h2

  -- Define real-valued denominator
  set D_real : ℝ := 1 + C_katz * katzTaoConstant * Real.log (1 / δ) with hD_real_def
  have hD_real_nonneg : 0 ≤ D_real := by positivity

  -- Step 3: D_real ≤ (1 + C_katz) * δ^(-katzExponent) * (1 + log(1/δ))
  have h_plus_log_nonneg : 0 ≤ 1 + Real.log (1 / δ) := by linarith [hlog_pos]
  have hD_bound : D_real ≤
      (1 + C_katz) * Real.rpow δ (-katzExponent) * (1 + Real.log (1 / δ)) := by
    have h5 : C_katz * katzTaoConstant * Real.log (1 / δ) ≤
        C_katz * Real.rpow δ (-katzExponent) * Real.log (1 / δ) := by
      gcongr
    have h6 : 1 ≤ Real.rpow δ (-katzExponent) * (1 + Real.log (1 / δ)) := by
      have h61 : 1 ≤ Real.rpow δ (-katzExponent) := h_rpow_kt_ge_one
      have h62 : 1 ≤ 1 + Real.log (1 / δ) := by linarith
      have h63 : 0 ≤ Real.rpow δ (-katzExponent) := by positivity
      nlinarith
    have h7 : C_katz * Real.rpow δ (-katzExponent) * Real.log (1 / δ) ≤
        C_katz * Real.rpow δ (-katzExponent) * (1 + Real.log (1 / δ)) := by
      have h71 : Real.log (1 / δ) ≤ 1 + Real.log (1 / δ) := by linarith
      have h72 : 0 ≤ C_katz * Real.rpow δ (-katzExponent) := by positivity
      exact mul_le_mul_of_nonneg_left h71 h72
    have h8 : 1 + C_katz * Real.rpow δ (-katzExponent) * Real.log (1 / δ) ≤
        (1 + C_katz) * Real.rpow δ (-katzExponent) * (1 + Real.log (1 / δ)) := by
      nlinarith
    calc D_real
      = 1 + C_katz * katzTaoConstant * Real.log (1 / δ) := by rw [hD_real_def]
    _ ≤ 1 + C_katz * Real.rpow δ (-katzExponent) * Real.log (1 / δ) := by gcongr
    _ ≤ (1 + C_katz) * Real.rpow δ (-katzExponent) * (1 + Real.log (1 / δ)) := h8

  -- Step 4: 1 + log(1/δ) ≤ C_log * δ^(-ε)
  have h_inv_rpow : (1 / δ) ^ ε = Real.rpow δ (-ε) := by
    have h3 : (1 / δ) ^ ε = (Real.rpow δ ε)⁻¹ := by
      have h4 : (1 / δ) = δ⁻¹ := by ring
      rw [h4]
      exact Real.inv_rpow hδ_pos.le ε
    have h4 : (Real.rpow δ ε)⁻¹ = Real.rpow δ (-ε) := by
      exact (Real.rpow_neg hδ_pos.le ε).symm
    rw [h3, h4]
  have hlog_bound : 1 + Real.log (1 / δ) ≤ C_log * Real.rpow δ (-ε) := by
    have h1 : Real.log (1 / δ) ≤ (1 / δ) ^ ε / ε :=
      Real.log_le_rpow_div (by positivity) hε_pos
    rw [h_inv_rpow] at h1
    have h4 : 1 ≤ Real.rpow δ (-ε) := h_rpow_ε_ge_one
    have h5 : 1 + Real.log (1 / δ) ≤ Real.rpow δ (-ε) + Real.rpow δ (-ε) / ε := by linarith
    have h6 : Real.rpow δ (-ε) + Real.rpow δ (-ε) / ε = C_log * Real.rpow δ (-ε) := by
      simp [hC_log_def] <;> ring
    rw [h6] at h5
    exact h5

  -- C_ratio * δ^ε ≤ 1
  have h_helper : C_ratio * Real.rpow δ ε ≤ 1 := hδ₁_bound δ hδ_pos hδ_le_δ₁

  -- Step 5: main real inequality
  set P : ℝ := D_real * (100 * (sigma / farRadius + 1)) with hP_def
  have hfarRadius_pos : 0 < farRadius := by
    rw [hfar_eq] <;> positivity
  have hD_real_pos : 0 < D_real := by
    rw [hD_real_def]
    have h2 : 0 ≤ C_katz * katzTaoConstant * Real.log (1 / δ) := by
      have h3 : 0 ≤ Real.log (1 / δ) := hlog_pos.le
      positivity
    linarith
  have hP_pos : 0 < P := by
    have h1 : 0 < sigma / farRadius := div_pos hsigma_pos hfarRadius_pos
    have h2 : 0 < sigma / farRadius + 1 := by linarith
    have h3 : 0 < 100 * (sigma / farRadius + 1) := by positivity
    exact mul_pos hD_real_pos h3

  -- rpow multiplication identities
  have h_rpow1 : Real.rpow δ outputLoss * Real.rpow δ (-katzExponent) =
      Real.rpow δ (outputLoss - katzExponent) := by
    have h := Real.rpow_add hδ_pos outputLoss (-katzExponent)
    have h' : outputLoss + (-katzExponent) = outputLoss - katzExponent := by ring
    rw [h'] at h
    exact h.symm
  have h_rpow2 : Real.rpow δ (outputLoss - katzExponent) * Real.rpow δ (-ε) =
      Real.rpow δ ε := by
    have h := Real.rpow_add hδ_pos (outputLoss - katzExponent) (-ε)
    have h' : (outputLoss - katzExponent) + (-ε) = ε := by
      linarith [hgap_def, hε_def]
    rw [h'] at h
    exact h.symm

  have h_main_real : Real.rpow δ outputLoss * radius * P ≤ densityFraction^2 := by
    have h7 : Real.rpow δ outputLoss * radius * P =
        Real.rpow δ outputLoss * (D_real * (radius * (100 * (sigma / farRadius + 1)))) := by
      simp [hP_def] <;> ring
    rw [h7]

    set A : ℝ := Real.rpow δ outputLoss with hA_def
    set B : ℝ := D_real with hB_def
    set C : ℝ := radius * (100 * (sigma / farRadius + 1)) with hC_def
    set D : ℝ := (1 + C_katz) * Real.rpow δ (-katzExponent) * (1 + Real.log (1 / δ)) with hD_def
    set E : ℝ := C_far with hE_def
    set D' : ℝ := (1 + C_katz) * Real.rpow δ (-katzExponent) * (C_log * Real.rpow δ (-ε)) with hD'_def

    have hA_nonneg : 0 ≤ A := (Real.rpow_pos_of_pos hδ_pos _).le
    have hB_nonneg : 0 ≤ B := hD_real_nonneg
    have hC_nonneg : 0 ≤ C := by
      have h2 : 0 < sigma / farRadius := div_pos hsigma_pos hfarRadius_pos
      have h3 : 0 < sigma / farRadius + 1 := by linarith
      have h4 : 0 < 100 * (sigma / farRadius + 1) := by positivity
      exact mul_nonneg hradius_pos.le h4.le
    have hD_nonneg : 0 ≤ D := by
      have h1 : 0 ≤ 1 + Real.log (1 / δ) := by linarith [hlog_pos]
      positivity
    have hE_nonneg : 0 ≤ E := hC_far_pos.le
    have hD'_nonneg : 0 ≤ D' := by positivity

    have hBC_le_DE : B * C ≤ D * E := mul_le_mul hD_bound h_far_bound hC_nonneg hD_nonneg
    have h8 : A * (B * C) ≤ A * (D * E) := mul_le_mul_of_nonneg_left hBC_le_DE hA_nonneg

    have hD_le_D' : D ≤ D' := by
      simp only [hD_def, hD'_def]
      have h9 : 1 + Real.log (1 / δ) ≤ C_log * Real.rpow δ (-ε) := hlog_bound
      have h10 : 0 ≤ (1 + C_katz) * Real.rpow δ (-katzExponent) := by positivity
      exact mul_le_mul_of_nonneg_left h9 h10
    have h11 : A * (D * E) ≤ A * (D' * E) := by
      have h12 : D * E ≤ D' * E := mul_le_mul_of_nonneg_right hD_le_D' hE_nonneg
      exact mul_le_mul_of_nonneg_left h12 hA_nonneg

    have h13 : A * (D' * E) = C_total * Real.rpow δ ε := by
      have h14 : Real.rpow δ outputLoss * Real.rpow δ (-katzExponent) * Real.rpow δ (-ε) =
          Real.rpow δ ε := by
        calc
          Real.rpow δ outputLoss * Real.rpow δ (-katzExponent) * Real.rpow δ (-ε)
            = (Real.rpow δ outputLoss * Real.rpow δ (-katzExponent)) * Real.rpow δ (-ε) := by ring
          _ = Real.rpow δ (outputLoss - katzExponent) * Real.rpow δ (-ε) := by rw [h_rpow1]
          _ = Real.rpow δ ε := h_rpow2
      have h_expand : A * (D' * E) =
          (1 + C_katz) * C_log * C_far * (Real.rpow δ outputLoss * Real.rpow δ (-katzExponent) * Real.rpow δ (-ε)) := by
        simp only [hA_def, hD'_def, hE_def] <;> ring
      rw [h_expand, h14]
      have h_total : (1 + C_katz) * C_log * C_far = C_total := by
        simp [hC_total_def] <;> ring
      rw [h_total]

    have h15 : C_total * Real.rpow δ ε ≤ densityFraction^2 := by
      have h16 : densityFraction^2 * C_ratio = C_total := by
        simp [hC_ratio_def] <;> field_simp [hdens_pos.ne']
      have h17 : C_total * Real.rpow δ ε =
          densityFraction^2 * (C_ratio * Real.rpow δ ε) := by
        calc
          C_total * Real.rpow δ ε
            = (densityFraction^2 * C_ratio) * Real.rpow δ ε := by rw [h16]
          _ = densityFraction^2 * (C_ratio * Real.rpow δ ε) := by ring
      rw [h17]
      have h17 : 0 ≤ densityFraction^2 := by positivity
      have h18 : densityFraction^2 * (C_ratio * Real.rpow δ ε) ≤ densityFraction^2 := by
        calc
          densityFraction^2 * (C_ratio * Real.rpow δ ε)
            ≤ densityFraction^2 * 1 := mul_le_mul_of_nonneg_left h_helper h17
          _ = densityFraction^2 := by ring
      exact h18

    calc A * (B * C)
      ≤ A * (D * E) := h8
    _ ≤ A * (D' * E) := h11
    _ = C_total * Real.rpow δ ε := h13
    _ ≤ densityFraction^2 := h15

  -- Step 6: lift to ENNReal
  have hD_ennreal : hairbrushFixedStemCordobaDenominator δ katzTaoConstant =
      ENNReal.ofReal D_real := by
    rw [hairbrushFixedStemCordobaDenominator]
    have h_nonneg1 : 0 ≤ 2000 * (3 : ℝ) * katzTaoConstant * 32 * Real.pi := by positivity
    have h_prod : ENNReal.ofReal (2000 * (3 : ℝ) * katzTaoConstant * 32 * Real.pi) *
        ENNReal.ofReal (Real.log (1 / δ)) =
        ENNReal.ofReal (C_katz * katzTaoConstant * Real.log (1 / δ)) := by
      have h_nonneg_log : 0 ≤ Real.log (1 / δ) := by linarith [hlog_pos]
      have h_eq : (2000 * (3 : ℝ) * katzTaoConstant * 32 * Real.pi) * Real.log (1 / δ) =
          C_katz * katzTaoConstant * Real.log (1 / δ) := by
        have h2 : C_katz = 2000 * (3 : ℝ) * 32 * Real.pi := hC_katz_def
        calc
          (2000 * (3 : ℝ) * katzTaoConstant * 32 * Real.pi) * Real.log (1 / δ)
            = (2000 * (3 : ℝ) * 32 * Real.pi * katzTaoConstant) * Real.log (1 / δ) := by ring
          _ = (C_katz * katzTaoConstant) * Real.log (1 / δ) := by rw [h2]
          _ = C_katz * katzTaoConstant * Real.log (1 / δ) := by ring
      rw [← ENNReal.ofReal_mul h_nonneg1, h_eq]
    rw [h_prod]
    have h_nonneg2 : 0 ≤ C_katz * katzTaoConstant * Real.log (1 / δ) := by positivity
    have h_sum : (1 : ENNReal) + ENNReal.ofReal (C_katz * katzTaoConstant * Real.log (1 / δ)) =
        ENNReal.ofReal D_real := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by positivity) h_nonneg2]
    exact h_sum

  have h_denom : hairbrushFixedStemCordobaDenominator δ katzTaoConstant *
      ENNReal.ofReal (100 * (sigma / farRadius + 1)) = ENNReal.ofReal P := by
    rw [hD_ennreal]
    have h13 : ENNReal.ofReal D_real * ENNReal.ofReal (100 * (sigma / farRadius + 1)) =
        ENNReal.ofReal P := by
      rw [← ENNReal.ofReal_mul hD_real_nonneg] <;> rfl
    exact h13

  rw [h_denom]
  have h14 : (ENNReal.ofReal P)⁻¹ = ENNReal.ofReal (P⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hP_pos]
  rw [h14]

  have h15 : Kakeya.realRpowENN δ outputLoss * ENNReal.ofReal radius =
      ENNReal.ofReal (Real.rpow δ outputLoss * radius) := by
    have h_nonneg : 0 ≤ Real.rpow δ outputLoss := (Real.rpow_pos_of_pos hδ_pos _).le
    have h_def : Kakeya.realRpowENN δ outputLoss = ENNReal.ofReal (Real.rpow δ outputLoss) := by
      simp [Kakeya.realRpowENN]
    rw [h_def]
    exact (ENNReal.ofReal_mul h_nonneg).symm

  have h16 : ENNReal.ofReal densityFraction ^ 2 * ENNReal.ofReal (P⁻¹) =
      ENNReal.ofReal (densityFraction^2 / P) := by
    have h17 : ENNReal.ofReal densityFraction ^ 2 = ENNReal.ofReal (densityFraction^2) := by
      have h_nonneg : 0 ≤ densityFraction := by linarith
      have h1 : ENNReal.ofReal densityFraction ^ 2 = ENNReal.ofReal densityFraction * ENNReal.ofReal densityFraction := by
        simp [pow_two]
      rw [h1]
      have h2 : ENNReal.ofReal densityFraction * ENNReal.ofReal densityFraction = ENNReal.ofReal (densityFraction * densityFraction) :=
        (ENNReal.ofReal_mul h_nonneg).symm
      rw [h2]
      have h3 : densityFraction * densityFraction = densityFraction ^ 2 := by ring
      rw [h3]
    rw [h17]
    have h18 : ENNReal.ofReal (densityFraction^2) * ENNReal.ofReal (P⁻¹) =
        ENNReal.ofReal (densityFraction^2 * P⁻¹) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    rw [h18]
    have h19 : densityFraction^2 * P⁻¹ = densityFraction^2 / P := by
      field_simp [hP_pos.ne'] <;> ring
    rw [h19]

  rw [h15, h16]
  have h18 : Real.rpow δ outputLoss * radius ≤ densityFraction^2 / P := by
    have h19 : Real.rpow δ outputLoss * radius * P ≤ densityFraction^2 := h_main_real
    have h20 : 0 < P := hP_pos
    calc Real.rpow δ outputLoss * radius
      = (Real.rpow δ outputLoss * radius * P) / P := by field_simp [h20.ne'] <;> ring
    _ ≤ densityFraction^2 / P := by gcongr
  have h_final : ENNReal.ofReal (Real.rpow δ outputLoss * radius) ≤
      ENNReal.ofReal (densityFraction^2 / P) :=
    ENNReal.ofReal_mono h18
  exact h_final

end Kakeya.Assouad
