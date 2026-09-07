import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.LensEndpointEnlargementAbsorptionInputs

namespace Kakeya.Cinematic

theorem lens_endpoint_enlargement_absorption :
    LensEndpointEnlargementAbsorptionStatement := by
  intro K tangency C hK htang hC hKC
  set V : ℝ := 25 * tangency ^ 10 + 2 * tangency + 2 with hV
  set E : ℝ := 12 * K * (V + 1) + Real.sqrt (6 * K * V) with hE
  have h_t1 : tangency ≥ 1 := by linarith
  have h_K0 : 0 ≤ K := by linarith
  have h_t0 : 0 ≤ tangency := by linarith
  have h_t10 : (1 : ℝ) ≤ tangency ^ 10 := by
    have h : (1 : ℝ) ^ 10 ≤ tangency ^ 10 := by gcongr
    simpa using h
  have h_t5 : tangency ^ 5 ≤ tangency ^ 10 :=
    pow_le_pow_right₀ h_t1 (by norm_num)
  have h9 : tangency ^ 9 ≥ 3 := by
    have h10 : tangency ^ 9 ≥ 5 ^ 9 := by gcongr
    have h11 : (5 : ℝ) ^ 9 ≥ 3 := by norm_num
    linarith
  have h11 : tangency ^ 10 ≥ 3 * tangency := by
    have h12 : tangency ^ 10 = tangency * tangency ^ 9 := by ring
    rw [h12]
    nlinarith
  have h_extra : 2 * tangency + 2 ≤ tangency ^ 10 := by
    have h13 : 2 * tangency + 2 ≤ 3 * tangency := by linarith
    linarith
  have hV_bound : V ≤ 26 * tangency ^ 10 := by
    simp only [hV]
    linarith
  have hsqrt_bound : Real.sqrt (6 * K * V) ≤ 13 * K * tangency ^ 10 := by
    have h_pos1 : 0 ≤ 6 * K * V := by positivity
    have h_ineq1 : 6 * K * V ≤ 156 * K * tangency ^ 10 := by
      calc
        6 * K * V ≤ 6 * K * (26 * tangency ^ 10) := by gcongr
        _ = 156 * K * tangency ^ 10 := by ring
    have h_sqrt1 : Real.sqrt (6 * K * V) ≤ Real.sqrt (156 * K * tangency ^ 10) :=
      Real.sqrt_le_sqrt h_ineq1
    have h_sqrt2 : Real.sqrt (156 * K * tangency ^ 10) = Real.sqrt (156 * K) * tangency ^ 5 := by
      have h22 : Real.sqrt (156 * K * tangency ^ 10) =
          Real.sqrt (156 * K) * Real.sqrt (tangency ^ 10) := by
        rw [Real.sqrt_mul]
        positivity
      rw [h22]
      have h23 : Real.sqrt (tangency ^ 10) = tangency ^ 5 := by
        have h24 : (tangency ^ 10 : ℝ) = (tangency ^ 5) ^ 2 := by ring
        rw [h24, Real.sqrt_sq_eq_abs, abs_of_nonneg]
        positivity
      rw [h23]
    have h_sqrt3 : Real.sqrt (156 * K) ≤ 13 * K := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    calc
      Real.sqrt (6 * K * V)
        ≤ Real.sqrt (156 * K * tangency ^ 10) := h_sqrt1
      _ = Real.sqrt (156 * K) * tangency ^ 5 := h_sqrt2
      _ ≤ (13 * K) * tangency ^ 5 := by gcongr
      _ = 13 * K * tangency ^ 5 := by ring
      _ ≤ 13 * K * tangency ^ 10 := by nlinarith [h_t5, h_K0]
  have hV1_bound : V + 1 ≤ 27 * tangency ^ 10 := by
    linarith [hV_bound, h_t10]
  have hE_bound : E ≤ 337 * K * tangency ^ 10 := by
    simp only [hE]
    have h1 : 12 * K * (V + 1) ≤ 324 * K * tangency ^ 10 := by
      calc
        12 * K * (V + 1) ≤ 12 * K * (27 * tangency ^ 10) := by gcongr
        _ = 324 * K * tangency ^ 10 := by ring
    linarith [hsqrt_bound]
  have hE_nonneg : 0 ≤ E := by
    simp only [hE]
    positivity
  have h2 : (2 : ℝ) ≤ K * tangency ^ 10 := by
    have h3 : (1 : ℝ) ≤ K * tangency ^ 10 := by
      have h4 : (1 : ℝ) ≤ tangency ^ 10 := h_t10
      nlinarith
    nlinarith
  have h_sum : 2 + 2 * E ≤ 675 * K * tangency ^ 10 := by
    have h3 : 2 * E ≤ 674 * K * tangency ^ 10 := by
      calc
        2 * E ≤ 2 * (337 * K * tangency ^ 10) := by gcongr
        _ = 674 * K * tangency ^ 10 := by ring
    linarith
  have h_sum_nonneg : 0 ≤ 2 + 2 * E := by linarith [hE_nonneg]
  have h_main1 : (2 + 2 * E) ^ 2 ≤ 455625 * K ^ 2 * tangency ^ 20 := by
    have h5 : (2 + 2 * E) ^ 2 ≤ (675 * K * tangency ^ 10) ^ 2 := by
      gcongr
    have h6 : (675 * K * tangency ^ 10) ^ 2 =
        455625 * K ^ 2 * tangency ^ 20 := by ring
    rw [h6] at h5
    exact h5
  have h_KC : 455625 * K ^ 2 ≤ 5 * C := by
    have h1 : 455625 * K ^ 2 ≤ 5 * (100000 * K ^ 2) := by nlinarith
    nlinarith
  have h_main2 : (2 + 2 * E) ^ 2 ≤ 5 * C * tangency ^ 20 := by
    calc
      (2 + 2 * E) ^ 2 ≤ 455625 * K ^ 2 * tangency ^ 20 := h_main1
      _ = (455625 * K ^ 2) * tangency ^ 20 := by ring
      _ ≤ (5 * C) * tangency ^ 20 := by gcongr
      _ = 5 * C * tangency ^ 20 := by ring
  have h_rpow1 : Real.rpow tangency (100 : ℝ) ≤ Real.rpow tangency C :=
    Real.rpow_le_rpow_of_exponent_le h_t1 (by linarith)
  have h_rpow2 : Real.rpow tangency (100 : ℝ) = tangency ^ 100 := by
    simp
  have h4 : (5 : ℝ) ≤ tangency ^ 80 := by
    have h5 : tangency ^ 80 ≥ 5 ^ 80 := by gcongr
    have h6 : (5 : ℝ) ^ 80 ≥ 5 := by norm_num
    linarith
  have h_rpow3 : (5 : ℝ) * tangency ^ 20 ≤ Real.rpow tangency C := by
    calc
      (5 : ℝ) * tangency ^ 20
        ≤ tangency ^ 80 * tangency ^ 20 := by nlinarith [h_t0]
      _ = tangency ^ 100 := by ring
      _ = Real.rpow tangency (100 : ℝ) := by rw [h_rpow2]
      _ ≤ Real.rpow tangency C := h_rpow1
  have h_posC : 0 < C := by linarith
  have h_final : 5 * C * tangency ^ 20 ≤ C * Real.rpow tangency C := by
    calc
      5 * C * tangency ^ 20 = C * (5 * tangency ^ 20) := by ring
      _ ≤ C * Real.rpow tangency C := by gcongr
  linarith [h_main2, h_final]

end Kakeya.Cinematic
