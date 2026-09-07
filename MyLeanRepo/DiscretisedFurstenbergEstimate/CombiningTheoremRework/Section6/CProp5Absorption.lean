module

/-
  C_prop5 absorption with FIXED majorants (no runtime constants).

  Key insight: C_prop5 = (1/K) * log(1/δ_m)^(-K) / (C_P * 13*CΔ*2^s)
  Since δ_m = δ_n^{1/2}, log(1/δ_m)^(-K) = 2^K * log(1/δ_n)^(-K).

  Upper-bound runtime constants by fixed polynomials:
    C_P ≤ δ_n^{-(εReg+pointLoss)} * P_point(n)
    CΔ ≤ δ_n^{-(εReg+tubeLoss)} * P_tube(n)

  Then invert:
    C_prop5 ≥ (2^K/K) * log(1/δ_n)^(-K) * δ_n^{2εReg+pointLoss+tubeLoss}
               / (P_point(n) * P_tube(n) * 13 * 2^s)

  Absorb the combined polynomial P(n) = P_point * P_tube * 13 * 2^s
  by converting n^degree to a power of log(1/δ_n), then use polylog
  absorption on log^{-(K+degree)}.

  The threshold depends ONLY on fixed K, polynomial coefficient/degree,
  and exponent budget — NOT on runtime C_P, CΔ, or data.

  Whiteprint node: coarse_elimination / c_prop5_absorption
  Dependencies: PolylogAbsorption
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.PolylogAbsorption
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

open DiscretisedFurstenbergEstimate

namespace DirecretisedFurstenbergEstimate.Section6

/-- Fixed-threshold C_prop5 absorption.

    Given outer K > 0, fixed polynomial majorant C_poly * n^degree,
    base exponent `a` (typically 2εReg + pointLoss + tubeLoss),
    polylog loss `b`, and target loss_coarse with a + b < loss_coarse:

    Produces δ₀ > 0 such that for all n with dyadicDelta n ≤ δ₀:
      (2^K / K) * log(1/δ_n)^(-K) * δ_n^a / (C_poly * n^degree) ≥ δ_n^{loss_coarse}

    The threshold depends only on K, C_poly, degree, a, b, loss_coarse.
    No runtime constants involved. -/
lemma coarse_prop5_fixed_absorption
    (K C_poly : ℝ) (degree : ℕ)
    (hK_pos : 0 < K)
    (hC_poly_pos : 0 < C_poly)
    (a b loss_coarse : ℝ)
    (hb_pos : 0 < b)
    (h_sum_lt : a + b < loss_coarse) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧
      ∀ (n : ℕ), dyadicDelta n ≤ δ₀ →
        (2^K / K) * Real.log (1 / dyadicDelta n)^(-K) * (dyadicDelta n)^a /
          (C_poly * (n : ℝ)^degree) ≥ (dyadicDelta n)^loss_coarse := by
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKdeg_pos : 0 < K + (degree : ℝ) := by linarith
  have h_n_eq_log : ∀ (n : ℕ), (n : ℝ) = Real.log (1 / dyadicDelta n) / Real.log 2 := by
    intro n
    have h2 : dyadicDelta n = 1 / (2 : ℝ)^n := by
      simp [dyadicDelta] <;> ring
    rw [h2]
    have h3 : Real.log (1 / (1 / (2 : ℝ)^n)) = (n : ℝ) * Real.log 2 := by
      have h4 : 1 / (1 / (2 : ℝ)^n) = (2 : ℝ)^n := by
        field_simp <;> ring
      rw [h4, Real.log_pow] <;> ring
    rw [h3] <;> field_simp [h_log2_pos.ne'] <;> ring
  let C_log : ℝ := (2 : ℝ)^K * (Real.log 2)^degree / (K * C_poly)
  have hC_log_pos : 0 < C_log := by positivity
  rcases polylog_absorption b (K + (degree : ℝ)) C_log hb_pos hKdeg_pos hC_log_pos (0 : ℕ)
    with ⟨δ_log, hδ_log_pos, h_abs_log⟩
  let δ₀ : ℝ := min δ_log (1 / 2)
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_le_log : δ₀ ≤ δ_log := min_le_left _ _
  have hδ₀_lt_one : δ₀ < 1 := by
    have h : δ₀ ≤ 1 / 2 := min_le_right _ _
    linarith
  refine ⟨δ₀, hδ₀_pos, fun n hδn_le => ?_⟩
  have hδn_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have hδn_le_log : dyadicDelta n ≤ δ_log := le_trans hδn_le hδ₀_le_log
  have hδn_lt_one : dyadicDelta n < 1 := by
    have h1 : dyadicDelta n ≤ δ₀ := hδn_le
    linarith
  have h_log_pos : 0 < Real.log (1 / dyadicDelta n) := by
    have h1 : 1 < 1 / dyadicDelta n := by
      apply one_lt_one_div <;> linarith
    exact Real.log_pos h1
  have h4_raw := h_abs_log (dyadicDelta n) hδn_pos hδn_le_log
  have h4 : (dyadicDelta n)^b ≤
      C_log * (Real.log (1 / dyadicDelta n))^(-(K + (degree : ℝ))) := by
    simpa using h4_raw
  have h5 : (n : ℝ)^degree =
      (Real.log (1 / dyadicDelta n))^degree / (Real.log 2)^degree := by
    rw [h_n_eq_log n, div_pow]
  set L : ℝ := Real.log (1 / dyadicDelta n) with hL_def
  have hL_pos : 0 < L := h_log_pos
  have h_rpow_div : L^(-K) / L^degree = L^(-(K + (degree : ℝ))) := by
    have h_deg : L ^ degree = L ^ (degree : ℝ) := by exact Eq.symm (Real.rpow_natCast L degree)
    rw [h_deg]
    have h1 : L^(-K) / L^(degree : ℝ) = L^(-K - (degree : ℝ)) := by
      have h2 : L^(-K - (degree : ℝ)) * L^(degree : ℝ) = L^(-K) := by
        rw [← Real.rpow_add hL_pos] <;> ring_nf
      field_simp [hL_pos.ne'] <;> linarith
    rw [h1] <;> ring_nf
  have h_main_eq : (2^K / K) * L^(-K) * (dyadicDelta n)^a / (C_poly * (n : ℝ)^degree) =
      C_log * L^(-(K + (degree : ℝ))) * (dyadicDelta n)^a := by
    rw [h5]
    calc
      (2^K / K) * L^(-K) * (dyadicDelta n)^a / (C_poly * (L^degree / (Real.log 2)^degree))
        = (2^K / K) * L^(-K) * (dyadicDelta n)^a * (Real.log 2)^degree / (C_poly * L^degree) := by
          field_simp [hC_poly_pos.ne', h_log2_pos.ne', hL_pos.ne'] <;> ring
      _ = ((2^K * (Real.log 2)^degree) / (K * C_poly)) * (L^(-K) / L^degree) * (dyadicDelta n)^a := by ring
      _ = C_log * L^(-(K + (degree : ℝ))) * (dyadicDelta n)^a := by
          rw [h_rpow_div] <;> simp [C_log] <;> ring
  rw [h_main_eq]
  have h6 : C_log * L^(-(K + (degree : ℝ))) ≥ (dyadicDelta n)^b := h4
  have h7 : C_log * L^(-(K + (degree : ℝ))) * (dyadicDelta n)^a ≥
      (dyadicDelta n)^b * (dyadicDelta n)^a := by gcongr
  have h8 : (dyadicDelta n)^b * (dyadicDelta n)^a = (dyadicDelta n)^(a + b) := by
    rw [← Real.rpow_add hδn_pos] <;> ring_nf
  have h9 : (dyadicDelta n)^(a + b) ≥ (dyadicDelta n)^loss_coarse := by
    have h10 : a + b ≤ loss_coarse := by linarith
    have h11 : dyadicDelta n ≤ 1 := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hδn_pos h11 h10
  calc
    C_log * L^(-(K + (degree : ℝ))) * (dyadicDelta n)^a
      ≥ (dyadicDelta n)^b * (dyadicDelta n)^a := h7
    _ = (dyadicDelta n)^(a + b) := h8
    _ ≥ (dyadicDelta n)^loss_coarse := h9

/-- At-point wrapper for coarse_prop5_fixed_absorption. -/
lemma coarse_prop5_fixed_absorb_at
    (K C_poly : ℝ) (degree : ℕ)
    (hK_pos : 0 < K) (hC_poly_pos : 0 < C_poly)
    (a b loss_coarse δ_n δ₀ : ℝ)
    (hb_pos : 0 < b) (h_sum_lt : a + b < loss_coarse)
    (hδ₀_spec : ∀ (x : ℕ), dyadicDelta x ≤ δ₀ →
      (2^K / K) * Real.log (1 / dyadicDelta x)^(-K) * (dyadicDelta x)^a /
        (C_poly * (x : ℝ)^degree) ≥ (dyadicDelta x)^loss_coarse)
    (n : ℕ) (hδn_le : dyadicDelta n ≤ δ₀) :
    (2^K / K) * Real.log (1 / dyadicDelta n)^(-K) * (dyadicDelta n)^a /
      (C_poly * (n : ℝ)^degree) ≥ (dyadicDelta n)^loss_coarse :=
  hδ₀_spec n hδn_le

/-- C_prop5 coefficient at a given scale δ.

    From uniform_prop5_wrapper_with_K, the incidence lower bound is
      C_prop5 * M * δ^{-s} * (M*δ^s)^α
    where
      C_prop5 = (1/K) * log(1/δ)^(-K) / (C_P * 13 * C₁ * 2^s). -/
noncomputable def C_prop5_at_coarse_scale
    (K C_P C₁ s : ℝ) (δ : ℝ) : ℝ :=
  (1 / K) * Real.log (1 / δ)^(-K) / (C_P * 13 * C₁ * Real.rpow 2 s)

/-- Scale conversion: when n = 2*m, coarse scale δ_m = δ_n^{1/2}, so
    log(1/δ_m)^(-K) = 2^K * log(1/δ_n)^(-K). -/
lemma C_prop5_coarse_to_fine_scale
    (K C_P C₁ s : ℝ) (n m : ℕ) (h_even : n = 2 * m)
    (hK_pos : 0 < K) (hn_pos : 0 < n) :
    C_prop5_at_coarse_scale K C_P C₁ s (dyadicDelta m) =
    (2^K / K) * Real.log (1 / dyadicDelta n)^(-K) /
      (C_P * 13 * C₁ * Real.rpow 2 s) := by
  have h_log_m : Real.log (1 / dyadicDelta m) = (m : ℝ) * Real.log 2 := by
    simp [dyadicDelta, Real.log_div, Real.log_pow] <;> ring
  have h_log_n : Real.log (1 / dyadicDelta n) = (n : ℝ) * Real.log 2 := by
    simp [dyadicDelta, Real.log_div, Real.log_pow] <;> ring
  have hmn : (m : ℝ) = (n : ℝ) / 2 := by
    have h : (n : ℝ) = 2 * (m : ℝ) := by exact_mod_cast h_even
    linarith
  have h_eq : Real.log (1 / dyadicDelta m) = (1 / 2 : ℝ) * Real.log (1 / dyadicDelta n) := by
    rw [h_log_m, h_log_n, hmn] <;> ring
  have h_log_n_pos : 0 < Real.log (1 / dyadicDelta n) := by
    rw [h_log_n]
    have h1 : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  set L : ℝ := Real.log (1 / dyadicDelta n) with hL_def
  have hL_pos : 0 < L := h_log_n_pos
  have h_half_pow : (1 / 2 : ℝ)^(-K) = (2 : ℝ)^K := by
    have h_pos_half : 0 < (1 / 2 : ℝ) := by norm_num
    have h1 : (1 / 2 : ℝ)^(-K) = ((1 / 2 : ℝ)^K)⁻¹ := by
      rw [Real.rpow_neg h_pos_half.le] <;> ring
    rw [h1]
    have h2 : (1 / 2 : ℝ)^K = ((2 : ℝ)^K)⁻¹ := by
      have h3 : (1 / 2 : ℝ)^K * (2 : ℝ)^K = 1 := by
        rw [← Real.mul_rpow (by norm_num) (by norm_num)] <;> norm_num
      have h4 : 0 < (2 : ℝ)^K := by positivity
      field_simp [h4.ne'] <;> linarith
    rw [h2]
    have h5 : 0 < (2 : ℝ)^K := by positivity
    field_simp [h5.ne'] <;> ring
  have h_mul : ((1 / 2 : ℝ) * L)^(-K) = (1 / 2 : ℝ)^(-K) * L^(-K) := by
    rw [Real.mul_rpow (by positivity) hL_pos.le]
  have h3 : (Real.log (1 / dyadicDelta m))^(-K) = (2 : ℝ)^K * L^(-K) := by
    rw [h_eq, hL_def, h_mul, h_half_pow] <;> ring
  simp only [C_prop5_at_coarse_scale, h3, hL_def] <;> ring

/-- Full C_prop5 absorption from runtime majorants.

    Given polynomial majorants for C_P and CΔ:
      C_P ≤ δ_n^{-aP} * C_P_poly * n^dP
      CΔ ≤ δ_n^{-aT} * C_T_poly * n^dT

    and a polylog loss budget `b` with `aP + aT + b < loss_coarse`,
    produces a threshold δ₀ such that for δ_n ≤ δ₀:
      C_prop5_at_coarse_scale K C_P CΔ s (δ_m) ≥ δ_n^{loss_coarse}

    where n = 2*m. -/
lemma C_prop5_absorption_from_majorants
    (K C_P C₁ s : ℝ) (n m : ℕ) (h_even : n = 2 * m)
    (hK_pos : 0 < K) (hn_pos : 0 < n)
    (aP aT b loss_coarse : ℝ)
    (C_P_poly C_T_poly : ℝ) (dP dT : ℕ)
    (hC_P_poly_pos : 0 < C_P_poly) (hC_T_poly_pos : 0 < C_T_poly)
    (hb_pos : 0 < b)
    (h_sum_lt : aP + aT + b < loss_coarse)
    (hCP_pos : 0 < C_P) (hC1_pos : 0 < C₁)
    (h_CP_majorant : C_P ≤ (dyadicDelta n)^(-aP) * C_P_poly * (n : ℝ)^dP)
    (h_C1_majorant : C₁ ≤ (dyadicDelta n)^(-aT) * C_T_poly * (n : ℝ)^dT) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧
      (dyadicDelta n ≤ δ₀ →
        C_prop5_at_coarse_scale K C_P C₁ s (dyadicDelta m) ≥
          (dyadicDelta n)^loss_coarse) := by
  let a : ℝ := aP + aT
  let C_poly : ℝ := C_P_poly * C_T_poly * 13 * Real.rpow 2 s
  have hC_poly_pos : 0 < C_poly := by
    dsimp only [C_poly]
    have h1 : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
    positivity
  let degree : ℕ := dP + dT
  have h_sum_lt' : a + b < loss_coarse := by
    dsimp only [a] <;> exact h_sum_lt
  rcases coarse_prop5_fixed_absorption K C_poly degree hK_pos hC_poly_pos a b loss_coarse hb_pos h_sum_lt'
    with ⟨δ₀, hδ₀_pos, h_abs⟩
  refine ⟨δ₀, hδ₀_pos, fun hδn_le => ?_⟩
  have hδn_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have hδn_lt_one : dyadicDelta n < 1 := by
    have h1 : 0 < n := hn_pos
    have h2 : dyadicDelta n = (1 / 2 : ℝ)^n := by
      simp [dyadicDelta] <;> ring
    rw [h2]
    have h3 : (1 / 2 : ℝ)^n < 1 := by
      have h4 : 1 ≤ n := by linarith
      have h6 : ∀ m : ℕ, m ≥ 1 → (1 / 2 : ℝ)^m ≤ 1 / 2 := by
        intro m hm
        induction' hm with m hm ih
        · norm_num
        · simp [pow_succ] at * <;> linarith
      have h7 : (1 / 2 : ℝ)^n ≤ 1 / 2 := h6 n h4
      linarith
    exact h3
  have h_rpow2s_pos : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
  have h_log_pos : 0 < Real.log (1 / dyadicDelta n) := by
    have h4 : 1 < 1 / dyadicDelta n := by apply one_lt_one_div <;> linarith
    exact Real.log_pos h4
  -- Scale conversion
  have h_scale : C_prop5_at_coarse_scale K C_P C₁ s (dyadicDelta m) =
      (2^K / K) * Real.log (1 / dyadicDelta n)^(-K) / (C_P * 13 * C₁ * Real.rpow 2 s) :=
    C_prop5_coarse_to_fine_scale K C_P C₁ s n m h_even hK_pos hn_pos
  rw [h_scale]
  -- Lower bound denominator using majorants
  have h_denom : C_P * 13 * C₁ * Real.rpow 2 s ≤
      (dyadicDelta n)^(-a) * C_poly * (n : ℝ)^degree := by
    have h_pos13 : 0 ≤ 13 * Real.rpow 2 s := by positivity
    have h1 : C_P * C₁ ≤
        (dyadicDelta n)^(-aP) * C_P_poly * (n : ℝ)^dP *
        ((dyadicDelta n)^(-aT) * C_T_poly * (n : ℝ)^dT) :=
      mul_le_mul h_CP_majorant h_C1_majorant (by positivity) (by positivity)
    have h2 : (dyadicDelta n)^(-aP) * (dyadicDelta n)^(-aT) = (dyadicDelta n)^(-(aP + aT)) := by
      rw [← Real.rpow_add hδn_pos] <;> ring_nf
    have h_a_eq : -(aP + aT) = -a := by
      dsimp only [a] <;> ring
    have h3 : (n : ℝ)^dP * (n : ℝ)^dT = (n : ℝ)^degree := by
      rw [← pow_add] <;> rfl
    have h4 : 13 * Real.rpow 2 s * ((dyadicDelta n)^(-aP) * C_P_poly * (n : ℝ)^dP *
          ((dyadicDelta n)^(-aT) * C_T_poly * (n : ℝ)^dT)) =
        (dyadicDelta n)^(-(aP + aT)) * (C_P_poly * C_T_poly * 13 * Real.rpow 2 s) * (n : ℝ)^degree := by
      have h5 : (dyadicDelta n)^(-aP) * C_P_poly * (n : ℝ)^dP *
            ((dyadicDelta n)^(-aT) * C_T_poly * (n : ℝ)^dT) =
          (dyadicDelta n)^(-aP) * (dyadicDelta n)^(-aT) * (C_P_poly * C_T_poly) * ((n : ℝ)^dP * (n : ℝ)^dT) := by ring
      rw [h5, h2, h3] <;> ring
    calc C_P * 13 * C₁ * Real.rpow 2 s
      = 13 * Real.rpow 2 s * (C_P * C₁) := by ring
    _ ≤ 13 * Real.rpow 2 s * ((dyadicDelta n)^(-aP) * C_P_poly * (n : ℝ)^dP *
          ((dyadicDelta n)^(-aT) * C_T_poly * (n : ℝ)^dT)) := by
        exact mul_le_mul_of_nonneg_left h1 h_pos13
    _ = (dyadicDelta n)^(-(aP + aT)) * (C_P_poly * C_T_poly * 13 * Real.rpow 2 s) * (n : ℝ)^degree := h4
    _ = (dyadicDelta n)^(-a) * C_poly * (n : ℝ)^degree := by
        rw [h_a_eq] <;> simp [C_poly] <;> ring
  -- Since denominator is positive, 1/denom ≥ 1/(upper bound)
  have h4 : 0 < C_P * 13 * C₁ * Real.rpow 2 s := by
    exact mul_pos (mul_pos (mul_pos hCP_pos (by norm_num)) hC1_pos) h_rpow2s_pos
  have h5 : 0 < (dyadicDelta n)^(-a) * C_poly * (n : ℝ)^degree := by positivity
  set D : ℝ := C_P * 13 * C₁ * Real.rpow 2 s with hD_def
  set U : ℝ := (dyadicDelta n)^(-a) * C_poly * (n : ℝ)^degree with hU_def
  have h_D_le_U : D ≤ U := h_denom
  have h7 : D⁻¹ ≥ U⁻¹ := by
    have h8 : (1 : ℝ) / U ≤ (1 : ℝ) / D := one_div_le_one_div_of_le h4 h_D_le_U
    simpa [one_div] using h8
  have h_prefactor_pos : 0 < (2^K / K) * Real.log (1 / dyadicDelta n)^(-K) := by
    have h9 : 0 < (2^K / K) := by positivity
    have h10 : 0 < Real.log (1 / dyadicDelta n)^(-K) := by positivity
    exact mul_pos h9 h10
  have h8 : U⁻¹ = (dyadicDelta n)^a / (C_poly * (n : ℝ)^degree) := by
    simp only [hU_def]
    have h9 : (dyadicDelta n)^(-a) * (dyadicDelta n)^a = 1 := by
      rw [← Real.rpow_add hδn_pos] <;> simp
    field_simp [hC_poly_pos.ne', hδn_pos.ne'] <;> linarith
  set P : ℝ := (2^K / K) * Real.log (1 / dyadicDelta n)^(-K) with hP_def
  have h_main1 : P * D⁻¹ ≥ P * U⁻¹ :=
    mul_le_mul_of_nonneg_left h7 h_prefactor_pos.le
  have h_main2 : P * U⁻¹ = P * ((dyadicDelta n)^a / (C_poly * (n : ℝ)^degree)) := by
    rw [h8]
  have h_main3 : P * ((dyadicDelta n)^a / (C_poly * (n : ℝ)^degree)) =
      P * (dyadicDelta n)^a / (C_poly * (n : ℝ)^degree) := by ring
  have h_main : P * D⁻¹ ≥ P * (dyadicDelta n)^a / (C_poly * (n : ℝ)^degree) := by
    calc P * D⁻¹ ≥ P * U⁻¹ := h_main1
    _ = P * ((dyadicDelta n)^a / (C_poly * (n : ℝ)^degree)) := h_main2
    _ = P * (dyadicDelta n)^a / (C_poly * (n : ℝ)^degree) := h_main3
  have h_final : (2^K / K) * Real.log (1 / dyadicDelta n)^(-K) / D = P * D⁻¹ := by
    simp [hP_def] <;> field_simp [h4.ne'] <;> ring
  rw [h_final]
  have h_goal : P * (dyadicDelta n)^a / (C_poly * (n : ℝ)^degree) ≥ (dyadicDelta n)^loss_coarse :=
    h_abs n hδn_le
  exact le_trans h_goal h_main

end DirecretisedFurstenbergEstimate.Section6

end
