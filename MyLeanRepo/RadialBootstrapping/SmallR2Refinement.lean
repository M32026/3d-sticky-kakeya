module

/-
 # Small r2 refinement

Given r2, N from the inner conclusion, produce a smaller r2' = 2^(-N') that
still satisfies the essential inner-conclusion conditions, plus r2' < r_max.

Conditions 10 (r^τ log(1/r) ≤ 1/100) and 11 (20*C*r^τ < 1) are NOT preserved
here; they are supplied by the concentrated parameter selection downstream.
-/

public import MyLeanRepo.RadialBootstrapping.ParameterSelectionFinal
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace RadialBootstrapping

/-- Refine r2 to a smaller value while preserving essential conditions. -/
lemma refine_r2_smaller
    (τ σ c K C M κ ε_F δ₀ C_X D_X : ℝ)
    (hτ : 0 < τ) (hτ_lt_01 : τ < 1 / 100)
    (hσ_pos : 0 < σ) (hσ_lt_one : σ < 1)
    (hκ_pos : 0 < κ) (hκ_lt_one : κ < 1)
    (hεF_pos : 0 < ε_F)
    (hεF_large3 : 8 * τ + 3 * κ < ε_F)
    (hc : c ∈ Set.Ioo (0 : ℝ) (1 / 10))
    (hC : 1 ≤ C) (hK : 1 ≤ K)
    (hM_gt2s : M > 2 * (σ + τ) / τ)
    (hM_gt400 : M > 400 / τ^2)
    (r2 : ℝ) (N : ℕ)
    (hr2_eq : r2 = (2 : ℝ)^(-(N : ℝ)))
    (h_geom_sum : ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ)^(-(n + N : ℝ)))^τ) < ENNReal.ofReal c)
    (K' : ℝ) (hK'_def : K' = Real.rpow (max K (C^2 * M / c)) M)
    (r0 : ℝ) (hr0_def : r0 = min (Real.rpow K (-(1 / τ))) r2)
    (hK'_r0_large : (2 : ℝ)^(σ + τ) < K' * r0^(σ + τ))
    (hK'_r0_lower : K' / (2 : ℝ)^(σ + τ) ≥ 2 * r0^(2 * τ))
    (h_r2_tau_le : r2^τ ≤ 1 / 6)
    (h_r2_kappa_le_half : r2^κ ≤ 1 / 2)
    (h_r2_1mkappa_le_sqrt34 : r2^(1 - κ) ≤ Real.sqrt 3 / 4)
    (h_r2_1mkappa_le_116 : r2^(1 - κ) ≤ 1 / 16)
    (h_2r2_le_delta : 2 * r2 ≤ δ₀)
    (h_scale_r2 : (2 : ℝ)^(-(2 * σ + ε_F)) * r2^(-(ε_F - 8 * τ - 2 * κ)) >
        80000 * r2^(-κ))
    (h_C_X_D_X_r2 : C_X * D_X ≤ (2 * r2)^(-ε_F))
    (r_max : ℝ)
    (hr_max_pos : 0 < r_max)
    (hr_max_le_r2 : r_max ≤ r2)
    (hr_max_gt : r_max > 4 / K'^(1 / (σ + τ))) :
    ∃ (r2' : ℝ) (N' : ℕ),
      (r2' = (2 : ℝ)^(-(N' : ℝ))) ∧
      (∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ)^(-(n + N' : ℝ)))^τ) < ENNReal.ofReal c) ∧
      ((2 : ℝ)^(σ + τ) < K' * (min (Real.rpow K (-(1 / τ))) r2')^(σ + τ)) ∧
      (K' / (2 : ℝ)^(σ + τ) ≥ 2 * (min (Real.rpow K (-(1 / τ))) r2')^(2 * τ)) ∧
      (r2'^τ ≤ 1 / 6) ∧
      (r2'^κ ≤ 1 / 2) ∧
      (r2'^(1 - κ) ≤ Real.sqrt 3 / 4) ∧
      (r2'^(1 - κ) ≤ 1 / 16) ∧
      (2 * r2' ≤ δ₀) ∧
      ((2 : ℝ)^(-(2 * σ + ε_F)) * r2'^(-(ε_F - 8 * τ - 2 * κ)) >
        80000 * r2'^(-κ)) ∧
      (C_X * D_X ≤ (2 * r2')^(-ε_F)) ∧
      (r2' < r_max) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr2_pos : 0 < r2 := by
    rw [hr2_eq]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hστ_pos : 0 < σ + τ := by linarith
  have hK'_pos : 0 < K' := by
    rw [hK'_def]
    have h1 : 0 < max K (C ^ 2 * M / c) := by positivity
    exact Real.rpow_pos_of_pos h1 _
  have h_ratio_ge_one : (1 : ℝ) ≤ r2 / r_max :=
    (one_le_div hr_max_pos).mpr hr_max_le_r2

  -- Choose n such that 2^n ≤ r2/r_max < 2^(n+1), then k = n+1
  have hP : ∃ n : ℕ, (2 : ℝ)^n ≤ r2 / r_max ∧ r2 / r_max < (2 : ℝ)^(n + 1) :=
    exists_nat_pow_near (x := r2 / r_max) (y := (2 : ℝ)) h_ratio_ge_one (by norm_num)
  rcases hP with ⟨n, hn_le, hn_gt⟩
  let k : ℕ := n + 1
  have hk_gt : (2 : ℝ)^k > r2 / r_max := by
    simpa [k] using hn_gt
  have h2k_le : (2 : ℝ)^k ≤ 2 * (r2 / r_max) := by
    have h : (2 : ℝ)^k = 2 * (2 : ℝ)^n := by
      simp [k, pow_succ] <;> ring
    rw [h]
    gcongr

  let r2' : ℝ := r2 / (2 : ℝ)^k
  let N' : ℕ := N + k

  have hr2'_lt : r2' < r_max := by
    simp only [r2']
    have h : r2 / (2 : ℝ)^k < r2 / (r2 / r_max) := by gcongr
    have h2 : r2 / (r2 / r_max) = r_max := by
      field_simp [hr_max_pos.ne'] <;> ring
    rw [h2] at h; exact h
  have hr2'_ge : r2' ≥ r_max / 2 := by
    simp only [r2']
    have h : r2 / (2 : ℝ)^k ≥ r2 / (2 * (r2 / r_max)) := by gcongr
    have h2 : r2 / (2 * (r2 / r_max)) = r_max / 2 := by
      field_simp [hr_max_pos.ne'] <;> ring
    rw [h2] at h; exact h
  have hr2'_pos : 0 < r2' := by positivity
  have hr2'_lt_r2 : r2' < r2 := by
    calc r2' < r_max := hr2'_lt
         _ ≤ r2 := hr_max_le_r2

  have hr2'_eq : r2' = (2 : ℝ)^(-(N' : ℝ)) := by
    have h3 : (N' : ℝ) = (N : ℝ) + (k : ℝ) := by simp [N', k]
    have h4 : r2 = (2 : ℝ)^(-(N : ℝ)) := hr2_eq
    have h5 : r2' = r2 / (2 : ℝ)^k := by rfl
    have h_pos2 : (0 : ℝ) < (2 : ℝ) := by norm_num
    have h6 : (2 : ℝ)^(-(N' : ℝ)) = (2 : ℝ)^(-(N : ℝ)) * (2 : ℝ)^(-(k : ℝ)) := by
      rw [h3]
      rw [← Real.rpow_add h_pos2] <;> ring_nf
    have h7 : (2 : ℝ)^(-(k : ℝ)) = 1 / (2 : ℝ)^k := by
      have h8 : (2 : ℝ)^(-(k : ℝ)) = ((2 : ℝ)^(k : ℝ))⁻¹ := by
        simp [Real.rpow_neg]
      rw [h8]
      have h9 : (2 : ℝ)^(k : ℝ) = (2 : ℝ)^k := by norm_cast
      rw [h9] <;> ring
    rw [h5, h4, h6, h7] <;> ring

  have hr2'_gt_min : r2' > 2 / K'^(1 / (σ + τ)) := by
    calc r2' ≥ r_max / 2 := hr2'_ge
         _ > (4 / K'^(1 / (σ + τ))) / 2 := by gcongr
         _ = 2 / K'^(1 / (σ + τ)) := by ring

  have hKinv_pos : 0 < Real.rpow K (-(1 / τ)) := Real.rpow_pos_of_pos (by linarith) _

  -- K' large condition by case split on r2' vs K^(-1/τ)
  have hK'_large' : (2 : ℝ)^(σ + τ) < K' * (min (Real.rpow K (-(1 / τ))) r2')^(σ + τ) := by
    by_cases h_case : r2' < Real.rpow K (-(1 / τ))
    · -- Case 1: r2' < K^(-1/τ), so min = r2'
      have hmin : min (Real.rpow K (-(1 / τ))) r2' = r2' := by
        rw [min_eq_right] <;> linarith
      have h_goal : (2 : ℝ)^(σ + τ) < K' * r2'^(σ + τ) := by
        have h1 : r2' > 2 / K'^(1 / (σ + τ)) := hr2'_gt_min
        have h2 : 0 < K'^(1 / (σ + τ)) := by positivity
        set b := K'^(1 / (σ + τ)) with hb_def
        have hb_pos : 0 < b := h2
        have h_eq1 : (2 / b)^(σ + τ) = (2 : ℝ)^(σ + τ) / b^(σ + τ) := by
          have h_pos2 : (0 : ℝ) ≤ 2 := by norm_num
          have h_inv_nonneg : 0 ≤ b⁻¹ := by positivity
          rw [div_eq_mul_inv]
          have h2 : ((2 : ℝ) * b⁻¹)^(σ + τ) = (2 : ℝ)^(σ + τ) * (b⁻¹)^(σ + τ) :=
            Real.mul_rpow h_pos2 h_inv_nonneg
          rw [h2]
          have h3 : (b⁻¹)^(σ + τ) = b^(-(σ + τ)) := by
            have h_pos : 0 ≤ b := by positivity
            have h4 : b⁻¹ = b^(-1 : ℝ) := by
              rw [Real.rpow_neg h_pos, Real.rpow_one] <;> ring
            rw [h4]
            rw [← Real.rpow_mul h_pos] <;> ring_nf
          rw [h3]
          rw [Real.rpow_neg (by positivity)]
          <;> field_simp [hK'_pos.ne'] <;> ring
        have h_eq2 : b^(σ + τ) = K' := by
          simp only [b]
          have h_pos : 0 ≤ K' := by positivity
          have h : (K'^(1 / (σ + τ)))^(σ + τ) = K'^((1 / (σ + τ)) * (σ + τ)) := by
            rw [← Real.rpow_mul h_pos] <;> rfl
          rw [h]
          have h9 : (1 / (σ + τ)) * (σ + τ) = 1 := by field_simp [hστ_pos.ne'] <;> ring
          rw [h9, Real.rpow_one]
        have h4 : K' * (2 / b)^(σ + τ) = (2 : ℝ)^(σ + τ) := by
          rw [h_eq1, h_eq2] <;> field_simp [hK'_pos.ne'] <;> ring
        have h3 : K' * r2'^(σ + τ) > K' * (2 / b)^(σ + τ) := by gcongr <;> positivity
        rw [h4] at h3
        exact h3
      rw [hmin]
      exact h_goal
    · -- Case 2: r2' ≥ K^(-1/τ), so min = K^(-1/τ) = original r0
      have h_ge : r2' ≥ Real.rpow K (-(1 / τ)) := by linarith
      have hmin : min (Real.rpow K (-(1 / τ))) r2' = Real.rpow K (-(1 / τ)) := by
        rw [min_eq_left] <;> linarith
      have h_orig_r0_eq : r0 = Real.rpow K (-(1 / τ)) := by
        have h : r2 ≥ Real.rpow K (-(1 / τ)) := by
          calc r2 ≥ r2' := by linarith [hr2'_lt_r2]
               _ ≥ Real.rpow K (-(1 / τ)) := h_ge
        simp only [hr0_def]
        rw [min_eq_left] <;> linarith
      rw [hmin, ←h_orig_r0_eq]
      exact hK'_r0_large

  -- Geometric sum
  have h_geom_sum' : ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ)^(-(n + N' : ℝ)))^τ) < ENNReal.ofReal c := by
    have hN_le_N' : N ≤ N' := by simp [N'] <;> omega
    have h1 : ∀ n : ℕ, ((2 : ℝ)^(-(n + N' : ℝ)))^τ ≤ ((2 : ℝ)^(-(n + N : ℝ)))^τ := by
      intro n
      have h2 : (n + N' : ℝ) ≥ (n + N : ℝ) := by
        simp [N'] <;> norm_cast <;> omega
      have h3 : (2 : ℝ)^(-(n + N' : ℝ)) ≤ (2 : ℝ)^(-(n + N : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le
        <;> norm_num <;> linarith
      have h4 : 0 ≤ (2 : ℝ)^(-(n + N' : ℝ)) := by positivity
      gcongr
    have h5 : ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ)^(-(n + N' : ℝ)))^τ) ≤
        ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ)^(-(n + N : ℝ)))^τ) := by
      apply ENNReal.tsum_le_tsum
      intro n
      have h6 : 2 * ((2 : ℝ)^(-(n + N' : ℝ)))^τ ≤ 2 * ((2 : ℝ)^(-(n + N : ℝ)))^τ := by
        exact mul_le_mul_of_nonneg_left (h1 n) (by norm_num)
      exact ENNReal.ofReal_le_ofReal h6
    exact lt_of_le_of_lt h5 h_geom_sum

  have hK'_lower' : K' / (2 : ℝ)^(σ + τ) ≥ 2 * (min (Real.rpow K (-(1 / τ))) r2')^(2 * τ) := by
    by_cases h_case : r2' < Real.rpow K (-(1 / τ))
    · -- Case 1: min = r2' < r0
      have hmin : min (Real.rpow K (-(1 / τ))) r2' = r2' := by
        rw [min_eq_right] <;> linarith
      have hr2'_lt_r0 : r2' < r0 := by
        have h2 : r2' < r2 := hr2'_lt_r2
        have h3 : r2' < min (Real.rpow K (-(1 / τ))) r2 := lt_min h_case h2
        simpa [hr0_def] using h3
      rw [hmin]
      have h4 : r2'^(2 * τ) ≤ r0^(2 * τ) := by gcongr <;> linarith
      have h5 : 2 * r2'^(2 * τ) ≤ 2 * r0^(2 * τ) := by gcongr
      exact le_trans h5 hK'_r0_lower
    · -- Case 2: min = K^(-1/τ) = original r0
      have h_ge : r2' ≥ Real.rpow K (-(1 / τ)) := by linarith
      have hmin : min (Real.rpow K (-(1 / τ))) r2' = Real.rpow K (-(1 / τ)) := by
        rw [min_eq_left] <;> linarith
      have h_orig_r0_eq : r0 = Real.rpow K (-(1 / τ)) := by
        have h : r2 ≥ Real.rpow K (-(1 / τ)) := by
          calc r2 ≥ r2' := by linarith [hr2'_lt_r2]
               _ ≥ Real.rpow K (-(1 / τ)) := h_ge
        simp only [hr0_def]
        rw [min_eq_left] <;> linarith
      rw [hmin, ←h_orig_r0_eq]
      exact hK'_r0_lower

  -- Smallness conditions
  have h6' : r2'^τ ≤ 1 / 6 := by
    have h : r2'^τ ≤ r2^τ := by gcongr <;> linarith
    exact le_trans h h_r2_tau_le
  have h7' : r2'^κ ≤ 1 / 2 := by
    have h : r2'^κ ≤ r2^κ := by gcongr <;> linarith
    exact le_trans h h_r2_kappa_le_half
  have h8' : r2'^(1 - κ) ≤ Real.sqrt 3 / 4 := by
    have h : r2'^(1 - κ) ≤ r2^(1 - κ) := by gcongr <;> linarith
    exact le_trans h h_r2_1mkappa_le_sqrt34
  have h9' : r2'^(1 - κ) ≤ 1 / 16 := by
    have h : r2'^(1 - κ) ≤ r2^(1 - κ) := by gcongr <;> linarith
    exact le_trans h h_r2_1mkappa_le_116
  have h12' : 2 * r2' ≤ δ₀ := by
    have h : 2 * r2' ≤ 2 * r2 := by gcongr
    exact le_trans h h_2r2_le_delta

  -- Scale inequality: simpler proof
  have h13' : (2 : ℝ)^(-(2 * σ + ε_F)) * r2'^(-(ε_F - 8 * τ - 2 * κ)) >
        80000 * r2'^(-κ) := by
    set p : ℝ := ε_F - 8 * τ - 2 * κ with hp_def
    have hp_pos : 0 < p := by linarith [hεF_large3]
    have hpk_pos : 0 < p - κ := by linarith [hεF_large3]
    -- Original implies: 2^(-(2σ+ε_F)) > 80000 * r2^(p-κ)
    have h_orig : (2 : ℝ)^(-(2 * σ + ε_F)) > 80000 * r2^(p - κ) := by
      have h1 : (2 : ℝ)^(-(2 * σ + ε_F)) * r2^(-p) > 80000 * r2^(-κ) := h_scale_r2
      have h_posp : 0 < r2^p := by positivity
      have h2 : (2 : ℝ)^(-(2 * σ + ε_F)) * (r2^(-p) * r2^p) > 80000 * (r2^(-κ) * r2^p) := by
        simpa [mul_assoc] using mul_lt_mul_of_pos_right h1 h_posp
      have h_eq1 : r2^(-p) * r2^p = 1 := by
        have h : r2^(-p) * r2^p = r2^((-p) + p) := by
          rw [← Real.rpow_add (by positivity)] <;> rfl
        rw [h]
        have h2 : (-p) + p = 0 := by ring
        rw [h2, Real.rpow_zero]
      have h_eq2 : r2^(-κ) * r2^p = r2^(p - κ) := by
        have h : r2^(-κ) * r2^p = r2^((-κ) + p) := by
          rw [← Real.rpow_add (by positivity)] <;> rfl
        rw [h]
        have h2 : (-κ) + p = p - κ := by ring
        rw [h2]
      rw [h_eq1, h_eq2] at h2
      simpa using h2
    -- r2' < r2 implies r2'^(p-κ) < r2^(p-κ)
    have h9 : r2'^(p - κ) < r2^(p - κ) := by gcongr <;> linarith
    have h10 : (2 : ℝ)^(-(2 * σ + ε_F)) > 80000 * r2'^(p - κ) := by
      calc (2 : ℝ)^(-(2 * σ + ε_F)) > 80000 * r2^(p - κ) := h_orig
           _ > 80000 * r2'^(p - κ) := by gcongr
    -- Multiply by r2'^(-p)
    have h11 : 0 < r2'^(-p) := by positivity
    have h12 : (2 : ℝ)^(-(2 * σ + ε_F)) * r2'^(-p) > 80000 * (r2'^(p - κ) * r2'^(-p)) := by
      simpa [mul_assoc] using mul_lt_mul_of_pos_right h10 h11
    have h13 : r2'^(p - κ) * r2'^(-p) = r2'^(-κ) := by
      have h : r2'^(p - κ) * r2'^(-p) = r2'^((p - κ) + (-p)) := by
        rw [← Real.rpow_add (by positivity)] <;> rfl
      rw [h]
      have h2 : (p - κ) + (-p) = -κ := by ring
      rw [h2]
    rw [h13] at h12
    simpa [hp_def] using h12

  -- C_X * D_X
  have h14' : C_X * D_X ≤ (2 * r2')^(-ε_F) := by
    have h2 : 2 * r2' < 2 * r2 := by gcongr
    have h3 : 0 < 2 * r2' := by positivity
    have h4 : 0 < 2 * r2 := by positivity
    have h7 : (2 * r2')^(ε_F) < (2 * r2)^(ε_F) := by gcongr <;> linarith
    have h8 : 0 < (2 * r2')^(ε_F) := by positivity
    have h9 : 1 / (2 * r2')^(ε_F) ≥ 1 / (2 * r2)^(ε_F) := one_div_le_one_div_of_le h8 h7.le
    have h10 : (2 * r2')^(-ε_F) = 1 / (2 * r2')^(ε_F) := by
      rw [Real.rpow_neg (by positivity)] <;> ring
    have h11 : (2 * r2)^(-ε_F) = 1 / (2 * r2)^(ε_F) := by
      rw [Real.rpow_neg (by positivity)] <;> ring
    have h12 : C_X * D_X ≤ (2 * r2)^(-ε_F) := h_C_X_D_X_r2
    rw [h11] at h12
    rw [h10]
    exact le_trans h12 h9

  exact ⟨r2', N', hr2'_eq, h_geom_sum',
    hK'_large', hK'_lower',
    h6', h7', h8', h9', h12', h13', h14', hr2'_lt⟩

/-- General threshold lemma: if T ≥ 1, p ≥ τ/2, T ≤ X^a, and M/2 > 2a/τ + 1,
    where X = max(K, C²M/c), then T^(-1/p) > 8/K'^(1/(σ+τ)). -/
lemma threshold_gt_Kprime
    (τ σ M K C c K' : ℝ)
    (hτ : 0 < τ) (hτ_lt_01 : τ < 1 / 100)
    (hσ_pos : 0 < σ) (hσ_lt_one : σ < 1)
    (hK : 1 ≤ K) (hC : 1 ≤ C)
    (hc : c ∈ Set.Ioo (0 : ℝ) (1 / 10))
    (hM_gt400 : M > 400 / τ^2)
    (hK'_def : K' = Real.rpow (max K (C^2 * M / c)) M)
    (T p a : ℝ) (hT_one : 1 ≤ T) (hp_pos : 0 < p) (hp_ge : p ≥ τ / 2)
    (ha_nonneg : 0 ≤ a)
    (hT_le : T ≤ (max K (C^2 * M / c))^a)
    (hM_cond : M / 2 > 2 * a / τ + 1) :
    T^(-1 / p) > 8 / K'^(1 / (σ + τ)) := by
  set X : ℝ := max K (C^2 * M / c) with hX_def
  have hX_ge_10M : X ≥ 10 * M := by
    have h2 : C^2 * M / c ≥ 10 * M := by
      have h3 : 1 / c > 10 := by
        have h4 : c < 1 / 10 := hc.2
        have h5 : 0 < c := hc.1
        have h6 : 1 / c > 1 / (1 / 10 : ℝ) := one_div_lt_one_div_of_lt h5 h4
        have h7 : (1 / (1 / 10 : ℝ)) = 10 := by norm_num
        rw [h7] at h6; exact h6
      have h4 : C^2 ≥ 1 := by nlinarith
      have h5 : 0 < M := by
        have h6 : 0 < 400 / τ^2 := by positivity
        exact lt_trans h6 hM_gt400
      have h6 : C^2 * M / c = C^2 * (M * (1 / c)) := by ring
      rw [h6]
      have h7 : M * (1 / c) > 10 * M := by
        have h8 : 1 / c > 10 := h3
        have h9 : M * (1 / c) > M * 10 := by gcongr
        linarith
      nlinarith
    have h3 : X ≥ C^2 * M / c := le_max_right _ _
    linarith
  have hτ2_lt : τ^2 < 1 / 10000 := by
    have h1 : τ < 1 / 100 := hτ_lt_01
    have h2 : 0 < τ := hτ
    have h3 : τ^2 < (1 / 100 : ℝ)^2 := by gcongr
    have h4 : (1 / 100 : ℝ)^2 = 1 / 10000 := by norm_num
    rw [h4] at h3; exact h3
  have h_inv_tau2_gt : 1 / τ^2 > 10000 := by
    have h1 : τ^2 < 1 / 10000 := hτ2_lt
    have h2 : 0 < τ^2 := by positivity
    have h3 : 1 / τ^2 > 1 / (1 / 10000 : ℝ) := one_div_lt_one_div_of_lt h2 h1
    have h4 : (1 / (1 / 10000 : ℝ)) = 10000 := by norm_num
    rw [h4] at h3; exact h3
  have hM_gt4M : M > 4000000 := by
    have h1 : 400 / τ^2 = 400 * (1 / τ^2) := by ring
    rw [h1] at hM_gt400
    have h2 : 400 * (1 / τ^2) > 400 * 10000 := by gcongr
    have h3 : 400 * (10000 : ℝ) = 4000000 := by norm_num
    rw [h3] at h2
    linarith [hM_gt400, h2]
  have hX_gt : X > 40000000 := by
    have h2 : X ≥ 10 * M := hX_ge_10M
    nlinarith [hM_gt4M]
  have hX_pos : 0 < X := by linarith
  have hK'_eq : K' = Real.rpow X M := by simpa [hX_def] using hK'_def
  have h_logK' : Real.log K' = M * Real.log X := by
    rw [hK'_eq]; exact Real.log_rpow hX_pos M
  have hστ_lt_two : σ + τ < 2 := by linarith
  have hστ_pos : 0 < σ + τ := by linarith
  have h_logX_pos : 0 < Real.log X := by
    have h : X > 1 := by linarith
    exact Real.log_pos h
  have hM_half_gt : M / 2 > 200 / τ^2 := by
    have h : M > 400 / τ^2 := hM_gt400
    have h2 : M / 2 > (400 / τ^2) / 2 := by gcongr
    have h3 : (400 / τ^2) / 2 = 200 / τ^2 := by ring
    rw [h3] at h2; exact h2
  have h_inv_tau_gt : 1 / τ > 100 := by
    have h1 : τ < 1 / 100 := hτ_lt_01
    have h2 : 0 < τ := hτ
    have h3 : 1 / τ > 1 / (1 / 100 : ℝ) := one_div_lt_one_div_of_lt h2 h1
    have h4 : (1 / (1 / 100 : ℝ)) = 100 := by norm_num
    rw [h4] at h3; exact h3
  have h_logX_gt_log8 : Real.log X > Real.log 8 :=
    Real.log_lt_log (by positivity) (by linarith [hX_gt])
  have h1 : (M / 2 - 2 * a / τ) * Real.log X > Real.log 8 := by
    have h2 : (M / 2 - 2 * a / τ) > 1 := by linarith [hM_cond]
    have h3 : (M / 2 - 2 * a / τ) * Real.log X > 1 * Real.log X :=
      mul_lt_mul_of_pos_right h2 h_logX_pos
    have h4 : 1 * Real.log X = Real.log X := by ring
    rw [h4] at h3
    linarith [h_logX_gt_log8]
  have h_main : (M / 2) * Real.log X > Real.log 8 + (2 * a / τ) * Real.log X := by
    have h5 : (M / 2) * Real.log X = (M / 2 - 2 * a / τ) * Real.log X + (2 * a / τ) * Real.log X := by ring
    rw [h5]
    linarith [h1]
  have h_div_gt : 1 / (σ + τ) > 1 / 2 := by
    have h1 : 0 < σ + τ := hστ_pos
    have h2 : σ + τ < 2 := hστ_lt_two
    gcongr
  have hMlog_pos : 0 < M * Real.log X := by positivity
  have h9 : M * Real.log X / (σ + τ) > (M / 2) * Real.log X := by
    have h12 : (1 / (σ + τ)) * (M * Real.log X) > (1 / 2 : ℝ) * (M * Real.log X) :=
      mul_lt_mul_of_pos_right h_div_gt hMlog_pos
    have h_eq1 : (1 / (σ + τ)) * (M * Real.log X) = M * Real.log X / (σ + τ) := by ring
    have h_eq2 : (1 / 2 : ℝ) * (M * Real.log X) = M * Real.log X / 2 := by ring
    rw [h_eq1, h_eq2] at h12
    have h13 : M * Real.log X / 2 = (M / 2) * Real.log X := by ring
    rw [h13] at h12; exact h12
  have h_logT_nonneg : 0 ≤ Real.log T := by
    have h : T ≥ 1 := hT_one
    exact Real.log_nonneg h
  have h_logT_le : Real.log T ≤ a * Real.log X := by
    have h1 : Real.log T ≤ Real.log (X^a) := Real.log_le_log (by linarith) hT_le
    have h2 : Real.log (X^a) = a * Real.log X := by
      rw [Real.log_rpow (by linarith)] <;> ring
    rw [h2] at h1; exact h1
  have h11 : 1 / p ≤ 2 / τ := by
    have h13 : p ≥ τ / 2 := hp_ge
    have h14 : 0 < p := hp_pos
    have h15 : 0 < τ / 2 := by positivity
    calc 1 / p ≤ 1 / (τ / 2) := by gcongr
         _ = 2 / τ := by field_simp [hτ.ne'] <;> ring
  have h16 : (1 / p) * Real.log T ≤ (2 / τ) * Real.log T :=
    mul_le_mul_of_nonneg_right h11 h_logT_nonneg
  have h17 : (2 / τ) * Real.log T ≤ (2 / τ) * (a * Real.log X) :=
    mul_le_mul_of_nonneg_left h_logT_le (by positivity)
  have h18 : (2 / τ) * (a * Real.log X) = (2 * a / τ) * Real.log X := by ring
  have h17' : (2 / τ) * Real.log T ≤ (2 * a / τ) * Real.log X := by
    calc (2 / τ) * Real.log T
      ≤ (2 / τ) * (a * Real.log X) := h17
    _ = (2 * a / τ) * Real.log X := h18
  have h10 : (M / 2) * Real.log X > Real.log 8 + (1 / p) * Real.log T := by
    have h19 : Real.log 8 + (2 * a / τ) * Real.log X ≥ Real.log 8 + (2 / τ) * Real.log T := by
      linarith [h17']
    have h20 : Real.log 8 + (2 / τ) * Real.log T ≥ Real.log 8 + (1 / p) * Real.log T := by
      linarith [h16]
    calc (M / 2) * Real.log X
      > Real.log 8 + (2 * a / τ) * Real.log X := h_main
    _ ≥ Real.log 8 + (2 / τ) * Real.log T := h19
    _ ≥ Real.log 8 + (1 / p) * Real.log T := h20
  have h_goal : M * Real.log X / (σ + τ) > Real.log 8 + (1 / p) * Real.log T :=
    calc M * Real.log X / (σ + τ)
      > (M / 2) * Real.log X := h9
    _ > Real.log 8 + (1 / p) * Real.log T := h10
  have hT_pos : 0 < T := by linarith
  have hK'_pos : 0 < K' := by
    rw [hK'_def]; exact Real.rpow_pos_of_pos hX_pos _
  have h_left_pos : 0 < T^(-1 / p) := Real.rpow_pos_of_pos hT_pos _
  have h_right_pos : 0 < (8 / K'^(1 / (σ + τ))) := by positivity
  have h_log_left : Real.log (T^(-1 / p)) = -(1 / p) * Real.log T := by
    rw [Real.log_rpow hT_pos] <;> ring
  have h_log_right : Real.log (8 / K'^(1 / (σ + τ))) =
      Real.log 8 - (1 / (σ + τ)) * Real.log K' := by
    have h1 : Real.log (K'^(1 / (σ + τ))) = (1 / (σ + τ)) * Real.log K' :=
      Real.log_rpow (by positivity) _
    rw [Real.log_div (by norm_num) (by positivity), h1] <;> ring
  have h_final : -(1 / p) * Real.log T > Real.log 8 - (1 / (σ + τ)) * Real.log K' := by
    have h_eq : Real.log K' = M * Real.log X := h_logK'
    have h_goal2 : M * Real.log X / (σ + τ) - (1 / p) * Real.log T > Real.log 8 := by
      linarith [h_goal]
    have h99 : (1 / (σ + τ)) * Real.log K' = M * Real.log X / (σ + τ) := by
      rw [h_eq] <;> ring
    rw [h99]
    linarith [h_goal2]
  have h_log_ineq : Real.log (T^(-1 / p)) > Real.log (8 / K'^(1 / (σ + τ))) := by
    rw [h_log_left, h_log_right]
    exact h_final
  exact Real.log_lt_log_iff h_right_pos h_left_pos |>.mp h_log_ineq

end RadialBootstrapping
