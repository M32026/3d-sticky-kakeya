import MyLeanRepo.Kakeya.Cinematic.TangencySublevelStructure.Basic
import MyLeanRepo.Kakeya.Cinematic.Targets.TangencySublevelDiameter.Helpers

/-!
# Convex case length upper bound

Given a component J of the sublevel set {|H| ≤ δ} in the convex/concave case
(large second derivative gap), prove J.length ≤ C1 * δ / scale.

Two core lemmas:
1. `quadratic_interpolation_length_bound`: Taylor-based calculus bound
2. `quadratic_bound_algebraic`: algebraic reduction to target scale
3. `convex_case_length_bound`: main bound using case split on Delta
-/

namespace Kakeya.Cinematic

/-- Length bound for a convex function component using quadratic interpolation.
  If H'' ≥ m on [c,d], H' ≥ a ≥ 0 on [c,d], and |H(c)|, |H(d)| ≤ δ,
  then d-c ≤ 4δ / (√(a² + 4mδ) + a). -/
lemma quadratic_interpolation_length_bound {H : ℝ → ℝ} {m a delta c d : ℝ}
    (hm_pos : 0 < m) (ha_nonneg : 0 ≤ a) (hdelta : 0 < delta)
    (hH_diff1 : Differentiable ℝ H) (hH_diff2 : Differentiable ℝ (deriv H))
    (hH''_ge : ∀ x ∈ Set.Icc c d, m ≤ deriv (deriv H) x)
    (hcd : c ≤ d)
    (hH'_ge : ∀ x ∈ Set.Icc c d, a ≤ deriv H x)
    (hHc_bound : |H c| ≤ delta) (hHd_bound : |H d| ≤ delta) :
    d - c ≤ 4 * delta / (Real.sqrt (a^2 + 4 * m * delta) + a) := by
  by_cases h_eq : c = d
  · have h_goal : d - c = 0 := by
      rw [h_eq] <;> ring
    rw [h_goal]
    have h_pos : 0 ≤ 4 * delta / (Real.sqrt (a^2 + 4 * m * delta) + a) := by positivity
    exact h_pos
  · have h_lt : c < d := by
      by_contra h
      have : c = d := by linarith
      exact h_eq this
    have hc_in : c ∈ Set.Icc c d := ⟨by linarith, by linarith⟩
    have hd_in : d ∈ Set.Icc c d := ⟨by linarith, by linarith⟩
    have h_taylor : H d ≥ H c + deriv H c * (d - c) + m / 2 * (d - c)^2 :=
      taylor_quadratic_lower_bound hH_diff1 hH_diff2 hcd hc_in hd_in hH''_ge
    have hH'c_ge : a ≤ deriv H c := hH'_ge c hc_in
    set L := d - c with hL_def
    have hL_pos : 0 < L := by linarith
    have h41 : H d - H c ≥ deriv H c * L + m / 2 * L ^ 2 := by
      linarith [h_taylor]
    have h42 : deriv H c * L ≥ a * L := by
      gcongr
    have h4 : H d - H c ≥ a * L + m / 2 * L ^ 2 := by linarith
    have h6 : |H d - H c| ≤ 2 * delta := by
      have h : |H d - H c| ≤ |H d| + |H c| := abs_sub (H d) (H c)
      have h' : |H d| + |H c| ≤ 2 * delta := by
        have h1 : |H d| ≤ delta := hHd_bound
        have h2 : |H c| ≤ delta := hHc_bound
        linarith [abs_le.mp h1, abs_le.mp h2]
      linarith
    have h7 : H d - H c ≤ |H d - H c| := le_abs_self (H d - H c)
    have h3 : a * L + m / 2 * L ^ 2 ≤ 2 * delta := by linarith [h4, h6, h7]
    have h_quad : m / 2 * L ^ 2 + a * L - 2 * delta ≤ 0 := by linarith
    set D := Real.sqrt (a^2 + 4 * m * delta) with hD_def
    have hD_nonneg : 0 ≤ D := by positivity
    have hD_sq : D^2 = a^2 + 4 * m * delta := by
      rw [hD_def]
      exact Real.sq_sqrt (by positivity)
    set r1 := (D - a) / m with hr1_def
    set r2 := -(D + a) / m with hr2_def
    have h_factor : m / 2 * L^2 + a * L - 2 * delta = (m / 2) * (L - r1) * (L - r2) := by
      simp only [hr1_def, hr2_def]
      field_simp [hm_pos.ne']
      nlinarith [hD_sq]
    have h_product : (L - r1) * (L - r2) ≤ 0 := by
      have h_m2_pos : 0 < m / 2 := by positivity
      have h : (m / 2) * ((L - r1) * (L - r2)) ≤ 0 := by
        have h_eq2 : (m / 2) * ((L - r1) * (L - r2)) = m / 2 * L^2 + a * L - 2 * delta := by
          simpa [mul_assoc] using h_factor.symm
        rw [h_eq2]
        exact h_quad
      nlinarith
    have hD_pos : 0 < D := by
      have h : 0 < a^2 + 4 * m * delta := by positivity
      exact Real.sqrt_pos.mpr h
    have h_r2_neg : r2 < 0 := by
      have h1 : r2 = -(D + a) / m := by simp [r2]
      rw [h1]
      have h2 : 0 < D + a := by linarith [hD_pos]
      have h3 : -(D + a) < 0 := by linarith
      exact div_neg_of_neg_of_pos h3 hm_pos
    have h_L_r2 : 0 < L - r2 := by linarith [h_r2_neg]
    have h_L_r1 : L - r1 ≤ 0 := by
      nlinarith [h_product]
    have h_main : L ≤ r1 := by
      exact sub_nonpos.mp h_L_r1
    have h_mult : (D - a) * (D + a) = 4 * m * delta := by
      have h : D^2 = a^2 + 4 * m * delta := hD_sq
      nlinarith
    have h_Da_pos : 0 < D + a := by linarith [hD_pos]
    have h_r1_eq : r1 = 4 * delta / (D + a) := by
      have h9 : (D - a) * (D + a) = 4 * m * delta := h_mult
      have h10 : (D - a) / m = (4 * delta) / (D + a) := by
        calc (D - a) / m
          = ((D - a) * (D + a)) / (m * (D + a)) := by field_simp [h_Da_pos.ne'] <;> ring
        _ = (4 * m * delta) / (m * (D + a)) := by rw [h9]
        _ = (4 * delta) / (D + a) := by
          field_simp [hm_pos.ne', h_Da_pos.ne'] <;> ring
      simpa [r1] using h10
    rw [h_r1_eq] at h_main
    exact h_main

/-- General algebraic bound for the quadratic interpolation case.
  If a ≥ t/(576K²), 0 < δ ≤ t/(6K), m = t/(6K), C1 ≥ 100K, then
  4δ/(√(a²+4mδ)+a) ≤ C1·δ/√((a+2δ)t). -/
lemma quadratic_bound_algebraic
    {K t delta m a C1 : ℝ}
    (hK : 1 ≤ K) (ht_pos : 0 < t) (hdelta : 0 < delta)
    (hm_def : m = t / (6 * K))
    (hdelta_le : delta ≤ t / (6 * K))
    (ha_large : a ≥ t / (576 * K^2))
    (hC1_large : 100 * K ≤ C1) :
    4 * delta / (Real.sqrt (a^2 + 4 * m * delta) + a) ≤
      C1 * delta / Real.sqrt ((a + 2 * delta) * t) := by
  have hK_pos : 0 < K := by linarith
  have hC1_pos : 0 < C1 := by nlinarith
  have ha_nonneg : 0 ≤ a := by
    have h : 0 ≤ t / (576 * K^2) := by positivity
    linarith [ha_large]
  have h_C1_sq : C1^2 ≥ (100 * K)^2 := by nlinarith
  have h_bound1 : (100 * K)^2 * (t / (576 * K^2)) ≥ 4 * t := by
    have h : (100 * K)^2 * (t / (576 * K^2)) = (10000 / 576 : ℝ) * t := by
      field_simp [hK_pos.ne'] <;> ring
    rw [h]
    have h' : (10000 / 576 : ℝ) ≥ 4 := by norm_num
    have h'' : (10000 / 576 : ℝ) * t ≥ 4 * t := by
      exact mul_le_mul_of_nonneg_right h' (by linarith)
    exact h''
  have h2 : 4 * t ≤ C1^2 * a := by
    have h3 : (100 * K)^2 * (t / (576 * K^2)) ≤ C1^2 * a := by
      have h4 : (100 * K)^2 ≤ C1^2 := by nlinarith
      have h5 : t / (576 * K^2) ≤ a := ha_large
      have h6 : (100 * K)^2 * (t / (576 * K^2)) ≤ C1^2 * a := by
        exact mul_le_mul h4 h5 (by positivity) (by positivity)
      exact h6
    linarith [h_bound1, h3]
  have h1a : 4 * a * t ≤ C1^2 * a^2 := by
    have h4 : 0 ≤ a := by linarith
    have h5 : 4 * t ≤ C1^2 * a := h2
    nlinarith
  have h_bound2 : (100 * K)^2 * (t / (6 * K)) ≥ 8 * t := by
    have h : (100 * K)^2 * (t / (6 * K)) = (10000 / 6 : ℝ) * K * t := by
      field_simp [hK_pos.ne'] <;> ring
    rw [h]
    have h' : (10000 / 6 : ℝ) * K * t ≥ 8 * t := by
      have hK1 : 1 ≤ K := hK
      nlinarith
    exact h'
  have h3 : 8 * t ≤ C1^2 * m := by
    rw [hm_def]
    have h4 : (100 * K)^2 * (t / (6 * K)) ≤ C1^2 * (t / (6 * K)) := by
      gcongr
      <;> nlinarith
    linarith [h_bound2, h4]
  have h1b : 8 * delta * t ≤ C1^2 * m * delta := by
    have h4 : 0 ≤ delta := by linarith
    have h5 : 8 * t ≤ C1^2 * m := h3
    nlinarith
  have h1 : 4 * (a + 2 * delta) * t ≤ C1^2 * (a^2 + m * delta) := by
    have h4 : 4 * (a + 2 * delta) * t = 4 * a * t + 8 * delta * t := by ring
    rw [h4]
    have h5 : C1^2 * (a^2 + m * delta) = C1^2 * a^2 + C1^2 * m * delta := by ring
    rw [h5]
    linarith
  set D := Real.sqrt (a^2 + 4 * m * delta) with hD_def
  have hD_arg_pos : 0 < a^2 + 4 * m * delta := by
    rw [hm_def]
    positivity
  have hD_nonneg : 0 ≤ D := by positivity
  have hD_sq : D^2 = a^2 + 4 * m * delta := by
    rw [hD_def]
    exact Real.sq_sqrt (by linarith [hD_arg_pos])
  have hD_ge_a : D ≥ a := by
    have h : D^2 ≥ a^2 := by nlinarith [hD_sq]
    nlinarith [hD_nonneg]
  have h2 : (D + a)^2 ≥ 4 * (a^2 + m * delta) := by
    nlinarith [hD_sq, hD_nonneg]
  have hD_pos : 0 < D := Real.sqrt_pos.mpr hD_arg_pos
  have h_pos1 : 0 < D + a := by linarith [hD_pos]
  have h_pos2 : 0 < Real.sqrt ((a + 2 * delta) * t) := by positivity
  have h4 : 16 * (a + 2 * delta) * t ≤ C1^2 * (D + a)^2 := by
    calc 16 * (a + 2 * delta) * t
      = 4 * (4 * (a + 2 * delta) * t) := by ring
    _ ≤ 4 * (C1^2 * (a^2 + m * delta)) := by gcongr
    _ ≤ C1^2 * (D + a)^2 := by nlinarith
  have h5 : 4 * Real.sqrt ((a + 2 * delta) * t) ≤ C1 * (D + a) := by
    have h6 : (4 * Real.sqrt ((a + 2 * delta) * t))^2 ≤ (C1 * (D + a))^2 := by
      have h7 : (4 * Real.sqrt ((a + 2 * delta) * t))^2 = 16 * ((a + 2 * delta) * t) := by
        have h8 : (Real.sqrt ((a + 2 * delta) * t))^2 = (a + 2 * delta) * t :=
          Real.sq_sqrt (by positivity)
        nlinarith
      rw [h7]
      nlinarith
    have h9 : 0 ≤ 4 * Real.sqrt ((a + 2 * delta) * t) := by positivity
    have h10 : 0 ≤ C1 * (D + a) := by positivity
    nlinarith
  have h_final : 4 * delta / (D + a) ≤ C1 * delta / Real.sqrt ((a + 2 * delta) * t) := by
    have h11 : 4 * delta / (D + a)
        = (4 * Real.sqrt ((a + 2 * delta) * t) * delta) / ((D + a) * Real.sqrt ((a + 2 * delta) * t)) := by
      field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
    have h16 : C1 * delta / Real.sqrt ((a + 2 * delta) * t)
        = (C1 * (D + a) * delta) / ((D + a) * Real.sqrt ((a + 2 * delta) * t)) := by
      field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
    rw [h11, h16]
    have h13 : 4 * Real.sqrt ((a + 2 * delta) * t) ≤ C1 * (D + a) := h5
    have h15 : 4 * Real.sqrt ((a + 2 * delta) * t) * delta ≤ C1 * (D + a) * delta := by
      exact mul_le_mul_of_nonneg_right h13 (by linarith)
    exact div_le_div_of_nonneg_right h15 (by positivity)
  exact h_final

/-- Main convex-case length upper bound.

  Given H'' ≥ m on [a,b], H'(a) ≥ 0, |H| ≤ δ on [a,b], and a tangency
  parameter Delta satisfying either:
    (1) Delta ≤ δ + H'(a)²/m, or
    (2) H'(a) ≥ t/(576K²),
  prove b-a ≤ C1·δ/√((Delta+δ)t). -/
lemma convex_case_length_bound
    {K : ℝ} (hK : 1 ≤ K)
    {t delta scale : ℝ}
    (ht_pos : 0 < t) (hdelta : 0 < delta)
    (hdelta_le : delta ≤ t / (6 * K))
    (H : ℝ → ℝ) (hH1 : Differentiable ℝ H) (hH2 : Differentiable ℝ (deriv H))
    (m : ℝ) (hm_def : m = t / (6 * K))
    (a b : ℝ) (hab : a ≤ b)
    (hH''_ge : ∀ x ∈ Set.Icc a b, m ≤ deriv (deriv H) x)
    (hH_bound : ∀ x ∈ Set.Icc a b, |H x| ≤ delta)
    (hA_nonneg : 0 ≤ deriv H a)
    (Delta : ℝ) (hDelta_nonneg : 0 ≤ Delta)
    (hDelta_le_A : Delta ≤ delta + deriv H a)
    (h_case : (Delta ≤ delta + (deriv H a)^2 / m) ∨ (deriv H a ≥ t / (576 * K^2)))
    (C1 : ℝ) (hC1_large : 1000 * K^2 ≤ C1)
    (hscale : scale = Real.sqrt ((Delta + delta) * t)) :
    b - a ≤ C1 * delta / scale := by
  have hK_pos : 0 < K := by linarith
  have hm_pos : 0 < m := by rw [hm_def] <;> positivity
  have hC1_pos : 0 < C1 := by nlinarith
  have hC1_100K : 100 * K ≤ C1 := by nlinarith
  set A := deriv H a with hA_def
  have hA_nonneg' : 0 ≤ A := hA_nonneg

  -- H' is increasing on [a,b] because H'' ≥ m > 0 (via MVT)
  have hH'_incr : ∀ (x y : ℝ), x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
      deriv H x ≤ deriv H y := by
    intro x y hx hy hxy
    by_cases h_eq : x = y
    · rw [h_eq]
    · have h_ne : x ≠ y := h_eq
      have h_lt : x < y := lt_of_le_of_ne hxy h_ne
      have h_cont : ContinuousOn (deriv H) (Set.Icc x y) := hH2.continuous.continuousOn
      have h_fd : ∀ z ∈ Set.Ioo x y, HasDerivAt (deriv H) (deriv (deriv H) z) z :=
        fun z _ => hH2.differentiableAt.hasDerivAt
      have h_mvt : ∃ ξ ∈ Set.Ioo x y, deriv (deriv H) ξ = (deriv H y - deriv H x) / (y - x) :=
        exists_hasDerivAt_eq_slope (f := deriv H) (f' := deriv (deriv H)) h_lt h_cont h_fd
      rcases h_mvt with ⟨ξ, hξ, h_slope⟩
      have hξ_in : ξ ∈ Set.Icc a b := by
        have h1 : x ≤ ξ := by linarith [hξ.1]
        have h2 : ξ ≤ y := by linarith [hξ.2]
        exact ⟨by linarith [hx.1, h1], by linarith [hy.2, h2]⟩
      have h_deriv_ge : m ≤ deriv (deriv H) ξ := hH''_ge ξ hξ_in
      have h_pos : 0 < y - x := by linarith
      have h_slope' : (deriv H y - deriv H x) / (y - x) ≥ m := by
        exact h_slope.symm ▸ h_deriv_ge
      have h' : deriv H y - deriv H x ≥ m * (y - x) := by
        calc deriv H y - deriv H x
          = ((deriv H y - deriv H x) / (y - x)) * (y - x) := by field_simp [h_pos.ne'] <;> ring
        _ ≥ m * (y - x) := by gcongr
      have h'' : 0 ≤ m * (y - x) := by positivity
      linarith

  -- A ≤ H'(x) for all x ∈ [a,b]
  have hH'_ge : ∀ x ∈ Set.Icc a b, A ≤ deriv H x := by
    intro x hx
    have ha_in : a ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
    have h_le : a ≤ x := hx.1
    have h : deriv H a ≤ deriv H x := hH'_incr a x ha_in hx h_le
    have hA_eq : A = deriv H a := by simp [hA_def]
    rw [hA_eq]
    exact h

  -- Quadratic interpolation bound
  have ha_Icc : a ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  have hb_Icc : b ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  have h_quad : b - a ≤ 4 * delta / (Real.sqrt (A^2 + 4 * m * delta) + A) :=
    quadratic_interpolation_length_bound hm_pos hA_nonneg' hdelta hH1 hH2
      hH''_ge hab hH'_ge (hH_bound a ha_Icc) (hH_bound b hb_Icc)

  rcases h_case with (h_case1 | h_case2)
  · -- Case 1: Delta ≤ δ + A²/m
    have hA2_ge : A^2 ≥ m * (Delta - delta) := by
      have h : Delta - delta ≤ A^2 / m := by linarith [h_case1]
      have h' : m * (Delta - delta) ≤ m * (A^2 / m) :=
        mul_le_mul_of_nonneg_left h (by linarith)
      have h'' : m * (A^2 / m) = A^2 := by
        field_simp [hm_pos.ne'] <;> ring
      rw [h''] at h'
      exact h'
    have h_sqrt_ge : Real.sqrt (A^2 + 4 * m * delta) ≥ Real.sqrt (m * (Delta + 3 * delta)) := by
      have h : A^2 + 4 * m * delta ≥ m * (Delta + 3 * delta) := by
        nlinarith [hA2_ge]
      exact Real.sqrt_le_sqrt h
    have h_bound2 : b - a ≤ 4 * delta / Real.sqrt (m * (Delta + 3 * delta)) := by
      have h_num_nonneg : 0 ≤ 4 * delta := by positivity
      calc b - a
        ≤ 4 * delta / (Real.sqrt (A^2 + 4 * m * delta) + A) := h_quad
      _ ≤ 4 * delta / Real.sqrt (A^2 + 4 * m * delta) := by
        have h_denom : Real.sqrt (A^2 + 4 * m * delta) ≤ Real.sqrt (A^2 + 4 * m * delta) + A := by
          linarith [hA_nonneg']
        gcongr
      _ ≤ 4 * delta / Real.sqrt (m * (Delta + 3 * delta)) := by
        gcongr
    have h_pos1 : 0 < Real.sqrt (m * (Delta + 3 * delta)) := by positivity
    have h_pos2 : 0 < Real.sqrt ((Delta + delta) * t) := by positivity
    have h16t : 16 * t ≤ C1^2 * m := by
      rw [hm_def]
      have h11 : C1^2 * (t / (6 * K)) ≥ 16 * t := by
        have h12 : C1 ≥ 1000 * K^2 := hC1_large
        have h13 : C1^2 ≥ (1000 * K^2)^2 := by nlinarith
        have h14 : (1000 * K^2)^2 * (t / (6 * K)) ≥ 16 * t := by
          have h15 : (1000 * K^2)^2 * (t / (6 * K)) = (1000000 / 6 : ℝ) * K^3 * t := by
            field_simp [hK_pos.ne'] <;> ring
          rw [h15]
          have h16 : (1000000 / 6 : ℝ) * K^3 * t ≥ 16 * t := by
            have h17 : K^3 ≥ 1 := by nlinarith
            nlinarith
          exact h16
        nlinarith
      exact h11
    have h_main_ineq : 4 * Real.sqrt ((Delta + delta) * t) ≤ C1 * Real.sqrt (m * (Delta + 3 * delta)) := by
      have h5 : Delta + delta ≤ Delta + 3 * delta := by linarith
      have h6 : 4 * Real.sqrt ((Delta + delta) * t) ≤ 4 * Real.sqrt ((Delta + 3 * delta) * t) := by
        gcongr <;> linarith
      have h7 : 4 * Real.sqrt ((Delta + 3 * delta) * t) ≤ C1 * Real.sqrt (m * (Delta + 3 * delta)) := by
        have h8 : 0 ≤ Delta + 3 * delta := by linarith
        have h9 : (4 * Real.sqrt ((Delta + 3 * delta) * t))^2 ≤
            (C1 * Real.sqrt (m * (Delta + 3 * delta)))^2 := by
          have h10 : 16 * ((Delta + 3 * delta) * t) ≤ C1^2 * (m * (Delta + 3 * delta)) := by
            calc 16 * ((Delta + 3 * delta) * t)
              = (Delta + 3 * delta) * (16 * t) := by ring
            _ ≤ (Delta + 3 * delta) * (C1^2 * m) := by gcongr
            _ = C1^2 * (m * (Delta + 3 * delta)) := by ring
          nlinarith [Real.sq_sqrt (show 0 ≤ (Delta + 3 * delta) * t by positivity),
            Real.sq_sqrt (show 0 ≤ m * (Delta + 3 * delta) by positivity)]
        have h11 : 0 ≤ 4 * Real.sqrt ((Delta + 3 * delta) * t) := by positivity
        have h12 : 0 ≤ C1 * Real.sqrt (m * (Delta + 3 * delta)) := by positivity
        nlinarith
      linarith
    have h_final : 4 * delta / Real.sqrt (m * (Delta + 3 * delta)) ≤
        C1 * delta / Real.sqrt ((Delta + delta) * t) := by
      set D := Real.sqrt (m * (Delta + 3 * delta)) * Real.sqrt ((Delta + delta) * t) with hD_def
      have hD_pos : 0 < D := by positivity
      set X := 4 * delta / Real.sqrt (m * (Delta + 3 * delta)) with hX_def
      set Y := C1 * delta / Real.sqrt ((Delta + delta) * t) with hY_def
      have h_left : X * D = 4 * delta * Real.sqrt ((Delta + delta) * t) := by
        simp [hX_def, hD_def, h_pos1.ne', h_pos2.ne'] <;> field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
      have h_right : Y * D = C1 * delta * Real.sqrt (m * (Delta + 3 * delta)) := by
        simp [hY_def, hD_def, h_pos1.ne', h_pos2.ne'] <;> field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
      have h_delta_nonneg : 0 ≤ delta := by exact le_of_lt hdelta
      have h_mul : X * D ≤ Y * D := by
        rw [h_left, h_right]
        have h : delta * (4 * Real.sqrt ((Delta + delta) * t)) ≤ delta * (C1 * Real.sqrt (m * (Delta + 3 * delta))) :=
          mul_le_mul_of_nonneg_left h_main_ineq h_delta_nonneg
        have h5 : delta * (4 * Real.sqrt ((Delta + delta) * t)) = 4 * delta * Real.sqrt ((Delta + delta) * t) := by ring
        have h6 : delta * (C1 * Real.sqrt (m * (Delta + 3 * delta))) = C1 * delta * Real.sqrt (m * (Delta + 3 * delta)) := by ring
        rw [h5, h6] at h
        exact h
      have h : X ≤ Y := by
        by_contra h2
        have h3 : Y < X := by linarith
        have h4 : Y * D < X * D := mul_lt_mul_of_pos_right h3 hD_pos
        linarith [h_mul]
      exact h
    have h_goal : b - a ≤ C1 * delta / Real.sqrt ((Delta + delta) * t) := h_bound2.trans h_final
    rw [hscale]
    exact h_goal

  · -- Case 2: A ≥ t/(576K²)
    have hA_large : A ≥ t / (576 * K^2) := h_case2
    have h_algebraic : 4 * delta / (Real.sqrt (A^2 + 4 * m * delta) + A) ≤
        C1 * delta / Real.sqrt ((A + 2 * delta) * t) :=
      quadratic_bound_algebraic hK ht_pos hdelta hm_def hdelta_le hA_large hC1_100K
    have hDelta_le_A2delta : Delta + delta ≤ A + 2 * delta := by
      linarith [hDelta_le_A]
    have h_scale_compare : Real.sqrt ((Delta + delta) * t) ≤ Real.sqrt ((A + 2 * delta) * t) := by
      gcongr <;> linarith
    have h_final : C1 * delta / Real.sqrt ((A + 2 * delta) * t) ≤
        C1 * delta / Real.sqrt ((Delta + delta) * t) := by
      gcongr
      <;> positivity
    calc b - a
      ≤ 4 * delta / (Real.sqrt (A^2 + 4 * m * delta) + A) := h_quad
    _ ≤ C1 * delta / Real.sqrt ((A + 2 * delta) * t) := h_algebraic
    _ ≤ C1 * delta / Real.sqrt ((Delta + delta) * t) := h_final
    _ = C1 * delta / scale := by rw [hscale]

end Kakeya.Cinematic
