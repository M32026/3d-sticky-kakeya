import MyLeanRepo.Kakeya.Cinematic.Targets.TangencySublevelDiameter.Helpers
import MyLeanRepo.Kakeya.Cinematic.Targets.CommonTangentRectangleHelpers
import MyLeanRepo.Kakeya.Cinematic.Targets.CommonTangentRectangleRobustMain
import MyLeanRepo.Kakeya.Cinematic.Statements

/-!
# Standalone main proof for PYZ Lemma 17

This module contains `common_tangent_main_proof`, extracted from
`common_tangent_rectangle_controls_parameter` to avoid elaboration timeouts
from large inline proof blocks with complex local `let` bindings.
-/

namespace Kakeya.Cinematic

/-
/-- Helper: when H'(x0)=0 with x0 < a, prove the final bound. -/
lemma zero_crossing_left_final
    {H : ℝ → ℝ} {K d delta t L a b x0 Δ : ℝ}
    (hH1 : Differentiable ℝ H)
    (hH2 : Differentiable ℝ (deriv H))
    (hK : 1 ≤ K) (hK_pos : 0 < K) (hd_pos : 0 < d)
    (hδ_pos : 0 < delta) (ht_pos : 0 < t)
    (hL_eq : L = Real.sqrt (delta / t)) (hL_pos : 0 < L)
    (h_ab_L : b - a = L) (hab : a ≤ b)
    (hx0_lt_a : x0 < a)
    (hderiv0 : deriv H x0 = 0)
    (hH''_ge : ∀ z ∈ Set.Icc x0 b, d / (2 * K) ≤ deriv (deriv H) z)
    (hH''_le : ∀ z ∈ Set.Icc x0 a, deriv (deriv H) z ≤ d)
    (h_bound : ∀ z ∈ Set.Icc a b, |H z| ≤ 10 * delta)
    (hfa : |H a| ≤ 10 * delta)
    (hfb : |H b| ≤ 10 * delta)
    (hΔ_x0 : Δ ≤ |H x0|)
    (h_d_le_from_var : (0 ≤ deriv H a) → d ≤ 80 * K * t) :
    (Δ + delta) * d ≤ 270000 * K^2 * delta * t := by
  have h_zcl := zero_crossing_left hH1 hH2 hx0_lt_a hab hderiv0
    hH''_ge hH''_le h_bound (by positivity) (by positivity) (by positivity)
  set u : ℝ := a - x0 with hu_def
  have h_u_pos : 0 < u := by linarith
  have h_var_raw : d / (2 * K) * u * (b - a) + d / (2 * K) / 2 * (b - a)^2 ≤ 2 * (10 * delta) := h_zcl.2.1
  have h_var : d / (2 * K) * u * L + d / (4 * K) * L^2 ≤ 20 * delta := by
    have h9 : (b - a) = L := h_ab_L
    have h10 : d / (2 * K) * u * (b - a) + d / (2 * K) / 2 * (b - a)^2 = d / (2 * K) * u * L + d / (4 * K) * L^2 := by
      rw [h9] <;> ring
    have h11 : 2 * (10 * delta) = 20 * delta := by ring
    rw [h10, h11] at h_var_raw
    exact h_var_raw
  have h_pos1 : 0 ≤ d / (4 * K) * L^2 := by positivity
  have h2 : d / (2 * K) * u * L ≤ 20 * delta := by linarith
  have h3 : d * u * L ≤ 40 * K * delta := by
    have h4 : d / (2 * K) * u * L = d * u * L / (2 * K) := by ring
    rw [h4] at h2
    calc d * u * L
        = (d * u * L / (2 * K)) * (2 * K) := by field_simp [hK_pos.ne'] <;> ring
      _ ≤ (20 * delta) * (2 * K) := by gcongr
      _ = 40 * K * delta := by ring
  have h6 : 0 < L := hL_pos
  have h_d_u_le : d * u ≤ 40 * K * delta / L := by
    calc d * u
        = (d * u * L) / L := by field_simp [h6.ne'] <;> ring
      _ ≤ (40 * K * delta) / L := by gcongr
      _ = 40 * K * delta / L := by ring
  have h_Hx0 : |H x0| ≤ 10 * delta + d * u^2 / 2 := h_zcl.2.2
  have hΔ_le : Δ ≤ 10 * delta + d * u^2 / 2 := by linarith [hΔ_x0, h_Hx0]
  have h_d2u2 : d^2 * u^2 / 2 ≤ 800 * K^2 * delta * t := by
    have h1 : 0 ≤ d * u := by positivity
    have h2 : d^2 * u^2 ≤ (40 * K * delta / L)^2 := by
      have h3 : d * u ≤ 40 * K * delta / L := h_d_u_le
      have h4 : 0 ≤ 40 * K * delta / L := by positivity
      nlinarith
    have h5 : (40 * K * delta / L)^2 = 1600 * K^2 * delta^2 / L^2 := by ring
    have h6 : L^2 = delta / t := by
      rw [hL_eq] <;> rw [Real.sq_sqrt (by positivity)]
    have h7 : 1600 * K^2 * delta^2 / L^2 = 1600 * K^2 * delta * t := by
      rw [h6]; field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
    have h8 : d^2 * u^2 ≤ 1600 * K^2 * delta * t := by
      rw [h5, h7] at h2; exact h2
    linarith
  have h_H'a_pos : 0 ≤ deriv H a := by
    have h : deriv H a ≥ d / (2 * K) * u := h_zcl.1
    have h_pos : 0 < d / (2 * K) * u := by positivity
    linarith
  have h_d_le : d ≤ 80 * K * t := h_d_le_from_var h_H'a_pos
  have h_11δd : 11 * delta * d ≤ 880 * K^2 * delta * t := by
    have h4 : 11 * delta * d ≤ 11 * delta * (80 * K * t) := by gcongr
    have h5 : 11 * delta * (80 * K * t) = 880 * K * delta * t := by ring
    rw [h5] at h4
    have h6 : 880 * K * delta * t <= 880 * K^2 * delta * t := by
      have h7 : 0 <= 880 * delta * t := by positivity
      have h8 : K <= K^2 := by nlinarith
      have h9 : 880 * delta * t * K <= 880 * delta * t * K^2 := mul_le_mul_of_nonneg_left h8 h7
      have h10 : 880 * K * delta * t = 880 * delta * t * K := by ring
      have h11 : 880 * K^2 * delta * t = 880 * delta * t * K^2 := by ring
      rw [h10, h11]; exact h9
    linarith
  have h_main : (Δ + delta) * d ≤ 11 * delta * d + d^2 * u^2 / 2 := by
    have h1 : (Δ + delta) * d ≤ (10 * delta + d * u^2 / 2 + delta) * d := by gcongr <;> linarith [hΔ_le]
    have h2 : (10 * delta + d * u^2 / 2 + delta) * d = 11 * delta * d + d^2 * u^2 / 2 := by ring
    rw [h2] at h1; exact h1
  have h_final : 11 * delta * d + d^2 * u^2 / 2 ≤ 270000 * K^2 * delta * t := by
    calc 11 * delta * d + d^2 * u^2 / 2
        ≤ 880 * K^2 * delta * t + 800 * K^2 * delta * t := by gcongr
      _ = 1680 * K^2 * delta * t := by ring
      _ ≤ 270000 * K^2 * delta * t := by
        have h : 0 ≤ K^2 * delta * t := by positivity
        nlinarith
  exact le_trans h_main h_final

/-- Reflection facts for H2(x) = H(a+b-x): differentiability and derivative formulas. -/
lemma reflection_facts
    (H H2 : ℝ → ℝ) (a b : ℝ)
    (hH2_def : ∀ x, H2 x = H (a + b - x))
    (hH1 : Differentiable ℝ H)
    (hH2diff : Differentiable ℝ (deriv H)) :
    Differentiable ℝ H2 ∧
    Differentiable ℝ (deriv H2) ∧
    (∀ x, deriv H2 x = -deriv H (a + b - x)) ∧
    (∀ x, deriv (deriv H2) x = deriv (deriv H) (a + b - x)) := by
  let g : ℝ → ℝ := fun x => a + b - x
  have hg_diff : Differentiable ℝ g := differentiable_id.neg.const_add (a + b)
  have hH2_eq : H2 = fun x => H (g x) := by funext x; exact hH2_def x
  have h1_diff : Differentiable ℝ H2 := by
    rw [hH2_eq]; exact hH1.comp hg_diff
  have h_eq1 : ∀ x, deriv H2 x = -deriv H (a + b - x) := by
    intro x
    have hg' : HasDerivAt g (-1 : ℝ) x := (hasDerivAt_id x).neg.const_add (a + b)
    have hH' : HasDerivAt H (deriv H (g x)) (g x) := hH1.differentiableAt.hasDerivAt
    have hcomp : HasDerivAt H2 (deriv H (g x) * (-1 : ℝ)) x := by
      rw [hH2_eq]; exact hH'.comp x hg'
    have h : HasDerivAt H2 (-deriv H (a + b - x)) x := by
      convert hcomp using 1; ring
    exact h.deriv
  have h_eq2 : deriv H2 = fun x => -deriv H (a + b - x) := by funext x; exact h_eq1 x
  have h2_diff : Differentiable ℝ (deriv H2) := by
    rw [h_eq2]
    exact hH2diff.neg.comp hg_diff
  have hH2''_eq : ∀ x, deriv (deriv H2) x = deriv (deriv H) (a + b - x) := by
    intro x
    rw [h_eq2]
    have hg' : HasDerivAt g (-1 : ℝ) x := (hasDerivAt_id x).neg.const_add (a + b)
    have hF : HasDerivAt (fun y => deriv H (g y)) (deriv (deriv H) (g x) * (-1 : ℝ)) x :=
      hH2diff.differentiableAt.hasDerivAt.comp x hg'
    have hG : HasDerivAt (fun y => -deriv H (g y)) (-(deriv (deriv H) (g x) * (-1 : ℝ))) x := hF.neg
    have h3 : HasDerivAt (fun y => -deriv H (g y)) (deriv (deriv H) (g x)) x := by
      convert hG using 1; ring
    exact h3.deriv
  exact ⟨h1_diff, h2_diff, h_eq1, hH2''_eq⟩

/-- The main sub-proof of PYZ Lemma 17: given a function with bounded curvature
on a controlled interval, and tangency bounds, prove the parameter-distance bound. -/
lemma common_tangent_main_proof
    (K d delta t L a b a_J b_J Δ : ℝ)
    (I : ParameterInterval)
    (hK : 1 ≤ K)
    (hK_pos : 0 < K)
    (hd_pos : 0 < d)
    (hδ_pos : 0 < delta)
    (ht_pos : 0 < t)
    (hδt : delta ≤ t)
    (ht1 : t ≤ 1)
    (hL_eq : L = Real.sqrt (delta / t))
    (hL_le : L ≤ 1 / (24 * K))
    (hL_pos : 0 < L)
    (h_ab_L : b - a = L)
    (hab : a ≤ b)
    (ha_in_I : a ∈ Set.Icc I.left I.right)
    (hb_in_I : b ∈ Set.Icc I.left I.right)
    (hJ_sub_I : Set.Icc a_J b_J ⊆ Set.Icc I.left I.right)
    (hR_sub_J : Set.Icc a b ⊆ Set.Icc a_J b_J)
    (h_geom5 : a - a_J ≥ 1 / (96 * K))
    (h_geom6 : a - a_J ≤ 1)
    (h_geom7 : b_J - b ≥ 1 / (96 * K))
    (h_geom8 : b_J - b ≤ 1 / (16 * K))
    (Hfunc : ℝ → ℝ)
    (hdiff1 : Differentiable ℝ Hfunc)
    (hdiff2 : Differentiable ℝ (deriv Hfunc))
    (hpos : ∀ x ∈ Set.Icc I.left I.right, d / (2 * K) ≤ deriv (deriv Hfunc) x)
    (habs : ∀ x ∈ Set.Icc I.left I.right, |deriv (deriv Hfunc) x| ≤ d)
    (hfa : |Hfunc a| ≤ 10 * delta)
    (hfb : |Hfunc b| ≤ 10 * delta)
    (hint : ∀ (x0 : ℝ), x0 ∈ Set.Icc a b → |Hfunc x0| ≤ 10 * delta)
    (hΔ_J : ∀ (x0 : ℝ), x0 ∈ Set.Icc a_J b_J → Δ ≤ |Hfunc x0| + |deriv Hfunc x0|) :
    (Δ + delta) * d ≤ 270000 * K^2 * delta * t := by
  let J_set : Set ℝ := Set.Icc a_J b_J
  have hpos_J : ∀ x ∈ J_set, d / (2 * K) ≤ deriv (deriv Hfunc) x :=
    fun x hx => hpos x (hJ_sub_I hx)
  have ha_in_J : a ∈ J_set := hR_sub_J ⟨by linarith, by linarith⟩
  have hb_in_J : b ∈ J_set := hR_sub_J ⟨by linarith, by linarith⟩
  have haJ_le_bJ : a_J ≤ b_J := ha_in_J.1.trans ha_in_J.2
  have h_var_lower_a : Hfunc b - Hfunc a ≥ deriv Hfunc a * L + d / (4 * K) * L^2 := by
    have h_taylor := taylor_quadratic_lower_bound hdiff1 hdiff2 I.left_le_right ha_in_I hb_in_I hpos
    have h1 : b - a = L := h_ab_L
    have h_coeff : (d / (2 * K)) / 2 * (b - a)^2 = d / (4 * K) * (b - a)^2 := by ring
    rw [h_coeff, h1] at h_taylor; linarith
  have h_var_lower_b : Hfunc a - Hfunc b ≥ -deriv Hfunc b * L + d / (4 * K) * L^2 := by
    have h_taylor := taylor_quadratic_lower_bound hdiff1 hdiff2 I.left_le_right hb_in_I ha_in_I hpos
    have h1 : a - b = -L := by linarith [h_ab_L]
    have h_coeff : (d / (2 * K)) / 2 * (a - b)^2 = d / (4 * K) * (a - b)^2 := by ring
    rw [h_coeff, h1] at h_taylor; linarith
  have h_var_bound : |Hfunc b - Hfunc a| ≤ 20 * delta := by
    have h3 : |Hfunc b - Hfunc a| ≤ |Hfunc b| + |Hfunc a| := by
      calc |Hfunc b - Hfunc a|
          ≤ |Hfunc b| + |(-Hfunc a)| := by
            exact abs_add_le (Hfunc b) (-Hfunc a)
        _ = |Hfunc b| + |Hfunc a| := by rw [abs_neg]
    linarith [abs_le.mp hfa, abs_le.mp hfb]
  have h_d_le_from_var : (0 ≤ deriv Hfunc a) → d ≤ 80 * K * t := by
    intro hpos'
    have h_upper : Hfunc b - Hfunc a ≤ 20 * delta := (abs_le.mp h_var_bound).2
    have h : deriv Hfunc a * L + d / (4 * K) * L^2 ≤ 20 * delta := by
      calc deriv Hfunc a * L + d / (4 * K) * L^2
          ≤ Hfunc b - Hfunc a := h_var_lower_a
        _ ≤ 20 * delta := h_upper
    have h_pos1 : 0 ≤ deriv Hfunc a * L := by positivity
    have h2 : d / (4 * K) * L^2 ≤ 20 * delta := by linarith
    have h3 : d * L^2 ≤ 80 * K * delta := by
      have h4 : d / (4 * K) * L^2 = d * L^2 / (4 * K) := by ring
      rw [h4] at h2
      calc d * L^2
          = (d * L^2 / (4 * K)) * (4 * K) := by field_simp [hK_pos.ne'] <;> ring
        _ ≤ (20 * delta) * (4 * K) := by gcongr
        _ = 80 * K * delta := by ring
    have hL2 : L^2 = delta / t := by
      rw [hL_eq]; rw [Real.sq_sqrt (by positivity)]
    rw [hL2] at h3
    have h5 : d * (delta / t) ≤ 80 * K * delta := h3
    have h6 : d ≤ 80 * K * t := by
      calc d
          = (d * (delta / t)) * t / delta := by field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
        _ ≤ (80 * K * delta) * t / delta := by gcongr
        _ = 80 * K * t := by field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
    exact h6
  have h_d_le_from_abs_var : (0 ≤ -deriv Hfunc b) → d ≤ 80 * K * t := by
    intro hpos'
    have h_upper : Hfunc a - Hfunc b ≤ 20 * delta := by
      have h : |Hfunc a - Hfunc b| ≤ 20 * delta := by
        have h5 : |Hfunc a - Hfunc b| = |Hfunc b - Hfunc a| := by
          have h6 : Hfunc a - Hfunc b = -(Hfunc b - Hfunc a) := by ring
          rw [h6, abs_neg]
        rw [h5]; exact h_var_bound
      have h7 : Hfunc a - Hfunc b ≤ |Hfunc a - Hfunc b| := le_abs_self (Hfunc a - Hfunc b)
      linarith
    have h : -deriv Hfunc b * L + d / (4 * K) * L^2 ≤ 20 * delta := by
      calc -deriv Hfunc b * L + d / (4 * K) * L^2
          ≤ Hfunc a - Hfunc b := h_var_lower_b
        _ ≤ 20 * delta := h_upper
    have h_pos1 : 0 ≤ -deriv Hfunc b * L := by positivity
    have h2 : d / (4 * K) * L^2 ≤ 20 * delta := by linarith
    have h3 : d * L^2 ≤ 80 * K * delta := by
      have h4 : d / (4 * K) * L^2 = d * L^2 / (4 * K) := by ring
      rw [h4] at h2
      calc d * L^2
          = (d * L^2 / (4 * K)) * (4 * K) := by field_simp [hK_pos.ne'] <;> ring
        _ ≤ (20 * delta) * (4 * K) := by gcongr
        _ = 80 * K * delta := by ring
    have hL2 : L^2 = delta / t := by
      rw [hL_eq]; rw [Real.sq_sqrt (by positivity)]
    rw [hL2] at h3
    have h5 : d * (delta / t) ≤ 80 * K * delta := h3
    have h6 : d ≤ 80 * K * t := by
      calc d
          = (d * (delta / t)) * t / delta := by field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
        _ ≤ (80 * K * delta) * t / delta := by gcongr
        _ = 80 * K * t := by field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
    exact h6
  have h_int_bound : ∀ (x0 : ℝ), x0 ∈ Set.Icc a b → |Hfunc x0| ≤ 10 * delta := hint
  by_cases h_zero : ∃ (x0 : ℝ), x0 ∈ J_set ∧ deriv Hfunc x0 = 0
  · rcases h_zero with ⟨x0, hx0_J, hderiv0⟩
    have hΔ_x0 : Δ ≤ |Hfunc x0| := by
      have h1 : Δ ≤ |Hfunc x0| + |deriv Hfunc x0| := hΔ_J x0 hx0_J
      rw [hderiv0] at h1; simpa using h1
    by_cases h_x0_in_R : x0 ∈ Set.Icc a b
    · -- Case x0 ∈ [a,b]
      have hH_x0 : |Hfunc x0| ≤ 10 * delta := h_int_bound x0 h_x0_in_R
      have h1 : Δ ≤ 10 * delta := by linarith [hΔ_x0, hH_x0]
      have h_dL2_bound : d * L^2 ≤ 320 * K * delta := by
        have hx0_I : x0 ∈ Set.Icc I.left I.right := hJ_sub_I hx0_J
        have h_taylor_a_raw := taylor_quadratic_lower_bound hdiff1 hdiff2 I.left_le_right hx0_I ha_in_I hpos
        have h_taylor_b_raw := taylor_quadratic_lower_bound hdiff1 hdiff2 I.left_le_right hx0_I hb_in_I hpos
        have h_coeff_a : (d / (2 * K)) / 2 * (a - x0)^2 = d / (4 * K) * (a - x0)^2 := by ring
        have h_coeff_b : (d / (2 * K)) / 2 * (b - x0)^2 = d / (4 * K) * (b - x0)^2 := by ring
        rw [h_coeff_a] at h_taylor_a_raw
        rw [h_coeff_b] at h_taylor_b_raw
        rw [hderiv0] at h_taylor_a_raw h_taylor_b_raw
        have h_sum : Hfunc a + Hfunc b ≥ 2 * Hfunc x0 + d / (4 * K) * ((a - x0)^2 + (b - x0)^2) := by linarith
        have h_quad : (a - x0)^2 + (b - x0)^2 ≥ L^2 / 2 := by
          nlinarith [sq_nonneg (a + b - 2 * x0), h_ab_L]
        have h_endpoints : Hfunc a + Hfunc b ≤ 20 * delta := by
          have h1 : Hfunc a ≤ 10 * delta := by linarith [abs_le.mp hfa]
          have h2 : Hfunc b ≤ 10 * delta := by linarith [abs_le.mp hfb]
          linarith
        have h9 : 2 * Hfunc x0 + d / (4 * K) * (L^2 / 2) ≤ 20 * delta := by
          calc 2 * Hfunc x0 + d / (4 * K) * (L^2 / 2)
              ≤ 2 * Hfunc x0 + d / (4 * K) * ((a - x0)^2 + (b - x0)^2) := by gcongr
            _ ≤ Hfunc a + Hfunc b := h_sum
            _ ≤ 20 * delta := h_endpoints
        have h10 : Hfunc x0 ≥ -(10 * delta) := by
          have h11 : |Hfunc x0| ≤ 10 * delta := hH_x0
          linarith [abs_le.mp h11]
        have h12 : d / (4 * K) * (L^2 / 2) ≤ 40 * delta := by linarith
        have h13 : d * L^2 ≤ 320 * K * delta := by
          have h14 : d / (4 * K) * (L^2 / 2) = d * L^2 / (8 * K) := by ring
          rw [h14] at h12
          calc d * L^2
              = (d * L^2 / (8 * K)) * (8 * K) := by field_simp [hK_pos.ne'] <;> ring
            _ ≤ (40 * delta) * (8 * K) := by gcongr
            _ = 320 * K * delta := by ring
        exact h13
      have h_d_le : d ≤ 320 * K * t := by
        have h11 : L^2 = delta / t := by
          rw [hL_eq]; rw [Real.sq_sqrt (by positivity)]
        rw [h11] at h_dL2_bound
        have h12 : d * (delta / t) ≤ 320 * K * delta := h_dL2_bound
        calc d
            = (d * (delta / t)) * t / delta := by field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
          _ ≤ (320 * K * delta) * t / delta := by gcongr
          _ = 320 * K * t := by field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
      have h2 : (Δ + delta) * d ≤ 11 * delta * d := by gcongr <;> linarith
      have h3 : 11 * delta * d ≤ 3520 * K * delta * t := by
        calc 11 * delta * d
            ≤ 11 * delta * (320 * K * t) := by gcongr
          _ = 3520 * K * delta * t := by ring
      have h4 : 3520 * K * delta * t ≤ 270000 * K^2 * delta * t := by
        have h9 : 3520 * K ≤ 270000 * K^2 := by
          have h10 : 1 ≤ K := hK
          have h11 : 3520 ≤ 270000 * K := by nlinarith
          nlinarith
        have h10 : 0 ≤ delta * t := by positivity
        nlinarith
      linarith [h2, h3, h4]
    · -- Case x0 ∉ [a,b]
      have h_x0_out : x0 < a ∨ x0 > b := by
        by_contra h
        push Not at h
        exact h_x0_in_R ⟨h.1, h.2⟩
      rcases h_x0_out with (h_x0_lt_a | h_x0_gt_b)
      · -- Case x0 < a
        have haJ_le_x0 : a_J ≤ x0 := hx0_J.1
        have hH''_ge_x0b : ∀ z ∈ Set.Icc x0 b, d / (2 * K) ≤ deriv (deriv Hfunc) z :=
          fun z hz => hpos_J z ⟨by linarith [haJ_le_x0, hz.1], by linarith [hb_in_J.2, hz.2]⟩
        have hH''_le_x0a : ∀ z ∈ Set.Icc x0 a, deriv (deriv Hfunc) z ≤ d :=
          fun z hz => by
            have h1 : z ∈ J_set := ⟨by linarith [haJ_le_x0, hz.1], by linarith [ha_in_J.2, hz.2]⟩
            have h2 : z ∈ Set.Icc I.left I.right := hJ_sub_I h1
            exact (abs_le.mp (habs z h2)).2
        exact zero_crossing_left_final hdiff1 hdiff2 hK hK_pos hd_pos hδ_pos ht_pos hL_eq hL_pos h_ab_L hab
          h_x0_lt_a hderiv0 hH''_ge_x0b hH''_le_x0a h_int_bound hfa hfb hΔ_x0 h_d_le_from_var
      · -- Case x0 > b: reflect
        let H2 : ℝ → ℝ := fun x => Hfunc (a + b - x)
        have h_refl := reflection_facts Hfunc H2 a b (fun _ => rfl) hdiff1 hdiff2
        rcases h_refl with ⟨hH2_diff1, hH2_diff2, h_eq1, hH2''_eq⟩
        let x0' : ℝ := a + b - x0
        have h_x0'_lt_a : x0' < a := by dsimp only [x0']; linarith
        have h_deriv0' : deriv H2 x0' = 0 := by
          have h1 : deriv H2 x0' = -deriv Hfunc x0 := by
            have h_eq : a + b - x0' = x0 := by simp [x0'] <;> ring
            rw [h_eq1 x0', h_eq]
          rw [h1, hderiv0]; ring
        have hH2a : |H2 a| ≤ 10 * delta := by
          have h1 : H2 a = Hfunc b := by simp [H2] <;> ring
          rw [h1]; exact hfb
        have hH2b : |H2 b| ≤ 10 * delta := by
          have h1 : H2 b = Hfunc a := by simp [H2] <;> ring
          rw [h1]; exact hfa
        have hH2_int : ∀ (z : ℝ), z ∈ Set.Icc a b → |H2 z| ≤ 10 * delta := by
          intro z hz
          have h1 : H2 z = Hfunc (a + b - z) := by simp [H2] <;> ring
          rw [h1]
          have h2 : a + b - z ∈ Set.Icc a b := by
            exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
          exact hint (a + b - z) h2
        have hH2''_ge_x0'b : ∀ z ∈ Set.Icc x0' b, d / (2 * K) ≤ deriv (deriv H2) z :=
          fun z hz => by
            rw [hH2''_eq z]
            have h_lower : a ≤ a + b - z := by linarith [hz.2]
            have h_upper : a + b - z ≤ x0 := by
              have h_eq : x0' = a + b - x0 := by simp [x0']
              linarith [h_eq, hz.1]
            have h2 : a + b - z ∈ J_set := ⟨by linarith [ha_in_J.1, h_lower], by linarith [hx0_J.2, h_upper]⟩
            exact hpos_J (a + b - z) h2
        have hH2''_le_x0'a : ∀ z ∈ Set.Icc x0' a, deriv (deriv H2) z ≤ d :=
          fun z hz => by
            rw [hH2''_eq z]
            have h_lower : b ≤ a + b - z := by linarith [hz.2]
            have h_upper : a + b - z ≤ x0 := by
              have h_eq : x0' = a + b - x0 := by simp [x0']
              linarith [h_eq, hz.1]
            have h2 : a + b - z ∈ J_set := ⟨by linarith [hb_in_J.1, h_lower], by linarith [hx0_J.2, h_upper]⟩
            have h3 : a + b - z ∈ Set.Icc I.left I.right := hJ_sub_I h2
            exact (abs_le.mp (habs (a + b - z) h3)).2
        have hH2Δ_x0 : Δ ≤ |H2 x0'| := by
          have h1 : H2 x0' = Hfunc x0 := by simp [H2, x0'] <;> ring
          rw [h1]; exact hΔ_x0
        have h_d_le_from_var_H2 : (0 ≤ deriv H2 a) → d ≤ 80 * K * t := by
          intro h
          have h' : 0 ≤ -deriv Hfunc b := by
            have h_eq : deriv H2 a = -deriv Hfunc b := by
              rw [h_eq1 a]
              ring_nf
            rw [h_eq] at h; exact h
          exact h_d_le_from_abs_var h'
        exact zero_crossing_left_final hH2_diff1 hH2_diff2 hK hK_pos hd_pos hδ_pos ht_pos hL_eq hL_pos h_ab_L hab
          h_x0'_lt_a h_deriv0' hH2''_ge_x0'b hH2''_le_x0'a hH2_int hH2a hH2b hH2Δ_x0 h_d_le_from_var_H2
  · -- Case no zero in J: constant sign
    have haJ_le_bJ : a_J ≤ b_J := by
      exact ha_in_J.1.trans ha_in_J.2
    have hH'_cont : ContinuousOn (deriv Hfunc) J_set := hdiff2.continuous.continuousOn
    have hH'_ne : ∀ x, x ∈ J_set → deriv Hfunc x ≠ 0 := by
      intro x hx; intro h; exact h_zero ⟨x, hx, h⟩
    have h_sign' : (∀ x ∈ J_set, 0 < deriv Hfunc x) ∨ (∀ x ∈ J_set, deriv Hfunc x < 0) :=
      constant_sign_of_never_zero haJ_le_bJ hH'_cont hH'_ne
    rcases h_sign' with (hH'_pos | hH'_neg)
    · -- Positive sign
      have hΔ_aJ : Δ ≤ |Hfunc a_J| + deriv Hfunc a_J := by
        have h1 : Δ ≤ |Hfunc a_J| + |deriv Hfunc a_J| := hΔ_J a_J ⟨by linarith, by linarith⟩
        have h2 : 0 < deriv Hfunc a_J := hH'_pos a_J ⟨by linarith, by linarith⟩
        have h3 : |deriv Hfunc a_J| = deriv Hfunc a_J := abs_of_pos h2
        rw [h3] at h1; exact h1
      have haJ_le_a : a_J ≤ a := by
        have hpos : 0 < 1 / (96 * K) := by positivity
        linarith [h_geom5, hpos]
      have hb_le_bJ : b ≤ b_J := by
        have hpos : 0 < 1 / (96 * K) := by positivity
        linarith [h_geom7, hpos]
      exact constant_sign_geometric_bound hdiff1 hdiff2 hK hd_pos hδ_pos ht_pos hδt ht1 hL_eq hL_le hL_pos
        haJ_le_a hb_le_bJ h_ab_L h_geom5 h_geom6
        hH'_pos hpos_J hfa hfb hΔ_aJ
    · -- Negative sign: reflect
      let a'_J : ℝ := a + b - b_J
      let b'_J : ℝ := a + b - a_J
      let H2 : ℝ → ℝ := fun x => Hfunc (a + b - x)
      have h_refl := reflection_facts Hfunc H2 a b (fun _ => rfl) hdiff1 hdiff2
      rcases h_refl with ⟨hH2_diff1, hH2_diff2, h_eq1, hH2''_eq⟩
      have hH2''_ge : ∀ x ∈ Set.Icc a'_J b'_J, d / (2 * K) ≤ deriv (deriv H2) x := by
        intro x hx
        rw [hH2''_eq x]
        have h2 : a + b - x ∈ J_set := by
          have h3 : a'_J ≤ x := hx.1
          have h4 : x ≤ b'_J := hx.2
          dsimp only [a'_J, b'_J] at *
          exact ⟨by linarith, by linarith⟩
        exact hpos_J (a + b - x) h2
      have hH2'_pos : ∀ x ∈ Set.Icc a'_J b'_J, 0 < deriv H2 x := by
        intro x hx
        have h1 : deriv H2 x = -deriv Hfunc (a + b - x) := h_eq1 x
        rw [h1]
        have h2 : a + b - x ∈ J_set := by
          have h3 : a'_J ≤ x := hx.1
          have h4 : x ≤ b'_J := hx.2
          dsimp only [a'_J, b'_J] at *
          exact ⟨by linarith, by linarith⟩
        have h3 : deriv Hfunc (a + b - x) < 0 := hH'_neg (a + b - x) h2
        linarith
      have h_geom_low2 : a - a'_J ≥ 1 / (96 * K) := by
        have h_eq : a - a'_J = b_J - b := by
          simp [a'_J] <;> ring
        rw [h_eq]
        exact h_geom7
      have h_geom_high2 : a - a'_J ≤ 1 := by
        dsimp only [a'_J]
        have h : b_J - b ≤ 1 / (16 * K) := h_geom8
        have h2 : 1 / (16 * K) ≤ 1 := by
          have h3 : 0 < K := hK_pos
          have h4 : 1 / (16 * K) ≤ 1 / 16 := by gcongr <;> linarith
          linarith
        linarith
      have hH2a : |H2 a| ≤ 10 * delta := by
        have h1 : H2 a = Hfunc b := by simp [H2] <;> ring
        rw [h1]; exact hfb
      have hH2b : |H2 b| ≤ 10 * delta := by
        have h1 : H2 b = Hfunc a := by simp [H2] <;> ring
        rw [h1]; exact hfa
      have hΔ2 : Δ ≤ |H2 a'_J| + deriv H2 a'_J := by
        have h1 : H2 a'_J = Hfunc b_J := by simp [H2, a'_J] <;> ring
        have h2 : deriv H2 a'_J = -deriv Hfunc b_J := by
          rw [h_eq1 a'_J]
          have h3 : a + b - a'_J = b_J := by simp [a'_J] <;> ring
          rw [h3]
        have h3 : Δ ≤ |Hfunc b_J| + |deriv Hfunc b_J| := hΔ_J b_J ⟨by linarith [haJ_le_bJ], by linarith [haJ_le_bJ]⟩
        have h4 : deriv Hfunc b_J < 0 := hH'_neg b_J ⟨by linarith [haJ_le_bJ], by linarith [haJ_le_bJ]⟩
        have h5 : |deriv Hfunc b_J| = -deriv Hfunc b_J := abs_of_neg h4
        rw [h1, h2]; rw [h5] at h3; exact h3
      have ha'J_le_a : a'_J ≤ a := by
        dsimp only [a'_J]
        have hpos : 0 < 1 / (96 * K) := by positivity
        have h : b ≤ b_J := by linarith [h_geom7, hpos]
        linarith
      have hb_le_b'J : b ≤ b'_J := by
        dsimp only [b'_J]
        have hpos : 0 < 1 / (96 * K) := by positivity
        have h : a_J ≤ a := by linarith [h_geom5, hpos]
        linarith
      exact constant_sign_geometric_bound hH2_diff1 hH2_diff2 hK hd_pos hδ_pos ht_pos hδt ht1 hL_eq hL_le hL_pos
        ha'J_le_a hb_le_b'J h_ab_L h_geom_low2 h_geom_high2
        hH2'_pos hH2''_ge hH2a hH2b hΔ2
-/

/-- The fixed value-gap form is the `M = 10` specialization of the robust main proof. -/
lemma common_tangent_main_proof
    (K d delta t L a b a_J b_J Δ : ℝ)
    (I : ParameterInterval)
    (hK : 1 ≤ K)
    (hK_pos : 0 < K)
    (hd_pos : 0 < d)
    (hδ_pos : 0 < delta)
    (ht_pos : 0 < t)
    (hδt : delta ≤ t)
    (ht1 : t ≤ 1)
    (hL_eq : L = Real.sqrt (delta / t))
    (hL_le : L ≤ 1 / (24 * K))
    (hL_pos : 0 < L)
    (h_ab_L : b - a = L)
    (hab : a ≤ b)
    (ha_in_I : a ∈ Set.Icc I.left I.right)
    (hb_in_I : b ∈ Set.Icc I.left I.right)
    (hJ_sub_I : Set.Icc a_J b_J ⊆ Set.Icc I.left I.right)
    (hR_sub_J : Set.Icc a b ⊆ Set.Icc a_J b_J)
    (h_geom5 : a - a_J ≥ 1 / (96 * K))
    (h_geom6 : a - a_J ≤ 1)
    (h_geom7 : b_J - b ≥ 1 / (96 * K))
    (h_geom8 : b_J - b ≤ 1 / (16 * K))
    (Hfunc : ℝ → ℝ)
    (hdiff1 : Differentiable ℝ Hfunc)
    (hdiff2 : Differentiable ℝ (deriv Hfunc))
    (hpos : ∀ x ∈ Set.Icc I.left I.right, d / (2 * K) ≤ deriv (deriv Hfunc) x)
    (habs : ∀ x ∈ Set.Icc I.left I.right, |deriv (deriv Hfunc) x| ≤ d)
    (hfa : |Hfunc a| ≤ 10 * delta)
    (hfb : |Hfunc b| ≤ 10 * delta)
    (hint : ∀ (x0 : ℝ), x0 ∈ Set.Icc a b → |Hfunc x0| ≤ 10 * delta)
    (hΔ_J : ∀ (x0 : ℝ), x0 ∈ Set.Icc a_J b_J →
      Δ ≤ |Hfunc x0| + |deriv Hfunc x0|) :
    (Δ + delta) * d ≤ 270000 * K^2 * delta * t := by
  have h := common_tangent_main_proof_general K d delta t L a b a_J b_J Δ 10 I
    hK hK_pos hd_pos hδ_pos ht_pos hδt ht1 hL_eq hL_le hL_pos h_ab_L hab
    ha_in_I hb_in_I hJ_sub_I hR_sub_J h_geom5 h_geom6 h_geom7 h_geom8
    Hfunc hdiff1 hdiff2 hpos habs (by norm_num) hfa hfb hint hΔ_J
  convert h using 1 <;> ring

end Kakeya.Cinematic
