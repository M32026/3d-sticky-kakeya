import MyLeanRepo.Kakeya.Cinematic.Targets.TangencySublevelDiameter.Helpers
import MyLeanRepo.Kakeya.Cinematic.Targets.CommonTangentRectangleHelpers
import MyLeanRepo.Kakeya.Cinematic.Targets.CommonTangentRectangleRobustHelpers
import MyLeanRepo.Kakeya.Cinematic.Statements


/-!
# Generalized main proof for robust common-tangent rectangle

This module generalizes `zero_crossing_left_final` and `common_tangent_main_proof`
to take a value-gap multiplier `M : ℝ` (with `1 ≤ M`) instead of hardcoding `10`.
-/

namespace Kakeya.Cinematic

private lemma reflected_left_gap (a b b_J : ℝ) :
    a - (a + b - b_J) = b_J - b := by
  ring

private lemma reflected_left_endpoint (a b : ℝ) :
    a + b - a = b := by
  ring

private lemma reflected_right_endpoint (a b : ℝ) :
    a + b - b = a := by
  ring

private lemma reflected_outer_endpoint (a b b_J : ℝ) :
    a + b - (a + b - b_J) = b_J := by
  ring

private lemma inv_sixteen_mul_le_one {K : ℝ} (hK : 1 ≤ K) :
    1 / (16 * K) ≤ 1 := by
  calc
    1 / (16 * K) ≤ 1 / 16 := by
      gcongr
      nlinarith
    _ ≤ 1 := by norm_num

private lemma le_of_gap_lower {K x y : ℝ} (hK : 0 < K)
    (hgap : 1 / (96 * K) ≤ x - y) :
    y ≤ x := by
  have hpositive : 0 < 1 / (96 * K) := by positivity
  linarith

private lemma reflected_delta_bound
    {H H2 : ℝ → ℝ} {a b a_J b_J Δ : ℝ}
    (haJ_le_bJ : a_J ≤ b_J)
    (hH2 : ∀ x, H2 x = H (a + b - x))
    (hderiv : ∀ x, deriv H2 x = -deriv H (a + b - x))
    (hneg : ∀ x ∈ Set.Icc a_J b_J, deriv H x < 0)
    (hΔ : ∀ x ∈ Set.Icc a_J b_J, Δ ≤ |H x| + |deriv H x|) :
    Δ ≤ |H2 (a + b - b_J)| + deriv H2 (a + b - b_J) := by
  have hbJ_mem : b_J ∈ Set.Icc a_J b_J := ⟨haJ_le_bJ, le_rfl⟩
  have hbound := hΔ b_J hbJ_mem
  have hnegative := hneg b_J hbJ_mem
  rw [abs_of_neg hnegative] at hbound
  rw [hH2, reflected_outer_endpoint, hderiv, reflected_outer_endpoint]
  exact hbound

/-- Reflection facts for H2(x) = H(a+b-x): differentiability and derivative formulas. -/
lemma reflection_facts_general
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

/-- Generalized helper: when H'(x0)=0 with x0 < a, prove the final bound
with value gap Mδ. -/
lemma zero_crossing_left_final_general
    {H : ℝ → ℝ} {K d delta t L a b x0 Δ M : ℝ}
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
    (hM : 1 ≤ M)
    (h_bound : ∀ z ∈ Set.Icc a b, |H z| ≤ M * delta)
    (hfa : |H a| ≤ M * delta)
    (hfb : |H b| ≤ M * delta)
    (hΔ_x0 : Δ ≤ |H x0|)
    (h_d_le_from_var : (0 ≤ deriv H a) → d ≤ 8 * K * M * t) :
    (Δ + delta) * d ≤ 2700 * K^2 * M^2 * delta * t := by
  have h_zcl := zero_crossing_left hH1 hH2 hx0_lt_a hab hderiv0
    hH''_ge hH''_le h_bound (by positivity) (by positivity) (by positivity)
  set u : ℝ := a - x0 with hu_def
  have h_u_pos : 0 < u := by linarith
  have h_var_raw : d / (2 * K) * u * (b - a) + d / (2 * K) / 2 * (b - a)^2 ≤ 2 * (M * delta) := h_zcl.2.1
  have h_var : d / (2 * K) * u * L + d / (4 * K) * L^2 ≤ 2 * M * delta := by
    have h9 : (b - a) = L := h_ab_L
    have h10 : d / (2 * K) * u * (b - a) + d / (2 * K) / 2 * (b - a)^2 = d / (2 * K) * u * L + d / (4 * K) * L^2 := by
      rw [h9] <;> ring
    have h11 : 2 * (M * delta) = 2 * M * delta := by ring
    rw [h10, h11] at h_var_raw
    exact h_var_raw
  have h_pos1 : 0 ≤ d / (4 * K) * L^2 := by positivity
  have h2 : d / (2 * K) * u * L ≤ 2 * M * delta := by linarith
  have h3 : d * u * L ≤ 4 * K * M * delta := by
    have h4 : d / (2 * K) * u * L = d * u * L / (2 * K) := by ring
    rw [h4] at h2
    calc d * u * L
        = (d * u * L / (2 * K)) * (2 * K) := by field_simp [hK_pos.ne'] <;> ring
      _ ≤ (2 * M * delta) * (2 * K) := by gcongr
      _ = 4 * K * M * delta := by ring
  have h6 : 0 < L := hL_pos
  have h_d_u_le : d * u ≤ 4 * K * M * delta / L := by
    calc d * u
        = (d * u * L) / L := by field_simp [h6.ne'] <;> ring
      _ ≤ (4 * K * M * delta) / L := by gcongr
      _ = 4 * K * M * delta / L := by ring
  have h_Hx0 : |H x0| ≤ M * delta + d * u^2 / 2 := h_zcl.2.2
  have hΔ_le : Δ ≤ M * delta + d * u^2 / 2 := by linarith [hΔ_x0, h_Hx0]
  have h_d2u2 : d^2 * u^2 / 2 ≤ 8 * K^2 * M^2 * delta * t := by
    have h1 : 0 ≤ d * u := by positivity
    have h2 : d^2 * u^2 ≤ (4 * K * M * delta / L)^2 := by
      have h3 : d * u ≤ 4 * K * M * delta / L := h_d_u_le
      have h4 : 0 ≤ 4 * K * M * delta / L := by positivity
      nlinarith
    have h5 : (4 * K * M * delta / L)^2 = 16 * K^2 * M^2 * delta^2 / L^2 := by ring
    have h6 : L^2 = delta / t := by
      rw [hL_eq]; rw [Real.sq_sqrt (by positivity)]
    have h7 : 16 * K^2 * M^2 * delta^2 / L^2 = 16 * K^2 * M^2 * delta * t := by
      rw [h6]; field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
    have h8 : d^2 * u^2 ≤ 16 * K^2 * M^2 * delta * t := by
      rw [h5, h7] at h2; exact h2
    linarith
  have h_H'a_pos : 0 ≤ deriv H a := by
    have h : deriv H a ≥ d / (2 * K) * u := h_zcl.1
    have h_pos : 0 < d / (2 * K) * u := by positivity
    linarith
  have h_d_le : d ≤ 8 * K * M * t := h_d_le_from_var h_H'a_pos
  have h_M1δd : (M + 1) * delta * d ≤ 16 * K^2 * M^2 * delta * t := by
    have h4 : (M + 1) * delta * d ≤ 8 * M * (M + 1) * K * delta * t := by
      calc (M + 1) * delta * d
        ≤ (M + 1) * delta * (8 * K * M * t) := by gcongr
      _ = 8 * M * (M + 1) * K * delta * t := by ring
    have h6 : M + 1 ≤ 2 * K * M := by
      have h7 : M + 1 ≤ 2 * M := by linarith [hM]
      have h8 : 2 * M ≤ 2 * K * M := by
        have h9 : 0 ≤ M := by linarith
        nlinarith [hK]
      linarith
    have h7 : 0 ≤ 8 * M * K * delta * t := by positivity
    have h10 : 8 * M * (M + 1) * K * delta * t ≤ 16 * K^2 * M^2 * delta * t := by
      have h11 : 8 * M * (M + 1) * K * delta * t = 8 * M * K * delta * t * (M + 1) := by ring
      have h12 : 16 * K^2 * M^2 * delta * t = 8 * M * K * delta * t * (2 * K * M) := by ring
      rw [h11, h12]
      exact mul_le_mul_of_nonneg_left h6 h7
    exact le_trans h4 h10
  have h_main : (Δ + delta) * d ≤ (M + 1) * delta * d + d^2 * u^2 / 2 := by
    have h1 : (Δ + delta) * d ≤ (M * delta + d * u^2 / 2 + delta) * d := by gcongr <;> linarith [hΔ_le]
    have h2 : (M * delta + d * u^2 / 2 + delta) * d = (M + 1) * delta * d + d^2 * u^2 / 2 := by ring
    rw [h2] at h1; exact h1
  have h_sum : (M + 1) * delta * d + d^2 * u^2 / 2 ≤ 16 * K^2 * M^2 * delta * t + 8 * K^2 * M^2 * delta * t :=
    add_le_add h_M1δd h_d2u2
  have h_final2 : 16 * K^2 * M^2 * delta * t + 8 * K^2 * M^2 * delta * t = 24 * K^2 * M^2 * delta * t := by ring
  have h_final3 : 24 * K^2 * M^2 * delta * t ≤ 2700 * K^2 * M^2 * delta * t := by
    have h_pos : 0 ≤ K^2 * M^2 * delta * t := by positivity
    have h : (24 : ℝ) ≤ (2700 : ℝ) := by norm_num
    have h' : 24 * (K^2 * M^2 * delta * t) ≤ 2700 * (K^2 * M^2 * delta * t) :=
      mul_le_mul_of_nonneg_right h h_pos
    simpa [mul_assoc] using h'
  rw [h_final2] at h_sum
  exact le_trans h_main (le_trans h_sum h_final3)

/-- Generalized main sub-proof of PYZ Lemma 17: value gap Mδ instead of 10δ. -/
lemma common_tangent_main_proof_general
    (K d delta t L a b a_J b_J Δ M : ℝ)
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
    (hM : 1 ≤ M)
    (hfa : |Hfunc a| ≤ M * delta)
    (hfb : |Hfunc b| ≤ M * delta)
    (hint : ∀ (x0 : ℝ), x0 ∈ Set.Icc a b → |Hfunc x0| ≤ M * delta)
    (hΔ_J : ∀ (x0 : ℝ), x0 ∈ Set.Icc a_J b_J → Δ ≤ |Hfunc x0| + |deriv Hfunc x0|) :
    (Δ + delta) * d ≤ 2700 * K^2 * M^2 * delta * t := by
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
  have h_var_bound : |Hfunc b - Hfunc a| ≤ 2 * M * delta := by
    have h3 : |Hfunc b - Hfunc a| ≤ |Hfunc b| + |Hfunc a| := by
      calc |Hfunc b - Hfunc a|
          ≤ |Hfunc b| + |(-Hfunc a)| := by exact abs_add_le (Hfunc b) (-Hfunc a)
        _ = |Hfunc b| + |Hfunc a| := by rw [abs_neg]
    linarith [abs_le.mp hfa, abs_le.mp hfb]
  have h_d_le_from_var : (0 ≤ deriv Hfunc a) → d ≤ 8 * K * M * t := by
    intro hpos'
    have h_upper : Hfunc b - Hfunc a ≤ 2 * M * delta := (abs_le.mp h_var_bound).2
    have h : deriv Hfunc a * L + d / (4 * K) * L^2 ≤ 2 * M * delta := by
      calc deriv Hfunc a * L + d / (4 * K) * L^2
          ≤ Hfunc b - Hfunc a := h_var_lower_a
        _ ≤ 2 * M * delta := h_upper
    have h_pos1 : 0 ≤ deriv Hfunc a * L := by positivity
    have h2 : d / (4 * K) * L^2 ≤ 2 * M * delta := by linarith
    have h3 : d * L^2 ≤ 8 * K * M * delta := by
      have h4 : d / (4 * K) * L^2 = d * L^2 / (4 * K) := by ring
      rw [h4] at h2
      calc d * L^2
          = (d * L^2 / (4 * K)) * (4 * K) := by field_simp [hK_pos.ne'] <;> ring
        _ ≤ (2 * M * delta) * (4 * K) := by gcongr
        _ = 8 * K * M * delta := by ring
    have hL2 : L^2 = delta / t := by
      rw [hL_eq]; rw [Real.sq_sqrt (by positivity)]
    rw [hL2] at h3
    have h5 : d * (delta / t) ≤ 8 * K * M * delta := h3
    have h6 : d ≤ 8 * K * M * t := by
      calc d
          = (d * (delta / t)) * t / delta := by field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
        _ ≤ (8 * K * M * delta) * t / delta := by gcongr
        _ = 8 * K * M * t := by field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
    exact h6
  have h_d_le_from_abs_var : (0 ≤ -deriv Hfunc b) → d ≤ 8 * K * M * t := by
    intro hpos'
    have h_upper : Hfunc a - Hfunc b ≤ 2 * M * delta := by
      have h : |Hfunc a - Hfunc b| ≤ 2 * M * delta := by
        have h5 : |Hfunc a - Hfunc b| = |Hfunc b - Hfunc a| := by
          have h6 : Hfunc a - Hfunc b = -(Hfunc b - Hfunc a) := by ring
          rw [h6, abs_neg]
        rw [h5]; exact h_var_bound
      have h7 : Hfunc a - Hfunc b ≤ |Hfunc a - Hfunc b| := le_abs_self (Hfunc a - Hfunc b)
      linarith
    have h : -deriv Hfunc b * L + d / (4 * K) * L^2 ≤ 2 * M * delta := by
      calc -deriv Hfunc b * L + d / (4 * K) * L^2
          ≤ Hfunc a - Hfunc b := h_var_lower_b
        _ ≤ 2 * M * delta := h_upper
    have h_pos1 : 0 ≤ -deriv Hfunc b * L := by positivity
    have h2 : d / (4 * K) * L^2 ≤ 2 * M * delta := by linarith
    have h3 : d * L^2 ≤ 8 * K * M * delta := by
      have h4 : d / (4 * K) * L^2 = d * L^2 / (4 * K) := by ring
      rw [h4] at h2
      calc d * L^2
          = (d * L^2 / (4 * K)) * (4 * K) := by field_simp [hK_pos.ne'] <;> ring
        _ ≤ (2 * M * delta) * (4 * K) := by gcongr
        _ = 8 * K * M * delta := by ring
    have hL2 : L^2 = delta / t := by
      rw [hL_eq]; rw [Real.sq_sqrt (by positivity)]
    rw [hL2] at h3
    have h5 : d * (delta / t) ≤ 8 * K * M * delta := h3
    have h6 : d ≤ 8 * K * M * t := by
      calc d
          = (d * (delta / t)) * t / delta := by field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
        _ ≤ (8 * K * M * delta) * t / delta := by gcongr
        _ = 8 * K * M * t := by field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
    exact h6
  have h_int_bound : ∀ (x0 : ℝ), x0 ∈ Set.Icc a b → |Hfunc x0| ≤ M * delta := hint
  by_cases h_zero : ∃ (x0 : ℝ), x0 ∈ J_set ∧ deriv Hfunc x0 = 0
  · rcases h_zero with ⟨x0, hx0_J, hderiv0⟩
    have hΔ_x0 : Δ ≤ |Hfunc x0| := by
      have h1 : Δ ≤ |Hfunc x0| + |deriv Hfunc x0| := hΔ_J x0 hx0_J
      rw [hderiv0] at h1; simpa using h1
    by_cases h_x0_in_R : x0 ∈ Set.Icc a b
    · -- Case x0 ∈ [a,b]
      have hH_x0 : |Hfunc x0| ≤ M * delta := h_int_bound x0 h_x0_in_R
      have h1 : Δ ≤ M * delta := by linarith [hΔ_x0, hH_x0]
      have h_dL2_bound : d * L^2 ≤ 32 * K * M * delta := by
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
        have h_endpoints : Hfunc a + Hfunc b ≤ 2 * M * delta := by
          have h1 : Hfunc a ≤ M * delta := by linarith [abs_le.mp hfa]
          have h2 : Hfunc b ≤ M * delta := by linarith [abs_le.mp hfb]
          linarith
        have h9 : 2 * Hfunc x0 + d / (4 * K) * (L^2 / 2) ≤ 2 * M * delta := by
          calc 2 * Hfunc x0 + d / (4 * K) * (L^2 / 2)
              ≤ 2 * Hfunc x0 + d / (4 * K) * ((a - x0)^2 + (b - x0)^2) := by gcongr
            _ ≤ Hfunc a + Hfunc b := h_sum
            _ ≤ 2 * M * delta := h_endpoints
        have h10 : Hfunc x0 ≥ -(M * delta) := by
          have h11 : |Hfunc x0| ≤ M * delta := hH_x0
          linarith [abs_le.mp h11]
        have h12 : d / (4 * K) * (L^2 / 2) ≤ 4 * M * delta := by linarith
        have h13 : d * L^2 ≤ 32 * K * M * delta := by
          have h14 : d / (4 * K) * (L^2 / 2) = d * L^2 / (8 * K) := by ring
          rw [h14] at h12
          calc d * L^2
              = (d * L^2 / (8 * K)) * (8 * K) := by field_simp [hK_pos.ne'] <;> ring
            _ ≤ (4 * M * delta) * (8 * K) := by gcongr
            _ = 32 * K * M * delta := by ring
        exact h13
      have h_d_le : d ≤ 32 * K * M * t := by
        have h11 : L^2 = delta / t := by
          rw [hL_eq]; rw [Real.sq_sqrt (by positivity)]
        rw [h11] at h_dL2_bound
        have h12 : d * (delta / t) ≤ 32 * K * M * delta := h_dL2_bound
        calc d
            = (d * (delta / t)) * t / delta := by field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
          _ ≤ (32 * K * M * delta) * t / delta := by gcongr
          _ = 32 * K * M * t := by field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
      have h2 : (Δ + delta) * d ≤ (M + 1) * delta * d := by gcongr <;> linarith
      have h3 : (M + 1) * delta * d ≤ 64 * K^2 * M^2 * delta * t := by
        have h4 : (M + 1) * delta * d ≤ 32 * M * (M + 1) * K * delta * t := by
          calc (M + 1) * delta * d
            ≤ (M + 1) * delta * (32 * K * M * t) := by gcongr
          _ = 32 * M * (M + 1) * K * delta * t := by ring
        have h6 : M + 1 ≤ 2 * K * M := by
          have h7 : M + 1 ≤ 2 * M := by linarith [hM]
          have h8 : 2 * M ≤ 2 * K * M := by
            have h9 : 0 ≤ M := by linarith
            nlinarith [hK]
          linarith
        have h7 : 0 ≤ 32 * M * K * delta * t := by positivity
        have h10 : 32 * M * (M + 1) * K * delta * t ≤ 64 * K^2 * M^2 * delta * t := by
          have h11 : 32 * M * (M + 1) * K * delta * t = 32 * M * K * delta * t * (M + 1) := by ring
          have h12 : 64 * K^2 * M^2 * delta * t = 32 * M * K * delta * t * (2 * K * M) := by ring
          rw [h11, h12]
          exact mul_le_mul_of_nonneg_left h6 h7
        exact le_trans h4 h10
      have h4 : 64 * K^2 * M^2 * delta * t ≤ 2700 * K^2 * M^2 * delta * t := by
        have h : 0 ≤ K^2 * M^2 * delta * t := by positivity
        have h5 : (64 : ℝ) ≤ 2700 := by norm_num
        have h6 : 64 * (K^2 * M^2 * delta * t) ≤ 2700 * (K^2 * M^2 * delta * t) :=
          mul_le_mul_of_nonneg_right h5 h
        simpa [mul_assoc] using h6
      exact le_trans (le_trans h2 h3) h4
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
        exact zero_crossing_left_final_general hdiff1 hdiff2 hK hK_pos hd_pos hδ_pos ht_pos hL_eq hL_pos h_ab_L hab
          h_x0_lt_a hderiv0 hH''_ge_x0b hH''_le_x0a hM h_int_bound hfa hfb hΔ_x0 h_d_le_from_var
      · -- Case x0 > b: reflect
        let H2 : ℝ → ℝ := fun x => Hfunc (a + b - x)
        have h_refl := reflection_facts_general Hfunc H2 a b (fun _ => rfl) hdiff1 hdiff2
        rcases h_refl with ⟨hH2_diff1, hH2_diff2, h_eq1, hH2''_eq⟩
        let x0' : ℝ := a + b - x0
        have h_x0'_lt_a : x0' < a := by dsimp only [x0']; linarith
        have h_deriv0' : deriv H2 x0' = 0 := by
          have h1 : deriv H2 x0' = -deriv Hfunc x0 := by
            have h_eq : a + b - x0' = x0 := by simp [x0'] <;> ring
            rw [h_eq1 x0', h_eq]
          rw [h1, hderiv0]; ring
        have hH2a : |H2 a| ≤ M * delta := by
          have h1 : H2 a = Hfunc b := by simp [H2] <;> ring
          rw [h1]; exact hfb
        have hH2b : |H2 b| ≤ M * delta := by
          have h1 : H2 b = Hfunc a := by simp [H2] <;> ring
          rw [h1]; exact hfa
        have hH2_int : ∀ (z : ℝ), z ∈ Set.Icc a b → |H2 z| ≤ M * delta := by
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
        have h_d_le_from_var_H2 : (0 ≤ deriv H2 a) → d ≤ 8 * K * M * t := by
          intro h
          have h' : 0 ≤ -deriv Hfunc b := by
            have h_eq : deriv H2 a = -deriv Hfunc b := by
              rw [h_eq1 a]
              ring_nf
            rw [h_eq] at h; exact h
          exact h_d_le_from_abs_var h'
        exact zero_crossing_left_final_general hH2_diff1 hH2_diff2 hK hK_pos hd_pos hδ_pos ht_pos hL_eq hL_pos h_ab_L hab
          h_x0'_lt_a h_deriv0' hH2''_ge_x0'b hH2''_le_x0'a hM hH2_int hH2a hH2b hH2Δ_x0 h_d_le_from_var_H2
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
      exact constant_sign_geometric_bound_general hdiff1 hdiff2 hK hM hd_pos hδ_pos ht_pos hδt ht1 hL_eq hL_le hL_pos
        haJ_le_a hb_le_bJ h_ab_L h_geom5 h_geom6
        hH'_pos hpos_J hfa hfb hΔ_aJ
    · -- Negative sign: reflect
      let a'_J : ℝ := a + b - b_J
      let b'_J : ℝ := a + b - a_J
      let H2 : ℝ → ℝ := fun x => Hfunc (a + b - x)
      have h_refl := reflection_facts_general Hfunc H2 a b (fun _ => rfl) hdiff1 hdiff2
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
          exact reflected_left_gap a b b_J
        rw [h_eq]
        exact h_geom7
      have h_geom_high2 : a - a'_J ≤ 1 := by
        rw [show a - a'_J = b_J - b from reflected_left_gap a b b_J]
        exact h_geom8.trans (inv_sixteen_mul_le_one hK)
      have hH2a : |H2 a| ≤ M * delta := by
        have h1 : H2 a = Hfunc b := by
          change Hfunc (a + b - a) = Hfunc b
          rw [reflected_left_endpoint]
        rw [h1]; exact hfb
      have hH2b : |H2 b| ≤ M * delta := by
        have h1 : H2 b = Hfunc a := by
          change Hfunc (a + b - b) = Hfunc a
          rw [reflected_right_endpoint]
        rw [h1]; exact hfa
      have hΔ2 : Δ ≤ |H2 a'_J| + deriv H2 a'_J := by
        exact reflected_delta_bound haJ_le_bJ (fun _ => rfl) h_eq1 hH'_neg hΔ_J
      have ha'J_le_a : a'_J ≤ a := by
        dsimp only [a'_J]
        have h : b ≤ b_J := le_of_gap_lower hK_pos h_geom7
        linarith
      have hb_le_b'J : b ≤ b'_J := by
        dsimp only [b'_J]
        have h : a_J ≤ a := le_of_gap_lower hK_pos h_geom5
        linarith
      exact constant_sign_geometric_bound_general hH2_diff1 hH2_diff2 hK hM hd_pos hδ_pos ht_pos hδt ht1 hL_eq hL_le hL_pos
        ha'J_le_a hb_le_b'J h_ab_L h_geom_low2 h_geom_high2
        hH2'_pos hH2''_ge hH2a hH2b hΔ2

end Kakeya.Cinematic
