import MyLeanRepo.Kakeya.Cinematic.Geometry
import MyLeanRepo.Kakeya.Cinematic.Targets.TangencySublevelDiameter.Helpers
import MyLeanRepo.Kakeya.Cinematic.Targets.CommonTangentRectangleHelpers
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Sqrt

/-!
# Generalized helper lemmas for CommonTangentRectangleRobust (PYZ Lemma 17)

These lemmas generalize the value-gap bounds from a fixed multiplier of 10
to an arbitrary multiplier `M ≥ 1`, enabling polynomially uniform bounds
in the tangency dilation parameter.
-/

namespace Kakeya.Cinematic

/-- If both f and g are λ-tangent to R (λ ≥ 1), then
`|f x - g x| ≤ 2 * (λ - 1) * δ` on R.interval. -/
lemma both_tangent_implies_close_general {δ t : ℝ} (hδ : 0 < δ)
    (R : CurvilinearRectangle δ t) (f g : C2Function) {lambda : ℝ}
    (hlambda : 1 ≤ lambda)
    (hf : R.IsLambdaTangent f lambda) (hg : R.IsLambdaTangent g lambda) :
    ∀ (x : UnitPoint), x ∈ R.interval.carrier →
      |f x - g x| ≤ 2 * (lambda - 1) * δ := by
  intro x hx
  have h1 : |f x - R.function x| ≤ (lambda - 1) * δ :=
    tangency_implies_value_close hδ R f hlambda hf x hx
  have h2 : |g x - R.function x| ≤ (lambda - 1) * δ :=
    tangency_implies_value_close hδ R g hlambda hg x hx
  have h_main : |f x - g x| ≤ |f x - R.function x| + |g x - R.function x| := by
    have h_eq : f x - g x = (f x - R.function x) - (g x - R.function x) := by ring
    rw [h_eq]
    exact abs_sub _ _
  calc
    |f x - g x| ≤ |f x - R.function x| + |g x - R.function x| := h_main
    _ ≤ (lambda - 1) * δ + (lambda - 1) * δ := by gcongr
    _ = 2 * (lambda - 1) * δ := by ring

/-- Generalized upper bound on H'(a) from variation:
H'(a) ≤ 2*M*δ/L - d*L/(4*K). -/
lemma variation_H'a_upper_general {H : ℝ → ℝ} {K d delta L M a b : ℝ}
    (hH1 : Differentiable ℝ H)
    (hH2 : Differentiable ℝ (deriv H))
    (hK_pos : 0 < K)
    (hd_pos : 0 < d)
    (hδ_pos : 0 < delta)
    (hL_pos : 0 < L)
    (hM_nonneg : 0 ≤ M)
    (hab : a ≤ b)
    (hba : b - a = L)
    (hH''_ge : ∀ x ∈ Set.Icc a b, d / (2 * K) ≤ deriv (deriv H) x)
    (hHa_bound : |H a| ≤ M * delta)
    (hHb_bound : |H b| ≤ M * delta) :
    deriv H a ≤ 2 * M * delta / L - d * L / (4 * K) := by
  have ha_in : a ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  have hb_in : b ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  have h_var : H b - H a ≥ deriv H a * (b - a) + (d / (2 * K)) / 2 * (b - a)^2 :=
    variation_lower_bound hH1 hH2 hab ha_in hb_in hH''_ge
  have h_var2 : H b - H a ≥ deriv H a * L + d * L^2 / (4 * K) := by
    have h9 : (b - a) = L := hba
    rw [h9] at h_var
    have h10 : (d / (2 * K)) / 2 * L^2 = d * L^2 / (4 * K) := by ring
    rw [h10] at h_var
    exact h_var
  have h3 : H b - H a ≤ 2 * M * delta := by
    linarith [abs_le.mp hHa_bound, abs_le.mp hHb_bound]
  have h4 : deriv H a * L + d * L^2 / (4 * K) ≤ 2 * M * delta := by linarith
  have h5 : deriv H a * L ≤ 2 * M * delta - d * L^2 / (4 * K) := by linarith
  have h6 : deriv H a ≤ (2 * M * delta - d * L^2 / (4 * K)) / L := by
    have h7 : deriv H a = (deriv H a * L) / L := by field_simp [hL_pos.ne'] <;> ring
    rw [h7]
    gcongr
  have h8 : (2 * M * delta - d * L^2 / (4 * K)) / L = 2 * M * delta / L - d * L / (4 * K) := by
    field_simp [hL_pos.ne'] <;> ring
  rw [h8] at h6
  exact h6

/-- Generalized bound on Δ at a_J: Δ ≤ M*δ + 2*H'(a). -/
lemma Delta_bound_general {H : ℝ → ℝ} {K delta M a_J b_J a Δ : ℝ}
    (hH1 : Differentiable ℝ H)
    (hH2 : Differentiable ℝ (deriv H))
    (hK : 1 ≤ K)
    (hM_nonneg : 0 ≤ M)
    (haJ_le_a : a_J ≤ a)
    (hb_le_bJ : a ≤ b_J)
    (h_geometric_high : a - a_J ≤ 1)
    (hH'_pos : ∀ x ∈ Set.Icc a_J b_J, 0 < deriv H x)
    (hH''_nonneg : ∀ x ∈ Set.Icc a_J b_J, 0 ≤ deriv (deriv H) x)
    (hHa_bound : |H a| ≤ M * delta)
    (hΔ : Δ ≤ |H a_J| + deriv H a_J) :
    Δ ≤ M * delta + (2 : ℝ) * deriv H a := by
  have hK_pos : 0 < K := by linarith
  have h_a_in_J : a ∈ Set.Icc a_J b_J := ⟨by linarith, by linarith⟩
  have h_aJ_in_J : a_J ∈ Set.Icc a_J b_J := ⟨by linarith, by linarith⟩
  have h_H'_mono : ∀ (x y : ℝ), x ∈ Set.Icc a_J b_J → y ∈ Set.Icc a_J b_J → x ≤ y → deriv H x ≤ deriv H y :=
    fun x y hx hy hxy => deriv_monotone_of_deriv2_nonneg hH1 hH2 hH''_nonneg hx hy hxy

  have h4a : H a_J ≤ M * delta := by
    by_cases h : a_J = a
    · rw [h]; exact (abs_le.mp hHa_bound).2
    · have h_aj_lt_a : a_J < a := lt_of_le_of_ne haJ_le_a h
      have hsub : Set.Icc a_J a ⊆ Set.Icc a_J b_J := by
        intro z hz; exact ⟨by linarith [hz.1], by linarith [hz.2, hb_le_bJ]⟩
      have hcont_H : ContinuousOn H (Set.Icc a_J a) := hH1.continuous.continuousOn.mono hsub
      have hfd_H : ∀ z ∈ Set.Ioo a_J a, HasDerivAt H (deriv H z) z :=
        fun z _ => hH1.differentiableAt.hasDerivAt
      have h_mvt : ∃ (z : ℝ), z ∈ Set.Ioo a_J a ∧ deriv H z = (H a - H a_J) / (a - a_J) :=
        exists_hasDerivAt_eq_slope (f := H) (f' := deriv H) h_aj_lt_a hcont_H hfd_H
      rcases h_mvt with ⟨z, hz_in, hderiv⟩
      have hz_in_J : z ∈ Set.Icc a_J b_J := hsub ⟨by linarith [hz_in.1], by linarith [hz_in.2]⟩
      have h_pos : 0 < deriv H z := hH'_pos z hz_in_J
      have h_pos2 : 0 < a - a_J := by linarith
      have h_eq : H a - H a_J = deriv H z * (a - a_J) := by
        rw [hderiv] <;> field_simp [h_pos2.ne'] <;> ring
      have h9 : H a_J ≤ H a := by
        have h10 : 0 ≤ deriv H z * (a - a_J) := by positivity
        linarith [h_eq]
      have h11 : H a ≤ M * delta := (abs_le.mp hHa_bound).2
      linarith

  have h4b : H a_J ≥ -(M * delta) - deriv H a * (a - a_J) := by
    by_cases h : a_J = a
    · subst h; simpa using (abs_le.mp hHa_bound).1
    · have h_aj_lt_a : a_J < a := lt_of_le_of_ne haJ_le_a h
      have hsub : Set.Icc a_J a ⊆ Set.Icc a_J b_J := by
        intro z hz; exact ⟨by linarith [hz.1], by linarith [hz.2, hb_le_bJ]⟩
      have hcont_H : ContinuousOn H (Set.Icc a_J a) := hH1.continuous.continuousOn.mono hsub
      have hfd_H : ∀ z ∈ Set.Ioo a_J a, HasDerivAt H (deriv H z) z :=
        fun z _ => hH1.differentiableAt.hasDerivAt
      have h_mvt : ∃ (z : ℝ), z ∈ Set.Ioo a_J a ∧ deriv H z = (H a - H a_J) / (a - a_J) :=
        exists_hasDerivAt_eq_slope (f := H) (f' := deriv H) h_aj_lt_a hcont_H hfd_H
      rcases h_mvt with ⟨z, hz_in, hderiv⟩
      have hz_in_J : z ∈ Set.Icc a_J b_J := hsub ⟨by linarith [hz_in.1], by linarith [hz_in.2]⟩
      have hz_le_a : z ≤ a := hz_in.2.le
      have h_deriv_le : deriv H z ≤ deriv H a := h_H'_mono z a hz_in_J h_a_in_J hz_le_a
      have h_pos2 : 0 < a - a_J := by linarith
      have h_eq : H a - H a_J = deriv H z * (a - a_J) := by
        rw [hderiv] <;> field_simp [h_pos2.ne'] <;> ring
      have h13 : H a - H a_J ≤ deriv H a * (a - a_J) := by
        rw [h_eq] <;> gcongr
      have h14 : H a ≥ -(M * delta) := (abs_le.mp hHa_bound).1
      linarith

  have h4c : |H a_J| ≤ M * delta + deriv H a * (a - a_J) := by
    have h_pos : 0 ≤ deriv H a * (a - a_J) := by
      have h1 : 0 < deriv H a := hH'_pos a h_a_in_J
      have h2 : 0 ≤ a - a_J := by linarith
      positivity
    have h_up : H a_J ≤ M * delta + deriv H a * (a - a_J) := by linarith [h4a]
    have h_low : -(M * delta + deriv H a * (a - a_J)) ≤ H a_J := by linarith [h4b]
    exact abs_le.mpr ⟨h_low, h_up⟩

  have h4d : deriv H a_J ≤ deriv H a := h_H'_mono a_J a h_aJ_in_J h_a_in_J (by linarith)
  have h3 : a - a_J + 1 ≤ (2 : ℝ) := by linarith [h_geometric_high]
  have hHa_pos : 0 ≤ deriv H a := by
    have h : 0 < deriv H a := hH'_pos a h_a_in_J
    linarith
  calc
    Δ ≤ |H a_J| + deriv H a_J := hΔ
    _ ≤ M * delta + deriv H a * (a - a_J) + deriv H a := by linarith [h4c, h4d]
    _ = M * delta + deriv H a * (a - a_J + 1) := by ring
    _ ≤ M * delta + deriv H a * (2 : ℝ) := by
      have h : deriv H a * (a - a_J + 1) ≤ deriv H a * (2 : ℝ) := mul_le_mul_of_nonneg_left h3 hHa_pos
      linarith
    _ = M * delta + (2 : ℝ) * deriv H a := by ring

/-- Generalized geometric bound for Case 2b(ii): H' has constant positive sign on J.
Given value-gap multiplier M ≥ 1, proves
(Δ + δ) * d ≤ 2700 * K^2 * M^2 * δ * t.

Key intermediate bounds:
- d ≤ 384 * K² * M * δ / L
- d ≤ 8 * K * M * t
- y * d ≤ 768 * K² * M² * δ * t
- (M+1) * δ * d ≤ 16 * K² * M² * δ * t (using M ≥ 1)
- Total ≤ 1552 * K² * M² * δ * t ≤ 2700 * K² * M² * δ * t
-/
lemma constant_sign_geometric_bound_general
    {H : ℝ → ℝ} {K d delta t L M a_J b_J a b Δ : ℝ}
    (hH1 : Differentiable ℝ H)
    (hH2 : Differentiable ℝ (deriv H))
    (hK : 1 ≤ K)
    (hM : 1 ≤ M)
    (hd_pos : 0 < d)
    (hδ_pos : 0 < delta)
    (ht_pos : 0 < t)
    (hδt : delta ≤ t)
    (ht1 : t ≤ 1)
    (hL_eq : L = Real.sqrt (delta / t))
    (hL_le : L ≤ 1 / (24 * K))
    (hL_pos : 0 < L)
    (haJ_le_a : a_J ≤ a)
    (hb_le_bJ : b ≤ b_J)
    (hba : b - a = L)
    (h_geometric_low : a - a_J ≥ 1 / (96 * K))
    (h_geometric_high : a - a_J ≤ 1)
    (hH'_pos : ∀ x ∈ Set.Icc a_J b_J, 0 < deriv H x)
    (hH''_ge : ∀ x ∈ Set.Icc a_J b_J, d / (2 * K) ≤ deriv (deriv H) x)
    (hHa_bound : |H a| ≤ M * delta)
    (hHb_bound : |H b| ≤ M * delta)
    (hΔ : Δ ≤ |H a_J| + deriv H a_J) :
    (Δ + delta) * d ≤ 2700 * K^2 * M^2 * delta * t := by
  have hK_pos : 0 < K := by linarith
  have hM_nonneg : 0 ≤ M := by linarith
  let c_geo : ℝ := 2
  have hc_geo : c_geo = 2 := by rfl
  have h_a_in_J : a ∈ Set.Icc a_J b_J := ⟨by linarith, by linarith⟩
  have h_aJ_in_J : a_J ∈ Set.Icc a_J b_J := ⟨by linarith, by linarith⟩
  have hH''_nonneg : ∀ x ∈ Set.Icc a_J b_J, 0 ≤ deriv (deriv H) x := by
    intro x hx
    have h : d / (2 * K) ≤ deriv (deriv H) x := hH''_ge x hx
    have h' : 0 ≤ d / (2 * K) := by positivity
    linarith
  have hH''_ge_ab : ∀ x ∈ Set.Icc a b, d / (2 * K) ≤ deriv (deriv H) x :=
    fun x hx => hH''_ge x ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h1_lower : deriv H a ≥ d / (192 * K^2) :=
    geometric_H'a_lower hH2 hK_pos hd_pos haJ_le_a (by linarith) h_geometric_low
      (hH'_pos a_J h_aJ_in_J) hH''_ge
  have h2_upper : deriv H a ≤ 2 * M * delta / L - d * L / (4 * K) :=
    variation_H'a_upper_general hH1 hH2 hK_pos hd_pos hδ_pos hL_pos hM_nonneg
      (by linarith) hba hH''_ge_ab hHa_bound hHb_bound
  let y : ℝ := 2 * M * delta / L - d * L / (4 * K)
  have hy_def : y = 2 * M * delta / L - d * L / (4 * K) := by rfl
  have hy_pos : 0 < y := by
    have h : 0 < deriv H a := hH'_pos a h_a_in_J
    have h' : deriv H a ≤ y := h2_upper
    exact lt_of_lt_of_le h h'
  have h3_geo : d / (192 * K^2) ≤ y := by
    calc
      d / (192 * K^2) ≤ deriv H a := h1_lower
      _ ≤ y := h2_upper
  have h4Δ : Δ ≤ M * delta + c_geo * deriv H a :=
    Delta_bound_general hH1 hH2 hK hM_nonneg haJ_le_a (by linarith) h_geometric_high
      hH'_pos hH''_nonneg hHa_bound hΔ
  have h5Δ : Δ ≤ M * delta + c_geo * y := by
    have h6 : deriv H a ≤ y := h2_upper
    have h7 : 0 ≤ c_geo := by norm_num
    have h8 : c_geo * deriv H a ≤ c_geo * y := mul_le_mul_of_nonneg_left h6 h7
    linarith [h4Δ, h8]
  have hL2 : L^2 = delta / t := by
    rw [hL_eq]
    rw [Real.sq_sqrt (by positivity)]
  have h_d_bound1 : d ≤ 384 * K^2 * M * delta / L := by
    have h_y_le : y ≤ 2 * M * delta / L := by
      rw [hy_def]
      have h_pos : 0 ≤ d * L / (4 * K) := by positivity
      linarith
    have h2 : d / (192 * K^2) ≤ 2 * M * delta / L := by
      calc
        d / (192 * K^2) ≤ y := h3_geo
        _ ≤ 2 * M * delta / L := h_y_le
    have h5 : 0 < 192 * K^2 := by positivity
    have h4 : d ≤ (2 * M * delta / L) * (192 * K^2) := by
      calc
        d = (d / (192 * K^2)) * (192 * K^2) := by field_simp [h5.ne'] <;> ring
        _ ≤ (2 * M * delta / L) * (192 * K^2) := by gcongr
    have h6 : (2 * M * delta / L) * (192 * K^2) = 384 * K^2 * M * delta / L := by ring
    linarith
  have h_d_bound2 : d ≤ 8 * K * M * t := by
    have h : d * L / (4 * K) < 2 * M * delta / L := by
      have h_pos : 0 < y := hy_pos
      rw [hy_def] at h_pos
      linarith
    have h2 : d * L^2 < 8 * K * M * delta := by
      have h3 : 0 < 4 * K * L := by positivity
      have h5 : 4 * K * L * (d * L / (4 * K)) < 4 * K * L * (2 * M * delta / L) :=
        mul_lt_mul_of_pos_left h h3
      have h6 : 4 * K * L * (2 * M * delta / L) = 8 * K * M * delta := by
        field_simp [hL_pos.ne'] <;> ring
      have h7 : d * L^2 = 4 * K * L * (d * L / (4 * K)) := by
        field_simp [hK_pos.ne', hL_pos.ne'] <;> ring
      calc
        d * L^2 = 4 * K * L * (d * L / (4 * K)) := h7
        _ < 4 * K * L * (2 * M * delta / L) := h5
        _ = 8 * K * M * delta := h6
    rw [hL2] at h2
    have h4 : d * (delta / t) < 8 * K * M * delta := h2
    have h5 : d < 8 * K * M * t := by
      have h6 : 0 < delta / t := by positivity
      calc
        d = d * (delta / t) / (delta / t) := by field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
        _ < (8 * K * M * delta) / (delta / t) := by gcongr
        _ = 8 * K * M * t := by field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
    linarith
  have h_yd_bound : y * d ≤ 768 * K^2 * M^2 * delta * t := by
    have h_y_le : y ≤ 2 * M * delta / L := by
      rw [hy_def]
      have h_pos : 0 ≤ d * L / (4 * K) := by positivity
      linarith
    have h1 : y * d ≤ (2 * M * delta / L) * d :=
      mul_le_mul_of_nonneg_right h_y_le (by linarith)
    have h2 : (2 * M * delta / L) * d ≤ (2 * M * delta / L) * (384 * K^2 * M * delta / L) := by
      gcongr
      <;> linarith
    have h3 : (2 * M * delta / L) * (384 * K^2 * M * delta / L) = 768 * K^2 * M^2 * (delta^2 / L^2) := by ring
    have h4 : delta^2 / L^2 = delta * t := by
      rw [hL2]
      field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
    have h5 : (2 * M * delta / L) * (384 * K^2 * M * delta / L) = 768 * K^2 * M^2 * delta * t := by
      rw [h3, h4] <;> ring
    calc
      y * d ≤ (2 * M * delta / L) * d := h1
      _ ≤ (2 * M * delta / L) * (384 * K^2 * M * delta / L) := h2
      _ = 768 * K^2 * M^2 * delta * t := h5
  have h_M1_le_2M : M + 1 ≤ 2 * M := by linarith
  have h_M1δd_bound : (M + 1) * delta * d ≤ 16 * K^2 * M^2 * delta * t := by
    have h1 : (M + 1) * delta * d ≤ (2 * M) * delta * d := by
      gcongr <;> linarith
    have h2 : (2 * M) * delta * d ≤ (2 * M) * delta * (8 * K * M * t) := by gcongr
    have h3 : (2 * M) * delta * (8 * K * M * t) = 16 * K * M^2 * delta * t := by ring
    rw [h3] at h2
    have h4 : 16 * K * M^2 * delta * t ≤ 16 * K^2 * M^2 * delta * t := by
      have h5 : 1 ≤ K^2 := by nlinarith
      have h6 : 0 ≤ 16 * M^2 * delta * t := by positivity
      have h7 : K ≤ K^2 := by nlinarith
      nlinarith
    linarith
  have h_final : (Δ + delta) * d ≤ (M + 1) * delta * d + c_geo * y * d := by
    have h1 : (Δ + delta) * d ≤ (M * delta + c_geo * y + delta) * d := by
      gcongr <;> linarith [h5Δ]
    have h2 : (M * delta + c_geo * y + delta) * d = (M + 1) * delta * d + c_geo * y * d := by ring
    rw [h2] at h1
    exact h1
  have h_cgeo_yd : c_geo * y * d ≤ 1536 * K^2 * M^2 * delta * t := by
    have h1 : c_geo * (y * d) ≤ c_geo * (768 * K^2 * M^2 * delta * t) := by
      have h2 : 0 ≤ c_geo := by norm_num
      exact mul_le_mul_of_nonneg_left h_yd_bound h2
    have h1' : c_geo * y * d ≤ c_geo * (768 * K^2 * M^2 * delta * t) := by
      have h_assoc : c_geo * y * d = c_geo * (y * d) := by ring
      rw [h_assoc]
      exact h1
    have h2 : c_geo * (768 * K^2 * M^2 * delta * t) = 1536 * K^2 * M^2 * delta * t := by
      have h_cgeo2 : c_geo = 2 := hc_geo
      rw [h_cgeo2] <;> ring
    rw [h2] at h1'
    exact h1'
  have h_pos_all : 0 ≤ K^2 * M^2 * delta * t := by positivity
  have h_diff_pos : 0 ≤ (2700 - 1552 : ℝ) * (K^2 * M^2 * delta * t) := by
    have h : 0 ≤ (2700 - 1552 : ℝ) := by norm_num
    exact mul_nonneg h h_pos_all
  have h_final2 : 1552 * K^2 * M^2 * delta * t ≤ 2700 * K^2 * M^2 * delta * t := by
    have h_eq : 2700 * K^2 * M^2 * delta * t =
        1552 * K^2 * M^2 * delta * t +
          (2700 - 1552 : ℝ) * (K^2 * M^2 * delta * t) := by
      ring
    rw [h_eq]
    <;> linarith [h_diff_pos]
  calc
    (Δ + delta) * d ≤ (M + 1) * delta * d + c_geo * y * d := h_final
    _ ≤ 16 * K^2 * M^2 * delta * t + 1536 * K^2 * M^2 * delta * t := by
      exact add_le_add h_M1δd_bound h_cgeo_yd
    _ = 1552 * K^2 * M^2 * delta * t := by ring
    _ ≤ 2700 * K^2 * M^2 * delta * t := h_final2

end Kakeya.Cinematic
