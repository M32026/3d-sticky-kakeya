import MyLeanRepo.Kakeya.Cinematic.Geometry
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Minimizer bounds for strictly convex functions

Three elementary lemmas used in the lens-existence argument.
-/

namespace Kakeya.Cinematic

open Set

/-- MVT on subinterval [p,q] ⊆ [a,b]. -/
private lemma mvt_on_sub {f f' : ℝ → ℝ} {a b p q : ℝ}
    (f_cont : ContinuousOn f (Icc a b))
    (f_deriv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hp_Icc : p ∈ Icc a b) (hq_Icc : q ∈ Icc a b)
    (hpq : p < q) :
    ∃ ξ ∈ Ioo p q, f' ξ = (f q - f p) / (q - p) := by
  have h_sub : Icc p q ⊆ Icc a b := by
    intro z hz; exact ⟨by linarith [hp_Icc.1, hz.1], by linarith [hz.2, hq_Icc.2]⟩
  have h_cont' : ContinuousOn f (Icc p q) := f_cont.mono h_sub
  have h_diff' : DifferentiableOn ℝ f (Ioo p q) := by
    intro z hz
    have hz1 : a < z := by linarith [hp_Icc.1, hz.1]
    have hz2 : z < b := by linarith [hz.2, hq_Icc.2]
    exact (f_deriv z ⟨hz1, hz2⟩).differentiableAt.differentiableWithinAt
  have h : ∃ ξ ∈ Ioo p q, deriv f ξ = (f q - f p) / (q - p) := by
    exact exists_deriv_eq_slope f hpq h_cont' h_diff'
  rcases h with ⟨ξ, hξ_in, h_eq⟩
  have hξ1 : a < ξ := by linarith [hp_Icc.1, hξ_in.1]
  have hξ2 : ξ < b := by linarith [hξ_in.2, hq_Icc.2]
  have hderiv : deriv f ξ = f' ξ := (f_deriv ξ ⟨hξ1, hξ2⟩).deriv
  rw [hderiv] at h_eq
  exact ⟨ξ, hξ_in, h_eq⟩

/-- If f'' ≥ 0 on [a,b], then f' is monotone. -/
private lemma deriv_mono {f' f'' : ℝ → ℝ} {a b : ℝ}
    (f'_cont : ContinuousOn f' (Icc a b))
    (f'_deriv : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (f''_nonneg : ∀ x ∈ Ioo a b, 0 ≤ f'' x)
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u < v) :
    f' u ≤ f' v := by
  rcases mvt_on_sub f'_cont f'_deriv hu hv huv with ⟨ξ, hξ_in, h_eq⟩
  have hξ1 : a < ξ := by linarith [hu.1, hξ_in.1]
  have hξ2 : ξ < b := by linarith [hξ_in.2, hv.2]
  have hξ_ge : 0 ≤ f'' ξ := f''_nonneg ξ ⟨hξ1, hξ2⟩
  have h_pos : 0 < v - u := by linarith
  have h : f' v - f' u = f'' ξ * (v - u) := by
    field_simp [h_pos.ne'] at h_eq ⊢ <;> linarith
  have h6 : 0 ≤ f'' ξ * (v - u) := mul_nonneg hξ_ge (by linarith)
  have h7 : 0 ≤ f' v - f' u := by rw [h] <;> exact h6
  linarith

/-- Gradient inequality: f(y) ≥ f(x) + f'(x)*(y-x) when f'' ≥ 0. -/
private lemma gradient_ineq {f f' f'' : ℝ → ℝ} {a b x y : ℝ}
    (f_cont : ContinuousOn f (Icc a b))
    (f'_cont : ContinuousOn f' (Icc a b))
    (f_deriv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (f'_deriv : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (f''_nonneg : ∀ x ∈ Ioo a b, 0 ≤ f'' x)
    (hx_in : x ∈ Ioo a b) (hy_in : y ∈ Icc a b) :
    f y ≥ f x + f' x * (y - x) := by
  have h_x_Icc : x ∈ Icc a b := ⟨hx_in.1.le, hx_in.2.le⟩
  by_cases h_eq : x = y
  · subst h_eq
    simpa using le_refl (f x)
  · by_cases h_lt : x < y
    · rcases mvt_on_sub f_cont f_deriv h_x_Icc hy_in h_lt with ⟨ξ, hξ_in, h_eq2⟩
      have hξ_Icc : ξ ∈ Icc a b := ⟨by linarith [hx_in.1, hξ_in.1], by linarith [hξ_in.2, hy_in.2]⟩
      have h'_mono : f' x ≤ f' ξ := deriv_mono f'_cont f'_deriv f''_nonneg h_x_Icc hξ_Icc hξ_in.1
      have h_pos : 0 < y - x := by linarith
      have h9 : f y - f x = f' ξ * (y - x) := by
        field_simp [h_pos.ne'] at h_eq2 ⊢ <;> linarith
      have h10 : f' x * (y - x) ≤ f' ξ * (y - x) := by gcongr <;> linarith
      linarith [h9, h10]
    · have h_gt : y < x := by by_contra h; exact h_eq (by linarith)
      rcases mvt_on_sub f_cont f_deriv hy_in h_x_Icc h_gt with ⟨ξ, hξ_in, h_eq2⟩
      have hξ_Icc : ξ ∈ Icc a b := ⟨by linarith [hy_in.1, hξ_in.1], by linarith [hξ_in.2, hx_in.2]⟩
      have h'_mono : f' ξ ≤ f' x := deriv_mono f'_cont f'_deriv f''_nonneg hξ_Icc h_x_Icc hξ_in.2
      have h_pos : 0 < x - y := by linarith
      have h9 : f x - f y = f' ξ * (x - y) := by
        field_simp [h_pos.ne'] at h_eq2 ⊢ <;> linarith
      have h10 : f' ξ * (x - y) ≤ f' x * (x - y) := by gcongr <;> linarith
      linarith

/-- Derivative of (t - x0)^2 at x. -/
private lemma hasDerivAt_sq (x x0 : ℝ) :
    HasDerivAt (fun t : ℝ => (t - x0)^2) (2 * (x - x0)) x := by
  have h1 : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id (x := x)
  have h2 : HasDerivAt (fun t : ℝ => t - x0) 1 x := by simpa using h1.sub_const x0
  have h3 : HasDerivAt (fun t : ℝ => (t - x0) * (t - x0)) (1 * (x - x0) + (x - x0) * 1) x := h2.mul h2
  have h4 : (1 * (x - x0) + (x - x0) * 1 : ℝ) = 2 * (x - x0) := by ring
  have h5 : HasDerivAt (fun t : ℝ => (t - x0) * (t - x0)) (2 * (x - x0)) x := by
    rw [h4] at h3; exact h3
  have h6 : (fun t : ℝ => (t - x0) * (t - x0)) = (fun t : ℝ => (t - x0)^2) := by
    funext t; ring
  rw [h6] at h5
  exact h5

/--
For h'' ≥ c > 0 on [a,b] and interior critical point xm (h'(xm)=0),
`|xm - x0| ≤ |h'(x0)| / c`.
-/
lemma minimizer_location {h h' h'' : ℝ → ℝ} {a b c xm x0 : ℝ}
    (hab : a < b) (hc_pos : 0 < c)
    (h'_cont : ContinuousOn h' (Icc a b))
    (h'_deriv : ∀ x ∈ Ioo a b, HasDerivAt h' (h'' x) x)
    (h''_ge : ∀ x ∈ Ioo a b, c ≤ h'' x)
    (hxm_in : xm ∈ Ioo a b)
    (h'_xm : h' xm = 0)
    (hx0_in : x0 ∈ Icc a b) :
    |xm - x0| ≤ |h' x0| / c := by
  by_cases h_eq : xm = x0
  · subst h_eq; rw [h'_xm]; simp
  · by_cases h_lt : xm < x0
    · have h_xm_Icc : xm ∈ Icc a b := ⟨hxm_in.1.le, hxm_in.2.le⟩
      rcases mvt_on_sub h'_cont h'_deriv h_xm_Icc hx0_in h_lt with ⟨ξ, hξ_in, h_eq2⟩
      have hξ1 : a < ξ := by
        have h1 : a < xm := hxm_in.1
        have h2 : xm < ξ := hξ_in.1
        linarith
      have hξ2 : ξ < b := by
        have h1 : ξ < x0 := hξ_in.2
        have h2 : x0 ≤ b := hx0_in.2
        linarith
      have hξ_ge : c ≤ h'' ξ := h''_ge ξ ⟨hξ1, hξ2⟩
      have h_pos : 0 < x0 - xm := by linarith
      rw [h'_xm] at h_eq2
      have h9 : h'' ξ * (x0 - xm) = h' x0 := by
        field_simp [h_pos.ne'] at h_eq2 ⊢ <;> linarith
      have h10 : 0 < h' x0 := by rw [←h9]; exact mul_pos (lt_of_lt_of_le hc_pos hξ_ge) h_pos
      have h11 : |h' x0| = h' x0 := abs_of_pos h10
      have h12 : c * (x0 - xm) ≤ h'' ξ * (x0 - xm) := by gcongr <;> linarith
      have h13 : |xm - x0| = x0 - xm := by rw [abs_of_neg (show xm - x0 < 0 by linarith)] <;> linarith
      rw [h11, h13]
      have h14 : c * (x0 - xm) ≤ h' x0 := by rw [←h9] <;> exact h12
      have h15 : x0 - xm ≤ h' x0 / c := by
        calc x0 - xm = (c * (x0 - xm)) / c := by field_simp [hc_pos.ne'] <;> ring
          _ ≤ h' x0 / c := by gcongr
      exact h15
    · have h_gt : x0 < xm := by by_contra h; exact h_eq (by linarith)
      have h_xm_Icc : xm ∈ Icc a b := ⟨hxm_in.1.le, hxm_in.2.le⟩
      rcases mvt_on_sub h'_cont h'_deriv hx0_in h_xm_Icc h_gt with ⟨ξ, hξ_in, h_eq2⟩
      have hξ1 : a < ξ := by
        have h1 : a ≤ x0 := hx0_in.1
        have h2 : x0 < ξ := hξ_in.1
        linarith
      have hξ2 : ξ < b := by
        have h1 : ξ < xm := hξ_in.2
        have h2 : xm < b := hxm_in.2
        linarith
      have hξ_ge : c ≤ h'' ξ := h''_ge ξ ⟨hξ1, hξ2⟩
      have h_pos : 0 < xm - x0 := by linarith
      rw [h'_xm] at h_eq2
      have h9 : h'' ξ * (xm - x0) = -h' x0 := by
        field_simp [h_pos.ne'] at h_eq2 ⊢ <;> linarith
      have h10 : h' x0 < 0 := by
        have h11 : 0 < -h' x0 := by rw [←h9]; exact mul_pos (lt_of_lt_of_le hc_pos hξ_ge) h_pos
        linarith
      have h11 : |h' x0| = -h' x0 := abs_of_neg h10
      have h12 : c * (xm - x0) ≤ h'' ξ * (xm - x0) := by gcongr <;> linarith
      have h13 : |xm - x0| = xm - x0 := by rw [abs_of_pos (show 0 < xm - x0 by linarith)]
      rw [h11, h13]
      have h14 : c * (xm - x0) ≤ -h' x0 := by rw [←h9] <;> exact h12
      have h15 : xm - x0 ≤ (-h' x0) / c := by
        calc xm - x0 = (c * (xm - x0)) / c := by field_simp [hc_pos.ne'] <;> ring
          _ ≤ (-h' x0) / c := by gcongr
      exact h15

/--
Taylor lower bound: for h'' ≥ c > 0 on [a,b],
`h(y) ≥ h(x0) + h'(x0) * (y - x0) + (c/2) * (y - x0)^2`.
-/
lemma convex_value_lower_bound {h h' h'' : ℝ → ℝ} {a b c x0 y : ℝ}
    (hab : a < b) (hc_pos : 0 < c)
    (h_cont : ContinuousOn h (Icc a b))
    (h'_cont : ContinuousOn h' (Icc a b))
    (h_deriv : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x)
    (h'_deriv : ∀ x ∈ Ioo a b, HasDerivAt h' (h'' x) x)
    (h''_ge : ∀ x ∈ Ioo a b, c ≤ h'' x)
    (hx0_in : x0 ∈ Ioo a b)
    (hy_in : y ∈ Icc a b) :
    h y ≥ h x0 + h' x0 * (y - x0) + (c / 2) * (y - x0)^2 := by
  let g : ℝ → ℝ := fun t => h t - (c / 2) * (t - x0)^2
  let g' : ℝ → ℝ := fun t => h' t - c * (t - x0)
  let g'' : ℝ → ℝ := fun t => h'' t - c
  have hg_cont : ContinuousOn g (Icc a b) := by
    have h2 : ContinuousOn (fun t : ℝ => (c / 2) * (t - x0)^2) (Icc a b) := by fun_prop
    exact h_cont.sub h2
  have hg_deriv : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x := by
    intro x hx
    have hd1 : HasDerivAt h (h' x) x := h_deriv x hx
    have hd2 : HasDerivAt (fun t : ℝ => (c / 2) * (t - x0)^2) (c * (x - x0)) x := by
      have h3 := hasDerivAt_sq x x0
      have h4 : HasDerivAt (fun t : ℝ => (c / 2) * (t - x0)^2) ((c / 2) * (2 * (x - x0))) x := h3.const_mul (c / 2)
      have h5 : (c / 2) * (2 * (x - x0)) = c * (x - x0) := by ring
      rw [h5] at h4
      exact h4
    exact hd1.sub hd2
  have hg'_cont : ContinuousOn g' (Icc a b) := by
    have h2 : ContinuousOn (fun t : ℝ => c * (t - x0)) (Icc a b) := by fun_prop
    exact h'_cont.sub h2
  have hg'_deriv : ∀ x ∈ Ioo a b, HasDerivAt g' (g'' x) x := by
    intro x hx
    have hd1 : HasDerivAt h' (h'' x) x := h'_deriv x hx
    have hd2 : HasDerivAt (fun t : ℝ => c * (t - x0)) c x := by
      have h3 : HasDerivAt (fun t : ℝ => t - x0) 1 x := by
        have h4 : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id (x := x)
        simpa using h4.sub_const x0
      have h5 : HasDerivAt (fun t : ℝ => c * (t - x0)) (c * 1) x := h3.const_mul c
      have h6 : c * 1 = c := by ring
      rw [h6] at h5
      exact h5
    exact hd1.sub hd2
  have hg''_nonneg : ∀ x ∈ Ioo a b, 0 ≤ g'' x := by
    intro x hx
    have h1 : c ≤ h'' x := h''_ge x hx
    simpa [g''] using by linarith
  have h_main : g y ≥ g x0 + g' x0 * (y - x0) :=
    gradient_ineq hg_cont hg'_cont hg_deriv hg'_deriv hg''_nonneg hx0_in hy_in
  have hg_x0 : g x0 = h x0 := by
    simp [g] <;> ring
  have hg'_x0 : g' x0 = h' x0 := by
    simp [g'] <;> ring
  rw [hg_x0, hg'_x0] at h_main
  have hgy : g y = h y - (c / 2) * (y - x0)^2 := by
    simp [g] <;> ring
  rw [hgy] at h_main
  linarith

/--
For h'' ≥ c > 0 on [a,b] and interior critical point xm (h'(xm)=0),
`h(y) - h(xm) ≥ (c/2) * (y - xm)^2`.
-/
lemma convex_growth_from_min {h h' h'' : ℝ → ℝ} {a b c xm y : ℝ}
    (hab : a < b) (hc_pos : 0 < c)
    (h_cont : ContinuousOn h (Icc a b))
    (h'_cont : ContinuousOn h' (Icc a b))
    (h_deriv : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x)
    (h'_deriv : ∀ x ∈ Ioo a b, HasDerivAt h' (h'' x) x)
    (h''_ge : ∀ x ∈ Ioo a b, c ≤ h'' x)
    (hxm_in : xm ∈ Ioo a b)
    (h'_xm : h' xm = 0)
    (hy_in : y ∈ Icc a b) :
    h y - h xm ≥ (c / 2) * (y - xm)^2 := by
  have h_bound := convex_value_lower_bound hab hc_pos h_cont h'_cont h_deriv h'_deriv h''_ge hxm_in hy_in
  have h2 : h y ≥ h xm + h' xm * (y - xm) + (c / 2) * (y - xm)^2 := h_bound
  rw [h'_xm] at h2
  have h3 : h y ≥ h xm + (c / 2) * (y - xm)^2 := by simpa using h2
  linarith

end Kakeya.Cinematic
