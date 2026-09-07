import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Endpoint alternative for the convex sublevel bound

The left endpoint derivative of a convex sublevel component either forces
the tangency parameter to be controlled by its square, or is already large.
-/

namespace Kakeya.Cinematic

open Set

lemma convex_endpoint_case
    {H : ℝ → ℝ}
    {K t delta Delta m ell a A : ℝ}
    (hK : 1 ≤ K)
    (ht : 0 < t)
    (hm : m = t / (6 * K))
    (hgap : 1 / (96 * K) ≤ a - ell)
    (hH_diff : Differentiable ℝ H)
    (hH'_diff : Differentiable ℝ (deriv H))
    (hH'' : ∀ x ∈ Icc ell a, m ≤ deriv (deriv H) x)
    (hA : deriv H a = A)
    (hA_pos : 0 < A)
    (hHa : |H a| ≤ delta)
    (hDelta : ∀ x ∈ Icc ell a,
      Delta ≤ |H x| + |deriv H x|) :
    Delta ≤ delta + A ^ 2 / m ∨
      t / (576 * K ^ 2) ≤ A := by
  have hK_pos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hm_pos : 0 < m := by
    rw [hm]
    positivity
  have hgap_pos : 0 < 1 / (96 * K) := by positivity
  have hell_a : ell < a := by linarith
  have hderiv_growth :
      ∀ {x y : ℝ}, x ∈ Icc ell a → y ∈ Icc ell a → x ≤ y →
        m * (y - x) ≤ deriv H y - deriv H x := by
    intro x y hx hy hxy
    by_cases heq : x = y
    · subst y
      simp
    · have hxy_strict : x < y := lt_of_le_of_ne hxy heq
      have hcontinuous :
          ContinuousOn (deriv H) (Icc x y) :=
        hH'_diff.continuous.continuousOn
      have hdifferentiable :
          DifferentiableOn ℝ (deriv H) (Ioo x y) := by
        intro z hz
        exact (hH'_diff z).differentiableWithinAt
      obtain ⟨xi, hxi, hslope⟩ :=
        exists_deriv_eq_slope (deriv H) hxy_strict
          hcontinuous hdifferentiable
      have hxi_global : xi ∈ Icc ell a := by
        exact ⟨hx.1.trans (le_of_lt hxi.1),
          (le_of_lt hxi.2).trans hy.2⟩
      have hsecond : m ≤ deriv (deriv H) xi :=
        hH'' xi hxi_global
      have hdenominator : 0 < y - x := sub_pos.mpr hxy_strict
      have hslope_lower :
          m ≤ (deriv H y - deriv H x) / (y - x) := by
        rw [← hslope]
        exact hsecond
      calc
        m * (y - x)
            ≤ ((deriv H y - deriv H x) / (y - x)) *
                (y - x) := by
          gcongr
        _ = deriv H y - deriv H x := by
          field_simp [hdenominator.ne']
  by_cases hleft : 0 ≤ deriv H ell
  · right
    have hgrowth :=
      hderiv_growth
        (x := ell) (y := a)
        (left_mem_Icc.mpr hell_a.le)
        (right_mem_Icc.mpr hell_a.le)
        hell_a.le
    rw [hA] at hgrowth
    have hscale_identity :
        t / (576 * K ^ 2) =
          m * (1 / (96 * K)) := by
      rw [hm]
      field_simp [hK_pos.ne']
      ring
    calc
      t / (576 * K ^ 2)
          = m * (1 / (96 * K)) := hscale_identity
      _ ≤ m * (a - ell) :=
        mul_le_mul_of_nonneg_left hgap hm_pos.le
      _ ≤ A := by linarith
  · left
    have hleft_neg : deriv H ell < 0 := lt_of_not_ge hleft
    have hderiv_a_pos : 0 < deriv H a := by
      rw [hA]
      exact hA_pos
    have hzero_range :
        (0 : ℝ) ∈ Icc (deriv H ell) (deriv H a) :=
      ⟨hleft_neg.le, hderiv_a_pos.le⟩
    have hzero_image :
        (0 : ℝ) ∈ deriv H '' Icc ell a :=
      intermediate_value_Icc hell_a.le
        hH'_diff.continuous.continuousOn hzero_range
    obtain ⟨y, hy, hy_zero⟩ := hzero_image
    have hy_a : y < a := by
      have hya := hy.2
      by_contra hnot
      have heq : y = a := le_antisymm hya (le_of_not_gt hnot)
      rw [heq, hA] at hy_zero
      linarith
    have hgrowth_ya :=
      hderiv_growth hy
        (right_mem_Icc.mpr hell_a.le) hy.2
    rw [hy_zero, hA, sub_zero] at hgrowth_ya
    have hya_bound : a - y ≤ A / m := by
      apply (le_div_iff₀ hm_pos).2
      simpa [mul_comm] using hgrowth_ya
    have hcontinuous : ContinuousOn H (Icc y a) :=
      hH_diff.continuous.continuousOn
    have hdifferentiable : DifferentiableOn ℝ H (Ioo y a) := by
      intro z hz
      exact (hH_diff z).differentiableWithinAt
    obtain ⟨xi, hxi, hslope⟩ :=
      exists_deriv_eq_slope H hy_a hcontinuous hdifferentiable
    have hxi_global : xi ∈ Icc ell a := by
      exact ⟨hy.1.trans (le_of_lt hxi.1),
        le_of_lt hxi.2⟩
    have hxi_nonneg :
        0 ≤ deriv H xi := by
      have hgrowth :=
        hderiv_growth hy hxi_global
          (le_of_lt hxi.1)
      rw [hy_zero, sub_zero] at hgrowth
      have hxi_y : 0 ≤ xi - y := sub_nonneg.mpr (le_of_lt hxi.1)
      have : 0 ≤ m * (xi - y) :=
        mul_nonneg hm_pos.le hxi_y
      linarith
    have hxi_le_A :
        deriv H xi ≤ A := by
      have hgrowth :=
        hderiv_growth hxi_global
          (right_mem_Icc.mpr hell_a.le)
          (le_of_lt hxi.2)
      rw [hA] at hgrowth
      have ha_xi : 0 ≤ a - xi := sub_nonneg.mpr (le_of_lt hxi.2)
      have : 0 ≤ m * (a - xi) :=
        mul_nonneg hm_pos.le ha_xi
      linarith
    have hdenominator : 0 < a - y := sub_pos.mpr hy_a
    have hdifference :
        H a - H y = deriv H xi * (a - y) := by
      have hslope' :
          deriv H xi = (H a - H y) / (a - y) :=
        hslope
      field_simp [hdenominator.ne'] at hslope'
      linarith
    have hdifference_nonneg : 0 ≤ H a - H y := by
      rw [hdifference]
      positivity
    have hdifference_bound :
        H a - H y ≤ A ^ 2 / m := by
      calc
        H a - H y
            = deriv H xi * (a - y) := hdifference
        _ ≤ A * (a - y) := by
          gcongr
        _ ≤ A * (A / m) := by
          gcongr
        _ = A ^ 2 / m := by ring
    have hHy :
        |H y| ≤ delta + A ^ 2 / m := by
      have htriangle :
          |H y| ≤ |H a| + |H a - H y| := by
        have hrewrite : H y = H a - (H a - H y) := by ring
        calc
          |H y| = |H a - (H a - H y)| := congrArg abs hrewrite
          _ ≤ |H a| + |H a - H y| := abs_sub _ _
      have habsolute_difference :
          |H a - H y| = H a - H y :=
        abs_of_nonneg hdifference_nonneg
      rw [habsolute_difference] at htriangle
      linarith
    have hDelta_y := hDelta y hy
    rw [hy_zero, abs_zero, add_zero] at hDelta_y
    exact hDelta_y.trans hHy

end Kakeya.Cinematic
