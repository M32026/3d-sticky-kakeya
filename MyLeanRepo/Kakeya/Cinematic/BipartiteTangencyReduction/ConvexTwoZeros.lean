import MyLeanRepo.Kakeya.Cinematic.Geometry
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Convex two-zeros lemma

A strictly convex C² function that is positive at both endpoints of an interval
and negative at an interior point has exactly two transverse zeros.
-/

noncomputable section

namespace Kakeya.Cinematic

open Set

lemma convex_two_zeros
    {h : ℝ → ℝ} {a b xm : ℝ}
    (hab : a < b) (hxm1 : a < xm) (hxm2 : xm < b)
    (h_diff1 : Differentiable ℝ h)
    (h_diff2 : Differentiable ℝ (deriv h))
    (h''_pos : ∀ x ∈ Icc a b, 0 < deriv (deriv h) x)
    (ha_pos : 0 < h a) (hb_pos : 0 < h b)
    (hm_neg : h xm < 0) :
    ∃ (z1 z2 : ℝ), a < z1 ∧ z1 < xm ∧ xm < z2 ∧ z2 < b ∧
      h z1 = 0 ∧ h z2 = 0 ∧
      (∀ x, z1 < x → x < z2 → h x < 0) ∧
      (deriv h z1 < 0) ∧ (0 < deriv h z2) := by
  have h_cont : Continuous h := h_diff1.continuous
  have h'_cont : Continuous (deriv h) := h_diff2.continuous
  have h_diff_at : ∀ (x : ℝ), DifferentiableAt ℝ (deriv h) x := by
    intro x; exact h_diff2.differentiableAt
  have h_hasDeriv : ∀ (x : ℝ), HasDerivAt (deriv h) (deriv (deriv h) x) x :=
    fun x => (h_diff_at x).hasDerivAt

  have h'_inc : StrictMonoOn (deriv h) (Icc a b) := by
    intro x hx y hy hxy
    have h_mvt : ∃ c ∈ Ioo x y,
        deriv (deriv h) c = (deriv h y - deriv h x) / (y - x) := by
      exact exists_hasDerivAt_eq_slope (f := deriv h) (f' := deriv (deriv h))
        hxy h'_cont.continuousOn (fun z _ => h_hasDeriv z)
    rcases h_mvt with ⟨c, hc, h_eq⟩
    have hc' : c ∈ Icc a b := by
      exact ⟨by linarith [hx.1, hc.1], by linarith [hy.2, hc.2]⟩
    have h''c : 0 < deriv (deriv h) c := h''_pos c hc'
    have h_pos : 0 < y - x := by linarith
    rw [h_eq] at h''c
    have hdiv : (deriv h y - deriv h x) / (y - x) > 0 := h''c
    have hdiff : 0 < deriv h y - deriv h x := by
      exact (div_pos_iff_of_pos_right h_pos).mp hdiv
    linarith

  have hz1_Icc (z1 : ℝ) (h1 : a ≤ z1) (h2 : z1 ≤ xm) : z1 ∈ Icc a b :=
    ⟨by linarith, by linarith⟩
  have hz2_Icc (z2 : ℝ) (h1 : xm ≤ z2) (h2 : z2 ≤ b) : z2 ∈ Icc a b :=
    ⟨by linarith, by linarith⟩

  have h_left_zero : ∃ z1, a < z1 ∧ z1 < xm ∧ h z1 = 0 := by
    have h_neg_cont : Continuous (fun x => -h x) := h_cont.neg
    have h_ivt : ∃ z1 ∈ Ioo a xm, (-h) z1 = 0 := by
      apply intermediate_value_Ioo (by linarith) h_neg_cont.continuousOn
      exact ⟨by linarith, by linarith⟩
    rcases h_ivt with ⟨z1, hz1, h_eq⟩
    have h_z1_eq : h z1 = 0 := by simpa [neg_eq_zero] using h_eq
    exact ⟨z1, hz1.1, hz1.2, h_z1_eq⟩

  have h_right_zero : ∃ z2, xm < z2 ∧ z2 < b ∧ h z2 = 0 := by
    have h_ivt : ∃ z2 ∈ Ioo xm b, h z2 = 0 := by
      apply intermediate_value_Ioo (by linarith) h_cont.continuousOn
      exact ⟨by linarith, by linarith⟩
    rcases h_ivt with ⟨z2, hz2, h_eq⟩
    exact ⟨z2, hz2.1, hz2.2, h_eq⟩

  rcases h_left_zero with ⟨z1, haz1, hz1xm, hz1_eq⟩
  rcases h_right_zero with ⟨z2, hxmz2, hz2b, hz2_eq⟩
  have hz1_Icc' : z1 ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hz2_Icc' : z2 ∈ Icc a b := ⟨by linarith, by linarith⟩

  have h'_z1_neg : deriv h z1 < 0 := by
    by_cases h' : 0 ≤ deriv h z1
    · have h'_nonneg_on : ∀ x ∈ Icc z1 xm, 0 ≤ deriv h x := by
        intro x hx
        have h1 : z1 ≤ x := hx.1
        by_cases h_eq : z1 = x
        · have h_goal : 0 ≤ deriv h x := by
            rw [←h_eq]
            exact h'
          exact h_goal
        · have h2 : z1 < x := lt_of_le_of_ne h1 h_eq
          have hx_Icc : x ∈ Icc a b := ⟨by linarith [hx.1], by linarith [hx.2]⟩
          have h3 : deriv h z1 < deriv h x := h'_inc hz1_Icc' hx_Icc h2
          exact le_of_lt (lt_of_le_of_lt h' h3)
      have h_mvt : ∃ c ∈ Ioo z1 xm,
          deriv h c = (h xm - h z1) / (xm - z1) := by
        exact exists_hasDerivAt_eq_slope (f := h) (f' := deriv h)
          (by linarith) h_cont.continuousOn (fun z _ => h_diff1.differentiableAt.hasDerivAt)
      rcases h_mvt with ⟨c, hc, h_eq⟩
      have hc1 : z1 < c := hc.1
      have hc2 : c < xm := hc.2
      have hc_in : c ∈ Icc z1 xm := ⟨by linarith, by linarith⟩
      have h'c_nonneg : 0 ≤ deriv h c := h'_nonneg_on c hc_in
      have h_pos : 0 < xm - z1 := by linarith
      rw [h_eq] at h'c_nonneg
      have h4 : (h xm - h z1) / (xm - z1) ≥ 0 := h'c_nonneg
      have h5 : h xm - h z1 ≥ 0 := by
        have h6 : ((h xm - h z1) / (xm - z1)) * (xm - z1) = h xm - h z1 := by
          field_simp [h_pos.ne'] <;> ring
        have h7 : 0 ≤ ((h xm - h z1) / (xm - z1)) * (xm - z1) := mul_nonneg h4 h_pos.le
        rw [h6] at h7
        exact h7
      have h8 : h z1 = 0 := hz1_eq
      rw [h8] at h5
      linarith
    · exact lt_of_not_ge h'

  have h'_z2_pos : 0 < deriv h z2 := by
    by_cases h' : deriv h z2 ≤ 0
    · have h'_nonpos_on : ∀ x ∈ Icc xm z2, deriv h x ≤ 0 := by
        intro x hx
        have h1 : x ≤ z2 := hx.2
        by_cases h_eq : x = z2
        · have h_goal : deriv h x ≤ 0 := by
            rw [h_eq]
            exact h'
          exact h_goal
        · have h2 : x < z2 := lt_of_le_of_ne h1 h_eq
          have hx_Icc : x ∈ Icc a b := ⟨by linarith [hx.1], by linarith [hx.2]⟩
          have h3 : deriv h x < deriv h z2 := h'_inc hx_Icc hz2_Icc' h2
          exact le_of_lt (lt_of_lt_of_le h3 h')
      have h_mvt : ∃ c ∈ Ioo xm z2,
          deriv h c = (h z2 - h xm) / (z2 - xm) := by
        exact exists_hasDerivAt_eq_slope (f := h) (f' := deriv h)
          (by linarith) h_cont.continuousOn (fun z _ => h_diff1.differentiableAt.hasDerivAt)
      rcases h_mvt with ⟨c, hc, h_eq⟩
      have hc1 : xm < c := hc.1
      have hc2 : c < z2 := hc.2
      have hc_in : c ∈ Icc xm z2 := ⟨by linarith, by linarith⟩
      have h'c_nonpos : deriv h c ≤ 0 := h'_nonpos_on c hc_in
      have h_pos : 0 < z2 - xm := by linarith
      rw [h_eq] at h'c_nonpos
      have h4 : (h z2 - h xm) / (z2 - xm) ≤ 0 := h'c_nonpos
      have h5 : h z2 - h xm ≤ 0 := by
        have h6 : ((h z2 - h xm) / (z2 - xm)) * (z2 - xm) = h z2 - h xm := by
          field_simp [h_pos.ne'] <;> ring
        have h7 : ((h z2 - h xm) / (z2 - xm)) * (z2 - xm) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h4 h_pos.le
        rw [h6] at h7
        exact h7
      have h8 : h z2 = 0 := hz2_eq
      rw [h8] at h5
      linarith
    · exact lt_of_not_ge h'

  have h_between_neg : ∀ x, z1 < x → x < z2 → h x < 0 := by
    intro x hx1 hx2
    have h'_zero : ∃ c, z1 < c ∧ c < z2 ∧ deriv h c = 0 := by
      have h_ivt : ∃ c ∈ Ioo z1 z2, deriv h c = 0 := by
        apply intermediate_value_Ioo (by linarith) h'_cont.continuousOn
        exact ⟨by linarith, by linarith⟩
      rcases h_ivt with ⟨c, hc, h_eq⟩
      exact ⟨c, hc.1, hc.2, h_eq⟩
    rcases h'_zero with ⟨c, hz1c, hcz2, h'c_eq⟩
    have hc_Icc : c ∈ Icc a b := ⟨by linarith, by linarith⟩
    by_cases hcase : x ≤ c
    · have h_mvt : ∃ d ∈ Ioo z1 x,
          deriv h d = (h x - h z1) / (x - z1) := by
        exact exists_hasDerivAt_eq_slope (f := h) (f' := deriv h)
          (by linarith) h_cont.continuousOn (fun z _ => h_diff1.differentiableAt.hasDerivAt)
      rcases h_mvt with ⟨d, hd, h_eq⟩
      have h_d_gt_z1 : z1 < d := hd.1
      have h_d_lt_x : d < x := hd.2
      have h1 : a < d := lt_trans haz1 h_d_gt_z1
      have h2 : d < b := lt_trans (lt_trans h_d_lt_x hx2) hz2b
      have hd_Icc : d ∈ Icc a b := ⟨h1.le, h2.le⟩
      have h_d_lt_c : d < c := lt_of_lt_of_le h_d_lt_x hcase
      have h'd_neg : deriv h d < 0 := by
        have h3 : deriv h d < deriv h c := h'_inc hd_Icc hc_Icc h_d_lt_c
        rw [h'c_eq] at h3 <;> exact h3
      have h_pos : 0 < x - z1 := by linarith
      rw [h_eq] at h'd_neg
      have h4 : (h x - h z1) / (x - z1) < 0 := h'd_neg
      have h5 : h x - h z1 < 0 := by
        have h6 : ((h x - h z1) / (x - z1)) * (x - z1) = h x - h z1 := by
          field_simp [h_pos.ne'] <;> ring
        have h7 : ((h x - h z1) / (x - z1)) * (x - z1) < 0 := mul_neg_of_neg_of_pos h4 h_pos
        rw [h6] at h7
        exact h7
      rw [hz1_eq] at h5 <;> linarith
    · have h_x_gt_c : c < x := by linarith
      have h_mvt : ∃ d ∈ Ioo x z2,
          deriv h d = (h z2 - h x) / (z2 - x) := by
        exact exists_hasDerivAt_eq_slope (f := h) (f' := deriv h)
          (by linarith) h_cont.continuousOn (fun z _ => h_diff1.differentiableAt.hasDerivAt)
      rcases h_mvt with ⟨d, hd, h_eq⟩
      have h_d_gt_x : x < d := hd.1
      have h_d_lt_z2 : d < z2 := hd.2
      have h1 : a < d := lt_trans (lt_trans haz1 hx1) h_d_gt_x
      have h2 : d < b := lt_trans h_d_lt_z2 hz2b
      have hd_Icc : d ∈ Icc a b := ⟨h1.le, h2.le⟩
      have h_c_lt_d : c < d := lt_trans h_x_gt_c h_d_gt_x
      have h'd_pos : 0 < deriv h d := by
        have h3 : deriv h c < deriv h d := h'_inc hc_Icc hd_Icc h_c_lt_d
        rw [h'c_eq] at h3 <;> exact h3
      have h_pos : 0 < z2 - x := by linarith
      rw [h_eq] at h'd_pos
      have h4 : (h z2 - h x) / (z2 - x) > 0 := h'd_pos
      have h5 : h z2 - h x > 0 := by
        have h6 : ((h z2 - h x) / (z2 - x)) * (z2 - x) = h z2 - h x := by
          field_simp [h_pos.ne'] <;> ring
        have h7 : ((h z2 - h x) / (z2 - x)) * (z2 - x) > 0 := mul_pos h4 h_pos
        rw [h6] at h7
        exact h7
      rw [hz2_eq] at h5 <;> linarith

  exact ⟨z1, z2, by linarith, by linarith, by linarith, by linarith,
    hz1_eq, hz2_eq, h_between_neg, h'_z1_neg, h'_z2_pos⟩

end Kakeya.Cinematic
