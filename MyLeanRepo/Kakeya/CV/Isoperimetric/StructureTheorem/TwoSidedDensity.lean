import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic

/-!
# Two-Sided Density Theorem — Differential Inequality Lemma

Core real-analysis lemma for Maggi Theorem 15.5 Step 2:
if `m'(r) ≥ (1/C) m(r)^((n-1)/n)` a.e. with `m(0)=0`, `m` non-decreasing,
then `m(r) ≥ (r/(Cn))^n`.

## References

- Maggi, *Sets of Finite Perimeter*, Theorem 15.5, Steps 1-2
- Maggi, Remark 15.16
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry.StructureTheorem

variable {n : ℕ}

/-- **Isoperimetric differential inequality.**

If `m : ℝ → ℝ` is non-decreasing, non-negative, absolutely continuous on
`[0,R]`, with `m(0)=0`, `m(r)>0` for `0<r≤R`, and
`m'(r) ≥ (1/C)·m(r)^((n-1)/n)` a.e. on `(0,R)`, then
`m(r) ≥ (r/(C·n))^n` for all `r ∈ [0,R]`. -/
lemma isoperimetric_differential_inequality
    {n : ℕ} (hn : 1 ≤ n)
    {C : ℝ} (hC_pos : 0 < C)
    {R : ℝ} (hR_pos : 0 < R)
    {m : ℝ → ℝ}
    (hm_mono : MonotoneOn m (Set.Icc 0 R))
    (hm_nonneg : ∀ r ∈ Set.Icc 0 R, 0 ≤ m r)
    (hm_ac : AbsolutelyContinuousOnInterval m 0 R)
    (hm0 : m 0 = 0)
    (hm_pos : ∀ r ∈ Set.Ioc 0 R, 0 < m r)
    (h_ineq : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R →
      deriv m r ≥ (1 / C) * (m r) ^ (((n : ℝ) - 1) / (n : ℝ))) :
    ∀ r ∈ Set.Icc 0 R, m r ≥ (r / (C * (n : ℝ))) ^ n := by
  have h_n_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h_n_ne_zero : (n : ℝ) ≠ 0 := h_n_pos.ne'
  set α : ℝ := 1 / (n : ℝ) with hα_def
  have hα_pos : 0 < α := by positivity
  let F : ℝ → ℝ := fun r => (m r) ^ α

  have hF_mono : MonotoneOn F (Set.Icc 0 R) := by
    intro x hx y hy hxy
    have h1 : m x ≤ m y := hm_mono hx hy hxy
    have h2 : 0 ≤ m x := hm_nonneg x hx
    exact Real.rpow_le_rpow h2 h1 hα_pos.le

  have h_m_ae_diff : ∀ᵐ (r : ℝ), r ∈ Set.uIcc (0 : ℝ) R →
      DifferentiableAt ℝ m r := hm_ac.ae_differentiableAt

  have hF_deriv : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R →
      deriv F r = α * (m r) ^ (α - 1) * deriv m r := by
    filter_upwards [h_m_ae_diff] with r hr
    intro hr_in
    have h_pos : 0 < m r := hm_pos r ⟨hr_in.1, hr_in.2.le⟩
    have h_ne_zero : m r ≠ 0 := h_pos.ne'
    have h_in_uIcc : r ∈ Set.uIcc (0 : ℝ) R := by
      have h : Set.uIcc (0 : ℝ) R = Set.Icc 0 R := uIcc_of_le (by linarith)
      rw [h]
      exact ⟨hr_in.1.le, hr_in.2.le⟩
    have h_md : HasDerivAt m (deriv m r) r :=
      (hr h_in_uIcc).hasDerivAt
    have h_rpow_diff : HasDerivAt (fun x : ℝ => x ^ α)
        (α * (m r) ^ (α - 1)) (m r) :=
      Real.hasDerivAt_rpow_const (Or.inl h_ne_zero)
    have h_comp : HasDerivAt F (α * (m r) ^ (α - 1) * deriv m r) r := by
      have h : HasDerivAt ((fun x : ℝ => x ^ α) ∘ m)
          ((α * (m r) ^ (α - 1)) * deriv m r) r :=
        h_rpow_diff.comp r h_md
      have h_eq1 : ((fun x : ℝ => x ^ α) ∘ m) = F := by
        funext y; rfl
      rw [h_eq1] at h
      have h_eq2 : (α * (m r) ^ (α - 1)) * deriv m r =
          α * (m r) ^ (α - 1) * deriv m r := by ring
      rw [h_eq2] at h
      exact h
    exact h_comp.deriv

  have hF_ineq : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R →
      deriv F r ≥ 1 / (C * (n : ℝ)) := by
    filter_upwards [hF_deriv, h_ineq] with r hF_eq hm_ineq
    intro hr_in
    have h_pos : 0 < m r := hm_pos r ⟨hr_in.1, hr_in.2.le⟩
    rw [hF_eq hr_in]
    have h_m_ineq : deriv m r ≥ (1 / C) * (m r) ^ (((n : ℝ) - 1) / (n : ℝ)) := hm_ineq hr_in
    have h_coef_nonneg : 0 ≤ α * (m r) ^ (α - 1) :=
      mul_nonneg hα_pos.le (Real.rpow_nonneg h_pos.le (α - 1))
    have h3 : α * (m r) ^ (α - 1) * deriv m r ≥
        α * (m r) ^ (α - 1) * ((1 / C) * (m r) ^ (((n : ℝ) - 1) / (n : ℝ))) :=
      mul_le_mul_of_nonneg_left h_m_ineq h_coef_nonneg
    have h_exp_sum : α - 1 + (((n : ℝ) - 1) / (n : ℝ)) = 0 := by
      dsimp only [α] <;> field_simp <;> ring
    have h5 : (m r) ^ (α - 1) * (m r) ^ (((n : ℝ) - 1) / (n : ℝ)) = 1 := by
      have h7 : (m r) ^ (α - 1) * (m r) ^ (((n : ℝ) - 1) / (n : ℝ)) =
          (m r) ^ (α - 1 + (((n : ℝ) - 1) / (n : ℝ))) := by
        rw [← Real.rpow_add h_pos]
      rw [h7, h_exp_sum]
      <;> simp
    have h4 : α * (m r) ^ (α - 1) * ((1 / C) * (m r) ^ (((n : ℝ) - 1) / (n : ℝ))) =
        1 / (C * (n : ℝ)) := by
      calc
        α * (m r) ^ (α - 1) * ((1 / C) * (m r) ^ (((n : ℝ) - 1) / (n : ℝ)))
          = α * (1 / C) * ((m r) ^ (α - 1) * (m r) ^ (((n : ℝ) - 1) / (n : ℝ))) := by ring
        _ = α * (1 / C) * 1 := by rw [h5]
        _ = 1 / (C * (n : ℝ)) := by
          dsimp only [α] <;> field_simp <;> ring
    linarith

  intro r hr
  by_cases h_r0 : r = 0
  · -- Case r = 0
    subst h_r0
    have h_n_ne_zero' : n ≠ 0 := by linarith
    have h11 : (0 : ℝ) ^ n = 0 := zero_pow h_n_ne_zero'
    simp [hm0, h11]
  · -- Case 0 < r
    have h_r_pos : 0 < r := by
      have h : 0 ≤ r := hr.1
      exact lt_of_le_of_ne h (Ne.symm h_r0)

    have h_main : ∀ (a : ℝ), 0 < a → a < r →
        F r - F a ≥ (r - a) / (C * (n : ℝ)) := by
      intro a ha_pos ha_lt
      have h_ar : a ≤ r := by linarith
      have hF_mono' : MonotoneOn F (Set.Icc a r) :=
        hF_mono.mono (fun x hx =>
          have h_x1 : 0 ≤ x := by linarith [ha_pos, hx.1]
          have h_x2 : x ≤ R := by linarith [hr.2, hx.2]
          ⟨h_x1, h_x2⟩)
      have h_uIcc : Set.uIcc a r = Set.Icc a r := uIcc_of_le h_ar
      have hF_mono_uIcc : MonotoneOn F (Set.uIcc a r) := by
        rw [h_uIcc] <;> exact hF_mono'

      have hfi : IntervalIntegrable (deriv F) volume a r :=
        MonotoneOn.intervalIntegrable_deriv hF_mono_uIcc

      have h_int : ∫ (s : ℝ) in a..r, deriv F s ∈ Set.uIcc 0 (F r - F a) :=
        hF_mono_uIcc.intervalIntegral_deriv_mem_uIcc

      have h_ain : a ∈ Set.uIcc a r := by
        rw [h_uIcc] <;> exact ⟨by linarith, by linarith⟩
      have h_rin : r ∈ Set.uIcc a r := by
        rw [h_uIcc] <;> exact ⟨by linarith, by linarith⟩
      have h_Fa_le_Fr : F a ≤ F r := hF_mono_uIcc h_ain h_rin h_ar
      have h_nonneg : 0 ≤ F r - F a := by linarith
      have h_uIcc2 : Set.uIcc (0 : ℝ) (F r - F a) = Set.Icc (0 : ℝ) (F r - F a) :=
        uIcc_of_le h_nonneg
      rw [h_uIcc2] at h_int
      have h4 : ∫ (s : ℝ) in a..r, deriv F s ≤ F r - F a := h_int.2

      -- a.e. lower bound on deriv F, restricted to Icc a r
      have h_R_null : volume ({R} : Set ℝ) = 0 := by simp
      have h_ineq_restrict : ∀ᵐ (s : ℝ) ∂volume.restrict (Set.Icc a r),
          (1 / (C * (n : ℝ))) ≤ deriv F s := by
        have h11 : ∀ᵐ (s : ℝ), s ≠ R := by
          simpa [ae_iff] using h_R_null
        have h1 : ∀ᵐ (s : ℝ) ∂volume.restrict (Set.Icc a r), s ≠ R :=
          MeasureTheory.ae_restrict_of_ae h11
        have h2 : ∀ᵐ (s : ℝ) ∂volume.restrict (Set.Icc a r), s ∈ Set.Ioo 0 R := by
          filter_upwards [h1, self_mem_ae_restrict isClosed_Icc.measurableSet] with s hne hin
          have h_s_le_R : s ≤ R := by linarith [hr.2, hin.2]
          have h_s_lt_R : s < R := lt_of_le_of_ne h_s_le_R hne
          have h_s_pos : 0 < s := by linarith [ha_pos, hin.1]
          exact ⟨h_s_pos, h_s_lt_R⟩
        have h3 : ∀ᵐ (s : ℝ) ∂volume.restrict (Set.Icc a r),
            s ∈ Set.Ioo 0 R → deriv F s ≥ 1 / (C * (n : ℝ)) :=
          MeasureTheory.ae_restrict_of_ae hF_ineq
        filter_upwards [h2, h3] with s hs_in hs_imp
        exact hs_imp hs_in

      have h_const_int : ∫ (s : ℝ) in a..r, (1 / (C * (n : ℝ))) =
          (r - a) / (C * (n : ℝ)) := by
        rw [intervalIntegral.integral_const] <;> ring

      have h_mono : ∫ (s : ℝ) in a..r, (1 / (C * (n : ℝ))) ≤
          ∫ (s : ℝ) in a..r, deriv F s :=
        intervalIntegral.integral_mono_ae_restrict h_ar intervalIntegrable_const hfi h_ineq_restrict

      rw [h_const_int] at h_mono
      linarith

    have hF_at_r : F r ≥ r / (C * (n : ℝ)) := by
      by_contra h
      have h' : F r < r / (C * (n : ℝ)) := by linarith
      set D : ℝ := r / (C * (n : ℝ)) - F r with hD_def
      have hD_pos : 0 < D := by linarith
      have h_a_bound_pos : 0 < D * (C * (n : ℝ)) := by positivity
      let a0 : ℝ := min r (D * (C * (n : ℝ))) / 2
      have ha0_pos : 0 < a0 := by positivity
      have ha0_lt_r : a0 < r := by
        dsimp only [a0]
        have h1 : min r (D * (C * (n : ℝ))) ≤ r := min_le_left _ _
        linarith
      have ha0_lt_D : a0 < D * (C * (n : ℝ)) := by
        dsimp only [a0]
        have h1 : min r (D * (C * (n : ℝ))) ≤ D * (C * (n : ℝ)) := min_le_right _ _
        linarith
      have h5 := h_main a0 ha0_pos ha0_lt_r
      have ha0_le_R : a0 ≤ R := by
        dsimp only [a0]
        have h1 : min r (D * (C * (n : ℝ))) / 2 < r := by
          have h2 : min r (D * (C * (n : ℝ))) ≤ r := min_le_left _ _
          linarith
        linarith [hr.2]
      have ha0_in0 : a0 ∈ Set.Icc 0 R := ⟨by positivity, ha0_le_R⟩
      have hFa_nonneg : 0 ≤ F a0 := by
        have h6 : 0 ≤ m a0 := hm_nonneg a0 ha0_in0
        exact Real.rpow_nonneg h6 α
      have h7 : F r ≥ (r - a0) / (C * (n : ℝ)) := by linarith
      have h8 : (r - a0) / (C * (n : ℝ)) = r / (C * (n : ℝ)) - a0 / (C * (n : ℝ)) := by
        field_simp <;> ring
      rw [h8] at h7
      have h9 : a0 / (C * (n : ℝ)) < D := by
        have h10 : a0 < D * (C * (n : ℝ)) := ha0_lt_D
        calc a0 / (C * (n : ℝ))
          < (D * (C * (n : ℝ))) / (C * (n : ℝ)) := by gcongr
        _ = D := by
          field_simp [hC_pos.ne', h_n_pos.ne'] <;> ring
      have h_contra : F r > F r := by linarith [hD_def]
      exact lt_irrefl (F r) h_contra

    have h_final : (F r) ^ n ≥ (r / (C * (n : ℝ))) ^ n := by
      gcongr
      <;> linarith [Real.rpow_nonneg (hm_nonneg r hr) α]
    have h6 : (F r) ^ n = m r := by
      have h7 : F r = (m r) ^ α := by rfl
      rw [h7]
      have h8 : 0 ≤ m r := hm_nonneg r hr
      have h91 : ((m r) ^ α) ^ n = ((m r) ^ α) ^ (n : ℝ) := by norm_cast
      rw [h91]
      have h92 : (m r) ^ (α * (n : ℝ)) = ((m r) ^ α) ^ (n : ℝ) := Real.rpow_mul h8 α (n : ℝ)
      have h93 : ((m r) ^ α) ^ (n : ℝ) = (m r) ^ (α * (n : ℝ)) := h92.symm
      rw [h93]
      have h10 : α * (n : ℝ) = 1 := by
        simp [hα_def] <;> field_simp <;> ring
      rw [h10, Real.rpow_one]
    rw [h6] at h_final
    exact h_final

/-- **Density lower bound from isoperimetric inequality + perimeter bound.**

Given a volume function `m(r)` and perimeter function `P(r)` satisfying:
- `m(r)^((n-1)/n) ≤ C1 · P(r)` (isoperimetric inequality)
- `P(r) ≤ C2 · m'(r)` a.e. (perimeter controlled by boundary growth, from
  reduced boundary + coarea + intersection formula)

then `m(r) ≥ (r/(C1·C2·n))^n`.

This bridges the GMT infrastructure to the differential inequality lemma.
Once relative isoperimetric, perimeter intersection formula, and coarea for
distance are delivered, their combination discharges the two hypotheses here. -/
lemma density_from_isoperimetric_and_perimeter_bound
    {n : ℕ} (hn : 1 ≤ n)
    {C1 C2 : ℝ} (hC1_pos : 0 < C1) (hC2_pos : 0 < C2)
    {R : ℝ} (hR_pos : 0 < R)
    {m P : ℝ → ℝ}
    (hm_mono : MonotoneOn m (Set.Icc 0 R))
    (hm_nonneg : ∀ r ∈ Set.Icc 0 R, 0 ≤ m r)
    (hm_ac : AbsolutelyContinuousOnInterval m 0 R)
    (hm0 : m 0 = 0)
    (hm_pos : ∀ r ∈ Set.Ioc 0 R, 0 < m r)
    (h_isop : ∀ r ∈ Set.Ioo 0 R,
        (m r) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤ C1 * P r)
    (h_perim_bound : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R →
        P r ≤ C2 * deriv m r) :
    ∀ r ∈ Set.Icc 0 R, m r ≥ (r / (C1 * C2 * (n : ℝ))) ^ n := by
  have hC12_pos : 0 < C1 * C2 := mul_pos hC1_pos hC2_pos
  have h_diff_ineq : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R →
      deriv m r ≥ (1 / (C1 * C2)) * (m r) ^ (((n : ℝ) - 1) / (n : ℝ)) := by
    filter_upwards [h_perim_bound] with r hP
    intro hr_in
    have h1 : (m r) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤ C1 * P r := h_isop r hr_in
    have h2 : P r ≤ C2 * deriv m r := hP hr_in
    have h3 : (m r) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤ C1 * C2 * deriv m r := by
      calc
        (m r) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤ C1 * P r := h1
        _ ≤ C1 * (C2 * deriv m r) := by gcongr
        _ = C1 * C2 * deriv m r := by ring
    have h4 : 0 < C1 * C2 := hC12_pos
    calc
      deriv m r
        = (1 / (C1 * C2)) * (C1 * C2 * deriv m r) := by
          field_simp [h4.ne'] <;> ring
      _ ≥ (1 / (C1 * C2)) * (m r) ^ (((n : ℝ) - 1) / (n : ℝ)) := by gcongr
  exact isoperimetric_differential_inequality hn hC12_pos hR_pos
    hm_mono hm_nonneg hm_ac hm0 hm_pos h_diff_ineq

end Geometry.StructureTheorem
