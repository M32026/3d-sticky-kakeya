import MyLeanRepo.Kakeya.Cinematic.Statements
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# PYZ Lemma 13: short-interval dichotomy

Paper reference:
`reference/furstenberg_circles_2207.02259/03-geometry-of-cinematic-functions.md`.
-/

namespace Kakeya.Cinematic

theorem preliminary_dichotomy : PreliminaryDichotomyStatement := by
  intro K D hK hD family hfam I hI f hf g hg
  set t := c2Distance f g with ht
  have hK_pos : 0 < K := by linarith
  have h6K_pos : 0 < 6 * K := by linarith
  have h3K_pos : 0 < 3 * K := by linarith

  by_cases h_t0 : t = 0
  · have hL1 : ∀ x ∈ I.carrier, (6 * K)⁻¹ * t ≤ |f x - g x| := by
      intro x _
      rw [h_t0]
      <;> ring_nf <;> exact abs_nonneg _
    have hL2 : ∀ x ∈ I.carrier, (6 * K)⁻¹ * t ≤ |f.firstDeriv x - g.firstDeriv x| := by
      intro x _
      rw [h_t0]
      <;> ring_nf <;> exact abs_nonneg _
    let y0 : UnitPoint := ⟨I.left, I.left_mem⟩
    have hy0 : y0 ∈ I.carrier := by
      exact ⟨le_refl I.left, I.left_le_right⟩
    have hS_false : ¬((∀ x ∈ I.carrier, |f x - g x| < (3 * K)⁻¹ * t) ∧
        (∀ x ∈ I.carrier, |f.firstDeriv x - g.firstDeriv x| < (3 * K)⁻¹ * t)) := by
      intro h
      have h9 : |f y0 - g y0| < (3 * K)⁻¹ * t := h.1 y0 hy0
      rw [h_t0] at h9
      <;> linarith [abs_nonneg (f y0 - g y0)]
    exact ⟨Or.inr hL1, Or.inr hL2, fun h => False.elim (hS_false h)⟩

  · have h_t_pos : 0 < t := by
      exact lt_of_le_of_ne (dist_nonneg) (Ne.symm h_t0)

    let h0 : ℝ → ℝ := f.extension - g.extension
    let h1 : ℝ → ℝ := deriv f.extension - deriv g.extension
    let h2 : ℝ → ℝ := deriv (deriv f.extension) - deriv (deriv g.extension)

    have hfc2 : ContDiff ℝ 2 f.extension := f.extension_contDiff
    have hgc2 : ContDiff ℝ 2 g.extension := g.extension_contDiff
    have h0_c2 : ContDiff ℝ 2 h0 := by
      have h : ContDiff ℝ 2 (fun x : ℝ => f.extension x - g.extension x) :=
        ContDiff.sub hfc2 hgc2
      have h_eq : (fun x : ℝ => f.extension x - g.extension x) = h0 := by
        funext x
        rfl
      rw [h_eq] at h
      exact h
    have hfc1 : ContDiff ℝ 1 (deriv f.extension) := ContDiff.deriv' hfc2
    have hgc1 : ContDiff ℝ 1 (deriv g.extension) := ContDiff.deriv' hgc2
    have h1_c1 : ContDiff ℝ 1 h1 := by
      have h : ContDiff ℝ 1 (fun x : ℝ => deriv f.extension x - deriv g.extension x) :=
        ContDiff.sub hfc1 hgc1
      have h_eq : (fun x : ℝ => deriv f.extension x - deriv g.extension x) = h1 := by
        funext x
        rfl
      rw [h_eq] at h
      exact h

    have h0_diff : Differentiable ℝ h0 := h0_c2.differentiable (by norm_num)
    have h1_diff : Differentiable ℝ h1 := h1_c1.differentiable (by norm_num)
    have hf_diff : Differentiable ℝ f.extension := hfc2.differentiable (by norm_num)
    have hg_diff : Differentiable ℝ g.extension := hgc2.differentiable (by norm_num)
    have hf1_diff : Differentiable ℝ (deriv f.extension) := hfc1.differentiable (by norm_num)
    have hg1_diff : Differentiable ℝ (deriv g.extension) := hgc1.differentiable (by norm_num)

    have h_deriv0 : ∀ (x : ℝ), deriv h0 x = h1 x := by
      intro x
      have h : deriv h0 x = deriv f.extension x - deriv g.extension x := by
        have h_eq : h0 = f.extension - g.extension := by rfl
        rw [h_eq]
        exact deriv_sub hf_diff.differentiableAt hg_diff.differentiableAt
      simpa [h1] using h

    have h_deriv1 : ∀ (x : ℝ), deriv h1 x = h2 x := by
      intro x
      have h : deriv h1 x = deriv (deriv f.extension) x - deriv (deriv g.extension) x := by
        have h_eq : h1 = deriv f.extension - deriv g.extension := by rfl
        rw [h_eq]
        exact deriv_sub hf1_diff.differentiableAt hg1_diff.differentiableAt
      simpa [h2] using h

    have h0_val : ∀ (x : UnitPoint), h0 (x : ℝ) = f x - g x := by
      intro x
      simp [h0]
    have h1_val : ∀ (x : UnitPoint), h1 (x : ℝ) = f.firstDeriv x - g.firstDeriv x := by
      intro x
      simp [h1]
    have h2_val : ∀ (x : UnitPoint), h2 (x : ℝ) = f.secondDeriv x - g.secondDeriv x := by
      intro x
      simp [h2]

    have h_bound1 : ∀ (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 → ‖deriv h0 x‖ ≤ t := by
      intro x hx
      let y : UnitPoint := ⟨x, hx⟩
      have hderiv : deriv h0 x = f.firstDeriv y - g.firstDeriv y := by
        rw [h_deriv0 x, h1_val y]
      rw [hderiv]
      have h_abs : |f.firstDeriv y - g.firstDeriv y| ≤ t :=
        abs_firstDeriv_sub_le_c2Distance f g y
      simpa [Real.norm_eq_abs] using h_abs

    have h_bound2 : ∀ (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 → ‖deriv h1 x‖ ≤ t := by
      intro x hx
      let y : UnitPoint := ⟨x, hx⟩
      have hderiv : deriv h1 x = f.secondDeriv y - g.secondDeriv y := by
        rw [h_deriv1 x, h2_val y]
      rw [hderiv]
      have h_abs : |f.secondDeriv y - g.secondDeriv y| ≤ t :=
        abs_secondDeriv_sub_le_c2Distance f g y
      simpa [Real.norm_eq_abs] using h_abs

    have h0_diff_on : ∀ x ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ h0 x :=
      fun x _ => h0_diff.differentiableAt
    have h1_diff_on : ∀ x ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ h1 x :=
      fun x _ => h1_diff.differentiableAt

    have h_lip1 : ∀ (a b : ℝ), a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |h0 b - h0 a| ≤ t * |b - a| := by
      intro a b ha hb
      have h := Convex.norm_image_sub_le_of_norm_deriv_le
        h0_diff_on h_bound1 (convex_Icc (0 : ℝ) 1) ha hb
      simpa [Real.norm_eq_abs] using h

    have h_lip2 : ∀ (a b : ℝ), a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |h1 b - h1 a| ≤ t * |b - a| := by
      intro a b ha hb
      have h := Convex.norm_image_sub_le_of_norm_deriv_le
        h1_diff_on h_bound2 (convex_Icc (0 : ℝ) 1) ha hb
      simpa [Real.norm_eq_abs] using h

    have h_Icc : ∀ (x : UnitPoint), x ∈ I.carrier → (x : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      intro x _
      exact x.property

    have h_dist : ∀ (x y : UnitPoint), x ∈ I.carrier → y ∈ I.carrier →
        |(x : ℝ) - (y : ℝ)| ≤ (6 * K)⁻¹ := by
      intro x y hx hy
      have h1 : I.left ≤ (x : ℝ) := hx.1
      have h2 : (x : ℝ) ≤ I.right := hx.2
      have h3 : I.left ≤ (y : ℝ) := hy.1
      have h4 : (y : ℝ) ≤ I.right := hy.2
      have h5 : |(x : ℝ) - (y : ℝ)| ≤ I.length := by
        rw [ParameterInterval.length]
        exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
      have h6 : I.length ≤ (6 * K)⁻¹ := hI
      linarith

    have h_triangle : ∀ (a b : ℝ), |a| ≤ |b| + |a - b| := by
      intro a b
      have h : |a| - |b| ≤ |a - b| :=
        abs_sub_abs_le_abs_sub a b
      linarith [abs_nonneg b]

    have h_dich1 : ((∀ x ∈ I.carrier, |f x - g x| < (3 * K)⁻¹ * t) ∨
        (∀ x ∈ I.carrier, (6 * K)⁻¹ * t ≤ |f x - g x|)) := by
      by_cases h : ∀ x ∈ I.carrier, (6 * K)⁻¹ * t ≤ |f x - g x|
      · exact Or.inr h
      · push Not at h
        rcases h with ⟨x₀, hx₀, hlt⟩
        apply Or.inl
        intro x hx
        have h4 : |h0 (x : ℝ) - h0 (x₀ : ℝ)| ≤ t * |(x : ℝ) - (x₀ : ℝ)| :=
          h_lip1 (x₀ : ℝ) (x : ℝ) (h_Icc x₀ hx₀) (h_Icc x hx)
        have h5 : |(x : ℝ) - (x₀ : ℝ)| ≤ (6 * K)⁻¹ :=
          h_dist x x₀ hx hx₀
        have h6 : |f x - g x| ≤
            |f x₀ - g x₀| + |h0 (x : ℝ) - h0 (x₀ : ℝ)| := by
          have h_eq1 : h0 (x : ℝ) = f x - g x := h0_val x
          have h_eq0 : h0 (x₀ : ℝ) = f x₀ - g x₀ := h0_val x₀
          have h7 : |h0 (x : ℝ)| ≤
              |h0 (x₀ : ℝ)| + |h0 (x : ℝ) - h0 (x₀ : ℝ)| :=
            h_triangle (h0 (x : ℝ)) (h0 (x₀ : ℝ))
          simpa [h_eq1, h_eq0] using h7
        have h7 : |h0 (x : ℝ) - h0 (x₀ : ℝ)| ≤ t * (6 * K)⁻¹ := by
          calc
            |h0 (x : ℝ) - h0 (x₀ : ℝ)| ≤
                t * |(x : ℝ) - (x₀ : ℝ)| := h4
            _ ≤ t * (6 * K)⁻¹ :=
              mul_le_mul_of_nonneg_left h5 h_t_pos.le
        have h8 : |f x - g x| ≤ |f x₀ - g x₀| + t * (6 * K)⁻¹ := by
          calc
            |f x - g x| ≤
                |f x₀ - g x₀| + |h0 (x : ℝ) - h0 (x₀ : ℝ)| := h6
            _ ≤ |f x₀ - g x₀| + t * (6 * K)⁻¹ := by gcongr
        have h9 : |f x₀ - g x₀| + t * (6 * K)⁻¹ < (3 * K)⁻¹ * t := by
          have h10 : t * (6 * K)⁻¹ = (6 * K)⁻¹ * t := by ring
          have h11 : (6 * K)⁻¹ * t + (6 * K)⁻¹ * t =
              (3 * K)⁻¹ * t := by
            field_simp [h6K_pos.ne'] <;> ring
          rw [h10]
          linarith
        linarith

    have h_dich2 :
        ((∀ x ∈ I.carrier,
            |f.firstDeriv x - g.firstDeriv x| < (3 * K)⁻¹ * t) ∨
          (∀ x ∈ I.carrier,
            (6 * K)⁻¹ * t ≤ |f.firstDeriv x - g.firstDeriv x|)) := by
      by_cases h : ∀ x ∈ I.carrier,
          (6 * K)⁻¹ * t ≤ |f.firstDeriv x - g.firstDeriv x|
      · exact Or.inr h
      · push Not at h
        rcases h with ⟨x₀, hx₀, hlt⟩
        apply Or.inl
        intro x hx
        have h4 : |h1 (x : ℝ) - h1 (x₀ : ℝ)| ≤
            t * |(x : ℝ) - (x₀ : ℝ)| :=
          h_lip2 (x₀ : ℝ) (x : ℝ) (h_Icc x₀ hx₀) (h_Icc x hx)
        have h5 : |(x : ℝ) - (x₀ : ℝ)| ≤ (6 * K)⁻¹ :=
          h_dist x x₀ hx hx₀
        have h6 : |f.firstDeriv x - g.firstDeriv x| ≤
            |f.firstDeriv x₀ - g.firstDeriv x₀| +
              |h1 (x : ℝ) - h1 (x₀ : ℝ)| := by
          have h_eq1 : h1 (x : ℝ) =
              f.firstDeriv x - g.firstDeriv x := h1_val x
          have h_eq0 : h1 (x₀ : ℝ) =
              f.firstDeriv x₀ - g.firstDeriv x₀ := h1_val x₀
          have h7 : |h1 (x : ℝ)| ≤
              |h1 (x₀ : ℝ)| + |h1 (x : ℝ) - h1 (x₀ : ℝ)| :=
            h_triangle (h1 (x : ℝ)) (h1 (x₀ : ℝ))
          simpa [h_eq1, h_eq0] using h7
        have h7 : |h1 (x : ℝ) - h1 (x₀ : ℝ)| ≤ t * (6 * K)⁻¹ := by
          calc
            |h1 (x : ℝ) - h1 (x₀ : ℝ)| ≤
                t * |(x : ℝ) - (x₀ : ℝ)| := h4
            _ ≤ t * (6 * K)⁻¹ :=
              mul_le_mul_of_nonneg_left h5 h_t_pos.le
        have h8 : |f.firstDeriv x - g.firstDeriv x| ≤
            |f.firstDeriv x₀ - g.firstDeriv x₀| + t * (6 * K)⁻¹ := by
          calc
            |f.firstDeriv x - g.firstDeriv x| ≤
                |f.firstDeriv x₀ - g.firstDeriv x₀| +
                  |h1 (x : ℝ) - h1 (x₀ : ℝ)| := h6
            _ ≤ |f.firstDeriv x₀ - g.firstDeriv x₀| +
                t * (6 * K)⁻¹ := by gcongr
        have h9 : |f.firstDeriv x₀ - g.firstDeriv x₀| +
            t * (6 * K)⁻¹ < (3 * K)⁻¹ * t := by
          have h10 : t * (6 * K)⁻¹ = (6 * K)⁻¹ * t := by ring
          have h11 : (6 * K)⁻¹ * t + (6 * K)⁻¹ * t =
              (3 * K)⁻¹ * t := by
            field_simp [h6K_pos.ne'] <;> ring
          rw [h10]
          linarith
        linarith

    have h_curv : ∀ (x : UnitPoint), K⁻¹ * t ≤ jetGap f g x :=
      hfam.2.2 hf hg
    have h_third :
        (((∀ x ∈ I.carrier, |f x - g x| < (3 * K)⁻¹ * t) ∧
          (∀ x ∈ I.carrier,
            |f.firstDeriv x - g.firstDeriv x| < (3 * K)⁻¹ * t)) →
          ∀ x ∈ I.carrier,
            (6 * K)⁻¹ * t ≤ |f.secondDeriv x - g.secondDeriv x|) := by
      intro h x hx
      have hS1 : |f x - g x| < (3 * K)⁻¹ * t := h.1 x hx
      have hS2 : |f.firstDeriv x - g.firstDeriv x| <
          (3 * K)⁻¹ * t := h.2 x hx
      have hcurv : K⁻¹ * t ≤
          |f x - g x| + |f.firstDeriv x - g.firstDeriv x| +
            |f.secondDeriv x - g.secondDeriv x| :=
        h_curv x
      have h10 : K⁻¹ * t <
          (3 * K)⁻¹ * t + (3 * K)⁻¹ * t +
            |f.secondDeriv x - g.secondDeriv x| := by
        linarith
      have h11 : K⁻¹ * t = 3 * ((3 * K)⁻¹ * t) := by
        field_simp [h3K_pos.ne'] <;> ring
      rw [h11] at h10
      have h12 : (3 * K)⁻¹ * t ≤
          |f.secondDeriv x - g.secondDeriv x| := by
        linarith
      have h13 : (6 * K)⁻¹ * t ≤ (3 * K)⁻¹ * t := by
        have h14 : (6 * K)⁻¹ ≤ (3 * K)⁻¹ := by
          have h16 : 3 * K ≤ 6 * K := by linarith
          have h17 : 1 / (6 * K) ≤ 1 / (3 * K) :=
            one_div_le_one_div_of_le h3K_pos h16
          simpa only [inv_eq_one_div] using h17
        exact mul_le_mul_of_nonneg_right h14 h_t_pos.le
      linarith

    exact ⟨h_dich1, h_dich2, h_third⟩

end Kakeya.Cinematic
