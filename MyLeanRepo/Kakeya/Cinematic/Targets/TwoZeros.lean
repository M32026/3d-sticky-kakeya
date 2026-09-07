import MyLeanRepo.Kakeya.Cinematic.Statements
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# PYZ Lemma 14: two-zero theorem

Three ordered zeros of the difference of two distinct cinematic functions are
impossible on a sufficiently short parameter interval.

## Proof sketch

Given `f ≠ g` with three zeros `x₁ < x₂ < x₃` of `f - g` on a short interval `I`:

1. Apply Rolle's theorem to `f.extension - g.extension` on `[x₁, x₂]` and
   `[x₂, x₃]` to obtain `y₁`, `y₂` where the first derivative vanishes.
2. Apply Rolle again to the derivative on `[y₁, y₂]` to obtain `z` where the
   second derivative vanishes.
3. By `preliminary_dichotomy`, since `f'' - g''` has a zero, the alternative (L)
   for `f'' - g''` fails. The contrapositive of the last assertion implies that
   (S) cannot hold for both `f - g` and `f' - g'`.
4. Since `f' - g'` has a zero at `y₁`, (L) for `f' - g'` fails, so (S) for
   `f' - g'` must hold.
5. Therefore (S) for `f - g` fails, so (L) for `f - g` holds.
6. But (L) for `f - g` says `|f x - g x| ≥ (6K)⁻¹ * c2Distance f g > 0` for all
   `x ∈ I`, contradicting the zero at `x₁`.
-/

namespace Kakeya.Cinematic

theorem cinematic_difference_has_at_most_two_zeros
    (hPreliminary : PreliminaryDichotomyStatement) :
    TwoZerosStatement := by
  intro K D hK hD family hfam I hI f hf g hg hfg x₁ x₂ x₃ hx₁ hx₂ hx₃ h12 h23 heq1 heq2 heq3
  let t := c2Distance f g
  have ht_pos : 0 < t := by
    have h : 0 < dist f g := dist_pos.mpr hfg
    exact h
  let hfunc : ℝ → ℝ := f.extension - g.extension
  have hfc : ContDiff ℝ 2 f.extension := C2Function.extension_contDiff f
  have hgc : ContDiff ℝ 2 g.extension := C2Function.extension_contDiff g
  have hcd : ContDiff ℝ 2 hfunc := ContDiff.sub hfc hgc
  have h_cont : Continuous hfunc := ContDiff.continuous hcd
  have hcd1 : ContDiff ℝ 1 (deriv hfunc) := ContDiff.deriv' hcd
  have h_deriv_cont : Continuous (deriv hfunc) := ContDiff.continuous hcd1
  have h_eq12 : hfunc (x₁ : ℝ) = hfunc (x₂ : ℝ) := by
    simp [hfunc, heq1, heq2]
  have h_eq23 : hfunc (x₂ : ℝ) = hfunc (x₃ : ℝ) := by
    simp [hfunc, heq2, heq3]
  -- Rolle on [x₁, x₂]
  obtain ⟨y₁, hy₁_mem, hy₁_deriv⟩ :=
    exists_deriv_eq_zero h12 h_cont.continuousOn h_eq12
  -- Rolle on [x₂, x₃]
  obtain ⟨y₂, hy₂_mem, hy₂_deriv⟩ :=
    exists_deriv_eq_zero h23 h_cont.continuousOn h_eq23
  have hy₁_lt_y₂ : y₁ < y₂ := by
    have h1 : y₁ < (x₂ : ℝ) := hy₁_mem.2
    have h2 : (x₂ : ℝ) < y₂ := hy₂_mem.1
    linarith
  have h_deriv_eq12 : deriv hfunc y₁ = deriv hfunc y₂ := by
    rw [hy₁_deriv, hy₂_deriv]
  -- Rolle on deriv hfunc over [y₁, y₂]
  obtain ⟨z, hz_mem, hz_deriv2⟩ :=
    exists_deriv_eq_zero hy₁_lt_y₂ h_deriv_cont.continuousOn h_deriv_eq12
  -- All points are in [0,1]
  have hx₁_in : (x₁ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := x₁.prop
  have hx₃_in : (x₃ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := x₃.prop
  have hy₁_in : y₁ ∈ Set.Icc (0 : ℝ) 1 := by
    have h1 : (x₁ : ℝ) < y₁ := hy₁_mem.1
    have h2 : y₁ < (x₂ : ℝ) := hy₁_mem.2
    exact ⟨by linarith [hx₁_in.1], by linarith [hx₃_in.2]⟩
  have hy₂_in : y₂ ∈ Set.Icc (0 : ℝ) 1 := by
    have h1 : (x₂ : ℝ) < y₂ := hy₂_mem.1
    have h2 : y₂ < (x₃ : ℝ) := hy₂_mem.2
    exact ⟨by linarith [hx₁_in.1], by linarith [hx₃_in.2]⟩
  have hz_in : z ∈ Set.Icc (0 : ℝ) 1 := by
    have h1 : y₁ < z := hz_mem.1
    have h2 : z < y₂ := hz_mem.2
    exact ⟨by linarith [hy₁_in.1], by linarith [hy₂_in.2]⟩
  let y₁' : UnitPoint := ⟨y₁, hy₁_in⟩
  let y₂' : UnitPoint := ⟨y₂, hy₂_in⟩
  let z' : UnitPoint := ⟨z, hz_in⟩
  -- y₁', y₂', z' are in I.carrier
  have hy₁'_inI : y₁' ∈ I.carrier := by
    simp only [ParameterInterval.carrier, Set.mem_setOf_eq]
    have h1 : (x₁ : ℝ) < y₁ := hy₁_mem.1
    have h2 : y₁ < (x₂ : ℝ) := hy₁_mem.2
    have hx₁_left : I.left ≤ (x₁ : ℝ) := hx₁.1
    have hx₂_right : (x₂ : ℝ) ≤ I.right := hx₂.2
    exact ⟨by linarith, by linarith⟩
  have hy₂'_inI : y₂' ∈ I.carrier := by
    simp only [ParameterInterval.carrier, Set.mem_setOf_eq]
    have h1 : (x₂ : ℝ) < y₂ := hy₂_mem.1
    have h2 : y₂ < (x₃ : ℝ) := hy₂_mem.2
    have hx₂_left : I.left ≤ (x₂ : ℝ) := hx₂.1
    have hx₃_right : (x₃ : ℝ) ≤ I.right := hx₃.2
    exact ⟨by linarith, by linarith⟩
  have hz'_inI : z' ∈ I.carrier := by
    simp only [ParameterInterval.carrier, Set.mem_setOf_eq]
    have h1 : y₁ < z := hz_mem.1
    have h2 : z < y₂ := hz_mem.2
    have hy₁_left : I.left ≤ y₁ := hy₁'_inI.1
    have hy₂_right : y₂ ≤ I.right := hy₂'_inI.2
    exact ⟨by linarith, by linarith⟩
  -- Differentiability facts
  have hf_diff : Differentiable ℝ f.extension := ContDiff.differentiable hfc (by norm_num)
  have hg_diff : Differentiable ℝ g.extension := ContDiff.differentiable hgc (by norm_num)
  have hfderiv_diff : Differentiable ℝ (deriv f.extension) :=
    ContDiff.differentiable_deriv_two hfc
  have hgderiv_diff : Differentiable ℝ (deriv g.extension) :=
    ContDiff.differentiable_deriv_two hgc
  -- Derivative equalities
  have h_diff : ∀ (x : UnitPoint), deriv hfunc (x : ℝ) = f.firstDeriv x - g.firstDeriv x := by
    intro x
    have h1 : deriv hfunc (x : ℝ) = deriv f.extension (x : ℝ) - deriv g.extension (x : ℝ) := by
      rw [show hfunc = f.extension - g.extension from rfl]
      exact deriv_sub hf_diff.differentiableAt hg_diff.differentiableAt
    rw [h1]
    simp
  have h_diff2 : ∀ (x : UnitPoint), deriv (deriv hfunc) (x : ℝ) = f.secondDeriv x - g.secondDeriv x := by
    intro x
    have h21 : deriv hfunc = deriv f.extension - deriv g.extension := by
      funext y
      rw [show hfunc = f.extension - g.extension from rfl]
      exact deriv_sub hf_diff.differentiableAt hg_diff.differentiableAt
    rw [h21]
    have h22 : deriv (deriv f.extension - deriv g.extension) (x : ℝ) =
        deriv (deriv f.extension) (x : ℝ) - deriv (deriv g.extension) (x : ℝ) := by
      exact deriv_sub hfderiv_diff.differentiableAt hgderiv_diff.differentiableAt
    rw [h22]
    simp
  -- f.firstDeriv y₁' = g.firstDeriv y₁'
  have hfy₁ : f.firstDeriv y₁' = g.firstDeriv y₁' := by
    have h : deriv hfunc y₁ = 0 := hy₁_deriv
    have h2 : deriv hfunc y₁ = f.firstDeriv y₁' - g.firstDeriv y₁' := h_diff y₁'
    rw [h2] at h
    linarith
  -- f.firstDeriv y₂' = g.firstDeriv y₂'
  have hfy₂ : f.firstDeriv y₂' = g.firstDeriv y₂' := by
    have h : deriv hfunc y₂ = 0 := hy₂_deriv
    have h2 : deriv hfunc y₂ = f.firstDeriv y₂' - g.firstDeriv y₂' := h_diff y₂'
    rw [h2] at h
    linarith
  -- f.secondDeriv z' = g.secondDeriv z'
  have hfz : f.secondDeriv z' = g.secondDeriv z' := by
    have h : deriv (deriv hfunc) z = 0 := hz_deriv2
    have h2 : deriv (deriv hfunc) z = f.secondDeriv z' - g.secondDeriv z' := h_diff2 z'
    rw [h2] at h
    linarith
  -- Now apply preliminary_dichotomy
  have dich := hPreliminary K D hK hD family hfam I hI f hf g hg
  rcases dich with ⟨dich_val, dich_deriv, dich_deriv2⟩
  -- (L) for f''-g'' fails at z'
  have hz_abs : |f.secondDeriv z' - g.secondDeriv z'| = 0 := by
    simp [hfz]
  have h_third_pos : 0 < (6 * K)⁻¹ * t := by positivity
  have h_not_L_deriv2 : ¬(∀ x ∈ I.carrier, (6 * K)⁻¹ * t ≤ |f.secondDeriv x - g.secondDeriv x|) := by
    intro h
    have h4 := h z' hz'_inI
    rw [hz_abs] at h4
    linarith
  -- By contrapositive: NOT (S for f-g AND S for f'-g')
  have h_not_both_S : ¬((∀ x ∈ I.carrier, |f x - g x| < (3 * K)⁻¹ * t) ∧
      (∀ x ∈ I.carrier, |f.firstDeriv x - g.firstDeriv x| < (3 * K)⁻¹ * t)) := by
    intro h
    exact h_not_L_deriv2 (dich_deriv2 h)
  -- (L) for f'-g' fails at y₁'
  have hy₁_abs : |f.firstDeriv y₁' - g.firstDeriv y₁'| = 0 := by
    simp [hfy₁]
  have h_not_L_deriv : ¬(∀ x ∈ I.carrier, (6 * K)⁻¹ * t ≤ |f.firstDeriv x - g.firstDeriv x|) := by
    intro h
    have h4 := h y₁' hy₁'_inI
    rw [hy₁_abs] at h4
    linarith
  -- From dich_deriv: (S for f'-g') OR (L for f'-g')
  have h_S_deriv : ∀ x ∈ I.carrier, |f.firstDeriv x - g.firstDeriv x| < (3 * K)⁻¹ * t := by
    rcases dich_deriv with (h | h)
    · exact h
    · exfalso
      exact h_not_L_deriv h
  -- From h_not_both_S and h_S_deriv: NOT (S for f-g)
  have h_not_S_val : ¬(∀ x ∈ I.carrier, |f x - g x| < (3 * K)⁻¹ * t) := by
    intro h
    exact h_not_both_S ⟨h, h_S_deriv⟩
  -- From dich_val: (S for f-g) OR (L for f-g)
  have h_L_val : ∀ x ∈ I.carrier, (6 * K)⁻¹ * t ≤ |f x - g x| := by
    rcases dich_val with (h | h)
    · exfalso
      exact h_not_S_val h
    · exact h
  -- But x₁ is a zero of f-g
  have hx₁_abs : |f x₁ - g x₁| = 0 := by
    simp [heq1]
  have h_contra := h_L_val x₁ hx₁
  rw [hx₁_abs] at h_contra
  linarith

end Kakeya.Cinematic
