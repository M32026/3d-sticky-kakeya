import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Derivative bound via Mean Value Theorem

If f is continuous on [a,b], differentiable on (a,b), and |f(x)| ≤ M,
then there exists x₁ ∈ [a,b] such that |f'(x₁)| ≤ 2M/(b-a).

This follows directly from the Mean Value Theorem.
-/

namespace Kakeya.Cinematic

open Set

/--
MVT derivative bound: if f is continuous on [a,b], differentiable on (a,b),
and |f(x)| ≤ M for all x ∈ [a,b], then ∃ x₁ ∈ [a,b] with |f'(x₁)| ≤ 2M/(b-a).
-/
lemma exists_deriv_bound_by_mvt
    {f f' : ℝ → ℝ} {a b M : ℝ}
    (hab : a < b)
    (hcont : ContinuousOn f (Icc a b))
    (hdiff : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hbound : ∀ x ∈ Icc a b, |f x| ≤ M) :
    ∃ x₁ ∈ Icc a b, |f' x₁| ≤ 2 * M / (b - a) := by
  set L := b - a with hL_def
  have hL_pos : 0 < L := by linarith
  have hL_ne : L ≠ 0 := by linarith

  have h_diff_on : DifferentiableOn ℝ f (Ioo a b) := by
    intro x hx
    exact (hdiff x hx).differentiableAt.differentiableWithinAt

  have h_mvt : ∃ ξ ∈ Ioo a b, deriv f ξ = (f b - f a) / L :=
    exists_deriv_eq_slope f hab hcont h_diff_on
  rcases h_mvt with ⟨ξ, hξ, hξ_eq⟩

  have h_deriv_eq : deriv f ξ = f' ξ := (hdiff ξ hξ).deriv
  have h_f'_eq : f' ξ = (f b - f a) / L := by
    rw [←h_deriv_eq, hξ_eq]

  have h_bound : |f' ξ| ≤ 2 * M / L := by
    rw [h_f'_eq]
    have h1 : |(f b - f a) / L| = |f b - f a| / L := by
      rw [abs_div, abs_of_pos hL_pos]
    rw [h1]
    have h2 : |f b - f a| ≤ |f b| + |f a| := abs_sub (f b) (f a)
    have h3 : |f b| ≤ M := hbound b (right_mem_Icc.mpr (by linarith))
    have h4 : |f a| ≤ M := hbound a (left_mem_Icc.mpr (by linarith))
    have h5 : |f b - f a| ≤ 2 * M := by linarith
    have h6 : |f b - f a| / L ≤ 2 * M / L := by gcongr
    exact h6

  have hξ_cc : ξ ∈ Icc a b := ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
  exact ⟨ξ, hξ_cc, h_bound⟩

/--
If |f''(x)| ≤ B on [a,b], then f' is B-Lipschitz:
|f'(x) - f'(y)| ≤ B * |x - y| for all x, y ∈ [a,b].
-/
lemma deriv_lipschitz_from_second_deriv
    {f' f'' : ℝ → ℝ} {a b B : ℝ}
    (f'_cont : ContinuousOn f' (Icc a b))
    (f'_deriv : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (hB : ∀ x ∈ Icc a b, |f'' x| ≤ B) :
    ∀ (x y : ℝ), x ∈ Icc a b → y ∈ Icc a b → |f' x - f' y| ≤ B * |x - y| := by
  have h_main : ∀ (x y : ℝ), x ∈ Icc a b → y ∈ Icc a b → x < y →
      |f' y - f' x| ≤ B * (y - x) := by
    intro x y hx hy hlt
    have h_ax : a ≤ x := hx.1
    have h_yb : y ≤ b := hy.2
    have h_diff_on : DifferentiableOn ℝ f' (Ioo x y) := by
      intro z hz
      have h_z1 : a < z := lt_of_le_of_lt h_ax hz.1
      have h_z2 : z < b := lt_of_lt_of_le hz.2 h_yb
      exact (f'_deriv z ⟨h_z1, h_z2⟩).differentiableAt.differentiableWithinAt
    have h_cont' : ContinuousOn f' (Icc x y) :=
      f'_cont.mono (Icc_subset_Icc h_ax h_yb)
    have h_mvt : ∃ ξ ∈ Ioo x y, deriv f' ξ = (f' y - f' x) / (y - x) :=
      exists_deriv_eq_slope f' hlt h_cont' h_diff_on
    rcases h_mvt with ⟨ξ, hξ, hξ_eq⟩
    have hξ_oo1 : a < ξ := lt_of_le_of_lt h_ax hξ.1
    have hξ_oo2 : ξ < b := lt_of_lt_of_le hξ.2 h_yb
    have hξ_oo : ξ ∈ Ioo a b := ⟨hξ_oo1, hξ_oo2⟩
    have hξ_in_ab : ξ ∈ Icc a b := ⟨le_of_lt hξ_oo1, le_of_lt hξ_oo2⟩
    have h_deriv_eq : deriv f' ξ = f'' ξ := (f'_deriv ξ hξ_oo).deriv
    rw [h_deriv_eq] at hξ_eq
    have h_bound : |f'' ξ| ≤ B := hB ξ hξ_in_ab
    have h_pos : 0 < y - x := by linarith
    have h_eq : |f' y - f' x| = |f'' ξ| * (y - x) := by
      have h9 : f' y - f' x = f'' ξ * (y - x) := by
        field_simp [h_pos.ne'] at hξ_eq ⊢ <;> linarith
      rw [h9, abs_mul, abs_of_pos h_pos]
    rw [h_eq]
    exact mul_le_mul_of_nonneg_right h_bound (by linarith)

  intro x y hx hy
  by_cases hxy : x = y
  · rw [hxy]; simp
  · by_cases hlt : x < y
    · have h := h_main x y hx hy hlt
      have h_neg : x - y < 0 := by linarith
      have h_abs : |x - y| = y - x := by
        rw [abs_of_neg h_neg] <;> linarith
      rw [h_abs]
      simpa [abs_sub_comm] using h
    · have hlt' : y < x := by
        by_contra h; exact hxy (by linarith)
      have h := h_main y x hy hx hlt'
      have h_pos : 0 < x - y := by linarith
      have h_abs : |x - y| = x - y := by
        rw [abs_of_pos h_pos]
      rw [h_abs]
      exact h

/--
Uniform derivative bound: if |f| ≤ M and |f''| ≤ B on [a,b], then
|f'(x)| ≤ 2M/(b-a) + B*(b-a) for all x ∈ [a,b].

Proof: MVT gives x₁ with |f'(x₁)| ≤ 2M/(b-a). Then f' is B-Lipschitz,
so |f'(x)| ≤ |f'(x₁)| + B*|x-x₁| ≤ 2M/(b-a) + B*(b-a).
-/
lemma uniform_deriv_bound
    {f f' f'' : ℝ → ℝ} {a b M B : ℝ}
    (hab : a < b)
    (f_cont : ContinuousOn f (Icc a b))
    (f_deriv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (f'_cont : ContinuousOn f' (Icc a b))
    (f'_deriv : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ Icc a b, |f x| ≤ M)
    (hB : ∀ x ∈ Icc a b, |f'' x| ≤ B) :
    ∀ x ∈ Icc a b, |f' x| ≤ 2 * M / (b - a) + B * (b - a) := by
  set L := b - a with hL_def
  have hL_pos : 0 < L := by linarith

  have h1 := exists_deriv_bound_by_mvt hab f_cont f_deriv hM
  rcases h1 with ⟨x₁, hx₁, h_bound1⟩

  have h_lip := deriv_lipschitz_from_second_deriv f'_cont f'_deriv hB

  intro x hx
  have h2 : |f' x - f' x₁| ≤ B * |x - x₁| := h_lip x x₁ hx hx₁
  have h3 : |x - x₁| ≤ L := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hx₁.1, hx₁.2]
  have h4 : |f' x| ≤ |f' x₁| + |f' x - f' x₁| := by
    have h41 : |f' x| = |f' x₁ + (f' x - f' x₁)| := by ring_nf
    rw [h41]
    have h42 : -(|f' x₁| + |f' x - f' x₁|) ≤ f' x₁ + (f' x - f' x₁) := by
      have h421 : -|f' x₁| ≤ f' x₁ := by
        have h1 : -(f' x₁) ≤ |-(f' x₁)| := le_abs_self (-(f' x₁))
        have h2 : |-(f' x₁)| = |f' x₁| := by rw [abs_neg]
        rw [h2] at h1
        linarith
      have h422 : -|f' x - f' x₁| ≤ f' x - f' x₁ := by
        have h1 : -(f' x - f' x₁) ≤ |-(f' x - f' x₁)| := le_abs_self (-(f' x - f' x₁))
        have h2 : |-(f' x - f' x₁)| = |f' x - f' x₁| := by rw [abs_neg]
        rw [h2] at h1
        linarith
      linarith
    have h43 : f' x₁ + (f' x - f' x₁) ≤ |f' x₁| + |f' x - f' x₁| := by
      have h431 : f' x₁ ≤ |f' x₁| := le_abs_self (f' x₁)
      have h432 : f' x - f' x₁ ≤ |f' x - f' x₁| := le_abs_self (f' x - f' x₁)
      linarith
    exact abs_le.mpr ⟨h42, h43⟩
  have hB_nonneg : 0 ≤ B := by
    have h : |f'' a| ≤ B := hB a (left_mem_Icc.mpr (by linarith))
    have h' : 0 ≤ |f'' a| := abs_nonneg _
    linarith
  have h5 : |f' x - f' x₁| ≤ B * L := by
    calc |f' x - f' x₁|
      ≤ B * |x - x₁| := h2
    _ ≤ B * L := by
      exact mul_le_mul_of_nonneg_left h3 hB_nonneg
  linarith [h_bound1, h4, h5]

end Kakeya.Cinematic
