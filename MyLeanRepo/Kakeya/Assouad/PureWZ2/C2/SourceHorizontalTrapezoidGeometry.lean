import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalRichShading

/-!
# Robust Alternative-A geometry on whole source cells
-/

noncomputable section

namespace Kakeya.Assouad

lemma pureWZ2_nonvertical_centered_approximation
    (direction : Point2) (scale : ℝ) (hscale : 0 < scale)
    (f : ℝ → ℝ) (z : ℝ)
    (hdirection : 1 / Real.sqrt 5 ≤ |direction 1|)
    (hstrip :
      |direction 0 * z + direction 1 * f z| ≤
        scale / Real.sqrt 3) :
    |f z - (-(direction 0 / direction 1)) * z| ≤ 2 * scale := by
  have hsqrt3 : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt5 : 0 < Real.sqrt (5 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hdirectionPos : 0 < |direction 1| :=
    (one_div_pos.mpr hsqrt5).trans_le hdirection
  have hdirectionNe : direction 1 ≠ 0 := by
    simpa [abs_pos] using hdirectionPos
  have hformula :
      |f z - (-(direction 0 / direction 1)) * z| =
        |direction 0 * z + direction 1 * f z| / |direction 1| := by
    have heq :
        f z - (-(direction 0 / direction 1)) * z =
          (direction 0 * z + direction 1 * f z) / direction 1 := by
      field_simp [hdirectionNe]
      ring
    rw [heq, abs_div]
  rw [hformula]
  calc
    |direction 0 * z + direction 1 * f z| / |direction 1|
        ≤ (scale / Real.sqrt 3) / |direction 1| :=
      div_le_div_of_nonneg_right hstrip (abs_nonneg _)
    _ ≤ (scale / Real.sqrt 3) / (1 / Real.sqrt 5) := by
      exact div_le_div_of_nonneg_left (by positivity)
        (one_div_pos.mpr hsqrt5) hdirection
    _ ≤ 2 * scale := by
      have hsqrtBound : Real.sqrt (5 : ℝ) ≤ 2 * Real.sqrt 3 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
          Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (3 : ℝ)]
      field_simp [hsqrt3.ne', hsqrt5.ne']
      nlinarith

lemma pureWZ2_near_vertical_centered_approximation
    (direction : Point2) (hdirectionUnit : ‖direction‖ = 1)
    (scale : ℝ) (hscale : 0 < scale)
    (f : ℝ → ℝ)
    (hf : ∀ first second, |f first - f second| ≤ |first - second|)
    (hdirection : |direction 1| < 1 / Real.sqrt 5)
    (first second : ℝ)
    (hfirst :
      |direction 0 * first + direction 1 * f first| ≤
        scale / Real.sqrt 3)
    (hsecond :
      |direction 0 * second + direction 1 * f second| ≤
        scale / Real.sqrt 3) :
    |f first - f second| ≤ 3 * scale := by
  let C : ℝ := 1 / Real.sqrt 3
  let c : ℝ := 1 / Real.sqrt 5
  have hc : 0 < c := by positivity
  have hgap : c ≤ |direction 0| - |direction 1| :=
    near_vertical_gap direction hdirectionUnit hdirection
  have hfirst' :
      |direction 0 * first + direction 1 * f first| ≤ C * scale := by
    simpa [C, div_eq_mul_inv, mul_comm] using hfirst
  have hsecond' :
      |direction 0 * second + direction 1 * f second| ≤ C * scale := by
    simpa [C, div_eq_mul_inv, mul_comm] using hsecond
  have hheight := height_range_bound_of_strip
    direction scale C c hscale hc f hf hgap first second hfirst' hsecond'
  have hratio : 2 * C * scale / c ≤ 3 * scale := by
    have hsqrt3 : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    have hsqrt5 : 0 < Real.sqrt (5 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    have hsqrtBound : 2 * Real.sqrt (5 : ℝ) ≤ 3 * Real.sqrt 3 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
        Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
        Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (3 : ℝ)]
    dsimp only [C, c]
    field_simp [hsqrt3.ne', hsqrt5.ne']
    nlinarith
  exact (hf first second).trans (hheight.trans hratio)

end Kakeya.Assouad
