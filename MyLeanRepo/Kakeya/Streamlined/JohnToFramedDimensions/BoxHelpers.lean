import MyLeanRepo.Kakeya.Streamlined.JohnToFramedDimensions.PrincipalAxes
import MyLeanRepo.Kakeya.Streamlined.Geometry
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Helper lemmas for box-ellipsoid inclusions

These lemmas relate ellipsoids (images of the unit ball under a linear map)
to axis-aligned boxes, using the SVD decomposition.
-/

noncomputable section

open JohnEllipsoid

namespace Kakeya.Streamlined

/-- The square of `1 / (3 * √3)` equals `1 / 27`. -/
lemma one_over_3sqrt3_sq : (1 / (3 * Real.sqrt 3)) ^ 2 = 1 / 27 := by
  have h : (3 * Real.sqrt 3) ^ 2 = 27 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  field_simp [h] <;> nlinarith

/--
Given singular values `σ` and orthonormal basis `v`, if
`w = ∑ i, l i • v i`, then `‖w‖^2 = ∑ i, (l i)^2`.
-/
lemma norm_of_orthonormal_combination {v : OrthonormalBasis (Fin 3) ℝ (E 3)}
    {l : Fin 3 → ℝ} : ‖(∑ i : Fin 3, l i • v i)‖ ^ 2 = ∑ i : Fin 3, (l i)^2 := by
  have h1 : inner ℝ (∑ i : Fin 3, l i • v i) (∑ i : Fin 3, l i • v i) =
      ∑ i : Fin 3, (l i)^2 := by
    have h2 := Orthonormal.inner_sum v.orthonormal l l Finset.univ
    have h3 : ∑ i : Fin 3, (starRingEnd ℝ) (l i) * l i = ∑ i : Fin 3, (l i)^2 := by
      apply Finset.sum_congr rfl
      intro i _
      simp [starRingEnd]
      <;> ring
    rw [h2, h3]
  have h3 : ‖(∑ i : Fin 3, l i • v i)‖ ^ 2 =
      inner ℝ (∑ i : Fin 3, l i • v i) (∑ i : Fin 3, l i • v i) := by
    simp [real_inner_self_eq_norm_sq]
  rw [h3, h1]

/-- If `|x| ≤ y / (3 * √3)` and `y > 0`, then `(x / y)^2 ≤ 1 / 27`. -/
lemma div_sq_bound {x y : ℝ} (hy : 0 < y) (h : |x| ≤ y / (3 * Real.sqrt 3)) :
    (x / y)^2 ≤ 1 / 27 := by
  have h1 : |x / y| ≤ 1 / (3 * Real.sqrt 3) := by
    calc |x / y|
      = |x| / y := by rw [abs_div, abs_of_pos hy]
    _ ≤ (y / (3 * Real.sqrt 3)) / y := div_le_div_of_nonneg_right h hy.le
    _ = 1 / (3 * Real.sqrt 3) := by
      field_simp [hy.ne'] <;> ring
  have h2 : (x / y)^2 = |x / y|^2 := by rw [sq_abs]
  rw [h2]
  have h3 : |x / y|^2 ≤ (1 / (3 * Real.sqrt 3))^2 := by gcongr
  rw [one_over_3sqrt3_sq] at h3
  exact h3

end Kakeya.Streamlined
