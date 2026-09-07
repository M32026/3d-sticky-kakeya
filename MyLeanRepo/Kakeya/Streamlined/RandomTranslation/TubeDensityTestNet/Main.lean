import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet.GeometricLemmas
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet.Grids
import MyLeanRepo.Kakeya.Streamlined.MaximalDensityFactoring.DensityMax
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.FrameMatrixGrid
import MyLeanRepo.Kakeya.Streamlined.VolumeHelpers
import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.Estimates
import Mathlib.Analysis.Convex.Hull
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Helper lemmas for the tube density test net theorem

This module contains independent proved helper lemmas used in the
tube density test net construction.

The main theorem `tube_density_test_net` is in `Targets/TubeDensityTestNet.lean`.
-/

noncomputable section

open MeasureTheory Metric Finset
open scoped Pointwise
open Kakeya.Streamlined.GeometricLemmas
open Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet

namespace Kakeya.Streamlined

/-- Apply a 3×3 matrix to a Point3 via the EuclideanSpace equivalence. -/
def matrixToLin (M : Matrix (Fin 3) (Fin 3) ℝ) : Point3 →ₗ[ℝ] Point3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearMap.comp <|
    (Matrix.toLin' M).comp (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap

lemma matrixToLin_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (x : Point3) (i : Fin 3) :
    (matrixToLin M x) i = ∑ j : Fin 3, M i j * x j := by
  rfl

lemma matrixToLin_mul (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    matrixToLin (A * B) = (matrixToLin A).comp (matrixToLin B) := by
  let e : Point3 ≃ₗ[ℝ] (Fin 3 → ℝ) := EuclideanSpace.equiv (Fin 3) ℝ
  ext x
  have h1 : matrixToLin (A * B) x =
      e.symm (Matrix.toLin' (A * B) (e x)) := by rfl
  have h2 : (matrixToLin A).comp (matrixToLin B) x =
      e.symm (Matrix.toLin' A (e (e.symm (Matrix.toLin' B (e x))))) := by rfl
  rw [h1, h2]
  have h3 : e (e.symm (Matrix.toLin' B (e x))) = Matrix.toLin' B (e x) :=
    e.apply_symm_apply _
  rw [h3]
  have h4 : Matrix.toLin' (A * B) = (Matrix.toLin' A).comp (Matrix.toLin' B) :=
    Matrix.toLin'_mul A B
  rw [h4]
  <;> rfl

lemma matrixToLin_add (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    matrixToLin (A + B) = matrixToLin A + matrixToLin B := by
  let e : Point3 ≃ₗ[ℝ] (Fin 3 → ℝ) := EuclideanSpace.equiv (Fin 3) ℝ
  ext x
  simp [matrixToLin, LinearMap.add_apply, Matrix.toLin'_apply, e.apply_symm_apply]
  <;> rfl

lemma matrixToLin_sub (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    matrixToLin (A - B) = matrixToLin A - matrixToLin B := by
  let e : Point3 ≃ₗ[ℝ] (Fin 3 → ℝ) := EuclideanSpace.equiv (Fin 3) ℝ
  ext x
  simp [matrixToLin, LinearMap.sub_apply, Matrix.toLin'_apply, e.apply_symm_apply]
  <;> rfl

lemma matrixToLin_one :
    matrixToLin (1 : Matrix (Fin 3) (Fin 3) ℝ) = LinearMap.id := by
  let e : Point3 ≃ₗ[ℝ] (Fin 3 → ℝ) := EuclideanSpace.equiv (Fin 3) ℝ
  ext x
  simp [matrixToLin, Matrix.toLin'_one, e.apply_symm_apply]
  <;> rfl

lemma norm_sq_point3 (v : Point3) : ‖v‖ ^ 2 = ∑ i : Fin 3, (v i) ^ 2 := by
  have h : ‖v‖ ^ 2 = inner ℝ v v := (real_inner_self_eq_norm_sq v).symm
  rw [h]
  simp [inner, Fin.sum_univ_succ] <;> ring

/-- A test parallelepiped: image of an axis box under a matrix, translated, intersected with B(0,20). -/
def testParallelepiped (c : Point3) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (a b c_dim : ℝ) : Set Point3 :=
  let f : Point3 → Point3 := fun x => matrixToLin M x
  let S : Set Point3 := f '' axisBox a b c_dim
  (c +ᵥ S) ∩ closedBall (0 : Point3) 20

/-! ### Helper lemmas for rounding -/

/-- If open ball radius δ is in an axisBox, smallest dimension ≥ 2δ. -/
lemma ball_in_axisBox_dim_bound {δ d e f : ℝ} (hδ : 0 < δ)
    (hd : 0 < d) (q : Point3) (h : Metric.ball q δ ⊆ axisBox d e f) : d ≥ 2 * δ := by
  let e0 : Point3 := EuclideanSpace.single 0 1
  have h_e0_norm : ‖e0‖ = 1 := by simp [e0]
  have hq_in : q ∈ axisBox d e f := h (by simp [Metric.mem_ball, hδ])
  have hq0 : |q 0| ≤ d / 2 := hq_in.1
  have hq0_le : q 0 ≤ d / 2 := by linarith [abs_le.mp hq0]
  have hq0_ge : -d / 2 ≤ q 0 := by linarith [abs_le.mp hq0]
  have h_pos : ∀ (r : ℝ), 0 ≤ r → r < δ → |q 0 + r| ≤ d / 2 := by
    intro r hr_pos hr_lt
    have h_in : q + r • e0 ∈ Metric.ball q δ := by
      simpa [Metric.mem_ball, dist_eq_norm, h_e0_norm, norm_smul, abs_of_nonneg hr_pos] using hr_lt
    have h5 : q + r • e0 ∈ axisBox d e f := h h_in
    have h6 : |(q + r • e0) 0| ≤ d / 2 := h5.1
    have h7 : (q + r • e0) 0 = q 0 + r := by
      simp [e0, EuclideanSpace.single] <;> ring
    rw [h7] at h6
    exact h6
  have h_neg : ∀ (r : ℝ), 0 ≤ r → r < δ → |q 0 - r| ≤ d / 2 := by
    intro r hr_pos hr_lt
    have h_in : q - r • e0 ∈ Metric.ball q δ := by
      simpa [Metric.mem_ball, dist_eq_norm, h_e0_norm, norm_smul, abs_neg, abs_of_nonneg hr_pos] using hr_lt
    have h5 : q - r • e0 ∈ axisBox d e f := h h_in
    have h6 : |(q - r • e0) 0| ≤ d / 2 := h5.1
    have h7 : (q - r • e0) 0 = q 0 - r := by
      simp [e0, EuclideanSpace.single] <;> ring
    rw [h7] at h6
    exact h6
  have h1 : q 0 + δ ≤ d / 2 := by
    by_contra h4
    have h5 : 0 < q 0 + δ - d / 2 := by linarith
    set ε : ℝ := (q 0 + δ - d / 2) / 2 with hε_def
    have hε_pos : 0 < ε := by linarith
    have hε_le : ε ≤ δ := by linarith [hq0_le]
    set r : ℝ := δ - ε with hr_def
    have hr_lt : r < δ := by linarith
    have hr_pos : 0 ≤ r := by linarith
    have h6 : q 0 + r > d / 2 := by
      simp [hr_def, hε_def] <;> linarith
    have h7 : |q 0 + r| ≤ d / 2 := h_pos r hr_pos hr_lt
    have h8 : q 0 + r ≤ d / 2 := by linarith [abs_le.mp h7]
    linarith
  have h2 : -q 0 + δ ≤ d / 2 := by
    by_contra h4
    have h5 : 0 < -q 0 + δ - d / 2 := by linarith
    set ε : ℝ := (-q 0 + δ - d / 2) / 2 with hε_def
    have hε_pos : 0 < ε := by linarith
    have hε_le : ε ≤ δ := by linarith [hq0_ge]
    set r : ℝ := δ - ε with hr_def
    have hr_lt : r < δ := by linarith
    have hr_pos : 0 ≤ r := by linarith
    have h7 : |q 0 - r| ≤ d / 2 := h_neg r hr_pos hr_lt
    have h8 : -(q 0 - r) ≤ d / 2 := by linarith [abs_le.mp h7]
    simp [hr_def, hε_def] at h8 <;> linarith
  linarith

/-- Operator norm ≤ 3 times max entrywise bound for 3×3 matrices. -/
lemma operator_norm_entrywise_bound (B : Matrix (Fin 3) (Fin 3) ℝ)
    (C : ℝ) (hC : 0 ≤ C) (h : ∀ i j, |B i j| ≤ C) :
    ‖(matrixToLin B).toContinuousLinearMap‖ ≤ 3 * C := by
  have h1 : ∀ (x : Point3), ‖matrixToLin B x‖ ≤ 3 * C * ‖x‖ := by
    intro x
    have h2 : ‖matrixToLin B x‖ ^ 2 = ∑ i : Fin 3, (∑ j : Fin 3, B i j * x j) ^ 2 := by
      rw [norm_sq_point3 (matrixToLin B x)]
      apply Finset.sum_congr rfl
      intro i _
      rw [matrixToLin_apply B x i]
    have h3 : ∀ i : Fin 3, (∑ j : Fin 3, B i j * x j) ^ 2 ≤ (∑ j : Fin 3, (B i j)^2) * ‖x‖ ^ 2 := by
      intro i
      have h4 : (∑ j : Fin 3, B i j * x j) ^ 2 ≤ (∑ j : Fin 3, (B i j)^2) * (∑ j : Fin 3, (x j)^2) :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => B i j) (fun j => x j)
      have h5 : ‖x‖ ^ 2 = ∑ j : Fin 3, (x j)^2 := by
        have h6 : ‖x‖ ^ 2 = inner ℝ x x := (real_inner_self_eq_norm_sq x).symm
        rw [h6]; simp [inner, Fin.sum_univ_succ] <;> ring
      rw [←h5] at h4; exact h4
    have h4 : ∑ i : Fin 3, (∑ j : Fin 3, B i j * x j) ^ 2 ≤ ∑ i : Fin 3, ((∑ j : Fin 3, (B i j)^2) * ‖x‖ ^ 2) := by
      apply Finset.sum_le_sum; intro i _; exact h3 i
    have h5 : ∀ i : Fin 3, (∑ j : Fin 3, (B i j)^2) ≤ 3 * C^2 := by
      intro i
      have h6 : ∀ j, (B i j)^2 ≤ C^2 := by
        intro j
        have h7 : |B i j| ≤ C := h i j
        have h8 : (B i j)^2 = |B i j|^2 := by rw [sq_abs]
        rw [h8]
        gcongr
      have h8 : ∑ j : Fin 3, (B i j)^2 ≤ ∑ j : Fin 3, C^2 := by
        apply Finset.sum_le_sum; intro j _; exact h6 j
      simpa using h8
    have h6 : ∑ i : Fin 3, ((∑ j : Fin 3, (B i j)^2) * ‖x‖ ^ 2) ≤ 9 * C^2 * ‖x‖ ^ 2 := by
      have h7 : ∑ i : Fin 3, ((∑ j : Fin 3, (B i j)^2) * ‖x‖ ^ 2) = (∑ i : Fin 3, (∑ j : Fin 3, (B i j)^2)) * ‖x‖ ^ 2 := by
        rw [Finset.sum_mul]
      rw [h7]
      have h8 : ∑ i : Fin 3, (∑ j : Fin 3, (B i j)^2) ≤ 3 * (3 * C^2) := by
        have h9 : ∀ i, (∑ j : Fin 3, (B i j)^2) ≤ 3 * C^2 := h5
        have h10 : ∑ i : Fin 3, (∑ j : Fin 3, (B i j)^2) ≤ ∑ i : Fin 3, (3 * C^2) := by
          apply Finset.sum_le_sum; intro i _; exact h9 i
        simpa using h10
      nlinarith
    have h7 : ‖matrixToLin B x‖ ^ 2 ≤ (3 * C * ‖x‖) ^ 2 := by nlinarith
    have h8 : 0 ≤ ‖matrixToLin B x‖ := by positivity
    have h9 : 0 ≤ 3 * C * ‖x‖ := by positivity
    nlinarith
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) h1

/-! ### Near-orthogonal matrix inverse norm -/

/-- Inverse operator norm ≤ 2 for near-orthogonal matrices. -/
lemma near_orthogonal_inverse_norm (M : Matrix (Fin 3) (Fin 3) ℝ)
    (h : isNearOrthogonal M) :
    ‖(matrixToLin (M⁻¹)).toContinuousLinearMap‖ ≤ 2 := by
  let f := matrixToLin M
  let f_inv := matrixToLin (M⁻¹)
  let B_mat := M.transpose * M - 1
  have hB : ∀ i j, |B_mat i j| ≤ 1 / 10 := by
    intro i j
    simpa [B_mat, isNearOrthogonal, Matrix.sub_apply, Matrix.one_apply] using h i j
  have hB_norm : ‖(matrixToLin B_mat).toContinuousLinearMap‖ ≤ 3 / 10 := by
    have h := operator_norm_entrywise_bound B_mat (1 / 10) (by norm_num) hB
    norm_num at h ⊢
    exact h
  have hdet_bounds : 1 / 2 ≤ |Matrix.det M| ∧ |Matrix.det M| ≤ 2 :=
    near_orthogonal_det_bound M h
  have hdet_ne_zero : Matrix.det M ≠ 0 := by
    have hpos : 0 < |Matrix.det M| := by linarith [hdet_bounds.1]
    exact abs_ne_zero.mp hpos.ne'
  have h_mul_id : M * M⁻¹ = 1 :=
    Matrix.mul_nonsing_inv M (IsUnit.mk0 (Matrix.det M) hdet_ne_zero)
  have h_main : ∀ (x : Point3), ‖f x‖ ≥ Real.sqrt (7 / 10) * ‖x‖ := by
    intro x
    let g := (matrixToLin B_mat).toContinuousLinearMap
    have h_eq1 : ‖f x‖ ^ 2 = ‖x‖ ^ 2 + inner ℝ x (g x) := by
      have h_adj : ∀ (y z : Point3),
          inner ℝ (f y) z = inner ℝ y (matrixToLin (M.transpose) z) := by
        intro y z
        have h_inner_sum : ∀ (a b : Point3),
            inner ℝ a b = ∑ i : Fin 3, a i * b i := by
          intro a b
          simp [inner, Fin.sum_univ_succ] <;> ring
        rw [h_inner_sum (f y) z,
          h_inner_sum y (matrixToLin (M.transpose) z)]
        have hL :
            ∑ i : Fin 3, (f y) i * z i =
              ∑ i : Fin 3, ∑ j : Fin 3, M i j * y j * z i := by
          have h1 : ∀ i : Fin 3,
              (f y) i * z i = ∑ j : Fin 3, M i j * y j * z i := by
            intro i
            have h2 : (f y) i = ∑ j : Fin 3, M i j * y j :=
              matrixToLin_apply M y i
            rw [h2]
            rw [Finset.sum_mul]
            <;> ring
          exact Finset.sum_congr rfl (fun i _ => h1 i)
        have hR :
            ∑ i : Fin 3, y i * (matrixToLin (M.transpose) z) i =
              ∑ i : Fin 3, ∑ j : Fin 3, M i j * y j * z i := by
          have h1 : ∀ i : Fin 3,
              y i * (matrixToLin (M.transpose) z) i =
                ∑ j : Fin 3, M j i * y i * z j := by
            intro i
            have h2 :
                (matrixToLin (M.transpose) z) i =
                  ∑ j : Fin 3, M j i * z j := by
              rw [matrixToLin_apply M.transpose z i]
              apply Finset.sum_congr rfl
              intro j _
              simp [Matrix.transpose_apply] <;> ring
            rw [h2]
            rw [Finset.mul_sum]
            <;> ring
          have h4 :
              ∑ i : Fin 3, y i * (matrixToLin (M.transpose) z) i =
                ∑ i : Fin 3, ∑ j : Fin 3, M j i * y i * z j :=
            Finset.sum_congr rfl (fun i _ => h1 i)
          rw [h4]
          have h5 :
              ∑ i : Fin 3, ∑ j : Fin 3, M j i * y i * z j =
                ∑ j : Fin 3, ∑ i : Fin 3, M i j * y j * z i := by
            rw [Finset.sum_comm] <;> rfl
          rw [h5, Finset.sum_comm]
        rw [hL, hR]
      have h1 : ‖f x‖ ^ 2 = inner ℝ (f x) (f x) := by
        rw [real_inner_self_eq_norm_sq] <;> ring
      rw [h1]
      have h2 :
          inner ℝ (f x) (f x) =
            inner ℝ x (matrixToLin (M.transpose) (f x)) :=
        h_adj x (f x)
      rw [h2]
      have h3 :
          matrixToLin (M.transpose) (f x) =
            matrixToLin (M.transpose * M) x := by
        simp [f, matrixToLin_mul, Matrix.mulVec] <;> rfl
      rw [h3]
      have h4 : matrixToLin (M.transpose * M) x = x + g x := by
        have h5 : M.transpose * M = 1 + B_mat := by
          ext i j
          simp [B_mat, Matrix.add_apply] <;> ring
        rw [h5]
        have h6 :
            matrixToLin (1 + B_mat) x =
              matrixToLin (1 : Matrix (Fin 3) (Fin 3) ℝ) x + g x := by
          rw [matrixToLin_add] <;> rfl
        rw [h6]
        have h7 : matrixToLin (1 : Matrix (Fin 3) (Fin 3) ℝ) x = x := by
          rw [matrixToLin_one] <;> rfl
        rw [h7] <;> abel
      rw [h4]
      have h6 :
          inner ℝ x (x + g x) = ‖x‖ ^ 2 + inner ℝ x (g x) := by
        rw [inner_add_right, real_inner_self_eq_norm_sq] <;> ring
      exact h6
    have h_bound :
        |inner ℝ x (g x)| ≤ (3 / 10 : ℝ) * ‖x‖ ^ 2 := by
      have h7 : |inner ℝ x (g x)| ≤ ‖x‖ * ‖g x‖ :=
        abs_real_inner_le_norm _ _
      have h8 : ‖g x‖ ≤ ‖g‖ * ‖x‖ := g.le_opNorm x
      calc
        |inner ℝ x (g x)| ≤ ‖x‖ * ‖g x‖ := h7
        _ ≤ ‖x‖ * (‖g‖ * ‖x‖) := by gcongr
        _ ≤ ‖x‖ * ((3 / 10 : ℝ) * ‖x‖) := by gcongr
        _ = (3 / 10 : ℝ) * ‖x‖ ^ 2 := by ring
    have h9 : ‖f x‖ ^ 2 ≥ (7 / 10 : ℝ) * ‖x‖ ^ 2 := by
      rw [h_eq1]
      have h10 :
          inner ℝ x (g x) ≥ -(3 / 10 : ℝ) * ‖x‖ ^ 2 := by
        have h11 :
            |inner ℝ x (g x)| ≤ (3 / 10 : ℝ) * ‖x‖ ^ 2 :=
          h_bound
        linarith [abs_le.mp h11]
      linarith
    have h10 : 0 ≤ ‖f x‖ := by positivity
    have h11 : 0 ≤ Real.sqrt (7 / 10) * ‖x‖ := by positivity
    have h12 :
        (Real.sqrt (7 / 10) * ‖x‖) ^ 2 =
          (7 / 10 : ℝ) * ‖x‖ ^ 2 := by
      have h13 : Real.sqrt (7 / 10) ^ 2 = 7 / 10 := by
        rw [Real.sq_sqrt] <;> norm_num
      nlinarith
    have h14 :
        ‖f x‖ ^ 2 ≥ (Real.sqrt (7 / 10) * ‖x‖) ^ 2 := by
      linarith [h9, h12]
    nlinarith [sq_nonneg (‖f x‖ - Real.sqrt (7 / 10) * ‖x‖)]
  have h_sqrt_ratio :
      Real.sqrt (10 / 7) = 1 / Real.sqrt (7 / 10) := by
    have h1 : 0 < Real.sqrt (7 / 10) := by positivity
    have h2 : Real.sqrt (10 / 7) * Real.sqrt (7 / 10) = 1 := by
      have h3 :
          Real.sqrt (10 / 7) * Real.sqrt (7 / 10) =
            Real.sqrt ((10 / 7) * (7 / 10)) := by
        rw [← Real.sqrt_mul] <;> norm_num
      rw [h3]
      have h4 : (10 / 7 : ℝ) * (7 / 10) = 1 := by norm_num
      rw [h4, Real.sqrt_one]
    exact (eq_div_iff h1.ne').mpr h2
  have h_inv :
      ∀ (y : Point3), ‖f_inv y‖ ≤ Real.sqrt (10 / 7) * ‖y‖ := by
    intro y
    let x := f_inv y
    have h14 : f x = y := by
      have h15 :
          f (f_inv y) = (matrixToLin (M * M⁻¹)) y := by
        have h : (matrixToLin (M * M⁻¹)) y = f (f_inv y) := by
          rw [matrixToLin_mul] <;> rfl
        exact h.symm
      rw [h15, h_mul_id]
      rw [matrixToLin_one] <;> rfl
    have h16 : ‖y‖ ≥ Real.sqrt (7 / 10) * ‖x‖ := by
      have h17 : ‖f x‖ ≥ Real.sqrt (7 / 10) * ‖x‖ := h_main x
      rw [h14] at h17
      exact h17
    have h18 : 0 < Real.sqrt (7 / 10) := by positivity
    have h19 : ‖x‖ * Real.sqrt (7 / 10) ≤ ‖y‖ := by
      linarith [h16]
    have h20 : ‖x‖ ≤ ‖y‖ / Real.sqrt (7 / 10) := by
      have h201 :
          (‖x‖ * Real.sqrt (7 / 10)) / Real.sqrt (7 / 10) = ‖x‖ := by
        field_simp [h18.ne'] <;> ring
      have h202 :
          (‖x‖ * Real.sqrt (7 / 10)) / Real.sqrt (7 / 10) ≤
            ‖y‖ / Real.sqrt (7 / 10) := by
        gcongr
      rw [h201] at h202
      exact h202
    have h21 :
        ‖y‖ / Real.sqrt (7 / 10) = Real.sqrt (10 / 7) * ‖y‖ := by
      rw [h_sqrt_ratio] <;> ring
    linarith [h20, h21]
  have h20 : Real.sqrt (10 / 7) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)] <;> norm_num
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun y => by
    calc
      ‖f_inv y‖ ≤ Real.sqrt (10 / 7) * ‖y‖ := h_inv y
      _ ≤ 2 * ‖y‖ := by gcongr)

/-- Matrix of a linear isometry is orthogonal and recovers the linear map. -/
lemma isometry_matrix_orthogonal (e : Point3 ≃ₗᵢ[ℝ] Point3) :
    let R : Matrix (Fin 3) (Fin 3) ℝ :=
      fun i j => e (EuclideanSpace.single j (1 : ℝ)) i
    R.transpose * R = 1 ∧
    (matrixToLin R : Point3 →ₗ[ℝ] Point3) =
      (e : Point3 →ₗ[ℝ] Point3) := by
  let R : Matrix (Fin 3) (Fin 3) ℝ :=
    fun i j => e (EuclideanSpace.single j (1 : ℝ)) i
  let eqv : Point3 ≃ₗ[ℝ] (Fin 3 → ℝ) :=
    EuclideanSpace.equiv (Fin 3) ℝ
  let e' : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
    eqv.toLinearMap.comp (e.toLinearMap.comp eqv.symm.toLinearMap)
  have hR : R = LinearMap.toMatrix' e' := by
    ext i j
    simp [R, e', LinearMap.toMatrix'_apply] <;> rfl
  have h1 :
      (matrixToLin R : Point3 →ₗ[ℝ] Point3) =
        (e : Point3 →ₗ[ℝ] Point3) := by
    ext x
    have h2 : Matrix.toLin' R = e' := by
      rw [hR]
      exact Matrix.toLin'_toMatrix' e'
    have h3 :
        matrixToLin R x = eqv.symm (Matrix.toLin' R (eqv x)) := by
      rfl
    rw [h3, h2]
    simp [e', LinearEquiv.apply_symm_apply] <;> rfl
  have h2 : R.transpose * R = 1 := by
    ext i j
    have h3 :
        (R.transpose * R) i j =
          inner ℝ (e (EuclideanSpace.single i (1 : ℝ)))
            (e (EuclideanSpace.single j (1 : ℝ))) := by
      simp [Matrix.mul_apply, Matrix.transpose_apply, inner,
        Fin.sum_univ_succ] <;> ring
    rw [h3]
    have h4 :
        inner ℝ (e (EuclideanSpace.single i (1 : ℝ)))
            (e (EuclideanSpace.single j (1 : ℝ))) =
          inner ℝ (EuclideanSpace.single i (1 : ℝ))
            (EuclideanSpace.single j (1 : ℝ)) :=
      LinearIsometryEquiv.inner_map_map e
        (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single j (1 : ℝ))
    rw [h4]
    have h5 :
        inner ℝ (EuclideanSpace.single i (1 : ℝ))
            (EuclideanSpace.single j (1 : ℝ)) =
          (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
      simp [EuclideanSpace.inner_single_left, Matrix.one_apply] <;>
        split_ifs <;> norm_num
    exact h5
  exact ⟨h2, h1⟩

/-! ### Helper lemmas for ENNReal density inequality -/

/-- ENNReal density inequality: a/b ≤ L*(c/d) from a≤c and d≤L*b. -/
lemma ennreal_density_ineq (a b c d L : ENNReal)
    (hL_one : 1 ≤ L) (hL_ne_top : L ≠ ⊤)
    (ha : a ≤ c) (hbd : d ≤ L * b)
    (hb_pos : 0 < b) (hd_pos : 0 < d)
    (hb_ne_top : b ≠ ⊤) (hd_ne_top : d ≠ ⊤) :
    a / b ≤ L * (c / d) := by
  have hL_pos : 0 < L := lt_of_lt_of_le (by norm_num) hL_one
  have hL_ne_zero : L ≠ 0 := hL_pos.ne'
  have h1 : a * b⁻¹ ≤ c * b⁻¹ :=
    mul_le_mul_of_nonneg_right ha (by positivity)
  have h2 : (L * b)⁻¹ = L⁻¹ * b⁻¹ := by
    rw [ENNReal.mul_inv] <;> simp [hL_ne_zero, hL_ne_top, hb_pos.ne', hb_ne_top] <;> tauto
  have h3 : (L * b)⁻¹ ≤ d⁻¹ := ENNReal.inv_le_inv' hbd
  have h4 : L⁻¹ * b⁻¹ ≤ d⁻¹ := by
    rw [h2] at h3; exact h3
  have h5 : L * L⁻¹ = 1 := ENNReal.mul_inv_cancel hL_ne_zero hL_ne_top
  have h6 : c * b⁻¹ ≤ L * (c * d⁻¹) := by
    have h7 : c * b⁻¹ = (L * L⁻¹) * (c * b⁻¹) := by
      rw [h5] <;> simp
    rw [h7]
    have h8 : (L * L⁻¹) * (c * b⁻¹) = L * c * (L⁻¹ * b⁻¹) := by
      simp [mul_assoc, mul_comm, mul_left_comm]
    rw [h8]
    have h9 : L * c * (L⁻¹ * b⁻¹) ≤ L * c * d⁻¹ := by
      gcongr
      <;> exact h4
    simpa [mul_assoc] using h9
  exact le_trans h1 h6

/-- A δ-tube contains a closed ball of radius δ around its base. -/
lemma tube_contains_ball {δ : ℝ} (hδ : 0 < δ) (T : Kakeya.DeltaTube δ) :
    Metric.closedBall T.base δ ⊆ T.carrier := by
  intro x hx
  have h_dist : dist x T.base ≤ δ := by
    simpa [Metric.mem_closedBall] using hx
  have h_base_in : T.base ∈ unitSegment T.base T.direction := by
    have h : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    exact ⟨0, h, by simp⟩
  exact Metric.mem_cthickening_of_dist_le x T.base δ (unitSegment T.base T.direction) h_base_in h_dist

/-- Volume of a δ-tube is at least the volume of a δ-ball. -/
lemma tube_volume_lower_bound {δ : ℝ} (hδ : 0 < δ) (T : Kakeya.DeltaTube δ) :
    T.volume ≥ volume (Metric.closedBall (0 : Point3) δ) := by
  have h1 : Metric.closedBall T.base δ ⊆ T.carrier := tube_contains_ball hδ T
  have h2 : volume (Metric.closedBall T.base δ) ≤ T.volume := measure_mono h1
  have h3 : volume (Metric.closedBall T.base δ) = volume (Metric.closedBall (0 : Point3) δ) := by
    have h4 : Metric.closedBall T.base δ = T.base +ᵥ Metric.closedBall (0 : Point3) δ := by
      ext x
      simp [Metric.mem_closedBall, dist_eq_norm]
      <;> abel
    rw [h4]
    have h5 : T.base +ᵥ Metric.closedBall (0 : Point3) δ =
        (fun h : Point3 => -T.base + h) ⁻¹' (Metric.closedBall (0 : Point3) δ) := by
      ext y
      simp [Metric.mem_closedBall, dist_eq_norm]
      <;> abel
    rw [h5]
    exact MeasureTheory.measure_preimage_add volume (-T.base) (Metric.closedBall (0 : Point3) δ)
  rw [h3] at h2; exact h2

/-- Volume ratio: vol(B20) = 64000 * vol(B1/2). -/
lemma ball20_ball_half_ratio :
    volume (Metric.closedBall (0 : Point3) 20) =
    64000 * volume (Metric.closedBall (0 : Point3) (1 / 2)) := by
  rw [EuclideanSpace.volume_closedBall_fin_three, EuclideanSpace.volume_closedBall_fin_three]
  let C : ENNReal := ENNReal.ofReal (Real.pi * 4 / 3)
  have h9 : (ENNReal.ofReal (20 : ℝ)) ^ 3 = (8000 : ENNReal) := by norm_cast <;> norm_num
  have h10 : (ENNReal.ofReal ((1 / 2 : ℝ))) ^ 3 = (8 : ENNReal)⁻¹ := by
    have h11 : (ENNReal.ofReal ((1 / 2 : ℝ))) = (2 : ENNReal)⁻¹ := by norm_cast <;> simp
    rw [h11]
    have h12 : (2 : ENNReal)⁻¹ ^ 3 = (8 : ENNReal)⁻¹ := by
      have h13 : (2 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ = (4 : ENNReal)⁻¹ := by
        rw [← ENNReal.mul_inv] <;> norm_num <;> tauto
      have h14 : (2 : ENNReal)⁻¹ ^ 3 = (2 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ := by
        simp [pow_succ] <;> simp [mul_assoc]
      rw [h14, h13]; rw [← ENNReal.mul_inv] <;> norm_num <;> tauto
    exact h12
  have h15 : (64000 : ENNReal) * (8 : ENNReal)⁻¹ = (8000 : ENNReal) := by
    have h16 : (8 : ENNReal) ≠ 0 := by norm_num
    have h17 : (8 : ENNReal) ≠ ⊤ := by norm_num
    have h18 : (64000 : ENNReal) = (8000 : ENNReal) * (8 : ENNReal) := by norm_cast <;> norm_num
    rw [h18, mul_assoc, ENNReal.mul_inv_cancel h16 h17] <;> simp
  rw [h9, h10]
  have h19 : (8000 : ENNReal) * C = (64000 : ENNReal) * ((8 : ENNReal)⁻¹ * C) := by
    have h20 : (64000 : ENNReal) * ((8 : ENNReal)⁻¹ * C) = ((64000 : ENNReal) * (8 : ENNReal)⁻¹) * C := by rw [mul_assoc]
    rw [h20, h15] <;> simp [mul_assoc]
  exact h19



/-- A test parallelepiped is closed: it is the intersection of a translated
    linear image of a closed axis box with a closed ball. -/
lemma testParallelepiped_isClosed (c : Point3) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (a b c_dim : ℝ) : IsClosed (testParallelepiped c M a b c_dim) := by
  let f : Point3 → Point3 := fun x => matrixToLin M x
  have hf : Continuous f :=
    (matrixToLin M).toContinuousLinearMap.continuous
  have h_axisBox_closed : IsClosed (axisBox a b c_dim) := by
    have h1 : IsClosed {x : Point3 | |x 0| ≤ a / 2} :=
      isClosed_le (PiLp.continuous_apply 2 (fun _ => ℝ) 0).abs continuous_const
    have h2 : IsClosed {x : Point3 | |x 1| ≤ b / 2} :=
      isClosed_le (PiLp.continuous_apply 2 (fun _ => ℝ) 1).abs continuous_const
    have h3 : IsClosed {x : Point3 | |x 2| ≤ c_dim / 2} :=
      isClosed_le (PiLp.continuous_apply 2 (fun _ => ℝ) 2).abs continuous_const
    have h_eq : axisBox a b c_dim =
        {x : Point3 | |x 0| ≤ a / 2} ∩
        ({x : Point3 | |x 1| ≤ b / 2} ∩ {x : Point3 | |x 2| ≤ c_dim / 2}) := by
      ext x; simp [axisBox]
    rw [h_eq]
    exact h1.inter (h2.inter h3)
  have h_axisBox_bounded : Bornology.IsBounded (axisBox a b c_dim) := by
    have h_sub : axisBox a b c_dim ⊆
        Metric.closedBall (0 : Point3) (|a / 2| + |b / 2| + |c_dim / 2|) := by
      intro x hx
      have h0 : |x 0| ≤ a / 2 := hx.1
      have h1 : |x 1| ≤ b / 2 := hx.2.1
      have h2 : |x 2| ≤ c_dim / 2 := hx.2.2
      have ha_nonneg : 0 ≤ a / 2 := by linarith [abs_nonneg (x 0)]
      have hb_nonneg : 0 ≤ b / 2 := by linarith [abs_nonneg (x 1)]
      have hc_nonneg : 0 ≤ c_dim / 2 := by linarith [abs_nonneg (x 2)]
      have h0' : |x 0| ≤ |a / 2| := by
        rw [abs_of_nonneg ha_nonneg] <;> exact h0
      have h1' : |x 1| ≤ |b / 2| := by
        rw [abs_of_nonneg hb_nonneg] <;> exact h1
      have h2' : |x 2| ≤ |c_dim / 2| := by
        rw [abs_of_nonneg hc_nonneg] <;> exact h2
      have h3 : ‖x‖ ≤ |x 0| + |x 1| + |x 2| := by
        have h_sum_nonneg : 0 ≤ ∑ i : Fin 3, (x i) ^ 2 := by positivity
        have h4 : ‖x‖ ^ 2 = ∑ i : Fin 3, (x i) ^ 2 := by
          have h41 : ‖x‖ = Real.sqrt (∑ i : Fin 3, (x i) ^ 2) := by
            simpa [EuclideanSpace.norm_eq] using rfl
          rw [h41]
          rw [Real.sq_sqrt h_sum_nonneg]
        have h5 : ‖x‖ ^ 2 ≤ (|x 0| + |x 1| + |x 2|) ^ 2 := by
          rw [h4]
          have h_sum3 : ∑ i : Fin 3, (x i) ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
            simp [Fin.sum_univ_succ] <;> ring
          rw [h_sum3]
          have h_abs0 : |x 0| ^ 2 = (x 0) ^ 2 := by rw [sq_abs]
          have h_abs1 : |x 1| ^ 2 = (x 1) ^ 2 := by rw [sq_abs]
          have h_abs2 : |x 2| ^ 2 = (x 2) ^ 2 := by rw [sq_abs]
          have h6 : 0 ≤ 2 * (|x 0| * |x 1| + |x 0| * |x 2| + |x 1| * |x 2|) := by positivity
          have h7 : (|x 0| + |x 1| + |x 2|) ^ 2 =
              |x 0| ^ 2 + |x 1| ^ 2 + |x 2| ^ 2 +
              2 * (|x 0| * |x 1| + |x 0| * |x 2| + |x 1| * |x 2|) := by ring
          rw [h7, h_abs0, h_abs1, h_abs2]
          linarith
        have h9 : 0 ≤ ‖x‖ := by positivity
        have h10 : 0 ≤ |x 0| + |x 1| + |x 2| := by positivity
        nlinarith
      have h4 : |x 0| + |x 1| + |x 2| ≤ |a / 2| + |b / 2| + |c_dim / 2| := by
        linarith
      have h5 : ‖x‖ ≤ |a / 2| + |b / 2| + |c_dim / 2| := by
        calc ‖x‖ ≤ |x 0| + |x 1| + |x 2| := h3
             _ ≤ |a / 2| + |b / 2| + |c_dim / 2| := h4
      simpa [Metric.mem_closedBall] using h5
    exact Metric.isBounded_closedBall.subset h_sub
  have h_axisBox_compact : IsCompact (axisBox a b c_dim) :=
    Metric.isCompact_of_isClosed_isBounded h_axisBox_closed h_axisBox_bounded
  set S : Set Point3 := f '' axisBox a b c_dim with hS_def
  have hS_closed : IsClosed S := (h_axisBox_compact.image hf).isClosed
  have h_vadd_closed : IsClosed (c +ᵥ S) := hS_closed.vadd c
  have h_main : IsClosed ((c +ᵥ S) ∩ Metric.closedBall (0 : Point3) 20) :=
    h_vadd_closed.inter Metric.isClosed_closedBall
  have h_goal : (c +ᵥ S) ∩ Metric.closedBall (0 : Point3) 20 = testParallelepiped c M a b c_dim := by
    simp [testParallelepiped, hS_def]
    <;> rfl
  rw [←h_goal]
  exact h_main

end Kakeya.Streamlined
