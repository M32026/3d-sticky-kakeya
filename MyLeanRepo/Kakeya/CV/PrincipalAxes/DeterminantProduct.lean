import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.RotationTransfer
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Determinant product for principal-axis transformations

Proves `|det A| = ∏ ℓ_i` when `A e_i = ℓ_i • b_i`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators RealInnerProductSpace

namespace Kakeya.CV

private abbrev eStd : OrthonormalBasis (Fin 3) ℝ (Point 3) :=
  EuclideanSpace.basisFun (Fin 3) ℝ

private lemma eStd_eq_eBasis (j : Fin 3) : eStd j = eBasis j := by
  ext m
  simp [eStd, eBasis, EuclideanSpace.basisFun_apply,
    EuclideanSpace.single]

/-- The absolute determinant of a principal-axis map is the product of its
positive semiaxes. -/
lemma abs_det_eq_product
    (A : Point 3 ≃ₗ[ℝ] Point 3)
    (b : OrthonormalBasis (Fin 3) ℝ (Point 3))
    (ℓ : Fin 3 → ℝ)
    (hℓ : ∀ i, 0 < ℓ i)
    (hA : ∀ i, A (eBasis i) = ℓ i • b i) :
    |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| =
      ∏ i : Fin 3, ℓ i := by
  let eb := eStd.toBasis
  let A' : Point 3 →ₗ[ℝ] Point 3 := A
  let P_change : Point 3 →ₗ[ℝ] Point 3 :=
    eb.constr ℝ b
  let D_diag : Point 3 →ₗ[ℝ] Point 3 :=
    eb.constr ℝ (fun j => ℓ j • eb j)
  have h_ej : ∀ j, eb j = eBasis j :=
    fun j => eStd_eq_eBasis j
  have hA_eq : A' = P_change.comp D_diag := by
    apply eb.ext
    intro j
    have hD : D_diag (eb j) = ℓ j • eb j :=
      eb.constr_basis ℝ (fun k => ℓ k • eb k) j
    have hP2 : P_change (eb j) = b j :=
      eb.constr_basis ℝ b j
    have hP :
        (P_change.comp D_diag) (eb j) = ℓ j • b j := by
      rw [LinearMap.comp_apply, hD, map_smul, hP2]
    have hA' : A' (eb j) = ℓ j • b j := by
      rw [h_ej j]
      exact hA j
    rw [hA', hP]
  have hdet_P : |LinearMap.det P_change| = 1 := by
    have h_mat :
        LinearMap.toMatrix eb eb P_change = eb.toMatrix b := by
      ext i j
      have hP : P_change (eb j) = b j :=
        eb.constr_basis ℝ b j
      have h :
          (eb.repr (P_change (eb j))) i =
            (eb.repr (b j)) i := by
        rw [hP]
      simpa [LinearMap.toMatrix_apply,
        Module.Basis.toMatrix_apply] using h
    have h_det :
        LinearMap.det P_change =
          (LinearMap.toMatrix eb eb P_change).det :=
      (LinearMap.det_toMatrix eb P_change).symm
    have h2 :
        LinearMap.det P_change = (eb.toMatrix b).det := by
      rw [h_det, h_mat]
    rw [h2]
    have h3 :
        (eb.toMatrix b).det = 1 ∨
          (eb.toMatrix b).det = -1 := by
      have h4 :=
        OrthonormalBasis.det_to_matrix_orthonormalBasis_real
          eStd b
      simpa [Module.Basis.det_apply] using h4
    rcases h3 with (h3 | h3) <;> rw [h3] <;> norm_num
  let M3 : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.diagonal ℓ
  have hD_eq : D_diag = Matrix.toLin eb eb M3 := by
    apply eb.ext
    intro j
    have h1 : D_diag (eb j) = ℓ j • eb j :=
      eb.constr_basis ℝ (fun k => ℓ k • eb k) j
    have h2 :
        (Matrix.toLin eb eb M3) (eb j) = ℓ j • eb j := by
      rw [Matrix.toLin_self]
      simp [M3, Matrix.diagonal_apply, Finset.sum_ite_eq']
    exact h1.trans h2.symm
  have hdet_D : LinearMap.det D_diag = M3.det := by
    rw [hD_eq, LinearMap.det_toLin eb M3]
  have h4 : M3.det = ℓ 0 * ℓ 1 * ℓ 2 := by
    rw [Matrix.det_diagonal]
    simp [Fin.prod_univ_succ]
    ring
  have hprod :
      (∏ i : Fin 3, ℓ i) = ℓ 0 * ℓ 1 * ℓ 2 := by
    simp [Fin.prod_univ_succ]
    ring
  calc
    |LinearMap.det A'|
        = |LinearMap.det (P_change.comp D_diag)| := by
            rw [hA_eq]
    _ = |LinearMap.det P_change * LinearMap.det D_diag| := by
          rw [LinearMap.det_comp]
    _ = |LinearMap.det P_change| *
          |LinearMap.det D_diag| := by
          rw [abs_mul]
    _ = 1 * |M3.det| := by
          rw [hdet_P, hdet_D]
    _ = |ℓ 0 * ℓ 1 * ℓ 2| := by
          rw [h4]
          simp
    _ = ∏ i : Fin 3, ℓ i := by
          rw [hprod]
          have h_all_pos : 0 < ℓ 0 * ℓ 1 * ℓ 2 :=
            mul_pos (mul_pos (hℓ 0) (hℓ 1)) (hℓ 2)
          rw [abs_of_pos h_all_pos]

end Kakeya.CV
