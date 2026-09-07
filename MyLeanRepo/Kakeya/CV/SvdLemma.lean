import MyLeanRepo.Kakeya.CV.Geometry
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.UnitaryGroup

open scoped MatrixOrder

namespace Kakeya.CV

/-- **Polar decomposition of an invertible real matrix**.

Every invertible real matrix `M` can be written as `M = R * P`, where `R` is
orthogonal and `P` is symmetric positive definite. -/
theorem polar_decomposition_matrix {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : IsUnit M) :
    ∃ (R : Matrix n n ℝ) (P : Matrix n n ℝ),
      R ∈ Matrix.orthogonalGroup n ℝ ∧
      P.PosDef ∧
      M = R * P := by
  let Q := M.transpose * M
  have hQ_psd : Q.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  have hMtrans_unit : IsUnit M.transpose := (Matrix.isUnit_transpose M).mpr hM
  have hQ_unit : IsUnit Q := hMtrans_unit.mul hM
  have hQ_pd : Q.PosDef := hQ_psd.posDef_iff_isUnit.mpr hQ_unit
  let P : Matrix n n ℝ := CFC.sqrt Q
  have hP2 : P * P = Q := by
    have h : (CFC.sqrt Q) ^ 2 = Q := CFC.sq_sqrt Q
    simpa [pow_two] using h
  have hP_unit : IsUnit P := by
    have h1 : IsUnit (P * P) := by rw [hP2]; exact hQ_unit
    exact (IsUnit.mul_iff.mp h1).1
  have hP_psd : P.PosSemidef := by
    have h_nonneg : 0 ≤ P := CFC.sqrt_nonneg Q
    exact Matrix.LE.le.posSemidef h_nonneg
  have hP_pd : P.PosDef := hP_psd.posDef_iff_isUnit.mpr hP_unit
  have hP_symm : P.transpose = P := hP_pd.isHermitian.eq
  have hdetP : IsUnit P.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hP_unit
  let R : Matrix n n ℝ := M * P⁻¹
  have hPinj_transpose : (P⁻¹).transpose = P⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hP_symm]
  have hR_orth : R.transpose * R = 1 := by
    calc
      R.transpose * R
        = (P⁻¹).transpose * M.transpose * M * P⁻¹ := by
          simp [R, Matrix.transpose_mul, mul_assoc]
      _ = P⁻¹ * Q * P⁻¹ := by
          rw [hPinj_transpose]
          simp [mul_assoc, Q]
      _ = P⁻¹ * (P * P) * P⁻¹ := by rw [hP2]
      _ = (P⁻¹ * P) * (P * P⁻¹) := by simp [mul_assoc]
      _ = 1 * 1 := by
          rw [Matrix.nonsing_inv_mul P hdetP, Matrix.mul_nonsing_inv P hdetP]
      _ = 1 := by simp
  have hR_mem_orth : R ∈ Matrix.orthogonalGroup n ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff']
    exact hR_orth
  have hM_eq : M = R * P := by
    have h : R * P = M := by
      dsimp only [R]
      rw [mul_assoc, Matrix.nonsing_inv_mul P hdetP, Matrix.mul_one]
    exact h.symm
  exact ⟨R, P, hR_mem_orth, hP_pd, hM_eq⟩

/-- **Singular value decomposition** of an invertible real matrix.

Every invertible real matrix `M` can be written as `M = U * D * V.transpose`,
where `U, V` are orthogonal and `D` is diagonal with positive entries. -/
theorem singular_value_decomposition {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : IsUnit M) :
    ∃ (U V : Matrix n n ℝ) (σ : n → ℝ),
      U ∈ Matrix.orthogonalGroup n ℝ ∧
      V ∈ Matrix.orthogonalGroup n ℝ ∧
      (∀ i, 0 < σ i) ∧
      M = U * Matrix.diagonal σ * V.transpose := by
  rcases polar_decomposition_matrix M hM with ⟨R, P, hR_orth, hP_pd, hM_eq⟩
  let hP_herm : P.IsHermitian := hP_pd.isHermitian
  let Vmat : Matrix n n ℝ := hP_herm.eigenvectorUnitary
  let σ : n → ℝ := hP_herm.eigenvalues
  have hσ_nonneg : ∀ i, 0 ≤ σ i := hP_pd.posSemidef.eigenvalues_nonneg
  have hdetP : P.det ≠ 0 := by
    have hP_unit : IsUnit P := hP_pd.isUnit
    have hdet_unit : IsUnit P.det := by
      rwa [Matrix.isUnit_iff_isUnit_det] at hP_unit
    exact IsUnit.ne_zero hdet_unit
  have hdet_prod : P.det = ∏ i, σ i := hP_herm.det_eq_prod_eigenvalues
  have hσ_pos : ∀ i, 0 < σ i := by
    intro i
    have h1 : 0 ≤ σ i := hσ_nonneg i
    by_contra h2
    have h3 : σ i = 0 := by linarith
    have h4 : (∏ j, σ j) = 0 := by
      rw [Finset.prod_eq_zero (Finset.mem_univ i)]
      exact h3
    rw [hdet_prod] at hdetP
    contradiction
  have hV_unitary : Vmat ∈ Matrix.unitaryGroup n ℝ :=
    hP_herm.eigenvectorUnitary.prop
  have hV_orth : Vmat ∈ Matrix.orthogonalGroup n ℝ := by
    simpa [Matrix.mem_orthogonalGroup_iff', Matrix.mem_unitaryGroup_iff'] using hV_unitary
  have h_spectral : P = Vmat * Matrix.diagonal σ * Vmat.transpose := by
    have h1 : P = Vmat * Matrix.diagonal σ * (star hP_herm.eigenvectorUnitary : Matrix n n ℝ) :=
      hP_herm.spectral_theorem
    have h2 : (star hP_herm.eigenvectorUnitary : Matrix n n ℝ) = Vmat.transpose := by
      ext i j
      simp [Vmat]
    rw [h2] at h1
    exact h1
  let U : Matrix n n ℝ := R * Vmat
  have hR_transpose_mul : R.transpose * R = 1 :=
    (Matrix.mem_orthogonalGroup_iff' n ℝ).mp hR_orth
  have hV_transpose_mul : Vmat.transpose * Vmat = 1 :=
    (Matrix.mem_orthogonalGroup_iff' n ℝ).mp hV_orth
  have hU_orth : U ∈ Matrix.orthogonalGroup n ℝ := by
    have h1 : U.transpose * U = 1 := by
      calc
        U.transpose * U
          = (R * Vmat).transpose * (R * Vmat) := by rfl
        _ = Vmat.transpose * (R.transpose * R) * Vmat := by
            simp [Matrix.transpose_mul, mul_assoc]
        _ = Vmat.transpose * 1 * Vmat := by rw [hR_transpose_mul]
        _ = Vmat.transpose * Vmat := by simp
        _ = 1 := hV_transpose_mul
    rw [Matrix.mem_orthogonalGroup_iff']
    exact h1
  have hM_svd : M = U * Matrix.diagonal σ * Vmat.transpose := by
    calc
      M = R * P := hM_eq
      _ = R * (Vmat * Matrix.diagonal σ * Vmat.transpose) := by rw [h_spectral]
      _ = (R * Vmat) * Matrix.diagonal σ * Vmat.transpose := by simp [mul_assoc]
      _ = U * Matrix.diagonal σ * Vmat.transpose := by rfl
  exact ⟨U, Vmat, σ, hU_orth, hV_orth, hσ_pos, hM_svd⟩

end Kakeya.CV
