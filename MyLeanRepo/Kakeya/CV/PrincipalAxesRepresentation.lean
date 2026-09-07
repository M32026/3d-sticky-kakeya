import MyLeanRepo.Kakeya.CV.SvdLemma
import MyLeanRepo.Kakeya.CV.Statements
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Principal-axis representation of centered ellipsoids

Uses singular-value decomposition to remove the right orthogonal factor from
an ellipsoid parameterization. The remaining map has positive semiaxes along
an orthonormal basis and the same centered carrier.
-/

open scoped MatrixOrder Pointwise

noncomputable section


namespace Kakeya.CV

private abbrev principalAxesStdBasis :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

private lemma orthogonalMatrix_columns_orthonormal
    (orthogonalMatrix : Matrix (Fin 3) (Fin 3) ℝ)
    (hOrthogonal : orthogonalMatrix ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    Orthonormal ℝ (fun i =>
      (Matrix.toLpLin 2 2) orthogonalMatrix
        ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hmul := congr_fun
    (congr_fun
      ((Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hOrthogonal) i) j
  simpa [Matrix.toLpLin_apply, PiLp.inner_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.one_apply, mul_comm] using hmul

private noncomputable def orthogonalMatrixLinearEquiv
    (orthogonalMatrix : Matrix (Fin 3) (Fin 3) ℝ)
    (hOrthogonal : orthogonalMatrix ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    Point 3 ≃ₗ[ℝ] Point 3 :=
  Matrix.toLinearEquiv principalAxesStdBasis orthogonalMatrix (by
    exact Matrix.UnitaryGroup.det_isUnit ⟨orthogonalMatrix, hOrthogonal⟩)

@[simp] private lemma orthogonalMatrixLinearEquiv_apply
    (orthogonalMatrix : Matrix (Fin 3) (Fin 3) ℝ)
    (hOrthogonal : orthogonalMatrix ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (x : Point 3) :
    orthogonalMatrixLinearEquiv orthogonalMatrix hOrthogonal x =
      (Matrix.toLpLin 2 2) orthogonalMatrix x := by
  rw [orthogonalMatrixLinearEquiv, Matrix.toLinearEquiv_apply,
    Matrix.toLpLin_eq_toLin]
  rfl

private noncomputable def orthogonalMatrixOrthonormalBasis
    (orthogonalMatrix : Matrix (Fin 3) (Fin 3) ℝ)
    (hOrthogonal : orthogonalMatrix ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    OrthonormalBasis (Fin 3) ℝ (Point 3) :=
  let linearEquiv := orthogonalMatrixLinearEquiv orthogonalMatrix hOrthogonal
  let basis := principalAxesStdBasis.map linearEquiv
  have hbasis : (basis : Fin 3 → Point 3) =
      fun i => (Matrix.toLpLin 2 2) orthogonalMatrix
        ((EuclideanSpace.basisFun (Fin 3) ℝ) i) := by
    funext i
    simp [basis, linearEquiv, principalAxesStdBasis,
      orthogonalMatrixLinearEquiv_apply]
  basis.toOrthonormalBasis (by
    rw [hbasis]
    exact orthogonalMatrix_columns_orthonormal orthogonalMatrix hOrthogonal)

@[simp] private lemma orthogonalMatrixOrthonormalBasis_apply
    (orthogonalMatrix : Matrix (Fin 3) (Fin 3) ℝ)
    (hOrthogonal : orthogonalMatrix ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (i : Fin 3) :
    orthogonalMatrixOrthonormalBasis orthogonalMatrix hOrthogonal i =
      (Matrix.toLpLin 2 2) orthogonalMatrix
        ((EuclideanSpace.basisFun (Fin 3) ℝ) i) := by
  simp [orthogonalMatrixOrthonormalBasis, principalAxesStdBasis,
    orthogonalMatrixLinearEquiv_apply]

private noncomputable def orthogonalMatrixLinearIsometryEquiv
    (orthogonalMatrix : Matrix (Fin 3) (Fin 3) ℝ)
    (hOrthogonal : orthogonalMatrix ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    Point 3 ≃ₗᵢ[ℝ] Point 3 :=
  (orthogonalMatrixOrthonormalBasis orthogonalMatrix hOrthogonal).repr.symm

@[simp] private lemma orthogonalMatrixLinearIsometryEquiv_apply
    (orthogonalMatrix : Matrix (Fin 3) (Fin 3) ℝ)
    (hOrthogonal : orthogonalMatrix ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (x : Point 3) :
    orthogonalMatrixLinearIsometryEquiv orthogonalMatrix hOrthogonal x =
      (Matrix.toLpLin 2 2) orthogonalMatrix x := by
  have hmaps :
      (orthogonalMatrixLinearIsometryEquiv orthogonalMatrix hOrthogonal).toLinearEquiv.toLinearMap =
        (Matrix.toLpLin 2 2) orthogonalMatrix := by
    apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
    intro i
    simp [orthogonalMatrixLinearIsometryEquiv,
      orthogonalMatrixOrthonormalBasis_apply]
  exact LinearMap.congr_fun hmaps x

private lemma matrixLinearEquiv_apply
    (matrix : Matrix (Fin 3) (Fin 3) ℝ) (hDet : IsUnit matrix.det)
    (x : Point 3) :
    Matrix.toLinearEquiv principalAxesStdBasis matrix hDet x =
      (Matrix.toLpLin 2 2) matrix x := by
  rw [Matrix.toLinearEquiv_apply, Matrix.toLpLin_eq_toLin]
  rfl

theorem principalAxes_representation :
    PrincipalAxesRepresentationStatement := by
  intro linearEquiv
  let standardBasis := EuclideanSpace.basisFun (Fin 3) ℝ
  let basis := standardBasis.toBasis
  let matrix : Matrix (Fin 3) (Fin 3) ℝ :=
    LinearMap.toMatrix basis basis linearEquiv
  have hMatrixUnit : IsUnit matrix := by
    rw [Matrix.isUnit_iff_isUnit_det, LinearMap.det_toMatrix]
    exact LinearEquiv.isUnit_det' linearEquiv
  rcases singular_value_decomposition matrix hMatrixUnit with
    ⟨leftOrthogonal, rightOrthogonal, semiaxis, hLeftOrthogonal,
      hRightOrthogonal, hSemiaxis, hMatrix⟩
  have hPrincipalDet :
      IsUnit (leftOrthogonal * Matrix.diagonal semiaxis).det := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    exact (Matrix.UnitaryGroup.det_isUnit
      ⟨leftOrthogonal, hLeftOrthogonal⟩).mul
      (isUnit_iff_ne_zero.mpr
        (Finset.prod_ne_zero_iff.mpr fun i _ => (hSemiaxis i).ne'))
  let principalMap : Point 3 ≃ₗ[ℝ] Point 3 :=
    Matrix.toLinearEquiv basis
      (leftOrthogonal * Matrix.diagonal semiaxis) hPrincipalDet
  let principalBasis : OrthonormalBasis (Fin 3) ℝ (Point 3) :=
    orthogonalMatrixOrthonormalBasis leftOrthogonal hLeftOrthogonal
  have hAxes : ∀ i,
      principalMap (standardBasis i) = semiaxis i • principalBasis i := by
    intro i
    dsimp only [principalMap]
    rw [matrixLinearEquiv_apply]
    calc
      (Matrix.toLpLin 2 2)
          (leftOrthogonal * Matrix.diagonal semiaxis) (standardBasis i)
          = (Matrix.toLpLin 2 2) leftOrthogonal
              ((Matrix.toLpLin 2 2) (Matrix.diagonal semiaxis)
                (standardBasis i)) := by
            exact LinearMap.congr_fun
              (Matrix.toLpLin_mul 2 2 2
                leftOrthogonal (Matrix.diagonal semiaxis))
              (standardBasis i)
      _ = (Matrix.toLpLin 2 2) leftOrthogonal
            (semiaxis i • standardBasis i) := by
            congr 1
            ext k
            simp [Matrix.toLpLin_apply, standardBasis]
      _ = semiaxis i •
            (Matrix.toLpLin 2 2) leftOrthogonal (standardBasis i) := by
            rw [map_smul]
      _ = semiaxis i • principalBasis i := by
            rw [orthogonalMatrixOrthonormalBasis_apply]
  have hRightTranspose :
      rightOrthogonal.transpose ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
    Matrix.transpose_mem_unitaryGroup_iff.mpr hRightOrthogonal
  let rightIsometry : Point 3 ≃ₗᵢ[ℝ] Point 3 :=
    orthogonalMatrixLinearIsometryEquiv
      rightOrthogonal.transpose hRightTranspose
  have hFactor : ∀ x, linearEquiv x = principalMap (rightIsometry x) := by
    intro x
    have hLinearMatrix :
        (Matrix.toLpLin 2 2) matrix =
          (linearEquiv : Point 3 →ₗ[ℝ] Point 3) := by
      rw [Matrix.toLpLin_eq_toLin]
      exact Matrix.toLin_toMatrix basis basis linearEquiv
    have hProduct :
        (Matrix.toLpLin 2 2) matrix =
          ((Matrix.toLpLin 2 2)
            (leftOrthogonal * Matrix.diagonal semiaxis)).comp
            ((Matrix.toLpLin 2 2) rightOrthogonal.transpose) := by
      rw [hMatrix]
      exact Matrix.toLpLin_mul 2 2 2
        (leftOrthogonal * Matrix.diagonal semiaxis)
        rightOrthogonal.transpose
    calc
      linearEquiv x = (Matrix.toLpLin 2 2) matrix x := by
        simpa using (LinearMap.congr_fun hLinearMatrix x).symm
      _ = (Matrix.toLpLin 2 2)
            (leftOrthogonal * Matrix.diagonal semiaxis)
            ((Matrix.toLpLin 2 2) rightOrthogonal.transpose x) := by
            exact LinearMap.congr_fun hProduct x
      _ = principalMap (rightIsometry x) := by
        rw [orthogonalMatrixLinearIsometryEquiv_apply]
        symm
        exact Matrix.toLinearEquiv_apply basis
          (leftOrthogonal * Matrix.diagonal semiaxis) hPrincipalDet _
  refine ⟨principalMap, principalBasis, semiaxis, hSemiaxis, hAxes, ?_⟩
  change (0 : Point 3) +ᵥ
      principalMap '' Metric.closedBall 0 1 =
    (0 : Point 3) +ᵥ linearEquiv '' Metric.closedBall 0 1
  congr 1
  rw [show linearEquiv '' Metric.closedBall (0 : Point 3) 1 =
      principalMap '' (rightIsometry '' Metric.closedBall (0 : Point 3) 1) by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨rightIsometry x, ⟨x, hx, rfl⟩, (hFactor x).symm⟩
        · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨x, hx, hFactor x⟩]
  rw [rightIsometry.image_closedBall]
  simp

end Kakeya.CV
