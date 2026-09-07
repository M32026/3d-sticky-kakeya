import MyLeanRepo.Kakeya.CV.PrincipalAxes.DiagonalTransformedGraphProjection
import MyLeanRepo.Kakeya.CV.PrincipalAxes.DeterminantProduct
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.RotationTransfer

/-!
# Measurable affine graph patch identity

The direction-two affine surface-area identity on a measurable graph-base
subset. The geometric graph transformation and projection formulas are supplied
by `diagonal_transformed_graph_projection`; this module performs only the
orthonormal rotation and coefficient algebra.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

/-- Direction-two measurable affine patch identity. -/
lemma affine_patch_identity_dir2_meas
    (p q : MvPolynomial (Fin 3) ℝ)
    (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (z : Point 3) (hη : 0 < η)
    (b : OrthonormalBasis (Fin 3) ℝ (Point 3))
    (ℓ : Fin 3 → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (hA : ∀ i, A (eBasis i) = ℓ i • b i)
    (hpq : ∀ x, polynomialValue p (z + η • A x) = polynomialValue q x)
    {U : Set R2} {g : R2 → ℝ} {B : Set R2}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U)
    (hB : MeasurableSet B) (hB_sub : B ⊆ U)
    (h_zero : ∀ u ∈ U, polynomialValue q (graphMap g u) = 0)
    (h_reg : ∀ u ∈ U, (polynomialGradient q (graphMap g u)) 2 ≠ 0) :
    ENNReal.ofReal (ℓ 2) *
      directionalSurfaceArea (b 2) p
        ((fun y => z + η • A y) '' (graphMap g '' B)) =
    ENNReal.ofReal
        (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
      directionalSurfaceArea (eBasis 2) q (graphMap g '' B) := by
  let f : Point 3 → Point 3 := fun y => z + η • A y
  let stdBasis := EuclideanSpace.basisFun (Fin 3) ℝ
  let R : Point 3 ≃ₗᵢ[ℝ] Point 3 :=
    b.equiv stdBasis (Equiv.refl (Fin 3))
  let p' : MvPolynomial (Fin 3) ℝ := rotatedPoly p R
  have hR_bi : ∀ i, R (b i) = eBasis i := by
    intro i
    have h1 : R (b i) = stdBasis i :=
      OrthonormalBasis.equiv_apply_basis b stdBasis (Equiv.refl (Fin 3)) i
    have h2 : stdBasis i = eBasis i := by
      rw [EuclideanSpace.basisFun_apply]
      rfl
    exact Eq.trans h1 h2
  let D : Point 3 ≃ₗ[ℝ] Point 3 :=
    { toFun := fun x => R (A x)
      invFun := fun y => A.symm (R.symm y)
      left_inv := by
        intro x
        simp
      right_inv := by
        intro y
        simp
      map_add' := by
        intro x y
        simp [map_add]
      map_smul' := by
        intro r x
        simp [map_smul] }
  have hD0 : D (eBasis 0) = ℓ 0 • eBasis 0 := by
    have h : D (eBasis 0) = R (A (eBasis 0)) := by rfl
    rw [h, hA 0, map_smul, hR_bi 0]
  have hD1 : D (eBasis 1) = ℓ 1 • eBasis 1 := by
    have h : D (eBasis 1) = R (A (eBasis 1)) := by rfl
    rw [h, hA 1, map_smul, hR_bi 1]
  have hD2 : D (eBasis 2) = ℓ 2 • eBasis 2 := by
    have h : D (eBasis 2) = R (A (eBasis 2)) := by rfl
    rw [h, hA 2, map_smul, hR_bi 2]
  let d0 := η * ℓ 0
  let d1 := η * ℓ 1
  let d2 := η * ℓ 2
  have hd0 : 0 < d0 := mul_pos hη (hℓ 0)
  have hd1 : 0 < d1 := mul_pos hη (hℓ 1)
  have hd2 : 0 < d2 := mul_pos hη (hℓ 2)
  let D' : Point 3 ≃ₗ[ℝ] Point 3 :=
    { toFun := fun x => η • D x
      invFun := fun x => η⁻¹ • D.symm x
      left_inv := by
        intro x
        simp [smul_smul, hη.ne']
      right_inv := by
        intro x
        simp [smul_smul, hη.ne']
      map_add' := by
        intro x y
        simp [map_add, smul_add]
      map_smul' := by
        intro r x
        simp [map_smul, smul_smul]
        ring_nf }
  have hD'0 : D' (eBasis 0) = d0 • eBasis 0 := by
    have h : D' (eBasis 0) = η • D (eBasis 0) := by rfl
    rw [h, hD0, smul_smul]
  have hD'1 : D' (eBasis 1) = d1 • eBasis 1 := by
    have h : D' (eBasis 1) = η • D (eBasis 1) := by rfl
    rw [h, hD1, smul_smul]
  have hD'2 : D' (eBasis 2) = d2 • eBasis 2 := by
    have h : D' (eBasis 2) = η • D (eBasis 2) := by rfl
    rw [h, hD2, smul_smul]
  let c : Point 3 := R z
  let F : Point 3 → Point 3 := fun y => c + D' y
  have hF_eq : ∀ x, F x = R (f x) := by
    intro x
    have h1 : F x = R z + D' x := by
      simp [F, c]
    rw [h1]
    have h2 : D' x = η • D x := by rfl
    rw [h2]
    have h3 : R z + η • D x = R (z + η • A x) := by
      have h4 : D x = R (A x) := by rfl
      rw [h4, map_add, map_smul]
    rw [h3]
  have hpq' : ∀ x, polynomialValue p' (c + D' x) =
      polynomialValue q x := by
    intro x
    have h1 : c + D' x = R (f x) := by
      have h2 : c + D' x = F x := by simp [F]
      rw [h2, hF_eq]
    rw [h1]
    have h3 : polynomialValue p' (R (f x)) =
        polynomialValue p (f x) :=
      rotatedPoly_eval p R (f x)
    rw [h3, hpq x]
  have h_leaf := diagonal_transformed_graph_projection
    p' q D' d0 d1 d2 hd0 hd1 hD'0 hD'1 hD'2 c hpq'
    hU hg hB hB_sub h_zero h_reg
  have h_p'_side :
      directionalSurfaceArea (eBasis 2) p' (F '' (graphMap g '' B)) =
        planeConstant * (ENNReal.ofReal (d0 * d1) * volume B) :=
    h_leaf.1
  have h_q_side :
      directionalSurfaceArea (eBasis 2) q (graphMap g '' B) =
        planeConstant * volume B :=
    h_leaf.2
  have h_transfer :
      directionalSurfaceArea (b 2) p (f '' (graphMap g '' B)) =
        directionalSurfaceArea (eBasis 2) p'
          (R '' (f '' (graphMap g '' B))) := by
    have h := directionalSurfaceArea_transfer
      p R (b 2) (hR_bi 2) (f '' (graphMap g '' B))
    simpa [e3, eBasis] using h
  have h_image_eq2 :
      R '' (f '' (graphMap g '' B)) = F '' (graphMap g '' B) := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨fx, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, hF_eq x⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, (hF_eq x).symm⟩
  have h_abs_det :
      |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| =
        ℓ 0 * ℓ 1 * ℓ 2 := by
    have h :
        |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| =
          ∏ i : Fin 3, ℓ i :=
      abs_det_eq_product A b ℓ hℓ hA
    have h_prod : (∏ i : Fin 3, ℓ i) = ℓ 0 * ℓ 1 * ℓ 2 := by
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp
      ring
    rw [h, h_prod]
  have h_cancel :
      ENNReal.ofReal (ℓ 2) =
        ENNReal.ofReal η⁻¹ * ENNReal.ofReal d2 := by
    have h1 :
        ENNReal.ofReal (η⁻¹ * d2) =
          ENNReal.ofReal η⁻¹ * ENNReal.ofReal d2 :=
      ENNReal.ofReal_mul (show 0 ≤ η⁻¹ by positivity)
    rw [← h1]
    have h2 : η⁻¹ * d2 = ℓ 2 := by
      simp [d2]
      field_simp [hη.ne']
    rw [h2]
  have h_mul_coeff :
      ENNReal.ofReal η⁻¹ * ENNReal.ofReal d2 *
          ENNReal.ofReal (d0 * d1) =
        ENNReal.ofReal
          (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) := by
    have h_pos1 : 0 ≤ η⁻¹ := by positivity
    have h_eq1 :
        ENNReal.ofReal (η⁻¹ * d2) =
          ENNReal.ofReal η⁻¹ * ENNReal.ofReal d2 :=
      ENNReal.ofReal_mul h_pos1
    have h_eq2 :
        ENNReal.ofReal ((η⁻¹ * d2) * (d0 * d1)) =
          ENNReal.ofReal (η⁻¹ * d2) * ENNReal.ofReal (d0 * d1) :=
      ENNReal.ofReal_mul (show 0 ≤ η⁻¹ * d2 by positivity)
    rw [← h_eq1, ← h_eq2]
    have h_real :
        (η⁻¹ * d2) * (d0 * d1) =
          η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| := by
      rw [h_abs_det]
      simp [d0, d1, d2]
      field_simp [hη.ne']
    rw [h_real]
  have h_rearrange :
      ENNReal.ofReal η⁻¹ *
          (ENNReal.ofReal d2 *
            (planeConstant * (ENNReal.ofReal (d0 * d1) * volume B))) =
        (ENNReal.ofReal η⁻¹ * ENNReal.ofReal d2 *
            ENNReal.ofReal (d0 * d1)) *
          (planeConstant * volume B) := by
    simp [mul_assoc, mul_left_comm, mul_comm]
  calc
    ENNReal.ofReal (ℓ 2) *
        directionalSurfaceArea (b 2) p (f '' (graphMap g '' B))
      = ENNReal.ofReal (ℓ 2) *
          directionalSurfaceArea (eBasis 2) p'
            (F '' (graphMap g '' B)) := by
        rw [h_transfer, h_image_eq2]
    _ = (ENNReal.ofReal η⁻¹ * ENNReal.ofReal d2) *
          directionalSurfaceArea (eBasis 2) p'
            (F '' (graphMap g '' B)) := by
        rw [h_cancel]
    _ = ENNReal.ofReal η⁻¹ *
          (ENNReal.ofReal d2 *
            directionalSurfaceArea (eBasis 2) p'
              (F '' (graphMap g '' B))) := by
        simp [mul_assoc]
    _ = ENNReal.ofReal η⁻¹ *
          (ENNReal.ofReal d2 *
            (planeConstant * (ENNReal.ofReal (d0 * d1) * volume B))) := by
        rw [h_p'_side]
    _ = ENNReal.ofReal
          (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
          (planeConstant * volume B) := by
        rw [h_rearrange, h_mul_coeff]
    _ = ENNReal.ofReal
          (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
          directionalSurfaceArea (eBasis 2) q
            (graphMap g '' B) := by
        rw [h_q_side]

end Kakeya.CV
