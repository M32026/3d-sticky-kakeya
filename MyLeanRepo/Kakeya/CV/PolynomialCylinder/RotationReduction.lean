import MyLeanRepo.Kakeya.CV.PolynomialCylinder.Basic
import Mathlib.Geometry.Euclidean.Projection

/-!
# Rotation reduction for the polynomial cylinder estimate

For any unit vector `e`, there exists a linear isometry equivalence (rotation)
`R` sending `e` to the standard basis vector `e₃`. Such rotations preserve both
the 2-dimensional Hausdorff measure and inner products.

## Whiteprint node: rotation-reduction
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

variable {n : ℕ}

/-- For any unit vector `e`, there exists an orthogonal transformation `R` of
`Point 3` such that `R e = e₃`. -/
lemma exists_rotation_to_e3 (e : Point 3) (he : ‖e‖ = 1) :
    ∃ (R : Point 3 ≃ₗᵢ[ℝ] Point 3), R e = e3 := by
  let v : Finset (Point 3) := {e}
  have hv : Orthonormal ℝ ((↑) : v → Point 3) := by
    simp [v, Orthonormal, he] <;> norm_num
  obtain ⟨u, b, hvu, hb⟩ := Orthonormal.exists_orthonormalBasis_extension hv
  have h_e_in_u : e ∈ u := by
    have h : ({e} : Finset (Point 3)) ⊆ u := hvu
    exact h (by simp)
  let i0 : u := ⟨e, h_e_in_u⟩
  have h_finrank : Module.finrank ℝ (Point 3) = Fintype.card u :=
    Module.finrank_eq_card_basis b.toBasis
  have h_rank3 : Module.finrank ℝ (Point 3) = 3 := by simp
  have h_card3 : Fintype.card u = 3 := by
    rw [← h_finrank, h_rank3]
  have h_equiv : Nonempty (u ≃ Fin 3) := by
    have h : Fintype.card u = Fintype.card (Fin 3) := by
      rw [h_card3] <;> simp
    exact (Fintype.card_eq.mp h)
  let e0 : u ≃ Fin 3 := h_equiv.some
  let j : Fin 3 := e0 i0
  let σ : Equiv.Perm (Fin 3) := Equiv.swap j 2
  let eqv : u ≃ Fin 3 := e0.trans σ
  have heqv : eqv i0 = 2 := by
    have h1 : eqv i0 = σ (e0 i0) := by rfl
    rw [h1]
    dsimp only [σ]
    rw [Equiv.swap_apply_left]
  let stdBasis := EuclideanSpace.basisFun (Fin 3) ℝ
  let R : Point 3 ≃ₗᵢ[ℝ] Point 3 := b.equiv stdBasis eqv
  have hR : R e = e3 := by
    have h1 : R (b i0) = stdBasis (eqv i0) :=
      OrthonormalBasis.equiv_apply_basis b stdBasis eqv i0
    have h2 : (b i0 : Point 3) = e := by
      rw [hb] <;> rfl
    have h3 : R e = stdBasis (eqv i0) := by
      rw [← h2, h1]
    rw [h3, heqv]
    have h4 : stdBasis 2 = e3 := by
      rw [EuclideanSpace.basisFun_apply] <;> rfl
    rw [h4]
  exact ⟨R, hR⟩

/-- A linear isometry equivalence preserves the 2-dimensional Hausdorff measure. -/
lemma linearIsometryEquiv_preserves_hausdorffMeasure
    (R : Point 3 ≃ₗᵢ[ℝ] Point 3) (s : Set (Point 3)) :
    Measure.hausdorffMeasure (2 : ℝ) (R '' s) = Measure.hausdorffMeasure (2 : ℝ) s := by
  have h_isom : Isometry (R : Point 3 → Point 3) :=
    LinearIsometryEquiv.isometry R
  let e : Point 3 ≃ᵢ Point 3 :=
    { toFun := R
      invFun := R.symm
      left_inv := R.left_inv
      right_inv := R.right_inv
      isometry_toFun := h_isom }
  exact IsometryEquiv.hausdorffMeasure_image e (2 : ℝ) s

/-- A linear isometry equivalence preserves inner products. -/
lemma linearIsometryEquiv_preserves_inner
    (R : Point 3 ≃ₗᵢ[ℝ] Point 3) (x y : Point 3) :
    inner ℝ (R x) (R y) = inner ℝ x y := by
  let f : Point 3 →ₗᵢ[ℝ] Point 3 :=
    { toFun := R
      map_add' := R.map_add
      map_smul' := R.map_smul
      norm_map' := R.norm_map }
  exact LinearIsometry.inner_map_map f x y

end Kakeya.CV
