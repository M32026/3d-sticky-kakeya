import MyLeanRepo.Kakeya.CV.PolynomialCylinder.RotationTransfer
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Directional surface-area transport

A linear isometry preserves directional surface area when the polynomial,
direction, and set are transported together.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real

namespace Kakeya.CV

/-- Rotating the polynomial, direction, and set by a linear isometry preserves
directional surface area. -/
lemma directionalSurfaceArea_transfer_general
    (p : MvPolynomial (Fin 3) ℝ) (R : Point 3 ≃ₗᵢ[ℝ] Point 3)
    (e : Point 3) (S : Set (Point 3)) :
    directionalSurfaceArea (R e) (rotatedPoly p R) (R '' S) =
    directionalSurfaceArea e p S := by
  let p' := rotatedPoly p R
  let μ : Measure (Point 3) := Measure.hausdorffMeasure 2
  let g : Point 3 → ENNReal := fun y =>
    ENNReal.ofReal ‖inner ℝ (R e) (polynomialUnitNormal p' y)‖
  let f : Point 3 → ENNReal := fun x =>
    ENNReal.ofReal ‖inner ℝ e (polynomialUnitNormal p x)‖
  let e_iso : Point 3 ≃ᵢ Point 3 :=
    { toFun := R
      invFun := R.symm
      left_inv := R.left_inv
      right_inv := R.right_inv
      isometry_toFun := LinearIsometryEquiv.isometry R }
  have h_mp : MeasurePreserving R μ μ :=
    IsometryEquiv.measurePreserving_hausdorffMeasure e_iso (2 : ℝ)
  have h_integrand : ∀ x : Point 3, g (R x) = f x := by
    intro x
    have h1 : polynomialUnitNormal p' (R x) =
        R (polynomialUnitNormal p x) :=
      rotatedPoly_unitNormal p R x
    dsimp only [g, f]
    rw [h1]
    have h2 : inner ℝ (R e) (R (polynomialUnitNormal p x)) =
        inner ℝ e (polynomialUnitNormal p x) :=
      R.inner_map_map e (polynomialUnitNormal p x)
    rw [h2]
  have h_main : ∫⁻ y in R '' S, g y ∂μ = ∫⁻ x in S, f x ∂μ := by
    classical
    have h_mp_restrict :
        MeasurePreserving R (μ.restrict S) (μ.restrict (R '' S)) := by
      have h_map : Measure.map R (μ.restrict S) =
          μ.restrict (R '' S) := by
        ext T hT
        have h1 : Measure.map R (μ.restrict S) T =
            (μ.restrict S) (R ⁻¹' T) := by
          rw [Measure.map_apply R.continuous.measurable hT]
        rw [h1]
        have hRinv : MeasurableSet (R ⁻¹' T) :=
          R.continuous.measurable hT
        have h_left : (μ.restrict S) (R ⁻¹' T) =
            μ (R ⁻¹' T ∩ S) :=
          Measure.restrict_apply hRinv
        have h_right : (μ.restrict (R '' S)) T =
            μ (T ∩ R '' S) :=
          Measure.restrict_apply hT
        rw [h_left, h_right]
        have h_set : R '' (R ⁻¹' T ∩ S) = T ∩ R '' S := by
          ext z
          simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_preimage]
          constructor
          · rintro ⟨y, ⟨hyT, hyS⟩, rfl⟩
            exact ⟨hyT, y, hyS, rfl⟩
          · rintro ⟨hzT, y, hyS, rfl⟩
            exact ⟨y, ⟨hzT, hyS⟩, rfl⟩
        have h_image : μ (R '' (R ⁻¹' T ∩ S)) =
            μ (R ⁻¹' T ∩ S) :=
          linearIsometryEquiv_preserves_hausdorffMeasure
            R (R ⁻¹' T ∩ S)
        have h_eq : μ (R ⁻¹' T ∩ S) = μ (T ∩ R '' S) := by
          rw [h_set] at h_image
          exact h_image.symm
        exact h_eq
      exact ⟨R.continuous.measurable, h_map⟩
    let h_measEquiv : Point 3 ≃ᵐ Point 3 :=
      { R with
        measurable_toFun := R.continuous.measurable
        measurable_invFun := R.symm.continuous.measurable }
    have h_map2 :
        ∫⁻ y, g y ∂(μ.restrict (R '' S)) =
          ∫⁻ x, g (R x) ∂(μ.restrict S) :=
      MeasureTheory.MeasurePreserving.lintegral_map_equiv
        g h_measEquiv h_mp_restrict
    have h3 :
        ∫⁻ x, g (R x) ∂(μ.restrict S) =
          ∫⁻ x, f x ∂(μ.restrict S) := by
      congr with x
      exact h_integrand x
    rw [h_map2, h3]
  dsimp only [directionalSurfaceArea, f, g]
  exact h_main

end Kakeya.CV
