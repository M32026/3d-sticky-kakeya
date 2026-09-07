import MyLeanRepo.Kakeya.CV.ShapeNet
import MyLeanRepo.Kakeya.CV.EllipsoidShapeClose
import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.BoundedEllipsoidShapeBand

/-!
# Finiteness of bounded stable-palette bands

A bounded inverse-shape band contains only finitely many separated palette
shapes of each colour.  Since every palette ellipsoid is centered at zero,
inverse shape determines the full ellipsoid parameter.
-/

noncomputable section

open Set
open MeasureTheory
open Kakeya.CV.ShapeSpace

namespace Kakeya.CV

theorem stable_ellipsoid_palette_band_finite
    (hBand : BoundedEllipsoidShapeBandStatement) :
    StableEllipsoidPaletteBandFinitenessStatement := by
  intro α N net colour hα hcenter hseparation R v hR hv
  let band : Set EllipsoidParameter :=
    {E | E ∈ net ∧
      ellipsoidCarrier E ⊆ Metric.closedBall 0 R ∧
      ENNReal.ofReal v ≤ volume (ellipsoidCarrier E)}
  let bandColour : Fin N → Set EllipsoidParameter := fun θ =>
    {E | E ∈ band ∧ colour E = θ}
  obtain ⟨C, hC, hshape⟩ := hBand R v hR hv
  have hα3 : 1 < α ^ 3 := by
    nlinarith [sq_pos_of_pos (show 0 < α by linarith)]
  obtain ⟨D, hpacking⟩ := packing_bound_general hC hα3
  have h_finite_colour : ∀ θ, (bandColour θ).Finite := by
    intro θ
    let shape : EllipsoidParameter → Point 3 ≃ₗ[ℝ] Point 3 := fun E => E.2.symm
    let shapes : Set (Point 3 ≃ₗ[ℝ] Point 3) := shape '' bandColour θ
    have h_shapes_bounded :
        ∀ A ∈ shapes, ShapeClose C (1 : Point 3 ≃ₗ[ℝ] Point 3) A := by
      rintro A ⟨E, hE, rfl⟩
      have hEband : E ∈ band := hE.1
      have hEcenter : E.1 = 0 := hcenter E hEband.1
      have hcarrier :
          ellipsoidCarrier E = JohnEllipsoid.ellipsoid 0 E.2 := by
        simp [ellipsoidCarrier, hEcenter]
      apply hshape E.2
      · simpa [hcarrier] using hEband.2.1
      · simpa [hcarrier] using hEband.2.2
    have h_shapes_separated :
        ∀ A₁ ∈ shapes, ∀ A₂ ∈ shapes, A₁ ≠ A₂ →
          ¬ShapeClose (α ^ 3) A₁ A₂ := by
      rintro A₁ ⟨E₁, hE₁, rfl⟩ A₂ ⟨E₂, hE₂, rfl⟩ hne hclose
      have hE₁band : E₁ ∈ band := hE₁.1
      have hE₂band : E₂ ∈ band := hE₂.1
      have hE₁center : E₁.1 = 0 := hcenter E₁ hE₁band.1
      have hE₂center : E₂.1 = 0 := hcenter E₂ hE₂band.1
      have hhom :
          AreHomotheticallyCloseAt 0 (α ^ 3)
            (ellipsoidCarrier E₁) (ellipsoidCarrier E₂) := by
        have hraw := shapeClose_imp_homothety_at
          (show 0 < α ^ 3 by positivity) (0 : Point 3) hclose
        have hshape1 : (shape E₁).symm = E₁.2 := by simp [shape]
        have hshape2 : (shape E₂).symm = E₂.2 := by simp [shape]
        have hcarrier1 :
            ellipsoidCarrier E₁ = JohnEllipsoid.ellipsoid 0 E₁.2 := by
          simp [ellipsoidCarrier, hE₁center]
        have hcarrier2 :
            ellipsoidCarrier E₂ = JohnEllipsoid.ellipsoid 0 E₂.2 := by
          simp [ellipsoidCarrier, hE₂center]
        rw [hcarrier1, hcarrier2]
        change
          dilateAbout 0 (α ^ 3)⁻¹ (JohnEllipsoid.ellipsoid 0 E₁.2) ⊆
              JohnEllipsoid.ellipsoid 0 E₂.2 ∧
            JohnEllipsoid.ellipsoid 0 E₂.2 ⊆
              dilateAbout 0 (α ^ 3) (JohnEllipsoid.ellipsoid 0 E₁.2)
        simpa [hshape1, hshape2] using hraw
      have hEeq : E₁ = E₂ :=
        hseparation E₁ hE₁band.1 E₂ hE₂band.1
          (hE₁.2.trans hE₂.2.symm) hhom
      apply hne
      simpa [hEeq]
    have h_shapes_finite : shapes.Finite :=
      (hpacking shapes h_shapes_bounded h_shapes_separated).1
    have h_shape_injective : Set.InjOn shape (bandColour θ) := by
      intro E₁ hE₁ E₂ hE₂ heq
      have hE₁center : E₁.1 = 0 := hcenter E₁ hE₁.1.1
      have hE₂center : E₂.1 = 0 := hcenter E₂ hE₂.1.1
      have hlinear : E₁.2 = E₂.2 := by
        simpa [shape] using congr_arg
          (fun A : Point 3 ≃ₗ[ℝ] Point 3 => A.symm) heq
      exact Prod.ext (hE₁center.trans hE₂center.symm) hlinear
    exact Set.Finite.of_finite_image h_shapes_finite h_shape_injective
  have h_union : band = ⋃ θ, bandColour θ := by
    ext E
    simp [bandColour]
  change band.Finite
  rw [h_union]
  exact Set.finite_iUnion h_finite_colour

/-- Every fixed radius and positive-volume band of the stable palette is finite. -/
theorem stable_ellipsoid_palette_band_finiteness :
    StableEllipsoidPaletteBandFinitenessStatement :=
  stable_ellipsoid_palette_band_finite bounded_ellipsoid_shape_band

end Kakeya.CV
