import MyLeanRepo.Kakeya.Geometry.OuterJohnEllipsoid
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.VolumeUtils
import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Variable-factor common homothetic envelope

The outer John ellipsoid turns homotheties of one convex body about varying
centers in that body into one common convex envelope.  This is the
variable-factor form of the fixed factor-`100` sticky envelope.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory
open scoped Pointwise Real

private lemma variable_john_envelope_point_inclusion
    {center : Point3}
    {linear : Point3 ≃ₗ[ℝ] Point3}
    {sourcePoint homothetyCenter : Point3}
    {factor : ℝ}
    (hfactor : 1 ≤ factor)
    (hsourcePoint :
      sourcePoint ∈ JohnEllipsoid.ellipsoid center linear)
    (hcenter :
      homothetyCenter ∈ JohnEllipsoid.ellipsoid center linear) :
    AffineMap.homothety homothetyCenter factor sourcePoint ∈
      AffineMap.homothety center (2 * factor - 1) ''
        JohnEllipsoid.ellipsoid center linear := by
  have hscale : 0 < 2 * factor - 1 := by linarith
  have hsourceNorm :
      ‖linear.symm (sourcePoint - center)‖ ≤ 1 :=
    (JohnEllipsoid.ellipsoid_mem_iff center linear sourcePoint).mp
      hsourcePoint
  have hcenterNorm :
      ‖linear.symm (homothetyCenter - center)‖ ≤ 1 :=
    (JohnEllipsoid.ellipsoid_mem_iff center linear homothetyCenter).mp
      hcenter
  let sourceVector := linear.symm (sourcePoint - center)
  let centerVector := linear.symm (homothetyCenter - center)
  let envelopePoint : Point3 :=
    center +
      (2 * factor - 1)⁻¹ •
        (factor • (sourcePoint - center) -
          (factor - 1) • (homothetyCenter - center))
  have henvelopeCoordinates :
      linear.symm (envelopePoint - center) =
        (2 * factor - 1)⁻¹ •
          (factor • sourceVector - (factor - 1) • centerVector) := by
    simp [envelopePoint, sourceVector, centerVector, map_sub, map_smul]
  have hcombination :
      ‖factor • sourceVector - (factor - 1) • centerVector‖ ≤
        2 * factor - 1 := by
    calc
      ‖factor • sourceVector - (factor - 1) • centerVector‖ ≤
          ‖factor • sourceVector‖ +
            ‖(factor - 1) • centerVector‖ := norm_sub_le _ _
      _ = factor * ‖sourceVector‖ +
            (factor - 1) * ‖centerVector‖ := by
        rw [norm_smul, norm_smul]
        simp [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ factor by linarith),
          abs_of_nonneg (show 0 ≤ factor - 1 by linarith)]
      _ ≤ factor * 1 + (factor - 1) * 1 := by gcongr
      _ = 2 * factor - 1 := by ring
  have henvelopePoint :
      envelopePoint ∈ JohnEllipsoid.ellipsoid center linear := by
    rw [JohnEllipsoid.ellipsoid_mem_iff, henvelopeCoordinates]
    calc
      ‖(2 * factor - 1)⁻¹ •
          (factor • sourceVector - (factor - 1) • centerVector)‖ =
          (2 * factor - 1)⁻¹ *
            ‖factor • sourceVector -
              (factor - 1) • centerVector‖ := by
        rw [norm_smul]
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hscale)]
      _ ≤ (2 * factor - 1)⁻¹ * (2 * factor - 1) :=
        mul_le_mul_of_nonneg_left hcombination
          (inv_nonneg.mpr hscale.le)
      _ = 1 := by field_simp [hscale.ne']
  have hscaled :
      (2 * factor - 1) • (envelopePoint - center) =
        factor • (sourcePoint - center) -
          (factor - 1) • (homothetyCenter - center) := by
    simp [envelopePoint, smul_smul, hscale.ne']
  refine ⟨envelopePoint, henvelopePoint, ?_⟩
  rw [AffineMap.homothety_apply, AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  rw [hscaled]
  module

/-- Common outer-John envelope for all factor-`factor` homotheties whose
centers lie in the original convex body. -/
theorem john_variable_homothetic_envelope
    (convexBody : Set Point3)
    (hbody : JohnEllipsoid.IsConvexBody convexBody)
    (factor : ℝ) (hfactor : 1 ≤ factor) :
    ∃ envelope : Set Point3,
      Convex ℝ envelope ∧
      volume envelope ≤
        ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
          volume convexBody ∧
      ∀ point ∈ convexBody,
        AffineMap.homothety point factor '' convexBody ⊆ envelope := by
  let center : Point3 := hbody.outerJohnEllipsoidCenter
  let linear : Point3 ≃ₗ[ℝ] Point3 := hbody.outerJohnEllipsoidMap
  let ellipsoid : Set Point3 := hbody.outerJohnEllipsoid
  let envelope : Set Point3 :=
    AffineMap.homothety center (2 * factor - 1) '' ellipsoid
  have hscale : 0 < 2 * factor - 1 := by linarith
  refine ⟨envelope, ?_, ?_, ?_⟩
  · exact (JohnEllipsoid.ellipsoid_convex center linear).affine_image
      (AffineMap.homothety center (2 * factor - 1))
  · have hinner :
        AffineMap.homothety center (3 : ℝ)⁻¹ '' ellipsoid ⊆
          convexBody := hbody.homothety_subset_outerJohnEllipsoid
    have hinnerVolume :
        ENNReal.ofReal (1 / 27 : ℝ) * volume ellipsoid ≤
          volume convexBody := by
      calc
        ENNReal.ofReal (1 / 27 : ℝ) * volume ellipsoid =
            volume (AffineMap.homothety center (3 : ℝ)⁻¹ ''
              ellipsoid) := by
          rw [JohnEllipsoid.volume_homothety]
          norm_num
        _ ≤ volume convexBody := measure_mono hinner
    have hellipsoidVolume :
        volume ellipsoid ≤ 27 * volume convexBody := by
      have hcancel :
          (27 : ENNReal) * ENNReal.ofReal (1 / 27 : ℝ) = 1 := by
        have htwentySeven : (27 : ENNReal) =
            ENNReal.ofReal (27 : ℝ) := by norm_num
        rw [htwentySeven, ← ENNReal.ofReal_mul (by norm_num)]
        norm_num
      calc
        volume ellipsoid = 27 *
            (ENNReal.ofReal (1 / 27 : ℝ) * volume ellipsoid) := by
          rw [← mul_assoc, hcancel, one_mul]
        _ ≤ 27 * volume convexBody := by gcongr
    rw [JohnEllipsoid.volume_homothety]
    have habs : |2 * factor - 1| = 2 * factor - 1 :=
      abs_of_pos hscale
    rw [habs]
    calc
      ENNReal.ofReal ((2 * factor - 1) ^ 3) * volume ellipsoid ≤
          ENNReal.ofReal ((2 * factor - 1) ^ 3) *
            (27 * volume convexBody) := by gcongr
      _ = ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
            volume convexBody := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 27)]
        norm_num
        ring
  · intro homothetyCenter hcenter target htarget
    rcases htarget with ⟨sourcePoint, hsourcePoint, rfl⟩
    have hspec := hbody.outerJohnEllipsoid_spec
    exact variable_john_envelope_point_inclusion hfactor
      (hspec.1 hsourcePoint) (hspec.1 hcenter)

end Kakeya.Assouad.PureWZ2

end
