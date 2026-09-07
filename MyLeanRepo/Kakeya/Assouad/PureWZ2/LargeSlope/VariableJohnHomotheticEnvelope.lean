import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.GeneralInclusionMain
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.VolumeUtils
import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Variable-factor outer-John homothetic envelope

This is the variable-factor version of the fixed factor-100 envelope used by
the public Definition 2.12 infrastructure.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

private lemma variable_john_homothetic_envelope_point_inclusion
    {center : Point3}
    {linear : Point3 ≃ₗ[ℝ] Point3}
    {factor : ℝ}
    (hfactor : 1 ≤ factor)
    {sourcePoint homothetyCenter : Point3}
    (hsourcePoint :
      sourcePoint ∈ JohnEllipsoid.ellipsoid center linear)
    (hcenter :
      homothetyCenter ∈ JohnEllipsoid.ellipsoid center linear) :
    AffineMap.homothety homothetyCenter factor sourcePoint ∈
      AffineMap.homothety center (2 * factor - 1) ''
        JohnEllipsoid.ellipsoid center linear := by
  let sourceVector := linear.symm (sourcePoint - center)
  let centerVector := linear.symm (homothetyCenter - center)
  let envelopePoint : Point3 :=
    center + (2 * factor - 1)⁻¹ •
      (factor • (sourcePoint - center) -
        (factor - 1) • (homothetyCenter - center))
  have hsourceNorm : ‖sourceVector‖ ≤ 1 := by
    exact (JohnEllipsoid.ellipsoid_mem_iff center linear sourcePoint).mp
      hsourcePoint
  have hcenterNorm : ‖centerVector‖ ≤ 1 := by
    exact (JohnEllipsoid.ellipsoid_mem_iff center linear homothetyCenter).mp
      hcenter
  have hscalePos : 0 < 2 * factor - 1 := by linarith
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
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : 0 ≤ factor),
          abs_of_nonneg (by linarith : 0 ≤ factor - 1)]
      _ ≤ factor * 1 + (factor - 1) * 1 := by gcongr
      _ = 2 * factor - 1 := by ring
  have henvelopePoint :
      envelopePoint ∈ JohnEllipsoid.ellipsoid center linear := by
    rw [JohnEllipsoid.ellipsoid_mem_iff, henvelopeCoordinates]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hscalePos)]
    exact (inv_mul_le_one₀ hscalePos).2 hcombination
  refine ⟨envelopePoint, henvelopePoint, ?_⟩
  rw [AffineMap.homothety_apply, AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  dsimp only [envelopePoint]
  have hscaleNe : 2 * factor - 1 ≠ 0 := hscalePos.ne'
  apply PiLp.ext
  intro coordinate
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp [hscaleNe]
  ring

/-- A common variable-factor homothetic envelope. -/
theorem pureWZ2_variable_john_homothetic_envelope
    (factor : ℝ) (hfactor : 1 ≤ factor)
    (convexBody : Set Point3)
    (hbody : JohnEllipsoid.IsConvexBody convexBody) :
    ∃ envelope : Set Point3,
      Convex ℝ envelope ∧
        volume envelope ≤
          ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
            volume convexBody ∧
        ∀ point ∈ convexBody,
          AffineMap.homothety point factor '' convexBody ⊆ envelope := by
  let center := hbody.outerJohnEllipsoidCenter
  let linear := hbody.outerJohnEllipsoidMap
  let ellipsoid := hbody.outerJohnEllipsoid
  let envelope := AffineMap.homothety center (2 * factor - 1) '' ellipsoid
  have hscalePos : 0 < 2 * factor - 1 := by linarith
  refine ⟨envelope, ?_, ?_, ?_⟩
  · exact (JohnEllipsoid.ellipsoid_convex center linear).affine_image
      (AffineMap.homothety center (2 * factor - 1))
  · have hinner :
        AffineMap.homothety center ((3 : ℝ)⁻¹) '' ellipsoid ⊆
          convexBody :=
        JohnEllipsoid.IsConvexBody.homothety_subset_outerJohnEllipsoid_main
          hbody
    have hinnerVolume :
        ENNReal.ofReal (1 / 27 : ℝ) * volume ellipsoid ≤
          volume convexBody := by
      calc
        ENNReal.ofReal (1 / 27 : ℝ) * volume ellipsoid =
            volume (AffineMap.homothety center ((3 : ℝ)⁻¹) '' ellipsoid) := by
          rw [JohnEllipsoid.volume_homothety]
          norm_num
        _ ≤ volume convexBody := measure_mono hinner
    have hellipsoidVolume : volume ellipsoid ≤ 27 * volume convexBody := by
      have hcancel : (27 : ENNReal) * ENNReal.ofReal (1 / 27 : ℝ) = 1 := by
        rw [← ENNReal.ofReal_ofNat (n := 27),
          ← ENNReal.ofReal_mul (by norm_num)]
        norm_num
      calc
        volume ellipsoid = 27 *
            (ENNReal.ofReal (1 / 27 : ℝ) * volume ellipsoid) := by
          rw [← mul_assoc, hcancel, one_mul]
        _ ≤ 27 * volume convexBody := by gcongr
    rw [JohnEllipsoid.volume_homothety]
    have hscale :
        ENNReal.ofReal (|2 * factor - 1| ^ 3) =
          ENNReal.ofReal ((2 * factor - 1) ^ 3) := by
      rw [abs_of_pos hscalePos]
    rw [hscale]
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
    have hsourceEllipsoid := hbody.outerJohnEllipsoid_spec.1 hsourcePoint
    have hcenterEllipsoid := hbody.outerJohnEllipsoid_spec.1 hcenter
    exact variable_john_homothetic_envelope_point_inclusion hfactor
      hsourceEllipsoid hcenterEllipsoid

end Kakeya.Assouad

end
