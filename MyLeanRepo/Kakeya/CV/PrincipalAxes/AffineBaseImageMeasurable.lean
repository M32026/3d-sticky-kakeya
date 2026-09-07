import MyLeanRepo.Kakeya.CV.PrincipalAxes.AffineBaseVolume
import MyLeanRepo.Kakeya.CV.Geometry
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Measurable affine-base images

An invertible planar affine map sends measurable sets to measurable sets and
scales their volume by the absolute determinant.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Kakeya.CV

/-- The image of a measurable planar set under an invertible affine map is
measurable, with the expected determinant volume scaling. -/
lemma affineBaseImage_measurable_volume
    {B : Set R2} (hB : MeasurableSet B)
    (c : R2) (M : R2 ≃ₗ[ℝ] R2) :
    MeasurableSet ((fun u : R2 => c + M u) '' B) ∧
    volume ((fun u : R2 => c + M u) '' B) =
      ENNReal.ofReal |LinearMap.det (M : R2 →ₗ[ℝ] R2)| * volume B := by
  let Mclm : R2 ≃L[ℝ] R2 := M.toContinuousLinearEquiv
  let L : R2 ≃ₜ R2 :=
    { toFun := fun u => c + Mclm u
      invFun := fun y => Mclm.symm (y - c)
      left_inv := by
        intro u
        simp
      right_inv := by
        intro y
        simp
      continuous_toFun := continuous_const.add Mclm.continuous
      continuous_invFun :=
        Mclm.symm.continuous.comp (continuous_id.sub continuous_const) }
  have himage : L '' B = L.symm ⁻¹' B := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa [L] using hu
    · intro hy
      exact ⟨L.symm y, hy, L.right_inv y⟩
  have hmeas : MeasurableSet (L '' B) := by
    rw [himage]
    exact L.symm.continuous.measurable hB
  have hvolume :
      volume (L '' B) =
        ENNReal.ofReal |LinearMap.det (M : R2 →ₗ[ℝ] R2)| * volume B :=
    volume_affineBaseMap_image c M B
  exact ⟨hmeas, hvolume⟩

end Kakeya.CV
