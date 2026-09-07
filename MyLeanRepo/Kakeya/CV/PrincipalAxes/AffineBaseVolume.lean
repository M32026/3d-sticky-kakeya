import MyLeanRepo.Kakeya.CV.PolynomialCylinder.GraphAreaFderiv
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Volume scaling for affine base maps

This module records the determinant scaling of planar volume under an
invertible affine map. It is used when an anisotropic affine image of a
regular coordinate graph is rewritten as a graph over a transformed base.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace Kakeya.CV

/-- Planar volume under the affine map `u ↦ c + M u` scales by `|det M|`. -/
lemma volume_affineBaseMap_image
    (c : R2) (M : R2 ≃ₗ[ℝ] R2) (U : Set R2) :
    volume ((fun u : R2 => c + M u) '' U) =
      ENNReal.ofReal |LinearMap.det (M : R2 →ₗ[ℝ] R2)| * volume U := by
  have himage :
      (fun u : R2 => c + M u) '' U =
        (fun x : R2 => c + x) '' (M '' U) := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨M u, ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, rfl⟩
  rw [himage]
  have htranslate :
      volume ((fun x : R2 => c + x) '' (M '' U)) =
        volume (M '' U) := by
    have hpreimage :
        (fun x : R2 => c + x) '' (M '' U) =
          (fun x : R2 => -c + x) ⁻¹' (M '' U) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        change -c + (c + x) ∈ M '' U
        convert hx using 1 <;> abel
      · intro hy
        refine ⟨-c + y, hy, ?_⟩
        abel_nf
    rw [hpreimage]
    exact measure_preimage_add volume (-c) (M '' U)
  rw [htranslate]
  exact
    MeasureTheory.Measure.addHaar_image_linearMap
      volume (M : R2 →ₗ[ℝ] R2) U

end Kakeya.CV
