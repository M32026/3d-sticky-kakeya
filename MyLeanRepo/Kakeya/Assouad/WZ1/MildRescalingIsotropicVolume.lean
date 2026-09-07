import MyLeanRepo.Kakeya.Assouad.TranslationInfrastructure
import MyLeanRepo.Kakeya.Assouad.VolumeScaling
import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingRediscretizationStatements

/-!
# Volume of the Proposition 9 isotropic similarity

The final mild rescaling is a translation followed by a positive homothety.
This module records its exact three-dimensional Jacobian independently of the
cleanup and target-UTS constructions.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

lemma volume_image_wz1IsotropicRescalingMap
    {scale : ℝ} (hscale : 0 < scale)
    (center : Point3) {S : Set Point3}
    (hS : MeasurableSet S) :
    volume (wz1IsotropicRescalingMap center scale '' S) =
      ENNReal.ofReal (scale ^ 3) * volume S := by
  let translate : Point3 → Point3 :=
    fun point => point + (-center)
  have himage :
      wz1IsotropicRescalingMap center scale '' S =
        homothety scale '' (translate '' S) := by
    ext point
    simp only [Set.mem_image]
    constructor
    · rintro ⟨source, hsource, rfl⟩
      exact
        ⟨translate source, ⟨source, hsource, rfl⟩, by
          simp [translate, homothety_apply,
            wz1IsotropicRescalingMap, sub_eq_add_neg]⟩
    · rintro ⟨translated, ⟨source, hsource, rfl⟩, rfl⟩
      exact
        ⟨source, hsource, by
          simp [translate, homothety_apply,
            wz1IsotropicRescalingMap, sub_eq_add_neg]⟩
  rw [himage, volume_homothety scale hscale]
  have htranslate :
      volume (translate '' S) = volume S := by
    simpa [translate] using
      (volume_translate (v := -center) hS)
  rw [htranslate]

end Kakeya.Assouad
