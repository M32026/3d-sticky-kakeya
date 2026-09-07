import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Measure preservation for the cinematic shear

The map `cinematicShear c₀` changes the twisted-projection coordinates from
`(horizontal, z)` to `(z, horizontal - c₀ z)`.  Its determinant has absolute
value one, so it preserves planar Lebesgue measure and all `Lᵖ` norms.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

lemma cinematicShear_measurePreserving (c₀ : ℝ) :
    MeasurePreserving (cinematicShear c₀) volume volume := by
  let shearMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
    !![0, 1; 1, -c₀]
  let shearLinear : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
    shearMatrix.toLin'
  have hdet : LinearMap.det shearLinear = -1 := by
    change LinearMap.det (Matrix.toLin' shearMatrix) = -1
    rw [LinearMap.det_toLin']
    simp [shearMatrix, Matrix.det_fin_two]
  have hdet_ne : LinearMap.det shearLinear ≠ 0 := by
    rw [hdet]
    norm_num
  have hmap : Measure.map shearLinear volume = volume := by
    rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet_ne, hdet]
    simp
  have hlinear : MeasurePreserving shearLinear volume volume :=
    ⟨LinearMap.continuous_on_pi shearLinear |>.measurable, hmap⟩
  let coordinates : (Fin 2 → ℝ) → ℝ × ℝ :=
    fun q => (q 0, q 1)
  have hcoordinates :
      MeasurePreserving coordinates volume volume :=
    MeasureTheory.measurePreserving_finTwoArrow volume
  have hofLp :
      MeasurePreserving (@WithLp.ofLp 2 (Fin 2 → ℝ)) volume volume :=
    PiLp.volume_preserving_ofLp (Fin 2)
  have hformula :
      cinematicShear c₀ =
        coordinates ∘ shearLinear ∘ (@WithLp.ofLp 2 (Fin 2 → ℝ)) := by
    funext p
    apply Prod.ext
    · simp [cinematicShear, coordinates, shearLinear, shearMatrix,
        Matrix.toLin'_apply, Fin.sum_univ_two, Matrix.vecHead,
        Matrix.vecTail]
    · simp [cinematicShear, coordinates, shearLinear, shearMatrix,
        Matrix.toLin'_apply, Fin.sum_univ_two, Matrix.vecHead,
        Matrix.vecTail]
      <;> ring
  rw [hformula]
  exact hcoordinates.comp (hlinear.comp hofLp)

lemma lintegral_comp_cinematicShear
    (c₀ : ℝ) (g : ℝ × ℝ → ENNReal) (hg : Measurable g) :
    ∫⁻ q : Point2, g (cinematicShear c₀ q) =
      ∫⁻ p : ℝ × ℝ, g p :=
  (cinematicShear_measurePreserving c₀).lintegral_comp hg

lemma eLpNorm_comp_cinematicShear
    (c₀ : ℝ) (g : ℝ × ℝ → ENNReal) (p : ENNReal)
    (hg : Measurable g) :
    eLpNorm (g ∘ cinematicShear c₀) p volume =
      eLpNorm g p volume :=
  eLpNorm_comp_measurePreserving hg.aestronglyMeasurable
    (cinematicShear_measurePreserving c₀)

end Kakeya.Assouad
