import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.Streamlined.VolumeHelpers

/-!
# Finiteness of cropped-paper shaded mass

Every cropped paper carrier is contained in the fixed box `[-1,1]^3`.
Consequently any shading of a finite indexed paper-tube family has finite
total mass, without a small-scale hypothesis.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

theorem wz1PaperTubeShading_mass_ne_top
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) :
    shading.mass ≠ ⊤ := by
  have boxFinite :
      volume (Kakeya.Streamlined.axisBox 2 2 2) ≠ ⊤ := by
    rw [Kakeya.Streamlined.volume_axisBox
      2 2 2 (by norm_num) (by norm_num) (by norm_num)]
    exact ENNReal.ofReal_ne_top
  apply ENNReal.sum_ne_top.mpr
  intro index _
  apply ne_top_of_le_ne_top boxFinite
  exact measure_mono fun point hpoint =>
    (shading.subset_body index hpoint).2

end Kakeya.Assouad

end
