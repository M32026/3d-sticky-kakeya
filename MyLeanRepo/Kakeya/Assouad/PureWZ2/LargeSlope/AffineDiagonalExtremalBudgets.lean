import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalMap
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper
import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement

/-!
# Density and union-volume budgets for the affine-diagonal target

This module contains only the final numerical implications used by paper
Lemma 8.  The geometric producers must separately provide the target family,
its shading, and the honest affine-image containment.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- Once all finite selection losses have been absorbed into the displayed
mass budget, the standard quadratic paper-carrier estimate gives the exact
aggregate density required by cropped extremality. -/
theorem pureWZ2_affineDiagonal_dense_of_mass_budget
    {targetDelta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily targetDelta}
    (shading : WZ1PaperTubeShading family)
    (hdelta : 0 < targetDelta)
    (hdeltaSmall : targetDelta ≤ 1 / 24)
    (hline : WZ1PaperIsLineClass family)
    (density : ENNReal)
    (hbudget :
      density *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN targetDelta 2 * family.enncard) ≤
        shading.mass) :
    shading.IsLambdaDense density := by
  have hbody :
      (wz1PaperBodyFamily family).mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN targetDelta 2 * family.enncard :=
    wz2_paper_shading_mass_upper hdelta hdeltaSmall hline
      { carrier := fun index =>
          wz1PaperTubeCarrier (family.tube index)
        measurable_carrier := fun index =>
          wz1PaperTubeCarrier_measurable (family.tube index)
        subset_body := fun _ => Set.Subset.rfl }
  exact (mul_le_mul_left' hbody density).trans hbudget

/-- Union volume transfers through the literal fixed horizontal rotation and
diagonal dilation.  No cubical saturation may be substituted here unless its
union is separately proved to lie in this exact affine image. -/
theorem pureWZ2_affineDiagonal_volume_upper_of_image_subset
    {sourceDelta targetDelta sigma inputLoss outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    {targetFamily : Kakeya.Streamlined.TubeFamily targetDelta}
    (targetShading : WZ1PaperTubeShading targetFamily)
    (frameSlope : ℝ) (center : Point3) (m : ℝ)
    (hm : 0 < m)
    (hsubset : targetShading.union ⊆
      pureWZ2AffineDiagonalMapCentered frameSlope center
        (100 / m) (m ^ 2 / 100) 1 '' sourceShading.union)
    (hsource : volume sourceShading.union ≤
      Kakeya.realRpowENN sourceDelta (sigma - inputLoss))
    (hbudget :
      ENNReal.ofReal m *
          Kakeya.realRpowENN sourceDelta (sigma - inputLoss) ≤
        Kakeya.realRpowENN targetDelta (sigma - outputLoss)) :
    volume targetShading.union ≤
      Kakeya.realRpowENN targetDelta (sigma - outputLoss) := by
  calc
    volume targetShading.union ≤
        volume
          (pureWZ2AffineDiagonalMapCentered frameSlope center
            (100 / m) (m ^ 2 / 100) 1 '' sourceShading.union) :=
      measure_mono hsubset
    _ = ENNReal.ofReal m * volume sourceShading.union :=
      pureWZ2AffineDiagonalMapCentered_volume_image frameSlope center hm
        (measurableSet_shading_union sourceShading)
    _ ≤ ENNReal.ofReal m *
        Kakeya.realRpowENN sourceDelta (sigma - inputLoss) := by gcongr
    _ ≤ Kakeya.realRpowENN targetDelta (sigma - outputLoss) := hbudget

end Kakeya.Assouad

end
