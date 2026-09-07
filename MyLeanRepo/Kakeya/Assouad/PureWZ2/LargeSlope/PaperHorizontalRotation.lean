import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.RotatedHorizontalCoordinates
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ConfigurationWeakening
import MyLeanRepo.Kakeya.Assouad.WZ1.HorizontalChartNormalization.Basic
import MyLeanRepo.Kakeya.Assouad.WZ1.HorizontalChartNormalization.Frostman

/-!
# Exact horizontal-rotation transport for pure paper data

The fixed rotation preserves the vertical coordinate and Lebesgue measure.
This module transports tube axes, arbitrary measurable shadings, the pure
nearby-scale CWA structure, and local grain data without changing constants.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

def pureWZ2RotateFamily (frameSlope : ℝ) {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta) :
    Kakeya.Streamlined.TubeFamily delta :=
  transportFamily (pureWZ2HorizontalRotation frameSlope) family

def pureWZ2RotatePaperShading (frameSlope : ℝ) {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (hrotatedBox : pureWZ2HorizontalRotation frameSlope '' shading.union ⊆
      Kakeya.Streamlined.axisBox 2 2 2) :
    WZ1PaperTubeShading (pureWZ2RotateFamily frameSlope family) where
  carrier index := pureWZ2HorizontalRotation frameSlope '' shading.carrier index
  measurable_carrier index := by
    exact (pureWZ2HorizontalRotation frameSlope).toMeasurableEquiv
      |>.measurableSet_image.mpr (shading.measurable_carrier index)
  subset_body index := by
    rintro target ⟨source, hsource, rfl⟩
    have hthick := (shading.subset_body index hsource).1
    constructor
    · have hline : pureWZ2HorizontalRotation frameSlope ''
          tubeAxisLine (family.tube index) =
        tubeAxisLine ((pureWZ2RotateFamily frameSlope family).tube index) := by
        ext target
        constructor
        · rintro ⟨source, ⟨parameter, rfl⟩, rfl⟩
          refine ⟨parameter, ?_⟩
          simp [pureWZ2RotateFamily, transportFamily, transportTube,
            tubeAxisLine]
        · rintro ⟨parameter, rfl⟩
          refine ⟨(family.tube index).base +
              parameter • (family.tube index).direction,
            ⟨parameter, rfl⟩, ?_⟩
          simp [pureWZ2RotateFamily, transportFamily, transportTube]
      have himage : pureWZ2HorizontalRotation frameSlope ''
          Metric.cthickening (6 * delta) (tubeAxisLine (family.tube index)) =
        Metric.cthickening (6 * delta)
          (tubeAxisLine ((pureWZ2RotateFamily frameSlope family).tube index)) := by
        rw [image_cthickening]
        rw [hline]
      have : pureWZ2HorizontalRotation frameSlope source ∈
          pureWZ2HorizontalRotation frameSlope ''
            Metric.cthickening (6 * delta)
              (tubeAxisLine (family.tube index)) :=
        ⟨source, hthick, rfl⟩
      rwa [himage] at this
    · exact hrotatedBox ⟨source, ⟨index, hsource⟩, rfl⟩

@[simp] theorem pureWZ2RotatePaperShading_union
    (frameSlope : ℝ) {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (hrotatedBox : pureWZ2HorizontalRotation frameSlope '' shading.union ⊆
      Kakeya.Streamlined.axisBox 2 2 2) :
    (pureWZ2RotatePaperShading frameSlope shading hrotatedBox).union =
      pureWZ2HorizontalRotation frameSlope '' shading.union := by
  ext point
  constructor
  · rintro ⟨index, source, hsource, rfl⟩
    exact ⟨source, ⟨index, hsource⟩, rfl⟩
  · rintro ⟨source, ⟨index, hsource⟩, rfl⟩
    exact ⟨index, source, hsource, rfl⟩

theorem pureWZ2RotatePaperShading_mass
    (frameSlope : ℝ) {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (hrotatedBox : pureWZ2HorizontalRotation frameSlope '' shading.union ⊆
      Kakeya.Streamlined.axisBox 2 2 2) :
    (pureWZ2RotatePaperShading frameSlope shading hrotatedBox).mass = shading.mass := by
  apply Finset.sum_congr rfl
  intro index _
  exact pureWZ2HorizontalRotation_volume_image frameSlope
    (shading.measurable_carrier index)

end Kakeya.Assouad

end
