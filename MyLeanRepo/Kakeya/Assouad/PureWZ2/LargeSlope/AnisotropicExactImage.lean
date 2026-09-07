import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicPaperRetubing

/-!
# Exact affine-image shading before cubical saturation

The induced paper shading used by Proposition 6.5 is a cubical saturation of
the exact affine image.  Local grains must first be transported on the exact
image, where every point has a literal source preimage.  This module records
that intermediate shading without claiming that it is cubical.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- The exact, unsaturated affine-image shading underlying one paper
retubing. -/
def PureWZ2AnisotropicPaperRetubingData.exactShading
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm) :
    WZ1PaperTubeShading
      (anisotropicPaperTargetFamily sourceFamily g c d m center
        targetDelta hcd hm) where
  carrier index := anisotropicCenteredRescalingMap g c d m center ''
    sourceShading.carrier index
  measurable_carrier index := by
    let equiv := anisotropicCenteredRescalingAffineEquiv
      g c d m center hcd hm
    have heq :
        anisotropicCenteredRescalingMap g c d m center ''
            sourceShading.carrier index =
          equiv '' sourceShading.carrier index := by
      ext point
      simp only [Set.mem_image]
      constructor
      · rintro ⟨source, hsource, rfl⟩
        exact ⟨source, hsource,
          anisotropicCenteredRescalingAffineEquiv_apply
            g c d m center hcd hm source⟩
      · rintro ⟨source, hsource, rfl⟩
        exact ⟨source, hsource,
          (anisotropicCenteredRescalingAffineEquiv_apply
            g c d m center hcd hm source).symm⟩
    rw [heq]
    exact equiv.toHomeomorphOfFiniteDimensional.toMeasurableEquiv
      |>.measurableSet_image.mpr (sourceShading.measurable_carrier index)
  subset_body index := raw.exact_image_subset index |>.trans
    (raw.shading.subset_body index)

@[simp] theorem PureWZ2AnisotropicPaperRetubingData.exactShading_carrier
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm) (index) :
    raw.exactShading.carrier index =
      anisotropicCenteredRescalingMap g c d m center ''
        sourceShading.carrier index := rfl

theorem PureWZ2AnisotropicPaperRetubingData.exactShading_union
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm) :
    raw.exactShading.union =
      anisotropicCenteredRescalingMap g c d m center ''
        sourceShading.union := by
  ext point
  constructor
  · rintro ⟨index, source, hsource, rfl⟩
    exact ⟨source, ⟨index, hsource⟩, rfl⟩
  · rintro ⟨source, ⟨index, hsource⟩, rfl⟩
    exact ⟨index, source, hsource, rfl⟩

theorem PureWZ2AnisotropicPaperRetubingData.exactShading_mass
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm) :
    raw.exactShading.mass = ENNReal.ofReal m * sourceShading.mass := by
  change (∑ index, volume
      (anisotropicCenteredRescalingMap g c d m center ''
        sourceShading.carrier index)) =
    ENNReal.ofReal m * ∑ index, volume (sourceShading.carrier index)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  exact volume_image_anisotropicCenteredRescalingMap
    g hcd hm center _ (sourceShading.measurable_carrier index)

theorem PureWZ2AnisotropicPaperRetubingData.exactShading_subshading
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm) :
    ∀ index, raw.exactShading.carrier index ⊆ raw.shading.carrier index :=
  raw.exact_image_subset

end Kakeya.Assouad

end
