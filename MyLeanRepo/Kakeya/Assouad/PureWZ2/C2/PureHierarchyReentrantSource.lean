import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.QuantitativeConfiguration
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropStickyReentry

/-! # Re-entry-preserving grain source -/

noncomputable section

namespace Kakeya.Assouad

/-- One grain configuration together with an exact ordinary/cropped re-entry
certificate on its literal family and shading. -/
structure PureWZ2ReentrantGrainSource
    (sigma loss delta : ℝ) (normalizationExponent : ℕ) where
  ordinaryLoss : ℝ
  grain : PureWZ2QuantitativeGrainConfiguration sigma loss delta
  reentry : PureWZ2PropStickyReentryData
    (sigma := sigma) grain.shading normalizationExponent ordinaryLoss loss
  ordinary_axial_window_eighth :
    ∀ index point,
      point ∈
          reentry.geometry.frame ''
            reentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8

namespace PureWZ2PropStickyReentryData

/-- Change only the bookkeeping exponent of an exact re-entry geometry when
the new refinement fraction is no larger.  Every geometric witness and both
losses remain definitionally unchanged. -/
noncomputable def reindexNormalizationExponent
    {sigma delta : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {sourceLoss normalizationLoss : ℝ}
    {firstExponent : ℕ}
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading firstExponent sourceLoss
        normalizationLoss)
    (nextExponent : ℕ)
    (fraction_le :
      wz2PaperPureRefinementFraction delta nextExponent ≤
        wz2PaperPureRefinementFraction delta firstExponent) :
    PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading nextExponent sourceLoss
        normalizationLoss where
  sourceLoss_pos := reentry.sourceLoss_pos
  normalizationLoss_pos := reentry.normalizationLoss_pos
  sourceLoss_le_half := reentry.sourceLoss_le_half
  ordinarySource := reentry.ordinarySource
  geometry := {
    selected := reentry.geometry.selected
    selected_nonempty := reentry.geometry.selected_nonempty
    ordinaryRefined := reentry.geometry.ordinaryRefined
    ordinary_subshading := reentry.geometry.ordinary_subshading
    retained_mass := by
      calc
        wz2PaperPureRefinementFraction delta nextExponent *
              reentry.ordinarySource.shading.mass ≤
            wz2PaperPureRefinementFraction delta firstExponent *
              reentry.ordinarySource.shading.mass := by
          simpa [mul_comm] using
            (mul_le_mul_left fraction_le
              reentry.ordinarySource.shading.mass)
        _ ≤ reentry.geometry.ordinaryRefined.mass :=
          reentry.geometry.retained_mass
    frame := reentry.geometry.frame
    indexEquiv := reentry.geometry.indexEquiv
    ordinary_carrier_image_eq :=
      reentry.geometry.ordinary_carrier_image_eq
    ordinaryDensity := reentry.geometry.ordinaryDensity
    ordinaryDensity_pos := reentry.geometry.ordinaryDensity_pos
    ordinary_per_tube := reentry.geometry.ordinary_per_tube
    ordinary_axial_window := reentry.geometry.ordinary_axial_window
    cropped_carrier_eq_dense_cubicalization :=
      reentry.geometry.cropped_carrier_eq_dense_cubicalization
    cropped_cubical := reentry.geometry.cropped_cubical
    line_class := reentry.geometry.line_class
    ordinary_cell_containment :=
      reentry.geometry.ordinary_cell_containment
    ordinary_bounded_base := reentry.geometry.ordinary_bounded_base
  }
  ordinary_density_budget := reentry.ordinary_density_budget
  cropped_top_level_cwa := reentry.cropped_top_level_cwa
  cropped_extremal := reentry.cropped_extremal

/-- Specialize exponent reindexing to the production M9 exponent zero. -/
noncomputable def reindexZeroNormalizationExponent
    {sigma delta : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {sourceLoss normalizationLoss : ℝ}
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading 0 sourceLoss normalizationLoss)
    (nextExponent : ℕ)
    (fraction_le_one :
      wz2PaperPureRefinementFraction delta nextExponent ≤ 1) :
    PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading nextExponent sourceLoss
        normalizationLoss :=
  reentry.reindexNormalizationExponent nextExponent (by
    simpa [wz2PaperPureRefinementFraction] using fraction_le_one)

end PureWZ2PropStickyReentryData

end Kakeya.Assouad

end
