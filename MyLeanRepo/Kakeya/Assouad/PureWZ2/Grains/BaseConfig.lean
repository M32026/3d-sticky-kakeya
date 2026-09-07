import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky

/-!
# Base grain configuration from critical package (Node 4)

Extracts the six structural fields of a grain configuration (family, shading,
line class, cubical shading, cropped extremal, top-level CWA) from the pure
critical package via the Node 3 sticky normalization.

This is the easy part of `prop: grain`; the global and local grain AD bounds
are constructed separately.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The six non-grain fields of a `PureWZ2GrainConfiguration`. -/
structure PureWZ2GrainBaseConfig (sigma outputLoss delta : ℝ) where
  family : Kakeya.Streamlined.TubeFamily delta
  shading : WZ1PaperTubeShading family
  line_class : WZ1PaperIsLineClass family
  cubical : WZ1PaperIsCubicalShading shading
  extremal : WZ2PaperCroppedIsExtremal sigma outputLoss family shading
  top_level_cwa :
    WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-outputLoss))

/-- Extract a base grain configuration from a pure critical package.

Applies the Node 3 sticky normalization to obtain the cropped family, shading,
line class, cubical shading, cropped extremal, and top-level CWA. All six fields
come directly from `PureWZ2CroppedCriticalNormalizationData`.

Also returns the unpacked Node 3 sticky data (`lE`, `hStickyAt`) so that
downstream consumers can derive shading-specific sticky provision for
`normalized.croppedRefined`. -/
theorem pure_wz2_grain_base_config
    (h_sticky : PureWZ2PropStickyStatement)
    (h_subunit : PureWZ2SubunitPackageStatement)
    (h_extraction : PureWZ2CriticalExtractionStatement)
    (sigma : ℝ)
    (hcrit : PureWZ2CriticalPackage sigma)
    (outputLoss delta₀ : ℝ)
    (hloss : 0 < outputLoss)
    (hdelta₀ : 0 < delta₀) :
    ∃ (nE lE : ℕ) (inputLoss delta : ℝ)
      (source : PureWZ2ExtremalConfiguration sigma inputLoss delta)
      (normalized :
        PureWZ2CroppedCriticalNormalizationData
          (outputLoss := outputLoss) source nE)
      (base : PureWZ2GrainBaseConfig sigma outputLoss delta)
      (hStickyAt : PureWZ2CroppedPropStickyAt nE lE),
      0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
      0 < delta ∧ delta ≤ delta₀ := by
  rcases h_sticky h_subunit h_extraction with ⟨capability⟩
  have h_sticky_from_crit : PureWZ2PropStickyFromCriticalStatement :=
    capability.toLegacyFromCritical
  rcases h_sticky_from_crit with
    ⟨nE, lE, hNormAt, hStickyAt, _realizationAt⟩
  have h_norm := hNormAt sigma hcrit outputLoss delta₀ hloss hdelta₀
  rcases h_norm with ⟨inputLoss, delta, hinputLoss, hinputLoss_le,
    hdelta, hdelta_le, source, hnorm⟩
  let normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := outputLoss) source nE := hnorm.some
  let base : PureWZ2GrainBaseConfig sigma outputLoss delta :=
    { family := normalized.croppedFamily
      shading := normalized.croppedRefined
      line_class := normalized.line_class
      cubical := normalized.cropped_cubical
      extremal := normalized.final_extremal
      top_level_cwa := normalized.cropped_top_level_cwa }
  exact ⟨nE, lE, inputLoss, delta, source, normalized, base, hStickyAt,
    hinputLoss, hinputLoss_le, hdelta, hdelta_le⟩

end Kakeya.Assouad
