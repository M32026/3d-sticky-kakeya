import MyLeanRepo.Kakeya.Assouad.PureWZ2.SmallTwistedProjectionVolumeBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CriticalExtraction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.TwistedProjection

/-!
# Node 7 first conjunct: small twisted projection from critical package

The concrete Node-6 terminal freezes the dynamic slope-offset cost before
runtime and stores the paper's immediate twisted-projection consequence on
the same family, shading, and slope.  This assembly only packages that
certificate; in particular, it does not assume `slope 0 = 0`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace Kakeya.Assouad

/-- First conjunct of Node 7, preserving the exact Node-6 configuration. -/
theorem pure_wz2_node7_from_critical
    (h_subunit : PureWZ2SubunitPackageStatement)
    (h_critical : PureWZ2CriticalExtractionStatement)
    (h_propsticky : PureWZ2PropStickyStatement)
    (h_grains : PureWZ2GrainsStatement)
    (h_c2grains : PureWZ2C2GrainsStatement)
    (h_largeslope : PureWZ2LargeSlopeStatement) :
    PureWZ2SmallTwistedProjectionFromCriticalStatement := by
  intro sigma critical outputLoss scaleCeiling
    houtputLoss hscaleCeiling
  let deltaCeiling := min scaleCeiling (1 / 2 : ℝ)
  have hdeltaCeiling : 0 < deltaCeiling := by
    dsimp only [deltaCeiling]
    positivity
  rcases h_largeslope h_subunit h_critical h_propsticky h_grains h_c2grains
      sigma critical outputLoss deltaCeiling houtputLoss hdeltaCeiling with
    ⟨delta, hdelta, hdeltaCeiling', ⟨cfg⟩⟩
  have hdeltaScale : delta ≤ scaleCeiling :=
    hdeltaCeiling'.trans (min_le_left _ _)
  have hdeltaOne : delta < 1 := by
    calc
      delta ≤ deltaCeiling := hdeltaCeiling'
      _ ≤ 1 / 2 := min_le_right _ _
      _ < 1 := by norm_num
  let data : PureWZ2SmallTwistedProjectionData sigma outputLoss delta :=
    { family := cfg.family
      family_nonempty := cfg.extremal.nonempty
      line_class := cfg.line_class
      convex_wolff := cfg.top_level_cwa
      shading := cfg.shading
      dense := cfg.extremal.dense
      slope := cfg.slope
      slope_nonsingular := cfg.slope_nonsingular
      projection_upper := cfg.projection_upper }
  exact ⟨delta, hdelta, hdeltaScale, hdeltaOne, ⟨data⟩⟩

end Kakeya.Assouad

end
