import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulClosingArithmetic
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulClosingTransport
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulExtremeCases
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulSanity
import MyLeanRepo.Kakeya.Assouad.WZ1.ClosingHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.CoarseningArithmetic
import MyLeanRepo.Kakeya.Assouad.WZ1.ClosingCoveringTransport
import MyLeanRepo.Kakeya.Assouad.WZ1.KaufmanProjectionApplication

/-!
# Target: faithful Kaufman closing for PDF Lemma 8.13

The output records the actual Kaufman direction and the exact transported
radius and scale before returning the original long-projection conclusion.
The sub-delta branch must use one-dimensional covering coarsening.
-/

namespace Kakeya.Assouad

open scoped ENNReal
attribute [local instance] Classical.propDecidable

theorem wz1_lemma8_13_faithful_closing :
    WZ1Lemma8_13FaithfulClosingStatement := by
  intro epsilon hepsilon hepsilon_lt_one
  rcases wz1Lemma8_13_faithful_closing_numerical epsilon hepsilon hepsilon_lt_one with
    ⟨delta₀, hdelta₀_pos, hdelta₀_one, hnum⟩
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta hdelta hdelta_le input affine kaufman
  have hdeltaOne : delta ≤ 1 := hdelta_le.trans hdelta₀_one
  rcases wz1_lemma8_13_faithful_kaufman_projection kaufman with
    ⟨direction, hdirection, hfiberCovering⟩
  set angularScale := wz1Lemma8_13FaithfulAngularScale input with has_def
  have has_pos : 0 < angularScale := affine.angularScale_pos
  have hscale_upper : angularScale ≤ Real.rpow delta epsilon :=
    (wz1Lemma8_13_angularScale_lt_rpow input hdelta).le
  have hnumerical_at_scale :=
    hnum delta hdelta hdelta_le angularScale has_pos hscale_upper
  have hcovering :=
    closing_covering_transport
      hepsilon hepsilon_lt_one direction hdirection hdeltaOne
      hfiberCovering hnumerical_at_scale
  have hD_pos : 0 < dist (kaufman.firstEndpoint direction) (kaufman.secondEndpoint direction) := by
    have haspect_pos : 0 < wz1Lemma8_13FaithfulAspect input := by
      dsimp only [wz1Lemma8_13FaithfulAspect]
      exact zero_lt_one.trans_le (le_max_left _ _)
    have hpos : 0 < 1 / (4 * wz1Lemma8_13FaithfulAspect input) := by positivity
    have h : 1 / (4 * wz1Lemma8_13FaithfulAspect input) ≤
        dist (kaufman.firstEndpoint direction) (kaufman.secondEndpoint direction) :=
      kaufman.endpointDistance_lower direction hdirection
    linarith
  refine ⟨{
    direction := direction,
    direction_mem := hdirection,
    normalizedFiberCovering := hfiberCovering,
    endpointDistance_eq := rfl,
    endpointDistance_lower := kaufman.endpointDistance_lower direction hdirection,
    endpointDistance_upper := kaufman.endpointDistance_upper direction hdirection,
    transportedRadius_eq := rfl,
    transportedScale_eq := rfl,
    rho_eq := rfl,
    rho_lower := le_max_left _ _,
    rho_upper := closing_rho_upper direction hdirection hdeltaOne,
    transportedRadius_pos := by
      have hnorm_pos : 0 < wz1Lemma8_13FaithfulNormalizationWidth input :=
        affine.normalizationWidth_pos
      positivity,
    long_radius := closing_long_radius direction hdirection hdeltaOne hepsilon hepsilon_lt_one,
    covering := hcovering
  }⟩

end Kakeya.Assouad
