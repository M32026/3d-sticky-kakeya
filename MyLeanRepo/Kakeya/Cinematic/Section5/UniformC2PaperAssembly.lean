import MyLeanRepo.Kakeya.Cinematic.Section5.UniformC2FinalExport
import MyLeanRepo.Kakeya.Cinematic.Section5.UniformC2Globalization
import MyLeanRepo.Kakeya.Cinematic.Section5.UniformC2LocalIntegral

/-!
# Uniform absolute-C2 PYZ assembly

This theorem records the complete remaining dependency chain from faithful
centered Taylor globalization to the WZ2-facing export.  All steps after the
full-interval level-set estimate are closed analytic reductions.
-/

namespace Kakeya.Cinematic

theorem wz2_uniformC2_input_from_taylor_globalization
    (hCover : CenteredSixteenthIntervalCoverStatement)
    (hGraph : HorizontalGraphNeighborhoodVolumeStatement)
    (hStub : HorizontalStubMultiplicityVolumeStatement)
    (hStubAbsorption : HorizontalStubLevelSetAbsorptionStatement)
    (hQuadratic : CenteredTaylorQuadraticCinematicTransportStatement)
    (hFinite : CenteredTaylorUniformFiniteGraphTransportStatement)
    (hShort : WZ2UniformC2ShortCurveLevelSetInput)
    (hMultiplicity : MultiplicityLevelSelectionStatement)
    (hRestricted : RestrictedWeakTypeReductionStatement) :
    WZ2UniformC2Input := by
  apply wz2_uniformC2_input_of_local
  apply uniformC2_local_integral_of_level_set hMultiplicity hRestricted
  exact wz2_uniformC2_local_level_set_from_taylor_globalization
    hCover hGraph hStub hStubAbsorption
    hQuadratic hFinite hShort

end Kakeya.Cinematic
