import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SubfamilyGrainConfigurationExtension
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PolylogAbsorption
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12CroppedExtremal

/-!
# Extremality of a retained sticky zero-extension

A Node-3 sticky output retains a fixed polylogarithmic fraction of an ambient
extremal shading.  After spending an explicit positive loss gap, its refined
selected-family shading, zero-extended back to the ambient family, is itself a
cropped extremal shading.  This is a quantitative derivation; no arbitrary
subshading inheritance of nearby-scale CWA or extremality is asserted.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- A retained sticky refinement becomes genuinely extremal after paying a
power which dominates the explicit polylogarithmic retention loss. -/
theorem sticky_zero_extension_extremal
    {delta sigma sourceLoss stickyLoss targetLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss family sourceShading)
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (hsourceTarget : sourceLoss ≤ targetLoss)
    (hretentionPower :
      Kakeya.realRpowENN delta targetLoss ≤
        wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta sourceLoss) :
    WZ2PaperCroppedIsExtremal sigma targetLoss family
      (extendShading sticky.selected sticky.refined) := by
  let weakened := sourceExtremal.mono_loss hsourceTarget
  have hunion :
      (extendShading sticky.selected sticky.refined).union ⊆
        sourceShading.union := by
    intro point hpoint
    rw [extendShading_union] at hpoint
    rcases hpoint with ⟨index, hindex⟩
    exact ⟨sticky.selected.embedding index, sticky.subshading index hindex⟩
  have hdense :
      (extendShading sticky.selected sticky.refined).IsLambdaDense
        (Kakeya.realRpowENN delta targetLoss) := by
    calc
      Kakeya.realRpowENN delta targetLoss *
          (wz1PaperBodyFamily family).mass ≤
        (wz2PaperPureRefinementFraction delta logExponent *
            Kakeya.realRpowENN delta sourceLoss) *
          (wz1PaperBodyFamily family).mass := by gcongr
      _ = wz2PaperPureRefinementFraction delta logExponent *
          (Kakeya.realRpowENN delta sourceLoss *
            (wz1PaperBodyFamily family).mass) := by ring
      _ ≤ wz2PaperPureRefinementFraction delta logExponent *
          sourceShading.mass :=
        mul_le_mul_left' sourceExtremal.dense
          (wz2PaperPureRefinementFraction delta logExponent)
      _ ≤ sticky.refined.mass := sticky.retained_mass
      _ = (extendShading sticky.selected sticky.refined).mass :=
        (extendShading_mass sticky.selected sticky.refined).symm
  exact {
    delta_pos := weakened.delta_pos
    delta_le_one := weakened.delta_le_one
    nonempty := weakened.nonempty
    cwa_nearby_scales := weakened.cwa_nearby_scales
    cubical := Kakeya.Assouad.extendShading_cubical
      sticky.selected sticky.refined_cubical
    dense := hdense
    volume_upper := (measure_mono hunion).trans weakened.volume_upper
  }

end Kakeya.Assouad.PureWZ2

end
