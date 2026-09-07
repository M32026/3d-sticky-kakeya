import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Node6FixedC2ZeroExtension
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.RotatedProjectedNormal

/-! # Minimal Node-6 frame-normal compatibility interface -/

noncomputable section

namespace Kakeya.Assouad

/-- The exact pointwise normal certificate consumed by the power-scale
Lemma-6.6 prism construction. -/
def PureWZ2FrameNormalCompatibility
    {sigma loss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta) : Prop :=
  ∀ (frameSlope : ℝ)
      (source : {point : Point3 // point ∈ cfg.shading.union}),
    |cfg.globalGrains.slope (source.1 2) - frameSlope| ≤ 1 / 50 →
      (1 / 16 : ℝ) ≤
        ‖pureWZ2FrameProjectedNormal frameSlope
          (cfg.localGrains.planeMap source)‖

/-- The construction-level local/global certificate implies the exact
pointwise certificate used in Lemma 31. -/
theorem PureWZ2LocalGlobalCompatibility.frameNormalCompatibility
    {sigma loss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma loss delta}
    (compatibility : PureWZ2LocalGlobalCompatibility cfg) :
    PureWZ2FrameNormalCompatibility cfg := by
  intro frameSlope source hframe
  exact pureWZ2_frameProjectedNormal_norm_lower
    cfg compatibility source (by linarith)

/-- Zero extension of a fixed-scale refinement preserves frame-normal
compatibility, because both the slope and the restricted local plane map come
from the same source configuration. -/
theorem PureWZ2Node6FixedC2ZeroExtensionData.configuration_frameNormalCompatibility
    {sigma sourceLoss fixedLoss targetLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {fixed : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := fixedLoss)
      cfg.shading rho logExponent}
    (zeroData : PureWZ2Node6FixedC2ZeroExtensionData
      (targetLoss := targetLoss) cfg fixed)
    (compatibility : PureWZ2FrameNormalCompatibility cfg) :
    PureWZ2FrameNormalCompatibility
      (zeroData.configuration (targetLoss := targetLoss)) := by
  intro frameSlope point hframe
  have hpointRefined : (point : Point3) ∈ fixed.refined.union := by
    rw [← zeroData.configuration_union]
    exact point.property
  rcases hpointRefined with ⟨index, hindex⟩
  let source : {point : Point3 // point ∈ cfg.shading.union} :=
    ⟨point, ⟨fixed.selected.embedding index, fixed.subshading index hindex⟩⟩
  have hframe' :
      |cfg.globalGrains.slope (point.1 2) - frameSlope| ≤ 1 / 50 := by
    rw [← zeroData.configuration_slope]
    exact hframe
  have h := compatibility frameSlope source hframe'
  simpa [PureWZ2Node6FixedC2ZeroExtensionData.configuration, source,
    PureWZ2LocalGrainData.weaken_constant] using h

end Kakeya.Assouad

end
