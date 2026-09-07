import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Node6FixedScaleOutput
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ConfigurationRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSubfamilyZeroExtension

/-!
# Put a Node-6 fixed-scale refinement back on its C2 source family

The fixed-scale Proposition-6.2 output is indexed by a genuine subfamily of
the C2 source family.  This module extends its final fine shading by zero to
the source family and records the resulting same-family C2 configuration.

The extremal fields are rebuilt directly from the fixed-scale output.  In
particular, the volume bound comes from `fine_volume_upper`, and the density
bound comes from `retained_mass` together with the source density and one
explicit scalar absorption.  No full Proposition-sticky output is used.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- Honest scalar data, together with the zero extension, needed to turn a
Node-6 fixed-scale output into a same-family C2 configuration. -/
structure PureWZ2Node6FixedC2ZeroExtensionData
    {sigma sourceLoss fixedLoss targetLoss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta)
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := fixedLoss)
      cfg.shading rho logExponent) where
  targetLoss_nonneg : 0 ≤ targetLoss
  source_loss_le : sourceLoss ≤ targetLoss
  fixed_loss_le : fixedLoss ≤ targetLoss
  density_absorption :
    Kakeya.realRpowENN delta targetLoss ≤
      wz2PaperPureRefinementFraction delta logExponent *
        Kakeya.realRpowENN delta sourceLoss
  zeroExtension :
    WZ2PaperSubfamilyZeroExtensionData data.selected data.refined

namespace PureWZ2Node6FixedC2ZeroExtensionData

/-- The zero-extended fixed-scale refinement is a genuine C2 configuration
on the original source family. -/
def configuration
    {sigma sourceLoss fixedLoss targetLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {fixed : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := fixedLoss)
      cfg.shading rho logExponent}
    (data : PureWZ2Node6FixedC2ZeroExtensionData
      (targetLoss := targetLoss) cfg fixed) :
    PureWZ2C2GrainConfiguration sigma targetLoss delta := by
  let shading := data.zeroExtension.ambientShading
  have hsub : ∀ index, shading.carrier index ⊆
      cfg.shading.carrier index := by
    intro ambient point hpoint
    rcases data.zeroExtension.carrier_support ambient point hpoint with
      ⟨index, rfl, hrefined⟩
    exact fixed.subshading index hrefined
  have hconstant : Kakeya.realRpowENN delta (-sourceLoss) ≤
      Kakeya.realRpowENN delta (-targetLoss) :=
    realRpowENN_antitone cfg.extremal.delta_pos
      cfg.extremal.delta_le_one (by linarith [data.source_loss_le])
  have hconstantOne :
      1 ≤ Kakeya.realRpowENN delta (-targetLoss) := by
    rw [Kakeya.realRpowENN, ENNReal.one_le_ofReal]
    have hpow := Real.rpow_le_rpow_of_exponent_ge
      cfg.extremal.delta_pos cfg.extremal.delta_le_one
      (show -targetLoss ≤ (0 : ℝ) by
        linarith [data.targetLoss_nonneg])
    simpa using hpow
  have hconstantTop :
      Kakeya.realRpowENN delta (-targetLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have hdense : shading.IsLambdaDense
      (Kakeya.realRpowENN delta targetLoss) := by
    calc
      Kakeya.realRpowENN delta targetLoss *
            (wz1PaperBodyFamily cfg.family).mass ≤
          (wz2PaperPureRefinementFraction delta logExponent *
              Kakeya.realRpowENN delta sourceLoss) *
            (wz1PaperBodyFamily cfg.family).mass :=
        mul_le_mul_left data.density_absorption _
      _ = wz2PaperPureRefinementFraction delta logExponent *
          (Kakeya.realRpowENN delta sourceLoss *
            (wz1PaperBodyFamily cfg.family).mass) := by ring
      _ ≤ wz2PaperPureRefinementFraction delta logExponent *
          cfg.shading.mass :=
        mul_le_mul_right cfg.extremal.dense _
      _ ≤ fixed.refined.mass := fixed.retained_mass
      _ = shading.mass := data.zeroExtension.mass_eq.symm
  have hextremal : WZ2PaperCroppedIsExtremal
      sigma targetLoss cfg.family shading :=
    { delta_pos := cfg.extremal.delta_pos
      delta_le_one := cfg.extremal.delta_le_one
      nonempty := cfg.extremal.nonempty
      cwa_nearby_scales :=
        cfg.extremal.cwa_nearby_scales.mono hconstant
          (by simp [Kakeya.realRpowENN])
      cubical := data.zeroExtension.cubical fixed.refined_cubical
      dense := hdense
      volume_upper := by
        rw [data.zeroExtension.union_eq]
        exact fixed.fine_volume_upper.trans <|
          pure_wz2_rpowENN_antitone cfg.extremal.delta_pos
            cfg.extremal.delta_le_one (by
              linarith [data.fixed_loss_le]) }
  exact
    { family := cfg.family
      shading := shading
      line_class := cfg.line_class
      bounded_base := cfg.bounded_base
      cubical := hextremal.cubical
      extremal := hextremal
      top_level_cwa := cfg.top_level_cwa.weaken_constant hconstant
      globalGrains :=
        (cfg.globalGrains.weaken_constant hconstant
          hconstantOne hconstantTop).restrict_same_constant hsub
      localGrains :=
        (cfg.localGrains.weaken_constant hconstant
          hconstantTop).restrict hsub }

@[simp] theorem configuration_family
    {sigma sourceLoss fixedLoss targetLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {fixed : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := fixedLoss)
      cfg.shading rho logExponent}
    (data : PureWZ2Node6FixedC2ZeroExtensionData
      (targetLoss := targetLoss) cfg fixed) :
    data.configuration.family = cfg.family := rfl

@[simp] theorem configuration_shading
    {sigma sourceLoss fixedLoss targetLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {fixed : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := fixedLoss)
      cfg.shading rho logExponent}
    (data : PureWZ2Node6FixedC2ZeroExtensionData
      (targetLoss := targetLoss) cfg fixed) :
    data.configuration.shading =
      data.zeroExtension.ambientShading := rfl

@[simp] theorem configuration_union
    {sigma sourceLoss fixedLoss targetLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {fixed : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := fixedLoss)
      cfg.shading rho logExponent}
    (data : PureWZ2Node6FixedC2ZeroExtensionData
      (targetLoss := targetLoss) cfg fixed) :
    data.configuration.shading.union = fixed.refined.union := by
  exact data.zeroExtension.union_eq

@[simp] theorem configuration_mass
    {sigma sourceLoss fixedLoss targetLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {fixed : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := fixedLoss)
      cfg.shading rho logExponent}
    (data : PureWZ2Node6FixedC2ZeroExtensionData
      (targetLoss := targetLoss) cfg fixed) :
    data.configuration.shading.mass = fixed.refined.mass := by
  exact data.zeroExtension.mass_eq

/-- The zero-extended fixed refinement is pointwise a subshading of the
original C2 source.  This is the transport used when an earlier fixed-scale
call supplies a global multiplicity cap for later Node-6 refinements. -/
theorem configuration_pointMultiplicity_le_source
    {sigma sourceLoss fixedLoss targetLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {fixed : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := fixedLoss)
      cfg.shading rho logExponent}
    (data : PureWZ2Node6FixedC2ZeroExtensionData
      (targetLoss := targetLoss) cfg fixed)
    (point : Point3) :
    data.configuration.shading.pointMultiplicity point ≤
      cfg.shading.pointMultiplicity point := by
  apply paperSubshading_pointMultiplicity_le
  intro ambient p hp
  rcases data.zeroExtension.carrier_support ambient p hp with
    ⟨index, rfl, hrefined⟩
  exact fixed.subshading index hrefined

@[simp] theorem configuration_slope
    {sigma sourceLoss fixedLoss targetLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {fixed : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := fixedLoss)
      cfg.shading rho logExponent}
    (data : PureWZ2Node6FixedC2ZeroExtensionData
      (targetLoss := targetLoss) cfg fixed) :
    data.configuration.globalGrains.slope =
      cfg.globalGrains.slope := rfl

end PureWZ2Node6FixedC2ZeroExtensionData

namespace PureWZ2Node6FixedScaleOutput

/-- Construct the zero extension and its same-family C2 configuration from a
fixed-scale Node-6 output and the explicit scalar absorptions. -/
theorem zeroExtendC2
    {sigma sourceLoss fixedLoss targetLoss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta)
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := fixedLoss)
      cfg.shading rho logExponent)
    (targetLoss_nonneg : 0 ≤ targetLoss)
    (source_loss_le : sourceLoss ≤ targetLoss)
    (fixed_loss_le : fixedLoss ≤ targetLoss)
    (density_absorption :
      Kakeya.realRpowENN delta targetLoss ≤
        wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta sourceLoss) :
    Nonempty (PureWZ2Node6FixedC2ZeroExtensionData
      (targetLoss := targetLoss) cfg data) := by
  rcases wz2_paper_subfamily_zero_extension
      data.selected data.refined with ⟨zeroExtension⟩
  exact ⟨{
    targetLoss_nonneg := targetLoss_nonneg
    source_loss_le := source_loss_le
    fixed_loss_le := fixed_loss_le
    density_absorption := density_absorption
    zeroExtension := zeroExtension
  }⟩

end PureWZ2Node6FixedScaleOutput

end Kakeya.Assouad

end
