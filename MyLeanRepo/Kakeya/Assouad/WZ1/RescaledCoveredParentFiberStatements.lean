import MyLeanRepo.Kakeya.Assouad.WZ1.UnitRescaling
import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions

/-!
# One-parent unit-rescaled Lemma 6

This module freezes the shared mathematical core of WZ1 Proposition 5 Step 2
and its later item-(ii) consumer.  It deliberately does not depend on an
already completed `WZ1BalancedCoverData`.

Starting from one quantitatively dense parent fiber, the output keeps a
mass-retaining source subshading, proves the desired source fiber-point cap,
and constructs the normalized rediscretized target configuration to which the
critical volume floor is applied.  The indexed source pieces preserve the
exact parent provenance through rediscretization.
-/

noncomputable section

namespace Kakeya.Assouad

/--
The paper's one-parent `rescaledCoveredTube` output.

The target family is a rediscretization of a retained source parent fiber,
not an unrelated extremal family.  A source tube may contribute finitely many
target pieces after its affine image is covered by normalized unit segments.
`sourcePiece` records the source set assigned to each target index and
supplies both coverage and two-sided image control.
-/
structure WZ1RescaledCoveredParentFiberData
    {delta sigma outputLoss retentionLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (parent : Fin (U.coarse rho).card)
    (hrho : 0 < rho.1) where
  sourceShading : Kakeya.Streamlined.TubeShading F
  source_subshading :
    IsSubshading sourceShading Y
  source_supported_on_parent :
    ∀ i p, p ∈ sourceShading.carrier i →
      (U.cover rho).parent i = parent
  retained_source_mass :
    Kakeya.realRpowENN delta retentionLoss *
        (U.cover rho).toFactoring.fiberShadedMass Y parent ≤
      sourceShading.mass
  source_fiber_cap :
    ∀ p,
      ((U.cover rho).toFactoring.fiberPointMultiplicity
          sourceShading parent p : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho.1)
          (-sigma - outputLoss)
  distinguished : Fin F.card
  distinguished_parent :
    (U.cover rho).parent distinguished = parent
  distinguished_nonempty :
    (sourceShading.carrier distinguished).Nonempty
  targetFamily :
    Kakeya.Streamlined.TubeFamily (delta / rho.1)
  targetUniform :
    Kakeya.Streamlined.UniformTubeStructure targetFamily
  targetShading :
    Kakeya.Streamlined.TubeShading targetFamily
  target_extremal :
    WZ1ExtremalPair sigma outputLoss
      targetFamily targetUniform targetShading
  target_vertical :
    IsInVerticalChart targetFamily
  target_uniform_vertical :
    ∀ scale,
      IsInVerticalChart (targetUniform.coarse scale)
  targetMultiplicity : ℕ
  targetMultiplicity_pos : 0 < targetMultiplicity
  target_constant_multiplicity :
    targetShading.HasConstantMultiplicity
      targetMultiplicity (2 * targetMultiplicity)
  target_multiplicity_upper :
    (targetMultiplicity : ENNReal) ≤
      Kakeya.realRpowENN (delta / rho.1)
        (-sigma - outputLoss)
  sourceIndex : Fin targetFamily.card → Fin F.card
  sourceIndex_parent :
    ∀ k, (U.cover rho).parent (sourceIndex k) = parent
  target_axis :
    ∀ k,
      tubeAxisLine (targetFamily.tube k) =
        wz1AnchoredUnitRescalingMap
            (F.tube distinguished) rho.1 hrho ''
          tubeAxisLine (F.tube (sourceIndex k))
  sourcePiece : Fin targetFamily.card → Set Point3
  sourcePiece_measurable :
    ∀ k, MeasurableSet (sourcePiece k)
  sourcePiece_subset :
    ∀ k,
      sourcePiece k ⊆
        sourceShading.carrier (sourceIndex k)
  sourcePiece_cover :
    ∀ i,
      sourceShading.carrier i ⊆
        ⋃ k : Fin targetFamily.card,
          if sourceIndex k = i then sourcePiece k else ∅
  pullback_multiplicity_le :
    ∀ p,
      (sourceShading.pointMultiplicity p : ENNReal) ≤
        (targetShading.pointMultiplicity
          (wz1AnchoredUnitRescalingMap
            (F.tube distinguished) rho.1 hrho p) : ENNReal)
  source_image_subset :
    ∀ k,
      wz1AnchoredUnitRescalingMap
          (F.tube distinguished) rho.1 hrho ''
        sourcePiece k ⊆
          targetShading.carrier k
  target_near_source_image :
    ∀ k,
      targetShading.carrier k ⊆
        Metric.cthickening (delta / rho.1)
          (wz1AnchoredUnitRescalingMap
              (F.tube distinguished) rho.1 hrho ''
            sourcePiece k)

/--
WZ1 Lemma 6 on one quantitatively dense coarse-parent fiber.

The producer chooses a stronger global input loss.  The parent-mass premise is
the output of the preceding parent-fiber balancing step:
`delta^inputLoss * fiberMass parent` is a lower bound for the total shaded
mass in this parent.  The conclusion retains a power fraction of that exact
fiber shaded mass,
constructs the normalized target UTS at radius `delta / rho`, applies the
critical floor there, and pulls the resulting multiplicity cap back to the
source parent.
-/
def WZ1RescaledCoveredParentFiberStatement : Prop :=
  ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
    HasWZ1CriticalVolumeFloor sigma →
      ∀ outputLoss retentionLoss scaleLoss : ℝ,
        0 < outputLoss →
        0 < retentionLoss → retentionLoss < outputLoss →
        0 < scaleLoss →
          ∃ inputLoss delta₀ : ℝ,
            0 < inputLoss ∧ inputLoss < retentionLoss ∧
            0 < delta₀ ∧ delta₀ ≤ 1 ∧
            ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
              ∀ F : Kakeya.Streamlined.TubeFamily delta,
                ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
                  ∀ Y : Kakeya.Streamlined.TubeShading F,
                    ∀ hExt : WZ1ExtremalPair sigma inputLoss F U Y,
                    ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
                      Real.rpow delta (1 - scaleLoss) ≤ rho.1 →
                      rho.1 ≤ Real.rpow delta scaleLoss →
                        ∀ parent : Fin (U.coarse rho).card,
                          Kakeya.realRpowENN delta inputLoss *
                              (U.cover rho).toFactoring.fiberMass parent ≤
                            (U.cover rho).toFactoring.fiberShadedMass
                              Y parent →
                          Nonempty
                            (WZ1RescaledCoveredParentFiberData
                              (sigma := sigma)
                              (outputLoss := outputLoss)
                              (retentionLoss := retentionLoss)
                              U Y rho parent
                              (lt_of_lt_of_le hExt.1 rho.2.1))

end Kakeya.Assouad
