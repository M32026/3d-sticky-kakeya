import MyLeanRepo.Kakeya.Assouad.WZ1.Statements

/-!
# Weak plane maps on a supplied extremal configuration

WZ1 Proposition 9 applies Lemma 11 to the particular unit-rescaled fiber
selected in Step 1.  The existing existential weak-plane-map conclusion is
not sufficient: it may choose an unrelated extremal family.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Dependent WZ1 Lemma 11 output on a supplied fine configuration. -/
structure WZ1SuppliedWeakPlaneMapData
    {delta sigma outputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F) where
  shading : Kakeya.Streamlined.TubeShading F
  subshading : IsSubshading shading Y
  extremal : WZ1ExtremalPair sigma outputLoss F U shading
  planeMap :
    WZ1WeakPlaneMapData shading
      (Real.rpow delta (sigma / 2))

/--
Construct the WZ1 Lemma 11 weak plane map on an arbitrary supplied extremal
configuration.

The source loss is selected before the scale threshold.  The output remains
on the supplied indexed family and coherent uniform structure, and its
incidence scale is the paper's `delta^(sigma/2)`.
-/
def WZ1SuppliedWeakPlaneMapConclusion : Prop :=
  ∀ sigma outputLoss : ℝ,
    0 < sigma → sigma < 1 → 0 < outputLoss →
    HasCriticalVolumeFloor sigma →
      ∃ inputLoss delta₀ : ℝ,
        0 < inputLoss ∧
        inputLoss < outputLoss ∧
        inputLoss < sigma / 2 ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ,
          0 < delta → delta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
              ∀ Y : Kakeya.Streamlined.TubeShading F,
                WZ1ExtremalPair sigma inputLoss F U Y →
                  Nonempty
                    (WZ1SuppliedWeakPlaneMapData
                      (sigma := sigma)
                      (outputLoss := outputLoss)
                      U Y)

/--
Prove the dependent Lemma 11 conclusion using the Proposition 5 balanced-cover
producer.  The CV broad-mass and coarse direction-packing inputs are already
closed repository theorems.
-/
def WZ1SuppliedWeakPlaneMapStatement : Prop :=
  WZ1BalancedCoverStatement →
    WZ1SuppliedWeakPlaneMapConclusion

end Kakeya.Assouad
