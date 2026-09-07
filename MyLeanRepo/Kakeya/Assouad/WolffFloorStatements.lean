import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.AssertionD

/-!
# Assertion D input boundary for the WZ2 Wolff floor

The hairbrush theorem is stated for finite sets of tubes satisfying both
Katz--Tao convex and Frostman slab Wolff bounds.  WZ2 starts from an indexed
uniform tube structure with every-scale fiber Frostman control.  The
refinement below is the exact GWZ-owned bridge between those models.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Select a same-configuration tube subfamily and shading to which Assertion D
applies.

The selected finite-set model retains enough indexed cardinality for the
`sigma = 1/2` lower-bound algebra, and its shaded union stays inside the
original indexed shaded union.  The requested Assertion D error exponent is
fixed before the original configuration, while the input uniformity exponent
and scale threshold may depend on it and on the requested cardinality loss.
-/
def AssertionDAdmissibleRefinementStatement : Prop :=
  ∀ cardLoss assertionEta : ℝ,
    0 < cardLoss → 0 < assertionEta →
      ∃ inputEta delta₀ : ℝ,
        0 < inputEta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            F.Nonempty →
            F.IsInUnitBall →
            F.IsEssentiallyDistinct →
            ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
              U.uniformity ≤
                  Kakeya.realRpowENN delta (-inputEta) →
              U.IsFrostmanAtEveryScale
                  (Kakeya.realRpowENN delta (-inputEta)) →
              ∀ Y : Kakeya.Streamlined.TubeShading F,
                Y.IsLambdaDense
                    (Kakeya.realRpowENN delta inputEta) →
                ∃ G : Kakeya.TubeFamily delta,
                  ∃ source :
                      ∀ T : Kakeya.DeltaTube delta,
                        T ∈ G → Fin F.card,
                  ∃ Z : Kakeya.Shading G,
                    G.IsInUnitBall ∧
                    G.IsEssentiallyDistinct ∧
                    (∀ T, ∀ hT : T ∈ G,
                      F.tube (source T hT) = T) ∧
                    (∀ T, ∀ hT : T ∈ G,
                      Z.carrier T ⊆ Y.carrier (source T hT)) ∧
                    Z.IsLambdaDense
                      (Kakeya.realRpowENN delta assertionEta) ∧
                    Kakeya.KatzTaoConvexWolffBound G
                      (Real.rpow delta (-assertionEta)) ∧
                    Kakeya.FrostmanSlabWolffBound G
                      (Real.rpow delta (-assertionEta)) ∧
                    Kakeya.realRpowENN delta (-2 + cardLoss) ≤
                      G.enncard

/--
Apply the proved hairbrush theorem to the admissible refinement, then absorb
the retained-cardinality, tube-volume, and fixed-constant losses to obtain the
WZ2-facing `delta^(1/2 + epsilon)` volume floor.
-/
def WolffVolumeFloorFromAssertionDRefinementStatement : Prop :=
  Kakeya.AssertionD (1 / 2) 0 →
    AssertionDAdmissibleRefinementStatement →
      WolffVolumeFloorInput

end Kakeya.Assouad
