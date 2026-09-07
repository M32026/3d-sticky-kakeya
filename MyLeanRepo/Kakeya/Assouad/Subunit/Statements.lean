import MyLeanRepo.Kakeya.Assouad.WolffFloorStatements
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement

/-!
# Subunit admissible-ceiling refinement statements

These propositions isolate the non-circular route from WZ2's normalized
every-scale Frostman model to the hypotheses of the shaded Wolff hairbrush
estimate.

The probabilistic leaf is formulated in the indexed `Streamlined` model.  The
second leaf performs only the deterministic conversion to the finite-set
`AssertionD` model.  The final assembly chooses internal losses and recovers
the existing `AssertionDAdmissibleRefinementStatement`.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Extract an indexed Katz--Tao subfamily with retained aggregate shading density
and near-critical cardinality.

The requested cardinality, Katz--Tao, and density losses are independent.
The producer may choose a stronger input loss and a sufficiently small scale.
This is the WZ2-facing consequence of Bernoulli thinning together with the
polynomial convex density-test net.
-/
def ProbabilisticKatzTaoSubfamilyStatement : Prop :=
  ∀ cardLoss ktEta densityEta : ℝ,
    0 < cardLoss → 0 < ktEta → 0 < densityEta →
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
                ∃ S : Kakeya.Streamlined.TubeSubfamily F,
                  S.family.Nonempty ∧
                  S.family.IsInUnitBall ∧
                  S.family.IsEssentiallyDistinct ∧
                  (S.restrictShading Y).union ⊆ Y.union ∧
                  (S.restrictShading Y).IsLambdaDense
                    (Kakeya.realRpowENN delta densityEta) ∧
                  S.family.toBodyFamily.IsCKatzTao
                    (Kakeya.realRpowENN delta (-ktEta)) ∧
                  Kakeya.realRpowENN delta (-2 + cardLoss) ≤
                    S.family.enncard

/--
Convert one indexed Katz--Tao subfamily to the finite-set model consumed by
`AssertionD`.

The input cardinality loss `coreCardLoss` may be stronger than the caller's
requested output loss.  The strict inequality
`ktEta + coreCardLoss < assertionEta` leaves room to absorb fixed geometric
constants when deriving the Frostman slab bound.
-/
def IndexedKatzTaoToAssertionDStatement : Prop :=
  ∀ requestedCardLoss coreCardLoss ktEta assertionEta : ℝ,
    0 < requestedCardLoss →
    0 < coreCardLoss →
    coreCardLoss ≤ requestedCardLoss →
    0 < ktEta →
    0 < assertionEta →
    ktEta + coreCardLoss < assertionEta →
      ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              ∀ S : Kakeya.Streamlined.TubeSubfamily F,
                S.family.Nonempty →
                S.family.IsInUnitBall →
                S.family.IsEssentiallyDistinct →
                (S.restrictShading Y).IsLambdaDense
                    (Kakeya.realRpowENN delta assertionEta) →
                S.family.toBodyFamily.IsCKatzTao
                    (Kakeya.realRpowENN delta (-ktEta)) →
                Kakeya.realRpowENN delta (-2 + coreCardLoss) ≤
                    S.family.enncard →
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
                    Kakeya.realRpowENN delta
                        (-2 + requestedCardLoss) ≤
                      G.enncard

/--
The two frozen leaves imply the existing same-configuration refinement
boundary used by the already-proved Wolff-volume-floor algebra.
-/
def AssertionDAdmissibleRefinementAssemblyStatement : Prop :=
  ProbabilisticKatzTaoSubfamilyStatement →
    IndexedKatzTaoToAssertionDStatement →
      AssertionDAdmissibleRefinementStatement

/--
The closed subunit route from the shaded hairbrush estimate and the two
refinement leaves to one non-admissible exponent below one.

The canonical witness is `a = 3 / 4`: Assertion D at `(1/2, 0)` gives the
Wolff volume floor, and `wolff_not_admissible` applied with `epsilon = 1/4`
rules out admissibility at `3/4`.
-/
def SubunitAdmissibleCeilingAssemblyStatement : Prop :=
  Kakeya.AssertionD (1 / 2) 0 →
    ProbabilisticKatzTaoSubfamilyStatement →
      IndexedKatzTaoToAssertionDStatement →
        SubunitAdmissibleCeilingInput

end Kakeya.Assouad
