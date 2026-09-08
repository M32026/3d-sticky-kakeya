import MyLeanRepo.Kakeya.Streamlined.CombinatorialLemmas.TotalConflictExtraction
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.ResidualAbsorption

/-!
# Conflict degree after same-axis parent enlargement

The one-level random-translation construction first works with an
essentially-distinct family of `sigma`-parents.  Residual shifts of norm at
most `rho - sigma` are absorbed by enlarging every parent coaxially to radius
`rho`.  The enlarged parents need not remain essentially distinct.

This module freezes the quantitative replacement needed before applying the
whole-fiber coarse selection: every enlarged parent has at most
`O((rho / sigma)^4)` conflicts.  The fourth power is the three-dimensional
tube phase-space packing exponent.
-/

noncomputable section

namespace Kakeya.Streamlined

open RandomTranslation.WithShading

/--
An essentially-distinct selected cover at radius `sigma`, arising from a
unit-ball fine family, has bounded conflict degree after all parents are
enlarged coaxially to radius `rho`.

The constant is universal.  In particular, it is chosen before the fine
scale, the tube family, the uniform structure, and both parent scales.
Midpoint boundedness is not an additional input: it follows from
surjectivity of the `sigma`-cover and containment of the fine family in the
unit ball.
-/
def SameAxisEnlargementConflictDegreeStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {delta : ℝ}, 0 < delta →
      ∀ (fine : TubeFamily delta),
        fine.IsInUnitBall →
        ∀ (U : UniformTubeStructure fine),
          ∀ (sigma rho : AdmissibleScale delta),
            sigma.1 ≤ rho.1 →
              ∀ j : Fin (U.coarse sigma).card,
                tubeConflictDegree
                    (sameAxisEnlargedFamily
                      (rho := rho.1) (U.coarse sigma)) j ≤
                  Nat.ceil (C * (rho.1 / sigma.1) ^ 4)

end Kakeya.Streamlined
