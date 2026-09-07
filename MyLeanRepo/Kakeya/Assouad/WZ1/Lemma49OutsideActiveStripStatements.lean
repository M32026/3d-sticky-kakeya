import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremLocalizationStatements

/-!
# Outside-active-strip leaf for WZ1 Lemma 49

This module freezes the direct covering branch of Lemma 49.  The common strip
width is the exact maximum over graph-active second and third coordinates.
If one graph-active first coordinate escapes the corresponding enlarged
orthogonal strip, a dense second-coordinate fiber and the Frostman bound
produce the long dot-difference projection directly.
-/

namespace Kakeya.Assouad

noncomputable section

/--
The graph-active outside-strip branch of WZ1 Lemma 49.

The auxiliary strip loss is `epsilon₁ = epsilon² / 100`, matching the paper's
hierarchy `eta ≪ epsilon₁ ≪ epsilon`.  The exponent budget
`eta ≤ epsilon² / 100` absorbs the direct separated-fiber count.
-/
def WZ1Lemma49OutsideActiveStripStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧ eta ≤ epsilon ^ 2 / 100 ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F G₁ G₂ : DiscreteSet 2,
          F.Nonempty → G₁.Nonempty → G₂.Nonempty →
          F.IsInUnitBall → G₁.IsInUnitBall → G₂.IsInUnitBall →
          F.IsDeltaSeparated delta →
          G₁.IsDeltaSeparated delta →
          G₂.IsDeltaSeparated delta →
          F.IsFrostman delta 1
            (Kakeya.realRpowENN delta (-eta)) →
          G₁.IsFrostman delta 1
            (Kakeya.realRpowENN delta (-eta)) →
          G₂.IsFrostman delta 1
            (Kakeya.realRpowENN delta (-eta)) →
          WZ1StandardSeparation F G₁ G₂ →
          ∀ H : Finset (Point2 × Point2 × Point2),
            ∀ hDensity :
                WZ1UniformTripleDensity
                  (Kakeya.realRpowENN delta eta)
                  F G₁ G₂ H,
              ∀ base direction : Point2,
                ‖direction‖ = 1 →
                let t :=
                  wz1ActiveCommonWidth
                    delta H hDensity.1 base direction
                (∃ edge ∈ H,
                  edge.1 ∉
                    wz1LineNeighborhood 0
                      (wz1Perp2 direction)
                      (Real.rpow delta
                        (-wz1Lemma49AuxiliaryEpsilon epsilon) * t)) →
                  WZ1StripLocalizationLongProjection
                    delta epsilon eta H

end

end Kakeya.Assouad
