import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44TransverseBounds

/-!
# Remaining finite bad-pair inputs for WZ1 Lemma 44

The three geometric cases are closed.  The next independent input is the
packing bound for a separated collection of heavy strips through one base
point.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Two planar affine lines are separated by `r` in both normal orientations. -/
def WZ1LinesSeparated
    (r : ℝ)
    (line₁ line₂ : AffineSubspace ℝ Point2) : Prop :=
  ∀ normal₁ normal₂ : Point2,
    ‖normal₁‖ = 1 →
    ‖normal₂‖ = 1 →
    (∀ v ∈ line₁.direction,
      inner ℝ v normal₁ = 0) →
    (∀ v ∈ line₂.direction,
      inner ℝ v normal₂ = 0) →
      r ≤ ‖normal₁ - normal₂‖ ∧
        r ≤ ‖normal₁ + normal₂‖

/--
Packing bound for separated heavy lines through one point.

Each selected line contains `base`, the lines are pairwise separated at scale
`r`, and every line contains more than
`K * r^(1/4) * #G₂` points of `G₂` in its `r`-thickening.  Mutual separation
of `G₁` and `G₂` keeps every contributing point a fixed distance from `base`,
so one point of `G₂` can belong to only a bounded number of selected strips.
-/
def WZ1HeavyLinePackingStatement : Prop :=
  ∀ delta r K : ℝ,
    0 < delta →
    delta ≤ r →
    r ≤ 1 / 4 →
    0 < K →
      ∀ G₁ G₂ : DiscreteSet 2,
        WZ1MutuallySeparated G₁ G₂ (1 / 2) →
          ∀ base : Point2,
            base ∈ G₁ →
              ∀ lines :
                  Finset (AffineSubspace ℝ Point2),
                (∀ line ∈ lines,
                  base ∈ (line : Set Point2)) →
                (∀ line ∈ lines,
                  Module.finrank ℝ line.direction = 1) →
                (∀ line₁ ∈ lines,
                  ∀ line₂ ∈ lines,
                    line₁ ≠ line₂ →
                      WZ1LinesSeparated r line₁ line₂) →
                (∀ line ∈ lines,
                  ((G₂.filter fun point =>
                    point ∈ Metric.thickening r
                      (line : Set Point2)).card :
                    ENNReal) >
                    ENNReal.ofReal
                        (K * Real.rpow r (1 / 4 : ℝ)) *
                      G₂.enncard) →
                  (lines.card : ℝ) ≤
                    20 /
                      (K ^ 2 *
                        Real.rpow r (1 / 2 : ℝ))

/-- A pair is supported by a heavy strip at one fixed scale. -/
def WZ1BadAtScale
    (G₁ G₂ : DiscreteSet 2)
    (scale K : ℝ)
    (b₁ b₂ : Point2) : Prop :=
  ∃ line : AffineSubspace ℝ Point2,
    b₁ ∈ (line : Set Point2) ∧
    Module.finrank ℝ line.direction = 1 ∧
    b₂ ∈ Metric.thickening scale
      (line : Set Point2) ∧
    ((G₂.filter fun point =>
      point ∈ Metric.thickening scale
        (line : Set Point2)).card : ENNReal) >
      ENNReal.ofReal
          (K * Real.rpow scale (1 / 4 : ℝ)) *
        G₂.enncard

/--
Single-scale exceptional-pair estimate after the heavy-line packing step.

The three summands are exactly `threeCase_case1`, `threeCase_case2`, and
`threeCase_case3`.  The displayed arithmetic premises are the power
inequalities chosen later by the dyadic-scale assembly.
-/
def WZ1Lemma44SingleScaleBadPairStatement : Prop :=
  WZ1HeavyLinePackingStatement →
    ∀ delta lambda zeta alpha : ℝ,
      0 < delta → delta < 1 →
      0 < lambda → 0 < zeta → 0 < alpha →
        ∀ G₁ G₂ : DiscreteSet 2,
          G₁.Nonempty → G₂.Nonempty →
          G₁.IsInUnitBall → G₂.IsInUnitBall →
          G₁.IsDeltaSeparated delta →
          G₂.IsDeltaSeparated delta →
          G₁.IsFrostman delta 1
            (Kakeya.realRpowENN delta (-lambda)) →
          G₂.IsFrostman delta 1
            (Kakeya.realRpowENN delta (-lambda)) →
          WZ1MutuallySeparated G₁ G₂ (1 / 2) →
          WZ1LineNonConcentration
            delta lambda zeta G₂ →
            ∀ K scale : ℝ,
              1 ≤ K →
              0 < scale → delta ≤ scale →
              scale ≤ 1 →
              K * Real.rpow scale (1 / 4 : ℝ) < 1 →
              13 * scale ≤ 1 →
              8 * (13 * scale) ≤
                Real.rpow delta
                    (lambda + 4 * alpha) *
                  Real.rpow delta
                    (lambda + 4 * alpha / zeta) →
              (312000 : ℝ) / K ^ 4 *
                  Real.rpow delta
                    (-(3 * lambda + 4 * alpha +
                      4 * alpha / zeta)) ≤
                Real.rpow delta (4 * alpha) →
                (((G₁ ×ˢ G₂).filter fun
                    pair : Point2 × Point2 =>
                  WZ1BadAtScale G₁ G₂ scale K
                    pair.1 pair.2).card : ℝ) ≤
                  Real.sqrt 312002 *
                    Real.rpow delta (2 * alpha) *
                    (G₁.card : ℝ) * (G₂.card : ℝ)

end Kakeya.Assouad
