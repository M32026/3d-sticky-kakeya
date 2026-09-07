import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Nested weighted lower regularization

The preparation step in Section 6 does not need pairwise factor-two
comparability at every scale.  It only needs a lower bound for every occupied
parent fiber.  For nested partitions, this can be obtained by deleting cells
below half the average weight, starting at the finest level and moving
towards the root.

Each level loses at most a factor two.  Since the number of levels depends
only on the loss parameter, the resulting constant `2 ^ levelCount` is
absorbed into one fixed paper logarithmic refinement factor by taking the
small-scale threshold sufficiently small.  In particular, there is no
`(log(1 / delta)) ^ levelCount` loss.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped BigOperators

def WZ2PropStickyNestedWeightedLowerRegularizationStatement : Prop :=
  ∀ (indexType : Type) [DecidableEq indexType],
    ∀ (ambient : Finset indexType),
      ∀ (weight : indexType → ENNReal),
        ∀ (levelCount : ℕ),
          ∀ (partition : ℕ → Finset (Finset indexType)),
            (∀ level < levelCount,
              (∀ cell ∈ partition level, cell ⊆ ambient) ∧
              (∀ first ∈ partition level,
                ∀ second ∈ partition level,
                  first ≠ second → Disjoint first second) ∧
              ambient ⊆ Finset.biUnion (partition level) id) →
            (∀ level, level + 1 < levelCount →
              ∀ child ∈ partition (level + 1),
                ∃ parent ∈ partition level, child ⊆ parent) →
            (∑ index ∈ ambient, weight index) ≠ ⊤ →
              ∃ selected : Finset indexType,
                selected ⊆ ambient ∧
                (∑ index ∈ ambient, weight index) ≤
                    (2 : ENNReal) ^ levelCount *
                      ∑ index ∈ selected, weight index ∧
                ∀ level < levelCount,
                  ∀ cell ∈ partition level,
                    (selected ∩ cell).Nonempty →
                      (1 / 2 : ENNReal) *
                            (∑ index ∈ selected, weight index) ≤
                        ((partition level).card : ENNReal) *
                          ∑ index ∈ selected ∩ cell, weight index

end Kakeya.Assouad

end
