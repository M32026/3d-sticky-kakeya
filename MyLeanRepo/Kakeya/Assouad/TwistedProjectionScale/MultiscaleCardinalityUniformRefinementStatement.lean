import MyLeanRepo.Kakeya.Assouad.UniformRefinement

/-!
# Two-sided multiscale cardinality uniformization

The finite uniform-refinement input used in Section 7 must compare any two
occupied cells at the same scale.  A one-sided lower bound by the average
cell occupancy is not enough for the local-to-global projection comparison.

This module freezes the required tree-pruning lemma.  Starting at the finest
partition and moving towards the root, one keeps a dyadic class of occupied
cells.  Coarser pruning removes whole parent cells, so uniformity already
obtained at finer levels is preserved.
-/

namespace Kakeya.Assouad

/--
Every finite set equipped with `T` nested finite partitions has a subset
whose occupied cells at each level have pairwise comparable cardinalities.

The loss is at most one dyadic pigeonholing factor
`Nat.log 2 A.card + 1` per level.  The conclusion compares the final
cardinalities inside the retained set, not the original cell cardinalities.
-/
def MultiscaleCardinalityUniformRefinementStatement : Prop :=
  ∀ (α : Type) [DecidableEq α],
    ∀ (A : Finset α),
      A.Nonempty →
      ∀ (T : ℕ) (P : ℕ → Finset (Finset α)),
        (∀ k < T,
          (∀ c ∈ P k, c ⊆ A) ∧
          (∀ c₁ ∈ P k, ∀ c₂ ∈ P k,
            c₁ ≠ c₂ → Disjoint c₁ c₂) ∧
          A ⊆ Finset.biUnion (P k) id) →
        (∀ k, k + 1 < T →
          ∀ c ∈ P (k + 1), ∃ p ∈ P k, c ⊆ p) →
        ∃ A' : Finset α,
          A'.Nonempty ∧
          A' ⊆ A ∧
          (A.card : ℝ) ≤
            (Nat.log 2 A.card + 1 : ℝ) ^ T * (A'.card : ℝ) ∧
          ∀ k < T,
            ∀ c₁ ∈ P k, ∀ c₂ ∈ P k,
              (A' ∩ c₁).Nonempty →
              (A' ∩ c₂).Nonempty →
              (A' ∩ c₁).card ≤ 2 * (A' ∩ c₂).card

end Kakeya.Assouad
