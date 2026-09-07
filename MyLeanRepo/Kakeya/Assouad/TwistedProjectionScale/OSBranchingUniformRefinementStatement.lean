import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Orponen--Shmerkin local-branching uniform refinement

The multiscale uniformization used in Section 7 is a tree-pruning lemma.  Its
loss depends on the maximum number of children of one parent, not on the
total number of cells at a level.

Starting from the atomic finest partition, process levels from fine to
coarse.  At one level, dyadically pigeonhole the number of currently active
children of each active parent, keep one class, and trim every retained
parent to the same power-of-two number of children.  Uniformity already
obtained below that level makes all active child subtrees equicardinal, so
the loss is at most `2 * (Nat.log 2 childBound + 1)` per level.
-/

namespace Kakeya.Assouad

/-- Children of `parent` in the next partition level. -/
def partitionChildren
    {α : Type} [DecidableEq α]
    (P : ℕ → Finset (Finset α))
    (level : ℕ)
    (parent : Finset α) : Finset (Finset α) :=
  (P (level + 1)).filter fun child => child ⊆ parent

/-- Children of `parent` that remain occupied by `A'`. -/
def occupiedPartitionChildren
    {α : Type} [DecidableEq α]
    (A' : Finset α)
    (P : ℕ → Finset (Finset α))
    (level : ℕ)
    (parent : Finset α) : Finset (Finset α) :=
  (partitionChildren P level parent).filter fun child =>
    (A' ∩ child).Nonempty

/--
Every finite locally bounded partition tree has a dense uniform subtree.

The finest partition is atomic.  The output has one power-of-two branching
number at each level, and every occupied parent at that level has exactly
that many occupied children.  The retention loss is local:

`|A| ≤ (2 * (log₂ childBound + 1))^levels * |A'|`.

For dyadic cubes grouped in blocks of `T` coordinate scales in dimension
`d`, one may take `childBound = 2^(d*T)`.  In the planar case this recovers
the paper's `(2T)^(-levels)` loss up to an absolute factor.
-/
def OSBranchingUniformRefinementStatement : Prop :=
  ∀ (α : Type) [DecidableEq α],
    ∀ A : Finset α,
      A.Nonempty →
      ∀ levels childBound : ℕ,
        0 < childBound →
        ∀ P : ℕ → Finset (Finset α),
          (∀ level ≤ levels,
            (∀ cell ∈ P level, cell.Nonempty ∧ cell ⊆ A) ∧
            (∀ cell₁ ∈ P level, ∀ cell₂ ∈ P level,
              cell₁ ≠ cell₂ → Disjoint cell₁ cell₂) ∧
            A ⊆ Finset.biUnion (P level) id) →
          (∀ cell ∈ P levels, cell.card = 1) →
          (∀ level, level < levels →
            ∀ child ∈ P (level + 1),
              ∃ parent ∈ P level, child ⊆ parent) →
          (∀ level, level < levels →
            ∀ parent ∈ P level,
              (partitionChildren P level parent).card ≤ childBound) →
          ∃ A' : Finset α,
            A'.Nonempty ∧
            A' ⊆ A ∧
            (A.card : ℝ) ≤
              (2 * (Nat.log 2 childBound + 1) : ℝ) ^ levels *
                (A'.card : ℝ) ∧
            ∃ branchExponent : Fin levels → ℕ,
              (∀ level : Fin levels,
                2 ^ branchExponent level ≤ childBound) ∧
              ∀ level : Fin levels,
                ∀ parent ∈ P level,
                  (A' ∩ parent).Nonempty →
                    (occupiedPartitionChildren
                      A' P level parent).card =
                        2 ^ branchExponent level

end Kakeya.Assouad
