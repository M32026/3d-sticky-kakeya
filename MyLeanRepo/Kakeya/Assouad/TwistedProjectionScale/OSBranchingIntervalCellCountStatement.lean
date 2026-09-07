import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingCellCardinalityStatement

/-!
# Uniform occupied-cell counts between two levels of an exact branching tree

Exact occupied-child counts imply more than equal terminal-leaf
cardinalities.  Between any two fixed levels, every occupied coarse cell has
the same positive number of occupied fine descendants.

This is the recursive combinatorial invariant needed after the first
selected-scale transition: a coarse tube family has one fixed-size block per
occupied parameter cell, and later transitions group those blocks by
ancestors in the same frozen OS tree.
-/

namespace Kakeya.Assouad

/-- Occupied cells of `A'` at one partition level. -/
def occupiedPartitionCells
    {α : Type} [DecidableEq α]
    (A' : Finset α)
    (partition : ℕ → Finset (Finset α))
    (level : ℕ) : Finset (Finset α) :=
  (partition level).filter fun cell =>
    (A' ∩ cell).Nonempty

/--
Every occupied coarse cell has the same number of occupied descendants at a
fixed finer level.
-/
def OSBranchingIntervalCellCountStatement : Prop :=
  ∀ (α : Type) [DecidableEq α],
    ∀ A : Finset α,
      ∀ levels : ℕ,
        ∀ partition : ℕ → Finset (Finset α),
          (∀ level ≤ levels,
            (∀ cell ∈ partition level,
              cell.Nonempty ∧ cell ⊆ A) ∧
            (∀ cell₁ ∈ partition level,
              ∀ cell₂ ∈ partition level,
                cell₁ ≠ cell₂ → Disjoint cell₁ cell₂) ∧
            A ⊆ Finset.biUnion (partition level) id) →
          (∀ cell ∈ partition levels, cell.card = 1) →
          (∀ level, level < levels →
            ∀ child ∈ partition (level + 1),
              ∃ parent ∈ partition level, child ⊆ parent) →
          ∀ A' : Finset α,
            A'.Nonempty →
            A' ⊆ A →
            ∀ branchExponent : Fin levels → ℕ,
              (∀ level : Fin levels,
                ∀ parent ∈ partition level,
                  (A' ∩ parent).Nonempty →
                    (occupiedPartitionChildren
                      A' partition level parent).card =
                        2 ^ branchExponent level) →
              ∀ coarseLevel fineLevel : ℕ,
                coarseLevel ≤ fineLevel →
                fineLevel ≤ levels →
                  ∃ descendantCount : ℕ,
                    0 < descendantCount ∧
                      ∀ parent ∈
                          occupiedPartitionCells
                            A' partition coarseLevel,
                        ((occupiedPartitionCells
                            A' partition fineLevel).filter fun child =>
                              child ⊆ parent).card =
                          descendantCount

end Kakeya.Assouad
