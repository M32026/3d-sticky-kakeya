import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingUniformRefinementStatement

/-!
# Cell cardinalities in an exact branching tree

Exact occupied-child counts at every level, together with atomic terminal
cells, determine the number of retained leaves below every occupied cell.
Thus all occupied cells at a fixed level contain the same number of retained
atoms.
-/

namespace Kakeya.Assouad

/--
An exact branching profile forces equal retained cardinality in every
occupied cell at each level.

This is the quantitative consequence of OS branching needed for projected
mass uniformity.  It concerns `A' ∩ cell`, not the cardinality of the ambient
partition cell.
-/
def OSBranchingCellCardinalityStatement : Prop :=
  ∀ (α : Type) [DecidableEq α],
    ∀ A : Finset α,
      ∀ levels : ℕ,
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
          ∀ A' : Finset α,
            A'.Nonempty →
            A' ⊆ A →
            ∀ branchExponent : Fin levels → ℕ,
              (∀ level : Fin levels,
                ∀ parent ∈ P level,
                  (A' ∩ parent).Nonempty →
                    (occupiedPartitionChildren
                      A' P level parent).card =
                        2 ^ branchExponent level) →
              ∀ level : ℕ, level ≤ levels →
                ∃ cellCard : ℕ,
                  0 < cellCard ∧
                    ∀ cell ∈ P level,
                      (A' ∩ cell).Nonempty →
                        (A' ∩ cell).card = cellCard

end Kakeya.Assouad
