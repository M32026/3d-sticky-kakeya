import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingUniformRefinementStatement

/-!
# Measure-weighted Orponen--Shmerkin branching refinement

The finest projected grid cells in Section 7 carry unequal masses rather than
unit cardinality.  After one dyadic mass pigeonhole their masses are pairwise
comparable.  This statement upgrades the finite OS branching refinement to
retain the corresponding measurable union with the same local tree loss,
paying one additional factor two for the atom-mass comparison.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Union of a finite family of atoms indexed by `A`. -/
def finiteAtomUnion
    {α β : Type}
    (A : Finset α)
    (atom : α → Set β) : Set β :=
  ⋃ a ∈ A, atom a

/--
A locally bounded measurable atom tree has a dense, exactly branching
subtree when all terminal atom masses are within a factor two.

The output loss is

`2 * (2 * (log₂ childBound + 1))^levels`.

The leading factor two is paid once, not once per level.  This is the bridge
needed after the projected-fiber band is partitioned into finest grid atoms:
the retained index set gives a genuine measurable planar subset whose
pullback is still a shading on the original tube family.
-/
def WeightedOSBranchingUniformRefinementStatement : Prop :=
  ∀ (β : Type) [MeasurableSpace β],
    ∀ μ : Measure β,
      ∀ (α : Type) [DecidableEq α],
        ∀ A : Finset α,
          A.Nonempty →
          ∀ atom : α → Set β,
            (∀ a ∈ A, MeasurableSet (atom a)) →
            (∀ a ∈ A, ∀ b ∈ A,
              a ≠ b → Disjoint (atom a) (atom b)) →
            (∀ a ∈ A, μ (atom a) ≠ 0) →
            (∀ a ∈ A, μ (atom a) ≠ ⊤) →
            (∀ a ∈ A, ∀ b ∈ A,
              μ (atom a) ≤ 2 * μ (atom b)) →
            ∀ levels childBound : ℕ,
              0 < childBound →
              ∀ P : ℕ → Finset (Finset α),
                (∀ level ≤ levels,
                  (∀ cell ∈ P level,
                    cell.Nonempty ∧ cell ⊆ A) ∧
                  (∀ cell₁ ∈ P level, ∀ cell₂ ∈ P level,
                    cell₁ ≠ cell₂ → Disjoint cell₁ cell₂) ∧
                  A ⊆ Finset.biUnion (P level) id) →
                (∀ cell ∈ P levels, cell.card = 1) →
                (∀ level, level < levels →
                  ∀ child ∈ P (level + 1),
                    ∃ parent ∈ P level, child ⊆ parent) →
                (∀ level, level < levels →
                  ∀ parent ∈ P level,
                    (partitionChildren P level parent).card ≤
                      childBound) →
                ∃ A' : Finset α,
                  A'.Nonempty ∧
                  A' ⊆ A ∧
                  MeasurableSet (finiteAtomUnion A' atom) ∧
                  finiteAtomUnion A' atom ⊆
                    finiteAtomUnion A atom ∧
                  μ (finiteAtomUnion A atom) ≤
                    (2 : ENNReal) *
                        ((((2 * (Nat.log 2 childBound + 1)) ^
                          levels : ℕ)) : ENNReal) *
                      μ (finiteAtomUnion A' atom) ∧
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
