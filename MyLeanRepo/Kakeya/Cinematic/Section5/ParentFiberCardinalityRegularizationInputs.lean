import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Log

/-!
# Dyadic regularization of parent-fiber cardinalities

This is the first coarse-parent pigeonhole in PYZ Section 5.3.  It selects
coarse parents according to how many selected fine rectangles they own and
retains a logarithmic fraction of the fine-rectangle cardinality.
-/

namespace Kakeya.Cinematic

def parentFiber
    {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (rectangles : Finset β) (parent : β → γ)
    (coarse : γ) : Finset β :=
  rectangles.filter fun rectangle => parent rectangle = coarse

def parentSupport
    {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (rectangles : Finset β) (parent : β → γ) : Finset γ :=
  rectangles.image parent

def rectanglesOverParents
    {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (rectangles : Finset β) (parent : β → γ)
    (parents : Finset γ) : Finset β :=
  rectangles.filter fun rectangle => parent rectangle ∈ parents

def ParentFiberCardinalityRegularizationStatement : Prop :=
  ∀ {β γ : Type*} [DecidableEq β] [DecidableEq γ],
    ∀ (rectangles : Finset β) (parent : β → γ),
      rectangles.Nonempty →
      ∃ (level : ℕ) (selectedParents : Finset γ),
        level ≤ Nat.log2 rectangles.card ∧
        selectedParents.Nonempty ∧
        selectedParents =
          (parentSupport rectangles parent).filter (fun coarse =>
            2 ^ level ≤ (parentFiber rectangles parent coarse).card ∧
              (parentFiber rectangles parent coarse).card <
                2 ^ (level + 1)) ∧
        rectangles.card ≤
          (Nat.log2 rectangles.card + 1) *
            (rectanglesOverParents
              rectangles parent selectedParents).card ∧
        (rectanglesOverParents
          rectangles parent selectedParents).card =
            ∑ coarse ∈ selectedParents,
              (parentFiber rectangles parent coarse).card ∧
        ∀ coarse ∈ selectedParents,
          2 ^ level ≤ (parentFiber rectangles parent coarse).card ∧
            (parentFiber rectangles parent coarse).card <
              2 ^ (level + 1)

end Kakeya.Cinematic
