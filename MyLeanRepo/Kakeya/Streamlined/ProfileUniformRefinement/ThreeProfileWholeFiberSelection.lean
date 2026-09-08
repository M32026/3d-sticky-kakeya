import MyLeanRepo.Kakeya.Streamlined.Estimates

/-!
# Whole-fiber selection with three uniform parent profiles

The strengthened Definition 2.1 requires simultaneous comparability of
branching numbers, fiber Frostman constants, and fiber `deltaMax` values.
This module freezes the finite combinatorial selection used at one scale.

Each active parent is assigned one dyadic bin for each of the three profiles.
The output selects one common triple of bins and retains the complete fine
fiber over every selected parent.  Consequently all three profiles are
pairwise comparable on the selected parent family.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- Cardinality of one fiber of a map between finite types. -/
def finiteFiberCount
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (parent : I → J) (j : J) : ENNReal :=
  ((Finset.univ.filter fun i => parent i = j).card : ENNReal)

/-- An `ENNReal` profile lies in the dyadic interval assigned by `bin`. -/
def InDyadicProfileBin {B : ℕ} (bin : Fin B) (x : ENNReal) : Prop :=
  ((2 ^ bin.val : ℕ) : ENNReal) ≤ x ∧
    x ≤ 2 * ((2 ^ bin.val : ℕ) : ENNReal)

/--
Select one common triple of parent-profile bins while retaining complete
parent fibers.

The three profiles are:

1. the actual fine-fiber cardinality;
2. an abstract Frostman profile;
3. an abstract maximal-density profile.

The input bin certificates are required only for active parents.  The output
parent set is exactly the image of the selected fine set, and the selected
fine set is exactly its full preimage.  Thus no parent fiber is partially
selected.  The weighted retention loss is at most the number `B^3` of bin
triples.
-/
def ThreeProfileWholeFiberSelectionStatement : Prop :=
  ∀ (I J : Type*) [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J],
    ∀ (parent : I → J) (weight : I → ENNReal),
    ∀ (B : ℕ), 1 ≤ B →
    ∀ (frostmanProfile deltaMaxProfile : J → ENNReal),
    ∀ (branchBin frostmanBin deltaMaxBin : J → Fin B),
      (∀ j, 0 < finiteFiberCount parent j →
        InDyadicProfileBin (branchBin j) (finiteFiberCount parent j)) →
      (∀ j, 0 < finiteFiberCount parent j →
        InDyadicProfileBin (frostmanBin j) (frostmanProfile j)) →
      (∀ j, 0 < finiteFiberCount parent j →
        InDyadicProfileBin (deltaMaxBin j) (deltaMaxProfile j)) →
      0 < ∑ i, weight i →
      ∃ (selectedFine : Finset I) (selectedParents : Finset J),
        selectedFine.Nonempty ∧
        selectedParents.Nonempty ∧
        (∀ i, i ∈ selectedFine ↔ parent i ∈ selectedParents) ∧
        (∀ j, j ∈ selectedParents ↔
          j ∈ Finset.image parent selectedFine) ∧
        (∑ i, weight i) ≤
          (B : ENNReal) ^ 3 *
            ∑ i ∈ selectedFine, weight i ∧
        (∀ j ∈ selectedParents, ∀ k ∈ selectedParents,
          ComparableBy 2
            (finiteFiberCount parent j)
            (finiteFiberCount parent k)) ∧
        (∀ j ∈ selectedParents, ∀ k ∈ selectedParents,
          ComparableBy 2
            (frostmanProfile j)
            (frostmanProfile k)) ∧
        (∀ j ∈ selectedParents, ∀ k ∈ selectedParents,
          ComparableBy 2
            (deltaMaxProfile j)
            (deltaMaxProfile k))

end Kakeya.Streamlined
