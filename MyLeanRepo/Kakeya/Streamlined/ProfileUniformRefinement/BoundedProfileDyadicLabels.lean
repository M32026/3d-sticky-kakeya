import MyLeanRepo.Kakeya.Streamlined.ProfileUniformRefinement.ThreeProfileWholeFiberSelection

/-!
# Dyadic labels for three bounded `ENNReal` profiles

The one-scale strengthened uniform refinement simultaneously bins branching
numbers, fiber Frostman constants, and fiber `deltaMax` values.  This module
freezes the numerical step that constructs sound dyadic labels from one
common finite upper bound.
-/

noncomputable section

namespace Kakeya.Streamlined

/--
Three positive finite profiles bounded by the same natural number admit
sound dyadic labels using exactly `Nat.log 2 N + 1` bins.

The theorem is stated for arbitrary finite parent types.  The later geometric
adapter supplies:

* the actual parent-fiber cardinality;
* the fiber Frostman constant;
* the fiber maximal density;

together with one common polynomial natural upper bound.
-/
def BoundedProfileDyadicLabelsStatement : Prop :=
  ∀ (J : Type*) [Fintype J] [DecidableEq J],
    ∀ (N : ℕ), 1 ≤ N →
    ∀ (branchProfile frostmanProfile deltaMaxProfile : J → ENNReal),
      (∀ j, 1 ≤ branchProfile j ∧ branchProfile j ≤ (N : ENNReal)) →
      (∀ j, 1 ≤ frostmanProfile j ∧ frostmanProfile j ≤ (N : ENNReal)) →
      (∀ j, 1 ≤ deltaMaxProfile j ∧ deltaMaxProfile j ≤ (N : ENNReal)) →
      ∃ (branchBin frostmanBin deltaMaxBin :
          J → Fin (Nat.log 2 N + 1)),
        (∀ j,
          InDyadicProfileBin (branchBin j) (branchProfile j)) ∧
        (∀ j,
          InDyadicProfileBin (frostmanBin j) (frostmanProfile j)) ∧
        (∀ j,
          InDyadicProfileBin (deltaMaxBin j) (deltaMaxProfile j))

end Kakeya.Streamlined
