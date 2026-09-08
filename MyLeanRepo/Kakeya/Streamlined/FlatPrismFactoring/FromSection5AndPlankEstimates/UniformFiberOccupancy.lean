import MyLeanRepo.Kakeya.Streamlined.Basic

/-!
# Uniform fiber-occupancy selection

This is the finite dyadic selection used before the Part A Frostman
inheritance step in Section 6.

It regularizes the cardinalities of the geometric factoring fibers. It does
not use or produce pointwise shading multiplicity.
-/

noncomputable section

namespace Kakeya.Streamlined

open MeasureTheory

/-- Fine indices whose parent belongs to the selected coarse set. -/
def Factoring.selectedFineIndices {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (selected : Finset (Fin coarse.card)) :
    Finset (Fin fine.card) :=
  Finset.univ.filter fun i => P.parent i ∈ selected

/--
For an equal-volume fine family, one dyadic band of parent-fiber
cardinalities retains a logarithmic fraction of the total fine mass.

The selected fine indices are the full preimage of the selected coarse
indices. Every selected fiber has cardinality in `[n, 2n)`.
-/
def UniformFiberOccupancySelectionStatement : Prop :=
  ∀ {fine coarse : BodyFamily},
    ∀ P : Factoring fine coarse,
      0 < fine.card →
      ∀ V : ENNReal,
        V ≠ 0 →
        V ≠ ⊤ →
        (∀ i, (fine.body i).volume = V) →
        ∃ selected : Finset (Fin coarse.card),
        ∃ n : ℕ,
          selected.Nonempty ∧
          1 ≤ n ∧
          (∀ j ∈ selected,
            n ≤ (P.fiberIndices j).card ∧
              (P.fiberIndices j).card < 2 * n) ∧
          (∑ i ∈ P.selectedFineIndices selected,
              (fine.body i).volume) =
            ∑ j ∈ selected, P.fiberMass j ∧
          fine.mass ≤
            (Nat.log 2 fine.card + 1 : ENNReal) *
              ∑ i ∈ P.selectedFineIndices selected,
                (fine.body i).volume

end Kakeya.Streamlined
