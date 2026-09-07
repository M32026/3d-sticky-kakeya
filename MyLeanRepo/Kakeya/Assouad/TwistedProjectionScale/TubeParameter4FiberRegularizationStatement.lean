import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterOSUniformRefinementStatements

/-!
# Dyadic regularization of complete four-parameter tube fibers

The map from indexed tubes to supporting-line parameters `(a,b,c,d)` need
not be injective.  The paper explicitly permits a multiset of line
parameters, so the Section 7 uniformization must not discard all but one tube
from each exact parameter fiber.

This boundary selects one dyadic multiplicity class of complete fibers.  All
nonempty selected fibers have comparable cardinality, and the logarithmic
retention is measured against the original active index set.
-/

noncomputable section

namespace Kakeya.Assouad

/--
A substantial union of complete exact four-parameter fibers with one common
dyadic multiplicity scale.
-/
structure TubeParameter4FiberRegularizationData
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (active : Finset (Fin family.card)) where
  selected : Finset (Fin family.card)
  selected_subset : selected ⊆ active
  selected_nonempty : selected.Nonempty
  fiberMultiplicity : ℕ
  fiberMultiplicity_pos : 0 < fiberMultiplicity
  fiber_lower :
    ∀ point ∈ selected.image indexedTubeParameterPoint4,
      fiberMultiplicity ≤
        (selected.filter fun index =>
          indexedTubeParameterPoint4 index = point).card
  fiber_upper :
    ∀ point ∈ selected.image indexedTubeParameterPoint4,
      (selected.filter fun index =>
        indexedTubeParameterPoint4 index = point).card <
          2 * fiberMultiplicity
  selected_saturated :
    ∀ index ∈ active,
      indexedTubeParameterPoint4 index ∈
          selected.image indexedTubeParameterPoint4 →
        index ∈ selected
  active_card_le :
    active.card ≤
      (Nat.log 2 active.card + 1) * selected.card

/--
Every nonempty finite active index set admits a dyadically regularized class
of complete exact four-parameter fibers.
-/
def TubeParameter4FiberRegularizationStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ family : Kakeya.Streamlined.TubeFamily delta,
      ∀ active : Finset (Fin family.card),
        active.Nonempty →
          Nonempty
            (TubeParameter4FiberRegularizationData family active)

end Kakeya.Assouad
