import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameter4FiberRegularizationStatement

/-!
# Dyadic regularization of complete terminal parameter-cell fibers

The paper-uniform Section 7 tree stops at parameter mesh comparable to the
fine tube radius.  Its terminal atoms are occupied grid cells, not distinct
exact parameter points.

This boundary dyadically regularizes the indexed tube multiplicity of the map

`index ↦ tubeParameterGridIndex base levels (indexedTubeParameterPoint4 index)`.

The selected set is a union of complete active terminal-cell fibers.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Terminal grid index attached to one indexed tube parameter point. -/
def indexedTubeTerminalCellIndex
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (base levels : ℕ)
    (index : Fin family.card) : Fin 4 → ℤ :=
  tubeParameterGridIndex base levels
    (indexedTubeParameterPoint4 index)

/--
A substantial class of complete terminal-cell fibers with one common dyadic
tube multiplicity scale.
-/
structure TubeParameterTerminalCellFiberRegularizationData
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (active : Finset (Fin family.card))
    (base levels : ℕ) where
  selected : Finset (Fin family.card)
  selected_subset : selected ⊆ active
  selected_nonempty : selected.Nonempty
  cells : Finset (Fin 4 → ℤ)
  cells_eq :
    cells = selected.image (indexedTubeTerminalCellIndex base levels)
  cells_nonempty : cells.Nonempty
  fiberMultiplicity : ℕ
  fiberMultiplicity_pos : 0 < fiberMultiplicity
  fiber_lower :
    ∀ cell ∈ cells,
      fiberMultiplicity ≤
        (selected.filter fun index =>
          indexedTubeTerminalCellIndex base levels index = cell).card
  fiber_upper :
    ∀ cell ∈ cells,
      (selected.filter fun index =>
        indexedTubeTerminalCellIndex base levels index = cell).card <
          2 * fiberMultiplicity
  selected_saturated :
    ∀ index ∈ active,
      indexedTubeTerminalCellIndex base levels index ∈ cells →
        index ∈ selected
  active_card_le :
    active.card ≤
      (Nat.log 2 active.card + 1) * selected.card

/--
Every nonempty active index set admits one dyadic class of complete terminal
parameter-cell fibers.
-/
def TubeParameterTerminalCellFiberRegularizationStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ family : Kakeya.Streamlined.TubeFamily delta,
      ∀ active : Finset (Fin family.card),
        active.Nonempty →
        ∀ base levels : ℕ,
          Nonempty
            (TubeParameterTerminalCellFiberRegularizationData
              family active base levels)

end Kakeya.Assouad
