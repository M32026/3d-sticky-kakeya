import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterTerminalCellFiberRegularizationStatement

/-!
# Representatives of occupied terminal tube-parameter cells

Choose one actual indexed tube from every selected terminal parameter cell.
Its exact four-parameter point represents that cell in the OS tree.  Different
terminal cells have different grid indices, so the representative parameter
map is injective even when exact source parameters are arbitrarily close
inside one terminal cell.
-/

noncomputable section

namespace Kakeya.Assouad

/--
One actual tube index and parameter point for every occupied terminal cell.
-/
structure TubeParameterTerminalCellRepresentativesData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {active : Finset (Fin family.card)}
    {base levels : ℕ}
    (regularized :
      TubeParameterTerminalCellFiberRegularizationData
        family active base levels) where
  index : regularized.cells → Fin family.card
  index_mem_selected :
    ∀ cell, index cell ∈ regularized.selected
  index_cell :
    ∀ cell,
      indexedTubeTerminalCellIndex base levels (index cell) = cell.1
  parameters : DiscreteSet 4
  parameters_eq :
    parameters =
      Finset.univ.image fun cell : regularized.cells =>
        indexedTubeParameterPoint4 (index cell)
  parameters_nonempty : parameters.Nonempty
  representative_injective :
    Function.Injective fun cell : regularized.cells =>
      indexedTubeParameterPoint4 (index cell)
  parameter_terminal_cell :
    ∀ point ∈ parameters,
      ∃ cell : regularized.cells,
        point = indexedTubeParameterPoint4 (index cell) ∧
          tubeParameterGridIndex base levels point = cell.1

/--
Choose one actual source index from every occupied regularized terminal cell.
-/
def TubeParameterTerminalCellRepresentativesStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ family : Kakeya.Streamlined.TubeFamily delta,
      ∀ active : Finset (Fin family.card),
        ∀ base levels : ℕ,
          ∀ regularized :
              TubeParameterTerminalCellFiberRegularizationData
                family active base levels,
            Nonempty
              (TubeParameterTerminalCellRepresentativesData regularized)

end Kakeya.Assouad
