import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterRepresentativeGridTreeStatement

/-!
# Lift an OS-uniform representative tree to complete terminal-cell tube fibers

Run exact OS branching on one representative point per occupied terminal
`delta`-scale parameter cell.  Then retain every indexed tube in each
surviving terminal cell.  The resulting indexed selection is a union of
complete terminal-cell fibers and has uniform branching on a tree of depth
controlled by the fine scale rather than by arbitrary exact-point spacing.
-/

noncomputable section

namespace Kakeya.Assouad

/--
An OS-uniform representative set together with all indexed tubes in its
surviving complete terminal-cell fibers.
-/
structure TubeParameterTerminalCellOSLiftData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {active : Finset (Fin family.card)}
    {base levels : ℕ}
    (regularized :
      TubeParameterTerminalCellFiberRegularizationData
        family active base levels)
    (representatives :
      TubeParameterTerminalCellRepresentativesData regularized) where
  selectedRepresentatives : DiscreteSet 4
  selectedRepresentatives_nonempty :
    selectedRepresentatives.Nonempty
  selectedRepresentatives_subset :
    selectedRepresentatives ⊆ representatives.parameters
  selectedCells : Finset (Fin 4 → ℤ)
  selectedCells_eq :
    selectedCells =
      regularized.cells.filter fun cell =>
        ∃ point ∈ selectedRepresentatives,
          tubeParameterGridIndex base levels point = cell
  selectedCells_nonempty : selectedCells.Nonempty
  selected : Finset (Fin family.card)
  selected_eq :
    selected =
      regularized.selected.filter fun index =>
        indexedTubeTerminalCellIndex base levels index ∈ selectedCells
  selected_nonempty : selected.Nonempty
  selected_subset : selected ⊆ regularized.selected
  selected_complete_cells :
    ∀ index ∈ regularized.selected,
      indexedTubeTerminalCellIndex base levels index ∈ selectedCells →
        index ∈ selected
  selected_image_cells :
    selected.image (indexedTubeTerminalCellIndex base levels) =
      selectedCells
  fiber_lower :
    ∀ cell ∈ selectedCells,
      regularized.fiberMultiplicity ≤
        (selected.filter fun index =>
          indexedTubeTerminalCellIndex base levels index = cell).card
  fiber_upper :
    ∀ cell ∈ selectedCells,
      (selected.filter fun index =>
        indexedTubeTerminalCellIndex base levels index = cell).card <
          2 * regularized.fiberMultiplicity
  retention :
    (regularized.selected.card : ℝ) ≤
      2 *
        (2 * (Nat.log 2 ((base + 1) ^ 4) + 1) : ℝ) ^ levels *
          (selected.card : ℝ)
  branchExponent : Fin levels → ℕ
  branch_bound :
    ∀ level : Fin levels,
      2 ^ branchExponent level ≤ (base + 1) ^ 4
  branch_uniform :
    let parameters := representatives.parameters
    let partition : ℕ → Finset (Finset (Point 4)) :=
      fun level => tubeParameterGridPartition base level parameters
    ∀ level : Fin levels,
      ∀ parent ∈ partition level,
        (selectedRepresentatives ∩ parent).Nonempty →
          (occupiedPartitionChildren
            selectedRepresentatives partition level parent).card =
              2 ^ branchExponent level

/--
Direct callable producer for the terminal-cell OS lift.
-/
def TubeParameterTerminalCellOSLiftInput : Prop :=
  ∀ {delta : ℝ},
        ∀ family : Kakeya.Streamlined.TubeFamily delta,
          ∀ active : Finset (Fin family.card),
            ∀ base levels : ℕ,
              2 ≤ base →
              ∀ regularized :
                  TubeParameterTerminalCellFiberRegularizationData
                    family active base levels,
                ∀ representatives :
                    TubeParameterTerminalCellRepresentativesData regularized,
                  Nonempty
                    (TubeParameterTerminalCellOSLiftData
                      regularized representatives)

/--
Apply generic OS branching to the representative atomic tree, then expose the
direct lift producer.
-/
def TubeParameterTerminalCellOSLiftStatement : Prop :=
  OSBranchingUniformRefinementStatement →
    TubeParameterRepresentativeGridTreeStatement →
      TubeParameterTerminalCellOSLiftInput

end Kakeya.Assouad
