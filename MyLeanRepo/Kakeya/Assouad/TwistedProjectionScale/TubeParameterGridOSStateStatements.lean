import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingIntervalCellCountStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterTerminalCellOSLiftStatement

/-!
# Iterable states on one delta-grid tube-parameter OS tree

The corrected Section 7 state is indexed by occupied grid cells, not exact
supporting-line points.

At the terminal level, one cell may contain several arbitrarily close exact
parameters and all of their indexed tubes.  At later coarser levels, several
terminal cells are grouped under one ancestor.  The state records:

* the occupied current-level grid indices from the same frozen OS tree;
* a surjective assignment of current tube indices to those grid indices;
* exact agreement between the assignment and each tube's parameter grid
  index;
* factor-two comparability of indexed tube fiber sizes;
* the current shading density and parameter Frostman certificate.
-/

noncomputable section

namespace Kakeya.Assouad

/--
One iterable current family/shading state on the corrected terminal-cell OS
tree.
-/
structure TubeParameterGridOSStateData
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {active : Finset (Fin source.card)}
    {base levels : ℕ}
    (terminal :
      TubeParameterTerminalCellFiberRegularizationData
        source active base levels)
    (representatives :
      TubeParameterTerminalCellRepresentativesData terminal)
    (uniform :
      TubeParameterTerminalCellOSLiftData terminal representatives)
    (scale : ℝ)
    (level : ℕ)
    (family : Kakeya.Streamlined.TubeFamily scale)
    (shading : Kakeya.Streamlined.TubeShading family) where
  level_le : level ≤ levels
  scale_pos : 0 < scale
  scale_le_one : scale ≤ 1
  terminal_or_mesh_control :
    level = levels ∨
      6 * ((base ^ level : ℝ)⁻¹) ≤ scale
  family_nonempty : family.Nonempty
  vertical : IsInVerticalChart family
  parameter_bounds :
    ∀ index : Fin family.card,
      |(tubeParams index).a| ≤ 12 ∧
        |(tubeParams index).b| ≤ 12 ∧
        |(tubeParams index).c| ≤ 2 ∧
        |(tubeParams index).d| ≤ 2
  cells : Finset (Finset (Point 4))
  cells_eq :
    let partition : ℕ → Finset (Finset (Point 4)) :=
      fun gridLevel =>
        tubeParameterGridPartition
          base gridLevel representatives.parameters
    cells =
      occupiedPartitionCells
        uniform.selectedRepresentatives partition level
  cells_nonempty : cells.Nonempty
  parent : Fin family.card → Fin cells.card
  parent_surjective : Function.Surjective parent
  representative : Fin cells.card → Fin family.card
  representative_parent :
    ∀ cell, parent (representative cell) = cell
  parameter_cell :
    ∀ index : Fin family.card,
      tubeParameterGridIndex base level
          (indexedTubeParameterPoint4 index) =
        tubeParameterGridIndex base level
          (indexedTubeParameterPoint4
            (representative (parent index)))
  representative_parameter :
    ∀ cell,
      ∃ point ∈ (cells.equivFin.symm cell).1,
        tubeParameterGridIndex base level
            (indexedTubeParameterPoint4 (representative cell)) =
          tubeParameterGridIndex base level point
  fiberMultiplicity : ℕ
  fiberMultiplicity_pos : 0 < fiberMultiplicity
  fiber_lower :
    ∀ cell : Fin cells.card,
      fiberMultiplicity ≤
        (Finset.univ.filter fun index : Fin family.card =>
          parent index = cell).card
  fiber_upper :
    ∀ cell : Fin cells.card,
      (Finset.univ.filter fun index : Fin family.card =>
        parent index = cell).card <
          2 * fiberMultiplicity
  densityConstant : ENNReal
  density_ne_zero : densityConstant ≠ 0
  density_ne_top : densityConstant ≠ ⊤
  density : shading.IsLambdaDense densityConstant
  slope_window : IsInSlopeWindow shading
  parameterConstant : ENNReal
  parameter_one : 1 ≤ parameterConstant
  parameter_ne_top : parameterConstant ≠ ⊤
  parameter_frostman :
    TubeParameterFrostmanBound family parameterConstant

end Kakeya.Assouad
