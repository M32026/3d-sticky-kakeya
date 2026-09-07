import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingIntervalCellCountStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridCellDiameterStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridOSStateStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterRepresentativeGridTreeStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.UniformFourBlockRelationDensityStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.WindowParameterCellFourBlockStatement

/-!
# Four-block package at one coarser level of the delta-grid OS tree

The current state has factor-two comparable indexed tube fibers over all
occupied current-level parameter cells.  Exact OS branching gives the same
number of occupied current cells inside every occupied next-level cell.
Therefore the indexed tube fibers over next-level cells remain comparable by
factor two.

One current tube representative is chosen in every next-level cell.  The
windowed cell geometry builds four canonical coarse tubes on that
representative line and covers every current shaded piece assigned to the
cell.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Complete factor-two uniform four-block package at one coarser level. -/
structure TubeParameterGridOSFourBlockPackageData
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {active : Finset (Fin source.card)}
    {base levels : ℕ}
    {terminal :
      TubeParameterTerminalCellFiberRegularizationData
        source active base levels}
    {representatives :
      TubeParameterTerminalCellRepresentativesData terminal}
    {uniform :
      TubeParameterTerminalCellOSLiftData terminal representatives}
    {currentScale : ℝ}
    {currentLevel : ℕ}
    {currentFamily : Kakeya.Streamlined.TubeFamily currentScale}
    {currentShading : Kakeya.Streamlined.TubeShading currentFamily}
    (state :
      TubeParameterGridOSStateData
        terminal representatives uniform currentScale currentLevel
          currentFamily currentShading)
    (fineShading : Kakeya.Streamlined.TubeShading currentFamily)
    (rho : ℝ)
    (nextLevel : ℕ) where
  nextLevel_le_current : nextLevel ≤ currentLevel
  nextLevel_le : nextLevel ≤ levels
  blocks :
    UniformFourBlockRelationData
      (rho := rho) currentFamily fineShading
  representative :
    Fin blocks.parentCount → Fin currentFamily.card
  representative_parent :
    ∀ parentIndex,
      blocks.parent (representative parentIndex) = parentIndex
  nextCells : Finset (Finset (Point 4))
  nextCells_eq :
    let partition : ℕ → Finset (Finset (Point 4)) :=
      fun gridLevel =>
        tubeParameterGridPartition
          base gridLevel representatives.parameters
    nextCells =
      occupiedPartitionCells
        uniform.selectedRepresentatives partition nextLevel
  nextCells_nonempty : nextCells.Nonempty
  parentCount_eq : blocks.parentCount = nextCells.card
  parameter_close :
    let mesh := (base ^ nextLevel : ℝ)⁻¹
    ∀ fineIndex,
      let reference := representative (blocks.parent fineIndex)
      |(tubeParams fineIndex).a -
          (tubeParams reference).a| ≤ mesh ∧
        |(tubeParams fineIndex).b -
          (tubeParams reference).b| ≤ mesh ∧
        |(tubeParams fineIndex).c -
          (tubeParams reference).c| ≤ mesh ∧
        |(tubeParams fineIndex).d -
          (tubeParams reference).d| ≤ mesh
  block_vertical :
    ∀ parentIndex, IsInVerticalChart (blocks.block parentIndex)
  block_base :
    ∀ parentIndex, HasBoundedBase (blocks.block parentIndex) 23
  block_parameters :
    ∀ parentIndex,
      ∀ slot : Fin (blocks.block parentIndex).card,
        tubeParamsOfTube ((blocks.block parentIndex).tube slot) =
          tubeParams (representative parentIndex)
  coarse_nonempty : blocks.coarse.Nonempty
  coarse_vertical : IsInVerticalChart blocks.coarse
  coarse_parameter_bounds :
    ∀ index : Fin blocks.coarse.card,
      |(tubeParams index).a| ≤ 12 ∧
        |(tubeParams index).b| ≤ 12 ∧
        |(tubeParams index).c| ≤ 2 ∧
        |(tubeParams index).d| ≤ 2
  coarse_cells :
    Finset (Finset (Point 4))
  coarse_cells_eq : coarse_cells = nextCells
  coarse_parent :
    Fin blocks.coarse.card → Fin coarse_cells.card
  coarse_parent_surjective :
    Function.Surjective coarse_parent
  coarse_representative :
    Fin coarse_cells.card → Fin blocks.coarse.card
  coarse_representative_parent :
    ∀ cell,
      coarse_parent (coarse_representative cell) = cell
  coarse_parameter_cell :
    ∀ index : Fin blocks.coarse.card,
      tubeParameterGridIndex base nextLevel
          (indexedTubeParameterPoint4 index) =
        tubeParameterGridIndex base nextLevel
          (indexedTubeParameterPoint4
            (coarse_representative (coarse_parent index)))
  coarse_representative_parameter :
    ∀ cell,
      ∃ point ∈ (coarse_cells.equivFin.symm cell).1,
        tubeParameterGridIndex base nextLevel
            (indexedTubeParameterPoint4
              (coarse_representative cell)) =
          tubeParameterGridIndex base nextLevel point
  coarse_fiber_lower :
    ∀ cell : Fin coarse_cells.card,
      4 ≤
        (Finset.univ.filter fun index : Fin blocks.coarse.card =>
          coarse_parent index = cell).card
  coarse_fiber_upper :
    ∀ cell : Fin coarse_cells.card,
      (Finset.univ.filter fun index : Fin blocks.coarse.card =>
        coarse_parent index = cell).card < 8

/--
Direct callable producer for one uniform four-block package.
-/
def TubeParameterGridOSFourBlockPackageInput : Prop :=
  ∀ {delta : ℝ},
            ∀ source : Kakeya.Streamlined.TubeFamily delta,
              ∀ active : Finset (Fin source.card),
                ∀ base levels : ℕ,
                  2 ≤ base →
                  ∀ terminal :
                      TubeParameterTerminalCellFiberRegularizationData
                        source active base levels,
                    ∀ representatives :
                        TubeParameterTerminalCellRepresentativesData terminal,
                      ∀ uniform :
                          TubeParameterTerminalCellOSLiftData
                            terminal representatives,
                        ∀ {currentScale : ℝ},
                          ∀ {currentLevel : ℕ},
                            ∀ currentFamily :
                                Kakeya.Streamlined.TubeFamily currentScale,
                              ∀ currentShading :
                                  Kakeya.Streamlined.TubeShading currentFamily,
                                ∀ state :
                                    TubeParameterGridOSStateData
                                      terminal representatives uniform
                                      currentScale currentLevel
                                      currentFamily currentShading,
                                  ∀ fineShading :
                                      Kakeya.Streamlined.TubeShading
                                        currentFamily,
                                    IsSubshading fineShading currentShading →
                                    IsInSlopeWindow fineShading →
                                    ∀ rho : ℝ,
                                      0 < rho →
                                      rho ≤ 1 / 8 →
                                      ∀ nextLevel : ℕ,
                                        nextLevel ≤ currentLevel →
                                        let mesh :=
                                          (base ^ nextLevel : ℝ)⁻¹
                                        3 * currentScale + 3 * mesh ≤ rho →
                                          Nonempty
                                            (TubeParameterGridOSFourBlockPackageData
                                              state fineShading rho
                                                nextLevel)

/--
Build the direct four-block package producer from the representative tree,
branching count, cell diameter, and windowed cell geometry leaves.
-/
def TubeParameterGridOSFourBlockPackageStatement : Prop :=
  TubeParameterRepresentativeGridTreeStatement →
    OSBranchingIntervalCellCountStatement →
      TubeParameterGridCellDiameterStatement →
        WindowParameterCellFourBlockInput →
          TubeParameterGridOSFourBlockPackageInput

end Kakeya.Assouad
