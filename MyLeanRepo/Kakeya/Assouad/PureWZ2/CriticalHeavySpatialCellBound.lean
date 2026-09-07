import MyLeanRepo.Kakeya.Assouad.PureWZ2.ExtremalHeavySpatialCell
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureCriticalFloorSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationTopLevelAssembly

/-!
# Critical-floor bound for active heavy spatial cells

The fixed-grid heavy-cell construction assigns every retained source tube to
one active cell.  To use the critical floor, each active cell must first
supply a nonempty pure configuration with the critical structural loss,
contained both in the source union and in that fixed grid cell.  The weighted
degree-uniform restriction theorem is the intended producer of these
cell-group configurations.

Once those configurations are available, the critical floor gives the same
volume lower bound in every active cell.  Their unions are pairwise disjoint,
while their total union is contained in the source extremal union.  This
closes the active-cell small-power bound and hence the factor
`6750 * activeCells.card` in the maximal-heavy-cell estimate.

The final interface keeps the critical package before all source choices.
It therefore follows the frozen quantifier order
`sigma -> critical -> outputLoss -> delta0` and closes
`PureWZ2CroppedCriticalNormalizationAt 0` without routing through the older
critical-unaware source-derived leaf.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private theorem criticalHeavy_tubeShading_union_measurable
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : Kakeya.Streamlined.TubeShading family) :
    MeasurableSet shading.union := by
  have unionEq :
      shading.union =
        ⋃ index : Fin family.card, shading.carrier index := by
    ext point
    constructor
    · rintro ⟨index, pointMem⟩
      exact Set.mem_iUnion.mpr ⟨index, pointMem⟩
    · intro pointMem
      rcases Set.mem_iUnion.mp pointMem with
        ⟨index, indexMem⟩
      exact ⟨index, indexMem⟩
  rw [unionEq]
  exact MeasurableSet.iUnion shading.measurable_carrier

/--
One critical-floor-ready pure configuration for every active heavy cell.

The group family may be a degree-regularized subfamily of the raw cell group.
Only nonemptiness, critical-floor CWA and density, source containment, and
fixed-cell containment are needed for the counting argument.
-/
structure PureWZ2CriticalActiveCellFloorSystem
    {sigma sourceLoss pruningLoss floorLoss structuralBudget delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss)
    (floor :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss structuralBudget) where
  groupFamily :
    (ℤ × ℤ × ℤ) → Kakeya.Streamlined.TubeFamily delta
  groupEmbedding :
    ∀ cell, Fin (groupFamily cell).card ↪ Fin source.family.card
  group_tube_eq :
    ∀ cell index,
      (groupFamily cell).tube index =
        source.family.tube (groupEmbedding cell index)
  groupShading :
    ∀ cell, Kakeya.Streamlined.TubeShading (groupFamily cell)
  group_subshading :
    ∀ cell index,
      (groupShading cell).carrier index ⊆
        source.shading.carrier (groupEmbedding cell index)
  group_nonempty :
    ∀ cell ∈ pruning.activeCells, (groupFamily cell).Nonempty
  group_cwa :
    ∀ cell ∈ pruning.activeCells,
      WZ2PaperPureCWAAtNearbyScales
        (groupFamily cell)
        (Kakeya.realRpowENN delta (-floor.structuralLoss))
  group_dense :
    ∀ cell ∈ pruning.activeCells,
      (groupShading cell).IsLambdaDense
        (Kakeya.realRpowENN delta floor.structuralLoss)
  group_union_subset_cell :
    ∀ cell ∈ pruning.activeCells,
      (groupShading cell).union ⊆
        wz1PaperGridCube pureWZ2HeavyCellSide cell

namespace PureWZ2CriticalActiveCellFloorSystem

variable
    {sigma sourceLoss pruningLoss floorLoss structuralBudget delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss}
    {floor :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss structuralBudget}
    (system :
      PureWZ2CriticalActiveCellFloorSystem
        source pruning floor)

/-- Apply the selected critical floor to one active cell group. -/
theorem group_volume_floor
    (deltaFloor : delta ≤ floor.delta₀)
    (cell : ℤ × ℤ × ℤ)
    (cellMem : cell ∈ pruning.activeCells) :
    Kakeya.realRpowENN delta (sigma + floorLoss) ≤
      volume (system.groupShading cell).union := by
  exact
    floor.volume_floor
      delta source.extremal.delta_pos deltaFloor
      (system.groupFamily cell)
      (system.group_nonempty cell cellMem)
      (system.groupShading cell)
      (system.group_cwa cell cellMem)
      (system.group_dense cell cellMem)

/-- Different fixed grid cells carry disjoint group unions. -/
theorem group_unions_pairwiseDisjoint :
    Set.PairwiseDisjoint
      (↑pruning.activeCells : Set (ℤ × ℤ × ℤ))
      (fun cell => (system.groupShading cell).union) := by
  intro first firstMem second secondMem distinct
  exact
    (wz1PaperGridCube_disjoint distinct).mono
      (system.group_union_subset_cell first firstMem)
      (system.group_union_subset_cell second secondMem)

/-- The union of all floor-ready cell groups stays in the source union. -/
theorem group_biUnion_subset_source :
    (⋃ cell ∈ pruning.activeCells,
        (system.groupShading cell).union) ⊆
      source.shading.union := by
  intro point pointMem
  rcases Set.mem_iUnion₂.mp pointMem with
    ⟨cell, cellMem, pointGroup⟩
  rcases pointGroup with ⟨index, pointCarrier⟩
  exact
    ⟨system.groupEmbedding cell index,
      system.group_subshading cell index pointCarrier⟩

include system

/--
Summing the critical floor over the fixed disjoint grid cells bounds the
number of active labels by the source extremal upper volume.
-/
theorem activeCells_mul_floor_le_source :
    delta ≤ floor.delta₀ →
      (pruning.activeCells.card : ENNReal) *
          Kakeya.realRpowENN delta (sigma + floorLoss) ≤
        Kakeya.realRpowENN delta (sigma - sourceLoss) := by
  intro deltaFloor
  calc
    (pruning.activeCells.card : ENNReal) *
          Kakeya.realRpowENN delta (sigma + floorLoss) =
        ∑ _cell ∈ pruning.activeCells,
          Kakeya.realRpowENN delta (sigma + floorLoss) := by
      simp
    _ ≤
        ∑ cell ∈ pruning.activeCells,
          volume
            (PureWZ2CriticalActiveCellFloorSystem.groupShading
              system cell).union := by
      exact
        Finset.sum_le_sum fun cell cellMem =>
          group_volume_floor system deltaFloor cell cellMem
    _ =
        volume
          (⋃ cell ∈ pruning.activeCells,
            (PureWZ2CriticalActiveCellFloorSystem.groupShading
              system cell).union) := by
      symm
      exact
        MeasureTheory.measure_biUnion_finset
          (group_unions_pairwiseDisjoint system)
          (fun cell _ =>
            criticalHeavy_tubeShading_union_measurable
              (PureWZ2CriticalActiveCellFloorSystem.groupShading
                system cell))
    _ ≤ volume source.shading.union :=
      measure_mono (group_biUnion_subset_source system)
    _ ≤ Kakeya.realRpowENN delta (sigma - sourceLoss) :=
      source.extremal.volume_upper

/--
Cancel the common `delta^(sigma-sourceLoss)` factor.  This is the exact
small-power active-cell bound supplied by the critical floor.
-/
theorem activeCells_power_bound
    (deltaFloor : delta ≤ floor.delta₀) :
    (pruning.activeCells.card : ENNReal) *
        Kakeya.realRpowENN delta (sourceLoss + floorLoss) ≤
      1 := by
  let commonPower :=
    Kakeya.realRpowENN delta (sigma - sourceLoss)
  have commonPowerPos : 0 < commonPower := by
    dsimp only [commonPower, Kakeya.realRpowENN]
    exact
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos source.extremal.delta_pos _)
  have commonPowerTop : commonPower ≠ ⊤ := by
    dsimp only [commonPower, Kakeya.realRpowENN]
    exact ENNReal.ofReal_ne_top
  have powerSplit :
      Kakeya.realRpowENN delta (sigma + floorLoss) =
        commonPower *
          Kakeya.realRpowENN delta
            (sourceLoss + floorLoss) := by
    dsimp only [commonPower]
    rw [Subunit.realRpowENN_mul source.extremal.delta_pos]
    congr 1
    ring
  have withCommonPower :
      commonPower *
          ((pruning.activeCells.card : ENNReal) *
            Kakeya.realRpowENN delta
              (sourceLoss + floorLoss)) ≤
        commonPower * 1 := by
    calc
      commonPower *
            ((pruning.activeCells.card : ENNReal) *
              Kakeya.realRpowENN delta
                (sourceLoss + floorLoss)) =
          (pruning.activeCells.card : ENNReal) *
            Kakeya.realRpowENN delta
              (sigma + floorLoss) := by
        rw [powerSplit]
        ring
      _ ≤ Kakeya.realRpowENN delta (sigma - sourceLoss) :=
        activeCells_mul_floor_le_source system deltaFloor
      _ = commonPower * 1 := by
        simp [commonPower]
  exact
    (ENNReal.mul_le_mul_iff_left
      commonPowerPos.ne' commonPowerTop).mp <| by
        simpa [mul_comm] using withCommonPower

/--
Spend the remaining exponent gap on the absolute heavy-cell factor `6750`.
-/
theorem activeCells_absorption
    (cellLoss : ℝ)
    (deltaFloor : delta ≤ floor.delta₀)
    (constantAbsorption :
      (6750 : ENNReal) *
          Kakeya.realRpowENN delta
            (cellLoss - (sourceLoss + floorLoss)) ≤
        1) :
    ((6750 : ENNReal) *
          (pruning.activeCells.card : ENNReal)) *
        Kakeya.realRpowENN delta cellLoss ≤
      1 := by
  have cellPowerSplit :
      Kakeya.realRpowENN delta cellLoss =
        Kakeya.realRpowENN delta
            (sourceLoss + floorLoss) *
          Kakeya.realRpowENN delta
            (cellLoss - (sourceLoss + floorLoss)) := by
    rw [Subunit.realRpowENN_mul source.extremal.delta_pos]
    congr 1
    ring
  calc
    ((6750 : ENNReal) *
          (pruning.activeCells.card : ENNReal)) *
        Kakeya.realRpowENN delta cellLoss =
      ((pruning.activeCells.card : ENNReal) *
          Kakeya.realRpowENN delta
            (sourceLoss + floorLoss)) *
        ((6750 : ENNReal) *
          Kakeya.realRpowENN delta
            (cellLoss - (sourceLoss + floorLoss))) := by
      rw [cellPowerSplit]
      ring
    _ ≤ 1 * 1 := by
      gcongr
      exact activeCells_power_bound system deltaFloor
    _ = 1 := by simp

/--
The critical-floor count closes the scalar hypothesis of the existing
maximal-heavy-cell theorem.
-/
theorem exists_heavyCell_with_source_mass
    (cellLoss : ℝ)
    (deltaFloor : delta ≤ floor.delta₀)
    (constantAbsorption :
      (6750 : ENNReal) *
          Kakeya.realRpowENN delta
            (cellLoss - (sourceLoss + floorLoss)) ≤
        1) :
    ∃ cell ∈ pruning.activeCells,
      Kakeya.realRpowENN delta cellLoss *
          source.shading.mass ≤
        pruning.cellWeight cell := by
  exact
    pruning.exists_max_cell_source_mass_of_absorption
      cellLoss
      (activeCells_absorption system
        cellLoss deltaFloor constantAbsorption)

end PureWZ2CriticalActiveCellFloorSystem

/--
A spatial preselection tied to the particular heavy label selected by the
critical-floor count.
-/
structure PureWZ2HeavyCellPreselectionData
    {sigma sourceLoss pruningLoss cellLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss)
    (cell : ℤ × ℤ × ℤ) where
  data :
    PureWZ2SpatialCellPreselectionData
      (cellLoss := cellLoss) source pruning
  center_eq :
    data.center =
      cellCorner pureWZ2HeavyCellSide cell
  selected_has_label :
    ∀ index,
      pruning.heavyCell (data.preSelected.embedding index) = cell
  localShading_subset_cell :
    ∀ index,
      data.localShading.carrier index ⊆
        wz1PaperGridCube pureWZ2HeavyCellSide cell

/--
One source-level normalization step after the critical floor has selected its
structural loss.

The producer supplies all active cell groups needed by the counting theorem.
After that theorem chooses a heavy cell, `preselection_of_heavy` must supply
the exact preselection and scalar absorptions consumed by
`pureWZ2_spatialCellSelectionCertificate_of_preselection`.  Thus nearby pure
CWA and local density are genuinely restored by the existing weighted
restriction theorem before the remaining rigid/cropped normalization.
-/
structure PureWZ2CriticalHeavySpatialCellNormalizationStep
    {sigma sourceLoss inputLoss pruningLoss outputLoss floorLoss
      structuralBudget cellLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss)
    (floor :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss structuralBudget) where
  floorSystem :
    PureWZ2CriticalActiveCellFloorSystem source pruning floor
  sourceLoss_lt_inputLoss : sourceLoss < inputLoss
  pruningLoss_le_inputLoss : pruningLoss ≤ inputLoss
  delta_lt_one : delta < 1
  constant_absorption :
    (6750 : ENNReal) *
        Kakeya.realRpowENN delta
          (cellLoss - (sourceLoss + floorLoss)) ≤
      1
  preselection_of_heavy :
    ∀ cell ∈ pruning.activeCells,
      Kakeya.realRpowENN delta cellLoss *
            source.shading.mass ≤
          pruning.cellWeight cell →
        ∃ heavyData :
            PureWZ2HeavyCellPreselectionData
              (cellLoss := cellLoss) source pruning cell,
          pureWZ2SpatialCellRegularizationLoss
                (inputLoss - sourceLoss)
                heavyData.data.preSelected.family.card *
              Kakeya.realRpowENN delta
                (inputLoss - cellLoss) ≤
            1 ∧
          wz2PaperPureNearbyRestrictionConstant
              (Kakeya.realRpowENN delta (-sourceLoss))
              (pureWZ2SpatialCellNormalizationWeight
                delta sourceLoss cellLoss)
              (pureWZ2SpatialCellDegreeConstant
                (inputLoss - sourceLoss)
                heavyData.data.preSelected.family.card)
              (pureWZ2SpatialCellRegularizationLoss
                  (inputLoss - sourceLoss)
                  heavyData.data.preSelected.family.card *
                Kakeya.deltaTubeVolume delta) ≤
            Kakeya.realRpowENN delta (-inputLoss)
  normalize_certificate :
    ∀ certificate :
        PureWZ2SpatialCellSelectionCertificate
          (inputLoss := inputLoss) source pruning,
      Nonempty
        (PureWZ2CroppedCriticalNormalizationData
          (outputLoss := outputLoss)
          (certificate.toLocalizedExtremal
            sourceLoss_lt_inputLoss.le) 0)

namespace PureWZ2CriticalHeavySpatialCellNormalizationStep

variable
    {sigma sourceLoss inputLoss pruningLoss outputLoss floorLoss
      structuralBudget cellLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss}
    {floor :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss structuralBudget}
    (step :
      PureWZ2CriticalHeavySpatialCellNormalizationStep
        (inputLoss := inputLoss)
        (outputLoss := outputLoss)
        (cellLoss := cellLoss)
        source pruning floor)

include step

/--
The critical-floor count and weighted preselection producer construct the
existing spatial-cell certificate on the selected heavy cell.
-/
theorem exists_spatialCertificate
    (deltaFloor : delta ≤ floor.delta₀) :
    Nonempty
      (PureWZ2SpatialCellSelectionCertificate
        (inputLoss := inputLoss) source pruning) := by
  rcases
      PureWZ2CriticalActiveCellFloorSystem.exists_heavyCell_with_source_mass
        (system := step.floorSystem)
        cellLoss deltaFloor step.constant_absorption
    with
    ⟨cell, cellMem, heavyMass⟩
  rcases
      step.preselection_of_heavy cell cellMem heavyMass
    with
    ⟨heavyData, massAbsorption, cwaAbsorption⟩
  rcases
      pureWZ2_spatialCellSelectionCertificate_of_preselection
        source pruning heavyData.data
        step.sourceLoss_lt_inputLoss
        step.pruningLoss_le_inputLoss
        step.delta_lt_one
        massAbsorption cwaAbsorption
    with
    ⟨result⟩
  exact ⟨result.certificate⟩

end PureWZ2CriticalHeavySpatialCellNormalizationStep

/--
Critical-aware producer for the heavy-spatial-cell normalization route.

The critical floor is selected before the source scale.  The producer must
recover pure CWA and local density in every active cell at the selected
structural loss, and it must normalize whichever cell the floor count proves
heavy.  In particular, it does not assert hereditary floors for arbitrary
subshadings and does not strengthen `extremal_sequence`.
-/
def PureWZ2CriticalHeavySpatialCellNormalizationProducerAtZero : Prop :=
  ∀ sigma : ℝ,
    ∀ critical : PureWZ2CriticalPackage sigma,
      ∀ outputLoss : ℝ,
        0 < outputLoss →
          ∃ floorLoss structuralBudget : ℝ,
            0 < floorLoss ∧
            0 < structuralBudget ∧
            ∀ floor :
                PureWZ2CriticalFloorSelectionData
                  sigma floorLoss structuralBudget,
              ∃ sourceLoss inputLoss pruningLoss cellLoss delta₁ : ℝ,
                0 < sourceLoss ∧
                0 < inputLoss ∧
                inputLoss ≤ outputLoss ∧
                0 < pruningLoss ∧
                0 < cellLoss ∧
                sourceLoss + floorLoss < cellLoss ∧
                0 < delta₁ ∧
                ∀ delta : ℝ,
                  0 < delta →
                  delta ≤ delta₁ →
                  delta ≤ floor.delta₀ →
                    ∀ source :
                        PureWZ2ExtremalConfiguration
                          sigma sourceLoss delta,
                      ∃ pruning :
                          PureWZ2PerTubeDensityPruningData
                            source pruningLoss,
                        Nonempty
                          (PureWZ2CriticalHeavySpatialCellNormalizationStep
                            (inputLoss := inputLoss)
                            (outputLoss := outputLoss)
                            (cellLoss := cellLoss)
                            source pruning floor)

/--
The critical-aware heavy-cell producer closes the frozen normalization target
at exponent zero with the required quantifier order.
-/
theorem
    pureWZ2_cropped_critical_normalization_of_criticalHeavySpatialCell
    (producer :
      PureWZ2CriticalHeavySpatialCellNormalizationProducerAtZero) :
    PureWZ2CroppedCriticalNormalizationAt 0 := by
  intro sigma critical outputLoss delta₀ outputLossPos delta₀Pos
  rcases
      producer sigma critical outputLoss outputLossPos
    with
    ⟨floorLoss, structuralBudget,
      floorLossPos, structuralBudgetPos, produceForFloor⟩
  let floor :=
    Classical.choice
      (critical.select_pure_floor
        floorLossPos structuralBudgetPos)
  rcases produceForFloor floor with
    ⟨sourceLoss, inputLoss, pruningLoss, cellLoss, delta₁,
      sourceLossPos, inputLossPos, inputLossLe,
      _pruningLossPos, _cellLossPos, _cellGap,
      delta₁Pos, produceAtScale⟩
  let threshold := min delta₀ (min delta₁ floor.delta₀)
  have thresholdPos : 0 < threshold := by
    exact
      lt_min delta₀Pos
        (lt_min delta₁Pos floor.delta₀_pos)
  rcases
      critical.extremal_sequence
        sourceLoss threshold sourceLossPos thresholdPos
    with
    ⟨delta, deltaPos, deltaLe, ⟨source⟩⟩
  have deltaOutput : delta ≤ delta₀ :=
    deltaLe.trans (min_le_left _ _)
  have deltaProducer : delta ≤ delta₁ :=
    deltaLe.trans
      ((min_le_right delta₀ (min delta₁ floor.delta₀)).trans
        (min_le_left delta₁ floor.delta₀))
  have deltaFloor : delta ≤ floor.delta₀ :=
    deltaLe.trans
      ((min_le_right delta₀ (min delta₁ floor.delta₀)).trans
        (min_le_right delta₁ floor.delta₀))
  rcases
      produceAtScale
        delta deltaPos deltaProducer deltaFloor source
    with
    ⟨pruning, ⟨step⟩⟩
  rcases
      PureWZ2CriticalHeavySpatialCellNormalizationStep.exists_spatialCertificate
        (step := step) deltaFloor
    with
    ⟨certificate⟩
  let localized :=
    certificate.toLocalizedExtremal
      step.sourceLoss_lt_inputLoss.le
  exact
    ⟨inputLoss, delta,
      inputLossPos, inputLossLe,
      deltaPos, deltaOutput,
      localized,
      step.normalize_certificate certificate⟩

end Kakeya.Assouad

end
