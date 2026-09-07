import MyLeanRepo.Kakeya.Assouad.PureWZ2.CriticalHeavySpatialCellBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CallerCenterEnvelopeConflictDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationRigidCropGeometryProducer
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Heavy-cell producer for the critical normalization step

This module closes the record wiring after a critical active-cell floor
system has been fixed.

The heavy-cell preselection is the raw fiber of the chosen heavy-cell label.
Its local shading is the source shading intersected with that cell.  The
base, support, and full-mass statements are the existing conclusions of
`ExtremalHeavySpatialCell`.  A strengthened per-tube pruning estimate pays
the unavoidable factor `3375` and restores the literal local density needed
by `pureWZ2_spatialCellSelectionCertificate_of_preselection`.

Finite rigid geometry selection belongs before weighted regularization.  The
final section therefore exposes a conditional geometry-selected preselection
record and an adapter which restores nearby pure CWA only after that selection,
while retaining direction-cone and near-segment witnesses on the final family.
It makes no cropped-CWA or normalization conclusion.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-! ## Strengthening a pruning for the raw heavy-cell intersection -/

/--
The pointwise estimate needed to recover the literal pruning density after
the fixed `15^3` heavy-cell pigeonhole.
-/
def PureWZ2HeavyCellStrongPerTubeDensity
    {sigma sourceLoss pruningLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss) : Prop :=
  ∀ index ∈ pruning.indices,
    (3375 : ENNReal) *
          (Kakeya.realRpowENN delta pruningLoss *
            (source.family.tube index).volume) ≤
      volume (source.shading.carrier index)

/--
Absorb the factor `3375` between a stronger raw pruning loss and the loss
exposed to the spatial-cell certificate.
-/
theorem pureWZ2_heavyCell_density_power_absorption
    {delta rawPruningLoss pruningLoss : ℝ}
    (deltaPos : 0 < delta)
    (absorption :
      (3375 : ENNReal) *
          Kakeya.realRpowENN delta
            (pruningLoss - rawPruningLoss) ≤
        1) :
    (3375 : ENNReal) *
        Kakeya.realRpowENN delta pruningLoss ≤
      Kakeya.realRpowENN delta rawPruningLoss := by
  have powerSplit :
      Kakeya.realRpowENN delta pruningLoss =
        Kakeya.realRpowENN delta
            (pruningLoss - rawPruningLoss) *
          Kakeya.realRpowENN delta rawPruningLoss := by
    rw [Subunit.realRpowENN_mul deltaPos]
    congr 1
    ring
  rw [powerSplit, ← mul_assoc]
  calc
    ((3375 : ENNReal) *
          Kakeya.realRpowENN delta
            (pruningLoss - rawPruningLoss)) *
        Kakeya.realRpowENN delta rawPruningLoss ≤
      1 * Kakeya.realRpowENN delta rawPruningLoss := by
        gcongr
    _ = Kakeya.realRpowENN delta rawPruningLoss := one_mul _

namespace PureWZ2PerTubeDensityPruningData

variable
    {sigma sourceLoss rawPruningLoss pruningLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}

private theorem target_power_le_raw
    (densityAbsorption :
      (3375 : ENNReal) *
          Kakeya.realRpowENN delta pruningLoss ≤
        Kakeya.realRpowENN delta rawPruningLoss) :
    Kakeya.realRpowENN delta pruningLoss ≤
      Kakeya.realRpowENN delta rawPruningLoss := by
  calc
    Kakeya.realRpowENN delta pruningLoss =
        1 * Kakeya.realRpowENN delta pruningLoss := by
      rw [one_mul]
    _ ≤
        (3375 : ENNReal) *
          Kakeya.realRpowENN delta pruningLoss := by
      exact
        (mul_le_mul_right'
          (show (1 : ENNReal) ≤ 3375 by norm_num)
          (Kakeya.realRpowENN delta pruningLoss))
    _ ≤ Kakeya.realRpowENN delta rawPruningLoss :=
      densityAbsorption

/--
Reuse the same retained indices at a weaker loss while remembering enough of
the raw pointwise estimate to pay the heavy-cell factor.
-/
noncomputable def weakenForHeavyCells
    (raw :
      PureWZ2PerTubeDensityPruningData source rawPruningLoss)
    (densityAbsorption :
      (3375 : ENNReal) *
          Kakeya.realRpowENN delta pruningLoss ≤
        Kakeya.realRpowENN delta rawPruningLoss) :
    PureWZ2PerTubeDensityPruningData source pruningLoss where
  indices := raw.indices
  nonempty := raw.nonempty
  cardinality_retention := by
    calc
      Kakeya.realRpowENN delta pruningLoss *
            source.family.enncard ≤
          Kakeya.realRpowENN delta rawPruningLoss *
            source.family.enncard := by
        gcongr
        exact target_power_le_raw densityAbsorption
      _ ≤
          (selectedTubeFamily source.family raw.indices).enncard :=
        raw.cardinality_retention
  mass_retention := raw.mass_retention
  per_tube_density := by
    intro index indexMem
    calc
      Kakeya.realRpowENN delta pruningLoss *
            (source.family.tube index).volume ≤
          Kakeya.realRpowENN delta rawPruningLoss *
            (source.family.tube index).volume := by
        gcongr
        exact target_power_le_raw densityAbsorption
      _ ≤ volume (source.shading.carrier index) :=
        raw.per_tube_density index indexMem

/--
The weakened pruning carries the stronger pointwise estimate needed by the
raw heavy-cell intersection.
-/
theorem weakenForHeavyCells_strongPerTubeDensity
    (raw :
      PureWZ2PerTubeDensityPruningData source rawPruningLoss)
    (densityAbsorption :
      (3375 : ENNReal) *
          Kakeya.realRpowENN delta pruningLoss ≤
        Kakeya.realRpowENN delta rawPruningLoss) :
    PureWZ2HeavyCellStrongPerTubeDensity
      source (raw.weakenForHeavyCells densityAbsorption) := by
  intro index indexMem
  calc
    (3375 : ENNReal) *
          (Kakeya.realRpowENN delta pruningLoss *
            (source.family.tube index).volume) =
        ((3375 : ENNReal) *
            Kakeya.realRpowENN delta pruningLoss) *
          (source.family.tube index).volume := by ring
    _ ≤
        Kakeya.realRpowENN delta rawPruningLoss *
          (source.family.tube index).volume := by
      gcongr
    _ ≤ volume (source.shading.carrier index) :=
      raw.per_tube_density index indexMem

end PureWZ2PerTubeDensityPruningData

/-! ## The concrete raw heavy-cell preselection -/

/-- Ambient indices assigned to one fixed heavy-cell label. -/
def pureWZ2HeavyCellIndices
    {sigma sourceLoss pruningLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss)
    (cell : ℤ × ℤ × ℤ) :
    Finset (Fin source.family.card) :=
  pruning.indices.filter fun index =>
    pruning.heavyCell index = cell

/-- The raw tube group over one heavy-cell label. -/
noncomputable def pureWZ2HeavyCellSubfamily
    {sigma sourceLoss pruningLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss)
    (cell : ℤ × ℤ × ℤ) :
    WZ2PaperPureTubeSubfamily source.family :=
  WZ2PaperPureTubeSubfamily.fromFinset
    source.family (pureWZ2HeavyCellIndices pruning cell)

/-- The literal source shading intersected with one heavy cell. -/
noncomputable def pureWZ2HeavyCellLocalShading
    {sigma sourceLoss pruningLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss)
    (cell : ℤ × ℤ × ℤ) :
    Kakeya.Streamlined.TubeShading
      (pureWZ2HeavyCellSubfamily source pruning cell).family where
  carrier index :=
    source.shading.carrier
        ((pureWZ2HeavyCellSubfamily
          source pruning cell).embedding index) ∩
      wz1PaperGridCube pureWZ2HeavyCellSide cell
  measurable_carrier index :=
    (source.shading.measurable_carrier
      ((pureWZ2HeavyCellSubfamily
        source pruning cell).embedding index)).inter
        (wz1PaperGridCube_measurable cell)
  subset_body index := by
    change
      source.shading.carrier
            ((pureWZ2HeavyCellSubfamily
              source pruning cell).embedding index) ∩
          wz1PaperGridCube pureWZ2HeavyCellSide cell ⊆
        ((pureWZ2HeavyCellSubfamily
          source pruning cell).family.tube index).carrier
    rw [(pureWZ2HeavyCellSubfamily
      source pruning cell).tube_eq index]
    exact Set.Subset.trans Set.inter_subset_left
      (source.shading.subset_body _)

namespace PureWZ2PerTubeDensityPruningData

variable
    {sigma sourceLoss pruningLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss)
    (cell : ℤ × ℤ × ℤ)

theorem heavyCellSubfamily_embedding_mem
    (index :
      Fin
        (pureWZ2HeavyCellSubfamily
          source pruning cell).family.card) :
    (pureWZ2HeavyCellSubfamily
      source pruning cell).embedding index ∈
      pureWZ2HeavyCellIndices pruning cell := by
  dsimp only [pureWZ2HeavyCellSubfamily,
    WZ2PaperPureTubeSubfamily.fromFinset]
  exact Finset.orderEmbOfFin_mem
    (pureWZ2HeavyCellIndices pruning cell) rfl index

theorem heavyCellSubfamily_embedding_pruning_mem
    (index :
      Fin
        (pureWZ2HeavyCellSubfamily
          source pruning cell).family.card) :
    (pureWZ2HeavyCellSubfamily
      source pruning cell).embedding index ∈ pruning.indices :=
  (Finset.mem_filter.mp
    (pruning.heavyCellSubfamily_embedding_mem cell index)).1

theorem heavyCellSubfamily_embedding_label
    (index :
      Fin
        (pureWZ2HeavyCellSubfamily
          source pruning cell).family.card) :
    pruning.heavyCell
        ((pureWZ2HeavyCellSubfamily
          source pruning cell).embedding index) =
      cell :=
  (Finset.mem_filter.mp
    (pruning.heavyCellSubfamily_embedding_mem cell index)).2

theorem heavyCellIndices_nonempty
    (cellMem : cell ∈ pruning.activeCells) :
    (pureWZ2HeavyCellIndices pruning cell).Nonempty := by
  rcases Finset.mem_image.mp cellMem with
    ⟨index, indexMem, labelEq⟩
  exact
    ⟨index,
      Finset.mem_filter.mpr
        ⟨indexMem, labelEq⟩⟩

theorem heavyCellLocalShading_mass :
    (pureWZ2HeavyCellLocalShading
      source pruning cell).mass =
      pruning.cellWeight cell := by
  let indices := pureWZ2HeavyCellIndices pruning cell
  let equivalence : Fin indices.card ≃ indices :=
    (indices.orderIsoOfFin rfl).toEquiv
  change
    (∑ index : Fin indices.card,
        volume
          (source.shading.carrier
              ((indices.orderEmbOfFin rfl).toEmbedding index) ∩
            wz1PaperGridCube pureWZ2HeavyCellSide cell)) =
      ∑ index ∈ indices,
        volume
          (source.shading.carrier index ∩
            wz1PaperGridCube pureWZ2HeavyCellSide cell)
  calc
    (∑ index : Fin indices.card,
        volume
          (source.shading.carrier
              ((indices.orderEmbOfFin rfl).toEmbedding index) ∩
            wz1PaperGridCube pureWZ2HeavyCellSide cell)) =
        ∑ index : indices,
          volume
            (source.shading.carrier index.1 ∩
              wz1PaperGridCube pureWZ2HeavyCellSide cell) := by
      exact
        Fintype.sum_equiv equivalence
          (fun index : Fin indices.card =>
            volume
              (source.shading.carrier
                  ((indices.orderEmbOfFin rfl).toEmbedding index) ∩
                wz1PaperGridCube pureWZ2HeavyCellSide cell))
          (fun index : indices =>
            volume
              (source.shading.carrier index.1 ∩
                wz1PaperGridCube pureWZ2HeavyCellSide cell))
          (fun _ => rfl)
    _ =
        ∑ index ∈ indices,
          volume
            (source.shading.carrier index ∩
              wz1PaperGridCube pureWZ2HeavyCellSide cell) := by
      exact
        Finset.sum_coe_sort indices fun index =>
          volume
            (source.shading.carrier index ∩
              wz1PaperGridCube pureWZ2HeavyCellSide cell)

theorem heavyCellLocalShading_per_tube_density
    (strongDensity :
      PureWZ2HeavyCellStrongPerTubeDensity source pruning)
    (index :
      Fin
        (pureWZ2HeavyCellSubfamily
          source pruning cell).family.card) :
    Kakeya.realRpowENN delta pruningLoss *
          ((pureWZ2HeavyCellSubfamily
            source pruning cell).family.tube index).volume ≤
      volume
        ((pureWZ2HeavyCellLocalShading
          source pruning cell).carrier index) := by
  let ambientIndex :=
    (pureWZ2HeavyCellSubfamily
      source pruning cell).embedding index
  have ambientMem : ambientIndex ∈ pruning.indices :=
    pruning.heavyCellSubfamily_embedding_pruning_mem cell index
  have labelEq : pruning.heavyCell ambientIndex = cell :=
    pruning.heavyCellSubfamily_embedding_label cell index
  have scaled :=
    mul_le_mul_left'
      (strongDensity ambientIndex ambientMem) (3375 : ENNReal)⁻¹
  have heavy := pruning.heavyCell_full_mass ambientIndex ambientMem
  have inverseCancel :
      (3375 : ENNReal)⁻¹ * 3375 = 1 :=
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  rw [(pureWZ2HeavyCellSubfamily
    source pruning cell).tube_eq index]
  change
    Kakeya.realRpowENN delta pruningLoss *
          (source.family.tube ambientIndex).volume ≤
      volume
        (source.shading.carrier ambientIndex ∩
          wz1PaperGridCube pureWZ2HeavyCellSide cell)
  calc
    Kakeya.realRpowENN delta pruningLoss *
          (source.family.tube ambientIndex).volume =
        (3375 : ENNReal)⁻¹ *
          ((3375 : ENNReal) *
            (Kakeya.realRpowENN delta pruningLoss *
              (source.family.tube ambientIndex).volume)) := by
      rw [← mul_assoc, inverseCancel, one_mul]
    _ ≤
        (3375 : ENNReal)⁻¹ *
          volume (source.shading.carrier ambientIndex) :=
      scaled
    _ ≤
        volume
          (source.shading.carrier ambientIndex ∩
            wz1PaperGridCube pureWZ2HeavyCellSide cell) := by
      simpa [labelEq] using heavy

theorem heavyCellSubfamily_base
    (index :
      Fin
        (pureWZ2HeavyCellSubfamily
          source pruning cell).family.card) :
    dist
        ((pureWZ2HeavyCellSubfamily
          source pruning cell).family.tube index).base
        (cellCorner pureWZ2HeavyCellSide cell) ≤
      3 := by
  rw [(pureWZ2HeavyCellSubfamily
    source pruning cell).tube_eq index]
  simpa [pruning.heavyCellSubfamily_embedding_label cell index] using
    pruning.heavyCell_base
      ((pureWZ2HeavyCellSubfamily
        source pruning cell).embedding index)
      (pruning.heavyCellSubfamily_embedding_pruning_mem cell index)

theorem heavyCellLocalShading_support :
    (pureWZ2HeavyCellLocalShading
      source pruning cell).union ⊆
      Metric.closedBall
        (cellCorner pureWZ2HeavyCellSide cell) 1 := by
  rintro point ⟨index, pointMem⟩
  exact pureWZ2_gridCube_subset_corner_closedBall cell pointMem.2

end PureWZ2PerTubeDensityPruningData

/--
The raw group of all retained tubes assigned to one heavy cell, equipped
with their literal intersections with that cell.
-/
noncomputable def pureWZ2_heavyCellPreselectionData
    {sigma sourceLoss pruningLoss cellLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss)
    (strongDensity :
      PureWZ2HeavyCellStrongPerTubeDensity source pruning)
    (cell : ℤ × ℤ × ℤ)
    (cellMem : cell ∈ pruning.activeCells)
    (heavyMass :
      Kakeya.realRpowENN delta cellLoss *
            source.shading.mass ≤
        pruning.cellWeight cell) :
    PureWZ2HeavyCellPreselectionData
      (cellLoss := cellLoss) source pruning cell :=
  {
    data :=
      {
        preSelected := pureWZ2HeavyCellSubfamily source pruning cell
        preSelected_nonempty :=
          (pruning.heavyCellIndices_nonempty cell cellMem).card_pos
        selected_from_pruning :=
          pruning.heavyCellSubfamily_embedding_pruning_mem cell
        localShading :=
          pureWZ2HeavyCellLocalShading source pruning cell
        subshading := fun _ => Set.inter_subset_left
        per_tube_local_density :=
          pruning.heavyCellLocalShading_per_tube_density
            cell strongDensity
        source_mass_retention := by
          rw [pruning.heavyCellLocalShading_mass cell]
          exact heavyMass
        center := cellCorner pureWZ2HeavyCellSide cell
        family_bases_local := pruning.heavyCellSubfamily_base cell
        shading_support_local :=
          pruning.heavyCellLocalShading_support cell
      }
    center_eq := rfl
    selected_has_label :=
      pruning.heavyCellSubfamily_embedding_label cell
    localShading_subset_cell := fun _ => Set.inter_subset_right
  }

/--
The critical active-cell count selects a genuine heavy-cell preselection.

The returned local shading is the literal intersection of every selected
source shading with the same grid cell.  Thus this packages the geometric
selection itself, before any weighted CWA regularization.
-/
theorem
    PureWZ2CriticalActiveCellFloorSystem.exists_heavyCellPreselectionData
    {sigma sourceLoss pruningLoss floorLoss structuralBudget cellLoss
      delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss}
    {floor :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss structuralBudget}
    (system :
      PureWZ2CriticalActiveCellFloorSystem source pruning floor)
    (strongDensity :
      PureWZ2HeavyCellStrongPerTubeDensity source pruning)
    (deltaFloor : delta ≤ floor.delta₀)
    (constantAbsorption :
      (6750 : ENNReal) *
          Kakeya.realRpowENN delta
            (cellLoss - (sourceLoss + floorLoss)) ≤
        1) :
    ∃ cell ∈ pruning.activeCells,
      Nonempty
        (PureWZ2HeavyCellPreselectionData
          (cellLoss := cellLoss) source pruning cell) := by
  rcases
      system.exists_heavyCell_with_source_mass
        cellLoss deltaFloor constantAbsorption
    with ⟨cell, cellMem, heavyMass⟩
  exact
    ⟨cell, cellMem,
      ⟨pureWZ2_heavyCellPreselectionData
        source pruning strongDensity cell cellMem heavyMass⟩⟩

/--
Forget the selected heavy-cell label and expose the spatial preselection
interface consumed by the weighted regularizer.
-/
theorem
    PureWZ2CriticalActiveCellFloorSystem.exists_spatialCellPreselectionData
    {sigma sourceLoss pruningLoss floorLoss structuralBudget cellLoss
      delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss}
    {floor :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss structuralBudget}
    (system :
      PureWZ2CriticalActiveCellFloorSystem source pruning floor)
    (strongDensity :
      PureWZ2HeavyCellStrongPerTubeDensity source pruning)
    (deltaFloor : delta ≤ floor.delta₀)
    (constantAbsorption :
      (6750 : ENNReal) *
          Kakeya.realRpowENN delta
            (cellLoss - (sourceLoss + floorLoss)) ≤
        1) :
    Nonempty
      (PureWZ2SpatialCellPreselectionData
        (cellLoss := cellLoss) source pruning) := by
  rcases
      system.exists_heavyCellPreselectionData
        strongDensity deltaFloor constantAbsorption
    with ⟨_cell, _cellMem, ⟨heavyData⟩⟩
  exact ⟨heavyData.data⟩

/-! ## Uniform bounds for the actual weighted regularization constants -/

/-- Fixed coefficient in the heavy-cell logarithmic cardinality bound. -/
def pureWZ2HeavyCellCardLogConstant : ℝ :=
  max
    (6 * Real.log 515 / Real.log 2 + 2)
    (6 / Real.log 2)

private theorem pureWZ2HeavyCellSubfamily_card_bound
    {sigma sourceLoss pruningLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss)
    (cell : ℤ × ℤ × ℤ)
    (cellMem : cell ∈ pruning.activeCells) :
    (pureWZ2HeavyCellSubfamily source pruning cell).family.card ≤
      (2 * Nat.ceil (256 / delta) + 1) ^ 6 := by
  let family :=
    (pureWZ2HeavyCellSubfamily source pruning cell).family
  have familyDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct family :=
    source.extremal.cwa_nearby_scales.2.2.1.subfamily
      (pureWZ2HeavyCellSubfamily source pruning cell)
  have midpointLocal :
      ∀ index : Fin family.card,
        ‖wz2PaperTubeMidpoint (family.tube index) -
            cellCorner pureWZ2HeavyCellSide cell‖ ≤
          4 := by
    intro index
    have baseLocal :=
      pruning.heavyCellSubfamily_base cell index
    have directionUnit := (family.tube index).direction_unit
    have identity :
        wz2PaperTubeMidpoint (family.tube index) -
            cellCorner pureWZ2HeavyCellSide cell =
          ((family.tube index).base -
              cellCorner pureWZ2HeavyCellSide cell) +
            (1 / 2 : ℝ) • (family.tube index).direction := by
      simp [wz2PaperTubeMidpoint]
      module
    rw [identity]
    calc
      ‖((family.tube index).base -
              cellCorner pureWZ2HeavyCellSide cell) +
            (1 / 2 : ℝ) • (family.tube index).direction‖ ≤
          ‖(family.tube index).base -
              cellCorner pureWZ2HeavyCellSide cell‖ +
            ‖(1 / 2 : ℝ) • (family.tube index).direction‖ :=
        norm_add_le _ _
      _ = dist (family.tube index).base
              (cellCorner pureWZ2HeavyCellSide cell) +
            1 / 2 := by
        rw [dist_eq_norm, norm_smul, directionUnit]
        norm_num
      _ ≤ 3 + 1 / 2 := by
        gcongr
      _ ≤ 4 := by norm_num
  have rawBound :=
    wz2PaperOrdinary_local_six_grid_card_bound
      source.extremal.delta_pos
      (show (0 : ℝ) ≤ 4 by norm_num)
      familyDistinct Finset.univ
      (cellCorner pureWZ2HeavyCellSide cell)
      (fun index _ => midpointLocal index)
  let scaleCount := Nat.ceil (256 / delta)
  have firstArgument :
      4 / (delta / 64) = 256 / delta := by
    field_simp [source.extremal.delta_pos.ne']
    norm_num
  have secondArgument :
      1 / (delta / 64) ≤ 256 / delta := by
    have deltaPos := source.extremal.delta_pos
    have :
        1 / (delta / 64) = 64 / delta := by
      field_simp [deltaPos.ne']
    rw [this]
    exact div_le_div_of_nonneg_right (by norm_num) deltaPos.le
  have firstCeil :
      Nat.ceil (4 / (delta / 64)) = scaleCount := by
    rw [firstArgument]
  have secondCeil :
      Nat.ceil (1 / (delta / 64)) ≤ scaleCount :=
    Nat.ceil_mono secondArgument
  have rawBound' :
      family.card ≤
        (2 * Nat.ceil (4 / (delta / 64)) + 1) ^ 3 *
          (2 * Nat.ceil (1 / (delta / 64)) + 1) ^ 3 := by
    simpa using rawBound
  change family.card ≤ _
  calc
    family.card ≤
        (2 * Nat.ceil (4 / (delta / 64)) + 1) ^ 3 *
          (2 * Nat.ceil (1 / (delta / 64)) + 1) ^ 3 := by
      exact rawBound'
    _ ≤
        (2 * scaleCount + 1) ^ 3 *
          (2 * scaleCount + 1) ^ 3 := by
      rw [firstCeil]
      gcongr
    _ = (2 * scaleCount + 1) ^ 6 := by ring

theorem pureWZ2HeavyCell_card_log_bound
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    {cardinality : ℕ}
    (cardBound :
      cardinality ≤
        (2 * Nat.ceil (256 / delta) + 1) ^ 6) :
    (Nat.log 2 (2 * cardinality) + 1 : ℝ) ≤
      pureWZ2HeavyCellCardLogConstant *
        (1 + Real.log delta⁻¹) := by
  let bound : ℕ := 2 * Nat.ceil (256 / delta) + 1
  have boundPos : 0 < bound := by positivity
  have logTwoPos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num)
  have ceilLt :
      (Nat.ceil (256 / delta) : ℝ) <
        256 / delta + 1 := by
    have ceilPos : 0 < Nat.ceil (256 / delta) := by
      apply Nat.ceil_pos.mpr
      positivity
    have predecessor :
        Nat.ceil (256 / delta) - 1 <
          Nat.ceil (256 / delta) := by omega
    have lower :
        ((Nat.ceil (256 / delta) - 1 : ℕ) : ℝ) <
          256 / delta :=
      Nat.lt_ceil.mp predecessor
    have cast :
        ((Nat.ceil (256 / delta) - 1 : ℕ) : ℝ) =
          (Nat.ceil (256 / delta) : ℝ) - 1 := by
      simp [ceilPos]
    rw [cast] at lower
    linarith
  have boundLe : (bound : ℝ) ≤ 515 / delta := by
    have cast :
        (bound : ℝ) =
          2 * (Nat.ceil (256 / delta) : ℝ) + 1 := by
      simp [bound]
    rw [cast]
    have threeLe : 3 ≤ 3 / delta := by
      calc
        (3 : ℝ) = 3 / 1 := by norm_num
        _ ≤ 3 / delta := by gcongr
    exact (calc
      2 * (Nat.ceil (256 / delta) : ℝ) + 1 <
          2 * (256 / delta + 1) + 1 := by
        gcongr
      _ = 512 / delta + 3 := by ring
      _ ≤ 512 / delta + 3 / delta := by
        gcongr
      _ = 515 / delta := by
        field_simp [deltaPos.ne']
        ring).le
  by_cases cardinalityZero : cardinality = 0
  · have logInvNonnegative : 0 ≤ Real.log delta⁻¹ := by
      apply Real.log_nonneg
      calc
        (1 : ℝ) = (1 : ℝ)⁻¹ := by norm_num
        _ ≤ delta⁻¹ := by gcongr
    have constantOne :
        1 ≤ pureWZ2HeavyCellCardLogConstant := by
      have logPositive : 0 < Real.log 515 :=
        Real.log_pos (by norm_num)
      have quotientPositive :
          0 < 6 * Real.log 515 / Real.log 2 := by
        positivity
      exact
        (show (1 : ℝ) ≤
            6 * Real.log 515 / Real.log 2 + 2 by
          linarith).trans (le_max_left _ _)
    rw [cardinalityZero]
    simp
    have constantNonnegative :
        0 ≤ pureWZ2HeavyCellCardLogConstant :=
      zero_le_one.trans constantOne
    have onePlus :
        1 ≤ 1 + Real.log delta⁻¹ := by
      linarith
    have final :
        (1 : ℝ) ≤
          pureWZ2HeavyCellCardLogConstant *
            (1 + Real.log delta⁻¹) := by
      calc
      (1 : ℝ) ≤ pureWZ2HeavyCellCardLogConstant :=
        constantOne
      _ = pureWZ2HeavyCellCardLogConstant * 1 := by
        rw [mul_one]
      _ ≤
          pureWZ2HeavyCellCardLogConstant *
            (1 + Real.log delta⁻¹) :=
        mul_le_mul_of_nonneg_left onePlus constantNonnegative
    simpa [Real.log_inv] using final
  · have cardinalityPos : 0 < cardinality :=
      Nat.pos_of_ne_zero cardinalityZero
    have doublePos : 0 < 2 * cardinality := by positivity
    have natLog :
        (Nat.log 2 (2 * cardinality) : ℝ) ≤
          Real.log ((2 * cardinality : ℕ) : ℝ) /
            Real.log 2 := by
      have power :
          (2 : ℕ) ^ Nat.log 2 (2 * cardinality) ≤
            2 * cardinality :=
        Nat.pow_log_le_self 2 doublePos.ne'
      have powerReal :
          (2 : ℝ) ^ Nat.log 2 (2 * cardinality) ≤
            ((2 * cardinality : ℕ) : ℝ) := by
        exact_mod_cast power
      have logarithm :=
        Real.log_le_log (by positivity) powerReal
      rw [Real.log_pow] at logarithm
      exact (le_div_iff₀ logTwoPos).mpr (by simpa using logarithm)
    have cardinalityReal :
        (cardinality : ℝ) ≤ (bound : ℝ) ^ 6 := by
      exact_mod_cast cardBound
    have doubleReal :
        ((2 * cardinality : ℕ) : ℝ) ≤
          2 * (bound : ℝ) ^ 6 := by
      exact_mod_cast
        (mul_le_mul_left' cardBound 2)
    have logBound :
        Real.log ((2 * cardinality : ℕ) : ℝ) ≤
          Real.log (2 * (bound : ℝ) ^ 6) :=
      Real.log_le_log (by exact_mod_cast doublePos) doubleReal
    have boundLog :
        Real.log (bound : ℝ) ≤ Real.log (515 / delta) :=
      Real.log_le_log (by exact_mod_cast boundPos) boundLe
    have quotientLog :
        Real.log (515 / delta) =
          Real.log 515 + Real.log delta⁻¹ := by
      rw [Real.log_div (by norm_num) deltaPos.ne',
        Real.log_inv]
      ring
    have raw :
        (Nat.log 2 (2 * cardinality) + 1 : ℝ) ≤
          (6 * Real.log 515 / Real.log 2 + 2) +
            (6 / Real.log 2) * Real.log delta⁻¹ := by
      calc
        (Nat.log 2 (2 * cardinality) + 1 : ℝ) ≤
            Real.log ((2 * cardinality : ℕ) : ℝ) /
                Real.log 2 + 1 := by
          linarith
        _ ≤
            Real.log (2 * (bound : ℝ) ^ 6) /
                Real.log 2 + 1 := by
          gcongr
        _ =
            2 + 6 * Real.log (bound : ℝ) /
              Real.log 2 := by
          rw [Real.log_mul
              (by norm_num : (2 : ℝ) ≠ 0)
              (pow_ne_zero 6 (by exact_mod_cast boundPos.ne')),
            Real.log_pow]
          field_simp [logTwoPos.ne']
          ring
        _ ≤
            2 + 6 * Real.log (515 / delta) /
              Real.log 2 := by
          gcongr
        _ =
            (6 * Real.log 515 / Real.log 2 + 2) +
              (6 / Real.log 2) * Real.log delta⁻¹ := by
          rw [quotientLog]
          field_simp [logTwoPos.ne']
          ring
    have logInvNonnegative : 0 ≤ Real.log delta⁻¹ := by
      apply Real.log_nonneg
      calc
        (1 : ℝ) = (1 : ℝ)⁻¹ := by norm_num
        _ ≤ delta⁻¹ := by gcongr
    calc
      (Nat.log 2 (2 * cardinality) + 1 : ℝ) ≤
          (6 * Real.log 515 / Real.log 2 + 2) +
            (6 / Real.log 2) * Real.log delta⁻¹ := raw
      _ ≤
          pureWZ2HeavyCellCardLogConstant +
            pureWZ2HeavyCellCardLogConstant *
              Real.log delta⁻¹ := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
      _ =
          pureWZ2HeavyCellCardLogConstant *
            (1 + Real.log delta⁻¹) := by ring

/--
The two exact scalar hypotheses consumed by the weighted spatial-cell
regularizer, uniformly for every cardinality satisfying the heavy-cell
logarithmic envelope.
-/
def PureWZ2HeavyCellActualAbsorptionsAtScale
    (sourceLoss inputLoss cellLoss delta : ℝ) : Prop :=
  ∀ cardinality : ℕ,
    (Nat.log 2 (2 * cardinality) + 1 : ℝ) ≤
        pureWZ2HeavyCellCardLogConstant *
          (1 + Real.log delta⁻¹) →
      pureWZ2SpatialCellRegularizationLoss
            (inputLoss - sourceLoss) cardinality *
          Kakeya.realRpowENN delta
            (inputLoss - cellLoss) ≤
        1 ∧
      wz2PaperPureNearbyRestrictionConstant
          (Kakeya.realRpowENN delta (-sourceLoss))
          (pureWZ2SpatialCellNormalizationWeight
            delta sourceLoss cellLoss)
          (pureWZ2SpatialCellDegreeConstant
            (inputLoss - sourceLoss) cardinality)
          (pureWZ2SpatialCellRegularizationLoss
              (inputLoss - sourceLoss) cardinality *
            Kakeya.deltaTubeVolume delta) ≤
        Kakeya.realRpowENN delta (-inputLoss)

/--
One source-uniform threshold absorbs the actual finite constants returned by
the weighted regularizer.

The restriction ratio contains three copies of the source CWA power and one
copy of the cell normalization power after the normalization weight and tube
volume cancel.  Hence the precise strict gap is
`3 * sourceLoss + cellLoss < inputLoss`.
-/
theorem exists_pureWZ2HeavyCellActualAbsorptions
    {sourceLoss inputLoss cellLoss : ℝ}
    (inputLossPos : 0 < inputLoss)
    (sourceLossLtInputLoss : sourceLoss < inputLoss)
    (cellLossLtInputLoss : cellLoss < inputLoss)
    (restrictionGap :
      3 * sourceLoss + cellLoss < inputLoss) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ delta : ℝ,
        0 < delta →
        delta ≤ delta₀ →
          PureWZ2HeavyCellActualAbsorptionsAtScale
            sourceLoss inputLoss cellLoss delta := by
  let epsilon := inputLoss - sourceLoss
  let scaleCount := geometricScaleCount epsilon
  have epsilonPos : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  have scaleCountPos : 0 < scaleCount := by
    dsimp only [scaleCount, geometricScaleCount]
    omega
  have massGapPos : 0 < inputLoss - cellLoss := by
    linarith
  have ratioGapPos :
      0 < inputLoss - (3 * sourceLoss + cellLoss) := by
    linarith
  let degreeCoefficient : ENNReal :=
    16 * (scaleCount : ENNReal)
  let ratioCoefficient : ENNReal :=
    128 * (scaleCount : ENNReal)
  have degreeCoefficientFinite :
      degreeCoefficient ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.natCast_ne_top _)
  have ratioCoefficientFinite :
      ratioCoefficient ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.natCast_ne_top _)
  have logConstantNonnegative :
      0 ≤ pureWZ2HeavyCellCardLogConstant := by
    dsimp only [pureWZ2HeavyCellCardLogConstant]
    exact le_max_of_le_right (by positivity)
  rcases
      exists_delta_C_pow_log_absorbed_ennreal
        (8 : ENNReal) (by norm_num)
        pureWZ2HeavyCellCardLogConstant
        logConstantNonnegative massGapPos
        (show 0 < scaleCount + 1 by omega)
    with
    ⟨massDelta, massDeltaPos, massDeltaLeOne, massBound⟩
  rcases
      exists_delta_C_pow_log_absorbed_ennreal
        degreeCoefficient degreeCoefficientFinite
        pureWZ2HeavyCellCardLogConstant
        logConstantNonnegative inputLossPos scaleCountPos
    with
    ⟨degreeDelta, degreeDeltaPos,
      degreeDeltaLeOne, degreeBound⟩
  rcases
      exists_delta_C_pow_log_absorbed_ennreal
        ratioCoefficient ratioCoefficientFinite
        pureWZ2HeavyCellCardLogConstant
        logConstantNonnegative ratioGapPos
        (show 0 < 2 * scaleCount + 1 by omega)
    with
    ⟨ratioDelta, ratioDeltaPos,
      ratioDeltaLeOne, ratioBound⟩
  let delta₀ := min massDelta (min degreeDelta ratioDelta)
  have delta₀Pos : 0 < delta₀ :=
    lt_min massDeltaPos
      (lt_min degreeDeltaPos ratioDeltaPos)
  have delta₀LeOne : delta₀ ≤ 1 :=
    (min_le_left massDelta
      (min degreeDelta ratioDelta)).trans massDeltaLeOne
  refine ⟨delta₀, delta₀Pos, delta₀LeOne, ?_⟩
  intro delta deltaPos deltaLe cardinality cardLog
  have deltaOne : delta ≤ 1 :=
    deltaLe.trans delta₀LeOne
  have deltaMass : delta ≤ massDelta :=
    deltaLe.trans
      (min_le_left massDelta (min degreeDelta ratioDelta))
  have deltaDegree : delta ≤ degreeDelta :=
    deltaLe.trans
      ((min_le_right massDelta
        (min degreeDelta ratioDelta)).trans
          (min_le_left degreeDelta ratioDelta))
  have deltaRatio : delta ≤ ratioDelta :=
    deltaLe.trans
      ((min_le_right massDelta
        (min degreeDelta ratioDelta)).trans
          (min_le_right degreeDelta ratioDelta))
  let logTerm : ENNReal :=
    (Nat.log 2 (2 * cardinality) + 1 : ENNReal)
  let logBound : ENNReal :=
    ENNReal.ofReal
      (pureWZ2HeavyCellCardLogConstant *
        (1 + Real.log delta⁻¹))
  have logTermLe : logTerm ≤ logBound := by
    have representation :
        logTerm =
          ENNReal.ofReal
            ((Nat.log 2 (2 * cardinality) + 1 : ℝ)) := by
      dsimp only [logTerm]
      norm_cast
    rw [representation]
    exact ENNReal.ofReal_mono cardLog
  let regularizationLoss :=
    pureWZ2SpatialCellRegularizationLoss epsilon cardinality
  let degreeConstant :=
    pureWZ2SpatialCellDegreeConstant epsilon cardinality
  have regularizationBound :
      regularizationLoss ≤
        Kakeya.realRpowENN delta
          (-(inputLoss - cellLoss)) := by
    calc
      regularizationLoss =
          8 * logTerm ^ (scaleCount + 1) := by
        rfl
      _ ≤ 8 * logBound ^ (scaleCount + 1) := by
        gcongr
      _ ≤
          Kakeya.realRpowENN delta
            (-(inputLoss - cellLoss)) :=
        massBound delta deltaPos deltaMass
  have degreeBound' :
      degreeConstant ≤
        Kakeya.realRpowENN delta (-inputLoss) := by
    calc
      degreeConstant =
          degreeCoefficient * logTerm ^ scaleCount := by
        rfl
      _ ≤ degreeCoefficient * logBound ^ scaleCount := by
        gcongr
      _ ≤ Kakeya.realRpowENN delta (-inputLoss) :=
        degreeBound delta deltaPos deltaDegree
  have productIdentity :
      regularizationLoss * degreeConstant =
        ratioCoefficient * logTerm ^ (2 * scaleCount + 1) := by
    have regularizationLossEq :
        regularizationLoss =
          8 * logTerm ^ (scaleCount + 1) := rfl
    have degreeConstantEq :
        degreeConstant =
          16 * (scaleCount : ENNReal) *
            logTerm ^ scaleCount := rfl
    rw [regularizationLossEq, degreeConstantEq]
    dsimp only [ratioCoefficient]
    calc
      8 * logTerm ^ (scaleCount + 1) *
            (16 * (scaleCount : ENNReal) *
              logTerm ^ scaleCount) =
          (128 * (scaleCount : ENNReal)) *
            (logTerm ^ (scaleCount + 1) *
              logTerm ^ scaleCount) := by ring
      _ =
          (128 * (scaleCount : ENNReal)) *
            logTerm ^ ((scaleCount + 1) + scaleCount) := by
        exact
          congrArg
            (fun value : ENNReal =>
              (128 * (scaleCount : ENNReal)) * value)
            (pow_add logTerm (scaleCount + 1) scaleCount).symm
      _ =
          (128 * (scaleCount : ENNReal)) *
            logTerm ^ (2 * scaleCount + 1) := by
        congr 2
        omega
  have productBound :
      regularizationLoss * degreeConstant ≤
        Kakeya.realRpowENN delta
          (-(inputLoss -
            (3 * sourceLoss + cellLoss))) := by
    calc
      regularizationLoss * degreeConstant =
          ratioCoefficient *
            logTerm ^ (2 * scaleCount + 1) :=
        productIdentity
      _ ≤
          ratioCoefficient *
            logBound ^ (2 * scaleCount + 1) := by
        gcongr
      _ ≤
          Kakeya.realRpowENN delta
            (-(inputLoss -
              (3 * sourceLoss + cellLoss))) :=
        ratioBound delta deltaPos deltaRatio
  have massAbsorption :
      regularizationLoss *
          Kakeya.realRpowENN delta
            (inputLoss - cellLoss) ≤
        1 := by
    calc
      regularizationLoss *
            Kakeya.realRpowENN delta
              (inputLoss - cellLoss) ≤
          Kakeya.realRpowENN delta
              (-(inputLoss - cellLoss)) *
            Kakeya.realRpowENN delta
              (inputLoss - cellLoss) := by
        gcongr
      _ =
          Kakeya.realRpowENN delta 0 := by
        rw [Subunit.realRpowENN_mul deltaPos]
        congr 1
        ring
      _ = 1 := by
        simp [Kakeya.realRpowENN]
  have sourcePowerPos :
      Kakeya.realRpowENN delta sourceLoss ≠ 0 := by
    exact
      (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos deltaPos sourceLoss)).ne'
  have sourcePowerFinite :
      Kakeya.realRpowENN delta sourceLoss ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have cellPowerPos :
      Kakeya.realRpowENN delta cellLoss ≠ 0 := by
    exact
      (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos deltaPos cellLoss)).ne'
  have cellPowerFinite :
      Kakeya.realRpowENN delta cellLoss ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have tubeVolumePos :
      Kakeya.deltaTubeVolume delta ≠ 0 :=
    ((tube_volume_scaling.2.1 delta deltaPos deltaOne).1).ne'
  have tubeVolumeFinite :
      Kakeya.deltaTubeVolume delta ≠ ⊤ :=
    (tube_volume_scaling.2.1 delta deltaPos deltaOne).2
  have normalizationInverse :
      (pureWZ2SpatialCellNormalizationWeight
          delta sourceLoss cellLoss)⁻¹ =
        Kakeya.realRpowENN delta (-sourceLoss) *
          Kakeya.realRpowENN delta (-cellLoss) *
            (Kakeya.deltaTubeVolume delta)⁻¹ := by
    dsimp only [pureWZ2SpatialCellNormalizationWeight]
    rw [ENNReal.mul_inv, ENNReal.mul_inv]
    · rw [pure_wz2_realRpowENN_inv deltaPos,
        pure_wz2_realRpowENN_inv deltaPos]
    all_goals
      simp [sourcePowerPos, sourcePowerFinite,
        cellPowerPos, cellPowerFinite,
        tubeVolumePos, tubeVolumeFinite]
  have tubeCancel :
      (Kakeya.deltaTubeVolume delta)⁻¹ *
          Kakeya.deltaTubeVolume delta =
        1 :=
    ENNReal.inv_mul_cancel tubeVolumePos tubeVolumeFinite
  have sourcePowerProduct :
      Kakeya.realRpowENN delta (-sourceLoss) *
            Kakeya.realRpowENN delta (-sourceLoss) *
          Kakeya.realRpowENN delta (-sourceLoss) *
        Kakeya.realRpowENN delta (-cellLoss) =
      Kakeya.realRpowENN delta
        (-(3 * sourceLoss + cellLoss)) := by
    rw [Subunit.realRpowENN_mul deltaPos,
      Subunit.realRpowENN_mul deltaPos,
      Subunit.realRpowENN_mul deltaPos]
    congr 1
    ring
  have ratioIdentity :
      ((pureWZ2SpatialCellNormalizationWeight
              delta sourceLoss cellLoss)⁻¹ *
            (Kakeya.realRpowENN delta (-sourceLoss) *
              (regularizationLoss *
                Kakeya.deltaTubeVolume delta) *
              degreeConstant)) *
          Kakeya.realRpowENN delta (-sourceLoss) =
        (regularizationLoss * degreeConstant) *
          Kakeya.realRpowENN delta
            (-(3 * sourceLoss + cellLoss)) := by
    rw [normalizationInverse]
    calc
      ((Kakeya.realRpowENN delta (-sourceLoss) *
              Kakeya.realRpowENN delta (-cellLoss) *
              (Kakeya.deltaTubeVolume delta)⁻¹) *
            (Kakeya.realRpowENN delta (-sourceLoss) *
              (regularizationLoss *
                Kakeya.deltaTubeVolume delta) *
              degreeConstant)) *
          Kakeya.realRpowENN delta (-sourceLoss) =
        (((Kakeya.deltaTubeVolume delta)⁻¹ *
            Kakeya.deltaTubeVolume delta) *
          (regularizationLoss * degreeConstant)) *
            ((Kakeya.realRpowENN delta (-sourceLoss) *
                  Kakeya.realRpowENN delta (-sourceLoss) *
                Kakeya.realRpowENN delta (-sourceLoss)) *
              Kakeya.realRpowENN delta (-cellLoss)) := by
        ring
      _ =
          (regularizationLoss * degreeConstant) *
            ((Kakeya.realRpowENN delta (-sourceLoss) *
                  Kakeya.realRpowENN delta (-sourceLoss) *
                Kakeya.realRpowENN delta (-sourceLoss)) *
              Kakeya.realRpowENN delta (-cellLoss)) := by
        rw [tubeCancel]
        simp
      _ =
          (regularizationLoss * degreeConstant) *
            Kakeya.realRpowENN delta
              (-(3 * sourceLoss + cellLoss)) := by
        rw [sourcePowerProduct]
  have ratioAbsorption :
      ((pureWZ2SpatialCellNormalizationWeight
              delta sourceLoss cellLoss)⁻¹ *
            (Kakeya.realRpowENN delta (-sourceLoss) *
              (regularizationLoss *
                Kakeya.deltaTubeVolume delta) *
              degreeConstant)) *
          Kakeya.realRpowENN delta (-sourceLoss) ≤
        Kakeya.realRpowENN delta (-inputLoss) := by
    rw [ratioIdentity]
    calc
      (regularizationLoss * degreeConstant) *
            Kakeya.realRpowENN delta
              (-(3 * sourceLoss + cellLoss)) ≤
          Kakeya.realRpowENN delta
              (-(inputLoss -
                (3 * sourceLoss + cellLoss))) *
            Kakeya.realRpowENN delta
              (-(3 * sourceLoss + cellLoss)) := by
        gcongr
      _ =
          Kakeya.realRpowENN delta (-inputLoss) := by
        rw [Subunit.realRpowENN_mul deltaPos]
        congr 1
        ring
  refine ⟨?_, ?_⟩
  · simpa [regularizationLoss, epsilon] using massAbsorption
  · rw [wz2PaperPureNearbyRestrictionConstant]
    refine max_le ?_ (max_le ?_ ?_)
    · exact
        pure_wz2_rpowENN_antitone
          deltaPos deltaOne (by linarith)
    · simpa [degreeConstant, epsilon] using degreeBound'
    · simpa [regularizationLoss, degreeConstant, epsilon] using
        ratioAbsorption

/-! ## Geometry-selected preselection adapter -/

/--
A spatial-cell preselection after the finite rigid-geometry selection.

No CWA conclusion is assumed.  The existing weighted regularizer restores
nearby pure CWA only after this package has been formed.
-/
structure PureWZ2GeometrySelectedSpatialCellPreselectionData
    {sigma sourceLoss pruningLoss cellLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss) where
  data :
    PureWZ2SpatialCellPreselectionData
      (cellLoss := cellLoss) source pruning
  card_log :
    (Nat.log 2 (2 * data.preSelected.family.card) + 1 : ℝ) ≤
      pureWZ2HeavyCellCardLogConstant *
        (1 + Real.log delta⁻¹)
  referenceDirection : Point3
  referenceDirection_unit : ‖referenceDirection‖ = 1
  spatialCell : ℤ × ℤ × ℤ
  commonPoint : Point3
  commonPoint_eq :
    commonPoint =
      pureWZ2RigidCropCellCenter spatialCell
  localShading_subset_cell :
    ∀ index,
      data.localShading.carrier index ⊆
        wz1PaperGridCube
          pureWZ2RigidCropGridScale spatialCell
  halfStart : ℝ
  halfStart_cases :
    halfStart = 0 ∨ halfStart = 1 / 2
  direction_cone :
    ∀ index,
      1 / 2 ≤
        inner ℝ referenceDirection
          (data.preSelected.family.tube index).direction
  segment_near :
    ∀ index,
      ∃ parameter : ℝ,
        parameter ∈ Set.Icc (0 : ℝ) 1 ∧
        parameter ∈ Set.Icc halfStart (halfStart + 1 / 2) ∧
        ‖(data.preSelected.family.tube index).base +
              parameter •
                (data.preSelected.family.tube index).direction -
            commonPoint‖ ≤
          Real.sqrt 3 / 32 + delta

namespace PureWZ2DirectionalHalfPreselectionData

variable
    {sigma sourceLoss pruningLoss outputPruningLoss cellLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss}
    {data :
      PureWZ2SpatialCellPreselectionData
        (cellLoss := cellLoss) source pruning}
    (selection :
      PureWZ2DirectionalHalfPreselectionData
        (outputPruningLoss := outputPruningLoss) data)

/--
Package the corrected whole-cell directional selection for weighted CWA
regularization while retaining the exact fine cell and rigid-frame geometry.
-/
noncomputable def toGeometrySelectedSpatialCellPreselectionData
    (outputCellLoss : ℝ)
    (densityAbsorption :
      Kakeya.realRpowENN delta outputPruningLoss ≤
        pureWZ2DirectionalHalfDensityFactor *
          Kakeya.realRpowENN delta pruningLoss)
    (fixedLossAbsorption :
      Kakeya.realRpowENN delta
          (outputCellLoss - cellLoss) ≤
        pureWZ2DirectionalHalfSelectionFactor)
    (cardLog :
      (Nat.log 2
          (2 *
            (selection.toSpatialCellPreselectionData
              outputCellLoss densityAbsorption
              fixedLossAbsorption).preSelected.family.card) + 1 : ℝ) ≤
        pureWZ2HeavyCellCardLogConstant *
          (1 + Real.log delta⁻¹)) :
    PureWZ2GeometrySelectedSpatialCellPreselectionData
      (cellLoss := outputCellLoss) source
      (PureWZ2DirectionalHalfPreselectionData.toWeakerPruningData
        (source := source) (pruning := pruning)
        densityAbsorption) := by
  let spatial :=
    selection.toSpatialCellPreselectionData
      outputCellLoss densityAbsorption fixedLossAbsorption
  exact
    {
      data := spatial
      card_log := by
        simpa [spatial] using cardLog
      referenceDirection := selection.centerDirection
      referenceDirection_unit := selection.centerDirection_unit
      spatialCell := selection.spatialCell
      commonPoint := selection.commonPoint
      commonPoint_eq := selection.commonPoint_eq
      localShading_subset_cell := by
        intro index
        simpa [spatial] using
          selection.toSpatialCellPreselectionData_local_subset_spatialCell
            outputCellLoss densityAbsorption fixedLossAbsorption index
      halfStart := selection.halfStart
      halfStart_cases := selection.halfStart_cases
      direction_cone := by
        intro index
        exact selection.direction_cone index
      segment_near := by
        intro index
        exact selection.segment_near index
    }

end PureWZ2DirectionalHalfPreselectionData

/--
The weighted-regularized spatial certificate together with an explicit trace
back to the geometry-selected prefamily.
-/
structure PureWZ2GeometryPreservingSpatialCellSelectionCertificate
    {sigma sourceLoss inputLoss pruningLoss cellLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss}
    (geometry :
      PureWZ2GeometrySelectedSpatialCellPreselectionData
        (cellLoss := cellLoss) source pruning) where
  certificate :
    PureWZ2SpatialCellSelectionCertificate
      (inputLoss := inputLoss) source pruning
  geometryIndex :
    Fin certificate.selected.family.card →
      Fin geometry.data.preSelected.family.card
  source_index_eq :
    ∀ index,
      certificate.selected.embedding index =
        geometry.data.preSelected.embedding (geometryIndex index)
  localShading_subset_cell :
    ∀ index,
      certificate.localShading.carrier index ⊆
        wz1PaperGridCube
          pureWZ2RigidCropGridScale geometry.spatialCell
  direction_cone :
    ∀ index,
      1 / 2 ≤
        inner ℝ geometry.referenceDirection
          (certificate.selected.family.tube index).direction
  segment_near :
    ∀ index,
      ∃ parameter : ℝ,
        parameter ∈ Set.Icc (0 : ℝ) 1 ∧
        parameter ∈
          Set.Icc geometry.halfStart
            (geometry.halfStart + 1 / 2) ∧
        ‖(certificate.selected.family.tube index).base +
              parameter •
                (certificate.selected.family.tube index).direction -
            geometry.commonPoint‖ ≤
          Real.sqrt 3 / 32 + delta

/--
Run weighted regularization after finite geometry selection and preserve the
geometry witnesses on the final certificate family.

The only quantitative input is the already-proved uniform package for the
actual degree and regularization constants.  Cropped CWA is neither assumed
nor produced.
-/
theorem
    pureWZ2_spatialCellSelectionCertificate_withGeometry_of_preselection
    {sigma sourceLoss inputLoss pruningLoss cellLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss)
    (geometry :
      PureWZ2GeometrySelectedSpatialCellPreselectionData
        (cellLoss := cellLoss) source pruning)
    (sourceLossLtInputLoss : sourceLoss < inputLoss)
    (pruningLossLeInputLoss : pruningLoss ≤ inputLoss)
    (deltaLtOne : delta < 1)
    (actualAbsorptions :
      PureWZ2HeavyCellActualAbsorptionsAtScale
        sourceLoss inputLoss cellLoss delta) :
    Nonempty
      (PureWZ2GeometryPreservingSpatialCellSelectionCertificate
        (inputLoss := inputLoss) geometry) := by
  have absorptions :=
    actualAbsorptions
      geometry.data.preSelected.family.card geometry.card_log
  rcases
      pureWZ2_spatialCellSelectionCertificate_of_preselection
        source pruning geometry.data
        sourceLossLtInputLoss
        pruningLossLeInputLoss
        deltaLtOne absorptions.1 absorptions.2
    with
    ⟨result⟩
  let certificate := result.certificate
  let geometryIndex := result.preselectionIndex
  have sourceIndexEq :
      ∀ index,
        certificate.selected.embedding index =
          geometry.data.preSelected.embedding
            (geometryIndex index) :=
    result.source_index_eq
  refine
    ⟨{
      certificate := certificate
      geometryIndex := geometryIndex
      source_index_eq := sourceIndexEq
      localShading_subset_cell := by
        intro index
        exact
          (result.localShading_subset_preselection index).trans
            (geometry.localShading_subset_cell
              (geometryIndex index))
      direction_cone := ?_
      segment_near := ?_
    }⟩
  · intro index
    have inherited :=
      geometry.direction_cone (geometryIndex index)
    simpa only
      [certificate.selected.tube_eq,
        geometry.data.preSelected.tube_eq,
        sourceIndexEq index] using inherited
  · intro index
    rcases geometry.segment_near (geometryIndex index) with
      ⟨parameter, parameterMem, parameterHalf, near⟩
    refine
      ⟨parameter, parameterMem, parameterHalf, ?_⟩
    simpa only
      [certificate.selected.tube_eq,
        geometry.data.preSelected.tube_eq,
        sourceIndexEq index] using near

end Kakeya.Assouad

end
