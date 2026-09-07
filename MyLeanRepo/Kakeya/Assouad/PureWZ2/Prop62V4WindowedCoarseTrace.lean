import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationFinalOrdinaryTrace
import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryTraceCenteredParentContainment
import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryTubeCubeOverlap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4FinalCoarseCriticalWitness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4CellIncidenceBounds
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperFinalV4PointwiseProductUpper
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4PureRefinementComposition
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4SelectedIncidenceScalar
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedVolumeIdentities
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGlobalMultiplicityHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperParentCellMassUpper
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CroppedCriticalFloorLocalReduction

/-!
# Windowed ordinary trace on the final Proposition 6.2 coarse family

Given an ordinary trace on the final fine family, assign its carrier to the
same parent map as the final V4 Section-6 cover.  A pointwise Euclidean
containment into the assigned ordinary parent is the only geometric input
needed to make this fiber union an ordinary coarse shading.

The V4 specialization obtains that containment from:

* the whole normalized ordinary shading lying in the central height window;
* the final fine family's exact embedding into the normalized family;
* the strict `rho / 2` metric parent relation;
* centered representatives for the final coarse parents; and
* the scale ratio `delta / rho <= 1 / 24`.

All mass transfer and density statements below are then derived from the
recorded fiber multiplicity cap.  No coarse trace density is assumed.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62MetricParentsV4Certificate

/--
The deterministic public metric-data projection keeps the exact internal
coarse family.  Thus no second centered field is needed on
`MetricParentsAtPrescribedScaleData`.
-/
theorem toMetricData_coarse_eq
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {c0 : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (certificate :
      PureWZ2Prop62MetricParentsV4Certificate
        shading rho c0 parentConstant fiberConstant) :
    certificate.toMetricData.scaleData.coarse = certificate.coarse := by
  rcases certificate with
    ⟨rhoPos, c0Pos, refinement, fine, fineEq, refinedNonempty,
      refinedCubical, coarse, _coarseCentered, section6Cover, cover, coverEq,
      fullFiberUniform, coarseCWA, coarseSeparated, sourceFiberConstant,
      fiberConstantEq, fiberRescaling, fiberPublicCWA, metricFiber,
      fineParentClose⟩
  subst fine
  rfl

end PureWZ2Prop62MetricParentsV4Certificate

namespace PureWZ2Prop62FourDegreeOutputCertificate

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {ambientCover : PureWZ2Section6Cover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {densityConstant outputParentConstant sourceFiberConstant : ENNReal}
    {input : PureWZ2Prop62PacketCellInput ambientCover sourceShading}
    (output :
      PureWZ2Prop62FourDegreeOutputCertificate
        input densityConstant outputParentConstant sourceFiberConstant)

/-- Final fine shading restricted to the exact complete fiber of one parent. -/
def windowedFullFiberShading
    (parent : Fin output.coarse.family.card) :
    WZ1PaperTubeShading
      (wz2PaperFullFiberSubfamily
        output.refinement.selected.family
        output.coarse.family parent).family :=
  restrictPaperShading
    (wz2PaperFullFiberSubfamily
      output.refinement.selected.family
      output.coarse.family parent)
    output.refinement.refined

/--
The selected parent cells are exactly the active `rho`-cells actually hit by
the final refined shading in that parent's complete fiber.
-/
def selectedParentCells
    (parent : Fin output.coarse.family.card) :
    Finset WZ2PaperCellIndex :=
  output.balanced.activeCells.filter fun cell =>
    ((output.windowedFullFiberShading parent).union ∩
      wz1PaperGridCube rho cell).Nonempty

/-- Every selected parent cell has a final fine point in the corresponding
complete fiber. -/
theorem selectedParentCells_witness
    (parent : Fin output.coarse.family.card)
    (cell : WZ2PaperCellIndex)
    (cellMem : cell ∈ output.selectedParentCells parent) :
    ∃ source : Fin output.refinement.selected.family.card,
      output.cover.toWZ1PaperTubeCover.parent source = parent ∧
        ∃ point,
          point ∈ output.refinement.refined.carrier source ∧
            point ∈ wz1PaperGridCube rho cell := by
  rcases (Finset.mem_filter.mp cellMem).2 with
    ⟨point, pointFiber, pointCell⟩
  rcases pointFiber with ⟨fiberIndex, pointFine⟩
  let fiber :=
    wz2PaperFullFiberSubfamily
      output.refinement.selected.family output.coarse.family parent
  let source := fiber.embedding fiberIndex
  have sourceFiber :
      source ∈
        wz2PaperFullFiberIndices
          output.refinement.selected.family output.coarse.family parent :=
    Finset.orderEmbOfFin_mem
      (wz2PaperFullFiberIndices
        output.refinement.selected.family output.coarse.family parent)
      rfl fiberIndex
  have parentEq :
      output.cover.toWZ1PaperTubeCover.parent source = parent := by
    exact
      (output.cover.toWZ1PaperTubeCover.parent_unique
        source parent
        ((mem_wz2PaperFullFiberIndices_iff parent source).mp
          sourceFiber)).symm
  refine ⟨source, parentEq, point, ?_, pointCell⟩
  simpa only [windowedFullFiberShading, restrictPaperShading, fiber, source]
    using pointFine

/-- Every selected parent cell lies in that parent's final cropped shading. -/
theorem selectedParentCell_subset_coarseShading
    (parent : Fin output.coarse.family.card)
    (cell : WZ2PaperCellIndex)
    (cellMem : cell ∈ output.selectedParentCells parent) :
    wz1PaperGridCube rho cell ⊆
      output.coarseShading.carrier parent := by
  rcases output.selectedParentCells_witness parent cell cellMem with
    ⟨source, parentEq, point, pointFine, pointCell⟩
  have pointCoarse :
      point ∈ output.coarseShading.carrier parent := by
    have := output.balanced.point_compatibility source point pointFine
    rwa [parentEq] at this
  have pointIndex :
      wz1PaperGridIndex rho point = cell :=
    (mem_wz1PaperGridCube rho cell point).mp pointCell
  simpa only [pointIndex] using
    output.balanced.coarse_cubical parent point pointCoarse

/-- The cropped shading made only of genuine final parent-cell incidences. -/
def selectedIncidenceCoarseShading :
    WZ1PaperTubeShading output.coarse.family where
  carrier parent :=
    ⋃ cell ∈ output.selectedParentCells parent,
      wz1PaperGridCube rho cell
  measurable_carrier parent := by
    apply MeasurableSet.iUnion
    intro cell
    apply MeasurableSet.iUnion
    intro _
    exact wz1PaperGridCube_measurable cell
  subset_body parent := by
    apply Set.iUnion_subset
    intro cell
    apply Set.iUnion_subset
    intro cellMem
    exact
      (output.selectedParentCell_subset_coarseShading
        parent cell cellMem).trans
          (output.coarseShading.subset_body parent)

@[simp] theorem selectedIncidenceCoarseShading_carrier
    (parent : Fin output.coarse.family.card) :
    output.selectedIncidenceCoarseShading.carrier parent =
      ⋃ cell ∈ output.selectedParentCells parent,
        wz1PaperGridCube rho cell :=
  rfl

/-- The selected-incidence shading is a genuine subshading of the final
cropped coarse shading. -/
theorem selectedIncidenceCoarseShading_carrier_subset
    (parent : Fin output.coarse.family.card) :
    output.selectedIncidenceCoarseShading.carrier parent ⊆
      output.coarseShading.carrier parent := by
  intro point pointMem
  rcases Set.mem_iUnion₂.mp pointMem with ⟨cell, cellMem, pointCell⟩
  exact output.selectedParentCell_subset_coarseShading
    parent cell cellMem pointCell

/-- The complete final fiber is supported on its genuinely incident cells. -/
theorem windowedFullFiberShading_support
    (parent : Fin output.coarse.family.card)
    (index :
      Fin
        (wz2PaperFullFiberSubfamily
          output.refinement.selected.family
          output.coarse.family parent).family.card) :
    (output.windowedFullFiberShading parent).carrier index ⊆
      ⋃ cell ∈ output.selectedParentCells parent,
        wz1PaperGridCube rho cell := by
  intro point pointMem
  have pointCoarse :
      point ∈ output.coarseShading.carrier parent := by
    let fiber :=
      wz2PaperFullFiberSubfamily
        output.refinement.selected.family output.coarse.family parent
    let source := fiber.embedding index
    have sourceFiber :
        source ∈
          wz2PaperFullFiberIndices
            output.refinement.selected.family
            output.coarse.family parent :=
      Finset.orderEmbOfFin_mem
        (wz2PaperFullFiberIndices
          output.refinement.selected.family output.coarse.family parent)
        rfl index
    have parentEq :
        output.cover.toWZ1PaperTubeCover.parent source = parent := by
      exact
        (output.cover.toWZ1PaperTubeCover.parent_unique
          source parent
          ((mem_wz2PaperFullFiberIndices_iff parent source).mp
            sourceFiber)).symm
    have sourceMem :
        point ∈ output.refinement.refined.carrier source := by
      simpa only [windowedFullFiberShading, restrictPaperShading,
        fiber, source] using pointMem
    have :=
      output.balanced.point_compatibility source point sourceMem
    rwa [parentEq] at this
  have pointUnion : point ∈ output.coarseShading.union :=
    ⟨parent, pointCoarse⟩
  rw [output.balanced.coarse_union_eq] at pointUnion
  rcases Set.mem_iUnion₂.mp pointUnion with
    ⟨cell, cellActive, pointCell⟩
  have cellSelected :
      cell ∈ output.selectedParentCells parent := by
    apply Finset.mem_filter.mpr
    refine ⟨cellActive, ?_⟩
    exact ⟨point, ⟨index, pointMem⟩, pointCell⟩
  exact Set.mem_iUnion₂.mpr ⟨cell, cellSelected, pointCell⟩

/-- The union of one exact complete final fiber is bounded by the number of
its genuinely incident balanced cells times the common fine-cell mass. -/
theorem windowedFullFiberShading_union_volume_upper
    (parent : Fin output.coarse.family.card) :
    volume (output.windowedFullFiberShading parent).union ≤
      ((output.selectedParentCells parent).card : ENNReal) *
        output.balanced.cellMass := by
  let cells := output.selectedParentCells parent
  have fiberUnionSubset :
      (output.windowedFullFiberShading parent).union ⊆
        ⋃ cell ∈ cells,
          output.refinement.refined.union ∩ wz1PaperGridCube rho cell := by
    rintro point ⟨index, pointMem⟩
    rcases Set.mem_iUnion₂.mp
        (output.windowedFullFiberShading_support parent index pointMem) with
      ⟨cell, cellMem, pointCell⟩
    have pointRefined : point ∈ output.refinement.refined.union := by
      refine
        ⟨(wz2PaperFullFiberSubfamily
            output.refinement.selected.family
            output.coarse.family parent).embedding index, ?_⟩
      simpa only [windowedFullFiberShading, restrictPaperShading] using pointMem
    exact Set.mem_iUnion₂.mpr
      ⟨cell, cellMem, pointRefined, pointCell⟩
  calc
    volume (output.windowedFullFiberShading parent).union ≤
        volume
          (⋃ cell ∈ cells,
            output.refinement.refined.union ∩ wz1PaperGridCube rho cell) :=
      measure_mono fiberUnionSubset
    _ ≤ ∑ cell ∈ cells,
          volume
            (output.refinement.refined.union ∩
              wz1PaperGridCube rho cell) :=
      MeasureTheory.measure_biUnion_finset_le cells _
    _ = ∑ _cell ∈ cells, output.balanced.cellMass := by
      apply Finset.sum_congr rfl
      intro cell cellMem
      exact output.balanced.fine_cell_mass cell
        (Finset.mem_filter.mp cellMem).1
    _ = (cells.card : ENNReal) * output.balanced.cellMass := by
      simp [Finset.sum_const]

/-- One complete fiber has mass at most its cardinality times the number of
genuine incident cells times the tube--cell intersection bound. -/
theorem windowedFullFiberShading_mass_upper
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (parent : Fin output.coarse.family.card) :
    (output.windowedFullFiberShading parent).mass ≤
      (wz2PaperFullFiberSubfamily
        output.refinement.selected.family
        output.coarse.family parent).family.enncard *
      ((output.selectedParentCells parent).card : ENNReal) *
        ENNReal.ofReal (288 * delta ^ 2 * rho) := by
  let fiber :=
    wz2PaperFullFiberSubfamily
      output.refinement.selected.family output.coarse.family parent
  let fiberShading := output.windowedFullFiberShading parent
  let cells := output.selectedParentCells parent
  let cellBound := ENNReal.ofReal (288 * delta ^ 2 * rho)
  have carrierMass :
      ∀ index : Fin fiber.family.card,
        volume (fiberShading.carrier index) ≤
          (cells.card : ENNReal) * cellBound := by
    intro index
    have carrierPartition :
        fiberShading.carrier index =
          ⋃ cell ∈ cells,
            fiberShading.carrier index ∩
              wz1PaperGridCube rho cell := by
      ext point
      constructor
      · intro pointMem
        have pointCells :=
          output.windowedFullFiberShading_support parent index pointMem
        rcases Set.mem_iUnion₂.mp pointCells with
          ⟨cellIndex, cellMem, pointCell⟩
        exact Set.mem_iUnion₂.mpr
          ⟨cellIndex, cellMem, ⟨pointMem, pointCell⟩⟩
      · intro pointMem
        rcases Set.mem_iUnion₂.mp pointMem with
          ⟨_cell, _cellMem, pointFiber, _pointCell⟩
        exact pointFiber
    calc
      volume (fiberShading.carrier index) =
          volume
            (⋃ cell ∈ cells,
              fiberShading.carrier index ∩
                wz1PaperGridCube rho cell) :=
        congrArg volume carrierPartition
      _ ≤
          ∑ cell ∈ cells,
            volume
              (fiberShading.carrier index ∩
                wz1PaperGridCube rho cell) :=
        MeasureTheory.measure_biUnion_finset_le cells _
      _ ≤ ∑ _cell ∈ cells, cellBound := by
        exact Finset.sum_le_sum fun cell _ => by
          have carrierSubset :
              fiberShading.carrier index ⊆
                wz1PaperTubeCarrier (fiber.family.tube index) :=
            fiberShading.subset_body index
          exact
            (measure_mono
              (Set.inter_subset_inter
                carrierSubset Set.Subset.rfl)).trans
              (wz2_paper_tube_cell_intersection_volume
                hdelta hrho (fiber.family.tube index) cell)
      _ = (cells.card : ENNReal) * cellBound := by
        simp [Finset.sum_const]
  calc
    fiberShading.mass =
        ∑ index : Fin fiber.family.card,
          volume (fiberShading.carrier index) := rfl
    _ ≤
        ∑ _index : Fin fiber.family.card,
          (cells.card : ENNReal) * cellBound :=
      Finset.sum_le_sum fun index _ => carrierMass index
    _ =
        fiber.family.enncard * (cells.card : ENNReal) *
          cellBound := by
      simp [Kakeya.Streamlined.TubeFamily.enncard,
        Finset.sum_const]
      ring

/-- Exact volume of one selected-incidence parent shading. -/
theorem selectedIncidenceCoarseShading_carrier_volume
    (hrho : 0 < rho)
    (parent : Fin output.coarse.family.card) :
    volume (output.selectedIncidenceCoarseShading.carrier parent) =
      ((output.selectedParentCells parent).card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  rw [output.selectedIncidenceCoarseShading_carrier]
  exact
    wz1PaperGridCube_volume_biUnion
      hrho (output.selectedParentCells parent)

/-- Every final V4 parent meets at most `O(rho⁻¹)` genuinely selected coarse
cells. -/
theorem selectedParentCells_card_mul_scale_le
    (hrho : 0 < rho)
    (rhoSmall : rho ≤ 1 / 24)
    (parent : Fin output.coarse.family.card) :
    ((output.selectedParentCells parent).card : ENNReal) *
        ENNReal.ofReal rho ≤
      55296 * Kakeya.deltaTubeVolume 1 := by
  exact
    paper_parent_selected_cells_card_mul_scale_le
      output.coarseShading
      (output.selectedParentCells parent)
      (output.selectedIncidenceCoarseShading.carrier parent)
      parent hrho rhoSmall
      (output.cover.coarse_line_class parent)
      (output.selectedIncidenceCoarseShading_carrier_volume hrho parent)
      (output.selectedIncidenceCoarseShading_carrier_subset parent)

/-- Coarse-density scalar in the exact form used by the selected-incidence
argument. -/
def SelectedIncidenceDensityScalar
    (lambda : ENNReal) : Prop :=
  (576 * (55296 * Kakeya.deltaTubeVolume 1) : ENNReal) * lambda ≤
    densityConstant

/-- Parentwise form of selected-incidence coarse density. -/
theorem selectedIncidenceCoarseShading_parent_dense
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (rhoSmall : rho ≤ 1 / 24)
    (lambda : ENNReal)
    (scalar :
      SelectedIncidenceDensityScalar
        (densityConstant := densityConstant) lambda)
    (parent : Fin output.coarse.family.card) :
    lambda *
        volume
          (wz1PaperTubeCarrier
            (output.coarse.family.tube parent)) ≤
      volume
        (output.selectedIncidenceCoarseShading.carrier parent) := by
  let fiberFloor : ENNReal := output.fiberFloor
  let cellBound : ENNReal :=
    ENNReal.ofReal (288 * delta ^ 2 * rho)
  let cellVolume : ENNReal :=
    volume (wz1PaperGridCube rho (0, 0, 0))
  let bodyBound : ENNReal :=
    (55296 * Kakeya.deltaTubeVolume 1) *
      Kakeya.realRpowENN rho 2
  let packetCoefficient : ENNReal :=
    densityConstant * Kakeya.realRpowENN delta 2
  have fiberFloorZero : fiberFloor ≠ 0 := by
    dsimp only [fiberFloor]
    exact_mod_cast output.fiberFloor_pos.ne'
  have factorZero : 2 * cellBound ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · change ENNReal.ofReal (288 * delta ^ 2 * rho) ≠ 0
      apply (ENNReal.ofReal_pos.mpr ?_).ne'
      exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hdelta)) hrho
  have factorTop : 2 * cellBound ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have deltaSquare :
      ENNReal.ofReal (delta ^ 2) =
        Kakeya.realRpowENN delta 2 := by
    simp [Kakeya.realRpowENN]
  have rhoPower :
      ENNReal.ofReal rho * Kakeya.realRpowENN rho 2 =
        ENNReal.ofReal (rho ^ 3) := by
    simp [Kakeya.realRpowENN, ← ENNReal.ofReal_mul hrho.le]
    ring_nf
  have rhoCube :
      ENNReal.ofReal (rho ^ 3) = cellVolume := by
    dsimp only [cellVolume]
    exact (wz1PaperGridCube_volume_exact hrho).symm
  have cellBoundEq :
      cellBound =
        (288 : ENNReal) * Kakeya.realRpowENN delta 2 *
          ENNReal.ofReal rho := by
    dsimp only [cellBound]
    rw [ENNReal.ofReal_mul
      (by positivity : 0 ≤ 288 * delta ^ 2)]
    rw [ENNReal.ofReal_mul
      (by norm_num : (0 : ℝ) ≤ 288), deltaSquare]
    norm_num
  have packetScalar :
      (2 * cellBound) * (lambda * bodyBound) ≤
        packetCoefficient * cellVolume := by
    calc
      (2 * cellBound) * (lambda * bodyBound) =
          ((576 * (55296 * Kakeya.deltaTubeVolume 1) : ENNReal) *
              lambda) *
            Kakeya.realRpowENN delta 2 *
            (ENNReal.ofReal rho *
              Kakeya.realRpowENN rho 2) := by
        rw [cellBoundEq]
        dsimp only [bodyBound]
        ring
      _ =
          ((576 * (55296 * Kakeya.deltaTubeVolume 1) : ENNReal) *
              lambda) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (rho ^ 3) := by
        rw [rhoPower]
      _ ≤
          densityConstant * Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (rho ^ 3) := by
        gcongr
        exact scalar
      _ = packetCoefficient * cellVolume := by
        rw [rhoCube]
  let cells := output.selectedParentCells parent
  let fiber :=
    wz2PaperFullFiberSubfamily
      output.refinement.selected.family output.coarse.family parent
  have bodyUpper :
      volume
          (wz1PaperTubeCarrier
            (output.coarse.family.tube parent)) ≤
        bodyBound :=
    (wz2PaperTubeCarrier_convex_and_volume_quadratic
      wz2_paper_tube_carrier_geometry hrho rhoSmall
      (output.coarse.family.tube parent)
      (output.cover.coarse_line_class parent)).2
  have packetLower :
      packetCoefficient * fiberFloor ≤
        (output.windowedFullFiberShading parent).mass := by
    simpa [packetCoefficient, fiberFloor, windowedFullFiberShading,
      mul_assoc, mul_comm, mul_left_comm] using
      output.packet_density parent
  have fiberMassUpper :
      (output.windowedFullFiberShading parent).mass ≤
        (2 * fiberFloor * cellBound) *
          (cells.card : ENNReal) := by
    calc
      _ ≤ fiber.family.enncard * (cells.card : ENNReal) *
            cellBound :=
        output.windowedFullFiberShading_mass_upper
          hdelta hrho parent
      _ ≤
          (2 * fiberFloor) * (cells.card : ENNReal) *
            cellBound := by
        gcongr
        change
          ((wz2PaperFullFiberIndices
            output.refinement.selected.family
            output.coarse.family parent).card : ENNReal) ≤
              2 * (output.fiberFloor : ENNReal)
        exact (output.fiber_cardinality parent).2.le
      _ =
          (2 * fiberFloor * cellBound) *
            (cells.card : ENNReal) := by ring
  have packetLe :
      packetCoefficient ≤
        2 * cellBound * (cells.card : ENNReal) := by
    apply
      (ENNReal.mul_le_mul_iff_right
        fiberFloorZero (ENNReal.natCast_ne_top _)).mp
    calc
      fiberFloor * packetCoefficient =
          packetCoefficient * fiberFloor := by ring
      _ ≤ (output.windowedFullFiberShading parent).mass :=
        packetLower
      _ ≤ (2 * fiberFloor * cellBound) *
            (cells.card : ENNReal) :=
        fiberMassUpper
      _ =
          fiberFloor *
            (2 * cellBound * (cells.card : ENNReal)) := by ring
  have scaled :
      (2 * cellBound) *
          (lambda *
            volume
              (wz1PaperTubeCarrier
                (output.coarse.family.tube parent))) ≤
        (2 * cellBound) *
          ((cells.card : ENNReal) * cellVolume) := by
    calc
      _ ≤ (2 * cellBound) * (lambda * bodyBound) := by
        gcongr
      _ ≤ packetCoefficient * cellVolume := packetScalar
      _ ≤
          (2 * cellBound * (cells.card : ENNReal)) *
            cellVolume := by
        gcongr
      _ =
          (2 * cellBound) *
            ((cells.card : ENNReal) * cellVolume) := by ring
  apply
    (ENNReal.mul_le_mul_iff_left factorZero factorTop).mp
  rw [output.selectedIncidenceCoarseShading_carrier_volume hrho parent]
  simpa [mul_comm] using scaled

/-- The selected-incidence cropped shading is dense at every constant
satisfying the same reduced scalar inequality as `coarseDensityOfReduced`. -/
theorem selectedIncidenceCoarseShading_dense
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (rhoSmall : rho ≤ 1 / 24)
    (lambda : ENNReal)
    (scalar :
      SelectedIncidenceDensityScalar
        (densityConstant := densityConstant) lambda) :
    output.selectedIncidenceCoarseShading.IsLambdaDense lambda := by
  let fiberFloor : ENNReal := output.fiberFloor
  let cellBound : ENNReal :=
    ENNReal.ofReal (288 * delta ^ 2 * rho)
  let cellVolume : ENNReal :=
    volume (wz1PaperGridCube rho (0, 0, 0))
  let bodyBound : ENNReal :=
    (55296 * Kakeya.deltaTubeVolume 1) *
      Kakeya.realRpowENN rho 2
  let packetCoefficient : ENNReal :=
    densityConstant * Kakeya.realRpowENN delta 2
  have fiberFloorZero : fiberFloor ≠ 0 := by
    dsimp only [fiberFloor]
    exact_mod_cast output.fiberFloor_pos.ne'
  have factorZero : 2 * cellBound ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · change ENNReal.ofReal (288 * delta ^ 2 * rho) ≠ 0
      apply (ENNReal.ofReal_pos.mpr ?_).ne'
      exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hdelta)) hrho
  have factorTop : 2 * cellBound ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have deltaSquare :
      ENNReal.ofReal (delta ^ 2) =
        Kakeya.realRpowENN delta 2 := by
    simp [Kakeya.realRpowENN]
  have rhoPower :
      ENNReal.ofReal rho * Kakeya.realRpowENN rho 2 =
        ENNReal.ofReal (rho ^ 3) := by
    simp [Kakeya.realRpowENN, ← ENNReal.ofReal_mul hrho.le]
    ring_nf
  have rhoCube :
      ENNReal.ofReal (rho ^ 3) = cellVolume := by
    dsimp only [cellVolume]
    exact (wz1PaperGridCube_volume_exact hrho).symm
  have cellBoundEq :
      cellBound =
        (288 : ENNReal) * Kakeya.realRpowENN delta 2 *
          ENNReal.ofReal rho := by
    dsimp only [cellBound]
    rw [ENNReal.ofReal_mul
      (by positivity : 0 ≤ 288 * delta ^ 2)]
    rw [ENNReal.ofReal_mul
      (by norm_num : (0 : ℝ) ≤ 288), deltaSquare]
    norm_num
  have packetScalar :
      (2 * cellBound) * (lambda * bodyBound) ≤
        packetCoefficient * cellVolume := by
    calc
      (2 * cellBound) * (lambda * bodyBound) =
          ((576 * (55296 * Kakeya.deltaTubeVolume 1) : ENNReal) *
              lambda) *
            Kakeya.realRpowENN delta 2 *
            (ENNReal.ofReal rho *
              Kakeya.realRpowENN rho 2) := by
        rw [cellBoundEq]
        dsimp only [bodyBound]
        ring
      _ =
          ((576 * (55296 * Kakeya.deltaTubeVolume 1) : ENNReal) *
              lambda) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (rho ^ 3) := by
        rw [rhoPower]
      _ ≤
          densityConstant * Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (rho ^ 3) := by
        gcongr
        exact scalar
      _ = packetCoefficient * cellVolume := by
        rw [rhoCube]
  have parentDensity :
      ∀ parent : Fin output.coarse.family.card,
        lambda *
            volume
              (wz1PaperTubeCarrier
                (output.coarse.family.tube parent)) ≤
          volume
            (output.selectedIncidenceCoarseShading.carrier parent) := by
    intro parent
    let cells := output.selectedParentCells parent
    let fiber :=
      wz2PaperFullFiberSubfamily
        output.refinement.selected.family output.coarse.family parent
    have bodyUpper :
        volume
            (wz1PaperTubeCarrier
              (output.coarse.family.tube parent)) ≤
          bodyBound :=
      (wz2PaperTubeCarrier_convex_and_volume_quadratic
        wz2_paper_tube_carrier_geometry hrho rhoSmall
        (output.coarse.family.tube parent)
        (output.cover.coarse_line_class parent)).2
    have packetLower :
        packetCoefficient * fiberFloor ≤
          (output.windowedFullFiberShading parent).mass := by
      simpa [packetCoefficient, fiberFloor, windowedFullFiberShading,
        mul_assoc, mul_comm, mul_left_comm] using
        output.packet_density parent
    have fiberMassUpper :
        (output.windowedFullFiberShading parent).mass ≤
          (2 * fiberFloor * cellBound) *
            (cells.card : ENNReal) := by
      calc
        _ ≤ fiber.family.enncard * (cells.card : ENNReal) *
              cellBound :=
          output.windowedFullFiberShading_mass_upper
            hdelta hrho parent
        _ ≤
            (2 * fiberFloor) * (cells.card : ENNReal) *
              cellBound := by
          gcongr
          change
            ((wz2PaperFullFiberIndices
              output.refinement.selected.family
              output.coarse.family parent).card : ENNReal) ≤
                2 * (output.fiberFloor : ENNReal)
          exact (output.fiber_cardinality parent).2.le
        _ =
            (2 * fiberFloor * cellBound) *
              (cells.card : ENNReal) := by ring
    have packetLe :
        packetCoefficient ≤
          2 * cellBound * (cells.card : ENNReal) := by
      apply
        (ENNReal.mul_le_mul_iff_right
          fiberFloorZero (ENNReal.natCast_ne_top _)).mp
      calc
        fiberFloor * packetCoefficient =
            packetCoefficient * fiberFloor := by ring
        _ ≤ (output.windowedFullFiberShading parent).mass :=
          packetLower
        _ ≤ (2 * fiberFloor * cellBound) *
              (cells.card : ENNReal) :=
          fiberMassUpper
        _ =
            fiberFloor *
              (2 * cellBound * (cells.card : ENNReal)) := by ring
    have scaled :
        (2 * cellBound) *
            (lambda *
              volume
                (wz1PaperTubeCarrier
                  (output.coarse.family.tube parent))) ≤
          (2 * cellBound) *
            ((cells.card : ENNReal) * cellVolume) := by
      calc
        _ ≤ (2 * cellBound) * (lambda * bodyBound) := by
          gcongr
        _ ≤ packetCoefficient * cellVolume := packetScalar
        _ ≤
            (2 * cellBound * (cells.card : ENNReal)) *
              cellVolume := by
          gcongr
        _ =
            (2 * cellBound) *
              ((cells.card : ENNReal) * cellVolume) := by ring
    apply
      (ENNReal.mul_le_mul_iff_left factorZero factorTop).mp
    rw [output.selectedIncidenceCoarseShading_carrier_volume hrho parent]
    simpa [mul_comm] using scaled
  rw [Kakeya.Streamlined.Shading.IsLambdaDense]
  change
    lambda *
        (∑ parent : Fin output.coarse.family.card,
          volume
            (wz1PaperTubeCarrier
              (output.coarse.family.tube parent))) ≤
      output.selectedIncidenceCoarseShading.mass
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun parent _ => parentDensity parent

/-- The ordinary part of the genuinely selected parent--cell incidences. -/
noncomputable def ordinarySelectedIncidenceShading :
    Kakeya.Streamlined.TubeShading output.coarse.family :=
  wz2PaperCroppedShadingToOrdinary
    output.selectedIncidenceCoarseShading

@[simp] theorem ordinarySelectedIncidenceShading_carrier
    (parent : Fin output.coarse.family.card) :
    output.ordinarySelectedIncidenceShading.carrier parent =
      output.selectedIncidenceCoarseShading.carrier parent ∩
        (output.coarse.family.tube parent).carrier :=
  rfl

/--
If every selected parent--cell incidence has the absolute overlap supplied by
`OrdinaryTubeCubeOverlap`, then the ordinary selected-incidence shading keeps
at least a `1 / 100000` fraction of the cropped selected-incidence mass.
-/
theorem ordinarySelectedIncidenceShading_mass_lower
    (hrho : 0 < rho)
    (cellOverlap :
      ∀ parent cell,
        cell ∈ output.selectedParentCells parent →
          ENNReal.ofReal ((1 / 100000 : ℝ) * rho ^ 3) ≤
            volume
              (wz1PaperGridCube rho cell ∩
                (output.coarse.family.tube parent).carrier)) :
    (100000 : ENNReal)⁻¹ *
        output.selectedIncidenceCoarseShading.mass ≤
      output.ordinarySelectedIncidenceShading.mass := by
  have parentLower :
      ∀ parent : Fin output.coarse.family.card,
        (100000 : ENNReal)⁻¹ *
            volume
              (output.selectedIncidenceCoarseShading.carrier parent) ≤
          volume
            (output.ordinarySelectedIncidenceShading.carrier parent) := by
    intro parent
    let cells := output.selectedParentCells parent
    have cellsDisjoint :
        Set.PairwiseDisjoint (↑cells)
          (fun cell =>
            wz1PaperGridCube rho cell ∩
              (output.coarse.family.tube parent).carrier) := by
      intro first _firstMem second _secondMem distinct
      exact
        (wz1PaperGridCube_disjoint distinct).mono
          Set.inter_subset_left Set.inter_subset_left
    have cellsMeasurable :
        ∀ cell ∈ cells,
          MeasurableSet
            (wz1PaperGridCube rho cell ∩
              (output.coarse.family.tube parent).carrier) := by
      intro cell _cellMem
      exact
        (wz1PaperGridCube_measurable cell).inter
          Metric.isClosed_cthickening.measurableSet
    have ordinaryCarrierEq :
        output.ordinarySelectedIncidenceShading.carrier parent =
          ⋃ cell ∈ cells,
            wz1PaperGridCube rho cell ∩
              (output.coarse.family.tube parent).carrier := by
      ext point
      constructor
      · rintro ⟨pointSelected, pointParent⟩
        rcases Set.mem_iUnion₂.mp pointSelected with
          ⟨cell, cellMem, pointCell⟩
        exact Set.mem_iUnion₂.mpr
          ⟨cell, cellMem, pointCell, pointParent⟩
      · intro pointMem
        rcases Set.mem_iUnion₂.mp pointMem with
          ⟨cell, cellMem, pointCell, pointParent⟩
        exact
          ⟨Set.mem_iUnion₂.mpr ⟨cell, cellMem, pointCell⟩,
            pointParent⟩
    have cellScale :
        ∀ cell : WZ2PaperCellIndex,
          (100000 : ENNReal)⁻¹ *
              volume (wz1PaperGridCube rho cell) =
            ENNReal.ofReal ((1 / 100000 : ℝ) * rho ^ 3) := by
      intro cell
      rw [wz1PaperGridCube_volume_eq hrho cell (0, 0, 0),
        wz1PaperGridCube_volume_exact hrho]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 100000)]
      have reciprocal :
          (100000 : ENNReal)⁻¹ =
            ENNReal.ofReal (1 / 100000 : ℝ) := by
        rw [show (1 / 100000 : ℝ) = (100000 : ℝ)⁻¹ by norm_num]
        rw [ENNReal.ofReal_inv_of_pos
          (by norm_num : (0 : ℝ) < 100000)]
        norm_num
      rw [reciprocal]
    change
      (100000 : ENNReal)⁻¹ *
          volume
            (⋃ cell ∈ cells, wz1PaperGridCube rho cell) ≤
        volume
          (output.ordinarySelectedIncidenceShading.carrier parent)
    rw [wz1PaperGridCube_volume_biUnion hrho cells, ordinaryCarrierEq,
      MeasureTheory.measure_biUnion_finset cellsDisjoint cellsMeasurable]
    calc
      (100000 : ENNReal)⁻¹ *
          ((cells.card : ENNReal) *
            volume (wz1PaperGridCube rho (0, 0, 0))) =
          ∑ cell ∈ cells,
            (100000 : ENNReal)⁻¹ *
              volume (wz1PaperGridCube rho cell) := by
        simp only [wz1PaperGridCube_volume_eq hrho _ (0, 0, 0),
          Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤
          ∑ cell ∈ cells,
            volume
              (wz1PaperGridCube rho cell ∩
                (output.coarse.family.tube parent).carrier) := by
        exact Finset.sum_le_sum fun cell cellMem => by
          rw [cellScale cell]
          exact cellOverlap parent cell cellMem
  change
    (100000 : ENNReal)⁻¹ *
        (∑ parent : Fin output.coarse.family.card,
          volume
            (output.selectedIncidenceCoarseShading.carrier parent)) ≤
      ∑ parent : Fin output.coarse.family.card,
        volume
          (output.ordinarySelectedIncidenceShading.carrier parent)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun parent _ => parentLower parent

/-- The selected-incidence ordinary shading is contained parentwise in the
canonical final coarse ordinary trace. -/
theorem ordinarySelectedIncidenceShading_carrier_subset_finalCoarse
    (parent : Fin output.coarse.family.card) :
    output.ordinarySelectedIncidenceShading.carrier parent ⊆
      output.finalCoarseOrdinaryTrace.carrier parent := by
  rintro point ⟨pointSelected, pointOrdinary⟩
  exact
    ⟨output.selectedIncidenceCoarseShading_carrier_subset
        parent pointSelected,
      pointOrdinary⟩

/-- The same fixed mass fraction reaches the canonical final coarse trace. -/
theorem finalCoarseOrdinaryTrace_mass_lower_of_cell_overlap
    (hrho : 0 < rho)
    (cellOverlap :
      ∀ parent cell,
        cell ∈ output.selectedParentCells parent →
          ENNReal.ofReal ((1 / 100000 : ℝ) * rho ^ 3) ≤
            volume
              (wz1PaperGridCube rho cell ∩
                (output.coarse.family.tube parent).carrier)) :
    (100000 : ENNReal)⁻¹ *
        output.selectedIncidenceCoarseShading.mass ≤
      output.finalCoarseOrdinaryTrace.mass := by
  exact
    (output.ordinarySelectedIncidenceShading_mass_lower
      hrho cellOverlap).trans <| by
        apply Finset.sum_le_sum
        intro parent _
        exact measure_mono
          (output.ordinarySelectedIncidenceShading_carrier_subset_finalCoarse
            parent)

/-- The union of the fine trace over the exact final fiber of one parent. -/
def windowedCoarseTraceCarrier
    (fineTrace :
      Kakeya.Streamlined.TubeShading output.refinement.selected.family)
    (parent : Fin output.coarse.family.card) : Set Point3 :=
  ⋃ source : Fin output.refinement.selected.family.card,
    ⋃ (_ : output.cover.toWZ1PaperTubeCover.parent source = parent),
      fineTrace.carrier source

theorem windowedCoarseTraceCarrier_measurable
    (fineTrace :
      Kakeya.Streamlined.TubeShading output.refinement.selected.family)
    (parent : Fin output.coarse.family.card) :
    MeasurableSet (output.windowedCoarseTraceCarrier fineTrace parent) := by
  apply MeasurableSet.iUnion
  intro source
  apply MeasurableSet.iUnion
  intro _
  exact fineTrace.measurable_carrier source

/--
The ordinary coarse shading induced by a fine trace.  The sole geometric
premise says that every fine traced point lies in its assigned ordinary
parent carrier.
-/
def windowedCoarseTrace
    (fineTrace :
      Kakeya.Streamlined.TubeShading output.refinement.selected.family)
    (fineTraceInParent :
      ∀ source,
        fineTrace.carrier source ⊆
          (output.coarse.family.tube
            (output.cover.toWZ1PaperTubeCover.parent source)).carrier) :
    Kakeya.Streamlined.TubeShading output.coarse.family where
  carrier := output.windowedCoarseTraceCarrier fineTrace
  measurable_carrier :=
    output.windowedCoarseTraceCarrier_measurable fineTrace
  subset_body parent := by
    intro point pointMem
    rcases Set.mem_iUnion.mp pointMem with ⟨source, pointMem⟩
    rcases Set.mem_iUnion.mp pointMem with ⟨parentEq, pointMem⟩
    change point ∈ (output.coarse.family.tube parent).carrier
    rw [← parentEq]
    exact fineTraceInParent source pointMem

@[simp] theorem windowedCoarseTrace_carrier
    (fineTrace :
      Kakeya.Streamlined.TubeShading output.refinement.selected.family)
    (fineTraceInParent :
      ∀ source,
        fineTrace.carrier source ⊆
          (output.coarse.family.tube
            (output.cover.toWZ1PaperTubeCover.parent source)).carrier)
    (parent : Fin output.coarse.family.card) :
    (output.windowedCoarseTrace fineTrace fineTraceInParent).carrier parent =
      output.windowedCoarseTraceCarrier fineTrace parent :=
  rfl

/-- Reinterpret the fine ordinary trace as a paper shading using its inclusion
in the final fine paper shading. -/
def windowedFinePaperTrace
    (fineTrace :
      Kakeya.Streamlined.TubeShading output.refinement.selected.family)
    (fineTraceSubset :
      ∀ source,
        fineTrace.carrier source ⊆
          output.refinement.refined.carrier source) :
    WZ1PaperTubeShading output.refinement.selected.family where
  carrier := fineTrace.carrier
  measurable_carrier := fineTrace.measurable_carrier
  subset_body source :=
    (fineTraceSubset source).trans
      (output.refinement.refined.subset_body source)

/-- The same fiber-union carriers viewed in the cropped paper convention. -/
def windowedCoarsePaperTrace
    (fineTrace :
      Kakeya.Streamlined.TubeShading output.refinement.selected.family)
    (fineTraceSubset :
      ∀ source,
        fineTrace.carrier source ⊆
          output.refinement.refined.carrier source) :
    WZ1PaperTubeShading output.coarse.family where
  carrier := output.windowedCoarseTraceCarrier fineTrace
  measurable_carrier :=
    output.windowedCoarseTraceCarrier_measurable fineTrace
  subset_body parent := by
    intro point pointMem
    rcases Set.mem_iUnion.mp pointMem with ⟨source, pointMem⟩
    rcases Set.mem_iUnion.mp pointMem with ⟨parentEq, pointMem⟩
    have refinedMem :
        point ∈ output.refinement.refined.carrier source :=
      fineTraceSubset source pointMem
    have coarseMem :=
      output.balanced.point_compatibility source point refinedMem
    rw [parentEq] at coarseMem
    exact output.coarseShading.subset_body parent coarseMem

theorem windowedFinePaperTrace_point_compatibility
    (fineTrace :
      Kakeya.Streamlined.TubeShading output.refinement.selected.family)
    (fineTraceSubset :
      ∀ source,
        fineTrace.carrier source ⊆
          output.refinement.refined.carrier source)
    (source : Fin output.refinement.selected.family.card)
    (point : Point3)
    (pointMem :
      point ∈
        (output.windowedFinePaperTrace
          fineTrace fineTraceSubset).carrier source) :
    point ∈
      (output.windowedCoarsePaperTrace
        fineTrace fineTraceSubset).carrier
          (output.cover.toWZ1PaperTubeCover.parent source) := by
  exact Set.mem_iUnion.mpr
    ⟨source, Set.mem_iUnion.mpr ⟨rfl, pointMem⟩⟩

/-- The full geometric fiber is the fiber of the canonical parent map
constructed from a Section-6 cover. -/
private theorem windowed_fullFiberIndices_eq
    (parent : Fin output.coarse.family.card) :
    wz2PaperFullFiberIndices
        output.refinement.selected.family output.coarse.family parent =
      output.cover.toWZ1PaperTubeCover.fiberIndices parent := by
  ext source
  simp only [
    wz2PaperFullFiberIndices,
    WZ1PaperTubeCover.fiberIndices,
    Finset.mem_filter,
    Finset.mem_univ,
    true_and
  ]
  constructor
  · intro sourceCovered
    exact
      (output.cover.toWZ1PaperTubeCover.parent_unique
        source parent sourceCovered).symm
  · intro parentEq
    rw [← parentEq]
    exact
      output.cover.toWZ1PaperTubeCover.parent_covers source

/--
The exact packet-cell multiplicity in the internal four-degree certificate
gives the fiber cap needed by the trace mass transfer.
-/
theorem windowed_refined_fiberPointMultiplicity_le
    (hdelta : 0 < delta)
    (parent : Fin output.coarse.family.card)
    (point : Point3) :
    (output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
        output.refinement.refined parent point : ENNReal) ≤
      output.muFine := by
  by_cases positive :
      0 <
        output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
          output.refinement.refined parent point
  · let cell := wz1PaperGridIndex delta point
    let fiberSources :=
      (output.cover.toWZ1PaperTubeCover.fiberIndices parent).filter
        fun source =>
          point ∈ output.refinement.refined.carrier source
    have fiberNonempty : fiberSources.Nonempty := by
      change 0 < fiberSources.card at positive
      exact Finset.card_pos.mp positive
    rcases fiberNonempty with ⟨sourceIndex, sourceMem⟩
    have sourceData := Finset.mem_filter.mp sourceMem
    have sourceFiber :
        sourceIndex ∈
          wz2PaperFullFiberIndices
            output.refinement.selected.family
            output.coarse.family parent := by
      rw [output.windowed_fullFiberIndices_eq parent]
      exact sourceData.1
    have wholeCell :
        wz1PaperGridCube delta cell ⊆
          output.refinement.refined.carrier sourceIndex := by
      exact
        output.refined_cubical sourceIndex point sourceData.2
    have cellActive :
        cell ∈
          wz1PaperActiveCells output.refinement.refined hdelta := by
      rw [mem_wz1PaperActiveCells]
      refine ⟨?_, ⟨point, ⟨sourceIndex, sourceData.2⟩, ?_⟩⟩
      · exact
          paper_point_gridIndex_in_window hdelta
            (output.refinement.refined.subset_body
              sourceIndex sourceData.2).2
      · exact (mem_wz1PaperGridCube delta cell point).mpr rfl
    have packetMem : (parent, cell) ∈ output.packetCells := by
      rw [output.packetCells_eq]
      apply Finset.mem_filter.mpr
      refine
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_univ parent, cellActive⟩, ?_⟩
      exact
        ⟨sourceIndex,
          Finset.mem_filter.mpr ⟨sourceFiber, wholeCell⟩⟩
    have activeFiberEq :
        fiberSources =
          (wz2PaperFullFiberIndices
              output.refinement.selected.family
              output.coarse.family parent).filter
            fun candidate =>
              wz1PaperGridCube delta cell ⊆
                output.refinement.refined.carrier candidate := by
      dsimp only [fiberSources]
      rw [← output.windowed_fullFiberIndices_eq parent]
      apply Finset.filter_congr
      intro candidate _candidateFiber
      constructor
      · intro candidatePoint
        exact output.refined_cubical candidate point candidatePoint
      · intro candidateCell
        exact candidateCell
          ((mem_wz1PaperGridCube delta cell point).mpr rfl)
    have countEq : fiberSources.card = output.muFine := by
      rw [activeFiberEq, output.exact_fine_multiplicity
        (parent, cell) packetMem]
    unfold WZ1PaperTubeCover.fiberPointMultiplicity
    norm_cast
    exact countEq.le
  · have zero :
        output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
            output.refinement.refined parent point =
          0 :=
      Nat.eq_zero_of_not_pos positive
    rw [zero]
    simp

private theorem windowedFinePaperTrace_fiberPointMultiplicity_le
    (fineTrace :
      Kakeya.Streamlined.TubeShading output.refinement.selected.family)
    (fineTraceSubset :
      ∀ source,
        fineTrace.carrier source ⊆
          output.refinement.refined.carrier source)
    (refinedFiberMultiplicity :
      ∀ parent point,
        (output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
            output.refinement.refined parent point : ENNReal) ≤
          output.muFine)
    (parent : Fin output.coarse.family.card)
    (point : Point3) :
    (output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
        (output.windowedFinePaperTrace fineTrace fineTraceSubset)
        parent point : ENNReal) ≤
      output.muFine := by
  calc
    (output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
        (output.windowedFinePaperTrace fineTrace fineTraceSubset)
        parent point : ENNReal) ≤
        output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
          output.refinement.refined parent point := by
      exact_mod_cast Finset.card_le_card (by
        intro source sourceMem
        have sourceData := Finset.mem_filter.mp sourceMem
        exact Finset.mem_filter.mpr
          ⟨sourceData.1, fineTraceSubset source sourceData.2⟩)
    _ ≤ output.muFine :=
      refinedFiberMultiplicity parent point

/--
The exact fine trace mass is at most `muFine` times the induced coarse trace
mass.  This is the full quantitative content of grouping the trace by final
V4 parents.
-/
theorem windowedFineTrace_mass_le_muFine_mul_coarseTrace_mass
    (fineTrace :
      Kakeya.Streamlined.TubeShading output.refinement.selected.family)
    (fineTraceSubset :
      ∀ source,
        fineTrace.carrier source ⊆
          output.refinement.refined.carrier source)
    (refinedFiberMultiplicity :
      ∀ parent point,
        (output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
            output.refinement.refined parent point : ENNReal) ≤
          output.muFine)
    (fineTraceInParent :
      ∀ source,
        fineTrace.carrier source ⊆
          (output.coarse.family.tube
            (output.cover.toWZ1PaperTubeCover.parent source)).carrier) :
    fineTrace.mass ≤
      (output.muFine : ENNReal) *
        (output.windowedCoarseTrace
          fineTrace fineTraceInParent).mass := by
  have paperMass :=
    output.cover.toWZ1PaperTubeCover
      |>.fine_mass_le_fiberCap_mul_coarse_mass
        (output.windowedFinePaperTrace fineTrace fineTraceSubset)
        (output.windowedCoarsePaperTrace fineTrace fineTraceSubset)
        (output.windowedFinePaperTrace_point_compatibility
          fineTrace fineTraceSubset)
        (output.windowedFinePaperTrace_fiberPointMultiplicity_le
          fineTrace fineTraceSubset refinedFiberMultiplicity)
  exact paperMass

/-- The induced ordinary coarse trace lies in the already constructed final
cropped coarse shaded union. -/
theorem windowedCoarseTrace_union_subset_coarseShading
    (fineTrace :
      Kakeya.Streamlined.TubeShading output.refinement.selected.family)
    (fineTraceSubset :
      ∀ source,
        fineTrace.carrier source ⊆
          output.refinement.refined.carrier source)
    (fineTraceInParent :
      ∀ source,
        fineTrace.carrier source ⊆
          (output.coarse.family.tube
            (output.cover.toWZ1PaperTubeCover.parent source)).carrier) :
    (output.windowedCoarseTrace
        fineTrace fineTraceInParent).union ⊆
      output.coarseShading.union := by
  rintro point ⟨parent, pointMem⟩
  rcases Set.mem_iUnion.mp pointMem with ⟨source, pointMem⟩
  rcases Set.mem_iUnion.mp pointMem with ⟨parentEq, pointMem⟩
  have refinedMem :
      point ∈ output.refinement.refined.carrier source :=
    fineTraceSubset source pointMem
  refine ⟨parent, ?_⟩
  have coarseMem :=
    output.balanced.point_compatibility source point refinedMem
  rwa [parentEq] at coarseMem

/-- Parentwise support in both the ordinary parent and the already selected
cropped coarse shading. -/
theorem windowedCoarseTrace_carrier_subset
    (fineTrace :
      Kakeya.Streamlined.TubeShading output.refinement.selected.family)
    (fineTraceSubset :
      ∀ source,
        fineTrace.carrier source ⊆
          output.refinement.refined.carrier source)
    (fineTraceInParent :
      ∀ source,
        fineTrace.carrier source ⊆
          (output.coarse.family.tube
            (output.cover.toWZ1PaperTubeCover.parent source)).carrier)
    (parent : Fin output.coarse.family.card) :
    (output.windowedCoarseTrace
          fineTrace fineTraceInParent).carrier parent ⊆
        (output.coarse.family.tube parent).carrier ∩
          output.coarseShading.carrier parent := by
  intro point pointMem
  refine
    ⟨(output.windowedCoarseTrace
        fineTrace fineTraceInParent).subset_body parent pointMem, ?_⟩
  rcases Set.mem_iUnion.mp pointMem with ⟨source, pointMem⟩
  rcases Set.mem_iUnion.mp pointMem with ⟨parentEq, pointMem⟩
  have refinedMem :
      point ∈ output.refinement.refined.carrier source :=
    fineTraceSubset source pointMem
  have coarseMem :=
    output.balanced.point_compatibility source point refinedMem
  rwa [parentEq] at coarseMem

/--
A scalar lower bound on the fine trace gives density of the induced ordinary
coarse trace after paying exactly the final fiber cap.
-/
theorem windowedCoarseTrace_dense_of_mass_lower
    (fineTrace :
      Kakeya.Streamlined.TubeShading output.refinement.selected.family)
    (fineTraceSubset :
      ∀ source,
        fineTrace.carrier source ⊆
          output.refinement.refined.carrier source)
    (refinedFiberMultiplicity :
      ∀ parent point,
        (output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
            output.refinement.refined parent point : ENNReal) ≤
          output.muFine)
    (fineTraceInParent :
      ∀ source,
        fineTrace.carrier source ⊆
          (output.coarse.family.tube
            (output.cover.toWZ1PaperTubeCover.parent source)).carrier)
    (lambda massLower : ENNReal)
    (traceMassLower : massLower ≤ fineTrace.mass)
    (absorption :
      (output.muFine : ENNReal) *
          (lambda * output.coarse.family.toBodyFamily.mass) ≤
        massLower) :
    (output.windowedCoarseTrace
      fineTrace fineTraceInParent).IsLambdaDense lambda := by
  have scaled :
      (output.muFine : ENNReal) *
          (lambda * output.coarse.family.toBodyFamily.mass) ≤
        (output.muFine : ENNReal) *
          (output.windowedCoarseTrace
            fineTrace fineTraceInParent).mass :=
    absorption.trans <|
      traceMassLower.trans <|
        output.windowedFineTrace_mass_le_muFine_mul_coarseTrace_mass
          fineTrace fineTraceSubset refinedFiberMultiplicity
            fineTraceInParent
  exact
    (ENNReal.mul_le_mul_iff_right
      (by exact_mod_cast output.muFine_pos.ne')
      (ENNReal.natCast_ne_top output.muFine)).mp scaled

end PureWZ2Prop62FourDegreeOutputCertificate

namespace Prop62PaperAudit.V4

/-- The exact final fine ordinary trace attached to the normalized V4 chain. -/
noncomputable def Prop62V4RichCertificateCompanionData.finalWindowedFineTrace
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent)
    {rho : WZ2PaperRequestedScale delta}
    {hdelta : 0 < delta}
    (preparation :
      FixedGridPreparationData
        (rho := rho.1) normalized.croppedRefined hdelta)
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {metricCertificate :
      PureWZ2Prop62MetricParentsV4Certificate
        preparation.cleanup.refined rho fineParentDistanceConstant
          parentConstant fiberConstant}
    {eta : ℝ}
    {packetDensityExponent cwaLossExponent polylogExponent : ℕ}
    (rich :
      Prop62V4RichCertificateCompanionData
        (eta := eta)
        (packetDensityExponent := packetDensityExponent)
        (cwaLossExponent := cwaLossExponent)
        (polylogExponent := polylogExponent)
        hdelta
        (prop62V4FixedGridMetricCompanionOfCertificate
          normalized preparation metricCertificate)) :
    Kakeya.Streamlined.TubeShading
      rich.outputCertificate.refinement.selected.family :=
  normalized.finalOrdinaryTrace
    rich.fixedGridComposedSelected
    rich.fixedGridComposedShading

namespace Prop62V4RichCertificateCompanionData

variable
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent}
    {rho : WZ2PaperRequestedScale delta}
    {hdelta : 0 < delta}
    {preparation :
      FixedGridPreparationData
        (rho := rho.1) normalized.croppedRefined hdelta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {metricCertificate :
      PureWZ2Prop62MetricParentsV4Certificate
        preparation.cleanup.refined rho fineParentDistanceConstant
          parentConstant fiberConstant}
    {eta : ℝ}
    {packetDensityExponent cwaLossExponent polylogExponent : ℕ}
    (rich :
      Prop62V4RichCertificateCompanionData
        (eta := eta)
        (packetDensityExponent := packetDensityExponent)
        (cwaLossExponent := cwaLossExponent)
        (polylogExponent := polylogExponent)
        hdelta
        (prop62V4FixedGridMetricCompanionOfCertificate
          normalized preparation metricCertificate))

/-- The centered-parent certificate propagates through the exact Target-4
`coarseSelected` reindex. -/
theorem finalParentsCentered :
    ∀ parent,
      wz2PaperCenteredLineTube (targetScale := rho.1)
          (rich.outputCertificate.coarse.family.tube parent) =
        rich.outputCertificate.coarse.family.tube parent := by
  have projectedCentered :
      ∀ parent,
        wz2PaperCenteredLineTube (targetScale := rho.1)
            ((prop62V4FixedGridMetricCompanionOfCertificate
              normalized preparation metricCertificate
            ).metric.scaleData.coarse.tube parent) =
          (prop62V4FixedGridMetricCompanionOfCertificate
            normalized preparation metricCertificate
          ).metric.scaleData.coarse.tube parent := by
    change
      ∀ parent,
        wz2PaperCenteredLineTube (targetScale := rho.1)
            (metricCertificate.toMetricData.scaleData.coarse.tube parent) =
          metricCertificate.toMetricData.scaleData.coarse.tube parent
    rw [metricCertificate.toMetricData_coarse_eq]
    exact metricCertificate.coarse_centered
  intro parent
  change
    wz2PaperCenteredLineTube (targetScale := rho.1)
        (rich.producer.families.restriction.coarseSelected.family.tube
          parent) =
      rich.producer.families.restriction.coarseSelected.family.tube parent
  rw [rich.producer.families.restriction.coarseSelected.tube_eq]
  exact projectedCentered
    (rich.producer.families.restriction.coarseSelected.embedding parent)

/--
Exact scalar condition needed to turn the final fine-trace lower bound into
`lambda`-density of the induced ordinary coarse trace.
-/
def WindowedCoarseDensityAbsorption
    (lambda : ENNReal) : Prop :=
  (rich.outputCertificate.muFine : ENNReal) *
      (lambda *
        rich.outputCertificate.coarse.family.toBodyFamily.mass) ≤
    (100 : ENNReal)⁻¹ *
      (Kakeya.realRpowENN delta sourceLoss / 2) *
      rich.fixedGridComposedShading.mass

theorem finalWindowedFineTrace_subset_refined
    (fineIndex :
      Fin rich.outputCertificate.refinement.selected.family.card) :
    (rich.finalWindowedFineTrace normalized preparation).carrier fineIndex ⊆
      rich.outputCertificate.refinement.refined.carrier fineIndex := by
  intro point pointMem
  exact pointMem.2

/-- The normalization trace estimate already supplies the complete final
fine-trace mass lower bound, independently of the missing centered-parent
provenance. -/
theorem finalWindowedFineTrace_mass_lower :
    (100 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN delta sourceLoss / 2) *
          rich.fixedGridComposedShading.mass ≤
      (rich.finalWindowedFineTrace normalized preparation).mass :=
  normalized.finalOrdinaryTrace_mass_lower_normalized
    rich.fixedGridComposedSelected rich.fixedGridComposedShading
    normalized.final_extremal.delta_pos
    rich.fixedGridComposed_cubical
    rich.fixedGridComposed_subshading

/--
Every genuinely selected parent--cell incidence contains a point of the final
ordinary trace.  The ordinary point is extracted in the same fine
`delta`-cell as the defining refined point; `packet_coarse_support` then keeps
it in the original `rho`-cell.
-/
theorem selectedParentCell_exists_finalWindowedFineTrace_point
    (parent : Fin rich.outputCertificate.coarse.family.card)
    (cell : WZ2PaperCellIndex)
    (cellMem :
      cell ∈ rich.outputCertificate.selectedParentCells parent) :
    ∃ source : Fin
          rich.outputCertificate.refinement.selected.family.card,
      rich.outputCertificate.cover.toWZ1PaperTubeCover.parent source =
          parent ∧
        ∃ point,
          point ∈
              (rich.finalWindowedFineTrace
                normalized preparation).carrier source ∧
            point ∈ wz1PaperGridCube rho.1 cell := by
  rcases
      rich.outputCertificate.selectedParentCells_witness
        parent cell cellMem
    with ⟨sourceIndex, parentEq, refinedPoint, refinedPointMem,
      refinedPointCell⟩
  let ordinaryIndex :=
    PureWZ2CroppedCriticalNormalizationData.ordinaryIndex
      normalized rich.fixedGridComposedSelected sourceIndex
  let ordinarySource : Set Point3 :=
    normalized.frame ''
      normalized.ordinaryRefined.carrier ordinaryIndex
  let fineCell := wz1PaperGridIndex delta refinedPoint
  have refinedPointFineCell :
      refinedPoint ∈ wz1PaperGridCube delta fineCell :=
    (mem_wz1PaperGridCube delta fineCell refinedPoint).mpr rfl
  have finalSubset :
      refinedPoint ∈
        normalized.croppedRefined.carrier
          (rich.fixedGridComposedSelected.embedding sourceIndex) :=
    rich.fixedGridComposed_subshading sourceIndex refinedPointMem
  have indexEq :
      normalized.indexEquiv ordinaryIndex =
        rich.fixedGridComposedSelected.embedding sourceIndex := by
    exact normalized.indexEquiv.apply_symm_apply
      (rich.fixedGridComposedSelected.embedding sourceIndex)
  have pointDense :
      refinedPoint ∈
        pureWZ2DenseCubicalization
          (normalized.croppedFamily.tube
            (rich.fixedGridComposedSelected.embedding sourceIndex))
          ordinarySource := by
    have normalizedEq :=
      normalized.cropped_carrier_eq_dense_cubicalization ordinaryIndex
    rw [indexEq] at normalizedEq
    rw [← normalizedEq]
    exact finalSubset
  have ordinarySourceVolumePos : 0 < volume ordinarySource := by
    have ordinaryDensity :
        (Kakeya.realRpowENN delta sourceLoss / 2) *
              volume
                (normalized.croppedFamily.tube
                  (rich.fixedGridComposedSelected.embedding
                    sourceIndex)).carrier ≤
          volume ordinarySource := by
      simpa only [ordinarySource, ordinaryIndex] using
        normalized.framed_ordinary_per_tube
          rich.fixedGridComposedSelected sourceIndex
    have densityPos :
        0 < Kakeya.realRpowENN delta sourceLoss / 2 := by
      apply ENNReal.div_pos
      · simp [Kakeya.realRpowENN,
          Real.rpow_pos_of_pos normalized.final_extremal.delta_pos]
      · norm_num
    have tubeVolumePos :
        0 <
          volume
            (normalized.croppedFamily.tube
              (rich.fixedGridComposedSelected.embedding
                sourceIndex)).carrier :=
      wz2_paper_ordinary_tube_volume_pos
        (normalized.croppedFamily.tube
          (rich.fixedGridComposedSelected.embedding sourceIndex))
        normalized.final_extremal.delta_pos
    exact
      (ENNReal.mul_pos densityPos.ne' tubeVolumePos.ne').trans_le
        ordinaryDensity
  have tubeVolumeTop :
      volume
          (normalized.croppedFamily.tube
            (rich.fixedGridComposedSelected.embedding
              sourceIndex)).carrier ≠ ⊤ :=
    wz2_paper_ordinary_tube_volume_ne_top
      (normalized.croppedFamily.tube
        (rich.fixedGridComposedSelected.embedding sourceIndex))
      normalized.final_extremal.delta_pos
  have fineCellDensity :
      (100 : ENNReal)⁻¹ *
            volume ordinarySource *
            (volume
              (normalized.croppedFamily.tube
                (rich.fixedGridComposedSelected.embedding
                  sourceIndex)).carrier)⁻¹ *
            volume (wz1PaperGridCube delta fineCell) ≤
        volume
          (ordinarySource ∩ wz1PaperGridCube delta fineCell) := by
    simpa only [pureWZ2DenseCubicalization, fineCell] using pointDense.2
  have fineCellTraceVolumePos :
      0 <
        volume
          (ordinarySource ∩ wz1PaperGridCube delta fineCell) := by
    have thresholdPos :
        0 <
          (100 : ENNReal)⁻¹ *
              volume ordinarySource *
              (volume
                (normalized.croppedFamily.tube
                  (rich.fixedGridComposedSelected.embedding
                    sourceIndex)).carrier)⁻¹ *
              volume (wz1PaperGridCube delta fineCell) := by
      exact
        ENNReal.mul_pos
          (ENNReal.mul_pos
            (ENNReal.mul_pos
              (ENNReal.inv_ne_zero.mpr (by norm_num))
              ordinarySourceVolumePos.ne').ne'
            (ENNReal.inv_ne_zero.mpr tubeVolumeTop)).ne'
          (wz1PaperGridCube_volume_pos
            normalized.final_extremal.delta_pos fineCell).ne'
    exact thresholdPos.trans_le fineCellDensity
  rcases
      nonempty_of_measure_ne_zero fineCellTraceVolumePos.ne'
    with ⟨ordinaryPoint, ordinaryPointSource, ordinaryPointFineCell⟩
  have wholeFineCell :
      wz1PaperGridCube delta fineCell ⊆
        rich.outputCertificate.refinement.refined.carrier sourceIndex :=
    rich.outputCertificate.refined_cubical
      sourceIndex refinedPoint refinedPointMem
  have ordinaryPointRefined :
      ordinaryPoint ∈
        rich.outputCertificate.refinement.refined.carrier sourceIndex :=
    wholeFineCell ordinaryPointFineCell
  have ordinaryPointTrace :
      ordinaryPoint ∈
        (rich.finalWindowedFineTrace
          normalized preparation).carrier sourceIndex := by
    exact ⟨ordinaryPointSource, ordinaryPointRefined⟩
  have sourceFiber :
      sourceIndex ∈
        wz2PaperFullFiberIndices
          rich.outputCertificate.refinement.selected.family
          rich.outputCertificate.coarse.family parent := by
    apply (mem_wz2PaperFullFiberIndices_iff parent sourceIndex).mpr
    rw [← parentEq]
    exact
      rich.outputCertificate.cover.toWZ1PaperTubeCover.parent_covers
        sourceIndex
  have fineCellActive :
      fineCell ∈
        wz1PaperActiveCells
          rich.outputCertificate.refinement.refined
          normalized.final_extremal.delta_pos := by
    rw [mem_wz1PaperActiveCells]
    refine ⟨?_, ⟨refinedPoint, ⟨sourceIndex, refinedPointMem⟩,
      refinedPointFineCell⟩⟩
    exact
      paper_point_gridIndex_in_window
        normalized.final_extremal.delta_pos
        (rich.outputCertificate.refinement.refined.subset_body
          sourceIndex refinedPointMem).2
  have packetMem :
      (parent, fineCell) ∈ rich.outputCertificate.packetCells := by
    rw [rich.outputCertificate.packetCells_eq]
    apply Finset.mem_filter.mpr
    refine
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_univ parent, fineCellActive⟩, ?_⟩
    exact
      ⟨sourceIndex,
        Finset.mem_filter.mpr ⟨sourceFiber, wholeFineCell⟩⟩
  have packetSupport :=
    rich.outputCertificate.packet_coarse_support
      (parent, fineCell) packetMem
  have refinedPointPacketCell :
      refinedPoint ∈
        wz1PaperGridCube rho.1
          (rich.outputCertificate.coarseOfFine fineCell) :=
    packetSupport.2.1 refinedPointFineCell
  have packetCellEq :
      rich.outputCertificate.coarseOfFine fineCell = cell := by
    exact
      ((mem_wz1PaperGridCube rho.1
        (rich.outputCertificate.coarseOfFine fineCell)
        refinedPoint).mp refinedPointPacketCell).symm.trans
          ((mem_wz1PaperGridCube rho.1 cell refinedPoint).mp
            refinedPointCell)
  have ordinaryPointCell :
      ordinaryPoint ∈ wz1PaperGridCube rho.1 cell := by
    rw [← packetCellEq]
    exact packetSupport.2.1 ordinaryPointFineCell
  exact
    ⟨sourceIndex, parentEq, ordinaryPoint,
      ordinaryPointTrace, ordinaryPointCell⟩

/--
Every genuine selected parent--cell incidence contributes a fixed-volume
piece to the ordinary carrier of that parent.
-/
theorem selectedParentCell_ordinary_overlap
    (ratioSmall : delta / rho.1 ≤ 1 / 24)
    (parent : Fin rich.outputCertificate.coarse.family.card)
    (cell : WZ2PaperCellIndex)
    (cellMem :
      cell ∈ rich.outputCertificate.selectedParentCells parent) :
    ENNReal.ofReal ((1 / 100000 : ℝ) * rho.1 ^ 3) ≤
      volume
        (wz1PaperGridCube rho.1 cell ∩
          (rich.outputCertificate.coarse.family.tube parent).carrier) := by
  rcases
      rich.selectedParentCell_exists_finalWindowedFineTrace_point
        (normalized := normalized) (preparation := preparation)
        parent cell cellMem
    with ⟨sourceIndex, parentEq, point, pointTrace, pointCell⟩
  have parentClose :
      wz1PaperLineDistance
          (rich.outputCertificate.refinement.selected.family.tube sourceIndex)
          (rich.outputCertificate.coarse.family.tube parent) ≤
        rho.1 / 2 := by
    have covered :=
      rich.outputCertificate.cover.toWZ1PaperTubeCover.parent_covers
        sourceIndex
    rwa [parentEq] at covered
  have axisWitness :
      ∃ axisPoint ∈
          Kakeya.unitSegment
            (rich.outputCertificate.coarse.family.tube parent).base
            (rich.outputCertificate.coarse.family.tube parent).direction,
        dist point axisPoint ≤ 5 * rho.1 / 6 := by
    apply
      fineOrdinaryTrace_exists_centeredParent_axisPoint
        normalized.final_extremal.delta_pos metricCertificate.rho_pos
        (rich.outputCertificate.refinement.selected.family.tube sourceIndex)
        (rich.outputCertificate.coarse.family.tube parent)
        (rich.outputCertificate.cover.fine_line_class sourceIndex)
        (rich.outputCertificate.cover.coarse_line_class parent)
        (rich.finalParentsCentered parent)
        ratioSmall parentClose
        ((rich.finalWindowedFineTrace
          normalized preparation).carrier sourceIndex)
        (by
          intro tracePoint tracePointMem
          exact
            (rich.finalWindowedFineTrace
              normalized preparation).subset_body sourceIndex tracePointMem)
        (by
          intro tracePoint tracePointMem
          exact
            (normalized.ordinary_axial_window
              (PureWZ2CroppedCriticalNormalizationData.ordinaryIndex
                normalized rich.fixedGridComposedSelected sourceIndex)
              tracePoint tracePointMem.1).trans (by norm_num))
        pointTrace
  exact
    ordinaryTube_gridCube_overlap_volume_lower_of_exists
      metricCertificate.rho_pos
      (rich.outputCertificate.coarse.family.tube parent)
      cell pointCell axisWitness

/-- The geometric selected-incidence route supplies the fixed mass retention
for the canonical final coarse ordinary trace. -/
theorem finalCoarseOrdinaryTrace_selectedIncidence_mass_lower
    (ratioSmall : delta / rho.1 ≤ 1 / 24) :
    (100000 : ENNReal)⁻¹ *
        rich.outputCertificate.selectedIncidenceCoarseShading.mass ≤
      rich.outputCertificate.finalCoarseOrdinaryTrace.mass := by
  apply
    rich.outputCertificate.finalCoarseOrdinaryTrace_mass_lower_of_cell_overlap
      metricCertificate.rho_pos
  intro parent cell cellMem
  exact
    rich.selectedParentCell_ordinary_overlap
      (normalized := normalized) (preparation := preparation)
      ratioSmall parent cell cellMem

/--
Half-structural-loss density of the genuine cropped incidences, together with
the fixed overlap receipt, gives full structural-loss density of the canonical
final coarse ordinary trace.
-/
theorem finalCoarseOrdinaryTrace_dense_of_selectedIncidence
    {floorLoss structuralBudget outputLoss : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss structuralBudget)
    (receipt :
      Prop62V4SelectedIncidenceScalarReceipt outputLoss critical)
    (deltaLe : delta ≤ receipt.delta₀)
    (rhoUpper : rho.1 ≤ Real.rpow delta outputLoss)
    (rhoSmall : rho.1 ≤ 1 / 24)
    (ratioSmall : delta / rho.1 ≤ 1 / 24)
    (selectedDensityScalar :
      (576 * (55296 * Kakeya.deltaTubeVolume 1) : ENNReal) *
          Kakeya.realRpowENN rho.1
            (critical.structuralLoss / 2) ≤
        Kakeya.realRpowENN delta
          ((packetDensityExponent : ℝ) * eta)) :
    rich.outputCertificate.finalCoarseOrdinaryTrace.IsLambdaDense
      (Kakeya.realRpowENN rho.1 critical.structuralLoss) := by
  have croppedDense :
      Kakeya.realRpowENN rho.1
            (critical.structuralLoss / 2) *
          rich.outputCertificate.coarse.family.toBodyFamily.mass ≤
        rich.outputCertificate.selectedIncidenceCoarseShading.mass := by
    have dense :=
      rich.outputCertificate.selectedIncidenceCoarseShading_dense
        normalized.final_extremal.delta_pos metricCertificate.rho_pos
        rhoSmall
        (Kakeya.realRpowENN rho.1
          (critical.structuralLoss / 2))
        selectedDensityScalar
    have paperDense :
        Kakeya.realRpowENN rho.1
              (critical.structuralLoss / 2) *
            (wz1PaperBodyFamily
              rich.outputCertificate.coarse.family).mass ≤
          rich.outputCertificate.selectedIncidenceCoarseShading.mass := by
      simpa [Kakeya.Streamlined.Shading.IsLambdaDense] using dense
    have ordinaryBodyMassLe :
        rich.outputCertificate.coarse.family.toBodyFamily.mass ≤
          (wz1PaperBodyFamily
            rich.outputCertificate.coarse.family).mass :=
      pureWZ2_ordinary_body_mass_le_cropped_body_mass
        metricCertificate.rho_pos
        (rhoSmall.trans (by norm_num))
        rich.outputCertificate.coarse.family
        rich.outputCertificate.cover.coarse_line_class
    calc
      Kakeya.realRpowENN rho.1
            (critical.structuralLoss / 2) *
          rich.outputCertificate.coarse.family.toBodyFamily.mass ≤
        Kakeya.realRpowENN rho.1
            (critical.structuralLoss / 2) *
          (wz1PaperBodyFamily
            rich.outputCertificate.coarse.family).mass := by
        gcongr
      _ ≤
          rich.outputCertificate.selectedIncidenceCoarseShading.mass :=
        paperDense
  have ordinaryOverlap :
      (100000 : ENNReal)⁻¹ *
          rich.outputCertificate.selectedIncidenceCoarseShading.mass ≤
        rich.outputCertificate.finalCoarseOrdinaryTrace.mass :=
    rich.finalCoarseOrdinaryTrace_selectedIncidence_mass_lower
      (normalized := normalized) (preparation := preparation) ratioSmall
  exact
    receipt.dense_of_half_dense_and_overlap
      normalized.final_extremal.delta_pos deltaLe
      metricCertificate.rho_pos rhoUpper
      croppedDense ordinaryOverlap

/--
Final ordinary critical-floor witness obtained entirely from genuine selected
parent--cell incidences.  No coarse ordinary density is assumed.
-/
noncomputable def finalCoarseCriticalWitness_of_selectedIncidence
    {floorLoss structuralBudget outputLoss : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss structuralBudget)
    (receipt :
      Prop62V4SelectedIncidenceScalarReceipt outputLoss critical)
    (deltaLe : delta ≤ receipt.delta₀)
    (rhoUpper : rho.1 ≤ Real.rpow delta outputLoss)
    (rhoSmall : rho.1 ≤ 1 / 24)
    (ratioSmall : delta / rho.1 ≤ 1 / 24)
    (selectedDensityScalar :
      (576 * (55296 * Kakeya.deltaTubeVolume 1) : ENNReal) *
          Kakeya.realRpowENN rho.1
            (critical.structuralLoss / 2) ≤
        Kakeya.realRpowENN delta
          ((packetDensityExponent : ℝ) * eta))
    (parentCWAWeakening :
      Kakeya.realRpowENN delta
          (-(cwaLossExponent : ℝ) * eta) ≤
        Kakeya.realRpowENN rho.1
          (-critical.structuralLoss)) :
    Prop62V4FinalCoarseCriticalWitness
      rich.outputCertificate critical.structuralLoss :=
  rich.outputCertificate.finalCoarseCriticalWitnessOfTraceDense
    critical.structuralLoss parentCWAWeakening
    (rich.finalCoarseOrdinaryTrace_dense_of_selectedIncidence
      (normalized := normalized) (preparation := preparation)
      critical receipt deltaLe rhoUpper rhoSmall ratioSmall
      selectedDensityScalar)

/--
The central-window fine trace lies in its exact centered V4 metric parent at
the same radius.
-/
theorem finalWindowedFineTrace_subset_assignedParent
    (ratioSmall : delta / rho.1 ≤ 1 / 24)
    (fineIndex :
      Fin rich.outputCertificate.refinement.selected.family.card) :
    (rich.finalWindowedFineTrace normalized preparation).carrier fineIndex ⊆
      (rich.outputCertificate.coarse.family.tube
        (rich.outputCertificate.cover.toWZ1PaperTubeCover.parent
          fineIndex)).carrier := by
  let parent :=
    rich.outputCertificate.cover.toWZ1PaperTubeCover.parent fineIndex
  apply
    fineOrdinaryTrace_subset_sameRadius_centeredParent
      normalized.final_extremal.delta_pos metricCertificate.rho_pos
      (rich.outputCertificate.refinement.selected.family.tube fineIndex)
      (rich.outputCertificate.coarse.family.tube parent)
      (rich.outputCertificate.cover.fine_line_class fineIndex)
      (rich.outputCertificate.cover.coarse_line_class parent)
      (rich.finalParentsCentered parent)
      ratioSmall
      (rich.outputCertificate.cover.toWZ1PaperTubeCover.parent_covers fineIndex)
      ((rich.finalWindowedFineTrace
        normalized preparation).carrier fineIndex)
      (by
        intro point pointMem
        change
          point ∈
            (rich.outputCertificate.refinement.selected.family.tube
              fineIndex).carrier
        exact
          (rich.finalWindowedFineTrace
            normalized preparation).subset_body fineIndex pointMem)
  intro point pointMem
  exact (normalized.ordinary_axial_window
    (PureWZ2CroppedCriticalNormalizationData.ordinaryIndex
      normalized rich.fixedGridComposedSelected fineIndex)
    point pointMem.1).trans (by norm_num)

end Prop62V4RichCertificateCompanionData

end Prop62PaperAudit.V4

end Kakeya.Assouad

end
