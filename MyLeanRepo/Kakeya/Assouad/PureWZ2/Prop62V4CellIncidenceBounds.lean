import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CanonicalFourDegreeOutput
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGridCubeVolume

/-!
# Proposition 6.2: source-indexed fine mass in an active coarse cell

This module deliberately counts the final shading with its source index
retained.  It is therefore different from the balanced-cover mass, which is
the volume of the union of the source carriers.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62PacketCellInput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput cover sourceShading)
    (multiplicity : input.FineMultiplicityClassData)
    (parentClass : input.ParentClassData multiplicity)
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        coarse ambientConstant scaleWindow}
    (treeCleanup :
      input.ParentTreeCleanupData
        multiplicity parentClass schedule)
    (exactification :
      input.PacketCellExactificationData
        multiplicity parentClass treeCleanup)
    (parentDegree :
      input.ReferenceParentDegreeData
        multiplicity parentClass treeCleanup exactification)
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}
    {A0 : ℕ}
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup
        exactification parentDegree bins A0)
    {degreeLoss : ℕ}
    (good : core.ranges.GoodBalancingSampleData degreeLoss)
    (families :
      input.TerminalCompleteFamiliesData
        multiplicity parentClass treeCleanup exactification
          core.ranges)
    {fiberConstant densityConstant : ENNReal}
    {logExponent : ℕ}
    (output :
      input.FourDegreeLemmaOutputData
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          fiberConstant densityConstant logExponent)

/-- The actual fine mass in `coarseCell`, with each source carrier counted
separately.  In particular this does not collapse overlaps by taking a union. -/
def indexedCellMass
    (coarseCell : WZ2PaperCellIndex) : ENNReal :=
  ∑ source : Fin families.restriction.fineSelected.family.card,
    volume
      (output.fineShading.carrier source ∩
        wz1PaperGridCube rho coarseCell)

/-- The retained fine cells of one ambient source whose canonical coarse
owner is `coarseCell`. -/
def retainedCellsForSourceAt
    (source : Fin fine.card)
    (coarseCell : WZ2PaperCellIndex) :
    Finset WZ2PaperCellIndex :=
  (input.retainedCellsForSource
      multiplicity parentClass treeCleanup exactification
        core.ranges good source).filter fun fineCell =>
    input.coarseCellOf fineCell = coarseCell

/-- Local form of the exact-shading carrier identity.  Intersecting one
source carrier with a coarse cube keeps precisely the retained fine cubes
whose canonical coarse owner is that cube. -/
theorem exactFineShading_carrier_inter_coarseCube
    (source : Fin fine.card)
    (coarseCell : WZ2PaperCellIndex) :
    (input.exactFineShading
        multiplicity parentClass treeCleanup exactification
          core.ranges good).carrier source ∩
        wz1PaperGridCube rho coarseCell =
      wz2RetainedCellsUnion delta
        (input.retainedCellsForSourceAt
          multiplicity parentClass treeCleanup exactification
            parentDegree core good source coarseCell) := by
  rw [ExactFineShading.carrier_eq
    input multiplicity parentClass treeCleanup exactification
      core.ranges good source]
  ext point
  constructor
  · rintro ⟨pointCarrier, pointCoarse⟩
    rcases Set.mem_iUnion₂.mp pointCarrier with
      ⟨fineCell, fineCellMem, pointFine⟩
    rcases Finset.mem_image.mp fineCellMem with
      ⟨edge, edgeMem, edgeFine⟩
    have sourceSelected :
        input.sourceSelectedOnEdge
          multiplicity parentClass treeCleanup exactification
            source edge :=
      (Finset.mem_filter.mp edgeMem).2
    have packetData :=
      exactification.selectedSources_subset
        (input.referencePairOfEdge
          multiplicity parentClass treeCleanup exactification edge)
        sourceSelected
    have packetMem :=
      (input.mem_packetCellSources_iff
        (exactification.incidence.edgeParent edge)
        (exactification.incidence.edgeFineCell edge) source).mp <| by
          simpa [referencePairOfEdge,
            PureWZ2Prop62FourDegreeIncidenceData.edgeParent,
            PureWZ2Prop62FourDegreeIncidenceData.edgeFineCell] using
              packetData
    have fineContainment :=
      input.fine_cell_containment
        (exactification.incidence.edgeFineCell edge) packetMem.1
    have pointOwnCoarse :
        point ∈ wz1PaperGridCube rho
          (input.coarseCellOf
            (exactification.incidence.edgeFineCell edge)) := by
      apply fineContainment
      rwa [edgeFine]
    have coarseEq :
        input.coarseCellOf fineCell = coarseCell := by
      have firstIndex :=
        (mem_wz1PaperGridCube rho
          (input.coarseCellOf
            (exactification.incidence.edgeFineCell edge)) point).mp
              pointOwnCoarse
      have secondIndex :=
        (mem_wz1PaperGridCube rho coarseCell point).mp pointCoarse
      rw [edgeFine] at firstIndex
      exact firstIndex.symm.trans secondIndex
    exact Set.mem_iUnion₂.mpr
      ⟨fineCell, Finset.mem_filter.mpr ⟨fineCellMem, coarseEq⟩,
        pointFine⟩
  · intro pointMem
    rcases Set.mem_iUnion₂.mp pointMem with
      ⟨fineCell, fineCellMem, pointFine⟩
    have retainedMem := (Finset.mem_filter.mp fineCellMem).1
    have coarseEq := (Finset.mem_filter.mp fineCellMem).2
    rcases Finset.mem_image.mp retainedMem with
      ⟨edge, edgeMem, edgeFine⟩
    have sourceSelected :
        input.sourceSelectedOnEdge
          multiplicity parentClass treeCleanup exactification
            source edge :=
      (Finset.mem_filter.mp edgeMem).2
    have packetData :=
      exactification.selectedSources_subset
        (input.referencePairOfEdge
          multiplicity parentClass treeCleanup exactification edge)
        sourceSelected
    have packetMem :=
      (input.mem_packetCellSources_iff
        (exactification.incidence.edgeParent edge)
        (exactification.incidence.edgeFineCell edge) source).mp <| by
          simpa [referencePairOfEdge,
            PureWZ2Prop62FourDegreeIncidenceData.edgeParent,
            PureWZ2Prop62FourDegreeIncidenceData.edgeFineCell] using
              packetData
    have fineContainment :=
      input.fine_cell_containment
        (exactification.incidence.edgeFineCell edge) packetMem.1
    refine ⟨Set.mem_iUnion₂.mpr ⟨fineCell, retainedMem, pointFine⟩, ?_⟩
    rw [← coarseEq]
    rw [← edgeFine]
    apply fineContainment
    rwa [edgeFine]

theorem exactFineShading_carrier_inter_coarseCube_volume
    (source : Fin fine.card)
    (coarseCell : WZ2PaperCellIndex) :
    volume
        ((input.exactFineShading
            multiplicity parentClass treeCleanup exactification
              core.ranges good).carrier source ∩
          wz1PaperGridCube rho coarseCell) =
      ((input.retainedCellsForSourceAt
          multiplicity parentClass treeCleanup exactification
            parentDegree core good source coarseCell).card : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  rw [input.exactFineShading_carrier_inter_coarseCube
    multiplicity parentClass treeCleanup exactification
      parentDegree core good source coarseCell]
  exact
    wz1PaperGridCube_volume_biUnion input.delta_pos
      (input.retainedCellsForSourceAt
        multiplicity parentClass treeCleanup exactification
          parentDegree core good source coarseCell)

theorem retainedCellsForSourceAt_eq_image
    (source : Fin fine.card)
    (coarseCell : WZ2PaperCellIndex) :
    input.retainedCellsForSourceAt
        multiplicity parentClass treeCleanup exactification
          parentDegree core good source coarseCell =
      (((core.ranges.selectedEdges good.sample).filter fun edge =>
          exactification.incidence.edgeCoarseCell edge = coarseCell).filter
        fun edge =>
          input.sourceSelectedOnEdge
            multiplicity parentClass treeCleanup exactification
              source edge).image
        exactification.incidence.edgeFineCell := by
  ext fineCell
  constructor
  · intro fineCellMem
    have retainedData := Finset.mem_filter.mp fineCellMem
    rcases Finset.mem_image.mp retainedData.1 with
      ⟨edge, edgeMem, edgeFine⟩
    apply Finset.mem_image.mpr
    refine ⟨edge, Finset.mem_filter.mpr ⟨?_, ?_⟩, edgeFine⟩
    · apply Finset.mem_filter.mpr
      refine ⟨(Finset.mem_filter.mp edgeMem).1, ?_⟩
      unfold PureWZ2Prop62FourDegreeIncidenceData.edgeCoarseCell
      rw [exactification.incidence_coarseCellOf_eq, edgeFine]
      exact retainedData.2
    · exact (Finset.mem_filter.mp edgeMem).2
  · intro fineCellMem
    rcases Finset.mem_image.mp fineCellMem with
      ⟨edge, edgeMem, edgeFine⟩
    have edgeData := Finset.mem_filter.mp edgeMem
    have selectedData := Finset.mem_filter.mp edgeData.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨edge, ?_, edgeFine⟩, ?_⟩
    · exact Finset.mem_filter.mpr ⟨selectedData.1, edgeData.2⟩
    · unfold PureWZ2Prop62FourDegreeIncidenceData.edgeCoarseCell at selectedData
      rw [exactification.incidence_coarseCellOf_eq] at selectedData
      rw [← edgeFine]
      exact selectedData.2

theorem retainedCellsForSourceAt_card
    (source : Fin fine.card)
    (coarseCell : WZ2PaperCellIndex) :
    (input.retainedCellsForSourceAt
        multiplicity parentClass treeCleanup exactification
          parentDegree core good source coarseCell).card =
      (((core.ranges.selectedEdges good.sample).filter fun edge =>
          exactification.incidence.edgeCoarseCell edge = coarseCell).filter
        fun edge =>
          input.sourceSelectedOnEdge
            multiplicity parentClass treeCleanup exactification
              source edge).card := by
  rw [input.retainedCellsForSourceAt_eq_image
    multiplicity parentClass treeCleanup exactification
      parentDegree core good source coarseCell]
  apply Finset.card_image_iff.mpr
  apply
    (ExactFineShading.edgeFineCell_injective_on_sourceSelected
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good source).mono
  intro edge edgeMem
  have edgeData := Finset.mem_filter.mp edgeMem
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp edgeData.1).1, edgeData.2⟩

private theorem local_source_edge_count_swap
    (coarseCell : WZ2PaperCellIndex) :
    (∑ source : Fin fine.card,
        (((core.ranges.selectedEdges good.sample).filter fun edge =>
            exactification.incidence.edgeCoarseCell edge = coarseCell).filter
          fun edge =>
            input.sourceSelectedOnEdge
              multiplicity parentClass treeCleanup exactification
                source edge).card) =
      ∑ edge ∈
          (core.ranges.selectedEdges good.sample).filter fun edge =>
            exactification.incidence.edgeCoarseCell edge = coarseCell,
        ((Finset.univ : Finset (Fin fine.card)).filter fun source =>
          input.sourceSelectedOnEdge
            multiplicity parentClass treeCleanup exactification
              source edge).card := by
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]

theorem sum_retainedCellsForSourceAt_card
    (coarseCell : WZ2PaperCellIndex) :
    (∑ source : Fin fine.card,
        (input.retainedCellsForSourceAt
          multiplicity parentClass treeCleanup exactification
            parentDegree core good source coarseCell).card) =
      multiplicity.muFine *
        exactification.incidence.coarseDegree
          (core.ranges.selectedEdges good.sample) coarseCell := by
  calc
    (∑ source : Fin fine.card,
        (input.retainedCellsForSourceAt
          multiplicity parentClass treeCleanup exactification
            parentDegree core good source coarseCell).card) =
        ∑ source : Fin fine.card,
          (((core.ranges.selectedEdges good.sample).filter fun edge =>
              exactification.incidence.edgeCoarseCell edge = coarseCell).filter
            fun edge =>
              input.sourceSelectedOnEdge
                multiplicity parentClass treeCleanup exactification
                  source edge).card := by
      apply Finset.sum_congr rfl
      intro source _sourceMem
      exact input.retainedCellsForSourceAt_card
        multiplicity parentClass treeCleanup exactification
          parentDegree core good source coarseCell
    _ =
        ∑ edge ∈
            (core.ranges.selectedEdges good.sample).filter fun edge =>
              exactification.incidence.edgeCoarseCell edge = coarseCell,
          ((Finset.univ : Finset (Fin fine.card)).filter fun source =>
            input.sourceSelectedOnEdge
              multiplicity parentClass treeCleanup exactification
                source edge).card :=
      local_source_edge_count_swap
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good coarseCell
    _ =
        ∑ _edge ∈
            (core.ranges.selectedEdges good.sample).filter fun edge =>
              exactification.incidence.edgeCoarseCell edge = coarseCell,
          multiplicity.muFine := by
      apply Finset.sum_congr rfl
      intro edge edgeMem
      exact
        ExactFineShading.selectedSourceFilter_card
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good (Finset.mem_filter.mp edgeMem).1
    _ =
        multiplicity.muFine *
          exactification.incidence.coarseDegree
            (core.ranges.selectedEdges good.sample) coarseCell := by
      simp [PureWZ2Prop62FourDegreeIncidenceData.coarseDegree]
      ring

theorem retainedCellsForSourceAt_eq_empty_of_not_terminal
    {source : Fin fine.card}
    (sourceNotTerminal : source ∉ families.terminalFine)
    (coarseCell : WZ2PaperCellIndex) :
    input.retainedCellsForSourceAt
        multiplicity parentClass treeCleanup exactification
          parentDegree core good source coarseCell = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro retainedNonempty
  rcases retainedNonempty with ⟨fineCell, fineCellMem⟩
  have retainedMem := (Finset.mem_filter.mp fineCellMem).1
  let point := cellCorner delta fineCell
  have pointFine : point ∈ wz1PaperGridCube delta fineCell :=
    cellCorner_mem_gridCube input.delta_pos fineCell
  have pointCarrier :
      point ∈
        (input.ambientExactShading
          multiplicity parentClass treeCleanup exactification
            core.ranges good).carrier source := by
    rw [ExactFineShading.carrier_eq
      input multiplicity parentClass treeCleanup exactification
        core.ranges good source]
    exact Set.mem_iUnion₂.mpr ⟨fineCell, retainedMem, pointFine⟩
  exact sourceNotTerminal <|
    input.ambientExact_source_mem_terminalFine
      multiplicity parentClass treeCleanup exactification
        core.ranges good families ⟨point, pointCarrier⟩

theorem sum_terminal_retainedCellsForSourceAt_card
    (coarseCell : WZ2PaperCellIndex) :
    (∑ source : Fin families.restriction.fineSelected.family.card,
        (input.retainedCellsForSourceAt
          multiplicity parentClass treeCleanup exactification
            parentDegree core good
            (families.restriction.fineSelected.embedding source)
            coarseCell).card) =
      multiplicity.muFine *
        exactification.incidence.coarseDegree
          (core.ranges.selectedEdges good.sample) coarseCell := by
  calc
    (∑ source : Fin families.restriction.fineSelected.family.card,
        (input.retainedCellsForSourceAt
          multiplicity parentClass treeCleanup exactification
            parentDegree core good
            (families.restriction.fineSelected.embedding source)
            coarseCell).card) =
        ∑ source ∈ families.terminalFine,
          (input.retainedCellsForSourceAt
            multiplicity parentClass treeCleanup exactification
              parentDegree core good source coarseCell).card := by
      have imageSum :
          (∑ ambientSource ∈
              Finset.image
                families.restriction.fineSelected.embedding Finset.univ,
              (input.retainedCellsForSourceAt
                multiplicity parentClass treeCleanup exactification
                  parentDegree core good ambientSource coarseCell).card) =
            ∑ source :
                Fin families.restriction.fineSelected.family.card,
              (input.retainedCellsForSourceAt
                multiplicity parentClass treeCleanup exactification
                  parentDegree core good
                  (families.restriction.fineSelected.embedding source)
                  coarseCell).card :=
        Finset.sum_image
          families.restriction.fineSelected.embedding.injective.injOn
      rw [families.restriction.fine_image_univ] at imageSum
      exact imageSum.symm
    _ =
        ∑ source : Fin fine.card,
          (input.retainedCellsForSourceAt
            multiplicity parentClass treeCleanup exactification
              parentDegree core good source coarseCell).card := by
      rw [Finset.sum_subset (Finset.subset_univ families.terminalFine)]
      intro source _sourceUniv sourceNotTerminal
      rw [input.retainedCellsForSourceAt_eq_empty_of_not_terminal
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families sourceNotTerminal coarseCell]
      simp
    _ = _ :=
      input.sum_retainedCellsForSourceAt_card
        multiplicity parentClass treeCleanup exactification
          parentDegree core good coarseCell

theorem activeFineCellsAt_selectedEdges_eq
    (coarseCell : WZ2PaperCellIndex) :
    exactification.incidence.activeFineCellsAt
        (core.ranges.selectedEdges good.sample) coarseCell =
      core.ranges.selectedFineCellsAt good.sample coarseCell := by
  ext fineCell
  constructor
  · intro fineCellMem
    have fineData :=
      (exactification.incidence.mem_activeFineCellsAt_iff
        (core.ranges.selectedEdges good.sample) coarseCell fineCell).mp
          fineCellMem
    rcases Finset.card_pos.mp fineData.1 with ⟨edge, edgeMem⟩
    have edgeData := Finset.mem_filter.mp edgeMem
    apply Finset.mem_image.mpr
    refine ⟨edge, Finset.mem_filter.mpr ⟨edgeData.1, ?_⟩, edgeData.2⟩
    unfold PureWZ2Prop62FourDegreeIncidenceData.edgeCoarseCell
    rw [edgeData.2]
    exact fineData.2
  · intro fineCellMem
    rcases Finset.mem_image.mp fineCellMem with
      ⟨edge, edgeMem, edgeFine⟩
    have edgeData := Finset.mem_filter.mp edgeMem
    apply
      (exactification.incidence.mem_activeFineCellsAt_iff
        (core.ranges.selectedEdges good.sample) coarseCell fineCell).mpr
    constructor
    · apply Finset.card_pos.mpr
      exact ⟨edge, Finset.mem_filter.mpr ⟨edgeData.1, edgeFine⟩⟩
    · unfold PureWZ2Prop62FourDegreeIncidenceData.edgeCoarseCell at edgeData
      rw [← edgeFine]
      exact edgeData.2

theorem selected_fineCellDegree_eq_terminal
    (coarseCell : core.ranges.ActiveCoarseCell)
    {fineCell : WZ2PaperCellIndex}
    (fineCellSelected :
      fineCell ∈
        core.ranges.selectedFineCellsAt good.sample coarseCell.1) :
    exactification.incidence.fineCellDegree
        (core.ranges.selectedEdges good.sample) fineCell =
      exactification.incidence.fineCellDegree
        core.ranges.terminalEdges fineCell := by
  have fineCellSample : fineCell ∈ (good.sample coarseCell).1 := by
    rw [← core.ranges.selectedFineCellsAt_eq_sample
      good.sample coarseCell]
    exact fineCellSelected
  have fineCellAvailable :=
    core.ranges.sample_subset_available
      good.sample coarseCell fineCellSample
  have fineCellCoarse :
      input.coarseCellOf fineCell = coarseCell.1 := by
    rw [← exactification.incidence_coarseCellOf_eq]
    exact
      (exactification.incidence.mem_activeFineCellsAt_iff
        core.ranges.terminalEdges coarseCell.1 fineCell).mp
          fineCellAvailable |>.2
  unfold PureWZ2Prop62FourDegreeIncidenceData.fineCellDegree
  apply congrArg Finset.card
  ext edge
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨edgeSelected, edgeFine⟩
    exact ⟨good.selectedEdges_subset edgeSelected, edgeFine⟩
  · rintro ⟨edgeTerminal, edgeFine⟩
    have edgeCoarse :
        exactification.incidence.edgeCoarseCell edge = coarseCell.1 := by
      unfold PureWZ2Prop62FourDegreeIncidenceData.edgeCoarseCell
      rw [exactification.incidence_coarseCellOf_eq, edgeFine, fineCellCoarse]
    have edgeCoarseActive :
        exactification.incidence.edgeCoarseCell edge ∈
          exactification.incidence.activeCoarseCells
            core.ranges.terminalEdges := by
      simpa [edgeCoarse] using coarseCell.2
    have coarseSubtypeEq :
        (⟨exactification.incidence.edgeCoarseCell edge, edgeCoarseActive⟩ :
          core.ranges.ActiveCoarseCell) = coarseCell :=
      Subtype.ext edgeCoarse
    refine ⟨core.ranges.selectedEdges_keep_all_incident_parents
      good.sample edgeTerminal ?_, edgeFine⟩
    rw [coarseSubtypeEq, edgeFine]
    exact fineCellSample

theorem selected_coarseDegree_band
    (coarseCell : core.ranges.ActiveCoarseCell) :
    input.fineCellThreshold
          multiplicity parentClass treeCleanup exactification bins A0 *
        core.ranges.commonFineCellCount ≤
      exactification.incidence.coarseDegree
        (core.ranges.selectedEdges good.sample) coarseCell.1 ∧
    exactification.incidence.coarseDegree
        (core.ranges.selectedEdges good.sample) coarseCell.1 ≤
      (2 * A0) *
        (input.fineCellThreshold
          multiplicity parentClass treeCleanup exactification bins A0 *
          core.ranges.commonFineCellCount) := by
  let selectedFine :=
    core.ranges.selectedFineCellsAt good.sample coarseCell.1
  have selectedCard :
      selectedFine.card = core.ranges.commonFineCellCount :=
    good.exact_fine_cell_count coarseCell
  have selectedDegreeSum :
      exactification.incidence.coarseDegree
          (core.ranges.selectedEdges good.sample) coarseCell.1 =
        ∑ fineCell ∈ selectedFine,
          exactification.incidence.fineCellDegree
            core.ranges.terminalEdges fineCell := by
    rw [exactification.incidence.coarseDegree_eq_sum_fineCellDegree]
    rw [input.activeFineCellsAt_selectedEdges_eq
      multiplicity parentClass treeCleanup exactification
        parentDegree core good coarseCell.1]
    apply Finset.sum_congr rfl
    intro fineCell fineCellMem
    exact input.selected_fineCellDegree_eq_terminal
      multiplicity parentClass treeCleanup exactification
        parentDegree core good coarseCell fineCellMem
  have pointwiseLower :
      ∀ fineCell ∈ selectedFine,
        input.fineCellThreshold
            multiplicity parentClass treeCleanup exactification bins A0 ≤
          exactification.incidence.fineCellDegree
            core.ranges.terminalEdges fineCell := by
    intro fineCell fineCellMem
    have fineCellSample : fineCell ∈ (good.sample coarseCell).1 := by
      rw [← core.ranges.selectedFineCellsAt_eq_sample
        good.sample coarseCell]
      exact fineCellMem
    have available :=
      core.ranges.sample_subset_available
        good.sample coarseCell fineCellSample
    have degreePos :=
      (exactification.incidence.mem_activeFineCellsAt_iff
        core.ranges.terminalEdges coarseCell.1 fineCell).mp available |>.1
    exact
      (PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.fineCell_range
        exactification.incidence core.ranges fineCell degreePos).1
  have pointwiseUpper :
      ∀ fineCell ∈ selectedFine,
        exactification.incidence.fineCellDegree
            core.ranges.terminalEdges fineCell ≤
          core.ranges.fineUpper := by
    intro fineCell fineCellMem
    have fineCellSample : fineCell ∈ (good.sample coarseCell).1 := by
      rw [← core.ranges.selectedFineCellsAt_eq_sample
        good.sample coarseCell]
      exact fineCellMem
    have available :=
      core.ranges.sample_subset_available
        good.sample coarseCell fineCellSample
    have degreePos :=
      (exactification.incidence.mem_activeFineCellsAt_iff
        core.ranges.terminalEdges coarseCell.1 fineCell).mp available |>.1
    exact
      (PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.fineCell_range
        exactification.incidence core.ranges fineCell degreePos).2.le
  have baseLeThreshold :
      2 ^ bins.fineCellBin.level ≤
        A0 *
          input.fineCellThreshold
            multiplicity parentClass treeCleanup exactification bins A0 := by
    simpa [PureWZ2Prop62PacketCellInput.fineCellThreshold] using
      (le_smul_ceilDiv
        (FourDegreeCoreAssemblyData.A0_pos core) :
        2 ^ bins.fineCellBin.level ≤
          A0 * (2 ^ bins.fineCellBin.level ⌈/⌉ A0))
  constructor
  · rw [selectedDegreeSum, ← selectedCard]
    simpa [Nat.mul_comm] using
      Finset.card_nsmul_le_sum selectedFine
        (exactification.incidence.fineCellDegree core.ranges.terminalEdges)
        (input.fineCellThreshold
          multiplicity parentClass treeCleanup exactification bins A0)
        pointwiseLower
  · rw [selectedDegreeSum, ← selectedCard]
    calc
      (∑ fineCell ∈ selectedFine,
          exactification.incidence.fineCellDegree
            core.ranges.terminalEdges fineCell) ≤
          core.ranges.fineUpper * selectedFine.card := by
        simpa [Nat.mul_comm] using
          Finset.sum_le_card_nsmul selectedFine
            (exactification.incidence.fineCellDegree
              core.ranges.terminalEdges)
            core.ranges.fineUpper pointwiseUpper
      _ ≤
          (2 * A0) *
            (input.fineCellThreshold
              multiplicity parentClass treeCleanup exactification bins A0 *
              selectedFine.card) := by
        unfold
          PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.fineUpper
        rw [pow_succ]
        nlinarith

theorem indexedCellMass_eq_source_sum
    (coarseCell : WZ2PaperCellIndex) :
    input.indexedCellMass
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families output coarseCell =
      ∑ source : Fin families.restriction.fineSelected.family.card,
        volume
          (output.fineShading.carrier source ∩
            wz1PaperGridCube rho coarseCell) :=
  rfl

/-- The actual source-indexed shaded mass in a coarse cell is exactly the
selected edge count there, with the exact multiplicity `muFine`. -/
theorem indexedCellMass_eq_coarseDegree
    (coarseCell : WZ2PaperCellIndex) :
    input.indexedCellMass
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families output coarseCell =
      ((output.muFine *
          exactification.incidence.coarseDegree
            (core.ranges.selectedEdges good.sample) coarseCell : ℕ) : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  rw [indexedCellMass]
  calc
    (∑ source : Fin families.restriction.fineSelected.family.card,
        volume
          (output.fineShading.carrier source ∩
            wz1PaperGridCube rho coarseCell)) =
        ∑ source : Fin families.restriction.fineSelected.family.card,
          ((input.retainedCellsForSourceAt
            multiplicity parentClass treeCleanup exactification
              parentDegree core good
              (families.restriction.fineSelected.embedding source)
              coarseCell).card : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
      apply Finset.sum_congr rfl
      intro source _sourceMem
      rw [output.fineShading_eq, TerminalFineShading.carrier_eq
        input multiplicity parentClass treeCleanup exactification
          core.ranges good families source]
      exact input.exactFineShading_carrier_inter_coarseCube_volume
        multiplicity parentClass treeCleanup exactification
          parentDegree core good
          (families.restriction.fineSelected.embedding source) coarseCell
    _ =
        ((∑ source : Fin families.restriction.fineSelected.family.card,
            (input.retainedCellsForSourceAt
              multiplicity parentClass treeCleanup exactification
                parentDegree core good
                (families.restriction.fineSelected.embedding source)
                coarseCell).card : ℕ) : ENNReal) *
          volume (wz1PaperGridCube delta (0, 0, 0)) := by
      rw [Nat.cast_sum, Finset.sum_mul]
    _ =
        ((output.muFine *
            exactification.incidence.coarseDegree
              (core.ranges.selectedEdges good.sample) coarseCell : ℕ) : ENNReal) *
          volume (wz1PaperGridCube delta (0, 0, 0)) := by
      rw [input.sum_terminal_retainedCellsForSourceAt_card
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families coarseCell, output.muFine_eq]

/-- The edge-side counterpart of `indexedCellMass`.  This is the literal
source--edge incidence count in one coarse cell, before the still-missing
carrier-to-edge local double-counting bridge is applied. -/
def indexedEdgeCellMass
    (coarseCell : WZ2PaperCellIndex) : ENNReal :=
  ∑ edge ∈
      (core.ranges.selectedEdges good.sample).filter fun edge =>
        exactification.incidence.edgeCoarseCell edge = coarseCell,
    (output.muFine : ENNReal) *
      volume (wz1PaperGridCube delta (0, 0, 0))

theorem indexedEdgeCellMass_eq
    (coarseCell : WZ2PaperCellIndex) :
    input.indexedEdgeCellMass
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families output coarseCell =
      ((output.muFine *
          exactification.incidence.coarseDegree
            (core.ranges.selectedEdges good.sample) coarseCell : ℕ) : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  rw [indexedEdgeCellMass]
  simp only [PureWZ2Prop62FourDegreeIncidenceData.coarseDegree]
  rw [Finset.sum_const]
  rw [Nat.cast_mul]
  ring

/-- The carrier-side and edge-side local masses agree exactly. -/
theorem indexedCellMass_eq_indexedEdgeCellMass
    (coarseCell : WZ2PaperCellIndex) :
    input.indexedCellMass
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families output coarseCell =
      input.indexedEdgeCellMass
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families output coarseCell := by
  rw [input.indexedCellMass_eq_coarseDegree
    multiplicity parentClass treeCleanup exactification
      parentDegree core good families output coarseCell]
  rw [input.indexedEdgeCellMass_eq
    multiplicity parentClass treeCleanup exactification
      parentDegree core good families output coarseCell]

theorem fineCellThreshold_pos
    (_core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup
          exactification parentDegree bins A0) :
    0 <
      input.fineCellThreshold
        multiplicity parentClass treeCleanup exactification bins A0 := by
  have basePos : 0 < 2 ^ bins.fineCellBin.level := pow_pos (by omega) _
  have baseLe :
      2 ^ bins.fineCellBin.level ≤
        A0 *
          input.fineCellThreshold
            multiplicity parentClass treeCleanup exactification bins A0 := by
    simpa [PureWZ2Prop62PacketCellInput.fineCellThreshold] using
      (le_smul_ceilDiv
        (FourDegreeCoreAssemblyData.A0_pos _core) :
        2 ^ bins.fineCellBin.level ≤
          A0 * (2 ^ bins.fineCellBin.level ⌈/⌉ A0))
  exact Nat.pos_of_mul_pos_left (basePos.trans_le baseLe)

/-- The lower endpoint used by `indexedCellMass_band` is strictly positive. -/
theorem indexedCellMass_bandBase_pos :
    0 <
      (((output.muFine *
        (input.fineCellThreshold
          multiplicity parentClass treeCleanup exactification bins A0 *
          core.ranges.commonFineCellCount) : ℕ) : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0))) := by
  apply ENNReal.mul_pos
  · have natPos :=
      Nat.mul_pos output.muFine_pos <|
        Nat.mul_pos
          (input.fineCellThreshold_pos
            multiplicity parentClass treeCleanup exactification
              parentDegree core)
          core.ranges.commonFineCellCount_pos
    exact_mod_cast Nat.ne_of_gt natPos
  · exact ne_of_gt <|
      wz1PaperGridCube_volume_pos input.delta_pos (0, 0, 0)

theorem indexedCellMass_bandBase_ne_zero :
    (((output.muFine *
      (input.fineCellThreshold
        multiplicity parentClass treeCleanup exactification bins A0 *
        core.ranges.commonFineCellCount) : ℕ) : ENNReal) *
      volume (wz1PaperGridCube delta (0, 0, 0))) ≠ 0 :=
  ne_of_gt <| input.indexedCellMass_bandBase_pos
    multiplicity parentClass treeCleanup exactification
      parentDegree core good families output

/-- The lower endpoint used by `indexedCellMass_band` is finite. -/
theorem indexedCellMass_bandBase_ne_top :
    (((output.muFine *
      (input.fineCellThreshold
        multiplicity parentClass treeCleanup exactification bins A0 *
        core.ranges.commonFineCellCount) : ℕ) : ENNReal) *
      volume (wz1PaperGridCube delta (0, 0, 0))) ≠ ⊤ := by
  exact ENNReal.mul_ne_top
    (ENNReal.natCast_ne_top _)
    (wz1PaperGridCube_volume_ne_top input.delta_pos (0, 0, 0))

/-- The honest upper-band factor is positive. -/
theorem indexedCellMass_bandFactor_pos :
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup
          exactification parentDegree bins A0) →
    0 < (2 * A0 : ENNReal) := by
  intro core
  apply ENNReal.mul_pos
  · norm_num
  · exact_mod_cast Nat.ne_of_gt
      (FourDegreeCoreAssemblyData.A0_pos core)

theorem indexedCellMass_bandFactor_ne_zero :
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup
          exactification parentDegree bins A0) →
    (2 * A0 : ENNReal) ≠ 0 :=
  fun core => ne_of_gt <| input.indexedCellMass_bandFactor_pos
    multiplicity parentClass treeCleanup exactification parentDegree core

/-- The honest upper-band factor is finite. -/
theorem indexedCellMass_bandFactor_ne_top :
    (2 * A0 : ENNReal) ≠ ⊤ := by
  exact ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top A0)

/-- Honest local incidence band on every active coarse cell.  The upper
factor is `2 * A0`: the factor `2` is the dyadic-bin width, while `A0` is
the unavoidable loss between the bin base and the peeling threshold. -/
theorem indexedCellMass_band
    (coarseCell : core.ranges.ActiveCoarseCell) :
    (((output.muFine *
        (input.fineCellThreshold
          multiplicity parentClass treeCleanup exactification bins A0 *
          core.ranges.commonFineCellCount) : ℕ) : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0)) ≤
      input.indexedCellMass
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families output coarseCell.1) ∧
    input.indexedCellMass
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families output coarseCell.1 ≤
      (2 * A0 : ENNReal) *
        (((output.muFine *
          (input.fineCellThreshold
            multiplicity parentClass treeCleanup exactification bins A0 *
            core.ranges.commonFineCellCount) : ℕ) : ENNReal) *
          volume (wz1PaperGridCube delta (0, 0, 0))) := by
  have degreeBand := input.selected_coarseDegree_band
    multiplicity parentClass treeCleanup exactification
      parentDegree core good coarseCell
  have lowerNat :
      output.muFine *
          (input.fineCellThreshold
            multiplicity parentClass treeCleanup exactification bins A0 *
            core.ranges.commonFineCellCount) ≤
        output.muFine *
          exactification.incidence.coarseDegree
            (core.ranges.selectedEdges good.sample) coarseCell.1 :=
    Nat.mul_le_mul_left output.muFine degreeBand.1
  have upperNat :
      output.muFine *
          exactification.incidence.coarseDegree
            (core.ranges.selectedEdges good.sample) coarseCell.1 ≤
        (2 * A0) *
          (output.muFine *
            (input.fineCellThreshold
              multiplicity parentClass treeCleanup exactification bins A0 *
              core.ranges.commonFineCellCount)) := by
    have multiplied := Nat.mul_le_mul_left output.muFine degreeBand.2
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using multiplied
  rw [input.indexedCellMass_eq_coarseDegree
    multiplicity parentClass treeCleanup exactification
      parentDegree core good families output coarseCell.1]
  constructor
  · gcongr
  · calc
      (((output.muFine *
          exactification.incidence.coarseDegree
            (core.ranges.selectedEdges good.sample) coarseCell.1 : ℕ) :
            ENNReal) *
          volume (wz1PaperGridCube delta (0, 0, 0))) ≤
          (((2 * A0) *
            (output.muFine *
              (input.fineCellThreshold
                multiplicity parentClass treeCleanup exactification bins A0 *
                core.ranges.commonFineCellCount)) : ℕ) : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
        gcongr
      _ =
          (2 * A0 : ENNReal) *
            (((output.muFine *
              (input.fineCellThreshold
                multiplicity parentClass treeCleanup exactification bins A0 *
                core.ranges.commonFineCellCount) : ℕ) : ENNReal) *
              volume (wz1PaperGridCube delta (0, 0, 0))) := by
        simp only [Nat.cast_mul]
        ring

/-- The direct four-degree coarse multiplicity is controlled by the fine-cell
base and the canonical common fine-cell count. -/
theorem muCoarse_le_A0_fineCellThreshold_commonFineCellCount :
    output.muCoarse ≤
      A0 *
        (input.fineCellThreshold
          multiplicity parentClass treeCleanup exactification bins A0 *
          core.ranges.commonFineCellCount) := by
  let fineBase : ℕ := 2 ^ bins.fineCellBin.level
  let coarseBase : ℕ := 2 ^ bins.coarseCellBin.level
  let parentCoarseBase : ℕ := 2 ^ bins.parentCoarseBin.level
  let fineThreshold : ℕ :=
    input.fineCellThreshold
      multiplicity parentClass treeCleanup exactification bins A0
  let coarseThreshold : ℕ :=
    input.coarseCellThreshold
      multiplicity parentClass treeCleanup exactification bins A0
  let W : ℕ := core.ranges.commonFineCellCount
  have fineBasePos : 0 < fineBase := by
    simp [fineBase]
  have parentCoarseBasePos : 0 < parentCoarseBase := by
    simp [parentCoarseBase]
  have fineBaseLe : fineBase ≤ A0 * fineThreshold := by
    simpa [fineBase, fineThreshold,
      PureWZ2Prop62PacketCellInput.fineCellThreshold] using
      (le_smul_ceilDiv core.A0_pos :
        2 ^ bins.fineCellBin.level ≤
          A0 * (2 ^ bins.fineCellBin.level ⌈/⌉ A0))
  have coarseBaseLe : coarseBase ≤ A0 * coarseThreshold := by
    simpa [coarseBase, coarseThreshold,
      PureWZ2Prop62PacketCellInput.coarseCellThreshold] using
      (le_smul_ceilDiv core.A0_pos :
        2 ^ bins.coarseCellBin.level ≤
          A0 * (2 ^ bins.coarseCellBin.level ⌈/⌉ A0))
  have coarseThresholdLe : coarseThreshold ≤ 2 * fineBase * W := by
    calc
      coarseThreshold ≤
          (2 * fineBase) * (coarseThreshold ⌈/⌉ (2 * fineBase)) :=
        le_smul_ceilDiv (show 0 < 2 * fineBase by omega)
      _ ≤ (2 * fineBase) * W := by
        apply Nat.mul_le_mul_left
        simpa [W, coarseThreshold, fineBase,
          PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.commonFineCellCount,
          PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.fineUpper,
          pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
          (le_max_right 1 (coarseThreshold ⌈/⌉ (2 * fineBase)))
  have numeratorLe : coarseBase ≤ 2 * A0 * fineBase * W := by
    calc
      coarseBase ≤ A0 * coarseThreshold := coarseBaseLe
      _ ≤ A0 * (2 * fineBase * W) := Nat.mul_le_mul_left A0 coarseThresholdLe
      _ = 2 * A0 * fineBase * W := by ring
  have denominatorPos : 0 < 2 * A0 * parentCoarseBase := by
    exact Nat.mul_pos (Nat.mul_pos (by omega) core.A0_pos)
      parentCoarseBasePos
  have quotientLe :
      coarseBase ⌈/⌉ (2 * A0 * parentCoarseBase) ≤
        A0 * (fineThreshold * W) := by
    apply (ceilDiv_le_iff_le_mul denominatorPos).mpr
    calc
      coarseBase ≤ 2 * A0 * fineBase * W := numeratorLe
      _ ≤ 2 * A0 * (A0 * fineThreshold) * W := by
        gcongr
      _ ≤ (2 * A0 * parentCoarseBase) *
          (A0 * (fineThreshold * W)) := by
        have parentCoarseBaseOne : 1 ≤ parentCoarseBase := parentCoarseBasePos
        calc
          2 * A0 * (A0 * fineThreshold) * W ≤
              parentCoarseBase * (2 * A0 * (A0 * fineThreshold) * W) :=
            calc
              2 * A0 * (A0 * fineThreshold) * W =
                  1 * (2 * A0 * (A0 * fineThreshold) * W) := by ring
              _ ≤ parentCoarseBase *
                  (2 * A0 * (A0 * fineThreshold) * W) :=
                Nat.mul_le_mul_right _ parentCoarseBaseOne
          _ = (2 * A0 * parentCoarseBase) *
              (A0 * (fineThreshold * W)) := by ring
  rw [output.muCoarse_eq]
  unfold FourDegreeCoreAssemblyData.terminalCoarseMultiplicity
  apply max_le
  · have rhsPos : 0 < A0 * (fineThreshold * W) := by
      have fineThresholdPos : 0 < fineThreshold := by
        by_contra fineThresholdNotPos
        have fineThresholdZero : fineThreshold = 0 := by omega
        have fineBaseZero : fineBase = 0 := by
          simpa [fineThresholdZero] using fineBaseLe
        omega
      have WPos : 0 < W := by
        exact core.ranges.commonFineCellCount_pos
      exact Nat.mul_pos core.A0_pos (Nat.mul_pos fineThresholdPos WPos)
    exact rhsPos
  · simpa [coarseBase, parentCoarseBase, fineThreshold, W, Nat.mul_assoc,
      FourDegreeCoreAssemblyData.terminalCoarseMultiplicityDenominator]
      using quotientLe

end PureWZ2Prop62PacketCellInput

/--
Any finite family of literal `rho`-cells whose union is contained in one
cropped paper tube has cardinality `O(rho⁻¹)`.  The hypotheses are phrased in
terms of an abstract selected carrier so downstream V4 code can instantiate
the result without introducing a dependency cycle.
-/
theorem paper_parent_selected_cells_card_mul_scale_le
    {rho : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (coarseShading : WZ1PaperTubeShading coarse)
    (cells : Finset WZ2PaperCellIndex)
    (selectedCarrier : Set Point3)
    (parent : Fin coarse.card)
    (hrho : 0 < rho)
    (rhoSmall : rho ≤ 1 / 24)
    (parentLine : WZ1PaperTubeInLineClass (coarse.tube parent))
    (selectedVolume :
      volume selectedCarrier =
        (cells.card : ENNReal) *
          volume (wz1PaperGridCube rho (0, 0, 0)))
    (selectedSubset :
      selectedCarrier ⊆ coarseShading.carrier parent) :
    (cells.card : ENNReal) * ENNReal.ofReal rho ≤
      55296 * Kakeya.deltaTubeVolume 1 := by
  let rhoENN : ENNReal := ENNReal.ofReal rho
  have rhoENNZero : rhoENN ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr hrho).ne'
  have rhoENNTop : rhoENN ≠ ⊤ := ENNReal.ofReal_ne_top
  have rhoSquareZero : rhoENN ^ 2 ≠ 0 := pow_ne_zero _ rhoENNZero
  have rhoSquareTop : rhoENN ^ 2 ≠ ⊤ := by
    exact ENNReal.pow_ne_top rhoENNTop
  have rhoCube :
      volume (wz1PaperGridCube rho (0, 0, 0)) = rhoENN ^ 3 := by
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_pow hrho.le 3
  have rhoPower :
      Kakeya.realRpowENN rho 2 = rhoENN ^ 2 := by
    simp [Kakeya.realRpowENN, rhoENN, ENNReal.ofReal_pow hrho.le]
  have volumeBound :
      (cells.card : ENNReal) * rhoENN ^ 3 ≤
        (55296 * Kakeya.deltaTubeVolume 1) * rhoENN ^ 2 := by
    calc
      (cells.card : ENNReal) * rhoENN ^ 3 =
          volume selectedCarrier := by
        rw [selectedVolume, rhoCube]
      _ ≤ volume (coarseShading.carrier parent) :=
        measure_mono selectedSubset
      _ ≤ volume (wz1PaperTubeCarrier (coarse.tube parent)) :=
        measure_mono (coarseShading.subset_body parent)
      _ ≤ (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN rho 2 :=
        (wz2PaperTubeCarrier_convex_and_volume_quadratic
          wz2_paper_tube_carrier_geometry hrho rhoSmall
          (coarse.tube parent) parentLine).2
      _ = (55296 * Kakeya.deltaTubeVolume 1) * rhoENN ^ 2 := by
        rw [rhoPower]
  apply
    (ENNReal.mul_le_mul_iff_right rhoSquareZero rhoSquareTop).mp
  calc
    rhoENN ^ 2 * ((cells.card : ENNReal) * rhoENN) =
        (cells.card : ENNReal) * rhoENN ^ 3 := by ring
    _ ≤ (55296 * Kakeya.deltaTubeVolume 1) * rhoENN ^ 2 :=
      volumeBound
    _ = rhoENN ^ 2 * (55296 * Kakeya.deltaTubeVolume 1) := by ring

end Kakeya.Assouad

end
