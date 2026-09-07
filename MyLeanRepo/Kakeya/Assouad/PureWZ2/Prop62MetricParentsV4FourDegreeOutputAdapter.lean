import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreeOutputCertificate
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4FiberCWAWeakening
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4PacketCellAdapter

/-!
# Proposition 6.2 V4 four-degree output adapter

This module transports the canonical four-degree producer to the frozen V4
packet-core record.  It does not perform another selection: the final
refinement and both terminal families are the producer's existing terminal
restriction, and every fiber certificate is reindexed from the corresponding
ambient metric fiber.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open MeasureTheory
open Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace MetricParentsV4PacketCellLocalInput

variable
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {metric :
      MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
          parentConstant fiberConstant}
    (localInput : MetricParentsV4PacketCellLocalInput metric)
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        metric.scaleData.coarse ambientConstant scaleWindow)
    {eta : ℝ}
    {packetDensityExponent : ℕ}
    (producer :
      localInput.toPacketCellInput.CanonicalFourDegreeProducerData
        (schedule := schedule) fiberConstant
        (Kakeya.realRpowENN delta
          ((packetDensityExponent : ℝ) * eta)))

private abbrev packetInput :=
  localInput.toPacketCellInput

private abbrev initial :=
  producer.initial

private abbrev core :=
  producer.core

private abbrev families :=
  producer.families

private abbrev canonical :=
  producer.output.output

private noncomputable def terminalRescaling :
    producer.families.TerminalPublicRescalingData
      localInput.toPacketCellInput producer.initial.multiplicity
      producer.initial.parentClass producer.initial.treeCleanup
      producer.initial.exactification producer.initial.parentDegree
      producer.core rho.2.2 (fiberConstant / 81000000) where
  ambient ambientParent _parentMem := by
    let ambientFiber :=
      Classical.choice
        (metric.scaleData.rescaledFiber ambientParent)
    exact
      (ambientFiber.weakenConstant le_rfl
        ambientFiber.cwa.2.1).rescalingInput

/-
private def finalRefinement :
    WZ1PaperRefinement metric.refinement.refined 50 where
  selected := producer.families.restriction.fineSelected
  refined := producer.output.output.fineShading
  subshading sourceIndex := by
    rw [producer.output.output.fineShading_eq]
    exact
      PureWZ2Prop62PacketCellInput.TerminalFineShading.subshading
        localInput.toPacketCellInput producer.initial.multiplicity
        producer.initial.parentClass producer.initial.treeCleanup
        producer.initial.exactification producer.core.ranges
        producer.output.good producer.families sourceIndex
  retained_mass := producer.output.output.retained_mass

private theorem parent_commutes
    (sourceIndex :
      Fin producer.families.restriction.fineSelected.family.card) :
    metric.scaleData.cover.parent
        (producer.families.restriction.fineSelected.embedding sourceIndex) =
      producer.families.restriction.coarseSelected.embedding
        (producer.families.restriction.section6Cover.toWZ1PaperTubeCover.parent
          sourceIndex) := by
  rw [metric.scaleData.cover_eq]
  symm
  apply metric.scaleData.section6Cover.toWZ1PaperTubeCover.parent_unique
  simpa only [
    producer.families.restriction.fineSelected.tube_eq,
    producer.families.restriction.coarseSelected.tube_eq
  ] using
    producer.families.restriction.section6Cover.toWZ1PaperTubeCover
      |>.parent_covers sourceIndex

private theorem complete_metric_fibers
    (oldSource : Fin metric.refinement.selected.family.card)
    (newParent :
      Fin producer.families.restriction.coarseSelected.family.card)
    (parentEq :
      metric.scaleData.cover.parent oldSource =
        producer.families.restriction.coarseSelected.embedding newParent) :
    ∃ newSource,
      producer.families.restriction.fineSelected.embedding newSource =
        oldSource := by
  have ambientParentEq :
      metric.scaleData.section6Cover.toWZ1PaperTubeCover.parent oldSource =
        producer.families.restriction.coarseSelected.embedding newParent := by
    rw [← metric.scaleData.cover_eq]
    exact parentEq
  have oldSourceTerminal : oldSource ∈ producer.families.terminalFine := by
    rw [producer.families.terminalFine_eq]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ oldSource, ?_⟩
    rw [ambientParentEq, ← producer.families.terminalParents_eq,
      ← producer.families.coarse_image_univ]
    exact Finset.mem_image.mpr
      ⟨newParent, Finset.mem_univ newParent, rfl⟩
  have oldSourceImage :
      oldSource ∈
        Finset.image
          producer.families.restriction.fineSelected.embedding
          Finset.univ := by
    rw [producer.families.restriction.fine_image_univ]
    exact oldSourceTerminal
  rcases Finset.mem_image.mp oldSourceImage with
    ⟨newSource, _newSourceUniv, sourceEq⟩
  exact ⟨newSource, sourceEq⟩

private def balanced :
    WZ1PaperBalancedCoverData
      producer.families.restriction.section6Cover.toWZ1PaperTubeCover
      producer.output.output.fineShading
      producer.output.output.coarseShading where
  point_compatibility sourceIndex point pointMem :=
    producer.output.output.balanced.point_compatibility
      sourceIndex
      (producer.families.restriction.section6Cover.toWZ1PaperTubeCover.parent
        sourceIndex)
      (producer.families.restriction.section6Cover.toWZ1PaperTubeCover
        |>.parent_covers sourceIndex)
      point pointMem
  coarse_cubical := producer.output.output.balanced.coarse_cubical
  activeCells :=
    producer.initial.exactification.incidence.activeCoarseCells
      producer.core.ranges.terminalEdges
  coarse_union_eq := by
    rw [producer.output.output.coarseShading_eq]
    exact
      PureWZ2Prop62PacketCellInput.FrozenCoarseShading.terminal_union_eq_activeCoarseCells
          localInput.toPacketCellInput producer.initial.multiplicity
          producer.initial.parentClass producer.initial.treeCleanup
          producer.initial.exactification producer.core.ranges
          producer.families
  cellMass :=
    (producer.output.output.W : ENNReal) *
      volume (wz1PaperGridCube delta (0, 0, 0))
  cellMass_pos :=
    ENNReal.mul_pos
      (by exact_mod_cast producer.output.output.W_pos.ne')
      (wz1PaperGridCube_volume_pos localInput.delta_pos _).ne'
  cellMass_ne_top :=
    ENNReal.mul_ne_top
      (by simp)
      (wz1PaperGridCube_volume_ne_top localInput.delta_pos _)
  fine_cell_mass := by
    intro coarseCell coarseCellMem
    exact producer.output.output.exact_balance coarseCell coarseCellMem

private def packetCells :
    Finset
      (Fin producer.families.restriction.coarseSelected.family.card ×
        CellIndex) :=
  ((Finset.univ :
      Finset
        (Fin producer.families.restriction.coarseSelected.family.card)).product
      (wz1PaperActiveCells
        (localInput.finalRefinement schedule producer).refined localInput.delta_pos)).filter
    fun edge =>
      ((wz2PaperFullFiberIndices
          (localInput.finalRefinement schedule producer).selected.family
          producer.families.restriction.coarseSelected.family edge.1).filter
        fun sourceIndex =>
          wz1PaperGridCube delta edge.2 ⊆
            (localInput.finalRefinement schedule producer).refined.carrier
              sourceIndex).Nonempty

private theorem exists_selectedEdge_of_packetCell
    {parent :
      Fin producer.families.restriction.coarseSelected.family.card}
    {cell : CellIndex}
    {sourceIndex :
      Fin producer.families.restriction.fineSelected.family.card}
    (sourceFiber :
      sourceIndex ∈
        wz2PaperFullFiberIndices
          producer.families.restriction.fineSelected.family
          producer.families.restriction.coarseSelected.family parent)
    (cellSubset :
      wz1PaperGridCube delta cell ⊆
        producer.output.output.fineShading.carrier sourceIndex) :
    ∃ edge :
        producer.initial.exactification.incidence.Edge,
      edge ∈
          producer.core.ranges.selectedEdges
            producer.output.good.sample ∧
        producer.initial.exactification.incidence.edgeParent edge =
          producer.families.restriction.coarseSelected.embedding parent ∧
        producer.initial.exactification.incidence.edgeFineCell edge = cell := by
  let point := cellCorner delta cell
  have pointCell : point ∈ wz1PaperGridCube delta cell :=
    cellCorner_mem_gridCube localInput.delta_pos cell
  have pointTerminal :
      point ∈ producer.output.output.fineShading.carrier sourceIndex :=
    cellSubset pointCell
  have pointAmbient :
      point ∈
        (localInput.toPacketCellInput.exactFineShading
          producer.initial.multiplicity producer.initial.parentClass
          producer.initial.treeCleanup producer.initial.exactification
          producer.core.ranges producer.output.good).carrier
            (producer.families.restriction.fineSelected.embedding
              sourceIndex) := by
    rw [producer.output.output.fineShading_eq] at pointTerminal
    exact pointTerminal
  rw [PureWZ2Prop62PacketCellInput.ExactFineShading.carrier_eq
    localInput.toPacketCellInput producer.initial.multiplicity
    producer.initial.parentClass producer.initial.treeCleanup
    producer.initial.exactification producer.core.ranges
    producer.output.good] at pointAmbient
  rcases Set.mem_iUnion₂.mp pointAmbient with
    ⟨otherCell, otherCellMem, pointOtherCell⟩
  rcases Finset.mem_image.mp otherCellMem with
    ⟨edge, edgeMem, edgeFine⟩
  have edgeSelected :
      edge ∈
        producer.core.ranges.selectedEdges producer.output.good.sample :=
    (Finset.mem_filter.mp edgeMem).1
  have sourceSelected :
      localInput.toPacketCellInput.sourceSelectedOnEdge
        producer.initial.multiplicity producer.initial.parentClass
        producer.initial.treeCleanup producer.initial.exactification
        (producer.families.restriction.fineSelected.embedding sourceIndex)
        edge :=
    (Finset.mem_filter.mp edgeMem).2
  have ambientFiber :
      producer.families.restriction.fineSelected.embedding sourceIndex ∈
        wz2PaperFullFiberIndices
          metric.refinement.selected.family metric.scaleData.coarse
          (producer.families.restriction.coarseSelected.embedding parent) := by
    have sourceImage :
        producer.families.restriction.fineSelected.embedding sourceIndex ∈
          Finset.image
            producer.families.restriction.fineSelected.embedding
            (wz2PaperFullFiberIndices
              producer.families.restriction.fineSelected.family
              producer.families.restriction.coarseSelected.family parent) :=
      Finset.mem_image.mpr ⟨sourceIndex, sourceFiber, rfl⟩
    rw [producer.families.fine_complete parent] at sourceImage
    exact sourceImage
  have edgeParent :
      producer.initial.exactification.incidence.edgeParent edge =
        producer.families.restriction.coarseSelected.embedding parent :=
    PureWZ2Prop62PacketCellInput.ExactFineShading.sourceSelectedOnEdge_parent_eq
        localInput.toPacketCellInput producer.initial.multiplicity
        producer.initial.parentClass producer.initial.treeCleanup
        producer.initial.exactification ambientFiber sourceSelected
  have cellEq : otherCell = cell := by
    have otherIndex :
        wz1PaperGridIndex delta point = otherCell :=
      (mem_wz1PaperGridCube delta otherCell point).mp pointOtherCell
    have ownIndex :
        wz1PaperGridIndex delta point = cell :=
      (mem_wz1PaperGridCube delta cell point).mp pointCell
    exact otherIndex.symm.trans ownIndex
  exact
    ⟨edge, edgeSelected, edgeParent, edgeFine.trans cellEq⟩

private theorem packetCells_nonempty :
    (localInput.packetCells schedule producer).Nonempty := by
  have selectedEdgesNonempty :
      producer.core.ranges.selectedEdges producer.output.good.sample
        |>.Nonempty := by
    let terminalEdge := Classical.choose producer.core.core_nonempty
    have terminalEdgeMem : terminalEdge ∈ producer.core.ranges.terminalEdges := by
      change terminalEdge ∈ producer.core.ranges.peeling.core
      rw [producer.core.ranges_peeling_eq]
      exact Classical.choose_spec producer.core.core_nonempty
    let coarseActive :
        producer.core.ranges.ActiveCoarseCell :=
      ⟨producer.initial.exactification.incidence.edgeCoarseCell terminalEdge,
        by
          rw [producer.initial.exactification.incidence.mem_activeCoarseCells_iff]
          exact Finset.card_pos.mpr
            ⟨terminalEdge,
              Finset.mem_filter.mpr ⟨terminalEdgeMem, rfl⟩⟩⟩
    have selectedCellNonempty :
        (producer.output.good.sample coarseActive).1.Nonempty := by
      apply Finset.card_pos.mp
      rw [producer.core.ranges.sample_card producer.output.good.sample
        coarseActive]
      exact producer.core.ranges.commonFineCellCount_pos
    rcases selectedCellNonempty with ⟨fineCell, fineCellMem⟩
    have available :=
      producer.core.ranges.sample_subset_available
        producer.output.good.sample coarseActive fineCellMem
    rcases Finset.mem_image.mp (Finset.mem_filter.mp available).1 with
      ⟨edge, edgeMem, edgeFine⟩
    have edgeCoarse :
        producer.initial.exactification.incidence.edgeCoarseCell edge =
          coarseActive.1 := by
      unfold PureWZ2Prop62FourDegreeIncidenceData.edgeCoarseCell
      rw [edgeFine]
      exact (Finset.mem_filter.mp available).2
    have edgeCoarseActive :
        producer.initial.exactification.incidence.edgeCoarseCell edge ∈
          producer.initial.exactification.incidence.activeCoarseCells
            producer.core.ranges.terminalEdges := by
      simpa [edgeCoarse] using coarseActive.2
    have coarseActiveEq :
        (⟨producer.initial.exactification.incidence.edgeCoarseCell edge,
          edgeCoarseActive⟩ : producer.core.ranges.ActiveCoarseCell) =
            coarseActive :=
      Subtype.ext edgeCoarse
    exact
      ⟨edge,
        producer.core.ranges.selectedEdges_keep_all_incident_parents
          producer.output.good.sample edgeMem <| by
            rw [coarseActiveEq]
            simpa [edgeFine] using fineCellMem⟩
  rcases selectedEdgesNonempty with ⟨edge, edgeSelected⟩
  rcases
      producer.output.output.exact_fine edge edgeSelected
    with ⟨parent, edgeParent, sourcesCard⟩
  have sourcesNonempty :
      (PureWZ2Prop62PacketCellInput.TerminalFineShading.terminalPacketCellSources
        localInput.toPacketCellInput producer.initial.multiplicity
        producer.initial.parentClass producer.initial.treeCleanup
        producer.initial.exactification producer.initial.parentDegree
        producer.core producer.output.good producer.families parent edge
      ).Nonempty := by
    apply Finset.card_pos.mp
    rw [sourcesCard]
    exact producer.output.output.muFine_pos
  rcases sourcesNonempty with ⟨sourceIndex, sourceMem⟩
  refine ⟨(parent,
    producer.initial.exactification.incidence.edgeFineCell edge), ?_⟩
  unfold packetCells
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ parent, ?_⟩, ?_⟩
  · rw [mem_wz1PaperActiveCells]
    constructor
    · have edgePoolMem :
          edge.1 ∈ producer.initial.exactification.incidence.edgePool :=
        edge.2
      have referenceEdgeMem :
          edge.1 ∈
            localInput.toPacketCellInput.referencePairs
              producer.initial.multiplicity producer.initial.parentClass
              producer.initial.treeCleanup := by
        rw [← producer.initial.exactification.incidence_edgePool_eq]
        exact edgePoolMem
      have referenceMem :=
        (localInput.toPacketCellInput.mem_referencePairs_iff
          producer.initial.multiplicity producer.initial.parentClass
          producer.initial.treeCleanup edge.1).mp referenceEdgeMem
      have selectedMem := referenceMem.1
      have positiveMem :=
        producer.initial.multiplicity.selectedPairs_subset selectedMem
      have fineCellMem :=
        (localInput.toPacketCellInput.mem_positivePairs_iff edge.1).mp positiveMem |>.1
      have originalActive :
          producer.initial.exactification.incidence.edgeFineCell edge ∈
            wz1PaperActiveCells metric.refinement.refined
              localInput.delta_pos := by
        rw [← localInput.toPacketCellInput.fineCells_eq]
        simpa [PureWZ2Prop62FourDegreeIncidenceData.edgeFineCell] using
          fineCellMem
      exact
        (mem_wz1PaperActiveCells metric.refinement.refined
          localInput.delta_pos _).mp originalActive |>.1
    · let point :=
        cellCorner delta
          (producer.initial.exactification.incidence.edgeFineCell edge)
      refine ⟨point, ?_, cellCorner_mem_gridCube localInput.delta_pos _⟩
      refine ⟨sourceIndex, ?_⟩
      change point ∈ producer.output.output.fineShading.carrier sourceIndex
      rw [producer.output.output.fineShading_eq]
      exact
        (Finset.mem_filter.mp sourceMem).2
          (cellCorner_mem_gridCube localInput.delta_pos _)
  · change
      (wz2PaperFullFiberIndices
          producer.families.restriction.fineSelected.family
          producer.families.restriction.coarseSelected.family parent).filter
          (fun sourceIndex =>
            wz1PaperGridCube delta
                (producer.initial.exactification.incidence.edgeFineCell edge) ⊆
              producer.output.output.fineShading.carrier sourceIndex)
        |>.Nonempty
    refine ⟨sourceIndex, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact (Finset.mem_filter.mp sourceMem).1
    · rw [producer.output.output.fineShading_eq]
      exact (Finset.mem_filter.mp sourceMem).2

private noncomputable def reindexedRescaledFiberCWA
    (parent :
      Fin producer.families.restriction.coarseSelected.family.card)
    (outputFiberConstant : ENNReal)
    (fiberConstantLe : fiberConstant ≤ outputFiberConstant)
    (outputFiberConstantFinite : outputFiberConstant ≠ ⊤) :
    RescaledMetricFiberCWAData
      producer.families.restriction.section6Cover parent metric.rho_pos
      outputFiberConstant := by
  let terminalData :
      producer.families.TerminalPublicRescalingData
        localInput.toPacketCellInput producer.initial.multiplicity
        producer.initial.parentClass producer.initial.treeCleanup
        producer.initial.exactification producer.initial.parentDegree
        producer.core rho.2.2 (fiberConstant / 81000000) :=
    {
      ambient := fun ambientParent _parentMem => by
        let ambientFiber :=
          Classical.choice
            (metric.scaleData.rescaledFiber ambientParent)
        exact
          (ambientFiber.weakenConstant le_rfl
            ambientFiber.cwa.2.1).rescalingInput
    }
  let reindex :=
    terminalData.reindexData
      localInput.toPacketCellInput producer.initial.multiplicity
      producer.initial.parentClass producer.initial.treeCleanup
      producer.initial.exactification producer.initial.parentDegree
      producer.core producer.families parent
  let terminalFiber :=
    producer.families.terminalFiber
      localInput.toPacketCellInput producer.initial.multiplicity
      producer.initial.parentClass producer.initial.treeCleanup
      producer.initial.exactification producer.initial.parentDegree
      producer.core parent
  let sourceIndices :=
    wz2PaperFullFiberIndices
      producer.families.restriction.fineSelected.family
      producer.families.restriction.coarseSelected.family parent
  let terminalEnum := sourceIndices.orderIsoOfFin rfl
  let sourceEquiv :
      Fin reindex.input.sourceFamily.card ≃ sourceIndices :=
    reindex.indexEquiv.symm.trans terminalEnum.toEquiv
  have sourceEquivVal :
      ∀ index,
        (sourceEquiv index).1 =
          terminalFiber.embedding (reindex.indexEquiv.symm index) := by
    intro index
    rfl
  have sourceTubeEq :
      ∀ index,
        reindex.input.sourceFamily.tube index =
          producer.families.restriction.fineSelected.family.tube
            (sourceEquiv index).1 := by
    intro index
    let terminalIndex := reindex.indexEquiv.symm index
    have tubeEq := reindex.tube_eq terminalIndex
    have indexEq : reindex.indexEquiv terminalIndex = index :=
      reindex.indexEquiv.apply_symm_apply index
    rw [indexEq] at tubeEq
    calc
      reindex.input.sourceFamily.tube index =
          terminalFiber.family.tube terminalIndex :=
        tubeEq.symm
      _ =
          producer.families.restriction.fineSelected.family.tube
            (terminalFiber.embedding terminalIndex) :=
        terminalFiber.tube_eq terminalIndex
      _ =
          producer.families.restriction.fineSelected.family.tube
            (sourceEquiv index).1 := by
        rw [sourceEquivVal]
  let fiberInput :
      PureWZ2Prop62MetricFiberRescalingInput
        producer.families.restriction.section6Cover parent
        (fiberConstant / 81000000) :=
    PureWZ2Prop62MetricFiberRescalingInput.reanchor
      producer.families.restriction.section6Cover parent
      reindex.input reindex.anchor_eq sourceIndices rfl
      (by
        rcases producer.families.restriction.section6Cover.parent_hit parent with
          ⟨sourceIndex, sourceCovered⟩
        exact
          ⟨sourceIndex,
            (mem_wz2PaperFullFiberIndices_iff parent sourceIndex).mpr
              sourceCovered⟩)
      sourceEquiv sourceTubeEq
  have constantEq :
      fiberConstant =
        (81000000 : ENNReal) * (fiberConstant / 81000000) :=
    (ENNReal.mul_div_cancel (by norm_num) (by norm_num)).symm
  let base :
      RescaledMetricFiberCWAData
        producer.families.restriction.section6Cover parent metric.rho_pos
        ((81000000 : ENNReal) * (fiberConstant / 81000000)) :=
    {
      sourceConstant := fiberConstant / 81000000
      rescalingInput := fiberInput
      familyData := fiberInput.literal
      familyData_eq := rfl
      rescalingCertificate := fiberInput.certificate
      rescalingCertificate_eq := HEq.rfl
      constant_eq := rfl
      cwa := fiberInput.publicPureCWA
    }
  have outputFinite : WZ2PaperFiniteErrorConstant outputFiberConstant :=
    ⟨base.cwa.2.1.1.trans
        (constantEq.ge.trans fiberConstantLe),
      outputFiberConstantFinite⟩
  exact
    base.weakenConstant
      (constantEq.ge.trans fiberConstantLe) outputFinite

/--
The canonical four-degree producer, re-expressed in the frozen V4 output
record.  The two inequalities only weaken the already produced nearby-CWA
constants; no family, packet core, or balancing sample is selected again.
-/
private noncomputable def fourDegreePacketCoreData_of_canonicalProducer_direct
    (cwaLossExponent : ℕ)
    (parentConstantLe :
      producer.output.output.parentConstant ≤
        Kakeya.realRpowENN delta
          (-(cwaLossExponent : ℝ) * eta))
    (fiberConstantLe :
      fiberConstant ≤
        Kakeya.realRpowENN delta
          (-(cwaLossExponent : ℝ) * eta)) :
    FourDegreePacketCoreData
      (eta := eta)
      (packetDensityExponent := packetDensityExponent)
      localInput.delta_pos metric
      (Kakeya.realRpowENN delta
        (-(cwaLossExponent : ℝ) * eta))
      (Kakeya.realRpowENN delta
        (-(cwaLossExponent : ℝ) * eta)) := by
  let outputConstant :=
    Kakeya.realRpowENN delta
      (-(cwaLossExponent : ℝ) * eta)
  have outputConstantFinite : outputConstant ≠ ⊤ := by
    simp [outputConstant, Kakeya.realRpowENN]
  let refinement := localInput.finalRefinement schedule producer
  let publicBalanced := localInput.balanced schedule producer
  let packets := localInput.packetCells schedule producer
  exact
    {
      refinement := refinement
      refined_cubical := by
        change
          WZ1PaperIsCubicalShading
            producer.output.output.fineShading
        rw [producer.output.output.fineShading_eq]
        exact
          PureWZ2Prop62PacketCellInput.TerminalFineShading.cubical
            localInput.toPacketCellInput producer.initial.multiplicity
            producer.initial.parentClass producer.initial.treeCleanup
            producer.initial.exactification producer.core.ranges
            producer.output.good producer.families
      coarse := producer.families.restriction.coarseSelected
      cover := producer.families.restriction.section6Cover
      parent_commutes :=
        localInput.parent_commutes schedule producer
      complete_metric_fibers :=
        localInput.complete_metric_fibers schedule producer
      refined_nonempty := by
        change
          producer.families.restriction.fineSelected.family.Nonempty
        rw [producer.families.restriction.fineSelected_eq]
        exact producer.families.terminalFine_nonempty.card_pos
      coarseShading := producer.output.output.coarseShading
      balanced := publicBalanced
      muFine := producer.output.output.muFine
      muCoarse := producer.output.output.muCoarse
      W := producer.output.output.W
      fiberFloor := producer.output.output.fiberFloor
      muFine_pos := producer.output.output.muFine_pos
      muCoarse_pos := producer.output.output.muCoarse_pos
      W_pos := producer.output.output.W_pos
      fiberFloor_pos := producer.output.output.fiberFloor_pos
      regularity := producer.output.output.coarseLoss
      regularity_pos := by
        rw [producer.output.output.coarseLoss_eq]
        exact Nat.mul_pos (by norm_num) (pow_pos producer.core.A0_pos 2)
      packetCells := packets
      packetCells_nonempty :=
        localInput.packetCells_nonempty schedule producer
      packetCells_eq := rfl
      activeFineCells := packets.image Prod.snd
      active_fine_cells_eq := rfl
      activeCoarseCells := publicBalanced.activeCells
      active_coarse_cells_eq := rfl
      active_coarse_cells_nonempty := by
        rcases producer.core.core_nonempty with ⟨edge, edgeMem⟩
        refine
          ⟨producer.initial.exactification.incidence.edgeCoarseCell edge, ?_⟩
        change
          producer.initial.exactification.incidence.edgeCoarseCell edge ∈
            producer.initial.exactification.incidence.activeCoarseCells
              producer.core.ranges.terminalEdges
        apply Finset.mem_image.mpr
        refine ⟨edge, ?_, rfl⟩
        change edge ∈ producer.core.ranges.peeling.core
        rw [producer.core.ranges_peeling_eq]
        exact edgeMem
      coarseOfFine := localInput.toPacketCellInput.coarseCellOf
      packet_coarse_support := by
        intro edge edgeMem
        have packetData := Finset.mem_filter.mp edgeMem
        have edgeProduct := Finset.mem_product.mp packetData.1
        rcases packetData.2 with ⟨sourceIndex, sourceMem⟩
        have sourceData := Finset.mem_filter.mp sourceMem
        have wholeOriginal :
            wz1PaperGridCube delta edge.2 ⊆
              metric.refinement.refined.carrier
                (producer.families.restriction.fineSelected.embedding
                  sourceIndex) := by
          intro point pointMem
          exact
            (localInput.finalRefinement schedule producer).subshading
              sourceIndex (sourceData.2 pointMem)
        have originalActive :
            edge.2 ∈
              wz1PaperActiveCells metric.refinement.refined
                localInput.delta_pos := by
          have finalActive :=
            (mem_wz1PaperActiveCells
              (localInput.finalRefinement schedule producer).refined
              localInput.delta_pos edge.2).mp edgeProduct.2
          rw [mem_wz1PaperActiveCells]
          refine ⟨finalActive.1, ?_⟩
          let point := cellCorner delta edge.2
          exact
            ⟨point,
              ⟨producer.families.restriction.fineSelected.embedding
                  sourceIndex,
                wholeOriginal
                  (cellCorner_mem_gridCube localInput.delta_pos edge.2)⟩,
              cellCorner_mem_gridCube localInput.delta_pos edge.2⟩
        have ambientFiber :
            producer.families.restriction.fineSelected.embedding sourceIndex ∈
              wz2PaperFullFiberIndices
                metric.refinement.selected.family metric.scaleData.coarse
                (producer.families.restriction.coarseSelected.embedding
                  edge.1) := by
          have sourceImage :
              producer.families.restriction.fineSelected.embedding
                    sourceIndex ∈
                Finset.image
                  producer.families.restriction.fineSelected.embedding
                  (wz2PaperFullFiberIndices
                    producer.families.restriction.fineSelected.family
                    producer.families.restriction.coarseSelected.family
                    edge.1) :=
            Finset.mem_image.mpr ⟨sourceIndex, sourceData.1, rfl⟩
          rw [producer.families.fine_complete edge.1] at sourceImage
          exact sourceImage
        rcases
            localInput.exists_selectedEdge_of_packetCell schedule producer
              sourceData.1 sourceData.2
          with ⟨selectedEdge, selectedEdgeMem, _parentEq, fineCellEq⟩
        have selectedEdgeTerminal :=
          producer.output.good.selectedEdges_subset selectedEdgeMem
        constructor
        · change
            localInput.toPacketCellInput.coarseCellOf edge.2 ∈
              producer.initial.exactification.incidence.activeCoarseCells
                producer.core.ranges.terminalEdges
          apply Finset.mem_image.mpr
          refine ⟨selectedEdge, selectedEdgeTerminal, ?_⟩
          unfold
            PureWZ2Prop62FourDegreeIncidenceData.edgeCoarseCell
          rw [producer.initial.exactification.incidence_coarseCellOf_eq,
            fineCellEq]
        · exact
            ⟨localInput.toPacketCellInput.fine_cell_containment
                edge.2 originalActive,
              by
                rw [
                  producer.families.restriction.coarseSelected.tube_eq
                ]
                exact
                  localInput.toPacketCellInput.parent_cell_containment
                    (producer.families.restriction.coarseSelected.embedding
                      edge.1)
                    edge.2
                    (producer.families.restriction.fineSelected.embedding
                      sourceIndex)
                    originalActive ambientFiber wholeOriginal⟩
      exact_fine_multiplicity := by
        intro edge edgeMem
        rcases (Finset.mem_filter.mp edgeMem).2 with
          ⟨sourceIndex, sourceMem⟩
        have sourceData := Finset.mem_filter.mp sourceMem
        rcases
            localInput.exists_selectedEdge_of_packetCell schedule producer
              sourceData.1 sourceData.2
          with ⟨selectedEdge, selectedEdgeMem, edgeParent, fineCellEq⟩
        rcases
            producer.output.output.exact_fine selectedEdge selectedEdgeMem
          with ⟨selectedParent, selectedParentEq, cardEq⟩
        have parentEq : selectedParent = edge.1 := by
          apply producer.families.restriction.coarseSelected.embedding.injective
          exact selectedParentEq.symm.trans edgeParent
        subst selectedParent
        change
          ((wz2PaperFullFiberIndices
              producer.families.restriction.fineSelected.family
              producer.families.restriction.coarseSelected.family edge.1).filter
            fun sourceIndex =>
              wz1PaperGridCube delta edge.2 ⊆
                producer.output.output.fineShading.carrier sourceIndex).card =
            producer.output.output.muFine
        rw [← fineCellEq, producer.output.output.fineShading_eq]
        exact cardEq
      balanced_cell_mass := rfl
      coarse_multiplicity := by
        intro cell cellMem
        let activeCell : producer.core.ranges.ActiveCoarseCell :=
          ⟨cell, by
            change
              cell ∈
                producer.initial.exactification.incidence.activeCoarseCells
                  producer.core.ranges.terminalEdges
            exact cellMem⟩
        have band :=
          producer.output.output.coarse_multiplicity activeCell
        rw [producer.output.output.coarseShading_eq]
        change
          producer.output.output.muCoarse ≤
              (PureWZ2Prop62PacketCellInput.FrozenCoarseShading.terminalParentsAtCoarseCell
                localInput.toPacketCellInput producer.initial.multiplicity
                producer.initial.parentClass producer.initial.treeCleanup
                producer.initial.exactification producer.initial.parentDegree
                producer.core producer.families cell).card ∧
            (PureWZ2Prop62PacketCellInput.FrozenCoarseShading.terminalParentsAtCoarseCell
                localInput.toPacketCellInput producer.initial.multiplicity
                producer.initial.parentClass producer.initial.treeCleanup
                producer.initial.exactification producer.initial.parentDegree
                producer.core producer.families cell).card ≤
              producer.output.output.coarseLoss *
                producer.output.output.muCoarse
        simpa only [activeCell] using band
      fiber_cardinality := by
        intro parent
        change
          (producer.output.output.fiberFloor : ENNReal) ≤
                ((wz2PaperFullFiberIndices
                  producer.families.restriction.fineSelected.family
                  producer.families.restriction.coarseSelected.family
                  parent).card : ENNReal) ∧
            ((wz2PaperFullFiberIndices
                  producer.families.restriction.fineSelected.family
                  producer.families.restriction.coarseSelected.family
                  parent).card : ENNReal) <
              2 * (producer.output.output.fiberFloor : ENNReal)
        constructor
        · exact_mod_cast
            (producer.output.output.fiber_cardinality parent).1
        · exact_mod_cast
            (producer.output.output.fiber_cardinality parent).2
      parent_cwa :=
        producer.output.output.parent_cwa.mono
          parentConstantLe outputConstantFinite
      rescaled_fiber_cwa := by
        intro parent
        have outputFinite :
            WZ2PaperFiniteErrorConstant outputConstant :=
          ⟨producer.output.output.parent_cwa.2.1.1.trans parentConstantLe,
            outputConstantFinite⟩
        exact
          ⟨localInput.reindexedRescaledFiberCWA schedule producer parent
            outputConstant fiberConstantLe outputConstantFinite⟩
      packet_density := by
        intro parent
        have density := producer.output.output.packet_density parent
        change
          Kakeya.realRpowENN delta
                ((packetDensityExponent : ℝ) * eta) *
                (producer.output.output.fiberFloor : ENNReal) *
                Kakeya.realRpowENN delta 2 ≤
            (restrictPaperShading
              (wz2PaperFullFiberSubfamily
                producer.families.restriction.fineSelected.family
                producer.families.restriction.coarseSelected.family parent)
              producer.output.output.fineShading).mass
        unfold wz2PaperFullFiberSubfamily
        rw [restrictPaperShading_fromFinset_mass]
        rw [producer.output.output.fineShading_eq]
        exact density
      total_mass_retention := producer.output.output.retained_mass
    }
-/

/--
Package the neutral canonical four-degree certificate as the frozen V4
packet-core output.  This adapter adds only the V4 metric-cover equality and
the frozen public rescaling wrapper.
-/
noncomputable def fourDegreePacketCoreData_of_canonicalProducer
    (cwaLossExponent : ℕ)
    (parentConstantLe :
      producer.output.output.parentConstant ≤
        Kakeya.realRpowENN delta
          (-(cwaLossExponent : ℝ) * eta))
    (fiberConstantLe :
      fiberConstant ≤
        Kakeya.realRpowENN delta
          (-(cwaLossExponent : ℝ) * eta)) :
    FourDegreePacketCoreData
      (eta := eta)
      (packetDensityExponent := packetDensityExponent)
      localInput.delta_pos metric
      (Kakeya.realRpowENN delta
        (-(cwaLossExponent : ℝ) * eta))
      (Kakeya.realRpowENN delta
        (-(cwaLossExponent : ℝ) * eta)) := by
  let outputConstant :=
    Kakeya.realRpowENN delta
      (-(cwaLossExponent : ℝ) * eta)
  have outputConstantFinite : outputConstant ≠ ⊤ := by
    simp [outputConstant, Kakeya.realRpowENN]
  let certificate :=
    localInput.toPacketCellInput.fourDegreeOutputCertificate_of_canonicalProducer
      schedule producer outputConstantFinite parentConstantLe
      (localInput.terminalRescaling schedule producer)
  exact
    {
      refinement := certificate.refinement
      refined_cubical := certificate.refined_cubical
      coarse := certificate.coarse
      cover := certificate.cover
      parent_commutes := by
        intro sourceIndex
        rw [metric.scaleData.cover_eq]
        exact certificate.parent_commutes sourceIndex
      complete_metric_fibers := by
        intro oldSource newParent parentEq
        apply certificate.complete_fibers oldSource newParent
        rw [← metric.scaleData.cover_eq]
        exact parentEq
      refined_nonempty := certificate.refined_nonempty
      coarseShading := certificate.coarseShading
      balanced := certificate.balanced
      muFine := certificate.muFine
      muCoarse := certificate.muCoarse
      W := certificate.W
      fiberFloor := certificate.fiberFloor
      muFine_pos := certificate.muFine_pos
      muCoarse_pos := certificate.muCoarse_pos
      W_pos := certificate.W_pos
      fiberFloor_pos := certificate.fiberFloor_pos
      regularity := certificate.regularity
      regularity_pos := certificate.regularity_pos
      packetCells := certificate.packetCells
      packetCells_nonempty := certificate.packetCells_nonempty
      packetCells_eq := certificate.packetCells_eq
      activeFineCells := certificate.activeFineCells
      active_fine_cells_eq := certificate.active_fine_cells_eq
      activeCoarseCells := certificate.activeCoarseCells
      active_coarse_cells_eq := certificate.active_coarse_cells_eq
      active_coarse_cells_nonempty :=
        certificate.active_coarse_cells_nonempty
      coarseOfFine := certificate.coarseOfFine
      packet_coarse_support := certificate.packet_coarse_support
      exact_fine_multiplicity := certificate.exact_fine_multiplicity
      balanced_cell_mass := certificate.balanced_cell_mass
      coarse_multiplicity := certificate.coarse_multiplicity
      fiber_cardinality := certificate.fiber_cardinality
      parent_cwa := certificate.parent_cwa
      rescaled_fiber_cwa := by
        intro parent
        let fiberInput := certificate.rescaled_fiber_input parent
        let base :
            RescaledMetricFiberCWAData
              certificate.cover parent metric.rho_pos
              ((81000000 : ENNReal) * (fiberConstant / 81000000)) :=
          {
            sourceConstant := fiberConstant / 81000000
            rescalingInput := fiberInput
            familyData := fiberInput.literal
            familyData_eq := rfl
            rescalingCertificate := fiberInput.certificate
            rescalingCertificate_eq := HEq.rfl
            constant_eq := rfl
            cwa := fiberInput.publicPureCWA
          }
        have constantEq :
            fiberConstant =
              (81000000 : ENNReal) * (fiberConstant / 81000000) :=
          (ENNReal.mul_div_cancel (by norm_num) (by norm_num)).symm
        have productLe :
            (81000000 : ENNReal) * (fiberConstant / 81000000) ≤
              outputConstant :=
          constantEq.ge.trans fiberConstantLe
        have outputFinite :
            WZ2PaperFiniteErrorConstant outputConstant :=
          ⟨certificate.parent_cwa.2.1.1, outputConstantFinite⟩
        exact ⟨base.weakenConstant productLe outputFinite⟩
      packet_density := certificate.packet_density
      total_mass_retention := certificate.total_mass_retention
    }

end MetricParentsV4PacketCellLocalInput

end Kakeya.Assouad.Prop62PaperAudit.V4

end
