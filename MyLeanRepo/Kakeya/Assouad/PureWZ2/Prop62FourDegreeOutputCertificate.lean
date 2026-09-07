import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CanonicalBalancingFromDensity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TerminalFiberCWA

/-!
# Proposition 6.2 generic four-degree output certificate

This module packages the canonical four-degree producer without referring to
the frozen V4 statement.  The terminal fine and coarse families, packet-cell
support, degree bands, density bound, and complete-fiber rescaling inputs all
remain the producer's existing objects.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62MetricFiberRescalingInput

/--
Change only the ambient cover and parent used to name a metric fiber.
The physical source family and every analytic/geometric witness remain those
of `input`; `sourceEquiv` certifies that this same family enumerates the target
cover's complete fiber.
-/
noncomputable def reanchor
    {fineScale parentScale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily fineScale}
    {coarse : Kakeya.Streamlined.TubeFamily parentScale}
    (cover : PureWZ2Section6Cover fine coarse)
    (parent : Fin coarse.card)
    {ambientFine : Kakeya.Streamlined.TubeFamily fineScale}
    {ambientCoarse : Kakeya.Streamlined.TubeFamily parentScale}
    {ambientCover : PureWZ2Section6Cover ambientFine ambientCoarse}
    {ambientParent : Fin ambientCoarse.card}
    {sourceConstant : ENNReal}
    (input :
      PureWZ2Prop62MetricFiberRescalingInput
        ambientCover ambientParent sourceConstant)
    (anchorEq :
      ambientCoarse.tube ambientParent = coarse.tube parent)
    (sourceIndices : Finset (Fin fine.card))
    (sourceIndicesEq :
      sourceIndices = wz2PaperFullFiberIndices fine coarse parent)
    (sourceIndicesNonempty : sourceIndices.Nonempty)
    (sourceEquiv :
      Fin input.sourceFamily.card ≃ sourceIndices)
    (sourceTubeEq :
      ∀ index,
        input.sourceFamily.tube index =
          fine.tube (sourceEquiv index).1) :
    PureWZ2Prop62MetricFiberRescalingInput
      cover parent sourceConstant where
  rho_pos := input.rho_pos
  rho_le_one := input.rho_le_one
  delta_pos := input.delta_pos
  scale_separation := input.scale_separation
  sourceIndices := sourceIndices
  sourceIndices_eq := sourceIndicesEq
  sourceIndices_nonempty := sourceIndicesNonempty
  sourceFamily := input.sourceFamily
  sourceEquiv := sourceEquiv
  source_tube_eq := sourceTubeEq
  source_line_class := input.source_line_class
  anchor_line_class := anchorEq ▸ input.anchor_line_class
  source_covered := fun index => anchorEq ▸ input.source_covered index
  source_strongly_separated := input.source_strongly_separated
  source_constant_finite := input.source_constant_finite
  target_locality := fun index => anchorEq ▸ input.target_locality index
  rescaled_physical_cwa := anchorEq ▸ input.rescaled_physical_cwa
  requested_route := fun requested =>
    anchorEq ▸ input.requested_route requested

end PureWZ2Prop62MetricFiberRescalingInput

/--
The V4-independent terminal output of the four-degree construction.

Unlike the frozen statement record, this certificate names the original
Section 6 cover directly and exposes the complete-fiber rescaling input at
its source constant.  A downstream statement adapter may package that input
into its own public rescaling record without changing the family.
-/
structure PureWZ2Prop62FourDegreeOutputCertificate
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {ambientCover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput ambientCover shading)
    (densityConstant outputParentConstant sourceFiberConstant : ENNReal) where
  refinement : WZ1PaperRefinement shading 50
  refined_cubical : WZ1PaperIsCubicalShading refinement.refined
  coarse : Kakeya.Streamlined.TubeSubfamily coarse
  cover :
    PureWZ2Section6Cover refinement.selected.family coarse.family
  parent_commutes :
    ∀ sourceIndex,
      ambientCover.toWZ1PaperTubeCover.parent
          (refinement.selected.embedding sourceIndex) =
        coarse.embedding
          (cover.toWZ1PaperTubeCover.parent sourceIndex)
  complete_fibers :
    ∀ oldSource newParent,
      ambientCover.toWZ1PaperTubeCover.parent oldSource =
          coarse.embedding newParent →
        ∃ newSource,
          refinement.selected.embedding newSource = oldSource
  refined_nonempty : refinement.selected.family.Nonempty
  coarseShading : WZ1PaperTubeShading coarse.family
  balanced :
    WZ1PaperBalancedCoverData
      cover.toWZ1PaperTubeCover refinement.refined coarseShading
  muFine : ℕ
  muCoarse : ℕ
  W : ℕ
  fiberFloor : ℕ
  muFine_pos : 0 < muFine
  muCoarse_pos : 0 < muCoarse
  W_pos : 0 < W
  fiberFloor_pos : 0 < fiberFloor
  regularity : ℕ
  regularity_pos : 0 < regularity
  packetCells : Finset (Fin coarse.family.card × WZ2PaperCellIndex)
  packetCells_nonempty : packetCells.Nonempty
  packetCells_eq :
    packetCells =
      ((Finset.univ : Finset (Fin coarse.family.card)).product
        (wz1PaperActiveCells refinement.refined input.delta_pos)).filter
          fun edge =>
            ((wz2PaperFullFiberIndices
                refinement.selected.family coarse.family edge.1).filter
              fun sourceIndex =>
                wz1PaperGridCube delta edge.2 ⊆
                  refinement.refined.carrier sourceIndex).Nonempty
  activeFineCells : Finset WZ2PaperCellIndex
  active_fine_cells_eq :
    activeFineCells = packetCells.image Prod.snd
  activeCoarseCells : Finset WZ2PaperCellIndex
  active_coarse_cells_eq :
    activeCoarseCells = balanced.activeCells
  active_coarse_cells_nonempty : activeCoarseCells.Nonempty
  coarseOfFine : WZ2PaperCellIndex → WZ2PaperCellIndex
  packet_coarse_support :
    ∀ edge ∈ packetCells,
      coarseOfFine edge.2 ∈ activeCoarseCells ∧
        wz1PaperGridCube delta edge.2 ⊆
          wz1PaperGridCube rho (coarseOfFine edge.2) ∧
        wz1PaperGridCube rho (coarseOfFine edge.2) ⊆
          wz1PaperTubeCarrier (coarse.family.tube edge.1)
  exact_fine_multiplicity :
    ∀ edge ∈ packetCells,
      ((wz2PaperFullFiberIndices
          refinement.selected.family coarse.family edge.1).filter
        fun sourceIndex =>
          wz1PaperGridCube delta edge.2 ⊆
            refinement.refined.carrier sourceIndex).card =
        muFine
  balanced_cell_mass :
    balanced.cellMass =
      W * volume (wz1PaperGridCube delta (0, 0, 0))
  coarse_multiplicity :
    ∀ cell ∈ activeCoarseCells,
      muCoarse ≤
          (Finset.univ.filter fun parent =>
            wz1PaperGridCube rho cell ⊆
              coarseShading.carrier parent).card ∧
        (Finset.univ.filter fun parent =>
          wz1PaperGridCube rho cell ⊆
            coarseShading.carrier parent).card ≤
          regularity * muCoarse
  fiber_cardinality :
    ∀ parent,
      (fiberFloor : ENNReal) ≤
          wz2PaperFullFiberCount
            refinement.selected.family coarse.family parent ∧
        wz2PaperFullFiberCount
            refinement.selected.family coarse.family parent <
          2 * (fiberFloor : ENNReal)
  parent_cwa :
    WZ2PaperPureCWAAtNearbyScales coarse.family outputParentConstant
  rescaled_fiber_input :
    ∀ parent,
      PureWZ2Prop62MetricFiberRescalingInput
        cover parent sourceFiberConstant
  packet_density :
    ∀ parent,
      densityConstant * (fiberFloor : ENNReal) *
            Kakeya.realRpowENN delta 2 ≤
        (restrictPaperShading
          (wz2PaperFullFiberSubfamily
            refinement.selected.family coarse.family parent)
          refinement.refined).mass
  total_mass_retention :
    wz1PaperRefinementFraction delta 50 * shading.mass ≤
      refinement.refined.mass

/--
Every retained final fine cell lies in the active coarse cell recorded by
the same V4 packet certificate.  This is intrinsic certificate data used by
both Node 4 and the direct-rich Node 5 continuation.
-/
theorem PureWZ2Prop62FourDegreeOutputCertificate.fine_cell_nested
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {ambientCover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {input : PureWZ2Prop62PacketCellInput ambientCover shading}
    {densityConstant outputParentConstant sourceFiberConstant : ENNReal}
    (output : PureWZ2Prop62FourDegreeOutputCertificate input
      densityConstant outputParentConstant sourceFiberConstant) :
    ∀ source point,
      point ∈ output.refinement.refined.carrier source →
        ∃ cell ∈ output.balanced.activeCells,
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperGridCube rho cell := by
  intro source point pointMem
  let parent : Fin output.coarse.family.card :=
    output.cover.toWZ1PaperTubeCover.parent source
  let fineCell : WZ2PaperCellIndex := wz1PaperGridIndex delta point
  have wholeFineCell : wz1PaperGridCube delta fineCell ⊆
      output.refinement.refined.carrier source :=
    output.refined_cubical source point pointMem
  have fineCellActive : fineCell ∈
      wz1PaperActiveCells output.refinement.refined input.delta_pos := by
    rw [mem_wz1PaperActiveCells]
    constructor
    · apply paper_point_gridIndex_in_window input.delta_pos
      exact shading_union_subset_axisBox
        (show point ∈ output.refinement.refined.union from
          ⟨source, pointMem⟩)
    · exact ⟨point, ⟨source, pointMem⟩,
        (mem_wz1PaperGridCube delta fineCell point).mpr rfl⟩
  have sourceFiber : source ∈
      wz2PaperFullFiberIndices output.refinement.selected.family
        output.coarse.family parent := by
    exact (mem_wz2PaperFullFiberIndices_iff parent source).mpr
      (output.cover.toWZ1PaperTubeCover.parent_covers source)
  have packetMem : (parent, fineCell) ∈ output.packetCells := by
    rw [output.packetCells_eq]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨Finset.mem_univ parent, fineCellActive⟩, ?_⟩
    exact ⟨source, Finset.mem_filter.mpr
      ⟨sourceFiber, wholeFineCell⟩⟩
  have support := output.packet_coarse_support (parent, fineCell) packetMem
  refine ⟨output.coarseOfFine fineCell, ?_, support.2.1⟩
  rw [← output.active_coarse_cells_eq]
  exact support.1

namespace PureWZ2Prop62PacketCellInput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {ambientCover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput ambientCover shading)
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        coarse ambientConstant scaleWindow)
    {fiberConstant densityConstant : ENNReal}
    (producer :
      input.CanonicalFourDegreeProducerData
        (schedule := schedule) fiberConstant densityConstant)

private def finalRefinement :
    WZ1PaperRefinement shading 50 where
  selected := producer.families.restriction.fineSelected
  refined := producer.output.output.fineShading
  subshading sourceIndex := by
    rw [producer.output.output.fineShading_eq]
    exact
      TerminalFineShading.subshading
        input producer.initial.multiplicity producer.initial.parentClass
        producer.initial.treeCleanup producer.initial.exactification
        producer.core.ranges producer.output.good producer.families sourceIndex
  retained_mass := producer.output.output.retained_mass

private theorem parent_commutes
    (sourceIndex :
      Fin producer.families.restriction.fineSelected.family.card) :
    ambientCover.toWZ1PaperTubeCover.parent
        (producer.families.restriction.fineSelected.embedding sourceIndex) =
      producer.families.restriction.coarseSelected.embedding
        (producer.families.restriction.section6Cover.toWZ1PaperTubeCover.parent
          sourceIndex) := by
  symm
  apply ambientCover.toWZ1PaperTubeCover.parent_unique
  simpa only [
    producer.families.restriction.fineSelected.tube_eq,
    producer.families.restriction.coarseSelected.tube_eq
  ] using
    producer.families.restriction.section6Cover.toWZ1PaperTubeCover
      |>.parent_covers sourceIndex

private theorem complete_fibers
    (oldSource : Fin fine.card)
    (newParent :
      Fin producer.families.restriction.coarseSelected.family.card)
    (parentEq :
      ambientCover.toWZ1PaperTubeCover.parent oldSource =
        producer.families.restriction.coarseSelected.embedding newParent) :
    ∃ newSource,
      producer.families.restriction.fineSelected.embedding newSource =
        oldSource := by
  have oldSourceTerminal : oldSource ∈ producer.families.terminalFine := by
    rw [producer.families.terminalFine_eq]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ oldSource, ?_⟩
    rw [parentEq, ← producer.families.terminalParents_eq,
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
      FrozenCoarseShading.terminal_union_eq_activeCoarseCells
        input producer.initial.multiplicity producer.initial.parentClass
        producer.initial.treeCleanup producer.initial.exactification
        producer.core.ranges producer.families
  cellMass :=
    (producer.output.output.W : ENNReal) *
      volume (wz1PaperGridCube delta (0, 0, 0))
  cellMass_pos :=
    ENNReal.mul_pos
      (by exact_mod_cast producer.output.output.W_pos.ne')
      (wz1PaperGridCube_volume_pos input.delta_pos _).ne'
  cellMass_ne_top :=
    ENNReal.mul_ne_top
      (by simp)
      (wz1PaperGridCube_volume_ne_top input.delta_pos _)
  fine_cell_mass := by
    intro coarseCell coarseCellMem
    exact producer.output.output.exact_balance coarseCell coarseCellMem

def packetCells :
    Finset
      (Fin producer.families.restriction.coarseSelected.family.card ×
        WZ2PaperCellIndex) :=
  ((Finset.univ :
      Finset
        (Fin producer.families.restriction.coarseSelected.family.card)).product
      (wz1PaperActiveCells
        (input.finalRefinement schedule producer).refined input.delta_pos)).filter
    fun edge =>
      ((wz2PaperFullFiberIndices
          (input.finalRefinement schedule producer).selected.family
          producer.families.restriction.coarseSelected.family edge.1).filter
        fun sourceIndex =>
          wz1PaperGridCube delta edge.2 ⊆
            (input.finalRefinement schedule producer).refined.carrier
              sourceIndex).Nonempty

private theorem exists_selectedEdge_of_packetCell
    {parent :
      Fin producer.families.restriction.coarseSelected.family.card}
    {cell : WZ2PaperCellIndex}
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
    ∃ edge : producer.initial.exactification.incidence.Edge,
      edge ∈
          producer.core.ranges.selectedEdges
            producer.output.good.sample ∧
        producer.initial.exactification.incidence.edgeParent edge =
          producer.families.restriction.coarseSelected.embedding parent ∧
        producer.initial.exactification.incidence.edgeFineCell edge = cell := by
  let point := cellCorner delta cell
  have pointCell : point ∈ wz1PaperGridCube delta cell :=
    cellCorner_mem_gridCube input.delta_pos cell
  have pointTerminal :
      point ∈ producer.output.output.fineShading.carrier sourceIndex :=
    cellSubset pointCell
  have pointAmbient :
      point ∈
        (input.exactFineShading
          producer.initial.multiplicity producer.initial.parentClass
          producer.initial.treeCleanup producer.initial.exactification
          producer.core.ranges producer.output.good).carrier
            (producer.families.restriction.fineSelected.embedding
              sourceIndex) := by
    rw [producer.output.output.fineShading_eq] at pointTerminal
    exact pointTerminal
  rw [ExactFineShading.carrier_eq
    input producer.initial.multiplicity producer.initial.parentClass
    producer.initial.treeCleanup producer.initial.exactification
    producer.core.ranges producer.output.good] at pointAmbient
  rcases Set.mem_iUnion₂.mp pointAmbient with
    ⟨otherCell, otherCellMem, pointOtherCell⟩
  rcases Finset.mem_image.mp otherCellMem with
    ⟨edge, edgeMem, edgeFine⟩
  have edgeSelected :
      edge ∈
        producer.core.ranges.selectedEdges producer.output.good.sample :=
    (Finset.mem_filter.mp edgeMem).1
  have sourceSelected :
      input.sourceSelectedOnEdge
        producer.initial.multiplicity producer.initial.parentClass
        producer.initial.treeCleanup producer.initial.exactification
        (producer.families.restriction.fineSelected.embedding sourceIndex)
        edge :=
    (Finset.mem_filter.mp edgeMem).2
  have ambientFiber :
      producer.families.restriction.fineSelected.embedding sourceIndex ∈
        wz2PaperFullFiberIndices fine coarse
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
    ExactFineShading.sourceSelectedOnEdge_parent_eq
      input producer.initial.multiplicity producer.initial.parentClass
      producer.initial.treeCleanup producer.initial.exactification
      ambientFiber sourceSelected
  have cellEq : otherCell = cell := by
    have otherIndex :
        wz1PaperGridIndex delta point = otherCell :=
      (mem_wz1PaperGridCube delta otherCell point).mp pointOtherCell
    have ownIndex :
        wz1PaperGridIndex delta point = cell :=
      (mem_wz1PaperGridCube delta cell point).mp pointCell
    exact otherIndex.symm.trans ownIndex
  exact ⟨edge, edgeSelected, edgeParent, edgeFine.trans cellEq⟩

private theorem packetCells_nonempty :
    (input.packetCells schedule producer).Nonempty := by
  have selectedEdgesNonempty :
      producer.core.ranges.selectedEdges producer.output.good.sample
        |>.Nonempty := by
    let terminalEdge := Classical.choose producer.core.core_nonempty
    have terminalEdgeMem : terminalEdge ∈ producer.core.ranges.terminalEdges := by
      change terminalEdge ∈ producer.core.ranges.peeling.core
      rw [producer.core.ranges_peeling_eq]
      exact Classical.choose_spec producer.core.core_nonempty
    let coarseActive : producer.core.ranges.ActiveCoarseCell :=
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
  rcases producer.output.output.exact_fine edge edgeSelected with
    ⟨parent, edgeParent, sourcesCard⟩
  have sourcesNonempty :
      (TerminalFineShading.terminalPacketCellSources
        input producer.initial.multiplicity producer.initial.parentClass
        producer.initial.treeCleanup producer.initial.exactification
        producer.initial.parentDegree producer.core producer.output.good
        producer.families parent edge).Nonempty := by
    apply Finset.card_pos.mp
    rw [sourcesCard]
    exact producer.output.output.muFine_pos
  rcases sourcesNonempty with ⟨sourceIndex, sourceMem⟩
  refine
    ⟨(parent, producer.initial.exactification.incidence.edgeFineCell edge), ?_⟩
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
            input.referencePairs
              producer.initial.multiplicity producer.initial.parentClass
              producer.initial.treeCleanup := by
        rw [← producer.initial.exactification.incidence_edgePool_eq]
        exact edgePoolMem
      have referenceMem :=
        (input.mem_referencePairs_iff
          producer.initial.multiplicity producer.initial.parentClass
          producer.initial.treeCleanup edge.1).mp referenceEdgeMem
      have selectedMem := referenceMem.1
      have positiveMem :=
        producer.initial.multiplicity.selectedPairs_subset selectedMem
      have fineCellMem :=
        (input.mem_positivePairs_iff edge.1).mp positiveMem |>.1
      have originalActive :
          producer.initial.exactification.incidence.edgeFineCell edge ∈
            wz1PaperActiveCells shading input.delta_pos := by
        rw [← input.fineCells_eq]
        simpa [PureWZ2Prop62FourDegreeIncidenceData.edgeFineCell] using
          fineCellMem
      exact
        (mem_wz1PaperActiveCells shading input.delta_pos _).mp
          originalActive |>.1
    · let point :=
        cellCorner delta
          (producer.initial.exactification.incidence.edgeFineCell edge)
      refine ⟨point, ?_, cellCorner_mem_gridCube input.delta_pos _⟩
      refine ⟨sourceIndex, ?_⟩
      change point ∈ producer.output.output.fineShading.carrier sourceIndex
      rw [producer.output.output.fineShading_eq]
      exact
        (Finset.mem_filter.mp sourceMem).2
          (cellCorner_mem_gridCube input.delta_pos _)
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

/-- Every selected terminal incidence edge gives the corresponding public
parent--fine-cell packet.  This is the reverse direction needed when a
downstream consumer counts all terminal parents through one selected cell. -/
private theorem packetCell_of_selectedEdge
    {edge : producer.initial.exactification.incidence.Edge}
    (edgeSelected :
      edge ∈ producer.core.ranges.selectedEdges producer.output.good.sample) :
    ∃ parent : Fin producer.families.restriction.coarseSelected.family.card,
      (parent, producer.initial.exactification.incidence.edgeFineCell edge) ∈
          input.packetCells schedule producer ∧
        producer.initial.exactification.incidence.edgeParent edge =
          producer.families.restriction.coarseSelected.embedding parent := by
  rcases producer.output.output.exact_fine edge edgeSelected with
    ⟨parent, edgeParent, sourcesCard⟩
  have sourcesNonempty :
      (TerminalFineShading.terminalPacketCellSources
        input producer.initial.multiplicity producer.initial.parentClass
        producer.initial.treeCleanup producer.initial.exactification
        producer.initial.parentDegree producer.core producer.output.good
        producer.families parent edge).Nonempty := by
    apply Finset.card_pos.mp
    rw [sourcesCard]
    exact producer.output.output.muFine_pos
  rcases sourcesNonempty with ⟨sourceIndex, sourceMem⟩
  refine ⟨parent, ?_, edgeParent⟩
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
            input.referencePairs producer.initial.multiplicity
              producer.initial.parentClass producer.initial.treeCleanup := by
        rw [← producer.initial.exactification.incidence_edgePool_eq]
        exact edgePoolMem
      have selectedMem :=
        (input.mem_referencePairs_iff producer.initial.multiplicity
          producer.initial.parentClass producer.initial.treeCleanup edge.1).mp
          referenceEdgeMem |>.1
      have positiveMem :=
        producer.initial.multiplicity.selectedPairs_subset selectedMem
      have fineCellMem :=
        (input.mem_positivePairs_iff edge.1).mp positiveMem |>.1
      have originalActive :
          producer.initial.exactification.incidence.edgeFineCell edge ∈
            wz1PaperActiveCells shading input.delta_pos := by
        rw [← input.fineCells_eq]
        simpa [PureWZ2Prop62FourDegreeIncidenceData.edgeFineCell] using
          fineCellMem
      exact
        (mem_wz1PaperActiveCells shading input.delta_pos _).mp
          originalActive |>.1
    · let point := cellCorner delta
          (producer.initial.exactification.incidence.edgeFineCell edge)
      refine ⟨point, ?_, cellCorner_mem_gridCube input.delta_pos _⟩
      refine ⟨sourceIndex, ?_⟩
      change point ∈ producer.output.output.fineShading.carrier sourceIndex
      rw [producer.output.output.fineShading_eq]
      exact
        (Finset.mem_filter.mp sourceMem).2
          (cellCorner_mem_gridCube input.delta_pos _)
  · refine ⟨sourceIndex, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact (Finset.mem_filter.mp sourceMem).1
    · change
        wz1PaperGridCube delta
            (producer.initial.exactification.incidence.edgeFineCell edge) ⊆
          producer.output.output.fineShading.carrier sourceIndex
      rw [producer.output.output.fineShading_eq]
      exact (Finset.mem_filter.mp sourceMem).2

/-- The public packet degree of every selected fine cell is bounded below by
the fine-cell threshold of the terminal four-degree core. -/
theorem packetCells_fine_degree_lower
    (cell : WZ2PaperCellIndex)
    (cellMem : cell ∈ (input.packetCells schedule producer).image Prod.snd) :
    input.fineCellThreshold producer.initial.multiplicity
          producer.initial.parentClass producer.initial.treeCleanup
          producer.initial.exactification producer.initial.bins
          (input.canonicalPeelingA0 producer.initial.multiplicity
            producer.initial.parentClass producer.initial.treeCleanup
            producer.initial.exactification producer.initial.bins) ≤
      ((input.packetCells schedule producer).filter
        fun edge => edge.2 = cell).card := by
  rcases Finset.mem_image.mp cellMem with
    ⟨packet, packetMem, packetCell⟩
  rcases (Finset.mem_filter.mp packetMem).2 with
    ⟨sourceIndex, sourceMem⟩
  have sourceData := Finset.mem_filter.mp sourceMem
  rcases input.exists_selectedEdge_of_packetCell schedule producer
      sourceData.1 sourceData.2 with
    ⟨selectedEdge, selectedEdgeMem, _selectedParent, selectedCell⟩
  have selectedCellEq :
      producer.initial.exactification.incidence.edgeFineCell selectedEdge =
        cell := selectedCell.trans packetCell
  have selectedTerminal :
      selectedEdge ∈ producer.core.ranges.terminalEdges :=
    producer.output.good.selectedEdges_subset selectedEdgeMem
  have fineDegreePos :
      0 < producer.initial.exactification.incidence.fineCellDegree
        producer.core.ranges.terminalEdges cell := by
    apply Finset.card_pos.mpr
    exact ⟨selectedEdge, Finset.mem_filter.mpr
      ⟨selectedTerminal, selectedCellEq⟩⟩
  have thresholdLower :=
    (PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.fineCell_range
      producer.initial.exactification.incidence
      producer.core.ranges cell fineDegreePos).1
  let terminalAtCell := producer.core.ranges.terminalEdges.filter fun edge =>
    producer.initial.exactification.incidence.edgeFineCell edge = cell
  let packetsAtCell := (input.packetCells schedule producer).filter fun edge =>
    edge.2 = cell
  have selectedFine :
      producer.initial.exactification.incidence.edgeFineCell selectedEdge ∈
        (producer.output.good.sample
          ⟨producer.initial.exactification.incidence.edgeCoarseCell selectedEdge,
            by
              rw [producer.initial.exactification.incidence.mem_activeCoarseCells_iff]
              exact Finset.card_pos.mpr ⟨selectedEdge,
                Finset.mem_filter.mpr ⟨selectedTerminal, rfl⟩⟩⟩).1 := by
    have selectedData := Finset.mem_filter.mp selectedEdgeMem
    have selectedCondition := selectedData.2
    have selectedActive :
        producer.initial.exactification.incidence.edgeCoarseCell selectedEdge ∈
          producer.initial.exactification.incidence.activeCoarseCells
            producer.core.ranges.terminalEdges := by
      rw [producer.initial.exactification.incidence.mem_activeCoarseCells_iff]
      exact Finset.card_pos.mpr ⟨selectedEdge,
        Finset.mem_filter.mpr ⟨selectedTerminal, rfl⟩⟩
    change
      (if coarseActive :
          producer.initial.exactification.incidence.edgeCoarseCell selectedEdge ∈
            producer.initial.exactification.incidence.activeCoarseCells
              producer.core.ranges.terminalEdges then
        producer.initial.exactification.incidence.edgeFineCell selectedEdge ∈
          (producer.output.good.sample
            ⟨producer.initial.exactification.incidence.edgeCoarseCell
                selectedEdge, coarseActive⟩).1
      else False) at selectedCondition
    rw [dif_pos selectedActive] at selectedCondition
    exact selectedCondition
  have edgeSelected : ∀ edge ∈ terminalAtCell,
      edge ∈ producer.core.ranges.selectedEdges producer.output.good.sample := by
    intro edge edgeMem
    have edgeData := Finset.mem_filter.mp edgeMem
    have sameFine :
        producer.initial.exactification.incidence.edgeFineCell edge =
          producer.initial.exactification.incidence.edgeFineCell selectedEdge :=
      edgeData.2.trans selectedCellEq.symm
    have sameCoarse :
        producer.initial.exactification.incidence.edgeCoarseCell edge =
          producer.initial.exactification.incidence.edgeCoarseCell selectedEdge := by
      unfold PureWZ2Prop62FourDegreeIncidenceData.edgeCoarseCell
      rw [sameFine]
    apply Finset.mem_filter.mpr
    refine ⟨edgeData.1, ?_⟩
    have edgeCoarseActive :
        producer.initial.exactification.incidence.edgeCoarseCell edge ∈
          producer.initial.exactification.incidence.activeCoarseCells
            producer.core.ranges.terminalEdges := by
      rw [sameCoarse]
      rw [producer.initial.exactification.incidence.mem_activeCoarseCells_iff]
      exact Finset.card_pos.mpr ⟨selectedEdge,
        Finset.mem_filter.mpr ⟨selectedTerminal, rfl⟩⟩
    simp only [dif_pos edgeCoarseActive]
    have activeEq :
        (⟨producer.initial.exactification.incidence.edgeCoarseCell edge,
          edgeCoarseActive⟩ : producer.core.ranges.ActiveCoarseCell) =
          ⟨producer.initial.exactification.incidence.edgeCoarseCell selectedEdge,
            by
              rw [producer.initial.exactification.incidence.mem_activeCoarseCells_iff]
              exact Finset.card_pos.mpr ⟨selectedEdge,
                Finset.mem_filter.mpr ⟨selectedTerminal, rfl⟩⟩⟩ :=
      Subtype.ext sameCoarse
    rw [activeEq, sameFine]
    exact selectedFine
  let assigned : ∀ edge : {edge // edge ∈ terminalAtCell},
      Fin producer.families.restriction.coarseSelected.family.card := fun edge =>
    Classical.choose <|
      input.packetCell_of_selectedEdge schedule producer
        (edgeSelected edge.1 edge.2)
  let toPacket : {edge // edge ∈ terminalAtCell} →
      {packet // packet ∈ packetsAtCell} := fun edge =>
    ⟨(assigned edge,
        producer.initial.exactification.incidence.edgeFineCell edge.1), by
      apply Finset.mem_filter.mpr
      refine ⟨(Classical.choose_spec <|
        input.packetCell_of_selectedEdge schedule producer
          (edgeSelected edge.1 edge.2)).1, ?_⟩
      exact (Finset.mem_filter.mp edge.2).2⟩
  have toPacketInjective : Function.Injective toPacket := by
    intro first second equality
    have pairEq := congrArg Subtype.val equality
    have parentEq : assigned first = assigned second :=
      congrArg Prod.fst pairEq
    have firstParent := (Classical.choose_spec <|
      input.packetCell_of_selectedEdge schedule producer
        (edgeSelected first.1 first.2)).2
    have secondParent := (Classical.choose_spec <|
      input.packetCell_of_selectedEdge schedule producer
        (edgeSelected second.1 second.2)).2
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · have ambientParentEq := congrArg
          producer.families.restriction.coarseSelected.embedding parentEq
      exact firstParent.trans (ambientParentEq.trans secondParent.symm)
    · exact (Finset.mem_filter.mp first.2).2.trans
        (Finset.mem_filter.mp second.2).2.symm
  have cardLower : terminalAtCell.card ≤ packetsAtCell.card :=
    Finset.card_le_card_of_injective toPacketInjective
  exact thresholdLower.trans cardLower

/-- The public packet degree of a selected fine cell is bounded above by the
same terminal dyadic degree, with only the canonical peeling loss.  Together
with `packetCells_fine_degree_lower`, this keeps the absolute size of the
fine-cell degree available after the producer-specific graph is forgotten. -/
theorem packetCells_fine_degree_upper
    (cell : WZ2PaperCellIndex)
    (cellMem : cell ∈ (input.packetCells schedule producer).image Prod.snd) :
    ((input.packetCells schedule producer).filter
        fun edge => edge.2 = cell).card ≤
      2 *
        input.canonicalPeelingA0 producer.initial.multiplicity
          producer.initial.parentClass producer.initial.treeCleanup
          producer.initial.exactification producer.initial.bins *
        input.fineCellThreshold producer.initial.multiplicity
          producer.initial.parentClass producer.initial.treeCleanup
          producer.initial.exactification producer.initial.bins
          (input.canonicalPeelingA0 producer.initial.multiplicity
            producer.initial.parentClass producer.initial.treeCleanup
            producer.initial.exactification producer.initial.bins) := by
  let packetsAtCell := (input.packetCells schedule producer).filter fun edge =>
    edge.2 = cell
  let terminalAtCell := producer.core.ranges.terminalEdges.filter fun edge =>
    producer.initial.exactification.incidence.edgeFineCell edge = cell
  have existsEdge : ∀ packet : {packet // packet ∈ packetsAtCell},
      ∃ edge : producer.initial.exactification.incidence.Edge,
        edge ∈ terminalAtCell ∧
          producer.initial.exactification.incidence.edgeParent edge =
            producer.families.restriction.coarseSelected.embedding packet.1.1 := by
    intro packet
    have packetMem : packet.1 ∈ input.packetCells schedule producer :=
      (Finset.mem_filter.mp packet.2).1
    have packetCell : packet.1.2 = cell :=
      (Finset.mem_filter.mp packet.2).2
    rcases (Finset.mem_filter.mp packetMem).2 with ⟨sourceIndex, sourceMem⟩
    rcases input.exists_selectedEdge_of_packetCell schedule producer
        (Finset.mem_filter.mp sourceMem).1
        (Finset.mem_filter.mp sourceMem).2 with
      ⟨edge, edgeSelected, edgeParent, edgeFine⟩
    refine ⟨edge, Finset.mem_filter.mpr ⟨?_, edgeFine.trans packetCell⟩,
      edgeParent⟩
    exact producer.output.good.selectedEdges_subset edgeSelected
  let assigned : {packet // packet ∈ packetsAtCell} →
      {edge // edge ∈ terminalAtCell} := fun packet =>
    ⟨Classical.choose (existsEdge packet),
      (Classical.choose_spec (existsEdge packet)).1⟩
  have assignedInjective : Function.Injective assigned := by
    intro first second assignedEq
    apply Subtype.ext
    apply Prod.ext
    · apply producer.families.restriction.coarseSelected.embedding.injective
      have edgeEq := congrArg Subtype.val assignedEq
      calc
        producer.families.restriction.coarseSelected.embedding first.1.1 =
            producer.initial.exactification.incidence.edgeParent
              (assigned first).1 :=
          (Classical.choose_spec (existsEdge first)).2.symm
        _ = producer.initial.exactification.incidence.edgeParent
              (assigned second).1 := by rw [edgeEq]
        _ = producer.families.restriction.coarseSelected.embedding second.1.1 :=
          (Classical.choose_spec (existsEdge second)).2
    · exact (Finset.mem_filter.mp first.2).2.trans
        (Finset.mem_filter.mp second.2).2.symm
  have packetLeTerminal : packetsAtCell.card ≤ terminalAtCell.card :=
    Finset.card_le_card_of_injective assignedInjective
  have terminalDegreeEq : terminalAtCell.card =
      producer.initial.exactification.incidence.fineCellDegree
        producer.core.ranges.terminalEdges cell := rfl
  have fineDegreePos :
      0 < producer.initial.exactification.incidence.fineCellDegree
        producer.core.ranges.terminalEdges cell := by
    rcases Finset.mem_image.mp cellMem with ⟨packet, packetMem, packetCell⟩
    rcases (Finset.mem_filter.mp packetMem).2 with ⟨sourceIndex, sourceMem⟩
    rcases input.exists_selectedEdge_of_packetCell schedule producer
        (Finset.mem_filter.mp sourceMem).1
        (Finset.mem_filter.mp sourceMem).2 with
      ⟨edge, edgeSelected, _edgeParent, edgeFine⟩
    apply Finset.card_pos.mpr
    refine ⟨edge, Finset.mem_filter.mpr ⟨?_, edgeFine.trans packetCell⟩⟩
    exact producer.output.good.selectedEdges_subset edgeSelected
  have terminalDegreeUpper :=
    (PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.fineCell_range
      producer.initial.exactification.incidence producer.core.ranges cell
      fineDegreePos).2.le
  let A0 := input.canonicalPeelingA0 producer.initial.multiplicity
    producer.initial.parentClass producer.initial.treeCleanup
    producer.initial.exactification producer.initial.bins
  let fineBase : ℕ := 2 ^ producer.initial.bins.fineCellBin.level
  have baseLe : fineBase ≤ A0 *
      input.fineCellThreshold producer.initial.multiplicity
        producer.initial.parentClass producer.initial.treeCleanup
        producer.initial.exactification producer.initial.bins A0 := by
    simpa [fineBase, A0, PureWZ2Prop62PacketCellInput.fineCellThreshold] using
      (le_smul_ceilDiv producer.core.A0_pos :
        2 ^ producer.initial.bins.fineCellBin.level ≤
          A0 * (2 ^ producer.initial.bins.fineCellBin.level ⌈/⌉ A0))
  calc
    ((input.packetCells schedule producer).filter
        fun edge => edge.2 = cell).card = packetsAtCell.card := rfl
    _ ≤ terminalAtCell.card := packetLeTerminal
    _ = producer.initial.exactification.incidence.fineCellDegree
        producer.core.ranges.terminalEdges cell := terminalDegreeEq
    _ ≤ 2 * fineBase := by
      simpa [fineBase,
        PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.terminalEdges,
        pow_succ, Nat.mul_comm] using terminalDegreeUpper
    _ ≤ 2 * (A0 * input.fineCellThreshold producer.initial.multiplicity
        producer.initial.parentClass producer.initial.treeCleanup
        producer.initial.exactification producer.initial.bins A0) :=
      Nat.mul_le_mul_left 2 baseLe
    _ = 2 * A0 * input.fineCellThreshold producer.initial.multiplicity
        producer.initial.parentClass producer.initial.treeCleanup
        producer.initial.exactification producer.initial.bins A0 := by ring

/-- The public packet-degree upper bound expressed with the regularity factor
that is exported by the canonical four-degree output.  Keeping this
conversion next to the producer avoids unfolding the full dependent producer
record in downstream Node 4 constructions. -/
theorem packetCells_fine_degree_upper_canonical
    (cell : WZ2PaperCellIndex)
    (cellMem : cell ∈ (input.packetCells schedule producer).image Prod.snd) :
    ((input.packetCells schedule producer).filter
        fun edge => edge.2 = cell).card ≤
      producer.output.output.coarseLoss *
        input.fineCellThreshold producer.initial.multiplicity
          producer.initial.parentClass producer.initial.treeCleanup
          producer.initial.exactification producer.initial.bins
          (input.canonicalPeelingA0 producer.initial.multiplicity
            producer.initial.parentClass producer.initial.treeCleanup
            producer.initial.exactification producer.initial.bins) := by
  let A0 := input.canonicalPeelingA0 producer.initial.multiplicity
    producer.initial.parentClass producer.initial.treeCleanup
    producer.initial.exactification producer.initial.bins
  have packetUpper :=
    input.packetCells_fine_degree_upper schedule producer cell cellMem
  calc
    ((input.packetCells schedule producer).filter
        fun edge => edge.2 = cell).card ≤
      2 * A0 *
        input.fineCellThreshold producer.initial.multiplicity
          producer.initial.parentClass producer.initial.treeCleanup
          producer.initial.exactification producer.initial.bins A0 := by
      exact packetUpper
    _ ≤ producer.output.output.coarseLoss *
        input.fineCellThreshold producer.initial.multiplicity
          producer.initial.parentClass producer.initial.treeCleanup
          producer.initial.exactification producer.initial.bins A0 := by
      gcongr
      rw [producer.output.output.coarseLoss_eq]
      change 2 * A0 ≤ 4 * A0 ^ 2
      nlinarith [producer.core.A0_pos]

private noncomputable def terminalMetricFiberRescalingInput
    {rhoLeOne : rho ≤ 1}
    {sourceFiberConstant : ENNReal}
    (terminalRescaling :
      producer.families.TerminalPublicRescalingData
        input producer.initial.multiplicity producer.initial.parentClass
        producer.initial.treeCleanup producer.initial.exactification
        producer.initial.parentDegree producer.core
        rhoLeOne sourceFiberConstant)
    (parent :
      Fin producer.families.restriction.coarseSelected.family.card) :
    PureWZ2Prop62MetricFiberRescalingInput
      producer.families.restriction.section6Cover parent
      sourceFiberConstant := by
  let reindex :=
    terminalRescaling.reindexData
      input producer.initial.multiplicity producer.initial.parentClass
      producer.initial.treeCleanup producer.initial.exactification
      producer.initial.parentDegree producer.core producer.families parent
  let terminalFiber :=
    producer.families.terminalFiber
      input producer.initial.multiplicity producer.initial.parentClass
      producer.initial.treeCleanup producer.initial.exactification
      producer.initial.parentDegree producer.core parent
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
  exact
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

/--
Canonical producer for the neutral terminal four-degree certificate.
The only external fiber datum is the already constructed ambient complete
fiber rescaling input; it is reindexed onto the producer's exact terminal
complete fibers without selecting a new family.
-/
noncomputable def fourDegreeOutputCertificate_of_canonicalProducer
    {outputParentConstant sourceFiberConstant : ENNReal}
    (outputParentFinite : outputParentConstant ≠ ⊤)
    (parentConstantLe :
      producer.output.output.parentConstant ≤ outputParentConstant)
    {rhoLeOne : rho ≤ 1}
    (terminalRescaling :
      producer.families.TerminalPublicRescalingData
        input producer.initial.multiplicity producer.initial.parentClass
        producer.initial.treeCleanup producer.initial.exactification
        producer.initial.parentDegree producer.core
        rhoLeOne sourceFiberConstant) :
    PureWZ2Prop62FourDegreeOutputCertificate
      input densityConstant outputParentConstant sourceFiberConstant := by
  let refinement := input.finalRefinement schedule producer
  let publicBalanced := input.balanced schedule producer
  let packets := input.packetCells schedule producer
  exact
    {
      refinement := refinement
      refined_cubical := by
        change WZ1PaperIsCubicalShading producer.output.output.fineShading
        rw [producer.output.output.fineShading_eq]
        exact
          TerminalFineShading.cubical
            input producer.initial.multiplicity producer.initial.parentClass
            producer.initial.treeCleanup producer.initial.exactification
            producer.core.ranges producer.output.good producer.families
      coarse := producer.families.restriction.coarseSelected
      cover := producer.families.restriction.section6Cover
      parent_commutes := input.parent_commutes schedule producer
      complete_fibers := input.complete_fibers schedule producer
      refined_nonempty := by
        change producer.families.restriction.fineSelected.family.Nonempty
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
      packetCells_nonempty := input.packetCells_nonempty schedule producer
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
      coarseOfFine := input.coarseCellOf
      packet_coarse_support := by
        intro edge edgeMem
        have packetData := Finset.mem_filter.mp edgeMem
        have edgeProduct := Finset.mem_product.mp packetData.1
        rcases packetData.2 with ⟨sourceIndex, sourceMem⟩
        have sourceData := Finset.mem_filter.mp sourceMem
        have wholeOriginal :
            wz1PaperGridCube delta edge.2 ⊆
              shading.carrier
                (producer.families.restriction.fineSelected.embedding
                  sourceIndex) := by
          intro point pointMem
          exact
            (input.finalRefinement schedule producer).subshading
              sourceIndex (sourceData.2 pointMem)
        have originalActive :
            edge.2 ∈ wz1PaperActiveCells shading input.delta_pos := by
          have finalActive :=
            (mem_wz1PaperActiveCells
              (input.finalRefinement schedule producer).refined
              input.delta_pos edge.2).mp edgeProduct.2
          rw [mem_wz1PaperActiveCells]
          refine ⟨finalActive.1, ?_⟩
          let point := cellCorner delta edge.2
          exact
            ⟨point,
              ⟨producer.families.restriction.fineSelected.embedding
                  sourceIndex,
                wholeOriginal
                  (cellCorner_mem_gridCube input.delta_pos edge.2)⟩,
              cellCorner_mem_gridCube input.delta_pos edge.2⟩
        have inputFineCell : edge.2 ∈ input.fineCells := by
          rw [input.fineCells_eq]
          exact originalActive
        have ambientFiber :
            producer.families.restriction.fineSelected.embedding sourceIndex ∈
              wz2PaperFullFiberIndices fine coarse
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
            input.exists_selectedEdge_of_packetCell schedule producer
              sourceData.1 sourceData.2
          with ⟨selectedEdge, selectedEdgeMem, _parentEq, fineCellEq⟩
        have selectedEdgeTerminal :=
          producer.output.good.selectedEdges_subset selectedEdgeMem
        constructor
        · change
            input.coarseCellOf edge.2 ∈
              producer.initial.exactification.incidence.activeCoarseCells
                producer.core.ranges.terminalEdges
          apply Finset.mem_image.mpr
          refine ⟨selectedEdge, selectedEdgeTerminal, ?_⟩
          unfold PureWZ2Prop62FourDegreeIncidenceData.edgeCoarseCell
          rw [producer.initial.exactification.incidence_coarseCellOf_eq,
            fineCellEq]
        · exact
            ⟨input.fine_cell_containment edge.2 inputFineCell,
              by
                rw [
                  producer.families.restriction.coarseSelected.tube_eq
                ]
                exact
                  input.parent_cell_containment
                    (producer.families.restriction.coarseSelected.embedding
                      edge.1)
                    edge.2
                    (producer.families.restriction.fineSelected.embedding
                      sourceIndex)
                    inputFineCell ambientFiber wholeOriginal⟩
      exact_fine_multiplicity := by
        intro edge edgeMem
        rcases (Finset.mem_filter.mp edgeMem).2 with
          ⟨sourceIndex, sourceMem⟩
        have sourceData := Finset.mem_filter.mp sourceMem
        rcases
            input.exists_selectedEdge_of_packetCell schedule producer
              sourceData.1 sourceData.2
          with ⟨selectedEdge, selectedEdgeMem, edgeParent, fineCellEq⟩
        rcases producer.output.output.exact_fine selectedEdge selectedEdgeMem with
          ⟨selectedParent, selectedParentEq, cardEq⟩
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
              (FrozenCoarseShading.terminalParentsAtCoarseCell
                input producer.initial.multiplicity
                producer.initial.parentClass producer.initial.treeCleanup
                producer.initial.exactification producer.initial.parentDegree
                producer.core producer.families cell).card ∧
            (FrozenCoarseShading.terminalParentsAtCoarseCell
                input producer.initial.multiplicity
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
          parentConstantLe outputParentFinite
      rescaled_fiber_input :=
        input.terminalMetricFiberRescalingInput schedule producer
          terminalRescaling
      packet_density := by
        intro parent
        have density := producer.output.output.packet_density parent
        change
          densityConstant *
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

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
