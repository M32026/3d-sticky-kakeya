import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62BalancingUnionBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PacketCellExactification

/-!
# Proposition 6.2: the exact fine shading after balancing

For a good exact-balancing sample, the tube families remain unchanged.
For each fine tube, retain precisely the whole fixed cells attached to
selected packet-cell edges for which that tube was one of the previously
chosen `muFine` incidences.

The resulting shading is cubical and is a subshading of the source shading.
For every surviving packet-cell edge `(P,q)`, exactly `muFine` members of the
complete genuine metric fiber over `P` contain the whole cell `q`.
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
    {TreeLabel : Type*} [DecidableEq TreeLabel]
    {initialEdges : Finset exactification.incidence.Edge}
    {bins :
      exactification.incidence.ThreeDegreeBinningData initialEdges}
    {parentLower fineLower parentCoarseLower coarseLower : ℕ}
    {treeLabels : Finset TreeLabel}
    {treeBad :
      Finset exactification.incidence.Edge → TreeLabel → Prop}
    {treeCharge : TreeLabel → ℕ}
    (ranges :
      exactification.incidence.FourDegreeRangeData
        bins parentLower fineLower parentCoarseLower coarseLower
        treeLabels treeBad treeCharge)
    {degreeLoss : ℕ}
    (good :
      ranges.GoodBalancingSampleData degreeLoss)

/-- Reindex an incidence edge by the literal reference-pair finset. -/
def referencePairOfEdge
    (edge : exactification.incidence.Edge) :
    {pair //
      pair ∈
        input.referencePairs
          multiplicity parentClass treeCleanup} :=
  ⟨edge.1, by
    rw [← exactification.incidence_edgePool_eq]
    exact edge.2⟩

def sourceSelectedOnEdge
    (source : Fin fine.card)
    (edge : exactification.incidence.Edge) : Prop :=
  source ∈
    exactification.selectedSources
      (input.referencePairOfEdge
        multiplicity parentClass treeCleanup exactification edge)

/-- Whole selected fine cells retained in one source-tube shading. -/
def retainedCellsForSource
    (source : Fin fine.card) :
    Finset WZ2PaperCellIndex :=
  ((ranges.selectedEdges good.sample).filter fun edge =>
      input.sourceSelectedOnEdge
        multiplicity parentClass treeCleanup exactification
        source edge).image exactification.incidence.edgeFineCell

/-- The final fine shading on the unchanged fine family. -/
def exactFineShading : WZ1PaperTubeShading fine where
  carrier source :=
    wz2RetainedCellsUnion delta
      (input.retainedCellsForSource
        multiplicity parentClass treeCleanup exactification
        ranges good source)
  measurable_carrier source :=
    wz2RetainedCellsUnion_measurable
  subset_body source := by
    intro point pointMem
    rcases Set.mem_iUnion₂.mp pointMem with
      ⟨cell, cellMem, pointCell⟩
    rcases Finset.mem_image.mp cellMem with
      ⟨edge, edgeMem, edgeCell⟩
    have sourceSelected :
        input.sourceSelectedOnEdge
          multiplicity parentClass treeCleanup exactification
          source edge :=
      (Finset.mem_filter.mp edgeMem).2
    have sourceMem :
        source ∈
          exactification.selectedSources
            (input.referencePairOfEdge
              multiplicity parentClass treeCleanup exactification edge) :=
      sourceSelected
    have cubeSubset :
        wz1PaperGridCube delta
            (input.referencePairOfEdge
              multiplicity parentClass treeCleanup
              exactification edge).1.2 ⊆
          sourceShading.carrier source :=
      PacketCellExactificationData.selectedCell_subset_carrier
        input multiplicity parentClass treeCleanup
        exactification
        (input.referencePairOfEdge
          multiplicity parentClass treeCleanup exactification edge)
        sourceMem
    have pointSource : point ∈ sourceShading.carrier source := by
      apply cubeSubset
      change
        point ∈ wz1PaperGridCube delta
          (exactification.incidence.edgeFineCell edge)
      rw [edgeCell]
      exact pointCell
    exact sourceShading.subset_body source pointSource

namespace ExactFineShading

theorem carrier_eq
    (source : Fin fine.card) :
    (input.exactFineShading
      multiplicity parentClass treeCleanup exactification
      ranges good).carrier source =
      wz2RetainedCellsUnion delta
        (input.retainedCellsForSource
          multiplicity parentClass treeCleanup exactification
          ranges good source) := by
  rfl

theorem subshading
    (source : Fin fine.card) :
    (input.exactFineShading
      multiplicity parentClass treeCleanup exactification
      ranges good).carrier source ⊆
        sourceShading.carrier source := by
  intro point pointMem
  rcases Set.mem_iUnion₂.mp pointMem with
    ⟨cell, cellMem, pointCell⟩
  rcases Finset.mem_image.mp cellMem with
    ⟨edge, edgeMem, edgeCell⟩
  have sourceMem :
      source ∈
        exactification.selectedSources
          (input.referencePairOfEdge
            multiplicity parentClass treeCleanup exactification edge) :=
    (Finset.mem_filter.mp edgeMem).2
  have cubeSubset :=
    PacketCellExactificationData.selectedCell_subset_carrier
      input multiplicity parentClass treeCleanup
      exactification
      (input.referencePairOfEdge
        multiplicity parentClass treeCleanup exactification edge)
      sourceMem
  apply cubeSubset
  change
    point ∈ wz1PaperGridCube delta
      (exactification.incidence.edgeFineCell edge)
  rw [edgeCell]
  exact pointCell

theorem cubical :
    WZ1PaperIsCubicalShading
      (input.exactFineShading
        multiplicity parentClass treeCleanup exactification
        ranges good) := by
  intro source point pointMem
  rcases Set.mem_iUnion₂.mp pointMem with
    ⟨cell, cellMem, pointCell⟩
  have pointIndex :
      wz1PaperGridIndex delta point = cell :=
    (mem_wz1PaperGridCube delta cell point).mp pointCell
  intro other otherMem
  have otherCell :
      other ∈ wz1PaperGridCube delta cell := by
    apply
      (mem_wz1PaperGridCube delta cell other).mpr
    exact
      ((mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) other).mp
          otherMem).trans pointIndex
  exact Set.mem_iUnion₂.mpr ⟨cell, cellMem, otherCell⟩

theorem sourceSelectedOnEdge_fullFiber
    {source : Fin fine.card}
    {edge : exactification.incidence.Edge}
    (sourceSelected :
      input.sourceSelectedOnEdge
        multiplicity parentClass treeCleanup exactification
        source edge) :
    source ∈
      wz2PaperFullFiberIndices fine coarse
        (exactification.incidence.edgeParent edge) := by
  have sourceMem :
      source ∈
        exactification.selectedSources
          (input.referencePairOfEdge
            multiplicity parentClass treeCleanup exactification edge) :=
    sourceSelected
  simpa [
    referencePairOfEdge,
    PureWZ2Prop62FourDegreeIncidenceData.edgeParent
  ] using
    PacketCellExactificationData.selectedSource_mem_fullFiber
      input multiplicity parentClass treeCleanup
      exactification
      (input.referencePairOfEdge
        multiplicity parentClass treeCleanup exactification edge)
      sourceMem

theorem selectedEdge_cell_subset_carrier
    {source : Fin fine.card}
    {edge : exactification.incidence.Edge}
    (edgeSelected : edge ∈ ranges.selectedEdges good.sample)
    (sourceSelected :
      input.sourceSelectedOnEdge
        multiplicity parentClass treeCleanup exactification
        source edge) :
    wz1PaperGridCube delta
        (exactification.incidence.edgeFineCell edge) ⊆
      (input.exactFineShading
        multiplicity parentClass treeCleanup exactification
        ranges good).carrier source := by
  intro point pointMem
  apply Set.mem_iUnion₂.mpr
  refine
    ⟨exactification.incidence.edgeFineCell edge, ?_, pointMem⟩
  apply Finset.mem_image.mpr
  exact
    ⟨edge,
      Finset.mem_filter.mpr
        ⟨edgeSelected, sourceSelected⟩,
      rfl⟩

theorem carrier_cell_implies_sourceSelected
    {source : Fin fine.card}
    {edge : exactification.incidence.Edge}
    (edgeSelected : edge ∈ ranges.selectedEdges good.sample)
    (sourceFiber :
      source ∈
        wz2PaperFullFiberIndices fine coarse
          (exactification.incidence.edgeParent edge))
    (cellSubset :
      wz1PaperGridCube delta
          (exactification.incidence.edgeFineCell edge) ⊆
        (input.exactFineShading
          multiplicity parentClass treeCleanup exactification
          ranges good).carrier source) :
    input.sourceSelectedOnEdge
      multiplicity parentClass treeCleanup exactification
      source edge := by
  let cell :=
    exactification.incidence.edgeFineCell edge
  let point := cellCorner delta cell
  have pointCell :
      point ∈ wz1PaperGridCube delta cell :=
    cellCorner_mem_gridCube input.delta_pos cell
  have pointCarrier :
      point ∈
        (input.exactFineShading
          multiplicity parentClass treeCleanup exactification
          ranges good).carrier source :=
    cellSubset pointCell
  rcases Set.mem_iUnion₂.mp pointCarrier with
    ⟨otherCell, otherCellMem, pointOtherCell⟩
  rcases Finset.mem_image.mp otherCellMem with
    ⟨otherEdge, otherEdgeMem, otherEdgeCell⟩
  have otherSelected :
      otherEdge ∈ ranges.selectedEdges good.sample :=
    (Finset.mem_filter.mp otherEdgeMem).1
  have sourceOtherSelected :
      input.sourceSelectedOnEdge
        multiplicity parentClass treeCleanup exactification
        source otherEdge :=
    (Finset.mem_filter.mp otherEdgeMem).2
  have cellEq : otherCell = cell := by
    have firstIndex :
        wz1PaperGridIndex delta point = cell :=
      (mem_wz1PaperGridCube delta cell point).mp pointCell
    have secondIndex :
        wz1PaperGridIndex delta point = otherCell :=
      (mem_wz1PaperGridCube delta otherCell point).mp pointOtherCell
    exact secondIndex.symm.trans firstIndex
  have edgeFineEq :
      exactification.incidence.edgeFineCell otherEdge =
        exactification.incidence.edgeFineCell edge := by
    rw [otherEdgeCell, cellEq]
  have sourceOtherFiber :
      source ∈
        wz2PaperFullFiberIndices fine coarse
          (exactification.incidence.edgeParent otherEdge) :=
    ExactFineShading.sourceSelectedOnEdge_fullFiber
      input
      multiplicity parentClass treeCleanup exactification
      sourceOtherSelected
  have parentEq :
      exactification.incidence.edgeParent otherEdge =
        exactification.incidence.edgeParent edge := by
    have otherCover :=
      (mem_wz2PaperFullFiberIndices_iff
        (exactification.incidence.edgeParent otherEdge) source).mp
          sourceOtherFiber
    have edgeCover :=
      (mem_wz2PaperFullFiberIndices_iff
        (exactification.incidence.edgeParent edge) source).mp
          sourceFiber
    have otherCanonical :=
      cover.toWZ1PaperTubeCover.parent_unique
        source (exactification.incidence.edgeParent otherEdge)
        otherCover
    have edgeCanonical :=
      cover.toWZ1PaperTubeCover.parent_unique
        source (exactification.incidence.edgeParent edge)
        edgeCover
    exact otherCanonical.trans edgeCanonical.symm
  have edgeEq : otherEdge = edge := by
    apply Subtype.ext
    apply Prod.ext
    · exact parentEq
    · exact edgeFineEq
  rw [← edgeEq]
  exact sourceOtherSelected

/-- Fine sources in the complete metric fiber whose final shading contains
the selected whole cell. -/
def finalPacketCellSources
    (edge : exactification.incidence.Edge) :
    Finset (Fin fine.card) :=
  (wz2PaperFullFiberIndices fine coarse
      (exactification.incidence.edgeParent edge)).filter fun source =>
    wz1PaperGridCube delta
        (exactification.incidence.edgeFineCell edge) ⊆
      (input.exactFineShading
        multiplicity parentClass treeCleanup exactification
        ranges good).carrier source

theorem finalPacketCellSources_eq_selectedSources
    {edge : exactification.incidence.Edge}
    (edgeSelected : edge ∈ ranges.selectedEdges good.sample) :
    ExactFineShading.finalPacketCellSources
        input
        multiplicity parentClass treeCleanup exactification
        ranges good edge =
      exactification.selectedSources
        (input.referencePairOfEdge
          multiplicity parentClass treeCleanup exactification edge) := by
  ext source
  constructor
  · intro sourceMem
    have sourceData := Finset.mem_filter.mp sourceMem
    exact
      ExactFineShading.carrier_cell_implies_sourceSelected
        input
        multiplicity parentClass treeCleanup exactification
        ranges good edgeSelected sourceData.1 sourceData.2
  · intro sourceMem
    apply Finset.mem_filter.mpr
    refine
      ⟨ExactFineShading.sourceSelectedOnEdge_fullFiber
          input
          multiplicity parentClass treeCleanup exactification
          sourceMem,
        ?_⟩
    exact
      ExactFineShading.selectedEdge_cell_subset_carrier
        input
        multiplicity parentClass treeCleanup exactification
        ranges good edgeSelected sourceMem

theorem exact_fine_multiplicity
    {edge : exactification.incidence.Edge}
    (edgeSelected : edge ∈ ranges.selectedEdges good.sample) :
    (ExactFineShading.finalPacketCellSources
      input
      multiplicity parentClass treeCleanup exactification
      ranges good edge).card =
        multiplicity.muFine := by
  rw [ExactFineShading.finalPacketCellSources_eq_selectedSources
    input
    multiplicity parentClass treeCleanup exactification
    ranges good edgeSelected]
  exact exactification.selectedSources_card _

theorem ambient_union_inter_coarseCube
    (coarseCell : ranges.ActiveCoarseCell) :
    (input.exactFineShading
        multiplicity parentClass treeCleanup exactification
        ranges good).union ∩
        wz1PaperGridCube rho coarseCell.1 =
      wz2RetainedCellsUnion delta
        (ranges.selectedFineCellsAt good.sample coarseCell.1) := by
  ext point
  constructor
  · intro pointData
    rcases pointData.1 with ⟨source, pointCarrier⟩
    rcases Set.mem_iUnion₂.mp pointCarrier with
      ⟨cell, cellMem, pointCell⟩
    rcases Finset.mem_image.mp cellMem with
      ⟨edge, edgeMem, edgeCell⟩
    have edgeSelected :
        edge ∈ ranges.selectedEdges good.sample :=
      (Finset.mem_filter.mp edgeMem).1
    have sourceSelected :
        input.sourceSelectedOnEdge
          multiplicity parentClass treeCleanup exactification
          source edge :=
      (Finset.mem_filter.mp edgeMem).2
    have sourceMem :
        source ∈
          exactification.selectedSources
            (input.referencePairOfEdge
              multiplicity parentClass treeCleanup exactification edge) :=
      sourceSelected
    have packetData :=
      exactification.selectedSources_subset
        (input.referencePairOfEdge
          multiplicity parentClass treeCleanup exactification edge)
        sourceMem
    have packetMem :=
      (input.mem_packetCellSources_iff
        (exactification.incidence.edgeParent edge)
        (exactification.incidence.edgeFineCell edge)
        source).mp <| by
          simpa [
            referencePairOfEdge,
            PureWZ2Prop62FourDegreeIncidenceData.edgeParent,
            PureWZ2Prop62FourDegreeIncidenceData.edgeFineCell
          ] using packetData
    have fineCellMem :
        exactification.incidence.edgeFineCell edge ∈
          input.fineCells :=
      packetMem.1
    have fineContainment :
        wz1PaperGridCube delta
            (exactification.incidence.edgeFineCell edge) ⊆
          wz1PaperGridCube rho
            (input.coarseCellOf
              (exactification.incidence.edgeFineCell edge)) :=
      input.fine_cell_containment
        (exactification.incidence.edgeFineCell edge) fineCellMem
    have pointFine :
        point ∈ wz1PaperGridCube delta
          (exactification.incidence.edgeFineCell edge) := by
      rw [edgeCell]
      exact pointCell
    have pointOwnCoarse :
        point ∈ wz1PaperGridCube rho
          (exactification.incidence.edgeCoarseCell edge) := by
      unfold PureWZ2Prop62FourDegreeIncidenceData.edgeCoarseCell
      rw [exactification.incidence_coarseCellOf_eq]
      exact fineContainment pointFine
    have edgeCoarse :
        exactification.incidence.edgeCoarseCell edge =
          coarseCell.1 := by
      have firstIndex :
          wz1PaperGridIndex rho point =
            exactification.incidence.edgeCoarseCell edge :=
        (mem_wz1PaperGridCube rho
          (exactification.incidence.edgeCoarseCell edge) point).mp
            pointOwnCoarse
      have secondIndex :
          wz1PaperGridIndex rho point = coarseCell.1 :=
        (mem_wz1PaperGridCube rho coarseCell.1 point).mp
          pointData.2
      exact firstIndex.symm.trans secondIndex
    have selectedCellMem :
        exactification.incidence.edgeFineCell edge ∈
          ranges.selectedFineCellsAt good.sample coarseCell.1 :=
      Finset.mem_image.mpr
        ⟨edge,
          Finset.mem_filter.mpr
            ⟨edgeSelected, edgeCoarse⟩,
          rfl⟩
    exact
      Set.mem_iUnion₂.mpr
        ⟨exactification.incidence.edgeFineCell edge,
          selectedCellMem, pointFine⟩
  · intro pointMem
    rcases Set.mem_iUnion₂.mp pointMem with
      ⟨fineCell, fineCellMem, pointFine⟩
    rcases Finset.mem_image.mp fineCellMem with
      ⟨edge, edgeMem, edgeFine⟩
    have edgeSelected :
        edge ∈ ranges.selectedEdges good.sample :=
      (Finset.mem_filter.mp edgeMem).1
    have edgeCoarse :
        exactification.incidence.edgeCoarseCell edge =
          coarseCell.1 :=
      (Finset.mem_filter.mp edgeMem).2
    have selectedSourcesNonempty :
        (exactification.selectedSources
          (input.referencePairOfEdge
            multiplicity parentClass treeCleanup exactification edge)).Nonempty := by
      apply Finset.card_pos.mp
      rw [exactification.selectedSources_card]
      exact multiplicity.muFine_pos
    rcases selectedSourcesNonempty with ⟨source, sourceMem⟩
    have wholeCell :=
      ExactFineShading.selectedEdge_cell_subset_carrier
        input
        multiplicity parentClass treeCleanup exactification
        ranges good edgeSelected sourceMem
    have pointCarrier :
        point ∈
          (input.exactFineShading
            multiplicity parentClass treeCleanup exactification
            ranges good).carrier source := by
      apply wholeCell
      rw [edgeFine]
      exact pointFine
    have packetData :=
      exactification.selectedSources_subset
        (input.referencePairOfEdge
          multiplicity parentClass treeCleanup exactification edge)
        sourceMem
    have packetMem :=
      (input.mem_packetCellSources_iff
        (exactification.incidence.edgeParent edge)
        (exactification.incidence.edgeFineCell edge)
        source).mp <| by
          simpa [
            referencePairOfEdge,
            PureWZ2Prop62FourDegreeIncidenceData.edgeParent,
            PureWZ2Prop62FourDegreeIncidenceData.edgeFineCell
          ] using packetData
    have fineContainment :=
      input.fine_cell_containment
        (exactification.incidence.edgeFineCell edge) packetMem.1
    have pointOwnCoarse :
        point ∈ wz1PaperGridCube rho
          (exactification.incidence.edgeCoarseCell edge) := by
      unfold PureWZ2Prop62FourDegreeIncidenceData.edgeCoarseCell
      rw [exactification.incidence_coarseCellOf_eq]
      apply fineContainment
      rw [edgeFine]
      exact pointFine
    exact
      ⟨⟨source, pointCarrier⟩,
        by simpa [edgeCoarse] using pointOwnCoarse⟩

theorem ambient_union_inter_coarseCube_volume
    (coarseCell : ranges.ActiveCoarseCell) :
    volume
        ((input.exactFineShading
            multiplicity parentClass treeCleanup exactification
            ranges good).union ∩
          wz1PaperGridCube rho coarseCell.1) =
      (ranges.commonFineCellCount : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  rw [ExactFineShading.ambient_union_inter_coarseCube
    input
    multiplicity parentClass treeCleanup exactification
    ranges good coarseCell]
  unfold wz2RetainedCellsUnion
  rw [wz1PaperGridCube_volume_biUnion
    input.delta_pos
    (ranges.selectedFineCellsAt good.sample coarseCell.1)]
  rw [good.exact_fine_cell_count coarseCell]

end ExactFineShading

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
