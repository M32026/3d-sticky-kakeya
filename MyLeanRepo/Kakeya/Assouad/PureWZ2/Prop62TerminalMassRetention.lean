import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TerminalFiberCWA

/-!
# Proposition 6.2: exact terminal mass retention

This module converts the discrete retention certificates of the four-degree
construction into one explicit mass inequality.

For a cubical input shading, total shaded mass is exactly the number of
positive packet-cell incidences times the fixed `delta`-cube volume.  For the
final shading, total mass is exactly `muFine` times the number of selected
terminal edges times the same cube volume.

The intermediate coefficient is the literal product of:

* the fine-multiplicity dyadic bin count;
* the parent-weight and fiber-cardinality bin counts;
* the one-pass parent-tree loss;
* exactification loss `2`;
* the three ordered degree-bin counts;
* simultaneous peeling loss `2`;
* the balancing lower-tail loss.

No logarithmic asymptotic absorption is asserted here.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

private theorem card_relation_eq_sum_left
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (left : Finset α) (right : Finset β)
    (relation : α → β → Prop) [DecidableRel relation] :
    ((left ×ˢ right).filter fun pair =>
        relation pair.1 pair.2).card =
      ∑ first ∈ left,
        (right.filter fun second =>
          relation first second).card := by
  rw [Finset.card_filter, Finset.sum_product]
  simp_rw [Finset.card_filter]

private theorem card_relation_eq_sum_right
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (left : Finset α) (right : Finset β)
    (relation : α → β → Prop) [DecidableRel relation] :
    ((left ×ˢ right).filter fun pair =>
        relation pair.1 pair.2).card =
      ∑ second ∈ right,
        (left.filter fun first =>
          relation first second).card := by
  rw [Finset.card_filter, Finset.sum_product]
  rw [Finset.sum_comm]
  simp_rw [Finset.card_filter]

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

/-- Active fixed cells whose whole cube lies in one input tube shading. -/
def sourceCellsForSource
    (source : Fin fine.card) :
    Finset WZ2PaperCellIndex :=
  input.fineCells.filter fun cell =>
    wz1PaperGridCube delta cell ⊆ sourceShading.carrier source

theorem source_carrier_eq_cellsUnion
    (source : Fin fine.card) :
    sourceShading.carrier source =
      wz2RetainedCellsUnion delta
        (input.sourceCellsForSource source) := by
  apply Set.Subset.antisymm
  · intro point pointCarrier
    let cell := wz1PaperGridIndex delta point
    have pointCell :
        point ∈ wz1PaperGridCube delta cell :=
      (mem_wz1PaperGridCube delta cell point).mpr rfl
    have pointBody :
        point ∈ wz1PaperTubeCarrier (fine.tube source) :=
      sourceShading.subset_body source pointCarrier
    have cellWindow :
        cell ∈ wz1PaperGridIndicesInWindow delta input.delta_pos :=
      paper_point_gridIndex_in_window input.delta_pos pointBody.2
    have cellActive :
        cell ∈ wz1PaperActiveCells sourceShading input.delta_pos := by
      rw [mem_wz1PaperActiveCells]
      exact
        ⟨cellWindow,
          ⟨point, ⟨source, pointCarrier⟩, pointCell⟩⟩
    have cellMem : cell ∈ input.fineCells := by
      rw [input.fineCells_eq]
      exact cellActive
    have wholeCell :
        wz1PaperGridCube delta cell ⊆
          sourceShading.carrier source :=
      input.cubical source point pointCarrier
    exact
      Set.mem_iUnion₂.mpr
        ⟨cell,
          Finset.mem_filter.mpr ⟨cellMem, wholeCell⟩,
          pointCell⟩
  · intro point pointMem
    rcases Set.mem_iUnion₂.mp pointMem with
      ⟨cell, cellMem, pointCell⟩
    exact (Finset.mem_filter.mp cellMem).2 pointCell

theorem source_carrier_volume_eq
    (source : Fin fine.card) :
    volume (sourceShading.carrier source) =
      ((input.sourceCellsForSource source).card : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  rw [input.source_carrier_eq_cellsUnion source]
  exact
    wz1PaperGridCube_volume_biUnion input.delta_pos
      (input.sourceCellsForSource source)

theorem sourcePairCells_image
    (source : Fin fine.card) :
    Finset.image Prod.snd
        (input.positivePairs.filter fun pair =>
          source ∈ input.packetCellSources pair.1 pair.2) =
      input.sourceCellsForSource source := by
  ext cell
  constructor
  · intro cellImage
    rcases Finset.mem_image.mp cellImage with
      ⟨pair, pairMem, pairCell⟩
    have relationData := Finset.mem_filter.mp pairMem
    have packetData :=
      (input.mem_packetCellSources_iff
        pair.1 pair.2 source).mp relationData.2
    subst cell
    exact
      Finset.mem_filter.mpr
        ⟨packetData.1, packetData.2.2⟩
  · intro cellMem
    have cellData := Finset.mem_filter.mp cellMem
    let parent := cover.toWZ1PaperTubeCover.parent source
    have sourceFiber :
        source ∈ wz2PaperFullFiberIndices fine coarse parent :=
      (mem_wz2PaperFullFiberIndices_iff parent source).mpr
        (cover.toWZ1PaperTubeCover.parent_covers source)
    have sourcePacket :
        source ∈ input.packetCellSources parent cell :=
      (input.mem_packetCellSources_iff parent cell source).mpr
        ⟨cellData.1, sourceFiber, cellData.2⟩
    have pairPositive :
        (parent, cell) ∈ input.positivePairs := by
      apply (input.mem_positivePairs_iff (parent, cell)).mpr
      exact
        ⟨cellData.1,
          Finset.card_pos.mpr ⟨source, sourcePacket⟩⟩
    exact
      Finset.mem_image.mpr
        ⟨(parent, cell),
          Finset.mem_filter.mpr
            ⟨pairPositive, sourcePacket⟩,
          rfl⟩

theorem sourcePairCells_second_injective
    (source : Fin fine.card) :
    Set.InjOn
      (fun pair : Fin coarse.card × WZ2PaperCellIndex => pair.2)
      (↑(input.positivePairs.filter fun pair =>
        source ∈ input.packetCellSources pair.1 pair.2) :
        Set (Fin coarse.card × WZ2PaperCellIndex)) := by
  intro first firstMem second secondMem cellEq
  have firstData :=
    (input.mem_packetCellSources_iff
      first.1 first.2 source).mp (Finset.mem_filter.mp firstMem).2
  have secondData :=
    (input.mem_packetCellSources_iff
      second.1 second.2 source).mp (Finset.mem_filter.mp secondMem).2
  have firstCover :=
    (mem_wz2PaperFullFiberIndices_iff first.1 source).mp
      firstData.2.1
  have secondCover :=
    (mem_wz2PaperFullFiberIndices_iff second.1 source).mp
      secondData.2.1
  have parentEq : first.1 = second.1 :=
    (cover.toWZ1PaperTubeCover.parent_unique
      source first.1 firstCover).trans
      (cover.toWZ1PaperTubeCover.parent_unique
        source second.1 secondCover).symm
  exact Prod.ext parentEq cellEq

theorem sourceCellsForSource_card
    (source : Fin fine.card) :
    (input.sourceCellsForSource source).card =
      (input.positivePairs.filter fun pair =>
        source ∈ input.packetCellSources pair.1 pair.2).card := by
  rw [← input.sourcePairCells_image source]
  exact
    Finset.card_image_iff.mpr
      (input.sourcePairCells_second_injective source)

theorem positiveMultiplicityCount_eq_sourceCellCount :
    (∑ pair ∈ input.positivePairs,
        input.packetCellMultiplicity pair) =
      ∑ source : Fin fine.card,
        (input.sourceCellsForSource source).card := by
  let sources : Finset (Fin fine.card) := Finset.univ
  let relation :
      (Fin coarse.card × WZ2PaperCellIndex) →
        Fin fine.card → Prop :=
    fun pair source =>
      source ∈ input.packetCellSources pair.1 pair.2
  have leftCount :
      ((input.positivePairs ×ˢ sources).filter fun incidence =>
          relation incidence.1 incidence.2).card =
        ∑ pair ∈ input.positivePairs,
          (sources.filter fun source =>
            relation pair source).card :=
    card_relation_eq_sum_left input.positivePairs sources relation
  have rightCount :
      ((input.positivePairs ×ˢ sources).filter fun incidence =>
          relation incidence.1 incidence.2).card =
        ∑ source ∈ sources,
          (input.positivePairs.filter fun pair =>
            relation pair source).card :=
    card_relation_eq_sum_right input.positivePairs sources relation
  calc
    (∑ pair ∈ input.positivePairs,
        input.packetCellMultiplicity pair) =
        ∑ pair ∈ input.positivePairs,
          (sources.filter fun source =>
            relation pair source).card := by
      apply Finset.sum_congr rfl
      intro pair pairMem
      change
        (input.packetCellSources pair.1 pair.2).card =
          (Finset.univ.filter fun source =>
            source ∈ input.packetCellSources pair.1 pair.2).card
      congr 1
      ext source
      simp
    _ =
        ((input.positivePairs ×ˢ sources).filter fun incidence =>
          relation incidence.1 incidence.2).card :=
      leftCount.symm
    _ =
        ∑ source ∈ sources,
          (input.positivePairs.filter fun pair =>
            relation pair source).card :=
      rightCount
    _ =
        ∑ source : Fin fine.card,
          (input.sourceCellsForSource source).card := by
      apply Finset.sum_congr rfl
      intro source _sourceMem
      exact (input.sourceCellsForSource_card source).symm

theorem sourceShading_mass_eq :
    sourceShading.mass =
      ((∑ pair ∈ input.positivePairs,
        input.packetCellMultiplicity pair : ℕ) : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  calc
    sourceShading.mass =
        ∑ source : Fin fine.card,
          ((input.sourceCellsForSource source).card : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
      apply Finset.sum_congr rfl
      intro source _sourceMem
      exact input.source_carrier_volume_eq source
    _ =
        (∑ source : Fin fine.card,
          ((input.sourceCellsForSource source).card : ENNReal)) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
      rw [Finset.sum_mul]
    _ =
        ((∑ source : Fin fine.card,
          (input.sourceCellsForSource source).card : ℕ) : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
      rw [Nat.cast_sum]
    _ =
        ((∑ pair ∈ input.positivePairs,
          input.packetCellMultiplicity pair : ℕ) : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
      rw [input.positiveMultiplicityCount_eq_sourceCellCount]

namespace ExactFineShading

theorem edgeFineCell_injective_on_sourceSelected
    (source : Fin fine.card) :
    Set.InjOn exactification.incidence.edgeFineCell
      ((core.ranges.selectedEdges good.sample).filter fun edge =>
        input.sourceSelectedOnEdge
          multiplicity parentClass treeCleanup exactification
            source edge) := by
  intro first firstMem second secondMem fineEq
  have firstSelected := (Finset.mem_filter.mp firstMem).2
  have secondSelected := (Finset.mem_filter.mp secondMem).2
  have firstFiber :=
    ExactFineShading.sourceSelectedOnEdge_fullFiber
      input multiplicity parentClass treeCleanup exactification
        firstSelected
  have secondFiber :=
    ExactFineShading.sourceSelectedOnEdge_fullFiber
      input multiplicity parentClass treeCleanup exactification
        secondSelected
  have firstCover :=
    (mem_wz2PaperFullFiberIndices_iff
      (exactification.incidence.edgeParent first) source).mp firstFiber
  have secondCover :=
    (mem_wz2PaperFullFiberIndices_iff
      (exactification.incidence.edgeParent second) source).mp secondFiber
  have parentEq :
      exactification.incidence.edgeParent first =
        exactification.incidence.edgeParent second :=
    (cover.toWZ1PaperTubeCover.parent_unique
      source (exactification.incidence.edgeParent first)
        firstCover).trans
      (cover.toWZ1PaperTubeCover.parent_unique
        source (exactification.incidence.edgeParent second)
          secondCover).symm
  apply Subtype.ext
  apply Prod.ext parentEq fineEq

theorem retainedCellsForSource_card_global
    (source : Fin fine.card) :
    (input.retainedCellsForSource
      multiplicity parentClass treeCleanup exactification
        core.ranges good source).card =
      ((core.ranges.selectedEdges good.sample).filter fun edge =>
        input.sourceSelectedOnEdge
          multiplicity parentClass treeCleanup exactification
            source edge).card := by
  unfold retainedCellsForSource
  exact
    Finset.card_image_iff.mpr
      (ExactFineShading.edgeFineCell_injective_on_sourceSelected
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good source)

theorem selectedSourceFilter_card
    {edge : exactification.incidence.Edge}
    (edgeSelected :
      edge ∈ core.ranges.selectedEdges good.sample) :
    ((Finset.univ : Finset (Fin fine.card)).filter fun source =>
      input.sourceSelectedOnEdge
        multiplicity parentClass treeCleanup exactification
          source edge).card =
      multiplicity.muFine := by
  have filterEq :
      ((Finset.univ : Finset (Fin fine.card)).filter fun source =>
        input.sourceSelectedOnEdge
          multiplicity parentClass treeCleanup exactification
            source edge) =
        exactification.selectedSources
          (input.referencePairOfEdge
            multiplicity parentClass treeCleanup exactification edge) := by
    ext source
    simp [sourceSelectedOnEdge]
  rw [filterEq, exactification.selectedSources_card]

theorem global_retained_cell_count :
    (∑ source : Fin fine.card,
        (input.retainedCellsForSource
          multiplicity parentClass treeCleanup exactification
            core.ranges good source).card) =
      multiplicity.muFine *
        (core.ranges.selectedEdges good.sample).card := by
  let edges := core.ranges.selectedEdges good.sample
  let sources : Finset (Fin fine.card) := Finset.univ
  let relation :
      exactification.incidence.Edge → Fin fine.card → Prop :=
    fun edge source =>
      input.sourceSelectedOnEdge
        multiplicity parentClass treeCleanup exactification
          source edge
  have rightCount :
      ((edges ×ˢ sources).filter fun incidence =>
          relation incidence.1 incidence.2).card =
        ∑ source ∈ sources,
          (edges.filter fun edge =>
            relation edge source).card :=
    card_relation_eq_sum_right edges sources relation
  have leftCount :
      ((edges ×ˢ sources).filter fun incidence =>
          relation incidence.1 incidence.2).card =
        ∑ edge ∈ edges,
          (sources.filter fun source =>
            relation edge source).card :=
    card_relation_eq_sum_left edges sources relation
  calc
    (∑ source : Fin fine.card,
        (input.retainedCellsForSource
          multiplicity parentClass treeCleanup exactification
            core.ranges good source).card) =
        ∑ source ∈ sources,
          (edges.filter fun edge =>
            relation edge source).card := by
      apply Finset.sum_congr rfl
      intro source _sourceMem
      exact
        ExactFineShading.retainedCellsForSource_card_global
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good source
    _ =
        ((edges ×ˢ sources).filter fun incidence =>
          relation incidence.1 incidence.2).card :=
      rightCount.symm
    _ =
        ∑ edge ∈ edges,
          (sources.filter fun source =>
            relation edge source).card :=
      leftCount
    _ = ∑ _edge ∈ edges, multiplicity.muFine := by
      apply Finset.sum_congr rfl
      intro edge edgeMem
      exact
        ExactFineShading.selectedSourceFilter_card
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good edgeMem
    _ =
        multiplicity.muFine * edges.card := by
      simp
      ring

theorem ambientExactShading_mass_eq :
    (input.ambientExactShading
      multiplicity parentClass treeCleanup exactification
        core.ranges good).mass =
      (multiplicity.muFine *
        (core.ranges.selectedEdges good.sample).card : ℕ) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  calc
    (input.ambientExactShading
      multiplicity parentClass treeCleanup exactification
        core.ranges good).mass =
        ∑ source : Fin fine.card,
          ((input.retainedCellsForSource
            multiplicity parentClass treeCleanup exactification
              core.ranges good source).card : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
      apply Finset.sum_congr rfl
      intro source _sourceMem
      rw [ExactFineShading.carrier_eq
        input multiplicity parentClass treeCleanup exactification
          core.ranges good source]
      exact
        wz1PaperGridCube_volume_biUnion input.delta_pos
          (input.retainedCellsForSource
            multiplicity parentClass treeCleanup exactification
              core.ranges good source)
    _ =
        (∑ source : Fin fine.card,
          ((input.retainedCellsForSource
            multiplicity parentClass treeCleanup exactification
              core.ranges good source).card : ENNReal)) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
      rw [Finset.sum_mul]
    _ =
        ((∑ source : Fin fine.card,
          (input.retainedCellsForSource
            multiplicity parentClass treeCleanup exactification
              core.ranges good source).card : ℕ) : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
      rw [Nat.cast_sum]
    _ =
        (multiplicity.muFine *
          (core.ranges.selectedEdges good.sample).card : ℕ) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
      rw [ExactFineShading.global_retained_cell_count
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good]

end ExactFineShading

theorem terminalFineShading_mass_eq :
    (input.terminalFineShading
      multiplicity parentClass treeCleanup exactification
        core.ranges good families).mass =
      (multiplicity.muFine *
        (core.ranges.selectedEdges good.sample).card : ℕ) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  rw [TerminalFineShading.mass_eq_ambient
    input multiplicity parentClass treeCleanup exactification
      core.ranges good families]
  exact
    ExactFineShading.ambientExactShading_mass_eq
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good

/-- The exact multiplicative loss before the logarithmic absorption step. -/
def terminalMassRetentionLoss
    (_treeCleanup :
      input.ParentTreeCleanupData
        multiplicity parentClass schedule)
    (_exactification :
      input.PacketCellExactificationData
        multiplicity parentClass _treeCleanup)
    (_parentDegree :
      input.ReferenceParentDegreeData
        multiplicity parentClass _treeCleanup _exactification)
    {bins :
      _exactification.incidence.ThreeDegreeBinningData
        _exactification.incidence.allEdges}
    {A0 : ℕ}
    (_core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass _treeCleanup
        _exactification _parentDegree bins A0)
    {degreeLoss : ℕ}
    (_good :
      _core.ranges.GoodBalancingSampleData degreeLoss) :
    ENNReal :=
  (multiplicity.binCount : ENNReal) *
    parentClass.weightBinCount *
    parentClass.fiberBinCount *
    (2 ^ (schedule.levelCount + 1) : ENNReal) *
    4 *
    bins.fineCellBin.binCount *
    bins.parentCoarseBin.binCount *
    bins.coarseCellBin.binCount *
    degreeLoss

theorem sum_referenceParentIncidenceWeight :
    (∑ parent ∈ treeCleanup.referenceParents,
        input.parentIncidenceWeight multiplicity parent) =
      ∑ pair ∈
          input.referencePairs
            multiplicity parentClass treeCleanup,
        input.packetCellMultiplicity pair := by
  change
    (∑ parent ∈ treeCleanup.referenceParents,
        ∑ pair ∈ multiplicity.selectedPairs with pair.1 = parent,
          input.packetCellMultiplicity pair) =
      ∑ pair ∈
          multiplicity.selectedPairs.filter fun pair =>
            pair.1 ∈ treeCleanup.referenceParents,
        input.packetCellMultiplicity pair
  exact
    Finset.sum_fiberwise_eq_sum_filter
      multiplicity.selectedPairs treeCleanup.referenceParents
        Prod.fst input.packetCellMultiplicity

theorem terminalEdges_card_le_balanced :
    core.ranges.terminalEdges.card ≤
      degreeLoss *
        (core.ranges.selectedEdges good.sample).card := by
  have selectedParentSum :
      (∑ parent ∈ core.ranges.terminalParents,
          core.ranges.selectedParentDegree good.sample parent) =
        (core.ranges.selectedEdges good.sample).card := by
    have fiberwise :=
      Finset.sum_card_fiberwise_eq_card_filter
        (core.ranges.selectedEdges good.sample)
        core.ranges.terminalParents
        exactification.incidence.edgeParent
    have filterEq :
        (core.ranges.selectedEdges good.sample).filter
            (fun edge =>
              exactification.incidence.edgeParent edge ∈
                core.ranges.terminalParents) =
          core.ranges.selectedEdges good.sample := by
      apply Finset.filter_true_of_mem
      intro edge edgeSelected
      have edgeTerminal := good.selectedEdges_subset edgeSelected
      rw [
        PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.terminalParents
      ]
      exact
        Finset.mem_image.mpr
          ⟨edge, edgeTerminal, rfl⟩
    simpa [
      PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.selectedParentDegree,
      PureWZ2Prop62FourDegreeIncidenceData.parentDegree,
      filterEq
    ] using fiberwise
  calc
    core.ranges.terminalEdges.card =
        ∑ parent ∈ core.ranges.terminalParents,
          exactification.incidence.parentDegree
            core.ranges.terminalEdges parent := by
      exact
        exactification.incidence.card_eq_sum_parentDegree
          core.ranges.terminalEdges
    _ ≤
        ∑ parent ∈ core.ranges.terminalParents,
          degreeLoss *
            core.ranges.selectedParentDegree good.sample parent := by
      exact
        Finset.sum_le_sum fun parent parentMem =>
          good.parent_degree_retention parent parentMem
    _ =
        degreeLoss *
          ∑ parent ∈ core.ranges.terminalParents,
            core.ranges.selectedParentDegree good.sample parent := by
      rw [Finset.mul_sum]
    _ =
        degreeLoss *
          (core.ranges.selectedEdges good.sample).card := by
      rw [selectedParentSum]

theorem sourceMultiplicityCount_le_terminal :
    ((∑ pair ∈ input.positivePairs,
        input.packetCellMultiplicity pair : ℕ) : ENNReal) ≤
      input.terminalMassRetentionLoss
          multiplicity parentClass treeCleanup exactification
            parentDegree core good *
        (multiplicity.muFine *
          (core.ranges.selectedEdges good.sample).card : ℕ) := by
  let positiveCount : ENNReal :=
    ∑ pair ∈ input.positivePairs,
      (input.packetCellMultiplicity pair : ENNReal)
  let selectedCount : ENNReal :=
    ∑ pair ∈ multiplicity.selectedPairs,
      (input.packetCellMultiplicity pair : ENNReal)
  let weightClassCount : ENNReal :=
    ∑ parent ∈ parentClass.weightClass,
      (input.parentIncidenceWeight multiplicity parent : ENNReal)
  let selectedParentCount : ENNReal :=
    ∑ parent ∈ parentClass.selectedParents,
      (input.parentIncidenceWeight multiplicity parent : ENNReal)
  let referenceCount : ENNReal :=
    ∑ parent ∈ treeCleanup.referenceParents,
      (input.parentIncidenceWeight multiplicity parent : ENNReal)
  have positiveCountEq :
      positiveCount =
        ((∑ pair ∈ input.positivePairs,
          input.packetCellMultiplicity pair : ℕ) : ENNReal) := by
    dsimp only [positiveCount]
    rw [Nat.cast_sum]
  have classRetention :
      positiveCount ≤
        (multiplicity.binCount : ENNReal) * selectedCount := by
    dsimp only [positiveCount, selectedCount]
    exact_mod_cast multiplicity.class_retention
  have selectedCountEq :
      selectedCount =
        ∑ parent ∈ input.multiplicityParents multiplicity,
          (input.parentIncidenceWeight multiplicity parent : ENNReal) := by
    dsimp only [selectedCount]
    exact_mod_cast
      (input.sum_parentIncidenceWeight multiplicity).symm
  have weightRetention :
      selectedCount ≤
        (parentClass.weightBinCount : ENNReal) *
          weightClassCount := by
    rw [selectedCountEq]
    dsimp only [weightClassCount]
    exact_mod_cast parentClass.weight_retention
  have fiberRetention :
      weightClassCount ≤
        (parentClass.fiberBinCount : ENNReal) *
          selectedParentCount := by
    exact parentClass.fiber_weight_retention
  have treeRetention :
      selectedParentCount ≤
        (2 ^ (schedule.levelCount + 1) : ENNReal) *
          referenceCount := by
    exact treeCleanup.weight_retention
  have referenceCountEq :
      referenceCount =
        ((∑ pair ∈
            input.referencePairs
              multiplicity parentClass treeCleanup,
          input.packetCellMultiplicity pair : ℕ) : ENNReal) := by
    dsimp only [referenceCount]
    exact_mod_cast
      input.sum_referenceParentIncidenceWeight
        multiplicity parentClass treeCleanup
  have exactificationRetention :
      referenceCount ≤
        2 *
          (multiplicity.muFine : ENNReal) *
          exactification.incidence.allEdges.card := by
    rw [referenceCountEq]
    have exactCount :
        (∑ pair, (exactification.selectedSources pair).card) =
          multiplicity.muFine *
            exactification.incidence.allEdges.card := by
      calc
        (∑ pair, (exactification.selectedSources pair).card) =
            multiplicity.muFine *
              exactification.incidence.edgePool.card :=
          exactification.selected_incidence_count
        _ =
            multiplicity.muFine *
              exactification.incidence.allEdges.card := by
          simp [
            PureWZ2Prop62FourDegreeIncidenceData.allEdges,
            Fintype.card_coe
          ]
    calc
      (((∑ pair ∈
          input.referencePairs
            multiplicity parentClass treeCleanup,
        input.packetCellMultiplicity pair : ℕ) : ENNReal)) ≤
          (2 : ENNReal) *
            ((∑ pair,
              (exactification.selectedSources pair).card : ℕ) : ENNReal) := by
        exact_mod_cast exactification.reference_multiplicity_sum_le_exact
      _ =
          2 * (multiplicity.muFine : ENNReal) *
            exactification.incidence.allEdges.card := by
        rw [exactCount]
        norm_cast
        ring
  have binRetention :
      (exactification.incidence.allEdges.card : ENNReal) ≤
        (bins.fineCellBin.binCount : ENNReal) *
          bins.parentCoarseBin.binCount *
          bins.coarseCellBin.binCount *
          bins.finalEdges.card := by
    exact_mod_cast bins.exact_retention
  have coreRetention :
      (bins.finalEdges.card : ENNReal) ≤
        2 * core.ranges.terminalEdges.card := by
    have half := core.half_retention
    rw [← core.ranges_peeling_eq] at half
    exact_mod_cast half
  have balanceRetention :
      (core.ranges.terminalEdges.card : ENNReal) ≤
        degreeLoss *
          (core.ranges.selectedEdges good.sample).card := by
    exact_mod_cast
      input.terminalEdges_card_le_balanced
        multiplicity parentClass treeCleanup exactification
          parentDegree core good
  rw [← positiveCountEq]
  calc
    positiveCount ≤
        (multiplicity.binCount : ENNReal) * selectedCount :=
      classRetention
    _ ≤
        (multiplicity.binCount : ENNReal) *
          ((parentClass.weightBinCount : ENNReal) *
            weightClassCount) := by
      gcongr
    _ ≤
        (multiplicity.binCount : ENNReal) *
          ((parentClass.weightBinCount : ENNReal) *
            ((parentClass.fiberBinCount : ENNReal) *
              selectedParentCount)) := by
      gcongr
    _ ≤
        (multiplicity.binCount : ENNReal) *
          ((parentClass.weightBinCount : ENNReal) *
            ((parentClass.fiberBinCount : ENNReal) *
              ((2 ^ (schedule.levelCount + 1) : ENNReal) *
                referenceCount))) := by
      gcongr
    _ ≤
        (multiplicity.binCount : ENNReal) *
          ((parentClass.weightBinCount : ENNReal) *
            ((parentClass.fiberBinCount : ENNReal) *
              ((2 ^ (schedule.levelCount + 1) : ENNReal) *
                (2 * multiplicity.muFine *
                  exactification.incidence.allEdges.card)))) := by
      gcongr
    _ ≤
        (multiplicity.binCount : ENNReal) *
          ((parentClass.weightBinCount : ENNReal) *
            ((parentClass.fiberBinCount : ENNReal) *
              ((2 ^ (schedule.levelCount + 1) : ENNReal) *
                (2 * multiplicity.muFine *
                  ((bins.fineCellBin.binCount : ENNReal) *
                    bins.parentCoarseBin.binCount *
                    bins.coarseCellBin.binCount *
                    bins.finalEdges.card))))) := by
      gcongr
    _ ≤
        (multiplicity.binCount : ENNReal) *
          ((parentClass.weightBinCount : ENNReal) *
            ((parentClass.fiberBinCount : ENNReal) *
              ((2 ^ (schedule.levelCount + 1) : ENNReal) *
                (2 * multiplicity.muFine *
                  ((bins.fineCellBin.binCount : ENNReal) *
                    bins.parentCoarseBin.binCount *
                    bins.coarseCellBin.binCount *
                    (2 * core.ranges.terminalEdges.card)))))) := by
      gcongr
    _ ≤
        (multiplicity.binCount : ENNReal) *
          ((parentClass.weightBinCount : ENNReal) *
            ((parentClass.fiberBinCount : ENNReal) *
              ((2 ^ (schedule.levelCount + 1) : ENNReal) *
                (2 * multiplicity.muFine *
                  ((bins.fineCellBin.binCount : ENNReal) *
                    bins.parentCoarseBin.binCount *
                    bins.coarseCellBin.binCount *
                    (2 * (degreeLoss *
                      (core.ranges.selectedEdges good.sample).card))))))) := by
      gcongr
    _ =
        input.terminalMassRetentionLoss
            multiplicity parentClass treeCleanup exactification
              parentDegree core good *
          (multiplicity.muFine *
            (core.ranges.selectedEdges good.sample).card : ℕ) := by
      simp [terminalMassRetentionLoss]
      ring

theorem terminal_mass_retention :
    sourceShading.mass ≤
      input.terminalMassRetentionLoss
          multiplicity parentClass treeCleanup exactification
            parentDegree core good *
        (input.terminalFineShading
          multiplicity parentClass treeCleanup exactification
            core.ranges good families).mass := by
  rw [input.sourceShading_mass_eq]
  rw [input.terminalFineShading_mass_eq
    multiplicity parentClass treeCleanup exactification
      parentDegree core good families]
  exact
    by
      simpa [mul_assoc] using
        mul_le_mul_right'
          (input.sourceMultiplicityCount_le_terminal
            multiplicity parentClass treeCleanup exactification
              parentDegree core good)
          (volume (wz1PaperGridCube delta (0, 0, 0)))

/-- The final asymptotic absorption gate for the paper's `log^-50` claim. -/
structure MassRetentionAbsorptionData
    (logExponent : ℕ) : Prop where
  scalar :
    wz2PaperPureRefinementFraction delta logExponent *
        input.terminalMassRetentionLoss
          multiplicity parentClass treeCleanup exactification
            parentDegree core good ≤
      1

theorem terminal_mass_retention_fraction
    {logExponent : ℕ}
    (absorption :
      input.MassRetentionAbsorptionData
        multiplicity parentClass treeCleanup exactification
          parentDegree core good logExponent) :
    wz2PaperPureRefinementFraction delta logExponent *
        sourceShading.mass ≤
      (input.terminalFineShading
        multiplicity parentClass treeCleanup exactification
          core.ranges good families).mass := by
  calc
    wz2PaperPureRefinementFraction delta logExponent *
        sourceShading.mass ≤
      wz2PaperPureRefinementFraction delta logExponent *
        (input.terminalMassRetentionLoss
          multiplicity parentClass treeCleanup exactification
            parentDegree core good *
          (input.terminalFineShading
            multiplicity parentClass treeCleanup exactification
              core.ranges good families).mass) := by
      gcongr
      exact
        input.terminal_mass_retention
          multiplicity parentClass treeCleanup exactification
            parentDegree core good families
    _ =
      (wz2PaperPureRefinementFraction delta logExponent *
        input.terminalMassRetentionLoss
          multiplicity parentClass treeCleanup exactification
            parentDegree core good) *
        (input.terminalFineShading
          multiplicity parentClass treeCleanup exactification
            core.ranges good families).mass := by
      ring
    _ ≤
      1 *
        (input.terminalFineShading
          multiplicity parentClass treeCleanup exactification
            core.ranges good families).mass := by
      gcongr
      exact absorption.scalar
    _ =
      (input.terminalFineShading
        multiplicity parentClass treeCleanup exactification
          core.ranges good families).mass := by
      simp

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
