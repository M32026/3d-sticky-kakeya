import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TerminalFineShading

/-!
# Proposition 6.2: the frozen coarse shading and balanced cover

The parent--coarse-cell relation is frozen at the terminal four-degree core:

`P ~ Q` iff `n(P,Q) > 0`.

It is not recomputed after the random whole-cell choice.  The ambient coarse
shading of `P` is the union of every fixed `rho`-cube related to `P`.  This
shading is then restricted, without further selection, to the terminal coarse
family.

For a good balancing sample, every active coarse cell contains exactly the
common number `W` of selected fine cells.  Hence the terminal fine shading
has one common mass in every active coarse cell, and the resulting Section 6
cover is balanced.
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
    (good : ranges.GoodBalancingSampleData degreeLoss)
    (families :
      input.TerminalCompleteFamiliesData
        multiplicity parentClass treeCleanup exactification ranges)

/-- Frozen coarse cells related to one ambient metric parent. -/
def frozenCoarseCellsAt
    (parent : Fin coarse.card) :
    Finset WZ2PaperCellIndex :=
  (ranges.terminalEdges.filter fun edge =>
      exactification.incidence.edgeParent edge = parent).image
        exactification.incidence.edgeCoarseCell

theorem mem_frozenCoarseCellsAt_iff
    (parent : Fin coarse.card)
    (coarseCell : WZ2PaperCellIndex) :
    coarseCell ∈
        input.frozenCoarseCellsAt
          multiplicity parentClass treeCleanup exactification
          ranges parent ↔
      0 <
        exactification.incidence.parentCoarseDegree
          ranges.terminalEdges parent coarseCell := by
  constructor
  · intro cellMem
    rcases Finset.mem_image.mp cellMem with
      ⟨edge, edgeMem, edgeCoarse⟩
    have edgeData := Finset.mem_filter.mp edgeMem
    apply Finset.card_pos.mpr
    exact
      ⟨edge,
        Finset.mem_filter.mpr
          ⟨edgeData.1, edgeData.2, edgeCoarse⟩⟩
  · intro degreePos
    rcases Finset.card_pos.mp degreePos with
      ⟨edge, edgeMem⟩
    have edgeData := Finset.mem_filter.mp edgeMem
    exact
      Finset.mem_image.mpr
        ⟨edge,
          Finset.mem_filter.mpr
            ⟨edgeData.1, edgeData.2.1⟩,
          edgeData.2.2⟩

theorem frozenCoarseCell_subset_parentCarrier
    {parent : Fin coarse.card}
    {coarseCell : WZ2PaperCellIndex}
    (cellMem :
      coarseCell ∈
        input.frozenCoarseCellsAt
          multiplicity parentClass treeCleanup exactification
          ranges parent) :
    wz1PaperGridCube rho coarseCell ⊆
      wz1PaperTubeCarrier (coarse.tube parent) := by
  rcases Finset.mem_image.mp cellMem with
    ⟨edge, edgeMem, edgeCoarse⟩
  have edgeData := Finset.mem_filter.mp edgeMem
  have selectedSourcesNonempty :
      (exactification.selectedSources
        (input.referencePairOfEdge
          multiplicity parentClass treeCleanup exactification edge)).Nonempty := by
    apply Finset.card_pos.mp
    rw [exactification.selectedSources_card]
    exact multiplicity.muFine_pos
  rcases selectedSourcesNonempty with ⟨source, sourceMem⟩
  have coarseSubset :=
    PacketCellExactificationData.selectedCoarseCell_subset_parentCarrier
      input multiplicity parentClass treeCleanup exactification
      (input.referencePairOfEdge
        multiplicity parentClass treeCleanup exactification edge)
      sourceMem
  have edgeParent :
      exactification.incidence.edgeParent edge = parent :=
    edgeData.2
  have edgeCoarse' :
      exactification.incidence.edgeCoarseCell edge = coarseCell :=
    edgeCoarse
  change
    wz1PaperGridCube rho
        (input.coarseCellOf
          (exactification.incidence.edgeFineCell edge)) ⊆
      wz1PaperTubeCarrier
        (coarse.tube (exactification.incidence.edgeParent edge)) at coarseSubset
  rw [
    ← exactification.incidence_coarseCellOf_eq,
    ← PureWZ2Prop62FourDegreeIncidenceData.edgeCoarseCell,
    edgeCoarse',
    edgeParent
  ] at coarseSubset
  exact coarseSubset

/-- Ambient frozen coarse shading before reindexing the terminal parents. -/
def ambientFrozenCoarseShading :
    WZ1PaperTubeShading coarse where
  carrier parent :=
    wz2RetainedCellsUnion rho
      (input.frozenCoarseCellsAt
        multiplicity parentClass treeCleanup exactification
        ranges parent)
  measurable_carrier parent :=
    wz2RetainedCellsUnion_measurable
  subset_body parent := by
    intro point pointMem
    rcases Set.mem_iUnion₂.mp pointMem with
      ⟨coarseCell, cellMem, pointCell⟩
    exact
      input.frozenCoarseCell_subset_parentCarrier
        multiplicity parentClass treeCleanup exactification
        ranges cellMem pointCell

/-- Frozen coarse shading on the terminal coarse subfamily. -/
def terminalCoarseShading :
    WZ1PaperTubeShading
      families.restriction.coarseSelected.family :=
  restrictPaperShading
    families.restriction.coarseSelected
    (input.ambientFrozenCoarseShading
      multiplicity parentClass treeCleanup exactification ranges)

namespace FrozenCoarseShading

theorem terminal_carrier_eq
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    (input.terminalCoarseShading
      multiplicity parentClass treeCleanup exactification
      ranges families).carrier parent =
      wz2RetainedCellsUnion rho
        (input.frozenCoarseCellsAt
          multiplicity parentClass treeCleanup exactification
          ranges
          (families.restriction.coarseSelected.embedding parent)) := by
  rfl

theorem terminal_cubical :
    WZ1PaperIsCubicalShading
      (input.terminalCoarseShading
        multiplicity parentClass treeCleanup exactification
        ranges families) := by
  intro parent point pointMem
  rcases Set.mem_iUnion₂.mp pointMem with
    ⟨coarseCell, coarseCellMem, pointCell⟩
  have pointIndex :
      wz1PaperGridIndex rho point = coarseCell :=
    (mem_wz1PaperGridCube rho coarseCell point).mp pointCell
  intro other otherMem
  have otherCell :
      other ∈ wz1PaperGridCube rho coarseCell := by
    apply (mem_wz1PaperGridCube rho coarseCell other).mpr
    exact
      ((mem_wz1PaperGridCube rho
        (wz1PaperGridIndex rho point) other).mp otherMem).trans
          pointIndex
  exact
    Set.mem_iUnion₂.mpr
      ⟨coarseCell, coarseCellMem, otherCell⟩

theorem activeCoarseCell_mem_some_terminal_parent
    (coarseCell : ranges.ActiveCoarseCell) :
    ∃ parent :
        Fin families.restriction.coarseSelected.family.card,
      coarseCell.1 ∈
        input.frozenCoarseCellsAt
          multiplicity parentClass treeCleanup exactification
          ranges
          (families.restriction.coarseSelected.embedding parent) := by
  have coarseDegreePos :=
    ranges.activeCoarseCell_degree_pos coarseCell
  rcases Finset.card_pos.mp coarseDegreePos with
    ⟨edge, edgeMem⟩
  have edgeData := Finset.mem_filter.mp edgeMem
  have edgeParentTerminal :
      exactification.incidence.edgeParent edge ∈
        families.terminalParents := by
    rw [families.terminalParents_eq]
    exact
      Finset.mem_image.mpr
        ⟨edge, edgeData.1, rfl⟩
  have parentImage :
      exactification.incidence.edgeParent edge ∈
        Finset.image
          families.restriction.coarseSelected.embedding Finset.univ := by
    rw [families.coarse_image_univ]
    exact edgeParentTerminal
  rcases Finset.mem_image.mp parentImage with
    ⟨parent, _parentUniv, parentEq⟩
  refine ⟨parent, ?_⟩
  apply
    (input.mem_frozenCoarseCellsAt_iff
      multiplicity parentClass treeCleanup exactification
      ranges
      (families.restriction.coarseSelected.embedding parent)
      coarseCell.1).mpr
  apply Finset.card_pos.mpr
  exact
    ⟨edge,
      Finset.mem_filter.mpr
        ⟨edgeData.1, by simpa [parentEq] using edgeData.2⟩⟩

theorem terminal_union_eq_activeCoarseCells :
    (input.terminalCoarseShading
      multiplicity parentClass treeCleanup exactification
      ranges families).union =
      wz2RetainedCellsUnion rho
        (exactification.incidence.activeCoarseCells
          ranges.terminalEdges) := by
  apply Set.Subset.antisymm
  · intro point pointMem
    rcases pointMem with ⟨parent, parentMem⟩
    rcases Set.mem_iUnion₂.mp parentMem with
      ⟨coarseCell, coarseCellMem, pointCell⟩
    have degreePos :=
      (input.mem_frozenCoarseCellsAt_iff
        multiplicity parentClass treeCleanup exactification
        ranges
        (families.restriction.coarseSelected.embedding parent)
        coarseCell).mp coarseCellMem
    have coarseActive :
        coarseCell ∈
          exactification.incidence.activeCoarseCells
            ranges.terminalEdges := by
      rw [exactification.incidence.mem_activeCoarseCells_iff]
      have degreeLe :
          exactification.incidence.parentCoarseDegree
              ranges.terminalEdges
              (families.restriction.coarseSelected.embedding parent)
              coarseCell ≤
            exactification.incidence.coarseDegree
              ranges.terminalEdges coarseCell := by
        apply Finset.card_le_card
        intro edge edgeMem
        have edgeData := Finset.mem_filter.mp edgeMem
        exact
          Finset.mem_filter.mpr
            ⟨edgeData.1, edgeData.2.2⟩
      exact degreePos.trans_le degreeLe
    exact
      Set.mem_iUnion₂.mpr
        ⟨coarseCell, coarseActive, pointCell⟩
  · intro point pointMem
    rcases Set.mem_iUnion₂.mp pointMem with
      ⟨coarseCell, coarseCellMem, pointCell⟩
    let activeCell : ranges.ActiveCoarseCell :=
      ⟨coarseCell, coarseCellMem⟩
    rcases
        FrozenCoarseShading.activeCoarseCell_mem_some_terminal_parent
          input
          multiplicity parentClass treeCleanup exactification
          ranges families activeCell
      with ⟨parent, parentCellMem⟩
    exact
      ⟨parent,
        Set.mem_iUnion₂.mpr
          ⟨coarseCell, parentCellMem, pointCell⟩⟩

theorem point_compatibility
    (source :
      Fin families.restriction.fineSelected.family.card)
    (parent :
      Fin families.restriction.coarseSelected.family.card)
    (sourceCovered :
      WZ1PaperTubeCovers
        (families.restriction.fineSelected.family.tube source)
        (families.restriction.coarseSelected.family.tube parent))
    (point : Point3)
    (pointFine :
      point ∈
        (input.terminalFineShading
          multiplicity parentClass treeCleanup exactification
          ranges good families).carrier source) :
    point ∈
      (input.terminalCoarseShading
        multiplicity parentClass treeCleanup exactification
        ranges families).carrier parent := by
  have pointAmbient :
      point ∈
        (input.ambientExactShading
          multiplicity parentClass treeCleanup exactification
          ranges good).carrier
            (families.restriction.fineSelected.embedding source) := by
    exact pointFine
  rcases Set.mem_iUnion₂.mp pointAmbient with
    ⟨fineCell, fineCellMem, pointCell⟩
  rcases Finset.mem_image.mp fineCellMem with
    ⟨edge, edgeMem, edgeFine⟩
  have sourceSelected :
      input.sourceSelectedOnEdge
        multiplicity parentClass treeCleanup exactification
        (families.restriction.fineSelected.embedding source) edge :=
    (Finset.mem_filter.mp edgeMem).2
  have sourceEdgeFiber :
      families.restriction.fineSelected.embedding source ∈
        wz2PaperFullFiberIndices fine coarse
          (exactification.incidence.edgeParent edge) :=
    ExactFineShading.sourceSelectedOnEdge_fullFiber
      input multiplicity parentClass treeCleanup exactification
      sourceSelected
  have sourceParentFiber :
      families.restriction.fineSelected.embedding source ∈
        wz2PaperFullFiberIndices fine coarse
          (families.restriction.coarseSelected.embedding parent) := by
    apply
      (mem_wz2PaperFullFiberIndices_iff
        (families.restriction.coarseSelected.embedding parent)
        (families.restriction.fineSelected.embedding source)).mpr
    simpa only [
      families.restriction.fineSelected.tube_eq,
      families.restriction.coarseSelected.tube_eq
    ] using sourceCovered
  have parentEq :
      exactification.incidence.edgeParent edge =
        families.restriction.coarseSelected.embedding parent := by
    have edgeCover :=
      (mem_wz2PaperFullFiberIndices_iff
        (exactification.incidence.edgeParent edge)
        (families.restriction.fineSelected.embedding source)).mp
          sourceEdgeFiber
    have parentCover :=
      (mem_wz2PaperFullFiberIndices_iff
        (families.restriction.coarseSelected.embedding parent)
        (families.restriction.fineSelected.embedding source)).mp
          sourceParentFiber
    exact
      (cover.toWZ1PaperTubeCover.parent_unique
        (families.restriction.fineSelected.embedding source)
        (exactification.incidence.edgeParent edge) edgeCover).trans
      (cover.toWZ1PaperTubeCover.parent_unique
        (families.restriction.fineSelected.embedding source)
        (families.restriction.coarseSelected.embedding parent)
        parentCover).symm
  have edgeSelected :
      edge ∈ ranges.selectedEdges good.sample :=
    (Finset.mem_filter.mp edgeMem).1
  have edgeTerminal :
      edge ∈ ranges.terminalEdges :=
    good.selectedEdges_subset edgeSelected
  have coarseCellMem :
      exactification.incidence.edgeCoarseCell edge ∈
        input.frozenCoarseCellsAt
          multiplicity parentClass treeCleanup exactification
          ranges
          (families.restriction.coarseSelected.embedding parent) := by
    apply Finset.mem_image.mpr
    exact
      ⟨edge,
        Finset.mem_filter.mpr
          ⟨edgeTerminal, parentEq⟩,
        rfl⟩
  apply Set.mem_iUnion₂.mpr
  refine
    ⟨exactification.incidence.edgeCoarseCell edge,
      coarseCellMem, ?_⟩
  have packetData :=
    exactification.selectedSources_subset
      (input.referencePairOfEdge
        multiplicity parentClass treeCleanup exactification edge)
      sourceSelected
  have packetMem :=
    (input.mem_packetCellSources_iff
      (exactification.incidence.edgeParent edge)
      (exactification.incidence.edgeFineCell edge)
      (families.restriction.fineSelected.embedding source)).mp <| by
        simpa [
          referencePairOfEdge,
          PureWZ2Prop62FourDegreeIncidenceData.edgeParent,
          PureWZ2Prop62FourDegreeIncidenceData.edgeFineCell
        ] using packetData
  have fineContainment :=
    input.fine_cell_containment
      (exactification.incidence.edgeFineCell edge) packetMem.1
  have pointFineCell :
      point ∈ wz1PaperGridCube delta
        (exactification.incidence.edgeFineCell edge) := by
    rw [edgeFine]
    exact pointCell
  unfold PureWZ2Prop62FourDegreeIncidenceData.edgeCoarseCell
  rw [exactification.incidence_coarseCellOf_eq]
  exact fineContainment pointFineCell

def balancedCoverData :
    PureWZ2BalancedCoverData
      families.restriction.section6Cover
      (input.terminalFineShading
        multiplicity parentClass treeCleanup exactification
        ranges good families)
      (input.terminalCoarseShading
        multiplicity parentClass treeCleanup exactification
        ranges families) where
  point_compatibility :=
    FrozenCoarseShading.point_compatibility
      input
      multiplicity parentClass treeCleanup exactification
      ranges good families
  coarse_cubical :=
    FrozenCoarseShading.terminal_cubical
      input
      multiplicity parentClass treeCleanup exactification
      ranges families
  activeCells :=
    exactification.incidence.activeCoarseCells
      ranges.terminalEdges
  coarse_union_eq := by
    exact
      FrozenCoarseShading.terminal_union_eq_activeCoarseCells
        input
        multiplicity parentClass treeCleanup exactification
        ranges families
  cellMass :=
    (ranges.commonFineCellCount : ENNReal) *
      volume (wz1PaperGridCube delta (0, 0, 0))
  cellMass_pos := by
    exact
      ENNReal.mul_pos
        (by exact_mod_cast ranges.commonFineCellCount_pos.ne')
        (wz1PaperGridCube_volume_pos input.delta_pos _).ne'
  cellMass_ne_top := by
    exact
      ENNReal.mul_ne_top
        (by simp)
        (wz1PaperGridCube_volume_ne_top input.delta_pos _)
  fine_cell_mass := by
    intro coarseCell coarseCellMem
    let activeCell : ranges.ActiveCoarseCell :=
      ⟨coarseCell, coarseCellMem⟩
    rw [TerminalFineShading.union_eq_ambient
      input multiplicity parentClass treeCleanup exactification
      ranges good families]
    exact
      ExactFineShading.ambient_union_inter_coarseCube_volume
        input multiplicity parentClass treeCleanup exactification
        ranges good activeCell
end FrozenCoarseShading

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
