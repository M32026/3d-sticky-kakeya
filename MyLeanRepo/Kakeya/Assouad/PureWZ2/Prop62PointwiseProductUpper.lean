import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreeLemmaOutput
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGlobalMultiplicityHelpers

/-!
# Proposition 6.2: pointwise fine/coarse multiplicity product upper bound

The fourth-lemma output has exact fine packet-cell multiplicity and a frozen
coarse parent--cell multiplicity band.  Since both final shadings are unions
of whole fixed cells, these cellwise statements give uniform pointwise caps.

The standard finite parent-fiber decomposition then yields

`fineMultiplicity ≤ coarseLoss * muCoarse * muFine`.
-/

noncomputable section

namespace Kakeya.Assouad

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

namespace FourDegreeLemmaOutputData

theorem mem_lineCover_fiberIndices_iff_fullFiber
    (parent :
      Fin families.restriction.coarseSelected.family.card)
    (source :
      Fin families.restriction.fineSelected.family.card) :
    source ∈ families.restriction.lineCover.fiberIndices parent ↔
      source ∈
        wz2PaperFullFiberIndices
          families.restriction.fineSelected.family
          families.restriction.coarseSelected.family parent := by
  rw [mem_wz2PaperFullFiberIndices_iff]
  simp only [
    WZ1PaperTubeCover.fiberIndices,
    Finset.mem_filter,
    Finset.mem_univ,
    true_and
  ]
  constructor
  · intro sourceParent
    rw [← sourceParent]
    exact families.restriction.lineCover.parent_covers source
  · intro sourceCovered
    exact
      (families.restriction.lineCover.parent_unique
        source parent sourceCovered).symm

theorem coarse_pointMultiplicity_eq_cellCount
    {point : Point3}
    (pointMem : point ∈ output.coarseShading.union) :
    output.coarseShading.pointMultiplicity point =
      (FrozenCoarseShading.terminalParentsAtCoarseCell
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families
          (wz1PaperGridIndex rho point)).card := by
  rw [output.coarseShading_eq]
  let activeParents :
      Finset
        (Fin families.restriction.coarseSelected.family.card) :=
      ((Finset.univ :
        Finset
          (Fin families.restriction.coarseSelected.family.card)).filter
        fun parent =>
          point ∈
            (input.terminalCoarseShading
              multiplicity parentClass treeCleanup exactification
                core.ranges families).carrier parent)
  change
    activeParents.card =
      (FrozenCoarseShading.terminalParentsAtCoarseCell
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families
          (wz1PaperGridIndex rho point)).card
  apply Finset.card_bij (fun parent _ => parent)
  · intro parent parentMem
    have pointCarrier :
        point ∈
          (input.terminalCoarseShading
            multiplicity parentClass treeCleanup exactification
              core.ranges families).carrier parent :=
      (Finset.mem_filter.mp parentMem).2
    apply
      (FrozenCoarseShading.mem_terminalParentsAtCoarseCell_iff
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families
          (wz1PaperGridIndex rho point) parent).mpr
    rw [FrozenCoarseShading.terminal_carrier_eq
      input multiplicity parentClass treeCleanup exactification
        core.ranges families parent] at pointCarrier
    rcases Set.mem_iUnion₂.mp pointCarrier with
      ⟨coarseCell, coarseCellMem, pointCell⟩
    have cellEq :
        wz1PaperGridIndex rho point = coarseCell :=
      (mem_wz1PaperGridCube rho coarseCell point).mp pointCell
    simpa [cellEq] using coarseCellMem
  · intro first _ second _ equality
    exact equality
  · intro parent parentMem
    refine ⟨parent, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have coarseCellMem :=
      (FrozenCoarseShading.mem_terminalParentsAtCoarseCell_iff
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families
          (wz1PaperGridIndex rho point) parent).mp parentMem
    exact
      Set.mem_iUnion₂.mpr
        ⟨wz1PaperGridIndex rho point, coarseCellMem,
          (mem_wz1PaperGridCube rho
            (wz1PaperGridIndex rho point) point).mpr rfl⟩

theorem coarse_pointMultiplicity_le
    (point : Point3) :
    (output.coarseShading.pointMultiplicity point : ENNReal) ≤
      (output.coarseLoss * output.muCoarse : ℕ) := by
  by_cases pointMem : point ∈ output.coarseShading.union
  · have cellActive :
        wz1PaperGridIndex rho point ∈
          exactification.incidence.activeCoarseCells
            core.ranges.terminalEdges := by
      rw [output.coarseShading_eq] at pointMem
      rw [FrozenCoarseShading.terminal_union_eq_activeCoarseCells
        input multiplicity parentClass treeCleanup exactification
          core.ranges families] at pointMem
      rcases Set.mem_iUnion₂.mp pointMem with
        ⟨coarseCell, coarseCellMem, pointCell⟩
      have cellEq :
          wz1PaperGridIndex rho point = coarseCell :=
        (mem_wz1PaperGridCube rho coarseCell point).mp pointCell
      simpa [cellEq] using coarseCellMem
    let activeCell : core.ranges.ActiveCoarseCell :=
      ⟨wz1PaperGridIndex rho point, cellActive⟩
    rw [output.coarse_pointMultiplicity_eq_cellCount
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families pointMem]
    exact_mod_cast (output.coarse_multiplicity activeCell).2
  · have pointMultiplicityZero :
        output.coarseShading.pointMultiplicity point = 0 := by
      simp [
        Kakeya.Streamlined.Shading.pointMultiplicity,
        show ∀ parent, point ∉ output.coarseShading.carrier parent by
          intro parent pointCarrier
          exact pointMem ⟨parent, pointCarrier⟩
      ]
    rw [pointMultiplicityZero]
    simp

theorem coarse_pointMultiplicity_lower
    {point : Point3}
    (pointMem : point ∈ output.coarseShading.union) :
    (output.muCoarse : ENNReal) ≤
      output.coarseShading.pointMultiplicity point := by
  have cellActive :
      wz1PaperGridIndex rho point ∈
        exactification.incidence.activeCoarseCells
          core.ranges.terminalEdges := by
    rw [output.coarseShading_eq] at pointMem
    rw [FrozenCoarseShading.terminal_union_eq_activeCoarseCells
      input multiplicity parentClass treeCleanup exactification
        core.ranges families] at pointMem
    rcases Set.mem_iUnion₂.mp pointMem with
      ⟨coarseCell, coarseCellMem, pointCell⟩
    have cellEq :
        wz1PaperGridIndex rho point = coarseCell :=
      (mem_wz1PaperGridCube rho coarseCell point).mp pointCell
    simpa [cellEq] using coarseCellMem
  let activeCell : core.ranges.ActiveCoarseCell :=
    ⟨wz1PaperGridIndex rho point, cellActive⟩
  rw [output.coarse_pointMultiplicity_eq_cellCount
    input multiplicity parentClass treeCleanup exactification
      parentDegree core good families pointMem]
  exact_mod_cast (output.coarse_multiplicity activeCell).1

theorem fiber_pointMultiplicity_eq_muFine_of_pos
    (parent :
      Fin families.restriction.coarseSelected.family.card)
    (point : Point3)
    (positive :
      0 <
        families.restriction.lineCover.fiberPointMultiplicity
          output.fineShading parent point) :
    families.restriction.lineCover.fiberPointMultiplicity
        output.fineShading parent point =
      output.muFine := by
  let fiberSources :=
    (families.restriction.lineCover.fiberIndices parent).filter fun source =>
      point ∈ output.fineShading.carrier source
  have fiberNonempty : fiberSources.Nonempty := by
    change 0 < fiberSources.card at positive
    exact Finset.card_pos.mp positive
  rcases fiberNonempty with ⟨source, sourceMem⟩
  have sourceData := Finset.mem_filter.mp sourceMem
  have sourceFiber :
      source ∈
        wz2PaperFullFiberIndices
          families.restriction.fineSelected.family
          families.restriction.coarseSelected.family parent := by
    exact
      (mem_lineCover_fiberIndices_iff_fullFiber
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families parent source).mp sourceData.1
  have pointCarrier :
      point ∈ output.fineShading.carrier source :=
    sourceData.2
  rw [output.fineShading_eq] at pointCarrier
  rw [TerminalFineShading.carrier_eq
    input multiplicity parentClass treeCleanup exactification
      core.ranges good families source] at pointCarrier
  rcases Set.mem_iUnion₂.mp pointCarrier with
    ⟨fineCell, fineCellMem, pointCell⟩
  rcases Finset.mem_image.mp fineCellMem with
    ⟨edge, edgeMem, edgeFine⟩
  have edgeSelected :
      edge ∈ core.ranges.selectedEdges good.sample :=
    (Finset.mem_filter.mp edgeMem).1
  have sourceSelected :
      input.sourceSelectedOnEdge
        multiplicity parentClass treeCleanup exactification
          (families.restriction.fineSelected.embedding source) edge :=
    (Finset.mem_filter.mp edgeMem).2
  have edgeParent :
      exactification.incidence.edgeParent edge =
        families.restriction.coarseSelected.embedding parent := by
    have ambientSourceFiber :
        families.restriction.fineSelected.embedding source ∈
          wz2PaperFullFiberIndices fine coarse
            (families.restriction.coarseSelected.embedding parent) := by
      have imageMem :
          families.restriction.fineSelected.embedding source ∈
            Finset.image families.restriction.fineSelected.embedding
              (wz2PaperFullFiberIndices
                families.restriction.fineSelected.family
                families.restriction.coarseSelected.family parent) :=
        Finset.mem_image.mpr ⟨source, sourceFiber, rfl⟩
      rw [families.fine_complete parent] at imageMem
      exact imageMem
    exact
      ExactFineShading.sourceSelectedOnEdge_parent_eq
        input multiplicity parentClass treeCleanup exactification
          ambientSourceFiber sourceSelected
  have pointOwnCell :
      point ∈
        wz1PaperGridCube delta
          (exactification.incidence.edgeFineCell edge) := by
    rw [edgeFine]
    exact pointCell
  have baseFiberEq :
      families.restriction.lineCover.fiberIndices parent =
        wz2PaperFullFiberIndices
          families.restriction.fineSelected.family
          families.restriction.coarseSelected.family parent := by
    ext candidate
    exact
      mem_lineCover_fiberIndices_iff_fullFiber
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families parent candidate
  have activeFiberEq :
      fiberSources =
        TerminalFineShading.terminalPacketCellSources
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families parent edge := by
    dsimp only [
      fiberSources,
      TerminalFineShading.terminalPacketCellSources
    ]
    rw [baseFiberEq]
    apply Finset.filter_congr
    intro candidate _candidateFiber
    constructor
    · intro candidatePoint
      rw [output.fineShading_eq] at candidatePoint
      intro other otherMem
      have pointIndex :
          wz1PaperGridIndex delta point =
            exactification.incidence.edgeFineCell edge :=
        (mem_wz1PaperGridCube delta
          (exactification.incidence.edgeFineCell edge) point).mp
            pointOwnCell
      have otherIndex :
          wz1PaperGridIndex delta other =
            exactification.incidence.edgeFineCell edge :=
        (mem_wz1PaperGridCube delta
          (exactification.incidence.edgeFineCell edge) other).mp
            otherMem
      exact
        TerminalFineShading.cubical
          input multiplicity parentClass treeCleanup exactification
            core.ranges good families candidate point candidatePoint
            <|
          (mem_wz1PaperGridCube delta
            (wz1PaperGridIndex delta point) other).mpr
            (otherIndex.trans pointIndex.symm)
    · intro wholeCell
      rw [output.fineShading_eq]
      exact wholeCell pointOwnCell
  change fiberSources.card = output.muFine
  rw [activeFiberEq]
  rcases output.exact_fine edge edgeSelected with
    ⟨exactParent, exactParentEq, exactCard⟩
  have exactParentCurrent : exactParent = parent := by
    apply families.restriction.coarseSelected.embedding.injective
    exact exactParentEq.symm.trans edgeParent
  subst exactParent
  exact exactCard

theorem fiber_pointMultiplicity_le
    (parent :
      Fin families.restriction.coarseSelected.family.card)
    (point : Point3) :
    (families.restriction.lineCover.fiberPointMultiplicity
        output.fineShading parent point : ENNReal) ≤
      output.muFine := by
  by_cases positive :
      0 <
        families.restriction.lineCover.fiberPointMultiplicity
          output.fineShading parent point
  · rw [output.fiber_pointMultiplicity_eq_muFine_of_pos
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent point positive]
  · have zero :
        families.restriction.lineCover.fiberPointMultiplicity
            output.fineShading parent point =
          0 := Nat.eq_zero_of_not_pos positive
    rw [zero]
    simp

theorem pointwise_product_upper
    (point : Point3) :
    (output.fineShading.pointMultiplicity point : ENNReal) ≤
      (output.coarseLoss * output.muCoarse : ENNReal) *
        output.muFine := by
  simpa only [Nat.cast_mul] using
    (families.restriction.lineCover
      |>.pointMultiplicity_le_coarse_mul_fiber
        output.fineShading output.coarseShading
        (fun source point pointMem =>
          output.balanced.point_compatibility
            source
            (families.restriction.lineCover.parent source)
            (families.restriction.lineCover.parent_covers source)
            point pointMem)
        output.coarse_pointMultiplicity_le
        output.fiber_pointMultiplicity_le
        point)

end FourDegreeLemmaOutputData

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
