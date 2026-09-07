import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FrozenCoarseShading
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TerminalParentCWA

/-!
# Proposition 6.2: terminal coarse multiplicity

The coarse parent--cell relation was frozen before the exact balancing
sample:

`P ~ Q` if and only if `n(P,Q) > 0`.

This module defines the paper's common coarse multiplicity from the two
dyadic degree levels and the simultaneous-peeling loss `A0`.  It proves the
uniform band with loss `4 * A0^2`, then identifies the terminal incidence
count exactly with the number of final coarse shadings containing the whole
fixed `rho`-cube.  No relation is recomputed after balancing.
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

namespace FourDegreeCoreAssemblyData

/-- The denominator `2 A0 n_*` in the paper lower bound for `c(Q)`. -/
def terminalCoarseMultiplicityDenominator
    (_core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup
        exactification parentDegree bins A0) : ℕ :=
  2 * A0 * 2 ^ bins.parentCoarseBin.level

/-- The paper's common coarse multiplicity, with integer ceiling division. -/
def terminalCoarseMultiplicity
    (_core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup
        exactification parentDegree bins A0) : ℕ :=
  max 1
    (2 ^ bins.coarseCellBin.level ⌈/⌉
      _core.terminalCoarseMultiplicityDenominator
        input multiplicity parentClass treeCleanup
          exactification parentDegree)

/-- The explicit comparison loss for all terminal coarse cells. -/
def terminalCoarseMultiplicityLoss
    (_core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup
        exactification parentDegree bins A0) : ℕ :=
  4 * A0 ^ 2

theorem terminalCoarseMultiplicity_pos :
    0 <
      core.terminalCoarseMultiplicity
        input multiplicity parentClass treeCleanup
          exactification parentDegree := by
  simp [terminalCoarseMultiplicity]

theorem terminalCoarseMultiplicityDenominator_pos :
    0 <
      core.terminalCoarseMultiplicityDenominator
        input multiplicity parentClass treeCleanup
          exactification parentDegree := by
  simp [
    terminalCoarseMultiplicityDenominator,
    core.A0_pos
  ]

theorem activeParentCount_coarseMultiplicity_band
    (coarseCell : WZ2PaperCellIndex)
    (coarse_pos :
      0 <
        exactification.incidence.coarseDegree
          core.ranges.terminalEdges coarseCell) :
    core.terminalCoarseMultiplicity
          input multiplicity parentClass treeCleanup
            exactification parentDegree ≤
        core.ranges.activeParentCount coarseCell ∧
      core.ranges.activeParentCount coarseCell ≤
        core.terminalCoarseMultiplicityLoss
            input multiplicity parentClass treeCleanup
              exactification parentDegree *
          core.terminalCoarseMultiplicity
            input multiplicity parentClass treeCleanup
              exactification parentDegree := by
  let coarseBase : ℕ := 2 ^ bins.coarseCellBin.level
  let parentCoarseBase : ℕ :=
    2 ^ bins.parentCoarseBin.level
  let coarseCount : ℕ :=
    core.ranges.activeParentCount coarseCell
  let coarseMultiplicity : ℕ :=
    core.terminalCoarseMultiplicity
      input multiplicity parentClass treeCleanup
        exactification parentDegree
  let denominator : ℕ :=
    core.terminalCoarseMultiplicityDenominator
      input multiplicity parentClass treeCleanup
        exactification parentDegree
  have coarseCountPos : 0 < coarseCount := by
    exact
      (core.ranges.activeParentsAt_nonempty coarse_pos).card_pos
  have coarseLower :
      input.coarseCellThreshold
          multiplicity parentClass treeCleanup
            exactification bins A0 ≤
        exactification.incidence.coarseDegree
          core.ranges.terminalEdges coarseCell :=
    (core.ranges.coarse_degree_range coarse_pos).1
  have coarseUpperByParents :
      exactification.incidence.coarseDegree
          core.ranges.terminalEdges coarseCell <
        core.ranges.parentCoarseUpper * coarseCount := by
    simpa [coarseCount] using
      core.ranges.coarseDegree_lt_parentCoarseUpper_mul_activeParentCount
        coarse_pos
  have coarseBaseLeThreshold :
      coarseBase ≤
        A0 *
          input.coarseCellThreshold
            multiplicity parentClass treeCleanup
              exactification bins A0 := by
    simpa [
      coarseBase,
      PureWZ2Prop62PacketCellInput.coarseCellThreshold
    ] using
      (le_smul_ceilDiv core.A0_pos :
        2 ^ bins.coarseCellBin.level ≤
          A0 *
            (2 ^ bins.coarseCellBin.level ⌈/⌉ A0))
  have coarseBaseLt :
      coarseBase < denominator * coarseCount := by
    calc
      coarseBase ≤
          A0 *
            input.coarseCellThreshold
              multiplicity parentClass treeCleanup
                exactification bins A0 :=
        coarseBaseLeThreshold
      _ ≤
          A0 *
            exactification.incidence.coarseDegree
              core.ranges.terminalEdges coarseCell :=
        Nat.mul_le_mul_left A0 coarseLower
      _ <
          A0 *
            (core.ranges.parentCoarseUpper * coarseCount) :=
        (Nat.mul_lt_mul_left core.A0_pos).2 coarseUpperByParents
      _ = denominator * coarseCount := by
        simp [
          denominator,
          FourDegreeCoreAssemblyData.terminalCoarseMultiplicityDenominator,
          PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.parentCoarseUpper,
          parentCoarseBase,
          pow_succ
        ]
        ring
  have ceilLeCount :
      coarseBase ⌈/⌉ denominator ≤ coarseCount := by
    apply
      (ceilDiv_le_iff_le_mul
        (core.terminalCoarseMultiplicityDenominator_pos
          input multiplicity parentClass treeCleanup
            exactification parentDegree)).mpr
    exact coarseBaseLt.le
  have multiplicityLeCount :
      coarseMultiplicity ≤ coarseCount := by
    apply max_le
    · exact coarseCountPos
    · simpa [
        coarseMultiplicity,
        FourDegreeCoreAssemblyData.terminalCoarseMultiplicity,
        coarseBase,
        denominator
      ] using ceilLeCount
  have parentCoarseLower :
      input.parentCoarseThreshold
          multiplicity parentClass treeCleanup
            exactification bins A0 *
          coarseCount ≤
        exactification.incidence.coarseDegree
          core.ranges.terminalEdges coarseCell := by
    simpa [coarseCount] using
      core.ranges.parentCoarseLower_mul_activeParentCount_le_coarseDegree
        coarse_pos
  have coarseDegreeUpper :
      exactification.incidence.coarseDegree
          core.ranges.terminalEdges coarseCell <
        2 * coarseBase := by
    have upper :=
      (core.ranges.coarse_degree_range coarse_pos).2
    simpa [
      PureWZ2Prop62FourDegreeIncidenceData.FourDegreeRangeData.coarseUpper,
      coarseBase,
      pow_succ,
      Nat.mul_comm
    ] using upper
  have parentBaseLeThreshold :
      parentCoarseBase ≤
        A0 *
          input.parentCoarseThreshold
            multiplicity parentClass treeCleanup
              exactification bins A0 := by
    simpa [
      parentCoarseBase,
      PureWZ2Prop62PacketCellInput.parentCoarseThreshold
    ] using
      (le_smul_ceilDiv core.A0_pos :
        2 ^ bins.parentCoarseBin.level ≤
          A0 *
            (2 ^ bins.parentCoarseBin.level ⌈/⌉ A0))
  have coarseBaseLeDenominatorMultiplicity :
      coarseBase ≤ denominator * coarseMultiplicity := by
    have ceilBound :
        coarseBase ≤
          denominator * (coarseBase ⌈/⌉ denominator) :=
      le_smul_ceilDiv
        (core.terminalCoarseMultiplicityDenominator_pos
          input multiplicity parentClass treeCleanup
            exactification parentDegree)
    exact ceilBound.trans <|
      Nat.mul_le_mul_left denominator <| by
        simpa [
          coarseMultiplicity,
          FourDegreeCoreAssemblyData.terminalCoarseMultiplicity,
          coarseBase,
          denominator
        ] using
          (le_max_right 1 (coarseBase ⌈/⌉ denominator))
  have scaledCoarseBase :
      2 * coarseBase ≤
        (4 * A0 ^ 2 * coarseMultiplicity) *
          input.parentCoarseThreshold
            multiplicity parentClass treeCleanup
              exactification bins A0 := by
    calc
      2 * coarseBase ≤
          2 * (denominator * coarseMultiplicity) :=
        Nat.mul_le_mul_left 2
          coarseBaseLeDenominatorMultiplicity
      _ =
          4 * A0 * parentCoarseBase * coarseMultiplicity := by
        simp [
          denominator,
          FourDegreeCoreAssemblyData.terminalCoarseMultiplicityDenominator
        ]
        ring
      _ ≤
          4 * A0 *
              (A0 *
                input.parentCoarseThreshold
                  multiplicity parentClass treeCleanup
                    exactification bins A0) *
            coarseMultiplicity := by
        gcongr
      _ =
          (4 * A0 ^ 2 * coarseMultiplicity) *
            input.parentCoarseThreshold
              multiplicity parentClass treeCleanup
                exactification bins A0 := by
        ring
  have multipliedUpper :
      input.parentCoarseThreshold
            multiplicity parentClass treeCleanup
              exactification bins A0 *
          coarseCount <
        (4 * A0 ^ 2 * coarseMultiplicity) *
          input.parentCoarseThreshold
            multiplicity parentClass treeCleanup
              exactification bins A0 :=
    parentCoarseLower.trans_lt <|
      coarseDegreeUpper.trans_le scaledCoarseBase
  have thresholdPos :
      0 <
        input.parentCoarseThreshold
          multiplicity parentClass treeCleanup
            exactification bins A0 := by
    by_contra thresholdNotPos
    have thresholdZero :
        input.parentCoarseThreshold
          multiplicity parentClass treeCleanup
            exactification bins A0 = 0 := by omega
    have parentBaseZero : parentCoarseBase = 0 := by
      have := parentBaseLeThreshold
      simp [thresholdZero] at this
      exact this
    have parentBasePos : 0 < parentCoarseBase := by
      simp [parentCoarseBase]
    omega
  have countLt :
      coarseCount < 4 * A0 ^ 2 * coarseMultiplicity := by
    apply (Nat.mul_lt_mul_left thresholdPos).mp
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      multipliedUpper
  refine
    ⟨by simpa [coarseMultiplicity, coarseCount] using multiplicityLeCount,
      ?_⟩
  simpa [
    coarseMultiplicity,
    coarseCount,
    FourDegreeCoreAssemblyData.terminalCoarseMultiplicityLoss
  ] using countLt.le

end FourDegreeCoreAssemblyData

variable
    (families :
      input.TerminalCompleteFamiliesData
        multiplicity parentClass treeCleanup exactification
          core.ranges)

namespace FrozenCoarseShading

/-- Final coarse parents whose frozen shading contains the whole coarse cube. -/
def terminalParentsAtCoarseCell
    (coarseCell : WZ2PaperCellIndex) :
    Finset
      (Fin families.restriction.coarseSelected.family.card) :=
  Finset.univ.filter fun parent =>
    wz1PaperGridCube rho coarseCell ⊆
      (input.terminalCoarseShading
        multiplicity parentClass treeCleanup exactification
          core.ranges families).carrier parent

theorem mem_terminalParentsAtCoarseCell_iff
    (coarseCell : WZ2PaperCellIndex)
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    parent ∈
        FrozenCoarseShading.terminalParentsAtCoarseCell
          input multiplicity parentClass treeCleanup exactification
            parentDegree core families coarseCell ↔
      coarseCell ∈
        input.frozenCoarseCellsAt
          multiplicity parentClass treeCleanup exactification
            core.ranges
            (families.restriction.coarseSelected.embedding parent) := by
  simp only [
    terminalParentsAtCoarseCell,
    Finset.mem_filter,
    Finset.mem_univ,
    true_and
  ]
  constructor
  · intro cubeSubset
    have cornerCarrier :=
      cubeSubset (cellCorner_mem_gridCube input.rho_pos coarseCell)
    rw [FrozenCoarseShading.terminal_carrier_eq
      input multiplicity parentClass treeCleanup exactification
        core.ranges families parent] at cornerCarrier
    rcases Set.mem_iUnion₂.mp cornerCarrier with
      ⟨otherCell, otherCellMem, cornerOther⟩
    have cornerOwn :
        cellCorner rho coarseCell ∈
          wz1PaperGridCube rho coarseCell :=
      cellCorner_mem_gridCube input.rho_pos coarseCell
    have cellEq : otherCell = coarseCell := by
      have otherIndex :
          wz1PaperGridIndex rho (cellCorner rho coarseCell) =
            otherCell :=
        (mem_wz1PaperGridCube rho otherCell _).mp cornerOther
      have ownIndex :
          wz1PaperGridIndex rho (cellCorner rho coarseCell) =
            coarseCell :=
        (mem_wz1PaperGridCube rho coarseCell _).mp cornerOwn
      exact otherIndex.symm.trans ownIndex
    simpa [cellEq] using otherCellMem
  · intro coarseCellMem point pointMem
    exact
      Set.mem_iUnion₂.mpr
        ⟨coarseCell, coarseCellMem, pointMem⟩

theorem terminalParentsAtCoarseCell_image
    (coarseCell : WZ2PaperCellIndex) :
    Finset.image
        families.restriction.coarseSelected.embedding
        (FrozenCoarseShading.terminalParentsAtCoarseCell
          input multiplicity parentClass treeCleanup exactification
            parentDegree core families coarseCell) =
      exactification.incidence.activeParentsAt
        core.ranges.terminalEdges coarseCell := by
  ext ambientParent
  constructor
  · intro parentImage
    rcases Finset.mem_image.mp parentImage with
      ⟨parent, parentMem, parentEq⟩
    have frozenMem :=
      (FrozenCoarseShading.mem_terminalParentsAtCoarseCell_iff
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families coarseCell parent).mp parentMem
    rw [exactification.incidence.mem_activeParentsAt_iff]
    rw [← parentEq]
    exact
      (input.mem_frozenCoarseCellsAt_iff
        multiplicity parentClass treeCleanup exactification
          core.ranges
          (families.restriction.coarseSelected.embedding parent)
          coarseCell).mp frozenMem
  · intro parentActive
    have degreePos :
        0 <
          exactification.incidence.parentCoarseDegree
            core.ranges.terminalEdges ambientParent coarseCell :=
      (exactification.incidence.mem_activeParentsAt_iff
        core.ranges.terminalEdges coarseCell ambientParent).mp parentActive
    have ambientTerminal : ambientParent ∈ families.terminalParents := by
      rw [families.terminalParents_eq]
      rcases Finset.card_pos.mp degreePos with ⟨edge, edgeMem⟩
      exact
        Finset.mem_image.mpr
          ⟨edge, (Finset.mem_filter.mp edgeMem).1,
            (Finset.mem_filter.mp edgeMem).2.1⟩
    have parentImage :
        ambientParent ∈
          Finset.image
            families.restriction.coarseSelected.embedding
              Finset.univ := by
      rw [families.coarse_image_univ]
      exact ambientTerminal
    rcases Finset.mem_image.mp parentImage with
      ⟨parent, _parentUniv, parentEq⟩
    apply Finset.mem_image.mpr
    refine ⟨parent, ?_, parentEq⟩
    apply
      (FrozenCoarseShading.mem_terminalParentsAtCoarseCell_iff
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families coarseCell parent).mpr
    apply
      (input.mem_frozenCoarseCellsAt_iff
        multiplicity parentClass treeCleanup exactification
          core.ranges
          (families.restriction.coarseSelected.embedding parent)
          coarseCell).mpr
    simpa [parentEq] using degreePos

theorem terminalParentsAtCoarseCell_card
    (coarseCell : WZ2PaperCellIndex) :
    (FrozenCoarseShading.terminalParentsAtCoarseCell
      input multiplicity parentClass treeCleanup exactification
        parentDegree core families coarseCell).card =
      core.ranges.activeParentCount coarseCell := by
  calc
    (FrozenCoarseShading.terminalParentsAtCoarseCell
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families coarseCell).card =
        (Finset.image
          families.restriction.coarseSelected.embedding
          (FrozenCoarseShading.terminalParentsAtCoarseCell
            input multiplicity parentClass treeCleanup exactification
              parentDegree core families coarseCell)).card := by
          symm
          exact
            Finset.card_image_of_injective _
              families.restriction.coarseSelected.embedding.injective
    _ =
        (exactification.incidence.activeParentsAt
          core.ranges.terminalEdges coarseCell).card := by
      rw [FrozenCoarseShading.terminalParentsAtCoarseCell_image
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families coarseCell]
    _ = core.ranges.activeParentCount coarseCell := rfl

theorem terminal_coarse_multiplicity_band
    (coarseCell : core.ranges.ActiveCoarseCell) :
    core.terminalCoarseMultiplicity
          input multiplicity parentClass treeCleanup
            exactification parentDegree ≤
        (FrozenCoarseShading.terminalParentsAtCoarseCell
          input multiplicity parentClass treeCleanup exactification
            parentDegree core families coarseCell.1).card ∧
      (FrozenCoarseShading.terminalParentsAtCoarseCell
          input multiplicity parentClass treeCleanup exactification
            parentDegree core families coarseCell.1).card ≤
        core.terminalCoarseMultiplicityLoss
            input multiplicity parentClass treeCleanup
              exactification parentDegree *
          core.terminalCoarseMultiplicity
            input multiplicity parentClass treeCleanup
              exactification parentDegree := by
  rw [FrozenCoarseShading.terminalParentsAtCoarseCell_card
    input multiplicity parentClass treeCleanup exactification
      parentDegree core families coarseCell.1]
  exact
    core.activeParentCount_coarseMultiplicity_band
      input multiplicity parentClass treeCleanup
        exactification parentDegree
        coarseCell.1
        (core.ranges.activeCoarseCell_degree_pos coarseCell)

end FrozenCoarseShading

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
