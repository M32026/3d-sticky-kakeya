import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreeRanges
import Mathlib.Algebra.Order.Floor.Div

/-!
# Proposition 6.2: ranges derived from the four terminal degrees

No further regularization occurs after the simultaneous peeling core.
For every active coarse cell `Q`, the two exact identities

`D(Q) = sum_q d(q) = sum_P n(P,Q)`

and the terminal four-degree ranges control:

* the number `N(Q)` of active fine cells in `Q`;
* the number `c(Q)` of active parents at `Q`.

The common balancing count is

`W = max 1 (coarseLower ⌈/⌉ fineUpper)`.

The inequalities below are kept in exact natural-number, cross-multiplied
form.  In particular, `W ≤ N(Q)` for every active `Q`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62FourDegreeIncidenceData

variable
    {Parent FineCell CoarseCell : Type*}
    [DecidableEq Parent]
    [DecidableEq FineCell]
    [DecidableEq CoarseCell]
    {data :
      PureWZ2Prop62FourDegreeIncidenceData
        Parent FineCell CoarseCell}
    {TreeLabel : Type*} [DecidableEq TreeLabel]
    {initialEdges : Finset data.Edge}
    {bins : data.ThreeDegreeBinningData initialEdges}
    {parentLower fineLower parentCoarseLower coarseLower : ℕ}
    {treeLabels : Finset TreeLabel}
    {treeBad : Finset data.Edge → TreeLabel → Prop}
    {treeCharge : TreeLabel → ℕ}
    (ranges :
      data.FourDegreeRangeData
        bins parentLower fineLower
        parentCoarseLower coarseLower
        treeLabels treeBad treeCharge)

namespace FourDegreeRangeData

def terminalEdges : Finset data.Edge :=
  ranges.peeling.core

def fineUpper
    (_ranges :
      data.FourDegreeRangeData
        bins parentLower fineLower
        parentCoarseLower coarseLower
        treeLabels treeBad treeCharge) : ℕ :=
  2 ^ (bins.fineCellBin.level + 1)

def parentCoarseUpper
    (_ranges :
      data.FourDegreeRangeData
        bins parentLower fineLower
        parentCoarseLower coarseLower
        treeLabels treeBad treeCharge) : ℕ :=
  2 ^ (bins.parentCoarseBin.level + 1)

def coarseUpper
    (_ranges :
      data.FourDegreeRangeData
        bins parentLower fineLower
        parentCoarseLower coarseLower
        treeLabels treeBad treeCharge) : ℕ :=
  2 ^ (bins.coarseCellBin.level + 1)

def activeFineCount (coarseCell : CoarseCell) : ℕ :=
  (data.activeFineCellsAt ranges.terminalEdges coarseCell).card

def activeParentCount (coarseCell : CoarseCell) : ℕ :=
  (data.activeParentsAt ranges.terminalEdges coarseCell).card

def commonFineCellCount
    (_ranges :
      data.FourDegreeRangeData
        bins parentLower fineLower
        parentCoarseLower coarseLower
        treeLabels treeBad treeCharge) : ℕ :=
  max 1 (coarseLower ⌈/⌉ _ranges.fineUpper)

theorem activeFineCellsAt_nonempty
    {coarseCell : CoarseCell}
    (coarse_pos :
      0 < data.coarseDegree ranges.terminalEdges coarseCell) :
    (data.activeFineCellsAt
      ranges.terminalEdges coarseCell).Nonempty := by
  by_contra notNonempty
  have empty :
      data.activeFineCellsAt ranges.terminalEdges coarseCell = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp notNonempty
  have identity :=
    data.coarseDegree_eq_sum_fineCellDegree
      ranges.terminalEdges coarseCell
  rw [empty] at identity
  simp at identity
  omega

theorem activeParentsAt_nonempty
    {coarseCell : CoarseCell}
    (coarse_pos :
      0 < data.coarseDegree ranges.terminalEdges coarseCell) :
    (data.activeParentsAt
      ranges.terminalEdges coarseCell).Nonempty := by
  by_contra notNonempty
  have empty :
      data.activeParentsAt ranges.terminalEdges coarseCell = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp notNonempty
  have identity :=
    data.coarseDegree_eq_sum_parentCoarseDegree
      ranges.terminalEdges coarseCell
  rw [empty] at identity
  simp at identity
  omega

theorem fineLower_mul_activeFineCount_le_coarseDegree
    {coarseCell : CoarseCell}
    (coarse_pos :
      0 < data.coarseDegree ranges.terminalEdges coarseCell) :
    fineLower * ranges.activeFineCount coarseCell ≤
      data.coarseDegree ranges.terminalEdges coarseCell := by
  rw [data.coarseDegree_eq_sum_fineCellDegree
    ranges.terminalEdges coarseCell]
  have lower :
      ∀ fineCell ∈
          data.activeFineCellsAt
            ranges.terminalEdges coarseCell,
        fineLower ≤
          data.fineCellDegree
            ranges.terminalEdges fineCell := by
    intro fineCell fineCellMem
    have degreePos :=
      (data.mem_activeFineCellsAt_iff
        ranges.terminalEdges coarseCell fineCell).mp
          fineCellMem |>.1
    exact
      (FourDegreeRangeData.fineCell_range
        data ranges fineCell degreePos).1
  simpa [activeFineCount, Nat.mul_comm] using
    Finset.card_nsmul_le_sum
      (data.activeFineCellsAt
        ranges.terminalEdges coarseCell)
      (data.fineCellDegree ranges.terminalEdges)
      fineLower lower

theorem coarseDegree_lt_fineUpper_mul_activeFineCount
    {coarseCell : CoarseCell}
    (coarse_pos :
      0 < data.coarseDegree ranges.terminalEdges coarseCell) :
    data.coarseDegree ranges.terminalEdges coarseCell <
      ranges.fineUpper * ranges.activeFineCount coarseCell := by
  rw [data.coarseDegree_eq_sum_fineCellDegree
    ranges.terminalEdges coarseCell]
  let active :=
    data.activeFineCellsAt ranges.terminalEdges coarseCell
  have pointwiseLe :
      ∀ fineCell ∈ active,
        data.fineCellDegree ranges.terminalEdges fineCell ≤
          ranges.fineUpper := by
    intro fineCell fineCellMem
    have degreePos :=
      (data.mem_activeFineCellsAt_iff
        ranges.terminalEdges coarseCell fineCell).mp
          fineCellMem |>.1
    exact
      (FourDegreeRangeData.fineCell_range
        data ranges fineCell degreePos).2.le
  have pointwiseStrict :
      ∃ fineCell ∈ active,
        data.fineCellDegree ranges.terminalEdges fineCell <
          ranges.fineUpper := by
    rcases ranges.activeFineCellsAt_nonempty coarse_pos with
      ⟨fineCell, fineCellMem⟩
    have degreePos :=
      (data.mem_activeFineCellsAt_iff
        ranges.terminalEdges coarseCell fineCell).mp
          fineCellMem |>.1
    exact
      ⟨fineCell, fineCellMem,
        (FourDegreeRangeData.fineCell_range
          data ranges fineCell degreePos).2⟩
  have strictSum :
      (∑ fineCell ∈ active,
          data.fineCellDegree
            ranges.terminalEdges fineCell) <
        ∑ _fineCell ∈ active, ranges.fineUpper :=
    Finset.sum_lt_sum pointwiseLe pointwiseStrict
  simpa [active, activeFineCount, Nat.mul_comm] using strictSum

theorem parentCoarseLower_mul_activeParentCount_le_coarseDegree
    {coarseCell : CoarseCell}
    (coarse_pos :
      0 < data.coarseDegree ranges.terminalEdges coarseCell) :
    parentCoarseLower *
        ranges.activeParentCount coarseCell ≤
      data.coarseDegree ranges.terminalEdges coarseCell := by
  rw [data.coarseDegree_eq_sum_parentCoarseDegree
    ranges.terminalEdges coarseCell]
  have lower :
      ∀ parent ∈
          data.activeParentsAt
            ranges.terminalEdges coarseCell,
        parentCoarseLower ≤
          data.parentCoarseDegree
            ranges.terminalEdges parent coarseCell := by
    intro parent parentMem
    have degreePos :=
      (data.mem_activeParentsAt_iff
        ranges.terminalEdges coarseCell parent).mp parentMem
    exact
      (FourDegreeRangeData.parentCoarse_range
        data ranges parent coarseCell degreePos).1
  simpa [activeParentCount, Nat.mul_comm] using
    Finset.card_nsmul_le_sum
      (data.activeParentsAt
        ranges.terminalEdges coarseCell)
      (fun parent =>
        data.parentCoarseDegree
          ranges.terminalEdges parent coarseCell)
      parentCoarseLower lower

theorem coarseDegree_lt_parentCoarseUpper_mul_activeParentCount
    {coarseCell : CoarseCell}
    (coarse_pos :
      0 < data.coarseDegree ranges.terminalEdges coarseCell) :
    data.coarseDegree ranges.terminalEdges coarseCell <
      ranges.parentCoarseUpper *
        ranges.activeParentCount coarseCell := by
  rw [data.coarseDegree_eq_sum_parentCoarseDegree
    ranges.terminalEdges coarseCell]
  let active :=
    data.activeParentsAt ranges.terminalEdges coarseCell
  have pointwiseLe :
      ∀ parent ∈ active,
        data.parentCoarseDegree
            ranges.terminalEdges parent coarseCell ≤
          ranges.parentCoarseUpper := by
    intro parent parentMem
    have degreePos :=
      (data.mem_activeParentsAt_iff
        ranges.terminalEdges coarseCell parent).mp parentMem
    exact
      (FourDegreeRangeData.parentCoarse_range
        data ranges parent coarseCell degreePos).2.le
  have pointwiseStrict :
      ∃ parent ∈ active,
        data.parentCoarseDegree
            ranges.terminalEdges parent coarseCell <
          ranges.parentCoarseUpper := by
    rcases ranges.activeParentsAt_nonempty coarse_pos with
      ⟨parent, parentMem⟩
    have degreePos :=
      (data.mem_activeParentsAt_iff
        ranges.terminalEdges coarseCell parent).mp parentMem
    exact
      ⟨parent, parentMem,
        (FourDegreeRangeData.parentCoarse_range
          data ranges parent coarseCell degreePos).2⟩
  have strictSum :
      (∑ parent ∈ active,
          data.parentCoarseDegree
            ranges.terminalEdges parent coarseCell) <
        ∑ _parent ∈ active, ranges.parentCoarseUpper :=
    Finset.sum_lt_sum pointwiseLe pointwiseStrict
  simpa [active, activeParentCount, Nat.mul_comm] using strictSum

theorem coarse_degree_range
    {coarseCell : CoarseCell}
    (coarse_pos :
      0 < data.coarseDegree ranges.terminalEdges coarseCell) :
    coarseLower ≤
        data.coarseDegree ranges.terminalEdges coarseCell ∧
      data.coarseDegree ranges.terminalEdges coarseCell <
        ranges.coarseUpper :=
  FourDegreeRangeData.coarseCell_range
    data ranges coarseCell coarse_pos

theorem commonFineCellCount_pos :
    0 < ranges.commonFineCellCount := by
  simp [commonFineCellCount]

theorem commonFineCellCount_le_activeFineCount
    {coarseCell : CoarseCell}
    (coarse_pos :
      0 < data.coarseDegree ranges.terminalEdges coarseCell) :
    ranges.commonFineCellCount ≤
      ranges.activeFineCount coarseCell := by
  have activePos :
      0 < ranges.activeFineCount coarseCell :=
    (ranges.activeFineCellsAt_nonempty coarse_pos).card_pos
  have lowerCoarse :=
    (ranges.coarse_degree_range coarse_pos).1
  have upperByFine :=
    ranges.coarseDegree_lt_fineUpper_mul_activeFineCount
      coarse_pos
  have ceilLe :
      coarseLower ⌈/⌉ ranges.fineUpper ≤
        ranges.activeFineCount coarseCell := by
    apply
      (ceilDiv_le_iff_le_mul
        (by simp [fineUpper] : 0 < ranges.fineUpper)).mpr
    exact lowerCoarse.trans upperByFine.le
  exact max_le activePos ceilLe

end FourDegreeRangeData

end PureWZ2Prop62FourDegreeIncidenceData

end Kakeya.Assouad

end
