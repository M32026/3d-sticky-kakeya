import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreeCore

/-!
# Proposition 6.2: terminal four-degree ranges

This module combines the lower bounds supplied by the simultaneous peeling
core with the upper bounds frozen by the three preceding dyadic bins.  The
core is assumed to be a subset of the binned edge set; no additional
selection is performed.
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
    (data :
      PureWZ2Prop62FourDegreeIncidenceData
        Parent FineCell CoarseCell)

structure FourDegreeRangeData
    {TreeLabel : Type*} [DecidableEq TreeLabel]
    {initialEdges : Finset data.Edge}
    (bins : data.ThreeDegreeBinningData initialEdges)
    (parentThreshold fineCellThreshold
      parentCoarseThreshold coarseCellThreshold : ℕ)
    (treeLabels : Finset TreeLabel)
    (treeBad : Finset data.Edge → TreeLabel → Prop)
    (treeCharge : TreeLabel → ℕ) where
  peeling :
    data.SimultaneousPeelingCoreData
      bins.finalEdges
      parentThreshold fineCellThreshold
      parentCoarseThreshold coarseCellThreshold
      treeLabels treeBad treeCharge
  parentUpper : ℕ
  parent_upper :
    ∀ parent,
      data.parentDegree peeling.core parent ≤ parentUpper

namespace FourDegreeRangeData

variable
    {TreeLabel : Type*} [DecidableEq TreeLabel]
    {initialEdges : Finset data.Edge}
    {bins : data.ThreeDegreeBinningData initialEdges}
    {parentThreshold fineCellThreshold
      parentCoarseThreshold coarseCellThreshold : ℕ}
    {treeLabels : Finset TreeLabel}
    {treeBad : Finset data.Edge → TreeLabel → Prop}
    {treeCharge : TreeLabel → ℕ}
    (ranges :
      data.FourDegreeRangeData
        bins
        parentThreshold fineCellThreshold
        parentCoarseThreshold coarseCellThreshold
        treeLabels treeBad treeCharge)

theorem core_subset_initial :
    ranges.peeling.core ⊆ initialEdges :=
  ranges.peeling.core_subset.trans
    bins.finalEdges_subset_initial

theorem parent_range
    (parent : Parent)
    (degree_pos :
      0 < data.parentDegree ranges.peeling.core parent) :
    parentThreshold ≤
        data.parentDegree ranges.peeling.core parent ∧
      data.parentDegree ranges.peeling.core parent ≤
        ranges.parentUpper :=
  ⟨SimultaneousPeelingCoreData.parent_degree_lower
      data ranges.peeling parent degree_pos,
    ranges.parent_upper parent⟩

theorem fineCell_range
    (fineCell : FineCell)
    (degree_pos :
      0 < data.fineCellDegree ranges.peeling.core fineCell) :
    fineCellThreshold ≤
        data.fineCellDegree ranges.peeling.core fineCell ∧
      data.fineCellDegree ranges.peeling.core fineCell <
        2 ^ (bins.fineCellBin.level + 1) := by
  refine
    ⟨SimultaneousPeelingCoreData.fineCell_degree_lower
      data ranges.peeling fineCell degree_pos, ?_⟩
  have degreeCoreLe :
      data.fineCellDegree ranges.peeling.core fineCell ≤
        data.fineCellDegree bins.finalEdges fineCell := by
    apply Finset.card_le_card
    intro edge edgeMem
    have edgeData := Finset.mem_filter.mp edgeMem
    exact
      Finset.mem_filter.mpr
        ⟨ranges.peeling.core_subset edgeData.1, edgeData.2⟩
  have finalDegreePos :
      0 < data.fineCellDegree bins.finalEdges fineCell :=
    lt_of_lt_of_le degree_pos degreeCoreLe
  exact
    lt_of_le_of_lt degreeCoreLe <|
      ThreeDegreeBinningData.final_fineCellDegree_upper
        data bins fineCell finalDegreePos

theorem parentCoarse_range
    (parent : Parent) (coarseCell : CoarseCell)
    (degree_pos :
      0 <
        data.parentCoarseDegree
          ranges.peeling.core parent coarseCell) :
    parentCoarseThreshold ≤
        data.parentCoarseDegree
          ranges.peeling.core parent coarseCell ∧
      data.parentCoarseDegree
          ranges.peeling.core parent coarseCell <
        2 ^ (bins.parentCoarseBin.level + 1) := by
  refine
    ⟨SimultaneousPeelingCoreData.parentCoarse_degree_lower
      data ranges.peeling parent coarseCell degree_pos, ?_⟩
  have degreeCoreLe :
      data.parentCoarseDegree
          ranges.peeling.core parent coarseCell ≤
        data.parentCoarseDegree
          bins.finalEdges parent coarseCell := by
    apply Finset.card_le_card
    intro edge edgeMem
    have edgeData := Finset.mem_filter.mp edgeMem
    exact
      Finset.mem_filter.mpr
        ⟨ranges.peeling.core_subset edgeData.1, edgeData.2⟩
  have finalDegreePos :
      0 <
        data.parentCoarseDegree
          bins.finalEdges parent coarseCell :=
    lt_of_lt_of_le degree_pos degreeCoreLe
  exact
    lt_of_le_of_lt degreeCoreLe <|
      ThreeDegreeBinningData.final_parentCoarseDegree_upper
        data bins parent coarseCell finalDegreePos

theorem coarseCell_range
    (coarseCell : CoarseCell)
    (degree_pos :
      0 < data.coarseDegree ranges.peeling.core coarseCell) :
    coarseCellThreshold ≤
        data.coarseDegree ranges.peeling.core coarseCell ∧
      data.coarseDegree ranges.peeling.core coarseCell <
        2 ^ (bins.coarseCellBin.level + 1) := by
  refine
    ⟨SimultaneousPeelingCoreData.coarseCell_degree_lower
      data ranges.peeling coarseCell degree_pos, ?_⟩
  have degreeCoreLe :
      data.coarseDegree ranges.peeling.core coarseCell ≤
        data.coarseDegree bins.finalEdges coarseCell := by
    apply Finset.card_le_card
    intro edge edgeMem
    have edgeData := Finset.mem_filter.mp edgeMem
    exact
      Finset.mem_filter.mpr
        ⟨ranges.peeling.core_subset edgeData.1, edgeData.2⟩
  have finalDegreePos :
      0 < data.coarseDegree bins.finalEdges coarseCell :=
    lt_of_lt_of_le degree_pos degreeCoreLe
  exact
    lt_of_le_of_lt degreeCoreLe <|
      ThreeDegreeBinningData.final_coarseDegree_upper
        data bins coarseCell finalDegreePos

end FourDegreeRangeData

end PureWZ2Prop62FourDegreeIncidenceData

end Kakeya.Assouad

end
