import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreeDerivedRanges

/-!
# Proposition 6.2: finite exact-balancing sample space

For every active coarse cell `Q`, choose one `W`-element subset of the active
fine cells `A(Q)`.  The global sample space is the finite dependent product
of these coordinate choices.

The edge restriction keeps an edge precisely when its fine-cell endpoint is
chosen in its coarse cell.  Thus all parent incidences of a chosen fine cell
are kept together.  This module proves the deterministic exact-balancing
fact: every active coarse cell has exactly `W` distinct selected fine cells.
It does not yet choose a sample satisfying the simultaneous parent-degree
lower tail estimate.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62FourDegreeIncidenceData
namespace FourDegreeRangeData

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

abbrev ActiveCoarseCell :=
  {coarseCell : CoarseCell //
    coarseCell ∈ data.activeCoarseCells ranges.terminalEdges}

def availableFineCells
    (coarseCell : ranges.ActiveCoarseCell) :
    Finset FineCell :=
  data.activeFineCellsAt ranges.terminalEdges coarseCell.1

def coordinateChoices
    (coarseCell : ranges.ActiveCoarseCell) :
    Finset (Finset FineCell) :=
  Finset.powersetCard
    ranges.commonFineCellCount
    (ranges.availableFineCells coarseCell)

abbrev BalancingSample :=
  ∀ coarseCell : ranges.ActiveCoarseCell,
    {selected : Finset FineCell //
      selected ∈ ranges.coordinateChoices coarseCell}

theorem activeCoarseCell_degree_pos
    (coarseCell : ranges.ActiveCoarseCell) :
    0 <
      data.coarseDegree ranges.terminalEdges coarseCell.1 := by
  exact
    (data.mem_activeCoarseCells_iff
      ranges.terminalEdges coarseCell.1).mp coarseCell.2

theorem coordinateChoices_nonempty
    (coarseCell : ranges.ActiveCoarseCell) :
    (ranges.coordinateChoices coarseCell).Nonempty := by
  have countLe :
      ranges.commonFineCellCount ≤
        (ranges.availableFineCells coarseCell).card := by
    exact
      ranges.commonFineCellCount_le_activeFineCount
        (ranges.activeCoarseCell_degree_pos coarseCell)
  rcases Finset.exists_subset_card_eq countLe with
    ⟨selected, selectedSubset, selectedCard⟩
  exact
    ⟨selected,
      Finset.mem_powersetCard.mpr
        ⟨selectedSubset, selectedCard⟩⟩

theorem balancingSample_nonempty :
    Nonempty ranges.BalancingSample := by
  let chooseAt :
      ∀ coarseCell : ranges.ActiveCoarseCell,
        {selected : Finset FineCell //
          selected ∈ ranges.coordinateChoices coarseCell} :=
    fun coarseCell =>
      ⟨Classical.choose
          (ranges.coordinateChoices_nonempty coarseCell),
        Classical.choose_spec
          (ranges.coordinateChoices_nonempty coarseCell)⟩
  exact ⟨chooseAt⟩

noncomputable instance balancingSampleFintype :
    Fintype ranges.BalancingSample := by
  dsimp only [BalancingSample]
  infer_instance

theorem sample_subset_available
    (sample : ranges.BalancingSample)
    (coarseCell : ranges.ActiveCoarseCell) :
    (sample coarseCell).1 ⊆
      ranges.availableFineCells coarseCell := by
  exact
    (Finset.mem_powersetCard.mp
      (sample coarseCell).2).1

theorem sample_card
    (sample : ranges.BalancingSample)
    (coarseCell : ranges.ActiveCoarseCell) :
    (sample coarseCell).1.card =
      ranges.commonFineCellCount := by
  exact
    (Finset.mem_powersetCard.mp
      (sample coarseCell).2).2

def selectedEdges
    (sample : ranges.BalancingSample) :
    Finset data.Edge :=
  ranges.terminalEdges.filter fun edge =>
    if coarseActive :
        data.edgeCoarseCell edge ∈
          data.activeCoarseCells ranges.terminalEdges then
      data.edgeFineCell edge ∈
        (sample
          ⟨data.edgeCoarseCell edge, coarseActive⟩).1
    else
      False

theorem selectedEdges_subset
    (sample : ranges.BalancingSample) :
    ranges.selectedEdges sample ⊆ ranges.terminalEdges :=
  Finset.filter_subset _ _

/-- Distinct fine cells selected by the new edge set inside `Q`. -/
def selectedFineCellsAt
    (sample : ranges.BalancingSample)
    (coarseCell : CoarseCell) :
    Finset FineCell :=
  ((ranges.selectedEdges sample).filter fun edge =>
    data.edgeCoarseCell edge = coarseCell).image
      data.edgeFineCell

theorem selectedFineCellsAt_eq_sample
    (sample : ranges.BalancingSample)
    (coarseCell : ranges.ActiveCoarseCell) :
    ranges.selectedFineCellsAt sample coarseCell.1 =
      (sample coarseCell).1 := by
  ext fineCell
  constructor
  · intro fineCellMem
    rcases Finset.mem_image.mp fineCellMem with
      ⟨edge, edgeMem, edgeFine⟩
    have edgeFiltered := Finset.mem_filter.mp edgeMem
    have edgeSelected := Finset.mem_filter.mp edgeFiltered.1
    have edgeCoarse :
        data.edgeCoarseCell edge = coarseCell.1 :=
      edgeFiltered.2
    have selectedCondition := edgeSelected.2
    change
      (if coarseActive :
          data.edgeCoarseCell edge ∈
            data.activeCoarseCells ranges.terminalEdges then
        data.edgeFineCell edge ∈
          (sample
            ⟨data.edgeCoarseCell edge, coarseActive⟩).1
      else False) at selectedCondition
    have edgeCoarseActive :
        data.edgeCoarseCell edge ∈
          data.activeCoarseCells ranges.terminalEdges := by
      simpa [edgeCoarse] using coarseCell.2
    simp only [dif_pos edgeCoarseActive] at selectedCondition
    have coarseSubtypeEq :
        (⟨data.edgeCoarseCell edge, edgeCoarseActive⟩ :
          ranges.ActiveCoarseCell) = coarseCell := by
      exact Subtype.ext edgeCoarse
    rw [coarseSubtypeEq] at selectedCondition
    subst fineCell
    exact selectedCondition
  · intro fineCellMem
    have fineCellAvailable :
        fineCell ∈
          data.activeFineCellsAt
            ranges.terminalEdges coarseCell.1 :=
      ranges.sample_subset_available sample coarseCell fineCellMem
    have fineDegreePos :
        0 <
          data.fineCellDegree
            ranges.terminalEdges fineCell :=
      (data.mem_activeFineCellsAt_iff
        ranges.terminalEdges coarseCell.1 fineCell).mp
          fineCellAvailable |>.1
    have fineCoarse :
        data.coarseCellOf fineCell = coarseCell.1 :=
      (data.mem_activeFineCellsAt_iff
        ranges.terminalEdges coarseCell.1 fineCell).mp
          fineCellAvailable |>.2
    rcases Finset.card_pos.mp fineDegreePos with
      ⟨edge, edgeMem⟩
    have edgeData := Finset.mem_filter.mp edgeMem
    have edgeFine :
        data.edgeFineCell edge = fineCell :=
      edgeData.2
    have edgeCoarse :
        data.edgeCoarseCell edge = coarseCell.1 := by
      rw [PureWZ2Prop62FourDegreeIncidenceData.edgeCoarseCell]
      rw [edgeFine, fineCoarse]
    have edgeCoarseActive :
        data.edgeCoarseCell edge ∈
          data.activeCoarseCells ranges.terminalEdges := by
      simpa [edgeCoarse] using coarseCell.2
    have coarseSubtypeEq :
        (⟨data.edgeCoarseCell edge, edgeCoarseActive⟩ :
          ranges.ActiveCoarseCell) = coarseCell := by
      exact Subtype.ext edgeCoarse
    have edgeSelected :
        edge ∈ ranges.selectedEdges sample := by
      apply Finset.mem_filter.mpr
      refine ⟨edgeData.1, ?_⟩
      change
        (if coarseActive :
            data.edgeCoarseCell edge ∈
              data.activeCoarseCells ranges.terminalEdges then
          data.edgeFineCell edge ∈
            (sample
              ⟨data.edgeCoarseCell edge, coarseActive⟩).1
        else False)
      simp only [dif_pos edgeCoarseActive]
      rw [coarseSubtypeEq]
      simpa [edgeFine] using fineCellMem
    exact
      Finset.mem_image.mpr
        ⟨edge,
          Finset.mem_filter.mpr
            ⟨edgeSelected, edgeCoarse⟩,
          edgeFine⟩

theorem selectedFineCellsAt_card
    (sample : ranges.BalancingSample)
    (coarseCell : ranges.ActiveCoarseCell) :
    (ranges.selectedFineCellsAt
      sample coarseCell.1).card =
      ranges.commonFineCellCount := by
  rw [ranges.selectedFineCellsAt_eq_sample
    sample coarseCell]
  exact ranges.sample_card sample coarseCell

theorem selectedEdges_keep_all_incident_parents
    (sample : ranges.BalancingSample)
    {edge : data.Edge}
    (edgeTerminal : edge ∈ ranges.terminalEdges)
    (fineSelected :
      data.edgeFineCell edge ∈
        (sample
          ⟨data.edgeCoarseCell edge,
            by
              rw [data.mem_activeCoarseCells_iff]
              apply Finset.card_pos.mpr
              exact
                ⟨edge,
                  Finset.mem_filter.mpr
                    ⟨edgeTerminal, rfl⟩⟩⟩).1) :
    edge ∈ ranges.selectedEdges sample := by
  apply Finset.mem_filter.mpr
  refine ⟨edgeTerminal, ?_⟩
  let coarseActive :
      data.edgeCoarseCell edge ∈
        data.activeCoarseCells ranges.terminalEdges := by
    rw [data.mem_activeCoarseCells_iff]
    apply Finset.card_pos.mpr
    exact
      ⟨edge,
        Finset.mem_filter.mpr
          ⟨edgeTerminal, rfl⟩⟩
  simp only [selectedEdges, dif_pos coarseActive]
  simpa only using fineSelected

def parentFineCellsAt
    (parent : Parent)
    (coarseCell : ranges.ActiveCoarseCell) :
    Finset FineCell :=
  (ranges.terminalEdges.filter fun edge =>
    data.edgeParent edge = parent ∧
      data.edgeCoarseCell edge = coarseCell.1).image
        data.edgeFineCell

theorem parentFineCellsAt_subset_available
    (parent : Parent)
    (coarseCell : ranges.ActiveCoarseCell) :
    ranges.parentFineCellsAt parent coarseCell ⊆
      ranges.availableFineCells coarseCell := by
  intro fineCell fineMem
  rcases Finset.mem_image.mp fineMem with
    ⟨edge, edgeMem, edgeFine⟩
  have edgeData := Finset.mem_filter.mp edgeMem
  apply
    (data.mem_activeFineCellsAt_iff
      ranges.terminalEdges coarseCell.1 fineCell).mpr
  constructor
  · apply Finset.card_pos.mpr
    exact
      ⟨edge,
        Finset.mem_filter.mpr
          ⟨edgeData.1, edgeFine⟩⟩
  · rw [← edgeFine]
    exact edgeData.2.2

theorem parentFineCellsAt_card
    (parent : Parent)
    (coarseCell : ranges.ActiveCoarseCell) :
    (ranges.parentFineCellsAt parent coarseCell).card =
      data.parentCoarseDegree
        ranges.terminalEdges parent coarseCell.1 := by
  let edges :=
    ranges.terminalEdges.filter fun edge =>
      data.edgeParent edge = parent ∧
        data.edgeCoarseCell edge = coarseCell.1
  have edgeFineInjective :
      Set.InjOn data.edgeFineCell edges := by
    intro first firstMem second secondMem fineEq
    have firstParent :
        data.edgeParent first = parent :=
      (Finset.mem_filter.mp firstMem).2.1
    have secondParent :
        data.edgeParent second = parent :=
      (Finset.mem_filter.mp secondMem).2.1
    apply Subtype.ext
    apply Prod.ext
    · exact firstParent.trans secondParent.symm
    · exact fineEq
  change (edges.image data.edgeFineCell).card = edges.card
  exact Finset.card_image_of_injOn edgeFineInjective

theorem parentDegree_eq_sum_parentFineCellsAt
    (parent : Parent) :
    data.parentDegree ranges.terminalEdges parent =
      ∑ coarseCell : ranges.ActiveCoarseCell,
        (ranges.parentFineCellsAt parent coarseCell).card := by
  let parentEdges :=
    ranges.terminalEdges.filter fun edge =>
      data.edgeParent edge = parent
  have fiberwise :=
    Finset.sum_card_fiberwise_eq_card_filter
      parentEdges
      (data.activeCoarseCells ranges.terminalEdges)
      data.edgeCoarseCell
  have allCoarse :
      parentEdges.filter (fun edge =>
          data.edgeCoarseCell edge ∈
            data.activeCoarseCells ranges.terminalEdges) =
        parentEdges := by
    apply Finset.filter_true_of_mem
    intro edge edgeMem
    have edgeTerminal := (Finset.mem_filter.mp edgeMem).1
    exact
      Finset.mem_image.mpr
        ⟨edge, edgeTerminal, rfl⟩
  rw [allCoarse] at fiberwise
  rw [parentDegree]
  change parentEdges.card = _
  rw [fiberwise.symm]
  rw [Finset.sum_subtype
    (data.activeCoarseCells ranges.terminalEdges)
    (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro coarseCell coarseMem
  rw [ranges.parentFineCellsAt_card parent coarseCell]
  simp only [parentEdges, parentCoarseDegree,
    Finset.filter_filter, and_assoc]

theorem selectedParentDegree_eq_sum_inter
    (sample : ranges.BalancingSample)
    (parent : Parent) :
    data.parentDegree (ranges.selectedEdges sample) parent =
      ∑ coarseCell : ranges.ActiveCoarseCell,
        ((sample coarseCell).1 ∩
          ranges.parentFineCellsAt parent coarseCell).card := by
  let selectedParentEdges :=
    (ranges.selectedEdges sample).filter fun edge =>
      data.edgeParent edge = parent
  have fiberwise :=
    Finset.sum_card_fiberwise_eq_card_filter
      selectedParentEdges
      (data.activeCoarseCells ranges.terminalEdges)
      data.edgeCoarseCell
  have allCoarse :
      selectedParentEdges.filter (fun edge =>
          data.edgeCoarseCell edge ∈
            data.activeCoarseCells ranges.terminalEdges) =
        selectedParentEdges := by
    apply Finset.filter_true_of_mem
    intro edge edgeMem
    have edgeSelected := (Finset.mem_filter.mp edgeMem).1
    have edgeTerminal := ranges.selectedEdges_subset sample edgeSelected
    exact
      Finset.mem_image.mpr
        ⟨edge, edgeTerminal, rfl⟩
  rw [allCoarse] at fiberwise
  rw [parentDegree]
  change selectedParentEdges.card = _
  rw [fiberwise.symm]
  rw [Finset.sum_subtype
    (data.activeCoarseCells ranges.terminalEdges)
    (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro activeCoarse _
  let selectedCoarseEdges :=
    selectedParentEdges.filter fun edge =>
      data.edgeCoarseCell edge = activeCoarse.1
  have edgeFineInjective :
      Set.InjOn data.edgeFineCell selectedCoarseEdges := by
    intro first firstMem second secondMem fineEq
    have firstParent :
        data.edgeParent first = parent :=
      (Finset.mem_filter.mp
        (Finset.mem_filter.mp firstMem).1).2
    have secondParent :
        data.edgeParent second = parent :=
      (Finset.mem_filter.mp
        (Finset.mem_filter.mp secondMem).1).2
    apply Subtype.ext
    exact Prod.ext (firstParent.trans secondParent.symm) fineEq
  rw [← Finset.card_image_of_injOn edgeFineInjective]
  apply congrArg Finset.card
  ext fineCell
  simp only [Finset.mem_image, selectedCoarseEdges]
  constructor
  · rintro ⟨edge, edgeMem, edgeFine⟩
    have edgeData := Finset.mem_filter.mp edgeMem
    have edgeSelectedData :=
      Finset.mem_filter.mp
        (Finset.mem_filter.mp edgeData.1).1
    have edgeParent :=
      (Finset.mem_filter.mp edgeData.1).2
    have coarseActive :
        data.edgeCoarseCell edge ∈
          data.activeCoarseCells ranges.terminalEdges := by
      rw [edgeData.2]
      exact activeCoarse.2
    simp only [dif_pos coarseActive] at edgeSelectedData
    have coarseSubtypeEq :
        (⟨data.edgeCoarseCell edge, coarseActive⟩ :
          ranges.ActiveCoarseCell) = activeCoarse := by
      exact Subtype.ext edgeData.2
    have fineSelected :
        data.edgeFineCell edge ∈ (sample activeCoarse).1 := by
      rw [coarseSubtypeEq] at edgeSelectedData
      exact edgeSelectedData.2
    have fineMarked :
        data.edgeFineCell edge ∈
          ranges.parentFineCellsAt parent activeCoarse := by
      apply Finset.mem_image.mpr
      exact
        ⟨edge,
          Finset.mem_filter.mpr
            ⟨ranges.selectedEdges_subset sample
                (Finset.mem_filter.mp edgeData.1).1,
              edgeParent, edgeData.2⟩,
          rfl⟩
    exact
      Finset.mem_inter.mpr
        ⟨by simpa [edgeFine] using fineSelected,
          by simpa [edgeFine] using fineMarked⟩
  · intro fineMem
    have fineData := Finset.mem_inter.mp fineMem
    rcases Finset.mem_image.mp fineData.2 with
      ⟨edge, edgeMem, edgeFine⟩
    have edgeData := Finset.mem_filter.mp edgeMem
    have coarseActive :
        data.edgeCoarseCell edge ∈
          data.activeCoarseCells ranges.terminalEdges := by
      rw [edgeData.2.2]
      exact activeCoarse.2
    have coarseSubtypeEq :
        (⟨data.edgeCoarseCell edge, coarseActive⟩ :
          ranges.ActiveCoarseCell) = activeCoarse := by
      exact Subtype.ext edgeData.2.2
    have fineSelected :
        data.edgeFineCell edge ∈
          (sample
            ⟨data.edgeCoarseCell edge, coarseActive⟩).1 := by
      rw [coarseSubtypeEq]
      simpa [edgeFine] using fineData.1
    have edgeSelected :
        edge ∈ ranges.selectedEdges sample :=
      ranges.selectedEdges_keep_all_incident_parents
        sample edgeData.1 fineSelected
    refine
      ⟨edge,
        Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr
              ⟨edgeSelected, edgeData.2.1⟩,
            edgeData.2.2⟩,
        edgeFine⟩

end FourDegreeRangeData
end PureWZ2Prop62FourDegreeIncidenceData

end Kakeya.Assouad

end
