import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreeBinning
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FiniteBlockPeeling

/-!
# Proposition 6.2: simultaneous four-degree and tree peeling

The paper interleaves four low-degree deletions with reference-tree
deletions.  They must be performed in one terminal process: a later tree
deletion may make a previously acceptable degree too small.

This module combines the four incidence labels with an arbitrary finite
family of already charged tree blocks and applies the one-time block peeling
lemma once.  The output has all four terminal lower-degree conditions and all
tree stability conditions simultaneously.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

inductive PureWZ2Prop62FourDegreeLabel
    (Parent FineCell CoarseCell : Type*)
  | parent : Parent → PureWZ2Prop62FourDegreeLabel Parent FineCell CoarseCell
  | fineCell : FineCell →
      PureWZ2Prop62FourDegreeLabel Parent FineCell CoarseCell
  | parentCoarse : Parent → CoarseCell →
      PureWZ2Prop62FourDegreeLabel Parent FineCell CoarseCell
  | coarseCell : CoarseCell →
      PureWZ2Prop62FourDegreeLabel Parent FineCell CoarseCell
  deriving DecidableEq

namespace PureWZ2Prop62FourDegreeIncidenceData

variable
    {Parent FineCell CoarseCell : Type*}
    [DecidableEq Parent]
    [DecidableEq FineCell]
    [DecidableEq CoarseCell]
    (data :
      PureWZ2Prop62FourDegreeIncidenceData
        Parent FineCell CoarseCell)

abbrev FourDegreeLabel
    (_data :
      PureWZ2Prop62FourDegreeIncidenceData
        Parent FineCell CoarseCell) :=
  PureWZ2Prop62FourDegreeLabel Parent FineCell CoarseCell

def fourDegreeIncident
    (label : data.FourDegreeLabel) (edge : data.Edge) : Prop :=
  match label with
  | .parent parent =>
      data.edgeParent edge = parent
  | .fineCell fineCell =>
      data.edgeFineCell edge = fineCell
  | .parentCoarse parent coarseCell =>
      data.edgeParent edge = parent ∧
        data.edgeCoarseCell edge = coarseCell
  | .coarseCell coarseCell =>
      data.edgeCoarseCell edge = coarseCell

def fourDegreeBlock
    (label : data.FourDegreeLabel) : Finset data.Edge :=
  data.allEdges.filter fun edge =>
    data.fourDegreeIncident label edge

def fourDegree
    (edges : Finset data.Edge)
    (label : data.FourDegreeLabel) : ℕ :=
  (edges ∩ data.fourDegreeBlock label).card

def fourDegreeThreshold
    (parentThreshold fineCellThreshold
      parentCoarseThreshold coarseCellThreshold : ℕ)
    (label : data.FourDegreeLabel) : ℕ :=
  match label with
  | .parent _ => parentThreshold
  | .fineCell _ => fineCellThreshold
  | .parentCoarse _ _ => parentCoarseThreshold
  | .coarseCell _ => coarseCellThreshold

def fourDegreeLabels
    (edges : Finset data.Edge) :
    Finset data.FourDegreeLabel :=
  (((edges.image fun edge =>
        PureWZ2Prop62FourDegreeLabel.parent
          (data.edgeParent edge)) ∪
      (edges.image fun edge =>
        PureWZ2Prop62FourDegreeLabel.fineCell
          (data.edgeFineCell edge))) ∪
    (edges.image fun edge =>
      PureWZ2Prop62FourDegreeLabel.parentCoarse
        (data.edgeParent edge) (data.edgeCoarseCell edge))) ∪
    (edges.image fun edge =>
      PureWZ2Prop62FourDegreeLabel.coarseCell
        (data.edgeCoarseCell edge))

def fourDegreeCapacity
    (parentThreshold fineCellThreshold
      parentCoarseThreshold coarseCellThreshold : ℕ)
    (edges : Finset data.Edge) : ℕ :=
  ∑ label ∈ data.fourDegreeLabels edges,
    (data.fourDegreeThreshold
        parentThreshold fineCellThreshold
        parentCoarseThreshold coarseCellThreshold label -
      1)

theorem fourDegreeCapacity_eq
    (parentThreshold fineCellThreshold
      parentCoarseThreshold coarseCellThreshold : ℕ)
    (edges : Finset data.Edge) :
    data.fourDegreeCapacity
        parentThreshold fineCellThreshold
        parentCoarseThreshold coarseCellThreshold edges =
      (data.activeParents edges).card *
          (parentThreshold - 1) +
        (data.activeFineCells edges).card *
          (fineCellThreshold - 1) +
        (data.activeParentCoarsePairs edges).card *
          (parentCoarseThreshold - 1) +
        (data.activeCoarseCells edges).card *
          (coarseCellThreshold - 1) := by
  let parentLabels :=
    edges.image fun edge =>
      PureWZ2Prop62FourDegreeLabel.parent
        (FineCell := FineCell) (CoarseCell := CoarseCell)
        (data.edgeParent edge)
  let fineCellLabels :=
    edges.image fun edge =>
      PureWZ2Prop62FourDegreeLabel.fineCell
        (Parent := Parent) (CoarseCell := CoarseCell)
        (data.edgeFineCell edge)
  let parentCoarseLabels :=
    edges.image fun edge =>
      PureWZ2Prop62FourDegreeLabel.parentCoarse
        (FineCell := FineCell)
        (data.edgeParent edge) (data.edgeCoarseCell edge)
  let coarseCellLabels :=
    edges.image fun edge =>
      PureWZ2Prop62FourDegreeLabel.coarseCell
        (Parent := Parent) (FineCell := FineCell)
        (data.edgeCoarseCell edge)
  have parentFineDisjoint :
      Disjoint parentLabels fineCellLabels := by
    rw [Finset.disjoint_left]
    intro label parentMem fineMem
    rcases Finset.mem_image.mp parentMem with
      ⟨edge, edgeMem, rfl⟩
    rcases Finset.mem_image.mp fineMem with
      ⟨other, otherMem, equality⟩
    cases equality
  have parentFineParentCoarseDisjoint :
      Disjoint
        (parentLabels ∪ fineCellLabels)
        parentCoarseLabels := by
    rw [Finset.disjoint_left]
    intro label labelMem parentCoarseMem
    rcases Finset.mem_union.mp labelMem with
      parentMem | fineMem
    · rcases Finset.mem_image.mp parentMem with
        ⟨edge, edgeMem, rfl⟩
      rcases Finset.mem_image.mp parentCoarseMem with
        ⟨other, otherMem, equality⟩
      cases equality
    · rcases Finset.mem_image.mp fineMem with
        ⟨edge, edgeMem, rfl⟩
      rcases Finset.mem_image.mp parentCoarseMem with
        ⟨other, otherMem, equality⟩
      cases equality
  have allCoarseDisjoint :
      Disjoint
        ((parentLabels ∪ fineCellLabels) ∪ parentCoarseLabels)
        coarseCellLabels := by
    rw [Finset.disjoint_left]
    intro label labelMem coarseMem
    rcases Finset.mem_union.mp labelMem with
      parentFineMem | parentCoarseMem
    · rcases Finset.mem_union.mp parentFineMem with
        parentMem | fineMem
      · rcases Finset.mem_image.mp parentMem with
          ⟨edge, edgeMem, rfl⟩
        rcases Finset.mem_image.mp coarseMem with
          ⟨other, otherMem, equality⟩
        cases equality
      · rcases Finset.mem_image.mp fineMem with
          ⟨edge, edgeMem, rfl⟩
        rcases Finset.mem_image.mp coarseMem with
          ⟨other, otherMem, equality⟩
        cases equality
    · rcases Finset.mem_image.mp parentCoarseMem with
        ⟨edge, edgeMem, rfl⟩
      rcases Finset.mem_image.mp coarseMem with
        ⟨other, otherMem, equality⟩
      cases equality
  have parentSum :
      (∑ label ∈ parentLabels,
          (data.fourDegreeThreshold
              parentThreshold fineCellThreshold
              parentCoarseThreshold coarseCellThreshold label -
            1)) =
        (data.activeParents edges).card *
          (parentThreshold - 1) := by
    have labelsEq :
        parentLabels =
          (data.activeParents edges).image fun parent =>
            PureWZ2Prop62FourDegreeLabel.parent
              (FineCell := FineCell) (CoarseCell := CoarseCell)
              parent := by
      ext label
      simp [parentLabels, activeParents]
    rw [labelsEq, Finset.sum_image]
    · simp [fourDegreeThreshold]
    · intro first firstMem second secondMem equality
      exact PureWZ2Prop62FourDegreeLabel.parent.inj equality
  have fineCellSum :
      (∑ label ∈ fineCellLabels,
          (data.fourDegreeThreshold
              parentThreshold fineCellThreshold
              parentCoarseThreshold coarseCellThreshold label -
            1)) =
        (data.activeFineCells edges).card *
          (fineCellThreshold - 1) := by
    have labelsEq :
        fineCellLabels =
          (data.activeFineCells edges).image fun fineCell =>
            PureWZ2Prop62FourDegreeLabel.fineCell
              (Parent := Parent) (CoarseCell := CoarseCell)
              fineCell := by
      ext label
      simp [fineCellLabels, activeFineCells]
    rw [labelsEq, Finset.sum_image]
    · simp [fourDegreeThreshold]
    · intro first firstMem second secondMem equality
      exact PureWZ2Prop62FourDegreeLabel.fineCell.inj equality
  have parentCoarseSum :
      (∑ label ∈ parentCoarseLabels,
          (data.fourDegreeThreshold
              parentThreshold fineCellThreshold
              parentCoarseThreshold coarseCellThreshold label -
            1)) =
        (data.activeParentCoarsePairs edges).card *
          (parentCoarseThreshold - 1) := by
    have labelsEq :
        parentCoarseLabels =
          (data.activeParentCoarsePairs edges).image fun pair =>
            PureWZ2Prop62FourDegreeLabel.parentCoarse
              (FineCell := FineCell) pair.1 pair.2 := by
      ext label
      simp [
        parentCoarseLabels, activeParentCoarsePairs,
        edgeParentCoarse
      ]
    rw [labelsEq, Finset.sum_image]
    · simp [fourDegreeThreshold]
    · intro first firstMem second secondMem equality
      exact Prod.ext
        (PureWZ2Prop62FourDegreeLabel.parentCoarse.inj equality).1
        (PureWZ2Prop62FourDegreeLabel.parentCoarse.inj equality).2
  have coarseCellSum :
      (∑ label ∈ coarseCellLabels,
          (data.fourDegreeThreshold
              parentThreshold fineCellThreshold
              parentCoarseThreshold coarseCellThreshold label -
            1)) =
        (data.activeCoarseCells edges).card *
          (coarseCellThreshold - 1) := by
    have labelsEq :
        coarseCellLabels =
          (data.activeCoarseCells edges).image fun coarseCell =>
            PureWZ2Prop62FourDegreeLabel.coarseCell
              (Parent := Parent) (FineCell := FineCell)
              coarseCell := by
      ext label
      simp [coarseCellLabels, activeCoarseCells]
    rw [labelsEq, Finset.sum_image]
    · simp [fourDegreeThreshold]
    · intro first firstMem second secondMem equality
      exact PureWZ2Prop62FourDegreeLabel.coarseCell.inj equality
  rw [fourDegreeCapacity]
  rw [show data.fourDegreeLabels edges =
      ((parentLabels ∪ fineCellLabels) ∪ parentCoarseLabels) ∪
        coarseCellLabels by rfl]
  rw [
    Finset.sum_union allCoarseDisjoint,
    Finset.sum_union parentFineParentCoarseDisjoint,
    Finset.sum_union parentFineDisjoint,
    parentSum, fineCellSum, parentCoarseSum, coarseCellSum
  ]

@[simp]
theorem fourDegree_parent
    (edges : Finset data.Edge) (parent : Parent) :
    data.fourDegree edges
        (.parent parent) =
      data.parentDegree edges parent := by
  apply congrArg Finset.card
  ext edge
  simp [
    fourDegree, fourDegreeBlock, allEdges,
    fourDegreeIncident, parentDegree
  ]

@[simp]
theorem fourDegree_fineCell
    (edges : Finset data.Edge) (fineCell : FineCell) :
    data.fourDegree edges
        (.fineCell fineCell) =
      data.fineCellDegree edges fineCell := by
  apply congrArg Finset.card
  ext edge
  simp [
    fourDegree, fourDegreeBlock, allEdges,
    fourDegreeIncident, fineCellDegree
  ]

@[simp]
theorem fourDegree_parentCoarse
    (edges : Finset data.Edge)
    (parent : Parent) (coarseCell : CoarseCell) :
    data.fourDegree edges
        (.parentCoarse parent coarseCell) =
      data.parentCoarseDegree edges parent coarseCell := by
  apply congrArg Finset.card
  ext edge
  simp [
    fourDegree, fourDegreeBlock, allEdges,
    fourDegreeIncident, parentCoarseDegree
  ]

@[simp]
theorem fourDegree_coarseCell
    (edges : Finset data.Edge) (coarseCell : CoarseCell) :
    data.fourDegree edges
        (.coarseCell coarseCell) =
      data.coarseDegree edges coarseCell := by
  apply congrArg Finset.card
  ext edge
  simp [
    fourDegree, fourDegreeBlock, allEdges,
    fourDegreeIncident, coarseDegree
  ]

theorem fourDegreeLabel_mem_of_degree_pos
    {initialEdges core : Finset data.Edge}
    (core_subset : core ⊆ initialEdges)
    (label : data.FourDegreeLabel)
    (degree_pos : 0 < data.fourDegree core label) :
    label ∈ data.fourDegreeLabels initialEdges := by
  rcases Finset.card_pos.mp degree_pos with
    ⟨edge, edgeMem⟩
  have edgeCore : edge ∈ core :=
    (Finset.mem_inter.mp edgeMem).1
  have edgeInitial : edge ∈ initialEdges :=
    core_subset edgeCore
  have edgeIncident :
      data.fourDegreeIncident label edge :=
    (Finset.mem_filter.mp
      (Finset.mem_inter.mp edgeMem).2).2
  cases label with
  | parent parent =>
      have edgeParent :
          data.edgeParent edge = parent :=
        edgeIncident
      have parentMem :
          PureWZ2Prop62FourDegreeLabel.parent parent ∈
            initialEdges.image (fun candidate =>
              PureWZ2Prop62FourDegreeLabel.parent
                (FineCell := FineCell)
                (CoarseCell := CoarseCell)
                (data.edgeParent candidate)) :=
        Finset.mem_image.mpr
          ⟨edge, edgeInitial, by rw [edgeParent]⟩
      unfold fourDegreeLabels
      simp only [Finset.mem_union]
      exact Or.inl <| Or.inl <| Or.inl parentMem
  | fineCell fineCell =>
      have edgeFineCell :
          data.edgeFineCell edge = fineCell :=
        edgeIncident
      have fineCellMem :
          PureWZ2Prop62FourDegreeLabel.fineCell fineCell ∈
            initialEdges.image (fun candidate =>
              PureWZ2Prop62FourDegreeLabel.fineCell
                (Parent := Parent)
                (CoarseCell := CoarseCell)
                (data.edgeFineCell candidate)) :=
        Finset.mem_image.mpr
          ⟨edge, edgeInitial, by rw [edgeFineCell]⟩
      unfold fourDegreeLabels
      simp only [Finset.mem_union]
      exact Or.inl <| Or.inl <| Or.inr fineCellMem
  | parentCoarse parent coarseCell =>
      have edgeParent :
          data.edgeParent edge = parent :=
        edgeIncident.1
      have edgeCoarse :
          data.edgeCoarseCell edge = coarseCell :=
        edgeIncident.2
      have parentCoarseMem :
          PureWZ2Prop62FourDegreeLabel.parentCoarse
              parent coarseCell ∈
            initialEdges.image (fun candidate =>
              PureWZ2Prop62FourDegreeLabel.parentCoarse
                (FineCell := FineCell)
                (data.edgeParent candidate)
                (data.edgeCoarseCell candidate)) :=
        Finset.mem_image.mpr
          ⟨edge, edgeInitial, by
            rw [edgeParent, edgeCoarse]⟩
      unfold fourDegreeLabels
      simp only [Finset.mem_union]
      exact Or.inl <| Or.inr parentCoarseMem
  | coarseCell coarseCell =>
      have edgeCoarse :
          data.edgeCoarseCell edge = coarseCell :=
        edgeIncident
      have coarseCellMem :
          PureWZ2Prop62FourDegreeLabel.coarseCell coarseCell ∈
            initialEdges.image (fun candidate =>
              PureWZ2Prop62FourDegreeLabel.coarseCell
                (Parent := Parent)
                (FineCell := FineCell)
                (data.edgeCoarseCell candidate)) :=
        Finset.mem_image.mpr
          ⟨edge, edgeInitial, by rw [edgeCoarse]⟩
      unfold fourDegreeLabels
      simp only [Finset.mem_union]
      exact Or.inr coarseCellMem

structure SimultaneousPeelingCoreData
    {TreeLabel : Type*} [DecidableEq TreeLabel]
    (initialEdges : Finset data.Edge)
    (parentThreshold fineCellThreshold
      parentCoarseThreshold coarseCellThreshold : ℕ)
    (treeLabels : Finset TreeLabel)
    (treeBad : Finset data.Edge → TreeLabel → Prop)
    (treeCharge : TreeLabel → ℕ) where
  core : Finset data.Edge
  core_subset : core ⊆ initialEdges
  four_degree_core :
    ∀ label ∈ data.fourDegreeLabels initialEdges,
      0 < data.fourDegree core label →
        data.fourDegreeThreshold
            parentThreshold fineCellThreshold
            parentCoarseThreshold coarseCellThreshold label ≤
          data.fourDegree core label
  tree_stable :
    ∀ label ∈ treeLabels, ¬treeBad core label
  removed_le :
    (initialEdges \ core).card ≤
      data.fourDegreeCapacity
          parentThreshold fineCellThreshold
          parentCoarseThreshold coarseCellThreshold initialEdges +
        ∑ label ∈ treeLabels, treeCharge label

theorem pureWZ2_prop62_simultaneous_peeling_core
    {TreeLabel : Type*} [DecidableEq TreeLabel]
    (initialEdges : Finset data.Edge)
    (parentThreshold fineCellThreshold
      parentCoarseThreshold coarseCellThreshold : ℕ)
    (treeLabels : Finset TreeLabel)
    (treeBlock : TreeLabel → Finset data.Edge)
    (treeBad : Finset data.Edge → TreeLabel → Prop)
    (treeCharge : TreeLabel → ℕ)
    (tree_bad_nonempty :
      ∀ edges label,
        treeBad edges label →
          (edges ∩ treeBlock label).Nonempty)
    (tree_bad_card_le :
      ∀ edges label,
        treeBad edges label →
          (edges ∩ treeBlock label).card ≤ treeCharge label) :
    Nonempty
      (data.SimultaneousPeelingCoreData
        initialEdges
        parentThreshold fineCellThreshold
        parentCoarseThreshold coarseCellThreshold
        treeLabels treeBad treeCharge) := by
  let coordinateLabels :=
    data.fourDegreeLabels initialEdges
  let allLabels : Finset (data.FourDegreeLabel ⊕ TreeLabel) :=
    coordinateLabels.image Sum.inl ∪
      treeLabels.image Sum.inr
  let block :
      data.FourDegreeLabel ⊕ TreeLabel →
        Finset data.Edge
    | .inl label => data.fourDegreeBlock label
    | .inr label => treeBlock label
  let bad :
      Finset data.Edge →
        data.FourDegreeLabel ⊕ TreeLabel → Prop
    | edges, .inl label =>
        0 < data.fourDegree edges label ∧
          data.fourDegree edges label <
            data.fourDegreeThreshold
              parentThreshold fineCellThreshold
              parentCoarseThreshold coarseCellThreshold label
    | edges, .inr label =>
        treeBad edges label
  let charge :
      data.FourDegreeLabel ⊕ TreeLabel → ℕ
    | .inl label =>
        data.fourDegreeThreshold
            parentThreshold fineCellThreshold
            parentCoarseThreshold coarseCellThreshold label -
          1
    | .inr label =>
        treeCharge label
  have badNonempty :
      ∀ edges label,
        bad edges label →
          (edges ∩ block label).Nonempty := by
    intro edges label labelBad
    cases label with
    | inl coordinate =>
        exact
          Finset.card_pos.mp labelBad.1
    | inr tree =>
        exact tree_bad_nonempty edges tree labelBad
  have badCardLe :
      ∀ edges label,
        bad edges label →
          (edges ∩ block label).card ≤
            charge label := by
    intro edges label labelBad
    cases label with
    | inl coordinate =>
        change
          data.fourDegree edges coordinate ≤
            data.fourDegreeThreshold
                parentThreshold fineCellThreshold
                parentCoarseThreshold coarseCellThreshold coordinate -
              1
        omega
    | inr tree =>
        exact tree_bad_card_le edges tree labelBad
  rcases
      pureWZ2_prop62_finite_block_peeling
        block bad charge badNonempty badCardLe
        initialEdges allLabels
    with
    ⟨core, coreSubset, noBad, removedBound⟩
  have coordinateStable :
      ∀ label ∈ coordinateLabels,
        0 < data.fourDegree core label →
          data.fourDegreeThreshold
              parentThreshold fineCellThreshold
              parentCoarseThreshold coarseCellThreshold label ≤
            data.fourDegree core label := by
    intro label labelMem degreePos
    have labelInAll :
        Sum.inl label ∈ allLabels := by
      exact Finset.mem_union_left _ <|
        Finset.mem_image.mpr
          ⟨label, labelMem, rfl⟩
    have labelNotBad :=
      noBad (Sum.inl label) labelInAll
    change
      ¬(0 < data.fourDegree core label ∧
        data.fourDegree core label <
          data.fourDegreeThreshold
            parentThreshold fineCellThreshold
            parentCoarseThreshold coarseCellThreshold label)
      at labelNotBad
    omega
  have treeStable :
      ∀ label ∈ treeLabels,
        ¬treeBad core label := by
    intro label labelMem
    have labelInAll :
        Sum.inr label ∈ allLabels := by
      exact Finset.mem_union_right _ <|
        Finset.mem_image.mpr
          ⟨label, labelMem, rfl⟩
    exact noBad (Sum.inr label) labelInAll
  have labelImagesDisjoint :
      Disjoint
        (coordinateLabels.image
          (Sum.inl : data.FourDegreeLabel →
            data.FourDegreeLabel ⊕ TreeLabel))
        (treeLabels.image
          (Sum.inr : TreeLabel →
            data.FourDegreeLabel ⊕ TreeLabel)) := by
    rw [Finset.disjoint_left]
    intro label labelCoordinate labelTree
    rcases Finset.mem_image.mp labelCoordinate with
      ⟨coordinate, coordinateMem, rfl⟩
    rcases Finset.mem_image.mp labelTree with
      ⟨tree, treeMem, impossible⟩
    cases impossible
  have chargeSum :
      (∑ label ∈ allLabels, charge label) =
        data.fourDegreeCapacity
            parentThreshold fineCellThreshold
            parentCoarseThreshold coarseCellThreshold initialEdges +
          ∑ label ∈ treeLabels, treeCharge label := by
    rw [show allLabels =
        coordinateLabels.image Sum.inl ∪
          treeLabels.image Sum.inr by rfl]
    rw [Finset.sum_union labelImagesDisjoint]
    rw [
      Finset.sum_image
        (fun _ _ _ _ equality =>
          Sum.inl.inj equality),
      Finset.sum_image
        (fun _ _ _ _ equality =>
          Sum.inr.inj equality)
    ]
    simp only [charge]
    simpa [coordinateLabels, fourDegreeCapacity]
  exact
    ⟨{
      core := core
      core_subset := coreSubset
      four_degree_core := by
        simpa [coordinateLabels] using coordinateStable
      tree_stable := treeStable
      removed_le := by
        rw [← chargeSum]
        exact removedBound
    }⟩

namespace SimultaneousPeelingCoreData

variable
    {TreeLabel : Type*} [DecidableEq TreeLabel]
    {initialEdges : Finset data.Edge}
    {parentThreshold fineCellThreshold
      parentCoarseThreshold coarseCellThreshold : ℕ}
    {treeLabels : Finset TreeLabel}
    {treeBad : Finset data.Edge → TreeLabel → Prop}
    {treeCharge : TreeLabel → ℕ}
    (core :
      data.SimultaneousPeelingCoreData
        initialEdges
        parentThreshold fineCellThreshold
        parentCoarseThreshold coarseCellThreshold
        treeLabels treeBad treeCharge)

theorem initial_card_eq_core_add_removed :
    initialEdges.card =
      core.core.card +
        (initialEdges \ core.core).card := by
  have coreCardLe :
      core.core.card ≤ initialEdges.card :=
    Finset.card_le_card core.core_subset
  have differenceCard :
      (initialEdges \ core.core).card =
        initialEdges.card - core.core.card :=
    Finset.card_sdiff_of_subset core.core_subset
  omega

theorem half_retention
    (half_charge :
      2 *
          (data.fourDegreeCapacity
              parentThreshold fineCellThreshold
              parentCoarseThreshold coarseCellThreshold initialEdges +
            ∑ label ∈ treeLabels, treeCharge label) ≤
        initialEdges.card) :
    initialEdges.card ≤ 2 * core.core.card := by
  have removedTwice :
      2 * (initialEdges \ core.core).card ≤
        initialEdges.card := by
    calc
      2 * (initialEdges \ core.core).card ≤
          2 *
            (data.fourDegreeCapacity
                parentThreshold fineCellThreshold
                parentCoarseThreshold coarseCellThreshold initialEdges +
              ∑ label ∈ treeLabels, treeCharge label) := by
        exact Nat.mul_le_mul_left 2 core.removed_le
      _ ≤ initialEdges.card := half_charge
  rw [core.initial_card_eq_core_add_removed] at removedTwice ⊢
  omega

theorem core_nonempty
    (initial_nonempty : initialEdges.Nonempty)
    (half_charge :
      2 *
          (data.fourDegreeCapacity
              parentThreshold fineCellThreshold
              parentCoarseThreshold coarseCellThreshold initialEdges +
            ∑ label ∈ treeLabels, treeCharge label) ≤
        initialEdges.card) :
    core.core.Nonempty := by
  apply Finset.card_pos.mp
  have initialPos := initial_nonempty.card_pos
  have retention :=
    SimultaneousPeelingCoreData.half_retention
      data core half_charge
  omega

theorem parent_degree_lower
    (parent : Parent)
    (degree_pos :
      0 < data.parentDegree core.core parent) :
    parentThreshold ≤
      data.parentDegree core.core parent := by
  have labelMem :=
    data.fourDegreeLabel_mem_of_degree_pos
      core.core_subset
      (.parent parent)
      (by simpa using degree_pos)
  simpa [fourDegreeThreshold] using
    core.four_degree_core (.parent parent) labelMem
      (by simpa using degree_pos)

theorem fineCell_degree_lower
    (fineCell : FineCell)
    (degree_pos :
      0 < data.fineCellDegree core.core fineCell) :
    fineCellThreshold ≤
      data.fineCellDegree core.core fineCell := by
  have labelMem :=
    data.fourDegreeLabel_mem_of_degree_pos
      core.core_subset
      (.fineCell fineCell)
      (by simpa using degree_pos)
  simpa [fourDegreeThreshold] using
    core.four_degree_core (.fineCell fineCell) labelMem
      (by simpa using degree_pos)

theorem parentCoarse_degree_lower
    (parent : Parent) (coarseCell : CoarseCell)
    (degree_pos :
      0 <
        data.parentCoarseDegree
          core.core parent coarseCell) :
    parentCoarseThreshold ≤
      data.parentCoarseDegree
        core.core parent coarseCell := by
  have labelMem :=
    data.fourDegreeLabel_mem_of_degree_pos
      core.core_subset
      (.parentCoarse parent coarseCell)
      (by simpa using degree_pos)
  simpa [fourDegreeThreshold] using
    core.four_degree_core
      (.parentCoarse parent coarseCell) labelMem
      (by simpa using degree_pos)

theorem coarseCell_degree_lower
    (coarseCell : CoarseCell)
    (degree_pos :
      0 < data.coarseDegree core.core coarseCell) :
    coarseCellThreshold ≤
      data.coarseDegree core.core coarseCell := by
  have labelMem :=
    data.fourDegreeLabel_mem_of_degree_pos
      core.core_subset
      (.coarseCell coarseCell)
      (by simpa using degree_pos)
  simpa [fourDegreeThreshold] using
    core.four_degree_core (.coarseCell coarseCell) labelMem
      (by simpa using degree_pos)

end SimultaneousPeelingCoreData

end PureWZ2Prop62FourDegreeIncidenceData

end Kakeya.Assouad

end
