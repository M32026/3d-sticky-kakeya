import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ReferenceParentDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreeCore

/-!
# Proposition 6.2: reference-tree deletion blocks and charges

The terminal peeling process may delete all currently active parent vertices
below one node of the previously cleaned reference tree.  A tree label is
the pair of a level and an actual node value; duplicate representatives of
the same node are removed by the finite image.

For a current edge set, the current parent count is the cardinality of the
parent image of the edges in that node.  If

`A0 * currentCount < referenceCount`,

then the entire current node block is bad.  Since every ambient reference
parent has fewer than `4*K` incident edges, deleting the block costs at most

`4 * K * (referenceCount / A0)`.
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
    {shading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput cover shading)
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

abbrev ReferenceTreeLabel
    (_input : PureWZ2Prop62PacketCellInput cover shading) :=
  ℕ × Finset (Fin coarse.card)

/-- All actual nodes hit by the reference parents at levels `0,...,L`. -/
def referenceTreeLabels : Finset input.ReferenceTreeLabel :=
  (Finset.range (schedule.levelCount + 1)).biUnion fun level =>
    treeCleanup.referenceParents.image fun parent =>
      (level, schedule.nodeAt level parent)

def referenceParentsAt
    (label : input.ReferenceTreeLabel) :
    Finset (Fin coarse.card) :=
  treeCleanup.referenceParents ∩
    schedule.tree.fiber label.1 label.2

def referenceCount
    (label : input.ReferenceTreeLabel) : ℕ :=
  (input.referenceParentsAt
    multiplicity parentClass treeCleanup label).card

/-- The ambient edge block whose parent vertex lies below the labeled node. -/
def referenceTreeBlock
    (label : input.ReferenceTreeLabel) :
    Finset exactification.incidence.Edge :=
  exactification.incidence.allEdges.filter fun edge =>
    exactification.incidence.edgeParent edge ∈
      schedule.tree.fiber label.1 label.2

def currentTreeBlock
    (edges : Finset exactification.incidence.Edge)
    (label : input.ReferenceTreeLabel) :
    Finset exactification.incidence.Edge :=
  edges ∩
    input.referenceTreeBlock
      multiplicity parentClass treeCleanup exactification label

def currentParents
    (edges : Finset exactification.incidence.Edge)
    (label : input.ReferenceTreeLabel) :
    Finset (Fin coarse.card) :=
  (input.currentTreeBlock
    multiplicity parentClass treeCleanup exactification
    edges label).image exactification.incidence.edgeParent

def currentParentCount
    (edges : Finset exactification.incidence.Edge)
    (label : input.ReferenceTreeLabel) : ℕ :=
  (input.currentParents
    multiplicity parentClass treeCleanup exactification
    edges label).card

def referenceTreeBad
    (A0 : ℕ)
    (edges : Finset exactification.incidence.Edge)
    (label : input.ReferenceTreeLabel) : Prop :=
  0 <
      input.currentParentCount
        multiplicity parentClass treeCleanup exactification
        edges label ∧
    A0 *
        input.currentParentCount
          multiplicity parentClass treeCleanup exactification
          edges label <
      input.referenceCount
        multiplicity parentClass treeCleanup label

def referenceTreeCharge
    (A0 : ℕ)
    (label : input.ReferenceTreeLabel) : ℕ :=
  4 * parentDegree.K *
    (input.referenceCount
      multiplicity parentClass treeCleanup label / A0)

theorem mem_referenceTreeLabels
    {label : input.ReferenceTreeLabel}
    (labelMem :
      label ∈
        input.referenceTreeLabels
          multiplicity parentClass treeCleanup) :
    label.1 ≤ schedule.levelCount ∧
      (input.referenceParentsAt
        multiplicity parentClass treeCleanup label).Nonempty := by
  rcases Finset.mem_biUnion.mp labelMem with
    ⟨level, levelMem, labelImage⟩
  have levelLt :
      level < schedule.levelCount + 1 :=
    Finset.mem_range.mp levelMem
  rcases Finset.mem_image.mp labelImage with
    ⟨parent, parentMem, labelEq⟩
  have levelEq : label.1 = level :=
    congrArg Prod.fst labelEq.symm
  have nodeEq :
      label.2 = schedule.nodeAt level parent :=
    congrArg Prod.snd labelEq.symm
  constructor
  · omega
  · refine
      ⟨parent, Finset.mem_inter.mpr
        ⟨parentMem, ?_⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ parent, ?_⟩
    rw [levelEq, nodeEq]
    rfl

theorem referenceCount_pos
    {label : input.ReferenceTreeLabel}
    (labelMem :
      label ∈
        input.referenceTreeLabels
          multiplicity parentClass treeCleanup) :
    0 <
      input.referenceCount
        multiplicity parentClass treeCleanup label := by
  exact Finset.card_pos.mpr
    (input.mem_referenceTreeLabels
      multiplicity parentClass treeCleanup labelMem).2

theorem currentTreeBlock_eq_inter :
    ∀ edges label,
      edges ∩
          input.referenceTreeBlock
            multiplicity parentClass treeCleanup exactification label =
        input.currentTreeBlock
          multiplicity parentClass treeCleanup exactification
          edges label := by
  intro edges label
  rfl

theorem referenceTreeBad_nonempty
    (A0 : ℕ)
    (edges : Finset exactification.incidence.Edge)
    (label : input.ReferenceTreeLabel)
    (bad :
      input.referenceTreeBad
        multiplicity parentClass treeCleanup exactification
        A0 edges label) :
    (edges ∩
      input.referenceTreeBlock
        multiplicity parentClass treeCleanup exactification
        label).Nonempty := by
  have currentParentsNonempty :
      (input.currentParents
        multiplicity parentClass treeCleanup exactification
        edges label).Nonempty := by
    exact Finset.card_pos.mp bad.1
  rcases currentParentsNonempty with
    ⟨parent, parentMem⟩
  rcases Finset.mem_image.mp parentMem with
    ⟨edge, edgeMem, _edgeParent⟩
  exact
    ⟨edge, by
      simpa [currentTreeBlock] using edgeMem⟩

theorem currentParent_ambient_degree_upper
    (edges : Finset exactification.incidence.Edge)
    (label : input.ReferenceTreeLabel)
    {parent : Fin coarse.card}
    (parentMem :
      parent ∈
        input.currentParents
          multiplicity parentClass treeCleanup exactification
          edges label) :
    exactification.incidence.parentDegree
        exactification.incidence.allEdges parent <
      4 * parentDegree.K := by
  rcases Finset.mem_image.mp parentMem with
    ⟨edge, edgeMem, edgeParent⟩
  have edgeCurrent :
      edge ∈
        input.currentTreeBlock
          multiplicity parentClass treeCleanup exactification
          edges label :=
    edgeMem
  have edgeAll :
      edge ∈ exactification.incidence.allEdges := by
    exact Finset.mem_univ edge
  have parentActive :
      parent ∈
        exactification.incidence.activeParents
          exactification.incidence.allEdges := by
    rw [exactification.incidence.mem_activeParents_iff]
    apply Finset.card_pos.mpr
    exact
      ⟨edge, Finset.mem_filter.mpr
        ⟨edgeAll, edgeParent⟩⟩
  exact
    (parentDegree.incidence_degree_band parent parentActive).2

theorem currentTreeBlock_card_le_fourK_mul_currentParentCount
    (edges : Finset exactification.incidence.Edge)
    (label : input.ReferenceTreeLabel) :
    (input.currentTreeBlock
        multiplicity parentClass treeCleanup exactification
        edges label).card ≤
      4 * parentDegree.K *
        input.currentParentCount
          multiplicity parentClass treeCleanup exactification
          edges label := by
  let block :=
    input.currentTreeBlock
      multiplicity parentClass treeCleanup exactification
      edges label
  let parents :=
    input.currentParents
      multiplicity parentClass treeCleanup exactification
      edges label
  have fiberwise :=
    Finset.sum_card_fiberwise_eq_card_filter
      block parents exactification.incidence.edgeParent
  have allParents :
      (block.filter fun edge =>
          exactification.incidence.edgeParent edge ∈ parents) =
        block := by
    apply Finset.filter_true_of_mem
    intro edge edgeMem
    exact
      Finset.mem_image.mpr
        ⟨edge, edgeMem, rfl⟩
  have blockCard :
      block.card =
        ∑ parent ∈ parents,
          (block.filter fun edge =>
            exactification.incidence.edgeParent edge = parent).card := by
    rw [allParents] at fiberwise
    exact fiberwise.symm
  rw [blockCard]
  calc
    (∑ parent ∈ parents,
        (block.filter fun edge =>
          exactification.incidence.edgeParent edge = parent).card) ≤
        ∑ _parent ∈ parents, 4 * parentDegree.K := by
      apply Finset.sum_le_sum
      intro parent parentMem
      have fiberSubset :
          block.filter (fun edge =>
              exactification.incidence.edgeParent edge = parent) ⊆
            exactification.incidence.allEdges.filter
              (fun edge =>
                exactification.incidence.edgeParent edge = parent) := by
        intro edge edgeMem
        have edgeData := Finset.mem_filter.mp edgeMem
        exact
          Finset.mem_filter.mpr
            ⟨Finset.mem_univ edge, edgeData.2⟩
      have ambientUpper :=
        input.currentParent_ambient_degree_upper
          multiplicity parentClass treeCleanup exactification
          parentDegree edges label parentMem
      exact
        (Finset.card_le_card fiberSubset).trans
          ambientUpper.le
    _ =
        4 * parentDegree.K * parents.card := by
      simp
      ring
    _ =
        4 * parentDegree.K *
          input.currentParentCount
            multiplicity parentClass treeCleanup exactification
            edges label := by
      rfl

theorem referenceTreeBad_card_le_charge
    (A0 : ℕ)
    (A0_pos : 0 < A0)
    (edges : Finset exactification.incidence.Edge)
    (label : input.ReferenceTreeLabel)
    (bad :
      input.referenceTreeBad
        multiplicity parentClass treeCleanup exactification
        A0 edges label) :
    (edges ∩
      input.referenceTreeBlock
        multiplicity parentClass treeCleanup exactification
        label).card ≤
      input.referenceTreeCharge
        multiplicity parentClass treeCleanup exactification parentDegree
        A0 label := by
  have currentCountLe :
      input.currentParentCount
          multiplicity parentClass treeCleanup exactification
          edges label ≤
        input.referenceCount
            multiplicity parentClass treeCleanup label / A0 := by
    apply
      (Nat.le_div_iff_mul_le A0_pos).mpr
    rw [Nat.mul_comm]
    exact bad.2.le
  calc
    (edges ∩
        input.referenceTreeBlock
          multiplicity parentClass treeCleanup exactification
          label).card =
        (input.currentTreeBlock
          multiplicity parentClass treeCleanup exactification
          edges label).card := rfl
    _ ≤
        4 * parentDegree.K *
          input.currentParentCount
            multiplicity parentClass treeCleanup exactification
            edges label :=
      input.currentTreeBlock_card_le_fourK_mul_currentParentCount
        multiplicity parentClass treeCleanup exactification
        parentDegree edges label
    _ ≤
        4 * parentDegree.K *
          (input.referenceCount
            multiplicity parentClass treeCleanup label / A0) := by
      exact Nat.mul_le_mul_left _ currentCountLe
    _ =
        input.referenceTreeCharge
          multiplicity parentClass treeCleanup exactification parentDegree
          A0 label := rfl

theorem referenceParents_eq_activeParents :
    treeCleanup.referenceParents =
      exactification.incidence.activeParents
        exactification.incidence.allEdges := by
  ext parent
  exact (exactification.active_parent_iff parent).symm

theorem referenceParents_card_mul_K_le_allEdges_card :
    treeCleanup.referenceParents.card * parentDegree.K ≤
      exactification.incidence.allEdges.card := by
  rw [input.referenceParents_eq_activeParents
    multiplicity parentClass treeCleanup exactification]
  calc
    (exactification.incidence.activeParents
          exactification.incidence.allEdges).card *
        parentDegree.K =
        ∑ parent ∈
            exactification.incidence.activeParents
              exactification.incidence.allEdges,
          parentDegree.K := by
      simp
    _ ≤
        ∑ parent ∈
            exactification.incidence.activeParents
              exactification.incidence.allEdges,
          exactification.incidence.parentDegree
            exactification.incidence.allEdges parent := by
      apply Finset.sum_le_sum
      intro parent parentMem
      exact (parentDegree.incidence_degree_band parent parentMem).1
    _ = exactification.incidence.allEdges.card := by
      exact
        (exactification.incidence.card_eq_sum_parentDegree
          exactification.incidence.allEdges).symm

theorem referenceTreeLabels_subset_full :
    input.referenceTreeLabels
        multiplicity parentClass treeCleanup ⊆
      (Finset.range (schedule.levelCount + 1)).product
        (Finset.univ : Finset (Finset (Fin coarse.card))) := by
  intro label labelMem
  rcases Finset.mem_biUnion.mp labelMem with
    ⟨level, levelMem, labelImage⟩
  rcases Finset.mem_image.mp labelImage with
    ⟨parent, parentMem, labelEq⟩
  subst label
  exact Finset.mem_product.mpr
    ⟨levelMem, Finset.mem_univ _⟩

theorem referenceTreeCharge_sum_scaled_le
    (A0 : ℕ) :
    A0 *
        ∑ label ∈
            input.referenceTreeLabels
              multiplicity parentClass treeCleanup,
          input.referenceTreeCharge
            multiplicity parentClass treeCleanup exactification
              parentDegree A0 label ≤
      4 * (schedule.levelCount + 1) *
        exactification.incidence.allEdges.card := by
  let fullLabels :=
    (Finset.range (schedule.levelCount + 1)).product
      (Finset.univ : Finset (Finset (Fin coarse.card)))
  have pointwise :
      ∀ label ∈
          input.referenceTreeLabels
            multiplicity parentClass treeCleanup,
        A0 *
            input.referenceTreeCharge
              multiplicity parentClass treeCleanup exactification
                parentDegree A0 label ≤
          4 * parentDegree.K *
            input.referenceCount
              multiplicity parentClass treeCleanup label := by
    intro label labelMem
    unfold referenceTreeCharge
    calc
      A0 *
          (4 * parentDegree.K *
            (input.referenceCount
              multiplicity parentClass treeCleanup label / A0)) =
          4 * parentDegree.K *
            (A0 *
              (input.referenceCount
                multiplicity parentClass treeCleanup label / A0)) := by
        ring
      _ ≤
          4 * parentDegree.K *
            input.referenceCount
              multiplicity parentClass treeCleanup label := by
        exact Nat.mul_le_mul_left _
          (Nat.mul_div_le
            (input.referenceCount
              multiplicity parentClass treeCleanup label) A0)
  have fullSum :
      (∑ label ∈ fullLabels,
          4 * parentDegree.K *
            input.referenceCount
              multiplicity parentClass treeCleanup label) =
        (schedule.levelCount + 1) *
          (4 * parentDegree.K *
            treeCleanup.referenceParents.card) := by
    calc
      (∑ label ∈ fullLabels,
          4 * parentDegree.K *
            input.referenceCount
              multiplicity parentClass treeCleanup label) =
          ∑ level ∈ Finset.range (schedule.levelCount + 1),
            ∑ node : Finset (Fin coarse.card),
              4 * parentDegree.K *
                (treeCleanup.referenceParents ∩
                  schedule.tree.fiber level node).card := by
        exact Finset.sum_product _ _ _
      _ =
          ∑ _level ∈ Finset.range (schedule.levelCount + 1),
            4 * parentDegree.K *
              treeCleanup.referenceParents.card := by
        apply Finset.sum_congr rfl
        intro level levelMem
        rw [← Finset.mul_sum]
        rw [schedule.tree.sum_selected_inter_fiber_card]
      _ =
          (schedule.levelCount + 1) *
            (4 * parentDegree.K *
              treeCleanup.referenceParents.card) := by
        simp
  calc
    A0 *
        ∑ label ∈
            input.referenceTreeLabels
              multiplicity parentClass treeCleanup,
          input.referenceTreeCharge
            multiplicity parentClass treeCleanup exactification
              parentDegree A0 label =
        ∑ label ∈
            input.referenceTreeLabels
              multiplicity parentClass treeCleanup,
          A0 *
            input.referenceTreeCharge
              multiplicity parentClass treeCleanup exactification
                parentDegree A0 label := by
      rw [Finset.mul_sum]
    _ ≤
        ∑ label ∈
            input.referenceTreeLabels
              multiplicity parentClass treeCleanup,
          4 * parentDegree.K *
            input.referenceCount
              multiplicity parentClass treeCleanup label := by
      exact Finset.sum_le_sum pointwise
    _ ≤
        ∑ label ∈ fullLabels,
          4 * parentDegree.K *
            input.referenceCount
              multiplicity parentClass treeCleanup label := by
      exact Finset.sum_le_sum_of_subset
        (input.referenceTreeLabels_subset_full
          multiplicity parentClass treeCleanup)
    _ =
        (schedule.levelCount + 1) *
          (4 * parentDegree.K *
            treeCleanup.referenceParents.card) :=
      fullSum
    _ ≤
        4 * (schedule.levelCount + 1) *
          exactification.incidence.allEdges.card := by
      have base :=
        input.referenceParents_card_mul_K_le_allEdges_card
          multiplicity parentClass treeCleanup exactification
            parentDegree
      calc
        (schedule.levelCount + 1) *
            (4 * parentDegree.K *
              treeCleanup.referenceParents.card) =
            4 * (schedule.levelCount + 1) *
              (treeCleanup.referenceParents.card * parentDegree.K) := by
          ring
        _ ≤
            4 * (schedule.levelCount + 1) *
              exactification.incidence.allEdges.card := by
          exact Nat.mul_le_mul_left _ base

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
