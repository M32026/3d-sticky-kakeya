import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TreeOneLevel

/-!
# Proposition 6.2 one-pass tree cleanup: finite pruning

This implements the deterministic top-down density pruning in
`WZ2_prop62.tex`, Lemma `prop62-tree-cleanup`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62FiniteTree
    (Leaf Node : Type)
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Node] [DecidableEq Node]
    (depth : ℕ) where
  nodeAt : ℕ → Leaf → Node
  root_constant :
    ∀ first second, nodeAt 0 first = nodeAt 0 second
  nested :
    ∀ level, level < depth →
      ∀ first second,
        nodeAt (level + 1) first = nodeAt (level + 1) second →
          nodeAt level first = nodeAt level second

namespace PureWZ2Prop62FiniteTree

variable
    {Leaf Node : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Node] [DecidableEq Node]
    {depth : ℕ}
    (tree : PureWZ2Prop62FiniteTree Leaf Node depth)

def fiber (level : ℕ) (node : Node) : Finset Leaf :=
  Finset.univ.filter fun leaf => tree.nodeAt level leaf = node

theorem fiber_pairwise_disjoint
    (level : ℕ) :
    ∀ first second, first ≠ second →
      Disjoint (tree.fiber level first) (tree.fiber level second) := by
  intro first second hne
  rw [Finset.disjoint_left]
  intro leaf hfirst hsecond
  have hfirstEq := (Finset.mem_filter.mp hfirst).2
  have hsecondEq := (Finset.mem_filter.mp hsecond).2
  exact hne (hfirstEq.symm.trans hsecondEq)

theorem fibers_cover (level : ℕ) :
    (Finset.univ : Finset Leaf) =
      Finset.biUnion Finset.univ (tree.fiber level) := by
  ext leaf
  simp only [Finset.mem_univ, Finset.mem_biUnion, true_iff]
  exact ⟨tree.nodeAt level leaf, by simp [fiber]⟩

theorem sum_fiber_card (level : ℕ) :
    ∑ node : Node, (tree.fiber level node).card =
      Fintype.card Leaf := by
  rw [← Finset.card_biUnion]
  · rw [← tree.fibers_cover level]
    simp
  · intro first hfirst second hsecond hne
    exact tree.fiber_pairwise_disjoint level first second hne

def layer (level : ℕ) (parent : Node) :
    PureWZ2Prop62FinitePartitionLayer Leaf Node where
  parentLeaves := tree.fiber level parent
  childLeaves := fun child =>
    tree.fiber (level + 1) child ∩ tree.fiber level parent
  child_subset := fun child => Finset.inter_subset_right
  children_pairwise_disjoint := by
    intro first second hne
    exact (tree.fiber_pairwise_disjoint (level + 1) first second hne).mono
      Finset.inter_subset_left Finset.inter_subset_left
  children_cover := by
    ext leaf
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_inter, fiber, Finset.mem_filter]
    constructor
    · intro hparent
      exact ⟨tree.nodeAt (level + 1) leaf, rfl, hparent⟩
    · rintro ⟨child, hchild, hparent⟩
      exact hparent

def pruneStep (level : ℕ) (selected : Finset Leaf) : Finset Leaf :=
  (Finset.univ : Finset Node).biUnion fun parent =>
    (tree.layer level parent).retainedLeaves selected

theorem layer_retained_subset_parent
    (level : ℕ) (selected : Finset Leaf) (parent : Node) :
    (tree.layer level parent).retainedLeaves selected ⊆
      tree.fiber level parent := by
  intro leaf hleaf
  have hselectedParent :=
    (tree.layer level parent).retainedLeaves_subset_selectedInParent
      selected hleaf
  exact (Finset.mem_inter.mp hselectedParent).2

theorem layer_retained_pairwise_disjoint
    (level : ℕ) (selected : Finset Leaf) :
    ∀ first ∈ (Finset.univ : Finset Node),
      ∀ second ∈ (Finset.univ : Finset Node),
        first ≠ second →
          Disjoint
            ((tree.layer level first).retainedLeaves selected)
            ((tree.layer level second).retainedLeaves selected) := by
  intro first hfirst second hsecond hne
  exact (tree.fiber_pairwise_disjoint level first second hne).mono
    (tree.layer_retained_subset_parent level selected first)
    (tree.layer_retained_subset_parent level selected second)

theorem pruneStep_subset
    (level : ℕ) (selected : Finset Leaf) :
    tree.pruneStep level selected ⊆ selected := by
  intro leaf hleaf
  rcases Finset.mem_biUnion.mp hleaf with
    ⟨parent, hparent, hleafRetained⟩
  have hselectedParent :=
    (tree.layer level parent).retainedLeaves_subset_selectedInParent
      selected hleafRetained
  exact (Finset.mem_inter.mp hselectedParent).1

theorem pruneStep_inter_fiber
    (level : ℕ) (selected : Finset Leaf) (parent : Node) :
    tree.pruneStep level selected ∩ tree.fiber level parent =
      (tree.layer level parent).retainedLeaves selected := by
  apply Finset.Subset.antisymm
  · intro leaf hleaf
    have hdata := Finset.mem_inter.mp hleaf
    rcases Finset.mem_biUnion.mp hdata.1 with
      ⟨owner, howner, hleafOwner⟩
    have hleafOwnerFiber :=
      tree.layer_retained_subset_parent level selected owner hleafOwner
    have hownerEq :
        tree.nodeAt level leaf = owner :=
      (Finset.mem_filter.mp hleafOwnerFiber).2
    have hparentEq :
        tree.nodeAt level leaf = parent :=
      (Finset.mem_filter.mp hdata.2).2
    have : owner = parent := hownerEq.symm.trans hparentEq
    rwa [← this]
  · intro leaf hleaf
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_biUnion.mpr
          ⟨parent, Finset.mem_univ _, hleaf⟩,
        tree.layer_retained_subset_parent level selected parent hleaf⟩

theorem sum_selected_inter_fiber_card
    (level : ℕ) (selected : Finset Leaf) :
    ∑ parent : Node,
        (selected ∩ tree.fiber level parent).card =
      selected.card := by
  have hpairwise :
      ∀ first ∈ (Finset.univ : Finset Node),
        ∀ second ∈ (Finset.univ : Finset Node),
          first ≠ second →
            Disjoint
              (selected ∩ tree.fiber level first)
              (selected ∩ tree.fiber level second) := by
    intro first hfirst second hsecond hne
    exact (tree.fiber_pairwise_disjoint level first second hne).mono
      Finset.inter_subset_right Finset.inter_subset_right
  rw [← Finset.card_biUnion hpairwise]
  congr 1
  ext leaf
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_inter, fiber, Finset.mem_filter]
  constructor
  · rintro ⟨parent, hselected, hparent⟩
    exact hselected
  · intro hselected
    exact ⟨tree.nodeAt level leaf, hselected, rfl⟩

theorem pruneStep_card_eq_sum
    (level : ℕ) (selected : Finset Leaf) :
    (tree.pruneStep level selected).card =
      ∑ parent : Node,
        ((tree.layer level parent).retainedLeaves selected).card := by
  exact Finset.card_biUnion
    (tree.layer_retained_pairwise_disjoint level selected)

theorem selected_card_le_two_pruneStep
    (level : ℕ) (selected : Finset Leaf) :
    selected.card ≤ 2 * (tree.pruneStep level selected).card := by
  calc
    selected.card =
        ∑ parent : Node,
          (selected ∩ tree.fiber level parent).card := by
      rw [tree.sum_selected_inter_fiber_card]
    _ ≤
        ∑ parent : Node,
          2 *
            ((tree.layer level parent).retainedLeaves selected).card := by
      exact Finset.sum_le_sum fun parent _ => by
        by_cases hnonempty :
            (selected ∩ tree.fiber level parent).Nonempty
        · exact
            (tree.layer level parent).selected_card_le_two_retained
              selected hnonempty
        · have hempty :
              selected ∩ tree.fiber level parent = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hnonempty
          rw [hempty]
          simp
    _ =
        2 *
          ∑ parent : Node,
            ((tree.layer level parent).retainedLeaves selected).card := by
      rw [Finset.mul_sum]
    _ = 2 * (tree.pruneStep level selected).card := by
      rw [tree.pruneStep_card_eq_sum]

theorem pruneStep_parent_density
    (level : ℕ) (selected : Finset Leaf) (parent : Node)
    (hlevel : level < depth)
    (hnonempty :
      (tree.pruneStep level selected ∩
        tree.fiber level parent).Nonempty) :
    (selected ∩ tree.fiber level parent).card *
        (tree.fiber (level + 1)
          (tree.nodeAt (level + 1)
            (Classical.choose hnonempty))).card ≤
      2 *
        (tree.pruneStep level selected ∩
          tree.fiber (level + 1)
            (tree.nodeAt (level + 1)
              (Classical.choose hnonempty))).card *
        (tree.fiber level parent).card := by
  let leaf := Classical.choose hnonempty
  let child := tree.nodeAt (level + 1) leaf
  have hleaf := Classical.choose_spec hnonempty
  have hleafParent := (Finset.mem_inter.mp hleaf).2
  have hparentEq :
      tree.nodeAt level leaf = parent :=
    (Finset.mem_filter.mp hleafParent).2
  have hchildSubsetParent :
      tree.fiber (level + 1) child ⊆
        tree.fiber level parent := by
    intro source hsource
    have hsourceChild :
        tree.nodeAt (level + 1) source = child :=
      (Finset.mem_filter.mp hsource).2
    have hleafChild :
        tree.nodeAt (level + 1) leaf = child := rfl
    have hsourceParent :
        tree.nodeAt level source = tree.nodeAt level leaf :=
      tree.nested level hlevel source leaf <|
        hsourceChild.trans hleafChild.symm
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hsourceParent.trans hparentEq⟩
  have hinterChild :
      (tree.layer level parent).childLeaves child =
        tree.fiber (level + 1) child := by
    apply Finset.inter_eq_left.mpr
    exact hchildSubsetParent
  have hparentOutput :
      (tree.pruneStep level selected ∩
        tree.fiber level parent) =
      (tree.layer level parent).retainedLeaves selected :=
    tree.pruneStep_inter_fiber level selected parent
  have hleafRetained :
      leaf ∈ (tree.layer level parent).retainedLeaves selected := by
    rw [← hparentOutput]
    exact hleaf
  have hchildGood :
      child ∈ (tree.layer level parent).goodChildren selected := by
    rcases Finset.mem_biUnion.mp hleafRetained with
      ⟨owner, hownerGood, hleafOwner⟩
    have hleafOwnerChild :
        leaf ∈ (tree.layer level parent).childLeaves owner :=
      (Finset.mem_inter.mp hleafOwner).2
    have hownerEq :
        tree.nodeAt (level + 1) leaf = owner :=
      (Finset.mem_filter.mp
        (Finset.mem_inter.mp hleafOwnerChild).1).2
    change tree.nodeAt (level + 1) leaf ∈
      (tree.layer level parent).goodChildren selected
    rwa [hownerEq]
  have hdensity :=
    (tree.layer level parent).good_child_density selected hchildGood
  rw [hinterChild] at hdensity
  have hselectedParent :
      (tree.layer level parent).selectedInParent selected =
        selected ∩ tree.fiber level parent := rfl
  rw [hselectedParent] at hdensity
  have hselectedChild :
      (tree.layer level parent).selectedInChild selected child =
        selected ∩ tree.fiber (level + 1) child := by
    change
      selected ∩
          ((tree.fiber (level + 1) child) ∩
            tree.fiber level parent) =
        selected ∩ tree.fiber (level + 1) child
    rw [Finset.inter_eq_left.mpr hchildSubsetParent]
  rw [hselectedChild] at hdensity
  have hstepChild :
      tree.pruneStep level selected ∩
          tree.fiber (level + 1) child =
        (tree.layer level parent).retainedLeaves selected ∩
          tree.fiber (level + 1) child := by
    apply Finset.Subset.antisymm
    · intro source hsource
      have hsourceData := Finset.mem_inter.mp hsource
      have hsourceParent := hchildSubsetParent hsourceData.2
      exact Finset.mem_inter.mpr
        ⟨by
          rw [← tree.pruneStep_inter_fiber level selected parent]
          exact Finset.mem_inter.mpr
            ⟨hsourceData.1, hsourceParent⟩,
          hsourceData.2⟩
    · intro source hsource
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_biUnion.mpr
            ⟨parent, Finset.mem_univ _,
              (Finset.mem_inter.mp hsource).1⟩,
          (Finset.mem_inter.mp hsource).2⟩
  have hretainedChild :
      (tree.layer level parent).retainedLeaves selected ∩
          tree.fiber (level + 1) child =
        selected ∩ tree.fiber (level + 1) child := by
    apply Finset.Subset.antisymm
    · intro source hsource
      exact Finset.mem_inter.mpr
        ⟨tree.pruneStep_subset level selected <|
            Finset.mem_biUnion.mpr
              ⟨parent, Finset.mem_univ _,
                (Finset.mem_inter.mp hsource).1⟩,
          (Finset.mem_inter.mp hsource).2⟩
    · intro source hsource
      have hsourceChild := (Finset.mem_inter.mp hsource).2
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_biUnion.mpr
            ⟨child, hchildGood, by
              exact Finset.mem_inter.mpr
                ⟨(Finset.mem_inter.mp hsource).1,
                  by
                    rw [hinterChild]
                    exact hsourceChild⟩⟩,
          hsourceChild⟩
  rw [hstepChild, hretainedChild]
  exact hdensity

theorem pruneStep_child_density
    (level : ℕ) (selected : Finset Leaf)
    (parent child : Node)
    (hlevel : level < depth)
    (hchildParent :
      tree.fiber (level + 1) child ⊆
        tree.fiber level parent)
    (hnonempty :
      (tree.pruneStep level selected ∩
        tree.fiber (level + 1) child).Nonempty) :
    (selected ∩ tree.fiber level parent).card *
        (tree.fiber (level + 1) child).card ≤
      2 *
        (tree.pruneStep level selected ∩
          tree.fiber (level + 1) child).card *
        (tree.fiber level parent).card := by
  have hchildGood :
      child ∈ (tree.layer level parent).goodChildren selected := by
    rcases Finset.nonempty_def.mp hnonempty with
      ⟨leaf, hleaf⟩
    have hleafData := Finset.mem_inter.mp hleaf
    have hleafParent : leaf ∈ tree.fiber level parent :=
      hchildParent hleafData.2
    have hleafParentOutput :
        leaf ∈ (tree.layer level parent).retainedLeaves selected := by
      rw [← tree.pruneStep_inter_fiber level selected parent]
      exact Finset.mem_inter.mpr
        ⟨hleafData.1, hleafParent⟩
    rcases Finset.mem_biUnion.mp hleafParentOutput with
      ⟨owner, hownerGood, hleafOwner⟩
    have hleafOwnerChild :
        leaf ∈ tree.fiber (level + 1) owner :=
      (Finset.mem_inter.mp
        (Finset.mem_inter.mp hleafOwner).2).1
    have hownerEq :
        tree.nodeAt (level + 1) leaf = owner :=
      (Finset.mem_filter.mp hleafOwnerChild).2
    have hchildEq :
        tree.nodeAt (level + 1) leaf = child :=
      (Finset.mem_filter.mp hleafData.2).2
    have : owner = child := hownerEq.symm.trans hchildEq
    rwa [← this]
  have hdensity :=
    (tree.layer level parent).good_child_density selected hchildGood
  have hparentSelected :
      (tree.layer level parent).selectedInParent selected =
        selected ∩ tree.fiber level parent := rfl
  rw [hparentSelected] at hdensity
  have hchildLeaves :
      (tree.layer level parent).childLeaves child =
        tree.fiber (level + 1) child := by
    exact Finset.inter_eq_left.mpr hchildParent
  rw [hchildLeaves] at hdensity
  have hselectedChild :
      (tree.layer level parent).selectedInChild selected child =
        selected ∩ tree.fiber (level + 1) child := by
    change
      selected ∩
          ((tree.fiber (level + 1) child) ∩
            tree.fiber level parent) =
        selected ∩ tree.fiber (level + 1) child
    rw [Finset.inter_eq_left.mpr hchildParent]
  rw [hselectedChild] at hdensity
  have hstepChild :
      tree.pruneStep level selected ∩
          tree.fiber (level + 1) child =
        selected ∩ tree.fiber (level + 1) child := by
    apply Finset.Subset.antisymm
    · intro leaf hleaf
      exact Finset.mem_inter.mpr
        ⟨tree.pruneStep_subset level selected
            (Finset.mem_inter.mp hleaf).1,
          (Finset.mem_inter.mp hleaf).2⟩
    · intro leaf hleaf
      have hleafData := Finset.mem_inter.mp hleaf
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_biUnion.mpr
            ⟨parent, Finset.mem_univ _,
              Finset.mem_biUnion.mpr
                ⟨child, hchildGood,
                  Finset.mem_inter.mpr
                    ⟨hleafData.1,
                      Finset.mem_inter.mpr
                        ⟨hleafData.2,
                          hchildParent hleafData.2⟩⟩⟩⟩,
          hleafData.2⟩
  rw [hstepChild]
  exact hdensity

end PureWZ2Prop62FiniteTree

end Kakeya.Assouad

end
