import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FixedGridCleanup

/-!
# Proposition 6.2 one-pass tree cleanup: one level

This is the one-parent, one-level counting step in
`WZ2_prop62.tex`, Lemma `prop62-tree-cleanup`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62FinitePartitionLayer
    (Leaf Node : Type)
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Node] [DecidableEq Node] where
  parentLeaves : Finset Leaf
  childLeaves : Node → Finset Leaf
  child_subset :
    ∀ node, childLeaves node ⊆ parentLeaves
  children_pairwise_disjoint :
    ∀ first second, first ≠ second →
      Disjoint (childLeaves first) (childLeaves second)
  children_cover :
    parentLeaves = Finset.biUnion Finset.univ childLeaves

namespace PureWZ2Prop62FinitePartitionLayer

variable
    {Leaf Node : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Node] [DecidableEq Node]
    (layer : PureWZ2Prop62FinitePartitionLayer Leaf Node)

def selectedInParent (selected : Finset Leaf) : Finset Leaf :=
  selected ∩ layer.parentLeaves

def selectedInChild
    (selected : Finset Leaf) (node : Node) : Finset Leaf :=
  selected ∩ layer.childLeaves node

def goodChildren (selected : Finset Leaf) : Finset Node :=
  Finset.univ.filter fun node =>
    2 * (layer.selectedInChild selected node).card *
        layer.parentLeaves.card ≥
      (layer.selectedInParent selected).card *
        (layer.childLeaves node).card

def retainedLeaves (selected : Finset Leaf) : Finset Leaf :=
  (layer.goodChildren selected).biUnion fun node =>
    layer.selectedInChild selected node

theorem selectedInChild_pairwise_disjoint
    (selected : Finset Leaf) :
    ∀ first ∈ (Finset.univ : Finset Node),
      ∀ second ∈ (Finset.univ : Finset Node),
        first ≠ second →
          Disjoint
            (layer.selectedInChild selected first)
            (layer.selectedInChild selected second) := by
  intro first hfirst second hsecond hne
  exact (layer.children_pairwise_disjoint first second hne).mono
    (Finset.inter_subset_right)
    (Finset.inter_subset_right)

theorem sum_selectedInChild_card
    (selected : Finset Leaf) :
    ∑ node : Node, (layer.selectedInChild selected node).card =
      (layer.selectedInParent selected).card := by
  rw [← Finset.card_biUnion
    (layer.selectedInChild_pairwise_disjoint selected)]
  congr 1
  ext leaf
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    selectedInChild, selectedInParent, Finset.mem_inter]
  constructor
  · rintro ⟨node, hselected, hchild⟩
    exact
      ⟨hselected,
        layer.child_subset node hchild⟩
  · rintro ⟨hselected, hparent⟩
    rw [layer.children_cover] at hparent
    rcases Finset.mem_biUnion.mp hparent with
      ⟨node, hnode, hchild⟩
    exact ⟨node, hselected, hchild⟩

theorem sum_child_card :
    ∑ node : Node, (layer.childLeaves node).card =
      layer.parentLeaves.card := by
  rw [← Finset.card_biUnion]
  · exact congrArg Finset.card layer.children_cover.symm
  · intro first hfirst second hsecond hne
    exact layer.children_pairwise_disjoint first second hne

theorem bad_children_selected_card_lt_half
    (selected : Finset Leaf)
    (hselectedNonempty :
      (layer.selectedInParent selected).Nonempty) :
    2 *
        ∑ node ∈
          (Finset.univ : Finset Node) \
            layer.goodChildren selected,
          (layer.selectedInChild selected node).card <
      (layer.selectedInParent selected).card := by
  let bad :=
    (Finset.univ : Finset Node) \
      layer.goodChildren selected
  by_cases hbadEmpty : bad = ∅
  · change
      2 *
          ∑ node ∈ bad,
            (layer.selectedInChild selected node).card <
        (layer.selectedInParent selected).card
    rw [hbadEmpty]
    simp
    exact hselectedNonempty
  · have hparentPos : 0 < layer.parentLeaves.card :=
      Finset.card_pos.mpr <| by
        rcases hselectedNonempty with ⟨leaf, hleaf⟩
        exact ⟨leaf, (Finset.mem_inter.mp hleaf).2⟩
    have hbadEach :
        ∀ node ∈ bad,
          2 * (layer.selectedInChild selected node).card *
              layer.parentLeaves.card <
            (layer.selectedInParent selected).card *
              (layer.childLeaves node).card := by
      intro node hnode
      have hnotGood :=
        (Finset.mem_sdiff.mp hnode).2
      simp only [goodChildren, Finset.mem_filter,
        Finset.mem_univ, true_and] at hnotGood
      exact Nat.lt_of_not_ge hnotGood
    have hsumStrict :
        (∑ node ∈ bad,
            2 * (layer.selectedInChild selected node).card) *
              layer.parentLeaves.card <
          (layer.selectedInParent selected).card *
            ∑ node ∈ bad, (layer.childLeaves node).card := by
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_lt_sum_of_nonempty
        (Finset.nonempty_iff_ne_empty.mpr hbadEmpty)
        hbadEach
    have hchildrenBad :
        ∑ node ∈ bad, (layer.childLeaves node).card ≤
          layer.parentLeaves.card := by
      calc
        ∑ node ∈ bad, (layer.childLeaves node).card ≤
            ∑ node : Node, (layer.childLeaves node).card := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.sdiff_subset)
            (fun _ _ _ => Nat.zero_le _)
        _ = layer.parentLeaves.card := by
          rw [layer.sum_child_card]
    have hcross :
        (∑ node ∈ bad,
            2 * (layer.selectedInChild selected node).card) *
              layer.parentLeaves.card <
          (layer.selectedInParent selected).card *
              layer.parentLeaves.card := by
      calc
        (∑ node ∈ bad,
            2 * (layer.selectedInChild selected node).card) *
              layer.parentLeaves.card <
            (layer.selectedInParent selected).card *
              ∑ node ∈ bad, (layer.childLeaves node).card :=
          hsumStrict
        _ ≤
            (layer.selectedInParent selected).card *
              layer.parentLeaves.card := by
          gcongr
    have hcancel :=
      Nat.lt_of_mul_lt_mul_right hcross
    simpa [Finset.mul_sum] using hcancel

theorem retainedLeaves_subset_selectedInParent
    (selected : Finset Leaf) :
    layer.retainedLeaves selected ⊆
      layer.selectedInParent selected := by
  intro leaf hleaf
  rcases Finset.mem_biUnion.mp hleaf with
    ⟨node, hnode, hleafChild⟩
  exact Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hleafChild).1,
      layer.child_subset node
        (Finset.mem_inter.mp hleafChild).2⟩

theorem retainedLeaves_card_eq_good_sum
    (selected : Finset Leaf) :
    (layer.retainedLeaves selected).card =
      ∑ node ∈ layer.goodChildren selected,
        (layer.selectedInChild selected node).card := by
  exact Finset.card_biUnion <| by
    intro first hfirst second hsecond hne
    exact
      (layer.children_pairwise_disjoint first second hne).mono
        Finset.inter_subset_right Finset.inter_subset_right

theorem selected_card_eq_good_add_bad
    (selected : Finset Leaf) :
    (layer.selectedInParent selected).card =
      (∑ node ∈ layer.goodChildren selected,
          (layer.selectedInChild selected node).card) +
        ∑ node ∈
          (Finset.univ : Finset Node) \
            layer.goodChildren selected,
          (layer.selectedInChild selected node).card := by
  have hpartition :
      (Finset.univ : Finset Node) =
        layer.goodChildren selected ∪
          ((Finset.univ : Finset Node) \
            layer.goodChildren selected) := by
    rw [Finset.union_sdiff_of_subset]
    exact Finset.filter_subset _ _
  rw [← layer.sum_selectedInChild_card selected]
  conv_lhs =>
    rw [hpartition]
  rw [Finset.sum_union]
  exact Finset.disjoint_sdiff

theorem selected_card_le_two_retained
    (selected : Finset Leaf)
    (hselectedNonempty :
      (layer.selectedInParent selected).Nonempty) :
    (layer.selectedInParent selected).card ≤
      2 * (layer.retainedLeaves selected).card := by
  let goodMass :=
    ∑ node ∈ layer.goodChildren selected,
      (layer.selectedInChild selected node).card
  let badMass :=
    ∑ node ∈
      (Finset.univ : Finset Node) \
        layer.goodChildren selected,
      (layer.selectedInChild selected node).card
  have hsplit :
      (layer.selectedInParent selected).card =
        goodMass + badMass := by
    simpa only [goodMass, badMass] using
      layer.selected_card_eq_good_add_bad selected
  have hbad :
      2 * badMass <
        (layer.selectedInParent selected).card := by
    simpa only [badMass] using
      layer.bad_children_selected_card_lt_half
        selected hselectedNonempty
  have hbadLe : badMass ≤ goodMass := by
    rw [hsplit] at hbad
    omega
  have hretained :
      (layer.retainedLeaves selected).card = goodMass := by
    simpa only [goodMass] using
      layer.retainedLeaves_card_eq_good_sum selected
  rw [hsplit, hretained]
  omega

theorem good_child_density
    (selected : Finset Leaf)
    {node : Node}
    (hnode : node ∈ layer.goodChildren selected) :
    (layer.selectedInParent selected).card *
        (layer.childLeaves node).card ≤
      2 * (layer.selectedInChild selected node).card *
        layer.parentLeaves.card := by
  exact (Finset.mem_filter.mp hnode).2

structure OneLevelOutput (selected : Finset Leaf) where
  retained : Finset Leaf
  retained_eq :
    retained = layer.retainedLeaves selected
  retained_subset :
    retained ⊆ layer.selectedInParent selected
  cardinality_retention :
    (layer.selectedInParent selected).card ≤
      2 * retained.card
  child_density :
    ∀ node,
      (retained ∩ layer.childLeaves node).Nonempty →
        (layer.selectedInParent selected).card *
            (layer.childLeaves node).card ≤
          2 * (retained ∩ layer.childLeaves node).card *
            layer.parentLeaves.card

noncomputable def oneLevelOutput
    (selected : Finset Leaf)
    (hselectedNonempty :
      (layer.selectedInParent selected).Nonempty) :
    layer.OneLevelOutput selected := by
  let retained := layer.retainedLeaves selected
  have hsubset :=
    layer.retainedLeaves_subset_selectedInParent selected
  have hcard :=
    layer.selected_card_le_two_retained
      selected hselectedNonempty
  refine
    {
      retained := retained
      retained_eq := rfl
      retained_subset := hsubset
      cardinality_retention := hcard
      child_density := ?_
    }
  intro node hnodeRetained
  have hnodeGood :
      node ∈ layer.goodChildren selected := by
    rcases Finset.nonempty_def.mp hnodeRetained with
      ⟨leaf, hleafRetained⟩
    have hleafData := Finset.mem_inter.mp hleafRetained
    rcases Finset.mem_biUnion.mp hleafData.1 with
      ⟨owner, hownerGood, hleafOwner⟩
    by_cases hEq : owner = node
    · rwa [← hEq]
    · have hdisjoint :=
        layer.children_pairwise_disjoint owner node hEq
      exact False.elim <|
        Finset.disjoint_left.mp hdisjoint
          (Finset.mem_inter.mp hleafOwner).2 hleafData.2
  have hinter :
      retained ∩ layer.childLeaves node =
        layer.selectedInChild selected node := by
    apply Finset.Subset.antisymm
    · intro leaf hleaf
      have hleafData := Finset.mem_inter.mp hleaf
      have hselectedParent :=
        layer.retainedLeaves_subset_selectedInParent
          selected hleafData.1
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hselectedParent).1,
          hleafData.2⟩
    · intro leaf hleaf
      refine Finset.mem_inter.mpr ⟨?_, (Finset.mem_inter.mp hleaf).2⟩
      exact Finset.mem_biUnion.mpr
        ⟨node, hnodeGood, hleaf⟩
  rw [hinter]
  exact layer.good_child_density selected hnodeGood

end PureWZ2Prop62FinitePartitionLayer

end Kakeya.Assouad

end
