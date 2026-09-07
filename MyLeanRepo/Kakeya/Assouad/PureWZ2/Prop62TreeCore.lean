import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TreeIteration

/-!
# Proposition 6.2 one-pass tree cleanup: final core

This proves the cardinality and node-density conclusions in
`WZ2_prop62.tex`, Lemma `prop62-tree-cleanup`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62FiniteTree

variable
    {Leaf Node : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Node] [DecidableEq Node]
    {depth : ℕ}
    (tree : PureWZ2Prop62FiniteTree Leaf Node depth)

theorem root_fiber_eq_univ
    {root : Node}
    (hroot : (tree.fiber 0 root).Nonempty) :
    tree.fiber 0 root = Finset.univ := by
  rcases Finset.nonempty_def.mp hroot with ⟨leaf, hleaf⟩
  have hleafRoot :
      tree.nodeAt 0 leaf = root :=
    (Finset.mem_filter.mp hleaf).2
  apply Finset.eq_univ_of_forall
  intro source
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,
      (tree.root_constant source leaf).trans hleafRoot⟩

theorem pruneIter_branch_density
    (selected : Finset Leaf)
    {level : ℕ}
    (hlevel : level ≤ depth)
    (node : Node)
    (hnonempty :
      (tree.pruneIter selected level ∩
        tree.fiber level node).Nonempty) :
    selected.card * (tree.fiber level node).card ≤
      2 ^ level *
        (tree.pruneIter selected level ∩
          tree.fiber level node).card *
        Fintype.card Leaf := by
  induction level generalizing node with
  | zero =>
      have hroot : (tree.fiber 0 node).Nonempty := by
        rcases Finset.nonempty_def.mp hnonempty with
          ⟨leaf, hleaf⟩
        exact Finset.nonempty_def.mpr
          ⟨leaf, (Finset.mem_inter.mp hleaf).2⟩
      have hfiber := tree.root_fiber_eq_univ hroot
      simp [hfiber]
  | succ level ih =>
      have hlevelLt : level < depth := by omega
      rcases Finset.nonempty_def.mp hnonempty with
        ⟨leaf, hleaf⟩
      have hleafData := Finset.mem_inter.mp hleaf
      let parent := tree.nodeAt level leaf
      have hchildEq :
          tree.nodeAt (level + 1) leaf = node :=
        (Finset.mem_filter.mp hleafData.2).2
      have hparentMem :
          leaf ∈ tree.fiber level parent :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
      have hparentNonempty :
          (tree.pruneIter selected level ∩
            tree.fiber level parent).Nonempty := by
        have hleafPrevious :
            leaf ∈ tree.pruneIter selected level :=
          tree.pruneIter_succ_subset selected level hleafData.1
        exact Finset.nonempty_def.mpr
          ⟨leaf, Finset.mem_inter.mpr
            ⟨hleafPrevious, hparentMem⟩⟩
      have hchildSubsetParent :
          tree.fiber (level + 1) node ⊆
            tree.fiber level parent := by
        intro source hsource
        have hsourceChild :
            tree.nodeAt (level + 1) source = node :=
          (Finset.mem_filter.mp hsource).2
        have hsourceParent :
            tree.nodeAt level source =
              tree.nodeAt level leaf :=
          tree.nested level hlevelLt source leaf <|
            hsourceChild.trans hchildEq.symm
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hsourceParent⟩
      have hlocal :=
        tree.pruneStep_child_density
          level (tree.pruneIter selected level)
          parent node hlevelLt hchildSubsetParent <| by
            simpa only [pruneIter_succ] using hnonempty
      have hih :=
        ih (by omega) parent hparentNonempty
      let parentCard := (tree.fiber level parent).card
      let childCard := (tree.fiber (level + 1) node).card
      let parentSelected :=
        (tree.pruneIter selected level ∩
          tree.fiber level parent).card
      let childSelected :=
        (tree.pruneIter selected (level + 1) ∩
          tree.fiber (level + 1) node).card
      have hparentCardPos : 0 < parentCard := by
        rcases Finset.nonempty_def.mp hparentNonempty with
          ⟨source, hsource⟩
        exact Finset.card_pos.mpr
          ⟨source, (Finset.mem_inter.mp hsource).2⟩
      have hfirst :
          selected.card * parentCard ≤
            2 ^ level * parentSelected * Fintype.card Leaf := by
        simpa only [parentCard, parentSelected] using hih
      have hsecond :
          parentSelected * childCard ≤
            2 * childSelected * parentCard := by
        simpa only [parentCard, childCard, parentSelected,
          childSelected, pruneIter_succ] using hlocal
      have hwithParent :
          (selected.card * childCard) * parentCard ≤
            (2 ^ (level + 1) * childSelected *
              Fintype.card Leaf) * parentCard := by
        calc
          (selected.card * childCard) * parentCard =
              (selected.card * parentCard) * childCard := by ring
          _ ≤
              (2 ^ level * parentSelected *
                Fintype.card Leaf) * childCard := by
            gcongr
          _ =
              2 ^ level * Fintype.card Leaf *
                (parentSelected * childCard) := by ring
          _ ≤
              2 ^ level * Fintype.card Leaf *
                (2 * childSelected * parentCard) := by
            gcongr
          _ =
              (2 ^ (level + 1) * childSelected *
                Fintype.card Leaf) * parentCard := by
            rw [pow_succ]
            ring
      have hcancel :=
        Nat.le_of_mul_le_mul_right hwithParent hparentCardPos
      simpa only [childCard, childSelected] using hcancel

theorem final_core_node_density
    (selected : Finset Leaf)
    {level : ℕ}
    (hlevel : level ≤ depth)
    (node : Node)
    (hnonempty :
      (tree.pruneIter selected depth ∩
        tree.fiber level node).Nonempty) :
    selected.card * (tree.fiber level node).card ≤
      2 ^ depth *
        (tree.pruneIter selected depth ∩
          tree.fiber level node).card *
        Fintype.card Leaf := by
  have hcurrentNonempty :
      (tree.pruneIter selected level ∩
        tree.fiber level node).Nonempty := by
    rcases Finset.nonempty_def.mp hnonempty with
      ⟨leaf, hleaf⟩
    have hleafData := Finset.mem_inter.mp hleaf
    exact Finset.nonempty_def.mpr
      ⟨leaf, Finset.mem_inter.mpr
        ⟨tree.pruneIter_antitone selected hlevel hleafData.1,
          hleafData.2⟩⟩
  have hbranch :=
    tree.pruneIter_branch_density
      selected hlevel node hcurrentNonempty
  have htail :=
    tree.pruneIter_local_cardinality
      selected (ancestorLevel := level) (start := level)
      (steps := depth - level) le_rfl (by omega) node
  have htail' :
      (tree.pruneIter selected level ∩
          tree.fiber level node).card ≤
        2 ^ (depth - level) *
          (tree.pruneIter selected depth ∩
            tree.fiber level node).card := by
    simpa [Nat.add_sub_of_le hlevel] using htail
  calc
    selected.card * (tree.fiber level node).card ≤
        2 ^ level *
          (tree.pruneIter selected level ∩
            tree.fiber level node).card *
          Fintype.card Leaf := hbranch
    _ ≤
        2 ^ level *
          (2 ^ (depth - level) *
            (tree.pruneIter selected depth ∩
              tree.fiber level node).card) *
          Fintype.card Leaf := by
      gcongr
    _ =
        2 ^ depth *
          (tree.pruneIter selected depth ∩
            tree.fiber level node).card *
          Fintype.card Leaf := by
      calc
        2 ^ level *
              (2 ^ (depth - level) *
                (tree.pruneIter selected depth ∩
                  tree.fiber level node).card) *
              Fintype.card Leaf =
            (2 ^ level * 2 ^ (depth - level)) *
              (tree.pruneIter selected depth ∩
                tree.fiber level node).card *
              Fintype.card Leaf := by ring
        _ = _ := by
          rw [← pow_add, Nat.add_sub_of_le hlevel]

structure CoreOutput (selected : Finset Leaf) where
  core : Finset Leaf
  core_eq :
    core = tree.pruneIter selected depth
  core_subset :
    core ⊆ selected
  global_retention :
    selected.card ≤ 2 ^ depth * core.card
  node_density :
    ∀ level, level ≤ depth →
      ∀ node,
        (core ∩ tree.fiber level node).Nonempty →
          selected.card * (tree.fiber level node).card ≤
            2 ^ depth *
              (core ∩ tree.fiber level node).card *
              Fintype.card Leaf

noncomputable def coreOutput (selected : Finset Leaf) :
    tree.CoreOutput selected where
  core := tree.pruneIter selected depth
  core_eq := rfl
  core_subset := tree.pruneIter_antitone selected (Nat.zero_le depth)
  global_retention := tree.pruneIter_cardinality selected depth
  node_density := by
    intro level hlevel node hnonempty
    exact tree.final_core_node_density
      selected hlevel node hnonempty

theorem final_core_density_from_global_fraction
    (selected : Finset Leaf)
    (pNumerator pDenominator : ℕ)
    (hglobal :
      pNumerator * Fintype.card Leaf ≤
        pDenominator * selected.card)
    {level : ℕ}
    (hlevel : level ≤ depth)
    (node : Node)
    (hnonempty :
      ((tree.coreOutput selected).core ∩
        tree.fiber level node).Nonempty) :
    pNumerator * (tree.fiber level node).card ≤
      (2 ^ depth * pDenominator) *
        (((tree.coreOutput selected).core ∩
          tree.fiber level node).card) := by
  have hnode :=
    (tree.coreOutput selected).node_density
      level hlevel node hnonempty
  have hmul :
      pNumerator * Fintype.card Leaf *
          (tree.fiber level node).card ≤
        pDenominator * selected.card *
          (tree.fiber level node).card := by
    gcongr
  have hright :
      pDenominator * selected.card *
          (tree.fiber level node).card ≤
        pDenominator *
          (2 ^ depth *
            (((tree.coreOutput selected).core ∩
              tree.fiber level node).card) *
            Fintype.card Leaf) := by
    calc
      pDenominator * selected.card *
            (tree.fiber level node).card =
          pDenominator *
            (selected.card *
              (tree.fiber level node).card) := by ring
      _ ≤
          pDenominator *
            (2 ^ depth *
              (((tree.coreOutput selected).core ∩
                tree.fiber level node).card) *
              Fintype.card Leaf) := by
        gcongr
  have hcombined := hmul.trans hright
  by_cases hleafCard : Fintype.card Leaf = 0
  · have hnodeEmpty : (tree.fiber level node).card = 0 := by
      have huniv : (Finset.univ : Finset Leaf) = ∅ := by
        apply Finset.card_eq_zero.mp
        simpa using hleafCard
      simp [fiber, huniv]
    rw [hnodeEmpty]
    simp
  · have hleafCardPos : 0 < Fintype.card Leaf :=
      Nat.pos_of_ne_zero hleafCard
    have hcancel :
        pNumerator * (tree.fiber level node).card ≤
          (2 ^ depth * pDenominator) *
            (((tree.coreOutput selected).core ∩
              tree.fiber level node).card) := by
      apply Nat.le_of_mul_le_mul_right
        (c := Fintype.card Leaf) ?_ hleafCardPos
      simpa [mul_assoc, mul_left_comm, mul_comm] using hcombined
    exact hcancel

end PureWZ2Prop62FiniteTree

end Kakeya.Assouad

end
