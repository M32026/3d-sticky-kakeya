import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TreePruning

/-!
# Proposition 6.2 one-pass tree cleanup: iteration

This iterates the one-level half-retention step from
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

theorem node_eq_of_le
    {coarse fine : ℕ}
    (hcoarseFine : coarse ≤ fine)
    (hfineDepth : fine ≤ depth)
    {first second : Leaf}
    (heq : tree.nodeAt fine first = tree.nodeAt fine second) :
    tree.nodeAt coarse first = tree.nodeAt coarse second := by
  induction fine generalizing coarse with
  | zero =>
      have hcoarse : coarse = 0 := by omega
      subst coarse
      exact heq
  | succ fine ih =>
      by_cases hcoarse : coarse = fine + 1
      · subst coarse
        exact heq
      · have hcoarseFine' : coarse ≤ fine := by omega
        have hfineDepth' : fine ≤ depth := by omega
        have hstep :
            tree.nodeAt fine first = tree.nodeAt fine second :=
          tree.nested fine (by omega) first second heq
        exact ih hcoarseFine' hfineDepth' hstep

theorem finer_fiber_subset_ancestor
    {coarse fine : ℕ}
    (hcoarseFine : coarse ≤ fine)
    (hfineDepth : fine ≤ depth)
    {fineNode coarseNode : Node}
    (hmeets :
      (tree.fiber fine fineNode ∩
        tree.fiber coarse coarseNode).Nonempty) :
    tree.fiber fine fineNode ⊆
      tree.fiber coarse coarseNode := by
  rcases Finset.nonempty_def.mp hmeets with
    ⟨witness, hwitness⟩
  have hwitnessData := Finset.mem_inter.mp hwitness
  have hwitnessFine := hwitnessData.1
  have hwitnessCoarse := hwitnessData.2
  have hwitnessFineEq :
      tree.nodeAt fine witness = fineNode :=
    (Finset.mem_filter.mp hwitnessFine).2
  have hwitnessCoarseEq :
      tree.nodeAt coarse witness = coarseNode :=
    (Finset.mem_filter.mp hwitnessCoarse).2
  intro source hsource
  have hsourceFineEq :
      tree.nodeAt fine source = fineNode :=
    (Finset.mem_filter.mp hsource).2
  have hsourceCoarse :
      tree.nodeAt coarse source =
        tree.nodeAt coarse witness :=
    tree.node_eq_of_le hcoarseFine hfineDepth <|
      hsourceFineEq.trans hwitnessFineEq.symm
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,
      hsourceCoarse.trans hwitnessCoarseEq⟩

def IsLevelSaturated
    (level : ℕ) (region : Finset Leaf) : Prop :=
  ∀ node,
    (tree.fiber level node ∩ region).Nonempty →
      tree.fiber level node ⊆ region

theorem ancestor_fiber_saturated
    {ancestorLevel level : ℕ}
    (hancestorLevel : ancestorLevel ≤ level)
    (hlevelDepth : level ≤ depth)
    (ancestor : Node) :
    tree.IsLevelSaturated level
      (tree.fiber ancestorLevel ancestor) := by
  intro node hmeets
  exact tree.finer_fiber_subset_ancestor
    hancestorLevel hlevelDepth hmeets

theorem selected_inter_region_card_eq_sum
    (level : ℕ)
    (selected region : Finset Leaf) :
    (selected ∩ region).card =
      ∑ node : Node,
        ((selected ∩ region) ∩ tree.fiber level node).card := by
  rw [tree.sum_selected_inter_fiber_card]

theorem pruneStep_local_half
    (level : ℕ)
    (selected region : Finset Leaf)
    (hsaturated : tree.IsLevelSaturated level region) :
    (selected ∩ region).card ≤
      2 * (tree.pruneStep level selected ∩ region).card := by
  have hterm :
      ∀ node : Node,
        ((selected ∩ region) ∩ tree.fiber level node).card ≤
          2 *
            ((tree.pruneStep level selected ∩ region) ∩
              tree.fiber level node).card := by
    intro node
    by_cases hnonempty :
        ((selected ∩ region) ∩ tree.fiber level node).Nonempty
    · have hfiberRegion :
          (tree.fiber level node ∩ region).Nonempty := by
        rcases Finset.nonempty_def.mp hnonempty with
          ⟨leaf, hleaf⟩
        have hdata := Finset.mem_inter.mp hleaf
        exact Finset.nonempty_def.mpr
          ⟨leaf,
            Finset.mem_inter.mpr
              ⟨hdata.2, (Finset.mem_inter.mp hdata.1).2⟩⟩
      have hfiberSubset : tree.fiber level node ⊆ region :=
        hsaturated node hfiberRegion
      have hleft :
          (selected ∩ region) ∩ tree.fiber level node =
            selected ∩ tree.fiber level node := by
        ext leaf
        simp only [Finset.mem_inter]
        constructor
        · rintro ⟨⟨hselected, hregion⟩, hfiber⟩
          exact ⟨hselected, hfiber⟩
        · rintro ⟨hselected, hfiber⟩
          exact ⟨⟨hselected, hfiberSubset hfiber⟩, hfiber⟩
      have hright :
          (tree.pruneStep level selected ∩ region) ∩
              tree.fiber level node =
            (tree.layer level node).retainedLeaves selected := by
        calc
          (tree.pruneStep level selected ∩ region) ∩
                tree.fiber level node =
              (tree.pruneStep level selected ∩
                tree.fiber level node) := by
            ext leaf
            simp only [Finset.mem_inter]
            constructor
            · rintro ⟨⟨hstep, hregion⟩, hfiber⟩
              exact ⟨hstep, hfiber⟩
            · rintro ⟨hstep, hfiber⟩
              exact ⟨⟨hstep, hfiberSubset hfiber⟩, hfiber⟩
          _ = (tree.layer level node).retainedLeaves selected :=
            tree.pruneStep_inter_fiber level selected node
      rw [hleft, hright]
      exact
        (tree.layer level node).selected_card_le_two_retained
          selected <| by
            change (selected ∩ tree.fiber level node).Nonempty
            rw [← hleft]
            exact hnonempty
    · have hempty :
          (selected ∩ region) ∩ tree.fiber level node = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnonempty
      rw [hempty]
      simp
  calc
    (selected ∩ region).card =
        ∑ node : Node,
          ((selected ∩ region) ∩ tree.fiber level node).card :=
      tree.selected_inter_region_card_eq_sum level selected region
    _ ≤
        ∑ node : Node,
          2 *
            ((tree.pruneStep level selected ∩ region) ∩
              tree.fiber level node).card :=
      Finset.sum_le_sum fun node _ => hterm node
    _ =
        2 *
          ∑ node : Node,
            ((tree.pruneStep level selected ∩ region) ∩
              tree.fiber level node).card := by
      rw [Finset.mul_sum]
    _ =
        2 * (tree.pruneStep level selected ∩ region).card := by
      rw [tree.sum_selected_inter_fiber_card]

def pruneIter (selected : Finset Leaf) : ℕ → Finset Leaf
  | 0 => selected
  | step + 1 => tree.pruneStep step (pruneIter selected step)

@[simp]
theorem pruneIter_zero (selected : Finset Leaf) :
    tree.pruneIter selected 0 = selected := rfl

@[simp]
theorem pruneIter_succ (selected : Finset Leaf) (step : ℕ) :
    tree.pruneIter selected (step + 1) =
      tree.pruneStep step (tree.pruneIter selected step) := rfl

theorem pruneIter_succ_subset
    (selected : Finset Leaf) (step : ℕ) :
    tree.pruneIter selected (step + 1) ⊆
      tree.pruneIter selected step :=
  tree.pruneStep_subset step (tree.pruneIter selected step)

theorem pruneIter_antitone
    (selected : Finset Leaf)
    {first second : ℕ}
    (hfirstSecond : first ≤ second) :
    tree.pruneIter selected second ⊆
      tree.pruneIter selected first := by
  induction second generalizing first with
  | zero =>
      have hfirst : first = 0 := by omega
      subst first
      exact fun _ h => h
  | succ second ih =>
      by_cases hEq : first = second + 1
      · subst first
        exact fun _ h => h
      · exact
          (tree.pruneIter_succ_subset selected second).trans
            (ih (by omega))

theorem pruneIter_cardinality
    (selected : Finset Leaf) (steps : ℕ) :
    selected.card ≤
      2 ^ steps * (tree.pruneIter selected steps).card := by
  induction steps with
  | zero =>
      simp
  | succ steps ih =>
      calc
        selected.card ≤
            2 ^ steps * (tree.pruneIter selected steps).card := ih
        _ ≤
            2 ^ steps *
              (2 *
                (tree.pruneIter selected (steps + 1)).card) := by
          gcongr
          exact tree.selected_card_le_two_pruneStep
            steps (tree.pruneIter selected steps)
        _ =
            2 ^ (steps + 1) *
              (tree.pruneIter selected (steps + 1)).card := by
          rw [pow_succ]
          ring

theorem pruneIter_local_cardinality
    (selected : Finset Leaf)
    {ancestorLevel start steps : ℕ}
    (hancestorStart : ancestorLevel ≤ start)
    (hfinishDepth : start + steps ≤ depth)
    (ancestor : Node) :
    (tree.pruneIter selected start ∩
        tree.fiber ancestorLevel ancestor).card ≤
      2 ^ steps *
        (tree.pruneIter selected (start + steps) ∩
          tree.fiber ancestorLevel ancestor).card := by
  induction steps with
  | zero =>
      simp
  | succ steps ih =>
      have hstepDepth : start + steps ≤ depth := by omega
      have hancestorStep : ancestorLevel ≤ start + steps := by omega
      have hlocal :=
        tree.pruneStep_local_half
          (start + steps)
          (tree.pruneIter selected (start + steps))
          (tree.fiber ancestorLevel ancestor)
          (tree.ancestor_fiber_saturated
            hancestorStep hstepDepth ancestor)
      have hlocal' :
          (tree.pruneIter selected (start + steps) ∩
              tree.fiber ancestorLevel ancestor).card ≤
            2 *
              (tree.pruneIter selected (start + steps + 1) ∩
                tree.fiber ancestorLevel ancestor).card := by
        rw [tree.pruneIter_succ selected (start + steps)]
        exact hlocal
      calc
        (tree.pruneIter selected start ∩
            tree.fiber ancestorLevel ancestor).card ≤
          2 ^ steps *
            (tree.pruneIter selected (start + steps) ∩
              tree.fiber ancestorLevel ancestor).card := by
            exact ih (by omega)
        _ ≤
          2 ^ steps *
            (2 *
              (tree.pruneIter selected (start + steps + 1) ∩
                tree.fiber ancestorLevel ancestor).card) := by
          gcongr
        _ =
          2 ^ (steps + 1) *
            (tree.pruneIter selected (start + (steps + 1)) ∩
              tree.fiber ancestorLevel ancestor).card := by
          rw [pow_succ]
          ring

end PureWZ2Prop62FiniteTree

end Kakeya.Assouad

end
