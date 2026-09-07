import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TreeWeight

/-!
# Proposition 6.2 one-pass tree cleanup: CWA transfer

This is the local Convex-Wolff transfer calculation in
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

theorem local_cwa_transfer
    (selected : Finset Leaf)
    {level : ℕ}
    (hlevel : level ≤ depth)
    (node : Node)
    (hnonempty :
      ((tree.coreOutput selected).core ∩
        tree.fiber level node).Nonempty)
    (C volumeFactor : ENNReal)
    (count : Finset Leaf → ENNReal)
    (count_mono :
      ∀ first second, first ⊆ second →
        count first ≤ count second)
    (ambient_cwa :
      count (tree.fiber level node) ≤
        C * volumeFactor *
          (tree.fiber level node).card) :
    count
        ((tree.coreOutput selected).core ∩
          tree.fiber level node) ≤
      (C * (2 ^ depth : ENNReal) *
          (Fintype.card Leaf : ENNReal) *
          (selected.card : ENNReal)⁻¹) *
        volumeFactor *
        (((tree.coreOutput selected).core ∩
          tree.fiber level node).card : ENNReal) := by
  let coreFiber :=
    (tree.coreOutput selected).core ∩
      tree.fiber level node
  have hcount :
      count coreFiber ≤ count (tree.fiber level node) :=
    count_mono _ _ Finset.inter_subset_right
  have hdensityNat :=
    (tree.coreOutput selected).node_density
      level hlevel node hnonempty
  have hdensity :
      (selected.card : ENNReal) *
          ((tree.fiber level node).card : ENNReal) ≤
        (2 ^ depth : ENNReal) *
          (coreFiber.card : ENNReal) *
          (Fintype.card Leaf : ENNReal) := by
    exact_mod_cast hdensityNat
  have hselectedPos : 0 < selected.card := by
    rcases Finset.nonempty_def.mp hnonempty with
      ⟨leaf, hleaf⟩
    exact Finset.card_pos.mpr
      ⟨leaf,
        (tree.coreOutput selected).core_subset
          (Finset.mem_inter.mp hleaf).1⟩
  have hselectedENNPos : 0 < (selected.card : ENNReal) := by
    exact_mod_cast hselectedPos
  have hselectedENNTop :
      (selected.card : ENNReal) ≠ ⊤ := by simp
  have hfiberBound :
      ((tree.fiber level node).card : ENNReal) ≤
        (2 ^ depth : ENNReal) *
          (coreFiber.card : ENNReal) *
          (Fintype.card Leaf : ENNReal) *
          (selected.card : ENNReal)⁻¹ := by
    calc
      ((tree.fiber level node).card : ENNReal) =
          (1 : ENNReal) *
            ((tree.fiber level node).card : ENNReal) := by simp
      _ =
          ((selected.card : ENNReal) *
            (selected.card : ENNReal)⁻¹) *
            ((tree.fiber level node).card : ENNReal) := by
        rw [ENNReal.mul_inv_cancel
          hselectedENNPos.ne' hselectedENNTop]
      _ =
          ((selected.card : ENNReal) *
            ((tree.fiber level node).card : ENNReal)) *
            (selected.card : ENNReal)⁻¹ := by ring
      _ ≤
          ((2 ^ depth : ENNReal) *
            (coreFiber.card : ENNReal) *
            (Fintype.card Leaf : ENNReal)) *
            (selected.card : ENNReal)⁻¹ := by
        gcongr
      _ =
          (2 ^ depth : ENNReal) *
            (coreFiber.card : ENNReal) *
            (Fintype.card Leaf : ENNReal) *
            (selected.card : ENNReal)⁻¹ := rfl
  calc
    count coreFiber ≤ count (tree.fiber level node) := hcount
    _ ≤
        C * volumeFactor *
          ((tree.fiber level node).card : ENNReal) :=
      ambient_cwa
    _ ≤
        C * volumeFactor *
          ((2 ^ depth : ENNReal) *
            (coreFiber.card : ENNReal) *
            (Fintype.card Leaf : ENNReal) *
            (selected.card : ENNReal)⁻¹) := by
      gcongr
    _ =
      (C * (2 ^ depth : ENNReal) *
          (Fintype.card Leaf : ENNReal) *
          (selected.card : ENNReal)⁻¹) *
        volumeFactor *
        (coreFiber.card : ENNReal) := by ring

end PureWZ2Prop62FiniteTree

end Kakeya.Assouad

end
