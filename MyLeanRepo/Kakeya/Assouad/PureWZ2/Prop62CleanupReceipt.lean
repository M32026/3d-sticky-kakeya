import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TreeCWA

/-!
# Proposition 6.2 cleanup receipt

This module packages the outputs of the one-pass finite-tree cleanup behind
an interface independent of the paper-audit statement modules.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62CleanupReceipt
    {Leaf Node : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Node] [DecidableEq Node]
    {depth : ℕ}
    (tree : PureWZ2Prop62FiniteTree Leaf Node depth)
    (selected : Finset Leaf) where
  core : Finset Leaf
  core_subset : core ⊆ selected
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
  weighted_retention :
    ∀ (weight : Leaf → ENNReal) (weightLevel : ENNReal),
      (∀ leaf ∈ selected, weightLevel ≤ weight leaf) →
      (∀ leaf ∈ selected, weight leaf ≤ 2 * weightLevel) →
        ∑ leaf ∈ selected, weight leaf ≤
          2 ^ (depth + 1) * ∑ leaf ∈ core, weight leaf
  local_cwa_transfer :
    ∀ level, level ≤ depth →
      ∀ node,
        (core ∩ tree.fiber level node).Nonempty →
        ∀ (constant volumeFactor : ENNReal),
          ∀ count : Finset Leaf → ENNReal,
            (∀ first second, first ⊆ second →
              count first ≤ count second) →
            count (tree.fiber level node) ≤
                constant * volumeFactor *
                  (tree.fiber level node).card →
              count (core ∩ tree.fiber level node) ≤
                (constant * (2 ^ depth : ENNReal) *
                    (Fintype.card Leaf : ENNReal) *
                    (selected.card : ENNReal)⁻¹) *
                  volumeFactor *
                  ((core ∩ tree.fiber level node).card : ENNReal)

noncomputable def pureWZ2Prop62CleanupReceipt
    {Leaf Node : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Node] [DecidableEq Node]
    {depth : ℕ}
    (tree : PureWZ2Prop62FiniteTree Leaf Node depth)
    (selected : Finset Leaf) :
    PureWZ2Prop62CleanupReceipt tree selected := by
  let output := tree.coreOutput selected
  exact
    {
      core := output.core
      core_subset := output.core_subset
      global_retention := output.global_retention
      node_density := output.node_density
      weighted_retention := by
        intro weight weightLevel lower upper
        exact
          tree.dyadic_weight_retention
            selected weight weightLevel lower upper
      local_cwa_transfer := by
        intro level levelLe node nonempty constant volumeFactor
          count countMono ambientCWA
        exact
          tree.local_cwa_transfer
            selected levelLe node nonempty constant volumeFactor
              count countMono ambientCWA
    }

end Kakeya.Assouad

end
