import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TreeCore

/-!
# Proposition 6.2 one-pass tree cleanup: dyadic weights

This proves the `2^{-(L+1)}` weight-retention statement in
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

theorem dyadic_weight_retention
    (selected : Finset Leaf)
    (weight : Leaf → ENNReal)
    (weightLevel : ENNReal)
    (hlower :
      ∀ leaf ∈ selected, weightLevel ≤ weight leaf)
    (hupper :
      ∀ leaf ∈ selected, weight leaf ≤ 2 * weightLevel) :
    ∑ leaf ∈ selected, weight leaf ≤
      2 ^ (depth + 1) *
        ∑ leaf ∈ (tree.coreOutput selected).core,
          weight leaf := by
  let core := (tree.coreOutput selected).core
  have hcoreSubset : core ⊆ selected :=
    (tree.coreOutput selected).core_subset
  have hselectedUpper :
      ∑ leaf ∈ selected, weight leaf ≤
        selected.card * (2 * weightLevel) := by
    calc
      ∑ leaf ∈ selected, weight leaf ≤
          ∑ _leaf ∈ selected, 2 * weightLevel := by
        exact Finset.sum_le_sum fun leaf hleaf =>
          hupper leaf hleaf
      _ = selected.card * (2 * weightLevel) := by
        simp [Finset.sum_const]
  have hcoreLower :
      core.card * weightLevel ≤
        ∑ leaf ∈ core, weight leaf := by
    calc
      core.card * weightLevel =
          ∑ _leaf ∈ core, weightLevel := by
        simp [Finset.sum_const]
      _ ≤ ∑ leaf ∈ core, weight leaf := by
        exact Finset.sum_le_sum fun leaf hleaf =>
          hlower leaf (hcoreSubset hleaf)
  have hcard :=
    (tree.coreOutput selected).global_retention
  have hcardENN :
      (selected.card : ENNReal) ≤
        (2 ^ depth : ENNReal) * (core.card : ENNReal) := by
    exact_mod_cast hcard
  calc
    ∑ leaf ∈ selected, weight leaf ≤
        selected.card * (2 * weightLevel) := hselectedUpper
    _ ≤
        (2 ^ depth * core.card) * (2 * weightLevel) := by
      gcongr
    _ =
        2 ^ (depth + 1) * (core.card * weightLevel) := by
      rw [pow_succ]
      ring
    _ ≤
        2 ^ (depth + 1) *
          ∑ leaf ∈ core, weight leaf := by
      gcongr

end PureWZ2Prop62FiniteTree

end Kakeya.Assouad

end
