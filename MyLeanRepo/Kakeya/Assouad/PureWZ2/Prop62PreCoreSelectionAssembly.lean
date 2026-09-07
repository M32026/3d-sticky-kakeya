import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62WholeFiberCardinalityBin
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PerParentSourceColorLeafBin

/-!
# Proposition 6.2 pre-core selection assembly

This module combines the whole-fiber `D_-` selection with the independent
source-color choices in each retained parent and one global leaf-weight bin.
All geometric and coloring facts are inputs.  No tree cleanup is performed.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62PreCoreRetentionLedger
    {Leaf Parent Color : Type*}
    [DecidableEq Leaf]
    [Fintype Parent] [DecidableEq Parent]
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    (parents : Finset Parent)
    (parentWeight : Parent → ENNReal)
    (leafWeight : Leaf → ENNReal)
    (fiberCardBound : ℕ)
    (wholeLeaves colorSelected selectedLeaves : Finset Leaf)
    (selectedParents : Finset Parent)
    (dyadicBinCount : ℕ) where
  fiberBinLoss : ENNReal
  fiberBinLoss_eq :
    fiberBinLoss =
      (Nat.log 2 fiberCardBound + 1 : ENNReal)
  sourceColorLoss : ENNReal
  sourceColorLoss_eq :
    sourceColorLoss = Fintype.card Color
  leafBinLoss : ENNReal
  leafBinLoss_eq :
    leafBinLoss = 2 * dyadicBinCount
  totalLoss : ENNReal
  totalLoss_eq :
    totalLoss =
      fiberBinLoss * sourceColorLoss * leafBinLoss
  whole_fiber_retention :
    (∑ parent ∈ parents, parentWeight parent) ≤
      fiberBinLoss *
        ∑ parent ∈ selectedParents, parentWeight parent
  whole_fiber_mass :
    (∑ parent ∈ selectedParents, parentWeight parent) =
      ∑ leaf ∈ wholeLeaves, leafWeight leaf
  source_color_retention :
    (∑ leaf ∈ wholeLeaves, leafWeight leaf) ≤
      sourceColorLoss *
        ∑ leaf ∈ colorSelected, leafWeight leaf
  leaf_bin_retention :
    (∑ leaf ∈ colorSelected, leafWeight leaf) ≤
      leafBinLoss *
        ∑ leaf ∈ selectedLeaves, leafWeight leaf
  combined_retention :
    (∑ parent ∈ parents, parentWeight parent) ≤
      totalLoss *
        ∑ leaf ∈ selectedLeaves, leafWeight leaf

structure PureWZ2Prop62PreCoreSelectionData
    (Leaf Parent Color : Type*)
    [DecidableEq Leaf]
    [Fintype Parent] [DecidableEq Parent]
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    (parents : Finset Parent)
    (completeFiber : Parent → Finset Leaf)
    (fiberCard : Parent → ℕ)
    (parentWeight : Parent → ENNReal)
    (owner : Leaf → Parent)
    (sourceColor : Leaf → Color)
    (leafWeight : Leaf → ENNReal)
    (fiberCardBound : ℕ) where
  fiberBin :
    PureWZ2Prop62WholeFiberCardinalityBin
      parents fiberCard parentWeight fiberCardBound
  wholeLeaves : Finset Leaf
  wholeLeaves_eq :
    wholeLeaves =
      fiberBin.selectedParents.biUnion completeFiber
  complete_metric_fibers :
    ∀ parent ∈ fiberBin.selectedParents,
      completeFiber parent ⊆ wholeLeaves
  wholeLeaf_parent_selected :
    ∀ leaf ∈ wholeLeaves,
      owner leaf ∈ fiberBin.selectedParents
  leafBin :
    PureWZ2Prop62PerParentSourceColorLeafBinData
      Leaf Parent Color wholeLeaves owner sourceColor leafWeight
        (∑ parent ∈ fiberBin.selectedParents, parentWeight parent)
  preliminary : Finset Leaf
  preliminary_eq :
    preliminary = leafBin.selected
  preliminary_nonempty :
    preliminary.Nonempty
  preliminary_subset_whole_fibers :
    preliminary ⊆ wholeLeaves
  preliminary_parent_selected :
    ∀ leaf ∈ preliminary,
      owner leaf ∈ fiberBin.selectedParents
  source_monochromatic :
    ∀ leaf ∈ preliminary,
      sourceColor leaf =
        leafBin.selectedColor (owner leaf)
  leaf_weight_band :
    ∀ leaf ∈ preliminary,
      leafBin.weightLevel ≤ leafWeight leaf ∧
        leafWeight leaf ≤ 2 * leafBin.weightLevel
  retention :
    PureWZ2Prop62PreCoreRetentionLedger
      (Color := Color)
      parents parentWeight leafWeight fiberCardBound
      wholeLeaves leafBin.colorSelected preliminary
      fiberBin.selectedParents leafBin.dyadicBinCount

theorem pureWZ2_prop62_preCore_selection
    (Leaf Parent Color : Type*)
    [DecidableEq Leaf]
    [Fintype Parent] [DecidableEq Parent]
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    (parents : Finset Parent)
    (completeFiber : Parent → Finset Leaf)
    (fiberCard : Parent → ℕ)
    (parentWeight : Parent → ENNReal)
    (owner : Leaf → Parent)
    (sourceColor : Leaf → Color)
    (leafWeight : Leaf → ENNReal)
    (fiberCardBound : ℕ)
    (fiberCard_eq :
      ∀ parent ∈ parents,
        fiberCard parent = (completeFiber parent).card)
    (fiberCard_pos :
      ∀ parent ∈ parents, 0 < fiberCard parent)
    (fiberCard_le :
      ∀ parent ∈ parents,
        fiberCard parent ≤ fiberCardBound)
    (completeFiber_disjoint :
      Set.PairwiseDisjoint
        (↑parents : Set Parent) completeFiber)
    (completeFiber_owner :
      ∀ parent ∈ parents,
        ∀ leaf ∈ completeFiber parent,
          owner leaf = parent)
    (parentWeight_eq :
      ∀ parent ∈ parents,
        parentWeight parent =
          ∑ leaf ∈ completeFiber parent, leafWeight leaf)
    (totalParentWeight_finite :
      (∑ parent ∈ parents, parentWeight parent) ≠ ⊤)
    (totalParentWeight_pos :
      0 < ∑ parent ∈ parents, parentWeight parent) :
    Nonempty
      (PureWZ2Prop62PreCoreSelectionData
        Leaf Parent Color parents completeFiber fiberCard
        parentWeight owner sourceColor leafWeight fiberCardBound) := by
  let fiberBin :=
    pureWZ2Prop62WholeFiberCardinalityBin
      parents fiberCard parentWeight fiberCardBound
      fiberCard_pos fiberCard_le totalParentWeight_pos
  let wholeLeaves : Finset Leaf :=
    fiberBin.selectedParents.biUnion completeFiber
  have wholeLeavesNonempty : wholeLeaves.Nonempty := by
    rcases fiberBin.selectedParents_nonempty with
      ⟨parent, parentMem⟩
    have parentInParents :
        parent ∈ parents :=
      fiberBin.selectedParents_subset parentMem
    have fiberNonempty :
        (completeFiber parent).Nonempty := by
      apply Finset.card_pos.mp
      rw [← fiberCard_eq parent parentInParents]
      exact fiberCard_pos parent parentInParents
    rcases fiberNonempty with ⟨leaf, leafMem⟩
    exact
      ⟨leaf,
        Finset.mem_biUnion.mpr
          ⟨parent, parentMem, leafMem⟩⟩
  have selectedFibersDisjoint :
      Set.PairwiseDisjoint
        (↑fiberBin.selectedParents : Set Parent)
        completeFiber := by
    intro first firstMem second secondMem distinct
    exact
      completeFiber_disjoint
        (fiberBin.selectedParents_subset firstMem)
        (fiberBin.selectedParents_subset secondMem)
        distinct
  have wholeLeafParentSelected :
      ∀ leaf ∈ wholeLeaves,
        owner leaf ∈ fiberBin.selectedParents := by
    intro leaf leafMem
    rcases Finset.mem_biUnion.mp leafMem with
      ⟨parent, parentMem, leafFiber⟩
    rw [completeFiber_owner parent
      (fiberBin.selectedParents_subset parentMem)
      leaf leafFiber]
    exact parentMem
  have wholeFiberMass :
      (∑ parent ∈ fiberBin.selectedParents,
          parentWeight parent) =
        ∑ leaf ∈ wholeLeaves, leafWeight leaf := by
    calc
      (∑ parent ∈ fiberBin.selectedParents,
          parentWeight parent) =
          ∑ parent ∈ fiberBin.selectedParents,
            ∑ leaf ∈ completeFiber parent,
              leafWeight leaf := by
        apply Finset.sum_congr rfl
        intro parent parentMem
        exact
          parentWeight_eq parent
            (fiberBin.selectedParents_subset parentMem)
      _ =
          ∑ leaf ∈
              fiberBin.selectedParents.biUnion completeFiber,
            leafWeight leaf := by
        rw [Finset.sum_biUnion selectedFibersDisjoint]
      _ = ∑ leaf ∈ wholeLeaves, leafWeight leaf := by
        rfl
  have selectedParentWeightLe :
      (∑ parent ∈ fiberBin.selectedParents,
          parentWeight parent) ≤
        ∑ parent ∈ parents, parentWeight parent :=
    Finset.sum_le_sum_of_subset
      fiberBin.selectedParents_subset
  have selectedParentWeightFinite :
      (∑ parent ∈ fiberBin.selectedParents,
          parentWeight parent) ≠ ⊤ :=
    ne_top_of_le_ne_top
      totalParentWeight_finite selectedParentWeightLe
  have selectedParentWeightPos :
      0 <
        ∑ parent ∈ fiberBin.selectedParents,
          parentWeight parent := by
    by_contra selectedNotPos
    have selectedZero :
        (∑ parent ∈ fiberBin.selectedParents,
          parentWeight parent) = 0 := by
      simpa using selectedNotPos
    have totalLeZero :
        (∑ parent ∈ parents, parentWeight parent) ≤ 0 := by
      simpa [selectedZero] using fiberBin.weighted_retention
    exact
      (not_le_of_gt totalParentWeight_pos) totalLeZero
  let leafBin :=
    Classical.choice <|
      pureWZ2_prop62_perParent_sourceColor_leaf_bin
        Leaf Parent Color wholeLeaves wholeLeavesNonempty
        owner sourceColor leafWeight
        (∑ parent ∈ fiberBin.selectedParents,
          parentWeight parent)
        wholeFiberMass
        selectedParentWeightFinite
        selectedParentWeightPos
  let preliminary := leafBin.selected
  let fiberBinLoss : ENNReal :=
    Nat.log 2 fiberCardBound + 1
  let sourceColorLoss : ENNReal :=
    Fintype.card Color
  let leafBinLoss : ENNReal :=
    2 * leafBin.dyadicBinCount
  let totalLoss :=
    fiberBinLoss * sourceColorLoss * leafBinLoss
  have combinedRetention :
      (∑ parent ∈ parents, parentWeight parent) ≤
        totalLoss *
          ∑ leaf ∈ preliminary, leafWeight leaf := by
    calc
      (∑ parent ∈ parents, parentWeight parent) ≤
          fiberBinLoss *
            ∑ parent ∈ fiberBin.selectedParents,
              parentWeight parent := by
        exact fiberBin.weighted_retention
      _ =
          fiberBinLoss *
            ∑ leaf ∈ wholeLeaves, leafWeight leaf := by
        rw [wholeFiberMass]
      _ ≤
          fiberBinLoss *
            (sourceColorLoss *
              ∑ leaf ∈ leafBin.colorSelected,
                leafWeight leaf) := by
        gcongr
        rw [← wholeFiberMass]
        exact leafBin.sourceColor_retention
      _ ≤
          fiberBinLoss *
            (sourceColorLoss *
              (leafBinLoss *
                ∑ leaf ∈ preliminary,
                  leafWeight leaf)) := by
        gcongr
        exact leafBin.leafBin_retention
      _ =
          totalLoss *
            ∑ leaf ∈ preliminary, leafWeight leaf := by
        simp only [totalLoss]
        ring
  exact
    ⟨{
      fiberBin := fiberBin
      wholeLeaves := wholeLeaves
      wholeLeaves_eq := rfl
      complete_metric_fibers := by
        intro parent parentMem leaf leafMem
        exact
          Finset.mem_biUnion.mpr
            ⟨parent, parentMem, leafMem⟩
      wholeLeaf_parent_selected :=
        wholeLeafParentSelected
      leafBin := leafBin
      preliminary := preliminary
      preliminary_eq := rfl
      preliminary_nonempty :=
        leafBin.selected_nonempty
      preliminary_subset_whole_fibers :=
        leafBin.selected_subset_wholeLeaves
      preliminary_parent_selected := by
        intro leaf leafMem
        exact
          wholeLeafParentSelected leaf
            (leafBin.selected_subset_wholeLeaves leafMem)
      source_monochromatic :=
        leafBin.selected_monochromatic
      leaf_weight_band :=
        leafBin.selected_weight_band
      retention := {
        fiberBinLoss := fiberBinLoss
        fiberBinLoss_eq := rfl
        sourceColorLoss := sourceColorLoss
        sourceColorLoss_eq := rfl
        leafBinLoss := leafBinLoss
        leafBinLoss_eq := rfl
        totalLoss := totalLoss
        totalLoss_eq := rfl
        whole_fiber_retention :=
          fiberBin.weighted_retention
        whole_fiber_mass := wholeFiberMass
        source_color_retention := by
          rw [← wholeFiberMass]
          exact leafBin.sourceColor_retention
        leaf_bin_retention :=
          leafBin.leafBin_retention
        combined_retention := combinedRetention
      }
    }⟩

namespace PureWZ2Prop62PreCoreSelectionData

variable
    {Leaf Parent Color : Type*}
    [DecidableEq Leaf]
    [Fintype Parent] [DecidableEq Parent]
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    {parents : Finset Parent}
    {completeFiber : Parent → Finset Leaf}
    {fiberCard : Parent → ℕ}
    {parentWeight : Parent → ENNReal}
    {owner : Leaf → Parent}
    {sourceColor : Leaf → Color}
    {leafWeight : Leaf → ENNReal}
    {fiberCardBound : ℕ}
    (output :
      PureWZ2Prop62PreCoreSelectionData
        Leaf Parent Color parents completeFiber fiberCard
        parentWeight owner sourceColor leafWeight fiberCardBound)

theorem selected_completeFiber_eq :
    output.wholeLeaves =
      output.fiberBin.selectedParents.biUnion completeFiber :=
  output.wholeLeaves_eq

theorem DMinus_band
    (parent : Parent)
    (parentMem : parent ∈ output.fiberBin.selectedParents) :
    output.fiberBin.DMinus ≤ fiberCard parent ∧
      fiberCard parent < 2 * output.fiberBin.DMinus :=
  output.fiberBin.fiber_card_band parent parentMem

theorem fiberLevel_unique
    (candidateLevel : ℕ)
    (candidateLevel_eq :
      ∀ parent ∈ output.fiberBin.selectedParents,
        Nat.log 2 (fiberCard parent) = candidateLevel) :
    candidateLevel = output.fiberBin.fiberLevel :=
  output.fiberBin.fiberLevel_unique
    candidateLevel candidateLevel_eq

theorem DMinus_unique
    (candidateDMinus : ℕ)
    (candidateDMinus_eq :
      candidateDMinus = 2 ^ output.fiberBin.fiberLevel) :
    candidateDMinus = output.fiberBin.DMinus :=
  output.fiberBin.DMinus_unique
    candidateDMinus candidateDMinus_eq

end PureWZ2Prop62PreCoreSelectionData

end Kakeya.Assouad

end
