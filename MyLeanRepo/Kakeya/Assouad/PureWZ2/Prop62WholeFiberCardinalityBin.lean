import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization.HeavyColorClass

/-!
# Proposition 6.2 whole-fiber cardinality bin

This module selects one dyadic whole-fiber cardinality class from a finite
set of parents.  Its interface is independent of all ancestry and metric
output records.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62WholeFiberCardinalityBin
    {Parent : Type*}
    [DecidableEq Parent]
    (parents : Finset Parent)
    (fiberCard : Parent → ℕ)
    (parentWeight : Parent → ENNReal)
    (fiberCardBound : ℕ) where
  fiberLevel : ℕ
  fiberLevel_lt :
    fiberLevel < Nat.log 2 fiberCardBound + 1
  DMinus : ℕ
  DMinus_eq :
    DMinus = 2 ^ fiberLevel
  DMinus_pos :
    0 < DMinus
  selectedParents : Finset Parent
  selectedParents_nonempty :
    selectedParents.Nonempty
  selectedParents_subset :
    selectedParents ⊆ parents
  fiberLevel_eq :
    ∀ parent ∈ selectedParents,
      Nat.log 2 (fiberCard parent) = fiberLevel
  fiber_card_band :
    ∀ parent ∈ selectedParents,
      DMinus ≤ fiberCard parent ∧
        fiberCard parent < 2 * DMinus
  weighted_retention :
    (∑ parent ∈ parents, parentWeight parent) ≤
      (Nat.log 2 fiberCardBound + 1 : ENNReal) *
        ∑ parent ∈ selectedParents, parentWeight parent
  fiberLevel_unique :
    ∀ candidateLevel,
      (∀ parent ∈ selectedParents,
        Nat.log 2 (fiberCard parent) = candidateLevel) →
      candidateLevel = fiberLevel
  DMinus_unique :
    ∀ candidateDMinus,
      candidateDMinus = 2 ^ fiberLevel →
      candidateDMinus = DMinus

theorem exists_pureWZ2Prop62WholeFiberCardinalityBin
    {Parent : Type*}
    [DecidableEq Parent]
    (parents : Finset Parent)
    (fiberCard : Parent → ℕ)
    (parentWeight : Parent → ENNReal)
    (fiberCardBound : ℕ)
    (fiberCard_pos :
      ∀ parent ∈ parents, 0 < fiberCard parent)
    (fiberCard_le :
      ∀ parent ∈ parents, fiberCard parent ≤ fiberCardBound)
    (totalWeight_pos :
      0 < ∑ parent ∈ parents, parentWeight parent) :
    Nonempty
      (PureWZ2Prop62WholeFiberCardinalityBin
        parents fiberCard parentWeight fiberCardBound) := by
  let fiberBinCount := Nat.log 2 fiberCardBound + 1
  have fiberBinCountPos : 0 < fiberBinCount := by
    simp [fiberBinCount]
  have fiberLevelLt :
      ∀ parent ∈ parents,
        Nat.log 2 (fiberCard parent) < fiberBinCount := by
    intro parent parentMem
    have logLe :
        Nat.log 2 (fiberCard parent) ≤
          Nat.log 2 fiberCardBound :=
      Nat.log_mono_right (fiberCard_le parent parentMem)
    simpa [fiberBinCount] using Nat.lt_succ_of_le logLe
  let fiberColor : Parent → Fin fiberBinCount :=
    fun parent =>
      if parentMem : parent ∈ parents then
        ⟨Nat.log 2 (fiberCard parent),
          fiberLevelLt parent parentMem⟩
      else
        ⟨0, fiberBinCountPos⟩
  rcases
      exists_heavy_color_class
        parents fiberBinCount fiberBinCountPos
        fiberColor parentWeight
    with ⟨selectedFiberLevel, fiberRetention⟩
  let fiberLevel := selectedFiberLevel.val
  let DMinus := 2 ^ fiberLevel
  let selectedParents :=
    parents.filter fun parent =>
      Nat.log 2 (fiberCard parent) = fiberLevel
  have selectedParentsColorEq :
      selectedParents =
        parents.filter fun parent =>
          fiberColor parent = selectedFiberLevel := by
    ext parent
    constructor
    · intro parentMem
      rcases Finset.mem_filter.mp parentMem with
        ⟨parentInParents, logEq⟩
      apply Finset.mem_filter.mpr
      refine ⟨parentInParents, Fin.ext ?_⟩
      simpa [fiberColor, parentInParents, fiberLevel] using logEq
    · intro parentMem
      rcases Finset.mem_filter.mp parentMem with
        ⟨parentInParents, colorEq⟩
      apply Finset.mem_filter.mpr
      refine ⟨parentInParents, ?_⟩
      have valueEq := congrArg Fin.val colorEq
      simpa [fiberColor, parentInParents, fiberLevel] using valueEq
  have selectedWeightPos :
      0 <
        ∑ parent ∈ selectedParents,
          parentWeight parent := by
    by_contra selectedNotPos
    have selectedZero :
        (∑ parent ∈ selectedParents,
          parentWeight parent) = 0 := by
      simpa using selectedNotPos
    have totalLeZero :
        (∑ parent ∈ parents, parentWeight parent) ≤ 0 := by
      have heavy :
          (∑ parent ∈ parents, parentWeight parent) ≤
            (fiberBinCount : ENNReal) *
              ∑ parent ∈ selectedParents,
                parentWeight parent := by
        rw [selectedParentsColorEq]
        exact fiberRetention
      simpa [selectedZero] using heavy
    exact (not_le_of_gt totalWeight_pos) totalLeZero
  have selectedParentsNonempty :
      selectedParents.Nonempty := by
    by_contra selectedEmpty
    have selectedEq : selectedParents = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp selectedEmpty
    rw [selectedEq] at selectedWeightPos
    simp at selectedWeightPos
  have fiberLevelEq :
      ∀ parent ∈ selectedParents,
        Nat.log 2 (fiberCard parent) = fiberLevel := by
    intro parent parentMem
    exact (Finset.mem_filter.mp parentMem).2
  have fiberCardBand :
      ∀ parent ∈ selectedParents,
        DMinus ≤ fiberCard parent ∧
          fiberCard parent < 2 * DMinus := by
    intro parent parentMem
    have parentInParents :
        parent ∈ parents :=
      (Finset.mem_filter.mp parentMem).1
    have logEq :=
      fiberLevelEq parent parentMem
    have cardPos :
        0 < fiberCard parent :=
      fiberCard_pos parent parentInParents
    constructor
    · simpa [DMinus, logEq] using
        Nat.pow_log_le_self 2 cardPos.ne'
    · have upper :=
        Nat.lt_pow_succ_log_self
          (by norm_num : 1 < 2)
          (fiberCard parent)
      rw [logEq, pow_succ] at upper
      simpa [DMinus, Nat.mul_comm] using upper
  have fiberLevelUnique :
      ∀ candidateLevel,
        (∀ parent ∈ selectedParents,
          Nat.log 2 (fiberCard parent) = candidateLevel) →
        candidateLevel = fiberLevel := by
    intro candidateLevel candidateLevelEq
    rcases selectedParentsNonempty with
      ⟨parent, parentMem⟩
    exact
      (candidateLevelEq parent parentMem).symm.trans
        (fiberLevelEq parent parentMem)
  exact
    ⟨{
      fiberLevel := fiberLevel
      fiberLevel_lt := selectedFiberLevel.2
      DMinus := DMinus
      DMinus_eq := rfl
      DMinus_pos := by positivity
      selectedParents := selectedParents
      selectedParents_nonempty := selectedParentsNonempty
      selectedParents_subset := Finset.filter_subset _ _
      fiberLevel_eq := fiberLevelEq
      fiber_card_band := fiberCardBand
      weighted_retention := by
        rw [selectedParentsColorEq]
        simpa [fiberBinCount] using fiberRetention
      fiberLevel_unique := fiberLevelUnique
      DMinus_unique := by
        intro candidateDMinus candidateEq
        exact candidateEq.trans rfl
    }⟩

noncomputable def pureWZ2Prop62WholeFiberCardinalityBin
    {Parent : Type*}
    [DecidableEq Parent]
    (parents : Finset Parent)
    (fiberCard : Parent → ℕ)
    (parentWeight : Parent → ENNReal)
    (fiberCardBound : ℕ)
    (fiberCard_pos :
      ∀ parent ∈ parents, 0 < fiberCard parent)
    (fiberCard_le :
      ∀ parent ∈ parents, fiberCard parent ≤ fiberCardBound)
    (totalWeight_pos :
      0 < ∑ parent ∈ parents, parentWeight parent) :
    PureWZ2Prop62WholeFiberCardinalityBin
      parents fiberCard parentWeight fiberCardBound :=
  Classical.choice <|
    exists_pureWZ2Prop62WholeFiberCardinalityBin
      parents fiberCard parentWeight fiberCardBound
      fiberCard_pos fiberCard_le totalWeight_pos

end Kakeya.Assouad

end
