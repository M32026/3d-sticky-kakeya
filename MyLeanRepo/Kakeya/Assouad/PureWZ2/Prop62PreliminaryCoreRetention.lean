import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PreliminarySelection

/-!
# Proposition 6.2 metric parents: preliminary-to-core weight retention

The paper makes every finite structural choice in one dependent color vector,
then performs one dyadic leaf-weight selection and one augmented-tree cleanup.
This module composes exactly those three losses.  No geometric family is
selected after the final core.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem PureWZ2Prop62PreliminarySelectionData.core_weight_retention
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule fine ambientConstant scaleWindow}
    {Aux : Type}
    [Fintype Aux] [DecidableEq Aux]
    (auxiliary : PureWZ2Prop62AuxiliaryLevel schedule Aux)
    (coordinateCount : ℕ)
    (Color : Fin coordinateCount → Type*)
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    (color : ∀ coordinate, Fin fine.card → Color coordinate)
    (weight : Fin fine.card → ENNReal)
    (preliminary :
      PureWZ2Prop62PreliminarySelectionData
        coordinateCount Color color weight) :
    (∑ leaf : Fin fine.card, weight leaf) ≤
      (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
        (2 * preliminary.dyadicBinCount : ENNReal) *
        (2 ^ (schedule.levelCount + 2) : ENNReal) *
        ∑ leaf ∈ auxiliary.coreIndices preliminary.selected,
          weight leaf := by
  have selectedRetention :
      ∑ leaf ∈ preliminary.selected, weight leaf ≤
        (2 ^ (schedule.levelCount + 2) : ENNReal) *
          ∑ leaf ∈ auxiliary.coreIndices preliminary.selected,
            weight leaf := by
    have treeRetention :=
      auxiliary.tree.dyadic_weight_retention
        preliminary.selected weight preliminary.weightLevel
        (fun leaf hleaf =>
          (preliminary.selected_weight_band leaf hleaf).1)
        (fun leaf hleaf =>
          (preliminary.selected_weight_band leaf hleaf).2)
    simpa only [
      PureWZ2Prop62AuxiliaryLevel.tree,
      PureWZ2Prop62AuxiliaryLevel.coreIndices,
      PureWZ2Prop62AuxiliaryLevel.coreOutput,
      Nat.add_assoc
    ] using treeRetention
  calc
    (∑ leaf : Fin fine.card, weight leaf) ≤
        (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
          ∑ leaf ∈ preliminary.colorClass, weight leaf :=
      preliminary.color_retention
    _ ≤
        (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
          ((2 * preliminary.dyadicBinCount : ENNReal) *
            ∑ leaf ∈ preliminary.selected, weight leaf) := by
      apply mul_le_mul_left'
      simpa only [Nat.cast_ofNat, Nat.cast_mul, Nat.cast_id] using
        preliminary.dyadic_retention
    _ ≤
        (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
          ((2 * preliminary.dyadicBinCount : ENNReal) *
            ((2 ^ (schedule.levelCount + 2) : ENNReal) *
              ∑ leaf ∈ auxiliary.coreIndices preliminary.selected,
                weight leaf)) := by
      gcongr
    _ = _ := by ring

end Kakeya.Assouad

end
