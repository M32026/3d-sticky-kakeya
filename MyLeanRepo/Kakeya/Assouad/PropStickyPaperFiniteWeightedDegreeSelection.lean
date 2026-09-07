import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization

/-!
# Packaged finite weighted simultaneous-degree selection

This is a typed wrapper around the closed simultaneous-degree regularizer.
The explicit coordinate map lets later paper-facing modules synchronize
spatial cells, current coarse parents, and every parent map in one finite
selection.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2FiniteWeightedDegreeSelectionData
    {indexType : Type*} [Fintype indexType] [DecidableEq indexType]
    (coordinateCount : ℕ)
    (Vertex : Fin coordinateCount → Type)
    [∀ coordinate, Fintype (Vertex coordinate)]
    [∀ coordinate, DecidableEq (Vertex coordinate)]
    (parent : ∀ coordinate, indexType → Vertex coordinate)
    (weight : indexType → ENNReal) where
  selected : Finset indexType
  degree_uniform :
    ∀ coordinate,
      ∀ first second : Vertex coordinate,
        0 <
            (selected.filter fun index =>
              parent coordinate index = first).card →
        0 <
            (selected.filter fun index =>
              parent coordinate index = second).card →
        ((selected.filter fun index =>
          parent coordinate index = first).card : ENNReal) ≤
          (16 * (coordinateCount : ENNReal) *
            (Nat.log 2 (2 * Fintype.card indexType) + 1 : ENNReal) ^
              coordinateCount) *
            ((selected.filter fun index =>
              parent coordinate index = second).card : ENNReal)
  retained_weight :
    (∑ index : indexType, weight index) ≤
      (8 : ENNReal) *
        (Nat.log 2 (2 * Fintype.card indexType) + 1 : ENNReal) ^
          (coordinateCount + 1) *
        ∑ index ∈ selected, weight index
  selected_weight_pos :
    ∀ index ∈ selected, 0 < weight index
  selected_weight_floor :
    ∀ index ∈ selected,
      (∑ source : indexType, weight source) /
            (2 * Fintype.card indexType : ENNReal) ≤
        weight index
  weightLevel : ENNReal
  weightLevel_pos : 0 < weightLevel
  weight_band :
    ∀ index ∈ selected,
      weightLevel ≤ weight index ∧
        weight index ≤ 2 * weightLevel

theorem wz2_finite_weighted_degree_selection
    {indexType : Type*} [Fintype indexType] [DecidableEq indexType]
    (coordinateCount : ℕ)
    (Vertex : Fin coordinateCount → Type)
    [∀ coordinate, Fintype (Vertex coordinate)]
    [∀ coordinate, DecidableEq (Vertex coordinate)]
    (parent : ∀ coordinate, indexType → Vertex coordinate)
    (weight : indexType → ENNReal)
    (coordinateCountPos : 0 < coordinateCount) :
    Nonempty
      (WZ2FiniteWeightedDegreeSelectionData
        coordinateCount Vertex parent weight) := by
  rcases
      simultaneous_degree_regularization_with_support_and_weight_band
        coordinateCount Vertex parent weight
    with
    ⟨selected, degreeUniform, retainedWeight, selectedWeightPos,
      selectedWeightFloor, weightBandExists⟩
  rcases weightBandExists coordinateCountPos with
    ⟨weightLevel, weightLevelPos, weightBand⟩
  exact
    ⟨{
      selected := selected
      degree_uniform := degreeUniform
      retained_weight := retainedWeight
      selected_weight_pos := selectedWeightPos
      selected_weight_floor :=
        selectedWeightFloor coordinateCountPos
      weightLevel := weightLevel
      weightLevel_pos := weightLevelPos
      weight_band := weightBand
    }⟩

end Kakeya.Assouad

end
