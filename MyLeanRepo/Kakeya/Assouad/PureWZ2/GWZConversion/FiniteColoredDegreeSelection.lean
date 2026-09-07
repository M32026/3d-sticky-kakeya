import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFiniteWeightedDegreeSelection

/-!
# Finite simultaneous colored degree selection

For finitely many dependent color maps and parent maps:

1. choose one complete color vector by a single weighted pigeonhole;
2. on that one color-vector class, apply the closed weighted simultaneous
   degree regularizer to all parent maps at once.

There is no sequential restriction by scale.  The output keeps the original
ambient index type through an explicit color-class subtype.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Weighted pigeonhole for a dependent finite color vector. -/
theorem wz2_finite_dependent_color_weighted_pigeonhole
    {indexType : Type*}
    [Fintype indexType] [DecidableEq indexType]
    (coordinateCount : ℕ)
    (Color : Fin coordinateCount → Type*)
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    (color : ∀ coordinate, indexType → Color coordinate)
    (weight : indexType → ENNReal) :
    ∃ colorVector : ∀ coordinate, Color coordinate,
      (∑ index : indexType, weight index) ≤
        (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
          ∑ index ∈
            (Finset.univ.filter fun index =>
              ∀ coordinate, color coordinate index =
                colorVector coordinate),
            weight index := by
  let ColorVector := ∀ coordinate, Color coordinate
  let indexColor : indexType → ColorVector := fun index coordinate =>
    color coordinate index
  let classWeight : ColorVector → ENNReal := fun vector =>
    ∑ index ∈
      (Finset.univ.filter fun index =>
        indexColor index = vector),
      weight index
  have hsingle :
      ∀ index : indexType,
        (∑ vector : ColorVector,
          if indexColor index = vector then weight index else 0) =
            weight index := by
    intro index
    rw [Finset.sum_eq_single_of_mem
      (indexColor index) (Finset.mem_univ _)]
    · rw [if_pos rfl]
    · intro vector _ hne
      rw [if_neg fun heq => hne heq.symm]
  have htotal :
      (∑ index : indexType, weight index) =
        ∑ vector : ColorVector, classWeight vector := by
    calc
      (∑ index : indexType, weight index) =
          ∑ index : indexType,
            ∑ vector : ColorVector,
              if indexColor index = vector then
                weight index else 0 := by
        apply Finset.sum_congr rfl
        intro index _
        exact (hsingle index).symm
      _ =
          ∑ vector : ColorVector,
            ∑ index : indexType,
              if indexColor index = vector then
                weight index else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ vector : ColorVector, classWeight vector := by
        apply Finset.sum_congr rfl
        intro vector _
        rw [show
          (∑ index : indexType,
            if indexColor index = vector then weight index else 0) =
          ∑ index ∈
            (Finset.univ.filter fun index =>
              indexColor index = vector),
            weight index by
              rw [Finset.sum_ite]
              simp]
  have hcolorNonempty :
      (Finset.univ : Finset ColorVector).Nonempty :=
    Finset.univ_nonempty
  rcases
      Finset.exists_max_image
        (Finset.univ : Finset ColorVector)
        classWeight hcolorNonempty with
    ⟨colorVector, _, hmax⟩
  refine ⟨colorVector, ?_⟩
  calc
    (∑ index : indexType, weight index) =
        ∑ vector : ColorVector, classWeight vector :=
      htotal
    _ ≤ ∑ _vector : ColorVector,
          classWeight colorVector := by
      apply Finset.sum_le_sum
      intro vector _
      exact hmax vector (Finset.mem_univ vector)
    _ =
        (Fintype.card ColorVector : ENNReal) *
          classWeight colorVector := by
      simp
    _ =
        (Fintype.card ColorVector : ENNReal) *
          ∑ index ∈
            (Finset.univ.filter fun index =>
              ∀ coordinate, color coordinate index =
                colorVector coordinate),
            weight index := by
      congr 1
      apply Finset.sum_congr
      · ext index
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          classWeight, indexColor]
        exact
          ⟨fun h coordinate =>
              congrFun h coordinate,
            fun h => funext h⟩
      · intro index hindex
        rfl

/--
One color-vector class together with simultaneous weighted regularization of
all parent maps on that class.
-/
structure WZ2FiniteColoredDegreeSelectionData
    {indexType : Type*}
    [Fintype indexType] [DecidableEq indexType] [LinearOrder indexType]
    (coordinateCount : ℕ)
    (Color Vertex : Fin coordinateCount → Type)
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    [∀ coordinate, Fintype (Vertex coordinate)]
    [∀ coordinate, DecidableEq (Vertex coordinate)]
    (color : ∀ coordinate, indexType → Color coordinate)
    (parent : ∀ coordinate, indexType → Vertex coordinate)
    (weight : indexType → ENNReal) where
  colorVector : ∀ coordinate, Color coordinate
  colorClass : Finset indexType
  colorClass_eq :
    colorClass =
      Finset.univ.filter fun index =>
        ∀ coordinate,
          color coordinate index = colorVector coordinate
  monochromatic :
    ∀ index ∈ colorClass,
      ∀ coordinate,
        color coordinate index = colorVector coordinate
  color_retained :
    (∑ index : indexType, weight index) ≤
      (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
        ∑ index ∈ colorClass, weight index
  regularized :
    WZ2FiniteWeightedDegreeSelectionData
      coordinateCount Vertex parent
      (fun index =>
        if index ∈ colorClass then weight index else 0)
  selected_subset_colorClass :
    regularized.selected ⊆ colorClass

/--
Perform one color-vector pigeonhole followed by one simultaneous degree
regularization.  No coordinate is processed by a nested restriction.
-/
theorem wz2_finite_colored_degree_selection
    {indexType : Type*}
    [Fintype indexType] [DecidableEq indexType] [LinearOrder indexType]
    (coordinateCount : ℕ)
    (Color Vertex : Fin coordinateCount → Type)
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    [∀ coordinate, Fintype (Vertex coordinate)]
    [∀ coordinate, DecidableEq (Vertex coordinate)]
    (color : ∀ coordinate, indexType → Color coordinate)
    (parent : ∀ coordinate, indexType → Vertex coordinate)
    (weight : indexType → ENNReal)
    (coordinateCountPos : 0 < coordinateCount) :
    Nonempty
      (WZ2FiniteColoredDegreeSelectionData
        coordinateCount Color Vertex color parent weight) := by
  rcases
      wz2_finite_dependent_color_weighted_pigeonhole
        coordinateCount Color color weight with
    ⟨colorVector, hcolorRetention⟩
  let colorClass : Finset indexType :=
    Finset.univ.filter fun index =>
      ∀ coordinate,
        color coordinate index = colorVector coordinate
  have hmono :
      ∀ index ∈ colorClass,
        ∀ coordinate,
          color coordinate index = colorVector coordinate := by
    intro index hindex
    exact (Finset.mem_filter.mp hindex).2
  have hcolorRetention' :
      (∑ index : indexType, weight index) ≤
        (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
          ∑ index ∈ colorClass, weight index := by
    simpa only [colorClass] using hcolorRetention
  let colorWeight : indexType → ENNReal :=
    fun index =>
      if index ∈ colorClass then weight index else 0
  rcases
      wz2_finite_weighted_degree_selection
        coordinateCount Vertex parent colorWeight
        coordinateCountPos with
    ⟨regularized⟩
  have hselectedSubset :
      regularized.selected ⊆ colorClass := by
    intro index hindex
    have hpositive :=
      regularized.selected_weight_pos index hindex
    dsimp only [colorWeight] at hpositive
    by_contra hnot
    rw [if_neg hnot] at hpositive
    exact (lt_self_iff_false 0).mp hpositive
  exact
    ⟨{
      colorVector := colorVector
      colorClass := colorClass
      colorClass_eq := rfl
      monochromatic := hmono
      color_retained := hcolorRetention'
      regularized := regularized
      selected_subset_colorClass := hselectedSubset
    }⟩

end Kakeya.Assouad

end
