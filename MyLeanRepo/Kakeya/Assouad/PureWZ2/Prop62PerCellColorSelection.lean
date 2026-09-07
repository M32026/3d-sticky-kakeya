import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.FiniteColoredDegreeSelection

/-!
# Proposition 6.2: one color independently in every metric cell

The metric-parent proof does not choose one global ancestry color.  It chooses
one ancestry class separately inside every occupied line-parameter cell.  A
finite color set still costs only its cardinality: take a maximum-weight color
in each cell and then sum the cellwise inequalities.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62PerCellColorSelectionData
    (Index Cell Color : Type*)
    [Fintype Index] [DecidableEq Index]
    [Fintype Cell] [DecidableEq Cell]
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    (cell : Index → Cell)
    (color : Index → Color)
    (weight : Index → ENNReal) where
  selectedColor : Cell → Color
  selected : Finset Index
  selected_eq :
    selected =
      Finset.univ.filter fun index =>
        color index = selectedColor (cell index)
  selected_monochromatic :
    ∀ index ∈ selected,
      color index = selectedColor (cell index)
  weight_retention :
    (∑ index : Index, weight index) ≤
      (Fintype.card Color : ENNReal) *
        ∑ index ∈ selected, weight index

theorem pureWZ2_prop62_perCell_color_selection
    (Index Cell Color : Type*)
    [Fintype Index] [DecidableEq Index]
    [Fintype Cell] [DecidableEq Cell]
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    (cell : Index → Cell)
    (color : Index → Color)
    (weight : Index → ENNReal) :
    Nonempty
      (PureWZ2Prop62PerCellColorSelectionData
        Index Cell Color cell color weight) := by
  let classWeight : Cell → Color → ENNReal :=
    fun currentCell currentColor =>
      ∑ index ∈
        (Finset.univ.filter fun index =>
          cell index = currentCell ∧ color index = currentColor),
        weight index
  let selectedColor : Cell → Color :=
    fun currentCell =>
      Classical.choose <|
        Finset.exists_max_image
          (Finset.univ : Finset Color)
          (classWeight currentCell)
          Finset.univ_nonempty
  have selectedColorMax :
      ∀ currentCell currentColor,
        classWeight currentCell currentColor ≤
          classWeight currentCell (selectedColor currentCell) := by
    intro currentCell currentColor
    exact
      (Classical.choose_spec
        (Finset.exists_max_image
          (Finset.univ : Finset Color)
          (classWeight currentCell)
          Finset.univ_nonempty)).2
        currentColor (Finset.mem_univ currentColor)
  let selected : Finset Index :=
    Finset.univ.filter fun index =>
      color index = selectedColor (cell index)
  have splitCell :
      ∀ currentCell,
        (∑ currentColor : Color,
            classWeight currentCell currentColor) =
          ∑ index ∈
            (Finset.univ.filter fun index =>
              cell index = currentCell),
            weight index := by
    intro currentCell
    calc
      (∑ currentColor : Color,
          classWeight currentCell currentColor) =
          ∑ currentColor : Color,
            ∑ index ∈
              (Finset.univ.filter fun index =>
                cell index = currentCell) with
                color index = currentColor,
              weight index := by
        apply Finset.sum_congr rfl
        intro currentColor _
        apply Finset.sum_congr
        · ext index
          simp only [classWeight, Finset.mem_filter,
            Finset.mem_univ, true_and]
        · intro index _
          rfl
      _ =
          ∑ index ∈
            (Finset.univ.filter fun index =>
              cell index = currentCell),
            weight index :=
        Finset.sum_fiberwise
          (Finset.univ.filter fun index =>
            cell index = currentCell)
          color weight
  have cellBound :
      ∀ currentCell,
        (∑ currentColor : Color,
            classWeight currentCell currentColor) ≤
          (Fintype.card Color : ENNReal) *
            classWeight currentCell (selectedColor currentCell) := by
    intro currentCell
    calc
      (∑ currentColor : Color,
          classWeight currentCell currentColor) ≤
          ∑ _currentColor : Color,
            classWeight currentCell (selectedColor currentCell) := by
        apply Finset.sum_le_sum
        intro currentColor _
        exact selectedColorMax currentCell currentColor
      _ =
          (Fintype.card Color : ENNReal) *
            classWeight currentCell (selectedColor currentCell) := by
        simp
  have totalByCell :
      (∑ currentCell : Cell,
          ∑ index ∈
            (Finset.univ.filter fun index =>
              cell index = currentCell),
            weight index) =
        ∑ index : Index, weight index :=
    Finset.sum_fiberwise Finset.univ cell weight
  have selectedByCell :
      (∑ currentCell : Cell,
          classWeight currentCell (selectedColor currentCell)) =
        ∑ index ∈ selected, weight index := by
    calc
      (∑ currentCell : Cell,
          classWeight currentCell (selectedColor currentCell)) =
          ∑ currentCell : Cell,
            ∑ index ∈ selected with
              cell index = currentCell,
              weight index := by
        apply Finset.sum_congr rfl
        intro currentCell _
        apply Finset.sum_congr
        · ext index
          simp only [classWeight, selected, Finset.mem_filter,
            Finset.mem_univ, true_and]
          constructor
          · rintro ⟨cellEq, colorEq⟩
            exact ⟨by simpa [cellEq] using colorEq, cellEq⟩
          · rintro ⟨colorEq, cellEq⟩
            exact
              ⟨cellEq, by
                rw [cellEq] at colorEq
                exact colorEq⟩
        · intro index _
          rfl
      _ = ∑ index ∈ selected, weight index :=
        Finset.sum_fiberwise selected cell weight
  have retention :
      (∑ index : Index, weight index) ≤
        (Fintype.card Color : ENNReal) *
          ∑ index ∈ selected, weight index := by
    calc
      (∑ index : Index, weight index) =
          ∑ currentCell : Cell,
            ∑ currentColor : Color,
              classWeight currentCell currentColor := by
        rw [← totalByCell]
        apply Finset.sum_congr rfl
        intro currentCell _
        exact (splitCell currentCell).symm
      _ ≤
          ∑ currentCell : Cell,
            (Fintype.card Color : ENNReal) *
              classWeight currentCell (selectedColor currentCell) := by
        apply Finset.sum_le_sum
        intro currentCell _
        exact cellBound currentCell
      _ =
          (Fintype.card Color : ENNReal) *
            ∑ currentCell : Cell,
              classWeight currentCell (selectedColor currentCell) := by
        rw [Finset.mul_sum]
      _ =
          (Fintype.card Color : ENNReal) *
            ∑ index ∈ selected, weight index := by
        rw [selectedByCell]
  exact
    ⟨{
      selectedColor := selectedColor
      selected := selected
      selected_eq := rfl
      selected_monochromatic := by
        intro index indexMem
        exact (Finset.mem_filter.mp indexMem).2
      weight_retention := retention
    }⟩

end Kakeya.Assouad

end
