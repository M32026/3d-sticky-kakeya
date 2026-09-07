import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PerCellColorSelection
import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization.WeightBinning

/-!
# Proposition 6.2: per-parent source color and one global leaf bin

First choose one source color independently in every parent, paying only the
number of colors in total weight.  Then apply one global dyadic pigeonhole to
all leaves retained by those parentwise choices.  The final finset lives in the
ambient leaf type rather than a subtype, so it can be restricted further or
mapped back into any ambient source set containing `wholeLeaves`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62PerParentSourceColorLeafBinData
    (Leaf Parent Color : Type*)
    [DecidableEq Leaf]
    [Fintype Parent] [DecidableEq Parent]
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    (wholeLeaves : Finset Leaf)
    (parent : Leaf → Parent)
    (sourceColor : Leaf → Color)
    (weight : Leaf → ENNReal)
    (total : ENNReal) where
  selectedColor : Parent → Color
  colorSelected : Finset Leaf
  colorSelected_eq :
    colorSelected =
      wholeLeaves.filter fun leaf =>
        sourceColor leaf = selectedColor (parent leaf)
  colorSelected_subset_wholeLeaves :
    colorSelected ⊆ wholeLeaves
  selected : Finset Leaf
  selected_nonempty : selected.Nonempty
  selected_subset_colorSelected :
    selected ⊆ colorSelected
  selected_subset_wholeLeaves :
    selected ⊆ wholeLeaves
  selected_monochromatic :
    ∀ leaf ∈ selected,
      sourceColor leaf = selectedColor (parent leaf)
  dyadicBinCount : ℕ
  dyadicBinCount_eq :
    dyadicBinCount =
      Nat.log 2 (2 * colorSelected.card) + 1
  weightLevel : ENNReal
  weightLevel_pos : 0 < weightLevel
  selected_weight_band :
    ∀ leaf ∈ selected,
      weightLevel ≤ weight leaf ∧
        weight leaf ≤ 2 * weightLevel
  sourceColor_retention :
    total ≤
      (Fintype.card Color : ENNReal) *
        ∑ leaf ∈ colorSelected, weight leaf
  leafBin_retention :
    (∑ leaf ∈ colorSelected, weight leaf) ≤
      (2 * dyadicBinCount : ENNReal) *
        ∑ leaf ∈ selected, weight leaf
  combined_retention :
    total ≤
      ((Fintype.card Color : ENNReal) *
          (2 * dyadicBinCount : ENNReal)) *
        ∑ leaf ∈ selected, weight leaf

theorem pureWZ2_prop62_perParent_sourceColor_leaf_bin
    (Leaf Parent Color : Type*)
    [DecidableEq Leaf]
    [Fintype Parent] [DecidableEq Parent]
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    (wholeLeaves : Finset Leaf)
    (wholeLeaves_nonempty : wholeLeaves.Nonempty)
    (parent : Leaf → Parent)
    (sourceColor : Leaf → Color)
    (weight : Leaf → ENNReal)
    (total : ENNReal)
    (total_eq :
      total = ∑ leaf ∈ wholeLeaves, weight leaf)
    (total_finite : total ≠ ⊤)
    (total_pos : 0 < total) :
    Nonempty
      (PureWZ2Prop62PerParentSourceColorLeafBinData
        Leaf Parent Color wholeLeaves parent sourceColor weight total) := by
  let WholeLeaf := {leaf : Leaf // leaf ∈ wholeLeaves}
  rcases wholeLeaves_nonempty with ⟨someLeaf, someLeafMem⟩
  letI : Nonempty WholeLeaf := ⟨⟨someLeaf, someLeafMem⟩⟩
  let wholeParent : WholeLeaf → Parent :=
    fun leaf => parent leaf.1
  let wholeSourceColor : WholeLeaf → Color :=
    fun leaf => sourceColor leaf.1
  let wholeWeight : WholeLeaf → ENNReal :=
    fun leaf => weight leaf.1
  let perParent :
      PureWZ2Prop62PerCellColorSelectionData
        WholeLeaf Parent Color wholeParent wholeSourceColor wholeWeight :=
    Classical.choice <|
      pureWZ2_prop62_perCell_color_selection
        WholeLeaf Parent Color wholeParent wholeSourceColor wholeWeight
  let colorSelected : Finset Leaf :=
    perParent.selected.image fun leaf => leaf.1
  have colorSelectedSubset :
      colorSelected ⊆ wholeLeaves := by
    intro leaf leafMem
    rcases Finset.mem_image.mp leafMem with
      ⟨wholeLeaf, _wholeLeafMem, rfl⟩
    exact wholeLeaf.2
  have colorSelectedEq :
      colorSelected =
        wholeLeaves.filter fun leaf =>
          sourceColor leaf =
            perParent.selectedColor (parent leaf) := by
    ext leaf
    constructor
    · intro leafMem
      rcases Finset.mem_image.mp leafMem with
        ⟨wholeLeaf, wholeLeafMem, rfl⟩
      exact
        Finset.mem_filter.mpr
          ⟨wholeLeaf.2, by
            simpa [wholeParent, wholeSourceColor] using
              perParent.selected_monochromatic
                wholeLeaf wholeLeafMem⟩
    · intro leafMem
      have wholeMem := (Finset.mem_filter.mp leafMem).1
      have colorEq := (Finset.mem_filter.mp leafMem).2
      let wholeLeaf : WholeLeaf := ⟨leaf, wholeMem⟩
      apply Finset.mem_image.mpr
      refine ⟨wholeLeaf, ?_, rfl⟩
      rw [perParent.selected_eq]
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ wholeLeaf, by
            simpa [wholeLeaf, wholeParent, wholeSourceColor] using
              colorEq⟩
  have wholeSubtypeSum :
      (∑ leaf : WholeLeaf, wholeWeight leaf) =
        ∑ leaf ∈ wholeLeaves, weight leaf := by
    exact Finset.sum_coe_sort wholeLeaves weight
  have colorSelectedSum :
      (∑ leaf ∈ colorSelected, weight leaf) =
        ∑ leaf ∈ perParent.selected, wholeWeight leaf := by
    exact
      Finset.sum_image
        (fun first _ second _ equality => Subtype.ext equality)
  have sourceColorRetention :
      total ≤
        (Fintype.card Color : ENNReal) *
          ∑ leaf ∈ colorSelected, weight leaf := by
    calc
      total = ∑ leaf : WholeLeaf, wholeWeight leaf := by
        rw [wholeSubtypeSum]
        exact total_eq
      _ ≤
          (Fintype.card Color : ENNReal) *
            ∑ leaf ∈ perParent.selected, wholeWeight leaf :=
        perParent.weight_retention
      _ =
          (Fintype.card Color : ENNReal) *
            ∑ leaf ∈ colorSelected, weight leaf := by
        rw [colorSelectedSum]
  let colorTotal : ENNReal :=
    ∑ leaf ∈ colorSelected, weight leaf
  have colorTotal_le : colorTotal ≤ total := by
    calc
      colorTotal ≤ ∑ leaf ∈ wholeLeaves, weight leaf := by
        exact Finset.sum_le_sum_of_subset colorSelectedSubset
      _ = total := total_eq.symm
  have colorTotal_finite : colorTotal ≠ ⊤ :=
    ne_top_of_le_ne_top total_finite colorTotal_le
  have colorTotal_pos : 0 < colorTotal := by
    by_contra colorTotalNotPos
    have colorTotalZero : colorTotal = 0 := by
      simpa [not_lt] using colorTotalNotPos
    have totalLeZero : total ≤ 0 := by
      simpa [colorTotal, colorTotalZero] using sourceColorRetention
    exact (not_le_of_gt total_pos) totalLeZero
  let ColorSelectedLeaf := {leaf : Leaf // leaf ∈ colorSelected}
  let colorSelectedWeight : ColorSelectedLeaf → ENNReal :=
    fun leaf => weight leaf.1
  have colorSelectedSubtypeSum :
      (∑ leaf : ColorSelectedLeaf, colorSelectedWeight leaf) =
        colorTotal := by
    exact Finset.sum_coe_sort colorSelected weight
  rcases
      ennreal_dyadic_bin
        colorSelectedWeight colorTotal colorSelectedSubtypeSum.symm
        colorTotal_finite colorTotal_pos
    with
    ⟨dyadicBinCount, selectedSubtype,
      dyadicBinCountEq, selectedSubtypeNonempty,
      selectedSubtypeRetention, _selectedFloor,
      weightLevel, weightLevelPos, selectedSubtypeBand⟩
  let selected : Finset Leaf :=
    selectedSubtype.image fun leaf => leaf.1
  have selectedNonempty : selected.Nonempty := by
    rcases selectedSubtypeNonempty with ⟨leaf, leafMem⟩
    exact
      ⟨leaf.1,
        Finset.mem_image.mpr ⟨leaf, leafMem, rfl⟩⟩
  have selectedSubsetColorSelected :
      selected ⊆ colorSelected := by
    intro leaf leafMem
    rcases Finset.mem_image.mp leafMem with
      ⟨selectedLeaf, _selectedLeafMem, rfl⟩
    exact selectedLeaf.2
  have selectedSum :
      (∑ leaf ∈ selected, weight leaf) =
        ∑ leaf ∈ selectedSubtype, colorSelectedWeight leaf := by
    exact
      Finset.sum_image
        (fun first _ second _ equality => Subtype.ext equality)
  have selectedBand :
      ∀ leaf ∈ selected,
        weightLevel ≤ weight leaf ∧
          weight leaf ≤ 2 * weightLevel := by
    intro leaf leafMem
    rcases Finset.mem_image.mp leafMem with
      ⟨selectedLeaf, selectedLeafMem, rfl⟩
    exact selectedSubtypeBand selectedLeaf selectedLeafMem
  have leafBinRetention :
      colorTotal ≤
        (2 * dyadicBinCount : ENNReal) *
          ∑ leaf ∈ selected, weight leaf := by
    calc
      colorTotal =
          colorTotal / 2 + colorTotal / 2 :=
        (ENNReal.add_halves colorTotal).symm
      _ ≤
          (∑ leaf ∈ selectedSubtype, colorSelectedWeight leaf) *
              (dyadicBinCount : ENNReal) +
            (∑ leaf ∈ selectedSubtype, colorSelectedWeight leaf) *
              (dyadicBinCount : ENNReal) := by
        gcongr
      _ =
          (2 * dyadicBinCount : ENNReal) *
            ∑ leaf ∈ selectedSubtype, colorSelectedWeight leaf := by
        ring
      _ =
          (2 * dyadicBinCount : ENNReal) *
            ∑ leaf ∈ selected, weight leaf := by
        rw [selectedSum]
  have combinedRetention :
      total ≤
        ((Fintype.card Color : ENNReal) *
            (2 * dyadicBinCount : ENNReal)) *
          ∑ leaf ∈ selected, weight leaf := by
    calc
      total ≤
          (Fintype.card Color : ENNReal) * colorTotal := by
        simpa only [colorTotal] using sourceColorRetention
      _ ≤
          (Fintype.card Color : ENNReal) *
            ((2 * dyadicBinCount : ENNReal) *
              ∑ leaf ∈ selected, weight leaf) := by
        exact
          mul_le_mul_right leafBinRetention
            (Fintype.card Color : ENNReal)
      _ =
          ((Fintype.card Color : ENNReal) *
              (2 * dyadicBinCount : ENNReal)) *
            ∑ leaf ∈ selected, weight leaf := by
        ring
  exact
    ⟨{
      selectedColor := perParent.selectedColor
      colorSelected := colorSelected
      colorSelected_eq := colorSelectedEq
      colorSelected_subset_wholeLeaves := colorSelectedSubset
      selected := selected
      selected_nonempty := selectedNonempty
      selected_subset_colorSelected := selectedSubsetColorSelected
      selected_subset_wholeLeaves :=
        selectedSubsetColorSelected.trans colorSelectedSubset
      selected_monochromatic := by
        intro leaf leafMem
        have colorSelectedMem :=
          selectedSubsetColorSelected leafMem
        rw [colorSelectedEq] at colorSelectedMem
        exact (Finset.mem_filter.mp colorSelectedMem).2
      dyadicBinCount := dyadicBinCount
      dyadicBinCount_eq := by
        simpa [ColorSelectedLeaf, Fintype.card_coe] using
          dyadicBinCountEq
      weightLevel := weightLevel
      weightLevel_pos := weightLevelPos
      selected_weight_band := selectedBand
      sourceColor_retention := sourceColorRetention
      leafBin_retention := by
        simpa only [colorTotal] using leafBinRetention
      combined_retention := combinedRetention
    }⟩

namespace PureWZ2Prop62PerParentSourceColorLeafBinData

theorem selected_subset_ambient
    {Leaf Parent Color : Type*}
    [DecidableEq Leaf]
    [Fintype Parent] [DecidableEq Parent]
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    {wholeLeaves ambient : Finset Leaf}
    {parent : Leaf → Parent}
    {sourceColor : Leaf → Color}
    {weight : Leaf → ENNReal}
    {total : ENNReal}
    (selection :
      PureWZ2Prop62PerParentSourceColorLeafBinData
        Leaf Parent Color wholeLeaves parent sourceColor weight total)
    (wholeLeaves_subset_ambient : wholeLeaves ⊆ ambient) :
    selection.selected ⊆ ambient :=
  selection.selected_subset_wholeLeaves.trans
    wholeLeaves_subset_ambient

end PureWZ2Prop62PerParentSourceColorLeafBinData

end Kakeya.Assouad

end
