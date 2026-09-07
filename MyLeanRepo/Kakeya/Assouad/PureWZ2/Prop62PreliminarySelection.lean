import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AuxiliaryPureSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.FiniteColoredDegreeSelection
import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization.WeightBinning

/-!
# Proposition 6.2 metric parents: one preliminary selection

All finite structural choices in the metric-parent lemma are encoded in one
dependent color vector.  One weighted color pigeonhole is followed by one
global dyadic leaf-weight pigeonhole.  No sequential restriction by scale is
performed.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62PreliminarySelectionData
    {Index : Type*}
    [Fintype Index] [DecidableEq Index]
    (coordinateCount : ℕ)
    (Color : Fin coordinateCount → Type*)
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    (color : ∀ coordinate, Index → Color coordinate)
    (weight : Index → ENNReal) where
  colorVector : ∀ coordinate, Color coordinate
  colorClass : Finset Index
  colorClass_eq :
    colorClass =
      Finset.univ.filter fun index =>
        ∀ coordinate,
          color coordinate index = colorVector coordinate
  selected : Finset Index
  selected_nonempty : selected.Nonempty
  selected_subset_colorClass : selected ⊆ colorClass
  selected_monochromatic :
    ∀ index ∈ selected,
      ∀ coordinate,
        color coordinate index = colorVector coordinate
  dyadicBinCount : ℕ
  dyadicBinCount_eq :
    dyadicBinCount =
      Nat.log 2 (2 * colorClass.card) + 1
  weightLevel : ENNReal
  weightLevel_pos : 0 < weightLevel
  selected_weight_band :
    ∀ index ∈ selected,
      weightLevel ≤ weight index ∧
        weight index ≤ 2 * weightLevel
  color_retention :
    (∑ index : Index, weight index) ≤
      (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
        ∑ index ∈ colorClass, weight index
  dyadic_retention :
    (∑ index ∈ colorClass, weight index) ≤
      (2 * dyadicBinCount : ENNReal) *
        ∑ index ∈ selected, weight index

theorem pureWZ2_prop62_preliminary_selection
    {Index : Type*}
    [Fintype Index] [DecidableEq Index]
    (coordinateCount : ℕ)
    (Color : Fin coordinateCount → Type*)
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    (color : ∀ coordinate, Index → Color coordinate)
    (weight : Index → ENNReal)
    (total_finite : (∑ index : Index, weight index) ≠ ⊤)
    (total_pos : 0 < ∑ index : Index, weight index) :
    Nonempty
      (PureWZ2Prop62PreliminarySelectionData
        coordinateCount Color color weight) := by
  rcases
      wz2_finite_dependent_color_weighted_pigeonhole
        coordinateCount Color color weight
    with ⟨colorVector, colorRetention⟩
  let colorClass : Finset Index :=
    Finset.univ.filter fun index =>
      ∀ coordinate,
        color coordinate index = colorVector coordinate
  let classTotal : ENNReal :=
    ∑ index ∈ colorClass, weight index
  have classTotal_le :
      classTotal ≤ ∑ index : Index, weight index := by
    change
      (∑ index ∈ colorClass, weight index) ≤
        ∑ index ∈ (Finset.univ : Finset Index), weight index
    exact Finset.sum_le_sum_of_subset
      (Finset.subset_univ colorClass)
  have classTotal_finite : classTotal ≠ ⊤ := by
    exact ne_top_of_le_ne_top total_finite classTotal_le
  have colorCard_pos :
      0 <
        Fintype.card (∀ coordinate, Color coordinate) := by
    exact Fintype.card_pos_iff.mpr inferInstance
  have colorCard_nonzero :
      (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) ≠ 0 := by
    exact_mod_cast colorCard_pos.ne'
  have classTotal_pos : 0 < classTotal := by
    by_contra hclass
    have classZero : classTotal = 0 := by
      simpa [not_lt] using hclass
    have totalZero :
        (∑ index : Index, weight index) ≤ 0 := by
      have hbound :
        (∑ index : Index, weight index) ≤
          (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
            classTotal := by
        simpa only [colorClass, classTotal] using colorRetention
      simpa [classZero] using hbound
    exact (not_le_of_gt total_pos) totalZero
  let ClassIndex := {index : Index // index ∈ colorClass}
  let classWeight : ClassIndex → ENNReal :=
    fun index => weight index.1
  have classSum :
      (∑ index : ClassIndex, classWeight index) = classTotal := by
    exact Finset.sum_coe_sort colorClass weight
  have classWeightTotal :
      classTotal = ∑ index : ClassIndex, classWeight index :=
    classSum.symm
  rcases
      ennreal_dyadic_bin
        classWeight classTotal classWeightTotal
        classTotal_finite classTotal_pos
    with
    ⟨dyadicBinCount, selectedClass,
      dyadicBinCountEq, selectedClassNonempty,
      selectedClassRetention, _selectedFloor,
      weightLevel, weightLevelPos, selectedClassBand⟩
  let selected : Finset Index :=
    selectedClass.image fun index => index.1
  have selectedNonempty : selected.Nonempty := by
    rcases selectedClassNonempty with ⟨index, hindex⟩
    exact
      ⟨index.1,
        Finset.mem_image.mpr ⟨index, hindex, rfl⟩⟩
  have selectedSubset : selected ⊆ colorClass := by
    intro index hindex
    rcases Finset.mem_image.mp hindex with
      ⟨classIndex, _hclassIndex, rfl⟩
    exact classIndex.2
  have selectedSum :
      (∑ index ∈ selected, weight index) =
        ∑ index ∈ selectedClass, classWeight index := by
    exact
      Finset.sum_image
        (fun first _ second _ heq => Subtype.ext heq)
  have selectedBand :
      ∀ index ∈ selected,
        weightLevel ≤ weight index ∧
          weight index ≤ 2 * weightLevel := by
    intro index hindex
    rcases Finset.mem_image.mp hindex with
      ⟨classIndex, hclassIndex, rfl⟩
    exact selectedClassBand classIndex hclassIndex
  have dyadicRetention :
      classTotal ≤
        (2 * dyadicBinCount : ENNReal) *
          ∑ index ∈ selected, weight index := by
    calc
      classTotal =
          classTotal / 2 + classTotal / 2 :=
        (ENNReal.add_halves classTotal).symm
      _ ≤
          (∑ index ∈ selectedClass, classWeight index) *
              (dyadicBinCount : ENNReal) +
            (∑ index ∈ selectedClass, classWeight index) *
              (dyadicBinCount : ENNReal) := by
        gcongr
      _ =
          (2 * dyadicBinCount : ENNReal) *
            ∑ index ∈ selectedClass, classWeight index := by
        ring
      _ =
          (2 * dyadicBinCount : ENNReal) *
            ∑ index ∈ selected, weight index := by
        rw [selectedSum]
  exact
    ⟨{
      colorVector := colorVector
      colorClass := colorClass
      colorClass_eq := rfl
      selected := selected
      selected_nonempty := selectedNonempty
      selected_subset_colorClass := selectedSubset
      selected_monochromatic := by
        intro index hindex coordinate
        have hcolorClass := selectedSubset hindex
        exact
          (Finset.mem_filter.mp hcolorClass).2 coordinate
      dyadicBinCount := dyadicBinCount
      dyadicBinCount_eq := by
        simpa [ClassIndex, Fintype.card_coe] using
          dyadicBinCountEq
      weightLevel := weightLevel
      weightLevel_pos := weightLevelPos
      selected_weight_band := selectedBand
      color_retention := by
        simpa only [colorClass] using colorRetention
      dyadic_retention := dyadicRetention
    }⟩

end Kakeya.Assouad

end
