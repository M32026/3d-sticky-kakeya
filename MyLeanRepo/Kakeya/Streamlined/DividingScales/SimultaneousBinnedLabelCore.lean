import MyLeanRepo.Kakeya.Streamlined.SimultaneousDegreeRegularization.ParentComponentCore
import MyLeanRepo.Kakeya.Streamlined.ProfileUniformRefinement.ThreeProfileWholeFiberSelection

/-!
# A simultaneous core for arbitrary finite binned label coordinates

The profile repair and conditional joint-cell regularization must be performed
in one selection: running either one afterward can cut the fibers controlled
by the other.

This module exposes the reusable finite core needed for that combined
selection.  An arbitrary finite coordinate type is reindexed by `Fin m` and
fed to the proved parent/component core with a dummy one-point component
coordinate.  The harmless square in the color count remains
subpolynomial for fixed coordinate depth.
-/

noncomputable section

open scoped Classical

namespace Kakeya.Streamlined

universe uItem uCoordinate uLabel

/-- Cardinality of one label fiber inside a finite vertex set. -/
def finiteSetFiberCount
    {Item Label : Type*}
    [DecidableEq Item] [DecidableEq Label]
    (vertices : Finset Item)
    (label : Item → Label)
    (value : Label) : ℕ :=
  (vertices.filter fun item => label item = value).card

/-- Two values in the same dyadic profile bin are comparable by `2`. -/
lemma inDyadicProfileBin_comparable_of_eq
    {B : ℕ} {firstBin secondBin : Fin B} {first second : ENNReal}
    (hfirst : InDyadicProfileBin firstBin first)
    (hsecond : InDyadicProfileBin secondBin second)
    (hbin : firstBin = secondBin) :
    ComparableBy 2 first second := by
  subst secondBin
  exact
    ⟨by norm_num,
      hfirst.2.trans (mul_le_mul_left' hsecond.1 2),
      hsecond.2.trans (mul_le_mul_left' hfirst.1 2)⟩

/-- Output of one common binned-label selection and label-dependent core. -/
structure SimultaneousBinnedLabelCorePackage
    (Item : Type uItem)
    (Coordinate : Type uCoordinate)
    [Fintype Item] [DecidableEq Item]
    [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    (Label : Coordinate → Type uLabel)
    [∀ coordinate, Fintype (Label coordinate)]
    [∀ coordinate, DecidableEq (Label coordinate)]
    (label : ∀ coordinate, Item → Label coordinate)
    (B : ℕ)
    (bin : ∀ coordinate, Label coordinate → Fin B)
    (vertices : Finset Item)
    (weight : Item → ENNReal) where
  selected : Finset Item
  selectedNonempty : selected.Nonempty
  selectedSubset : selected ⊆ vertices
  weightRetention :
    (∑ item ∈ vertices, weight item) ≤
      (8 * parentComponentColorCount
        (Fintype.card Coordinate) B : ℕ) *
        ∑ item ∈ selected, weight item
  binCommon :
    ∀ coordinate,
    ∀ first ∈ selected,
    ∀ second ∈ selected,
      bin coordinate (label coordinate first) =
        bin coordinate (label coordinate second)
  fiberRetention :
    ∀ coordinate,
    ∀ value : Label coordinate,
      0 < (selected.filter
        (fun item => label coordinate item = value)).card →
        (vertices.filter
          (fun item => label coordinate item = value)).card ≤
          parentComponentCoreDenominator
              (Fintype.card Coordinate) B *
            ((selected.filter
              (fun item => label coordinate item = value)).card + 1)

/--
Choose one common vector of dyadic label bins and prune to a core for every
finite label coordinate.
-/
theorem simultaneous_binned_label_core
    (Item : Type uItem)
    (Coordinate : Type uCoordinate)
    [Fintype Item] [DecidableEq Item]
    [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    (Label : Coordinate → Type uLabel)
    [∀ coordinate, Fintype (Label coordinate)]
    [∀ coordinate, DecidableEq (Label coordinate)]
    (label : ∀ coordinate, Item → Label coordinate)
    (B : ℕ) (hB : 0 < B)
    (bin : ∀ coordinate, Label coordinate → Fin B)
    (vertices : Finset Item) (hvertices : vertices.Nonempty)
    (weight : Item → ENNReal)
    (c : ENNReal) (hc : 0 < c)
    (hweight :
      ∀ item ∈ vertices,
        c ≤ weight item ∧ weight item ≤ 2 * c) :
    Nonempty
      (SimultaneousBinnedLabelCorePackage
        Item Coordinate Label label B bin vertices weight) := by
  classical
  let coordinateCount := Fintype.card Coordinate
  have hcoordinateCount : 0 < coordinateCount := by
    exact Fintype.card_pos
  let coordinateEquiv : Coordinate ≃ Fin coordinateCount :=
    Fintype.equivFin Coordinate
  let FinLabel : Fin coordinateCount → Type uLabel :=
    fun index => Label (coordinateEquiv.symm index)
  let finLabel :
      ∀ index : Fin coordinateCount, Item → FinLabel index :=
    fun index => label (coordinateEquiv.symm index)
  let finBin :
      ∀ index : Fin coordinateCount, FinLabel index → Fin B :=
    fun index => bin (coordinateEquiv.symm index)
  let Dummy : Fin coordinateCount → Type uLabel := FinLabel
  let dummyLabel :
      ∀ index : Fin coordinateCount, Item → Dummy index :=
    finLabel
  let zeroBin : Fin B := ⟨0, hB⟩
  let dummyBin :
      ∀ index : Fin coordinateCount, Dummy index → Fin B :=
    fun _ _ => zeroBin
  rcases
      simultaneous_parent_component_core
        coordinateCount hcoordinateCount
        FinLabel Dummy finLabel dummyLabel
        B hB finBin dummyBin
        vertices hvertices weight c hc hweight with
    ⟨selected, hselected, hsubset, hmass,
      hbin, _hdummyBin, hfiber, _hdummyFiber⟩
  refine
    ⟨{
      selected := selected
      selectedNonempty := hselected
      selectedSubset := hsubset
      weightRetention := ?_
      binCommon := ?_
      fiberRetention := ?_
    }⟩
  · simpa [coordinateCount] using hmass
  · intro coordinate first hfirst second hsecond
    let index := coordinateEquiv coordinate
    have hcoordinate :
        coordinateEquiv.symm index = coordinate :=
      coordinateEquiv.symm_apply_apply coordinate
    have hmain := hbin index first hfirst second hsecond
    dsimp only [finBin, finLabel, FinLabel] at hmain
    change
      bin (coordinateEquiv.symm index)
          (label (coordinateEquiv.symm index) first) =
        bin (coordinateEquiv.symm index)
          (label (coordinateEquiv.symm index) second) at hmain
    rw [hcoordinate] at hmain
    exact hmain
  · intro coordinate value hactive
    let index := coordinateEquiv coordinate
    have hcoordinate :
        coordinateEquiv.symm index = coordinate :=
      coordinateEquiv.symm_apply_apply coordinate
    let value' : FinLabel index :=
      cast (congrArg Label hcoordinate).symm value
    have hselectedFiber :
        selected.filter
            (fun item => finLabel index item = value') =
          selected.filter
            (fun item => label coordinate item = value) := by
      apply Finset.filter_congr
      intro item _
      dsimp only [finLabel, FinLabel, value']
      induction hcoordinate
      rfl
    have hverticesFiber :
        vertices.filter
            (fun item => finLabel index item = value') =
          vertices.filter
            (fun item => label coordinate item = value) := by
      apply Finset.filter_congr
      intro item _
      dsimp only [finLabel, FinLabel, value']
      induction hcoordinate
      rfl
    have hactive' :
        0 < (selected.filter
          (fun item => finLabel index item = value')).card := by
      rw [hselectedFiber]
      exact hactive
    have hmain := hfiber index value' hactive'
    rw [hselectedFiber, hverticesFiber] at hmain
    simpa [coordinateCount] using hmain

namespace SimultaneousBinnedLabelCorePackage

variable
    {Item : Type uItem}
    {Coordinate : Type uCoordinate}
    [Fintype Item] [DecidableEq Item]
    [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    {Label : Coordinate → Type uLabel}
    [∀ coordinate, Fintype (Label coordinate)]
    [∀ coordinate, DecidableEq (Label coordinate)]
    {label : ∀ coordinate, Item → Label coordinate}
    {B : ℕ}
    {bin : ∀ coordinate, Label coordinate → Fin B}
    {vertices : Finset Item}
    {weight : Item → ENNReal}

/--
The selected fiber over every active label is comparable to its original
fiber up to twice the common core denominator.
-/
lemma originalFiber_le_two_mul_denominator_mul_selectedFiber
    (package :
      SimultaneousBinnedLabelCorePackage
        Item Coordinate Label label B bin vertices weight)
    (coordinate : Coordinate)
    (value : Label coordinate)
    (hactive :
      0 < (package.selected.filter
        (fun item => label coordinate item = value)).card) :
    finiteSetFiberCount vertices (label coordinate) value ≤
      2 * parentComponentCoreDenominator
          (Fintype.card Coordinate) B *
        (package.selected.filter
          (fun item => label coordinate item = value)).card := by
  have hretention :=
    package.fiberRetention coordinate value hactive
  have hselectedPositive :
      1 ≤ (package.selected.filter
        (fun item => label coordinate item = value)).card := by
    omega
  calc
    finiteSetFiberCount vertices (label coordinate) value
        ≤ parentComponentCoreDenominator
            (Fintype.card Coordinate) B *
          ((package.selected.filter
            (fun item => label coordinate item = value)).card + 1) :=
      hretention
    _ ≤ parentComponentCoreDenominator
          (Fintype.card Coordinate) B *
        (2 * (package.selected.filter
          (fun item => label coordinate item = value)).card) := by
      gcongr
      omega
    _ = 2 * parentComponentCoreDenominator
          (Fintype.card Coordinate) B *
        (package.selected.filter
          (fun item => label coordinate item = value)).card := by
      ring

/--
If the original fiber sizes lie in their supplied dyadic bins, then all
nonempty selected fibers at one coordinate are pairwise comparable.

This is the generic conditional-cell consequence of the common core.
-/
lemma selectedFibersComparable
    (package :
      SimultaneousBinnedLabelCorePackage
        Item Coordinate Label label B bin vertices weight)
    (coordinate : Coordinate)
    (hbin :
      ∀ value : Label coordinate,
        0 < finiteSetFiberCount vertices (label coordinate) value →
          InDyadicProfileBin
            (bin coordinate value)
            (finiteSetFiberCount vertices
              (label coordinate) value : ENNReal))
    (first second : Label coordinate)
    (hfirst :
      0 < (package.selected.filter
        (fun item => label coordinate item = first)).card)
    (hsecond :
      0 < (package.selected.filter
        (fun item => label coordinate item = second)).card) :
    ComparableBy
      ((4 * parentComponentCoreDenominator
        (Fintype.card Coordinate) B : ℕ) : ENNReal)
      ((package.selected.filter
        (fun item => label coordinate item = first)).card : ENNReal)
      ((package.selected.filter
        (fun item => label coordinate item = second)).card : ENNReal) := by
  have hfirstOriginalPositive :
      0 < finiteSetFiberCount vertices
        (label coordinate) first := by
    have hsubset :
        package.selected.filter
            (fun item => label coordinate item = first) ⊆
          vertices.filter
            (fun item => label coordinate item = first) := by
      intro item hitem
      exact Finset.mem_filter.mpr
        ⟨package.selectedSubset (Finset.mem_filter.mp hitem).1,
          (Finset.mem_filter.mp hitem).2⟩
    have hcard :=
      Finset.card_le_card hsubset
    simpa [finiteSetFiberCount] using
      lt_of_lt_of_le hfirst hcard
  have hsecondOriginalPositive :
      0 < finiteSetFiberCount vertices
        (label coordinate) second := by
    have hsubset :
        package.selected.filter
            (fun item => label coordinate item = second) ⊆
          vertices.filter
            (fun item => label coordinate item = second) := by
      intro item hitem
      exact Finset.mem_filter.mpr
        ⟨package.selectedSubset (Finset.mem_filter.mp hitem).1,
          (Finset.mem_filter.mp hitem).2⟩
    have hcard :=
      Finset.card_le_card hsubset
    simpa [finiteSetFiberCount] using
      lt_of_lt_of_le hsecond hcard
  have hbins :
      bin coordinate first = bin coordinate second := by
    rcases Finset.card_pos.mp hfirst with ⟨firstItem, hfirstItem⟩
    rcases Finset.card_pos.mp hsecond with ⟨secondItem, hsecondItem⟩
    have hcommon := package.binCommon coordinate
      firstItem (Finset.mem_filter.mp hfirstItem).1
      secondItem (Finset.mem_filter.mp hsecondItem).1
    rw [(Finset.mem_filter.mp hfirstItem).2,
      (Finset.mem_filter.mp hsecondItem).2] at hcommon
    exact hcommon
  have hfirstCertificate :=
    hbin first hfirstOriginalPositive
  have hsecondCertificate :=
    hbin second hsecondOriginalPositive
  have horiginalComparable :
      ComparableBy 2
        (finiteSetFiberCount vertices
          (label coordinate) first : ENNReal)
        (finiteSetFiberCount vertices
          (label coordinate) second : ENNReal) := by
    exact inDyadicProfileBin_comparable_of_eq
      hfirstCertificate hsecondCertificate hbins
  have hfirstSubset :
      (package.selected.filter
        (fun item => label coordinate item = first)).card ≤
        finiteSetFiberCount vertices
          (label coordinate) first := by
    apply Finset.card_le_card
    intro item hitem
    exact Finset.mem_filter.mpr
      ⟨package.selectedSubset (Finset.mem_filter.mp hitem).1,
        (Finset.mem_filter.mp hitem).2⟩
  have hsecondSubset :
      (package.selected.filter
        (fun item => label coordinate item = second)).card ≤
        finiteSetFiberCount vertices
          (label coordinate) second := by
    apply Finset.card_le_card
    intro item hitem
    exact Finset.mem_filter.mpr
      ⟨package.selectedSubset (Finset.mem_filter.mp hitem).1,
        (Finset.mem_filter.mp hitem).2⟩
  have hfirstRetention :=
    package.originalFiber_le_two_mul_denominator_mul_selectedFiber
      coordinate first hfirst
  have hsecondRetention :=
    package.originalFiber_le_two_mul_denominator_mul_selectedFiber
      coordinate second hsecond
  refine
    ⟨by
      have hcoordinate : 0 < Fintype.card Coordinate :=
        Fintype.card_pos
      have hB : 0 < B := by
        exact Nat.pos_of_ne_zero <| by
          intro hzero
          subst B
          exact Fin.elim0 (bin coordinate second)
      have hdenominator :
          0 < parentComponentCoreDenominator
            (Fintype.card Coordinate) B := by
        dsimp only [parentComponentCoreDenominator,
          parentComponentColorCount]
        positivity
      exact_mod_cast
        (show 1 ≤ 4 *
          parentComponentCoreDenominator
            (Fintype.card Coordinate) B by omega),
      ?_, ?_⟩
  · exact_mod_cast
      (calc
        (package.selected.filter
          (fun item => label coordinate item = first)).card
            ≤ finiteSetFiberCount vertices
                (label coordinate) first := hfirstSubset
        _ ≤ 2 * finiteSetFiberCount vertices
                (label coordinate) second := by
          exact_mod_cast horiginalComparable.2.1
        _ ≤ 2 *
            (2 * parentComponentCoreDenominator
              (Fintype.card Coordinate) B *
              (package.selected.filter
                (fun item =>
                  label coordinate item = second)).card) := by
          gcongr
        _ = 4 * parentComponentCoreDenominator
              (Fintype.card Coordinate) B *
              (package.selected.filter
                (fun item =>
                  label coordinate item = second)).card := by ring)
  · exact_mod_cast
      (calc
        (package.selected.filter
          (fun item => label coordinate item = second)).card
            ≤ finiteSetFiberCount vertices
                (label coordinate) second := hsecondSubset
        _ ≤ 2 * finiteSetFiberCount vertices
                (label coordinate) first := by
          exact_mod_cast horiginalComparable.2.2
        _ ≤ 2 *
            (2 * parentComponentCoreDenominator
              (Fintype.card Coordinate) B *
              (package.selected.filter
                (fun item =>
                  label coordinate item = first)).card) := by
          gcongr
        _ = 4 * parentComponentCoreDenominator
              (Fintype.card Coordinate) B *
              (package.selected.filter
                (fun item =>
                  label coordinate item = first)).card := by ring)

end SimultaneousBinnedLabelCorePackage

end Kakeya.Streamlined
