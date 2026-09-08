import MyLeanRepo.Kakeya.Streamlined.SimultaneousDegreeRegularization.WeightBinning
import MyLeanRepo.Kakeya.Streamlined.SimultaneousDegreeRegularization.ParentComponentCore
import MyLeanRepo.Kakeya.Streamlined.DividingScales.SimultaneousBinnedLabelCore
import MyLeanRepo.Kakeya.Streamlined.ProfileUniformRefinement.BoundedProfileDyadicLabels.Proof

/-!
# One weighted finite-coordinate core with ambient-fiber profiles

This selector first chooses one positive dyadic weight band.  Inside that
same band it simultaneously records, at every coordinate, both the band-fiber
size and the original ambient-fiber size, and then takes one label-threshold
core.  The single final set therefore retains the weight, has uniform active
fibers, and keeps the original ambient fibers comparable on every active
parent.
-/

noncomputable section

open scoped Classical

namespace Kakeya.Streamlined

universe uItem uCoordinate uLabel

def weightedFiniteCoordinateFiberCoreBinCount (itemCount : ℕ) : ℕ :=
  Nat.log 2 (2 * itemCount) + 1

def weightedFiniteCoordinateFiberCoreUniformity
    (coordinateCount itemCount : ℕ) : ENNReal :=
  4 * parentComponentCoreDenominator coordinateCount
    (weightedFiniteCoordinateFiberCoreBinCount itemCount ^ 2)

def weightedFiniteCoordinateFiberCoreWeightLoss
    (coordinateCount itemCount : ℕ) : ENNReal :=
  2 * (weightedFiniteCoordinateFiberCoreBinCount itemCount : ENNReal) *
    (8 * parentComponentColorCount coordinateCount
      (weightedFiniteCoordinateFiberCoreBinCount itemCount ^ 2) : ℕ)

lemma weightedFiniteCoordinateFiberCoreUniformity_one_le
    {coordinateCount itemCount : ℕ} (hcoordinateCount : 0 < coordinateCount) :
    1 ≤ weightedFiniteCoordinateFiberCoreUniformity
      coordinateCount itemCount := by
  let B := weightedFiniteCoordinateFiberCoreBinCount itemCount
  have hB : 0 < B := by
    simp [B, weightedFiniteCoordinateFiberCoreBinCount]
  have hden : 0 < parentComponentCoreDenominator coordinateCount (B ^ 2) := by
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) hcoordinateCount)
      (pow_pos (pow_pos hB 2) (2 * coordinateCount))
  dsimp only [weightedFiniteCoordinateFiberCoreUniformity]
  exact_mod_cast Nat.mul_pos (by norm_num : 0 < 4) hden

lemma weightedFiniteCoordinateFiberCoreUniformity_ne_top
    (coordinateCount itemCount : ℕ) :
    weightedFiniteCoordinateFiberCoreUniformity coordinateCount itemCount ≠ ⊤ := by
  exact ENNReal.mul_ne_top (by norm_num) (by simp)

structure WeightedFiniteCoordinateFiberCorePackage
    (Item : Type uItem)
    (Coordinate : Type uCoordinate)
    [Fintype Item] [DecidableEq Item]
    [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    (Label : Coordinate → Type uLabel)
    [∀ coordinate, Fintype (Label coordinate)]
    [∀ coordinate, DecidableEq (Label coordinate)]
    (parent : ∀ coordinate, Item → Label coordinate)
    (weight : Item → ENNReal) where
  selected : Finset Item
  selectedNonempty : selected.Nonempty
  fiberUniformity :
    ∀ coordinate,
    ∀ first second : Label coordinate,
      0 < (selected.filter
        (fun item => parent coordinate item = first)).card →
      0 < (selected.filter
        (fun item => parent coordinate item = second)).card →
      (((selected.filter
          (fun item => parent coordinate item = first)).card : ℕ) :
          ENNReal) ≤
        weightedFiniteCoordinateFiberCoreUniformity
            (Fintype.card Coordinate) (Fintype.card Item) *
          (((selected.filter
            (fun item => parent coordinate item = second)).card : ℕ) :
            ENNReal)
  ambientFiberComparable :
    ∀ coordinate,
    ∀ first second : Label coordinate,
      0 < (selected.filter
        (fun item => parent coordinate item = first)).card →
      0 < (selected.filter
        (fun item => parent coordinate item = second)).card →
      ComparableBy 2
        (((Finset.univ.filter
          (fun item : Item => parent coordinate item = first)).card : ℕ) :
          ENNReal)
        (((Finset.univ.filter
          (fun item : Item => parent coordinate item = second)).card : ℕ) :
          ENNReal)
  weightRetention :
    (∑ item : Item, weight item) ≤
      weightedFiniteCoordinateFiberCoreWeightLoss
          (Fintype.card Coordinate) (Fintype.card Item) *
        ∑ item ∈ selected, weight item

namespace WeightedFiniteCoordinateFiberCorePackage

variable
    {Item : Type uItem}
    {Coordinate : Type uCoordinate}
    [Fintype Item] [DecidableEq Item]
    [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    {Label : Coordinate → Type uLabel}
    [∀ coordinate, Fintype (Label coordinate)]
    [∀ coordinate, DecidableEq (Label coordinate)]
    {parent : ∀ coordinate, Item → Label coordinate}
    {weight : Item → ENNReal}

/-- A positive finite lower bound for the average weight converts the core's
weight retention into global cardinality retention. -/
theorem cardinalityRetention_of_averageWeight
    (package : WeightedFiniteCoordinateFiberCorePackage
      Item Coordinate Label parent weight)
    (lambda : ENNReal)
    (hlambdaZero : lambda ≠ 0) (hlambdaTop : lambda ≠ ⊤)
    (haverage :
      lambda * (Fintype.card Item : ENNReal) ≤
        ∑ item : Item, weight item)
    (hweightOne : ∀ item, weight item ≤ 1) :
    (Fintype.card Item : ENNReal) ≤
      lambda⁻¹ *
          weightedFiniteCoordinateFiberCoreWeightLoss
            (Fintype.card Coordinate) (Fintype.card Item) *
        (package.selected.card : ENNReal) := by
  let L := weightedFiniteCoordinateFiberCoreWeightLoss
    (Fintype.card Coordinate) (Fintype.card Item)
  have hselectedWeight :
      (∑ item ∈ package.selected, weight item) ≤
        (package.selected.card : ENNReal) := by
    calc
      (∑ item ∈ package.selected, weight item) ≤
          ∑ _item ∈ package.selected, (1 : ENNReal) :=
        Finset.sum_le_sum fun item _ => hweightOne item
      _ = (package.selected.card : ENNReal) := by simp
  have hscaled :
      lambda * (Fintype.card Item : ENNReal) ≤
        L * (package.selected.card : ENNReal) :=
    haverage.trans <| package.weightRetention.trans <| by
      exact mul_le_mul_left' hselectedWeight L
  calc
    (Fintype.card Item : ENNReal) =
        lambda⁻¹ * (lambda * (Fintype.card Item : ENNReal)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hlambdaZero hlambdaTop, one_mul]
    _ ≤ lambda⁻¹ * (L * (package.selected.card : ENNReal)) := by
      gcongr
    _ = lambda⁻¹ * L * (package.selected.card : ENNReal) := by
      ring

/--
Global cardinality retention plus the two profile comparisons of the weighted
core imply pointwise ambient-to-selected retention on every active fiber.
The active-parent cardinality cancels between the ambient and selected fiber
sums, so the estimate has no label-count factor.
-/
theorem ambientFiber_le_of_cardinalityRetention
    (package : WeightedFiniteCoordinateFiberCorePackage
      Item Coordinate Label parent weight)
    (L : ENNReal)
    (hcardinality :
      (Fintype.card Item : ENNReal) ≤
        L * (package.selected.card : ENNReal))
    (coordinate : Coordinate) (value : Label coordinate)
    (hactive : 0 < (package.selected.filter fun item =>
      parent coordinate item = value).card) :
    (((Finset.univ.filter fun item : Item =>
        parent coordinate item = value).card : ℕ) : ENNReal) ≤
      (2 * L * weightedFiniteCoordinateFiberCoreUniformity
          (Fintype.card Coordinate) (Fintype.card Item)) *
        (((package.selected.filter fun item =>
          parent coordinate item = value).card : ℕ) : ENNReal) := by
  classical
  let activeLabels : Finset (Label coordinate) :=
    package.selected.image (parent coordinate)
  let ambientCount : Label coordinate → ENNReal := fun label =>
    ((Finset.univ.filter fun item : Item =>
      parent coordinate item = label).card : ENNReal)
  let selectedCount : Label coordinate → ENNReal := fun label =>
    ((package.selected.filter fun item =>
      parent coordinate item = label).card : ENNReal)
  have hvalueMem : value ∈ activeLabels := by
    rcases Finset.card_pos.mp hactive with ⟨item, hitem⟩
    exact Finset.mem_image.mpr
      ⟨item, (Finset.mem_filter.mp hitem).1,
        (Finset.mem_filter.mp hitem).2⟩
  have hactiveLabels : activeLabels.Nonempty := ⟨value, hvalueMem⟩
  have hlabelActive : ∀ label ∈ activeLabels,
      0 < (package.selected.filter fun item =>
        parent coordinate item = label).card := by
    intro label hlabel
    rcases Finset.mem_image.mp hlabel with ⟨item, hitem, hitemLabel⟩
    apply Finset.card_pos.mpr
    exact ⟨item, Finset.mem_filter.mpr ⟨hitem, hitemLabel⟩⟩
  have hambientTerm : ∀ label ∈ activeLabels,
      ambientCount value ≤ 2 * ambientCount label := by
    intro label hlabel
    exact (package.ambientFiberComparable coordinate value label
      hactive (hlabelActive label hlabel)).2.1
  have hselectedTerm : ∀ label ∈ activeLabels,
      selectedCount label ≤
        weightedFiniteCoordinateFiberCoreUniformity
            (Fintype.card Coordinate) (Fintype.card Item) *
          selectedCount value := by
    intro label hlabel
    exact package.fiberUniformity coordinate label value
      (hlabelActive label hlabel) hactive
  have hsumAmbientNat :
      ∑ label ∈ activeLabels,
          (Finset.univ.filter fun item : Item =>
            parent coordinate item = label).card ≤
        Fintype.card Item := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    exact Finset.card_le_univ _
  have hsumAmbient :
      ∑ label ∈ activeLabels, ambientCount label ≤
        (Fintype.card Item : ENNReal) := by
    change
      (∑ label ∈ activeLabels,
        (((Finset.univ.filter fun item : Item =>
          parent coordinate item = label).card : ℕ) : ENNReal)) ≤
        (Fintype.card Item : ENNReal)
    exact_mod_cast hsumAmbientNat
  have hselectedMaps :
      (package.selected : Set Item).MapsTo
        (parent coordinate) activeLabels := by
    intro item hitem
    exact Finset.mem_image.mpr ⟨item, hitem, rfl⟩
  have hsumSelectedNat :
      package.selected.card =
        ∑ label ∈ activeLabels,
          (package.selected.filter fun item =>
            parent coordinate item = label).card :=
    Finset.card_eq_sum_card_fiberwise hselectedMaps
  have hsumSelected :
      (package.selected.card : ENNReal) =
        ∑ label ∈ activeLabels, selectedCount label := by
    change
      (package.selected.card : ENNReal) =
        ∑ label ∈ activeLabels,
          (((package.selected.filter fun item =>
            parent coordinate item = label).card : ℕ) : ENNReal)
    exact_mod_cast hsumSelectedNat
  have hactiveCardPos :
      (activeLabels.card : ENNReal) ≠ 0 := by
    exact_mod_cast hactiveLabels.card_pos.ne'
  have hscaled :
      (activeLabels.card : ENNReal) * ambientCount value ≤
        (activeLabels.card : ENNReal) *
          ((2 * L * weightedFiniteCoordinateFiberCoreUniformity
              (Fintype.card Coordinate) (Fintype.card Item)) *
            selectedCount value) := by
    calc
      (activeLabels.card : ENNReal) * ambientCount value =
          ∑ _label ∈ activeLabels, ambientCount value := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ label ∈ activeLabels, 2 * ambientCount label := by
        exact Finset.sum_le_sum hambientTerm
      _ = 2 * ∑ label ∈ activeLabels, ambientCount label := by
        rw [Finset.mul_sum]
      _ ≤ 2 * (Fintype.card Item : ENNReal) := by
        gcongr
      _ ≤ 2 * (L * (package.selected.card : ENNReal)) := by
        gcongr
      _ = 2 * L * ∑ label ∈ activeLabels, selectedCount label := by
        rw [← hsumSelected]
        ring
      _ ≤ 2 * L * ∑ _label ∈ activeLabels,
          weightedFiniteCoordinateFiberCoreUniformity
              (Fintype.card Coordinate) (Fintype.card Item) *
            selectedCount value := by
        exact mul_le_mul_left'
          (Finset.sum_le_sum fun label hlabel =>
            hselectedTerm label hlabel) (2 * L)
      _ = (activeLabels.card : ENNReal) *
          ((2 * L * weightedFiniteCoordinateFiberCoreUniformity
              (Fintype.card Coordinate) (Fintype.card Item)) *
            selectedCount value) := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  apply (ENNReal.mul_le_mul_iff_left hactiveCardPos (by simp)).mp
  simpa [ambientCount, selectedCount, mul_assoc, mul_comm, mul_left_comm] using hscaled

end WeightedFiniteCoordinateFiberCorePackage

theorem weighted_finite_coordinate_fiber_core
    (Item : Type uItem)
    (Coordinate : Type uCoordinate)
    [Fintype Item] [DecidableEq Item]
    [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    (Label : Coordinate → Type uLabel)
    [∀ coordinate, Fintype (Label coordinate)]
    [∀ coordinate, DecidableEq (Label coordinate)]
    (parent : ∀ coordinate, Item → Label coordinate)
    (weight : Item → ENNReal)
    (hweightPos : 0 < ∑ item : Item, weight item)
    (hweightTop : ∀ item, weight item ≠ ⊤) :
    Nonempty
      (WeightedFiniteCoordinateFiberCorePackage
        Item Coordinate Label parent weight) := by
  classical
  let itemCount := Fintype.card Item
  let coordinateCount := Fintype.card Coordinate
  let B := weightedFiniteCoordinateFiberCoreBinCount itemCount
  have hItemCount : 0 < itemCount := by
    by_contra hzero
    have hcardZero : Fintype.card Item = 0 :=
      Nat.eq_zero_of_not_pos hzero
    letI : IsEmpty Item := Fintype.card_eq_zero_iff.mp hcardZero
    have hsum : (∑ item : Item, weight item) = 0 := by
      simp
    rw [hsum] at hweightPos
    exact (lt_irrefl 0) hweightPos
  have hB : 0 < B := by
    simp [B, weightedFiniteCoordinateFiberCoreBinCount]
  have hboundOne : 1 ≤ 2 * itemCount := by omega
  have htotalTop : (∑ item : Item, weight item) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun item _ => hweightTop item
  rcases ennreal_dyadic_bin weight (∑ item : Item, weight item) rfl
      htotalTop hweightPos with
    ⟨bins, vertices, hbins, hvertices, hbandRetention,
      _hweightFloor, c, hc, hweightBand⟩
  have hBbins : B = bins := by
    simpa [B, itemCount, weightedFiniteCoordinateFiberCoreBinCount] using
      hbins.symm
  let zeroBin : Fin B := ⟨0, hB⟩
  let ambientProfile : ∀ coordinate, Label coordinate → ENNReal :=
    fun coordinate value =>
      ((Finset.univ.filter fun item : Item =>
        parent coordinate item = value).card : ENNReal)
  let bandProfile : ∀ coordinate, Label coordinate → ENNReal :=
    fun coordinate value =>
      ((vertices.filter fun item =>
        parent coordinate item = value).card : ENNReal)
  have hambientBound : ∀ coordinate value,
      ambientProfile coordinate value ≤ (2 * itemCount : ℕ) := by
    intro coordinate value
    change
      (((Finset.univ.filter fun item : Item =>
        parent coordinate item = value).card : ℕ) : ENNReal) ≤
        (2 * itemCount : ℕ)
    exact_mod_cast
      (Finset.card_le_univ
        (Finset.univ.filter fun item : Item =>
          parent coordinate item = value)).trans (by omega)
  have hbandBound : ∀ coordinate value,
      bandProfile coordinate value ≤ (2 * itemCount : ℕ) := by
    intro coordinate value
    change
      (((vertices.filter fun item =>
        parent coordinate item = value).card : ℕ) : ENNReal) ≤
        (2 * itemCount : ℕ)
    exact_mod_cast
      (Finset.card_le_card (Finset.filter_subset _ _)).trans
        ((Finset.card_le_univ vertices).trans (by omega))
  let ambientBin : ∀ coordinate, Label coordinate → Fin B :=
    fun coordinate value =>
      if hpositive : 0 < ambientProfile coordinate value then
        Classical.choose <|
          exists_profile_dyadic_bin (2 * itemCount) hboundOne
            (ambientProfile coordinate value)
            (by
              change (0 : ENNReal) <
                ((Finset.univ.filter fun item : Item =>
                  parent coordinate item = value).card : ENNReal) at hpositive
              change (1 : ENNReal) ≤
                ((Finset.univ.filter fun item : Item =>
                  parent coordinate item = value).card : ENNReal)
              exact_mod_cast (by exact_mod_cast hpositive :
                0 < (Finset.univ.filter fun item : Item =>
                  parent coordinate item = value).card))
            (hambientBound coordinate value)
      else zeroBin
  let bandBin : ∀ coordinate, Label coordinate → Fin B :=
    fun coordinate value =>
      if hpositive : 0 < bandProfile coordinate value then
        Classical.choose <|
          exists_profile_dyadic_bin (2 * itemCount) hboundOne
            (bandProfile coordinate value)
            (by
              change (0 : ENNReal) <
                ((vertices.filter fun item =>
                  parent coordinate item = value).card : ENNReal) at hpositive
              change (1 : ENNReal) ≤
                ((vertices.filter fun item =>
                  parent coordinate item = value).card : ENNReal)
              exact_mod_cast (by exact_mod_cast hpositive :
                0 < (vertices.filter fun item =>
                  parent coordinate item = value).card))
            (hbandBound coordinate value)
      else zeroBin
  have hambientBin : ∀ coordinate value,
      0 < ambientProfile coordinate value →
        InDyadicProfileBin
          (ambientBin coordinate value)
          (ambientProfile coordinate value) := by
    intro coordinate value hpositive
    dsimp only [ambientBin]
    rw [dif_pos hpositive]
    simpa [B, itemCount, weightedFiniteCoordinateFiberCoreBinCount] using
      Classical.choose_spec
        (exists_profile_dyadic_bin (2 * itemCount) hboundOne
          (ambientProfile coordinate value)
          (by
            change (0 : ENNReal) <
              ((Finset.univ.filter fun item : Item =>
                parent coordinate item = value).card : ENNReal) at hpositive
            change (1 : ENNReal) ≤
              ((Finset.univ.filter fun item : Item =>
                parent coordinate item = value).card : ENNReal)
            exact_mod_cast (by exact_mod_cast hpositive :
              0 < (Finset.univ.filter fun item : Item =>
                parent coordinate item = value).card))
          (hambientBound coordinate value))
  have hbandBin : ∀ coordinate value,
      0 < bandProfile coordinate value →
        InDyadicProfileBin
          (bandBin coordinate value)
          (bandProfile coordinate value) := by
    intro coordinate value hpositive
    dsimp only [bandBin]
    rw [dif_pos hpositive]
    simpa [B, itemCount, weightedFiniteCoordinateFiberCoreBinCount] using
      Classical.choose_spec
        (exists_profile_dyadic_bin (2 * itemCount) hboundOne
          (bandProfile coordinate value)
          (by
            change (0 : ENNReal) <
              ((vertices.filter fun item =>
                parent coordinate item = value).card : ENNReal) at hpositive
            change (1 : ENNReal) ≤
              ((vertices.filter fun item =>
                parent coordinate item = value).card : ENNReal)
            exact_mod_cast (by exact_mod_cast hpositive :
              0 < (vertices.filter fun item =>
                parent coordinate item = value).card))
          (hbandBound coordinate value))
  let PairBin := Fin B × Fin B
  let pairEquiv : PairBin ≃ Fin (B ^ 2) := by
    simpa [PairBin, Fintype.card_prod, pow_two] using Fintype.equivFin PairBin
  let profileBin : ∀ coordinate, Label coordinate → Fin (B ^ 2) :=
    fun coordinate value =>
      pairEquiv (ambientBin coordinate value, bandBin coordinate value)
  let core := Classical.choice <|
    simultaneous_binned_label_core
      Item Coordinate Label parent (B ^ 2) (by positivity) profileBin
      vertices hvertices weight c hc hweightBand
  let selected := core.selected
  have hselected := core.selectedNonempty
  have hselectedSubset := core.selectedSubset
  have hcoreWeight := core.weightRetention
  have hprofileCommon :
      ∀ coordinate, ∀ first ∈ selected, ∀ second ∈ selected,
        profileBin coordinate (parent coordinate first) =
          profileBin coordinate (parent coordinate second) :=
    core.binCommon
  have hambientCommon :
      ∀ coordinate, ∀ first ∈ selected, ∀ second ∈ selected,
        ambientBin coordinate (parent coordinate first) =
          ambientBin coordinate (parent coordinate second) := by
    intro coordinate first hfirst second hsecond
    have hpair := pairEquiv.injective
      (hprofileCommon coordinate first hfirst second hsecond)
    exact congrArg Prod.fst hpair
  have hbandCommon :
      ∀ coordinate, ∀ first ∈ selected, ∀ second ∈ selected,
        bandBin coordinate (parent coordinate first) =
          bandBin coordinate (parent coordinate second) := by
    intro coordinate first hfirst second hsecond
    have hpair := pairEquiv.injective
      (hprofileCommon coordinate first hfirst second hsecond)
    exact congrArg Prod.snd hpair
  have hbandRetentionCore :
      ∀ coordinate, ∀ value : Label coordinate,
        0 < (selected.filter fun item =>
          parent coordinate item = value).card →
        (vertices.filter fun item =>
          parent coordinate item = value).card ≤
          parentComponentCoreDenominator coordinateCount (B ^ 2) *
            ((selected.filter fun item =>
              parent coordinate item = value).card + 1) := by
    simpa [selected, coordinateCount] using core.fiberRetention
  have hselectedFiberUniformity :
      ∀ coordinate,
      ∀ first second : Label coordinate,
        0 < (selected.filter
          (fun item => parent coordinate item = first)).card →
        0 < (selected.filter
          (fun item => parent coordinate item = second)).card →
        (((selected.filter
            (fun item => parent coordinate item = first)).card : ℕ) :
            ENNReal) ≤
          weightedFiniteCoordinateFiberCoreUniformity
              coordinateCount itemCount *
            (((selected.filter
              (fun item => parent coordinate item = second)).card : ℕ) :
              ENNReal) := by
    intro coordinate first second hfirst hsecond
    let d := parentComponentCoreDenominator coordinateCount (B ^ 2)
    have hfirstBandPositive : 0 < bandProfile coordinate first := by
      have hsubset :
          selected.filter (fun item => parent coordinate item = first) ⊆
            vertices.filter (fun item => parent coordinate item = first) := by
        intro item hitem
        exact Finset.mem_filter.mpr
          ⟨hselectedSubset (Finset.mem_filter.mp hitem).1,
            (Finset.mem_filter.mp hitem).2⟩
      change (0 : ENNReal) <
        ((vertices.filter fun item =>
          parent coordinate item = first).card : ENNReal)
      exact_mod_cast hfirst.trans_le (Finset.card_le_card hsubset)
    have hsecondBandPositive : 0 < bandProfile coordinate second := by
      have hsubset :
          selected.filter (fun item => parent coordinate item = second) ⊆
            vertices.filter (fun item => parent coordinate item = second) := by
        intro item hitem
        exact Finset.mem_filter.mpr
          ⟨hselectedSubset (Finset.mem_filter.mp hitem).1,
            (Finset.mem_filter.mp hitem).2⟩
      change (0 : ENNReal) <
        ((vertices.filter fun item =>
          parent coordinate item = second).card : ENNReal)
      exact_mod_cast hsecond.trans_le (Finset.card_le_card hsubset)
    have hbandComparable : ComparableBy 2
        (bandProfile coordinate first)
        (bandProfile coordinate second) :=
      inDyadicProfileBin_comparable_of_eq
        (hbandBin coordinate first hfirstBandPositive)
        (hbandBin coordinate second hsecondBandPositive) <| by
          rcases Finset.card_pos.mp hfirst with ⟨firstItem, hfirstItem⟩
          rcases Finset.card_pos.mp hsecond with ⟨secondItem, hsecondItem⟩
          have hcommon := hbandCommon coordinate
            firstItem (Finset.mem_filter.mp hfirstItem).1
            secondItem (Finset.mem_filter.mp hsecondItem).1
          rwa [(Finset.mem_filter.mp hfirstItem).2,
            (Finset.mem_filter.mp hsecondItem).2] at hcommon
    have hfirstSubset :
        (selected.filter fun item => parent coordinate item = first).card ≤
          (vertices.filter fun item => parent coordinate item = first).card :=
      Finset.card_le_card <| Finset.filter_subset_filter _ hselectedSubset
    have hsecondRetention :
        (vertices.filter fun item => parent coordinate item = second).card ≤
          d * ((selected.filter fun item =>
            parent coordinate item = second).card + 1) := by
      simpa [d] using hbandRetentionCore coordinate second hsecond
    have hfirstSubsetENN :
        ((selected.filter fun item =>
          parent coordinate item = first).card : ENNReal) ≤
          bandProfile coordinate first := by
      dsimp only [bandProfile]
      change
        ((selected.filter fun item =>
          parent coordinate item = first).card : ENNReal) ≤
          ((vertices.filter fun item =>
            parent coordinate item = first).card : ENNReal)
      exact_mod_cast hfirstSubset
    have hsecondRetentionENN :
        bandProfile coordinate second ≤
          (d : ENNReal) *
            ((selected.filter fun item =>
              parent coordinate item = second).card + 1) := by
      dsimp only [bandProfile]
      change
        ((vertices.filter fun item =>
          parent coordinate item = second).card : ENNReal) ≤
          (d : ENNReal) *
            ((selected.filter fun item =>
              parent coordinate item = second).card + 1)
      exact_mod_cast hsecondRetention
    have hone : (1 : ENNReal) ≤
        (selected.filter fun item =>
          parent coordinate item = second).card := by
      exact_mod_cast (show 1 ≤ (selected.filter fun item =>
        parent coordinate item = second).card by omega)
    calc
      ((selected.filter fun item =>
          parent coordinate item = first).card : ENNReal)
          ≤ bandProfile coordinate first := hfirstSubsetENN
      _ ≤ 2 * bandProfile coordinate second := hbandComparable.2.1
      _ ≤ 2 * ((d : ENNReal) *
            ((selected.filter fun item =>
              parent coordinate item = second).card + 1)) := by gcongr
      _ ≤ 2 * ((d : ENNReal) *
            (2 * (selected.filter fun item =>
              parent coordinate item = second).card)) := by
        gcongr
        simpa [two_mul] using
          add_le_add_left hone
            ((selected.filter fun item =>
              parent coordinate item = second).card : ENNReal)
      _ = weightedFiniteCoordinateFiberCoreUniformity
              coordinateCount itemCount *
            ((selected.filter fun item =>
              parent coordinate item = second).card : ENNReal) := by
        simp [weightedFiniteCoordinateFiberCoreUniformity, d, B, itemCount]
        ring
  have hambientComparable :
      ∀ coordinate,
      ∀ first second : Label coordinate,
        0 < (selected.filter
          (fun item => parent coordinate item = first)).card →
        0 < (selected.filter
          (fun item => parent coordinate item = second)).card →
        ComparableBy 2
          (ambientProfile coordinate first)
          (ambientProfile coordinate second) := by
    intro coordinate first second hfirst hsecond
    have hfirstAmbientPositive : 0 < ambientProfile coordinate first := by
      rcases Finset.card_pos.mp hfirst with ⟨item, hitem⟩
      have hnat : 0 < (Finset.univ.filter fun candidate : Item =>
          parent coordinate candidate = first).card :=
        Finset.card_pos.mpr ⟨item, Finset.mem_filter.mpr
          ⟨Finset.mem_univ item, (Finset.mem_filter.mp hitem).2⟩⟩
      change (0 : ENNReal) <
        ((Finset.univ.filter fun candidate : Item =>
          parent coordinate candidate = first).card : ENNReal)
      exact_mod_cast hnat
    have hsecondAmbientPositive : 0 < ambientProfile coordinate second := by
      rcases Finset.card_pos.mp hsecond with ⟨item, hitem⟩
      have hnat : 0 < (Finset.univ.filter fun candidate : Item =>
          parent coordinate candidate = second).card :=
        Finset.card_pos.mpr ⟨item, Finset.mem_filter.mpr
          ⟨Finset.mem_univ item, (Finset.mem_filter.mp hitem).2⟩⟩
      change (0 : ENNReal) <
        ((Finset.univ.filter fun candidate : Item =>
          parent coordinate candidate = second).card : ENNReal)
      exact_mod_cast hnat
    apply inDyadicProfileBin_comparable_of_eq
      (hambientBin coordinate first hfirstAmbientPositive)
      (hambientBin coordinate second hsecondAmbientPositive)
    rcases Finset.card_pos.mp hfirst with ⟨firstItem, hfirstItem⟩
    rcases Finset.card_pos.mp hsecond with ⟨secondItem, hsecondItem⟩
    have hcommon := hambientCommon coordinate
      firstItem (Finset.mem_filter.mp hfirstItem).1
      secondItem (Finset.mem_filter.mp hsecondItem).1
    rwa [(Finset.mem_filter.mp hfirstItem).2,
      (Finset.mem_filter.mp hsecondItem).2] at hcommon
  have htotalWeight :
      (∑ item : Item, weight item) ≤
        weightedFiniteCoordinateFiberCoreWeightLoss
            coordinateCount itemCount *
          ∑ item ∈ selected, weight item := by
    have hfirst :
        (∑ item : Item, weight item) ≤
          2 * (bins : ENNReal) * ∑ item ∈ vertices, weight item := by
      have hhalf := hbandRetention
      have htwo :
          (∑ item : Item, weight item) / 2 * 2 =
            ∑ item : Item, weight item := by
        exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
      calc
        (∑ item : Item, weight item) =
            (∑ item : Item, weight item) / 2 * 2 := htwo.symm
        _ ≤ ((∑ item ∈ vertices, weight item) * (bins : ENNReal)) * 2 := by
          gcongr
        _ = 2 * (bins : ENNReal) *
            ∑ item ∈ vertices, weight item := by ring
    have hsecond :
        (∑ item : Item, weight item) ≤
          (2 * (bins : ENNReal) *
            (8 * parentComponentColorCount coordinateCount (B ^ 2) : ℕ)) *
              ∑ item ∈ selected, weight item := by
      calc
      (∑ item : Item, weight item)
          ≤ 2 * (bins : ENNReal) *
              ∑ item ∈ vertices, weight item := hfirst
      _ ≤ 2 * (bins : ENNReal) *
            ((8 * parentComponentColorCount coordinateCount (B ^ 2) : ℕ) *
              ∑ item ∈ selected, weight item) := by gcongr
      _ = (2 * (bins : ENNReal) *
            (8 * parentComponentColorCount coordinateCount (B ^ 2) : ℕ)) *
              ∑ item ∈ selected, weight item := by ring
    have hbinsCast : (bins : ENNReal) = (B : ENNReal) := by
      exact_mod_cast hBbins.symm
    rw [hbinsCast] at hsecond
    simpa only [weightedFiniteCoordinateFiberCoreWeightLoss,
      B, itemCount, coordinateCount] using hsecond
  exact ⟨{
    selected := selected
    selectedNonempty := hselected
    fiberUniformity := hselectedFiberUniformity
    ambientFiberComparable := by
      simpa [ambientProfile] using hambientComparable
    weightRetention := htotalWeight
  }⟩

end Kakeya.Streamlined
