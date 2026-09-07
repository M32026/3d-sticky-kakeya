import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PacketCellMultiplicity
import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization.HeavyColorClass

/-!
# Proposition 6.2: parent weight and fiber-cardinality classes

After the common fine multiplicity class is fixed, the paper defines

`w(P) = sum_q m(P,q) * |q|`

and `N(P)` to be the cardinality of the complete metric fiber over `P`.
All fixed fine cells have the same volume, so the integer incidence weight
`sum_q m(P,q)` carries exactly the same weighted pigeonhole information as
`w(P)`.

This module first dyadically pigeonholes the parent incidence weights and
then pigeonholes the complete-fiber cardinality, weighted by those same
incidence weights.  It selects whole parent vertices only; no tube and no
packet-cell incidence is exactified here.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62PacketCellInput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput cover shading)
    (multiplicity : input.FineMultiplicityClassData)

/-- Multiplicity-class packet-cells incident to one metric parent. -/
def selectedPairsAt
    (parent : Fin coarse.card) :
    Finset (Fin coarse.card × WZ2PaperCellIndex) :=
  multiplicity.selectedPairs.filter fun pair =>
    pair.1 = parent

/-- Parent vertices occurring in the multiplicity class. -/
def multiplicityParents : Finset (Fin coarse.card) :=
  multiplicity.selectedPairs.image Prod.fst

/-- The integer part of the paper weight `w(P)`. -/
def parentIncidenceWeight
    (parent : Fin coarse.card) : ℕ :=
  ∑ pair ∈ input.selectedPairsAt multiplicity parent,
    input.packetCellMultiplicity pair

/-- The physical packet-cell mass represented by `parentIncidenceWeight`. -/
def parentClassMass
    (parent : Fin coarse.card) : ENNReal :=
  (input.parentIncidenceWeight multiplicity parent : ENNReal) *
    volume (wz1PaperGridCube delta (0, 0, 0))

/-- `N(P)`, the cardinality of the complete genuine metric fiber. -/
def parentFiberCard
    (_input : PureWZ2Prop62PacketCellInput cover shading)
    (parent : Fin coarse.card) : ℕ :=
  (wz2PaperFullFiberIndices fine coarse parent).card

@[simp]
theorem mem_multiplicityParents_iff
    (parent : Fin coarse.card) :
    parent ∈ input.multiplicityParents multiplicity ↔
      ∃ cell,
        (parent, cell) ∈ multiplicity.selectedPairs := by
  constructor
  · intro parentMem
    rcases Finset.mem_image.mp parentMem with
      ⟨pair, pairMem, pairParent⟩
    subst parent
    exact ⟨pair.2, by simpa using pairMem⟩
  · rintro ⟨cell, pairMem⟩
    exact
      Finset.mem_image.mpr
        ⟨(parent, cell), pairMem, rfl⟩

theorem multiplicityParents_nonempty :
    (input.multiplicityParents multiplicity).Nonempty := by
  rcases multiplicity.selectedPairs_nonempty with
    ⟨pair, pairMem⟩
  exact
    ⟨pair.1,
      Finset.mem_image.mpr ⟨pair, pairMem, rfl⟩⟩

theorem selectedPairsAt_nonempty
    {parent : Fin coarse.card}
    (parentMem :
      parent ∈ input.multiplicityParents multiplicity) :
    (input.selectedPairsAt multiplicity parent).Nonempty := by
  rcases
      (input.mem_multiplicityParents_iff
        multiplicity parent).mp parentMem
    with ⟨cell, pairMem⟩
  exact
    ⟨(parent, cell),
      Finset.mem_filter.mpr ⟨pairMem, rfl⟩⟩

theorem parentIncidenceWeight_pos
    {parent : Fin coarse.card}
    (parentMem :
      parent ∈ input.multiplicityParents multiplicity) :
    0 < input.parentIncidenceWeight multiplicity parent := by
  rcases input.selectedPairsAt_nonempty multiplicity parentMem with
    ⟨pair, pairMem⟩
  have pairSelected :
      pair ∈ multiplicity.selectedPairs :=
    (Finset.mem_filter.mp pairMem).1
  have pairPositive :=
    multiplicity.multiplicity_band pair pairSelected |>.1
  have pairWeightPos :
      0 < input.packetCellMultiplicity pair :=
    multiplicity.muFine_pos.trans_le pairPositive
  exact
    pairWeightPos.trans_le <|
      Finset.single_le_sum
        (fun _ _ => Nat.zero_le _)
        pairMem

theorem parentFiberCard_pos
    {parent : Fin coarse.card}
    (parentMem :
      parent ∈ input.multiplicityParents multiplicity) :
    0 < input.parentFiberCard parent := by
  rcases
      (input.mem_multiplicityParents_iff
        multiplicity parent).mp parentMem
    with ⟨cell, pairMem⟩
  have pairPositive :=
    multiplicity.selectedPairs_subset pairMem
  have sourceCountPos :
      0 < input.packetCellMultiplicity (parent, cell) :=
    (input.mem_positivePairs_iff (parent, cell)).mp
      pairPositive |>.2
  rcases Finset.card_pos.mp sourceCountPos with
    ⟨source, sourceMem⟩
  have sourceFiber :
      source ∈ wz2PaperFullFiberIndices fine coarse parent :=
    (input.mem_packetCellSources_iff
      parent cell source).mp sourceMem |>.2.1
  exact Finset.card_pos.mpr ⟨source, sourceFiber⟩

theorem parentFiberCard_le_fine
    (parent : Fin coarse.card) :
    input.parentFiberCard parent ≤ fine.card := by
  have bound :=
    Finset.card_le_card
      (Finset.subset_univ
        (wz2PaperFullFiberIndices fine coarse parent))
  simpa [parentFiberCard] using bound

theorem sum_parentIncidenceWeight :
    (∑ parent ∈ input.multiplicityParents multiplicity,
        input.parentIncidenceWeight multiplicity parent) =
      ∑ pair ∈ multiplicity.selectedPairs,
        input.packetCellMultiplicity pair := by
  have allPairs :
      (multiplicity.selectedPairs.filter fun pair =>
          pair.1 ∈
            input.multiplicityParents multiplicity) =
        multiplicity.selectedPairs := by
    apply Finset.filter_true_of_mem
    intro pair pairMem
    exact
      Finset.mem_image.mpr
        ⟨pair, pairMem, rfl⟩
  change
    (∑ parent ∈ input.multiplicityParents multiplicity,
        ∑ pair ∈ multiplicity.selectedPairs with pair.1 = parent,
          input.packetCellMultiplicity pair) =
      ∑ pair ∈ multiplicity.selectedPairs,
        input.packetCellMultiplicity pair
  rw [Finset.sum_fiberwise_eq_sum_filter]
  rw [allPairs]

theorem sum_parentClassMass :
    (∑ parent ∈ input.multiplicityParents multiplicity,
        input.parentClassMass multiplicity parent) =
      (∑ pair ∈ multiplicity.selectedPairs,
          input.packetCellMultiplicity pair : ℕ) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  rw [← input.sum_parentIncidenceWeight multiplicity]
  simp only [parentClassMass, Nat.cast_sum]
  rw [Finset.sum_mul]

structure ParentClassData where
  weightLevel : ℕ
  weightFloor : ℕ
  weightFloor_eq : weightFloor = 2 ^ weightLevel
  weightFloor_pos : 0 < weightFloor
  weightClass : Finset (Fin coarse.card)
  weightClass_nonempty : weightClass.Nonempty
  weightClass_subset :
    weightClass ⊆ input.multiplicityParents multiplicity
  weight_band :
    ∀ parent ∈ weightClass,
      weightFloor ≤
          input.parentIncidenceWeight multiplicity parent ∧
        input.parentIncidenceWeight multiplicity parent <
          2 * weightFloor
  weightBinCount : ℕ
  weightBinCount_eq :
    weightBinCount =
      Nat.log 2
        (∑ parent ∈ input.multiplicityParents multiplicity,
          input.parentIncidenceWeight multiplicity parent) + 1
  weight_retention :
    (∑ parent ∈ input.multiplicityParents multiplicity,
        input.parentIncidenceWeight multiplicity parent) ≤
      weightBinCount *
        ∑ parent ∈ weightClass,
          input.parentIncidenceWeight multiplicity parent
  fiberLevel : ℕ
  fiberFloor : ℕ
  fiberFloor_eq : fiberFloor = 2 ^ fiberLevel
  fiberFloor_pos : 0 < fiberFloor
  fiberBinCount : ℕ
  fiberBinCount_eq :
    fiberBinCount = Nat.log 2 fine.card + 1
  selectedParents : Finset (Fin coarse.card)
  selectedParents_nonempty : selectedParents.Nonempty
  selectedParents_subset :
    selectedParents ⊆ weightClass
  fiber_card_band :
    ∀ parent ∈ selectedParents,
      fiberFloor ≤ input.parentFiberCard parent ∧
        input.parentFiberCard parent < 2 * fiberFloor
  fiber_weight_retention :
    (∑ parent ∈ weightClass,
        (input.parentIncidenceWeight multiplicity parent : ENNReal)) ≤
      (fiberBinCount : ENNReal) *
        ∑ parent ∈ selectedParents,
          (input.parentIncidenceWeight multiplicity parent : ENNReal)

namespace ParentClassData

variable
    (data : input.ParentClassData multiplicity)

theorem selectedParent_weight_pos
    {parent : Fin coarse.card}
    (parentMem : parent ∈ data.selectedParents) :
    0 < input.parentIncidenceWeight multiplicity parent := by
  have parentWeight :=
    data.weight_band parent
      (data.selectedParents_subset parentMem) |>.1
  exact data.weightFloor_pos.trans_le parentWeight

theorem selectedParent_mass_band
    (parent : Fin coarse.card)
    (parentMem : parent ∈ data.selectedParents) :
    (data.weightFloor : ENNReal) *
          volume (wz1PaperGridCube delta (0, 0, 0)) ≤
        input.parentClassMass multiplicity parent ∧
      input.parentClassMass multiplicity parent <
        (2 * data.weightFloor : ENNReal) *
          volume (wz1PaperGridCube delta (0, 0, 0)) := by
  have band :=
    data.weight_band parent
      (data.selectedParents_subset parentMem)
  constructor
  · exact mul_le_mul_right'
      (by exact_mod_cast band.1)
      _
  · have castUpper :
        (input.parentIncidenceWeight multiplicity parent : ENNReal) <
          (2 * data.weightFloor : ENNReal) := by
      exact_mod_cast band.2
    have cellVolumePos :
        0 <
          volume (wz1PaperGridCube delta (0, 0, 0)) :=
      wz1PaperGridCube_volume_pos input.delta_pos _
    have cellVolumeFinite :
        volume (wz1PaperGridCube delta (0, 0, 0)) ≠ ⊤ :=
      wz1PaperGridCube_volume_ne_top input.delta_pos _
    exact
      by
        simpa [parentClassMass, mul_comm] using
          ENNReal.mul_lt_mul_right
            cellVolumePos.ne' cellVolumeFinite
            castUpper

end ParentClassData

theorem pureWZ2_prop62_parent_class_selection :
    Nonempty (input.ParentClassData multiplicity) := by
  let totalWeight : ℕ :=
    ∑ parent ∈ input.multiplicityParents multiplicity,
      input.parentIncidenceWeight multiplicity parent
  rcases
      dyadic_band_pigeonhole
        (input.multiplicityParents multiplicity)
        (input.parentIncidenceWeight multiplicity)
        (input.multiplicityParents_nonempty multiplicity)
        (fun parent parentMem =>
          input.parentIncidenceWeight_pos multiplicity parentMem)
    with
    ⟨weightLevel, weightClass, weightClassNonempty,
      weightClassSubset, weightBand, weightRetention⟩
  let weightFloor := 2 ^ weightLevel
  have weightFloorPos : 0 < weightFloor := by
    positivity
  let weightBinCount := Nat.log 2 totalWeight + 1
  have weightRetention' :
      totalWeight ≤
        weightBinCount *
          ∑ parent ∈ weightClass,
            input.parentIncidenceWeight multiplicity parent := by
    simpa [totalWeight, weightBinCount,
      Nat.mul_comm] using weightRetention
  let fiberBinCount := Nat.log 2 fine.card + 1
  have fiberBinCountPos : 0 < fiberBinCount := by
    simp [fiberBinCount]
  have fiberLevelLt :
      ∀ parent : Fin coarse.card,
        Nat.log 2 (input.parentFiberCard parent) <
          fiberBinCount := by
    intro parent
    have logLe :
        Nat.log 2 (input.parentFiberCard parent) ≤
          Nat.log 2 fine.card :=
      Nat.log_mono_right
        (input.parentFiberCard_le_fine parent)
    simpa [fiberBinCount] using Nat.lt_succ_of_le logLe
  let fiberColor : Fin coarse.card → Fin fiberBinCount :=
    fun parent =>
      ⟨Nat.log 2 (input.parentFiberCard parent),
        fiberLevelLt parent⟩
  let parentWeight : Fin coarse.card → ENNReal :=
    fun parent =>
      input.parentIncidenceWeight multiplicity parent
  rcases
      exists_heavy_color_class
        weightClass fiberBinCount fiberBinCountPos
        fiberColor parentWeight
    with ⟨selectedFiberLevel, fiberRetention⟩
  let selectedParents : Finset (Fin coarse.card) :=
    weightClass.filter fun parent =>
      fiberColor parent = selectedFiberLevel
  have weightClassSumPos :
      0 <
        ∑ parent ∈ weightClass,
          parentWeight parent := by
    rcases weightClassNonempty with ⟨parent, parentMem⟩
    have parentPos :
        0 < parentWeight parent := by
      change
        0 <
          (input.parentIncidenceWeight multiplicity parent : ENNReal)
      exact_mod_cast
        input.parentIncidenceWeight_pos multiplicity
          (weightClassSubset parentMem)
    exact
      parentPos.trans_le <|
        Finset.single_le_sum
          (fun _ _ => by positivity)
          parentMem
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
        (∑ parent ∈ weightClass,
          parentWeight parent) ≤ 0 := by
      have heavy :
          (∑ parent ∈ weightClass,
              parentWeight parent) ≤
            (fiberBinCount : ENNReal) *
              ∑ parent ∈ selectedParents,
                parentWeight parent := by
        simpa [selectedParents] using fiberRetention
      simpa [selectedZero] using heavy
    exact (not_le_of_gt weightClassSumPos) totalLeZero
  have selectedParentsNonempty :
      selectedParents.Nonempty := by
    by_contra selectedEmpty
    have selectedEq : selectedParents = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp selectedEmpty
    rw [selectedEq] at selectedWeightPos
    simp at selectedWeightPos
  let fiberLevel := selectedFiberLevel.val
  let fiberFloor := 2 ^ fiberLevel
  have fiberFloorPos : 0 < fiberFloor := by
    positivity
  have fiberCardBand :
      ∀ parent ∈ selectedParents,
        fiberFloor ≤ input.parentFiberCard parent ∧
          input.parentFiberCard parent < 2 * fiberFloor := by
    intro parent parentMem
    have colorEq :
        fiberColor parent = selectedFiberLevel :=
      (Finset.mem_filter.mp parentMem).2
    have logEq :
        Nat.log 2 (input.parentFiberCard parent) =
          fiberLevel := by
      exact congrArg Fin.val colorEq
    have cardPos :
        0 < input.parentFiberCard parent :=
      input.parentFiberCard_pos multiplicity <|
        weightClassSubset
          (Finset.mem_filter.mp parentMem).1
    constructor
    · simpa [fiberFloor, logEq] using
        Nat.pow_log_le_self 2 cardPos.ne'
    · have upper :=
        Nat.lt_pow_succ_log_self
          (by norm_num : 1 < 2)
          (input.parentFiberCard parent)
      rw [logEq, pow_succ] at upper
      simpa [fiberFloor, Nat.mul_comm] using upper
  exact
    ⟨{
      weightLevel := weightLevel
      weightFloor := weightFloor
      weightFloor_eq := rfl
      weightFloor_pos := weightFloorPos
      weightClass := weightClass
      weightClass_nonempty := weightClassNonempty
      weightClass_subset := weightClassSubset
      weight_band := by
        intro parent parentMem
        have band := weightBand parent parentMem
        simpa [weightFloor, pow_succ,
          Nat.mul_comm] using band
      weightBinCount := weightBinCount
      weightBinCount_eq := rfl
      weight_retention := weightRetention'
      fiberLevel := fiberLevel
      fiberFloor := fiberFloor
      fiberFloor_eq := rfl
      fiberFloor_pos := fiberFloorPos
      fiberBinCount := fiberBinCount
      fiberBinCount_eq := rfl
      selectedParents := selectedParents
      selectedParents_nonempty := selectedParentsNonempty
      selectedParents_subset := Finset.filter_subset _ _
      fiber_card_band := fiberCardBand
      fiber_weight_retention := by
        simpa [selectedParents] using fiberRetention
    }⟩

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
