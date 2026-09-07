import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryMetricPreliminaryAssembly
import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization.HeavyColorClass

/-!
# Proposition 6.2: the pre-core metric-fiber cardinality bin

The paper chooses `D_-` before the one augmented-tree cleanup.  The selection
is made on metric parents and therefore retains the complete genuine metric
fiber of every selected parent.  The coloring is weighted by the current
preliminary leaf weight, so the choice is part of the preliminary geometric
selection rather than a post-core tube-family pruning.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62AncestryMetricPreliminaryOutput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow}
    {scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {coordinateCount : ℕ}
    {Color : Fin coordinateCount → Type*}
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    {color : ∀ coordinate, Fin fine.card → Color coordinate}
    {weight : Fin fine.card → ENNReal}
    {preliminary :
      PureWZ2Prop62AncestryPreliminarySelectionData
        schedule scheduled rho width packetCoordinate
        Color color weight}
    {M : ℝ}
    (output :
      PureWZ2Prop62AncestryMetricPreliminaryOutput
        schedule scheduled width packetCoordinate
        Color color weight preliminary M)

/-- The genuine Section 6 metric parent of a complete-hull source. -/
def metricParentOf
    (source : Fin output.metric.selectedFine.card) :
    Fin output.metric.metricParents.card :=
  output.metric.metricInput.packetParent
    (output.metric.mesh.restrictedOldData.cover.parent source)

/-- Metric parents carrying at least one current preliminary leaf. -/
def activeMetricParents :
    Finset (Fin output.metric.metricParents.card) :=
  output.selectedPreliminary.image output.metricParentOf

/-- Current preliminary leaf weight in the complete metric packet hull. -/
def preliminarySourceWeight
    (source : Fin output.metric.selectedFine.card) : ENNReal :=
  preliminary.activeWeight
    (output.metric.mesh.complete.selectedFine.embedding source)

/-- Total current preliminary weight assigned to one metric parent. -/
def metricParentWeight
    (parent : Fin output.metric.metricParents.card) : ENNReal :=
  ∑ source ∈ output.selectedPreliminary.filter
      (fun source => output.metricParentOf source = parent),
    output.preliminarySourceWeight source

/-- Cardinality of the complete genuine metric fiber before the final core. -/
def completeMetricFiberCard
    (parent : Fin output.metric.metricParents.card) : ℕ :=
  (wz2PaperFullFiberIndices
    output.metric.selectedFine output.metric.metricParents parent).card

theorem activeMetricParents_nonempty :
    output.activeMetricParents.Nonempty :=
  output.selectedPreliminary_nonempty.image _

theorem selectedPreliminary_activeWeight_pos
    {source : Fin output.metric.selectedFine.card}
    (sourceMem : source ∈ output.selectedPreliminary) :
    0 < output.preliminarySourceWeight source := by
  have selectedMem :
      output.metric.mesh.complete.selectedFine.embedding source ∈
        preliminary.preliminary.selected := by
    rw [output.selectedPreliminary_eq] at sourceMem
    exact (Finset.mem_filter.mp sourceMem).2
  exact
    preliminary.preliminary.weightLevel_pos.trans_le
      (preliminary.preliminary.selected_weight_band
        _ selectedMem).1

theorem activeMetricParentWeight_pos
    {parent : Fin output.metric.metricParents.card}
    (parentMem : parent ∈ output.activeMetricParents) :
    0 < output.metricParentWeight parent := by
  rcases Finset.mem_image.mp parentMem with
    ⟨source, sourceMem, sourceParent⟩
  have sourceFilter :
      source ∈ output.selectedPreliminary.filter
        (fun index => output.metricParentOf index = parent) :=
    Finset.mem_filter.mpr ⟨sourceMem, sourceParent⟩
  exact
    (output.selectedPreliminary_activeWeight_pos sourceMem).trans_le <|
      Finset.single_le_sum
        (fun _ _ => by positivity)
        sourceFilter

theorem completeMetricFiberCard_pos
    {parent : Fin output.metric.metricParents.card}
    (parentMem : parent ∈ output.activeMetricParents) :
    0 < output.completeMetricFiberCard parent := by
  rcases Finset.mem_image.mp parentMem with
    ⟨source, _sourceMem, sourceParent⟩
  apply Finset.card_pos.mpr
  refine ⟨source, ?_⟩
  rw [output.metric.metricFiber_eq_assignedPackets]
  exact
    (show
      source ∈
        Finset.univ.filter
          (fun index : Fin output.metric.selectedFine.card =>
            output.metric.metricInput.packetParent
                (output.metric.mesh.restrictedOldData.cover.parent index) =
              parent)
      from
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ source, sourceParent⟩)

theorem completeMetricFiberCard_le_selectedFine
    (parent : Fin output.metric.metricParents.card) :
    output.completeMetricFiberCard parent ≤
      output.metric.selectedFine.card := by
  simpa only [completeMetricFiberCard, Finset.card_univ,
    Fintype.card_fin] using
    Finset.card_le_card <|
      Finset.subset_univ
        (wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents parent)

theorem sum_metricParentWeight :
    (∑ parent ∈ output.activeMetricParents,
        output.metricParentWeight parent) =
      ∑ source ∈ output.selectedPreliminary,
        output.preliminarySourceWeight source := by
  have allSelected :
      output.selectedPreliminary.filter
          (fun source =>
            output.metricParentOf source ∈
              output.activeMetricParents) =
        output.selectedPreliminary := by
    apply Finset.filter_true_of_mem
    intro source sourceMem
    exact
      Finset.mem_image.mpr
        ⟨source, sourceMem, rfl⟩
  change
    (∑ parent ∈ output.activeMetricParents,
        ∑ source ∈ output.selectedPreliminary with
            output.metricParentOf source = parent,
          output.preliminarySourceWeight source) =
      ∑ source ∈ output.selectedPreliminary,
        output.preliminarySourceWeight source
  rw [Finset.sum_fiberwise_eq_sum_filter]
  rw [allSelected]

structure MetricFiberCardinalityBinData where
  fiberLevel : ℕ
  fiberFloor : ℕ
  fiberFloor_eq : fiberFloor = 2 ^ fiberLevel
  fiberFloor_pos : 0 < fiberFloor
  fiberBinCount : ℕ
  fiberBinCount_eq :
    fiberBinCount =
      Nat.log 2 output.metric.selectedFine.card + 1
  selectedParents :
    Finset (Fin output.metric.metricParents.card)
  selectedParents_nonempty : selectedParents.Nonempty
  selectedParents_subset :
    selectedParents ⊆ output.activeMetricParents
  fiber_card_band :
    ∀ parent ∈ selectedParents,
      fiberFloor ≤ output.completeMetricFiberCard parent ∧
        output.completeMetricFiberCard parent < 2 * fiberFloor
  preliminary_weight_retention :
    (∑ source ∈ output.selectedPreliminary,
        output.preliminarySourceWeight source) ≤
      (fiberBinCount : ENNReal) *
        ∑ parent ∈ selectedParents,
          output.metricParentWeight parent

theorem exists_metricFiberCardinalityBinData :
    Nonempty output.MetricFiberCardinalityBinData := by
  let fiberBinCount :=
    Nat.log 2 output.metric.selectedFine.card + 1
  have fiberBinCountPos : 0 < fiberBinCount := by
    simp [fiberBinCount]
  have fiberLevelLt :
      ∀ parent : Fin output.metric.metricParents.card,
        Nat.log 2 (output.completeMetricFiberCard parent) <
          fiberBinCount := by
    intro parent
    have logLe :
        Nat.log 2 (output.completeMetricFiberCard parent) ≤
          Nat.log 2 output.metric.selectedFine.card :=
      Nat.log_mono_right
        (output.completeMetricFiberCard_le_selectedFine parent)
    simpa [fiberBinCount] using Nat.lt_succ_of_le logLe
  let fiberColor :
      Fin output.metric.metricParents.card → Fin fiberBinCount :=
    fun parent =>
      ⟨Nat.log 2 (output.completeMetricFiberCard parent),
        fiberLevelLt parent⟩
  rcases
      exists_heavy_color_class
        output.activeMetricParents fiberBinCount fiberBinCountPos
        fiberColor output.metricParentWeight
    with ⟨selectedFiberLevel, fiberRetention⟩
  let selectedParents :
      Finset (Fin output.metric.metricParents.card) :=
    output.activeMetricParents.filter fun parent =>
      fiberColor parent = selectedFiberLevel
  have activeWeightPos :
      0 <
        ∑ parent ∈ output.activeMetricParents,
          output.metricParentWeight parent := by
    rcases output.activeMetricParents_nonempty with
      ⟨parent, parentMem⟩
    exact
      (output.activeMetricParentWeight_pos parentMem).trans_le <|
        Finset.single_le_sum
          (fun _ _ => by positivity)
          parentMem
  have selectedWeightPos :
      0 <
        ∑ parent ∈ selectedParents,
          output.metricParentWeight parent := by
    by_contra selectedNotPos
    have selectedZero :
        (∑ parent ∈ selectedParents,
          output.metricParentWeight parent) = 0 := by
      simpa using selectedNotPos
    have activeLeZero :
        (∑ parent ∈ output.activeMetricParents,
          output.metricParentWeight parent) ≤ 0 := by
      have heavy :
          (∑ parent ∈ output.activeMetricParents,
              output.metricParentWeight parent) ≤
            (fiberBinCount : ENNReal) *
              ∑ parent ∈ selectedParents,
                output.metricParentWeight parent := by
        simpa [selectedParents] using fiberRetention
      simpa [selectedZero] using heavy
    exact (not_le_of_gt activeWeightPos) activeLeZero
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
        fiberFloor ≤ output.completeMetricFiberCard parent ∧
          output.completeMetricFiberCard parent < 2 * fiberFloor := by
    intro parent parentMem
    have activeMem :
        parent ∈ output.activeMetricParents :=
      (Finset.mem_filter.mp parentMem).1
    have colorEq :
        fiberColor parent = selectedFiberLevel :=
      (Finset.mem_filter.mp parentMem).2
    have logEq :
        Nat.log 2 (output.completeMetricFiberCard parent) =
          fiberLevel :=
      congrArg Fin.val colorEq
    have cardPos :
        0 < output.completeMetricFiberCard parent :=
      output.completeMetricFiberCard_pos activeMem
    constructor
    · simpa [fiberFloor, logEq] using
        Nat.pow_log_le_self 2 cardPos.ne'
    · have upper :=
        Nat.lt_pow_succ_log_self
          (by norm_num : 1 < 2)
          (output.completeMetricFiberCard parent)
      rw [logEq, pow_succ] at upper
      simpa [fiberFloor, Nat.mul_comm] using upper
  exact
    ⟨{
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
      preliminary_weight_retention := by
        rw [← output.sum_metricParentWeight]
        simpa [selectedParents] using fiberRetention
    }⟩

namespace MetricFiberCardinalityBinData

variable
    (data : output.MetricFiberCardinalityBinData)

/-- The complete pre-core fine family `U⁰` selected by the parent bin. -/
def completeFineIndices :
    Finset (Fin output.metric.selectedFine.card) :=
  Finset.univ.filter fun source =>
    output.metricParentOf source ∈ data.selectedParents

/-- Preliminary weighted leaves sent to the one final augmented-tree core. -/
def binnedPreliminary :
    Finset (Fin output.metric.selectedFine.card) :=
  output.selectedPreliminary.filter fun source =>
    output.metricParentOf source ∈ data.selectedParents

/-- Ambient indexing of the binned preliminary leaves. -/
def ambientPreliminary : Finset (Fin fine.card) :=
  data.binnedPreliminary.image
    output.metric.mesh.complete.selectedFine.embedding

theorem selectedParent_active
    {parent : Fin output.metric.metricParents.card}
    (parentMem : parent ∈ data.selectedParents) :
    parent ∈ output.activeMetricParents :=
  data.selectedParents_subset parentMem

theorem binnedPreliminary_nonempty :
    data.binnedPreliminary.Nonempty := by
  rcases data.selectedParents_nonempty with
    ⟨parent, parentMem⟩
  rcases Finset.mem_image.mp
      (selectedParent_active output data parentMem) with
    ⟨source, sourceMem, sourceParent⟩
  exact
    ⟨source,
      Finset.mem_filter.mpr
        ⟨sourceMem, by
          simpa only [sourceParent] using parentMem⟩⟩

theorem ambientPreliminary_nonempty :
    data.ambientPreliminary.Nonempty :=
  (binnedPreliminary_nonempty output data).image _

theorem binnedPreliminary_subset_selected :
    data.binnedPreliminary ⊆ output.selectedPreliminary :=
  Finset.filter_subset _ _

theorem completeFineIndices_nonempty :
    data.completeFineIndices.Nonempty := by
  rcases data.binnedPreliminary_nonempty with
    ⟨source, sourceMem⟩
  exact
    ⟨source,
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ source,
          (Finset.mem_filter.mp sourceMem).2⟩⟩

theorem binnedPreliminary_subset_complete :
    data.binnedPreliminary ⊆ data.completeFineIndices := by
  intro source sourceMem
  exact
    Finset.mem_filter.mpr
      ⟨Finset.mem_univ source,
        (Finset.mem_filter.mp sourceMem).2⟩

theorem ambientPreliminary_subset_original :
    data.ambientPreliminary ⊆
      preliminary.preliminary.selected := by
  intro ambientSource ambientMem
  rcases Finset.mem_image.mp ambientMem with
    ⟨source, sourceMem, sourceEq⟩
  have selectedMem :
      source ∈ output.selectedPreliminary :=
    binnedPreliminary_subset_selected output data sourceMem
  rw [output.selectedPreliminary_eq] at selectedMem
  have ambientSelected :=
    (Finset.mem_filter.mp selectedMem).2
  rwa [sourceEq] at ambientSelected

theorem ambientPreliminary_subset_packetHull :
    data.ambientPreliminary ⊆
      output.metric.mesh.complete.selectedFineIndices := by
  intro ambientSource ambientMem
  rw [output.packet_hull_eq_perCell]
  exact
    preliminary.selected_subset_perCell <|
      ambientPreliminary_subset_original output data ambientMem

theorem completeFineIndices_eq_biUnion :
    data.completeFineIndices =
      data.selectedParents.biUnion fun parent =>
        wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents parent := by
  ext source
  simp only [completeFineIndices, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_biUnion]
  constructor
  · intro parentMem
    refine
      ⟨output.metricParentOf source, parentMem, ?_⟩
    rw [output.metric.metricFiber_eq_assignedPackets]
    exact
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ source, rfl⟩
  · rintro ⟨parent, parentMem, sourceFiber⟩
    rw [output.metric.metricFiber_eq_assignedPackets] at sourceFiber
    have sourceParent :=
      (Finset.mem_filter.mp sourceFiber).2
    simpa only [metricParentOf, sourceParent] using parentMem

theorem selectedParent_completeFiber_subset
    {parent : Fin output.metric.metricParents.card}
    (parentMem : parent ∈ data.selectedParents) :
    wz2PaperFullFiberIndices
        output.metric.selectedFine
        output.metric.metricParents parent ⊆
      data.completeFineIndices := by
  rw [completeFineIndices_eq_biUnion output data]
  exact Finset.subset_biUnion_of_mem _ parentMem

theorem binnedPreliminary_weight_eq :
    (∑ source ∈ data.binnedPreliminary,
        output.preliminarySourceWeight source) =
      ∑ parent ∈ data.selectedParents,
        output.metricParentWeight parent := by
  change
    (∑ source ∈ output.selectedPreliminary.filter
        (fun source =>
          output.metricParentOf source ∈ data.selectedParents),
        output.preliminarySourceWeight source) =
      ∑ parent ∈ data.selectedParents,
        ∑ source ∈ output.selectedPreliminary.filter
            (fun source => output.metricParentOf source = parent),
          output.preliminarySourceWeight source
  rw [Finset.sum_fiberwise_eq_sum_filter]

theorem binnedPreliminary_weight_retention :
    (∑ source ∈ output.selectedPreliminary,
        output.preliminarySourceWeight source) ≤
      (data.fiberBinCount : ENNReal) *
        ∑ source ∈ data.binnedPreliminary,
          output.preliminarySourceWeight source := by
  rw [binnedPreliminary_weight_eq output data]
  exact data.preliminary_weight_retention

end MetricFiberCardinalityBinData

/-- The canonical paper `D_-` choice made before the final core. -/
noncomputable def metricFiberCardinalityBin :
    output.MetricFiberCardinalityBinData :=
  Classical.choice output.exists_metricFiberCardinalityBinData

/-- The complete pre-core family `U⁰`, as indices in the metric packet hull. -/
noncomputable def preCoreCompleteFineIndices :
    Finset (Fin output.metric.selectedFine.card) :=
  output.metricFiberCardinalityBin.completeFineIndices

/-- The binned preliminary set, reindexed in the original ambient family. -/
noncomputable def binnedAmbientPreliminary :
    Finset (Fin fine.card) :=
  output.metricFiberCardinalityBin.ambientPreliminary

theorem binnedAmbientPreliminary_nonempty :
    output.binnedAmbientPreliminary.Nonempty :=
  output.metricFiberCardinalityBin.ambientPreliminary_nonempty

theorem binnedAmbientPreliminary_subset_original :
    output.binnedAmbientPreliminary ⊆
      preliminary.preliminary.selected :=
  output.metricFiberCardinalityBin.ambientPreliminary_subset_original

theorem binnedAmbientPreliminary_subset_packetHull :
    output.binnedAmbientPreliminary ⊆
      output.metric.mesh.complete.selectedFineIndices :=
  output.metricFiberCardinalityBin.ambientPreliminary_subset_packetHull

theorem preCoreCompleteFineIndices_eq_biUnion :
    output.preCoreCompleteFineIndices =
      output.metricFiberCardinalityBin.selectedParents.biUnion fun parent =>
        wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents parent :=
  output.metricFiberCardinalityBin.completeFineIndices_eq_biUnion

theorem preCoreMetricFiber_card_band
    (parent :
      Fin output.metric.metricParents.card)
    (parentMem :
      parent ∈ output.metricFiberCardinalityBin.selectedParents) :
    output.metricFiberCardinalityBin.fiberFloor ≤
        (wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents parent).card ∧
      (wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents parent).card <
        2 * output.metricFiberCardinalityBin.fiberFloor :=
  output.metricFiberCardinalityBin.fiber_card_band parent parentMem

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end
