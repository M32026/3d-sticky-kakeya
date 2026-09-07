import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightSaturation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularWeightedParents

/-!
# One second-cover parent per y-layer for the joint-height source

The fixed common-bin strip bounds the number of second-cover parents above
one parent y-index by thirteen.  Selecting a maximum-weight parent in each
y-layer therefore retains the saturated source volume up to a fixed factor.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2Node05V4RichSourceVolumePopularHeightData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    {volumePopular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex}
    {B₀ threshold : ENNReal}
    (block : volumePopular.JointHeightCommonBinData B₀ threshold)

namespace JointHeightCommonBinData

def jointParentCells : Finset WZ2PaperCellIndex :=
  block.jointFixedBinRhoCells.image pullback.standardSecondParent

theorem jointParentCells_nonempty : block.jointParentCells.Nonempty :=
  block.jointFixedBinRhoCells_nonempty.image pullback.standardSecondParent

theorem jointParentCells_subset_active :
    block.jointParentCells ⊆ twoScale.secondBalancedCover.activeCells := by
  intro parent hparent
  rw [jointParentCells] at hparent
  rcases Finset.mem_image.mp hparent with ⟨cell, hcell, rfl⟩
  exact pullback.standardSecondParent_active
    (block.jointFixedBinRhoCells_subset_selected hcell)

theorem jointParent_has_source_cell
    {parent : WZ2PaperCellIndex} (hparent : parent ∈ block.jointParentCells) :
    ∃ cell ∈ block.jointFixedBinRhoCells,
      pullback.standardSecondParent cell = parent := by
  simpa [jointParentCells] using Finset.mem_image.mp hparent

theorem jointCellSource_nonempty
    {cell : WZ2PaperCellIndex}
    (hcell : cell ∈ block.jointFixedBinRhoCells) :
    (block.jointCellSource cell).Nonempty := by
  rw [jointFixedBinRhoCells, Finset.mem_filter] at hcell
  exact hcell.2

theorem jointParent_y_fiber_card (y : ℤ) :
    (block.jointParentCells.filter fun parent => parent.2.1 = y).card ≤ 13 := by
  let fiber := block.jointParentCells.filter fun parent => parent.2.1 = y
  change fiber.card ≤ 13
  by_cases hfiber : fiber = ∅
  · rw [hfiber]
    simp
  have hfiberNonempty : fiber.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hfiber
  let first := Classical.choose hfiberNonempty
  have hfirstFiber : first ∈ fiber := Classical.choose_spec hfiberNonempty
  have hfirstParent : first ∈ block.jointParentCells :=
    (Finset.mem_filter.mp hfirstFiber).1
  have hfirstY : first.2.1 = y :=
    (Finset.mem_filter.mp hfirstFiber).2
  let cellFor : WZ2PaperCellIndex → WZ2PaperCellIndex := fun parent =>
    if hparent : parent ∈ block.jointParentCells then
      Classical.choose (block.jointParent_has_source_cell hparent)
    else Classical.choose block.jointFixedBinRhoCells_nonempty
  have hcellForMem :
      ∀ parent (hparent : parent ∈ block.jointParentCells),
        cellFor parent ∈ block.jointFixedBinRhoCells := by
    intro parent hparent
    simp only [cellFor, dif_pos hparent]
    exact (Classical.choose_spec
      (block.jointParent_has_source_cell hparent)).1
  have hcellForParent :
      ∀ parent (hparent : parent ∈ block.jointParentCells),
        pullback.standardSecondParent (cellFor parent) = parent := by
    intro parent hparent
    simp only [cellFor, dif_pos hparent]
    exact (Classical.choose_spec
      (block.jointParent_has_source_cell hparent)).2
  let witness : WZ2PaperCellIndex → Point3 := fun parent =>
    if hparent : parent ∈ block.jointParentCells then
      Classical.choose (block.jointCellSource_nonempty
        (hcellForMem parent hparent))
    else 0
  have hwitness :
      ∀ parent (hparent : parent ∈ block.jointParentCells),
        witness parent ∈ block.jointCellSource (cellFor parent) := by
    intro parent hparent
    simp only [witness, dif_pos hparent]
    exact Classical.choose_spec
      (block.jointCellSource_nonempty (hcellForMem parent hparent))
  have hwitnessParent :
      ∀ parent (hparent : parent ∈ block.jointParentCells),
        witness parent ∈ wz1PaperGridCube sqrtRequested.1 parent := by
    intro parent hparent
    have hraw := pullback.standardSecondParent_cell_subset
      (block.jointFixedBinRhoCells_subset_selected
        (hcellForMem parent hparent))
      (hwitness parent hparent).2
    rwa [hcellForParent parent hparent] at hraw
  have hnear :
      ∀ parent (hparent : parent ∈ block.jointParentCells),
        |inner ℝ (witness parent)
              (globalGrainDirection
                (current.grain.globalGrains.slope block.referenceHeight)) -
            (block.bin : ℝ) * Real.sqrt rho| ≤ Real.sqrt rho := by
    intro parent hparent
    have hfixed := (hwitness parent hparent).1
    rw [jointFixedBinHeightRegion,
      pureWZ2FixedCommonBinRegion] at hfixed
    have hlabel := hfixed.1.2
    change Int.floor
        (inner ℝ (witness parent)
          (globalGrainDirection
            (current.grain.globalGrains.slope block.referenceHeight)) /
          Real.sqrt rho) = block.bin at hlabel
    rw [Int.floor_eq_iff] at hlabel
    have hroot : 0 < Real.sqrt rho := by
      rw [← pullback.rhoRequested_eq]
      exact Real.sqrt_pos.mpr
        twoScale.first.publicSticky.coarse_extremal.delta_pos
    have hlower :
        (block.bin : ℝ) * Real.sqrt rho ≤
          inner ℝ (witness parent)
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight)) := by
      exact (le_div_iff₀ hroot).mp (by simpa [mul_comm] using hlabel.1)
    have hupper :
        inner ℝ (witness parent)
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight)) <
          (block.bin : ℝ) * Real.sqrt rho + Real.sqrt rho := by
      have hraw := (div_lt_iff₀ hroot).mp (by simpa using hlabel.2)
      linarith
    rw [abs_le]
    constructor <;> linarith
  have hindexRange :
      ∀ parent ∈ fiber,
        first.1 - 6 ≤ parent.1 ∧ parent.1 ≤ first.1 + 6 := by
    intro parent hparentFiber
    have hparent : parent ∈ block.jointParentCells :=
      (Finset.mem_filter.mp hparentFiber).1
    have hparentY : parent.2.1 = y :=
      (Finset.mem_filter.mp hparentFiber).2
    have hparentMem := hwitnessParent parent hparent
    have hfirstMem := hwitnessParent first hfirstParent
    rw [wz1PaperGridCube_eq_Ico
      twoScale.secondSticky.coarse_extremal.delta_pos] at hparentMem hfirstMem
    rw [twoScale.sqrtRequested_eq, pullback.rhoRequested_eq] at hparentMem hfirstMem
    rw [hparentY] at hparentMem
    rw [hfirstY] at hfirstMem
    have hyClose :
        |witness parent 1 - witness first 1| ≤ Real.sqrt rho := by
      rw [abs_le]
      constructor <;>
        nlinarith [hparentMem.2.2.1, hparentMem.2.2.2.1,
          hfirstMem.2.2.1, hfirstMem.2.2.2.1, hparentY, hfirstY]
    have hcoordClose :
        |inner ℝ (witness parent)
              (globalGrainDirection
                (current.grain.globalGrains.slope block.referenceHeight)) -
            inner ℝ (witness first)
              (globalGrainDirection
                (current.grain.globalGrains.slope block.referenceHeight))| ≤
          2 * Real.sqrt rho := by
      have hp := hnear parent hparent
      have hf := hnear first hfirstParent
      have htriangle := abs_sub
        (inner ℝ (witness parent)
          (globalGrainDirection
            (current.grain.globalGrains.slope block.referenceHeight)) -
          (block.bin : ℝ) * Real.sqrt rho)
        (inner ℝ (witness first)
          (globalGrainDirection
            (current.grain.globalGrains.slope block.referenceHeight)) -
          (block.bin : ℝ) * Real.sqrt rho)
      have hrewrite :
          inner ℝ (witness parent)
                (globalGrainDirection
                  (current.grain.globalGrains.slope block.referenceHeight)) -
              inner ℝ (witness first)
                (globalGrainDirection
                  (current.grain.globalGrains.slope block.referenceHeight)) =
            (inner ℝ (witness parent)
                (globalGrainDirection
                  (current.grain.globalGrains.slope block.referenceHeight)) -
              (block.bin : ℝ) * Real.sqrt rho) -
            (inner ℝ (witness first)
                (globalGrainDirection
                  (current.grain.globalGrains.slope block.referenceHeight)) -
              (block.bin : ℝ) * Real.sqrt rho) := by ring
      rw [hrewrite]
      exact htriangle.trans (by linarith)
    have hreferenceRange :=
      volumePopular.jointPopularHeight_mem_paperRange
        block.referenceHeight_mem
    have hslope :=
      current.grain.globalGrains.slope_bound
        block.referenceHeight hreferenceRange
    have hxClose :
        |witness parent 0 - witness first 0| ≤ 5 * Real.sqrt rho := by
      have hformula :
          inner ℝ (witness parent)
                (globalGrainDirection
                  (current.grain.globalGrains.slope block.referenceHeight)) -
              inner ℝ (witness first)
                (globalGrainDirection
                  (current.grain.globalGrains.slope block.referenceHeight)) =
            (witness parent 0 - witness first 0) +
              current.grain.globalGrains.slope block.referenceHeight *
                (witness parent 1 - witness first 1) := by
        simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
        ring
      have hrewrite :
          witness parent 0 - witness first 0 =
            (inner ℝ (witness parent)
                (globalGrainDirection
                  (current.grain.globalGrains.slope block.referenceHeight)) -
              inner ℝ (witness first)
                (globalGrainDirection
                  (current.grain.globalGrains.slope block.referenceHeight))) -
            current.grain.globalGrains.slope block.referenceHeight *
              (witness parent 1 - witness first 1) := by
        linarith [hformula]
      rw [hrewrite]
      calc
        _ ≤ |inner ℝ (witness parent)
                (globalGrainDirection
                  (current.grain.globalGrains.slope block.referenceHeight)) -
              inner ℝ (witness first)
                (globalGrainDirection
                  (current.grain.globalGrains.slope block.referenceHeight))| +
            |current.grain.globalGrains.slope block.referenceHeight| *
              |witness parent 1 - witness first 1| := by
          simpa [abs_mul] using abs_sub_le
            (inner ℝ (witness parent)
              (globalGrainDirection
                (current.grain.globalGrains.slope block.referenceHeight)) -
             inner ℝ (witness first)
              (globalGrainDirection
                (current.grain.globalGrains.slope block.referenceHeight)))
            0
            (current.grain.globalGrains.slope block.referenceHeight *
              (witness parent 1 - witness first 1))
        _ ≤ 2 * Real.sqrt rho + 3 * Real.sqrt rho := by gcongr
        _ = 5 * Real.sqrt rho := by ring
    have hroot : 0 < Real.sqrt rho := by
      rw [← pullback.rhoRequested_eq]
      exact Real.sqrt_pos.mpr
        twoScale.first.publicSticky.coarse_extremal.delta_pos
    have hparentLowerReal :
        (first.1 : ℝ) - 6 ≤ (parent.1 : ℝ) := by
      have hmul :
          ((first.1 : ℝ) - 5) * Real.sqrt rho <
            ((parent.1 : ℝ) + 1) * Real.sqrt rho := by
        calc
          _ = (first.1 : ℝ) * Real.sqrt rho -
              5 * Real.sqrt rho := by ring
          _ ≤ witness first 0 - 5 * Real.sqrt rho := by
            linarith [hfirstMem.1]
          _ ≤ witness parent 0 := by
            linarith [(abs_le.mp hxClose).1]
          _ < ((parent.1 : ℝ) + 1) * Real.sqrt rho :=
            hparentMem.2.1
      have := lt_of_mul_lt_mul_right hmul hroot.le
      linarith
    have hparentUpperReal :
        (parent.1 : ℝ) ≤ (first.1 : ℝ) + 6 := by
      have hmul :
          (parent.1 : ℝ) * Real.sqrt rho <
            ((first.1 : ℝ) + 6) * Real.sqrt rho := by
        calc
          _ ≤ witness parent 0 := hparentMem.1
          _ ≤ witness first 0 + 5 * Real.sqrt rho := by
            linarith [(abs_le.mp hxClose).2]
          _ < ((first.1 : ℝ) + 1) * Real.sqrt rho +
              5 * Real.sqrt rho := by linarith [hfirstMem.2.1]
          _ = ((first.1 : ℝ) + 6) * Real.sqrt rho := by ring
      exact (lt_of_mul_lt_mul_right hmul hroot.le).le
    exact ⟨by exact_mod_cast hparentLowerReal,
      by exact_mod_cast hparentUpperReal⟩
  have himageSubset :
      fiber.image (fun parent => parent.1) ⊆
        Finset.Icc (first.1 - 6) (first.1 + 6) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨parent, hparent, rfl⟩
    exact Finset.mem_Icc.mpr (hindexRange parent hparent)
  have hparentHeight :
      ∀ parent ∈ block.jointParentCells,
        parent.2.2 = heightIndex.1.1 := by
    intro parent hparent
    rcases block.jointParent_has_source_cell hparent with
      ⟨cell, hcell, rfl⟩
    exact (pullback.mem_standardSqrtSlabRhoCells.mp
      (block.jointFixedBinRhoCells_subset_standard hcell)).2
  have hinjective :
      Set.InjOn (fun parent : WZ2PaperCellIndex => parent.1) fiber := by
    intro firstParent hfirst secondParent hsecond heq
    have hfirstY' := (Finset.mem_filter.mp hfirst).2
    have hsecondY' := (Finset.mem_filter.mp hsecond).2
    have hfirstParent' := (Finset.mem_filter.mp hfirst).1
    have hsecondParent' := (Finset.mem_filter.mp hsecond).1
    apply Prod.ext
    · exact heq
    · apply Prod.ext
      · exact hfirstY'.trans hsecondY'.symm
      · exact (hparentHeight firstParent hfirstParent').trans
          (hparentHeight secondParent hsecondParent').symm
  rw [← Finset.card_image_of_injOn hinjective]
  have hintervalCard :
      (Finset.Icc (first.1 - 6) (first.1 + 6)).card = 13 := by
    simp
    omega
  exact (Finset.card_le_card himageSubset).trans_eq hintervalCard

structure JointOneParentPerYData where
  parentWeight : WZ2PaperCellIndex → ENNReal := fun parent =>
    ∑ cell ∈ block.jointFixedBinRhoCells.filter fun cell =>
      pullback.standardSecondParent cell = parent,
        volume (block.jointCellSaturation cell)
  selection : PureWZ2FiniteWeightedParentYResidueData
    block.jointParentCells parentWeight
  selectedParents : Finset WZ2PaperCellIndex := selection.onePerY
  selectedParents_eq : selectedParents = selection.onePerY
  selectedParents_subset : selectedParents ⊆ block.jointParentCells
  selectedParents_nonempty : selectedParents.Nonempty
  selectedParents_y_injective :
    Set.InjOn (fun parent : WZ2PaperCellIndex => parent.2.1) selectedParents
  selectedCells : Finset WZ2PaperCellIndex :=
    block.jointFixedBinRhoCells.filter fun cell =>
      pullback.standardSecondParent cell ∈ selectedParents
  selectedCells_eq :
    selectedCells = block.jointFixedBinRhoCells.filter fun cell =>
      pullback.standardSecondParent cell ∈ selectedParents
  selectedCells_subset : selectedCells ⊆ block.jointFixedBinRhoCells
  selectedCells_nonempty : selectedCells.Nonempty
  selected_parent :
    ∀ cell ∈ selectedCells,
      pullback.standardSecondParent cell ∈ selectedParents
  saturatedUnion : Set Point3 :=
    ⋃ cell ∈ selectedCells, block.jointCellSaturation cell
  saturatedUnion_eq :
    saturatedUnion =
      ⋃ cell ∈ selectedCells, block.jointCellSaturation cell
  saturatedUnion_measurable : MeasurableSet saturatedUnion
  saturatedUnion_volume :
    volume saturatedUnion =
      ∑ cell ∈ selectedCells,
        volume (block.jointCellSaturation cell)
  volume_retention :
    volume block.jointSaturatedUnion ≤ 45 * volume saturatedUnion

theorem jointOneParentPerY :
    Nonempty block.JointOneParentPerYData := by
  let cellWeight : WZ2PaperCellIndex → ENNReal := fun cell =>
    volume (block.jointCellSaturation cell)
  let parentWeight : WZ2PaperCellIndex → ENNReal := fun parent =>
    ∑ cell ∈ block.jointFixedBinRhoCells.filter fun cell =>
      pullback.standardSecondParent cell = parent, cellWeight cell
  rcases pureWZ2_selectFiniteWeightedParentYResidue
      block.jointParentCells parentWeight block.jointParentCells_nonempty
      (fun y => (block.jointParent_y_fiber_card y).trans (by norm_num)) with
    ⟨selection⟩
  let selectedParents := selection.onePerY
  let selectedCells := block.jointFixedBinRhoCells.filter fun cell =>
    pullback.standardSecondParent cell ∈ selectedParents
  have hselectedCellsNonempty : selectedCells.Nonempty := by
    rcases selection.onePerY_nonempty with ⟨parent, hparent⟩
    have hparentAll := selection.onePerY_subset hparent
    rcases block.jointParent_has_source_cell hparentAll with
      ⟨cell, hcell, hparentCell⟩
    exact ⟨cell, Finset.mem_filter.mpr
      ⟨hcell, by simpa [selectedParents, hparentCell] using hparent⟩⟩
  have hallByParent :
      (∑ parent ∈ block.jointParentCells, parentWeight parent) =
        ∑ cell ∈ block.jointFixedBinRhoCells, cellWeight cell :=
    Finset.sum_fiberwise_of_maps_to
      (fun cell hcell => Finset.mem_image.mpr ⟨cell, hcell, rfl⟩)
      cellWeight
  have hselectedByParent :
      (∑ parent ∈ selectedParents, parentWeight parent) =
        ∑ cell ∈ selectedCells, cellWeight cell := by
    let finalMap : WZ2PaperCellIndex → WZ2PaperCellIndex :=
      pullback.standardSecondParent
    have hmaps :
        ∀ cell ∈ selectedCells, finalMap cell ∈ selectedParents := by
      intro cell hcell
      exact (Finset.mem_filter.mp hcell).2
    have hsum := Finset.sum_fiberwise_of_maps_to hmaps cellWeight
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro parent hparent
    dsimp only [parentWeight, finalMap]
    have hfilter :
        block.jointFixedBinRhoCells.filter
            (fun cell => pullback.standardSecondParent cell = parent) =
          selectedCells.filter
            (fun cell => pullback.standardSecondParent cell = parent) := by
      ext cell
      simp only [selectedCells, Finset.mem_filter]
      constructor
      · rintro ⟨hcell, hparentEq⟩
        exact ⟨⟨hcell, by rwa [hparentEq]⟩, hparentEq⟩
      · rintro ⟨⟨hcell, _hselectedParent⟩, hparentEq⟩
        exact ⟨hcell, hparentEq⟩
    rw [hfilter]
  let saturatedUnion :=
    ⋃ cell ∈ selectedCells, block.jointCellSaturation cell
  have hsaturatedMeas : MeasurableSet saturatedUnion :=
    MeasurableSet.biUnion selectedCells.finite_toSet.countable
      (fun cell _ =>
        measurableSet_wz1PaperGridCubeSameHeightSaturation
          rho cell (block.jointCellSource cell)
          (block.jointCellSource_measurable cell))
  have hsaturatedVolume :
      volume saturatedUnion =
        ∑ cell ∈ selectedCells, volume (block.jointCellSaturation cell) := by
    unfold saturatedUnion
    exact MeasureTheory.measure_biUnion_finset
      (fun first _ second _ hne =>
        (wz1PaperGridCube_disjoint hne).mono
          (wz1PaperGridCubeSameHeightSaturation_subset_cube
            rho first (block.jointCellSource first))
          (wz1PaperGridCubeSameHeightSaturation_subset_cube
            rho second (block.jointCellSource second)))
      (fun cell _ =>
        measurableSet_wz1PaperGridCubeSameHeightSaturation
          rho cell (block.jointCellSource cell)
          (block.jointCellSource_measurable cell))
  have hvolumeRetention :
      volume block.jointSaturatedUnion ≤ 45 * volume saturatedUnion := by
    calc
      volume block.jointSaturatedUnion =
          ∑ cell ∈ block.jointFixedBinRhoCells, cellWeight cell := by
        rw [block.jointSaturatedUnion_volume]
      _ = ∑ parent ∈ block.jointParentCells, parentWeight parent :=
        hallByParent.symm
      _ ≤ 45 * ∑ parent ∈ selectedParents, parentWeight parent := by
        simpa [selectedParents] using selection.onePerY_weight_retention
      _ = 45 * ∑ cell ∈ selectedCells, cellWeight cell := by
        rw [hselectedByParent]
      _ = 45 * volume saturatedUnion := by
        rw [hsaturatedVolume]
  exact ⟨{
    parentWeight := parentWeight
    selection := selection
    selectedParents := selectedParents
    selectedParents_eq := rfl
    selectedParents_subset := selection.onePerY_subset
    selectedParents_nonempty := selection.onePerY_nonempty
    selectedParents_y_injective := selection.onePerY_y_injective
    selectedCells := selectedCells
    selectedCells_eq := rfl
    selectedCells_subset := Finset.filter_subset _ _
    selectedCells_nonempty := hselectedCellsNonempty
    selected_parent := fun _ hcell => (Finset.mem_filter.mp hcell).2
    saturatedUnion := saturatedUnion
    saturatedUnion_eq := rfl
    saturatedUnion_measurable := hsaturatedMeas
    saturatedUnion_volume := hsaturatedVolume
    volume_retention := hvolumeRetention
  }⟩

end JointHeightCommonBinData

end PureWZ2Node05V4RichSourceVolumePopularHeightData

end Kakeya.Assouad

end
