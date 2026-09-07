import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSecondCall
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05IndexedIncidenceRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Section6CoverAdapter
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PaperCubeSliceArea
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSubfamilyZeroExtension

/-!
# Direct-rich two-scale cell pullback after both calls

The second rich call has already been run, definitionally, on
`first.finalCoarseFamily` and `first.finalCoarseShading`.  Only afterwards do
we synchronize the three paper levels spatially: the active `rho`-cells of
the second refined shading are imposed on the first `rho` shading, the first
fine shading, and its zero extension to the original `delta` source.

Thus `rawFirstT6Shading` is the literal second-call input, while
`postFirstT6Shading` and `postSourceShading` are post-two-call subshadings.
The first terminal certificate's `fine_cell_nested` proves that the source
restriction retains whole `delta`-cells.  Indexed incidence is kept as its
actual cell-indexed quantity; no union volume is identified with it.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2Node05V4RichSecondCallData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current :
      PureWZ2ReentrantGrainSource
        sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}

/-- Public first-call output. -/
abbrev firstSticky
    (data : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested) :=
  data.first.publicSticky

/-- Public second-call output. -/
abbrev secondSticky
    (data : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested) :=
  data.second.data

abbrev coarse
    (data : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested) :=
  data.firstSticky

abbrev fine
    (data : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested) :=
  data.secondSticky

abbrev rhoRequestedScale
    (_data : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested) :=
  rhoRequested

abbrev sqrtRequestedScale
    (_data : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested) :=
  sqrtRequested

end PureWZ2Node05V4RichSecondCallData

/--
Post-two-call synchronized pullback.  No family or witness in this record is
selected independently: all post shadings are literal restrictions by the
second refined shading's active `rho`-cells.
-/
structure PureWZ2Node05V4RichTwoScaleCellPullbackData
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta rho : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current :
      PureWZ2ReentrantGrainSource
        sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    (twoScale :
      PureWZ2Node05V4RichSecondCallData
        schedule current rhoRequested inputLossLe sqrtRequested) where
  rhoRequested_eq : rhoRequested.1 = rho
  rawFirstT6Shading :
    WZ1PaperTubeShading twoScale.first.finalCoarseFamily :=
      twoScale.first.finalCoarseShading
  rawFirstT6Shading_eq :
    rawFirstT6Shading = twoScale.first.finalCoarseShading
  second_input_shading_eq :
    twoScale.secondInputShading = rawFirstT6Shading
  selectedCells : Finset WZ2PaperCellIndex
  selectedCells_eq :
    selectedCells =
      wz1PaperActiveCells twoScale.secondRefinedFineShading
        twoScale.first.publicSticky.coarse_extremal.delta_pos
  selectedCells_subset_first :
    selectedCells ⊆ twoScale.first.fourDegreeBalancedCover.activeCells
  retainedRegion : Set Point3
  retainedRegion_eq :
    retainedRegion =
      pureWZ2Node05RetainedCellRegion rho selectedCells
  retainedRegion_measurable : MeasurableSet retainedRegion
  postFirstFineShading :
    WZ1PaperTubeShading twoScale.first.finalFineFamily
  postFirstFineShading_eq :
    postFirstFineShading =
      pureWZ2Node05RestrictToCells (rho := rho)
        twoScale.first.refinedFineShading selectedCells
  postFirstT6Shading :
    WZ1PaperTubeShading twoScale.first.finalCoarseFamily
  postFirstT6Shading_eq :
    postFirstT6Shading =
      pureWZ2Node05RestrictToCells (rho := rho)
        rawFirstT6Shading selectedCells
  postFirstFine_sub_raw :
    PureWZ2PaperIsSubshading
      postFirstFineShading twoScale.first.refinedFineShading
  postFirstT6_sub_raw :
    PureWZ2PaperIsSubshading postFirstT6Shading rawFirstT6Shading
  secondRefined_sub_rawFirstT6 :
    ∀ index point,
      point ∈ twoScale.secondRefinedFineShading.carrier index →
        point ∈ rawFirstT6Shading.carrier
          (twoScale.secondSticky.selected.embedding index)
  firstPostBalanced :
    PureWZ2BalancedCoverData
      twoScale.first.finalCover postFirstFineShading postFirstT6Shading
  firstPostBalanced_activeCells :
    firstPostBalanced.activeCells = selectedCells
  firstPost_cellMass_eq :
    firstPostBalanced.cellMass =
      twoScale.first.fourDegreeBalancedCover.cellMass
  firstPost_fine_cell_nested :
    ∀ source point,
      point ∈ postFirstFineShading.carrier source →
        ∃ cell ∈ firstPostBalanced.activeCells,
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperGridCube rhoRequested.1 cell
  zeroExtension :
    WZ2PaperSubfamilyZeroExtensionData
      twoScale.first.publicSticky.selected postFirstFineShading
  postSourceShading : WZ1PaperTubeShading current.grain.family
  postSourceShading_eq :
    postSourceShading = zeroExtension.ambientShading
  postSource_sub_original :
    PureWZ2PaperIsSubshading postSourceShading current.grain.shading
  postSource_whole_delta_cells :
    WZ1PaperIsCubicalShading postSourceShading
  postSource_union_eq :
    postSourceShading.union =
      zeroExtension.ambientShading.union
  cell_union_mass :
    ∀ cell ∈ selectedCells,
      volume
          (postSourceShading.union ∩ wz1PaperGridCube rho cell) =
        firstPostBalanced.cellMass
  cell_incidence_mass :
    ∀ cell ∈ selectedCells,
      (∑ sourceIndex : Fin current.grain.family.card,
        volume
          (postSourceShading.carrier sourceIndex ∩
            wz1PaperGridCube rho cell)) =
        wz2PaperCellIncidenceMass
          (rho := rho) postFirstFineShading cell
  source_volume_eq :
    volume postSourceShading.union =
      (selectedCells.card : ENNReal) * firstPostBalanced.cellMass
  source_mass_eq :
    postSourceShading.mass =
      ∑ cell ∈ selectedCells,
        wz2PaperCellIncidenceMass
          (rho := rho) postFirstFineShading cell
  selected_count_mul_rho_cube_volume :
    (selectedCells.card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) =
      volume twoScale.secondRefinedFineShading.union

namespace PureWZ2Node05V4RichTwoScaleCellPullbackData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta rho : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current :
      PureWZ2ReentrantGrainSource
        sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale :
      PureWZ2Node05V4RichSecondCallData
        schedule current rhoRequested inputLossLe sqrtRequested}

theorem sqrtRequested_eq
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale) :
    sqrtRequested.1 = Real.sqrt rho := by
  rw [twoScale.sqrtRequested_eq, pullback.rhoRequested_eq]

abbrev shading
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale) :=
  pullback.postSourceShading

theorem subshading
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale) :
    PureWZ2PaperIsSubshading pullback.shading current.grain.shading :=
  pullback.postSource_sub_original

theorem whole_cells
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale) :
    WZ1PaperIsCubicalShading pullback.shading :=
  pullback.postSource_whole_delta_cells

/-- Every active `delta` cell of the zero-extended post-source is contained
in one of the retained first-cover `rho` cells.  This is the literal nesting
receipt used by the same-height horizontal saturation. -/
theorem source_fine_cell_nested
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (source point)
    (hpoint : point ∈ pullback.shading.carrier source) :
    ∃ cell ∈ pullback.selectedCells,
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
        wz1PaperGridCube rho cell := by
  change point ∈ pullback.postSourceShading.carrier source at hpoint
  rw [pullback.postSourceShading_eq] at hpoint
  rcases pullback.zeroExtension.carrier_support source point hpoint with
    ⟨selectedIndex, _hsource, hselected⟩
  rcases pullback.firstPost_fine_cell_nested selectedIndex point hselected with
    ⟨cell, hcell, hnested⟩
  exact ⟨cell, by simpa only [pullback.firstPostBalanced_activeCells] using hcell,
    by simpa only [pullback.rhoRequested_eq] using hnested⟩

theorem volume_eq
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale) :
    volume pullback.shading.union =
      (pullback.selectedCells.card : ENNReal) *
        pullback.firstPostBalanced.cellMass :=
  pullback.source_volume_eq

/--
Exact cross-stage volume identity after both rich calls.  The common number
of retained side-`rho` cells is kept until it cancels; no lower bound for the
second refined union or either balanced cell mass is assumed here.
-/
theorem source_volume_mul_rho_cube_eq
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale) :
    volume pullback.shading.union *
          volume (wz1PaperGridCube rho (0, 0, 0)) =
      volume twoScale.secondRefinedFineShading.union *
        pullback.firstPostBalanced.cellMass := by
  rw [pullback.source_volume_eq,
    ← pullback.selected_count_mul_rho_cube_volume]
  ring

/-- One active cell already contributes the full second balanced-cell mass to
the exact second refined union. -/
theorem second_cellMass_le_refined_volume
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale) :
    twoScale.secondBalancedCover.cellMass ≤
      volume twoScale.secondRefinedFineShading.union := by
  have hnonempty : twoScale.secondBalancedCover.activeCells.Nonempty := by
    rcases twoScale.second.terminal.packetCells_nonempty with ⟨edge, hedge⟩
    rw [twoScale.second.terminal.packetCells_eq] at hedge
    rcases (Finset.mem_filter.mp hedge).2 with ⟨source, hsource⟩
    have hwhole := (Finset.mem_filter.mp hsource).2
    let point := cellCorner rhoRequested.1 edge.2
    have hpointCell :
        point ∈ wz1PaperGridCube rhoRequested.1 edge.2 :=
      cellCorner_mem_gridCube
        twoScale.first.publicSticky.coarse_extremal.delta_pos edge.2
    have hpointFine :
        point ∈ twoScale.secondRefinedFineShading.carrier source :=
      hwhole hpointCell
    rcases twoScale.second.terminal.fine_cell_nested
        source point hpointFine with ⟨coarseCell, hcoarseCell, _⟩
    exact ⟨coarseCell, hcoarseCell⟩
  have hcard :
      (1 : ENNReal) ≤ twoScale.secondBalancedCover.activeCells.card := by
    exact_mod_cast hnonempty.card_pos
  calc
    twoScale.secondBalancedCover.cellMass =
        1 * twoScale.secondBalancedCover.cellMass := by simp
    _ ≤ (twoScale.secondBalancedCover.activeCells.card : ENNReal) *
          twoScale.secondBalancedCover.cellMass := by gcongr
    _ = volume twoScale.secondRefinedFineShading.union := by
      exact twoScale.secondBalancedCover.fine_union_volume.symm

/-- The two direct rich cell-mass floors combine on the exact synchronized
source.  This is the division-free quantitative input for both P3 budgets. -/
theorem rich_cellMass_power_product_le_source_volume_mul_cube
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale) :
    (Kakeya.realRpowENN rhoRequested.1 3 *
        Kakeya.realRpowENN (delta / rhoRequested.1)
          (sigma + 2 * twoScale.first.rich.terminalLoss)) *
      (Kakeya.realRpowENN sqrtRequested.1 3 *
        Kakeya.realRpowENN (rhoRequested.1 / sqrtRequested.1)
          (sigma + 2 * twoScale.second.terminalLoss)) ≤
        volume pullback.shading.union *
          volume (wz1PaperGridCube rho (0, 0, 0)) := by
  calc
    (Kakeya.realRpowENN rhoRequested.1 3 *
          Kakeya.realRpowENN (delta / rhoRequested.1)
            (sigma + 2 * twoScale.first.rich.terminalLoss)) *
        (Kakeya.realRpowENN sqrtRequested.1 3 *
          Kakeya.realRpowENN (rhoRequested.1 / sqrtRequested.1)
            (sigma + 2 * twoScale.second.terminalLoss)) ≤
      pullback.firstPostBalanced.cellMass *
        twoScale.secondBalancedCover.cellMass := by
          gcongr
          · rw [pullback.firstPost_cellMass_eq]
            exact twoScale.first_cellMass_power_lower
          · exact twoScale.second_cellMass_power_lower
    _ ≤ pullback.firstPostBalanced.cellMass *
          volume twoScale.secondRefinedFineShading.union := by
      exact mul_le_mul_left' (pullback.second_cellMass_le_refined_volume) _
    _ = volume pullback.shading.union *
          volume (wz1PaperGridCube rho (0, 0, 0)) := by
      rw [pullback.source_volume_mul_rho_cube_eq]
      ring

/-- Relative volume floor for the exact post-two-call source pullback.  The
second-call union-volume retention supplies all active rho cells, the first
balanced cell supplies their common source mass, and the physical rho-cube
volume cancels. -/
theorem source_volume_relative_lower
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (hrhoSmall : rhoRequested.1 ≤ 1 / 12) :
    wz2PaperPureRefinementFraction rhoRequested.1 61 *
          Kakeya.realRpowENN rhoRequested.1
            (sigma + 2 * schedule.firstOutputLoss) *
          Kakeya.realRpowENN (delta / rhoRequested.1)
            (sigma + 2 * twoScale.first.rich.terminalLoss) ≤
      (twoScale.first.fourDegreeReceipts.regularity : ENNReal) *
        volume pullback.shading.union := by
  let cubeVolume := volume (wz1PaperGridCube rho (0, 0, 0))
  let secondFloor :=
    wz2PaperPureRefinementFraction rhoRequested.1 61 *
      Kakeya.realRpowENN rhoRequested.1
        (sigma + 2 * schedule.firstOutputLoss)
  let firstRatio :=
    Kakeya.realRpowENN (delta / rhoRequested.1)
      (sigma + 2 * twoScale.first.rich.terminalLoss)
  let firstCellFloor :=
    Kakeya.realRpowENN rhoRequested.1 3 * firstRatio
  let regularity : ENNReal := twoScale.first.fourDegreeReceipts.regularity
  have hsecond :
      secondFloor ≤ regularity *
        volume twoScale.secondRefinedFineShading.union := by
    simpa only [secondFloor, regularity] using
      twoScale.second_refined_volume_lower hrhoSmall
  have hfirst : firstCellFloor ≤ pullback.firstPostBalanced.cellMass := by
    dsimp only [firstCellFloor, firstRatio]
    rw [pullback.firstPost_cellMass_eq]
    exact twoScale.first_cellMass_power_lower
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hcube :
      cubeVolume = Kakeya.realRpowENN rhoRequested.1 3 := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    simp [Kakeya.realRpowENN, pullback.rhoRequested_eq, Real.rpow_natCast]
  have hcubePos : 0 < cubeVolume := by
    dsimp only [cubeVolume]
    exact wz1PaperGridCube_volume_pos hrho (0, 0, 0)
  have hcubeTop : cubeVolume ≠ ⊤ := by
    dsimp only [cubeVolume]
    exact wz1PaperGridCube_volume_ne_top hrho (0, 0, 0)
  apply (ENNReal.mul_le_mul_iff_right hcubePos.ne' hcubeTop).mp
  calc
    cubeVolume * (secondFloor * firstRatio) =
        secondFloor * firstCellFloor := by rw [hcube]; ring
    _ ≤ (regularity * volume twoScale.secondRefinedFineShading.union) *
          pullback.firstPostBalanced.cellMass :=
      mul_le_mul hsecond hfirst (by positivity) (by positivity)
    _ = regularity * (volume pullback.shading.union * cubeVolume) := by
      rw [pullback.source_volume_mul_rho_cube_eq]
      ring
    _ = cubeVolume * (regularity * volume pullback.shading.union) := by ring

/-- Exact volume cross-identity for the synchronized two-call pullback.  This
is the V4 analogue of the volume part of `balanced_mass_cross`: both sides
retain the same first-cover and second-cover active-cell counts.  Indexed mass
is deliberately not identified with volume here. -/
theorem balanced_volume_cross
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale) :
    volume pullback.shading.union *
          volume twoScale.first.finalCoarseShading.union =
      volume twoScale.first.refinedFineShading.union *
        volume twoScale.secondRefinedFineShading.union := by
  have hrhoRequested : 0 < rhoRequested.1 :=
    twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hfirstFine :=
    twoScale.first.fourDegreeBalancedCover.fine_union_volume
  have hfirstCoarse :=
    twoScale.first.fourDegreeBalancedCover.toWZ1PaperBalancedCoverData
      |>.coarse_union_volume hrhoRequested
  rw [pullback.source_volume_eq, hfirstFine, hfirstCoarse,
    ← pullback.selected_count_mul_rho_cube_volume]
  rw [pullback.firstPost_cellMass_eq]
  simp only [PureWZ2BalancedCoverData.toWZ1PaperBalancedCoverData_activeCells,
    pullback.rhoRequested_eq]
  ring

theorem mass_eq
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale) :
    pullback.shading.mass =
      ∑ cell ∈ pullback.selectedCells,
        wz2PaperCellIncidenceMass
          (rho := rho) pullback.postFirstFineShading cell :=
  pullback.source_mass_eq

/-- Construct the post-two-call synchronized pullback. -/
theorem nonempty
    (twoScale :
      PureWZ2Node05V4RichSecondCallData
        schedule current rhoRequested inputLossLe sqrtRequested)
    (rhoEq : rhoRequested.1 = rho) :
    Nonempty
      (PureWZ2Node05V4RichTwoScaleCellPullbackData
        (rho := rho) twoScale) := by
  have hrhoRequested : 0 < rhoRequested.1 :=
    twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hrho : 0 < rho := by simpa only [← rhoEq] using hrhoRequested
  let selectedCells :=
    wz1PaperActiveCells twoScale.secondRefinedFineShading hrhoRequested
  let retainedRegion :=
    pureWZ2Node05RetainedCellRegion rho selectedCells
  have hregionMeasurable : MeasurableSet retainedRegion := by
    exact pureWZ2Node05RetainedCellRegion_measurable rho selectedCells
  have hselectedSubset :
      selectedCells ⊆
        twoScale.first.fourDegreeBalancedCover.activeCells := by
    intro cell hcell
    rcases
        ((mem_wz1PaperActiveCells twoScale.secondRefinedFineShading
          hrhoRequested cell).mp hcell).2 with
      ⟨point, ⟨index, hpointSecond⟩, hpointCell⟩
    have hpointFirst :
        point ∈ twoScale.first.finalCoarseShading.union :=
      ⟨twoScale.secondSticky.selected.embedding index,
        twoScale.secondSticky.subshading index hpointSecond⟩
    rw [twoScale.first.fourDegreeBalancedCover.coarse_union_eq] at hpointFirst
    rcases Set.mem_iUnion₂.mp hpointFirst with
      ⟨firstCell, hfirstCell, hpointFirstCell⟩
    have hcellEq : firstCell = cell :=
      ((mem_wz1PaperGridCube rhoRequested.1 firstCell point).mp
        hpointFirstCell).symm.trans
      ((mem_wz1PaperGridCube rhoRequested.1 cell point).mp hpointCell)
    rwa [hcellEq] at hfirstCell
  let postFirstFineShading :=
    pureWZ2Node05RestrictToCells (rho := rho)
      twoScale.first.refinedFineShading selectedCells
  let postFirstT6Shading :=
    pureWZ2Node05RestrictToCells (rho := rho)
      twoScale.first.finalCoarseShading selectedCells
  have hpostFineSub :
      PureWZ2PaperIsSubshading postFirstFineShading
        twoScale.first.refinedFineShading :=
    fun _ _ hpoint => hpoint.1
  have hpostCoarseSub :
      PureWZ2PaperIsSubshading postFirstT6Shading
        twoScale.first.finalCoarseShading :=
    fun _ _ hpoint => hpoint.1
  have hcoarseUnion :
      postFirstT6Shading.union = retainedRegion := by
    rw [pureWZ2Node05RestrictToCells_union]
    apply Set.inter_eq_right.mpr
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨cell, hcell, hpointCell⟩
    rw [twoScale.first.fourDegreeBalancedCover.coarse_union_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨cell, hselectedSubset hcell, by
        simpa only [← rhoEq] using hpointCell⟩
  have hcoarseCubical : WZ1PaperIsCubicalShading postFirstT6Shading := by
    intro index point hpoint other hother
    refine ⟨twoScale.first.fourDegreeBalancedCover.coarse_cubical
      index point hpoint.1 hother, ?_⟩
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨cell, hcell, hpointCell⟩
    have hpointIndex : wz1PaperGridIndex rho point = cell :=
      (mem_wz1PaperGridCube rho cell point).mp hpointCell
    have hpointIndexRequested :
        wz1PaperGridIndex rhoRequested.1 point = cell := by
      simpa only [rhoEq] using hpointIndex
    have hotherCellRequested :
        other ∈ wz1PaperGridCube rhoRequested.1 cell := by
      rw [← hpointIndexRequested]
      exact hother
    have hotherCell :
        other ∈ wz1PaperGridCube rho cell := by
      simpa only [← rhoEq] using hotherCellRequested
    exact Set.mem_iUnion₂.mpr
      ⟨cell, hcell, hotherCell⟩
  have hpointCompatibility :
      ∀ source parent,
        WZ1PaperTubeCovers
            (twoScale.first.finalFineFamily.tube source)
            (twoScale.first.finalCoarseFamily.tube parent) →
          ∀ point, point ∈ postFirstFineShading.carrier source →
            point ∈ postFirstT6Shading.carrier parent := by
    intro source parent hcovered point hpoint
    exact
      ⟨twoScale.first.fourDegreeBalancedCover.point_compatibility
          source parent hcovered point hpoint.1,
        hpoint.2⟩
  have hfineCellMass :
      ∀ cell ∈ selectedCells,
        volume (postFirstFineShading.union ∩ wz1PaperGridCube rho cell) =
          twoScale.first.fourDegreeBalancedCover.cellMass := by
    intro cell hcell
    rw [pureWZ2Node05RestrictToCells_union]
    have hinter :
        (twoScale.first.refinedFineShading.union ∩ retainedRegion) ∩
            wz1PaperGridCube rho cell =
          twoScale.first.refinedFineShading.union ∩
            wz1PaperGridCube rho cell := by
      ext point
      constructor
      · rintro ⟨⟨hsource, _⟩, hpointCell⟩
        exact ⟨hsource, hpointCell⟩
      · rintro ⟨hsource, hpointCell⟩
        exact
          ⟨⟨hsource, Set.mem_iUnion₂.mpr
              ⟨cell, hcell, hpointCell⟩⟩,
            hpointCell⟩
    rw [hinter]
    simpa only [← rhoEq] using
      twoScale.first.fourDegreeBalancedCover.fine_cell_mass
        cell (hselectedSubset hcell)
  let firstPostBalanced :
      PureWZ2BalancedCoverData
        twoScale.first.finalCover postFirstFineShading postFirstT6Shading := {
    point_compatibility := hpointCompatibility
    coarse_cubical := hcoarseCubical
    activeCells := selectedCells
    coarse_union_eq := by
      simpa only [retainedRegion, pureWZ2Node05RetainedCellRegion,
        ← rhoEq] using hcoarseUnion
    cellMass := twoScale.first.fourDegreeBalancedCover.cellMass
    cellMass_pos :=
      twoScale.first.fourDegreeBalancedCover.cellMass_pos
    cellMass_ne_top :=
      twoScale.first.fourDegreeBalancedCover.cellMass_ne_top
    fine_cell_mass := by
      intro cell hcell
      simpa only [rhoEq] using hfineCellMass cell hcell
  }
  have hpostNested :
      ∀ source point,
        point ∈ postFirstFineShading.carrier source →
          ∃ cell ∈ firstPostBalanced.activeCells,
            wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
              wz1PaperGridCube rhoRequested.1 cell := by
    intro source point hpoint
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨retainedCell, hretainedCell, hpointRetainedCell⟩
    rcases twoScale.first.fourDegreeReceipts.fine_cell_nested
        source point hpoint.1 with
      ⟨rawCell, _hrawCell, hnested⟩
    have hpointFine :
        point ∈ wz1PaperGridCube delta (wz1PaperGridIndex delta point) :=
      (mem_wz1PaperGridCube delta _ point).mpr rfl
    have hpointRaw := hnested hpointFine
    have hcellEq : rawCell = retainedCell :=
      ((mem_wz1PaperGridCube rhoRequested.1 rawCell point).mp
        hpointRaw).symm.trans
      ((mem_wz1PaperGridCube rhoRequested.1 retainedCell point).mp
        (by simpa only [rhoEq] using hpointRetainedCell))
    refine ⟨retainedCell, hretainedCell, ?_⟩
    simpa only [← hcellEq] using hnested
  have hpostFineWhole :
      WZ1PaperIsCubicalShading postFirstFineShading := by
    intro source point hpoint other hother
    refine
      ⟨twoScale.first.fourDegreeReceipts.fine_cubical
          source point hpoint.1 hother,
        ?_⟩
    rcases hpostNested source point hpoint with
      ⟨cell, hcell, hnested⟩
    exact Set.mem_iUnion₂.mpr
      ⟨cell, by simpa only [firstPostBalanced] using hcell,
        by simpa only [rhoEq] using hnested hother⟩
  rcases wz2_paper_subfamily_zero_extension
      twoScale.first.publicSticky.selected postFirstFineShading with
    ⟨zeroExtension⟩
  let postSourceShading := zeroExtension.ambientShading
  have hpostSourceSub :
      PureWZ2PaperIsSubshading
        postSourceShading current.grain.shading := by
    intro sourceIndex point hpoint
    rcases zeroExtension.carrier_support sourceIndex point hpoint with
      ⟨selectedIndex, heq, hselected⟩
    subst sourceIndex
    exact twoScale.first.publicSticky.subshading selectedIndex
      (hpostFineSub selectedIndex hselected)
  have hpostWhole : WZ1PaperIsCubicalShading postSourceShading := by
    exact zeroExtension.cubical hpostFineWhole
  have hcellUnionMass :
      ∀ cell ∈ selectedCells,
        volume
            (postSourceShading.union ∩ wz1PaperGridCube rho cell) =
          firstPostBalanced.cellMass := by
    intro cell hcell
    rw [zeroExtension.union_eq]
    simpa [postSourceShading, firstPostBalanced] using
      hfineCellMass cell hcell
  have hcellIncidence :
      ∀ cell ∈ selectedCells,
        (∑ sourceIndex : Fin current.grain.family.card,
          volume
            (postSourceShading.carrier sourceIndex ∩
              wz1PaperGridCube rho cell)) =
          wz2PaperCellIncidenceMass
            (rho := rho) postFirstFineShading cell := by
    intro cell _hcell
    unfold wz2PaperCellIncidenceMass
    let supported : Finset (Fin current.grain.family.card) :=
      Finset.univ.map twoScale.first.publicSticky.selected.embedding
    calc
      (∑ sourceIndex : Fin current.grain.family.card,
          volume
            (postSourceShading.carrier sourceIndex ∩
              wz1PaperGridCube rho cell)) =
          ∑ sourceIndex ∈ supported,
            volume
              (postSourceShading.carrier sourceIndex ∩
                wz1PaperGridCube rho cell) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro sourceIndex _ hnot
        have hcarrier : postSourceShading.carrier sourceIndex = ∅ := by
          apply Set.not_nonempty_iff_eq_empty.mp
          rintro ⟨point, hpoint⟩
          rcases zeroExtension.carrier_support sourceIndex point hpoint with
            ⟨selectedIndex, heq, _⟩
          exact hnot (Finset.mem_map.mpr
            ⟨selectedIndex, Finset.mem_univ _, heq⟩)
        rw [hcarrier]
        simp
      _ =
          ∑ selectedIndex : Fin twoScale.first.finalFineFamily.card,
            volume
              (postFirstFineShading.carrier selectedIndex ∩
                wz1PaperGridCube rho cell) := by
        rw [Finset.sum_map]
        apply Finset.sum_congr rfl
        intro selectedIndex _
        rw [zeroExtension.carrier_embedding selectedIndex]
  have hsourceVolume :
      volume postSourceShading.union =
        (selectedCells.card : ENNReal) * firstPostBalanced.cellMass := by
    rw [zeroExtension.union_eq]
    have hpartition := firstPostBalanced.fine_union_volume
    simpa [postSourceShading] using hpartition
  have hsourceMass :
      postSourceShading.mass =
        ∑ cell ∈ selectedCells,
          wz2PaperCellIncidenceMass
            (rho := rho) postFirstFineShading cell := by
    rw [zeroExtension.mass_eq]
    simpa only [rhoEq] using
      firstPostBalanced.fineShading_mass_eq_sum_cellIncidence hpostNested
  have hselectedCount :
      (selectedCells.card : ENNReal) *
          volume (wz1PaperGridCube rho (0, 0, 0)) =
        volume twoScale.secondRefinedFineShading.union := by
    have hunion :=
      twoScale.second.terminal.fine_cubical.union_eq_activeCells hrhoRequested
    calc
      (selectedCells.card : ENNReal) *
            volume (wz1PaperGridCube rho (0, 0, 0)) =
          volume (⋃ cell ∈ selectedCells, wz1PaperGridCube rho cell) :=
        (wz1PaperGridCube_volume_biUnion hrho selectedCells).symm
      _ = volume twoScale.secondRefinedFineShading.union := by
        rw [← rhoEq]
        exact congrArg volume hunion.symm
  exact ⟨{
    rhoRequested_eq := rhoEq
    rawFirstT6Shading := twoScale.first.finalCoarseShading
    rawFirstT6Shading_eq := rfl
    second_input_shading_eq := rfl
    selectedCells := selectedCells
    selectedCells_eq := rfl
    selectedCells_subset_first := hselectedSubset
    retainedRegion := retainedRegion
    retainedRegion_eq := rfl
    retainedRegion_measurable := hregionMeasurable
    postFirstFineShading := postFirstFineShading
    postFirstFineShading_eq := rfl
    postFirstT6Shading := postFirstT6Shading
    postFirstT6Shading_eq := rfl
    postFirstFine_sub_raw := hpostFineSub
    postFirstT6_sub_raw := hpostCoarseSub
    secondRefined_sub_rawFirstT6 := by
      intro index point hpoint
      exact twoScale.secondSticky.subshading index hpoint
    firstPostBalanced := firstPostBalanced
    firstPostBalanced_activeCells := rfl
    firstPost_cellMass_eq := rfl
    firstPost_fine_cell_nested := hpostNested
    zeroExtension := zeroExtension
    postSourceShading := postSourceShading
    postSourceShading_eq := rfl
    postSource_sub_original := hpostSourceSub
    postSource_whole_delta_cells := hpostWhole
    postSource_union_eq := rfl
    cell_union_mass := hcellUnionMass
    cell_incidence_mass := hcellIncidence
    source_volume_eq := hsourceVolume
    source_mass_eq := hsourceMass
    selected_count_mul_rho_cube_volume := hselectedCount
  }⟩

section SpatialParents

variable
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)

/-- Actual source region over a finite family of retained `rho`-cells. -/
def selectedRhoCellsSourceRegion
    (cells : Finset WZ2PaperCellIndex) : Set Point3 :=
  pullback.shading.union ∩ pureWZ2Node05RetainedCellRegion rho cells

/-- The corresponding region in the second refined `rho` shading. -/
def selectedRhoCellsCoarseRegion
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (cells : Finset WZ2PaperCellIndex) : Set Point3 :=
  twoScale.secondRefinedFineShading.union ∩
    pureWZ2Node05RetainedCellRegion rho cells

theorem selectedRhoCellsSourceRegion_volume
    (cells : Finset WZ2PaperCellIndex)
    (hsubset : cells ⊆ pullback.selectedCells) :
    volume (pullback.selectedRhoCellsSourceRegion cells) =
      (cells.card : ENNReal) * pullback.firstPostBalanced.cellMass := by
  have hpartition :
      pullback.selectedRhoCellsSourceRegion cells =
        ⋃ cell ∈ cells,
          pullback.shading.union ∩ wz1PaperGridCube rho cell := by
    ext point
    simp [selectedRhoCellsSourceRegion,
      pureWZ2Node05RetainedCellRegion]
  rw [hpartition]
  rw [MeasureTheory.measure_biUnion_finset]
  · calc
      (∑ cell ∈ cells,
          volume
            (pullback.shading.union ∩ wz1PaperGridCube rho cell)) =
          ∑ _cell ∈ cells, pullback.firstPostBalanced.cellMass := by
        apply Finset.sum_congr rfl
        intro cell hcell
        exact pullback.cell_union_mass cell (hsubset hcell)
      _ = (cells.card : ENNReal) *
          pullback.firstPostBalanced.cellMass := by
        simp [Finset.sum_const]
  · intro first _ second _ hne
    exact (wz1PaperGridCube_disjoint hne).mono
      Set.inter_subset_right Set.inter_subset_right
  · intro cell _
    exact (measurableSet_shading_union _).inter
      (wz1PaperGridCube_measurable cell)

theorem selectedRhoCellsCoarseRegion_volume
    (cells : Finset WZ2PaperCellIndex)
    (hsubset : cells ⊆ pullback.selectedCells) :
    volume (pullback.selectedRhoCellsCoarseRegion cells) =
      (cells.card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  have hinter :
      pullback.selectedRhoCellsCoarseRegion cells =
        pureWZ2Node05RetainedCellRegion rho cells := by
    apply Set.inter_eq_right.mpr
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨cell, hcell, hpointCell⟩
    have hactive : cell ∈ pullback.selectedCells := hsubset hcell
    have hwhole :=
      twoScale.second.terminal.fine_cubical.inter_activeCell_eq
        (by simpa only [← pullback.rhoRequested_eq] using
          twoScale.first.publicSticky.coarse_extremal.delta_pos)
        (by simpa only [pullback.selectedCells_eq] using hactive)
    have : point ∈
        twoScale.secondRefinedFineShading.union ∩
          wz1PaperGridCube rhoRequested.1 cell := by
      rw [hwhole]
      simpa only [← pullback.rhoRequested_eq] using hpointCell
    exact this.1
  rw [hinter]
  simpa only [pureWZ2Node05RetainedCellRegion] using
    wz1PaperGridCube_volume_biUnion
      (by
        rw [← pullback.rhoRequested_eq]
        exact twoScale.first.publicSticky.coarse_extremal.delta_pos)
      cells

theorem selectedRhoCells_source_coarse_cross
    (cells : Finset WZ2PaperCellIndex)
    (hsubset : cells ⊆ pullback.selectedCells) :
    volume (pullback.selectedRhoCellsSourceRegion cells) *
          volume (wz1PaperGridCube rho (0, 0, 0)) =
      volume (pullback.selectedRhoCellsCoarseRegion cells) *
          pullback.firstPostBalanced.cellMass := by
  rw [pullback.selectedRhoCellsSourceRegion_volume cells hsubset,
    pullback.selectedRhoCellsCoarseRegion_volume cells hsubset]
  ring

private theorem exists_standardSecondParent
    {cell : WZ2PaperCellIndex}
    (hcell : cell ∈ pullback.selectedCells) :
    ∃ parent ∈ twoScale.second.terminal.balanced.activeCells,
      wz1PaperGridCube rho cell ⊆
        wz1PaperGridCube sqrtRequested.1 parent := by
  have hactive :
      cell ∈ wz1PaperActiveCells twoScale.secondRefinedFineShading
        twoScale.first.publicSticky.coarse_extremal.delta_pos := by
    simpa only [pullback.selectedCells_eq] using hcell
  rw [mem_wz1PaperActiveCells] at hactive
  rcases hactive.2 with
    ⟨point, ⟨index, hpoint⟩, hpointCell⟩
  rcases twoScale.second.terminal.fine_cell_nested index point hpoint with
    ⟨parent, hparent, hnested⟩
  refine ⟨parent, hparent, ?_⟩
  have hindex :
      wz1PaperGridIndex rhoRequested.1 point = cell :=
    (mem_wz1PaperGridCube rhoRequested.1 cell point).mp hpointCell
  rw [hindex] at hnested
  simpa only [← pullback.rhoRequested_eq] using hnested

/-- Canonical genuine second-cover parent of one selected `rho`-cell. -/
noncomputable def standardSecondParent
    (cell : WZ2PaperCellIndex) : WZ2PaperCellIndex :=
  if hcell : cell ∈ pullback.selectedCells then
    Classical.choose (pullback.exists_standardSecondParent hcell)
  else (0, 0, 0)

theorem standardSecondParent_active
    {cell : WZ2PaperCellIndex}
    (hcell : cell ∈ pullback.selectedCells) :
    pullback.standardSecondParent cell ∈
      twoScale.second.terminal.balanced.activeCells := by
  rw [standardSecondParent, dif_pos hcell]
  exact
    (Classical.choose_spec
      (pullback.exists_standardSecondParent hcell)).1

theorem standardSecondParent_cell_subset
    {cell : WZ2PaperCellIndex}
    (hcell : cell ∈ pullback.selectedCells) :
    wz1PaperGridCube rho cell ⊆
      wz1PaperGridCube sqrtRequested.1
        (pullback.standardSecondParent cell) := by
  rw [standardSecondParent, dif_pos hcell]
  exact
    (Classical.choose_spec
      (pullback.exists_standardSecondParent hcell)).2

def standardSqrtSlabIndex (cell : WZ2PaperCellIndex) : ℤ :=
  (pullback.standardSecondParent cell).2.2

def standardSqrtSlabIndices : Finset ℤ :=
  pullback.selectedCells.image pullback.standardSqrtSlabIndex

def standardSqrtSlabRhoCells
    (heightIndex : ℤ) : Finset WZ2PaperCellIndex :=
  pullback.selectedCells.filter fun cell =>
    pullback.standardSqrtSlabIndex cell = heightIndex

def standardSqrtSlabParents
    (heightIndex : ℤ) : Finset WZ2PaperCellIndex :=
  (pullback.standardSqrtSlabRhoCells heightIndex).image
    pullback.standardSecondParent

theorem standardSqrtSlabRhoCells_subset
    (heightIndex : ℤ) :
    pullback.standardSqrtSlabRhoCells heightIndex ⊆
      pullback.selectedCells :=
  Finset.filter_subset _ _

theorem mem_standardSqrtSlabRhoCells
    {heightIndex : ℤ} {cell : WZ2PaperCellIndex} :
    cell ∈ pullback.standardSqrtSlabRhoCells heightIndex ↔
      cell ∈ pullback.selectedCells ∧
        pullback.standardSqrtSlabIndex cell = heightIndex := by
  simp [standardSqrtSlabRhoCells]

theorem standardSqrtSlabParents_subset_active
    (heightIndex : ℤ) :
    pullback.standardSqrtSlabParents heightIndex ⊆
      twoScale.second.terminal.balanced.activeCells := by
  intro parent hparent
  rcases Finset.mem_image.mp hparent with ⟨cell, hcell, rfl⟩
  exact pullback.standardSecondParent_active
    (pullback.standardSqrtSlabRhoCells_subset heightIndex hcell)

theorem standardSqrtSlabParent_height
    {heightIndex : ℤ} {parent : WZ2PaperCellIndex}
    (hparent : parent ∈ pullback.standardSqrtSlabParents heightIndex) :
    parent.2.2 = heightIndex := by
  rcases Finset.mem_image.mp hparent with ⟨cell, hcell, rfl⟩
  exact (pullback.mem_standardSqrtSlabRhoCells.mp hcell).2

theorem standardSqrtSlabRhoCell_subset_parent
    {heightIndex : ℤ} {cell : WZ2PaperCellIndex}
    (hcell : cell ∈ pullback.standardSqrtSlabRhoCells heightIndex) :
    wz1PaperGridCube rho cell ⊆
      wz1PaperGridCube sqrtRequested.1
        (pullback.standardSecondParent cell) :=
  pullback.standardSecondParent_cell_subset
    (pullback.standardSqrtSlabRhoCells_subset heightIndex hcell)

theorem standardSqrtSlabRhoCells_nonempty
    {heightIndex : ℤ}
    (hheight : heightIndex ∈ pullback.standardSqrtSlabIndices) :
    (pullback.standardSqrtSlabRhoCells heightIndex).Nonempty := by
  rcases Finset.mem_image.mp hheight with ⟨cell, hcell, hindex⟩
  exact ⟨cell, pullback.mem_standardSqrtSlabRhoCells.mpr
    ⟨hcell, hindex⟩⟩

theorem selectedCells_card_eq_sum_standardSqrtSlabRhoCells :
    pullback.selectedCells.card =
      ∑ heightIndex ∈ pullback.standardSqrtSlabIndices,
        (pullback.standardSqrtSlabRhoCells heightIndex).card := by
  have hmaps :
      Set.MapsTo pullback.standardSqrtSlabIndex
        (pullback.selectedCells : Set WZ2PaperCellIndex)
        (pullback.standardSqrtSlabIndices : Set ℤ) := by
    intro cell hcell
    exact Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
  simpa [standardSqrtSlabRhoCells] using
    Finset.card_eq_sum_card_fiberwise hmaps

def standardSqrtSlabSourceRegion (heightIndex : ℤ) : Set Point3 :=
  pullback.selectedRhoCellsSourceRegion
    (pullback.standardSqrtSlabRhoCells heightIndex)

def standardSqrtSlabCoarseRegion (heightIndex : ℤ) : Set Point3 :=
  pullback.selectedRhoCellsCoarseRegion
    (pullback.standardSqrtSlabRhoCells heightIndex)

/-- Second refined shading restricted to all genuine second-cover parents in
one standard side-`sqrt rho` slab. -/
def standardSqrtSlabSecondRegion (heightIndex : ℤ) : Set Point3 :=
  twoScale.secondRefinedFineShading.union ∩
    ⋃ parent ∈ pullback.standardSqrtSlabParents heightIndex,
      wz1PaperGridCube sqrtRequested.1 parent

/-- The full second-parent carrier and the retained-rho-cell carrier of one
standard slab are the same set. -/
theorem standardSqrtSlabSecondRegion_eq_coarseRegion
    (heightIndex : ℤ) :
    pullback.standardSqrtSlabSecondRegion heightIndex =
      pullback.standardSqrtSlabCoarseRegion heightIndex := by
  have hrhoRequested : 0 < rhoRequested.1 :=
    twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hfull :=
    twoScale.second.terminal.fine_cubical.union_eq_activeCells hrhoRequested
  ext point
  constructor
  · rintro ⟨hpointFine, hpointParentUnion⟩
    rcases Set.mem_iUnion₂.mp hpointParentUnion with
      ⟨parent, hparent, hpointParent⟩
    have hpointFine' := hpointFine
    rw [hfull] at hpointFine'
    rcases Set.mem_iUnion₂.mp hpointFine' with
      ⟨rhoCell, hrhoCellActive, hpointRhoCell⟩
    have hrhoCellSelected : rhoCell ∈ pullback.selectedCells := by
      rw [pullback.selectedCells_eq]
      exact hrhoCellActive
    have hpointRhoCellAtRho :
        point ∈ wz1PaperGridCube rho rhoCell := by
      simpa only [pullback.rhoRequested_eq] using hpointRhoCell
    have hpointCanonical :
        point ∈ wz1PaperGridCube sqrtRequested.1
          (pullback.standardSecondParent rhoCell) :=
      pullback.standardSecondParent_cell_subset
        hrhoCellSelected hpointRhoCellAtRho
    have hparentIndex :
        wz1PaperGridIndex sqrtRequested.1 point = parent :=
      (mem_wz1PaperGridCube sqrtRequested.1 parent point).mp hpointParent
    have hcanonicalIndex :
        wz1PaperGridIndex sqrtRequested.1 point =
          pullback.standardSecondParent rhoCell :=
      (mem_wz1PaperGridCube sqrtRequested.1
        (pullback.standardSecondParent rhoCell) point).mp hpointCanonical
    have hparentCanonical :
        parent = pullback.standardSecondParent rhoCell :=
      hparentIndex.symm.trans hcanonicalIndex
    have hparentHeight : parent.2.2 = heightIndex :=
      pullback.standardSqrtSlabParent_height hparent
    have hrhoCellSlab :
        rhoCell ∈ pullback.standardSqrtSlabRhoCells heightIndex := by
      apply pullback.mem_standardSqrtSlabRhoCells.mpr
      refine ⟨hrhoCellSelected, ?_⟩
      unfold standardSqrtSlabIndex
      rw [← hparentCanonical]
      exact hparentHeight
    change point ∈ twoScale.secondRefinedFineShading.union ∩
      pureWZ2Node05RetainedCellRegion rho
        (pullback.standardSqrtSlabRhoCells heightIndex)
    refine ⟨hpointFine, ?_⟩
    exact Set.mem_iUnion₂.mpr
      ⟨rhoCell, hrhoCellSlab, hpointRhoCellAtRho⟩
  · intro hpoint
    have hpoint' := hpoint
    change point ∈ twoScale.secondRefinedFineShading.union ∩
      pureWZ2Node05RetainedCellRegion rho
        (pullback.standardSqrtSlabRhoCells heightIndex) at hpoint'
    rcases Set.mem_iUnion₂.mp hpoint'.2 with
      ⟨rhoCell, hrhoCellSlab, hpointRhoCell⟩
    let parent := pullback.standardSecondParent rhoCell
    have hparent :
        parent ∈ pullback.standardSqrtSlabParents heightIndex :=
      Finset.mem_image.mpr ⟨rhoCell, hrhoCellSlab, rfl⟩
    have hpointParent :
        point ∈ wz1PaperGridCube sqrtRequested.1 parent :=
      pullback.standardSqrtSlabRhoCell_subset_parent
        hrhoCellSlab hpointRhoCell
    exact ⟨hpoint'.1, Set.mem_iUnion₂.mpr
      ⟨parent, hparent, hpointParent⟩⟩

/-- Exact balanced second-cover mass on the full parent carrier of a standard
slab. -/
theorem standardSqrtSlabSecondRegion_volume
    (heightIndex : ℤ) :
    volume (pullback.standardSqrtSlabSecondRegion heightIndex) =
      ((pullback.standardSqrtSlabParents heightIndex).card : ENNReal) *
        twoScale.secondBalancedCover.cellMass := by
  unfold standardSqrtSlabSecondRegion
  exact twoScale.secondBalancedCover.selected_cells_volume
    (pullback.standardSqrtSlabParents heightIndex)
    (pullback.standardSqrtSlabParents_subset_active heightIndex)

/-- The full second-parent mass is exactly the coarse mass entering the
standard-slab source/coarse cross identity. -/
theorem standardSqrtSlab_parentMass_eq_coarseVolume
    (heightIndex : ℤ) :
    ((pullback.standardSqrtSlabParents heightIndex).card : ENNReal) *
        twoScale.secondBalancedCover.cellMass =
      volume (pullback.standardSqrtSlabCoarseRegion heightIndex) := by
  rw [← pullback.standardSqrtSlabSecondRegion_volume heightIndex,
    pullback.standardSqrtSlabSecondRegion_eq_coarseRegion heightIndex]

theorem standardSqrtSlabSourceRegion_volume (heightIndex : ℤ) :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex) =
      ((pullback.standardSqrtSlabRhoCells heightIndex).card : ENNReal) *
        pullback.firstPostBalanced.cellMass :=
  pullback.selectedRhoCellsSourceRegion_volume _
    (pullback.standardSqrtSlabRhoCells_subset heightIndex)

theorem sum_standardSqrtSlabSourceRegion_volume_subtype :
    (∑ heightIndex :
        {heightIndex // heightIndex ∈ pullback.standardSqrtSlabIndices},
      volume
        (pullback.standardSqrtSlabSourceRegion heightIndex.1)) =
      volume pullback.shading.union := by
  have hfin :
      (∑ heightIndex ∈ pullback.standardSqrtSlabIndices,
        volume
          (pullback.standardSqrtSlabSourceRegion heightIndex)) =
        volume pullback.shading.union := by
    simp_rw [pullback.standardSqrtSlabSourceRegion_volume]
    rw [← Finset.sum_mul, pullback.volume_eq]
    congr 1
    exact_mod_cast
      pullback.selectedCells_card_eq_sum_standardSqrtSlabRhoCells.symm
  rw [← hfin]
  rw [Finset.sum_subtype
    pullback.standardSqrtSlabIndices (fun _ => Iff.rfl)]

theorem standardSqrtSlabCoarseRegion_volume (heightIndex : ℤ) :
    volume (pullback.standardSqrtSlabCoarseRegion heightIndex) =
      ((pullback.standardSqrtSlabRhoCells heightIndex).card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) :=
  pullback.selectedRhoCellsCoarseRegion_volume _
    (pullback.standardSqrtSlabRhoCells_subset heightIndex)

theorem standardSqrtSlabSourceRegion_subset_source
    (heightIndex : ℤ) :
    pullback.standardSqrtSlabSourceRegion heightIndex ⊆
      pullback.shading.union :=
  Set.inter_subset_left

theorem measurableSet_standardSqrtSlabSourceRegion
    (heightIndex : ℤ) :
    MeasurableSet (pullback.standardSqrtSlabSourceRegion heightIndex) :=
  (measurableSet_shading_union _).inter
    (pureWZ2Node05RetainedCellRegion_measurable _ _)

theorem standardSqrtSlabSourceRegion_volume_pos
    {heightIndex : ℤ}
    (hheight : heightIndex ∈ pullback.standardSqrtSlabIndices) :
    0 < volume (pullback.standardSqrtSlabSourceRegion heightIndex) := by
  rw [pullback.standardSqrtSlabSourceRegion_volume]
  exact ENNReal.mul_pos
    (by
      exact_mod_cast
        (Nat.ne_of_gt
          (pullback.standardSqrtSlabRhoCells_nonempty hheight).card_pos))
    pullback.firstPostBalanced.cellMass_pos.ne'

theorem standardSqrtSlabSourceRegion_volume_ne_top
    (heightIndex : ℤ) :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex) ≠ ⊤ := by
  rw [pullback.standardSqrtSlabSourceRegion_volume]
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    pullback.firstPostBalanced.cellMass_ne_top

theorem standardSqrtSlabSourceRegion_height
    {heightIndex : ℤ} {point : Point3}
    (hpoint : point ∈
      pullback.standardSqrtSlabSourceRegion heightIndex) :
    point (2 : Fin 3) ∈
      Set.Ico ((heightIndex : ℝ) * Real.sqrt rho)
        ((heightIndex : ℝ) * Real.sqrt rho + Real.sqrt rho) := by
  rcases Set.mem_iUnion₂.mp hpoint.2 with
    ⟨cell, hcell, hpointCell⟩
  have hparent :=
    pullback.standardSqrtSlabRhoCell_subset_parent hcell hpointCell
  have hheight :=
    (pullback.mem_standardSqrtSlabRhoCells.mp hcell).2
  have hroot : 0 < sqrtRequested.1 :=
    twoScale.secondSticky.coarse_extremal.delta_pos
  rw [wz1PaperGridCube_eq_Ico hroot] at hparent
  unfold standardSqrtSlabIndex at hheight
  rw [hheight] at hparent
  change
    (heightIndex : ℝ) * Real.sqrt rho ≤ point (2 : Fin 3) ∧
      point (2 : Fin 3) <
        (heightIndex : ℝ) * Real.sqrt rho + Real.sqrt rho
  simpa only [pullback.sqrtRequested_eq,
    show ((heightIndex : ℝ) + 1) * Real.sqrt rho =
      (heightIndex : ℝ) * Real.sqrt rho + Real.sqrt rho by ring] using
    hparent.2.2.2.2

end SpatialParents

end PureWZ2Node05V4RichTwoScaleCellPullbackData

end Kakeya.Assouad

end
