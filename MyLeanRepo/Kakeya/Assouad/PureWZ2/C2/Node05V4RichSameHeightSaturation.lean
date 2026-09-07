import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64PreCommonBinLocalGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SameHeightHorizontalSaturation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinSpatialCellSliceBound

/-!
# Same-height saturation for the direct-rich Node 5 call

For every selected first-cover `rho` cell, horizontally saturate only the
heights where the exact post-source pullback has positive planar slice area.
The union over one selected second-cover parent is the carrier used to repair
the omitted same-height step between WZ Lemmas 5.4 and 5.3.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

namespace PureWZ2Node05V4RichTwoScaleCellPullbackData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta rho : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)

/-- Exact post-source part of one selected first-cover cell. -/
def sameHeightSourceCell (cell : WZ2PaperCellIndex) : Set Point3 :=
  pullback.shading.union ∩ wz1PaperGridCube rho cell

/-- Horizontal saturation of one selected first-cover cell at precisely its
positive source-slice heights. -/
def sameHeightSaturatedCell (cell : WZ2PaperCellIndex) : Set Point3 :=
  wz1PaperGridCubeSameHeightSaturation rho cell
    (pullback.sameHeightSourceCell cell)

/-- Same-height carrier over all selected `rho` cells in one genuine
side-`sqrt rho` parent. -/
def sameHeightParentSaturation (parent : WZ2PaperCellIndex) : Set Point3 :=
  ⋃ cell ∈ pullback.preCommonBinRhoCells parent,
    pullback.sameHeightSaturatedCell cell

theorem sameHeightSourceCell_measurable (cell : WZ2PaperCellIndex) :
    MeasurableSet (pullback.sameHeightSourceCell cell) :=
  (measurableSet_shading_union pullback.shading).inter
    (wz1PaperGridCube_measurable cell)

theorem sameHeightSourceCell_subset_cube (cell : WZ2PaperCellIndex) :
    pullback.sameHeightSourceCell cell ⊆ wz1PaperGridCube rho cell :=
  Set.inter_subset_right

theorem sameHeightSourceCell_volume
    {cell : WZ2PaperCellIndex} (hcell : cell ∈ pullback.selectedCells) :
    volume (pullback.sameHeightSourceCell cell) =
      pullback.firstPostBalanced.cellMass :=
  pullback.cell_union_mass cell hcell

theorem sameHeightSourceCell_slice_volume_le
    {cell : WZ2PaperCellIndex} (_hcell : cell ∈ pullback.selectedCells)
    (z : ℝ)
    (hz : z ∈ wz1Lemma23PositiveSliceHeights
      (pullback.sameHeightSourceCell cell)) :
    volume (wz1Lemma23PlanarSlice
        (pullback.sameHeightSourceCell cell) z) ≤
      32 * Kakeya.realRpowENN delta (-inputLoss) *
        Kakeya.realRpowENN delta sigma *
        Kakeya.realRpowENN rho (2 - sigma) := by
  have hzUnit : z ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases wz1Lemma23PositiveSliceHeights_exists_point hz with ⟨point, hpoint⟩
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
    have hcurrent : point3 (point 0) (point 1) z ∈
        current.grain.shading.union :=
      pullback.subshading.union_subset hlift.1
    have hbox := shading_union_subset_axisBox hcurrent
    simpa [Kakeya.Streamlined.axisBox, point3, abs_le] using hbox.2.2
  have hpaper :
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (current.grain.globalGrains.slope z))
          (horizontalSlice pullback.shading.union z))
        delta (1 - sigma)
        (Kakeya.realRpowENN delta (-inputLoss)) := by
    apply (current.grain.globalGrains.global_ad z hzUnit).mono
    rintro value ⟨point, hpoint, rfl⟩
    exact ⟨point, ⟨pullback.subshading.union_subset hpoint.1, hpoint.2⟩, rfl⟩
  exact paperGridCube_planarSlice_volume_le_of_paperAD
    (measurableSet_shading_union pullback.shading)
    (by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos)
    (by
      rw [← pullback.rhoRequested_eq]
      exact rhoRequested.property.1)
    (current.grain.globalGrains.slope_bound z hzUnit) cell hpaper

/-- Division-free sharp volume inequality for one selected `rho` cell. -/
theorem cellMass_mul_square_le_sliceCap_mul_sameHeightSaturatedCell
    {cell : WZ2PaperCellIndex} (hcell : cell ∈ pullback.selectedCells) :
    pullback.firstPostBalanced.cellMass * ENNReal.ofReal (rho ^ 2) ≤
      (32 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN delta sigma *
          Kakeya.realRpowENN rho (2 - sigma)) *
        volume (pullback.sameHeightSaturatedCell cell) := by
  rw [← pullback.sameHeightSourceCell_volume hcell]
  exact source_volume_mul_square_le_sliceCap_mul_saturation_volume
    (by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos)
    cell (pullback.sameHeightSourceCell cell)
    (pullback.sameHeightSourceCell_measurable cell)
    (pullback.sameHeightSourceCell_subset_cube cell) _
    (pullback.sameHeightSourceCell_slice_volume_le
      hcell)

theorem sameHeightParentSaturation_measurable (parent : WZ2PaperCellIndex) :
    MeasurableSet (pullback.sameHeightParentSaturation parent) := by
  exact MeasurableSet.biUnion
    (pullback.preCommonBinRhoCells parent).finite_toSet.countable
    (fun cell _ => measurableSet_wz1PaperGridCubeSameHeightSaturation
      rho cell (pullback.sameHeightSourceCell cell)
      (pullback.sameHeightSourceCell_measurable cell))

theorem sameHeightParentSaturation_volume (parent : WZ2PaperCellIndex) :
    volume (pullback.sameHeightParentSaturation parent) =
      ∑ cell ∈ pullback.preCommonBinRhoCells parent,
        volume (pullback.sameHeightSaturatedCell cell) := by
  unfold sameHeightParentSaturation
  apply MeasureTheory.measure_biUnion_finset
  · intro first _ second _ hne
    exact (wz1PaperGridCube_disjoint hne).mono
      (wz1PaperGridCubeSameHeightSaturation_subset_cube rho first
        (pullback.sameHeightSourceCell first))
      (wz1PaperGridCubeSameHeightSaturation_subset_cube rho second
        (pullback.sameHeightSourceCell second))
  · intro cell _
    exact measurableSet_wz1PaperGridCubeSameHeightSaturation
      rho cell (pullback.sameHeightSourceCell cell)
      (pullback.sameHeightSourceCell_measurable cell)

/-- Aggregate division-free saturation bound on one selected second-cover
parent.  No division by a runtime mass or AD constant occurs. -/
theorem preCommonBinFinePullback_volume_mul_square_le_sameHeightParent
    (parent : WZ2PaperCellIndex) :
    volume (pullback.preCommonBinFinePullback parent) *
        ENNReal.ofReal (rho ^ 2) ≤
      (32 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN delta sigma *
          Kakeya.realRpowENN rho (2 - sigma)) *
        volume (pullback.sameHeightParentSaturation parent) := by
  let cells := pullback.preCommonBinRhoCells parent
  let cap := 32 * Kakeya.realRpowENN delta (-inputLoss) *
    Kakeya.realRpowENN delta sigma *
    Kakeya.realRpowENN rho (2 - sigma)
  rw [pullback.preCommonBinFinePullback_volume parent,
    pullback.sameHeightParentSaturation_volume parent]
  calc
    (cells.card : ENNReal) * pullback.firstPostBalanced.cellMass *
          ENNReal.ofReal (rho ^ 2) =
        ∑ _cell ∈ cells,
          pullback.firstPostBalanced.cellMass * ENNReal.ofReal (rho ^ 2) := by
            simp [Finset.sum_const]
            ring
    _ ≤ ∑ cell ∈ cells,
          cap * volume (pullback.sameHeightSaturatedCell cell) := by
      apply Finset.sum_le_sum
      intro cell hcell
      exact pullback.cellMass_mul_square_le_sliceCap_mul_sameHeightSaturatedCell
        (pullback.preCommonBinRhoCells_subset parent hcell)
    _ = cap *
        ∑ cell ∈ cells, volume (pullback.sameHeightSaturatedCell cell) := by
      rw [Finset.mul_sum]

/-- The exact power-cancellation interface for the saturated parent.  The
single scalar premise is family-independent: it compares the requested target
with the two direct-rich balanced-cell floors and the source slice cap. -/
theorem sameHeightParentSaturation_volume_lower
    {parent : WZ2PaperCellIndex}
    (hparent : parent ∈ twoScale.secondBalancedCover.activeCells)
    (target : ENNReal)
    (hpower :
      ((32 * Kakeya.realRpowENN delta (-inputLoss) *
            Kakeya.realRpowENN delta sigma *
            Kakeya.realRpowENN rho (2 - sigma)) *
          ENNReal.ofReal rho) * target ≤
        (Kakeya.realRpowENN rhoRequested.1 3 *
            Kakeya.realRpowENN (delta / rhoRequested.1)
              (sigma + 2 * twoScale.first.rich.terminalLoss)) *
          Kakeya.realRpowENN rhoRequested.1
            (3 / 2 + sigma / 2 + twoScale.second.terminalLoss)) :
    target ≤ volume (pullback.sameHeightParentSaturation parent) := by
  let cap : ENNReal :=
    32 * Kakeya.realRpowENN delta (-inputLoss) *
      Kakeya.realRpowENN delta sigma *
      Kakeya.realRpowENN rho (2 - sigma)
  let factor : ENNReal := cap * ENNReal.ofReal rho
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hfirst := twoScale.first_cellMass_power_lower
  have hsecond := twoScale.second_cellMass_rho_power_lower
  have hcellSquare :
      ENNReal.ofReal (rho ^ 2) * ENNReal.ofReal rho =
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
    rw [wz1PaperGridCube_volume_exact hrho]
    rw [← ENNReal.ofReal_mul (sq_nonneg rho)]
    congr 1
  have hsaturation :=
    pullback.preCommonBinFinePullback_volume_mul_square_le_sameHeightParent
      parent
  have hscaled : factor * target ≤
      factor * volume (pullback.sameHeightParentSaturation parent) := by
    calc
      factor * target ≤
          (Kakeya.realRpowENN rhoRequested.1 3 *
              Kakeya.realRpowENN (delta / rhoRequested.1)
                (sigma + 2 * twoScale.first.rich.terminalLoss)) *
            Kakeya.realRpowENN rhoRequested.1
              (3 / 2 + sigma / 2 + twoScale.second.terminalLoss) := by
        simpa only [factor, cap] using hpower
      _ ≤ pullback.firstPostBalanced.cellMass *
          twoScale.secondBalancedCover.cellMass := by
        gcongr
        · rw [pullback.firstPost_cellMass_eq]
          exact hfirst
      _ = volume (pullback.preCommonBinFinePullback parent) *
          volume (wz1PaperGridCube rho (0, 0, 0)) := by
        rw [pullback.preCommonBinFinePullback_mass_cross hparent]
        ring
      _ = (volume (pullback.preCommonBinFinePullback parent) *
            ENNReal.ofReal (rho ^ 2)) * ENNReal.ofReal rho := by
        rw [← hcellSquare]
        ring
      _ ≤ (cap * volume (pullback.sameHeightParentSaturation parent)) *
          ENNReal.ofReal rho := by gcongr
      _ = factor * volume (pullback.sameHeightParentSaturation parent) := by
        simp only [factor]
        ring
  have hfactorZero : factor ≠ 0 := by
    dsimp only [factor, cap]
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · norm_num
          · exact (ENNReal.ofReal_pos.mpr
              (Real.rpow_pos_of_pos current.grain.extremal.delta_pos _)).ne'
        · exact (ENNReal.ofReal_pos.mpr
            (Real.rpow_pos_of_pos current.grain.extremal.delta_pos _)).ne'
      · exact (ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos hrho _)).ne'
    · exact (ENNReal.ofReal_pos.mpr hrho).ne'
  have hfactorTop : factor ≠ ⊤ := by
    dsimp only [factor, cap]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num) (by simp [Kakeya.realRpowENN]))
          (by simp [Kakeya.realRpowENN]))
        (by simp [Kakeya.realRpowENN]))
      ENNReal.ofReal_ne_top
  exact (ENNReal.mul_le_mul_iff_right hfactorZero hfactorTop).mp <| by
    simpa only [mul_comm] using hscaled

/-- Every point of the parent saturation lies in its genuine second-cover
parent. -/
theorem sameHeightParentSaturation_subset_parent
    {parent : WZ2PaperCellIndex} :
    pullback.sameHeightParentSaturation parent ⊆
      wz1PaperGridCube sqrtRequested.1 parent := by
  intro point hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
  have hdata := Finset.mem_filter.mp hcell
  have hpointRho : point ∈ wz1PaperGridCube rho cell :=
    wz1PaperGridCubeSameHeightSaturation_subset_cube rho cell
      (pullback.sameHeightSourceCell cell) hpointCell
  have hparent := pullback.standardSecondParent_cell_subset hdata.1 hpointRho
  simpa only [hdata.2] using hparent

theorem sameHeightParentSaturation_subset_secondRefined
    (parent : WZ2PaperCellIndex) :
    pullback.sameHeightParentSaturation parent ⊆
      twoScale.secondRefinedFineShading.union := by
  intro point hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hsat⟩
  have hselected := pullback.preCommonBinRhoCells_subset parent hcell
  have hactive : cell ∈ wz1PaperActiveCells
      twoScale.secondRefinedFineShading
      twoScale.first.publicSticky.coarse_extremal.delta_pos := by
    simpa only [pullback.selectedCells_eq] using hselected
  have hpointCell : point ∈ wz1PaperGridCube rho cell :=
    wz1PaperGridCubeSameHeightSaturation_subset_cube rho cell
      (pullback.sameHeightSourceCell cell) hsat
  have hpointRequested : point ∈ wz1PaperGridCube rhoRequested.1 cell := by
    simpa only [pullback.rhoRequested_eq] using hpointCell
  have hinter := twoScale.second.terminal.fine_cubical.inter_activeCell_eq
    twoScale.first.publicSticky.coarse_extremal.delta_pos hactive
  have hmem : point ∈ twoScale.secondRefinedFineShading.union ∩
      wz1PaperGridCube rhoRequested.1 cell := by
    rw [hinter]
    exact hpointRequested
  exact hmem.1

/-- Same-height global projection transport for the whole saturated parent. -/
theorem sameHeightParentSaturation_projection_subset_source_thickening
    {parent : WZ2PaperCellIndex} {z : ℝ}
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    scalarProjection
        (globalGrainDirection (current.grain.globalGrains.slope z))
        (horizontalSlice
          (pullback.sameHeightParentSaturation parent) z) ⊆
      Metric.cthickening (4 * rho)
        (scalarProjection
          (globalGrainDirection (current.grain.globalGrains.slope z))
          (horizontalSlice pullback.shading.union z)) := by
  rintro value ⟨point, hpoint, rfl⟩
  rcases Set.mem_iUnion₂.mp hpoint.1 with ⟨cell, hcell, hsat⟩
  have hlocal := sameHeightSaturation_projection_subset_source_thickening
    (z := z)
    (by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos)
    cell (pullback.sameHeightSourceCell cell)
    (pullback.sameHeightSourceCell_subset_cube cell)
    (current.grain.globalGrains.slope_bound z hz)
  let planar : Point2 := WithLp.toLp 2 ![point 0, point 1]
  have hplanarCell : planar ∈ wz1Lemma23PlanarSlice
      (pullback.sameHeightSaturatedCell cell) z := by
    rw [wz1Lemma23_mem_planarSlice_iff]
    have heq : point3 (planar 0) (planar 1) z = point := by
      ext coordinate
      fin_cases coordinate <;> simp [planar, point3, hpoint.2]
    rwa [heq]
  have hthin := hlocal ⟨planar, hplanarCell, rfl⟩
  have hthin' : inner ℝ point
        (globalGrainDirection (current.grain.globalGrains.slope z)) ∈
      Metric.cthickening (4 * rho)
        ((fun point : Point2 => point 0 +
            current.grain.globalGrains.slope z * point 1) ''
          wz1Lemma23PlanarSlice (pullback.sameHeightSourceCell cell) z) := by
    simpa [planar, globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      using hthin
  apply Metric.cthickening_subset_of_subset (4 * rho) ?_ hthin'
  rintro sourceValue ⟨sourcePlanar, hsourcePlanar, rfl⟩
  have hlift := wz1Lemma23_mem_planarSlice_iff.mp hsourcePlanar
  refine ⟨point3 (sourcePlanar 0) (sourcePlanar 1) z,
    ⟨hlift.1, by simp [point3]⟩, ?_⟩
  simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ, point3]

/-- The same-height parent saturation has exact-slice global AD at scale
`4*rho`, with the fixed factor `160`: ten for the paper/internal bridge and
sixteen for a thickening whose radius equals the new base scale. -/
theorem sameHeightParentSaturation_exactAD
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hfourOne : 4 * rho ≤ 1)
    (parent : WZ2PaperCellIndex)
    (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    IsADSet1
      (scalarProjection
        (globalGrainDirection (current.grain.globalGrains.slope z))
        (horizontalSlice (pullback.sameHeightParentSaturation parent) z))
      (4 * rho) (1 - sigma)
      (160 * Kakeya.realRpowENN delta (-inputLoss)) := by
  let sourceProjection :=
    scalarProjection
      (globalGrainDirection (current.grain.globalGrains.slope z))
      (horizontalSlice pullback.shading.union z)
  let saturatedProjection :=
    scalarProjection
      (globalGrainDirection (current.grain.globalGrains.slope z))
      (horizontalSlice (pullback.sameHeightParentSaturation parent) z)
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hpaper : PureWZ2PaperADSet1 sourceProjection delta (1 - sigma)
      (Kakeya.realRpowENN delta (-inputLoss)) := by
    apply (current.grain.globalGrains.global_ad z hz).mono
    rintro value ⟨point, hpoint, rfl⟩
    exact ⟨point, ⟨pullback.subshading.union_subset hpoint.1, hpoint.2⟩, rfl⟩
  have hsourceBounded : sourceProjection ⊆ Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨point, hpoint, rfl⟩
    have hbox := shading_union_subset_axisBox
      (pullback.subshading.union_subset hpoint.1)
    have hx : |point 0| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.1
    have hy : |point 1| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
    have hslope := current.grain.globalGrains.slope_bound z hz
    have hformula :
        inner ℝ point
            (globalGrainDirection (current.grain.globalGrains.slope z)) =
          point 0 + current.grain.globalGrains.slope z * point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    change inner ℝ point
        (globalGrainDirection (current.grain.globalGrains.slope z)) ∈
      Set.Icc (-4 : ℝ) 4
    rw [hformula]
    apply abs_le.mp
    calc
      |point 0 + current.grain.globalGrains.slope z * point 1| ≤
          |point 0| +
            |current.grain.globalGrains.slope z| * |point 1| := by
              simpa [abs_mul] using abs_add_le (point 0)
                (current.grain.globalGrains.slope z * point 1)
      _ ≤ 1 + 3 * 1 := by gcongr
      _ = 4 := by norm_num
  have hinternal : IsADSet1 sourceProjection delta (1 - sigma)
      (10 * Kakeya.realRpowENN delta (-inputLoss)) :=
    hbridge.1 _ delta (1 - sigma)
      (Kakeya.realRpowENN delta (-inputLoss)) hsourceBounded hpaper
  have hcoarse : IsADSet1 sourceProjection (4 * rho) (1 - sigma)
      (10 * Kakeya.realRpowENN delta (-inputLoss)) :=
    hinternal.coarsen_scale (by positivity)
      (by
        have hdeltaRho : delta ≤ rho := by
          rw [← pullback.rhoRequested_eq]
          exact rhoRequested.property.1
        linarith) hfourOne
  have hsaturatedBounded : saturatedProjection ⊆ Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨point, hpoint, rfl⟩
    have hcoarsePoint : point ∈ twoScale.secondRefinedFineShading.union :=
      pullback.sameHeightParentSaturation_subset_secondRefined parent hpoint.1
    have hbox := shading_union_subset_axisBox hcoarsePoint
    have hx : |point 0| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.1
    have hy : |point 1| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
    have hslope := current.grain.globalGrains.slope_bound z hz
    have hformula :
        inner ℝ point
            (globalGrainDirection (current.grain.globalGrains.slope z)) =
          point 0 + current.grain.globalGrains.slope z * point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    change inner ℝ point
        (globalGrainDirection (current.grain.globalGrains.slope z)) ∈
      Set.Icc (-4 : ℝ) 4
    rw [hformula]
    apply abs_le.mp
    calc
      |point 0 + current.grain.globalGrains.slope z * point 1| ≤
          |point 0| +
            |current.grain.globalGrains.slope z| * |point 1| := by
              simpa [abs_mul] using abs_add_le (point 0)
                (current.grain.globalGrains.slope z * point 1)
      _ ≤ 1 + 3 * 1 := by gcongr
      _ = 4 := by norm_num
  have hthick : saturatedProjection ⊆
      Metric.cthickening (4 * rho) sourceProjection := by
    simpa only [saturatedProjection, sourceProjection] using
      pullback.sameHeightParentSaturation_projection_subset_source_thickening
        hz
  have hdirect := hcoarse.generalized_thickening
    hthick hsaturatedBounded (by positivity : 0 < 4 * rho)
      (by positivity : 0 < 4 * rho)
  have hratioOne : (4 * rho) / (4 * rho) = (1 : ℝ) := by
    field_simp [hrho.ne']
  rw [hratioOne] at hdirect
  have hceil : Nat.ceil (1 : ℝ) = 1 := by norm_num
  rw [hceil] at hdirect
  convert hdirect using 1 <;> norm_num <;> ring

end PureWZ2Node05V4RichTwoScaleCellPullbackData

end Kakeya.Assouad

end
