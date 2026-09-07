import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightSeparatedParents

/-!
# Production graph on the separated joint-height saturation

The graph carrier is the selected same-height saturation after
one-parent-per-y and mod-512 separation.  Its global projection is transported
to the unchanged current source at the same height, so exact AD is inherited
without changing witnesses.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

namespace PureWZ2Node05V4RichJointSeparatedParentData

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
    {block : volumePopular.JointHeightCommonBinData B₀ threshold}
    {oneParent : block.JointOneParentPerYData}
    (separated : PureWZ2Node05V4RichJointSeparatedParentData oneParent)

def graphScale
    (_separated : PureWZ2Node05V4RichJointSeparatedParentData oneParent) : ℝ :=
  256 * rho

theorem graphScale_pos : 0 < separated.graphScale := by
  unfold graphScale
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  positivity

theorem saturatedUnion_subset_secondRefined :
    separated.saturatedUnion ⊆ twoScale.secondRefinedFineShading.union := by
  intro point hpoint
  rw [separated.saturatedUnion_eq] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hsat⟩
  have hpointCell :
      point ∈ wz1PaperGridCube rho cell :=
    wz1PaperGridCubeSameHeightSaturation_subset_cube
      rho cell (block.jointCellSource cell) hsat
  have hselected :
      cell ∈ pullback.selectedCells :=
    block.jointFixedBinRhoCells_subset_selected
      (oneParent.selectedCells_subset
        (separated.selectedCells_subset hcell))
  have hactive : cell ∈ wz1PaperActiveCells
      twoScale.secondRefinedFineShading
        twoScale.first.publicSticky.coarse_extremal.delta_pos := by
    simpa only [pullback.selectedCells_eq] using hselected
  have hwhole :=
    twoScale.second.terminal.fine_cubical.inter_activeCell_eq
      twoScale.first.publicSticky.coarse_extremal.delta_pos hactive
  have hpointRequested :
      point ∈ wz1PaperGridCube rhoRequested.1 cell := by
    simpa only [pullback.rhoRequested_eq] using hpointCell
  have : point ∈ twoScale.secondRefinedFineShading.union ∩
      wz1PaperGridCube rhoRequested.1 cell := by
    rw [hwhole]
    exact hpointRequested
  exact this.1

theorem saturatedUnion_exists_source_same_height
    {point : Point3} (hpoint : point ∈ separated.saturatedUnion) :
    ∃ cell ∈ separated.selectedCells,
      point ∈ block.jointCellSaturation cell ∧
        ∃ sourcePoint ∈ block.jointCellSource cell,
          sourcePoint (2 : Fin 3) = point (2 : Fin 3) := by
  rw [separated.saturatedUnion_eq] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hsat⟩
  rcases wz1PaperGridCubeSameHeightSaturation_exists_source_same_height
      (block.jointCellSource_subset_cube cell) hsat with
    ⟨sourcePoint, hsourcePoint, hheight⟩
  exact ⟨cell, hcell, hsat, sourcePoint, hsourcePoint.1, hheight⟩

theorem saturatedUnion_height_mem_ZS
    {point : Point3} (hpoint : point ∈ separated.saturatedUnion) :
    point (2 : Fin 3) ∈ volumePopular.continuous.popularHeights := by
  rcases separated.saturatedUnion_exists_source_same_height hpoint with
    ⟨_cell, _hcell, _hsat, sourcePoint, hsourcePoint, hheight⟩
  rw [← hheight]
  exact volumePopular.jointSourceSet_height_mem_ZS hsourcePoint.1.1.1

theorem saturatedUnion_height :
    ∀ point ∈ separated.saturatedUnion,
      point (2 : Fin 3) ∈
        Set.Ico volumePopular.jointSlabLeft
          (volumePopular.jointSlabLeft + Real.sqrt rho) := by
  intro point hpoint
  rcases separated.saturatedUnion_exists_source_same_height hpoint with
    ⟨_cell, _hcell, _hsat, sourcePoint, hsourcePoint, hheight⟩
  rw [← hheight]
  exact volumePopular.jointSourceSet_height sourcePoint hsourcePoint.1.1.1

theorem saturatedUnion_projection_subset_source_thickening
    {z : ℝ} :
    scalarProjection
        (globalGrainDirection (current.grain.globalGrains.slope z))
        (horizontalSlice separated.saturatedUnion z) ⊆
      Metric.cthickening (4 * rho)
        (scalarProjection
          (globalGrainDirection (current.grain.globalGrains.slope z))
          (horizontalSlice current.grain.shading.union z)) := by
  rintro value ⟨point, hpoint, rfl⟩
  have hpointSaturated : point ∈ separated.saturatedUnion := hpoint.1
  rw [separated.saturatedUnion_eq] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint.1 with ⟨cell, _hcell, hsat⟩
  have hlocal :=
    sameHeightSaturation_projection_subset_source_thickening
      (rho := rho)
      (slope := current.grain.globalGrains.slope z)
      (z := z)
      (by
        rw [← pullback.rhoRequested_eq]
        exact twoScale.first.publicSticky.coarse_extremal.delta_pos)
      cell (block.jointCellSource cell)
      (block.jointCellSource_subset_cube cell)
      (current.grain.globalGrains.slope_bound z <| by
        have hsourcePoint :=
          separated.saturatedUnion_height_mem_ZS hpointSaturated
        exact pullback.sourcePopularHeight_mem_paperRange heightIndex.1.2
          (by
            rw [← volumePopular.continuous.popularHeights_eq]
            simpa [hpoint.2] using hsourcePoint))
  let planar : Point2 := WithLp.toLp 2 ![point 0, point 1]
  have hplanar :
      planar ∈ wz1Lemma23PlanarSlice
        (block.jointCellSaturation cell) z := by
    rw [wz1Lemma23_mem_planarSlice_iff]
    have heq : point3 (planar 0) (planar 1) z = point := by
      ext coordinate
      fin_cases coordinate <;> simp [planar, point3, hpoint.2]
    rwa [heq]
  have hthin := hlocal ⟨planar, hplanar, rfl⟩
  have hsourceSubset :
      (fun sourcePlanar : Point2 =>
          sourcePlanar 0 +
            current.grain.globalGrains.slope z * sourcePlanar 1) ''
          wz1Lemma23PlanarSlice (block.jointCellSource cell) z ⊆
        scalarProjection
          (globalGrainDirection (current.grain.globalGrains.slope z))
          (horizontalSlice current.grain.shading.union z) := by
    rintro _value ⟨sourcePlanar, hsourcePlanar, rfl⟩
    let sourcePoint := point3 (sourcePlanar 0) (sourcePlanar 1) z
    have hsourceLift := wz1Lemma23_mem_planarSlice_iff.mp hsourcePlanar
    refine ⟨sourcePoint,
      ⟨volumePopular.jointSourceSet_subset_current
        hsourceLift.1.1.1,
        by simp [sourcePoint, point3]⟩, ?_⟩
    simp [sourcePoint, point3, globalGrainDirection, PiLp.inner_apply,
      Fin.sum_univ_succ]
  have hthinCurrent :=
    Metric.cthickening_subset_of_subset (4 * rho) hsourceSubset hthin
  simpa [scalarProjection, globalGrainDirection, PiLp.inner_apply,
    Fin.sum_univ_succ, planar] using hthinCurrent

theorem saturatedUnion_exactAD
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : separated.graphScale ≤ 1)
    (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    IsADSet1
      (scalarProjection
        (globalGrainDirection (current.grain.globalGrains.slope z))
        (horizontalSlice separated.saturatedUnion z))
      separated.graphScale (1 - sigma)
      (160 * Kakeya.realRpowENN delta (-inputLoss)) := by
  let sourceProjection :=
    scalarProjection
      (globalGrainDirection (current.grain.globalGrains.slope z))
      (horizontalSlice current.grain.shading.union z)
  let saturatedProjection :=
    scalarProjection
      (globalGrainDirection (current.grain.globalGrains.slope z))
      (horizontalSlice separated.saturatedUnion z)
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hpaper : PureWZ2PaperADSet1 sourceProjection delta (1 - sigma)
      (Kakeya.realRpowENN delta (-inputLoss)) :=
    current.grain.globalGrains.global_ad z hz
  have hsourceBounded : sourceProjection ⊆ Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨point, hpoint, rfl⟩
    have hbox := shading_union_subset_axisBox hpoint.1
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
      _ ≤ |point 0| + |current.grain.globalGrains.slope z| *
          |point 1| := by
        simpa [abs_mul] using abs_add_le (point 0)
          (current.grain.globalGrains.slope z * point 1)
      _ ≤ 1 + 3 * 1 := by
        gcongr
        · simpa [Kakeya.Streamlined.axisBox] using hbox.1
        · simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
      _ = 4 := by norm_num
  have hinternal : IsADSet1 sourceProjection delta (1 - sigma)
      (10 * Kakeya.realRpowENN delta (-inputLoss)) :=
    hbridge.1 _ delta (1 - sigma)
      (Kakeya.realRpowENN delta (-inputLoss)) hsourceBounded hpaper
  have hfourOne : 4 * rho ≤ 1 := by
    calc
      4 * rho ≤ separated.graphScale := by
        unfold graphScale
        nlinarith
      _ ≤ 1 := hgraphOne
  have hsourceAtFour : IsADSet1 sourceProjection (4 * rho) (1 - sigma)
      (10 * Kakeya.realRpowENN delta (-inputLoss)) :=
    hinternal.coarsen_scale (by positivity)
      (by
        have hdeltaRho : delta ≤ rho := by
          rw [← pullback.rhoRequested_eq]
          exact rhoRequested.property.1
        linarith)
      hfourOne
  have hsaturatedBounded : saturatedProjection ⊆ Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨point, hpoint, rfl⟩
    have hcoarse := separated.saturatedUnion_subset_secondRefined hpoint.1
    have hbox := shading_union_subset_axisBox hcoarse
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
      _ ≤ |point 0| + |current.grain.globalGrains.slope z| *
          |point 1| := by
        simpa [abs_mul] using abs_add_le (point 0)
          (current.grain.globalGrains.slope z * point 1)
      _ ≤ 1 + 3 * 1 := by
        gcongr
        · simpa [Kakeya.Streamlined.axisBox] using hbox.1
        · simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
      _ = 4 := by norm_num
  have hthick : saturatedProjection ⊆
      Metric.cthickening (4 * rho) sourceProjection := by
    simpa only [saturatedProjection, sourceProjection] using
      separated.saturatedUnion_projection_subset_source_thickening
  have hdirect := hsourceAtFour.generalized_thickening
    hthick hsaturatedBounded (by positivity : 0 < 4 * rho)
      (by positivity : 0 < 4 * rho)
  have hratioOne : (4 * rho) / (4 * rho) = (1 : ℝ) := by
    field_simp [hrho.ne']
  rw [hratioOne] at hdirect
  have hceil : Nat.ceil (1 : ℝ) = 1 := by norm_num
  rw [hceil] at hdirect
  have hfourAD : IsADSet1 saturatedProjection (4 * rho) (1 - sigma)
      (160 * Kakeya.realRpowENN delta (-inputLoss)) := by
    convert hdirect using 1
    all_goals norm_num
    ring
  exact hfourAD.coarsen_scale separated.graphScale_pos
    (by unfold graphScale; nlinarith) hgraphOne

def graphCells : Finset WZ2PaperCellIndex :=
  (wz1Lemma23BoundedCells separated.graphScale
      separated.graphScale_pos).filter fun cell =>
    (separated.saturatedUnion ∩
      wz1Lemma23Cell separated.graphScale cell).Nonempty

abbrev GraphCell :=
  {cell : WZ2PaperCellIndex // cell ∈ separated.graphCells}

def graphCellTube (cell : separated.GraphCell) :
    Kakeya.DeltaTube separated.graphScale where
  base := Classical.choose (Finset.mem_filter.mp cell.property).2 -
    (1 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  direction := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  direction_unit := by simp

theorem graphCell_subset_tube (cell : separated.GraphCell) :
    wz1Lemma23Cell separated.graphScale cell.1 ⊆
      (separated.graphCellTube cell).carrier := by
  intro point hpoint
  let tube := separated.graphCellTube cell
  let center := Classical.choose (Finset.mem_filter.mp cell.property).2
  have hcenterCell : center ∈ wz1Lemma23Cell separated.graphScale cell.1 :=
    (Classical.choose_spec (Finset.mem_filter.mp cell.property).2).2
  have hcenter : center ∈ Kakeya.unitSegment tube.base tube.direction := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    dsimp [tube, center, graphCellTube]
    module
  apply Metric.mem_cthickening_of_dist_le point center separated.graphScale
    (Kakeya.unitSegment tube.base tube.direction) hcenter
  apply wz1Lemma23_same_cell_dist separated.graphScale_pos
  exact hpoint.trans hcenterCell.symm

def graphFamily : Kakeya.Streamlined.TubeFamily separated.graphScale where
  card := separated.graphCells.card
  tube index := separated.graphCellTube
    (separated.graphCells.equivFin.symm index)

def graphShading : Kakeya.Streamlined.TubeShading separated.graphFamily where
  carrier index :=
    separated.saturatedUnion ∩
      wz1Lemma23Cell separated.graphScale
        ((separated.graphCells.equivFin.symm index).1)
  measurable_carrier _ :=
    separated.saturatedUnion_measurable.inter
      (wz1Lemma23Cell_measurable separated.graphScale_pos _)
  subset_body index := fun _ hpoint =>
    separated.graphCell_subset_tube
      (separated.graphCells.equivFin.symm index) hpoint.2

theorem graphShading_union :
    separated.graphShading.union = separated.saturatedUnion := by
  apply Set.Subset.antisymm
  · rintro point ⟨_index, hpoint⟩
    exact hpoint.1
  · intro point hpoint
    let cell := wz1Lemma23CellIndex separated.graphScale point
    have hcoarse := separated.saturatedUnion_subset_secondRefined hpoint
    have hnorm := norm_le_two_of_mem_paperShading hcoarse
    have hcellBounded : cell ∈
        wz1Lemma23BoundedCells separated.graphScale separated.graphScale_pos :=
      wz1Lemma23_index_mem_bounded_two separated.graphScale_pos hnorm
    have hpointCell : point ∈ wz1Lemma23Cell separated.graphScale cell := rfl
    have hcell : cell ∈ separated.graphCells :=
      Finset.mem_filter.mpr ⟨hcellBounded, ⟨point, hpoint, hpointCell⟩⟩
    let index : Fin separated.graphCells.card :=
      separated.graphCells.equivFin ⟨cell, hcell⟩
    refine ⟨index, hpoint, ?_⟩
    simpa [index] using hpointCell

/-- The original heavy source slab controls the final graph volume with only
the two height-popularity halves, dyadic bins, integrated-label count, and
fixed parent residues.  No positive power of `rho` is lost. -/
theorem sourceSlab_half_half_le_graph :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) / 2 / 2 ≤
      (volumePopular.popular.bins : ENNReal) *
        (4 * ((volumePopular.jointRichCommonBinLabels
          block.referenceHeight threshold).card : ENNReal) *
          (45 * (512 * volume separated.graphShading.union))) := by
  calc
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) / 2 / 2 ≤
        volume volumePopular.continuous.popularRegion / 2 := by
      gcongr
      exact volumePopular.continuous.popularRegion_half_volume
    _ = volume volumePopular.sourcePopularShading.union / 2 := by
      rw [volumePopular.sourcePopularShading_union]
    _ ≤ (volumePopular.popular.bins : ENNReal) *
        volume volumePopular.jointSourceSet := by
      simpa only [
        PureWZ2Node05V4RichSourceVolumePopularHeightData.jointSourceSet]
        using volumePopular.popular.retained_volume
    _ ≤ (volumePopular.popular.bins : ENNReal) *
        (4 * ((volumePopular.jointRichCommonBinLabels
          block.referenceHeight threshold).card : ENNReal) *
          volumePopular.jointIntegratedBinMass
            block.referenceHeight block.bin) := by
      gcongr
      exact block.source_average
    _ ≤ (volumePopular.popular.bins : ENNReal) *
        (4 * ((volumePopular.jointRichCommonBinLabels
          block.referenceHeight threshold).card : ENNReal) *
          volume block.jointSaturatedUnion) := by
      gcongr
      exact block.jointFixedBin_volume_le_saturation
    _ ≤ (volumePopular.popular.bins : ENNReal) *
        (4 * ((volumePopular.jointRichCommonBinLabels
          block.referenceHeight threshold).card : ENNReal) *
          (45 * volume oneParent.saturatedUnion)) := by
      gcongr
      exact oneParent.volume_retention
    _ ≤ (volumePopular.popular.bins : ENNReal) *
        (4 * ((volumePopular.jointRichCommonBinLabels
          block.referenceHeight threshold).card : ENNReal) *
          (45 * (512 * volume separated.saturatedUnion))) := by
      gcongr
      exact separated.volume_retention
    _ = (volumePopular.popular.bins : ENNReal) *
        (4 * ((volumePopular.jointRichCommonBinLabels
          block.referenceHeight threshold).card : ENNReal) *
          (45 * (512 * volume separated.graphShading.union))) := by
      rw [separated.graphShading_union]

/-- The sharp form of the preceding transfer.  It retains the horizontal
`rho^2 / sliceCap` gain from same-height saturation; this is the form needed
for the absolute volume hypothesis of Theorem 5.2. -/
theorem sourceSlab_half_half_mul_square_le_graph :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) / 2 / 2 *
        ENNReal.ofReal (rho ^ 2) ≤
      (volumePopular.popular.bins : ENNReal) * 4 *
        ((volumePopular.jointRichCommonBinLabels
          block.referenceHeight threshold).card : ENNReal) *
        (32 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN delta sigma *
          Kakeya.realRpowENN rho (2 - sigma)) *
        45 * 512 * volume separated.graphShading.union := by
  let cap : ENNReal :=
    32 * Kakeya.realRpowENN delta (-inputLoss) *
      Kakeya.realRpowENN delta sigma *
      Kakeya.realRpowENN rho (2 - sigma)
  calc
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) / 2 / 2 *
          ENNReal.ofReal (rho ^ 2) ≤
        ((volumePopular.popular.bins : ENNReal) *
          (4 * ((volumePopular.jointRichCommonBinLabels
            block.referenceHeight threshold).card : ENNReal) *
            volumePopular.jointIntegratedBinMass
              block.referenceHeight block.bin)) *
          ENNReal.ofReal (rho ^ 2) := by
      gcongr
      calc
        volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) / 2 / 2 ≤
            volume volumePopular.continuous.popularRegion / 2 := by
          gcongr
          exact volumePopular.continuous.popularRegion_half_volume
        _ = volume volumePopular.sourcePopularShading.union / 2 := by
          rw [volumePopular.sourcePopularShading_union]
        _ ≤ (volumePopular.popular.bins : ENNReal) *
            volume volumePopular.jointSourceSet := by
          simpa only [
            PureWZ2Node05V4RichSourceVolumePopularHeightData.jointSourceSet]
            using volumePopular.popular.retained_volume
        _ ≤ (volumePopular.popular.bins : ENNReal) *
            (4 * ((volumePopular.jointRichCommonBinLabels
              block.referenceHeight threshold).card : ENNReal) *
              volumePopular.jointIntegratedBinMass
                block.referenceHeight block.bin) := by
          gcongr
          exact block.source_average
    _ = (volumePopular.popular.bins : ENNReal) *
        (4 * ((volumePopular.jointRichCommonBinLabels
          block.referenceHeight threshold).card : ENNReal) *
          (volumePopular.jointIntegratedBinMass
            block.referenceHeight block.bin * ENNReal.ofReal (rho ^ 2))) := by
      ring
    _ ≤ (volumePopular.popular.bins : ENNReal) *
        (4 * ((volumePopular.jointRichCommonBinLabels
          block.referenceHeight threshold).card : ENNReal) *
          (cap * volume block.jointSaturatedUnion)) := by
      apply mul_le_mul_right
      apply mul_le_mul_right
      rw [← volumePopular.jointFixedBinHeightRegion_volume block]
      exact block.jointFixedBin_volume_mul_square_le_saturation
    _ ≤ (volumePopular.popular.bins : ENNReal) *
        (4 * ((volumePopular.jointRichCommonBinLabels
          block.referenceHeight threshold).card : ENNReal) *
          (cap * (45 * volume oneParent.saturatedUnion))) := by
      gcongr
      exact oneParent.volume_retention
    _ ≤ (volumePopular.popular.bins : ENNReal) *
        (4 * ((volumePopular.jointRichCommonBinLabels
          block.referenceHeight threshold).card : ENNReal) *
          (cap * (45 * (512 * volume separated.saturatedUnion)))) := by
      gcongr
      exact separated.volume_retention
    _ = (volumePopular.popular.bins : ENNReal) * 4 *
        ((volumePopular.jointRichCommonBinLabels
          block.referenceHeight threshold).card : ENNReal) *
        (32 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN delta sigma *
          Kakeya.realRpowENN rho (2 - sigma)) *
        45 * 512 * volume separated.graphShading.union := by
      rw [separated.graphShading_union]
      ring

/-- Cancel the positive finite joint popularity, slice-cap, and residue cost
after a family-free scalar estimate has paid it. -/
theorem graph_volume_lower_of_sharpSourceSlabScalar
    (target : ENNReal)
    (hscalar :
      (volumePopular.popular.bins : ENNReal) * 4 *
          ((volumePopular.jointRichCommonBinLabels
            block.referenceHeight threshold).card : ENNReal) *
          (32 * Kakeya.realRpowENN delta (-inputLoss) *
            Kakeya.realRpowENN delta sigma *
            Kakeya.realRpowENN rho (2 - sigma)) *
          45 * 512 * target ≤
        volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) / 2 / 2 *
          ENNReal.ofReal (rho ^ 2)) :
    target ≤ volume separated.graphShading.union := by
  let cost : ENNReal :=
    (volumePopular.popular.bins : ENNReal) * 4 *
      ((volumePopular.jointRichCommonBinLabels
        block.referenceHeight threshold).card : ENNReal) *
      (32 * Kakeya.realRpowENN delta (-inputLoss) *
        Kakeya.realRpowENN delta sigma *
        Kakeya.realRpowENN rho (2 - sigma)) * 45 * 512
  have hbinsPos : 0 < (volumePopular.popular.bins : ENNReal) := by
    exact_mod_cast (show 0 < volumePopular.popular.bins by
      rw [volumePopular.popular.bins_eq]
      omega)
  have hlabelsPos : 0 <
      ((volumePopular.jointRichCommonBinLabels
        block.referenceHeight threshold).card : ENNReal) := by
    exact_mod_cast Finset.card_pos.mpr ⟨block.bin, block.bin_mem⟩
  have hcapPos : 0 <
      32 * Kakeya.realRpowENN delta (-inputLoss) *
        Kakeya.realRpowENN delta sigma *
        Kakeya.realRpowENN rho (2 - sigma) := by
    have hdelta : 0 < delta := current.grain.extremal.delta_pos
    have hrho : 0 < rho := by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos
    have hfirst : 0 < Kakeya.realRpowENN delta (-inputLoss) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)
    have hsecond : 0 < Kakeya.realRpowENN delta sigma :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)
    have hthird : 0 < Kakeya.realRpowENN rho (2 - sigma) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hrho _)
    exact ENNReal.mul_pos
      (ENNReal.mul_pos (ENNReal.mul_pos (by norm_num) hfirst.ne').ne'
        hsecond.ne').ne' hthird.ne'
  have hcostPos : 0 < cost := by
    dsimp only [cost]
    have hfourPos : 0 < (4 : ENNReal) := by norm_num
    have hfortyFivePos : 0 < (45 : ENNReal) := by norm_num
    have hfiveTwelvePos : 0 < (512 : ENNReal) := by norm_num
    exact ENNReal.mul_pos
      (ENNReal.mul_pos
        (ENNReal.mul_pos
          (ENNReal.mul_pos
            (ENNReal.mul_pos hbinsPos.ne' hfourPos.ne').ne' hlabelsPos.ne').ne'
          hcapPos.ne').ne' hfortyFivePos.ne').ne' hfiveTwelvePos.ne'
  have hcostTop : cost ≠ ⊤ := by
    dsimp only [cost]
    repeat' apply ENNReal.mul_ne_top
    all_goals first | exact ENNReal.natCast_ne_top _ |
      simp [Kakeya.realRpowENN]
  have hscaled :
      cost * target ≤ cost * volume separated.graphShading.union := by
    calc
      cost * target ≤
          volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) / 2 / 2 *
            ENNReal.ofReal (rho ^ 2) := by
        simpa [cost, mul_assoc] using hscalar
      _ ≤ cost * volume separated.graphShading.union := by
        simpa [cost, mul_assoc] using
          separated.sourceSlab_half_half_mul_square_le_graph
  exact (ENNReal.mul_le_mul_iff_left hcostPos.ne' hcostTop).mp <| by
    simpa only [mul_comm] using hscaled

/-- Cancel the positive finite popularity/residue cost after a P0 scalar
absorption has paid it on the source slab. -/
theorem graph_volume_lower_of_sourceSlabScalar
    (target : ENNReal)
    (hscalar :
      (volumePopular.popular.bins : ENNReal) *
          (4 * ((volumePopular.jointRichCommonBinLabels
            block.referenceHeight threshold).card : ENNReal) *
            (45 * 512)) * target ≤
        volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) /
          2 / 2) :
    target ≤ volume separated.graphShading.union := by
  let cost : ENNReal :=
    (volumePopular.popular.bins : ENNReal) *
      (4 * ((volumePopular.jointRichCommonBinLabels
        block.referenceHeight threshold).card : ENNReal) * (45 * 512))
  have hbinsNat : 0 < volumePopular.popular.bins := by
    rw [volumePopular.popular.bins_eq]
    omega
  have hlabelsNat :
      0 < (volumePopular.jointRichCommonBinLabels
        block.referenceHeight threshold).card :=
    Finset.card_pos.mpr ⟨block.bin, block.bin_mem⟩
  have hbinsPos : 0 < (volumePopular.popular.bins : ENNReal) := by
    exact_mod_cast hbinsNat
  have hlabelsPos : 0 <
      ((volumePopular.jointRichCommonBinLabels
        block.referenceHeight threshold).card : ENNReal) := by
    exact_mod_cast hlabelsNat
  have hfourPos : 0 < (4 : ENNReal) := by norm_num
  have hfixedPos : 0 < (45 * 512 : ENNReal) := by norm_num
  have hmiddlePos : 0 <
      (4 : ENNReal) * ((volumePopular.jointRichCommonBinLabels
        block.referenceHeight threshold).card : ENNReal) :=
    ENNReal.mul_pos hfourPos.ne' hlabelsPos.ne'
  have hrestPos : 0 <
      (4 : ENNReal) * ((volumePopular.jointRichCommonBinLabels
        block.referenceHeight threshold).card : ENNReal) * (45 * 512) :=
    ENNReal.mul_pos hmiddlePos.ne' hfixedPos.ne'
  have hcostPos : 0 < cost := by
    dsimp only [cost]
    exact ENNReal.mul_pos hbinsPos.ne' hrestPos.ne'
  have hcostTop : cost ≠ ⊤ := by
    dsimp only [cost]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _))
        (by norm_num))
  have hscaled :
      cost * target ≤ cost * volume separated.graphShading.union := by
    calc
      cost * target ≤
          volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) /
            2 / 2 := by simpa [cost, mul_assoc] using hscalar
      _ ≤ cost * volume separated.graphShading.union := by
        simpa [cost, mul_assoc] using separated.sourceSlab_half_half_le_graph
  calc
    target = cost⁻¹ * (cost * target) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hcostPos.ne' hcostTop, one_mul]
    _ ≤ cost⁻¹ * (cost * volume separated.graphShading.union) :=
      mul_le_mul_right hscaled _
    _ = volume separated.graphShading.union := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hcostPos.ne' hcostTop, one_mul]

noncomputable def graphInput
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : separated.graphScale ≤ 1) :
    PureWZ2AnchoredGraphGlobalInput
      (delta := separated.graphScale)
      (rho := separated.graphScale) (sigma := sigma)
      separated.graphShading
      (160 * Kakeya.realRpowENN delta (-inputLoss)) where
  rho_pos := separated.graphScale_pos
  delta_le_rho := le_rfl
  rho_le_one := hgraphOne
  sourceSlope := current.grain.globalGrains.slope
  sourceSlope_lipschitz := current.grain.globalGrains.slope_lipschitz
  sourceSlope_bound := current.grain.globalGrains.slope_bound
  constant_ne_top := ENNReal.mul_ne_top (by norm_num)
    (by simp [Kakeya.realRpowENN])
  shadow_ball := by
    intro point hpoint
    rw [separated.graphShading_union] at hpoint
    have hcoarse := separated.saturatedUnion_subset_secondRefined hpoint
    have hnorm := norm_le_two_of_mem_paperShading hcoarse
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  shadow_coordinate := by
    intro point hpoint coordinate
    rw [separated.graphShading_union] at hpoint
    have hcoarse := separated.saturatedUnion_subset_secondRefined hpoint
    have hbox := shading_union_subset_axisBox hcoarse
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  exactAD := by
    intro z hz
    rw [separated.graphShading_union]
    exact separated.saturatedUnion_exactAD hbridge hgraphOne z hz

/-- Fixed-line localization on the separated same-height saturation. -/
theorem fixedLine_localization
    (point : Point3) (hpoint : point ∈ separated.saturatedUnion) :
    |inner ℝ point
          (globalGrainDirection
            (current.grain.globalGrains.slope (point (2 : Fin 3)))) -
        (block.bin : ℝ) * Real.sqrt rho| ≤
      10 * Real.sqrt rho := by
  let root := Real.sqrt rho
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hrhoOne : rho ≤ 1 := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.2
  have hroot : 0 < root := Real.sqrt_pos.mpr hrho
  have hrhoRoot : rho ≤ root := by
    dsimp only [root]
    nlinarith [Real.sq_sqrt hrho.le, Real.sqrt_nonneg rho]
  rcases separated.saturatedUnion_exists_source_same_height hpoint with
    ⟨cell, _hcell, hpointSat, sourcePoint, hsourcePoint, hheight⟩
  have hsourceCube := hsourcePoint.2
  have hpointCube :
      point ∈ wz1PaperGridCube rho cell :=
    wz1PaperGridCubeSameHeightSaturation_subset_cube
      rho cell (block.jointCellSource cell) hpointSat
  have hpointSourceCoordinate :
      ∀ coordinate : Fin 3,
        |point coordinate - sourcePoint coordinate| ≤ 2 * rho := by
    intro coordinate
    have hdist :=
      wz1_paper_grid_cube_diameter_lt_two_rho
        (by
          rw [← pullback.rhoRequested_eq]
          exact twoScale.first.publicSticky.coarse_extremal.delta_pos)
        hpointCube hsourceCube
    have hcoordinateLe := PiLp.dist_apply_le point sourcePoint coordinate
    have hcoordinate :
        |point coordinate - sourcePoint coordinate| ≤ dist point sourcePoint := by
      simpa [Real.dist_eq] using hcoordinateLe
    exact hcoordinate.trans hdist.le
  have hsourceHeight :
      sourcePoint (2 : Fin 3) ∈ volumePopular.jointPopularHeights :=
    hsourcePoint.1.2
  have hreferenceRange :=
    volumePopular.jointPopularHeight_mem_paperRange block.referenceHeight_mem
  have hsourceReference :
      |sourcePoint (2 : Fin 3) - block.referenceHeight| ≤ root :=
    volumePopular.jointPopularHeights_close
      hsourceHeight block.referenceHeight_mem
  have hpointRange : point (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 := by
    have hcoarse := separated.saturatedUnion_subset_secondRefined hpoint
    have hbox := shading_union_subset_axisBox hcoarse
    simpa [Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2
  have hslopeDifference :
      |current.grain.globalGrains.slope (point (2 : Fin 3)) -
          current.grain.globalGrains.slope block.referenceHeight| ≤ root := by
    have hlip :=
      current.grain.globalGrains.slope_lipschitz.dist_le_mul
        (point (2 : Fin 3)) hpointRange
        block.referenceHeight hreferenceRange
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
    rw [hheight] at hsourceReference
    exact hlip.trans hsourceReference
  have hpointY : |point (1 : Fin 3)| ≤ 1 := by
    have hcoarse := separated.saturatedUnion_subset_secondRefined hpoint
    have hbox := shading_union_subset_axisBox hcoarse
    simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
  have hslopeProjection :
      |inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope (point (2 : Fin 3)))) -
          inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight))| ≤
        root := by
    have hformula :
        inner ℝ point
              (globalGrainDirection
                (current.grain.globalGrains.slope (point (2 : Fin 3)))) -
            inner ℝ point
              (globalGrainDirection
                (current.grain.globalGrains.slope block.referenceHeight)) =
          (current.grain.globalGrains.slope (point (2 : Fin 3)) -
              current.grain.globalGrains.slope block.referenceHeight) *
            point (1 : Fin 3) := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      ring
    rw [hformula, abs_mul]
    calc
      _ ≤ root * 1 := by
        exact mul_le_mul hslopeDifference hpointY
          (abs_nonneg _) hroot.le
      _ = root := by ring
  have hreferenceSlope :=
    current.grain.globalGrains.slope_bound
      block.referenceHeight hreferenceRange
  have hspatialProjection :
      |inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight)) -
          inner ℝ sourcePoint
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight))| ≤
        8 * rho := by
    have hformula :
        inner ℝ point
              (globalGrainDirection
                (current.grain.globalGrains.slope block.referenceHeight)) -
            inner ℝ sourcePoint
              (globalGrainDirection
                (current.grain.globalGrains.slope block.referenceHeight)) =
          (point 0 - sourcePoint 0) +
            current.grain.globalGrains.slope block.referenceHeight *
              (point 1 - sourcePoint 1) := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      ring
    rw [hformula]
    calc
      _ ≤ |point 0 - sourcePoint 0| +
          |current.grain.globalGrains.slope block.referenceHeight| *
            |point 1 - sourcePoint 1| := by
        simpa [abs_mul] using abs_add_le (point 0 - sourcePoint 0)
          (current.grain.globalGrains.slope block.referenceHeight *
            (point 1 - sourcePoint 1))
      _ ≤ 2 * rho + 3 * (2 * rho) := by
        gcongr <;> exact hpointSourceCoordinate _
      _ = 8 * rho := by ring
  have hlabel :
      Int.floor
        (inner ℝ sourcePoint
          (globalGrainDirection
            (current.grain.globalGrains.slope block.referenceHeight)) /
          root) = block.bin := by
    have hlabelRaw := hsourcePoint.1.1.2
    change Int.floor
      (inner ℝ sourcePoint
        (globalGrainDirection
          (current.grain.globalGrains.slope block.referenceHeight)) /
        Real.sqrt rho) = block.bin at hlabelRaw
    simpa [root] using hlabelRaw
  have hsourceStrip :
      |inner ℝ sourcePoint
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight)) -
          (block.bin : ℝ) * root| ≤ root := by
    have hlower := Int.floor_le
      (inner ℝ sourcePoint
        (globalGrainDirection
          (current.grain.globalGrains.slope block.referenceHeight)) / root)
    have hupper := Int.lt_floor_add_one
      (inner ℝ sourcePoint
        (globalGrainDirection
          (current.grain.globalGrains.slope block.referenceHeight)) / root)
    rw [hlabel] at hlower hupper
    rw [abs_le]
    constructor
    · have := (le_div_iff₀ hroot).mp hlower
      linarith
    · have := (div_lt_iff₀ hroot).mp hupper
      linarith
  calc
    _ ≤
        |inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope (point (2 : Fin 3)))) -
          inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight))| +
        |inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight)) -
          inner ℝ sourcePoint
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight))| +
        |inner ℝ sourcePoint
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight)) -
          (block.bin : ℝ) * root| := by
      have hone := abs_sub_le
        (inner ℝ point
          (globalGrainDirection
            (current.grain.globalGrains.slope (point (2 : Fin 3)))))
        (inner ℝ point
          (globalGrainDirection
            (current.grain.globalGrains.slope block.referenceHeight)))
        ((block.bin : ℝ) * root)
      have htwo := abs_sub_le
        (inner ℝ point
          (globalGrainDirection
            (current.grain.globalGrains.slope block.referenceHeight)))
        (inner ℝ sourcePoint
          (globalGrainDirection
            (current.grain.globalGrains.slope block.referenceHeight)))
        ((block.bin : ℝ) * root)
      linarith
    _ ≤ root + 8 * rho + root := by
      gcongr
    _ ≤ 10 * root := by linarith

/-- Prepare the separated production graph. -/
theorem graphPreparation
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : separated.graphScale ≤ 1)
    (hwindowAbsorb :
      separated.graphScale + Real.sqrt rho ≤
        Real.sqrt separated.graphScale) :
    Nonempty
      (PureWZ2AnchoredGraphPreparationData
        (separated.graphInput hbridge hgraphOne)) := by
  apply pureWZ2_anchoredGraphPreparation
    (separated.graphInput hbridge hgraphOne)
  · intro global hslope
    let slabLeft := volumePopular.jointSlabLeft
    let left := slabLeft - separated.graphScale / 2
    refine ⟨left, ?_⟩
    intro cell hcell
    have hactive :=
      (wz1Lemma23_mem_active_iff separated.graphShading
        separated.graphScale_pos cell).mp hcell
    rcases hactive.2 with ⟨point, hpoint, hpointCell⟩
    have hpointSaturated : point ∈ separated.saturatedUnion := by
      rwa [separated.graphShading_union] at hpoint
    have hheight := separated.saturatedUnion_height point hpointSaturated
    have hcenter :=
      ((wz1_lemma23_snapped_cell_geometry separated.graphScale
        separated.graphScale_pos hgraphOne).2.1
        cell point hpointCell).1 (2 : Fin 3)
    rw [abs_le] at hcenter
    constructor
    · dsimp only [left, slabLeft]
      linarith [hheight.1, hcenter.1]
    · dsimp only [left, slabLeft]
      linarith [hheight.2, hcenter.2, hwindowAbsorb]
  · intro global hslope
    have hsqrtGraph :
        Real.sqrt separated.graphScale = 16 * Real.sqrt rho := by
      unfold graphScale
      rw [Real.sqrt_mul (by norm_num),
        show Real.sqrt (256 : ℝ) = 16 by norm_num]
    refine ⟨fun _ => (block.bin : ℝ) * Real.sqrt rho, ?_⟩
    intro graphHeightIndex hgraphHeightIndex
    rintro value ⟨point, hpoint, rfl⟩
    have hpointSaturated : point ∈ separated.saturatedUnion := by
      rw [separated.graphShading_union] at hpoint
      exact hpoint.1
    have hbound := separated.fixedLine_localization point hpointSaturated
    rw [Metric.mem_closedBall, Real.dist_eq, hslope]
    change
      |inner ℝ point
          (globalGrainDirection
            (current.grain.globalGrains.slope
              (global.selectedHeight graphHeightIndex))) -
        (block.bin : ℝ) * Real.sqrt rho| ≤
        Real.sqrt separated.graphScale
    rw [← hpoint.2, hsqrtGraph]
    exact hbound.trans (by
      have hrho : 0 < rho := by
        rw [← pullback.rhoRequested_eq]
        exact twoScale.first.publicSticky.coarse_extremal.delta_pos
      nlinarith [Real.sqrt_pos.mpr hrho])

end PureWZ2Node05V4RichJointSeparatedParentData

end Kakeya.Assouad

end
