import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FaithfulPrismSegment
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.RotatedProjectedNormal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GridCubeCover
import MyLeanRepo.Kakeya.Assouad.WZ1.NeighborPackingBound

/-!
# Raw faithful x'z prism cover
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set Finset

attribute [local instance] Classical.propDecidable

private lemma pureWZ2_abs_floor_sub_le {x y : ℝ} {n : ℕ}
    (h : |x - y| ≤ (n : ℝ)) :
    |(Int.floor x : ℤ) - (Int.floor y : ℤ)| ≤ (n : ℤ) := by
  have hxy : x - y ≤ (n : ℝ) := (abs_le.mp h).2
  have hyx : y - x ≤ (n : ℝ) := by
    have : |y - x| = |x - y| := by rw [abs_sub_comm]
    exact (abs_le.mp (this.trans_le h)).2
  have hupperReal : (Int.floor x : ℝ) - (Int.floor y : ℝ) <
      (n : ℝ) + 1 := by
    linarith [Int.floor_le x, Int.lt_floor_add_one y]
  have hupper : (Int.floor x : ℤ) - Int.floor y ≤ (n : ℤ) := by
    by_contra hbad
    have : (n : ℤ) + 1 ≤ Int.floor x - Int.floor y := by omega
    exact (not_lt_of_ge (by exact_mod_cast this)) hupperReal
  have hlowerReal : (Int.floor y : ℝ) - (Int.floor x : ℝ) <
      (n : ℝ) + 1 := by
    linarith [Int.floor_le y, Int.lt_floor_add_one x]
  have hlower : -(n : ℤ) ≤ (Int.floor x : ℤ) - Int.floor y := by
    by_contra hbad
    have : (n : ℤ) + 1 ≤ Int.floor y - Int.floor x := by omega
    exact (not_lt_of_ge (by exact_mod_cast this)) hlowerReal
  exact abs_le.mpr ⟨hlower, hupper⟩

structure PureWZ2FaithfulRawPrismCover
    {sigma grainLoss slabLoss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale)
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (frameSlope : ℝ)
    (common : PureWZ2RotatedWeightedCommonYCore
      cfg scale scaleData popular frameSlope)
    (rho : ℝ) where
  prismCount : ℕ
  prismCount_pos : 0 < prismCount
  gridIndex : Fin prismCount → ℤ
  gridIndex_injective : Function.Injective gridIndex
  sourceLabel : Fin prismCount → common.selectedLabels
  sourcePoint : Fin prismCount → {point : Point3 // point ∈ cfg.shading.union}
  source_mem_label : ∀ j, (sourcePoint j).1 ∈
    pureWZ2WeightedCroppedLabelRegion popular (sourceLabel j).1
  source_near_common_y : ∀ j,
    |pureWZ2HorizontalRotation frameSlope (sourcePoint j).1 1 - common.y0| ≤
      scale.1
  /-- Error between the selected global-grain labels and the fixed frame.
  It is supplied by the caller, rather than being tied to the quadratic
  Lemma-31 contradiction estimate. -/
  frameGap : ℝ
  frameGap_nonneg : 0 ≤ frameGap
  frameGap_small : 4 * frameGap ≤ scale.1 / 4
  frameGap_le_rho : 2 * frameGap ≤ rho
  selected_label_frame_close : ∀ label (hlabel : label ∈ common.selectedLabels),
    |cfg.globalGrains.slope
        ((pureWZ2PaperCellCenter delta
          (popular.label_anchor label
            (common.selectedLabels_subset hlabel))) 2) - frameSlope| ≤
      frameGap
  prism : Fin prismCount → Set Point3
  prism_eq : ∀ j, prism j =
    pureWZ2RotatedXZGridPrism frameSlope 0
      scaleData.slabLeft scaleData.slabRight (gridIndex j)
  source_near_prism : ∀ j point, point ∈ prism j →
    |pureWZ2HorizontalRotation frameSlope (sourcePoint j).1 0 -
        pureWZ2HorizontalRotation frameSlope point 0| ≤
          scale.1 + (8 * delta + 2 * frameGap) ∧
      |(sourcePoint j).1 2 - point 2| ≤ scale.1 + 8 * delta
  prismNormal : Fin prismCount → Point3
  prismNormal_eq : ∀ j, prismNormal j =
    pureWZ2NormalizedFrameProjectedNormal frameSlope
      (cfg.localGrains.planeMap (sourcePoint j))
  source_frame_projected_lower : ∀ j,
    (1 / 16 : ℝ) ≤
      ‖pureWZ2FrameProjectedNormal frameSlope
        (cfg.localGrains.planeMap (sourcePoint j))‖
  prismNormal_unit : ∀ j, ‖prismNormal j‖ = 1
  prismNormal_rotated_y_zero : ∀ j,
    pureWZ2HorizontalRotation frameSlope (prismNormal j) 1 = 0
  prism_card_raw :
    (prismCount : ENNReal) ≤
      4 * (common.rotatedCoverCenters.filter fun center =>
        |center 1 - common.y0| ≤ scale.1).card
  piece : Fin cfg.family.card → Fin prismCount → Set Point3
  piece_eq : ∀ tube j, piece tube j =
    common.F2.carrier tube ∩ prism j
  piece_measurable : ∀ tube j, MeasurableSet (piece tube j)
  covers : ∀ tube point, point ∈ common.F2.carrier tube →
    ∃ j, point ∈ piece tube j
  support_card : ∀ tube,
    ((Finset.univ : Finset (Fin prismCount)).filter fun j =>
      volume (piece tube j) ≠ 0).card ≤ 3
  segmentStart : Fin cfg.family.card → ℝ
  piece_sub_segment : ∀ tube j, piece tube j ⊆
    tubeSegmentCarrier (6 * delta) (cfg.family.tube tube).base
      (cfg.family.tube tube).direction (segmentStart tube) rho

private lemma pureWZ2_cell_center_in_own_prism
    {delta frameSlope a b : ℝ} (_hdelta : 0 < delta)
    (hwidth : 0 < b - a) (cell : ℤ × ℤ × ℤ)
    (hslab : pureWZ2PaperCellCenter delta cell 2 ∈ Set.Icc a b) :
    pureWZ2PaperCellCenter delta cell ∈
      pureWZ2RotatedXZGridPrism frameSlope 0 a b
        (Int.floor (pureWZ2HorizontalRotation frameSlope
          (pureWZ2PaperCellCenter delta cell) 0 / (b - a))) := by
  rw [pureWZ2RotatedXZGridPrism_mem]
  refine ⟨?_, hslab⟩
  let value := pureWZ2HorizontalRotation frameSlope
    (pureWZ2PaperCellCenter delta cell) 0 / (b - a)
  have hlower : (Int.floor value : ℝ) ≤ value := Int.floor_le _
  have hupper : value < (Int.floor value : ℝ) + 1 :=
    Int.lt_floor_add_one _
  rw [Set.mem_Ico]
  simp only [zero_add]
  constructor
  · have hmul := mul_le_mul_of_nonneg_right hlower hwidth.le
    have hcancel : value * (b - a) =
        pureWZ2HorizontalRotation frameSlope
          (pureWZ2PaperCellCenter delta cell) 0 := by
      dsimp only [value]
      field_simp [hwidth.ne']
    rw [hcancel] at hmul
    exact hmul
  · have hmul := mul_lt_mul_of_pos_right hupper hwidth
    have hcancel : value * (b - a) =
        pureWZ2HorizontalRotation frameSlope
          (pureWZ2PaperCellCenter delta cell) 0 := by
      dsimp only [value]
      field_simp [hwidth.ne']
    rw [hcancel] at hmul
    exact hmul

private lemma pureWZ2_point_mem_own_prism
    {frameSlope a b : ℝ} (hwidth : 0 < b - a)
    (point : Point3) (hslab : point 2 ∈ Set.Icc a b) :
    point ∈ pureWZ2RotatedXZGridPrism frameSlope 0 a b
      (Int.floor (pureWZ2HorizontalRotation frameSlope point 0 / (b - a))) := by
  rw [pureWZ2RotatedXZGridPrism_mem]
  refine ⟨?_, hslab⟩
  let value := pureWZ2HorizontalRotation frameSlope point 0 / (b - a)
  have hlower : (Int.floor value : ℝ) ≤ value := Int.floor_le _
  have hupper : value < (Int.floor value : ℝ) + 1 := Int.lt_floor_add_one _
  rw [Set.mem_Ico]
  simp only [zero_add]
  constructor
  · have hmul := mul_le_mul_of_nonneg_right hlower hwidth.le
    have hcancel : value * (b - a) =
        pureWZ2HorizontalRotation frameSlope point 0 := by
      dsimp only [value]
      field_simp [hwidth.ne']
    rwa [hcancel] at hmul
  · have hmul := mul_lt_mul_of_pos_right hupper hwidth
    have hcancel : value * (b - a) =
        pureWZ2HorizontalRotation frameSlope point 0 := by
      dsimp only [value]
      field_simp [hwidth.ne']
    rwa [hcancel] at hmul
private lemma pureWZ2_point_floor_mem_center_neighbors
    {delta frameSlope width : ℝ} (hdelta : 0 < delta)
    (hwidth : 0 < width) (hsmall : 256 * delta ≤ width)
    {cell : ℤ × ℤ × ℤ} {point : Point3}
    (hpoint : point ∈ wz1PaperGridCube delta cell) :
    let centerIndex := Int.floor
      (pureWZ2HorizontalRotation frameSlope
        (pureWZ2PaperCellCenter delta cell) 0 / width)
    Int.floor (pureWZ2HorizontalRotation frameSlope point 0 / width) ∈
      ({centerIndex - 1, centerIndex, centerIndex + 1} : Finset ℤ) := by
  dsimp only
  let rotation := pureWZ2HorizontalRotation frameSlope
  let center := pureWZ2PaperCellCenter delta cell
  have hcenter := pureWZ2PaperCellCenter_mem hdelta cell
  have hdist : dist point center ≤ delta * Real.sqrt 3 :=
    dist_le_sqrt3_of_mem_wz1PaperGridCube hdelta hpoint hcenter
  have hcoord : |rotation point 0 - rotation center 0| ≤
      delta * Real.sqrt 3 := by
    have happly := PiLp.dist_apply_le (rotation point) (rotation center) 0
    rw [rotation.isometry.dist_eq] at happly
    exact happly.trans hdist
  have hsqrt : Real.sqrt 3 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_nonneg 3]
  have hcoordWidth : |rotation point 0 - rotation center 0| < width := by
    calc
      |rotation point 0 - rotation center 0| ≤ delta * Real.sqrt 3 := hcoord
      _ < delta * 2 := mul_lt_mul_of_pos_left hsqrt hdelta
      _ ≤ width := by linarith
  have hratio : |rotation point 0 / width - rotation center 0 / width| < 1 := by
    rw [← sub_div, abs_div, abs_of_pos hwidth]
    exact (div_lt_one hwidth).2 hcoordWidth
  have hfloor := pureWZ2_abs_floor_sub_le
    (x := rotation point 0 / width)
    (y := rotation center 0 / width) (n := 1)
      (by simpa only [Nat.cast_one] using hratio.le)
  have halternatives :
      Int.floor (rotation point 0 / width) =
          Int.floor (rotation center 0 / width) - 1 ∨
      Int.floor (rotation point 0 / width) =
          Int.floor (rotation center 0 / width) ∨
      Int.floor (rotation point 0 / width) =
          Int.floor (rotation center 0 / width) + 1 := by
    rw [abs_le] at hfloor
    omega
  change Int.floor (rotation point 0 / width) ∈
    ({Int.floor (rotation center 0 / width) - 1,
      Int.floor (rotation center 0 / width),
      Int.floor (rotation center 0 / width) + 1} : Finset ℤ)
  rcases halternatives with (h | h | h)
  all_goals rw [h] <;> simp

/-- Raw cover construction, before local AD and heavy-piece regularization. -/
theorem pureWZ2_faithful_raw_prism_cover_of_frame_lower
    {sigma grainLoss slabLoss delta rho : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale)
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (frameSlope : ℝ)
    (common : PureWZ2RotatedWeightedCommonYCore
      cfg scale scaleData popular frameSlope)
    (frameGap : ℝ)
    (hframeGap : 0 ≤ frameGap)
    (hlabelClose : ∀ label (hlabel : label ∈ common.selectedLabels),
      |cfg.globalGrains.slope
          ((pureWZ2PaperCellCenter delta
            (popular.label_anchor label
              (common.selectedLabels_subset hlabel))) 2) - frameSlope| ≤
        frameGap)
    (hframeGapSmall : 4 * frameGap ≤ scale.1 / 4)
    (hframeGapRho : 2 * frameGap ≤ rho)
    (hframeSource : ∀ label (hlabel : label ∈ common.selectedLabels),
      ∃ source : {point : Point3 // point ∈ cfg.shading.union},
        source.1 ∈ pureWZ2WeightedCroppedLabelRegion popular label ∧
        |pureWZ2HorizontalRotation frameSlope source.1 1 - common.y0| ≤
          scale.1 ∧
        (1 / 16 : ℝ) ≤
          ‖pureWZ2FrameProjectedNormal frameSlope
            (cfg.localGrains.planeMap source)‖)
    (hrhoPos : 0 < rho)
    (hsqrtRho : Real.sqrt rho = 8 * scale.1)
    (hsmall : 256 * delta ≤ scale.1)
    (hscaleSmall : scale.1 ≤ 1 / 32) :
    Nonempty (PureWZ2FaithfulRawPrismCover
      cfg scale scaleData popular frameSlope common rho) := by
  let rotation := pureWZ2HorizontalRotation frameSlope
  let width := scale.1
  have hwidth : 0 < width := cfg.extremal.delta_pos.trans_le scale.2.1
  have hslabWidth : scaleData.slabRight - scaleData.slabLeft = width :=
    scaleData.slab_width
  let cellIndex : (ℤ × ℤ × ℤ) → ℤ := fun cell =>
    Int.floor (rotation (pureWZ2PaperCellCenter delta cell) 0 /
      (scaleData.slabRight - scaleData.slabLeft))
  let candidateIndices := common.selectedCells.biUnion fun cell =>
    ({cellIndex cell - 1, cellIndex cell, cellIndex cell + 1} : Finset ℤ)
  let indices := candidateIndices.filter fun index =>
    (common.F2.union ∩ pureWZ2RotatedXZGridPrism frameSlope 0
      scaleData.slabLeft scaleData.slabRight index).Nonempty
  have hindicesNonempty : indices.Nonempty := by
    rcases common.selectedLabels_nonempty with ⟨label, hlabel⟩
    have hkept := common.selectedLabels_subset hlabel
    let cell := popular.label_anchor label hkept
    have hcell : cell ∈ common.selectedCells := by
      rw [common.selectedCells_eq]
      exact Finset.mem_biUnion.mpr
        ⟨label, hlabel, popular.label_anchor_mem label hkept⟩
    let point := pureWZ2PaperCellCenter delta cell
    have hpointCell := pureWZ2PaperCellCenter_mem cfg.extremal.delta_pos cell
    have hpointF2 : point ∈ common.F2.union := by
      rw [common.F2_union_eq]
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCell⟩
    have hpointSlab : point 2 ∈
        Set.Icc scaleData.slabLeft scaleData.slabRight := by
      have hcellRetained := common.selectedCells_subset hcell
      have hcellActive := popular.retainedCells_subset hcellRetained
      have hactive : cell ∈ wz1PaperActiveCells scaleData.slabShading
          cfg.extremal.delta_pos := by
        simpa [popular.activeCells_eq] using hcellActive
      rcases pureWZ2_activeCellCenter_mem_union cfg.extremal.delta_pos
          scaleData.slab_cubical hactive with ⟨tube, htube⟩
      exact scaleData.slab_in_slab tube htube
    have hpointPrism := pureWZ2_cell_center_in_own_prism
      (delta := delta) (frameSlope := frameSlope)
      (a := scaleData.slabLeft) (b := scaleData.slabRight)
      cfg.extremal.delta_pos (sub_pos.mpr scaleData.slab_ordered) cell hpointSlab
    refine ⟨cellIndex cell, Finset.mem_filter.mpr ⟨?_,
      point, hpointF2, ?_⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨cell, hcell, by simp⟩
    · change pureWZ2PaperCellCenter delta cell ∈
        pureWZ2RotatedXZGridPrism frameSlope 0 scaleData.slabLeft
          scaleData.slabRight (cellIndex cell)
      simpa [cellIndex, rotation] using hpointPrism
  let prismCount := indices.card
  have hprismCount : 0 < prismCount := hindicesNonempty.card_pos
  let indexList := indices.toList
  have hlistLength : indexList.length = prismCount := by
    simp [indexList, prismCount]
  let gridIndex (prism : Fin prismCount) : ℤ :=
    indexList.get ⟨prism.1, by simpa [hlistLength] using prism.2⟩
  have hgridInjective : Function.Injective gridIndex := by
    intro first second heq
    apply Fin.ext
    have hnodup := Finset.nodup_toList indices
    have hpositions := hnodup.get_inj_iff.mp heq
    injection hpositions
  have hgridMem : ∀ prism, gridIndex prism ∈ indices := by
    intro prism
    exact Finset.mem_toList.mp (List.get_mem indexList
      ⟨prism.1, by simpa [hlistLength] using prism.2⟩)
  have hoccupied : ∀ prism : Fin prismCount,
      ∃ point, point ∈ common.F2.union ∧
        point ∈ pureWZ2RotatedXZGridPrism frameSlope 0
          scaleData.slabLeft scaleData.slabRight (gridIndex prism) := by
    intro prism
    exact (Finset.mem_filter.mp (hgridMem prism)).2
  choose occupiedPoint hoccupiedF2 hoccupiedPrism using hoccupied
  have hsource : ∀ prism : Fin prismCount,
      ∃ label, label ∈ common.selectedLabels ∧
        occupiedPoint prism ∈ pureWZ2WeightedCroppedLabelRegion popular label ∧
        ∃ source, source ∈ pureWZ2WeightedCroppedLabelRegion popular label ∧
          rotation source 1 = common.y0 := by
    intro prism
    exact common.exists_common_slice_companion (hoccupiedF2 prism)
  choose sourceLabel hsourceLabel sourceOccupied
    commonPoint hcommonPoint hcommonY using hsource
  have hnormalSource : ∀ prism : Fin prismCount,
      ∃ source : {point : Point3 // point ∈ cfg.shading.union},
        source.1 ∈ pureWZ2WeightedCroppedLabelRegion popular
          (sourceLabel prism) ∧
        |rotation source.1 1 - common.y0| ≤ width ∧
        (1 / 16 : ℝ) ≤
          ‖pureWZ2FrameProjectedNormal frameSlope
            (cfg.localGrains.planeMap source)‖ := by
    intro prism
    exact hframeSource (sourceLabel prism) (hsourceLabel prism)
  choose sourceSubtype hsourcePoint hsourceY hsourceLower using hnormalSource
  let sourceLabelSubtype : Fin prismCount → common.selectedLabels :=
    fun prism => ⟨sourceLabel prism, hsourceLabel prism⟩
  let prism : Fin prismCount → Set Point3 := fun j =>
    pureWZ2RotatedXZGridPrism frameSlope 0
      scaleData.slabLeft scaleData.slabRight (gridIndex j)
  have hsourceNear : ∀ j point, point ∈ prism j →
      |rotation (sourceSubtype j).1 0 - rotation point 0| ≤
          width + (8 * delta + 2 * frameGap) ∧
        |(sourceSubtype j).1 2 - point 2| ≤ width + 8 * delta := by
    intro j point hpoint
    have hoccupiedGrid := hoccupiedPrism j
    have hsame := pureWZ2_fixedFrame_globalGrain_pair_diameter
      cfg.globalGrains.slope cfg.extremal.delta_pos.le hframeGap
      (pureWZ2PaperCellCenter delta (popular.label_anchor
        (sourceLabel j) (common.selectedLabels_subset (hsourceLabel j))))
      (hlabelClose (sourceLabel j) (hsourceLabel j))
      ⟨popular.label_grain_containment (sourceLabel j)
          (common.selectedLabels_subset (hsourceLabel j)) (hsourcePoint j).1,
        (hsourcePoint j).2⟩
      ⟨popular.label_grain_containment (sourceLabel j)
          (common.selectedLabels_subset (hsourceLabel j)) (sourceOccupied j).1,
        (sourceOccupied j).2⟩
    rw [pureWZ2RotatedXZGridPrism_mem] at hoccupiedGrid hpoint
    constructor
    · calc
        |rotation (sourceSubtype j).1 0 - rotation point 0| ≤
            |rotation (sourceSubtype j).1 0 - rotation (occupiedPoint j) 0| +
            |rotation (occupiedPoint j) 0 - rotation point 0| := by
          simpa only [show rotation (sourceSubtype j).1 0 - rotation point 0 =
            (rotation (sourceSubtype j).1 0 - rotation (occupiedPoint j) 0) +
            (rotation (occupiedPoint j) 0 - rotation point 0) by ring]
            using abs_add_le _ _
        _ ≤ (8 * delta + 2 * frameGap) + width := by
          have hgrid : |rotation (occupiedPoint j) 0 - rotation point 0| ≤
              width := by
            rw [abs_le]
            constructor <;> linarith [hoccupiedGrid.1.1, hoccupiedGrid.1.2,
              hpoint.1.1, hpoint.1.2, hslabWidth]
          have hsameX : |rotation (sourceSubtype j).1 0 -
              rotation (occupiedPoint j) 0| ≤ 8 * delta + 2 * frameGap := by
            change |pureWZ2HorizontalRotation frameSlope (sourceSubtype j).1 0 -
              pureWZ2HorizontalRotation frameSlope (occupiedPoint j) 0| ≤
                8 * delta + 2 * frameGap
            simpa using hsame.1
          exact add_le_add hsameX hgrid
        _ = width + (8 * delta + 2 * frameGap) := by ring
    · calc
        |(sourceSubtype j).1 2 - point 2| ≤
            |(sourceSubtype j).1 2 - occupiedPoint j 2| +
            |occupiedPoint j 2 - point 2| := by
          simpa only [show (sourceSubtype j).1 2 - point 2 =
            ((sourceSubtype j).1 2 - occupiedPoint j 2) +
            (occupiedPoint j 2 - point 2) by ring] using abs_add_le _ _
        _ ≤ 8 * delta + width := by
          have hgrid : |occupiedPoint j 2 - point 2| ≤ width := by
            rw [abs_le]
            constructor <;> linarith [hoccupiedGrid.2.1, hoccupiedGrid.2.2,
              hpoint.2.1, hpoint.2.2, hslabWidth]
          exact add_le_add (by simpa [rotation] using hsame.2) hgrid
        _ = width + 8 * delta := by ring
  let prismNormal : Fin prismCount → Point3 := fun j =>
    pureWZ2NormalizedFrameProjectedNormal frameSlope
      (cfg.localGrains.planeMap (sourceSubtype j))
  have hprismNormalUnit : ∀ j, ‖prismNormal j‖ = 1 := by
    intro j
    apply pureWZ2NormalizedFrameProjectedNormal_unit
    exact lt_of_lt_of_le (by norm_num)
      (hsourceLower j)
  have hprismNormalY : ∀ j, rotation (prismNormal j) 1 = 0 := by
    intro j
    exact pureWZ2FrameProjectedNormal_rotated_y_zero _ _
  let activeCenters := common.rotatedCoverCenters.filter fun center =>
    |center 1 - common.y0| ≤ width
  have hsourceCovered : ∀ j : Fin prismCount,
      ∃ center ∈ activeCenters,
        rotation (commonPoint j) ∈ Metric.closedBall center width := by
    intro j
    have hsourceSlab : commonPoint j ∈ scaleData.slabShading.union := by
      have hregion := hcommonPoint j
      rw [pureWZ2WeightedCroppedLabelRegion_eq] at hregion
      rcases Set.mem_iUnion₂.mp hregion with ⟨cell, hcellFiber, hpointCell⟩
      have hactive := (mem_pureWZ2GlobalGrainFiber cfg.globalGrains.slope
        delta popular.activeCells (sourceLabel j) cell).mp hcellFiber |>.1
      have hslabActive : cell ∈ wz1PaperActiveCells scaleData.slabShading
          cfg.extremal.delta_pos := by
        simpa [popular.activeCells_eq] using hactive
      rw [scaleData.slab_cubical.union_eq_activeCells cfg.extremal.delta_pos]
      exact Set.mem_iUnion₂.mpr ⟨cell, hslabActive, hpointCell⟩
    rcases common.rotated_cover (rotation (commonPoint j))
        ⟨commonPoint j, hsourceSlab, rfl⟩ with ⟨center, hcenter, hball⟩
    have hy : |center 1 - common.y0| ≤ width := by
      have hcoord : |rotation (commonPoint j) 1 - center 1| ≤ width :=
        (PiLp.norm_apply_le (rotation (commonPoint j) - center) 1).trans hball
      rw [hcommonY j] at hcoord
      simpa [abs_sub_comm] using hcoord
    exact ⟨center, Finset.mem_filter.mpr ⟨hcenter, hy⟩, hball⟩
  let assignedCenter : Fin prismCount → Point3 := fun j =>
    Classical.choose (hsourceCovered j)
  have hassignedMem : ∀ j, assignedCenter j ∈ activeCenters := fun j =>
    (Classical.choose_spec (hsourceCovered j)).1
  have hassignedBall : ∀ j, rotation (commonPoint j) ∈
      Metric.closedBall (assignedCenter j) width := fun j =>
    (Classical.choose_spec (hsourceCovered j)).2
  have hfiberCard : ∀ center ∈ activeCenters,
      ((Finset.univ : Finset (Fin prismCount)).filter fun j =>
        assignedCenter j = center).card ≤ 4 := by
    intro center hcenter
    let fiber := (Finset.univ : Finset (Fin prismCount)).filter fun j =>
      assignedCenter j = center
    have hgridCard : fiber.card = (fiber.image gridIndex).card := by
      rw [Finset.card_image_of_injective _ hgridInjective]
    rw [hgridCard]
    let values : Set ℝ := {value | ∃ j ∈ fiber,
      value = rotation (occupiedPoint j) 0}
    have hdiam : ∀ first second, first ∈ values → second ∈ values →
      |first - second| < 3 * width := by
      intro first second hfirst hsecond
      rcases hfirst with ⟨firstIndex, hfirstFiber, rfl⟩
      rcases hsecond with ⟨secondIndex, hsecondFiber, rfl⟩
      have hfirstCenter := (Finset.mem_filter.mp hfirstFiber).2
      have hsecondCenter := (Finset.mem_filter.mp hsecondFiber).2
      have hfirstBall := hassignedBall firstIndex
      have hsecondBall := hassignedBall secondIndex
      rw [hfirstCenter] at hfirstBall
      rw [hsecondCenter] at hsecondBall
      have hfirstSourceX :
          |rotation (commonPoint firstIndex) 0 - center 0| ≤ width :=
        (PiLp.norm_apply_le
          (rotation (commonPoint firstIndex) - center) 0).trans hfirstBall
      have hsecondSourceX :
          |center 0 - rotation (commonPoint secondIndex) 0| ≤ width := by
        simpa [abs_sub_comm] using
          (PiLp.norm_apply_le
            (rotation (commonPoint secondIndex) - center) 0).trans hsecondBall
      have hfirstSame := pureWZ2_fixedFrame_globalGrain_pair_diameter
        cfg.globalGrains.slope cfg.extremal.delta_pos.le hframeGap
        (pureWZ2PaperCellCenter delta (popular.label_anchor
          (sourceLabel firstIndex)
          (common.selectedLabels_subset (hsourceLabel firstIndex))))
        (hlabelClose (sourceLabel firstIndex) (hsourceLabel firstIndex))
        ⟨popular.label_grain_containment (sourceLabel firstIndex)
            (common.selectedLabels_subset (hsourceLabel firstIndex))
            (hcommonPoint firstIndex).1, (hcommonPoint firstIndex).2⟩
        ⟨popular.label_grain_containment (sourceLabel firstIndex)
            (common.selectedLabels_subset (hsourceLabel firstIndex))
            (sourceOccupied firstIndex).1, (sourceOccupied firstIndex).2⟩
      have hsecondSame := pureWZ2_fixedFrame_globalGrain_pair_diameter
        cfg.globalGrains.slope cfg.extremal.delta_pos.le hframeGap
        (pureWZ2PaperCellCenter delta (popular.label_anchor
          (sourceLabel secondIndex)
          (common.selectedLabels_subset (hsourceLabel secondIndex))))
        (hlabelClose (sourceLabel secondIndex) (hsourceLabel secondIndex))
        ⟨popular.label_grain_containment (sourceLabel secondIndex)
            (common.selectedLabels_subset (hsourceLabel secondIndex))
            (hcommonPoint secondIndex).1, (hcommonPoint secondIndex).2⟩
        ⟨popular.label_grain_containment (sourceLabel secondIndex)
            (common.selectedLabels_subset (hsourceLabel secondIndex))
            (sourceOccupied secondIndex).1, (sourceOccupied secondIndex).2⟩
      have hfirstOccupiedX :
          |rotation (occupiedPoint firstIndex) 0 -
              rotation (commonPoint firstIndex) 0| ≤
                8 * delta + 2 * frameGap := by
        change |pureWZ2HorizontalRotation frameSlope
            (occupiedPoint firstIndex) 0 -
          pureWZ2HorizontalRotation frameSlope
            (commonPoint firstIndex) 0| ≤ 8 * delta + 2 * frameGap
        have hfirstSame' := hfirstSame.1
        rw [abs_sub_comm] at hfirstSame'
        simpa using hfirstSame'
      have hsecondOccupiedX :
          |rotation (commonPoint secondIndex) 0 -
              rotation (occupiedPoint secondIndex) 0| ≤
                8 * delta + 2 * frameGap :=
        (by
          change |pureWZ2HorizontalRotation frameSlope
              (commonPoint secondIndex) 0 -
            pureWZ2HorizontalRotation frameSlope
              (occupiedPoint secondIndex) 0| ≤ 8 * delta + 2 * frameGap
          simpa using hsecondSame.1)
      calc
        |rotation (occupiedPoint firstIndex) 0 -
            rotation (occupiedPoint secondIndex) 0| ≤
            |rotation (occupiedPoint firstIndex) 0 -
              rotation (commonPoint firstIndex) 0| +
            |rotation (commonPoint firstIndex) 0 - center 0| +
            (|center 0 - rotation (commonPoint secondIndex) 0| +
              |rotation (commonPoint secondIndex) 0 -
                rotation (occupiedPoint secondIndex) 0|) := by
          have hdecomp :
              rotation (occupiedPoint firstIndex) 0 -
                  rotation (occupiedPoint secondIndex) 0 =
                ((rotation (occupiedPoint firstIndex) 0 -
                    rotation (commonPoint firstIndex) 0) +
                  (rotation (commonPoint firstIndex) 0 - center 0)) +
                ((center 0 - rotation (commonPoint secondIndex) 0) +
                  (rotation (commonPoint secondIndex) 0 -
                    rotation (occupiedPoint secondIndex) 0)) := by ring
          rw [hdecomp]
          exact (abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) (abs_add_le _ _))
        _ ≤ (8 * delta + 2 * frameGap) + width +
            (width + (8 * delta + 2 * frameGap)) := by gcongr
        _ < 3 * width := by
          have hwidthSmall : width ≤ 1 / 32 := by
            simpa [width] using hscaleSmall
          have hdeltaWidth : 16 * delta ≤ width / 16 := by
            dsimp only [width]
            linarith [hsmall]
          have hgapWidth : 4 * frameGap ≤ width / 4 := by
            simpa only [width] using hframeGapSmall
          linarith
    have hfiltered :
        (fiber.image gridIndex).filter (fun (index : ℤ) =>
          (values ∩ Set.Ico
            (0 + (index : ℝ) * width)
            (0 + ((index : ℝ) + 1) * width)).Nonempty) =
          fiber.image gridIndex := by
      apply Finset.filter_true_of_mem
      intro index hindex
      rcases Finset.mem_image.mp hindex with ⟨j, hj, rfl⟩
      refine ⟨rotation (occupiedPoint j) 0, ⟨j, hj, rfl⟩, ?_⟩
      have hoccupied := hoccupiedPrism j
      rw [pureWZ2RotatedXZGridPrism_mem] at hoccupied
      change pureWZ2HorizontalRotation frameSlope (occupiedPoint j) 0 ∈
        Set.Ico (0 + (gridIndex j : ℝ) * width)
          (0 + ((gridIndex j : ℝ) + 1) * width)
      simpa [hslabWidth] using hoccupied.1
    rw [← hfiltered]
    exact pureWZ2_set_meets_at_most_four_intervals hwidth hdiam
      (fiber.image gridIndex)
  have hprismCardNat : prismCount ≤ 4 * activeCenters.card := by
    have hpartition : (Finset.univ : Finset (Fin prismCount)) =
        activeCenters.biUnion (fun center =>
          (Finset.univ : Finset (Fin prismCount)).filter fun j =>
            assignedCenter j = center) := by
      ext j
      simp only [Finset.mem_univ, true_iff, Finset.mem_biUnion,
        Finset.mem_filter, true_and]
      exact ⟨assignedCenter j, hassignedMem j, rfl⟩
    calc
      prismCount = (Finset.univ : Finset (Fin prismCount)).card := by simp
      _ = (activeCenters.biUnion (fun center =>
          (Finset.univ : Finset (Fin prismCount)).filter fun j =>
            assignedCenter j = center)).card := by rw [← hpartition]
      _ ≤ ∑ center ∈ activeCenters,
          ((Finset.univ : Finset (Fin prismCount)).filter fun j =>
            assignedCenter j = center).card := Finset.card_biUnion_le
      _ ≤ ∑ _center ∈ activeCenters, 4 :=
        Finset.sum_le_sum hfiberCard
      _ = 4 * activeCenters.card := by simp [Finset.sum_const]; ring
  let piece : Fin cfg.family.card → Fin prismCount → Set Point3 :=
    fun tube j => common.F2.carrier tube ∩ prism j
  have hpieceMeasurable : ∀ tube j, MeasurableSet (piece tube j) :=
    fun tube j => (common.F2.measurable_carrier tube).inter
      (measurableSet_pureWZ2RotatedXZGridPrism _ _ _ _ _)
  have hcovers : ∀ tube point, point ∈ common.F2.carrier tube →
      ∃ prism, point ∈ piece tube prism := by
    intro tube point hpoint
    have hpointUnion : point ∈ common.F2.union := ⟨tube, hpoint⟩
    rw [common.F2_union_eq] at hpointUnion
    rcases Set.mem_iUnion₂.mp hpointUnion with ⟨cell, hcell, hpointCell⟩
    let pointIndex := Int.floor (rotation point 0 /
      (scaleData.slabRight - scaleData.slabLeft))
    have hcandidate : pointIndex ∈ candidateIndices := by
      apply Finset.mem_biUnion.mpr
      refine ⟨cell, hcell, ?_⟩
      have hneighbor := pureWZ2_point_floor_mem_center_neighbors
        (frameSlope := frameSlope) cfg.extremal.delta_pos
        (sub_pos.mpr scaleData.slab_ordered)
        (by rw [scaleData.slab_width]; exact hsmall) hpointCell
      simpa [pointIndex, cellIndex, rotation] using hneighbor
    have hpointSlab := common.F2_in_slab tube hpoint
    have hpointPrism : point ∈ pureWZ2RotatedXZGridPrism frameSlope 0
        scaleData.slabLeft scaleData.slabRight pointIndex := by
      exact pureWZ2_point_mem_own_prism
        (sub_pos.mpr scaleData.slab_ordered) point hpointSlab
    have hindex : pointIndex ∈ indices := Finset.mem_filter.mpr
      ⟨hcandidate, point, ⟨tube, hpoint⟩, hpointPrism⟩
    have hlist : pointIndex ∈ indexList := by
      simpa [indexList] using hindex
    rcases List.mem_iff_get.mp hlist with ⟨position, hposition⟩
    let prismIndex : Fin prismCount :=
      ⟨position.1, by simpa [hlistLength] using position.2⟩
    have hgrid : gridIndex prismIndex = pointIndex := by
      simpa [gridIndex, prismIndex] using hposition
    refine ⟨prismIndex, hpoint, ?_⟩
    change point ∈ pureWZ2RotatedXZGridPrism frameSlope 0
      scaleData.slabLeft scaleData.slabRight (gridIndex prismIndex)
    rw [hgrid]
    exact hpointPrism
  have hsupport : ∀ tube,
      ((Finset.univ : Finset (Fin prismCount)).filter fun prism =>
        volume (piece tube prism) ≠ 0).card ≤ 3 := by
    intro tube
    let support := (Finset.univ : Finset (Fin prismCount)).filter fun prism =>
      volume (piece tube prism) ≠ 0
    have hcardImage : support.card = (support.image gridIndex).card := by
      rw [Finset.card_image_of_injective _ hgridInjective]
    rw [hcardImage]
    let gridSupport := (support.image gridIndex).filter fun index =>
      (wz1PaperTubeCarrier (cfg.family.tube tube) ∩
        pureWZ2RotatedXZGridPrism frameSlope 0 scaleData.slabLeft
          scaleData.slabRight index).Nonempty
    have hgridSupportEq : gridSupport = support.image gridIndex := by
      apply Finset.filter_true_of_mem
      intro index hindex
      rcases Finset.mem_image.mp hindex with ⟨prismIndex, hprismSupport, rfl⟩
      have hvolume := (Finset.mem_filter.mp hprismSupport).2
      have hnonempty : (piece tube prismIndex).Nonempty := by
        by_contra hempty
        rw [Set.not_nonempty_iff_eq_empty.mp hempty] at hvolume
        simp at hvolume
      rcases hnonempty with ⟨point, hpointF2, hpointPrism⟩
      exact ⟨point, common.F2.subset_body tube hpointF2, hpointPrism⟩
    rw [← hgridSupportEq]
    exact pureWZ2_rotated_paper_tube_three_prisms cfg.extremal.delta_pos
      scaleData.slab_ordered frameSlope (cfg.line_class tube).vertical
      (by rw [scaleData.slab_width]; exact hsmall) (support.image gridIndex)
  have hsegmentLength : 2 * (scaleData.slabRight - scaleData.slabLeft +
      12 * delta) ≤ Real.sqrt rho := by
    rw [hsqrtRho, hslabWidth]
    linarith
  choose segmentStart hsegment using fun tube =>
    pureWZ2_paper_tube_slab_in_segment cfg.extremal.delta_pos
      scaleData.slab_ordered hrhoPos hsegmentLength (cfg.line_class tube).vertical
  exact ⟨{
    prismCount := prismCount
    prismCount_pos := hprismCount
    gridIndex := gridIndex
    gridIndex_injective := hgridInjective
    sourceLabel := sourceLabelSubtype
    sourcePoint := sourceSubtype
    source_mem_label := hsourcePoint
    source_near_common_y := by simpa only [rotation] using hsourceY
    frameGap := frameGap
    frameGap_nonneg := hframeGap
    frameGap_small := hframeGapSmall
    frameGap_le_rho := hframeGapRho
    selected_label_frame_close := hlabelClose
    prism := prism
    prism_eq := fun _ => rfl
    source_near_prism := by
      intro j point hpoint
      simpa only [Subtype.coe_eta, rotation, width] using
        hsourceNear j point hpoint
    prismNormal := prismNormal
    prismNormal_eq := fun _ => rfl
    source_frame_projected_lower := hsourceLower
    prismNormal_unit := hprismNormalUnit
    prismNormal_rotated_y_zero := hprismNormalY
    prism_card_raw := by
      exact_mod_cast hprismCardNat
    piece := piece
    piece_eq := fun _ _ => rfl
    piece_measurable := hpieceMeasurable
    covers := hcovers
    support_card := hsupport
    segmentStart := segmentStart
    piece_sub_segment := by
      intro tube prismIndex point hpoint
      exact hsegment tube ⟨common.F2.subset_body tube hpoint.1,
        common.F2_in_slab tube hpoint.1⟩
  }⟩

/-- Compatibility wrapper for callers that still carry the historical
global pointwise certificate.  The geometric construction itself only uses
the displayed occupied-anchor lower bound. -/
theorem pureWZ2_faithful_raw_prism_cover
    {sigma grainLoss slabLoss delta rho : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale)
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (frameSlope : ℝ)
    (common : PureWZ2RotatedWeightedCommonYData
      cfg scale scaleData popular frameSlope)
    (compatibility : PureWZ2LocalGlobalCompatibility cfg)
    (hrhoPos : 0 < rho)
    (hsqrtRho : Real.sqrt rho = 8 * scale.1)
    (hsmall : 256 * delta ≤ scale.1)
    (hscaleSmall : scale.1 ≤ 1 / 32) :
    Nonempty (PureWZ2FaithfulRawPrismCover
      cfg scale scaleData popular frameSlope common.toPureWZ2RotatedWeightedCommonYCore rho) := by
  apply pureWZ2_faithful_raw_prism_cover_of_frame_lower cfg scale scaleData
    popular frameSlope common.toPureWZ2RotatedWeightedCommonYCore
      (2 * scale.1 ^ 2) (by positivity) common.selected_label_frame_close (by
        have hscalePos : 0 < scale.1 :=
          cfg.extremal.delta_pos.trans_le scale.2.1
        nlinarith [hscaleSmall]) (by
        have hsqrtSq := Real.sq_sqrt hrhoPos.le
        nlinarith [hsqrtSq])
  · intro label hlabel
    have hselected : label ∈
        pureWZ2WeightedLabelsMeetingRotatedGoodSlice popular frameSlope
          common.goodY common.y0 := by
      simpa [common.selectedLabels_eq] using hlabel
    rcases Finset.mem_filter.mp hselected with ⟨_hkept, hslice⟩
    rcases hslice with ⟨slicePoint, hslicePoint⟩
    rcases pureWZ2_mem_ySlice_iff.mp hslicePoint with
      ⟨companion, hcompanionGood, hcompanionEq⟩
    have hcompanionRegion : companion ∈
        pureWZ2WeightedCroppedLabelRegion popular label := hcompanionGood.1
    have hcompanionY :
        pureWZ2HorizontalRotation frameSlope companion 1 = common.y0 := by
      have hcoord := congr_arg (fun source : Point3 => source 1) hcompanionEq
      simpa [point3] using hcoord
    have hcompanionCfg : companion ∈ cfg.shading.union := by
      rw [pureWZ2WeightedCroppedLabelRegion_eq] at hcompanionRegion
      rcases Set.mem_iUnion₂.mp hcompanionRegion with
        ⟨sourceCell, hsourceCell, hpointCell⟩
      have hactive := (mem_pureWZ2GlobalGrainFiber
        cfg.globalGrains.slope delta popular.activeCells label sourceCell).mp
          hsourceCell |>.1
      have hslabActive : sourceCell ∈
          wz1PaperActiveCells scaleData.slabShading
            cfg.extremal.delta_pos := by
        simpa [popular.activeCells_eq] using hactive
      have hslabUnion : companion ∈ scaleData.slabShading.union := by
        rw [scaleData.slab_cubical.union_eq_activeCells
          cfg.extremal.delta_pos]
        exact Set.mem_iUnion₂.mpr
          ⟨sourceCell, hslabActive, hpointCell⟩
      rcases hslabUnion with ⟨index, hcarrier⟩
      exact ⟨index, scaleData.slab_subshading index hcarrier⟩
    let source : {point : Point3 // point ∈ cfg.shading.union} :=
      ⟨companion, hcompanionCfg⟩
    have hsourceFrame :
        |cfg.globalGrains.slope (source.1 2) - frameSlope| ≤ 1 / 25 := by
      have hclose := common.selected_source_frame_close hlabel hcompanionRegion
      have hraw : delta / 2 + 2 * scale.1 ^ 2 ≤ 1 / 25 := by
        have hdeltaHalf : delta / 2 ≤ scale.1 / 512 := by
          linarith [hsmall]
        have hscaleSq2 : 2 * scale.1 ^ 2 ≤ scale.1 / 16 := by
          have hscalePos : 0 < scale.1 :=
            cfg.extremal.delta_pos.trans_le scale.2.1
          nlinarith [hscaleSmall]
        linarith
      exact hclose.trans hraw
    exact ⟨source, hcompanionRegion, by
      rw [hcompanionY, sub_self, abs_zero]
      exact (cfg.extremal.delta_pos.trans_le scale.2.1).le,
      pureWZ2_frameProjectedNormal_norm_lower cfg compatibility source
        hsourceFrame⟩
  · exact hrhoPos
  · exact hsqrtRho
  · exact hsmall
  · exact hscaleSmall

end Kakeya.Assouad

end
