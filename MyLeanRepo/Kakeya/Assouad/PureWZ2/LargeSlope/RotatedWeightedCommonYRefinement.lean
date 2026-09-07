import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.WeightedCommonYRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.RotatedCoverSliceSelection

/-!
# Weighted common-y refinement in the paper's rotated coordinates

This is the active Refinement 2 for the large-slope contradiction.  One
frame slope `f(z0)` is fixed for the entire slab, the cover centers are
rotated into that frame, and Fubini selects one genuine common rotated-y
plane.  Labels met by that plane are then expanded back to complete cubical
fibers, producing the whole-cell shading `F2`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- Weighted label region after imposing the paper body crop. -/
def pureWZ2WeightedCroppedLabelRegion
    {sigma grainLoss slabLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale}
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (label : ℤ × ℤ) : Set Point3 :=
  pureWZ2WeightedLabelRegion popular label ∩
    Kakeya.Streamlined.axisBox 2 2 2

theorem measurableSet_pureWZ2WeightedCroppedLabelRegion
    {sigma grainLoss slabLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale}
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (label : ℤ × ℤ) :
    MeasurableSet (pureWZ2WeightedCroppedLabelRegion popular label) :=
  (measurableSet_pureWZ2WeightedLabelRegion popular label).inter
    (Kakeya.Streamlined.measurableSet_axisBox 2 2 2)

/-- Whole active cells already lie in the cropped paper body. -/
theorem pureWZ2WeightedCroppedLabelRegion_eq
    {sigma grainLoss slabLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale}
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (label : ℤ × ℤ) :
    pureWZ2WeightedCroppedLabelRegion popular label =
      pureWZ2WeightedLabelRegion popular label := by
  apply Set.inter_eq_left.mpr
  intro point hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
  have hactive := (mem_pureWZ2GlobalGrainFiber cfg.globalGrains.slope
    delta popular.activeCells label cell).mp hcell |>.1
  have hcellActive : cell ∈ wz1PaperActiveCells
      scaleData.slabShading cfg.extremal.delta_pos := by
    simpa [popular.activeCells_eq] using hactive
  have hcellSub := Set.inter_eq_right.mp
    (scaleData.slab_cubical.inter_activeCell_eq
      cfg.extremal.delta_pos hcellActive) hpointCell
  rcases hcellSub with ⟨index, hcarrier⟩
  exact (scaleData.slabShading.subset_body index hcarrier).2

/-- Half-volume retention after deleting a bad set for an arbitrary coordinate. -/
theorem volume_inter_coordinate_good_half_on
    (coordinate : Point3 → ℝ) (ambient : Set ℝ)
    (E : Set Point3)
    (hEWindow : ∀ point ∈ E, coordinate point ∈ ambient)
    (hEFinite : volume E ≠ ⊤)
    {good : Set ℝ}
    (hbad : volume (E ∩
        {point : Point3 | coordinate point ∈ ambient \ good}) ≤
      (1 / 2 : ENNReal) * volume E) :
    (1 / 2 : ENNReal) * volume E ≤
      volume (E ∩ {point : Point3 | coordinate point ∈ good}) := by
  let goodPart := E ∩ {point : Point3 | coordinate point ∈ good}
  let badPart := E ∩ {point : Point3 | coordinate point ∈ ambient \ good}
  have hcover : E ⊆ goodPart ∪ badPart := by
    intro point hpoint
    by_cases hgood : coordinate point ∈ good
    · exact Or.inl ⟨hpoint, hgood⟩
    · exact Or.inr ⟨hpoint, hEWindow point hpoint, hgood⟩
  have hmeasure : volume E ≤ volume goodPart + volume badPart :=
    (measure_mono hcover).trans (measure_union_le _ _)
  have hhalfTop : (1 / 2 : ENNReal) * volume E ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hEFinite
  have hhalfAdd :
      (1 / 2 : ENNReal) * volume E + (1 / 2 : ENNReal) * volume E =
        volume E := by
    rw [← add_mul]
    have hhalf : (1 / 2 : ENNReal) + (1 / 2 : ENNReal) = 1 := by
      rw [← two_mul, div_eq_mul_inv, one_mul]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    rw [hhalf, one_mul]
  have hadd :
      (1 / 2 : ENNReal) * volume E + (1 / 2 : ENNReal) * volume E ≤
        (1 / 2 : ENNReal) * volume E + volume goodPart := by
    calc
      _ = volume E := hhalfAdd
      _ ≤ volume goodPart + volume badPart := hmeasure
      _ ≤ volume goodPart + (1 / 2 : ENNReal) * volume E := by gcongr
      _ = (1 / 2 : ENNReal) * volume E + volume goodPart := by rw [add_comm]
  exact (ENNReal.add_le_add_iff_left hhalfTop).mp hadd

/-- Labels whose good part meets the common slice in the fixed rotated frame. -/
def pureWZ2WeightedLabelsMeetingRotatedGoodSlice
    {sigma grainLoss slabLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale}
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (frameSlope : ℝ) (goodY : Set ℝ) (y : ℝ) : Finset (ℤ × ℤ) :=
  popular.keptLabels.filter fun label =>
    (pureWZ2RotatedYSlice frameSlope
      (pureWZ2WeightedCroppedLabelRegion popular label ∩
        pureWZ2RotatedYWindow frameSlope goodY) y).Nonempty

/-- The geometric and mass output of the rotated weighted common-y
refinement.  The construction only needs a uniform `1/100` bound for the
chosen frame; the stronger quadratic bound used in the Lemma-31
contradiction is recorded separately below. -/
structure PureWZ2RotatedWeightedCommonYCore
    {sigma grainLoss slabLoss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale)
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (frameSlope : ℝ) where
  badYLoss : ℝ
  badYLoss_pos : 0 < badYLoss
  multiplicityCap : ENNReal
  multiplicityCap_ne_zero : multiplicityCap ≠ 0
  multiplicityCap_ne_top : multiplicityCap ≠ ⊤
  rotatedCoverCenters : Finset Point3
  cover_card : (rotatedCoverCenters.card : ENNReal) ≤
    Kakeya.realRpowENN delta (-slabLoss) *
      Kakeya.realRpowENN scale.1 (-2 + sigma)
  rotated_cover : ∀ point ∈
      pureWZ2HorizontalRotation frameSlope '' scaleData.slabShading.union,
    ∃ center ∈ rotatedCoverCenters,
      point ∈ Metric.closedBall center scale.1
  goodY : Set ℝ
  goodY_measurable : MeasurableSet goodY
  goodY_subset : goodY ⊆ Set.Icc (-2 : ℝ) 2
  goodY_ne_zero : volume goodY ≠ 0
  badY_volume : volume (Set.Icc (-2 : ℝ) 2 \ goodY) ≤
    2 * Kakeya.realRpowENN delta (4 * badYLoss)
  cover_count : ∀ y ∈ goodY,
    ((rotatedCoverCenters.filter fun center =>
      |center 1 - y| ≤ scale.1).card : ENNReal) ≤
      Kakeya.realRpowENN delta (-(4 * badYLoss)) *
        ENNReal.ofReal scale.1 * (rotatedCoverCenters.card : ENNReal)
  every_label_good_half : ∀ label ∈ popular.keptLabels,
    (1 / 2 : ENNReal) *
        volume (pureWZ2WeightedCroppedLabelRegion popular label) ≤
      volume (pureWZ2WeightedCroppedLabelRegion popular label ∩
        pureWZ2RotatedYWindow frameSlope goodY)
  goodRegion : Set Point3
  goodRegion_eq : goodRegion =
    (⋃ label ∈ popular.keptLabels,
      pureWZ2WeightedCroppedLabelRegion popular label) ∩
        pureWZ2RotatedYWindow frameSlope goodY
  goodRegion_measurable : MeasurableSet goodRegion
  goodRegion_ne_zero : volume goodRegion ≠ 0
  goodRegion_volume_lower :
    scaleData.slabShading.mass ≤
      4 * multiplicityCap * volume goodRegion
  y0 : ℝ
  y0_mem : y0 ∈ goodY
  common_slice_average : volume goodRegion / volume goodY ≤
    volume (pureWZ2RotatedYSlice frameSlope goodRegion y0)
  selectedLabels : Finset (ℤ × ℤ)
  selectedLabels_eq : selectedLabels =
    pureWZ2WeightedLabelsMeetingRotatedGoodSlice popular frameSlope goodY y0
  selectedLabels_subset : selectedLabels ⊆ popular.keptLabels
  selectedLabels_nonempty : selectedLabels.Nonempty
  selected_label_count_lower : volume goodRegion / volume goodY ≤
    (selectedLabels.card : ENNReal) * ENNReal.ofReal (128 * delta ^ 2)
  selectedCells : Finset (ℤ × ℤ × ℤ)
  selectedCells_eq : selectedCells = selectedLabels.biUnion
    (pureWZ2GlobalGrainFiber cfg.globalGrains.slope delta popular.activeCells)
  selectedCells_subset : selectedCells ⊆ popular.retainedCells
  F2 : WZ1PaperTubeShading cfg.family
  F2_eq : F2 = wz2RefinedShading scaleData.slabShading selectedCells
  F2_cubical : WZ1PaperIsCubicalShading F2
  F2_in_slab : ∀ index, F2.carrier index ⊆
    horizontalSlab scaleData.slabLeft scaleData.slabRight
  F2_union_eq : F2.union = wz2RetainedCellsUnion delta selectedCells
  selected_labels_mass_lower :
    (selectedLabels.card : ENNReal) * popular.labelThreshold ≤ F2.mass
  common_slice_mass_lower :
    (volume goodRegion / volume goodY) * popular.labelThreshold ≤
      ENNReal.ofReal (128 * delta ^ 2) * F2.mass
  F2_mass_retention :
    (1 / 4 : ENNReal) * Kakeya.realRpowENN delta (4 * badYLoss) *
        scaleData.slabShading.mass ≤ F2.mass
  common_slice_subset_F2 :
    pureWZ2RotatedYSlice frameSlope goodRegion y0 ⊆
      pureWZ2RotatedYSlice frameSlope F2.union y0

/-- Strong version used by the Lemma-31 contradiction.  Keeping the
quadratic frame estimate here prevents the positive Proposition-6.5 route
from manufacturing a witness that was only available under the contradictory
small-derivative assumption. -/
structure PureWZ2RotatedWeightedCommonYData
    {sigma grainLoss slabLoss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale)
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (frameSlope : ℝ)
    extends PureWZ2RotatedWeightedCommonYCore
      cfg scale scaleData popular frameSlope where
  selected_label_frame_close : ∀ label (hlabel : label ∈ selectedLabels),
    |cfg.globalGrains.slope
        ((pureWZ2PaperCellCenter delta
          (popular.label_anchor label
            (selectedLabels_subset hlabel))) 2) - frameSlope| ≤
      2 * scale.1 ^ 2
  frame_small : 2 * scale.1 ^ 2 ≤ 1 / 100

/-- Every point of the whole-cell refinement has a genuine companion on the
selected common rotated-y slice, in the same selected global-grain label. -/
theorem PureWZ2RotatedWeightedCommonYCore.exists_common_slice_companion
    {sigma grainLoss slabLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale}
    {popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData}
    {frameSlope : ℝ}
    (data : PureWZ2RotatedWeightedCommonYCore
      cfg scale scaleData popular frameSlope)
    {point : Point3} (hpoint : point ∈ data.F2.union) :
    ∃ label, label ∈ data.selectedLabels ∧
      point ∈ pureWZ2WeightedCroppedLabelRegion popular label ∧
      ∃ companion,
        companion ∈ pureWZ2WeightedCroppedLabelRegion popular label ∧
        pureWZ2HorizontalRotation frameSlope companion 1 = data.y0 := by
  rw [data.F2_union_eq] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
  rw [data.selectedCells_eq] at hcell
  rcases Finset.mem_biUnion.mp hcell with ⟨label, hlabel, hfiber⟩
  have hpointRegion :
      point ∈ pureWZ2WeightedCroppedLabelRegion popular label := by
    rw [pureWZ2WeightedCroppedLabelRegion_eq]
    exact Set.mem_iUnion₂.mpr ⟨cell, hfiber, hpointCell⟩
  have hselected : label ∈
      pureWZ2WeightedLabelsMeetingRotatedGoodSlice popular frameSlope
        data.goodY data.y0 := by
    simpa [data.selectedLabels_eq] using hlabel
  rcases Finset.mem_filter.mp hselected with ⟨_hkept, hslice⟩
  rcases hslice with ⟨slicePoint, hslicePoint⟩
  rcases pureWZ2_mem_ySlice_iff.mp hslicePoint with
    ⟨companion, hcompanion, hcompanionEq⟩
  refine ⟨label, hlabel, hpointRegion, companion, hcompanion.1, ?_⟩
  have hcoord := congr_arg (fun source : Point3 => source 1) hcompanionEq
  simpa [point3] using hcoord

/-- The common-slice companion may be chosen at the same source height as
the original point.  A global-grain label records the fine height-cell index,
so replacing the companion's third coordinate by the original point's third
coordinate stays inside the same selected label region.  This is the form
that survives every later restriction by a horizontal interval, in particular
the mass-popular derivative subband `J₀`. -/
theorem PureWZ2RotatedWeightedCommonYCore.exists_common_slice_companion_same_height
    {sigma grainLoss slabLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale}
    {popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData}
    {frameSlope : ℝ}
    (data : PureWZ2RotatedWeightedCommonYCore
      cfg scale scaleData popular frameSlope)
    {point : Point3} (hpoint : point ∈ data.F2.union) :
    ∃ label, label ∈ data.selectedLabels ∧
      point ∈ pureWZ2WeightedCroppedLabelRegion popular label ∧
      ∃ companion,
        companion ∈ pureWZ2WeightedCroppedLabelRegion popular label ∧
        pureWZ2HorizontalRotation frameSlope companion 1 = data.y0 ∧
        companion 2 = point 2 := by
  rcases data.exists_common_slice_companion hpoint with
    ⟨label, hlabel, hpointRegion, sourceCompanion,
      hsourceCompanionRegion, hsourceCompanionY⟩
  have hpointRegion' := hpointRegion
  have hsourceCompanionRegion' := hsourceCompanionRegion
  rw [pureWZ2WeightedCroppedLabelRegion_eq] at hpointRegion'
  rw [pureWZ2WeightedCroppedLabelRegion_eq] at hsourceCompanionRegion'
  rcases Set.mem_iUnion₂.mp hpointRegion' with
    ⟨pointCell, hpointCellFiber, hpointCell⟩
  rcases Set.mem_iUnion₂.mp hsourceCompanionRegion' with
    ⟨companionCell, hcompanionCellFiber, hsourceCompanionCell⟩
  have hpointLabel := (mem_pureWZ2GlobalGrainFiber
    cfg.globalGrains.slope delta popular.activeCells label pointCell).mp
      hpointCellFiber |>.2
  have hcompanionLabel := (mem_pureWZ2GlobalGrainFiber
    cfg.globalGrains.slope delta popular.activeCells label companionCell).mp
      hcompanionCellFiber |>.2
  have hheightIndex : pointCell.2.2 = companionCell.2.2 := by
    exact congrArg Prod.fst (hpointLabel.trans hcompanionLabel.symm)
  let companion : Point3 :=
    point3 (sourceCompanion 0) (sourceCompanion 1) (point 2)
  have hcompanionCell : companion ∈ wz1PaperGridCube delta companionCell := by
    rw [wz1PaperGridCube_eq_Ico cfg.extremal.delta_pos] at hpointCell
    rw [wz1PaperGridCube_eq_Ico cfg.extremal.delta_pos] at hsourceCompanionCell
    rw [wz1PaperGridCube_eq_Ico cfg.extremal.delta_pos]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [companion, point3] using hsourceCompanionCell.1
    · simpa [companion, point3] using hsourceCompanionCell.2.1
    · simpa [companion, point3] using hsourceCompanionCell.2.2.1
    · simpa [companion, point3] using hsourceCompanionCell.2.2.2.1
    · simpa [companion, point3, ← hheightIndex] using
        hpointCell.2.2.2.2.1
    · simpa [companion, point3, ← hheightIndex] using
        hpointCell.2.2.2.2.2
  have hcompanionRegion :
      companion ∈ pureWZ2WeightedCroppedLabelRegion popular label := by
    rw [pureWZ2WeightedCroppedLabelRegion_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨companionCell, hcompanionCellFiber, hcompanionCell⟩
  refine ⟨label, hlabel, hpointRegion, companion, hcompanionRegion, ?_, ?_⟩
  · have hrotation :
        pureWZ2HorizontalRotation frameSlope companion 1 =
          pureWZ2HorizontalRotation frameSlope sourceCompanion 1 := by
      rw [pureWZ2HorizontalRotation_coord_one,
        pureWZ2HorizontalRotation_coord_one]
      simp [companion, point3, div_eq_mul_inv]
    exact hrotation.trans hsourceCompanionY
  · simp [companion, point3]

/-- The same-height companion remains inside any later restriction depending
only on the source height.  This is the direct bridge from the whole-label
common-y refinement to the mass-popular derivative subband `J₀`. -/
theorem PureWZ2RotatedWeightedCommonYCore.exists_common_slice_companion_in_height_set
    {sigma grainLoss slabLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale}
    {popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData}
    {frameSlope : ℝ}
    (data : PureWZ2RotatedWeightedCommonYCore
      cfg scale scaleData popular frameSlope)
    (heightSet : Set ℝ)
    {point : Point3} (hpointF2 : point ∈ data.F2.union)
    (hpointHeight : point 2 ∈ heightSet) :
    ∃ label, label ∈ data.selectedLabels ∧
      point ∈ pureWZ2WeightedCroppedLabelRegion popular label ∧
      ∃ companion,
        companion ∈ pureWZ2WeightedCroppedLabelRegion popular label ∧
        pureWZ2HorizontalRotation frameSlope companion 1 = data.y0 ∧
        companion 2 ∈ heightSet := by
  rcases data.exists_common_slice_companion_same_height hpointF2 with
    ⟨label, hlabel, hpointRegion, companion, hcompanionRegion,
      hcompanionY, hcompanionHeight⟩
  exact ⟨label, hlabel, hpointRegion, companion, hcompanionRegion,
    hcompanionY, hcompanionHeight.symm ▸ hpointHeight⟩

/-- The same-height companion statement expressed directly on an arbitrary
height restriction of `F2`.  Both the original point and the companion lie in
the restricted set, so downstream retubing does not have to leave `J₀`. -/
theorem PureWZ2RotatedWeightedCommonYCore.exists_common_slice_companion_in_height_restriction
    {sigma grainLoss slabLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale}
    {popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData}
    {frameSlope : ℝ}
    (data : PureWZ2RotatedWeightedCommonYCore
      cfg scale scaleData popular frameSlope)
    (heightSet : Set ℝ)
    {point : Point3}
    (hpointF2 : point ∈ data.F2.union)
    (hpointHeight : point 2 ∈ heightSet) :
    ∃ companion,
      companion ∈ data.F2.union ∧
      companion 2 ∈ heightSet ∧
      pureWZ2HorizontalRotation frameSlope companion 1 = data.y0 := by
  rcases data.exists_common_slice_companion_in_height_set heightSet
      hpointF2 hpointHeight with
    ⟨label, hlabel, _hpointRegion, companion, hcompanionRegion,
      hcompanionY, hcompanionHeight⟩
  refine ⟨companion, ?_, hcompanionHeight, hcompanionY⟩
  rw [data.F2_union_eq, data.selectedCells_eq]
  rw [pureWZ2WeightedCroppedLabelRegion_eq] at hcompanionRegion
  rcases Set.mem_iUnion₂.mp hcompanionRegion with
    ⟨cell, hcellFiber, hcompanionCell⟩
  exact Set.mem_iUnion₂.mpr
    ⟨cell, Finset.mem_biUnion.mpr ⟨label, hlabel, hcellFiber⟩,
      hcompanionCell⟩

/-- Construct the common-y core in one fixed rotated horizontal frame.  The
frame error is kept as a caller parameter; only its comparison with `1/100`
enters the slice-volume estimate. -/
theorem pureWZ2_rotatedWeightedCommonYRefinementCore
    {sigma grainLoss slabLoss badYLoss delta frameGap : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale)
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (hbadYLoss : 0 < badYLoss) (hdeltaLtOne : delta < 1)
    (frameSlope : ℝ)
    (hlabelClose : ∀ label (hlabel : label ∈ popular.keptLabels),
      |cfg.globalGrains.slope
          ((pureWZ2PaperCellCenter delta
            (popular.label_anchor label hlabel)) 2) - frameSlope| ≤
        frameGap)
    (hframeSmall : frameGap ≤ 1 / 100)
    (multiplicityCap : ENNReal)
    (hcapZero : multiplicityCap ≠ 0)
    (hcapTop : multiplicityCap ≠ ⊤)
    (hpointCap : ∀ point,
      (scaleData.slabShading.pointMultiplicity point : ENNReal) ≤
        multiplicityCap)
    (hbadBudget :
      ENNReal.ofReal (128 * delta ^ 2) *
          (2 * Kakeya.realRpowENN delta (4 * badYLoss)) ≤
        (1 / 2 : ENNReal) *
          (popular.labelThreshold / multiplicityCap)) :
    ∃ common : PureWZ2RotatedWeightedCommonYCore
        cfg scale scaleData popular frameSlope,
      common.badYLoss = badYLoss := by
  rcases scaleData.slab_cover with ⟨coverCenters, hcoverCard, hcover⟩
  let rotation := pureWZ2HorizontalRotation frameSlope
  let embedding : Point3 ↪ Point3 := ⟨rotation, rotation.injective⟩
  let rotatedCoverCenters := coverCenters.map embedding
  have hrotatedCard : rotatedCoverCenters.card = coverCenters.card := by
    exact Finset.card_map embedding
  have hrotatedCover : CanCoverByBalls (rotation '' scaleData.slabShading.union)
      scale.1 (Kakeya.realRpowENN delta (-slabLoss) *
        Kakeya.realRpowENN scale.1 (-2 + sigma)) :=
    pureWZ2_rotate_ball_cover frameSlope scaleData.slab_cover
  let K := Kakeya.realRpowENN delta (-(4 * badYLoss))
  have hKZero : K ≠ 0 := by
    simp [K, Kakeya.realRpowENN, Real.rpow_pos_of_pos cfg.extremal.delta_pos]
  have hKTop : K ≠ ⊤ := by simp [K, Kakeya.realRpowENN]
  rcases exists_parametric_cover_slice_good_set_two
      (cfg.extremal.delta_pos.trans_le scale.2.1) hKZero hKTop
      rotatedCoverCenters with
    ⟨goodY, hgoodY, hgoodYSubset, hbadRaw, hcoverCount⟩
  have hKInv : 2 / K = 2 * Kakeya.realRpowENN delta (4 * badYLoss) := by
    have hmul : K * Kakeya.realRpowENN delta (4 * badYLoss) = 1 := by
      dsimp only [K]
      rw [← realRpowENN_add cfg.extremal.delta_pos]
      have hexp : -(4 * badYLoss) + 4 * badYLoss = 0 := by ring
      rw [hexp]
      simp [Kakeya.realRpowENN]
    have hinv : K⁻¹ = Kakeya.realRpowENN delta (4 * badYLoss) :=
      (ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hmul)).symm
    rw [div_eq_mul_inv, hinv]
  have hbadY : volume (Set.Icc (-2 : ℝ) 2 \ goodY) ≤
      2 * Kakeya.realRpowENN delta (4 * badYLoss) := by
    rwa [hKInv] at hbadRaw
  have hpower : Kakeya.realRpowENN delta (4 * badYLoss) < 1 := by
    apply ENNReal.ofReal_lt_one.mpr
    exact Real.rpow_lt_one cfg.extremal.delta_pos.le hdeltaLtOne (by positivity)
  have hgoodYZero : volume goodY ≠ 0 := by
    intro hzero
    have hgoodTop : volume goodY ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp [Real.volume_Icc] :
        volume (Set.Icc (-2 : ℝ) 2) ≠ ⊤) (measure_mono hgoodYSubset)
    have hbadSmall : volume (Set.Icc (-2 : ℝ) 2 \ goodY) < 4 := by
      calc
        volume (Set.Icc (-2 : ℝ) 2 \ goodY)
          ≤ 2 * Kakeya.realRpowENN delta (4 * badYLoss) := hbadY
        _ < 2 := by
          simpa [mul_comm] using ENNReal.mul_lt_mul_left
            (show (2 : ENNReal) ≠ 0 by norm_num)
            (show (2 : ENNReal) ≠ ⊤ by norm_num) hpower
        _ < 4 := by norm_num
    have hinterval : volume (Set.Icc (-2 : ℝ) 2) = 4 := by
      rw [Real.volume_Icc]
      norm_num
    have hsdiff : volume (Set.Icc (-2 : ℝ) 2 \ goodY) = 4 := by
      rw [measure_sdiff hgoodYSubset hgoodY.nullMeasurableSet hgoodTop,
        hzero, hinterval]
      simp
    rw [hsdiff] at hbadSmall
    exact (lt_irrefl 4 hbadSmall)
  have heveryHalf : ∀ label ∈ popular.keptLabels,
      (1 / 2 : ENNReal) *
          volume (pureWZ2WeightedCroppedLabelRegion popular label) ≤
        volume (pureWZ2WeightedCroppedLabelRegion popular label ∩
          pureWZ2RotatedYWindow frameSlope goodY) := by
    intro label hlabel
    let region := pureWZ2WeightedCroppedLabelRegion popular label
    let anchor := pureWZ2PaperCellCenter delta
      (popular.label_anchor label hlabel)
    have hanchorActive := (mem_pureWZ2GlobalGrainFiber
      cfg.globalGrains.slope delta popular.activeCells label
      (popular.label_anchor label hlabel)).mp
        (popular.label_anchor_mem label hlabel) |>.1
    have hanchorCell : popular.label_anchor label hlabel ∈
        wz1PaperActiveCells scaleData.slabShading cfg.extremal.delta_pos := by
      simpa [popular.activeCells_eq] using hanchorActive
    have hanchorUnion := pureWZ2_activeCellCenter_mem_union
      cfg.extremal.delta_pos scaleData.slab_cubical hanchorCell
    rcases hanchorUnion with ⟨index, hanchorCarrier⟩
    have hanchorBox : anchor ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
      (scaleData.slabShading.subset_body index hanchorCarrier).2
    have hregionFinite : volume region ≠ ⊤ := by
      exact ne_top_of_le_ne_top
        (show volume (Kakeya.Streamlined.axisBox 2 2 2) ≠ ⊤ by
          rw [Kakeya.Streamlined.volume_axisBox 2 2 2]
          · exact ENNReal.ofReal_ne_top
          all_goals norm_num) (measure_mono Set.inter_subset_right)
    have hregionWindow : ∀ point ∈ region,
        rotation point 1 ∈ Set.Icc (-2 : ℝ) 2 := by
      intro point hpoint
      exact pureWZ2HorizontalRotation_coord_one_mem_two frameSlope hpoint.2
    have hbadRegion : volume (region ∩
        pureWZ2RotatedYWindow frameSlope
          (Set.Icc (-2 : ℝ) 2 \ goodY)) ≤
        (1 / 2 : ENNReal) * volume region := by
      calc
        _ ≤ volume ((pureWZ2GlobalGrainWithConstant 4
              cfg.globalGrains.slope delta anchor ∩
              Kakeya.Streamlined.axisBox 2 2 2) ∩
            pureWZ2RotatedYWindow frameSlope
              (Set.Icc (-2 : ℝ) 2 \ goodY)) := by
          apply measure_mono
          intro point hpoint
          exact ⟨⟨popular.label_grain_containment label hlabel hpoint.1.1,
            hpoint.1.2⟩, hpoint.2⟩
        _ ≤ ENNReal.ofReal (128 * delta ^ 2) *
            volume (Set.Icc (-2 : ℝ) 2 \ goodY) :=
          pureWZ2_globalGrain_fixed_rotated_window_volume_upper
            cfg.globalGrains.slope cfg.extremal.delta_pos.le anchor hanchorBox
            (cfg.globalGrains.slope_normalized _ <| by
              simpa [Kakeya.Streamlined.axisBox, abs_le] using
                hanchorBox.2.2).1
            ((hlabelClose label hlabel).trans hframeSmall)
            (measurableSet_Icc.diff hgoodY)
        _ ≤ ENNReal.ofReal (128 * delta ^ 2) *
            (2 * Kakeya.realRpowENN delta (4 * badYLoss)) := by gcongr
        _ ≤ (1 / 2 : ENNReal) *
            (popular.labelThreshold / multiplicityCap) := hbadBudget
        _ ≤ (1 / 2 : ENNReal) * volume region := by
          gcongr
          have hlower := popular.label_volume_lower_of_cap
            hcapZero hcapTop hpointCap label hlabel
          change popular.labelThreshold / multiplicityCap ≤
            volume (pureWZ2WeightedLabelRegion popular label) at hlower
          change popular.labelThreshold / multiplicityCap ≤ volume region
          rw [show region = pureWZ2WeightedLabelRegion popular label by
            exact pureWZ2WeightedCroppedLabelRegion_eq popular label]
          exact hlower
    exact volume_inter_coordinate_good_half_on
      (fun point => rotation point 1) (Set.Icc (-2 : ℝ) 2)
      region hregionWindow hregionFinite
      (by simpa [pureWZ2RotatedYWindow, rotation] using hbadRegion)
  let goodRegion := (⋃ label ∈ popular.keptLabels,
      pureWZ2WeightedCroppedLabelRegion popular label) ∩
    pureWZ2RotatedYWindow frameSlope goodY
  have hgoodRegionMeasurable : MeasurableSet goodRegion := by
    apply (Finset.measurableSet_biUnion popular.keptLabels fun label _ =>
      measurableSet_pureWZ2WeightedCroppedLabelRegion popular label).inter
    exact measurableSet_pureWZ2RotatedYWindow frameSlope hgoodY
  have hgoodRegionZero : volume goodRegion ≠ 0 := by
    rcases popular.keptLabels_nonempty with ⟨label, hlabel⟩
    have hregionPos : volume
        (pureWZ2WeightedCroppedLabelRegion popular label) ≠ 0 := by
      rw [pureWZ2WeightedCroppedLabelRegion_eq popular label]
      change volume (⋃ cell ∈ pureWZ2GlobalGrainFiber
          cfg.globalGrains.slope delta popular.activeCells label,
        wz1PaperGridCube delta cell) ≠ 0
      rw [popular.label_volume label hlabel]
      have hfiber : (pureWZ2GlobalGrainFiber cfg.globalGrains.slope delta
          popular.activeCells label).Nonempty :=
        ⟨popular.label_anchor label hlabel,
          popular.label_anchor_mem label hlabel⟩
      exact mul_ne_zero (by exact_mod_cast hfiber.card_pos.ne')
        ((ENNReal.ofReal_pos.mpr (pow_pos cfg.extremal.delta_pos 3)).ne')
    have hgoodPartPos : volume
        (pureWZ2WeightedCroppedLabelRegion popular label ∩
          pureWZ2RotatedYWindow frameSlope goodY) ≠ 0 := by
      intro hzero
      have hhalfZero := le_zero_iff.mp ((heveryHalf label hlabel).trans_eq hzero)
      exact (mul_ne_zero (by norm_num) hregionPos) hhalfZero
    intro hzero
    apply hgoodPartPos
    apply measure_mono_null _ hzero
    intro point hpoint
    exact ⟨Set.mem_iUnion₂.mpr ⟨label, hlabel, hpoint.1⟩, hpoint.2⟩
  have hgoodRegionFinite : volume goodRegion ≠ ⊤ :=
    ne_top_of_le_ne_top
      (show volume (Kakeya.Streamlined.axisBox 2 2 2) ≠ ⊤ by
        rw [Kakeya.Streamlined.volume_axisBox 2 2 2]
        · exact ENNReal.ofReal_ne_top
        all_goals norm_num)
      (measure_mono (fun point hpoint => by
        rcases Set.mem_iUnion₂.mp hpoint.1 with ⟨label, _, hregion⟩
        exact hregion.2))
  have hregionDisjoint : Set.PairwiseDisjoint
      (popular.keptLabels : Set (ℤ × ℤ))
      (pureWZ2WeightedCroppedLabelRegion popular) := by
    intro first hfirst second hsecond hne
    change Disjoint
      (pureWZ2WeightedCroppedLabelRegion popular first)
      (pureWZ2WeightedCroppedLabelRegion popular second)
    rw [Set.disjoint_left]
    intro point hpointFirst hpointSecond
    rw [pureWZ2WeightedCroppedLabelRegion_eq] at hpointFirst hpointSecond
    rcases Set.mem_iUnion₂.mp hpointFirst with
      ⟨firstCell, hfirstFiber, hfirstCell⟩
    rcases Set.mem_iUnion₂.mp hpointSecond with
      ⟨secondCell, hsecondFiber, hsecondCell⟩
    have hfirstIndex := (mem_wz1PaperGridCube delta firstCell point).mp
      hfirstCell
    have hsecondIndex := (mem_wz1PaperGridCube delta secondCell point).mp
      hsecondCell
    have hfirstLabel := (mem_pureWZ2GlobalGrainFiber
      cfg.globalGrains.slope delta popular.activeCells first firstCell).mp
        hfirstFiber |>.2
    have hsecondLabel := (mem_pureWZ2GlobalGrainFiber
      cfg.globalGrains.slope delta popular.activeCells second secondCell).mp
        hsecondFiber |>.2
    have hcellEq : firstCell = secondCell := hfirstIndex.symm.trans hsecondIndex
    exact hne (hfirstLabel.symm.trans (hcellEq ▸ hsecondLabel))
  have hregionMeasure :
      volume (⋃ label ∈ popular.keptLabels,
          pureWZ2WeightedCroppedLabelRegion popular label) =
        ∑ label ∈ popular.keptLabels,
          volume (pureWZ2WeightedCroppedLabelRegion popular label) := by
    exact MeasureTheory.measure_biUnion_finset hregionDisjoint
      (fun label _ =>
        measurableSet_pureWZ2WeightedCroppedLabelRegion popular label)
  have hgoodPartsDisjoint : Set.PairwiseDisjoint
      (popular.keptLabels : Set (ℤ × ℤ))
      (fun label => pureWZ2WeightedCroppedLabelRegion popular label ∩
        pureWZ2RotatedYWindow frameSlope goodY) := by
    intro first hfirst second hsecond hne
    change Disjoint
      (pureWZ2WeightedCroppedLabelRegion popular first ∩
        pureWZ2RotatedYWindow frameSlope goodY)
      (pureWZ2WeightedCroppedLabelRegion popular second ∩
        pureWZ2RotatedYWindow frameSlope goodY)
    exact (hregionDisjoint hfirst hsecond hne).mono
      Set.inter_subset_left Set.inter_subset_left
  have hgoodRegionUnion : goodRegion =
      ⋃ label ∈ popular.keptLabels,
        pureWZ2WeightedCroppedLabelRegion popular label ∩
          pureWZ2RotatedYWindow frameSlope goodY := by
    ext point
    simp only [goodRegion, Set.mem_inter_iff, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨label, hlabel, hregion⟩, hwindow⟩
      exact ⟨label, hlabel, hregion, hwindow⟩
    · rintro ⟨label, hlabel, hregion, hwindow⟩
      exact ⟨⟨label, hlabel, hregion⟩, hwindow⟩
  have hgoodMeasure : volume goodRegion =
      ∑ label ∈ popular.keptLabels,
        volume (pureWZ2WeightedCroppedLabelRegion popular label ∩
          pureWZ2RotatedYWindow frameSlope goodY) := by
    rw [hgoodRegionUnion]
    exact MeasureTheory.measure_biUnion_finset hgoodPartsDisjoint
      (fun label _ =>
        (measurableSet_pureWZ2WeightedCroppedLabelRegion popular label).inter
          (measurableSet_pureWZ2RotatedYWindow frameSlope hgoodY))
  have hhalfRegions :
      (1 / 2 : ENNReal) *
          (∑ label ∈ popular.keptLabels,
            volume (pureWZ2WeightedCroppedLabelRegion popular label)) ≤
        volume goodRegion := by
    rw [hgoodMeasure, Finset.mul_sum]
    exact Finset.sum_le_sum fun label hlabel => heveryHalf label hlabel
  have hregionsGood :
      (∑ label ∈ popular.keptLabels,
        volume (pureWZ2WeightedCroppedLabelRegion popular label)) ≤
          2 * volume goodRegion := by
    calc
      (∑ label ∈ popular.keptLabels,
          volume (pureWZ2WeightedCroppedLabelRegion popular label)) =
          2 * ((1 / 2 : ENNReal) *
            (∑ label ∈ popular.keptLabels,
              volume (pureWZ2WeightedCroppedLabelRegion popular label))) := by
        have htwo : (2 : ENNReal) * (1 / 2) = 1 := by
          rw [show (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ by norm_num]
          exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
        rw [← mul_assoc, htwo, one_mul]
      _ ≤ 2 * volume goodRegion := by gcongr
  have hF1Spatial : popular.F1.mass ≤ multiplicityCap *
      (∑ label ∈ popular.keptLabels,
        volume (pureWZ2WeightedCroppedLabelRegion popular label)) := by
    rw [popular.F1_mass_eq]
    calc
      (∑ label ∈ popular.keptLabels,
          pureWZ2GlobalLabelIncidenceMass scaleData.slabShading
            cfg.globalGrains.slope popular.activeCells label) ≤
        ∑ label ∈ popular.keptLabels, multiplicityCap *
          volume (pureWZ2WeightedCroppedLabelRegion popular label) := by
            apply Finset.sum_le_sum
            intro label hlabel
            have hupper := popular.label_incidence_mass_upper_of_cap
              hpointCap label hlabel
            have hupper' :
                pureWZ2GlobalLabelIncidenceMass scaleData.slabShading
                    cfg.globalGrains.slope popular.activeCells label ≤
                multiplicityCap *
                    volume (pureWZ2WeightedLabelRegion popular label) := by
              simpa only [pureWZ2WeightedLabelRegion] using hupper
            rw [pureWZ2WeightedCroppedLabelRegion_eq popular label]
            exact hupper'
      _ = multiplicityCap *
          (∑ label ∈ popular.keptLabels,
            volume (pureWZ2WeightedCroppedLabelRegion popular label)) := by
        rw [Finset.mul_sum]
  have hgoodRegionLower : scaleData.slabShading.mass ≤
      4 * multiplicityCap * volume goodRegion := by
    calc
      scaleData.slabShading.mass ≤ 2 * popular.F1.mass :=
        popular.F1_mass_retention
      _ ≤ 2 * (multiplicityCap *
          (∑ label ∈ popular.keptLabels,
            volume (pureWZ2WeightedCroppedLabelRegion popular label))) := by
        gcongr
      _ ≤ 2 * (multiplicityCap * (2 * volume goodRegion)) := by
        gcongr
      _ = 4 * multiplicityCap * volume goodRegion := by ring
  have hgoodSupport : ∀ point ∈ goodRegion, rotation point 1 ∈ goodY :=
    fun _ h => h.2
  rcases pureWZ2_exists_rotatedYSlice_average_on frameSlope
      hgoodRegionMeasurable hgoodRegionFinite hgoodY hgoodYZero hgoodSupport with
    ⟨y0, hy0, hy0Average⟩
  let selectedLabels := pureWZ2WeightedLabelsMeetingRotatedGoodSlice
    popular frameSlope goodY y0
  have hsliceZero : volume
      (pureWZ2RotatedYSlice frameSlope goodRegion y0) ≠ 0 := by
    have hquot : volume goodRegion / volume goodY ≠ 0 :=
      ENNReal.div_ne_zero.mpr ⟨hgoodRegionZero,
        ne_top_of_le_ne_top (by simp [Real.volume_Icc] :
          volume (Set.Icc (-2 : ℝ) 2) ≠ ⊤) (measure_mono hgoodYSubset)⟩
    intro hzero
    exact hquot (le_zero_iff.mp (hy0Average.trans_eq hzero))
  have hselectedNonempty : selectedLabels.Nonempty := by
    rcases nonempty_of_measure_ne_zero hsliceZero with ⟨point, hpoint⟩
    have hp3 := pureWZ2_mem_ySlice_iff.mp hpoint
    rcases hp3 with ⟨source, hsourceGood, hsourceEq⟩
    rcases Set.mem_iUnion₂.mp hsourceGood.1 with ⟨label, hlabel, hregion⟩
    refine ⟨label, Finset.mem_filter.mpr ⟨hlabel, ⟨point, ?_⟩⟩⟩
    apply pureWZ2_mem_ySlice_iff.mpr
    exact ⟨source, ⟨hregion, hsourceGood.2⟩, hsourceEq⟩
  have hselectedSubset : selectedLabels ⊆ popular.keptLabels :=
    Finset.filter_subset _ _
  have hsliceUnionSubset : pureWZ2RotatedYSlice frameSlope goodRegion y0 ⊆
      ⋃ label ∈ selectedLabels, pureWZ2RotatedYSlice frameSlope
        (pureWZ2WeightedCroppedLabelRegion popular label) y0 := by
    intro point hpoint
    have hp3 := pureWZ2_mem_ySlice_iff.mp hpoint
    rcases hp3 with ⟨source, hsourceGood, hsourceEq⟩
    rcases Set.mem_iUnion₂.mp hsourceGood.1 with ⟨label, hlabel, hregion⟩
    have hlabelSelected : label ∈ selectedLabels :=
      Finset.mem_filter.mpr ⟨hlabel, ⟨point,
        pureWZ2_mem_ySlice_iff.mpr
          ⟨source, ⟨hregion, hsourceGood.2⟩, hsourceEq⟩⟩⟩
    exact Set.mem_iUnion₂.mpr ⟨label, hlabelSelected,
      pureWZ2_mem_ySlice_iff.mpr ⟨source, hregion, hsourceEq⟩⟩
  have hsliceUpper : volume (pureWZ2RotatedYSlice frameSlope goodRegion y0) ≤
      (selectedLabels.card : ENNReal) * ENNReal.ofReal (128 * delta ^ 2) := by
    calc
      volume (pureWZ2RotatedYSlice frameSlope goodRegion y0)
        ≤ volume (⋃ label ∈ selectedLabels,
            pureWZ2RotatedYSlice frameSlope
              (pureWZ2WeightedCroppedLabelRegion popular label) y0) :=
          measure_mono hsliceUnionSubset
      _ ≤ ∑ label ∈ selectedLabels,
          volume (pureWZ2RotatedYSlice frameSlope
            (pureWZ2WeightedCroppedLabelRegion popular label) y0) :=
        MeasureTheory.measure_biUnion_finset_le _ _
      _ ≤ ∑ _label ∈ selectedLabels,
          ENNReal.ofReal (128 * delta ^ 2) := by
        apply Finset.sum_le_sum
        intro label hlabel
        have hkept := hselectedSubset hlabel
        let anchor := pureWZ2PaperCellCenter delta
          (popular.label_anchor label hkept)
        have hanchorActive := (mem_pureWZ2GlobalGrainFiber
          cfg.globalGrains.slope delta popular.activeCells label
          (popular.label_anchor label hkept)).mp
            (popular.label_anchor_mem label hkept) |>.1
        have hanchorCell : popular.label_anchor label hkept ∈
            wz1PaperActiveCells scaleData.slabShading cfg.extremal.delta_pos := by
          simpa [popular.activeCells_eq] using hanchorActive
        have hanchorUnion := pureWZ2_activeCellCenter_mem_union
          cfg.extremal.delta_pos scaleData.slab_cubical hanchorCell
        rcases hanchorUnion with ⟨index, hanchorCarrier⟩
        have hanchorBox : anchor ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
          (scaleData.slabShading.subset_body index hanchorCarrier).2
        calc
          volume (pureWZ2RotatedYSlice frameSlope
              (pureWZ2WeightedCroppedLabelRegion popular label) y0)
            ≤ volume (pureWZ2RotatedYSlice frameSlope
                ((pureWZ2GlobalGrainWithConstant 4 cfg.globalGrains.slope
                  delta anchor) ∩ Kakeya.Streamlined.axisBox 2 2 2) y0) := by
              apply measure_mono
              apply pureWZ2YSlice_mono
              apply Set.image_mono
              intro point hpoint
              exact ⟨popular.label_grain_containment label hkept hpoint.1,
                hpoint.2⟩
          _ ≤ ENNReal.ofReal (128 * delta ^ 2) :=
            pureWZ2_fixed_rotatedYSlice_globalGrain_volume_upper
              cfg.globalGrains.slope cfg.extremal.delta_pos.le anchor hanchorBox
              (cfg.globalGrains.slope_normalized _ <| by
                simpa [Kakeya.Streamlined.axisBox, abs_le] using
                  hanchorBox.2.2).1
              ((hlabelClose label hkept).trans hframeSmall) y0
      _ = (selectedLabels.card : ENNReal) *
          ENNReal.ofReal (128 * delta ^ 2) := by
        simp [Finset.sum_const]
  have hselectedCountLower : volume goodRegion / volume goodY ≤
      (selectedLabels.card : ENNReal) * ENNReal.ofReal (128 * delta ^ 2) :=
    hy0Average.trans hsliceUpper
  let selectedCells := selectedLabels.biUnion
    (pureWZ2GlobalGrainFiber cfg.globalGrains.slope delta popular.activeCells)
  have hselectedCellsSubset : selectedCells ⊆ popular.retainedCells := by
    intro cell hcell
    rcases Finset.mem_biUnion.mp hcell with ⟨label, hlabel, hfiber⟩
    rw [popular.retainedCells_eq]
    exact Finset.mem_biUnion.mpr ⟨label, hselectedSubset hlabel, hfiber⟩
  let F2 := wz2RefinedShading scaleData.slabShading selectedCells
  have hactiveSelected : ∀ cell ∈ selectedCells,
      cell ∈ wz1PaperActiveCells scaleData.slabShading
        cfg.extremal.delta_pos := by
    intro cell hcell
    have : cell ∈ popular.activeCells :=
      popular.retainedCells_subset (hselectedCellsSubset hcell)
    simpa [popular.activeCells_eq] using this
  have hF2Union : F2.union = wz2RetainedCellsUnion delta selectedCells :=
    wz2RefinedShading_union_eq scaleData.slab_cubical
      cfg.extremal.delta_pos hactiveSelected
  have hselectedLabelsMass :
      (selectedLabels.card : ENNReal) * popular.labelThreshold ≤ F2.mass := by
    have hmassEq : F2.mass = ∑ label ∈ selectedLabels,
        pureWZ2GlobalLabelIncidenceMass scaleData.slabShading
          cfg.globalGrains.slope popular.activeCells label := by
      rw [show F2 = wz2RefinedShading scaleData.slabShading selectedCells by rfl,
        wz2RefinedShading_mass_eq_sum_cells]
      change (∑ cell ∈ selectedCells,
          ∑ index : Fin cfg.family.card,
            volume (scaleData.slabShading.carrier index ∩
              wz1PaperGridCube delta cell)) = _
      rw [show selectedCells = selectedLabels.biUnion
        (pureWZ2GlobalGrainFiber cfg.globalGrains.slope delta
          popular.activeCells) by rfl]
      rw [Finset.sum_biUnion]
      · rfl
      · intro first hfirst second hsecond hne
        exact pureWZ2GlobalGrainFiber_disjoint
          cfg.globalGrains.slope delta popular.activeCells hne
    rw [hmassEq]
    calc
      (selectedLabels.card : ENNReal) * popular.labelThreshold
        = ∑ _label ∈ selectedLabels, popular.labelThreshold := by
          simp [Finset.sum_const]
      _ ≤ ∑ label ∈ selectedLabels,
          pureWZ2GlobalLabelIncidenceMass scaleData.slabShading
            cfg.globalGrains.slope popular.activeCells label := by
        apply Finset.sum_le_sum
        intro label hlabel
        exact popular.label_mass_lower label (hselectedSubset hlabel)
  have hcommonSliceMass :
      (volume goodRegion / volume goodY) * popular.labelThreshold ≤
        ENNReal.ofReal (128 * delta ^ 2) * F2.mass := by
    calc
      (volume goodRegion / volume goodY) * popular.labelThreshold ≤
          ((selectedLabels.card : ENNReal) *
            ENNReal.ofReal (128 * delta ^ 2)) *
              popular.labelThreshold := by gcongr
      _ = ENNReal.ofReal (128 * delta ^ 2) *
          ((selectedLabels.card : ENNReal) * popular.labelThreshold) := by
        ring
      _ ≤ ENNReal.ofReal (128 * delta ^ 2) * F2.mass := by gcongr
  let sliceArea := ENNReal.ofReal (128 * delta ^ 2)
  let lossFactor := Kakeya.realRpowENN delta (4 * badYLoss)
  have htwoCapZero : (2 * multiplicityCap : ENNReal) ≠ 0 :=
    mul_ne_zero (by norm_num) hcapZero
  have htwoCapTop : (2 * multiplicityCap : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hcapTop
  have hthreshold :
      4 * sliceArea * lossFactor * multiplicityCap ≤
        popular.labelThreshold := by
    have hmul := mul_le_mul_right' hbadBudget (2 * multiplicityCap)
    have hcancel :
        ((1 / 2 : ENNReal) *
            (popular.labelThreshold / multiplicityCap)) *
              (2 * multiplicityCap) = popular.labelThreshold := by
      rw [show (1 / 2 : ENNReal) *
          (popular.labelThreshold / multiplicityCap) *
            (2 * multiplicityCap) =
          popular.labelThreshold / multiplicityCap * multiplicityCap by
        have hhalfTwo : (1 / 2 : ENNReal) * 2 = 1 := by
          rw [show (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ by norm_num]
          exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
        calc
          (1 / 2 : ENNReal) *
              (popular.labelThreshold / multiplicityCap) *
                (2 * multiplicityCap) =
            ((1 / 2 : ENNReal) * 2) *
              (popular.labelThreshold / multiplicityCap * multiplicityCap) := by
                ring
          _ = popular.labelThreshold / multiplicityCap * multiplicityCap := by
            rw [hhalfTwo, one_mul]]
      exact ENNReal.div_mul_cancel hcapZero hcapTop
    rw [hcancel] at hmul
    have hleft :
        (sliceArea * (2 * lossFactor)) * (2 * multiplicityCap) =
          4 * sliceArea * lossFactor * multiplicityCap := by
      ring
    rwa [hleft] at hmul
  have hgoodYTop : volume goodY ≠ ⊤ :=
    ne_top_of_le_ne_top
      (by simp [Real.volume_Icc] : volume (Set.Icc (-2 : ℝ) 2) ≠ ⊤)
      (measure_mono hgoodYSubset)
  have hgoodYVolume : volume goodY ≤ 4 := by
    calc
      volume goodY ≤ volume (Set.Icc (-2 : ℝ) 2) :=
        measure_mono hgoodYSubset
      _ = 4 := by rw [Real.volume_Icc]; norm_num
  let quotient := volume goodRegion / volume goodY
  have hgoodRegionQuotient : volume goodRegion ≤ 4 * quotient := by
    have hcancel : quotient * volume goodY = volume goodRegion := by
      exact ENNReal.div_mul_cancel hgoodYZero hgoodYTop
    rw [← hcancel]
    simpa [mul_comm] using mul_le_mul_left' hgoodYVolume quotient
  have hslabQuotient : scaleData.slabShading.mass ≤
      16 * multiplicityCap * quotient := by
    calc
      scaleData.slabShading.mass ≤
          4 * multiplicityCap * volume goodRegion := hgoodRegionLower
      _ ≤ 4 * multiplicityCap * (4 * quotient) := by gcongr
      _ = 16 * multiplicityCap * quotient := by ring
  have hsliceAreaZero : sliceArea ≠ 0 := by
    apply (ENNReal.ofReal_pos.mpr (by
      have hdeltaSq : 0 < delta ^ 2 := sq_pos_of_pos cfg.extremal.delta_pos
      positivity)).ne'
  have hsliceAreaTop : sliceArea ≠ ⊤ := by
    dsimp only [sliceArea]
    exact ENNReal.ofReal_ne_top
  have hretention :
      (1 / 4 : ENNReal) * lossFactor * scaleData.slabShading.mass ≤
        F2.mass := by
    have hfirst :
        (1 / 4 : ENNReal) * lossFactor * scaleData.slabShading.mass ≤
          4 * lossFactor * multiplicityCap * quotient := by
      calc
        (1 / 4 : ENNReal) * lossFactor * scaleData.slabShading.mass ≤
            (1 / 4 : ENNReal) * lossFactor *
              (16 * multiplicityCap * quotient) := by gcongr
        _ = 4 * lossFactor * multiplicityCap * quotient := by
          have hquarterSixteen : (1 / 4 : ENNReal) * 16 = 4 := by
            rw [show (1 / 4 : ENNReal) = (4 : ENNReal)⁻¹ by norm_num]
            calc
              (4 : ENNReal)⁻¹ * 16 = (4 : ENNReal)⁻¹ * (4 * 4) := by norm_num
              _ = ((4 : ENNReal)⁻¹ * 4) * 4 := by rw [mul_assoc]
              _ = 4 := by
                rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
          rw [show (1 / 4 : ENNReal) * lossFactor *
              (16 * multiplicityCap * quotient) =
            ((1 / 4 : ENNReal) * 16) * lossFactor *
              multiplicityCap * quotient by ring, hquarterSixteen]
    have hwithArea : sliceArea *
        (4 * lossFactor * multiplicityCap * quotient) ≤
          sliceArea * F2.mass := by
      calc
        sliceArea * (4 * lossFactor * multiplicityCap * quotient) =
            quotient * (4 * sliceArea * lossFactor * multiplicityCap) := by
          ring
        _ ≤ quotient * popular.labelThreshold := by gcongr
        _ ≤ sliceArea * F2.mass := by
          simpa [quotient, sliceArea] using hcommonSliceMass
    have hsecond : 4 * lossFactor * multiplicityCap * quotient ≤
        F2.mass := by
      apply (ENNReal.mul_le_mul_iff_left hsliceAreaZero hsliceAreaTop).mp
      simpa [mul_comm] using hwithArea
    exact hfirst.trans hsecond
  have hcommonSubset : pureWZ2RotatedYSlice frameSlope goodRegion y0 ⊆
      pureWZ2RotatedYSlice frameSlope F2.union y0 := by
    intro point hpoint
    have hp3 := pureWZ2_mem_ySlice_iff.mp hpoint
    rcases hp3 with ⟨source, hsourceGood, hsourceEq⟩
    rcases Set.mem_iUnion₂.mp hsourceGood.1 with ⟨label, hlabel, hregion⟩
    rcases Set.mem_iUnion₂.mp hregion.1 with ⟨cell, hfiber, hcell⟩
    have hlabelSelected : label ∈ selectedLabels :=
      Finset.mem_filter.mpr ⟨hlabel, ⟨point,
        pureWZ2_mem_ySlice_iff.mpr
          ⟨source, ⟨hregion, hsourceGood.2⟩, hsourceEq⟩⟩⟩
    apply pureWZ2_mem_ySlice_iff.mpr
    refine ⟨source, ?_, hsourceEq⟩
    rw [hF2Union]
    exact Set.mem_iUnion₂.mpr ⟨cell, Finset.mem_biUnion.mpr
      ⟨label, hlabelSelected, hfiber⟩, hcell⟩
  exact ⟨{
    badYLoss := badYLoss
    badYLoss_pos := hbadYLoss
    multiplicityCap := multiplicityCap
    multiplicityCap_ne_zero := hcapZero
    multiplicityCap_ne_top := hcapTop
    rotatedCoverCenters := rotatedCoverCenters
    cover_card := by simpa [hrotatedCard] using hcoverCard
    rotated_cover := by
      intro point hpoint
      rcases hpoint with ⟨source, hsource, rfl⟩
      rcases hcover source hsource with ⟨center, hcenter, hball⟩
      refine ⟨rotation center, Finset.mem_map.mpr
        ⟨center, hcenter, rfl⟩, ?_⟩
      have hdist := rotation.isometry.dist_eq source center
      simpa [Metric.mem_closedBall] using hdist ▸ hball
    goodY := goodY
    goodY_measurable := hgoodY
    goodY_subset := hgoodYSubset
    goodY_ne_zero := hgoodYZero
    badY_volume := hbadY
    cover_count := hcoverCount
    every_label_good_half := heveryHalf
    goodRegion := goodRegion
    goodRegion_eq := rfl
    goodRegion_measurable := hgoodRegionMeasurable
    goodRegion_ne_zero := hgoodRegionZero
    goodRegion_volume_lower := hgoodRegionLower
    y0 := y0
    y0_mem := hy0
    common_slice_average := hy0Average
    selectedLabels := selectedLabels
    selectedLabels_eq := rfl
    selectedLabels_subset := hselectedSubset
    selectedLabels_nonempty := hselectedNonempty
    selected_label_count_lower := hselectedCountLower
    selectedCells := selectedCells
    selectedCells_eq := rfl
    selectedCells_subset := hselectedCellsSubset
    F2 := F2
    F2_eq := rfl
    F2_cubical := wz2RefinedShading_cubical scaleData.slab_cubical
    F2_in_slab := fun index =>
      (wz2RefinedShading_subshading index).trans
        (scaleData.slab_in_slab index)
    F2_union_eq := hF2Union
    selected_labels_mass_lower := hselectedLabelsMass
    common_slice_mass_lower := hcommonSliceMass
    F2_mass_retention := by simpa [lossFactor] using hretention
    common_slice_subset_F2 := hcommonSubset
  }, rfl⟩

/-- Strong quadratic-frame wrapper used by the Lemma-31 contradiction. -/
theorem pureWZ2_rotatedWeightedCommonYRefinement
    {sigma grainLoss slabLoss badYLoss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale)
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (hbadYLoss : 0 < badYLoss) (hdeltaLtOne : delta < 1)
    (frameSlope : ℝ)
    (hlabelClose : ∀ label (hlabel : label ∈ popular.keptLabels),
      |cfg.globalGrains.slope
          ((pureWZ2PaperCellCenter delta
            (popular.label_anchor label hlabel)) 2) - frameSlope| ≤
        2 * scale.1 ^ 2)
    (hframeSmall : 2 * scale.1 ^ 2 ≤ 1 / 100)
    (multiplicityCap : ENNReal)
    (hcapZero : multiplicityCap ≠ 0)
    (hcapTop : multiplicityCap ≠ ⊤)
    (hpointCap : ∀ point,
      (scaleData.slabShading.pointMultiplicity point : ENNReal) ≤
        multiplicityCap)
    (hbadBudget :
      ENNReal.ofReal (128 * delta ^ 2) *
          (2 * Kakeya.realRpowENN delta (4 * badYLoss)) ≤
        (1 / 2 : ENNReal) *
          (popular.labelThreshold / multiplicityCap)) :
    ∃ common : PureWZ2RotatedWeightedCommonYData
        cfg scale scaleData popular frameSlope,
      common.badYLoss = badYLoss := by
  rcases pureWZ2_rotatedWeightedCommonYRefinementCore cfg scale scaleData
      popular hbadYLoss hdeltaLtOne frameSlope hlabelClose hframeSmall
      multiplicityCap hcapZero hcapTop hpointCap hbadBudget with
    ⟨core, hcoreLoss⟩
  exact ⟨{
    toPureWZ2RotatedWeightedCommonYCore := core
    selected_label_frame_close := fun label hlabel =>
      hlabelClose label (core.selectedLabels_subset hlabel)
    frame_small := hframeSmall
  }, hcoreLoss⟩

end Kakeya.Assouad

end
