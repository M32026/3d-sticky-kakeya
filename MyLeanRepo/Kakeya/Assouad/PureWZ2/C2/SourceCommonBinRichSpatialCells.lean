import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinOccupiedBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinSpatialCellSliceBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CommonBinRichSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains

/-!
# Rich fixed common bins meet many spatial cells

This module joins the fixed common-bin labels with the local source `a₀`
estimate.  A cell below is always a literal spatial paper-grid cube of side
`side`; it is never a parent tube.

The construction-independent part partitions one fixed-bin planar slice into
the finitely many bounded paper-grid cubes that it actually meets.  The source
specialization takes `side = sqrt rho`, bounds every summand by the source
global-AD slice estimate, and invokes the finite rich-bin cardinality lemma.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The part of `E` carrying one height-independent common-bin label. -/
def pureWZ2FixedCommonBinRegion
    (E : Set Point3) (slope : ℝ → ℝ)
    (referenceHeight side : ℝ) (bin : ℤ) : Set Point3 :=
  E ∩ {point |
    pureWZ2FixedCommonBinLabel slope referenceHeight side point = bin}

/-- Planar mass of one fixed common bin at the genuine height `height`. -/
def pureWZ2FixedCommonBinSliceMass
    (E : Set Point3) (slope : ℝ → ℝ)
    (referenceHeight side height : ℝ) (bin : ℤ) : ENNReal :=
  volume
    (wz1Lemma23PlanarSlice
      (pureWZ2FixedCommonBinRegion
        E slope referenceHeight side bin)
      height)

/-- The contribution of one literal side-`side` spatial cube to a fixed-bin
slice. -/
def pureWZ2FixedCommonBinSpatialCellSliceMass
    (E : Set Point3) (slope : ℝ → ℝ)
    (referenceHeight side height : ℝ) (bin : ℤ)
    (cell : ℤ × ℤ × ℤ) : ENNReal :=
  volume
    (wz1Lemma23PlanarSlice
      (pureWZ2FixedCommonBinRegion
          E slope referenceHeight side bin ∩
        wz1PaperGridCube side cell)
      height)

/-- A finite universe of literal side-`side` paper cubes containing every
cube that meets the radius-two ball. -/
def pureWZ2BoundedPaperGridCells
    (side : ℝ) (hside : 0 < side) : Finset (ℤ × ℤ × ℤ) :=
  gridIndicesInRadius 2 (side * Real.sqrt 3 / 2) (by positivity)

private lemma pureWZ2_paperGridIndex_mem_bounded
    {side : ℝ} (hside : 0 < side)
    {point : Point3} (hpoint : ‖point‖ ≤ 2) :
    wz1PaperGridIndex side point ∈
      pureWZ2BoundedPaperGridCells side hside := by
  have hsqrt : Real.sqrt 3 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hparameter : 0 < side * Real.sqrt 3 / 2 := by
    positivity
  have hscale :
      gridSide (side * Real.sqrt 3 / 2) = side := by
    rw [gridSide]
    field_simp
  have hindex :
      rhoGridIndex (side * Real.sqrt 3 / 2) point =
        wz1PaperGridIndex side point := by
    simp only [rhoGridIndex, wz1PaperGridIndex, hscale]
  change
    wz1PaperGridIndex side point ∈
      gridIndicesInRadius 2 (side * Real.sqrt 3 / 2) _
  rw [← hindex]
  exact gridIndex_inRadius (by norm_num) hparameter hpoint

/-- The active spatial cubes for one `(height, bin)` pair.  Activity means
that the corresponding genuine planar slice is nonempty. -/
def pureWZ2FixedCommonBinActiveSpatialCells
    (E : Set Point3) (slope : ℝ → ℝ)
    (referenceHeight side : ℝ) (hside : 0 < side)
    (height : ℝ) (bin : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (pureWZ2BoundedPaperGridCells side hside).filter fun cell =>
    (wz1Lemma23PlanarSlice
      (pureWZ2FixedCommonBinRegion
          E slope referenceHeight side bin ∩
        wz1PaperGridCube side cell)
      height).Nonempty

private theorem measurableSet_pureWZ2PlanarSlice
    {E : Set Point3} (hE : MeasurableSet E) (height : ℝ) :
    MeasurableSet (wz1Lemma23PlanarSlice E height) := by
  have hlift :
      Continuous (fun point : Point2 =>
        point3 (point 0) (point 1) height) := by
    unfold point3
    fun_prop
  have heq :
      wz1Lemma23PlanarSlice E height =
        (fun point : Point2 =>
          point3 (point 0) (point 1) height) ⁻¹' E := by
    ext point
    exact wz1Lemma23_mem_planarSlice_iff
  rw [heq]
  exact hE.preimage hlift.measurable

/-- A fixed common-bin region is measurable whenever its ambient set is. -/
theorem measurableSet_pureWZ2FixedCommonBinRegion
    {E : Set Point3} (hE : MeasurableSet E)
    (slope : ℝ → ℝ) (referenceHeight side : ℝ) (bin : ℤ) :
    MeasurableSet
      (pureWZ2FixedCommonBinRegion
        E slope referenceHeight side bin) := by
  have hcoordinate :
      Measurable (fun point : Point3 =>
        inner ℝ point
          (globalGrainDirection (slope referenceHeight)) / side) := by
    fun_prop
  have hlabel :
      MeasurableSet {point : Point3 |
        pureWZ2FixedCommonBinLabel
          slope referenceHeight side point = bin} := by
    exact
      (Int.measurable_floor.comp hcoordinate)
        (MeasurableSet.singleton bin)
  exact hE.inter hlabel

/-- The fixed-bin slice is exactly the disjoint union of the active literal
spatial-cube slices. -/
theorem pureWZ2_fixed_common_bin_slice_eq_iUnion_activeSpatialCells
    {E : Set Point3} (slope : ℝ → ℝ)
    (referenceHeight : ℝ) {side : ℝ} (hside : 0 < side)
    (height : ℝ) (bin : ℤ)
    (hbounded : ∀ point ∈ E, ‖point‖ ≤ 2) :
    wz1Lemma23PlanarSlice
        (pureWZ2FixedCommonBinRegion
          E slope referenceHeight side bin)
        height =
      ⋃ cell ∈
          pureWZ2FixedCommonBinActiveSpatialCells
            E slope referenceHeight side hside height bin,
        wz1Lemma23PlanarSlice
          (pureWZ2FixedCommonBinRegion
              E slope referenceHeight side bin ∩
            wz1PaperGridCube side cell)
          height := by
  ext point
  constructor
  · intro hpoint
    have hlift :
        point3 (point 0) (point 1) height ∈
          pureWZ2FixedCommonBinRegion
            E slope referenceHeight side bin :=
      wz1Lemma23_mem_planarSlice_iff.mp hpoint
    let cell :=
      wz1PaperGridIndex side
        (point3 (point 0) (point 1) height)
    have hcellBounded :
        cell ∈ pureWZ2BoundedPaperGridCells side hside := by
      apply pureWZ2_paperGridIndex_mem_bounded hside
      exact hbounded _ hlift.1
    have hcellCube :
        point3 (point 0) (point 1) height ∈
          wz1PaperGridCube side cell := by
      exact (mem_wz1PaperGridCube side cell _).mpr rfl
    have hlocal :
        point ∈
          wz1Lemma23PlanarSlice
            (pureWZ2FixedCommonBinRegion
                E slope referenceHeight side bin ∩
              wz1PaperGridCube side cell)
            height :=
      wz1Lemma23_mem_planarSlice_iff.mpr ⟨hlift, hcellCube⟩
    have hcellActive :
        cell ∈ pureWZ2FixedCommonBinActiveSpatialCells
          E slope referenceHeight side hside height bin := by
      exact Finset.mem_filter.mpr
        ⟨hcellBounded, ⟨point, hlocal⟩⟩
    exact Set.mem_iUnion₂.mpr ⟨cell, hcellActive, hlocal⟩
  · intro hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨cell, _hcell, hlocal⟩
    exact wz1Lemma23_mem_planarSlice_iff.mpr
      (wz1Lemma23_mem_planarSlice_iff.mp hlocal).1

/-- Exact fixed-bin mass decomposition over distinct active spatial cubes. -/
theorem pureWZ2_fixed_common_bin_sliceMass_eq_sum_activeSpatialCells
    {E : Set Point3} (hE : MeasurableSet E)
    (slope : ℝ → ℝ) (referenceHeight : ℝ)
    {side : ℝ} (hside : 0 < side)
    (height : ℝ) (bin : ℤ)
    (hbounded : ∀ point ∈ E, ‖point‖ ≤ 2) :
    pureWZ2FixedCommonBinSliceMass
        E slope referenceHeight side height bin =
      ∑ cell ∈
          pureWZ2FixedCommonBinActiveSpatialCells
            E slope referenceHeight side hside height bin,
        pureWZ2FixedCommonBinSpatialCellSliceMass
          E slope referenceHeight side height bin cell := by
  let cells :=
    pureWZ2FixedCommonBinActiveSpatialCells
      E slope referenceHeight side hside height bin
  let piece : (ℤ × ℤ × ℤ) → Set Point2 := fun cell =>
    wz1Lemma23PlanarSlice
      (pureWZ2FixedCommonBinRegion
          E slope referenceHeight side bin ∩
        wz1PaperGridCube side cell)
      height
  have hpartition :
      wz1Lemma23PlanarSlice
          (pureWZ2FixedCommonBinRegion
            E slope referenceHeight side bin)
          height =
        ⋃ cell ∈ cells, piece cell := by
    simpa [cells, piece] using
      pureWZ2_fixed_common_bin_slice_eq_iUnion_activeSpatialCells
        slope referenceHeight hside height bin hbounded
  have hdisjoint :
      (cells : Set (ℤ × ℤ × ℤ)).PairwiseDisjoint piece := by
    intro first _ second _ hne
    change Disjoint (piece first) (piece second)
    rw [Set.disjoint_left]
    intro point hfirst hsecond
    have hfirstLift :=
      wz1Lemma23_mem_planarSlice_iff.mp hfirst
    have hsecondLift :=
      wz1Lemma23_mem_planarSlice_iff.mp hsecond
    exact Set.disjoint_left.mp
      (wz1PaperGridCube_disjoint hne)
      hfirstLift.2 hsecondLift.2
  have hregionMeasurable :
      MeasurableSet
        (pureWZ2FixedCommonBinRegion
          E slope referenceHeight side bin) :=
    measurableSet_pureWZ2FixedCommonBinRegion
      hE slope referenceHeight side bin
  have hmeasurable :
      ∀ cell ∈ cells, MeasurableSet (piece cell) := by
    intro cell _
    exact measurableSet_pureWZ2PlanarSlice
      (hregionMeasurable.inter (wz1PaperGridCube_measurable cell))
      height
  rw [pureWZ2FixedCommonBinSliceMass, hpartition,
    MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable]
  rfl

/-- If a finite set contains the fixed label of every point in a horizontal
slice, then the bin slice masses sum exactly to the full planar slice mass. -/
theorem pureWZ2_fixed_common_bin_sliceMass_sum
    {E : Set Point3} (hE : MeasurableSet E)
    (slope : ℝ → ℝ) (referenceHeight side height : ℝ)
    (bins : Finset ℤ)
    (hcover :
      ∀ point ∈ horizontalSlice E height,
        pureWZ2FixedCommonBinLabel
          slope referenceHeight side point ∈ bins) :
    volume (wz1Lemma23PlanarSlice E height) =
      ∑ bin ∈ bins,
        pureWZ2FixedCommonBinSliceMass
          E slope referenceHeight side height bin := by
  let piece : ℤ → Set Point2 := fun bin =>
    wz1Lemma23PlanarSlice
      (pureWZ2FixedCommonBinRegion
        E slope referenceHeight side bin)
      height
  have hpartition :
      wz1Lemma23PlanarSlice E height =
        ⋃ bin ∈ bins, piece bin := by
    ext point
    constructor
    · intro hpoint
      have hlift :
          point3 (point 0) (point 1) height ∈ E :=
        wz1Lemma23_mem_planarSlice_iff.mp hpoint
      let bin :=
        pureWZ2FixedCommonBinLabel slope referenceHeight side
          (point3 (point 0) (point 1) height)
      have hhorizontal :
          point3 (point 0) (point 1) height ∈
            horizontalSlice E height := by
        exact ⟨hlift, by simp [point3]⟩
      have hbin : bin ∈ bins := hcover _ hhorizontal
      have hpiece : point ∈ piece bin := by
        apply wz1Lemma23_mem_planarSlice_iff.mpr
        exact ⟨hlift, rfl⟩
      exact Set.mem_iUnion₂.mpr ⟨bin, hbin, hpiece⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨bin, _hbin, hpiece⟩
      exact wz1Lemma23_mem_planarSlice_iff.mpr
        (wz1Lemma23_mem_planarSlice_iff.mp hpiece).1
  have hdisjoint :
      (bins : Set ℤ).PairwiseDisjoint piece := by
    intro first _ second _ hne
    change Disjoint (piece first) (piece second)
    rw [Set.disjoint_left]
    intro point hfirst hsecond
    have hfirstLift :=
      wz1Lemma23_mem_planarSlice_iff.mp hfirst
    have hsecondLift :=
      wz1Lemma23_mem_planarSlice_iff.mp hsecond
    exact hne (hfirstLift.2.symm.trans hsecondLift.2)
  have hmeasurable :
      ∀ bin ∈ bins, MeasurableSet (piece bin) := by
    intro bin _
    exact measurableSet_pureWZ2PlanarSlice
      (measurableSet_pureWZ2FixedCommonBinRegion
        hE slope referenceHeight side bin)
      height
  rw [hpartition,
    MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable]
  rfl

/-- A rich fixed bin contains at least `K` active spatial cubes once every
cube-slice summand is bounded by `cellCap`. -/
theorem pureWZ2_rich_common_bin_activeSpatialCells_card_lower
    {E : Set Point3} (hE : MeasurableSet E)
    (slope : ℝ → ℝ) (referenceHeight : ℝ)
    {side : ℝ} (hside : 0 < side)
    (height : ℝ) (bins : Finset ℤ)
    (threshold cellCap : ENNReal) (K : ℕ) (bin : ℤ)
    (hbounded : ∀ point ∈ E, ‖point‖ ≤ 2)
    (hrich :
      bin ∈ CommonBinRichSelection.richBins bins
        (pureWZ2FixedCommonBinSliceMass
          E slope referenceHeight side height)
        threshold)
    (hcellUpper :
      ∀ cell ∈
          pureWZ2FixedCommonBinActiveSpatialCells
            E slope referenceHeight side hside height bin,
        pureWZ2FixedCommonBinSpatialCellSliceMass
            E slope referenceHeight side height bin cell ≤
          cellCap)
    (hK : (K : ENNReal) * cellCap ≤ threshold)
    (hcellCapPos : 0 < cellCap)
    (hcellCapTop : cellCap ≠ ⊤) :
    K ≤
      (pureWZ2FixedCommonBinActiveSpatialCells
        E slope referenceHeight side hside height bin).card := by
  apply CommonBinRichSelection.cell_card_lower_of_rich
    (pureWZ2FixedCommonBinActiveSpatialCells
      E slope referenceHeight side hside height bin)
    (pureWZ2FixedCommonBinSpatialCellSliceMass
      E slope referenceHeight side height bin)
    (pureWZ2FixedCommonBinSliceMass
      E slope referenceHeight side height bin)
    threshold cellCap K
  · exact (Finset.mem_filter.mp hrich).2
  · exact le_of_eq
      (pureWZ2_fixed_common_bin_sliceMass_eq_sum_activeSpatialCells
        hE slope referenceHeight hside height bin hbounded)
  · exact hcellUpper
  · exact hK
  · exact hcellCapPos
  · exact hcellCapTop

namespace PureWZ2SourceHorizontalFixedLineData

/-- The fixed common-bin region inside the selected source-heavy window. -/
def commonBinRegion
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (_line : PureWZ2SourceHorizontalFixedLineData window)
    (referenceHeight : ℝ) (bin : ℤ) : Set Point3 :=
  pureWZ2FixedCommonBinRegion
    window.shading.union source.globalGrains.slope
    referenceHeight (Real.sqrt rho) bin

/-- Mass of the fixed common-bin region on the genuine slice at `height`. -/
def commonBinSliceMass
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (_line : PureWZ2SourceHorizontalFixedLineData window)
    (referenceHeight height : ℝ) (bin : ℤ) : ENNReal :=
  pureWZ2FixedCommonBinSliceMass
    window.shading.union source.globalGrains.slope
    referenceHeight (Real.sqrt rho) height bin

/-- One literal side-`sqrt rho` spatial cube's contribution to a fixed-bin
slice of the selected source-heavy window. -/
def commonBinSpatialCellSliceMass
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (_line : PureWZ2SourceHorizontalFixedLineData window)
    (referenceHeight height : ℝ) (bin : ℤ)
    (cell : ℤ × ℤ × ℤ) : ENNReal :=
  pureWZ2FixedCommonBinSpatialCellSliceMass
    window.shading.union source.globalGrains.slope
    referenceHeight (Real.sqrt rho) height bin cell

/-- Active literal side-`sqrt rho` spatial cubes for one `(height, bin)`.
The positivity proof is supplied by the fixed-line data and does not change
the underlying finite set. -/
def commonBinActiveSpatialCells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window)
    (referenceHeight height : ℝ) (bin : ℤ) :
    Finset (ℤ × ℤ × ℤ) :=
  pureWZ2FixedCommonBinActiveSpatialCells
    window.shading.union source.globalGrains.slope
    referenceHeight (Real.sqrt rho) (Real.sqrt_pos.mpr line.rho_pos)
    height bin

/-- The source global-AD upper bound `a₀` for one side-`sqrt rho` spatial
cube slice. -/
def commonBinSpatialCellCap
    (sigma inputLoss delta rho : ℝ) : ENNReal :=
  32 * Kakeya.realRpowENN delta (-inputLoss) *
    Kakeya.realRpowENN delta sigma *
    Kakeya.realRpowENN rho (1 - sigma / 2)

private theorem window_union_subset_source
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared} :
    window.shading.union ⊆ source.shading.union := by
  intro point hpoint
  have hshadow : point ∈ prepared.shadow.union :=
    window.subshading.union_subset hpoint
  have hpullback : point ∈ pullback.shading.union := by
    rwa [prepared.shadow_union] at hshadow
  exact pullback.subshading.union_subset hpullback

private theorem commonBin_window_norm_le_two
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (point : Point3) (hpoint : point ∈ window.shading.union) :
    ‖point‖ ≤ 2 :=
  norm_le_two_of_mem_paperShading
    (window_union_subset_source hpoint)

/-- The source `a₀` estimate bounds every active fixed-bin spatial-cube
summand.  The comparison is by set inclusion inside the same literal cube. -/
theorem commonBinSpatialCellSliceMass_le
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window)
    (referenceHeight height : ℝ)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (bin : ℤ) (cell : ℤ × ℤ × ℤ) :
    line.commonBinSpatialCellSliceMass
        referenceHeight height bin cell ≤
      commonBinSpatialCellCap sigma inputLoss delta rho := by
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hdeltaRho : delta ≤ rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1
  have hrhoRoot : rho ≤ Real.sqrt rho := by
    nlinarith [Real.sq_sqrt line.rho_pos.le, Real.sqrt_nonneg rho]
  have hdeltaRoot : delta ≤ Real.sqrt rho :=
    hdeltaRho.trans hrhoRoot
  have hsubset :
      wz1Lemma23PlanarSlice
          (line.commonBinRegion referenceHeight bin ∩
            wz1PaperGridCube (Real.sqrt rho) cell)
          height ⊆
        wz1Lemma23PlanarSlice
          (source.shading.union ∩
            wz1PaperGridCube (Real.sqrt rho) cell)
          height := by
    intro point hpoint
    have hlift :=
      wz1Lemma23_mem_planarSlice_iff.mp hpoint
    apply wz1Lemma23_mem_planarSlice_iff.mpr
    exact
      ⟨window_union_subset_source hlift.1.1, hlift.2⟩
  calc
    line.commonBinSpatialCellSliceMass
          referenceHeight height bin cell =
        volume
          (wz1Lemma23PlanarSlice
            (line.commonBinRegion referenceHeight bin ∩
              wz1PaperGridCube (Real.sqrt rho) cell)
            height) := rfl
    _ ≤ volume
          (wz1Lemma23PlanarSlice
            (source.shading.union ∩
              wz1PaperGridCube (Real.sqrt rho) cell)
            height) :=
      measure_mono hsubset
    _ ≤ commonBinSpatialCellCap sigma inputLoss delta rho := by
      simpa [commonBinSpatialCellCap] using
        source.sourceCommonBinSpatialCellSliceBound
          line.rho_pos hdeltaRoot cell height hheight

/-- Exact source-window fixed-bin mass decomposition into active
side-`sqrt rho` spatial cubes. -/
theorem commonBinSliceMass_eq_sum_activeSpatialCells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window)
    (referenceHeight height : ℝ) (bin : ℤ) :
    line.commonBinSliceMass referenceHeight height bin =
      ∑ cell ∈
          line.commonBinActiveSpatialCells referenceHeight height bin,
        line.commonBinSpatialCellSliceMass
          referenceHeight height bin cell := by
  simpa [commonBinSliceMass, commonBinActiveSpatialCells,
    commonBinSpatialCellSliceMass] using
    pureWZ2_fixed_common_bin_sliceMass_eq_sum_activeSpatialCells
      (measurableSet_shading_union window.shading)
      source.globalGrains.slope referenceHeight
      (Real.sqrt_pos.mpr line.rho_pos) height bin
      commonBin_window_norm_le_two

/-- Every point on the selected source-heavy line has its fixed label in the
finite occupied-bin set. -/
theorem fixedCommonBinLabel_mem_occupiedCommonBins
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window)
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight :
      |line.lineHeight - referenceHeight| ≤ Real.sqrt rho)
    {point : Point3}
    (hpoint :
      point ∈ horizontalSlice window.shading.union line.lineHeight) :
    pureWZ2FixedCommonBinLabel source.globalGrains.slope
        referenceHeight (Real.sqrt rho) point ∈
      line.occupiedCommonBins referenceHeight := by
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hrootPos : 0 < Real.sqrt rho :=
    Real.sqrt_pos.mpr line.rho_pos
  have hrhoRoot : rho ≤ Real.sqrt rho := by
    nlinarith [Real.sq_sqrt line.rho_pos.le, Real.sqrt_nonneg rho]
  have hrootOne : Real.sqrt rho ≤ 1 :=
    Real.sqrt_le_one.mpr hrhoOne
  have hADrho :
      IsADSet1
        (scalarProjection
          (globalGrainDirection
            (source.globalGrains.slope line.lineHeight))
          (horizontalSlice window.shading.union line.lineHeight))
        rho (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss)) := by
    apply (prepared.exactAD line.lineHeight line.lineHeight_mem).mono
    rintro value ⟨sourcePoint, hsourcePoint, rfl⟩
    exact
      ⟨sourcePoint,
        ⟨window.subshading.union_subset hsourcePoint.1,
          hsourcePoint.2⟩,
        rfl⟩
  have hADroot :
      IsADSet1
        (scalarProjection
          (globalGrainDirection
            (source.globalGrains.slope line.lineHeight))
          (horizontalSlice window.shading.union line.lineHeight))
        (Real.sqrt rho) (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss)) :=
    hADrho.coarsen_scale hrootPos hrhoRoot hrootOne
  have hy :
      ∀ sourcePoint ∈
          horizontalSlice window.shading.union line.lineHeight,
        |sourcePoint (1 : Fin 3)| ≤ 1 := by
    intro sourcePoint hsourcePoint
    have hsource :
        sourcePoint ∈ source.shading.union :=
      window_union_subset_source hsourcePoint.1
    have hbox := shading_union_subset_axisBox hsource
    simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
  simpa [occupiedCommonBins] using
    pureWZ2_fixed_common_bin_mem
      (horizontalSlice window.shading.union line.lineHeight)
      source.globalGrains.slope
      source.globalGrains.slope_lipschitz
      line.lineHeight referenceHeight
      line.lineHeight_mem hreference hheight hy
      hADroot hrootOne hpoint

/-- The fixed occupied bins form an exact mass partition of the selected
source-heavy planar slice. -/
theorem occupiedCommonBins_sliceMass_sum
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window)
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight :
      |line.lineHeight - referenceHeight| ≤ Real.sqrt rho) :
    volume
        (wz1Lemma23PlanarSlice
          window.shading.union line.lineHeight) =
      ∑ bin ∈ line.occupiedCommonBins referenceHeight,
        line.commonBinSliceMass
          referenceHeight line.lineHeight bin := by
  simpa [commonBinSliceMass] using
    pureWZ2_fixed_common_bin_sliceMass_sum
      (measurableSet_shading_union window.shading)
      source.globalGrains.slope referenceHeight (Real.sqrt rho)
      line.lineHeight (line.occupiedCommonBins referenceHeight)
      (fun point hpoint =>
        line.fixedCommonBinLabel_mem_occupiedCommonBins
          referenceHeight hreference hheight hpoint)

/-- A rich common bin on the fixed source line meets at least `K` distinct
active side-`sqrt rho` spatial cubes. -/
theorem richCommonBin_activeSpatialCells_card_lower
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window)
    (referenceHeight : ℝ) (threshold : ENNReal)
    (K : ℕ) (bin : ℤ)
    (hrich :
      bin ∈ CommonBinRichSelection.richBins
        (line.occupiedCommonBins referenceHeight)
        (line.commonBinSliceMass referenceHeight line.lineHeight)
        threshold)
    (hK :
      (K : ENNReal) *
          commonBinSpatialCellCap sigma inputLoss delta rho ≤
        threshold) :
    K ≤
      (line.commonBinActiveSpatialCells
        referenceHeight line.lineHeight bin).card := by
  apply CommonBinRichSelection.cell_card_lower_of_rich
    (line.commonBinActiveSpatialCells
      referenceHeight line.lineHeight bin)
    (line.commonBinSpatialCellSliceMass
      referenceHeight line.lineHeight bin)
    (line.commonBinSliceMass
      referenceHeight line.lineHeight bin)
    threshold
    (commonBinSpatialCellCap sigma inputLoss delta rho)
    K
  · exact (Finset.mem_filter.mp hrich).2
  · exact le_of_eq
      (line.commonBinSliceMass_eq_sum_activeSpatialCells
        referenceHeight line.lineHeight bin)
  · intro cell _hcell
    exact line.commonBinSpatialCellSliceMass_le
      referenceHeight line.lineHeight line.lineHeight_mem bin cell
  · exact hK
  · have hdeltaLoss :
        0 < Kakeya.realRpowENN delta (-inputLoss) :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos source.extremal.delta_pos _)
    have hdeltaSigma :
        0 < Kakeya.realRpowENN delta sigma :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos source.extremal.delta_pos _)
    have hrhoPower :
        0 < Kakeya.realRpowENN rho (1 - sigma / 2) :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos line.rho_pos _)
    exact ENNReal.mul_pos
      (ENNReal.mul_pos
        (ENNReal.mul_pos
          (by norm_num : (32 : ENNReal) ≠ 0)
          hdeltaLoss.ne').ne'
        hdeltaSigma.ne').ne'
      hrhoPower.ne'
  · simp only [commonBinSpatialCellCap, Kakeya.realRpowENN]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top

/-- Select a rich fixed bin on the genuine source-heavy line and obtain `K`
distinct active side-`sqrt rho` spatial cubes.  The first conjunct records the
independent occupied-bin bound `B₀`; the `K` conclusion uses only the local
source cell cap `a₀`. -/
theorem exists_richCommonBin_with_many_activeSpatialCells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window)
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight :
      |line.lineHeight - referenceHeight| ≤ Real.sqrt rho)
    (hwindowVolume : 0 < volume window.shading.union)
    (threshold : ENNReal) (K : ℕ)
    (hpoor :
      2 *
          ((line.occupiedCommonBins referenceHeight).card : ENNReal) *
          threshold ≤
        volume
          (wz1Lemma23PlanarSlice
            window.shading.union line.lineHeight))
    (hK :
      (K : ENNReal) *
          commonBinSpatialCellCap sigma inputLoss delta rho ≤
        threshold) :
    ((line.occupiedCommonBins referenceHeight).card : ENNReal) ≤
        132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ∧
      ∃ bin ∈ line.occupiedCommonBins referenceHeight,
        threshold ≤
            line.commonBinSliceMass
              referenceHeight line.lineHeight bin ∧
          K ≤
            (line.commonBinActiveSpatialCells
              referenceHeight line.lineHeight bin).card := by
  let bins := line.occupiedCommonBins referenceHeight
  let weight : ℤ → ENNReal :=
    line.commonBinSliceMass referenceHeight line.lineHeight
  let total :=
    volume
      (wz1Lemma23PlanarSlice window.shading.union line.lineHeight)
  have htotalEq :
      total = ∑ bin ∈ bins, weight bin := by
    simpa [total, bins, weight] using
      line.occupiedCommonBins_sliceMass_sum
        referenceHeight hreference hheight
  have htotalPos : 0 < total := by
    have hquotient :
        0 <
          volume window.shading.union /
            ENNReal.ofReal (Real.sqrt rho + 2 * rho) :=
      ENNReal.div_pos hwindowVolume.ne' ENNReal.ofReal_ne_top
    exact hquotient.trans_le (by
      simpa [total] using line.slice_area_lower)
  have hball :
      window.shading.union ⊆
        Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hnorm := commonBin_window_norm_le_two point hpoint
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have htotalUpper :=
    wz1_lemma23_exactSlice_area_le_two
      window.shading source.extremal.delta_pos hball line.lineHeight
  have htotalTop : total ≠ ⊤ := by
    apply ne_top_of_le_ne_top
      (show
        ((wz1Lemma23ExactSliceCells window.shading delta
            source.extremal.delta_pos line.lineHeight).card : ENNReal) *
            (ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi) ≠ ⊤ by
        exact ENNReal.mul_ne_top
          (ENNReal.natCast_ne_top _)
          (ENNReal.mul_ne_top
            (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
            ENNReal.ofReal_ne_top))
    simpa [total] using htotalUpper
  have hretained :=
    CommonBinRichSelection.total_le_two_mul_rich_sum
      bins weight threshold total htotalEq htotalTop (by
        simpa [bins, total, mul_assoc] using hpoor)
  have hrichNonempty :
      (CommonBinRichSelection.richBins
        bins weight threshold).Nonempty := by
    by_contra hnone
    have hempty :
        CommonBinRichSelection.richBins bins weight threshold = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnone
    have hzero :
        (∑ bin ∈
          CommonBinRichSelection.richBins bins weight threshold,
          weight bin) = 0 := by
      simp [hempty]
    rw [hzero] at hretained
    have htotalZero : total ≤ 0 := by
      simpa using hretained
    exact (not_le_of_gt htotalPos) htotalZero
  let bin := Classical.choose hrichNonempty
  have hbinRich :
      bin ∈ CommonBinRichSelection.richBins bins weight threshold :=
    Classical.choose_spec hrichNonempty
  have hbinData := Finset.mem_filter.mp hbinRich
  constructor
  · exact line.occupiedCommonBins_bound
      referenceHeight hreference hheight
  · refine ⟨bin, ?_, ?_, ?_⟩
    · simpa [bins] using hbinData.1
    · simpa [weight] using hbinData.2
    · apply line.richCommonBin_activeSpatialCells_card_lower
        referenceHeight threshold K bin
      · simpa [bins, weight] using hbinRich
      · exact hK

end PureWZ2SourceHorizontalFixedLineData

end Kakeya.Assouad

end
