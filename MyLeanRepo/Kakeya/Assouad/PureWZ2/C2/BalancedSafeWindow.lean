import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCarrierPreparation

/-!
# Balanced source cells safely inside one Lemma-23 height window

This module isolates the carrier-faithful replacement for the old spatial
expansion step.  We retain actual side-`rho` cells from the balanced pullback
and require their centers to stay one `rho` away from the endpoints of a
`sqrt rho` window.  The margin ensures that every auxiliary Lemma-23 cell
meeting the retained shading has its snapped center in the exact window.

The retained shading is a literal subshading of the prepared source carrier,
and its union volume is the exact number of retained balanced cells times the
balanced cell mass.  No fixed-line or parent carrier is substituted for the
source shading.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Height of the center of a paper side-`rho` cell. -/
def pureWZ2PaperCellCenterHeight
    (rho : ℝ) (cell : ℤ × ℤ × ℤ) : ℝ :=
  ((cell.2.2 : ℝ) + 1 / 2) * rho

/-- Balanced side-`rho` cells whose full one-cell margin lies inside the
requested `sqrt rho` height window. -/
def pureWZ2BalancedSafeWindowCells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (left : ℝ) : Finset (ℤ × ℤ × ℤ) :=
  pullback.selectedCells.filter fun cell =>
    pureWZ2PaperCellCenterHeight rho cell ∈
      Set.Icc (left + rho) (left + Real.sqrt rho - rho)

structure PureWZ2BalancedSafeWindowData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (left : ℝ) where
  cells : Finset (ℤ × ℤ × ℤ) :=
    pureWZ2BalancedSafeWindowCells (pullback := pullback) left
  cells_eq : cells =
    pureWZ2BalancedSafeWindowCells (pullback := pullback) left
  cells_nonempty : cells.Nonempty
  region : Set Point3 :=
    ⋃ cell ∈ cells, wz1PaperGridCube rho cell
  region_eq : region =
    ⋃ cell ∈ cells, wz1PaperGridCube rho cell
  region_measurable : MeasurableSet region
  shading : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily pullback.shading source.extremal.delta_pos)
  carrier_eq : ∀ index, shading.carrier index =
    prepared.shadow.carrier index ∩ region
  subshading : IsSubshading shading prepared.shadow
  union_eq : shading.union = prepared.shadow.union ∩ region
  volume_eq : MeasureTheory.volume shading.union =
    (cells.card : ENNReal) * twoScale.coarse.balanced.cellMass
  active_cell_window :
    ∀ cell ∈ wz1Lemma23ActiveCells shading rho
        (source.extremal.delta_pos.trans_le (by
          rw [← twoScale.rhoRequested_eq]
          exact twoScale.rhoRequested.property.1)),
      (wz1Lemma23SnappedPoint rho cell) (2 : Fin 3) ∈
        Set.Icc left (left + Real.sqrt rho)
  window : PureWZ2SourceCarrierWindow prepared
  window_left : window.left = left
  window_shading : window.shading = shading
  window_supply : window.volumeSupply =
    (cells.card : ENNReal) * twoScale.coarse.balanced.cellMass

theorem PureWZ2SourceCarrierPreparation.balancedSafeWindow
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (left : ℝ)
    (hnonempty :
      (pureWZ2BalancedSafeWindowCells
        (pullback := pullback) left).Nonempty) :
    Nonempty (PureWZ2BalancedSafeWindowData prepared left) := by
  let cells := pureWZ2BalancedSafeWindowCells
    (pullback := pullback) left
  let region : Set Point3 :=
    ⋃ cell ∈ cells, wz1PaperGridCube rho cell
  have hregionMeasurable : MeasurableSet region :=
    MeasurableSet.biUnion cells.finite_toSet.countable
      (fun cell _ => wz1PaperGridCube_measurable cell)
  let shading : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily pullback.shading source.extremal.delta_pos) :=
    { carrier := fun index => prepared.shadow.carrier index ∩ region
      measurable_carrier := fun index =>
        (prepared.shadow.measurable_carrier index).inter hregionMeasurable
      subset_body := fun index => Set.inter_subset_left.trans
        (prepared.shadow.subset_body index) }
  have hsub : IsSubshading shading prepared.shadow :=
    fun _ => Set.inter_subset_left
  have hunion : shading.union = prepared.shadow.union ∩ region := by
    ext point
    constructor
    · rintro ⟨index, hpoint, hregion⟩
      exact ⟨⟨index, hpoint⟩, hregion⟩
    · rintro ⟨⟨index, hpoint⟩, hregion⟩
      exact ⟨index, hpoint, hregion⟩
  have hcellsSubset : cells ⊆ pullback.selectedCells := by
    intro cell hcell
    exact (Finset.mem_filter.mp hcell).1
  have hpartition : prepared.shadow.union ∩ region =
      ⋃ cell ∈ cells,
        prepared.shadow.union ∩ wz1PaperGridCube rho cell := by
    ext point
    constructor
    · rintro ⟨hpoint, hregion⟩
      rcases Set.mem_iUnion₂.mp hregion with ⟨cell, hcell, hpointCell⟩
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpoint, hpointCell⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨cell, hcell, hpointShadow, hpointCell⟩
      exact ⟨hpointShadow, Set.mem_iUnion₂.mpr
        ⟨cell, hcell, hpointCell⟩⟩
  have hvolume : MeasureTheory.volume shading.union =
      (cells.card : ENNReal) * twoScale.coarse.balanced.cellMass := by
    rw [hunion, hpartition]
    rw [MeasureTheory.measure_biUnion_finset]
    · calc
        (∑ cell ∈ cells, MeasureTheory.volume
            (prepared.shadow.union ∩ wz1PaperGridCube rho cell)) =
            ∑ _cell ∈ cells, twoScale.coarse.balanced.cellMass := by
          apply Finset.sum_congr rfl
          intro cell hcell
          rw [prepared.shadow_union]
          exact pullback.cell_mass cell (hcellsSubset hcell)
        _ = (cells.card : ENNReal) *
            twoScale.coarse.balanced.cellMass := by
          simp [Finset.sum_const]
    · intro first _ second _ hne
      exact (wz1PaperGridCube_disjoint hne).mono
        Set.inter_subset_right Set.inter_subset_right
    · intro cell _
      exact (measurableSet_shading_union prepared.shadow).inter
        (wz1PaperGridCube_measurable cell)
  have hdeltaRho : delta ≤ rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1
  have hrho : 0 < rho := source.extremal.delta_pos.trans_le hdeltaRho
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hactive :
      ∀ cell ∈ wz1Lemma23ActiveCells shading rho
          (source.extremal.delta_pos.trans_le hdeltaRho),
        (wz1Lemma23SnappedPoint rho cell) (2 : Fin 3) ∈
          Set.Icc left (left + Real.sqrt rho) := by
    intro graphCell hgraphCell
    rw [wz1Lemma23_mem_active_iff] at hgraphCell
    rcases hgraphCell.2 with ⟨point, hpoint, hpointGraphCell⟩
    have hpointRegion : point ∈ region := by
      rcases hpoint with ⟨index, hpointCarrier⟩
      exact hpointCarrier.2
    rcases Set.mem_iUnion₂.mp hpointRegion with
      ⟨paperCell, hpaperCell, hpointPaperCell⟩
    have hsafe := (Finset.mem_filter.mp hpaperCell).2
    have hpaperBounds := hpointPaperCell
    rw [wz1PaperGridCube_eq_Ico hrho paperCell] at hpaperBounds
    have hpointCenter :
        |point (2 : Fin 3) - pureWZ2PaperCellCenterHeight rho paperCell| ≤
          rho / 2 := by
      rw [abs_le]
      constructor
      · calc
          -(rho / 2) =
              (paperCell.2.2 : ℝ) * rho -
                pureWZ2PaperCellCenterHeight rho paperCell := by
            dsimp only [pureWZ2PaperCellCenterHeight]
            ring
          _ ≤ point (2 : Fin 3) -
                pureWZ2PaperCellCenterHeight rho paperCell :=
            sub_le_sub_right hpaperBounds.2.2.2.2.1 _
      · calc
          point (2 : Fin 3) -
                pureWZ2PaperCellCenterHeight rho paperCell ≤
              ((paperCell.2.2 : ℝ) + 1) * rho -
                pureWZ2PaperCellCenterHeight rho paperCell :=
            sub_le_sub_right hpaperBounds.2.2.2.2.2.le _
          _ = rho / 2 := by
            dsimp only [pureWZ2PaperCellCenterHeight]
            ring
    have hgraphCenter :
        |point (2 : Fin 3) -
            (wz1Lemma23SnappedPoint rho graphCell) (2 : Fin 3)| ≤
          rho / 2 :=
      ((wz1_lemma23_snapped_cell_geometry rho hrho hrhoOne).2.1
        graphCell point hpointGraphCell).1 (2 : Fin 3)
    constructor
    · rw [abs_le] at hpointCenter hgraphCenter
      linarith [hsafe.1]
    · rw [abs_le] at hpointCenter hgraphCenter
      linarith [hsafe.2]
  have hvolumePos : 0 <
      (cells.card : ENNReal) * twoScale.coarse.balanced.cellMass := by
    have hcellsNonempty : cells.Nonempty := by
      simpa [cells] using hnonempty
    have hcardPos : 0 < (cells.card : ENNReal) := by
      exact_mod_cast hcellsNonempty.card_pos
    apply ENNReal.mul_pos
    · exact hcardPos.ne'
    · exact twoScale.coarse.balanced.cellMass_pos.ne'
  have hvolumeTop :
      (cells.card : ENNReal) * twoScale.coarse.balanced.cellMass ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      twoScale.coarse.balanced.cellMass_ne_top
  rcases prepared.ofSubshading left shading hsub hactive
      ((cells.card : ENNReal) * twoScale.coarse.balanced.cellMass)
      hvolumePos hvolumeTop (by rw [hvolume]) with
    ⟨window, hwindowLeft, hwindowShading, hwindowSupply⟩
  exact ⟨{
    cells := cells
    cells_eq := rfl
    cells_nonempty := hnonempty
    region := region
    region_eq := rfl
    region_measurable := hregionMeasurable
    shading := shading
    carrier_eq := fun _ => rfl
    subshading := hsub
    union_eq := hunion
    volume_eq := hvolume
    active_cell_window := hactive
    window := window
    window_left := hwindowLeft
    window_shading := hwindowShading
    window_supply := hwindowSupply
  }⟩

/-- A balanced safe window is a union of complete source `delta`-cells.
The first balanced cover supplies the containing side-`rho` cell; membership
in the selected safe region identifies that cell with the stored safe one. -/
theorem PureWZ2BalancedSafeWindowData.whole_cells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {left : ℝ}
    (data : PureWZ2BalancedSafeWindowData prepared left) :
    ∀ point, point ∈ data.shading.union →
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
        data.shading.union := by
  intro point hpoint other hother
  have hpointData := hpoint
  rw [data.union_eq] at hpointData
  have hpointPullback : point ∈ pullback.shading.union := by
    rw [← prepared.shadow_union]
    exact hpointData.1
  rcases hpointPullback with ⟨sourceIndex, hpointSource⟩
  have hotherSource : other ∈ pullback.shading.carrier sourceIndex :=
    pullback.whole_cells sourceIndex point hpointSource hother
  have hotherPrepared : other ∈ prepared.shadow.union := by
    rw [prepared.shadow_union]
    exact ⟨sourceIndex, hotherSource⟩
  rw [pullback.carrier_eq] at hpointSource
  rcases pullback.zeroExtension.carrier_support
      sourceIndex point hpointSource.1 with
    ⟨selectedIndex, _hindex, hselected⟩
  rcases twoScale.coarse.balanced.fine_cell_nested
      selectedIndex point hselected with
    ⟨coarseCell, _hcoarseCell, hnested⟩
  have hpointCoarse : point ∈ wz1PaperGridCube rho coarseCell := by
    rw [← twoScale.rhoRequested_eq]
    apply hnested
    exact (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta point) point).mpr rfl
  rcases Set.mem_iUnion₂.mp (by
      rw [data.region_eq] at hpointData
      exact hpointData.2) with
    ⟨safeCell, hsafeCell, hpointSafe⟩
  have hcoarseEq : coarseCell = safeCell :=
    ((mem_wz1PaperGridCube rho coarseCell point).mp hpointCoarse).symm.trans
      ((mem_wz1PaperGridCube rho safeCell point).mp hpointSafe)
  rw [data.union_eq]
  refine ⟨hotherPrepared, ?_⟩
  rw [data.region_eq]
  refine Set.mem_iUnion₂.mpr ⟨safeCell, hsafeCell, ?_⟩
  rw [← hcoarseEq, ← twoScale.rhoRequested_eq]
  exact hnested hother

end Kakeya.Assouad
