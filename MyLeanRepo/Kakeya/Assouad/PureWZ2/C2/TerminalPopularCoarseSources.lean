import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularRestrictedParentSelection
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma18SpatialSelfCenteredCover

/-!
# Popular-restricted terminal coarse sources

For every post-line selected official parent, the source is the actual
outer-popular retained carrier inside that parent cube.  The pre-line dyadic
weight floor makes this source positive.  A self-centered radius-`sqrt delta`
cover then supplies a positive anchored piece with the standard factor 512.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalPopularCoarseSourceData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    (restricted : PureWZ2TerminalPopularParentRestrictionData weightClass) where
  cell : ℤ × ℤ × ℤ
  cell_selected : cell ∈ weightClass.selectedParents
  fullSource : Set Point3 := restricted.shading.union ∩
    wz1PaperGridCube terminal.sqrtRequested.1 cell
  fullSource_eq : fullSource = restricted.shading.union ∩
    wz1PaperGridCube terminal.sqrtRequested.1 cell
  fullSource_eq_popular : fullSource = carrier.shading.union ∩
    wz1PaperGridCube terminal.sqrtRequested.1 cell
  fullSource_measurable : MeasurableSet fullSource
  fullSource_nonempty : fullSource.Nonempty
  fullSource_volume : volume fullSource =
    pureWZ2TerminalPopularParentWeight carrier cell
  weightFloor_le_fullSource : weightClass.weightFloor ≤ volume fullSource
  centers : Finset Point3
  centers_subset : (centers : Set Point3) ⊆ fullSource
  centers_card : centers.card ≤ 512
  centers_nonempty : centers.Nonempty
  cover : fullSource ⊆ ⋃ center ∈ centers,
    Metric.closedBall center terminal.sqrtRequested.1
  anchor : Point3
  anchor_mem : anchor ∈ centers
  coarseSource : Set Point3 :=
    fullSource ∩ Metric.closedBall anchor terminal.sqrtRequested.1
  coarseSource_eq : coarseSource =
    fullSource ∩ Metric.closedBall anchor terminal.sqrtRequested.1
  coarseSource_measurable : MeasurableSet coarseSource
  coarseSource_nonempty : coarseSource.Nonempty
  coarseSource_subset : coarseSource ⊆
    restricted.shading.union ∩
      Metric.closedBall anchor terminal.sqrtRequested.1
  source_height : ∀ point ∈ coarseSource,
    point (2 : Fin 3) ∈ Set.Ico
      ((cell.2.2 : ℝ) * terminal.sqrtRequested.1)
      (((cell.2.2 : ℝ) + 1) * terminal.sqrtRequested.1)
  volume_average : volume fullSource ≤
    (centers.card : ENNReal) * volume coarseSource
  weightFloor_le_coarseSource : weightClass.weightFloor ≤
    512 * volume coarseSource

theorem PureWZ2TerminalPopularParentRestrictionData.coarseSourceAt
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    (restricted : PureWZ2TerminalPopularParentRestrictionData weightClass)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ weightClass.selectedParents) :
    ∃ data : PureWZ2TerminalPopularCoarseSourceData restricted,
      data.cell = cell := by
  let radius := terminal.sqrtRequested.1
  have hradius : 0 < radius := terminal.sticky.coarse_extremal.delta_pos
  let fullSource := restricted.shading.union ∩
    wz1PaperGridCube radius cell
  have hcubeRegion : wz1PaperGridCube radius cell ⊆
      weightClass.selectedRegion := by
    intro point hpoint
    rw [weightClass.selectedRegion_eq]
    exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpoint⟩
  have hfullPopular : fullSource = carrier.shading.union ∩
      wz1PaperGridCube radius cell := by
    dsimp only [fullSource]
    rw [restricted.union_eq]
    ext point
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨hcarrier, _hregion⟩, hparent⟩
      exact ⟨hcarrier, hparent⟩
    · rintro ⟨hcarrier, hparent⟩
      exact ⟨⟨hcarrier, hcubeRegion hparent⟩, hparent⟩
  have hfullMeas : MeasurableSet fullSource :=
    restricted.shading.union_measurable.inter
      (wz1PaperGridCube_measurable cell)
  have hfullVolume : volume fullSource =
      pureWZ2TerminalPopularParentWeight carrier cell := by
    rw [hfullPopular]
    rfl
  have hfloor : weightClass.weightFloor ≤ volume fullSource := by
    rw [hfullVolume]
    exact (weightClass.weight_band cell hcell).1
  have hfullPositive : 0 < volume fullSource :=
    weightClass.weightFloor_pos.trans_le hfloor
  have hfullNonempty : fullSource.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty] at hfullPositive
    simpa using hfullPositive
  let first := Classical.choose hfullNonempty
  have hfirst : first ∈ fullSource := Classical.choose_spec hfullNonempty
  have hfullBall : fullSource ⊆ Metric.closedBall first (2 * radius) := by
    intro point hpoint
    rw [Metric.mem_closedBall]
    exact le_of_lt
      (wz1_paper_grid_cube_diameter_lt_two_rho hradius hpoint.2 hfirst.2)
  rcases point3_subset_self_centered_sqrt_cover hradius hfullBall with
    ⟨centers, hcentersSubset, hcentersCard, hcover⟩
  have hcentersNonempty : centers.Nonempty := by
    rcases hfullNonempty with ⟨point, hpoint⟩
    rcases Set.mem_iUnion₂.mp (hcover hpoint) with
      ⟨center, hcenter, _hpointBall⟩
    exact ⟨center, hcenter⟩
  let piece (center : Point3) : Set Point3 :=
    fullSource ∩ Metric.closedBall center radius
  rcases Finset.exists_max_image centers (fun center => volume (piece center))
      hcentersNonempty with ⟨anchor, hanchor, hmax⟩
  let coarseSource := piece anchor
  have hcoarseMeas : MeasurableSet coarseSource :=
    hfullMeas.inter measurableSet_closedBall
  have hvolumeCover : volume fullSource ≤
      ∑ center ∈ centers, volume (piece center) := by
    have hsubset : fullSource ⊆ ⋃ center ∈ centers, piece center := by
      intro point hpoint
      rcases Set.mem_iUnion₂.mp (hcover hpoint) with
        ⟨center, hcenter, hpointBall⟩
      exact Set.mem_iUnion₂.mpr
        ⟨center, hcenter, hpoint, hpointBall⟩
    exact (measure_mono hsubset).trans
      (MeasureTheory.measure_biUnion_finset_le centers piece)
  have haverage : volume fullSource ≤
      (centers.card : ENNReal) * volume coarseSource := by
    calc
      volume fullSource ≤ ∑ center ∈ centers, volume (piece center) :=
        hvolumeCover
      _ ≤ ∑ _center ∈ centers, volume (piece anchor) := by
        exact Finset.sum_le_sum fun center hcenter => hmax center hcenter
      _ = (centers.card : ENNReal) * volume coarseSource := by
        simp [Finset.sum_const, coarseSource, piece]
  have hcoarsePositive : 0 < volume coarseSource := by
    by_contra hzero
    have hzero' : volume coarseSource = 0 :=
      le_zero_iff.mp (not_lt.mp hzero)
    rw [hzero'] at haverage
    simp at haverage
    exact hfullPositive.ne' haverage
  have hsourceHeight : ∀ point ∈ coarseSource,
      point (2 : Fin 3) ∈ Set.Ico
        ((cell.2.2 : ℝ) * radius)
        (((cell.2.2 : ℝ) + 1) * radius) := by
    intro point hpoint
    have hpointCell := hpoint.1.2
    rw [wz1PaperGridCube_eq_Ico hradius cell] at hpointCell
    exact ⟨hpointCell.2.2.2.2.1, hpointCell.2.2.2.2.2⟩
  have hfloorCoarse : weightClass.weightFloor ≤
      512 * volume coarseSource := by
    calc
      weightClass.weightFloor ≤ volume fullSource := hfloor
      _ ≤ (centers.card : ENNReal) * volume coarseSource := haverage
      _ ≤ 512 * volume coarseSource := by
        gcongr
        exact_mod_cast hcentersCard
  exact ⟨{
    cell := cell
    cell_selected := hcell
    fullSource := fullSource
    fullSource_eq := rfl
    fullSource_eq_popular := hfullPopular
    fullSource_measurable := hfullMeas
    fullSource_nonempty := hfullNonempty
    fullSource_volume := hfullVolume
    weightFloor_le_fullSource := hfloor
    centers := centers
    centers_subset := hcentersSubset
    centers_card := hcentersCard
    centers_nonempty := hcentersNonempty
    cover := hcover
    anchor := anchor
    anchor_mem := hanchor
    coarseSource := coarseSource
    coarseSource_eq := rfl
    coarseSource_measurable := hcoarseMeas
    coarseSource_nonempty := nonempty_iff_ne_empty.mpr fun hempty => by
      rw [hempty] at hcoarsePositive
      simpa using hcoarsePositive
    coarseSource_subset := by
      intro point hpoint
      exact ⟨hpoint.1.1, hpoint.2⟩
    source_height := hsourceHeight
    volume_average := haverage
    weightFloor_le_coarseSource := hfloorCoarse
  }, rfl⟩

structure PureWZ2TerminalPopularCoarseSourceFamily
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line}
    (selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents) where
  sourceFor : ∀ parent, parent ∈ selection.selected →
    PureWZ2TerminalPopularCoarseSourceData restricted
  sourceFor_cell : ∀ parent (hparent : parent ∈ selection.selected),
    (sourceFor parent hparent).cell = parent
  anchor_mem_restricted : ∀ parent (hparent : parent ∈ selection.selected),
    (sourceFor parent hparent).anchor ∈ restricted.shading.union
  coarse_source_subset : ∀ parent (hparent : parent ∈ selection.selected),
    (sourceFor parent hparent).coarseSource ⊆
      restricted.shading.union ∩ Metric.closedBall
        (sourceFor parent hparent).anchor terminal.sqrtRequested.1

theorem PureWZ2TerminalPopularRestrictedParentSelectionData.coarseSources
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line}
    (selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents) :
    Nonempty (PureWZ2TerminalPopularCoarseSourceFamily selection) := by
  have hsourceExists : ∀ parent (hparent : parent ∈ selection.selected),
      ∃ data : PureWZ2TerminalPopularCoarseSourceData restricted,
        data.cell = parent := by
    intro parent hparent
    exact restricted.coarseSourceAt parent
      (selection.selected_subset_weightClass hparent)
  let sourceFor : ∀ parent, parent ∈ selection.selected →
      PureWZ2TerminalPopularCoarseSourceData restricted :=
    fun parent hparent => Classical.choose (hsourceExists parent hparent)
  have hsourceCell : ∀ parent (hparent : parent ∈ selection.selected),
      (sourceFor parent hparent).cell = parent := by
    intro parent hparent
    exact Classical.choose_spec (hsourceExists parent hparent)
  exact ⟨{
    sourceFor := sourceFor
    sourceFor_cell := hsourceCell
    anchor_mem_restricted := by
      intro parent hparent
      let data := sourceFor parent hparent
      have hfull : data.anchor ∈ data.fullSource :=
        data.centers_subset data.anchor_mem
      rw [data.fullSource_eq] at hfull
      exact hfull.1
    coarse_source_subset := by
      intro parent hparent point hpoint
      exact (sourceFor parent hparent).coarseSource_subset hpoint
  }⟩

end Kakeya.Assouad

end
