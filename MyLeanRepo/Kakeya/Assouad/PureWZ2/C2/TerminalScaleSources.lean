import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleParents
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma18SpatialSelfCenteredCover

/-!
# Actual coarse sources at the terminal scale

Every active side-`sqrt delta` parent has the same terminal refined volume.
We select a genuine anchor and one self-centered radius-`sqrt delta` piece,
retaining its exact source provenance and a `1/512` volume share.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalCoarseSourceData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    (terminalSource : PureWZ2TerminalPreparedSource source terminal) where
  cell : ℤ × ℤ × ℤ
  cell_active : cell ∈ terminal.sticky.balanced.activeCells
  fullSource : Set Point3 := terminalSource.shading.union ∩
    wz1PaperGridCube terminal.sqrtRequested.1 cell
  fullSource_eq : fullSource = terminalSource.shading.union ∩
    wz1PaperGridCube terminal.sqrtRequested.1 cell
  fullSource_measurable : MeasurableSet fullSource
  fullSource_nonempty : fullSource.Nonempty
  fullSource_volume : volume fullSource = terminal.sticky.balanced.cellMass
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
    terminalSource.shading.union ∩
      Metric.closedBall anchor terminal.sqrtRequested.1
  heightLeft : ℝ := (cell.2.2 : ℝ) * terminal.sqrtRequested.1
  heightLeft_eq : heightLeft =
    (cell.2.2 : ℝ) * terminal.sqrtRequested.1
  source_height : ∀ point ∈ coarseSource,
    point (2 : Fin 3) ∈ Set.Ico heightLeft
      (heightLeft + terminal.sqrtRequested.1)
  height_window : Set.Ico heightLeft
      (heightLeft + terminal.sqrtRequested.1) ⊆ Set.Icc (-1 : ℝ) 1
  volume_average : volume fullSource ≤
    (centers.card : ENNReal) * volume coarseSource

theorem PureWZ2TerminalPreparedSource.coarseSourceAt
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    (terminalSource : PureWZ2TerminalPreparedSource source terminal)
    (cell : ℤ × ℤ × ℤ)
    (hcell : cell ∈ terminal.sticky.balanced.activeCells) :
    ∃ data : PureWZ2TerminalCoarseSourceData terminalSource, data.cell = cell := by
  let radius := terminal.sqrtRequested.1
  have hradius : 0 < radius := terminal.sticky.coarse_extremal.delta_pos
  let fullSource := terminalSource.shading.union ∩ wz1PaperGridCube radius cell
  have hfullMeas : MeasurableSet fullSource :=
    (measurableSet_shading_union terminalSource.shading).inter
      (wz1PaperGridCube_measurable cell)
  have hfullVolume : volume fullSource = terminal.sticky.balanced.cellMass := by
    dsimp only [fullSource]
    rw [terminalSource.shading_eq]
    exact terminal.sticky.balanced.fine_cell_mass cell hcell
  have hfullNonempty : fullSource.Nonempty := by
    by_contra hempty
    have hzero : volume fullSource = 0 := by
      rw [Set.not_nonempty_iff_eq_empty.mp hempty]
      simp
    rw [hfullVolume] at hzero
    exact terminal.sticky.balanced.cellMass_pos.ne' hzero
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
    rcases Set.mem_iUnion₂.mp (hcover hpoint) with ⟨center, hcenter, _⟩
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
    have hzero' : volume coarseSource = 0 := le_zero_iff.mp (not_lt.mp hzero)
    rw [hzero'] at haverage
    simp at haverage
    have hfullPositive : 0 < volume fullSource := by
      rw [hfullVolume]
      exact terminal.sticky.balanced.cellMass_pos
    exact hfullPositive.ne' haverage
  have hcellAxis : wz1PaperGridCube radius cell ⊆
      Kakeya.Streamlined.axisBox 2 2 2 := by
    intro point hpoint
    have hcoarse : point ∈ terminal.sticky.croppedCoarseShading.union := by
      rw [terminal.sticky.balanced.coarse_union_eq]
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpoint⟩
    exact shading_union_subset_axisBox hcoarse
  have hsourceHeight : ∀ point ∈ coarseSource,
      point (2 : Fin 3) ∈ Set.Ico ((cell.2.2 : ℝ) * radius)
        ((cell.2.2 : ℝ) * radius + radius) := by
    intro point hpoint
    have hpointCell := hpoint.1.2
    rw [wz1PaperGridCube_eq_Ico hradius cell] at hpointCell
    exact ⟨hpointCell.2.2.2.2.1, by
      have h := hpointCell.2.2.2.2.2
      linarith⟩
  have hheightWindow : Set.Ico ((cell.2.2 : ℝ) * radius)
      ((cell.2.2 : ℝ) * radius + radius) ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro height hheight
    let point : Point3 := point3 (((cell.1 : ℝ) + 1 / 2) * radius)
      (((cell.2.1 : ℝ) + 1 / 2) * radius) height
    have hp0 : point 0 = ((cell.1 : ℝ) + 1 / 2) * radius := by
      simp [point, point3]
    have hp1 : point 1 = ((cell.2.1 : ℝ) + 1 / 2) * radius := by
      simp [point, point3]
    have hp2 : point 2 = height := by
      simp [point, point3]
    have hpointCell : point ∈ wz1PaperGridCube radius cell := by
      rw [wz1PaperGridCube_eq_Ico hradius cell]
      change
        (cell.1 : ℝ) * radius ≤ point 0 ∧
        point 0 < ((cell.1 : ℝ) + 1) * radius ∧
        (cell.2.1 : ℝ) * radius ≤ point 1 ∧
        point 1 < ((cell.2.1 : ℝ) + 1) * radius ∧
        (cell.2.2 : ℝ) * radius ≤ point 2 ∧
        point 2 < ((cell.2.2 : ℝ) + 1) * radius
      rw [hp0, hp1, hp2]
      exact ⟨by linarith, by linarith, by linarith, by linarith,
        hheight.1, by
          rw [show ((cell.2.2 : ℝ) + 1) * radius =
            (cell.2.2 : ℝ) * radius + radius by ring]
          exact hheight.2⟩
    have hbox := hcellAxis hpointCell
    rw [← hp2]
    simpa [Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2
  exact ⟨{
    cell := cell
    cell_active := hcell
    fullSource := fullSource
    fullSource_eq := rfl
    fullSource_measurable := hfullMeas
    fullSource_nonempty := hfullNonempty
    fullSource_volume := hfullVolume
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
    heightLeft := (cell.2.2 : ℝ) * radius
    heightLeft_eq := rfl
    source_height := hsourceHeight
    height_window := hheightWindow
    volume_average := haverage
  }, rfl⟩

theorem PureWZ2TerminalCoarseSourceData.volume_lower
    {sigma inputLoss delta stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (data : PureWZ2TerminalCoarseSourceData terminalSource)
    (habsorb : (512 : ENNReal) *
        Kakeya.realRpowENN delta (3 / 2 + sigma / 2 + eta) ≤
      Kakeya.realRpowENN delta
        (3 / 2 + sigma / 2 + 3 * stickyLoss / 2)) :
    Kakeya.realRpowENN delta (3 / 2 + sigma / 2 + eta) ≤
      volume data.coarseSource := by
  have hcard : (data.centers.card : ENNReal) ≤ 512 := by
    exact_mod_cast data.centers_card
  have hscaled : (data.centers.card : ENNReal) *
        Kakeya.realRpowENN delta (3 / 2 + sigma / 2 + eta) ≤
      volume data.fullSource := by
    calc
      _ ≤ (512 : ENNReal) *
          Kakeya.realRpowENN delta (3 / 2 + sigma / 2 + eta) := by gcongr
      _ ≤ Kakeya.realRpowENN delta
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) := habsorb
      _ ≤ terminal.sticky.balanced.cellMass := terminal.source_floor_power
      _ = volume data.fullSource := data.fullSource_volume.symm
  have hcardZero : (data.centers.card : ENNReal) ≠ 0 := by
    exact_mod_cast data.centers_nonempty.card_ne_zero
  have hcardTop : (data.centers.card : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  apply (ENNReal.mul_le_mul_iff_right hcardZero hcardTop).mp
  exact hscaled.trans data.volume_average

end Kakeya.Assouad
