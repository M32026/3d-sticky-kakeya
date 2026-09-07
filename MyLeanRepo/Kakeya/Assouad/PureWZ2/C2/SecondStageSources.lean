import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SecondStageSourceFloor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma18SpatialSelfCenteredCover
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment

/-!
# Actual second-stage coarse sources

Every active side-`sqrt rho` cell of the second balanced cover has the same
rho-scale shaded volume.  We refine that cell by a fixed self-centered cover
so that its anchor is a genuine shaded point and the retained source lies in
the radius-`sqrt rho` ball required by the local AD certificate.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

structure PureWZ2SecondStageSourceData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent) where
  cell : ℤ × ℤ × ℤ
  cell_active : cell ∈ twoScale.fine.balanced.activeCells
  fullSource : Set Point3 :=
    twoScale.fine.refined.union ∩
      wz1PaperGridCube twoScale.sqrtRequested.1 cell
  fullSource_eq :
    fullSource = twoScale.fine.refined.union ∩
      wz1PaperGridCube twoScale.sqrtRequested.1 cell
  fullSource_measurable : MeasurableSet fullSource
  fullSource_nonempty : fullSource.Nonempty
  fullSource_volume :
    MeasureTheory.volume fullSource =
      twoScale.fine.balanced.cellMass
  centers : Finset Point3
  centers_subset : (centers : Set Point3) ⊆ fullSource
  centers_card : centers.card ≤ 512
  centers_nonempty : centers.Nonempty
  cover :
    fullSource ⊆ ⋃ center ∈ centers,
      Metric.closedBall center twoScale.sqrtRequested.1
  anchor : Point3
  anchor_mem : anchor ∈ centers
  coarseSource : Set Point3 :=
    fullSource ∩ Metric.closedBall anchor twoScale.sqrtRequested.1
  coarseSource_eq :
    coarseSource =
      fullSource ∩ Metric.closedBall anchor twoScale.sqrtRequested.1
  coarseSource_measurable : MeasurableSet coarseSource
  coarseSource_nonempty : coarseSource.Nonempty
  coarseSource_subset :
    coarseSource ⊆ twoScale.coarseGrains.shading.union ∩
      Metric.closedBall anchor twoScale.sqrtRequested.1
  heightLeft : ℝ := (cell.2.2 : ℝ) * twoScale.sqrtRequested.1
  source_height :
    ∀ point ∈ coarseSource,
      point (2 : Fin 3) ∈
        Set.Ico heightLeft (heightLeft + twoScale.sqrtRequested.1)
  height_window :
    Set.Ico heightLeft (heightLeft + twoScale.sqrtRequested.1) ⊆
      Set.Icc (-1 : ℝ) 1
  volume_average :
    MeasureTheory.volume fullSource ≤
      (centers.card : ENNReal) * MeasureTheory.volume coarseSource

theorem PureWZ2OneScaleTwoScaleStickyData.secondStageSourceAt
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent)
    (cell : ℤ × ℤ × ℤ)
    (hcell : cell ∈ twoScale.fine.balanced.activeCells) :
    ∃ data : PureWZ2SecondStageSourceData twoScale, data.cell = cell := by
  let radius := twoScale.sqrtRequested.1
  have hradius : 0 < radius := twoScale.fine.coarse_extremal.delta_pos
  let fullSource := twoScale.fine.refined.union ∩
    wz1PaperGridCube radius cell
  have hfullMeas : MeasurableSet fullSource :=
    (measurableSet_shading_union twoScale.fine.refined).inter
      (wz1PaperGridCube_measurable cell)
  have hfullVolume :
      MeasureTheory.volume fullSource = twoScale.fine.balanced.cellMass := by
    exact twoScale.fine.balanced.fine_cell_mass cell hcell
  have hfullNonempty : fullSource.Nonempty := by
    by_contra hempty
    have hzero : MeasureTheory.volume fullSource = 0 := by
      rw [Set.not_nonempty_iff_eq_empty.mp hempty]
      simp
    rw [hfullVolume] at hzero
    exact twoScale.fine.balanced.cellMass_pos.ne' hzero
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
      ⟨center, hcenter, _⟩
    exact ⟨center, hcenter⟩
  let piece (center : Point3) : Set Point3 :=
    fullSource ∩ Metric.closedBall center radius
  rcases Finset.exists_max_image centers
      (fun center => MeasureTheory.volume (piece center)) hcentersNonempty with
    ⟨anchor, hanchor, hmax⟩
  let coarseSource := piece anchor
  have hcoarseMeas : MeasurableSet coarseSource :=
    hfullMeas.inter measurableSet_closedBall
  have hvolumeCover :
      MeasureTheory.volume fullSource ≤
        ∑ center ∈ centers, MeasureTheory.volume (piece center) := by
    have hsubset : fullSource ⊆ ⋃ center ∈ centers, piece center := by
      intro point hpoint
      rcases Set.mem_iUnion₂.mp (hcover hpoint) with
        ⟨center, hcenter, hpointBall⟩
      exact Set.mem_iUnion₂.mpr
        ⟨center, hcenter, hpoint, hpointBall⟩
    exact (MeasureTheory.measure_mono hsubset).trans
      (MeasureTheory.measure_biUnion_finset_le centers piece)
  have haverage :
      MeasureTheory.volume fullSource ≤
        (centers.card : ENNReal) * MeasureTheory.volume coarseSource := by
    calc
      MeasureTheory.volume fullSource ≤
          ∑ center ∈ centers, MeasureTheory.volume (piece center) := hvolumeCover
      _ ≤ ∑ _center ∈ centers, MeasureTheory.volume (piece anchor) := by
        exact Finset.sum_le_sum fun center hcenter => hmax center hcenter
      _ = (centers.card : ENNReal) * MeasureTheory.volume coarseSource := by
        simp [Finset.sum_const, coarseSource, piece]
  have hcoarsePositive : 0 < MeasureTheory.volume coarseSource := by
    by_contra hzero
    have hzero' : MeasureTheory.volume coarseSource = 0 := le_zero_iff.mp
      (not_lt.mp hzero)
    rw [hzero'] at haverage
    simp at haverage
    have hfullPositive : 0 < MeasureTheory.volume fullSource := by
      rw [hfullVolume]
      exact twoScale.fine.balanced.cellMass_pos
    exact hfullPositive.ne' haverage
  have hcellAxis :
      wz1PaperGridCube radius cell ⊆
        Kakeya.Streamlined.axisBox 2 2 2 := by
    intro point hpoint
    have hcoarse : point ∈ twoScale.fine.croppedCoarseShading.union := by
      rw [twoScale.fine.balanced.coarse_union_eq]
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpoint⟩
    exact shading_union_subset_axisBox hcoarse
  have hsourceHeight :
      ∀ point ∈ coarseSource,
        point (2 : Fin 3) ∈
          Set.Ico ((cell.2.2 : ℝ) * radius)
            ((cell.2.2 : ℝ) * radius + radius) := by
    intro point hpoint
    have hpointCell := hpoint.1.2
    rw [wz1PaperGridCube_eq_Ico hradius cell] at hpointCell
    exact ⟨hpointCell.2.2.2.2.1, by
      have h := hpointCell.2.2.2.2.2
      linarith⟩
  have hheightWindow :
      Set.Ico ((cell.2.2 : ℝ) * radius)
          ((cell.2.2 : ℝ) * radius + radius) ⊆
        Set.Icc (-1 : ℝ) 1 := by
    intro height hheight
    let point : Point3 :=
      point3 (((cell.1 : ℝ) + 1 / 2) * radius)
        (((cell.2.1 : ℝ) + 1 / 2) * radius) height
    have hpointCell : point ∈ wz1PaperGridCube radius cell := by
      rw [wz1PaperGridCube_eq_Ico hradius cell]
      change
        (cell.1 : ℝ) * radius ≤ point 0 ∧
        point 0 < ((cell.1 : ℝ) + 1) * radius ∧
        (cell.2.1 : ℝ) * radius ≤ point 1 ∧
        point 1 < ((cell.2.1 : ℝ) + 1) * radius ∧
        (cell.2.2 : ℝ) * radius ≤ point 2 ∧
        point 2 < ((cell.2.2 : ℝ) + 1) * radius
      have hp0 : point 0 = ((cell.1 : ℝ) + 1 / 2) * radius := by
        simp [point, point3]
      have hp1 : point 1 = ((cell.2.1 : ℝ) + 1 / 2) * radius := by
        simp [point, point3]
      have hp2 : point 2 = height := by simp [point, point3]
      rw [hp0, hp1, hp2]
      exact ⟨by linarith, by linarith, by linarith, by linarith,
        hheight.1, by
          rw [show ((cell.2.2 : ℝ) + 1) * radius =
            (cell.2.2 : ℝ) * radius + radius by ring]
          exact hheight.2⟩
    have hbox := hcellAxis hpointCell
    have hp2 : point 2 = height := by simp [point, point3]
    rw [← hp2]
    simpa [Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2
  exact
    ⟨{ cell := cell
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
       coarseSource_nonempty := by
         exact nonempty_iff_ne_empty.mpr fun hempty => by
           rw [hempty] at hcoarsePositive
           simpa using hcoarsePositive
       coarseSource_subset := by
         intro point hpoint
         rcases hpoint.1.1 with ⟨index, hindex⟩
         exact ⟨⟨twoScale.fine.selected.embedding index,
           twoScale.fine.subshading index hindex⟩, hpoint.2⟩
       heightLeft := (cell.2.2 : ℝ) * radius
       source_height := hsourceHeight
       height_window := hheightWindow
       volume_average := haverage }, rfl⟩

/-- Compatibility wrapper forgetting the selected-cell provenance. -/
theorem PureWZ2OneScaleTwoScaleStickyData.secondStageSource
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent)
    (cell : ℤ × ℤ × ℤ)
    (hcell : cell ∈ twoScale.fine.balanced.activeCells) :
    Nonempty (PureWZ2SecondStageSourceData twoScale) := by
  rcases twoScale.secondStageSourceAt cell hcell with ⟨data, _⟩
  exact ⟨data⟩

/-- Absorb the fixed 512-cover loss into an externally supplied source floor. -/
theorem PureWZ2SecondStageSourceData.volume_lower
    {sigma inputLoss delta rho middleLoss outputLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    (data : PureWZ2SecondStageSourceData twoScale)
    (habsorb :
      (512 : ENNReal) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + eta) ≤
        Kakeya.realRpowENN twoScale.rhoRequested.1
          (3 / 2 + sigma / 2 + 3 * outputLoss / 2)) :
    Kakeya.realRpowENN twoScale.rhoRequested.1
        (3 / 2 + sigma / 2 + eta) ≤
      MeasureTheory.volume data.coarseSource := by
  have hcard : (data.centers.card : ENNReal) ≤ 512 := by
    exact_mod_cast data.centers_card
  have hscaled :
      (data.centers.card : ENNReal) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + eta) ≤
        MeasureTheory.volume data.fullSource := by
    calc
      (data.centers.card : ENNReal) *
            Kakeya.realRpowENN twoScale.rhoRequested.1
              (3 / 2 + sigma / 2 + eta) ≤
          (512 : ENNReal) *
            Kakeya.realRpowENN twoScale.rhoRequested.1
              (3 / 2 + sigma / 2 + eta) := by gcongr
      _ ≤ Kakeya.realRpowENN twoScale.rhoRequested.1
          (3 / 2 + sigma / 2 + 3 * outputLoss / 2) := habsorb
      _ ≤ twoScale.fine.balanced.cellMass :=
        twoScale.second_source_floor_power
      _ = MeasureTheory.volume data.fullSource := data.fullSource_volume.symm
  by_cases hcardZero : data.centers.card = 0
  · exact False.elim
      ((Finset.card_ne_zero.mpr data.centers_nonempty) hcardZero)
  have hcardENNZero : (data.centers.card : ENNReal) ≠ 0 := by
    exact_mod_cast hcardZero
  have hcardENNTop : (data.centers.card : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hmul :
      (data.centers.card : ENNReal) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + eta) ≤
        (data.centers.card : ENNReal) *
          MeasureTheory.volume data.coarseSource := by
    calc
    (data.centers.card : ENNReal) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + eta) ≤
        MeasureTheory.volume data.fullSource := hscaled
    _ ≤ (data.centers.card : ENNReal) *
          MeasureTheory.volume data.coarseSource := data.volume_average
  exact (ENNReal.mul_le_mul_iff_right hcardENNZero hcardENNTop).mp hmul

/--
Absorb the fixed self-centered-cover loss for an arbitrary requested target
mass.  This is used when the downstream graph scale differs from the sticky
base scale by an explicit absolute factor.
-/
theorem PureWZ2SecondStageSourceData.volume_lower_target
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    (data : PureWZ2SecondStageSourceData twoScale)
    (target : ENNReal)
    (habsorb :
      (512 : ENNReal) * target ≤
        Kakeya.realRpowENN twoScale.rhoRequested.1
          (3 / 2 + sigma / 2 + 3 * outputLoss / 2)) :
    target ≤ MeasureTheory.volume data.coarseSource := by
  have hcard : (data.centers.card : ENNReal) ≤ 512 := by
    exact_mod_cast data.centers_card
  have hscaled :
      (data.centers.card : ENNReal) * target ≤
        MeasureTheory.volume data.fullSource := by
    calc
      (data.centers.card : ENNReal) * target ≤
          (512 : ENNReal) * target := by gcongr
      _ ≤ Kakeya.realRpowENN twoScale.rhoRequested.1
          (3 / 2 + sigma / 2 + 3 * outputLoss / 2) := habsorb
      _ ≤ twoScale.fine.balanced.cellMass :=
        twoScale.second_source_floor_power
      _ = MeasureTheory.volume data.fullSource := data.fullSource_volume.symm
  have hcardZero : data.centers.card ≠ 0 :=
    Finset.card_ne_zero.mpr data.centers_nonempty
  have hcardENNZero : (data.centers.card : ENNReal) ≠ 0 := by
    exact_mod_cast hcardZero
  have hcardENNTop : (data.centers.card : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hmul :
      (data.centers.card : ENNReal) * target ≤
        (data.centers.card : ENNReal) *
          MeasureTheory.volume data.coarseSource :=
    hscaled.trans data.volume_average
  exact (ENNReal.mul_le_mul_iff_right hcardENNZero hcardENNTop).mp hmul

end Kakeya.Assouad
