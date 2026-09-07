import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Node6FixedScaleOutput
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition5SpatialCover
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGridCubeVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment

/-! # Spatial cover from the Node-6 fixed-scale certificate -/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2Node6FixedScaleOutput

theorem activeCells_card_upper
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent) :
    (data.balanced.activeCells.card : ENNReal) ≤
      Kakeya.realRpowENN rho.1 (sigma - outputLoss - 3) := by
  have hvolume :
      volume data.croppedCoarseShading.union =
        (data.balanced.activeCells.card : ENNReal) *
          Kakeya.realRpowENN rho.1 3 := by
    have hrho : 0 < rho.1 := data.delta_pos.trans_le rho.2.1
    rw [data.balanced.coarse_union_eq,
      wz1PaperGridCube_volume_biUnion hrho,
      wz1PaperGridCube_volume_exact hrho]
    simp [Kakeya.realRpowENN]
  have hpowerZero : Kakeya.realRpowENN rho.1 3 ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos (data.delta_pos.trans_le rho.2.1) 3)).ne'
  have hpowerTop : Kakeya.realRpowENN rho.1 3 ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have hdivide :
      (data.balanced.activeCells.card : ENNReal) ≤
        Kakeya.realRpowENN rho.1 (sigma - outputLoss) /
          Kakeya.realRpowENN rho.1 3 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hpowerZero) (Or.inl hpowerTop)]
    rw [← hvolume]
    exact data.coarse_volume_upper
  have hquotient :
      Kakeya.realRpowENN rho.1 (sigma - outputLoss) /
          Kakeya.realRpowENN rho.1 3 =
        Kakeya.realRpowENN rho.1 (sigma - outputLoss - 3) := by
    simp only [Kakeya.realRpowENN]
    rw [ENNReal.div_eq_inv_mul]
    have hden : 0 < Real.rpow rho.1 3 :=
      Real.rpow_pos_of_pos (data.delta_pos.trans_le rho.2.1) 3
    rw [← ENNReal.ofReal_inv_of_pos hden]
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hden.le)]
    congr 1
    rw [← div_eq_inv_mul]
    exact (Real.rpow_sub (data.delta_pos.trans_le rho.2.1)
      (sigma - outputLoss) 3).symm
  rwa [hquotient] at hdivide

/-- The full final fine shading has the paper's three-dimensional fixed-scale
cover, using only spatial balance and the coarse volume upper bound. -/
theorem spatial_cover
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent) :
    CanCoverByBalls data.refined.union rho.1
      (8 * Kakeya.realRpowENN rho.1 (sigma - outputLoss - 3)) := by
  have hrho : 0 < rho.1 := data.delta_pos.trans_le rho.2.1
  have hcellCover : ∀ cell ∈ data.balanced.activeCells,
      ∃ centers : Finset Point3, centers.card ≤ 8 ∧
        ∀ point ∈ wz1PaperGridCube rho.1 cell,
          ∃ center ∈ centers, point ∈ Metric.closedBall center rho.1 := by
    intro cell _
    exact spatialCover_eightBalls hrho
      (Set.nonempty_iff_ne_empty.mpr (by
        intro hempty
        have hpositive := wz1PaperGridCube_volume_pos hrho cell
        rw [hempty] at hpositive
        simp at hpositive))
      (by
        intro first hfirst second hsecond
        exact (wz1_paper_grid_cube_diameter_lt_two_rho
          hrho hfirst hsecond).le)
  choose centers hcentersCard hcentersCover using hcellCover
  let allCenters := data.balanced.activeCells.biUnion fun cell =>
    if h : cell ∈ data.balanced.activeCells then centers cell h else ∅
  have hallCardNat : allCenters.card ≤
      8 * data.balanced.activeCells.card := by
    calc
      allCenters.card ≤ ∑ cell ∈ data.balanced.activeCells,
          (if h : cell ∈ data.balanced.activeCells then
            centers cell h else ∅).card := Finset.card_biUnion_le
      _ ≤ ∑ _cell ∈ data.balanced.activeCells, 8 := by
        apply Finset.sum_le_sum
        intro cell hcell
        simp only [hcell, dite_true]
        exact hcentersCard cell hcell
      _ = 8 * data.balanced.activeCells.card := by
        simp [Finset.sum_const, Nat.mul_comm]
  have hallCard : (allCenters.card : ENNReal) ≤
      8 * Kakeya.realRpowENN rho.1 (sigma - outputLoss - 3) := by
    calc
      (allCenters.card : ENNReal) ≤
          (8 * data.balanced.activeCells.card : ℕ) := by
        exact_mod_cast hallCardNat
      _ = (8 : ENNReal) *
          (data.balanced.activeCells.card : ENNReal) := by simp
      _ ≤ 8 * Kakeya.realRpowENN rho.1
          (sigma - outputLoss - 3) := by
        gcongr
        exact data.activeCells_card_upper
  refine ⟨allCenters, hallCard, ?_⟩
  intro point hpoint
  have hcoarse : point ∈ data.croppedCoarseShading.union := by
    rcases hpoint with ⟨source, hsource⟩
    rcases data.cover.covers source with ⟨parent, hparent⟩
    exact ⟨parent, data.balanced.point_compatibility
      source parent hparent point hsource⟩
  rw [data.balanced.coarse_union_eq] at hcoarse
  rcases Set.mem_iUnion₂.mp hcoarse with ⟨cell, hcell, hpointCell⟩
  rcases hcentersCover cell hcell point hpointCell with
    ⟨center, hcenter, hball⟩
  exact ⟨center, Finset.mem_biUnion.mpr ⟨cell, hcell, by
    simpa [hcell] using hcenter⟩, hball⟩

end PureWZ2Node6FixedScaleOutput

end Kakeya.Assouad

end
