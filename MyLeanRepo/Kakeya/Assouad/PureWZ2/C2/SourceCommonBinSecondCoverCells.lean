import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinRichSpatialCells
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PaperCubeSliceArea

/-!
# Common-bin spatial cells in the second balanced cover

The slab-local mass `w_s` is the second sticky cover's balanced mass on
literal side-`sqrt rho` spatial cells.  It is not the mass of a parent tube
or of a shifted safe window.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Every point of the exact two-scale source pullback lies in an active
side-`sqrt rho` cell of the second balanced cover. -/
theorem PureWZ2TwoScaleCellPullbackData.sqrt_gridIndex_mem_fine_balanced_activeCells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)
    {point : Point3}
    (hpoint : point ∈ pullback.shading.union) :
    wz1PaperGridIndex twoScale.sqrtRequested.1 point ∈
      twoScale.fine.balanced.activeCells := by
  have hselectedRegion : point ∈ pullback.selectedRegion := by
    rw [pullback.union_eq] at hpoint
    exact hpoint.2
  rw [pullback.selectedRegion_eq] at hselectedRegion
  rcases Set.mem_iUnion₂.mp hselectedRegion with
    ⟨rhoCell, hrhoCell, hpointRhoCell⟩
  have hrho :
      0 < twoScale.rhoRequested.1 :=
    twoScale.coarse.coarse_extremal.delta_pos
  have hrhoCellActive :
      rhoCell ∈
        wz1PaperActiveCells twoScale.fine.refined hrho := by
    simpa only [pullback.selectedCells_eq] using hrhoCell
  rw [mem_wz1PaperActiveCells] at hrhoCellActive
  rcases hrhoCellActive.2 with
    ⟨finePoint, hfinePoint, hfinePointCell⟩
  rcases hfinePoint with ⟨fineIndex, hfineCarrier⟩
  rcases
      twoScale.fine.balanced.fine_cell_nested
        fineIndex finePoint hfineCarrier
    with
    ⟨sqrtCell, hsqrtCellActive, hnested⟩
  have hfineRhoIndex :
      wz1PaperGridIndex twoScale.rhoRequested.1 finePoint = rhoCell :=
    (mem_wz1PaperGridCube
      twoScale.rhoRequested.1 rhoCell finePoint).mp hfinePointCell
  have hpointSourceCell :
      point ∈
        wz1PaperGridCube twoScale.rhoRequested.1
          (wz1PaperGridIndex twoScale.rhoRequested.1 finePoint) := by
    rw [hfineRhoIndex, twoScale.rhoRequested_eq]
    exact hpointRhoCell
  have hpointSqrtCell :
      point ∈ wz1PaperGridCube twoScale.sqrtRequested.1 sqrtCell :=
    hnested hpointSourceCell
  have hindex :
      wz1PaperGridIndex twoScale.sqrtRequested.1 point = sqrtCell :=
    (mem_wz1PaperGridCube
      twoScale.sqrtRequested.1 sqrtCell point).mp hpointSqrtCell
  rwa [hindex]

/-- Window-level form of the second-cover active-cell bridge. -/
theorem PureWZ2SourceCarrierWindow.sqrt_gridIndex_mem_fine_balanced_activeCells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    {point : Point3}
    (hpoint : point ∈ window.shading.union) :
    wz1PaperGridIndex twoScale.sqrtRequested.1 point ∈
      twoScale.fine.balanced.activeCells := by
  apply pullback.sqrt_gridIndex_mem_fine_balanced_activeCells
  have hshadow : point ∈ prepared.shadow.union :=
    window.subshading.union_subset hpoint
  rwa [prepared.shadow_union] at hshadow

namespace PureWZ2SourceHorizontalFixedLineData

/-- Every active common-bin spatial cube is a genuine active cell of the
second balanced cover. -/
theorem commonBinActiveSpatialCells_subset_fine_balanced
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
    (bin : ℤ) :
    line.commonBinActiveSpatialCells referenceHeight height bin ⊆
      twoScale.fine.balanced.activeCells := by
  intro cell hcell
  rw [commonBinActiveSpatialCells,
    pureWZ2FixedCommonBinActiveSpatialCells,
    Finset.mem_filter] at hcell
  rcases hcell.2 with ⟨planarPoint, hplanarPoint⟩
  have hlift :=
    wz1Lemma23_mem_planarSlice_iff.mp hplanarPoint
  let point : Point3 :=
    point3 (planarPoint 0) (planarPoint 1) height
  have hpointWindow : point ∈ window.shading.union := hlift.1.1
  have hpointCell :
      point ∈ wz1PaperGridCube (Real.sqrt rho) cell := hlift.2
  have hactive :=
    window.sqrt_gridIndex_mem_fine_balanced_activeCells hpointWindow
  have hpointCell' :
      point ∈ wz1PaperGridCube twoScale.sqrtRequested.1 cell := by
    simpa only [twoScale.sqrtRequested_eq] using hpointCell
  have hindex :
      wz1PaperGridIndex twoScale.sqrtRequested.1 point = cell :=
    (mem_wz1PaperGridCube
      twoScale.sqrtRequested.1 cell point).mp hpointCell'
  rwa [hindex] at hactive

/-- Each active common-bin spatial cube carries the exact second-cover
balanced mass `w_s`. -/
theorem commonBinActiveSpatialCell_mass
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window)
    {referenceHeight height : ℝ}
    {bin : ℤ}
    {cell : ℤ × ℤ × ℤ}
    (hcell :
      cell ∈ line.commonBinActiveSpatialCells
        referenceHeight height bin) :
    volume
        (twoScale.fine.refined.union ∩
          wz1PaperGridCube (Real.sqrt rho) cell) =
      twoScale.fine.balanced.cellMass := by
  have hactive :=
    line.commonBinActiveSpatialCells_subset_fine_balanced
      referenceHeight height bin hcell
  simpa only [twoScale.sqrtRequested_eq] using
    twoScale.fine.balanced.fine_cell_mass cell hactive

end PureWZ2SourceHorizontalFixedLineData

/-- Exact mass of any finite participating family of genuine second-cover
spatial cells. -/
theorem PureWZ2Node5BalancedCoverData.commonBinParticipatingCells_volume
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily scale}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    {base : PureWZ2BalancedCoverData cover fineShading coarseShading}
    (balanced : PureWZ2Node5BalancedCoverData base)
    (cells : Finset (ℤ × ℤ × ℤ))
    (hcells : cells ⊆ balanced.activeCells) :
    volume
        (fineShading.union ∩
          ⋃ cell ∈ cells, wz1PaperGridCube scale cell) =
      (cells.card : ENNReal) * balanced.cellMass :=
  balanced.selected_cells_volume cells hcells

end Kakeya.Assouad

end
