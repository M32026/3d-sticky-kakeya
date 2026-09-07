import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineSharpGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PaperCubeSliceArea
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ExactSliceCells

/-!
# Same-carrier volume floor for the Pure fixed-line residue

The fixed horizontal line is selected from one exact slice of the retained
`rho`-scale carrier.  Its complete `sqrt rho` parents come from the actual
second sticky balanced cover.  This file keeps every loss visible: the
height-window thickness, slice disks, global AD bins, the number of fixed-line
cells in one parent, and the final `45 * 512 = 23040` parent thinning.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- Exact finite cost between the retained height window and one residue. -/
def pureWZ2HorizontalFixedLineVolumeCost
    (rho sigma middleLoss : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.sqrt rho + 2 * rho) *
    (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi) *
    (132 * (10 * Kakeya.realRpowENN rho (-middleLoss)) *
      Kakeya.realRpowENN (1 / rho) (1 - sigma)) *
    (pureWZ2FixedLineParentFiberBound rho : ENNReal) *
    23040

/--
The two quantitative supplies used in the fixed-line count: the complete
height-window volume and the balanced mass of every active `sqrt rho` cell.
-/
def pureWZ2HorizontalFixedLineVolumeSupply
    (windowSupply : ENNReal)
    (rho sigma outputLoss : ℝ) : ENNReal :=
  windowSupply *
    Kakeya.realRpowENN rho
      (3 / 2 + sigma / 2 + 3 * outputLoss / 2)

/--
Raw fixed-line volume comparison on the final residue carrier.  In particular,
the right side is the volume of `prep.shadow.union`, not the earlier coarse or
height-window carrier.
-/
theorem PureWZ2HorizontalFixedLineResiduePreparation.volume_supply_le
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading : PureWZ2HorizontalFixedLineResidueShadingData residue}
    (prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading) :
    pureWZ2HorizontalFixedLineVolumeSupply
        windowed.volumeSupply
        twoScale.rhoRequested.1 sigma outputLoss ≤
      pureWZ2HorizontalFixedLineVolumeCost
          twoScale.rhoRequested.1 sigma middleLoss *
        MeasureTheory.volume prep.shadow.union := by
  let scale := twoScale.rhoRequested.1
  let sliceThickness : ENNReal :=
    ENNReal.ofReal (Real.sqrt scale + 2 * scale)
  let sliceDisk : ENNReal :=
    ENNReal.ofReal scale ^ 2 * ENNReal.ofReal Real.pi
  let globalBound : ENNReal :=
    132 * (10 * Kakeya.realRpowENN scale (-middleLoss)) *
      Kakeya.realRpowENN (1 / scale) (1 - sigma)
  let parentBound : ENNReal :=
    (pureWZ2FixedLineParentFiberBound scale : ENNReal)
  let windowSupply : ENNReal :=
    windowed.volumeSupply
  let cellSupply : ENNReal :=
    Kakeya.realRpowENN scale
      (3 / 2 + sigma / 2 + 3 * outputLoss / 2)
  have hscale : 0 < scale := twoScale.coarseGrains.extremal.delta_pos
  have hscaleOne : scale ≤ 1 := twoScale.rhoRequested.property.2
  have hwindowSupply :
      windowSupply ≤ MeasureTheory.volume windowed.shading.union := by
    simpa [windowSupply] using windowed.volume_lower
  have hcellSupply : cellSupply ≤ twoScale.fine.balanced.cellMass := by
    simpa [cellSupply, scale] using twoScale.second_source_floor_power
  have hball :
      windowed.shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hprepared : point ∈ prepared.shadow.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, windowed.subshading index hindex⟩
    have hfine : point ∈ twoScale.fine.refined.union := by
      rwa [prepared.shadow_union] at hprepared
    rcases hfine with ⟨index, hindex⟩
    have hsource : point ∈ twoScale.coarseGrains.shading.union :=
      ⟨twoScale.fine.selected.embedding index,
        twoScale.fine.subshading index hindex⟩
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hsliceAreaUpper :
      MeasureTheory.volume
          (wz1Lemma23PlanarSlice
            windowed.shading.union line.lineHeight) ≤
        (line.sliceCells.card : ENNReal) * sliceDisk := by
    have hraw := wz1_lemma23_exactSlice_area_le_two
      windowed.shading hscale hball line.lineHeight
    simpa [line.sliceCells_eq, sliceDisk, scale] using hraw
  have hsliceThicknessPos : 0 < sliceThickness := by
    apply ENNReal.ofReal_pos.mpr
    positivity
  have hsliceThicknessTop : sliceThickness ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hwindowToSlice :
      MeasureTheory.volume windowed.shading.union ≤
        MeasureTheory.volume
            (wz1Lemma23PlanarSlice
              windowed.shading.union line.lineHeight) *
          sliceThickness := by
    apply (ENNReal.div_le_iff
      hsliceThicknessPos.ne' hsliceThicknessTop).mp
    simpa [sliceThickness, scale] using line.slice_area_lower
  have hsliceCount :
      (line.sliceCells.card : ENNReal) ≤
        (line.globalBins.card : ENNReal) *
          (line.heavyCells.card : ENNReal) := by
    exact_mod_cast line.heavy_cell_count
  have hglobalCount :
      (line.globalBins.card : ENNReal) ≤ globalBound := by
    simpa [globalBound, scale] using line.global_bin_count
  have hheavyCount :
      (line.heavyCells.card : ENNReal) ≤
        parentBound * (parents.parents.card : ENNReal) := by
    change (line.heavyCells.card : ENNReal) ≤
      (pureWZ2FixedLineParentFiberBound scale : ENNReal) *
        (parents.parents.card : ENNReal)
    exact_mod_cast parents.heavy_card
  have hwindowCount :
      MeasureTheory.volume windowed.shading.union ≤
        sliceThickness * sliceDisk * globalBound * parentBound *
          (parents.parents.card : ENNReal) := by
    calc
      MeasureTheory.volume windowed.shading.union ≤
          MeasureTheory.volume
              (wz1Lemma23PlanarSlice
                windowed.shading.union line.lineHeight) *
            sliceThickness := hwindowToSlice
      _ ≤ ((line.sliceCells.card : ENNReal) * sliceDisk) *
            sliceThickness := by gcongr
      _ ≤ (((line.globalBins.card : ENNReal) *
              (line.heavyCells.card : ENNReal)) * sliceDisk) *
            sliceThickness := by gcongr
      _ ≤ ((globalBound * (parentBound *
              (parents.parents.card : ENNReal))) * sliceDisk) *
            sliceThickness := by gcongr
      _ = sliceThickness * sliceDisk * globalBound * parentBound *
            (parents.parents.card : ENNReal) := by ring
  have hparentVolume :
      (parents.parents.card : ENNReal) *
          twoScale.fine.balanced.cellMass ≤
        23040 * MeasureTheory.volume residueShading.shading.union := by
    have hselected := twoScale.fine.balanced.selected_cells_volume
      parents.parents parents.parents_subset
    rw [← hselected]
    simpa using residueShading.volume_fraction
  have hsupply :
      windowSupply * cellSupply ≤
        (sliceThickness * sliceDisk * globalBound * parentBound * 23040) *
          MeasureTheory.volume residueShading.shading.union := by
    calc
      windowSupply * cellSupply ≤
          MeasureTheory.volume windowed.shading.union *
            twoScale.fine.balanced.cellMass := by gcongr
      _ ≤ (sliceThickness * sliceDisk * globalBound * parentBound *
              (parents.parents.card : ENNReal)) *
            twoScale.fine.balanced.cellMass := by gcongr
      _ = (sliceThickness * sliceDisk * globalBound * parentBound) *
            ((parents.parents.card : ENNReal) *
              twoScale.fine.balanced.cellMass) := by ring
      _ ≤ (sliceThickness * sliceDisk * globalBound * parentBound) *
            (23040 * MeasureTheory.volume residueShading.shading.union) := by
        gcongr
      _ = (sliceThickness * sliceDisk * globalBound * parentBound * 23040) *
            MeasureTheory.volume residueShading.shading.union := by ring
  rw [prep.shadow_union]
  simpa [pureWZ2HorizontalFixedLineVolumeSupply,
    pureWZ2HorizontalFixedLineVolumeCost, windowSupply, cellSupply,
    sliceThickness, sliceDisk, globalBound, parentBound, scale] using hsupply

/--
Consume one explicit small-scale budget to obtain the exact volume premise of
the sharp Lemma-23 edge theorem on the final same carrier.
-/
theorem PureWZ2HorizontalFixedLineResiduePreparation.power_volume_lower
    {sigma inputLoss delta rho middleLoss outputLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading : PureWZ2HorizontalFixedLineResidueShadingData residue}
    (prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading)
    (hbudget :
      Kakeya.realRpowENN prep.graphScale
            (1 + sigma / 2 + volumeLoss) *
          pureWZ2HorizontalFixedLineVolumeCost
            twoScale.rhoRequested.1 sigma middleLoss ≤
        pureWZ2HorizontalFixedLineVolumeSupply
          windowed.volumeSupply
          twoScale.rhoRequested.1 sigma outputLoss) :
    Kakeya.realRpowENN prep.graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      MeasureTheory.volume prep.shadow.union := by
  let cost := pureWZ2HorizontalFixedLineVolumeCost
    twoScale.rhoRequested.1 sigma middleLoss
  have hcostPos : 0 < cost := by
    dsimp only [cost, pureWZ2HorizontalFixedLineVolumeCost]
    have hscale : 0 < twoScale.rhoRequested.1 :=
      twoScale.coarseGrains.extremal.delta_pos
    have hparent :
        0 < (pureWZ2FixedLineParentFiberBound
          twoScale.rhoRequested.1 : ENNReal) := by
      simp [pureWZ2FixedLineParentFiberBound,
        pureWZ2FixedLineParentYBound]
    have hthickness :
        0 < ENNReal.ofReal
          (Real.sqrt twoScale.rhoRequested.1 +
            2 * twoScale.rhoRequested.1) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    have hscaleENN :
        0 < ENNReal.ofReal twoScale.rhoRequested.1 :=
      ENNReal.ofReal_pos.mpr hscale
    have hpi : 0 < ENNReal.ofReal Real.pi :=
      ENNReal.ofReal_pos.mpr Real.pi_pos
    have hconstant :
        0 < 132 *
          (10 * Kakeya.realRpowENN
            twoScale.rhoRequested.1 (-middleLoss)) *
          Kakeya.realRpowENN
            (1 / twoScale.rhoRequested.1) (1 - sigma) := by
      have hmiddle :
          0 < Kakeya.realRpowENN
            twoScale.rhoRequested.1 (-middleLoss) :=
        ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hscale _)
      have hinv : 0 < 1 / twoScale.rhoRequested.1 := by positivity
      have hglobal :
          0 < Kakeya.realRpowENN
            (1 / twoScale.rhoRequested.1) (1 - sigma) :=
        ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hinv _)
      positivity
    positivity
  have hcostTop : cost ≠ ⊤ := by
    dsimp only [cost, pureWZ2HorizontalFixedLineVolumeCost]
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · exact ENNReal.ofReal_ne_top
          · exact ENNReal.mul_ne_top
              (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
              ENNReal.ofReal_ne_top
        · exact ENNReal.mul_ne_top
            (ENNReal.mul_ne_top (by norm_num)
              (ENNReal.mul_ne_top (by norm_num)
                (by simp [Kakeya.realRpowENN])))
            (by simp [Kakeya.realRpowENN])
      · exact ENNReal.natCast_ne_top _
    · norm_num
  have hscaled :
      Kakeya.realRpowENN prep.graphScale
            (1 + sigma / 2 + volumeLoss) * cost ≤
        MeasureTheory.volume prep.shadow.union * cost := by
    calc
      Kakeya.realRpowENN prep.graphScale
            (1 + sigma / 2 + volumeLoss) * cost ≤
          pureWZ2HorizontalFixedLineVolumeSupply
            windowed.volumeSupply
            twoScale.rhoRequested.1 sigma outputLoss := hbudget
      _ ≤ cost * MeasureTheory.volume prep.shadow.union := by
        simpa [cost] using prep.volume_supply_le
      _ = MeasureTheory.volume prep.shadow.union * cost := mul_comm _ _
  exact (ENNReal.mul_le_mul_iff_left hcostPos.ne' hcostTop).mp hscaled

end Kakeya.Assouad
