import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalSharpGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PaperCubeSliceArea
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ExactSliceCells

/-!
# Exact source-carrier volume floor

The source window and the final residue live on the same pullback carrier.
The exact supply is the window lower bound times the first-sticky balanced
side-`rho` cell mass.  No second-sticky cell mass is substituted.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

def pureWZ2SourceHorizontalVolumeCost
    (rho delta sigma inputLoss : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.sqrt rho + 2 * rho) *
    (ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi) *
    (132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
      Kakeya.realRpowENN (1 / delta) (1 - sigma)) *
    (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) *
    23040

theorem pureWZ2SourceHorizontalVolumeCost_pos
    {rho delta sigma inputLoss : ℝ}
    (hrho : 0 < rho) (hdelta : 0 < delta) :
    0 < pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss := by
  unfold pureWZ2SourceHorizontalVolumeCost
  have hinv : 0 < 1 / delta := by positivity
  have hthickness : 0 < ENNReal.ofReal
      (Real.sqrt rho + 2 * rho) := ENNReal.ofReal_pos.mpr (by positivity)
  have hdeltaENN : 0 < ENNReal.ofReal delta := ENNReal.ofReal_pos.mpr hdelta
  have hpi : 0 < ENNReal.ofReal Real.pi :=
    ENNReal.ofReal_pos.mpr Real.pi_pos
  have hdeltaPower : 0 < Kakeya.realRpowENN delta (-inputLoss) :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)
  have hdeltaInvPower :
      0 < Kakeya.realRpowENN (1 / delta) (1 - sigma) :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hinv _)
  have hparent :
      0 < (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) := by
    simp [pureWZ2SourceFixedLineParentFiberBound,
      pureWZ2SourceFixedLineParentYBound]
  positivity

def pureWZ2SourceHorizontalWindowSupply
    (volumeValue : ENNReal) (rho : ℝ) : ENNReal :=
  volumeValue * ENNReal.ofReal (Real.sqrt rho) /
    ENNReal.ofReal (2 + rho + Real.sqrt rho)

theorem PureWZ2SourceHorizontalResiduePreparation.volume_supply_le
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    (prep : PureWZ2SourceHorizontalResiduePreparation retained)
    (hshadow : prep.shadow.union = retained.shading.union) :
    window.volumeSupply *
          twoScale.coarse.balanced.cellMass *
        twoScale.fine.balanced.cellMass ≤
      (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
        MeasureTheory.volume prep.shadow.union := by
  let sliceThickness : ENNReal :=
    ENNReal.ofReal (Real.sqrt rho + 2 * rho)
  let sliceDisk : ENNReal :=
    ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi
  let globalBound : ENNReal :=
    132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
      Kakeya.realRpowENN (1 / delta) (1 - sigma)
  let parentBound : ENNReal :=
    (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal)
  let windowSupply : ENNReal := window.volumeSupply
  have hrho : 0 < rho := line.rho_pos
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hwindowSupply :
      windowSupply ≤ MeasureTheory.volume window.shading.union := by
    simpa [windowSupply] using window.volume_lower
  have hball : window.shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hprepared : point ∈ prepared.shadow.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, window.subshading index hindex⟩
    have hpull : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    have hsource := pullback.subshading.union_subset hpull
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hsliceAreaUpper :
      MeasureTheory.volume
          (wz1Lemma23PlanarSlice window.shading.union line.lineHeight) ≤
        (line.sliceCells.card : ENNReal) * sliceDisk := by
    have hraw := wz1_lemma23_exactSlice_area_le_two
      window.shading hdelta hball line.lineHeight
    simpa [line.sliceCells_eq, sliceDisk] using hraw
  have hsliceThicknessPos : 0 < sliceThickness := by
    apply ENNReal.ofReal_pos.mpr
    positivity
  have hwindowToSlice :
      MeasureTheory.volume window.shading.union ≤
        MeasureTheory.volume
            (wz1Lemma23PlanarSlice window.shading.union line.lineHeight) *
          sliceThickness := by
    apply (ENNReal.div_le_iff
      hsliceThicknessPos.ne' ENNReal.ofReal_ne_top).mp
    simpa [sliceThickness] using line.slice_area_lower
  have hsliceCount :
      (line.sliceCells.card : ENNReal) ≤
        (line.globalBins.card : ENNReal) *
          (line.heavyCells.card : ENNReal) := by
    exact_mod_cast line.heavy_cell_count
  have hglobalCount :
      (line.globalBins.card : ENNReal) ≤ globalBound := by
    simpa [globalBound] using line.global_bin_count
  have hheavyCount :
      (line.heavyCells.card : ENNReal) ≤
        parentBound * (parents.parents.card : ENNReal) := by
    change (line.heavyCells.card : ENNReal) ≤
      (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) *
        (parents.parents.card : ENNReal)
    exact_mod_cast parents.heavy_card
  have hwindowCount :
      MeasureTheory.volume window.shading.union ≤
        sliceThickness * sliceDisk * globalBound * parentBound *
          (parents.parents.card : ENNReal) := by
    calc
      MeasureTheory.volume window.shading.union ≤
          MeasureTheory.volume
              (wz1Lemma23PlanarSlice window.shading.union line.lineHeight) *
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
            twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass ≤
        23040 *
          (MeasureTheory.volume retained.shading.union *
            MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) := by
    have hparentCardNat :
        parents.parents.card ≤ 23040 * residue.selected.card := by
      calc
        parents.parents.card ≤ 45 * selection.selected.card :=
          selection.parent_card
        _ ≤ 45 * (512 * residue.selected.card) :=
          Nat.mul_le_mul_left 45 residue.card_fraction
        _ = 23040 * residue.selected.card := by ring
    have hparentCard :
        (parents.parents.card : ENNReal) ≤
          23040 * (residue.selected.card : ENNReal) := by
      exact_mod_cast hparentCardNat
    calc
      (parents.parents.card : ENNReal) *
            twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass ≤
        (23040 * (residue.selected.card : ENNReal)) *
            twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass := by gcongr
      _ = 23040 *
          (((residue.selected.card : ENNReal) *
              twoScale.fine.balanced.cellMass) *
            twoScale.coarse.balanced.cellMass) := by ring
      _ = 23040 *
          (MeasureTheory.volume retained.shading.union *
            MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) := by
        rw [retained.volume_mul_cube]
  have hsupply :
      windowSupply * twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass ≤
        ((sliceThickness * sliceDisk * globalBound * parentBound * 23040) *
            MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
          MeasureTheory.volume retained.shading.union := by
    calc
      windowSupply * twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass ≤
          MeasureTheory.volume window.shading.union *
            twoScale.coarse.balanced.cellMass *
              twoScale.fine.balanced.cellMass := by gcongr
      _ ≤ (sliceThickness * sliceDisk * globalBound * parentBound *
              (parents.parents.card : ENNReal)) *
            twoScale.coarse.balanced.cellMass *
              twoScale.fine.balanced.cellMass := by gcongr
      _ = (sliceThickness * sliceDisk * globalBound * parentBound) *
            (((parents.parents.card : ENNReal) *
                twoScale.coarse.balanced.cellMass) *
              twoScale.fine.balanced.cellMass) := by ring
      _ ≤ (sliceThickness * sliceDisk * globalBound * parentBound) *
            (23040 *
              (MeasureTheory.volume retained.shading.union *
                MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0)))) := by
        gcongr
      _ = ((sliceThickness * sliceDisk * globalBound * parentBound * 23040) *
              MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
            MeasureTheory.volume retained.shading.union := by ring
  rw [hshadow]
  simpa [pureWZ2SourceHorizontalVolumeCost, windowSupply,
    sliceThickness, sliceDisk, globalBound, parentBound] using hsupply

theorem PureWZ2SourceHorizontalResiduePreparation.power_volume_lower
    {sigma inputLoss delta rho middleLoss outputLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    (prep : PureWZ2SourceHorizontalResiduePreparation retained)
    (hshadow : prep.shadow.union = retained.shading.union)
    (hbudget :
      Kakeya.realRpowENN prep.graphScale
            (1 + sigma / 2 + volumeLoss) *
          (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
            MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) ≤
        window.volumeSupply *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass)) :
    Kakeya.realRpowENN prep.graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      MeasureTheory.volume prep.shadow.union := by
  let cost := pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss
  have hrho : 0 < rho := line.rho_pos
  have hcostPos : 0 < cost :=
    pureWZ2SourceHorizontalVolumeCost_pos hrho source.extremal.delta_pos
  have hcostTop : cost ≠ ⊤ := by
    dsimp only [cost, pureWZ2SourceHorizontalVolumeCost]
    repeat' apply ENNReal.mul_ne_top
    all_goals simp [Kakeya.realRpowENN]
  have hscaled :
      Kakeya.realRpowENN prep.graphScale
            (1 + sigma / 2 + volumeLoss) *
          (cost * MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) ≤
        MeasureTheory.volume prep.shadow.union *
          (cost * MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) := by
    calc
      _ ≤ window.volumeSupply *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass) := hbudget
      _ ≤ (cost * MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
          MeasureTheory.volume prep.shadow.union := by
        simpa [cost, mul_assoc] using prep.volume_supply_le hshadow
      _ = MeasureTheory.volume prep.shadow.union *
          (cost * MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) := by ring
  have hcubePos : 0 < MeasureTheory.volume
      (wz1PaperGridCube rho (0, 0, 0)) := by
    rw [wz1PaperGridCube_volume_exact line.rho_pos]
    exact ENNReal.ofReal_pos.mpr (pow_pos line.rho_pos 3)
  have hfactorPos : 0 < cost * MeasureTheory.volume
      (wz1PaperGridCube rho (0, 0, 0)) := by positivity
  have hfactorTop : cost * MeasureTheory.volume
      (wz1PaperGridCube rho (0, 0, 0)) ≠ ⊤ :=
    ENNReal.mul_ne_top hcostTop
      (by rw [wz1PaperGridCube_volume_exact line.rho_pos];
          exact ENNReal.ofReal_ne_top)
  exact (ENNReal.mul_le_mul_iff_left hfactorPos.ne' hfactorTop).mp hscaled

end Kakeya.Assouad
