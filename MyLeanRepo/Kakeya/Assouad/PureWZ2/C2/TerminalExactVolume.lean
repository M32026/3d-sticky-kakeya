import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleParentCount
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactGraphPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PaperCubeSliceArea

/-!
# Same-carrier volume floor for the exact terminal graph

This file keeps the full terminal counting loss visible.  The source is the
actual terminal height window, every parent is a genuine sticky parent, and
the target is the final exact auxiliary shadow used by the ready graph.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

def pureWZ2TerminalExactParentThinning : ℕ := 45 * 512 * 57 * 2

def pureWZ2TerminalExactAnchorCost : ENNReal :=
  512 * (2 * 512 * 57)

def pureWZ2TerminalExactVolumeCost
    (delta sigma inputLoss : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.sqrt delta + 2 * delta) *
    (ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi) *
    (132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
      Kakeya.realRpowENN (1 / delta) (1 - sigma)) *
    (pureWZ2FixedLineParentFiberBound delta : ENNReal) *
    pureWZ2TerminalExactParentThinning *
    pureWZ2TerminalExactAnchorCost

def pureWZ2TerminalExactWindowSupply
    (sourceVolume : ENNReal) (delta : ℝ) : ENNReal :=
  sourceVolume * ENNReal.ofReal (Real.sqrt delta) /
    ENNReal.ofReal (2 + delta + Real.sqrt delta)

theorem PureWZ2TerminalExactGraphPreparation.volume_supply_le
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    {selection : PureWZ2TerminalParentYSelection parents}
    {residue : PureWZ2TerminalParentYResidueData selection}
    {retained : PureWZ2TerminalRetainedShadingData residue}
    {sources : PureWZ2TerminalSourceFamily retained}
    {band : PureWZ2TerminalFixedBandSelection sources}
    {phase : PureWZ2TerminalHeightPhaseSelection band}
    {anchored : PureWZ2TerminalAnchoredPieceData phase}
    (prep : PureWZ2TerminalExactGraphPreparation anchored) :
    window.volumeSupply *
        terminal.sticky.balanced.cellMass ≤
      pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
        volume prep.shadow.union := by
  let sliceThickness : ENNReal :=
    ENNReal.ofReal (Real.sqrt delta + 2 * delta)
  let sliceDisk : ENNReal :=
    ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi
  let globalBound : ENNReal :=
    132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
      Kakeya.realRpowENN (1 / delta) (1 - sigma)
  let parentBound : ENNReal :=
    (pureWZ2FixedLineParentFiberBound delta : ENNReal)
  let windowSupply : ENNReal := window.volumeSupply
  have hwindowSupply : windowSupply ≤ volume window.shading.union := by
    simpa [windowSupply] using window.volume_lower
  have hball : window.shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hprepared := window.subshading.union_subset hpoint
    have hpaper : point ∈ terminalSource.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    have hnorm := norm_le_two_of_mem_paperShading hpaper
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hsliceAreaUpper :
      volume (wz1Lemma23PlanarSlice window.shading.union line.lineHeight) ≤
        (line.sliceCells.card : ENNReal) * sliceDisk := by
    have hraw := wz1_lemma23_exactSlice_area_le_two
      window.shading source.extremal.delta_pos hball line.lineHeight
    simpa [line.sliceCells_eq, sliceDisk] using hraw
  have hsliceThicknessPos : 0 < sliceThickness := by
    apply ENNReal.ofReal_pos.mpr
    have hroot : 0 < Real.sqrt delta :=
      Real.sqrt_pos.mpr source.extremal.delta_pos
    linarith [source.extremal.delta_pos]
  have hsliceThicknessTop : sliceThickness ≠ ⊤ := ENNReal.ofReal_ne_top
  have hwindowToSlice :
      volume window.shading.union ≤
        volume (wz1Lemma23PlanarSlice window.shading.union line.lineHeight) *
          sliceThickness := by
    apply (ENNReal.div_le_iff
      hsliceThicknessPos.ne' hsliceThicknessTop).mp
    simpa [sliceThickness] using line.slice_area_lower
  have hsliceCount :
      (line.sliceCells.card : ENNReal) ≤
        (line.globalBins.card : ENNReal) *
          (line.heavyCells.card : ENNReal) := by
    exact_mod_cast line.heavy_cell_count
  have hglobalCount : (line.globalBins.card : ENNReal) ≤ globalBound := by
    simpa [globalBound] using line.global_bin_count
  have hheavyCount :
      (line.heavyCells.card : ENNReal) ≤
        parentBound * (parents.parents.card : ENNReal) := by
    change (line.heavyCells.card : ENNReal) ≤
      (pureWZ2FixedLineParentFiberBound delta : ENNReal) *
        (parents.parents.card : ENNReal)
    exact_mod_cast parents.heavy_card
  have hwindowCount :
      volume window.shading.union ≤
        sliceThickness * sliceDisk * globalBound * parentBound *
          (parents.parents.card : ENNReal) := by
    calc
      volume window.shading.union ≤
          volume (wz1Lemma23PlanarSlice window.shading.union line.lineHeight) *
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
  have hparentCardNat :
      parents.parents.card ≤
        pureWZ2TerminalExactParentThinning * phase.selectedParents.card := by
    calc
      parents.parents.card ≤ 45 * selection.selected.card :=
        selection.parent_card
      _ ≤ 45 * (512 * residue.selected.card) :=
        Nat.mul_le_mul_left 45 residue.card_fraction
      _ ≤ 45 * (512 * (57 * band.selectedParents.card)) := by
        gcongr
        exact band.parent_card
      _ ≤ 45 * (512 * (57 * (2 * phase.selectedParents.card))) := by
        gcongr
        exact phase.parent_card
      _ = pureWZ2TerminalExactParentThinning *
          phase.selectedParents.card := by
        simp [pureWZ2TerminalExactParentThinning]
        ring
  have hparentCard :
      (parents.parents.card : ENNReal) ≤
        pureWZ2TerminalExactParentThinning *
          (phase.selectedParents.card : ENNReal) := by
    exact_mod_cast hparentCardNat
  have hparentVolume :
      (parents.parents.card : ENNReal) *
          terminal.sticky.balanced.cellMass ≤
        (pureWZ2TerminalExactParentThinning : ENNReal) *
          pureWZ2TerminalExactAnchorCost * volume prep.shadow.union := by
    calc
      (parents.parents.card : ENNReal) *
            terminal.sticky.balanced.cellMass ≤
          ((pureWZ2TerminalExactParentThinning : ENNReal) *
              (phase.selectedParents.card : ENNReal)) *
            terminal.sticky.balanced.cellMass := by gcongr
      _ = (pureWZ2TerminalExactParentThinning : ENNReal) *
          ((phase.selectedParents.card : ENNReal) *
            terminal.sticky.balanced.cellMass) := by ring
      _ ≤ (pureWZ2TerminalExactParentThinning : ENNReal) *
          (pureWZ2TerminalExactAnchorCost * volume prep.shadow.union) := by
        exact mul_le_mul_left'
          (by simpa [pureWZ2TerminalExactAnchorCost] using prep.volume_fraction)
          (pureWZ2TerminalExactParentThinning : ENNReal)
      _ = (pureWZ2TerminalExactParentThinning : ENNReal) *
          pureWZ2TerminalExactAnchorCost * volume prep.shadow.union := by ring
  calc
    windowSupply * terminal.sticky.balanced.cellMass ≤
        volume window.shading.union *
          terminal.sticky.balanced.cellMass := by gcongr
    _ ≤ (sliceThickness * sliceDisk * globalBound * parentBound *
          (parents.parents.card : ENNReal)) *
        terminal.sticky.balanced.cellMass := by gcongr
    _ = (sliceThickness * sliceDisk * globalBound * parentBound) *
        ((parents.parents.card : ENNReal) *
          terminal.sticky.balanced.cellMass) := by ring
    _ ≤ (sliceThickness * sliceDisk * globalBound * parentBound) *
        ((pureWZ2TerminalExactParentThinning : ENNReal) *
          pureWZ2TerminalExactAnchorCost * volume prep.shadow.union) := by
      gcongr
    _ = pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
        volume prep.shadow.union := by
      simp [pureWZ2TerminalExactVolumeCost, sliceThickness, sliceDisk,
        globalBound, parentBound]
      ring

theorem PureWZ2TerminalExactGraphPreparation.power_volume_lower
    {sigma inputLoss delta stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    {selection : PureWZ2TerminalParentYSelection parents}
    {residue : PureWZ2TerminalParentYResidueData selection}
    {retained : PureWZ2TerminalRetainedShadingData residue}
    {sources : PureWZ2TerminalSourceFamily retained}
    {band : PureWZ2TerminalFixedBandSelection sources}
    {phase : PureWZ2TerminalHeightPhaseSelection band}
    {anchored : PureWZ2TerminalAnchoredPieceData phase}
    (prep : PureWZ2TerminalExactGraphPreparation anchored)
    (hbudget :
      Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) *
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
        window.volumeSupply *
          terminal.sticky.balanced.cellMass) :
    Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) ≤
      volume prep.shadow.union := by
  let cost := pureWZ2TerminalExactVolumeCost delta sigma inputLoss
  have hcostPos : 0 < cost := by
    dsimp only [cost, pureWZ2TerminalExactVolumeCost,
      pureWZ2TerminalExactParentThinning, pureWZ2TerminalExactAnchorCost]
    have hparent : 0 < (pureWZ2FixedLineParentFiberBound delta : ENNReal) := by
      simp [pureWZ2FixedLineParentFiberBound, pureWZ2FixedLineParentYBound]
    have hthickness : 0 < ENNReal.ofReal
        (Real.sqrt delta + 2 * delta) := by
      apply ENNReal.ofReal_pos.mpr
      have hroot : 0 < Real.sqrt delta :=
        Real.sqrt_pos.mpr source.extremal.delta_pos
      linarith [source.extremal.delta_pos]
    have hdeltaENN : 0 < ENNReal.ofReal delta :=
      ENNReal.ofReal_pos.mpr source.extremal.delta_pos
    have hpi : 0 < ENNReal.ofReal Real.pi :=
      ENNReal.ofReal_pos.mpr Real.pi_pos
    have hsourcePower :
        0 < Kakeya.realRpowENN delta (-inputLoss) :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos source.extremal.delta_pos _)
    have hinv : 0 < 1 / delta := one_div_pos.mpr source.extremal.delta_pos
    have hglobalPower :
        0 < Kakeya.realRpowENN (1 / delta) (1 - sigma) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hinv _)
    positivity
  have hcostTop : cost ≠ ⊤ := by
    dsimp only [cost, pureWZ2TerminalExactVolumeCost,
      pureWZ2TerminalExactParentThinning, pureWZ2TerminalExactAnchorCost]
    repeat' apply ENNReal.mul_ne_top
    all_goals simp [Kakeya.realRpowENN]
  have hscaled :
      Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) * cost ≤
        volume prep.shadow.union * cost := by
    calc
      Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) * cost ≤
          window.volumeSupply *
            terminal.sticky.balanced.cellMass := hbudget
      _ ≤ cost * volume prep.shadow.union := by
        simpa [cost] using prep.volume_supply_le
      _ = volume prep.shadow.union * cost := mul_comm _ _
  exact (ENNReal.mul_le_mul_iff_left hcostPos.ne' hcostTop).mp hscaled

end Kakeya.Assouad

end
