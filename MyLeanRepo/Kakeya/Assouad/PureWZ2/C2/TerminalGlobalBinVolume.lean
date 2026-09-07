import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalGlobalBinPreparedFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalExactVolume

/-!
# Aggregate volume bound over every terminal global bin

The one-bin terminal estimate pays for the number of global AD bins before
entering the parent geometry. The paper keeps all bins. Summing the parent
estimates over the exact fibre partition removes that fixed power loss.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- Geometric cost of the all-global-bin terminal construction. The former
global-bin cardinality factor is absent. -/
def pureWZ2TerminalAllBinVolumeCost (delta : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.sqrt delta + 2 * delta) *
    (ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi) *
    (pureWZ2FixedLineParentFiberBound delta : ENNReal) *
    pureWZ2TerminalExactParentThinning *
    pureWZ2TerminalExactAnchorCost

/-- The common Fubini-slice supply is controlled by the sum of all sharp
per-bin carriers, with no loss by the number of global bins. -/
theorem PureWZ2TerminalGlobalBinParentFamily.aggregate_volume_supply_le
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    (family : PureWZ2TerminalGlobalBinParentFamily line) :
    window.volumeSupply * terminal.sticky.balanced.cellMass ≤
      pureWZ2TerminalAllBinVolumeCost delta *
        ∑ bin : {bin // bin ∈ line.globalBins},
          volume (family.preparedGraphCarrier bin).shadow.union := by
  let sliceThickness : ENNReal :=
    ENNReal.ofReal (Real.sqrt delta + 2 * delta)
  let sliceDisk : ENNReal :=
    ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi
  let parentBound : ENNReal :=
    (pureWZ2FixedLineParentFiberBound delta : ENNReal)
  let thinning : ENNReal := pureWZ2TerminalExactParentThinning
  let anchorCost : ENNReal := pureWZ2TerminalExactAnchorCost
  have hwindowSupply : window.volumeSupply ≤ volume window.shading.union :=
    window.volume_lower
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
  have hparentVolume : ∀ bin : {bin // bin ∈ line.globalBins},
      ((family.parents bin).parents.card : ENNReal) *
          terminal.sticky.balanced.cellMass ≤
        thinning * anchorCost *
          volume (family.preparedGraphCarrier bin).shadow.union := by
    intro bin
    let parents := family.parents bin
    let selection := family.selection bin
    let residue := family.residue bin
    let band := family.band bin
    let phase := family.phase bin
    let prep := family.preparedGraphCarrier bin
    have hparentCardNat : parents.parents.card ≤
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
    have hparentCard : (parents.parents.card : ENNReal) ≤
        thinning * (phase.selectedParents.card : ENNReal) := by
      dsimp only [thinning]
      exact_mod_cast hparentCardNat
    calc
      (parents.parents.card : ENNReal) *
            terminal.sticky.balanced.cellMass ≤
          (thinning * (phase.selectedParents.card : ENNReal)) *
            terminal.sticky.balanced.cellMass := by gcongr
      _ = thinning *
          ((phase.selectedParents.card : ENNReal) *
            terminal.sticky.balanced.cellMass) := by ring
      _ ≤ thinning *
          (anchorCost * volume prep.shadow.union) := by
        exact mul_le_mul_left'
          (by simpa [anchorCost, pureWZ2TerminalExactAnchorCost] using
            prep.volume_fraction) thinning
      _ = thinning * anchorCost * volume prep.shadow.union := by ring
  have hheavyMass : ∀ bin : {bin // bin ∈ line.globalBins},
      ((family.core bin).heavyCells.card : ENNReal) *
          terminal.sticky.balanced.cellMass ≤
        parentBound * thinning * anchorCost *
          volume (family.preparedGraphCarrier bin).shadow.union := by
    intro bin
    have hheavy : ((family.core bin).heavyCells.card : ENNReal) ≤
        parentBound * ((family.parents bin).parents.card : ENNReal) := by
      dsimp only [parentBound]
      exact_mod_cast (family.parents bin).heavy_card
    calc
      ((family.core bin).heavyCells.card : ENNReal) *
            terminal.sticky.balanced.cellMass ≤
          (parentBound * ((family.parents bin).parents.card : ENNReal)) *
            terminal.sticky.balanced.cellMass := by gcongr
      _ = parentBound *
          (((family.parents bin).parents.card : ENNReal) *
            terminal.sticky.balanced.cellMass) := by ring
      _ ≤ parentBound *
          (thinning * anchorCost *
            volume (family.preparedGraphCarrier bin).shadow.union) := by
        exact mul_le_mul_left' (hparentVolume bin) parentBound
      _ = parentBound * thinning * anchorCost *
          volume (family.preparedGraphCarrier bin).shadow.union := by ring
  have hsliceCard : (line.sliceCells.card : ENNReal) =
      ∑ bin : {bin // bin ∈ line.globalBins},
        ((family.core bin).heavyCells.card : ENNReal) := by
    exact_mod_cast family.slice_card
  have hsliceMass : (line.sliceCells.card : ENNReal) *
        terminal.sticky.balanced.cellMass ≤
      parentBound * thinning * anchorCost *
        ∑ bin : {bin // bin ∈ line.globalBins},
          volume (family.preparedGraphCarrier bin).shadow.union := by
    rw [hsliceCard, Finset.sum_mul]
    calc
      (∑ bin : {bin // bin ∈ line.globalBins},
          ((family.core bin).heavyCells.card : ENNReal) *
            terminal.sticky.balanced.cellMass) ≤
        ∑ bin : {bin // bin ∈ line.globalBins},
          parentBound * thinning * anchorCost *
            volume (family.preparedGraphCarrier bin).shadow.union := by
          exact Finset.sum_le_sum fun bin _ => hheavyMass bin
      _ = parentBound * thinning * anchorCost *
          ∑ bin : {bin // bin ∈ line.globalBins},
            volume (family.preparedGraphCarrier bin).shadow.union := by
        rw [Finset.mul_sum]
  calc
    window.volumeSupply * terminal.sticky.balanced.cellMass ≤
        volume window.shading.union *
          terminal.sticky.balanced.cellMass := by gcongr
    _ ≤ (volume (wz1Lemma23PlanarSlice window.shading.union line.lineHeight) *
          sliceThickness) * terminal.sticky.balanced.cellMass := by gcongr
    _ ≤ (((line.sliceCells.card : ENNReal) * sliceDisk) *
          sliceThickness) * terminal.sticky.balanced.cellMass := by gcongr
    _ = sliceThickness * sliceDisk *
          ((line.sliceCells.card : ENNReal) *
            terminal.sticky.balanced.cellMass) := by ring
    _ ≤ sliceThickness * sliceDisk *
          (parentBound * thinning * anchorCost *
            ∑ bin : {bin // bin ∈ line.globalBins},
              volume (family.preparedGraphCarrier bin).shadow.union) := by gcongr
    _ = pureWZ2TerminalAllBinVolumeCost delta *
          ∑ bin : {bin // bin ∈ line.globalBins},
            volume (family.preparedGraphCarrier bin).shadow.union := by
      simp [pureWZ2TerminalAllBinVolumeCost, sliceThickness, sliceDisk,
        parentBound, thinning, anchorCost]
      ring

end Kakeya.Assouad

end
