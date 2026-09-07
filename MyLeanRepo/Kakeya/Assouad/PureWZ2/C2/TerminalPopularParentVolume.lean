import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularParentCount
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PaperCubeSliceArea

/-!
# Full-parent volume selected by the outer-popular terminal line

The fixed line is chosen from the outer-popular carrier.  Its heavy exact
cells meet genuine sticky parents, and the fixed-line packing bound converts
their count into the volume of the corresponding complete balanced parents.

The target below is deliberately the full sticky parent region.  It is not
asserted to lie in the outer-popular height set; that synchronization is the
remaining mathematical boundary in the terminal producer.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- Cost through Fubini, the global-bin selection, and fixed-line parent
packing, before any parent residue/band/anchor thinning. -/
def pureWZ2TerminalPopularParentVolumeCost
    (delta sigma inputLoss : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.sqrt delta + 2 * delta) *
    (ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi) *
    (132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
      Kakeya.realRpowENN (1 / delta) (1 - sigma)) *
    (pureWZ2FixedLineParentFiberBound delta : ENNReal)

/-- The volume supply of the outer-popular carrier controls the complete
sticky parent region hit by its fixed line. -/
theorem PureWZ2TerminalPopularFixedBinParentData.volumeSupply_mul_cellMass_le
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {popularPrepared : PureWZ2TerminalPopularPreparedWindowData carrier}
    {line : PureWZ2HorizontalFixedBinCore
      popularPrepared.windowed source.globalGrains.slope}
    (parents : PureWZ2TerminalPopularFixedBinParentData line) :
    popularPrepared.volumeSupply * terminal.sticky.balanced.cellMass ≤
      pureWZ2TerminalPopularParentVolumeCost delta sigma inputLoss *
        volume (terminal.sticky.refined.union ∩
          ⋃ parent ∈ parents.parents,
            wz1PaperGridCube terminal.sqrtRequested.1 parent) := by
  let popularShadow := pureWZ2PartialActiveCellShading
    carrier.shading source.extremal.delta_pos
  let sliceThickness : ENNReal :=
    ENNReal.ofReal (Real.sqrt delta + 2 * delta)
  let sliceDisk : ENNReal :=
    ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi
  let globalBound : ENNReal :=
    132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
      Kakeya.realRpowENN (1 / delta) (1 - sigma)
  let parentBound : ENNReal :=
    (pureWZ2FixedLineParentFiberBound delta : ENNReal)
  have hwindowSupply : popularPrepared.volumeSupply ≤
      volume popularShadow.union := by
    exact popularPrepared.volume_lower
  have hball : popularShadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hcarrier : point ∈ carrier.shading.union := by
      simpa [popularShadow, pureWZ2PartialActiveCellShading_union] using hpoint
    have hsource := carrier.subshading.union_subset hcarrier
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hsliceAreaUpper :
      volume (wz1Lemma23PlanarSlice popularShadow.union line.lineHeight) ≤
        (line.sliceCells.card : ENNReal) * sliceDisk := by
    have hraw := wz1_lemma23_exactSlice_area_le_two
      popularShadow source.extremal.delta_pos hball line.lineHeight
    simpa [line.sliceCells_eq, sliceDisk] using hraw
  have hsliceThicknessPos : 0 < sliceThickness := by
    apply ENNReal.ofReal_pos.mpr
    have hroot : 0 < Real.sqrt delta :=
      Real.sqrt_pos.mpr source.extremal.delta_pos
    linarith [source.extremal.delta_pos]
  have hwindowToSlice : volume popularShadow.union ≤
      volume (wz1Lemma23PlanarSlice popularShadow.union line.lineHeight) *
        sliceThickness := by
    apply (ENNReal.div_le_iff
      hsliceThicknessPos.ne' ENNReal.ofReal_ne_top).mp
    simpa [sliceThickness] using line.slice_area_lower
  have hsliceCount : (line.sliceCells.card : ENNReal) ≤
      (line.globalBins.card : ENNReal) *
        (line.heavyCells.card : ENNReal) := by
    exact_mod_cast parents.heavy_cell_count
  have hglobalCount : (line.globalBins.card : ENNReal) ≤ globalBound := by
    simpa [globalBound] using line.global_bin_count
  have hheavyCount : (line.heavyCells.card : ENNReal) ≤
      parentBound * (parents.parents.card : ENNReal) := by
    change (line.heavyCells.card : ENNReal) ≤
      (pureWZ2FixedLineParentFiberBound delta : ENNReal) *
        (parents.parents.card : ENNReal)
    exact_mod_cast parents.heavy_card
  have hwindowCount : volume popularShadow.union ≤
      sliceThickness * sliceDisk * globalBound * parentBound *
        (parents.parents.card : ENNReal) := by
    calc
      volume popularShadow.union ≤
          volume (wz1Lemma23PlanarSlice popularShadow.union line.lineHeight) *
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
      volume (terminal.sticky.refined.union ∩
          ⋃ parent ∈ parents.parents,
            wz1PaperGridCube terminal.sqrtRequested.1 parent) =
        (parents.parents.card : ENNReal) *
          terminal.sticky.balanced.cellMass :=
    terminal.sticky.balanced.selected_cells_volume
      parents.parents parents.parents_subset
  calc
    popularPrepared.volumeSupply * terminal.sticky.balanced.cellMass ≤
        volume popularShadow.union *
          terminal.sticky.balanced.cellMass := by gcongr
    _ ≤ (sliceThickness * sliceDisk * globalBound * parentBound *
          (parents.parents.card : ENNReal)) *
        terminal.sticky.balanced.cellMass := by gcongr
    _ = (sliceThickness * sliceDisk * globalBound * parentBound) *
        ((parents.parents.card : ENNReal) *
          terminal.sticky.balanced.cellMass) := by ring
    _ = pureWZ2TerminalPopularParentVolumeCost delta sigma inputLoss *
        volume (terminal.sticky.refined.union ∩
          ⋃ parent ∈ parents.parents,
            wz1PaperGridCube terminal.sqrtRequested.1 parent) := by
      rw [hparentVolume]
      simp [pureWZ2TerminalPopularParentVolumeCost, sliceThickness, sliceDisk,
        globalBound, parentBound]

end Kakeya.Assouad

end
