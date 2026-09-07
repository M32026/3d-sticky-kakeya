import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularGeometricInput
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularParentVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalExactVolume

/-!
# Same-carrier volume ledger for the terminal graph

The outer-popular fixed line bounds its retained volume supply by the number
of visible official parents.  Weighted y/residue selection and the localized
piece sum keep the same positive finite parent-weight floor on both sides.
Complete terminal parents enter only as heterogeneous normal/heavy-fibre
witnesses and do not replace the measured outer-popular graph carrier.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

def pureWZ2TerminalPopularGraphVolumeCost
    (delta sigma inputLoss : ℝ) : ENNReal :=
  pureWZ2TerminalPopularParentVolumeCost delta sigma inputLoss *
    (45 * 512) * 2 * 114 * pureWZ2TerminalPopularLocalizedPieceCost

def pureWZ2TerminalPopularPrelocalizedCountCost
    (delta sigma inputLoss : ℝ) : ENNReal :=
  pureWZ2TerminalPopularParentVolumeCost delta sigma inputLoss *
    (45 * 512) * 2 * 114

theorem pureWZ2_terminalPopular_prelocalizedCountCost_le_exactVolumeCost
    (delta sigma inputLoss : ℝ) :
    pureWZ2TerminalPopularPrelocalizedCountCost delta sigma inputLoss ≤
      pureWZ2TerminalExactVolumeCost delta sigma inputLoss := by
  let base :=
    ENNReal.ofReal (Real.sqrt delta + 2 * delta) *
      (ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi) *
      (132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
        Kakeya.realRpowENN (1 / delta) (1 - sigma)) *
      (pureWZ2FixedLineParentFiberBound delta : ENNReal)
  have hleft :
      pureWZ2TerminalPopularPrelocalizedCountCost delta sigma inputLoss =
        base * ((45 * 512 : ENNReal) * 2 * 114) := by
    simp [pureWZ2TerminalPopularPrelocalizedCountCost,
      pureWZ2TerminalPopularParentVolumeCost, base]
    ring
  have hright :
      pureWZ2TerminalExactVolumeCost delta sigma inputLoss =
        base * ((45 * 512 * 57 * 2 : ENNReal) *
          (512 * (2 * 512 * 57))) := by
    simp [pureWZ2TerminalExactVolumeCost,
      pureWZ2TerminalExactParentThinning,
      pureWZ2TerminalExactAnchorCost, base]
    ring
  rw [hleft, hright]
  apply mul_le_mul_left'
  norm_num

theorem pureWZ2_terminalPopular_prelocalizedCountCost_mul_localizedPieceCost
    (delta sigma inputLoss : ℝ) :
    pureWZ2TerminalPopularPrelocalizedCountCost delta sigma inputLoss *
        pureWZ2TerminalPopularLocalizedPieceCost =
      2 * pureWZ2TerminalExactVolumeCost delta sigma inputLoss := by
  simp [pureWZ2TerminalPopularPrelocalizedCountCost,
    pureWZ2TerminalPopularParentVolumeCost,
    pureWZ2TerminalPopularLocalizedPieceCost,
    pureWZ2TerminalExactVolumeCost,
    pureWZ2TerminalExactParentThinning,
    pureWZ2TerminalExactAnchorCost]
  ring

/-- Before the anchored-piece volume loss is paid, the fixed-line and
weighted-residue selections control the number of final localized parents. -/
theorem PureWZ2TerminalPopularLocalizedPieceData.volume_supply_mul_floor_le_selected_card
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
    {selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents}
    {selectedCarrier :
      PureWZ2TerminalPopularSelectedParentCarrierData selection}
    {sources : PureWZ2TerminalPopularCoarseSourceFamily selection}
    (localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources) :
    restrictedPrepared.volumeSupply * weightClass.weightFloor ≤
      pureWZ2TerminalPopularPrelocalizedCountCost delta sigma inputLoss *
        ((localized.selectedParents.card : ENNReal) *
          weightClass.weightFloor) := by
  let sliceThickness : ENNReal :=
    ENNReal.ofReal (Real.sqrt delta + 2 * delta)
  let sliceDisk : ENNReal :=
    ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi
  let globalBound : ENNReal :=
    132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
      Kakeya.realRpowENN (1 / delta) (1 - sigma)
  let parentBound : ENNReal :=
    (pureWZ2FixedLineParentFiberBound delta : ENNReal)
  have hwindowSupply : restrictedPrepared.volumeSupply ≤
      volume (pureWZ2PartialActiveCellShading restricted.shading
        source.extremal.delta_pos).union := by
    rw [← restrictedPrepared.volume_eq]
  have hball : (pureWZ2PartialActiveCellShading restricted.shading
      source.extremal.delta_pos).union ⊆
        Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    rw [pureWZ2PartialActiveCellShading_union] at hpoint
    have hsource := restricted.subshading_source.union_subset hpoint
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hsliceAreaUpper : volume (wz1Lemma23PlanarSlice
      (pureWZ2PartialActiveCellShading restricted.shading
        source.extremal.delta_pos).union line.lineHeight) ≤
        (line.sliceCells.card : ENNReal) * sliceDisk := by
    have hraw := wz1_lemma23_exactSlice_area_le_two
      (pureWZ2PartialActiveCellShading restricted.shading
        source.extremal.delta_pos) source.extremal.delta_pos hball
      line.lineHeight
    simpa [line.sliceCells_eq, sliceDisk] using hraw
  have hsliceThicknessPos : 0 < sliceThickness := by
    apply ENNReal.ofReal_pos.mpr
    have hroot : 0 < Real.sqrt delta :=
      Real.sqrt_pos.mpr source.extremal.delta_pos
    linarith [source.extremal.delta_pos]
  have hwindowToSlice : volume (pureWZ2PartialActiveCellShading
      restricted.shading source.extremal.delta_pos).union ≤
      volume (wz1Lemma23PlanarSlice
        (pureWZ2PartialActiveCellShading restricted.shading
          source.extremal.delta_pos).union line.lineHeight) *
        sliceThickness := by
    apply (ENNReal.div_le_iff hsliceThicknessPos.ne' ENNReal.ofReal_ne_top).mp
    simpa [sliceThickness] using line.slice_area_lower
  have hsliceCount : (line.sliceCells.card : ENNReal) ≤
      (line.globalBins.card : ENNReal) * (line.heavyCells.card : ENNReal) := by
    exact_mod_cast parents.heavy_cell_count
  have hglobalCount : (line.globalBins.card : ENNReal) ≤ globalBound := by
    simpa [globalBound] using line.global_bin_count
  have hparentFiber : ∀ parent,
      (line.heavyCells.filter fun cell => parents.parentCell cell = parent).card ≤
        pureWZ2FixedLineParentFiberBound delta := by
    intro parent
    exact pureWZ2_fixedLine_parent_fiber_card line
      terminal.sqrtRequested.1 terminal.sticky.coarse_extremal.delta_pos
      terminal.sqrtRequested_eq parents.parentCell
      parents.representative_mem_parent parent
  have hheavyCountNat : line.heavyCells.card ≤
      pureWZ2FixedLineParentFiberBound delta * parents.parents.card := by
    rw [parents.parents_eq]
    exact Finset.card_le_mul_card_image line.heavyCells
      (pureWZ2FixedLineParentFiberBound delta)
      (fun parent _ => hparentFiber parent)
  have hheavyCount : (line.heavyCells.card : ENNReal) ≤
      parentBound * (parents.parents.card : ENNReal) := by
    dsimp only [parentBound]
    exact_mod_cast hheavyCountNat
  have hwindowCount : restrictedPrepared.volumeSupply ≤
      sliceThickness * sliceDisk * globalBound * parentBound *
        (parents.parents.card : ENNReal) := by
    calc
      restrictedPrepared.volumeSupply ≤ volume
          (pureWZ2PartialActiveCellShading restricted.shading
            source.extremal.delta_pos).union := hwindowSupply
      _ ≤ volume (wz1Lemma23PlanarSlice
          (pureWZ2PartialActiveCellShading restricted.shading
            source.extremal.delta_pos).union line.lineHeight) *
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
  have hparentsFloor :
      (parents.parents.card : ENNReal) * weightClass.weightFloor ≤
        (45 * 512 : ENNReal) * 2 *
          ((selection.selected.card : ENNReal) * weightClass.weightFloor) := by
    calc
      (parents.parents.card : ENNReal) * weightClass.weightFloor =
          ∑ _parent ∈ parents.parents, weightClass.weightFloor := by
        simp [Finset.sum_const]
      _ ≤ ∑ parent ∈ parents.parents,
          pureWZ2TerminalPopularParentWeight carrier parent := by
        exact Finset.sum_le_sum fun parent hparent =>
          (weightClass.weight_band parent
            (parents.parents_subset_selected hparent)).1
      _ ≤ (45 * 512 : ENNReal) *
          ∑ parent ∈ selection.selected,
            pureWZ2TerminalPopularParentWeight carrier parent :=
        selection.visible_to_selected_weight
      _ ≤ (45 * 512 : ENNReal) *
          (2 * weightClass.weightFloor *
            (selection.selected.card : ENNReal)) := by
        gcongr
        calc
          (∑ parent ∈ selection.selected,
              pureWZ2TerminalPopularParentWeight carrier parent) ≤
              ∑ _parent ∈ selection.selected,
                2 * weightClass.weightFloor := by
            exact Finset.sum_le_sum fun parent hparent =>
              (weightClass.weight_band parent
                (selection.selected_subset_weightClass hparent)).2
          _ = 2 * weightClass.weightFloor *
              (selection.selected.card : ENNReal) := by
            simp [Finset.sum_const]
            ring
      _ = (45 * 512 : ENNReal) * 2 *
          ((selection.selected.card : ENNReal) * weightClass.weightFloor) := by
        ring
  have hselectedCard : (selection.selected.card : ENNReal) ≤
      114 * (localized.selectedParents.card : ENNReal) := by
    exact_mod_cast localized.parent_card
  calc
    restrictedPrepared.volumeSupply * weightClass.weightFloor ≤
        (sliceThickness * sliceDisk * globalBound * parentBound *
          (parents.parents.card : ENNReal)) *
            weightClass.weightFloor := by gcongr
    _ = (sliceThickness * sliceDisk * globalBound * parentBound) *
        ((parents.parents.card : ENNReal) * weightClass.weightFloor) := by ring
    _ ≤ (sliceThickness * sliceDisk * globalBound * parentBound) *
        ((45 * 512 : ENNReal) * 2 *
          ((selection.selected.card : ENNReal) *
            weightClass.weightFloor)) := by gcongr
    _ ≤ (sliceThickness * sliceDisk * globalBound * parentBound) *
        ((45 * 512 : ENNReal) * 2 *
          ((114 * (localized.selectedParents.card : ENNReal)) *
            weightClass.weightFloor)) := by gcongr
    _ = pureWZ2TerminalPopularPrelocalizedCountCost delta sigma inputLoss *
        ((localized.selectedParents.card : ENNReal) *
          weightClass.weightFloor) := by
      simp [pureWZ2TerminalPopularPrelocalizedCountCost,
        pureWZ2TerminalPopularParentVolumeCost, sliceThickness, sliceDisk,
        globalBound, parentBound]
      ring

theorem PureWZ2TerminalPopularGraphPreparation.volume_supply_mul_floor_le
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
    {selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents}
    {selectedCarrier :
      PureWZ2TerminalPopularSelectedParentCarrierData selection}
    {sources : PureWZ2TerminalPopularCoarseSourceFamily selection}
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    (prep : PureWZ2TerminalPopularGraphPreparation localized) :
    restrictedPrepared.volumeSupply * weightClass.weightFloor ≤
      pureWZ2TerminalPopularGraphVolumeCost delta sigma inputLoss *
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
  have hwindowSupply : restrictedPrepared.volumeSupply ≤
      volume (pureWZ2PartialActiveCellShading restricted.shading
        source.extremal.delta_pos).union := by
    rw [← restrictedPrepared.volume_eq]
  have hball : (pureWZ2PartialActiveCellShading restricted.shading
      source.extremal.delta_pos).union ⊆
        Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    rw [pureWZ2PartialActiveCellShading_union] at hpoint
    have hsource := restricted.subshading_source.union_subset hpoint
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hsliceAreaUpper : volume (wz1Lemma23PlanarSlice
      (pureWZ2PartialActiveCellShading restricted.shading
        source.extremal.delta_pos).union line.lineHeight) ≤
        (line.sliceCells.card : ENNReal) * sliceDisk := by
    have hraw := wz1_lemma23_exactSlice_area_le_two
      (pureWZ2PartialActiveCellShading restricted.shading
        source.extremal.delta_pos) source.extremal.delta_pos hball
      line.lineHeight
    simpa [line.sliceCells_eq, sliceDisk] using hraw
  have hsliceThicknessPos : 0 < sliceThickness := by
    apply ENNReal.ofReal_pos.mpr
    have hroot : 0 < Real.sqrt delta :=
      Real.sqrt_pos.mpr source.extremal.delta_pos
    linarith [source.extremal.delta_pos]
  have hwindowToSlice : volume (pureWZ2PartialActiveCellShading
      restricted.shading source.extremal.delta_pos).union ≤
      volume (wz1Lemma23PlanarSlice
        (pureWZ2PartialActiveCellShading restricted.shading
          source.extremal.delta_pos).union line.lineHeight) *
        sliceThickness := by
    apply (ENNReal.div_le_iff hsliceThicknessPos.ne' ENNReal.ofReal_ne_top).mp
    simpa [sliceThickness] using line.slice_area_lower
  have hsliceCount : (line.sliceCells.card : ENNReal) ≤
      (line.globalBins.card : ENNReal) * (line.heavyCells.card : ENNReal) := by
    exact_mod_cast parents.heavy_cell_count
  have hglobalCount : (line.globalBins.card : ENNReal) ≤ globalBound := by
    simpa [globalBound] using line.global_bin_count
  have hparentFiber : ∀ parent,
      (line.heavyCells.filter fun cell => parents.parentCell cell = parent).card ≤
        pureWZ2FixedLineParentFiberBound delta := by
    intro parent
    exact pureWZ2_fixedLine_parent_fiber_card line
      terminal.sqrtRequested.1 terminal.sticky.coarse_extremal.delta_pos
      terminal.sqrtRequested_eq parents.parentCell
      parents.representative_mem_parent parent
  have hheavyCountNat : line.heavyCells.card ≤
      pureWZ2FixedLineParentFiberBound delta * parents.parents.card := by
    rw [parents.parents_eq]
    exact Finset.card_le_mul_card_image line.heavyCells
      (pureWZ2FixedLineParentFiberBound delta)
      (fun parent _ => hparentFiber parent)
  have hheavyCount : (line.heavyCells.card : ENNReal) ≤
      parentBound * (parents.parents.card : ENNReal) := by
    dsimp only [parentBound]
    exact_mod_cast hheavyCountNat
  have hwindowCount : restrictedPrepared.volumeSupply ≤
      sliceThickness * sliceDisk * globalBound * parentBound *
        (parents.parents.card : ENNReal) := by
    calc
      restrictedPrepared.volumeSupply ≤ volume
          (pureWZ2PartialActiveCellShading restricted.shading
            source.extremal.delta_pos).union := hwindowSupply
      _ ≤ volume (wz1Lemma23PlanarSlice
          (pureWZ2PartialActiveCellShading restricted.shading
            source.extremal.delta_pos).union line.lineHeight) *
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
  have hparentsFloor :
      (parents.parents.card : ENNReal) * weightClass.weightFloor ≤
        ∑ parent ∈ parents.parents,
          pureWZ2TerminalPopularParentWeight carrier parent := by
    calc
      (parents.parents.card : ENNReal) * weightClass.weightFloor =
          ∑ _parent ∈ parents.parents, weightClass.weightFloor := by
        simp [Finset.sum_const]
      _ ≤ ∑ parent ∈ parents.parents,
          pureWZ2TerminalPopularParentWeight carrier parent := by
        exact Finset.sum_le_sum fun parent hparent =>
          (weightClass.weight_band parent
            (parents.parents_subset_selected hparent)).1
  have hselectedWeight :
      (∑ parent ∈ selection.selected,
          pureWZ2TerminalPopularParentWeight carrier parent) ≤
        2 * weightClass.weightFloor *
          (selection.selected.card : ENNReal) := by
    calc
      (∑ parent ∈ selection.selected,
          pureWZ2TerminalPopularParentWeight carrier parent) ≤
        ∑ _parent ∈ selection.selected, 2 * weightClass.weightFloor := by
          exact Finset.sum_le_sum fun parent hparent =>
            (weightClass.weight_band parent
              (selection.selected_subset_weightClass hparent)).2
      _ = 2 * weightClass.weightFloor *
          (selection.selected.card : ENNReal) := by
        simp [Finset.sum_const]
        ring
  have hselectedCard : (selection.selected.card : ENNReal) ≤
      114 * (localized.selectedParents.card : ENNReal) := by
    exact_mod_cast localized.parent_card
  have hparentFloorToShadow :
      (parents.parents.card : ENNReal) * weightClass.weightFloor ≤
        (45 * 512 : ENNReal) * 2 * 114 *
          pureWZ2TerminalPopularLocalizedPieceCost *
            volume prep.shadow.union := by
    calc
      (parents.parents.card : ENNReal) * weightClass.weightFloor ≤
          ∑ parent ∈ parents.parents,
            pureWZ2TerminalPopularParentWeight carrier parent := hparentsFloor
      _ ≤ (45 * 512 : ENNReal) *
          ∑ parent ∈ selection.selected,
            pureWZ2TerminalPopularParentWeight carrier parent :=
        selection.visible_to_selected_weight
      _ ≤ (45 * 512 : ENNReal) *
          (2 * weightClass.weightFloor *
            (selection.selected.card : ENNReal)) := by gcongr
      _ ≤ (45 * 512 : ENNReal) *
          (2 * weightClass.weightFloor *
            (114 * (localized.selectedParents.card : ENNReal))) := by gcongr
      _ = (45 * 512 : ENNReal) * 2 * 114 *
          ((localized.selectedParents.card : ENNReal) *
            weightClass.weightFloor) := by ring
      _ ≤ (45 * 512 : ENNReal) * 2 * 114 *
          (pureWZ2TerminalPopularLocalizedPieceCost *
            volume prep.shadow.union) := by
        exact mul_le_mul_left' prep.volume_floor _
      _ = (45 * 512 : ENNReal) * 2 * 114 *
          pureWZ2TerminalPopularLocalizedPieceCost *
            volume prep.shadow.union := by ring
  calc
    restrictedPrepared.volumeSupply * weightClass.weightFloor ≤
        (sliceThickness * sliceDisk * globalBound * parentBound *
          (parents.parents.card : ENNReal)) * weightClass.weightFloor := by
      gcongr
    _ = (sliceThickness * sliceDisk * globalBound * parentBound) *
        ((parents.parents.card : ENNReal) * weightClass.weightFloor) := by ring
    _ ≤ (sliceThickness * sliceDisk * globalBound * parentBound) *
        ((45 * 512 : ENNReal) * 2 * 114 *
          pureWZ2TerminalPopularLocalizedPieceCost *
            volume prep.shadow.union) := by
      exact mul_le_mul_left' hparentFloorToShadow _
    _ = pureWZ2TerminalPopularGraphVolumeCost delta sigma inputLoss *
        volume prep.shadow.union := by
      simp [pureWZ2TerminalPopularGraphVolumeCost,
        pureWZ2TerminalPopularParentVolumeCost, sliceThickness, sliceDisk,
        globalBound, parentBound]
      ring

end Kakeya.Assouad

end
