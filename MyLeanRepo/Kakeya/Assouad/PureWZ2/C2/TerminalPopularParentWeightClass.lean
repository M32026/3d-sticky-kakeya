import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularWeightedParents
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedVolumeIdentities
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperActiveCellLogBound
import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization.WeightBinning

/-!
# Pre-line regularization of terminal outer-popular parent mass

The fixed line must be chosen only after the outer-popular carrier has been
restricted to a common positive parent-weight class.  This file partitions the
whole outer-popular carrier by all official active sticky parents, dyadically
regularizes the genuine intersection volumes, and keeps the exact retained
carrier.  It does not use the later fixed-line visible-parent family.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The outer-popular carrier is exactly partitioned by all official active
terminal parent cubes. -/
theorem PureWZ2TerminalPopularSourceCarrierData.parent_partition
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    (carrier : PureWZ2TerminalPopularSourceCarrierData heightData) :
    carrier.shading.union =
      ⋃ parent ∈ terminal.sticky.balanced.activeCells,
        carrier.shading.union ∩
          wz1PaperGridCube terminal.sqrtRequested.1 parent := by
  apply Set.Subset.antisymm
  · intro point hpoint
    have hambient : point ∈ carrier.zeroExtension.ambientShading.union := by
      rcases hpoint with ⟨index, hindex⟩
      refine ⟨index, ?_⟩
      rw [carrier.carrier_eq] at hindex
      exact hindex.1
    have hrefined : point ∈ terminal.sticky.refined.union := by
      rwa [carrier.zeroExtension.union_eq] at hambient
    rw [terminal.sticky.balanced.toWZ1PaperBalancedCoverData.fine_cell_partition]
      at hrefined
    rcases Set.mem_iUnion₂.mp hrefined with
      ⟨parent, hparent, _hrefined, hpointParent⟩
    exact Set.mem_iUnion₂.mpr ⟨parent, hparent, hpoint, hpointParent⟩
  · intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨_parent, _hparent, hcarrier, _hpointParent⟩
    exact hcarrier

/-- Exact total weight of all official active parents on the outer-popular
carrier. -/
theorem PureWZ2TerminalPopularSourceCarrierData.sum_parentWeight_eq
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    (carrier : PureWZ2TerminalPopularSourceCarrierData heightData) :
    (∑ parent ∈ terminal.sticky.balanced.activeCells,
        pureWZ2TerminalPopularParentWeight carrier parent) =
      volume carrier.shading.union := by
  rw [pureWZ2TerminalPopularParentWeight_sum_eq carrier
    terminal.sticky.balanced.activeCells]
  rw [Set.inter_eq_left.mpr]
  intro point hpoint
  rw [carrier.parent_partition] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint with
    ⟨parent, hparent, _hcarrier, hpointParent⟩
  exact Set.mem_iUnion₂.mpr ⟨parent, hparent, hpointParent⟩

/-- A positive dyadic class of official sticky parents, weighted by the
actual outer-popular volume inside each parent cube. -/
structure PureWZ2TerminalPopularParentWeightClassData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    (carrier : PureWZ2TerminalPopularSourceCarrierData heightData) where
  supportParents : Finset (ℤ × ℤ × ℤ)
  supportParents_nonempty : supportParents.Nonempty
  supportParents_subset :
    supportParents ⊆ terminal.sticky.balanced.activeCells
  bins : ℕ
  bins_eq : bins = Nat.log 2
    (2 * supportParents.card) + 1
  selectedParents : Finset (ℤ × ℤ × ℤ)
  selectedParents_nonempty : selectedParents.Nonempty
  selectedParents_subset_support : selectedParents ⊆ supportParents
  selectedParents_subset :
    selectedParents ⊆ terminal.sticky.balanced.activeCells
  weightFloor : ENNReal
  weightFloor_pos : 0 < weightFloor
  weightFloor_ne_top : weightFloor ≠ ⊤
  average_lower : ∀ parent ∈ selectedParents,
    volume carrier.shading.union /
        (2 * (supportParents.card : ENNReal)) ≤
      pureWZ2TerminalPopularParentWeight carrier parent
  weight_band : ∀ parent ∈ selectedParents,
    weightFloor ≤ pureWZ2TerminalPopularParentWeight carrier parent ∧
      pureWZ2TerminalPopularParentWeight carrier parent ≤ 2 * weightFloor
  selectedRegion : Set Point3 :=
    ⋃ parent ∈ selectedParents,
      wz1PaperGridCube terminal.sqrtRequested.1 parent
  selectedRegion_eq : selectedRegion =
    ⋃ parent ∈ selectedParents,
      wz1PaperGridCube terminal.sqrtRequested.1 parent
  selectedRegion_measurable : MeasurableSet selectedRegion
  selectedWeight : ENNReal :=
    ∑ parent ∈ selectedParents,
      pureWZ2TerminalPopularParentWeight carrier parent
  selectedWeight_eq : selectedWeight =
    volume (carrier.shading.union ∩ selectedRegion)
  selectedWeight_pos : 0 < selectedWeight
  retained_volume : volume carrier.shading.union ≤
    2 * bins * selectedWeight

/-- The dyadic floor controls the average outer-popular mass per official
terminal parent.  The factor four is the product of the initial factor-two
discard and the width-two dyadic band. -/
theorem PureWZ2TerminalPopularParentWeightClassData.average_le_weightFloor
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    (weightClass : PureWZ2TerminalPopularParentWeightClassData carrier) :
    volume carrier.shading.union /
        (4 * (weightClass.supportParents.card : ENNReal)) ≤
      weightClass.weightFloor := by
  rcases weightClass.selectedParents_nonempty with ⟨parent, hparent⟩
  have hactive : parent ∈ terminal.sticky.balanced.activeCells :=
    weightClass.selectedParents_subset hparent
  have hcardPos :
      0 < (weightClass.supportParents.card : ENNReal) := by
    exact_mod_cast weightClass.supportParents_nonempty.card_pos
  have htwoCardZero :
      2 * (weightClass.supportParents.card : ENNReal) ≠ 0 :=
    mul_ne_zero (by norm_num) hcardPos.ne'
  have htwoCardTop :
      2 * (weightClass.supportParents.card : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)
  have hfourCardZero :
      4 * (weightClass.supportParents.card : ENNReal) ≠ 0 :=
    mul_ne_zero (by norm_num) hcardPos.ne'
  have hfourCardTop :
      4 * (weightClass.supportParents.card : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)
  apply (ENNReal.div_le_iff hfourCardZero hfourCardTop).2
  have haverage := weightClass.average_lower parent hparent
  have hweightUpper := (weightClass.weight_band parent hparent).2
  have hcarrier : volume carrier.shading.union ≤
      pureWZ2TerminalPopularParentWeight carrier parent *
        (2 * (weightClass.supportParents.card : ENNReal)) :=
    (ENNReal.div_le_iff htwoCardZero htwoCardTop).1 haverage
  calc
    volume carrier.shading.union ≤
        pureWZ2TerminalPopularParentWeight carrier parent *
          (2 * (weightClass.supportParents.card : ENNReal)) :=
      hcarrier
    _ ≤ (2 * weightClass.weightFloor) *
          (2 * (weightClass.supportParents.card : ENNReal)) := by
      gcongr
    _ = weightClass.weightFloor *
          (4 * (weightClass.supportParents.card : ENNReal)) := by
      ring

/-- The parent-weight dyadic class is controlled by the physical active-cell
logarithm of the terminal coarse shading. -/
theorem PureWZ2TerminalPopularParentWeightClassData.bins_le_logEnvelope
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    (weightClass : PureWZ2TerminalPopularParentWeightClassData carrier) :
    (weightClass.bins : ENNReal) ≤
      2 * ENNReal.ofReal
        (wz2PaperBoundaryLogCoefficient *
          (1 + Real.log terminal.sqrtRequested.1⁻¹)) := by
  have hactive : terminal.sticky.balanced.activeCells ⊆
      wz1PaperActiveCells terminal.sticky.croppedCoarseShading
        terminal.sticky.coarse_extremal.delta_pos := by
    intro cell hcell
    let point : Point3 := cellCorner terminal.sqrtRequested.1 cell
    have hpointCell : point ∈
        wz1PaperGridCube terminal.sqrtRequested.1 cell :=
      cellCorner_mem_gridCube
        terminal.sticky.coarse_extremal.delta_pos cell
    have hpointUnion : point ∈
        terminal.sticky.croppedCoarseShading.union := by
      rw [terminal.sticky.balanced.coarse_union_eq]
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCell⟩
    rcases hpointUnion with ⟨index, hpointCarrier⟩
    have hpointBody := terminal.sticky.croppedCoarseShading.subset_body
      index hpointCarrier
    have hwindow : wz1PaperGridIndex terminal.sqrtRequested.1 point ∈
        wz1PaperGridIndicesInWindow terminal.sqrtRequested.1
          terminal.sticky.coarse_extremal.delta_pos :=
      paper_point_gridIndex_in_window
        terminal.sticky.coarse_extremal.delta_pos hpointBody.2
    have hindex : wz1PaperGridIndex terminal.sqrtRequested.1 point = cell :=
      (mem_wz1PaperGridCube terminal.sqrtRequested.1 cell point).mp
        hpointCell
    rw [hindex] at hwindow
    rw [mem_wz1PaperActiveCells]
    exact ⟨hwindow, ⟨point, ⟨index, hpointCarrier⟩, hpointCell⟩⟩
  have hactiveNonempty :
      terminal.sticky.balanced.activeCells.Nonempty := by
    exact weightClass.supportParents_nonempty.mono
      weightClass.supportParents_subset
  let activeCount := (wz1PaperActiveCells
    terminal.sticky.croppedCoarseShading
      terminal.sticky.coarse_extremal.delta_pos).card
  have hactiveCountNonempty : 0 < activeCount := by
    apply Finset.card_pos.mpr
    exact hactiveNonempty.mono hactive
  have hlogDouble : Nat.log 2 (2 * activeCount) + 1 =
      (Nat.log 2 activeCount + 1) + 1 := by
    rw [show 2 * activeCount = activeCount * 2 by omega,
      Nat.log_mul_base (by omega) hactiveCountNonempty.ne']
  have hlogNat : weightClass.bins ≤
      (Nat.log 2 activeCount + 1) + 1 := by
    rw [hlogDouble.symm, weightClass.bins_eq]
    apply Nat.add_le_add_right
    apply Nat.log_mono_right
    exact Nat.mul_le_mul_left 2 (Finset.card_le_card
      (weightClass.supportParents_subset.trans hactive))
  have hphysical :
      ((Nat.log 2 activeCount + 1 : ℕ) : ENNReal) ≤
      ENNReal.ofReal
        (wz2PaperBoundaryLogCoefficient *
          (1 + Real.log terminal.sqrtRequested.1⁻¹)) := by
    dsimp only [activeCount]
    exact wz2_paper_active_cell_log_bound_ennreal
      terminal.sticky.coarse_extremal.delta_pos
      terminal.sticky.coarse_extremal.delta_le_one
      terminal.sticky.croppedCoarseShading
  have honePhysical : (1 : ENNReal) ≤
      ENNReal.ofReal
        (wz2PaperBoundaryLogCoefficient *
          (1 + Real.log terminal.sqrtRequested.1⁻¹)) := by
    calc
      (1 : ENNReal) ≤
          ((Nat.log 2 activeCount + 1 : ℕ) : ENNReal) := by
        exact_mod_cast (show 1 ≤
          Nat.log 2 activeCount + 1 by omega)
      _ ≤ _ := hphysical
  have hlogCast : (weightClass.bins : ENNReal) ≤
      ((Nat.log 2 activeCount + 1 : ℕ) : ENNReal) + 1 := by
    exact_mod_cast hlogNat
  calc
    (weightClass.bins : ENNReal) ≤
        ((Nat.log 2 activeCount + 1 : ℕ) : ENNReal) + 1 := hlogCast
    _ ≤ ENNReal.ofReal
          (wz2PaperBoundaryLogCoefficient *
            (1 + Real.log terminal.sqrtRequested.1⁻¹)) +
        ENNReal.ofReal
          (wz2PaperBoundaryLogCoefficient *
            (1 + Real.log terminal.sqrtRequested.1⁻¹)) :=
      add_le_add hphysical honePhysical
    _ = _ := by ring

/-- Parent-weight regularization over an explicit support whose weights sum to
the current carrier volume.  This is the interface needed after a preceding
block--parent pair selection: zero parents outside the support do not enter the
dyadic denominator. -/
theorem PureWZ2TerminalPopularSourceCarrierData.regularizeParentWeightsOnSupport
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    (carrier : PureWZ2TerminalPopularSourceCarrierData heightData)
    (supportParents : Finset (ℤ × ℤ × ℤ))
    (hsupportNonempty : supportParents.Nonempty)
    (hsupportSubset :
      supportParents ⊆ terminal.sticky.balanced.activeCells)
    (hsupportSum :
      (∑ parent ∈ supportParents,
          pureWZ2TerminalPopularParentWeight carrier parent) =
        volume carrier.shading.union) :
    ∃ weightClass : PureWZ2TerminalPopularParentWeightClassData carrier,
      weightClass.supportParents = supportParents := by
  let parentType :=
    {parent // parent ∈ supportParents}
  let weight : parentType → ENNReal := fun parent =>
    pureWZ2TerminalPopularParentWeight carrier parent.1
  let total := volume carrier.shading.union
  have htotal : total = ∑ parent : parentType, weight parent := by
    calc
      total = ∑ parent ∈ supportParents,
          pureWZ2TerminalPopularParentWeight carrier parent :=
        hsupportSum.symm
      _ = ∑ parent : parentType, weight parent := by
        simpa [parentType, weight] using
          (Finset.sum_attach supportParents
            (pureWZ2TerminalPopularParentWeight carrier)).symm
  have htotalPos : 0 < total := by
    dsimp only [total]
    rw [carrier.volume_eq]
    exact heightData.graphWindow.volumeSupply_pos.trans_le
      heightData.graphWindow.volume_lower
  have htotalTop : total ≠ ⊤ := by
    have hball : carrier.shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
      intro point hpoint
      have hsource := carrier.subshading.union_subset hpoint
      have hnorm := norm_le_two_of_mem_paperShading hsource
      simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
    exact ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
      (measure_mono hball)
  rcases ennreal_dyadic_bin weight total htotal htotalTop htotalPos with
    ⟨bins, selected, hbins, hselected, hretained, hthreshold,
      weightFloor, hweightFloor, hweightBand⟩
  let selectedParents := selected.image Subtype.val
  have hselectedInjective : Set.InjOn
      (Subtype.val : parentType → (ℤ × ℤ × ℤ)) selected :=
    fun _ _ _ _ h => Subtype.ext h
  have hselectedSubset :
      selectedParents ⊆ supportParents := by
    intro parent hparent
    rcases Finset.mem_image.mp hparent with ⟨parentIndex, _hindex, rfl⟩
    exact parentIndex.property
  have hselectedSum :
      (∑ parent ∈ selectedParents,
          pureWZ2TerminalPopularParentWeight carrier parent) =
        ∑ parent ∈ selected, weight parent := by
    exact Finset.sum_image hselectedInjective
  let selectedRegion : Set Point3 :=
    ⋃ parent ∈ selectedParents,
      wz1PaperGridCube terminal.sqrtRequested.1 parent
  have hregionMeas : MeasurableSet selectedRegion :=
    MeasurableSet.biUnion selectedParents.finite_toSet.countable
      (fun parent _ => wz1PaperGridCube_measurable parent)
  have hselectedWeightEq :
      (∑ parent ∈ selectedParents,
          pureWZ2TerminalPopularParentWeight carrier parent) =
        volume (carrier.shading.union ∩ selectedRegion) := by
    simpa [selectedRegion] using
      pureWZ2TerminalPopularParentWeight_sum_eq carrier selectedParents
  have hretained' : volume carrier.shading.union ≤
      2 * bins *
        ∑ parent ∈ selectedParents,
          pureWZ2TerminalPopularParentWeight carrier parent := by
    rw [show volume carrier.shading.union = total by rfl, hselectedSum]
    have htwo : total ≤
        2 * ((∑ parent ∈ selected, weight parent) * bins) := by
      calc
        total = total / 2 + total / 2 := (ENNReal.add_halves total).symm
        _ ≤ (∑ parent ∈ selected, weight parent) * bins +
            (∑ parent ∈ selected, weight parent) * bins :=
          add_le_add hretained hretained
        _ = 2 * ((∑ parent ∈ selected, weight parent) * bins) := by ring
    simpa [mul_comm, mul_left_comm, mul_assoc] using htwo
  have hweightFloorTop : weightFloor ≠ ⊤ := by
    rcases hselected with ⟨parent, hparent⟩
    have hweightTop : weight parent ≠ ⊤ := by
      apply ne_top_of_le_ne_top htotalTop
      rw [htotal]
      exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ parent)
    exact ne_top_of_le_ne_top hweightTop (hweightBand parent hparent).1
  have hselectedWeightPos :
      0 < ∑ parent ∈ selectedParents,
        pureWZ2TerminalPopularParentWeight carrier parent := by
    rcases hselected with ⟨parent, hparent⟩
    have hpositive : 0 < weight parent :=
      hweightFloor.trans_le (hweightBand parent hparent).1
    rw [hselectedSum]
    exact hpositive.trans_le
      (Finset.single_le_sum (fun _ _ => bot_le) hparent)
  refine ⟨{
    supportParents := supportParents
    supportParents_nonempty := hsupportNonempty
    supportParents_subset := hsupportSubset
    bins := bins
    bins_eq := by
      simpa [parentType, Fintype.card_subtype] using hbins
    selectedParents := selectedParents
    selectedParents_nonempty := hselected.image _
    selectedParents_subset_support := hselectedSubset
    selectedParents_subset := hselectedSubset.trans hsupportSubset
    weightFloor := weightFloor
    weightFloor_pos := hweightFloor
    weightFloor_ne_top := hweightFloorTop
    average_lower := by
      intro parent hparent
      rcases Finset.mem_image.mp hparent with
        ⟨parentIndex, hparentIndex, heq⟩
      subst parent
      simpa [total, parentType, weight] using
        hthreshold parentIndex hparentIndex
    weight_band := by
      intro parent hparent
      rcases Finset.mem_image.mp hparent with
        ⟨parentIndex, hparentIndex, heq⟩
      subst parent
      simpa [weight] using hweightBand parentIndex hparentIndex
    selectedRegion := selectedRegion
    selectedRegion_eq := rfl
    selectedRegion_measurable := hregionMeas
    selectedWeight :=
      ∑ parent ∈ selectedParents,
        pureWZ2TerminalPopularParentWeight carrier parent
    selectedWeight_eq := hselectedWeightEq
    selectedWeight_pos := hselectedWeightPos
    retained_volume := hretained'
  }, rfl⟩

/-- Backwards-compatible regularization over all official active parents. -/
theorem PureWZ2TerminalPopularSourceCarrierData.regularizeParentWeights
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    (carrier : PureWZ2TerminalPopularSourceCarrierData heightData) :
    Nonempty (PureWZ2TerminalPopularParentWeightClassData carrier) := by
  have hactiveNonempty :
      terminal.sticky.balanced.activeCells.Nonempty := by
    have htotalPos : 0 < volume carrier.shading.union := by
      rw [carrier.volume_eq]
      exact heightData.graphWindow.volumeSupply_pos.trans_le
        heightData.graphWindow.volume_lower
    by_contra hempty
    have hzero : terminal.sticky.balanced.activeCells = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hsum := carrier.sum_parentWeight_eq
    rw [hzero] at hsum
    simp only [Finset.sum_empty] at hsum
    exact htotalPos.ne' hsum.symm
  rcases carrier.regularizeParentWeightsOnSupport
      terminal.sticky.balanced.activeCells hactiveNonempty Finset.Subset.rfl
      carrier.sum_parentWeight_eq with ⟨weightClass, _hsupport⟩
  exact ⟨weightClass⟩

end Kakeya.Assouad

end
