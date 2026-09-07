import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalGlobalBinVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalGoodBlocks
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalWindowHeightPopularity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalExactVolumeSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalAnalyticSchedule

/-!
# Volume-good terminal global bins

The all-bin preparation preserves the exact Fubini-slice partition.  We now
discard only bins whose own sharp carrier is below the ready-graph volume
threshold.  A separate numerical premise bounds the total contribution of
those bad bins, making the retained family nonempty and preserving at least
half of the aggregate volume.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

def pureWZ2GoodTerminalGlobalBins
    {sigma inputLoss delta stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parentFamily : PureWZ2TerminalGlobalBinParentFamily line}
    (data : PureWZ2TerminalGlobalBinPreparedFamily
      (eta := eta) parentFamily)
    (volumeLoss : ℝ) : Finset {bin // bin ∈ line.globalBins} :=
  Finset.univ.filter fun bin =>
    Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) ≤
      volume (parentFamily.preparedGraphCarrier bin).shadow.union

structure PureWZ2TerminalGoodGlobalBinFamily
    {sigma inputLoss delta stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parentFamily : PureWZ2TerminalGlobalBinParentFamily line}
    (data : PureWZ2TerminalGlobalBinPreparedFamily
      (eta := eta) parentFamily)
    (volumeLoss : ℝ) where
  selected : Finset {bin // bin ∈ line.globalBins} :=
    pureWZ2GoodTerminalGlobalBins data volumeLoss
  selected_eq : selected = pureWZ2GoodTerminalGlobalBins data volumeLoss
  selected_nonempty : selected.Nonempty
  volume_lower : ∀ bin ∈ selected,
    Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) ≤
      volume (parentFamily.preparedGraphCarrier bin).shadow.union
  total_volume_le :
    (∑ bin : {bin // bin ∈ line.globalBins},
        volume (parentFamily.preparedGraphCarrier bin).shadow.union) ≤
      2 * ∑ bin ∈ selected,
        volume (parentFamily.preparedGraphCarrier bin).shadow.union

/-- Select the volume-good global bins once their total bad-bin budget has
been absorbed. -/
theorem PureWZ2TerminalGlobalBinPreparedFamily.selectGoodBins
    {sigma inputLoss delta stickyLoss eta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parentFamily : PureWZ2TerminalGlobalBinParentFamily line}
    (data : PureWZ2TerminalGlobalBinPreparedFamily
      (eta := eta) parentFamily)
    (hbad :
      2 * ((line.globalBins.card : ENNReal) *
        Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss)) ≤
      ∑ bin : {bin // bin ∈ line.globalBins},
        volume (parentFamily.preparedGraphCarrier bin).shadow.union) :
    Nonempty (PureWZ2TerminalGoodGlobalBinFamily data volumeLoss) := by
  let bins := (Finset.univ : Finset {bin // bin ∈ line.globalBins})
  let supply : {bin // bin ∈ line.globalBins} → ENNReal := fun bin =>
    volume (parentFamily.preparedGraphCarrier bin).shadow.union
  let threshold :=
    Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss)
  have hcard : bins.card = line.globalBins.card := by
    simp [bins]
  have hthresholdTop : threshold ≠ ⊤ := by
    simp [threshold, Kakeya.realRpowENN]
  have hbad' : 2 * ((bins.card : ENNReal) * threshold) ≤
      ∑ bin ∈ bins, supply bin * 1 := by
    simpa [bins, supply, threshold, hcard] using hbad
  have hhalf := finset_good_weighted_supply_retains_half
    bins supply 1 threshold hthresholdTop hbad'
  let selected := bins.filter fun bin => threshold ≤ supply bin
  have htotalPos : 0 < ∑ bin ∈ bins, supply bin := by
    let first : {bin // bin ∈ line.globalBins} :=
      ⟨line.lineBin, line.lineBin_mem⟩
    have hheightNonempty :=
      (data.preparedGraph first).heightPopular.heightIndices_nonempty
    rcases hheightNonempty with ⟨heightIndex, hheightIndex⟩
    have hlocalPos : 0 < supply first := by
      dsimp only [supply]
      apply (data.preparedGraph first).heightPopular.layerMass_pos.trans_le
      calc
        (data.preparedGraph first).heightPopular.layerMass ≤
            volume ((parentFamily.preparedGraphCarrier first).shadow.union ∩
              wz1Lemma23HeightSlab delta heightIndex) :=
          ((data.preparedGraph first).heightPopular.layer_volume_band
            heightIndex hheightIndex).1
        _ ≤ volume (parentFamily.preparedGraphCarrier first).shadow.union :=
          measure_mono Set.inter_subset_left
    exact hlocalPos.trans_le
      (Finset.single_le_sum (fun _ _ => bot_le) (by simp [bins, first]))
  have hselectedNonempty : selected.Nonempty := by
    by_contra hempty
    have hselectedEmpty : selected = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hleZero : (∑ bin ∈ bins, supply bin) ≤ 0 := by
      simpa [selected, hselectedEmpty] using hhalf
    exact (not_le_of_gt htotalPos) hleZero
  exact ⟨{
    selected := selected
    selected_eq := by rfl
    selected_nonempty := hselectedNonempty
    volume_lower := by
      intro bin hbin
      exact (Finset.mem_filter.mp hbin).2
    total_volume_le := by
      simpa [selected, bins, supply, threshold] using hhalf
  }⟩

/-- Combine the certified initial window, source-volume height popularity, and
the all-bin aggregate estimate. The only remaining input is a scale-arithmetic
inequality absorbing the outer popularity logarithm. -/
theorem PureWZ2TerminalGlobalBinPreparedFamily.selectGoodBins_of_budget
    {sigma inputLoss delta stickyLoss eta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (certifiedWindow : PureWZ2TerminalCertifiedWindow prepared)
    (heightData : PureWZ2TerminalWindowHeightPopularData
      certifiedWindow.toGraphWindow)
    {line : PureWZ2HorizontalFixedLineCore
      heightData.graphWindow.windowed source.globalGrains.slope}
    {parentFamily : PureWZ2TerminalGlobalBinParentFamily line}
    (data : PureWZ2TerminalGlobalBinPreparedFamily
      (eta := eta) parentFamily)
    (hbudget :
      (4 * heightData.popular.bins : ENNReal) *
          Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) *
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
        (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2)) :
    Nonempty (PureWZ2TerminalGoodGlobalBinFamily data volumeLoss) := by
  let threshold :=
    Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss)
  let allCost := pureWZ2TerminalAllBinVolumeCost delta
  let globalBound : ENNReal :=
    132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
      Kakeya.realRpowENN (1 / delta) (1 - sigma)
  have hglobalCount : (line.globalBins.card : ENNReal) ≤ globalBound := by
    simpa [globalBound] using line.global_bin_count
  have hcostEq : pureWZ2TerminalExactVolumeCost delta sigma inputLoss =
      allCost * globalBound := by
    simp [pureWZ2TerminalExactVolumeCost,
      pureWZ2TerminalAllBinVolumeCost, allCost, globalBound]
    ring
  have hlower := pureWZ2_terminalExact_windowSupply_lower_of_window
    certifiedWindow source.extremal.delta_le_one
  have hcertifiedToPopular : certifiedWindow.volumeSupply ≤
      (2 * heightData.popular.bins : ENNReal) *
        heightData.graphWindow.volumeSupply := by
    calc
      certifiedWindow.volumeSupply ≤ volume certifiedWindow.shading.union :=
        certifiedWindow.volume_lower
      _ = volume certifiedWindow.toGraphWindow.shading.union := rfl
      _ ≤ (2 * heightData.popular.bins : ENNReal) *
          heightData.graphWindow.volumeSupply := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          heightData.source_volume_retention
  have hglobalToPopular :
      (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) ≤
        (2 * heightData.popular.bins : ENNReal) *
          (heightData.graphWindow.volumeSupply *
            terminal.sticky.balanced.cellMass) := by
    calc
      _ ≤ certifiedWindow.volumeSupply *
          terminal.sticky.balanced.cellMass := hlower
      _ ≤ ((2 * heightData.popular.bins : ENNReal) *
          heightData.graphWindow.volumeSupply) *
            terminal.sticky.balanced.cellMass := by gcongr
      _ = (2 * heightData.popular.bins : ENNReal) *
          (heightData.graphWindow.volumeSupply *
            terminal.sticky.balanced.cellMass) := by ring
  have hbinsPos : 0 < heightData.popular.bins := by
    rw [heightData.popular.bins_eq]
    omega
  have hfactorZero : (2 * heightData.popular.bins : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (by omega) hbinsPos).ne'
  have hfactorTop : (2 * heightData.popular.bins : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)
  have hreadySupply : 2 * threshold *
        pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
      heightData.graphWindow.volumeSupply *
        terminal.sticky.balanced.cellMass := by
    apply (ENNReal.mul_le_mul_iff_left hfactorZero hfactorTop).mp
    calc
      (2 * threshold *
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss) *
          (2 * heightData.popular.bins : ENNReal) =
        (4 * heightData.popular.bins : ENNReal) * threshold *
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss := by
        push_cast
        ring
      _ ≤ (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) := hbudget
      _ ≤ (2 * heightData.popular.bins : ENNReal) *
          (heightData.graphWindow.volumeSupply *
            terminal.sticky.balanced.cellMass) := hglobalToPopular
      _ = (heightData.graphWindow.volumeSupply *
          terminal.sticky.balanced.cellMass) *
            (2 * heightData.popular.bins : ENNReal) := by ring
  have haggregate := parentFamily.aggregate_volume_supply_le
  let total := ∑ bin : {bin // bin ∈ line.globalBins},
    volume (parentFamily.preparedGraphCarrier bin).shadow.union
  have hcostZero : allCost ≠ 0 := by
    dsimp only [allCost, pureWZ2TerminalAllBinVolumeCost,
      pureWZ2TerminalExactParentThinning, pureWZ2TerminalExactAnchorCost]
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
    have hparent : 0 < (pureWZ2FixedLineParentFiberBound delta : ENNReal) := by
      simp [pureWZ2FixedLineParentFiberBound, pureWZ2FixedLineParentYBound]
    positivity
  have hcostTop : allCost ≠ ⊤ := by
    dsimp only [allCost, pureWZ2TerminalAllBinVolumeCost]
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (ENNReal.mul_ne_top
              (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
              ENNReal.ofReal_ne_top)
        · exact ENNReal.natCast_ne_top _
      · exact ENNReal.natCast_ne_top _
    · unfold pureWZ2TerminalExactAnchorCost
      exact ENNReal.mul_ne_top
        (show (512 : ENNReal) ≠ ⊤ from ENNReal.natCast_ne_top 512)
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (show (2 : ENNReal) ≠ ⊤ from ENNReal.natCast_ne_top 2)
            (show (512 : ENNReal) ≠ ⊤ from ENNReal.natCast_ne_top 512))
          (show (57 : ENNReal) ≠ ⊤ from ENNReal.natCast_ne_top 57))
  have hbadCost : allCost *
        (2 * (line.globalBins.card : ENNReal) * threshold) ≤
      heightData.graphWindow.volumeSupply *
        terminal.sticky.balanced.cellMass := by
    calc
      allCost * (2 * (line.globalBins.card : ENNReal) * threshold) ≤
          allCost * (2 * globalBound * threshold) := by gcongr
      _ = 2 * threshold *
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss := by
        rw [hcostEq]
        ring
      _ ≤ _ := hreadySupply
  have hbad : 2 * ((line.globalBins.card : ENNReal) * threshold) ≤ total := by
    apply (ENNReal.mul_le_mul_iff_left hcostZero hcostTop).mp
    calc
      (2 * ((line.globalBins.card : ENNReal) * threshold)) * allCost =
          allCost * (2 * (line.globalBins.card : ENNReal) * threshold) := by ring
      _ ≤ heightData.graphWindow.volumeSupply *
          terminal.sticky.balanced.cellMass := hbadCost
      _ ≤ allCost * total := by
        simpa [allCost, total] using haggregate
      _ = total * allCost := by ring
  apply data.selectGoodBins
  simpa [threshold, total] using hbad

/-- Select the volume-good global bins directly from the certified source
window.  This is the terminal order used in Lemma 24: first choose the source
slice and its global-bin fibres, then run the per-bin graph construction,
whose own height popularity produces `Z_popular` before `Z_lin`. -/
theorem PureWZ2TerminalGlobalBinPreparedFamily.selectGoodBins_of_certified_budget
    {sigma inputLoss delta stickyLoss eta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (certifiedWindow : PureWZ2TerminalCertifiedWindow prepared)
    {line : PureWZ2HorizontalFixedLineCore
      certifiedWindow.toGraphWindow.windowed source.globalGrains.slope}
    {parentFamily : PureWZ2TerminalGlobalBinParentFamily line}
    (data : PureWZ2TerminalGlobalBinPreparedFamily
      (eta := eta) parentFamily)
    (hbudget :
      2 * Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) *
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
        (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2)) :
    Nonempty (PureWZ2TerminalGoodGlobalBinFamily data volumeLoss) := by
  let threshold :=
    Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss)
  let allCost := pureWZ2TerminalAllBinVolumeCost delta
  let globalBound : ENNReal :=
    132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
      Kakeya.realRpowENN (1 / delta) (1 - sigma)
  have hglobalCount : (line.globalBins.card : ENNReal) ≤ globalBound := by
    simpa [globalBound] using line.global_bin_count
  have hcostEq : pureWZ2TerminalExactVolumeCost delta sigma inputLoss =
      allCost * globalBound := by
    simp [pureWZ2TerminalExactVolumeCost,
      pureWZ2TerminalAllBinVolumeCost, allCost, globalBound]
    ring
  have hlower := pureWZ2_terminalExact_windowSupply_lower_of_window
    certifiedWindow source.extremal.delta_le_one
  have hreadySupply :
      2 * threshold * pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
        certifiedWindow.volumeSupply *
          terminal.sticky.balanced.cellMass :=
    hbudget.trans hlower
  have haggregate := parentFamily.aggregate_volume_supply_le
  let total := ∑ bin : {bin // bin ∈ line.globalBins},
    volume (parentFamily.preparedGraphCarrier bin).shadow.union
  have hcostZero : allCost ≠ 0 := by
    dsimp only [allCost, pureWZ2TerminalAllBinVolumeCost,
      pureWZ2TerminalExactParentThinning, pureWZ2TerminalExactAnchorCost]
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
    have hparent : 0 < (pureWZ2FixedLineParentFiberBound delta : ENNReal) := by
      simp [pureWZ2FixedLineParentFiberBound, pureWZ2FixedLineParentYBound]
    positivity
  have hcostTop : allCost ≠ ⊤ := by
    dsimp only [allCost, pureWZ2TerminalAllBinVolumeCost]
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (ENNReal.mul_ne_top
              (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
              ENNReal.ofReal_ne_top)
        · exact ENNReal.natCast_ne_top _
      · exact ENNReal.natCast_ne_top _
    · unfold pureWZ2TerminalExactAnchorCost
      exact ENNReal.mul_ne_top
        (show (512 : ENNReal) ≠ ⊤ from ENNReal.natCast_ne_top 512)
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (show (2 : ENNReal) ≠ ⊤ from ENNReal.natCast_ne_top 2)
            (show (512 : ENNReal) ≠ ⊤ from ENNReal.natCast_ne_top 512))
          (show (57 : ENNReal) ≠ ⊤ from ENNReal.natCast_ne_top 57))
  have hbadCost : allCost *
        (2 * (line.globalBins.card : ENNReal) * threshold) ≤
      certifiedWindow.volumeSupply * terminal.sticky.balanced.cellMass := by
    calc
      allCost * (2 * (line.globalBins.card : ENNReal) * threshold) ≤
          allCost * (2 * globalBound * threshold) := by gcongr
      _ = 2 * threshold *
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss := by
        rw [hcostEq]
        ring
      _ ≤ _ := hreadySupply
  have hbad : 2 * ((line.globalBins.card : ENNReal) * threshold) ≤ total := by
    apply (ENNReal.mul_le_mul_iff_left hcostZero hcostTop).mp
    calc
      (2 * ((line.globalBins.card : ENNReal) * threshold)) * allCost =
          allCost * (2 * (line.globalBins.card : ENNReal) * threshold) := by
        ring
      _ ≤ certifiedWindow.volumeSupply *
          terminal.sticky.balanced.cellMass := hbadCost
      _ ≤ allCost * total := by
        change certifiedWindow.toGraphWindow.volumeSupply *
            terminal.sticky.balanced.cellMass ≤ allCost * total
        simpa [allCost, total] using haggregate
      _ = total * allCost := by ring
  apply data.selectGoodBins
  simpa [threshold, total] using hbad

/-- The height-volume popularity parameter is logarithmic in the terminal
spatial grid.  This is the single outer logarithm paid before the fixed-line
and global-bin decompositions. -/
theorem PureWZ2TerminalWindowHeightPopularData.bins_real_le_log
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    (data : PureWZ2TerminalWindowHeightPopularData window) :
    (data.popular.bins : ℝ) ≤
      23 * (Real.log (1 / delta) + 1) := by
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hdeltaOne : delta ≤ 1 := source.extremal.delta_le_one
  have hheightCard :
      (wz1Lemma23BoundedHeightIndices delta hdelta).card ≤
        (wz1Lemma23BoundedCells delta hdelta).card :=
    Finset.card_image_le
  have hheightNonempty :
      (wz1Lemma23BoundedHeightIndices delta hdelta).Nonempty :=
    data.popular.heightIndices_nonempty.mono
      data.popular.heightIndices_subset
  have hcellsNonempty :
      (wz1Lemma23BoundedCells delta hdelta).Nonempty := by
    simpa [wz1Lemma23BoundedHeightIndices] using hheightNonempty
  have hbinsArg :
      2 * (wz1Lemma23BoundedHeightIndices delta hdelta).card ≤
        4 * (wz1Lemma23BoundedCells delta hdelta).card := by
    have hcellsPos : 0 < (wz1Lemma23BoundedCells delta hdelta).card :=
      hcellsNonempty.card_pos
    omega
  have hbinsLog :
      Nat.log 2 (2 * (wz1Lemma23BoundedHeightIndices delta hdelta).card) ≤
        Nat.log 2 (4 * (wz1Lemma23BoundedCells delta hdelta).card) :=
    Nat.log_mono_right hbinsArg
  have hcellsNe : (wz1Lemma23BoundedCells delta hdelta).card ≠ 0 :=
    hcellsNonempty.card_ne_zero
  have hfourEq :
      4 * (wz1Lemma23BoundedCells delta hdelta).card =
        (wz1Lemma23BoundedCells delta hdelta).card * 2 * 2 := by
    ring
  have hbinsNat : data.popular.bins ≤
      Nat.log 2 (wz1Lemma23BoundedCells delta hdelta).card + 3 := by
    rw [data.popular.bins_eq]
    calc
      Nat.log 2
          (2 * (wz1Lemma23BoundedHeightIndices delta hdelta).card) + 1 ≤
          Nat.log 2
            (4 * (wz1Lemma23BoundedCells delta hdelta).card) + 1 := by
        omega
      _ = Nat.log 2 (wz1Lemma23BoundedCells delta hdelta).card + 3 := by
        rw [hfourEq]
        calc
          Nat.log 2
                ((wz1Lemma23BoundedCells delta hdelta).card * 2 * 2) + 1 =
              Nat.log 2
                ((wz1Lemma23BoundedCells delta hdelta).card * 2) + 1 + 1 := by
            rw [Nat.log_mul_base (by omega)
              (Nat.mul_ne_zero hcellsNe (by omega))]
          _ = Nat.log 2 (wz1Lemma23BoundedCells delta hdelta).card +
                1 + 1 + 1 := by
            rw [Nat.log_mul_base (by omega) hcellsNe]
          _ = _ := by omega
  let L : ℝ := Real.log (1 / delta) + 1
  have hlog := wz1Lemma23BoundedCells_log_bound hdelta hdeltaOne
  have hLone : 1 ≤ L := by
    dsimp only [L]
    have hlogNonneg : 0 ≤ Real.log (1 / delta) := by
      apply Real.log_nonneg
      exact one_le_one_div hdelta hdeltaOne
    linarith
  have hnat : (data.popular.bins : ℝ) ≤
      (Nat.log 2 (wz1Lemma23BoundedCells delta hdelta).card + 3 : ℕ) := by
    exact_mod_cast hbinsNat
  calc
    (data.popular.bins : ℝ) ≤
        (Nat.log 2 (wz1Lemma23BoundedCells delta hdelta).card + 3 : ℕ) :=
      hnat
    _ ≤ 20 * L + 2 := by
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      linarith [hlog]
    _ ≤ 23 * L := by nlinarith

/-- At sufficiently small terminal scale, the outer height-popularity
logarithm is absorbed by any prescribed positive power. -/
theorem pureWZ2_terminalHeightBins_power_schedule
    {extraLoss : ℝ} (hextraLoss : 0 < extraLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sigma inputLoss delta stickyLoss : ℝ}
        {logExponent : ℕ}
        {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
        {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
        {terminalSource : PureWZ2TerminalPreparedSource source terminal}
        {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
        {window : PureWZ2TerminalWindow prepared}
        (data : PureWZ2TerminalWindowHeightPopularData window),
        0 < delta → delta ≤ delta₀ →
          (4 * data.popular.bins : ENNReal) *
              Kakeya.realRpowENN delta extraLoss ≤ 1 := by
  rcases log_poly_decay_general 92 extraLoss (by norm_num) hextraLoss with
    ⟨delta₀, hdelta₀, hdelta₀One, habsorb⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro sigma inputLoss delta stickyLoss logExponent source terminal
    terminalSource prepared window data hdelta hdeltaSmall
  have hbins := data.bins_real_le_log
  have hreal : ((4 * data.popular.bins : ℕ) : ℝ) ≤
      Real.rpow delta (-extraLoss) := by
    calc
      ((4 * data.popular.bins : ℕ) : ℝ) ≤
          92 * (Real.log (1 / delta) + 1) := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        linarith
      _ ≤ 1 / delta ^ extraLoss :=
        habsorb delta hdelta hdeltaSmall
      _ = Real.rpow delta (-extraLoss) := by
        simpa [one_div] using (Real.rpow_neg hdelta.le extraLoss).symm
  have hbinsENN : (4 * data.popular.bins : ENNReal) ≤
      Kakeya.realRpowENN delta (-extraLoss) := by
    calc
      (4 * data.popular.bins : ENNReal) =
          ENNReal.ofReal (((4 * data.popular.bins : ℕ) : ℝ)) := by simp
      _ ≤ ENNReal.ofReal (Real.rpow delta (-extraLoss)) :=
        ENNReal.ofReal_mono hreal
      _ = Kakeya.realRpowENN delta (-extraLoss) := rfl
  calc
    (4 * data.popular.bins : ENNReal) *
          Kakeya.realRpowENN delta extraLoss ≤
        Kakeya.realRpowENN delta (-extraLoss) *
          Kakeya.realRpowENN delta extraLoss := by gcongr
    _ = Kakeya.realRpowENN delta ((-extraLoss) + extraLoss) :=
      (realRpowENN_add hdelta (-extraLoss) extraLoss).symm
    _ = 1 := by simp [Kakeya.realRpowENN]

/-- Uniform good-bin schedule when the fixed source line is chosen before the
per-bin height-popularity step, as in Lemma 24. -/
theorem pureWZ2_terminalGlobalBin_certified_good_schedule
    {inputLoss stickyLoss volumeLoss : ℝ}
    (hgap : inputLoss + 5 * stickyLoss / 2 < volumeLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sigma delta eta : ℝ} {logExponent : ℕ}
        {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
        {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
        {terminalSource : PureWZ2TerminalPreparedSource source terminal}
        {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
        (certifiedWindow : PureWZ2TerminalCertifiedWindow prepared)
        {line : PureWZ2HorizontalFixedLineCore
          certifiedWindow.toGraphWindow.windowed source.globalGrains.slope}
        {parentFamily : PureWZ2TerminalGlobalBinParentFamily line}
        (data : PureWZ2TerminalGlobalBinPreparedFamily
          (eta := eta) parentFamily),
        0 < delta → delta ≤ delta₀ →
          Nonempty (PureWZ2TerminalGoodGlobalBinFamily data volumeLoss) := by
  let middleLoss := (inputLoss + 5 * stickyLoss / 2 + volumeLoss) / 2
  let extraLoss := volumeLoss - middleLoss
  have hvolumeGap : inputLoss + 5 * stickyLoss / 2 < middleLoss := by
    dsimp only [middleLoss]
    linarith
  have hextraLoss : 0 < extraLoss := by
    dsimp only [extraLoss, middleLoss]
    linarith
  rcases pureWZ2_terminalExact_volume_budget_schedule hvolumeGap with
    ⟨volumeScale, hvolumeScale, hvolumeScaleOne, hvolume⟩
  rcases exists_delta₀_const_mul_rpow_le 2 (by norm_num : (0 : ℝ) < 2)
      0 extraLoss hextraLoss with
    ⟨constantScale, hconstantScale, hconstantScaleOne, hconstant⟩
  let delta₀ := min volumeScale constantScale
  refine ⟨delta₀, lt_min hvolumeScale hconstantScale,
    (min_le_left _ _).trans hvolumeScaleOne, ?_⟩
  intro sigma delta eta logExponent source terminal terminalSource prepared
    certifiedWindow line parentFamily data hdelta hdeltaSmall
  have hvolumeBudget := hvolume (sigma := sigma) hdelta
    (hdeltaSmall.trans (min_le_left _ _))
  have hconstantBudget := hconstant delta hdelta
    (hdeltaSmall.trans (min_le_right _ _))
  apply data.selectGoodBins_of_certified_budget certifiedWindow
  have hexponent : 1 + sigma / 2 + volumeLoss =
      (1 + sigma / 2 + middleLoss) + extraLoss := by
    dsimp only [middleLoss, extraLoss]
    ring
  have hconstantENN : (2 : ENNReal) *
      Kakeya.realRpowENN delta extraLoss ≤ 1 := by
    simpa [Kakeya.realRpowENN] using hconstantBudget
  calc
    2 * Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) *
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss =
        (Kakeya.realRpowENN delta (1 + sigma / 2 + middleLoss) *
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss) *
        (2 * Kakeya.realRpowENN delta extraLoss) := by
      rw [hexponent, realRpowENN_add hdelta]
      ring
    _ ≤ ((16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2)) * 1 := by
      gcongr
    _ = (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) := by simp

/-- Uniform good-bin schedule after splitting the positive exponent gap
between exact-carrier geometry and the outer height-popularity logarithm. -/
theorem pureWZ2_terminalGlobalBin_good_schedule
    {inputLoss stickyLoss volumeLoss : ℝ}
    (hgap : inputLoss + 5 * stickyLoss / 2 < volumeLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sigma delta eta : ℝ} {logExponent : ℕ}
        {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
        {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
        {terminalSource : PureWZ2TerminalPreparedSource source terminal}
        {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
        (certifiedWindow : PureWZ2TerminalCertifiedWindow prepared)
        (heightData : PureWZ2TerminalWindowHeightPopularData
          certifiedWindow.toGraphWindow)
        {line : PureWZ2HorizontalFixedLineCore
          heightData.graphWindow.windowed source.globalGrains.slope}
        {parentFamily : PureWZ2TerminalGlobalBinParentFamily line}
        (data : PureWZ2TerminalGlobalBinPreparedFamily
          (eta := eta) parentFamily),
        0 < delta → delta ≤ delta₀ →
          Nonempty (PureWZ2TerminalGoodGlobalBinFamily data volumeLoss) := by
  let baseLoss := inputLoss + 5 * stickyLoss / 2
  let middleLoss := (baseLoss + volumeLoss) / 2
  let extraLoss := volumeLoss - middleLoss
  have hvolumeGap : inputLoss + 5 * stickyLoss / 2 < middleLoss := by
    dsimp only [middleLoss, baseLoss]
    linarith
  have hextraLoss : 0 < extraLoss := by
    dsimp only [extraLoss, middleLoss, baseLoss]
    linarith
  rcases pureWZ2_terminalExact_volume_budget_schedule hvolumeGap with
    ⟨volumeScale, hvolumeScale, hvolumeScaleOne, hvolume⟩
  rcases pureWZ2_terminalHeightBins_power_schedule hextraLoss with
    ⟨logScale, hlogScale, hlogScaleOne, hlog⟩
  let delta₀ := min volumeScale logScale
  refine ⟨delta₀, lt_min hvolumeScale hlogScale,
    (min_le_left _ _).trans hvolumeScaleOne, ?_⟩
  intro sigma delta eta logExponent source terminal terminalSource prepared
    certifiedWindow heightData line parentFamily data hdelta hdeltaSmall
  have hvolumeBudget := hvolume (sigma := sigma) hdelta
    (hdeltaSmall.trans (min_le_left _ _))
  have hlogBudget := hlog heightData hdelta
    (hdeltaSmall.trans (min_le_right _ _))
  apply data.selectGoodBins_of_budget certifiedWindow heightData
  have hexponent :
      1 + sigma / 2 + volumeLoss =
        (1 + sigma / 2 + middleLoss) + extraLoss := by
    dsimp only [middleLoss, extraLoss, baseLoss]
    ring
  calc
    (4 * heightData.popular.bins : ENNReal) *
          Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) *
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss =
        (Kakeya.realRpowENN delta (1 + sigma / 2 + middleLoss) *
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss) *
        ((4 * heightData.popular.bins : ENNReal) *
          Kakeya.realRpowENN delta extraLoss) := by
      rw [hexponent, realRpowENN_add hdelta]
      ring
    _ ≤ ((16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2)) * 1 := by
      gcongr
    _ = (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) := by simp

end Kakeya.Assouad

end
