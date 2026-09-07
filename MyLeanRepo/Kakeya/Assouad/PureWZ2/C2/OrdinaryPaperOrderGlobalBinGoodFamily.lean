import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderGlobalBinVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalGoodBlocks

/-!
# Volume-good global bins in one ordinary source block

An individual global-bin fibre need not satisfy the ready-graph volume
threshold.  The legitimate order is to prepare every nonempty fibre, prove an
aggregate lower bound, and only then discard the small graph shadows.  This
module packages that last finite selection for one source block.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

def pureWZ2OrdinaryPaperOrderGoodGlobalBins
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    (family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers)
    (volumeLoss : ℝ) :
    Finset {bin // bin ∈ family.line.globalBins} :=
  Finset.univ.filter fun bin =>
    Kakeya.realRpowENN (family.prep bin).graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      volume (family.prep bin).shadow.union

/-- The good global bins in one source block retain at least half of the
aggregate graph-shadow volume. -/
structure PureWZ2OrdinaryPaperOrderGoodGlobalBinFamilyData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    (family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers)
    (volumeLoss : ℝ) where
  selected : Finset {bin // bin ∈ family.line.globalBins} :=
    pureWZ2OrdinaryPaperOrderGoodGlobalBins family volumeLoss
  selected_eq : selected =
    pureWZ2OrdinaryPaperOrderGoodGlobalBins family volumeLoss
  selected_nonempty : selected.Nonempty
  volume_lower : ∀ bin ∈ selected,
    Kakeya.realRpowENN (family.prep bin).graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      volume (family.prep bin).shadow.union
  total_volume_le :
    (∑ bin : {bin // bin ∈ family.line.globalBins},
        volume (family.prep bin).shadow.union) ≤
      2 * ∑ bin ∈ selected, volume (family.prep bin).shadow.union

/-- Select the good bins once the total bad-bin contribution in this source
block has been absorbed. -/
theorem PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData.selectGoodGlobalBins
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    (family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers)
    (hbad :
      2 * ((family.line.globalBins.card : ENNReal) *
        Kakeya.realRpowENN (256 * rho)
          (1 + sigma / 2 + volumeLoss)) ≤
      ∑ bin : {bin // bin ∈ family.line.globalBins},
        volume (family.prep bin).shadow.union) :
    Nonempty
      (PureWZ2OrdinaryPaperOrderGoodGlobalBinFamilyData
        family volumeLoss) := by
  let bins :=
    (Finset.univ : Finset {bin // bin ∈ family.line.globalBins})
  let supply : {bin // bin ∈ family.line.globalBins} → ENNReal := fun bin =>
    volume (family.prep bin).shadow.union
  let threshold := Kakeya.realRpowENN (256 * rho)
    (1 + sigma / 2 + volumeLoss)
  have hcard : bins.card = family.line.globalBins.card := by
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
    have hthresholdPos : 0 < threshold := by
      apply ENNReal.ofReal_pos.mpr
      apply Real.rpow_pos_of_pos
      have hrho : 0 < rho := family.line.rho_pos
      positivity
    have hbinsPos : 0 < (bins.card : ENNReal) := by
      have hbinsNonempty : bins.Nonempty := by
        refine ⟨⟨family.line.lineBin, family.line.lineBin_mem⟩, ?_⟩
        simp [bins]
      exact_mod_cast hbinsNonempty.card_pos
    have hleftPos : 0 < 2 * ((bins.card : ENNReal) * threshold) := by
      positivity
    exact hleftPos.trans_le (by simpa [bins, supply] using hbad')
  have hselectedNonempty : selected.Nonempty := by
    by_contra hempty
    have hselectedEmpty : selected = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hleZero : (∑ bin ∈ bins, supply bin) ≤ 0 := by
      simpa [selected, hselectedEmpty] using hhalf
    exact (not_le_of_gt htotalPos) hleZero
  exact ⟨{
    selected := selected
    selected_eq := by
      ext bin
      simp [selected, bins, supply, threshold,
        pureWZ2OrdinaryPaperOrderGoodGlobalBins,
        (family.prep bin).graphScale_eq]
    selected_nonempty := hselectedNonempty
    volume_lower := by
      intro bin hbin
      have hgood := (Finset.mem_filter.mp hbin).2
      simpa [threshold, supply, (family.prep bin).graphScale_eq] using hgood
    total_volume_le := by
      simpa [selected, bins, supply, threshold,
        (family.prep _).graphScale_eq] using hhalf
  }⟩

/-- A canonical good bin for the source block.  This choice is made only
after aggregate selection, and therefore does not reintroduce a largest-fibre
pigeonhole. -/
def PureWZ2OrdinaryPaperOrderGoodGlobalBinFamilyData.chosenBin
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    {family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers}
    (good : PureWZ2OrdinaryPaperOrderGoodGlobalBinFamilyData
      family volumeLoss) :
    {bin // bin ∈ family.line.globalBins} :=
  Classical.choose good.selected_nonempty

theorem PureWZ2OrdinaryPaperOrderGoodGlobalBinFamilyData.chosenBin_mem
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    {family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers}
    (good : PureWZ2OrdinaryPaperOrderGoodGlobalBinFamilyData
      family volumeLoss) :
    good.chosenBin ∈ good.selected :=
  Classical.choose_spec good.selected_nonempty

theorem PureWZ2OrdinaryPaperOrderGoodGlobalBinFamilyData.chosenBin_volume_lower
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    {family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers}
    (good : PureWZ2OrdinaryPaperOrderGoodGlobalBinFamilyData
      family volumeLoss) :
    Kakeya.realRpowENN (family.prep good.chosenBin).graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      volume (family.prep good.chosenBin).shadow.union :=
  good.volume_lower good.chosenBin good.chosenBin_mem

end Kakeya.Assouad

end
