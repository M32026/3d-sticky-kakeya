import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderGlobalBinGoodFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarsePreparation

/-!
# Genuine-coarse graph preparations over all ordinary global bins

The common exact source slice is partitioned into all nonempty global-bin
fibres before choosing a bin.  For each fibre, this module prepares the
genuine first-sticky coarse carrier selected by the same parents.  Thus the
aggregate coarse-volume estimate becomes an aggregate lower bound for the
actual Lemma-23 graph carriers, without identifying those carriers with the
outer-popular original-family shading.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- The genuine-coarse Lemma-23 preparation attached to every global-bin
fibre of one ordinary source block. -/
structure PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData
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
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers) where
  original : ∀ bin : {bin // bin ∈ family.line.globalBins},
    PureWZ2SourceFixedBinCoarseOriginalSlopeData
      (family.coarseCarrier bin)
      (family.fineWitnesses bin).coarseWitnesses
  prep : ∀ bin : {bin // bin ∈ family.line.globalBins},
    PureWZ2SourceFixedBinCoarsePreparationData (original bin)
  prep_shadow_union : ∀ bin, (prep bin).shadow.union =
    (family.coarseCarrier bin).shading.union

/-- Prepare the genuine coarse carrier on every global-bin fibre.  The
endpoint absorption is common to the fibres because all use the same scales
and the same original interval slope. -/
theorem PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData.prepareAllCoarseGlobalBins
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
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCge :
      (4 : ENNReal) ≤ Kakeya.realRpowENN rho (-middleLoss))
    (hendpoint :
      ENNReal.ofReal
          ((2 * (28 * twoScale.sqrtRequested.1) / rho + 2) ^ sigma *
            4 ^ (1 - sigma)) ≤
        Kakeya.realRpowENN rho (-middleLoss))
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    Nonempty
      (PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData
        family) := by
  have horiginal : ∀ bin : {bin // bin ∈ family.line.globalBins},
      Nonempty (PureWZ2SourceFixedBinCoarseOriginalSlopeData
        (family.coarseCarrier bin)
        (family.fineWitnesses bin).coarseWitnesses) := fun bin =>
    (family.coarseCarrier bin).withEndpointBudgetFixedBin
      (family.fineWitnesses bin).coarseWitnesses
      hsigma hsigmaOne hCge hendpoint hbridge
  let original : ∀ bin : {bin // bin ∈ family.line.globalBins},
      PureWZ2SourceFixedBinCoarseOriginalSlopeData
        (family.coarseCarrier bin)
        (family.fineWitnesses bin).coarseWitnesses := fun bin =>
    Classical.choice (horiginal bin)
  have hprep : ∀ bin : {bin // bin ∈ family.line.globalBins},
      ∃ prep : PureWZ2SourceFixedBinCoarsePreparationData
          (original bin),
        prep.shadow.union = (family.coarseCarrier bin).shading.union := fun bin =>
    (original bin).prepareFixedBin hgraphOne hheightAbsorb
  exact ⟨{
    original := original
    prep := fun bin => (hprep bin).choose
    prep_shadow_union := fun bin => (hprep bin).choose_spec
  }⟩

/-- The all-bin coarse-volume estimate is already an aggregate lower bound
for the actual graph shadows used by the genuine-coarse Lemma-23 route. -/
theorem PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData.aggregate_graph_volume_supply_le
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
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
    (coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family) :
    carriers.outerPopular.popularWindow.volumeSupply *
        twoScale.fine.balanced.cellMass ≤
      pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta *
        ∑ bin : {bin // bin ∈ family.line.globalBins},
          volume (coarse.prep bin).shadow.union := by
  calc
    carriers.outerPopular.popularWindow.volumeSupply *
          twoScale.fine.balanced.cellMass ≤
        pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta *
          ∑ bin : {bin // bin ∈ family.line.globalBins},
            volume (family.coarseCarrier bin).shading.union :=
      family.aggregate_coarse_volume_supply_le
    _ = pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta *
        ∑ bin : {bin // bin ∈ family.line.globalBins},
          volume (coarse.prep bin).shadow.union := by
      congr 1
      apply Finset.sum_congr rfl
      intro bin _
      rw [coarse.prep_shadow_union bin]

/-- A scaled per-block budget cancels the positive finite all-bin geometric
cost and yields the unscaled graph-volume budget used by good-bin selection. -/
theorem PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData.graph_budget_of_scaled
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
    (coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family)
    (hscaled :
      (2 * ((family.line.globalBins.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss))) *
          pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta ≤
        carriers.outerPopular.popularWindow.volumeSupply *
          twoScale.fine.balanced.cellMass) :
    2 * ((family.line.globalBins.card : ENNReal) *
        Kakeya.realRpowENN (256 * rho)
          (1 + sigma / 2 + volumeLoss)) ≤
      ∑ bin : {bin // bin ∈ family.line.globalBins},
        volume (coarse.prep bin).shadow.union := by
  let cost := pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta
  have hcostPos : 0 < cost := by
    dsimp only [cost, pureWZ2OrdinaryAllBinCoarseVolumeCost]
    have hrho : 0 < rho := family.line.rho_pos
    have hdelta : 0 < delta := source.extremal.delta_pos
    have hparent :
        0 < (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) := by
      simp [pureWZ2SourceFixedLineParentFiberBound,
        pureWZ2SourceFixedLineParentYBound]
    positivity
  have hcostTop : cost ≠ ⊤ := by
    dsimp only [cost, pureWZ2OrdinaryAllBinCoarseVolumeCost]
    repeat' apply ENNReal.mul_ne_top
    all_goals simp [Kakeya.realRpowENN]
  apply (ENNReal.mul_le_mul_iff_right hcostPos.ne' hcostTop).mp
  calc
    cost * (2 * ((family.line.globalBins.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss))) =
        (2 * ((family.line.globalBins.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss))) * cost := by ring
    _ ≤
        carriers.outerPopular.popularWindow.volumeSupply *
          twoScale.fine.balanced.cellMass := hscaled
    _ ≤ cost * ∑ bin : {bin // bin ∈ family.line.globalBins},
        volume (coarse.prep bin).shadow.union :=
      coarse.aggregate_graph_volume_supply_le

/-- Global bins whose genuine-coarse Lemma-23 graph carrier meets the ready
volume threshold. -/
def pureWZ2OrdinaryPaperOrderGoodCoarseGlobalBins
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
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
    (coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family)
    (volumeLoss : ℝ) :
    Finset {bin // bin ∈ family.line.globalBins} :=
  Finset.univ.filter fun bin =>
    Kakeya.realRpowENN (coarse.prep bin).graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      volume (coarse.prep bin).shadow.union

/-- The retained genuine-coarse bins after the honest aggregate graph-volume
pigeonhole. -/
structure PureWZ2OrdinaryPaperOrderGoodCoarseGlobalBinFamilyData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
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
    (coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family)
    (volumeLoss : ℝ) where
  selected : Finset {bin // bin ∈ family.line.globalBins} :=
    pureWZ2OrdinaryPaperOrderGoodCoarseGlobalBins coarse volumeLoss
  selected_eq : selected =
    pureWZ2OrdinaryPaperOrderGoodCoarseGlobalBins coarse volumeLoss
  selected_nonempty : selected.Nonempty
  volume_lower : ∀ bin ∈ selected,
    Kakeya.realRpowENN (coarse.prep bin).graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      volume (coarse.prep bin).shadow.union
  total_volume_le :
    (∑ bin : {bin // bin ∈ family.line.globalBins},
        volume (coarse.prep bin).shadow.union) ≤
      2 * ∑ bin ∈ selected, volume (coarse.prep bin).shadow.union

/-- Select genuine-coarse graph-good bins after the per-block scaled budget
has been discharged. -/
theorem PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData.selectGoodCoarseGlobalBins
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
    (coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family)
    (hscaled :
      (2 * ((family.line.globalBins.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss))) *
          pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta ≤
        carriers.outerPopular.popularWindow.volumeSupply *
          twoScale.fine.balanced.cellMass) :
    Nonempty
      (PureWZ2OrdinaryPaperOrderGoodCoarseGlobalBinFamilyData
        coarse volumeLoss) := by
  let bins :=
    (Finset.univ : Finset {bin // bin ∈ family.line.globalBins})
  let supply : {bin // bin ∈ family.line.globalBins} → ENNReal := fun bin =>
    volume (coarse.prep bin).shadow.union
  let threshold := Kakeya.realRpowENN (256 * rho)
    (1 + sigma / 2 + volumeLoss)
  have hbad : 2 * ((bins.card : ENNReal) * threshold) ≤
      ∑ bin ∈ bins, supply bin * 1 := by
    have h := coarse.graph_budget_of_scaled hscaled
    simpa [bins, supply, threshold] using h
  have hthresholdTop : threshold ≠ ⊤ := by
    simp [threshold, Kakeya.realRpowENN]
  have hhalf := finset_good_weighted_supply_retains_half
    bins supply 1 threshold hthresholdTop hbad
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
    exact hleftPos.trans_le (by simpa using hbad)
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
        pureWZ2OrdinaryPaperOrderGoodCoarseGlobalBins,
        (coarse.prep bin).graphScale_eq]
    selected_nonempty := hselectedNonempty
    volume_lower := by
      intro bin hbin
      have hgood := (Finset.mem_filter.mp hbin).2
      simpa [threshold, supply, (coarse.prep bin).graphScale_eq] using hgood
    total_volume_le := by
      simpa [selected, bins, supply, threshold,
        (coarse.prep _).graphScale_eq] using hhalf
  }⟩

/-- A canonical genuine-coarse good bin for one source block.  The choice is
made only after the honest all-bin graph-volume selection, and maximizes the
actual graph-shadow volume inside the retained good family. -/
def PureWZ2OrdinaryPaperOrderGoodCoarseGlobalBinFamilyData.chosenBin
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
    {coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family}
    (good : PureWZ2OrdinaryPaperOrderGoodCoarseGlobalBinFamilyData
      coarse volumeLoss) :
    {bin // bin ∈ family.line.globalBins} :=
  Classical.choose (Finset.exists_max_image good.selected
    (fun bin => volume (coarse.prep bin).shadow.union)
    good.selected_nonempty)

theorem PureWZ2OrdinaryPaperOrderGoodCoarseGlobalBinFamilyData.chosenBin_mem
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
    {coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family}
    (good : PureWZ2OrdinaryPaperOrderGoodCoarseGlobalBinFamilyData
      coarse volumeLoss) :
    good.chosenBin ∈ good.selected :=
  (Classical.choose_spec (Finset.exists_max_image good.selected
    (fun bin => volume (coarse.prep bin).shadow.union)
    good.selected_nonempty)).1

/-- The canonical good bin dominates every other retained good bin in actual
graph-shadow volume. -/
theorem PureWZ2OrdinaryPaperOrderGoodCoarseGlobalBinFamilyData.volume_le_chosenBin
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
    {coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family}
    (good : PureWZ2OrdinaryPaperOrderGoodCoarseGlobalBinFamilyData
      coarse volumeLoss)
    (bin : {bin // bin ∈ family.line.globalBins})
    (hbin : bin ∈ good.selected) :
    volume (coarse.prep bin).shadow.union ≤
      volume (coarse.prep good.chosenBin).shadow.union :=
  (Classical.choose_spec (Finset.exists_max_image good.selected
    (fun bin => volume (coarse.prep bin).shadow.union)
    good.selected_nonempty)).2 bin hbin

/-- The complete all-bin graph volume is controlled by the canonical retained
bin, paying only the explicit number of global bins and the factor two from
discarding sub-threshold bins. -/
theorem PureWZ2OrdinaryPaperOrderGoodCoarseGlobalBinFamilyData.total_volume_le_chosenBin
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
    {coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family}
    (good : PureWZ2OrdinaryPaperOrderGoodCoarseGlobalBinFamilyData
      coarse volumeLoss) :
    (∑ bin : {bin // bin ∈ family.line.globalBins},
        volume (coarse.prep bin).shadow.union) ≤
      2 * (family.line.globalBins.card : ENNReal) *
        volume (coarse.prep good.chosenBin).shadow.union := by
  have hselected :
      (∑ bin ∈ good.selected, volume (coarse.prep bin).shadow.union) ≤
        (good.selected.card : ENNReal) *
          volume (coarse.prep good.chosenBin).shadow.union := by
    have hsum := Finset.sum_le_card_nsmul good.selected
      (fun bin => volume (coarse.prep bin).shadow.union)
      (volume (coarse.prep good.chosenBin).shadow.union)
      (fun bin hbin => good.volume_le_chosenBin bin hbin)
    simpa [nsmul_eq_mul] using hsum
  have hcard : (good.selected.card : ENNReal) ≤
      (family.line.globalBins.card : ENNReal) := by
    have hcardNat : good.selected.card ≤ family.line.globalBins.card := by
      simpa using Finset.card_le_univ good.selected
    exact_mod_cast hcardNat
  calc
    (∑ bin : {bin // bin ∈ family.line.globalBins},
        volume (coarse.prep bin).shadow.union) ≤
      2 * ∑ bin ∈ good.selected,
        volume (coarse.prep bin).shadow.union := good.total_volume_le
    _ ≤ 2 * ((good.selected.card : ENNReal) *
        volume (coarse.prep good.chosenBin).shadow.union) := by gcongr
    _ ≤ 2 * (family.line.globalBins.card : ENNReal) *
        volume (coarse.prep good.chosenBin).shadow.union := by
      calc
        _ ≤ 2 * ((family.line.globalBins.card : ENNReal) *
            volume (coarse.prep good.chosenBin).shadow.union) := by gcongr
        _ = _ := by ring

theorem PureWZ2OrdinaryPaperOrderGoodCoarseGlobalBinFamilyData.chosenBin_volume_lower
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
    {coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family}
    (good : PureWZ2OrdinaryPaperOrderGoodCoarseGlobalBinFamilyData
      coarse volumeLoss) :
    Kakeya.realRpowENN (coarse.prep good.chosenBin).graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      volume (coarse.prep good.chosenBin).shadow.union :=
  good.volume_lower good.chosenBin good.chosenBin_mem

end Kakeya.Assouad

end
