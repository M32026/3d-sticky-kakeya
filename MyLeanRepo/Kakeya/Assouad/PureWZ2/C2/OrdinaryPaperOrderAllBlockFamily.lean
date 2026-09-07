import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.BalancedSafeWindowBlocks
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderRichGraph
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalBlockResidue

/-!
# Paper-order ordinary carriers on every balanced safe block

The selected safe phase is kept as a finite family of genuine `sqrt rho`
source windows.  On every window we first perform source-volume height
popularity, then select the exact original-source slice and its `f(z₀)` fixed
line.  Only afterwards is the restricted Lemma-23 graph preparation built.

The source window is a type index of the local carrier.  Thus the family
cannot silently replace a retained block by an unrelated window while passing
to the graph-facing interface.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Paper-ordered carrier data on every retained balanced safe block. -/
structure PureWZ2OrdinaryPaperOrderAllBlockCarrierData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (safe : PureWZ2BalancedSafeBlockFamilyData prepared) where
  carrier : ∀ block : {block // block ∈ safe.blocks},
    PureWZ2OrdinaryPaperOrderCarrierAtWindowData
      (safe.blockWindow block).window

namespace PureWZ2OrdinaryPaperOrderAllBlockCarrierData

/-- Forget the external index only at the old graph interface.  The chosen
source window remains definitionally the window belonging to `block`. -/
def carrierData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
    (block : {block // block ∈ safe.blocks}) :
    PureWZ2OrdinaryPaperOrderCarrierData twoScale :=
  (family.carrier block).toCarrierData

@[simp] theorem carrierData_sourceWindow
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
    (block : {block // block ∈ safe.blocks}) :
    (family.carrierData block).sourceWindow =
      (safe.blockWindow block).window := rfl

end PureWZ2OrdinaryPaperOrderAllBlockCarrierData

/-- Run the literal pre-graph carrier construction on every safe block. -/
theorem PureWZ2BalancedSafeBlockFamilyData.ordinaryPaperOrderCarriers
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (safe : PureWZ2BalancedSafeBlockFamilyData prepared) :
    Nonempty (PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe) := by
  have hcarrier : ∀ block : {block // block ∈ safe.blocks},
      Nonempty (PureWZ2OrdinaryPaperOrderCarrierAtWindowData
        (safe.blockWindow block).window) := fun block =>
    (safe.blockWindow block).window.ordinaryPaperOrderCarriers
  exact ⟨{
    carrier := fun block => Classical.choice (hcarrier block)
  }⟩

/-- The exact-slice graph preparation on every already paper-ordered block. -/
structure PureWZ2OrdinaryPaperOrderAllBlockPreparationData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe) where
  graphPreparation : ∀ block : {block // block ∈ safe.blocks},
    PureWZ2OrdinaryPaperOrderPreparationData (family.carrierData block)

/-- Rebuild all dependent graph witnesses only after each block has performed
its own source-volume popularity and exact fixed-line choice. -/
theorem PureWZ2OrdinaryPaperOrderAllBlockCarrierData.prepareAllBlocks
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    Nonempty
      (PureWZ2OrdinaryPaperOrderAllBlockPreparationData family) := by
  have hpreparation : ∀ block : {block // block ∈ safe.blocks},
      Nonempty (PureWZ2OrdinaryPaperOrderPreparationData
        (family.carrierData block)) := fun block =>
    (family.carrierData block).prepareGraph
      hbridge hgraphOne hheightAbsorb
  exact ⟨{
    graphPreparation := fun block =>
      Classical.choice (hpreparation block)
  }⟩

/-- Sum the literal `Z_S` popularity and fixed-line/Fubini estimates over the
safe block family.  This is the last aggregate estimate before transporting
the selected genuine coarse carriers back to the exact outer-popular
original-family graph shadows. -/
theorem PureWZ2OrdinaryPaperOrderAllBlockCarrierData.aggregate_source_to_coarse_volume_supply
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe) :
    volume prepared.shadow.union * twoScale.fine.balanced.cellMass ≤
      2 * ∑ block : {block // block ∈ safe.blocks},
        (2 * (family.carrierData block).outerPopular.popular.bins : ℕ) *
          (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
            volume (family.carrierData block).coarseCarrier.shading.union) := by
  have hlocal : ∀ block : {block // block ∈ safe.blocks},
      volume (safe.blockWindow block).shading.union *
            twoScale.fine.balanced.cellMass ≤
        (2 * (family.carrierData block).outerPopular.popular.bins : ℕ) *
          (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
            volume (family.carrierData block).coarseCarrier.shading.union) := by
    intro block
    have hsupply := (family.carrierData block).source_to_coarse_volume_supply
    change volume (safe.blockWindow block).window.shading.union *
          twoScale.fine.balanced.cellMass ≤ _ at hsupply
    rw [(safe.blockWindow block).window_shading] at hsupply
    exact hsupply
  calc
    volume prepared.shadow.union * twoScale.fine.balanced.cellMass ≤
        (2 * ∑ block : {block // block ∈ safe.blocks},
          volume (safe.blockWindow block).shading.union) *
            twoScale.fine.balanced.cellMass := by
      gcongr
      exact safe.volume_half
    _ = 2 * ∑ block : {block // block ∈ safe.blocks},
        volume (safe.blockWindow block).shading.union *
          twoScale.fine.balanced.cellMass := by
      rw [mul_assoc, Finset.sum_mul]
    _ ≤ 2 * ∑ block : {block // block ∈ safe.blocks},
        (2 * (family.carrierData block).outerPopular.popular.bins : ℕ) *
          (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
            volume (family.carrierData block).coarseCarrier.shading.union) := by
      exact mul_le_mul_left' (Finset.sum_le_sum fun block _ => hlocal block) 2

/-- The blocks whose actual outer-popular original-family graph shadows meet
the common ready-graph volume threshold. -/
def pureWZ2OrdinaryPaperOrderGoodGraphBlocks
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    (all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family)
    (volumeLoss : ℝ) : Finset {block // block ∈ safe.blocks} :=
  safe.blocks.attach.filter fun block =>
    Kakeya.realRpowENN
        (all.graphPreparation block).prep.graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      volume (all.graphPreparation block).prep.shadow.union

theorem pureWZ2OrdinaryPaperOrderGoodGraphBlocks_volume_lower
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    {block : {block // block ∈ safe.blocks}}
    (hblock : block ∈
      pureWZ2OrdinaryPaperOrderGoodGraphBlocks all volumeLoss) :
    Kakeya.realRpowENN
        (all.graphPreparation block).prep.graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      volume (all.graphPreparation block).prep.shadow.union :=
  (Finset.mem_filter.mp hblock).2

/-- Graph-volume popularity retains half of the actual paper-order graph
shadows once the total bad-block contribution has been absorbed. -/
theorem PureWZ2OrdinaryPaperOrderAllBlockPreparationData.goodGraphBlocks_retains_half
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    (all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family)
    (hbad :
      2 * ((safe.blocks.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) ≤
        ∑ block : {block // block ∈ safe.blocks},
          volume (all.graphPreparation block).prep.shadow.union) :
    (∑ block : {block // block ∈ safe.blocks},
        volume (all.graphPreparation block).prep.shadow.union) ≤
      2 * ∑ block ∈
          pureWZ2OrdinaryPaperOrderGoodGraphBlocks all volumeLoss,
        volume (all.graphPreparation block).prep.shadow.union := by
  let blocks := safe.blocks.attach
  let supply : {block // block ∈ safe.blocks} → ENNReal := fun block =>
    volume (all.graphPreparation block).prep.shadow.union
  let threshold := Kakeya.realRpowENN (256 * rho)
    (1 + sigma / 2 + volumeLoss)
  have hthresholdTop : threshold ≠ ⊤ := by
    simp [threshold, Kakeya.realRpowENN]
  have hbad' : 2 * ((blocks.card : ENNReal) * threshold) ≤
      ∑ block ∈ blocks, supply block * 1 := by
    simpa [blocks, supply, threshold] using hbad
  have hhalf := finset_good_weighted_supply_retains_half
    blocks supply 1 threshold hthresholdTop hbad'
  simpa [blocks, supply, threshold,
    pureWZ2OrdinaryPaperOrderGoodGraphBlocks,
    (all.graphPreparation _).prep.graphScale_eq] using hhalf

theorem PureWZ2OrdinaryPaperOrderAllBlockPreparationData.goodGraphBlocks_nonempty
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    (all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family)
    (hbad :
      2 * ((safe.blocks.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) ≤
        ∑ block : {block // block ∈ safe.blocks},
          volume (all.graphPreparation block).prep.shadow.union) :
    (pureWZ2OrdinaryPaperOrderGoodGraphBlocks all volumeLoss).Nonempty := by
  have hhalf := all.goodGraphBlocks_retains_half hbad
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hblocks : 0 < (safe.blocks.card : ENNReal) := by
    exact_mod_cast safe.blocks_nonempty.card_pos
  have hthreshold : 0 < Kakeya.realRpowENN (256 * rho)
      (1 + sigma / 2 + volumeLoss) :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)
  have htotalPos : 0 < ∑ block : {block // block ∈ safe.blocks},
      volume (all.graphPreparation block).prep.shadow.union :=
    (ENNReal.mul_pos (by norm_num)
      (ENNReal.mul_pos hblocks.ne' hthreshold.ne').ne').trans_le hbad
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hhalf
  simp only [Finset.sum_empty, mul_zero] at hhalf
  exact (not_le_of_gt htotalPos) hhalf

/-- The finite family obtained after graph-volume popularity, the finite
Lemma-23 graph, `Z_popular`, and `Z_lin`, all on the original source family. -/
structure PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    (all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family)
    (volumeLoss : ℝ) where
  indexCount : ℕ
  indexCount_pos : 0 < indexCount
  safeBlock : Fin indexCount → {block // block ∈ safe.blocks}
  safeBlock_injective : Function.Injective safeBlock
  block_mem : ∀ index, safeBlock index ∈
    pureWZ2OrdinaryPaperOrderGoodGraphBlocks all volumeLoss
  block_surjective : ∀ block ∈
    pureWZ2OrdinaryPaperOrderGoodGraphBlocks all volumeLoss,
      ∃ index, safeBlock index = block
  graphData : ∀ index, PureWZ2OrdinaryPaperOrderGraphData
    (normalEta := normalEta) (all.graphPreparation (safeBlock index))
  rich : ∀ index, PureWZ2OrdinaryPaperOrderRichGraphData
    (finalLoss := finalLoss) (theoremEta := theoremEta) (graphData index)

/-- Run the paper-ordered graph and its two post-graph height selections on
every graph-volume-good block. -/
theorem PureWZ2OrdinaryPaperOrderAllBlockPreparationData.buildGraphGoodBlocks
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    (all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hfinal : 0 < finalLoss) (hfinalOne : finalLoss < 1)
    (hfinalSigma : finalLoss / 2 < sigma)
    (hnormalEta : 0 < normalEta) (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (hlocalizationAbsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hCOne :
      (1 : ENNReal) ≤ 10 * Kakeya.realRpowENN delta (-inputLoss))
    (hCpower : ∀ block : {block // block ∈ safe.blocks},
      (10 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
        Real.rpow (all.graphPreparation block).prep.graphScale
          (-constantLoss))
    (hextraPower : ∀ block : {block // block ∈ safe.blocks},
      ∀ graphData : PureWZ2OrdinaryPaperOrderGraphData
          (normalEta := normalEta) (all.graphPreparation block),
        (graphData.graph.residue.extraCost : ℝ) ≤
          Real.rpow (all.graphPreparation block).prep.graphScale (-extraLoss))
    (hedgeAbsorb : ∀ block : {block // block ∈ safe.blocks},
      Real.rpow (wz1Lemma23Theorem22Scale
          (all.graphPreparation block).prep.graphScale) (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow (all.graphPreparation block).prep.graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss))
    (hKatzTao : ∀ block : {block // block ∈ safe.blocks},
      (4 : ENNReal) ≤ Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale
          (all.graphPreparation block).prep.graphScale) (-theoremEta))
    (hprojection : ∀ block : {block // block ∈ safe.blocks},
      ∀ graphData : PureWZ2OrdinaryPaperOrderGraphData
          (normalEta := normalEta) (all.graphPreparation block),
        ∀ data : PureWZ2SourceHorizontalReadyGraph
          (theoremEta := theoremEta) graphData.sharp,
          WZ1Proposition8_9AlternativeAUnion
            data.ready.deltaGraph finalLoss
            data.common.F data.common.G₁ data.common.G₁)
    (hscaleOne : 5 * (256 * rho) ≤ 1)
    (hlengthLower :
      Real.rpow (5 * (256 * rho)) (1 / 2 + finalLoss) ≤
        twoScale.sqrtRequested.1)
    (hgoodNonempty :
      (pureWZ2OrdinaryPaperOrderGoodGraphBlocks all volumeLoss).Nonempty) :
    Nonempty (PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss) := by
  let good := pureWZ2OrdinaryPaperOrderGoodGraphBlocks all volumeLoss
  let goodEquiv := good.equivFin
  let safeBlock : Fin good.card → {block // block ∈ safe.blocks} :=
    fun index => (goodEquiv.symm index).1
  have hblockMem : ∀ index, safeBlock index ∈ good := fun index =>
    (goodEquiv.symm index).2
  have hblockInjective : Function.Injective safeBlock := by
    intro first second heq
    apply goodEquiv.symm.injective
    exact Subtype.ext heq
  have hlocal : ∀ index : Fin good.card,
      ∃ graphData : PureWZ2OrdinaryPaperOrderGraphData
          (normalEta := normalEta) (all.graphPreparation (safeBlock index)),
        Nonempty (PureWZ2OrdinaryPaperOrderRichGraphData
          (finalLoss := finalLoss) (theoremEta := theoremEta) graphData) := by
    intro index
    apply (all.graphPreparation (safeBlock index)).buildRichGraphOfVolumeLower
      hbridge hsigma hsigmaOne hfinal hfinalOne hfinalSigma
      hnormalEta hnormalEtaSigma hcertificateOne hsourceFloor hlocalPower
      hglobalPower hPlanarSmall hrootSmall20 hlocalizationAbsorb hCOne
      (hCpower (safeBlock index))
      (pureWZ2OrdinaryPaperOrderGoodGraphBlocks_volume_lower
        (hblockMem index))
      (hextraPower (safeBlock index)) (hedgeAbsorb (safeBlock index))
      (hKatzTao (safeBlock index)) (hprojection (safeBlock index))
    · simpa [(all.graphPreparation (safeBlock index)).prep.graphScale_eq]
        using hscaleOne
    · simpa [(all.graphPreparation (safeBlock index)).prep.graphScale_eq]
        using hlengthLower
  let graphData : ∀ index : Fin good.card,
      PureWZ2OrdinaryPaperOrderGraphData
        (normalEta := normalEta) (all.graphPreparation (safeBlock index)) :=
    fun index => Classical.choose (hlocal index)
  let rich : ∀ index : Fin good.card,
      PureWZ2OrdinaryPaperOrderRichGraphData
        (finalLoss := finalLoss) (theoremEta := theoremEta)
          (graphData index) :=
    fun index => Classical.choice (Classical.choose_spec (hlocal index))
  exact ⟨{
    indexCount := good.card
    indexCount_pos := Finset.card_pos.mpr hgoodNonempty
    safeBlock := safeBlock
    safeBlock_injective := hblockInjective
    block_mem := hblockMem
    block_surjective := by
      intro target htarget
      let index := goodEquiv ⟨target, htarget⟩
      refine ⟨index, ?_⟩
      change (goodEquiv.symm index).1 = target
      simp [index]
    graphData := graphData
    rich := rich
  }⟩

namespace PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData

private lemma ordinaryPaperOrderResidue_separated
    {first second : ℤ}
    (hne : first ≠ second)
    (hmod : first % (64 : ℤ) = second % (64 : ℤ)) :
    (64 : ℤ) ≤ |first - second| := by
  have hzero : (first - second) % (64 : ℤ) = 0 := by
    rw [Int.sub_emod, hmod]
    simp
  have hdiv : (64 : ℤ) ∣ first - second := by
    rwa [Int.dvd_iff_emod_eq_zero]
  exact Int.le_abs_of_dvd (sub_ne_zero.mpr hne) hdiv

/-- Sum the proved original-family source-mass lower bound over every retained
paper-order block. -/
theorem aggregate_source_mass_lower
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    (data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss) :
    ∑ index : Fin data.indexCount,
        (twoScale.coarse.fineMultiplicity : ENNReal) *
          (((data.rich index).rich.heightIndices.card : ENNReal) *
            (family.carrierData
              (data.safeBlock index)).outerPopular.popular.layerMass) ≤
      3 * ∑ index : Fin data.indexCount,
        (data.rich index).heightLift.shading.mass := by
  calc
    _ ≤ ∑ index : Fin data.indexCount,
        3 * (data.rich index).heightLift.shading.mass :=
      Finset.sum_le_sum fun index _ => (data.rich index).source_mass_lower
    _ = 3 * ∑ index : Fin data.indexCount,
        (data.rich index).heightLift.shading.mass := by
      rw [Finset.mul_sum]

/-- The exact popular source window used by a retained block has the same
left endpoint as that block's balanced-safe window. -/
theorem popularWindow_left_eq
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    (data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss)
    (index : Fin data.indexCount) :
    (family.carrierData
        (data.safeBlock index)).outerPopular.popularWindow.left =
      pureWZ2SourceCarrierBlockLeft rho (data.safeBlock index).1 +
        pureWZ2BalancedWindowPhaseShift rho safe.phase := by
  rw [(family.carrierData
      (data.safeBlock index)).outerPopular.popularWindow_left]
  rw [family.carrierData_sourceWindow]
  rw [(safe.blockWindow (data.safeBlock index)).window_left]
  rfl

/-- Paper-order rich trapezoid cores coming from two same-phase blocks whose
indices differ by at least 64 are separated at the public output scale. -/
theorem rich_cores_separated_of_block_gap
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    (data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss)
    (first second : Fin data.indexCount)
    (hblocks : (64 : ℤ) ≤
      |(data.safeBlock first).1 - (data.safeBlock second).1|) :
    ∀ z ∈ (data.rich first).richTrapezoid.trapezoid.core,
      ∀ w ∈ (data.rich second).richTrapezoid.trapezoid.core,
        Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) ≤ |z - w| := by
  have hrho : 0 < rho :=
    (family.carrierData (data.safeBlock first)).line.rho_pos
  let root := Real.sqrt rho
  have hroot : 0 < root := Real.sqrt_pos.mpr hrho
  have hscale := pureWZ2SourceHorizontalFinalScale_sqrt_le hrho
  intro z hz w hw
  have hzWindow := (data.rich first).richTrapezoid.core_height_window z hz
  have hwWindow := (data.rich second).richTrapezoid.core_height_window w hw
  rw [data.popularWindow_left_eq first] at hzWindow
  rw [data.popularWindow_left_eq second] at hwWindow
  simp only [pureWZ2SourceCarrierBlockLeft] at hzWindow hwWindow
  by_cases horder : (data.safeBlock first).1 < (data.safeBlock second).1
  · have hdiffInt : (64 : ℤ) ≤
        (data.safeBlock second).1 - (data.safeBlock first).1 := by
      rw [abs_of_nonpos (sub_nonpos.mpr horder.le)] at hblocks
      simpa using hblocks
    have hdiffReal : (64 : ℝ) ≤
        (data.safeBlock second).1 - (data.safeBlock first).1 := by
      exact_mod_cast hdiffInt
    have hwz : 59 * root ≤ w - z := by
      dsimp only [root] at hroot ⊢
      nlinarith [hzWindow.2, hwWindow.1]
    have hwzNonneg : 0 ≤ w - z :=
      (mul_pos (by norm_num) hroot).le.trans hwz
    rw [abs_sub_comm, abs_of_nonneg hwzNonneg]
    exact hscale.trans (by
      dsimp only [root] at hwz ⊢
      nlinarith [Real.sqrt_pos.mpr hrho])
  · have hreverse : (data.safeBlock second).1 <
        (data.safeBlock first).1 := by
      have hne : (data.safeBlock first).1 ≠
          (data.safeBlock second).1 := by
        intro heq
        rw [heq, sub_self, abs_zero] at hblocks
        norm_num at hblocks
      omega
    have hdiffInt : (64 : ℤ) ≤
        (data.safeBlock first).1 - (data.safeBlock second).1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hreverse.le)] at hblocks
      exact hblocks
    have hdiffReal : (64 : ℝ) ≤
        (data.safeBlock first).1 - (data.safeBlock second).1 := by
      exact_mod_cast hdiffInt
    have hzw : 59 * root ≤ z - w := by
      dsimp only [root] at hroot ⊢
      nlinarith [hzWindow.1, hwWindow.2]
    have hzwNonneg : 0 ≤ z - w :=
      (mul_pos (by norm_num) hroot).le.trans hzw
    rw [abs_of_nonneg hzwNonneg]
    exact hscale.trans (by
      dsimp only [root] at hzw ⊢
      nlinarith [Real.sqrt_pos.mpr hrho])

/-- A mod-64 subfamily of paper-order block outputs. -/
structure PureWZ2OrdinaryPaperOrderBlockResidueData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    (data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss) where
  residue : Fin 64
  selected : Finset (Fin data.indexCount)
  selected_eq : selected = Finset.univ.filter fun index =>
    ((data.safeBlock index).1 % (64 : ℤ)).toNat = residue
  selected_nonempty : selected.Nonempty
  selectedIndex : Fin selected.card → Fin data.indexCount
  selectedIndex_mem : ∀ index, selectedIndex index ∈ selected
  selectedIndex_injective : Function.Injective selectedIndex
  selectedIndex_surjective : ∀ index ∈ selected,
    ∃ selectedIndexValue, selectedIndex selectedIndexValue = index
  total_mass_le :
    (∑ index : Fin data.indexCount,
        (data.rich index).heightLift.shading.mass) ≤
      64 * ∑ index : Fin selected.card,
        (data.rich (selectedIndex index)).heightLift.shading.mass
  separated_cores :
    ∀ first second : Fin selected.card, first ≠ second →
      ∀ z ∈ (data.rich (selectedIndex first)).richTrapezoid.trapezoid.core,
        ∀ w ∈ (data.rich
            (selectedIndex second)).richTrapezoid.trapezoid.core,
          Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) ≤ |z - w|

/-- Select the mass-heavy residue class only after every local paper-order
graph has reached its `Z_lin` source-family output. -/
theorem selectResidue
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    (data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss) :
    Nonempty (PureWZ2OrdinaryPaperOrderBlockResidueData data) := by
  let label : Fin data.indexCount → Fin 64 := fun index =>
    ⟨((data.safeBlock index).1 % (64 : ℤ)).toNat, by
      have hnonneg : 0 ≤ (data.safeBlock index).1 % (64 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      have hlt : (data.safeBlock index).1 % (64 : ℤ) < (64 : ℤ) :=
        Int.emod_lt_of_pos _ (by norm_num)
      omega⟩
  let weight : Fin data.indexCount → ENNReal := fun index =>
    (data.rich index).heightLift.shading.mass
  rcases finset_ennreal_weighted_pigeonhole (n := 64) (by norm_num)
      Finset.univ weight label with ⟨residue, hretained⟩
  let selected := Finset.univ.filter fun index =>
    ((data.safeBlock index).1 % (64 : ℤ)).toNat = (residue : ℕ)
  have hretained' :
      (∑ index : Fin data.indexCount, weight index) ≤
        64 * ∑ index ∈ selected, weight index := by
    simpa [selected, label, Fin.ext_iff] using hretained
  have hweightPos : ∀ index : Fin data.indexCount, 0 < weight index := by
    intro index
    dsimp only [weight]
    have hmult : 0 < (twoScale.coarse.fineMultiplicity : ENNReal) := by
      exact_mod_cast twoScale.coarse.fineMultiplicity_pos
    have hheight : 0 <
        (((data.rich index).rich.heightIndices.card : ENNReal)) := by
      exact_mod_cast (data.rich index).rich.heightIndices_card.trans_gt
        (data.rich index).rich.richF_nonempty.card_pos
    have hlayer : 0 <
        (family.carrierData
          (data.safeBlock index)).outerPopular.popular.layerMass :=
      (family.carrierData
        (data.safeBlock index)).outerPopular.popular.layerMass_pos
    have hraw : 0 < (twoScale.coarse.fineMultiplicity : ENNReal) *
        (((data.rich index).rich.heightIndices.card : ENNReal) *
          (family.carrierData
            (data.safeBlock index)).outerPopular.popular.layerMass) :=
      ENNReal.mul_pos hmult.ne'
        (ENNReal.mul_pos hheight.ne' hlayer.ne').ne'
    have htriple : 0 <
        3 * (data.rich index).heightLift.shading.mass :=
      hraw.trans_le (data.rich index).source_mass_lower
    exact (ENNReal.mul_pos_iff.mp htriple).2
  have htotalPos : 0 < ∑ index : Fin data.indexCount, weight index := by
    let first : Fin data.indexCount := ⟨0, data.indexCount_pos⟩
    exact (hweightPos first).trans_le
      (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ first))
  have hselectedNonempty : selected.Nonempty := by
    by_contra hempty
    have hselectedEmpty : selected = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hzero : ∑ index ∈ selected, weight index = 0 := by
      simp [hselectedEmpty]
    have hleZero : (∑ index : Fin data.indexCount, weight index) ≤ 0 := by
      simpa [hzero] using hretained'
    exact (not_le_of_gt htotalPos) hleZero
  let selectedEquiv := selected.equivFin
  let selectedIndex : Fin selected.card → Fin data.indexCount := fun index =>
    (selectedEquiv.symm index).1
  have hselectedIndexMem : ∀ index, selectedIndex index ∈ selected :=
    fun index => (selectedEquiv.symm index).2
  have hselectedIndexInjective : Function.Injective selectedIndex := by
    intro first second heq
    apply selectedEquiv.symm.injective
    exact Subtype.ext heq
  have hselectedIndexSurjective : ∀ index ∈ selected,
      ∃ selectedIndexValue, selectedIndex selectedIndexValue = index := by
    intro index hindex
    let selectedValue : {index // index ∈ selected} := ⟨index, hindex⟩
    exact ⟨selectedEquiv selectedValue, by
      change (selectedEquiv.symm (selectedEquiv selectedValue)).1 = index
      simp [selectedValue]⟩
  have hmass : (∑ index : Fin data.indexCount,
        (data.rich index).heightLift.shading.mass) ≤
      64 * ∑ index : Fin selected.card,
        (data.rich (selectedIndex index)).heightLift.shading.mass := by
    have hselectedSum :
        (∑ index ∈ selected, weight index) =
          ∑ index : Fin selected.card, weight (selectedIndex index) := by
      symm
      apply Finset.sum_bij (fun index _ => selectedIndex index)
      · exact fun index _ => hselectedIndexMem index
      · exact fun first _ second _ heq => hselectedIndexInjective heq
      · intro index hindex
        rcases hselectedIndexSurjective index hindex with ⟨value, hvalue⟩
        exact ⟨value, Finset.mem_univ value, hvalue⟩
      · intro _ _
        rfl
    calc
      (∑ index : Fin data.indexCount,
          (data.rich index).heightLift.shading.mass) =
          ∑ index : Fin data.indexCount, weight index := rfl
      _ ≤ 64 * ∑ index ∈ selected, weight index := hretained'
      _ = 64 * ∑ index : Fin selected.card,
          (data.rich (selectedIndex index)).heightLift.shading.mass := by
        rw [hselectedSum]
  have hseparated :
      ∀ first second : Fin selected.card, first ≠ second →
        ∀ z ∈ (data.rich
            (selectedIndex first)).richTrapezoid.trapezoid.core,
          ∀ w ∈ (data.rich
              (selectedIndex second)).richTrapezoid.trapezoid.core,
            Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) ≤ |z - w| := by
    intro first second hne
    have hsourceNe : selectedIndex first ≠ selectedIndex second := by
      intro heq
      exact hne (hselectedIndexInjective heq)
    have hblockNe : (data.safeBlock (selectedIndex first)).1 ≠
        (data.safeBlock (selectedIndex second)).1 := by
      intro heq
      exact hsourceNe (data.safeBlock_injective (Subtype.ext heq))
    have hsameResidue :
        (data.safeBlock (selectedIndex first)).1 % (64 : ℤ) =
          (data.safeBlock (selectedIndex second)).1 % (64 : ℤ) := by
      have hfirst :=
        (Finset.mem_filter.mp (hselectedIndexMem first)).2
      have hsecond :=
        (Finset.mem_filter.mp (hselectedIndexMem second)).2
      have hfirstCast := congrArg (fun value : ℕ => (value : ℤ)) hfirst
      have hsecondCast := congrArg (fun value : ℕ => (value : ℤ)) hsecond
      have hfirstNonneg : 0 ≤
          (data.safeBlock (selectedIndex first)).1 % (64 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      have hsecondNonneg : 0 ≤
          (data.safeBlock (selectedIndex second)).1 % (64 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      simpa [label, Int.toNat_of_nonneg hfirstNonneg,
        Int.toNat_of_nonneg hsecondNonneg] using hfirstCast.trans hsecondCast.symm
    have hgap := ordinaryPaperOrderResidue_separated hblockNe hsameResidue
    exact data.rich_cores_separated_of_block_gap
      (selectedIndex first) (selectedIndex second) hgap
  exact ⟨{
    residue := residue
    selected := selected
    selected_eq := rfl
    selected_nonempty := hselectedNonempty
    selectedIndex := selectedIndex
    selectedIndex_mem := hselectedIndexMem
    selectedIndex_injective := hselectedIndexInjective
    selectedIndex_surjective := hselectedIndexSurjective
    total_mass_le := hmass
    separated_cores := hseparated
  }⟩

end PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData

end Kakeya.Assouad

end
