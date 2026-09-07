import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.BalancedSafeWindowBlocks
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderAllBlockFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseRichPipeline
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalGoodBlocks

/-!
# Genuine-coarse Lemma-24 graph on every safe source window

Each source window first performs the paper's outer `Z_S` selection and
fixed-line choice.  Its graph is then built on the corresponding genuine
first-sticky coarse carrier, using the original source slope throughout.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

structure PureWZ2SourceFixedLineCoarseAllBlockData
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe) where
  pipeline : ∀ block : {block // block ∈ safe.blocks},
    PureWZ2SourceFixedLineCoarsePipelineData
      (normalEta := normalEta) (family.carrierData block)

theorem PureWZ2OrdinaryPaperOrderAllBlockCarrierData.prepareAllCoarseBlocks
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hnormalEta : 0 < normalEta)
    (hnormalEtaSigma : 4 * normalEta < sigma)
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
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1)
    (hCge :
      (4 : ENNReal) ≤ Kakeya.realRpowENN rho (-middleLoss))
    (hendpoint :
      ENNReal.ofReal
          ((2 * (28 * twoScale.sqrtRequested.1) / rho + 2) ^ sigma *
            4 ^ (1 - sigma)) ≤
        Kakeya.realRpowENN rho (-middleLoss))
    (hlocalConstant :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * Kakeya.realRpowENN rho (-middleLoss))) :
    Nonempty (PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family) := by
  have hpipeline : ∀ block : {block // block ∈ safe.blocks},
      Nonempty (PureWZ2SourceFixedLineCoarsePipelineData
        (normalEta := normalEta) (family.carrierData block)) := fun block =>
    (family.carrierData block).coarseGraphPipeline hbridge hsigma hsigmaOne
      hnormalEta hnormalEtaSigma hcertificateOne hsourceFloor hlocalPower
      hglobalPower hPlanarSmall hrootSmall20 hlocalizationAbsorb hgraphOne
      hheightAbsorb hCge hendpoint hlocalConstant
  exact ⟨{ pipeline := fun block => Classical.choice (hpipeline block) }⟩

/-- Production all-block constructor.  Every dependent carrier is prepared
from the exact global AD data of the same intermediate coarse refinement, so
there is neither an endpoint-diameter hypothesis nor a source-slab AD input. -/
theorem PureWZ2OrdinaryPaperOrderAllBlockCarrierData.prepareAllCoarseBlocksFromCoarseGlobalGrains
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hnormalEta : 0 < normalEta)
    (hnormalEtaSigma : 4 * normalEta < sigma)
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
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1)
    (hlocalConstant :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * Kakeya.realRpowENN rho (-middleLoss))) :
    Nonempty (PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family) := by
  have hpipeline : ∀ block : {block // block ∈ safe.blocks},
      Nonempty (PureWZ2SourceFixedLineCoarsePipelineData
        (normalEta := normalEta) (family.carrierData block)) := fun block =>
    (family.carrierData block).coarseGraphPipelineFromCoarseGlobalGrains
      hbridge hsigma hsigmaOne hnormalEta hnormalEtaSigma hcertificateOne
      hsourceFloor hlocalPower hglobalPower hPlanarSmall hrootSmall20
      hlocalizationAbsorb hgraphOne hheightAbsorb hlocalConstant
  exact ⟨{ pipeline := fun block => Classical.choice (hpipeline block) }⟩

/-- Prepare every safe fixed-line carrier from one common original-source
`rho`-slab AD receipt.  Each block uses its own dependent carrier and fine
witnesses, but the source, original slope, slab certificate, and constant
budget are shared. -/
theorem PureWZ2OrdinaryPaperOrderAllBlockCarrierData.prepareAllCoarseBlocksOfSourceRhoSlabAD
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
    {C : ENNReal}
    (hsourceRhoSlabAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (globalGrainProjection source.globalGrains.slope
          (globalGrainSlab source.shading.union z rho))
        rho (1 - sigma) C)
    (hconstant :
      144 * C ≤ 10 * Kakeya.realRpowENN rho (-middleLoss))
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hnormalEta : 0 < normalEta)
    (hnormalEtaSigma : 4 * normalEta < sigma)
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
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1)
    (hlocalConstant :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * Kakeya.realRpowENN rho (-middleLoss))) :
    Nonempty (PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family) := by
  have hpipeline : ∀ block : {block // block ∈ safe.blocks},
      Nonempty (PureWZ2SourceFixedLineCoarsePipelineData
        (normalEta := normalEta) (family.carrierData block)) := fun block =>
    (family.carrierData block).coarseGraphPipelineOfSourceRhoSlabAD
      hsourceRhoSlabAD hconstant hbridge hsigma hsigmaOne hnormalEta
      hnormalEtaSigma hcertificateOne hsourceFloor hlocalPower hglobalPower
      hPlanarSmall hrootSmall20 hlocalizationAbsorb hgraphOne hheightAbsorb
      hlocalConstant
  exact ⟨{ pipeline := fun block => Classical.choice (hpipeline block) }⟩

/-- The aggregate source-to-coarse supply, with the new graph shadow
definitionally equal to the genuine coarse carrier on every block. -/
theorem PureWZ2SourceFixedLineCoarseAllBlockData.aggregate_graph_supply
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    (all : PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family) :
    volume prepared.shadow.union * twoScale.fine.balanced.cellMass ≤
      2 * ∑ block : {block // block ∈ safe.blocks},
        (2 * (family.carrierData block).outerPopular.popular.bins : ℕ) *
          (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
            volume (all.pipeline block).prep.shadow.union) := by
  have hlocal : ∀ block : {block // block ∈ safe.blocks},
      volume (safe.blockWindow block).shading.union *
            twoScale.fine.balanced.cellMass ≤
        (2 * (family.carrierData block).outerPopular.popular.bins : ℕ) *
          (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
            volume (all.pipeline block).prep.shadow.union) := by
    intro block
    have hsupply := (family.carrierData block).source_to_coarse_volume_supply
    have hwindow : volume (safe.blockWindow block).shading.union =
        volume (family.carrierData block).sourceWindow.shading.union := by
      rw [family.carrierData_sourceWindow,
        (safe.blockWindow block).window_shading]
      rfl
    rw [hwindow]
    simpa only [(all.pipeline block).prep_shadow_union] using hsupply
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
    _ ≤ _ := mul_le_mul_left' (Finset.sum_le_sum fun block _ =>
      hlocal block) 2

def pureWZ2SourceFixedLineCoarseGoodGraphBlocks
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    (all : PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family)
    (volumeLoss : ℝ) : Finset {block // block ∈ safe.blocks} :=
  safe.blocks.attach.filter fun block =>
    Kakeya.realRpowENN (all.pipeline block).prep.graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      volume (all.pipeline block).prep.shadow.union

theorem pureWZ2SourceFixedLineCoarseGoodGraphBlocks_volume_lower
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family}
    {block : {block // block ∈ safe.blocks}}
    (hblock : block ∈
      pureWZ2SourceFixedLineCoarseGoodGraphBlocks all volumeLoss) :
    Kakeya.realRpowENN (all.pipeline block).prep.graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      volume (all.pipeline block).prep.shadow.union :=
  (Finset.mem_filter.mp hblock).2

theorem PureWZ2SourceFixedLineCoarseAllBlockData.goodGraphBlocks_retains_half
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    (all : PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family)
    (hbad :
      2 * ((safe.blocks.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) ≤
        ∑ block : {block // block ∈ safe.blocks},
          volume (all.pipeline block).prep.shadow.union) :
    (∑ block : {block // block ∈ safe.blocks},
        volume (all.pipeline block).prep.shadow.union) ≤
      2 * ∑ block ∈
          pureWZ2SourceFixedLineCoarseGoodGraphBlocks all volumeLoss,
        volume (all.pipeline block).prep.shadow.union := by
  let blocks := safe.blocks.attach
  let supply : {block // block ∈ safe.blocks} → ENNReal := fun block =>
    volume (all.pipeline block).prep.shadow.union
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
    pureWZ2SourceFixedLineCoarseGoodGraphBlocks,
    (all.pipeline _).prep.graphScale_eq] using hhalf

theorem PureWZ2SourceFixedLineCoarseAllBlockData.goodGraphBlocks_nonempty
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    (all : PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family)
    (hbad :
      2 * ((safe.blocks.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) ≤
        ∑ block : {block // block ∈ safe.blocks},
          volume (all.pipeline block).prep.shadow.union) :
    (pureWZ2SourceFixedLineCoarseGoodGraphBlocks all volumeLoss).Nonempty := by
  have hhalf := all.goodGraphBlocks_retains_half hbad
  have htotalPos : 0 < ∑ block : {block // block ∈ safe.blocks},
      volume (all.pipeline block).prep.shadow.union := by
    rcases safe.blocks_nonempty with ⟨block, hblock⟩
    let first : {block // block ∈ safe.blocks} := ⟨block, hblock⟩
    have hfirstPos : 0 < volume (all.pipeline first).prep.shadow.union := by
      rw [(all.pipeline first).prep_shadow_union,
        (family.carrierData first).coarseCarrier.volume_eq]
      exact ENNReal.mul_pos
        (by
          exact_mod_cast
            (family.carrierData first).residue.selected_nonempty.card_ne_zero)
        twoScale.fine.balanced.cellMass_pos.ne'
    exact hfirstPos.trans_le
      (Finset.single_le_sum
        (s := Finset.univ)
        (f := fun block : {block // block ∈ safe.blocks} =>
          volume (all.pipeline block).prep.shadow.union)
        (fun _ _ => bot_le) (Finset.mem_univ first))
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hhalf
  simp only [Finset.sum_empty, mul_zero] at hhalf
  exact (not_le_of_gt htotalPos) hhalf

structure PureWZ2SourceFixedLineCoarseGoodBlockFamilyData
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
    (all : PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family) where
  indexCount : ℕ
  indexCount_pos : 0 < indexCount
  safeBlock : Fin indexCount → {block // block ∈ safe.blocks}
  safeBlock_injective : Function.Injective safeBlock
  block_mem : ∀ index, safeBlock index ∈
    pureWZ2SourceFixedLineCoarseGoodGraphBlocks all volumeLoss
  block_surjective : ∀ block ∈
    pureWZ2SourceFixedLineCoarseGoodGraphBlocks all volumeLoss,
      ∃ index, safeBlock index = block
  rich : ∀ index, PureWZ2SourceFixedLineCoarseRichPipelineData
    (finalLoss := finalLoss) (theoremEta := theoremEta)
    (all.pipeline (safeBlock index))
  extraLoss : ℝ
  extraCost_power : ∀ index,
    (((all.pipeline (safeBlock index)).preparedGraph.graph.residue.extraCost :
        ℕ) : ℝ) ≤
      Real.rpow (all.pipeline (safeBlock index)).prep.graphScale (-extraLoss)

theorem PureWZ2SourceFixedLineCoarseAllBlockData.buildGoodBlockFamily
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
    (all : PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCOne : (1 : ENNReal) ≤
      10 * Kakeya.realRpowENN rho (-middleLoss))
    (hCpower : ∀ block : {block // block ∈ safe.blocks},
      (10 * Kakeya.realRpowENN rho (-middleLoss)).toReal ≤
        Real.rpow (all.pipeline block).prep.graphScale (-constantLoss))
    (hextraPower : ∀ block : {block // block ∈ safe.blocks},
      ((all.pipeline block).preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow (all.pipeline block).prep.graphScale (-extraLoss))
    (hedgeAbsorb : ∀ block : {block // block ∈ safe.blocks},
      Real.rpow (wz1Lemma23Theorem22Scale
          (all.pipeline block).prep.graphScale) (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow (all.pipeline block).prep.graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss +
              4 * extraLoss))
    (hKatzTao : ∀ block : {block // block ∈ safe.blocks},
      (4 : ENNReal) ≤ Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale
          (all.pipeline block).prep.graphScale) (-theoremEta))
    (hprojection : ∀ block : {block // block ∈ safe.blocks},
      ∀ ready : PureWZ2SourceFixedLineCoarseReadyGraph
          (theoremEta := theoremEta) (all.pipeline block).sharp,
        WZ1Proposition8_9AlternativeAUnion
          ready.ready.deltaGraph finalLoss
          ready.common.F ready.common.G₁ ready.common.G₁)
    (hscaleOne : 5 * (256 * rho) ≤ 1)
    (hlengthLower : Real.rpow (5 * (256 * rho))
        (1 / 2 + finalLoss) ≤ twoScale.sqrtRequested.1)
    (hgoodNonempty :
      (pureWZ2SourceFixedLineCoarseGoodGraphBlocks all volumeLoss).Nonempty) :
    ∃ data : PureWZ2SourceFixedLineCoarseGoodBlockFamilyData
        (finalLoss := finalLoss) (theoremEta := theoremEta)
        (volumeLoss := volumeLoss) all,
      data.extraLoss = extraLoss := by
  let good := pureWZ2SourceFixedLineCoarseGoodGraphBlocks all volumeLoss
  let goodEquiv := good.equivFin
  let safeBlock : Fin good.card → {block // block ∈ safe.blocks} :=
    fun index => (goodEquiv.symm index).1
  have hblockMem : ∀ index, safeBlock index ∈ good := fun index =>
    (goodEquiv.symm index).2
  have hblockInjective : Function.Injective safeBlock := by
    intro first second heq
    apply goodEquiv.symm.injective
    exact Subtype.ext heq
  have hrichExists : ∀ index, Nonempty
      (PureWZ2SourceFixedLineCoarseRichPipelineData
        (finalLoss := finalLoss) (theoremEta := theoremEta)
        (all.pipeline (safeBlock index))) := by
    intro index
    apply (all.pipeline (safeBlock index)).toRichPipeline
      hsigma hsigmaOne hCOne (hCpower (safeBlock index))
      (pureWZ2SourceFixedLineCoarseGoodGraphBlocks_volume_lower
        (hblockMem index))
      (hextraPower (safeBlock index)) (hedgeAbsorb (safeBlock index))
      (hKatzTao (safeBlock index)) (hprojection (safeBlock index))
    · simpa [(all.pipeline (safeBlock index)).prep.graphScale_eq]
        using hscaleOne
    · simpa [(all.pipeline (safeBlock index)).prep.graphScale_eq]
        using hlengthLower
  let rich : ∀ index : Fin good.card,
      PureWZ2SourceFixedLineCoarseRichPipelineData
        (finalLoss := finalLoss) (theoremEta := theoremEta)
        (all.pipeline (safeBlock index)) := fun index =>
    Classical.choice (hrichExists index)
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
    rich := rich
    extraLoss := extraLoss
    extraCost_power := fun index => hextraPower (safeBlock index)
  }, rfl⟩

end Kakeya.Assouad

end
