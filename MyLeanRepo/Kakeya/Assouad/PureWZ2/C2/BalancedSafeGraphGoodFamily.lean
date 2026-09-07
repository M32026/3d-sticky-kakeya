import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.BalancedSafeAllBlockFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalRichPipelineOfVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalGoodBlocks

/-!
# Graph-volume popularity on balanced safe blocks

This is the ordinary all-block step in the proof of WZ Corollary 5.6.  Every
safe block is prepared through the sharp graph geometry first.  We then
discard precisely those blocks whose actual prepared graph carrier is below
the common Theorem-22 volume threshold.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

def pureWZ2GoodBalancedSafeGraphBlocks
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (all : PureWZ2BalancedSafeAllBlockFamilyData
      (normalEta := normalEta) safe)
    (volumeLoss : ℝ) : Finset {block // block ∈ safe.blocks} :=
  safe.blocks.attach.filter fun block =>
    Kakeya.realRpowENN (all.pipeline block).prep.graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      volume (all.pipeline block).prep.shadow.union

theorem pureWZ2GoodBalancedSafeGraphBlocks_volume_lower
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {all : PureWZ2BalancedSafeAllBlockFamilyData
      (normalEta := normalEta) safe}
    {block : {block // block ∈ safe.blocks}}
    (hblock : block ∈
      pureWZ2GoodBalancedSafeGraphBlocks all volumeLoss) :
    Kakeya.realRpowENN (all.pipeline block).prep.graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      volume (all.pipeline block).prep.shadow.union :=
  (Finset.mem_filter.mp hblock).2

theorem PureWZ2BalancedSafeAllBlockFamilyData.goodGraphBlocks_retains_half
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (all : PureWZ2BalancedSafeAllBlockFamilyData
      (normalEta := normalEta) safe)
    (hbad :
      2 * ((safe.blocks.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) ≤
        ∑ block : {block // block ∈ safe.blocks},
          volume (all.pipeline block).prep.shadow.union) :
    (∑ block : {block // block ∈ safe.blocks},
        volume (all.pipeline block).prep.shadow.union) ≤
      2 * ∑ block ∈ pureWZ2GoodBalancedSafeGraphBlocks all volumeLoss,
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
    pureWZ2GoodBalancedSafeGraphBlocks,
    (all.pipeline _).prep.graphScale_eq] using hhalf

theorem PureWZ2BalancedSafeAllBlockFamilyData.goodGraphBlocks_nonempty
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (all : PureWZ2BalancedSafeAllBlockFamilyData
      (normalEta := normalEta) safe)
    (hbad :
      2 * ((safe.blocks.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) ≤
        ∑ block : {block // block ∈ safe.blocks},
          volume (all.pipeline block).prep.shadow.union) :
    (pureWZ2GoodBalancedSafeGraphBlocks all volumeLoss).Nonempty := by
  have hhalf := all.goodGraphBlocks_retains_half hbad
  have htotalPos : 0 < ∑ block : {block // block ∈ safe.blocks},
      volume (all.pipeline block).prep.shadow.union := by
    rcases safe.blocks_nonempty with ⟨block, hblock⟩
    let first : {block // block ∈ safe.blocks} := ⟨block, hblock⟩
    have hfirstPos : 0 < volume (all.pipeline first).prep.shadow.union := by
      rcases (all.pipeline first).heightPopular.heightIndices_nonempty with
        ⟨heightIndex, hheightIndex⟩
      exact (all.pipeline first).heightPopular.layerMass_pos.trans_le <|
        ((all.pipeline first).heightPopular.layer_volume_band
          heightIndex hheightIndex).1 |>.trans
          (measure_mono Set.inter_subset_left)
    have hsingle : volume (all.pipeline first).prep.shadow.union ≤
        ∑ block : {block // block ∈ safe.blocks},
          volume (all.pipeline block).prep.shadow.union := by
      exact Finset.single_le_sum
        (fun block _ => (show (0 : ENNReal) ≤
          volume (all.pipeline block).prep.shadow.union from bot_le))
        (Finset.mem_univ first)
    exact hfirstPos.trans_le hsingle
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hhalf
  simp only [Finset.sum_empty, mul_zero] at hhalf
  exact (not_le_of_gt htotalPos) hhalf

structure PureWZ2BalancedSafeGraphGoodBlockFamilyData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (all : PureWZ2BalancedSafeAllBlockFamilyData
      (normalEta := normalEta) safe)
    (volumeLoss : ℝ) where
  outputs : PureWZ2SourceHorizontalBlockFamilyData
    (finalLoss := finalLoss) (normalEta := normalEta)
    (theoremEta := theoremEta) twoScale
  safeBlock : Fin outputs.indexCount → {block // block ∈ safe.blocks}
  safeBlock_injective : Function.Injective safeBlock
  block_mem : ∀ index, safeBlock index ∈
    pureWZ2GoodBalancedSafeGraphBlocks all volumeLoss
  block_surjective : ∀ block ∈
    pureWZ2GoodBalancedSafeGraphBlocks all volumeLoss,
      ∃ index, safeBlock index = block
  pipeline_eq : ∀ index, outputs.pipeline index = all.pipeline (safeBlock index)
  extraLoss : ℝ
  extraCost_power : ∀ index,
    ((outputs.pipeline index).graph.residue.extraCost : ℝ) ≤
      Real.rpow (outputs.pipeline index).prep.graphScale (-extraLoss)

/-- Complete the rich graph construction on every graph-volume-good block. -/
theorem PureWZ2BalancedSafeAllBlockFamilyData.buildGraphGoodBlockFamily
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta
      volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (all : PureWZ2BalancedSafeAllBlockFamilyData
      (normalEta := normalEta) safe)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon : 0 < finalLoss) (hepsilonOne : finalLoss < 1)
    (hepsilonSigma : finalLoss / 2 < sigma)
    (hCOne :
      (1 : ENNReal) ≤ 10 * Kakeya.realRpowENN delta (-inputLoss))
    (hCpower : ∀ pipeline : PureWZ2SourceHorizontalPipelineData
        (normalEta := normalEta) twoScale,
      (10 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
        Real.rpow pipeline.prep.graphScale (-constantLoss))
    (hextraPower : ∀ pipeline : PureWZ2SourceHorizontalPipelineData
        (normalEta := normalEta) twoScale,
      (pipeline.graph.residue.extraCost : ℝ) ≤
        Real.rpow pipeline.prep.graphScale (-extraLoss))
    (hedgeAbsorb : ∀ pipeline : PureWZ2SourceHorizontalPipelineData
        (normalEta := normalEta) twoScale,
      Real.rpow (wz1Lemma23Theorem22Scale pipeline.prep.graphScale)
          (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow pipeline.prep.graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss +
              4 * extraLoss))
    (hKatzTao : ∀ pipeline : PureWZ2SourceHorizontalPipelineData
        (normalEta := normalEta) twoScale,
      (4 : ENNReal) ≤ Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale pipeline.prep.graphScale)
        (-theoremEta))
    (hprojection : ∀ pipeline : PureWZ2SourceHorizontalPipelineData
        (normalEta := normalEta) twoScale,
      ∀ data : PureWZ2SourceHorizontalReadyGraph
          (theoremEta := theoremEta) pipeline.sharp,
        WZ1Proposition8_9AlternativeAUnion
          data.ready.deltaGraph finalLoss
          data.common.F data.common.G₁ data.common.G₁)
    (hscaleOne : 5 * (256 * rho) ≤ 1)
    (hlengthLower :
      Real.rpow (5 * (256 * rho)) (1 / 2 + finalLoss) ≤
        twoScale.sqrtRequested.1)
    (hgoodNonempty :
      (pureWZ2GoodBalancedSafeGraphBlocks all volumeLoss).Nonempty) :
    ∃ data : PureWZ2BalancedSafeGraphGoodBlockFamilyData
        (finalLoss := finalLoss) (theoremEta := theoremEta)
        all volumeLoss,
      data.extraLoss = extraLoss := by
  let good := pureWZ2GoodBalancedSafeGraphBlocks all volumeLoss
  let goodEquiv := good.equivFin
  let safeBlock : Fin good.card → {block // block ∈ safe.blocks} :=
    fun index => (goodEquiv.symm index).1
  have hblockMem : ∀ index, safeBlock index ∈ good := fun index =>
    (goodEquiv.symm index).2
  have hblockInjective : Function.Injective safeBlock := by
    intro first second heq
    apply goodEquiv.symm.injective
    exact Subtype.ext heq
  let pipeline : Fin good.card → PureWZ2SourceHorizontalPipelineData
      (normalEta := normalEta) twoScale := fun index =>
    all.pipeline (safeBlock index)
  have hrichExists : ∀ index, Nonempty
      (PureWZ2SourceHorizontalRichPipelineData
        (finalLoss := finalLoss) (theoremEta := theoremEta)
        (pipeline index)) := by
    intro index
    apply (pipeline index).toRichPipelineOfVolumeLower
      hsigma hsigmaOne hepsilon hepsilonOne hepsilonSigma hCOne
      (hCpower (pipeline index))
      (pureWZ2GoodBalancedSafeGraphBlocks_volume_lower
        (hblockMem index))
      (hextraPower (pipeline index)) (hedgeAbsorb (pipeline index))
      (hKatzTao (pipeline index)) (hprojection (pipeline index))
    · simpa [(pipeline index).prep.graphScale_eq] using hscaleOne
    · simpa [(pipeline index).prep.graphScale_eq] using hlengthLower
  let rich : ∀ index, PureWZ2SourceHorizontalRichPipelineData
      (finalLoss := finalLoss) (theoremEta := theoremEta)
      (pipeline index) := fun index => Classical.choice (hrichExists index)
  let outputs : PureWZ2SourceHorizontalBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) twoScale := {
    indexCount := good.card
    indexCount_pos := Finset.card_pos.mpr hgoodNonempty
    block := fun index => (safeBlock index).1
    block_injective := fun first second heq =>
      hblockInjective (Subtype.ext heq)
    shift := pureWZ2BalancedWindowPhaseShift rho safe.phase
    pipeline := pipeline
    rich := rich
    left_eq := by
      intro index
      rw [all.left_eq (safeBlock index),
        (safe.blockWindow (safeBlock index)).window_left]
      rfl
  }
  exact ⟨{
    outputs := outputs
    safeBlock := safeBlock
    safeBlock_injective := hblockInjective
    block_mem := hblockMem
    block_surjective := by
      intro target htarget
      let index := goodEquiv ⟨target, htarget⟩
      refine ⟨index, ?_⟩
      change (goodEquiv.symm index).1 = target
      simp [index]
    pipeline_eq := fun _ => rfl
    extraLoss := extraLoss
    extraCost_power := fun index => hextraPower (pipeline index)
  }, rfl⟩

namespace PureWZ2BalancedSafeGraphGoodBlockFamilyData

/-- Source-popular height layers have the common graph-window cardinality
bound on every retained block. -/
theorem popular_heights_le_cap
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {all : PureWZ2BalancedSafeAllBlockFamilyData
      (normalEta := normalEta) safe}
    (data : PureWZ2BalancedSafeGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (theoremEta := theoremEta) all volumeLoss)
    (index : Fin data.outputs.indexCount) :
    ((data.outputs.pipeline index).heightPopular.heightIndices.card :
        ENNReal) ≤
      PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho := by
  let pipeline := data.outputs.pipeline index
  have hsubset : pipeline.heightPopular.heightIndices ⊆
      wz1Lemma23SnappedHeights pipeline.prep.windowed.global.cells := by
    intro heightIndex hheight
    have hglobal : heightIndex ∈ pipeline.prep.windowed.global.heightIndices := by
      rw [pipeline.prep.windowed.global.heightIndices_eq]
      exact pipeline.heightPopular.heightIndices_subset hheight
    have hlayerNonempty :
        (pipeline.prep.windowed.global.layerCells heightIndex).Nonempty := by
      have hlayerPos : 0 < volume (pipeline.prep.shadow.union ∩
          wz1Lemma23HeightSlab pipeline.prep.graphScale heightIndex) :=
        pipeline.heightPopular.layerMass_pos.trans_le
          (pipeline.heightPopular.layer_volume_band heightIndex hheight).1
      by_contra hempty
      have hlayerEmpty := Finset.not_nonempty_iff_eq_empty.mp hempty
      have hbound := pipeline.prep.windowed.global.layer_volume_bound
        heightIndex hglobal
      have harea := wz1_lemma23_exactSlice_area_le_two pipeline.prep.shadow
        pipeline.prep.graphScale_pos
        (by
          intro point hpoint
          have hpaper : point ∈ pipeline.retained.shading.union := by
            exact pipeline.prep.shadow_union_subset hpoint
          have hnorm := norm_le_two_of_mem_paperShading hpaper
          simpa [Metric.mem_closedBall, dist_zero_right] using hnorm)
        (pipeline.prep.windowed.global.selectedHeight heightIndex)
      rw [← pipeline.prep.windowed.global.layerCells_eq heightIndex,
        hlayerEmpty] at harea
      norm_num at harea
      have hsidePos : 0 < ENNReal.ofReal
          (gridSide (pipeline.prep.graphScale / 2)) := by
        apply ENNReal.ofReal_pos.mpr
        dsimp [gridSide]
        apply div_pos
        · nlinarith [pipeline.prep.graphScale_pos]
        · exact Real.sqrt_pos.mpr (by norm_num)
      have hzero : volume (pipeline.prep.shadow.union ∩
          wz1Lemma23HeightSlab pipeline.prep.graphScale heightIndex) = 0 := by
        apply le_zero_iff.mp
        have hdiv : volume (pipeline.prep.shadow.union ∩
              wz1Lemma23HeightSlab pipeline.prep.graphScale heightIndex) /
              ENNReal.ofReal (gridSide (pipeline.prep.graphScale / 2)) ≤ 0 :=
          hbound.trans harea.le
        have hmul := (ENNReal.div_le_iff hsidePos.ne'
          ENNReal.ofReal_ne_top).mp hdiv
        simpa using hmul
      exact (ne_of_gt hlayerPos) hzero
    rcases hlayerNonempty with ⟨cell, hcell⟩
    have hcellGlobal : cell ∈ pipeline.prep.windowed.global.cells := by
      rw [pipeline.prep.windowed.global.cells_eq]
      exact Finset.mem_biUnion.mpr ⟨heightIndex, hglobal, hcell⟩
    exact Finset.mem_image.mpr ⟨cell, hcellGlobal,
      (pipeline.prep.windowed.global.layer_height
        heightIndex hglobal cell hcell)⟩
  have hreal := wz1Lemma23_height_layer_count
    pipeline.prep.graphScale_pos pipeline.prep.graphScale_one
    pipeline.prep.windowed.global_cells_window
  have hcardReal :
      (pipeline.heightPopular.heightIndices.card : ℝ) ≤
        3 / Real.sqrt pipeline.prep.graphScale := by
    have hcast : (pipeline.heightPopular.heightIndices.card : ℝ) ≤
        ((wz1Lemma23SnappedHeights
          pipeline.prep.windowed.global.cells).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    exact hcast.trans hreal
  have henn := ENNReal.natCast_le_ofReal
    pipeline.heightPopular.heightIndices_nonempty.card_ne_zero |>.mpr hcardReal
  simpa [PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap,
    pipeline.prep.graphScale_eq] using henn

/-- An actual retained graph carrier controls the complete multi-height lift
without reintroducing the source-window cell masses. -/
theorem graph_height_mass_bound_uniform
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {all : PureWZ2BalancedSafeAllBlockFamilyData
      (normalEta := normalEta) safe}
    (data : PureWZ2BalancedSafeGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (theoremEta := theoremEta) all volumeLoss)
    (index : Fin data.outputs.indexCount) :
    volume (data.outputs.pipeline index).prep.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
      PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho data.extraLoss *
        (data.outputs.rich index).heightLift.shading.mass := by
  let pipeline := data.outputs.pipeline index
  let rich := data.outputs.rich index
  let floor := pureWZ2SourceHorizontalRichFloor rho finalLoss
  have hpopular : volume pipeline.prep.shadow.union ≤
      2 * pipeline.heightPopular.bins *
        volume pipeline.heightPopular.shading.union := by
    have h := (ENNReal.div_le_iff (by norm_num) (by norm_num)).mp
      pipeline.heightPopular.retained_volume
    simpa [mul_comm, mul_left_comm,
      mul_assoc] using h
  have hfloor : floor ≤ (rich.rich.heightIndices.card : ENNReal) := by
    have hfloorEq : floor = Kakeya.realRpowENN
        rich.ready.ready.deltaGraph (finalLoss - 1) := by
      dsimp only [floor]
      unfold pureWZ2SourceHorizontalRichFloor
      rw [rich.ready.ready.deltaGraph_eq, pipeline.prep.graphScale_eq]
    rw [hfloorEq]
    simpa [rich.rich.heightIndices_card] using rich.rich.richF_card
  have hpopularLayer : volume pipeline.heightPopular.shading.union ≤
      2 * (pipeline.heightPopular.heightIndices.card : ENNReal) *
        pipeline.heightPopular.layerMass := by
    rw [pipeline.heightPopular.volume_eq_sum]
    calc
      (∑ heightIndex ∈ pipeline.heightPopular.heightIndices,
          volume (pipeline.prep.shadow.union ∩
            wz1Lemma23HeightSlab pipeline.prep.graphScale heightIndex)) ≤
        ∑ _heightIndex ∈ pipeline.heightPopular.heightIndices,
          2 * pipeline.heightPopular.layerMass := by
        exact Finset.sum_le_sum fun heightIndex hheight =>
          (pipeline.heightPopular.layer_volume_band heightIndex hheight).2
      _ = 2 * (pipeline.heightPopular.heightIndices.card : ENNReal) *
          pipeline.heightPopular.layerMass := by
        simp [Finset.sum_const]
        ring
  have hweightedMass :
      floor * volume pipeline.prep.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) ≤
        4 * pipeline.heightPopular.bins *
          (pipeline.heightPopular.heightIndices.card : ENNReal) *
            rich.heightLift.shading.mass := by
    calc
      floor * volume pipeline.prep.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) ≤
        floor * (2 * pipeline.heightPopular.bins *
          volume pipeline.heightPopular.shading.union) *
            (twoScale.coarse.fineMultiplicity : ENNReal) := by gcongr
      _ ≤ floor * (2 * pipeline.heightPopular.bins *
          (2 * (pipeline.heightPopular.heightIndices.card : ENNReal) *
            pipeline.heightPopular.layerMass)) *
            (twoScale.coarse.fineMultiplicity : ENNReal) := by gcongr
      _ ≤ (rich.rich.heightIndices.card : ENNReal) *
          (2 * pipeline.heightPopular.bins *
            (2 * (pipeline.heightPopular.heightIndices.card : ENNReal) *
              pipeline.heightPopular.layerMass)) *
            (twoScale.coarse.fineMultiplicity : ENNReal) := by gcongr
      _ = 4 * pipeline.heightPopular.bins *
          (pipeline.heightPopular.heightIndices.card : ENNReal) *
          ((twoScale.coarse.fineMultiplicity : ENNReal) *
            ((rich.rich.heightIndices.card : ENNReal) *
              pipeline.heightPopular.layerMass)) := by ring
      _ ≤ 4 * pipeline.heightPopular.bins *
          (pipeline.heightPopular.heightIndices.card : ENNReal) *
            rich.heightLift.shading.mass := by
        exact mul_le_mul_left' rich.heightVolume.mass_lower
          (4 * pipeline.heightPopular.bins *
            (pipeline.heightPopular.heightIndices.card : ENNReal))
  have hbinsNat : 4 * pipeline.heightPopular.bins ≤
      2 * pipeline.graph.residue.extraCost := by
    rw [pipeline.extraCost_eq]
    nlinarith
  have hbinsENN : (4 * pipeline.heightPopular.bins : ENNReal) ≤
      2 * (pipeline.graph.residue.extraCost : ENNReal) := by
    exact_mod_cast hbinsNat
  have hextraENN : (pipeline.graph.residue.extraCost : ENNReal) ≤
      ENNReal.ofReal (Real.rpow pipeline.prep.graphScale (-data.extraLoss)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (data.extraCost_power index)
  have hheight := data.popular_heights_le_cap index
  have hcost :
      (4 * pipeline.heightPopular.bins : ENNReal) *
          (pipeline.heightPopular.heightIndices.card : ENNReal) ≤
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho data.extraLoss := by
    calc
      _ ≤ (2 * (pipeline.graph.residue.extraCost : ENNReal)) *
          (pipeline.heightPopular.heightIndices.card : ENNReal) := by gcongr
      _ ≤ (2 * ENNReal.ofReal
          (Real.rpow pipeline.prep.graphScale (-data.extraLoss))) *
          PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho := by
        gcongr
      _ = PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho data.extraLoss := by
        rw [pipeline.prep.graphScale_eq]
        unfold PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  calc
    volume pipeline.prep.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) * floor =
        floor * volume pipeline.prep.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) := by ring
    _ ≤ (4 * pipeline.heightPopular.bins : ENNReal) *
          (pipeline.heightPopular.heightIndices.card : ENNReal) *
            rich.heightLift.shading.mass := hweightedMass
    _ ≤ PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho data.extraLoss * rich.heightLift.shading.mass := by gcongr

/-- Aggregate the retained graph carriers, then the multi-height lifts.  The
factor four is exactly the safe-phase loss followed by the graph-volume
good-block loss. -/
theorem aggregate_height_mass_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {all : PureWZ2BalancedSafeAllBlockFamilyData
      (normalEta := normalEta) safe}
    (data : PureWZ2BalancedSafeGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (theoremEta := theoremEta) all volumeLoss)
    (hbad :
      2 * ((safe.blocks.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) ≤
        ∑ block : {block // block ∈ safe.blocks},
          volume (all.pipeline block).prep.shadow.union) :
    volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
          twoScale.coarse.balanced.cellMass *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
      4 * (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          volume (wz1PaperGridCube rho (0, 0, 0))) *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho data.extraLoss *
        ∑ index : Fin data.outputs.indexCount,
          (data.outputs.rich index).heightLift.shading.mass := by
  let cost := pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
    volume (wz1PaperGridCube rho (0, 0, 0))
  let heightCost :=
    PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
      rho data.extraLoss
  let multiplicity : ENNReal := twoScale.coarse.fineMultiplicity
  let floor := pureWZ2SourceHorizontalRichFloor rho finalLoss
  let allGraph := ∑ block : {block // block ∈ safe.blocks},
    volume (all.pipeline block).prep.shadow.union
  let goodGraph := ∑ block ∈
      pureWZ2GoodBalancedSafeGraphBlocks all volumeLoss,
    volume (all.pipeline block).prep.shadow.union
  have hall : volume prepared.shadow.union *
        (twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass) ≤
      2 * cost * allGraph := by
    simpa [cost, allGraph] using all.aggregate_volume_supply_le
  have hgood : allGraph ≤ 2 * goodGraph := by
    simpa [allGraph, goodGraph] using
      all.goodGraphBlocks_retains_half hbad
  have hgoodIndexed : goodGraph =
      ∑ index : Fin data.outputs.indexCount,
        volume (data.outputs.pipeline index).prep.shadow.union := by
    symm
    dsimp only [goodGraph]
    apply Finset.sum_bij (fun index _ => data.safeBlock index)
    · intro index _
      exact data.block_mem index
    · intro first _ second _ heq
      exact data.safeBlock_injective heq
    · intro block hblock
      rcases data.block_surjective block hblock with ⟨index, heq⟩
      exact ⟨index, Finset.mem_univ index, heq⟩
    · intro index _
      rw [data.pipeline_eq index]
  have hlocal :
      (∑ index : Fin data.outputs.indexCount,
          volume (data.outputs.pipeline index).prep.shadow.union) *
          multiplicity * floor ≤
        heightCost * ∑ index : Fin data.outputs.indexCount,
          (data.outputs.rich index).heightLift.shading.mass := by
    calc
      _ = ∑ index : Fin data.outputs.indexCount,
          (volume (data.outputs.pipeline index).prep.shadow.union *
            multiplicity * floor) := by
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ ∑ index : Fin data.outputs.indexCount,
          heightCost *
            (data.outputs.rich index).heightLift.shading.mass := by
        exact Finset.sum_le_sum fun index _ => by
          simpa [heightCost, multiplicity, floor] using
            data.graph_height_mass_bound_uniform index
      _ = heightCost * ∑ index : Fin data.outputs.indexCount,
          (data.outputs.rich index).heightLift.shading.mass := by
        rw [Finset.mul_sum]
  calc
    volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
          twoScale.coarse.balanced.cellMass * multiplicity * floor =
        (volume prepared.shadow.union *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass)) * multiplicity * floor := by ring
    _ ≤ (2 * cost * allGraph) * multiplicity * floor := by gcongr
    _ ≤ (2 * cost * (2 * goodGraph)) * multiplicity * floor := by gcongr
    _ = 4 * cost * (goodGraph * multiplicity * floor) := by ring
    _ = 4 * cost *
        ((∑ index : Fin data.outputs.indexCount,
          volume (data.outputs.pipeline index).prep.shadow.union) *
            multiplicity * floor) := by rw [hgoodIndexed]
    _ ≤ 4 * cost *
        (heightCost * ∑ index : Fin data.outputs.indexCount,
          (data.outputs.rich index).heightLift.shading.mass) := by gcongr
    _ = 4 * (pureWZ2SourceHorizontalVolumeCost
          rho delta sigma inputLoss *
        volume (wz1PaperGridCube rho (0, 0, 0))) *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho data.extraLoss *
        ∑ index : Fin data.outputs.indexCount,
          (data.outputs.rich index).heightLift.shading.mass := by
      simp only [cost, heightCost]
      ring

/-- Select one mod-64 class after graph-volume selection. -/
theorem selectResidue_height_mass_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {all : PureWZ2BalancedSafeAllBlockFamilyData
      (normalEta := normalEta) safe}
    (data : PureWZ2BalancedSafeGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (theoremEta := theoremEta) all volumeLoss)
    (hbad :
      2 * ((safe.blocks.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) ≤
        ∑ block : {block // block ∈ safe.blocks},
          volume (all.pipeline block).prep.shadow.union) :
    ∃ residueData : PureWZ2SourceHorizontalBlockResidueData data.outputs,
      volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
          twoScale.coarse.balanced.cellMass *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
        256 * (pureWZ2SourceHorizontalVolumeCost
            rho delta sigma inputLoss *
          volume (wz1PaperGridCube rho (0, 0, 0))) *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho data.extraLoss *
          residueData.family.shading.mass := by
  rcases data.outputs.selectResidue with ⟨residueData⟩
  refine ⟨residueData, (data.aggregate_height_mass_bound hbad).trans ?_⟩
  calc
    4 * (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          volume (wz1PaperGridCube rho (0, 0, 0))) *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho data.extraLoss *
          ∑ index : Fin data.outputs.indexCount,
            (data.outputs.rich index).heightLift.shading.mass ≤
      4 * (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          volume (wz1PaperGridCube rho (0, 0, 0))) *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho data.extraLoss *
          (64 * residueData.family.shading.mass) := by
        gcongr
        exact residueData.total_mass_le
    _ = 256 * (pureWZ2SourceHorizontalVolumeCost
          rho delta sigma inputLoss *
        volume (wz1PaperGridCube rho (0, 0, 0))) *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho data.extraLoss *
        residueData.family.shading.mass := by ring

end PureWZ2BalancedSafeGraphGoodBlockFamilyData

end Kakeya.Assouad

end
