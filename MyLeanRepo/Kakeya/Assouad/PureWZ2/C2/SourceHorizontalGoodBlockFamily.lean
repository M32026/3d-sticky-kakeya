import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalGoodBlocks

/-!
# Dependent local outputs on every good source block

This is the finite assembly boundary before the mass-weighted mod-64
selection.  Every good block is run through the same source-horizontal
pipeline, but pipeline-dependent numerical obligations remain explicit.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem PureWZ2SourceCarrierPreparation.buildGoodBlockFamily
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta
      volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon : 0 < finalLoss) (hepsilonOne : finalLoss < 1)
    (hepsilonSigma : finalLoss / 2 < sigma)
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
    (habsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1)
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
      (4 : ENNReal) ≤
        Kakeya.realRpowENN
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
      (pureWZ2GoodSourceCarrierBlocks prepared volumeLoss).Nonempty) :
    ∃ data : PureWZ2SourceHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta)
      prepared volumeLoss,
      data.extraLoss = extraLoss := by
  let good := pureWZ2GoodSourceCarrierBlocks prepared volumeLoss
  let goodEquiv := good.equivFin
  let block : Fin good.card → ℤ := fun index => (goodEquiv.symm index).1
  have hblockMem : ∀ index, block index ∈ good := fun index =>
    (goodEquiv.symm index).2
  have hblockInjective : Function.Injective block := by
    intro first second heq
    apply goodEquiv.symm.injective
    exact Subtype.ext heq
  let windowData : ∀ index : Fin good.card,
      PureWZ2SourceCarrierBlockWindowData prepared (block index) := fun index =>
    Classical.choice (prepared.windowDataOfGoodBlock (hblockMem index))
  have hpipelineExists : ∀ index,
      ∃ pipeline : PureWZ2SourceHorizontalPipelineData
          (normalEta := normalEta) twoScale,
        pipeline.window.left = (windowData index).window.left ∧
          pipeline.window.volumeSupply =
            (windowData index).window.volumeSupply := by
    intro index
    exact (windowData index).window.sourceHorizontalPipelineWithWindow
      hbridge hsigma hsigmaOne hnormalEta hnormalEtaSigma
      hcertificateOne hsourceFloor hlocalPower hglobalPower hPlanarSmall
      hrootSmall20 habsorb hgraphOne hheightAbsorb
  let pipeline : Fin good.card → PureWZ2SourceHorizontalPipelineData
      (normalEta := normalEta) twoScale := fun index =>
    Classical.choose (hpipelineExists index)
  have hpipelineLeft : ∀ index, (pipeline index).window.left =
      (windowData index).window.left := fun index =>
    (Classical.choose_spec (hpipelineExists index)).1
  have hpipelineSupply : ∀ index, (pipeline index).window.volumeSupply =
      (windowData index).window.volumeSupply := fun index =>
    (Classical.choose_spec (hpipelineExists index)).2
  have hvolumeBudget : ∀ index,
      Kakeya.realRpowENN (pipeline index).prep.graphScale
            (1 + sigma / 2 + volumeLoss) *
          (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
            MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) ≤
        (pipeline index).window.volumeSupply *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass) := by
    intro index
    rw [(pipeline index).prep.graphScale_eq]
    rw [hpipelineSupply index, (windowData index).volumeSupply_eq,
      (windowData index).shading_eq]
    exact pureWZ2GoodSourceCarrierBlock_budget (hblockMem index)
  have hrichExists : ∀ index, Nonempty
      (PureWZ2SourceHorizontalRichPipelineData
        (finalLoss := finalLoss) (theoremEta := theoremEta)
        (pipeline index)) := by
    intro index
    apply (pipeline index).toRichPipeline hsigma hsigmaOne
      hepsilon hepsilonOne hepsilonSigma hCOne (hCpower (pipeline index))
      (hvolumeBudget index) (hextraPower (pipeline index))
      (hedgeAbsorb (pipeline index)) (hKatzTao (pipeline index))
      (hprojection (pipeline index))
    · simpa [(pipeline index).prep.graphScale_eq] using hscaleOne
    · simpa [(pipeline index).prep.graphScale_eq] using hlengthLower
  let rich : ∀ index, PureWZ2SourceHorizontalRichPipelineData
      (finalLoss := finalLoss) (theoremEta := theoremEta)
      (pipeline index) := fun index =>
    Classical.choice (hrichExists index)
  let outputs : PureWZ2SourceHorizontalBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) twoScale := {
    indexCount := good.card
    indexCount_pos := Finset.card_pos.mpr hgoodNonempty
    block := block
    block_injective := hblockInjective
    shift := 0
    pipeline := pipeline
    rich := rich
    left_eq := by
      intro index
      rw [hpipelineLeft index, (windowData index).left_eq]
      simp
  }
  exact ⟨{
    outputs := outputs
    block_mem := hblockMem
    block_surjective := by
      intro target htarget
      let index := goodEquiv ⟨target, htarget⟩
      refine ⟨index, ?_⟩
      change (goodEquiv.symm index).1 = target
      simp [index]
    volumeSupply_eq := by
      intro index
      rw [hpipelineSupply index, (windowData index).volumeSupply_eq,
        (windowData index).shading_eq]
    extraLoss := extraLoss
    extraCost_power := fun index => hextraPower (pipeline index)
  }, rfl⟩

end Kakeya.Assouad
