import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.BalancedSafeGoodBlocks
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalPipeline

/-!
# Safe balanced blocks enter the source-horizontal fixed-line pipeline

The safe phase retains genuine side-`rho` cells of the source pullback.  This
module records the dependent bridge from one such block to the existing
source-horizontal Lemma-23 pipeline.  In particular, the fixed line, the
root-source global slope, the fine local witnesses, and the later graph all
belong to the same pipeline, while its input supply is definitionally the
actual union volume of the safe block.

No graph-cell cardinality or auxiliary parent carrier is substituted for the
source volume.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Exact-slice Fubini on one genuine safe balanced source block. -/
theorem PureWZ2BalancedSafeBlockFamilyData.fixedLineOnBlock
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
    (block : {block // block ∈ safe.blocks}) :
    Nonempty
      (PureWZ2SourceHorizontalFixedLineData
        (safe.blockWindow block).window) := by
  have hvolume : 0 < MeasureTheory.volume
      (safe.blockWindow block).window.shading.union := by
    rw [(safe.blockWindow block).window_shading]
    rw [(safe.blockWindow block).volume_eq]
    exact ENNReal.mul_pos
      (by exact_mod_cast
        (safe.blockWindow block).cells_nonempty.card_ne_zero)
      twoScale.coarse.balanced.cellMass_pos.ne'
  exact (safe.blockWindow block).window.selectHorizontalFixedLine hvolume

/--
Run the complete dependent source-horizontal construction on one safe block.
The returned equalities expose the exact coarse-cell source volume at the
pipeline boundary used by all subsequent weighted estimates.
-/
theorem PureWZ2BalancedSafeBlockFamilyData.sourceHorizontalPipelineOnBlock
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
    (block : {block // block ∈ safe.blocks})
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
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
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    ∃ pipeline : PureWZ2SourceHorizontalPipelineData
        (normalEta := normalEta) twoScale,
      pipeline.window.left =
          (safe.blockWindow block).window.left ∧
      pipeline.window.volumeSupply =
          MeasureTheory.volume
            (safe.blockWindow block).shading.union ∧
      pipeline.window.volumeSupply =
          ((safe.blockWindow block).cells.card : ENNReal) *
            twoScale.coarse.balanced.cellMass := by
  rcases (safe.blockWindow block).window.sourceHorizontalPipelineWithWindow
      hbridge hsigma hsigmaOne hnormalEta hnormalEtaSigma
      hcertificateOne hsourceFloor hlocalPower hglobalPower hPlanarSmall
      hrootSmall20 hlocalizationAbsorb hgraphOne hheightAbsorb with
    ⟨pipeline, hleft, hsupply⟩
  refine ⟨pipeline, hleft, ?_, ?_⟩
  · calc
      pipeline.window.volumeSupply =
          (safe.blockWindow block).window.volumeSupply := hsupply
      _ = ((safe.blockWindow block).cells.card : ENNReal) *
          twoScale.coarse.balanced.cellMass :=
        (safe.blockWindow block).window_supply
      _ = MeasureTheory.volume
          (safe.blockWindow block).shading.union :=
        (safe.blockWindow block).volume_eq.symm
  · calc
      pipeline.window.volumeSupply =
          (safe.blockWindow block).window.volumeSupply := hsupply
      _ = ((safe.blockWindow block).cells.card : ENNReal) *
          twoScale.coarse.balanced.cellMass :=
        (safe.blockWindow block).window_supply

end Kakeya.Assouad
