import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.BalancedSafeFixedLineBridge

/-!
# Sharp source-horizontal graphs on every balanced safe block

The ordinary step in the proof of WZ Corollary 5.6 keeps the complete safe
block partition through the local graph preparation.  Popularity is applied
only afterwards, to the actual sharp graph volumes.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

structure PureWZ2BalancedSafeAllBlockFamilyData
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (safe : PureWZ2BalancedSafeBlockFamilyData prepared) where
  pipeline : ∀ block : {block // block ∈ safe.blocks},
    PureWZ2SourceHorizontalPipelineData
      (normalEta := normalEta) twoScale
  left_eq : ∀ block, (pipeline block).window.left =
    (safe.blockWindow block).window.left
  volumeSupply_eq : ∀ block, (pipeline block).window.volumeSupply =
    volume (safe.blockWindow block).shading.union

theorem PureWZ2BalancedSafeBlockFamilyData.prepareAllBlocks
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
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
    Nonempty (PureWZ2BalancedSafeAllBlockFamilyData
      (normalEta := normalEta) safe) := by
  have hpipeline : ∀ block : {block // block ∈ safe.blocks},
      ∃ pipeline : PureWZ2SourceHorizontalPipelineData
          (normalEta := normalEta) twoScale,
        pipeline.window.left = (safe.blockWindow block).window.left ∧
        pipeline.window.volumeSupply =
          volume (safe.blockWindow block).shading.union := by
    intro block
    rcases safe.sourceHorizontalPipelineOnBlock block hbridge
        hsigma hsigmaOne hnormalEta hnormalEtaSigma hcertificateOne
        hsourceFloor hlocalPower hglobalPower hPlanarSmall hrootSmall20
        hlocalizationAbsorb hgraphOne hheightAbsorb with
      ⟨pipeline, hleft, hsupply, _⟩
    exact ⟨pipeline, hleft, hsupply⟩
  let pipeline : ∀ block : {block // block ∈ safe.blocks},
      PureWZ2SourceHorizontalPipelineData
        (normalEta := normalEta) twoScale := fun block =>
    Classical.choose (hpipeline block)
  exact ⟨{
    pipeline := pipeline
    left_eq := fun block => (Classical.choose_spec (hpipeline block)).1
    volumeSupply_eq := fun block =>
      (Classical.choose_spec (hpipeline block)).2
  }⟩

/-- The selected safe phase is controlled by the sum of all sharp graph
carriers.  This is the aggregate form of the exact per-block Fubini bound. -/
theorem PureWZ2BalancedSafeAllBlockFamilyData.aggregate_volume_supply_le
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (data : PureWZ2BalancedSafeAllBlockFamilyData
      (normalEta := normalEta) safe) :
    volume prepared.shadow.union *
        (twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass) ≤
      2 * (pureWZ2SourceHorizontalVolumeCost
          rho delta sigma inputLoss *
        volume (wz1PaperGridCube rho (0, 0, 0))) *
        ∑ block : {block // block ∈ safe.blocks},
          volume (data.pipeline block).prep.shadow.union := by
  let cost := pureWZ2SourceHorizontalVolumeCost
      rho delta sigma inputLoss *
    volume (wz1PaperGridCube rho (0, 0, 0))
  have hphase := safe.volume_half
  have hlocal : ∀ block : {block // block ∈ safe.blocks},
      volume (safe.blockWindow block).shading.union *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass) ≤
        cost * volume (data.pipeline block).prep.shadow.union := by
    intro block
    rw [← data.volumeSupply_eq block]
    simpa [cost, mul_assoc] using
      (data.pipeline block).prep.volume_supply_le
        (data.pipeline block).shadow_union
  calc
    volume prepared.shadow.union *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass) ≤
        (2 * ∑ block : {block // block ∈ safe.blocks},
          volume (safe.blockWindow block).shading.union) *
            (twoScale.coarse.balanced.cellMass *
              twoScale.fine.balanced.cellMass) := by gcongr
    _ = 2 * ∑ block : {block // block ∈ safe.blocks},
          volume (safe.blockWindow block).shading.union *
            (twoScale.coarse.balanced.cellMass *
              twoScale.fine.balanced.cellMass) := by
        rw [mul_assoc, Finset.sum_mul]
    _ ≤ 2 * ∑ block : {block // block ∈ safe.blocks},
          cost * volume (data.pipeline block).prep.shadow.union := by
        exact mul_le_mul_left'
          (Finset.sum_le_sum fun block _ => hlocal block) 2
    _ = 2 * cost * ∑ block : {block // block ∈ safe.blocks},
          volume (data.pipeline block).prep.shadow.union := by
        rw [← Finset.mul_sum]
        ring

end Kakeya.Assouad

end
