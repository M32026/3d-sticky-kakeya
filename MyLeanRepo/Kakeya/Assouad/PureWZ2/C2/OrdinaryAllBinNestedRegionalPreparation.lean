import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryAllBinHeightLiftMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.BalancedSafeCoarseCompanion

/-!
# Second-stage regional relative mass for the ordinary all-bin chain

The first balanced cover already pulls every selected union of genuine
side-`rho` cells back to the original `delta` family.  The remaining paper
step is simultaneous: select the all-bin and rich witnesses together with the
second-sticky refinement so that source mass and the final height lift have the
same relative density.

The interface below packages that simultaneous choice.  It deliberately does
not assert a second cross identity for an arbitrary already chosen rich graph.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- The exact same-cell companions after the source-side outer-height
refinement, indexed by the already constructed all-block carrier family. -/
structure PureWZ2OrdinaryAllBinOuterPopularCompanionData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe) where
  companions : PureWZ2BalancedSafeCoarseCompanionFamilyData safe
  envelopes : companions.OuterPopularEnvelopeFamilyData fun block =>
    (carriers.carrier block).outerPopular

/-- Construct the synchronized outer-popular companion family without any
additional geometric hypothesis. -/
theorem PureWZ2OrdinaryPaperOrderAllBlockCarrierData.outerPopularCoarseCompanions
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe) :
    Nonempty (PureWZ2OrdinaryAllBinOuterPopularCompanionData carriers) := by
  rcases safe.coarseCompanions with ⟨companions⟩
  rcases companions.outerPopularEnvelopes
      (fun block => (carriers.carrier block).outerPopular) with ⟨envelopes⟩
  exact ⟨{ companions := companions, envelopes := envelopes }⟩

namespace PureWZ2OrdinaryAllBinOuterPopularCompanionData

variable
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}

/-- Source-relative regularized blocks retain indexed mass in the synchronized
outer-popular whole-cell coarse envelopes. -/
theorem aggregate_regularized_source_mass_lower
    (data : PureWZ2OrdinaryAllBinOuterPopularCompanionData carriers)
    (outerCost : ENNReal)
    (houterCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      (2 * (carriers.carrier block.1).outerPopular.popular.bins : ENNReal) ≤
        outerCost) :
    volume prepared.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) ≤
      8 * outerCost *
        ∑ block :
          {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
          (data.envelopes.envelope block.1).sourcePullback.shading.mass := by
  let blocks := pureWZ2OrdinaryPaperOrderRegularizedBlocks safe
  have hbase := data.companions.aggregate_regularized_source_mass_lower
  have hpopular := data.envelopes.source_mass_le_sum
    blocks outerCost (fun block hblock => houterCost ⟨block, hblock⟩)
  have hcompanionIndexed :
      (∑ block ∈ blocks,
          (data.companions.companion block).sourcePullback.shading.mass) =
        ∑ block : {block // block ∈ blocks},
          (data.companions.companion block.1).sourcePullback.shading.mass :=
    Finset.sum_subtype blocks (fun _ => Iff.rfl) _
  have henvelopeIndexed :
      (∑ block ∈ blocks,
          (data.envelopes.envelope block).sourcePullback.shading.mass) =
        ∑ block : {block // block ∈ blocks},
          (data.envelopes.envelope block.1).sourcePullback.shading.mass :=
    Finset.sum_subtype blocks (fun _ => Iff.rfl) _
  calc
    volume prepared.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) ≤
        4 * ∑ block : {block // block ∈ blocks},
          (data.companions.companion block.1).sourcePullback.shading.mass := by
      simpa [blocks] using hbase
    _ = 4 * ∑ block ∈ blocks,
          (data.companions.companion block).sourcePullback.shading.mass := by
      rw [hcompanionIndexed]
    _ ≤ 4 * (2 * outerCost * ∑ block ∈ blocks,
          (data.envelopes.envelope block).sourcePullback.shading.mass) := by
      gcongr
    _ = 8 * outerCost *
        ∑ block : {block // block ∈ blocks},
          (data.envelopes.envelope block.1).sourcePullback.shading.mass := by
      rw [henvelopeIndexed]
      ring

/-- The same exact cell ledger also retains genuine first-sticky coarse
volume.  The proof first transports source-block regularization through the
first balanced cover, and then transports outer-height popularity through the
common first-cover incidence mass.  No comparison between a balanced cell
mass and the volume of a physical `rho` cube is used. -/
theorem aggregate_regularized_coarse_volume_lower
    (data : PureWZ2OrdinaryAllBinOuterPopularCompanionData carriers)
    (outerCost : ENNReal)
    (houterCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      (2 * (carriers.carrier block.1).outerPopular.popular.bins : ENNReal) ≤
        outerCost) :
    volume twoScale.fine.refined.union ≤
      8 * outerCost *
        ∑ block :
          {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
          volume (data.envelopes.envelope block.1).shading.union := by
  let blocks := pureWZ2OrdinaryPaperOrderRegularizedBlocks safe
  let cubeVolume := volume (wz1PaperGridCube rho (0, 0, 0))
  let coarseCellMass := twoScale.coarse.balanced.cellMass
  let incidenceMass := twoScale.coarse.balanced.incidenceMass
  have hcoarseMassPos : 0 < coarseCellMass :=
    twoScale.coarse.balanced.cellMass_pos
  have hcoarseMassTop : coarseCellMass ≠ ⊤ :=
    twoScale.coarse.balanced.cellMass_ne_top
  have hincidencePos : 0 < incidenceMass :=
    twoScale.coarse.balanced.incidenceMass_pos
  have hincidenceTop : incidenceMass ≠ ⊤ :=
    twoScale.coarse.balanced.incidenceMass_ne_top
  have hregularized : volume prepared.shadow.union ≤
      4 * ∑ block : {block // block ∈ blocks},
        volume (safe.blockWindow block.1).shading.union := by
    calc
      volume prepared.shadow.union ≤
          4 * ∑ block ∈ blocks,
            volume (safe.blockWindow block).shading.union := by
        simpa [blocks] using safe.regularizedBlocks_retains_quarter
      _ = 4 * ∑ block : {block // block ∈ blocks},
          volume (safe.blockWindow block.1).shading.union := by
        rw [Finset.sum_subtype blocks (fun _ => Iff.rfl)]
  have hblockCross :
      (∑ block : {block // block ∈ blocks},
          volume (safe.blockWindow block.1).shading.union) * cubeVolume =
        (∑ block : {block // block ∈ blocks},
          volume (data.companions.companion block.1).shading.union) *
            coarseCellMass := by
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro block _
    simpa [cubeVolume, coarseCellMass] using
      (data.companions.companion block.1).block_volume_cross
  have hcoarseBlocks : volume twoScale.fine.refined.union ≤
      4 * ∑ block : {block // block ∈ blocks},
        volume (data.companions.companion block.1).shading.union := by
    apply (ENNReal.mul_le_mul_iff_right hcoarseMassPos.ne' hcoarseMassTop).mp
    calc
      coarseCellMass * volume twoScale.fine.refined.union =
          volume prepared.shadow.union * cubeVolume := by
        simpa [cubeVolume, coarseCellMass, mul_comm] using
          prepared.volume_mul_cube_eq.symm
      _ ≤ (4 * ∑ block : {block // block ∈ blocks},
          volume (safe.blockWindow block.1).shading.union) * cubeVolume := by
        gcongr
      _ = (4 * ∑ block : {block // block ∈ blocks},
          volume (data.companions.companion block.1).shading.union) *
            coarseCellMass := by
        rw [show (4 * ∑ block : {block // block ∈ blocks},
              volume (safe.blockWindow block.1).shading.union) * cubeVolume =
            4 * ((∑ block : {block // block ∈ blocks},
              volume (safe.blockWindow block.1).shading.union) * cubeVolume) by
              ring, hblockCross]
        ring
      _ = coarseCellMass *
          (4 * ∑ block : {block // block ∈ blocks},
            volume (data.companions.companion block.1).shading.union) := by
        rw [mul_comm]
  have hlocal : ∀ block : {block // block ∈ blocks},
      volume (data.companions.companion block.1).shading.union ≤
        2 * outerCost *
          volume (data.envelopes.envelope block.1).shading.union := by
    intro block
    have hmass :=
      PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData.block_source_mass_le
        (data.companions.companion block.1)
        (carriers.carrier block.1).outerPopular
        (data.envelopes.envelope block.1)
    have hmassCost :
        (data.companions.companion block.1).sourcePullback.shading.mass ≤
          2 * outerCost *
            (data.envelopes.envelope block.1).sourcePullback.shading.mass := by
      exact hmass.trans (by gcongr; exact houterCost block)
    apply (ENNReal.mul_le_mul_iff_right hincidencePos.ne' hincidenceTop).mp
    calc
      incidenceMass *
          volume (data.companions.companion block.1).shading.union =
          (data.companions.companion block.1).sourcePullback.shading.mass *
            cubeVolume := by
        simpa [cubeVolume, incidenceMass, mul_comm] using
          (data.companions.companion block.1).sourcePullback_mass_mul_cube.symm
      _ ≤ (2 * outerCost *
          (data.envelopes.envelope block.1).sourcePullback.shading.mass) *
            cubeVolume := by gcongr
      _ = 2 * outerCost *
          ((data.envelopes.envelope block.1).sourcePullback.shading.mass *
            cubeVolume) := by ring
      _ = 2 * outerCost *
          (volume (data.envelopes.envelope block.1).shading.union *
            incidenceMass) := by
        rw [(data.envelopes.envelope block.1).sourcePullback_mass_cross]
      _ = (2 * outerCost *
          volume (data.envelopes.envelope block.1).shading.union) *
            incidenceMass := by ring
      _ = incidenceMass *
          (2 * outerCost *
            volume (data.envelopes.envelope block.1).shading.union) := by
        rw [mul_comm]
  calc
    volume twoScale.fine.refined.union ≤
        4 * ∑ block : {block // block ∈ blocks},
          volume (data.companions.companion block.1).shading.union :=
      hcoarseBlocks
    _ ≤ 4 * ∑ block : {block // block ∈ blocks},
          2 * outerCost *
            volume (data.envelopes.envelope block.1).shading.union := by
      gcongr with block
      exact hlocal block
    _ = 8 * outerCost *
        ∑ block : {block // block ∈ blocks},
          volume (data.envelopes.envelope block.1).shading.union := by
      calc
        4 * ∑ block : {block // block ∈ blocks},
            2 * outerCost *
              volume (data.envelopes.envelope block.1).shading.union =
            ∑ block : {block // block ∈ blocks},
              8 * outerCost *
                volume (data.envelopes.envelope block.1).shading.union := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro block _
          ring
        _ = 8 * outerCost *
            ∑ block : {block // block ∈ blocks},
              volume (data.envelopes.envelope block.1).shading.union := by
          rw [Finset.mul_sum]

/-- Power-form aggregate supply for the whole-cell outer-popular envelopes.
The exponent is measured at the second sticky call's source scale `rho`; no
original-`delta` power and no physical-cube lower estimate enter the bound. -/
theorem aggregate_regularized_coarse_power_lower
    (data : PureWZ2OrdinaryAllBinOuterPopularCompanionData carriers)
    (outerCost : ENNReal)
    (houterCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      (2 * (carriers.carrier block.1).outerPopular.popular.bins : ENNReal) ≤
        outerCost) :
    Kakeya.realRpowENN rho (sigma + stickyLoss) ≤
      8 * outerCost *
        ∑ block :
          {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
          volume (data.envelopes.envelope block.1).shading.union := by
  have hfine : Kakeya.realRpowENN rho (sigma + stickyLoss) ≤
      volume twoScale.fine.refined.union := by
    simpa only [twoScale.rhoRequested_eq] using
      twoScale.fine.refined_volume_lower
  exact hfine.trans
    (data.aggregate_regularized_coarse_volume_lower outerCost houterCost)

end PureWZ2OrdinaryAllBinOuterPopularCompanionData

/-- The deterministic part of the nested regional construction, through the
second coarse all-bin decomposition but before imposing its graph-volume
threshold. -/
structure PureWZ2OrdinaryAllBinNestedRegionalPreparationData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
    (companions : PureWZ2OrdinaryAllBinOuterPopularCompanionData carriers) where
  parentData : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    PureWZ2BalancedSafeOuterPopularCoarseParentData
      (companions.companions.companion block.1)
      (carriers.carrier block.1).outerPopular
      (companions.envelopes.envelope block.1)
  weightClass : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
      (companions.companions.companion block.1)
      (carriers.carrier block.1).outerPopular
      (companions.envelopes.envelope block.1) (parentData block)
  weightRestriction : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
      (companions.companions.companion block.1)
      (carriers.carrier block.1).outerPopular
      (companions.envelopes.envelope block.1) (parentData block)
      (weightClass block)
  sourceWindow : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
      (weightRestriction block).restriction
  sourceBins : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
      (parentData := parentData block)
      (weightRestriction block).restriction (sourceWindow block)
  sync : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    ∀ bin : {bin // bin ∈ (sourceBins block).line.globalBins},
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        (weightRestriction block) (sourceWindow block)
        (sourceBins block) bin
  nested : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    ∀ bin : {bin // bin ∈ (sourceBins block).line.globalBins},
      PureWZ2BalancedSafeOuterPopularCoarseNestedGlobalBinFamilyData
        (sync block bin)

/-- Construct every provenance-bearing regional object up to the nested
coarse global bins. -/
theorem PureWZ2OrdinaryAllBinOuterPopularCompanionData.prepareNestedRegional
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    (companions : PureWZ2OrdinaryAllBinOuterPopularCompanionData carriers)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2OrdinaryAllBinNestedRegionalPreparationData
      carriers companions) := by
  let parentData : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      PureWZ2BalancedSafeOuterPopularCoarseParentData
        (companions.companions.companion block.1)
        (carriers.carrier block.1).outerPopular
        (companions.envelopes.envelope block.1) := fun block =>
    Classical.choice
      ((companions.envelopes.envelope block.1).toCoarseParents
        (companions.companions.companion block.1)
        (carriers.carrier block.1).outerPopular)
  let weightClass : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        (companions.companions.companion block.1)
        (carriers.carrier block.1).outerPopular
        (companions.envelopes.envelope block.1) (parentData block) := fun block =>
    Classical.choice
      ((parentData block).regularizeWeight
        (companions.companions.companion block.1)
        (carriers.carrier block.1).outerPopular
        (companions.envelopes.envelope block.1))
  let weightRestriction : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        (companions.companions.companion block.1)
        (carriers.carrier block.1).outerPopular
        (companions.envelopes.envelope block.1) (parentData block)
        (weightClass block) := fun block =>
    Classical.choice
      (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData.restrictCells
        (companions.companions.companion block.1)
        (carriers.carrier block.1).outerPopular
        (companions.envelopes.envelope block.1) (parentData block)
        (weightClass block))
  let sourceWindow : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        (weightRestriction block).restriction := fun block =>
    Classical.choice
      (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData.toSourceWindow
        (companions.companions.companion block.1)
        (carriers.carrier block.1).outerPopular
        (companions.envelopes.envelope block.1)
        (weightRestriction block).restriction)
  let sourceBins : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData block)
        (weightRestriction block).restriction (sourceWindow block) := fun block =>
    Classical.choice
      (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData.toSourceGlobalBins
        (companions.companions.companion block.1)
        (carriers.carrier block.1).outerPopular
        (companions.envelopes.envelope block.1) (parentData block)
        (weightRestriction block).restriction (sourceWindow block))
  let sync : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ∀ bin : {bin // bin ∈ (sourceBins block).line.globalBins},
        PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
          (weightRestriction block) (sourceWindow block)
          (sourceBins block) bin := fun block bin =>
    Classical.choice
      (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData.prepareSynchronizedBin
        (companions.companions.companion block.1)
        (carriers.carrier block.1).outerPopular
        (companions.envelopes.envelope block.1) (parentData block)
        (weightClass block) (weightRestriction block) (sourceWindow block)
        (sourceBins block) bin
        hbridge hgraphOne hheightAbsorb)
  let nested : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ∀ bin : {bin // bin ∈ (sourceBins block).line.globalBins},
        PureWZ2BalancedSafeOuterPopularCoarseNestedGlobalBinFamilyData
          (sync block bin) := fun block bin =>
    Classical.choice
      (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData.toNestedGlobalBins
        (sync block bin) hgraphOne hheightAbsorb)
  exact ⟨{
    parentData := parentData
    weightClass := weightClass
    weightRestriction := weightRestriction
    sourceWindow := sourceWindow
    sourceBins := sourceBins
    sync := sync
    nested := nested
  }⟩

end Kakeya.Assouad

end
