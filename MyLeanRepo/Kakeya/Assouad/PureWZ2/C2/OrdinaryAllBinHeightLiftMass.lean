import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryAllBinHeightLiftMultiWindow
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryAllBinExactMassBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseRichHeightSaturation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalRelativeMassBudget

/-!
# Internal-height source-mass budget for the ordinary all-bin construction

For each chosen genuine-coarse graph, Alternative A selects a subset of its
own volume-popular heights.  We saturate those height layers by complete
first-sticky `rho` cells and pull the resulting region back through the first
balanced cover.  The exact pullback mass identity and the common coarse-volume
factor replace the invalid requirement that these heights be literally among
the earlier source-popular heights.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The internally constructed whole-cell saturation for every regularized
source block. -/
structure PureWZ2OrdinaryAllBinRichHeightSaturationFamilyData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {allBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers}
    {coarseBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins}
    {selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
      (volumeLoss := volumeLoss) coarseBins}
    (rich : PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) selected) where
  saturation : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    PureWZ2SourceFixedBinCoarseRichHeightSaturationData
      (rich.rich block).heightLift

namespace PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData

/-- Construct all whole-cell rich-height saturations from the already chosen
dependent rich pipelines. -/
theorem toRichHeightSaturations
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {allBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers}
    {coarseBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins}
    {selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
      (volumeLoss := volumeLoss) coarseBins}
    (rich : PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) selected) :
    Nonempty (PureWZ2OrdinaryAllBinRichHeightSaturationFamilyData rich) := by
  have hsaturation : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      Nonempty (PureWZ2SourceFixedBinCoarseRichHeightSaturationData
        (rich.rich block).heightLift) := fun block =>
    (rich.rich block).toRichHeightSaturation
  exact ⟨{ saturation := fun block => Classical.choice (hsaturation block) }⟩

end PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData

namespace PureWZ2OrdinaryAllBinRichHeightSaturationFamilyData

variable
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {allBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers}
    {coarseBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins}
    {selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
      (volumeLoss := volumeLoss) coarseBins}
    {rich : PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) selected}

/-- One source block reaches its final height lift through the internal
genuine-coarse popular-height saturation and exact balanced pullback. -/
theorem block_source_to_heightLift_mass_cube
    (saturations :
      PureWZ2OrdinaryAllBinRichHeightSaturationFamilyData rich)
    (block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe})
    (outerCost binCost : ENNReal)
    (houterCost :
      (2 * (carriers.carrier block.1).outerPopular.popular.bins : ENNReal) ≤
        outerCost)
    (hbinCost :
      ((allBins.binFamily block.1).line.globalBins.card : ENNReal) *
          pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta ≤ binCost)
    {extraLoss : ℝ}
    (hextraPower :
      ((rich.pipeline block).preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow
          ((coarseBins.coarseFamily block.1).prep
            (selected.chosenBin block)).graphScale (-extraLoss)) :
    volume (safe.blockWindow block.1).shading.union *
          twoScale.fine.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass ≤
      2 * outerCost * binCost *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss *
        (rich.rich block).heightLift.shading.mass *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  have hsource := rich.source_window_to_chosen_graph
    block outerCost binCost houterCost hbinCost
  have hgraph := (saturations.saturation block).graph_height_mass_cube_bound
    hextraPower
  calc
    _ = (volume (safe.blockWindow block.1).shading.union *
          twoScale.fine.balanced.cellMass) *
        pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass := by ring
    _ ≤ (2 * outerCost * binCost *
          volume ((coarseBins.coarseFamily block.1).prep
            (selected.chosenBin block)).shadow.union) *
        pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass := by gcongr
    _ = 2 * outerCost * binCost *
        (volume ((coarseBins.coarseFamily block.1).prep
            (selected.chosenBin block)).shadow.union *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass) := by ring
    _ ≤ 2 * outerCost * binCost *
        (PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho extraLoss *
          (rich.rich block).heightLift.shading.mass *
          volume (wz1PaperGridCube rho (0, 0, 0))) := by gcongr
    _ = _ := by ring

/-- Sum the same-block internal-height estimates and pay the explicit
source-block regularization factor four. -/
theorem aggregate_heightLift_mass_cube_bound
    (saturations :
      PureWZ2OrdinaryAllBinRichHeightSaturationFamilyData rich)
    (outerCost binCost : ENNReal)
    (houterCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      (2 * (carriers.carrier block.1).outerPopular.popular.bins : ENNReal) ≤
        outerCost)
    (hbinCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((allBins.binFamily block.1).line.globalBins.card : ENNReal) *
          pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta ≤ binCost)
    {extraLoss : ℝ}
    (hextraPower : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((rich.pipeline block).preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow
          ((coarseBins.coarseFamily block.1).prep
            (selected.chosenBin block)).graphScale (-extraLoss)) :
    volume prepared.shadow.union * twoScale.fine.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass ≤
      8 * outerCost * binCost *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss *
        (∑ block :
          {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
          (rich.rich block).heightLift.shading.mass) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  let blocks := pureWZ2OrdinaryPaperOrderRegularizedBlocks safe
  let fineMass := twoScale.fine.balanced.cellMass
  let floor := pureWZ2SourceHorizontalRichFloor rho finalLoss
  let incidenceMass := twoScale.coarse.balanced.incidenceMass
  let cubeVolume := volume (wz1PaperGridCube rho (0, 0, 0))
  let heightCost :=
    PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
      rho extraLoss
  let cost := 2 * outerCost * binCost * heightCost
  have hsource : volume prepared.shadow.union ≤
      4 * ∑ block ∈ blocks,
        volume (safe.blockWindow block).shading.union := by
    simpa [blocks] using safe.regularizedBlocks_retains_quarter
  have hindexed :
      (∑ block ∈ blocks, volume (safe.blockWindow block).shading.union) =
        ∑ block : {block // block ∈ blocks},
          volume (safe.blockWindow block.1).shading.union :=
    Finset.sum_subtype blocks (fun _ => Iff.rfl) _
  have hlocal :
      (∑ block : {block // block ∈ blocks},
          volume (safe.blockWindow block.1).shading.union) *
            fineMass * floor * incidenceMass ≤
        cost * (∑ block : {block // block ∈ blocks},
          (rich.rich block).heightLift.shading.mass) * cubeVolume := by
    calc
      _ = ∑ block : {block // block ∈ blocks},
          (volume (safe.blockWindow block.1).shading.union *
            fineMass * floor * incidenceMass) := by
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      _ ≤ ∑ block : {block // block ∈ blocks},
          cost * (rich.rich block).heightLift.shading.mass * cubeVolume := by
        exact Finset.sum_le_sum fun block _ => by
          simpa [blocks, fineMass, floor, incidenceMass, cubeVolume,
            heightCost, cost] using
            saturations.block_source_to_heightLift_mass_cube block
              outerCost binCost (houterCost block) (hbinCost block)
              (hextraPower block)
      _ = cost * (∑ block : {block // block ∈ blocks},
          (rich.rich block).heightLift.shading.mass) * cubeVolume := by
        rw [Finset.mul_sum]
        rw [Finset.sum_mul]
  calc
    volume prepared.shadow.union * fineMass * floor * incidenceMass ≤
        (4 * ∑ block ∈ blocks,
          volume (safe.blockWindow block).shading.union) *
            fineMass * floor * incidenceMass := by gcongr
    _ = 4 * ((∑ block : {block // block ∈ blocks},
          volume (safe.blockWindow block.1).shading.union) *
            fineMass * floor * incidenceMass) := by rw [hindexed]; ring
    _ ≤ 4 * (cost * (∑ block : {block // block ∈ blocks},
          (rich.rich block).heightLift.shading.mass) * cubeVolume) := by
      gcongr
    _ = _ := by simp only [cost, heightCost, blocks, fineMass, floor,
      incidenceMass, cubeVolume]; ring

/-- After mod-64 selection, the internally saturated rich heights control the
actual final original-family height-lift shading. -/
theorem selected_heightLift_mass_cube_bound
    (saturations :
      PureWZ2OrdinaryAllBinRichHeightSaturationFamilyData rich)
    (residueData : rich.SelectedHeightLiftResidueData)
    (outerCost binCost : ENNReal)
    (houterCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      (2 * (carriers.carrier block.1).outerPopular.popular.bins : ENNReal) ≤
        outerCost)
    (hbinCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((allBins.binFamily block.1).line.globalBins.card : ENNReal) *
          pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta ≤ binCost)
    {extraLoss : ℝ}
    (hextraPower : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((rich.pipeline block).preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow
          ((coarseBins.coarseFamily block.1).prep
            (selected.chosenBin block)).graphScale (-extraLoss)) :
    volume prepared.shadow.union * twoScale.fine.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass ≤
      512 * outerCost * binCost *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss * residueData.shading.mass *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  calc
    _ ≤ 8 * outerCost * binCost *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss *
        (∑ block :
          {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
          (rich.rich block).heightLift.shading.mass) *
        volume (wz1PaperGridCube rho (0, 0, 0)) :=
      saturations.aggregate_heightLift_mass_cube_bound outerCost binCost
        houterCost hbinCost hextraPower
    _ ≤ 8 * outerCost * binCost *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss * (64 * residueData.shading.mass) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
      gcongr
      exact residueData.total_mass_le_shading_mass
    _ = _ := by ring

/-- Cancel the common coarse volume and all finite positive costs to obtain
the density required by the final source-family grain refinement. -/
theorem dense_of_internal_height_saturation
    (saturations :
      PureWZ2OrdinaryAllBinRichHeightSaturationFamilyData rich)
    (residueData : rich.SelectedHeightLiftResidueData)
    {extraLoss structuralLoss : ℝ}
    (outerCost binCost : ENNReal)
    (houterCostPos : 0 < outerCost) (houterCostTop : outerCost ≠ ⊤)
    (hbinCostPos : 0 < binCost) (hbinCostTop : binCost ≠ ⊤)
    (houterCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      (2 * (carriers.carrier block.1).outerPopular.popular.bins : ENNReal) ≤
        outerCost)
    (hbinCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((allBins.binFamily block.1).line.globalBins.card : ENNReal) *
          pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta ≤ binCost)
    (hextraPower : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((rich.pipeline block).preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow
          ((coarseBins.coarseFamily block.1).prep
            (selected.chosenBin block)).graphScale (-extraLoss))
    (hstructural :
      (512 * outerCost * binCost *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho extraLoss) *
          volume (wz1PaperGridCube rho (0, 0, 0)) *
          (Kakeya.realRpowENN delta structuralLoss *
            (wz1PaperBodyFamily source.family).mass) ≤
        volume prepared.shadow.union * twoScale.fine.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass) :
    residueData.shading.IsLambdaDense
      (Kakeya.realRpowENN delta structuralLoss) := by
  let heightCost :=
    PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
      rho extraLoss
  let cost : ENNReal := 512 * outerCost * binCost * heightCost
  let cubeVolume := volume (wz1PaperGridCube rho (0, 0, 0))
  let target := Kakeya.realRpowENN delta structuralLoss *
    (wz1PaperBodyFamily source.family).mass
  have hall := saturations.selected_heightLift_mass_cube_bound residueData
    outerCost binCost houterCost hbinCost hextraPower
  have hscaled : (cost * cubeVolume) * target ≤
      (cost * cubeVolume) * residueData.shading.mass := by
    calc
      (cost * cubeVolume) * target ≤
          volume prepared.shadow.union * twoScale.fine.balanced.cellMass *
            pureWZ2SourceHorizontalRichFloor rho finalLoss *
            twoScale.coarse.balanced.incidenceMass := by
        simpa [cost, target, cubeVolume, heightCost, mul_comm, mul_left_comm,
          mul_assoc] using hstructural
      _ ≤ cost * residueData.shading.mass * cubeVolume := by
        simpa [cost, cubeVolume, heightCost] using hall
      _ = (cost * cubeVolume) * residueData.shading.mass := by ring
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hcubePos : 0 < cubeVolume := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_pos.mpr (pow_pos hrho 3)
  have hcubeTop : cubeVolume ≠ ⊤ := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_ne_top
  have hcostPos : 0 < cost := by
    dsimp only [cost, heightCost]
    have hheightPos : 0 <
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss := by
      unfold PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
      unfold PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap
      have hrho : 0 < rho := by
        rw [← twoScale.rhoRequested_eq]
        exact twoScale.coarseGrains.extremal.delta_pos
      apply ENNReal.mul_pos
      · apply (ENNReal.ofReal_pos.mpr ?_).ne'
        exact mul_pos (by norm_num)
          (Real.rpow_pos_of_pos (by positivity : 0 < 256 * rho) _)
      · apply (ENNReal.ofReal_pos.mpr ?_).ne'
        exact div_pos (by norm_num) (Real.sqrt_pos.mpr (by positivity))
    exact ENNReal.mul_pos
      (ENNReal.mul_pos
        (ENNReal.mul_pos (by norm_num) houterCostPos.ne').ne'
          hbinCostPos.ne').ne' hheightPos.ne'
  have hcostTop : cost ≠ ⊤ := by
    dsimp only [cost, heightCost]
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) houterCostTop) hbinCostTop
    · unfold PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
      unfold PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hcommonPos : 0 < cost * cubeVolume := ENNReal.mul_pos
    hcostPos.ne' hcubePos.ne'
  have hcommonTop : cost * cubeVolume ≠ ⊤ :=
    ENNReal.mul_ne_top hcostTop hcubeTop
  have hdense : target ≤ residueData.shading.mass :=
    (ENNReal.mul_le_mul_iff_left hcommonPos.ne' hcommonTop).mp (by
      simpa [mul_comm] using hscaled)
  simpa [Kakeya.Streamlined.Shading.IsLambdaDense, target] using hdense

/-- Final one-scale assembly with no external rich-height provenance
certificate. -/
theorem toOneScaleOfInternalHeightBudgets
    (saturations :
      PureWZ2OrdinaryAllBinRichHeightSaturationFamilyData rich)
    (residueData : rich.SelectedHeightLiftResidueData)
    {extraLoss structuralLoss : ℝ}
    (outerCost binCost : ENNReal)
    (houterCostPos : 0 < outerCost) (houterCostTop : outerCost ≠ ⊤)
    (hbinCostPos : 0 < binCost) (hbinCostTop : binCost ≠ ⊤)
    (houterCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      (2 * (carriers.carrier block.1).outerPopular.popular.bins : ENNReal) ≤
        outerCost)
    (hbinCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((allBins.binFamily block.1).line.globalBins.card : ENNReal) *
          pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta ≤ binCost)
    (hextraPower : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((rich.pipeline block).preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow
          ((coarseBins.coarseFamily block.1).prep
            (selected.chosenBin block)).graphScale (-extraLoss))
    (hstructural :
      (512 * outerCost * binCost *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho extraLoss) *
          volume (wz1PaperGridCube rho (0, 0, 0)) *
          (Kakeya.realRpowENN delta structuralLoss *
            (wz1PaperBodyFamily source.family).mass) ≤
        volume prepared.shadow.union * twoScale.fine.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass)
    (hinputStructural : inputLoss ≤ structuralLoss)
    (hstructuralFinal : structuralLoss ≤ finalLoss)
    (grainProducer :
      ∀ targetFamily : Kakeya.Streamlined.TubeFamily delta,
        ∀ targetShading : WZ1PaperTubeShading targetFamily,
          WZ1PaperIsLineClass targetFamily →
          WZ2PaperCroppedIsExtremal
              sigma structuralLoss targetFamily targetShading →
            Nonempty
              (PureWZ2GrainRefinementData targetShading sigma finalLoss)) :
    Nonempty (PureWZ2LocallyLinearOneScaleData source finalLoss
      (pureWZ2SourceHorizontalFinalScale rho)) := by
  apply residueData.toOneScaleOfGrainProducer
    hinputStructural hstructuralFinal grainProducer
  exact saturations.dense_of_internal_height_saturation residueData
    outerCost binCost houterCostPos houterCostTop hbinCostPos hbinCostTop
    houterCost hbinCost hextraPower hstructural

end PureWZ2OrdinaryAllBinRichHeightSaturationFamilyData

end Kakeya.Assouad

end
