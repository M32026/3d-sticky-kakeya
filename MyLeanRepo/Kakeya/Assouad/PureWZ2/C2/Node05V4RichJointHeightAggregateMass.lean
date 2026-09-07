import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightAggregate
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSaturatedRelativeMass

/-!
# Aggregate relative mass for the joint-height one-scale output

This is the non-island mass assembly.  It combines both direct-rich
refinement fractions, heavy-slab retention, every block's weighted `Z_lin`
source return, and the mod-64 aggregate mass identity.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

namespace PureWZ2Node05V4RichJointAggregatedShadingData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta finalLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {B₀ threshold : ENNReal}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    {family : PureWZ2Node05V4RichJointBlockFamily
      (eta := eta) pullback B₀ threshold hbridge projection}
    {residue : PureWZ2Node05V4RichJointBlockResidueData family}
    (aggregated : PureWZ2Node05V4RichJointAggregatedShadingData residue)

/-- Exact assembled relative-mass inequality before P0 power absorption. -/
theorem relative_mass
    (hrhoSmall : rhoRequested.1 ≤ 1 / 12)
    (gain blockCost : ENNReal)
    (hgain : ∀ heightIndex,
      gain ≤ Kakeya.realRpowENN
        (family.theorem52 heightIndex).output.ready.ready.deltaGraph
        (finalLoss - 1))
    (hblockCost : ∀ heightIndex,
      24 * ((family.prepared heightIndex).volumePopular.popular.bins : ENNReal) *
          ((family.prepared heightIndex).volumePopular.popular.heightIndices.card :
            ENNReal) ≤
        blockCost) :
    (wz2PaperPureRefinementFraction delta 61 *
        wz2PaperPureRefinementFraction rhoRequested.1 61 *
        current.grain.shading.mass) * gain ≤
      (128 *
        (twoScale.first.fourDegreeReceipts.regularity : ENNReal) ^ 4 *
        blockCost) * aggregated.shading.mass := by
  let HeavySlab := {heightIndex //
    heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}
  let regularity : ENNReal :=
    twoScale.first.fourDegreeReceipts.regularity
  let floor : ENNReal :=
    (twoScale.first.fourDegreeReceipts.fineDegreeFloor *
      twoScale.first.fourDegreeReceipts.muFine : ℕ)
  have hblock :
      ∀ heightIndex : HeavySlab,
        (floor * gain) *
            volume (pullback.standardSqrtSlabSourceRegion
              heightIndex.1.1) ≤
          blockCost * (family.lift heightIndex).shading.mass := by
    intro heightIndex
    have hgainAt :
        gain ≤ Kakeya.realRpowENN
          (family.theorem52 heightIndex).output.ready.ready.deltaGraph
            (finalLoss - 1) := by
      simpa [HeavySlab] using hgain heightIndex
    have hblockCostAt :
        24 * ((family.prepared heightIndex).volumePopular.popular.bins :
            ENNReal) *
          ((family.prepared heightIndex).volumePopular.popular.heightIndices.card :
            ENNReal) ≤ blockCost := by
      simpa [HeavySlab] using hblockCost heightIndex
    calc
      (floor * gain) *
            volume (pullback.standardSqrtSlabSourceRegion
              heightIndex.1.1) ≤
          (floor * Kakeya.realRpowENN
            (family.theorem52 heightIndex).output.ready.ready.deltaGraph
              (finalLoss - 1)) *
            volume (pullback.standardSqrtSlabSourceRegion
              heightIndex.1.1) := by
        gcongr
      _ ≤ (24 *
          ((family.prepared heightIndex).volumePopular.popular.bins :
            ENNReal) *
          ((family.prepared heightIndex).volumePopular.popular.heightIndices.card :
            ENNReal)) *
          (family.theorem52 heightIndex).sourceMass.shading.mass := by
        simpa [floor] using
          (family.theorem52 heightIndex).sourceSlab_weighted_mass_return_whole
      _ ≤ blockCost *
          (family.theorem52 heightIndex).sourceMass.shading.mass := by
        gcongr
      _ ≤ blockCost * (family.lift heightIndex).shading.mass := by
        gcongr
        exact (family.lift heightIndex).sourceCore_mass_le
  have hblocks :
      (floor * gain) *
          ∑ heightIndex : HeavySlab,
            volume (pullback.standardSqrtSlabSourceRegion
              heightIndex.1.1) ≤
        blockCost *
          ∑ heightIndex : HeavySlab,
            (family.lift heightIndex).shading.mass := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun heightIndex _ => hblock heightIndex
  have hslabMass :
      ∑ heightIndex : HeavySlab,
          (pullback.standardSqrtSlabSourceShading heightIndex.1.1).mass ≤
        regularity * floor *
          ∑ heightIndex : HeavySlab,
            volume (pullback.standardSqrtSlabSourceRegion
              heightIndex.1.1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun heightIndex _ => by
      simpa [regularity, floor, Nat.cast_mul, mul_assoc] using
        pullback.standardSqrtSlabSourceShading_mass_upper heightIndex.1.1
  have hpullback :
      pullback.shading.mass * gain ≤
        (2 * regularity ^ 2 * blockCost) *
          ∑ heightIndex : HeavySlab,
            (family.lift heightIndex).shading.mass := by
    calc
      pullback.shading.mass * gain ≤
          (2 * regularity *
            ∑ heightIndex : HeavySlab,
              (pullback.standardSqrtSlabSourceShading
                heightIndex.1.1).mass) * gain := by
        have hheavy := pullback.heavySlabs_retains_mass
        rw [← Finset.sum_attach] at hheavy
        gcongr
        simpa [HeavySlab, regularity] using hheavy
      _ ≤ (2 * regularity *
            (regularity * floor *
              ∑ heightIndex : HeavySlab,
                volume (pullback.standardSqrtSlabSourceRegion
                  heightIndex.1.1))) * gain := by
        gcongr
      _ = 2 * regularity ^ 2 *
          ((floor * gain) *
            ∑ heightIndex : HeavySlab,
              volume (pullback.standardSqrtSlabSourceRegion
                heightIndex.1.1)) := by ring
      _ ≤ 2 * regularity ^ 2 *
          (blockCost *
            ∑ heightIndex : HeavySlab,
              (family.lift heightIndex).shading.mass) := by
        gcongr
      _ = (2 * regularity ^ 2 * blockCost) *
          ∑ heightIndex : HeavySlab,
            (family.lift heightIndex).shading.mass := by ring
  have hsource := pullback.mass_relative_lower hrhoSmall
  calc
    (wz2PaperPureRefinementFraction delta 61 *
          wz2PaperPureRefinementFraction rhoRequested.1 61 *
          current.grain.shading.mass) * gain ≤
        ((regularity ^ 2) * pullback.shading.mass) * gain := by
      exact mul_le_mul_left (by simpa [regularity] using hsource) gain
    _ = regularity ^ 2 * (pullback.shading.mass * gain) := by ring
    _ ≤ regularity ^ 2 *
        ((2 * regularity ^ 2 * blockCost) *
          ∑ heightIndex : HeavySlab,
            (family.lift heightIndex).shading.mass) := by
      gcongr
    _ = (2 * regularity ^ 4 * blockCost) *
        ∑ heightIndex : HeavySlab,
          (family.lift heightIndex).shading.mass := by ring
    _ ≤ (2 * regularity ^ 4 * blockCost) *
        (64 * aggregated.shading.mass) := by
      gcongr
      simpa [HeavySlab] using
        (PureWZ2Node05V4RichJointBlockResidueData.total_lift_mass_le
          residue aggregated)
    _ = (128 * regularity ^ 4 * blockCost) *
        aggregated.shading.mass := by ring

/-- A single P0 power absorption turns the assembled relative-mass inequality
into the density required by the generic re-entry-trace one-scale theorem. -/
theorem dense_of_relative_mass
    (hrhoSmall : rhoRequested.1 ≤ 1 / 12)
    (densityLoss : ℝ)
    (gain blockCost : ENNReal)
    (hgain : ∀ heightIndex,
      gain ≤ Kakeya.realRpowENN
        (family.theorem52 heightIndex).output.ready.ready.deltaGraph
        (finalLoss - 1))
    (hblockCost : ∀ heightIndex,
      24 * ((family.prepared heightIndex).volumePopular.popular.bins : ENNReal) *
          ((family.prepared heightIndex).volumePopular.popular.heightIndices.card :
            ENNReal) ≤
        blockCost)
    (hblockCostPos : 0 < blockCost)
    (hblockCostTop : blockCost ≠ ⊤)
    (habsorb :
      (128 *
          (twoScale.first.fourDegreeReceipts.regularity : ENNReal) ^ 4 *
          blockCost) *
          Kakeya.realRpowENN delta densityLoss ≤
        (wz2PaperPureRefinementFraction delta 61 *
          wz2PaperPureRefinementFraction rhoRequested.1 61 *
          Kakeya.realRpowENN delta inputLoss) * gain) :
    aggregated.shading.IsLambdaDense
      (Kakeya.realRpowENN delta densityLoss) := by
  let totalCost : ENNReal :=
    128 * (twoScale.first.fourDegreeReceipts.regularity : ENNReal) ^ 4 *
      blockCost
  let bodyMass : ENNReal := (wz1PaperBodyFamily current.grain.family).mass
  have hregularityPos : 0 <
      (twoScale.first.fourDegreeReceipts.regularity : ENNReal) := by
    exact_mod_cast twoScale.first.fourDegreeReceipts.regularity_pos
  have htotalCostPos : 0 < totalCost := by
    dsimp only [totalCost]
    have hpowPos : 0 <
        (twoScale.first.fourDegreeReceipts.regularity : ENNReal) ^ 4 :=
      ENNReal.pow_pos hregularityPos 4
    exact ENNReal.mul_pos
      (ENNReal.mul_pos (by norm_num) hpowPos.ne').ne'
      hblockCostPos.ne'
  have htotalCostTop : totalCost ≠ ⊤ := by
    dsimp only [totalCost]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
      hblockCostTop
  have hrelative := aggregated.relative_mass
    hrhoSmall gain blockCost hgain hblockCost
  have hsourceDense :
      Kakeya.realRpowENN delta inputLoss * bodyMass ≤
        current.grain.shading.mass := by
    simpa only [bodyMass, Kakeya.Streamlined.Shading.IsLambdaDense] using
      current.grain.extremal.dense
  have hscaled :
      totalCost *
          (Kakeya.realRpowENN delta densityLoss * bodyMass) ≤
        totalCost * aggregated.shading.mass := by
    calc
      totalCost *
            (Kakeya.realRpowENN delta densityLoss * bodyMass) =
          (totalCost * Kakeya.realRpowENN delta densityLoss) *
            bodyMass := by ring
      _ ≤ ((wz2PaperPureRefinementFraction delta 61 *
            wz2PaperPureRefinementFraction rhoRequested.1 61 *
            Kakeya.realRpowENN delta inputLoss) * gain) *
          bodyMass := by
        exact mul_le_mul_left (by simpa [totalCost] using habsorb) bodyMass
      _ = (wz2PaperPureRefinementFraction delta 61 *
            wz2PaperPureRefinementFraction rhoRequested.1 61 *
            (Kakeya.realRpowENN delta inputLoss * bodyMass)) * gain := by ring
      _ ≤ (wz2PaperPureRefinementFraction delta 61 *
            wz2PaperPureRefinementFraction rhoRequested.1 61 *
            current.grain.shading.mass) * gain := by
        gcongr
      _ ≤ totalCost * aggregated.shading.mass := by
        simpa [totalCost] using hrelative
  change Kakeya.realRpowENN delta densityLoss * bodyMass ≤
    aggregated.shading.mass
  calc
    Kakeya.realRpowENN delta densityLoss * bodyMass =
        totalCost⁻¹ *
          (totalCost *
            (Kakeya.realRpowENN delta densityLoss * bodyMass)) := by
      rw [← mul_assoc,
        ENNReal.inv_mul_cancel htotalCostPos.ne' htotalCostTop, one_mul]
    _ ≤ totalCost⁻¹ * (totalCost * aggregated.shading.mass) :=
      mul_le_mul_right hscaled _
    _ = aggregated.shading.mass := by
      rw [← mul_assoc,
        ENNReal.inv_mul_cancel htotalCostPos.ne' htotalCostTop, one_mul]

/-- Final non-island P3 assembly: the aggregate density and geometry feed the
generic same-source re-entry theorem and return one concrete one-scale
output. -/
theorem toOneScale_of_reentryTrace
    {structuralBudget : ℝ}
    (geometry : PureWZ2Node05V4RichJointAggregatedGeometryData aggregated)
    (floorSchedule : PureWZ2ReentryTraceFloorSchedule
      sigma finalLoss structuralBudget)
    (hinputDensity : inputLoss ≤ floorSchedule.densityLoss)
    (htraceSource :
      current.ordinaryLoss ≤ floorSchedule.traceSourceCeiling)
    (hdeltaSchedule : delta ≤ floorSchedule.delta₀)
    (hrhoSmall : rhoRequested.1 ≤ 1 / 12)
    (gain blockCost : ENNReal)
    (hgain : ∀ heightIndex,
      gain ≤ Kakeya.realRpowENN
        (family.theorem52 heightIndex).output.ready.ready.deltaGraph
        (finalLoss - 1))
    (hblockCost : ∀ heightIndex,
      24 * ((family.prepared heightIndex).volumePopular.popular.bins : ENNReal) *
          ((family.prepared heightIndex).volumePopular.popular.heightIndices.card :
            ENNReal) ≤
        blockCost)
    (hblockCostPos : 0 < blockCost)
    (hblockCostTop : blockCost ≠ ⊤)
    (habsorb :
      (128 *
          (twoScale.first.fourDegreeReceipts.regularity : ENNReal) ^ 4 *
          blockCost) *
          Kakeya.realRpowENN delta floorSchedule.densityLoss ≤
        (wz2PaperPureRefinementFraction delta 61 *
          wz2PaperPureRefinementFraction rhoRequested.1 61 *
          Kakeya.realRpowENN delta inputLoss) * gain) :
    Nonempty (PureWZ2LocallyLinearOneScaleData
      current.grain finalLoss geometry.scale) := by
  have hdense := aggregated.dense_of_relative_mass
    hrhoSmall floorSchedule.densityLoss gain blockCost hgain hblockCost
    hblockCostPos hblockCostTop habsorb
  exact pureWZ2_literalCurrentSourceOneScale_of_reentryTrace
    aggregated.shading aggregated.subshading_current aggregated.whole_cells
    floorSchedule hinputDensity htraceSource hdeltaSchedule hdense
    current.reentry (PureWZ2Node05V4RichJointBlockResidueData.toLiteralGeometry
      residue geometry)

end PureWZ2Node05V4RichJointAggregatedShadingData

end Kakeya.Assouad

end
