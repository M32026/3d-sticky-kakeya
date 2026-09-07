import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64P7ScaleConstantAbsorption

/-!
# Final direct-rich assembly for WZ2 Proposition 6.4

This is the terminal Node-5 connection corresponding to `wz2_64.tex`.
The paper objects and quantifier order are:

1. choose `N`, all losses, and every source-scale cutoff;
2. choose the one Proposition-6.3 source below their common minimum;
3. run the P0--P6 hierarchy and construct one joint paper-ED;
4. run one transported combined selection;
5. use that same selected family and final shading for nearby CWA, density,
   union-volume upper, local grains, and global grains.

The final scale is
`pureWZ2Proposition64Lemma35FinalDelta sourceDelta`.  The actual-John scalar
ledger spends `37 * epsilon₂`, is enclosed by the pre-runtime
`48 * epsilon₂` budget, and is absorbed into the target-base
`finalDelta ^ (-nearbyLoss)`.  No final critical-floor witness or
union-volume lower bound occurs in this assembly.
-/

noncomputable section

namespace Kakeya.Assouad

open
  PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

/-- WZ2 Proposition 6.4, assembled on the literal direct-rich production
chain without crossing a witness-erasing intermediate producer boundary. -/
theorem pureWZ2_c2_grains_directRich : PureWZ2C2GrainsStatement := by
  intro subunit criticalExtraction propSticky grains
  rcases propSticky subunit criticalExtraction with ⟨capability⟩
  have grainsOutput := grains subunit criticalExtraction propSticky
  let hbridge : PureWZ2PaperADBridgeStatement := grainsOutput.1
  intro sigma critical outputLoss targetDelta₀ houtputLoss htargetDelta₀
  rcases exists_pureWZ2C2RichEndpointClosureSchedule capability critical
      houtputLoss htargetDelta₀ (show (0 : ℝ) < 1 by norm_num)
      (show (64 : ℝ) ≤ 64 by norm_num) with
    ⟨schedule⟩
  rcases exists_pureWZ2Node05P7CanonicalScaleConstantCutoff schedule with
    ⟨scaleCutoff⟩
  let zero : Fin (schedule.ordinary.mild.levelCount - 1) :=
    ⟨0, by
      have hN := schedule.ordinary.mild.levelCount_ge_two
      omega⟩
  let initialCeiling :=
    schedule.ordinary.ordinaryPrefix.sourceLossCeiling zero
  have hinitialCeiling : 0 < initialCeiling :=
    schedule.ordinary.ordinaryPrefix.sourceLossCeiling_pos zero
  let requestedCutoff := min schedule.commonDelta₀ scaleCutoff.delta₀
  have hrequestedCutoff : 0 < requestedCutoff :=
    lt_min schedule.commonDelta₀_pos scaleCutoff.delta₀_pos
  rcases pureWZ2_hierarchy_initial_reentrant_source_production
      capability critical initialCeiling requestedCutoff
      hinitialCeiling hrequestedCutoff with
    ⟨initialLoss, sourceDelta, hinitialLoss, hinitialCeiling',
      hsourceDelta, hsourceRequested, ⟨initial⟩⟩
  have hsourceSchedule : sourceDelta ≤ schedule.commonDelta₀ :=
    hsourceRequested.trans (min_le_left _ _)
  have hsourceScaleCutoff : sourceDelta ≤ scaleCutoff.delta₀ :=
    hsourceRequested.trans (min_le_right _ _)
  rcases schedule.p7ActualJohnScaleCoversFromInitial hsourceDelta
      hsourceSchedule initial hinitialLoss.le hinitialCeiling'.le hbridge with
    ⟨actual, p6, frostman, raw, quotient, selected, _scaleCovers⟩
  let ed :=
    selected.finalED p6.normalized p6.geometry frostman schedule.p7Scale
  have hnearby :
      WZ2PaperPureCWAAtNearbyScales ed.subfamily.family
        (Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-schedule.p7Scale.nearbyLoss)) := by
    exact p6.p7NearbyCWA_ofScaleCutoff frostman selected scaleCutoff
      hsourceScaleCutoff
  let receipt : FinalQuantitativeReceipt p6.geometry ed outputLoss :=
    {
      nearbyLoss := schedule.p7Scale.nearbyLoss
      nearby := hnearby
      nearby_le_output := schedule.p7Scale.nearbyLoss_lt_output.le
      cwa_absorption := p6.p7TopLevelAbsorption
      dense := p6.p7FinalShadingDense frostman selected
      volume_upper := p6.p7FinalVolumeUpper frostman selected
      local_constant_absorption := p6.p7LocalConstantAbsorption
      global_constant_absorption := p6.p7GlobalConstantAbsorption
    }
  rcases p6.geometry.assembleVerticalRediscretization ed
      selected.selected_nonempty receipt with
    ⟨vertical⟩
  exact
    ⟨pureWZ2Proposition64Lemma35FinalDelta sourceDelta,
      p6.geometry.scales.finalDelta_pos,
      p6.geometry.scales.finalDelta_le_target,
      ⟨vertical.toC2GrainConfiguration⟩⟩

/-- Canonical paper-facing Node-5 theorem. -/
theorem pure_wz2_node05_c2_grains : PureWZ2C2GrainsStatement :=
  pureWZ2_c2_grains_directRich

end Kakeya.Assouad

end
