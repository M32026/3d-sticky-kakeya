import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantCurrentCoarseGrainProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05AnchoredSynchronizedSecondOwnerCall
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseGlobalPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.AnchoredTwoScaleSourceRelativeAD

/-!
# Anchored two-scale receipt for ordinary production

This receipt replaces the production dependency on
`PureWZ2OneScaleTwoScaleStickyData`.  It retains the two exact balanced owner
covers, uses the supplied current global slope, and evaluates every local
normal at a genuine occupied point of the supplied current shading.

The second fine cells are pulled back through the first exact balanced cover
before any AD argument.  Thus global AD is inherited by literal restriction
from the current source, rather than assumed on the enlarged second fine
union.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2HierarchyReentrantAnchoredTwoScaleReceipt
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho grainLoss
      outputEta selectedLoss sourceLoss seedLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    {firstOverlay : PureWZ2HierarchyReentrantFirstOverlayReceipt
      (current := current) kernelOutput}
    (anchored :
      PureWZ2HierarchyReentrantCurrentCoarseAnchoredReceipt firstOverlay)
    {selectedNormalizationExponent secondSeedLogExponent firstLogExponent : ℕ}
    (selection : PureWZ2Node05AnchoredSynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (sourceLoss := sourceLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      firstOverlay.ambient anchored.toAnchoredCoarseSource)
    (sqrtRequested : WZ2PaperRequestedScale kernelOutput.requested.1)
    (stage : PureWZ2Node05AnchoredSynchronizedTwoCallStage
      (seedLoss := seedLoss)
      (outputLoss := lossSchedule.ownerSchedule.stickyLoss)
      (firstLogExponent := firstLogExponent)
      (secondSeedLogExponent := secondSeedLogExponent)
      firstOverlay.ambient anchored.toAnchoredCoarseSource selection
      sqrtRequested) where
  sourceRelative :
    PureWZ2AnchoredSourceRelativeFineSelection
      stage.firstReceipt.toNode5StickyData
      stage.second.output.toNode5StickyData
  global_constant_absorption :
    Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN kernelOutput.requested.1 (-selectedLoss)
  selectedLoss_eq : selectedLoss = lossSchedule.middleLoss
  sqrtRequested_eq :
    sqrtRequested.1 = Real.sqrt kernelOutput.requested.1

namespace PureWZ2HierarchyReentrantAnchoredTwoScaleReceipt

variable
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho grainLoss
      outputEta selectedLoss sourceLoss seedLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    {firstOverlay : PureWZ2HierarchyReentrantFirstOverlayReceipt
      (current := current) kernelOutput}
    {anchored :
      PureWZ2HierarchyReentrantCurrentCoarseAnchoredReceipt firstOverlay}
    {selectedNormalizationExponent secondSeedLogExponent firstLogExponent : ℕ}
    {selection : PureWZ2Node05AnchoredSynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (sourceLoss := sourceLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      firstOverlay.ambient anchored.toAnchoredCoarseSource}
    {sqrtRequested : WZ2PaperRequestedScale kernelOutput.requested.1}
    {stage : PureWZ2Node05AnchoredSynchronizedTwoCallStage
      (seedLoss := seedLoss)
      (outputLoss := lossSchedule.ownerSchedule.stickyLoss)
      (firstLogExponent := firstLogExponent)
      (secondSeedLogExponent := secondSeedLogExponent)
      firstOverlay.ambient anchored.toAnchoredCoarseSource selection
      sqrtRequested}
    (receipt : PureWZ2HierarchyReentrantAnchoredTwoScaleReceipt
      (grainLoss := grainLoss) anchored selection sqrtRequested stage)

/-- The pre-scheduled scalar budget absorbs the current AD constant at the
first sticky radius. -/
theorem global_constant_absorption_of_schedule
    (hinput : 0 < inputLoss)
    (hinputCeiling : inputLoss ≤ sourceLossCeiling)
    (hdeltaSmall : delta ≤ lossSchedule.scalarDelta₀)
    (hrequestedUpper :
      kernelOutput.requested.1 ≤ Real.rpow delta outputLoss)
    (hselectedLoss : selectedLoss = lossSchedule.middleLoss) :
    Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN kernelOutput.requested.1 (-selectedLoss) := by
  let sourceC := Kakeya.realRpowENN delta (-inputLoss)
  let targetC :=
    Kakeya.realRpowENN kernelOutput.requested.1 (-lossSchedule.middleLoss)
  have hraw := lossSchedule.localConstant hinput hinputCeiling
    current.grain.extremal.delta_pos
    (hdeltaSmall.trans lossSchedule.scalarDelta₀_localConstant)
    (current.grain.extremal.delta_pos.trans_le
      kernelOutput.requested.property.1)
    kernelOutput.requested.property.2 hrequestedUpper
  have hscaled : (350 : ENNReal) * sourceC ≤ 350 * targetC := by
    calc
      (350 : ENNReal) * sourceC =
          35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) := by
            simp [sourceC]
            ring
      _ ≤ 19 * (10 * Kakeya.realRpowENN kernelOutput.requested.1
            (-lossSchedule.middleLoss)) := hraw
      _ = 190 * targetC := by
            simp [targetC]
            ring
      _ ≤ 350 * targetC := by
        gcongr
        norm_num
  rw [hselectedLoss]
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp hscaled

/-- Construct the anchored receipt by selecting the exact second-stage cells
on the genuine first-stage fine carrier.  The only extra argument is the
scalar loss absorption, not an AD receipt. -/
theorem nonempty_of_global_constant_absorption
    (hconstant :
      Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN kernelOutput.requested.1 (-selectedLoss))
    (hselectedLoss : selectedLoss = lossSchedule.middleLoss)
    (hsqrt : sqrtRequested.1 = Real.sqrt kernelOutput.requested.1) :
    Nonempty (PureWZ2HierarchyReentrantAnchoredTwoScaleReceipt
      (grainLoss := grainLoss) anchored selection sqrtRequested stage) := by
  rcases pureWZ2_anchored_sourceRelativeFineSelection
      stage.firstReceipt.toNode5StickyData
      stage.second.output.toNode5StickyData with
    ⟨sourceRelative⟩
  exact ⟨{
    sourceRelative := sourceRelative
    global_constant_absorption := hconstant
    selectedLoss_eq := hselectedLoss
    sqrtRequested_eq := hsqrt
  }⟩

/-- Runtime constructor using only the scheduled scalar inequalities and the
two exact owner outputs. -/
theorem nonempty_of_schedule
    (hinput : 0 < inputLoss)
    (hinputCeiling : inputLoss ≤ sourceLossCeiling)
    (hdeltaSmall : delta ≤ lossSchedule.scalarDelta₀)
    (hrequestedUpper :
      kernelOutput.requested.1 ≤ Real.rpow delta outputLoss)
    (hselectedLoss : selectedLoss = lossSchedule.middleLoss)
    (hsqrt : sqrtRequested.1 = Real.sqrt kernelOutput.requested.1) :
    Nonempty (PureWZ2HierarchyReentrantAnchoredTwoScaleReceipt
      (grainLoss := grainLoss) anchored selection sqrtRequested stage) :=
  nonempty_of_global_constant_absorption
    (global_constant_absorption_of_schedule
      hinput hinputCeiling hdeltaSmall hrequestedUpper
      hselectedLoss) hselectedLoss hsqrt

/-- The supplied current global AD remains available on its literal carrier. -/
theorem current_global_ad
    (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    PureWZ2PaperADSet1
      (scalarProjection
        (globalGrainDirection (current.grain.globalGrains.slope z))
        (horizontalSlice current.grain.shading.union z))
      delta (1 - sigma) (Kakeya.realRpowENN delta (-inputLoss)) :=
  current.grain.globalGrains.global_ad z hz

/-- Global AD on the exact selected-cell source pullback.  No AD witness is
an input to the anchored receipt. -/
theorem fine_global_ad
    (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    PureWZ2PaperADSet1
      (scalarProjection
        (globalGrainDirection (current.grain.globalGrains.slope z))
        (horizontalSlice receipt.sourceRelative.shading.union z))
      kernelOutput.requested.1 (1 - sigma)
      (Kakeya.realRpowENN kernelOutput.requested.1 (-selectedLoss)) :=
  receipt.sourceRelative.global_ad receipt.global_constant_absorption z hz

/-- Lift a selected coarse point to the honest source-witness subtype. -/
noncomputable def coarsePoint
    (point : {point : Point3 // point ∈ selection.overlay.union}) :
    {point : Point3 //
      point ∈ anchored.provenance.sourceWitness.shading.union} :=
  ⟨point, by
    rcases point.property with ⟨index, hpoint⟩
    exact ⟨selection.selectedCoarse.embedding index, hpoint⟩⟩

/-- Genuine occupied current point anchoring a selected coarse position. -/
noncomputable def sourceAnchor
    (point : {point : Point3 // point ∈ selection.overlay.union}) :
    {point : Point3 // point ∈ current.grain.shading.union} :=
  anchored.provenance.sourcePoint
    (coarsePoint (selection := selection) point)

/-- Every anchored normal is definitionally the supplied current plane map. -/
noncomputable def sourceNormal
    (point : {point : Point3 // point ∈ selection.overlay.union}) : Point3 :=
  current.grain.localGrains.planeMap
    (sourceAnchor (anchored := anchored) (selection := selection) point)

theorem sourceNormal_unit
    (point : {point : Point3 // point ∈ selection.overlay.union}) :
    ‖sourceNormal (anchored := anchored) (selection := selection) point‖ = 1 :=
  current.grain.localGrains.planeMap_unit _

theorem sourceNormal_vertical
    (point : {point : Point3 // point ∈ selection.overlay.union}) :
    |sourceNormal (anchored := anchored) (selection := selection)
        point (2 : Fin 3)| ≤ 1 / 2 :=
  current.grain.planeMap_vertical_bound _

theorem sourceNormal_dist_le_source_dist
    (first second : {point : Point3 // point ∈ selection.overlay.union}) :
    dist
        (sourceNormal (anchored := anchored) (selection := selection) first)
        (sourceNormal (anchored := anchored) (selection := selection) second) ≤
      dist
        (sourceAnchor (anchored := anchored) (selection := selection) first)
        (sourceAnchor (anchored := anchored) (selection := selection) second) := by
  have h := current.grain.localGrains.planeMap_lipschitz
    (sourceAnchor (anchored := anchored) (selection := selection) first)
    (sourceAnchor (anchored := anchored) (selection := selection) second)
  simpa [sourceNormal, edist_dist] using h

theorem source_local_ad
    (queryScale : ℝ) (hdelta : delta ≤ queryScale)
    (hone : queryScale ≤ 1)
    (point : {point : Point3 // point ∈ selection.overlay.union}) :
    PureWZ2PaperADSet1
      (scalarProjection
        (sourceNormal (anchored := anchored) (selection := selection) point)
        (current.grain.shading.union ∩
          Metric.closedBall
            (sourceAnchor (anchored := anchored) (selection := selection)
              point : Point3)
            (Real.sqrt queryScale)))
      queryScale (1 - sigma)
      (Kakeya.realRpowENN delta (-inputLoss)) :=
  current.grain.localGrains.local_ad queryScale hdelta hone _

end PureWZ2HierarchyReentrantAnchoredTwoScaleReceipt

end Kakeya.Assouad

end
