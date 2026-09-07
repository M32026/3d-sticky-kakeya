import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05SynchronizedOwnerSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05OwnerTwoCallAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantSource

/-!
# Anchored synchronized second owner call

This is the production continuation of a direct anchored selection.  Its
structural source is the first owner's literal coarse shading.  Current-source
geometry is sampled only at genuine occupied source points, while the second
owner consumes the exact selected re-entry normalization.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- Genuine current-source anchors for the first owner's occupied coarse
shading.  No normal or local AD statement is asserted at a coarse point. -/
structure PureWZ2Node05CurrentSourceAnchors
    {sigma inputLoss delta ambientLoss : ℝ}
    {normalizationExponent : ℕ}
    (current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      normalizationExponent)
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent : ℕ}
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      current.grain.shading rhoRequested ambientLogExponent) where
  sourcePoint :
    {point : Point3 // point ∈ ambient.croppedCoarseShading.union} →
      {point : Point3 // point ∈ current.grain.shading.union}
  sourcePoint_mem_refined :
    ∀ point, (sourcePoint point : Point3) ∈ ambient.refined.union
  sourcePoint_same_cell :
    ∀ point,
      wz1PaperGridIndex rhoRequested.1 (sourcePoint point : Point3) =
        wz1PaperGridIndex rhoRequested.1 (point : Point3)
  sourcePoint_dist_lt :
    ∀ point, dist (sourcePoint point : Point3) (point : Point3) <
      2 * rhoRequested.1

/-- The first owner's balanced cover constructs genuine source anchors
without any extremality reconstruction or coarse-cardinality factor. -/
theorem exists_pureWZ2Node05CurrentSourceAnchors
    {sigma inputLoss delta ambientLoss : ℝ}
    {normalizationExponent : ℕ}
    (current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      normalizationExponent)
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent : ℕ}
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      current.grain.shading rhoRequested ambientLogExponent) :
    Nonempty (PureWZ2Node05CurrentSourceAnchors current ambient) := by
  classical
  have source_exists :
      ∀ point :
          {point : Point3 // point ∈ ambient.croppedCoarseShading.union},
        ∃ source : {point : Point3 // point ∈ current.grain.shading.union},
          (source : Point3) ∈ ambient.refined.union ∧
            wz1PaperGridIndex rhoRequested.1 (source : Point3) =
              wz1PaperGridIndex rhoRequested.1 (point : Point3) := by
    intro point
    let pointValue : Point3 := point
    have hpointValue :
        pointValue ∈ ambient.croppedCoarseShading.union :=
      point.property
    have hcoarse :
        pointValue ∈
          ⋃ cell ∈ ambient.balanced.activeCells,
            wz1PaperGridCube rhoRequested.1 cell := by
      rw [← ambient.balanced.coarse_union_eq]
      exact hpointValue
    rcases Set.mem_iUnion₂.mp hcoarse with
      ⟨cell, hcell, hpointCell⟩
    let sourceRaw := ambient.data.balanced.cellRep cell hcell
    have hsourceFine : sourceRaw ∈ ambient.refined.union :=
      ambient.data.balanced.cellRep_in_union cell hcell
    rcases hsourceFine with ⟨sourceIndex, hsourceCarrier⟩
    have hsourceCurrent :
        sourceRaw ∈ current.grain.shading.carrier
          (ambient.selected.embedding sourceIndex) :=
      ambient.subshading sourceIndex hsourceCarrier
    refine
      ⟨⟨sourceRaw,
          ⟨ambient.selected.embedding sourceIndex, hsourceCurrent⟩⟩,
        ⟨sourceIndex, hsourceCarrier⟩, ?_⟩
    exact
      ((mem_wz1PaperGridCube rhoRequested.1 cell sourceRaw).mp
        (ambient.data.balanced.cellRep_in_cell cell hcell)).trans
      ((mem_wz1PaperGridCube rhoRequested.1 cell point).mp
        (by simpa [pointValue] using hpointCell)).symm
  let sourcePoint :
      {point : Point3 // point ∈ ambient.croppedCoarseShading.union} →
        {point : Point3 // point ∈ current.grain.shading.union} :=
    fun point => Classical.choose (source_exists point)
  have sourcePoint_spec : ∀ point,
      (sourcePoint point : Point3) ∈ ambient.refined.union ∧
        wz1PaperGridIndex rhoRequested.1
            (sourcePoint point : Point3) =
          wz1PaperGridIndex rhoRequested.1 (point : Point3) :=
    fun point => Classical.choose_spec (source_exists point)
  refine ⟨{
    sourcePoint := sourcePoint
    sourcePoint_mem_refined := fun point => (sourcePoint_spec point).1
    sourcePoint_same_cell := fun point => (sourcePoint_spec point).2
    sourcePoint_dist_lt := ?_
  }⟩
  intro point
  have hsourceCell :
      (sourcePoint point : Point3) ∈
        wz1PaperGridCube rhoRequested.1
          (wz1PaperGridIndex rhoRequested.1 (point : Point3)) :=
    (mem_wz1PaperGridCube rhoRequested.1 _ _).mpr
      (sourcePoint_spec point).2
  have hpointCell :
      (point : Point3) ∈
        wz1PaperGridCube rhoRequested.1
          (wz1PaperGridIndex rhoRequested.1 (point : Point3)) :=
    (mem_wz1PaperGridCube rhoRequested.1 _ _).mpr rfl
  exact wz1_paper_grid_cube_diameter_lt_two_rho
    ambient.coarse_extremal.delta_pos hsourceCell hpointCell

namespace PureWZ2Node05CurrentSourceAnchors

variable
    {sigma inputLoss delta ambientLoss : ℝ}
    {normalizationExponent : ℕ}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent : ℕ}
    {ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      current.grain.shading rhoRequested ambientLogExponent}
    (anchors : PureWZ2Node05CurrentSourceAnchors current ambient)

/-- Evaluate the supplied plane map only at a genuine occupied source
anchor. -/
noncomputable def sourceNormal
    (point : {point : Point3 //
      point ∈ ambient.croppedCoarseShading.union}) : Point3 :=
  current.grain.localGrains.planeMap (anchors.sourcePoint point)

theorem sourceNormal_unit
    (point : {point : Point3 //
      point ∈ ambient.croppedCoarseShading.union}) :
    ‖anchors.sourceNormal point‖ = 1 :=
  current.grain.localGrains.planeMap_unit _

theorem sourceNormal_vertical
    (point : {point : Point3 //
      point ∈ ambient.croppedCoarseShading.union}) :
    |anchors.sourceNormal point (2 : Fin 3)| ≤ 1 / 2 :=
  current.grain.planeMap_vertical_bound _

theorem sourceNormal_local_ad
    (queryScale : ℝ) (hdelta : delta ≤ queryScale)
    (hone : queryScale ≤ 1)
    (point : {point : Point3 //
      point ∈ ambient.croppedCoarseShading.union}) :
    PureWZ2PaperADSet1
      (scalarProjection (anchors.sourceNormal point)
        (current.grain.shading.union ∩
          Metric.closedBall (anchors.sourcePoint point : Point3)
            (Real.sqrt queryScale)))
      queryScale (1 - sigma)
      (Kakeya.realRpowENN delta (-inputLoss)) :=
  current.grain.localGrains.local_ad queryScale hdelta hone _

end PureWZ2Node05CurrentSourceAnchors

/-- Compatibility ABI for the existing anchored CommonBin modules.  The
pre-scheduled production route below does not construct this record. -/
structure PureWZ2Node05AnchoredSynchronizedSecondOwnerCall
    {delta sigma ambientLoss grainLoss outputEta selectedLoss sourceLoss
      seedLoss outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent selectedNormalizationExponent secondSeedLogExponent
      outputLogExponent : ℕ}
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent)
    (anchored : PureWZ2Node05AnchoredCoarseSource
      (grainLoss := grainLoss) ambient)
    (selection : PureWZ2Node05AnchoredSynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (sourceLoss := sourceLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      ambient anchored)
    (sqrtRequested : WZ2PaperRequestedScale rhoRequested.1) where
  input : PureWZ2CroppedPropStickyUniversalInput
    (outputLoss := seedLoss) selection.selectedReentry.toNormalizationData
    sqrtRequested secondSeedLogExponent
  ownerCompanion : PureWZ2Node05OwnerReentryCompanion input
  call : PureWZ2Node05OwnerCallReceipt input outputLoss outputLogExponent
  companion_eq : call.companion = ownerCompanion

namespace PureWZ2Node05AnchoredSynchronizedSecondOwnerCall

variable
    {delta sigma ambientLoss grainLoss outputEta selectedLoss sourceLoss
      seedLoss outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent selectedNormalizationExponent secondSeedLogExponent
      outputLogExponent : ℕ}
    {ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent}
    {anchored : PureWZ2Node05AnchoredCoarseSource
      (grainLoss := grainLoss) ambient}
    {selection : PureWZ2Node05AnchoredSynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (sourceLoss := sourceLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      ambient anchored}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}

noncomputable def output
    (second : PureWZ2Node05AnchoredSynchronizedSecondOwnerCall
      (seedLoss := seedLoss) (outputLoss := outputLoss)
      (secondSeedLogExponent := secondSeedLogExponent)
      (outputLogExponent := outputLogExponent)
      ambient anchored selection sqrtRequested) :
    PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      selection.overlay sqrtRequested selectedNormalizationExponent
      secondSeedLogExponent outputLogExponent :=
  second.call.output

end PureWZ2Node05AnchoredSynchronizedSecondOwnerCall

/-- Compatibility two-call stage retained for existing anchored consumers. -/
structure PureWZ2Node05AnchoredSynchronizedTwoCallStage
    {delta sigma ambientLoss grainLoss outputEta selectedLoss sourceLoss
      seedLoss outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent firstLogExponent selectedNormalizationExponent
      secondSeedLogExponent : ℕ}
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent)
    (anchored : PureWZ2Node05AnchoredCoarseSource
      (grainLoss := grainLoss) ambient)
    (selection : PureWZ2Node05AnchoredSynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (sourceLoss := sourceLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      ambient anchored)
    (sqrtRequested : WZ2PaperRequestedScale rhoRequested.1) where
  rho : ℝ
  rho_eq : rhoRequested.1 = rho
  sqrt_eq : sqrtRequested.1 = Real.sqrt rho
  firstReceipt : PureWZ2Node05CompleteParentOverlayReceipt
    (outputLoss := selectedLoss) ambient selection.selectedCoarse
    selection.pullback selection.overlay firstLogExponent
  second : PureWZ2Node05AnchoredSynchronizedSecondOwnerCall
    (seedLoss := seedLoss) (outputLoss := outputLoss)
    (secondSeedLogExponent := secondSeedLogExponent)
    (outputLogExponent := firstLogExponent)
    ambient anchored selection sqrtRequested

/-- The second owner input and exact call on one anchored synchronized
selection.  Every numerical field of the owner receipt is identified with
the pre-runtime schedule. -/
structure PureWZ2Node05PreScheduledAnchoredSynchronizedSecondOwnerCall
    {delta sigma : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    (schedule : PureWZ2Node05AnchoredSelectionSchedule)
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := schedule.firstOutputLoss)
      sourceShading rhoRequested schedule.firstOutputLogExponent)
    (ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      schedule.ancestorNormalizationExponent schedule.reentrySourceLoss
      schedule.reentryNormalizationLoss)
    (selection : PureWZ2Node05PreScheduledAnchoredSynchronizedOwnerSelection
      schedule ambient ancestor)
    (sqrtRequested : WZ2PaperRequestedScale rhoRequested.1) where
  input : PureWZ2CroppedPropStickyUniversalInput
    (outputLoss := schedule.seedLoss)
    selection.selectedReentry.toNormalizationData
    sqrtRequested schedule.secondSeedLogExponent
  call : PureWZ2Node05OwnerCallReceipt input schedule.secondOutputLoss
    schedule.outputLogExponent
  sourceFineLoss_eq : call.sourceFineLoss = schedule.sourceFineLoss
  structuralBudget_eq :
    call.structuralBudget = schedule.structuralBudget
  fineExponent_eq : call.fineExponent = schedule.secondFineExponent

namespace PureWZ2Node05PreScheduledAnchoredSynchronizedSecondOwnerCall

variable
    {delta sigma : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {schedule : PureWZ2Node05AnchoredSelectionSchedule}
    {ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := schedule.firstOutputLoss)
      sourceShading rhoRequested schedule.firstOutputLogExponent}
    {ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      schedule.ancestorNormalizationExponent schedule.reentrySourceLoss
      schedule.reentryNormalizationLoss}
    {selection : PureWZ2Node05PreScheduledAnchoredSynchronizedOwnerSelection
      schedule ambient ancestor}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}

/-- The owner companion is not selected independently from the call. -/
noncomputable abbrev ownerCompanion
    (second : PureWZ2Node05PreScheduledAnchoredSynchronizedSecondOwnerCall
      schedule ambient ancestor selection sqrtRequested) :
    PureWZ2Node05OwnerReentryCompanion second.input :=
  second.call.companion

/-- Concrete second owner output, indexed by the exact anchored overlay. -/
noncomputable def output
    (second : PureWZ2Node05PreScheduledAnchoredSynchronizedSecondOwnerCall
      schedule ambient ancestor selection sqrtRequested) :
    PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := schedule.seedLoss)
      (outputLoss := schedule.secondOutputLoss)
      selection.overlay sqrtRequested schedule.selectedNormalizationExponent
      schedule.secondSeedLogExponent schedule.outputLogExponent :=
  second.call.output

end PureWZ2Node05PreScheduledAnchoredSynchronizedSecondOwnerCall

/-- Same-witness first-call receipts after the anchored finite core has been
selected.  Unlike the legacy overlay receipt, this record has no global
coarse-cardinality recovery field. -/
structure PureWZ2Node05PreScheduledAnchoredFirstSelectionReceipt
    {delta sigma : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    (schedule : PureWZ2Node05AnchoredSelectionSchedule)
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := schedule.firstOutputLoss)
      sourceShading rhoRequested schedule.firstOutputLogExponent)
    (ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      schedule.ancestorNormalizationExponent schedule.reentrySourceLoss
      schedule.reentryNormalizationLoss)
    (selection : PureWZ2Node05PreScheduledAnchoredSynchronizedOwnerSelection
      schedule ambient ancestor) where
  ambientCoarseMultiplicityOne : ∀ point,
    (ambient.croppedCoarseShading.pointMultiplicity point : ENNReal) ≤ 1
  exactMultiplicity : ℕ
  exactMultiplicity_pos : 0 < exactMultiplicity
  ambientExactMultiplicity :
    ambient.refined.HasConstantMultiplicity
      exactMultiplicity exactMultiplicity
  fineRefinementExponent : ℕ
  fineRefinement :
    WZ1PaperRefinement ambient.seed.data.refined fineRefinementExponent
  coarseRefinementExponent : ℕ
  coarseRefinement : WZ1PaperRefinement
    ambient.seed.data.croppedCoarseShading coarseRefinementExponent
  logExponent_eq :
    schedule.outputLogExponent =
      ambient.seedLogExponent + fineRefinementExponent
  selected_eq :
    ambient.selected.comp selection.pullback.selectedFine =
      ambient.seed.data.selected.comp fineRefinement.selected
  refined_eq : HEq
    (pureWZ2Node05CompleteParentOverlayFineShading
      selection.pullback selection.overlay)
    fineRefinement.refined
  coarse_eq :
    selection.selectedCoarse.family = coarseRefinement.selected.family
  croppedCoarseShading_eq :
    HEq selection.overlay coarseRefinement.refined
  retained_mass :
    wz2PaperPureRefinementFraction delta schedule.outputLogExponent *
        sourceShading.mass ≤
      (pureWZ2Node05CompleteParentOverlayFineShading
        selection.pullback selection.overlay).mass
  refined_extremal :
    WZ2PaperCroppedIsExtremal sigma schedule.selectedLoss
      selection.pullback.selectedFine.family
      (pureWZ2Node05CompleteParentOverlayFineShading
        selection.pullback selection.overlay)
  refined_volume_lower :
    Kakeya.realRpowENN delta (sigma + schedule.selectedLoss) ≤
      volume (pureWZ2Node05CompleteParentOverlayFineShading
        selection.pullback selection.overlay).union
  rescaledFiber :
    ∀ parent : Fin selection.selectedCoarse.family.card,
      Nonempty
        (WZ2PaperPureRescaledFullFiberOutput
          (sigma := sigma) (loss := schedule.selectedLoss)
          (restrictPaperShading
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              selection.pullback.selectedFine.family
              (wz2PaperFullFiberIndices
                selection.pullback.selectedFine.family
                selection.selectedCoarse.family parent))
            (pureWZ2Node05CompleteParentOverlayFineShading
              selection.pullback selection.overlay))
          (selection.selectedCoarse.family.tube parent)
          selection.selectedReentry.cropped_extremal.delta_pos)

/-- Two-call synchronized stage on one exact first call, one selected core,
and one exact second call. -/
structure PureWZ2Node05PreScheduledAnchoredSynchronizedTwoCallStage
    {sigma inputLoss delta : ℝ}
    {normalizationExponent : ℕ}
    (current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      normalizationExponent)
    {rhoRequested : WZ2PaperRequestedScale delta}
    (schedule : PureWZ2Node05AnchoredSelectionSchedule)
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := schedule.firstOutputLoss)
      current.grain.shading rhoRequested schedule.firstOutputLogExponent)
    (ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      schedule.ancestorNormalizationExponent schedule.reentrySourceLoss
      schedule.reentryNormalizationLoss)
    (selection : PureWZ2Node05PreScheduledAnchoredSynchronizedOwnerSelection
      schedule ambient ancestor)
    (sqrtRequested : WZ2PaperRequestedScale rhoRequested.1) where
  rho : ℝ
  rho_eq : rhoRequested.1 = rho
  sqrt_eq : sqrtRequested.1 = Real.sqrt rho
  firstInput : PureWZ2CroppedPropStickyUniversalInput
    (outputLoss := schedule.firstSeedLoss)
    current.reentry.toNormalizationData rhoRequested
    schedule.firstSeedLogExponent
  firstCall : PureWZ2Node05OwnerCallReceipt firstInput
    schedule.firstOutputLoss schedule.firstOutputLogExponent
  first_sourceFineLoss_eq :
    firstCall.sourceFineLoss = schedule.firstSourceFineLoss
  first_structuralBudget_eq :
    firstCall.structuralBudget = schedule.firstStructuralBudget
  first_fineExponent_eq :
    firstCall.fineExponent = schedule.firstFineExponent
  ambient_eq : ambient = firstCall.output.toNode5StickyData
  firstReceipt : PureWZ2Node05PreScheduledAnchoredFirstSelectionReceipt
    schedule ambient ancestor selection
  second : PureWZ2Node05PreScheduledAnchoredSynchronizedSecondOwnerCall
    schedule ambient ancestor selection sqrtRequested

namespace PureWZ2Node05PreScheduledAnchoredSynchronizedTwoCallStage

variable
    {sigma inputLoss delta : ℝ}
    {normalizationExponent : ℕ}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {schedule : PureWZ2Node05AnchoredSelectionSchedule}
    {ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := schedule.firstOutputLoss)
      current.grain.shading rhoRequested schedule.firstOutputLogExponent}
    {ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      schedule.ancestorNormalizationExponent schedule.reentrySourceLoss
      schedule.reentryNormalizationLoss}
    {selection :
      PureWZ2Node05PreScheduledAnchoredSynchronizedOwnerSelection
        schedule ambient ancestor}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}

/-- Canonical current-source anchors attached to the exact first call in this
stage.  Their construction does not select any loss or owner witness. -/
noncomputable def currentAnchors
    (_stage : PureWZ2Node05PreScheduledAnchoredSynchronizedTwoCallStage
      current schedule ambient ancestor selection sqrtRequested) :
    PureWZ2Node05CurrentSourceAnchors current ambient :=
  Classical.choice (exists_pureWZ2Node05CurrentSourceAnchors current ambient)

/-- The structural shading used by the stage is literally the first owner's
coarse shading. -/
@[simp] theorem structuralShading_eq
    (_stage : PureWZ2Node05PreScheduledAnchoredSynchronizedTwoCallStage
      current schedule ambient ancestor selection sqrtRequested) :
    selection.structuralShading = ambient.croppedCoarseShading :=
  rfl

/-- The selected re-entry keeps the exact ordinary extremizer of the first
owner's re-entry. -/
theorem selectedReentry_ordinarySource_eq
    (_stage : PureWZ2Node05PreScheduledAnchoredSynchronizedTwoCallStage
      current schedule ambient ancestor selection sqrtRequested) :
    selection.selectedReentry.ordinarySource = ancestor.ordinarySource :=
  selection.ordinarySource_eq

end PureWZ2Node05PreScheduledAnchoredSynchronizedTwoCallStage

/-- Minimal fixed-schedule/runtime two-call leaf.

This is deliberately not named `ProducerAt`: family-dependent selected
re-entry/CWA/floor data and both exact owner calls remain the conclusion.
Admissibility contains only scalar pre-runtime facts. -/
def PureWZ2Node05PreScheduledAnchoredSynchronizedTwoCallLeafAt
    {sigma inputLoss delta : ℝ}
    {normalizationExponent : ℕ}
    (current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      normalizationExponent)
    {rhoRequested : WZ2PaperRequestedScale delta}
    (schedule : PureWZ2Node05AnchoredSelectionSchedule)
    (_admissible : schedule.IsAdmissible)
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := schedule.firstOutputLoss)
      current.grain.shading rhoRequested schedule.firstOutputLogExponent)
    (ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      schedule.ancestorNormalizationExponent schedule.reentrySourceLoss
      schedule.reentryNormalizationLoss)
    (sqrtRequested : WZ2PaperRequestedScale rhoRequested.1)
    (_runtime : schedule.RuntimeAdmissible
      delta rhoRequested.1 sqrtRequested.1) : Prop :=
  Nonempty (Sigma fun selection :
    PureWZ2Node05PreScheduledAnchoredSynchronizedOwnerSelection
      schedule ambient ancestor =>
    PureWZ2Node05PreScheduledAnchoredSynchronizedTwoCallStage
      current schedule ambient ancestor selection sqrtRequested)

end Kakeya.Assouad

end
