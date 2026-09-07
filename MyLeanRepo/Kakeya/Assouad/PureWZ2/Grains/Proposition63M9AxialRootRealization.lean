import MyLeanRepo.Kakeya.Assouad.PureWZ2.CompleteFiberNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9SampledCoarseOuterTerminal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RichBoundarySlackSchedule

/-!
# Axial-slack root realization for the first Proposition 6.3 call

The public Node-3 projection intentionally remembers only the reusable
eighth-height window.  The first coarse sampled call needs one further coarse
cell of slack.  This Node-4-local realization keeps the sharper bound already
proved by complete-fiber normalization and the rich terminal witness that
transports that margin to its exact coarse re-entry.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- One aligned preliminary sticky output with the exact root normalization,
the root axial margin, and the corresponding strict coarse axial window. -/
structure Proposition63M9AlignedSampledStickyData
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy) where
  rootNormalizationLoss : ℝ
  rootDelta : ℝ
  rootSource : PureWZ2ExtremalConfiguration sigma
    (pureWZ2CompleteNormalizationFinalLoss rootNormalizationLoss) rootDelta
  normalization : PureWZ2CroppedCriticalNormalizationData
    (outputLoss := rootNormalizationLoss) rootSource 0
  rootSourceLoss_pos :
    0 < pureWZ2CompleteNormalizationFinalLoss rootNormalizationLoss
  rootNormalizationLoss_pos : 0 < rootNormalizationLoss
  rootNormalizationLoss_lt_sticky :
    rootNormalizationLoss < cutoff.sampledM8RootLosses.stickyLoss
  rootSourceLoss_le_half :
    pureWZ2CompleteNormalizationFinalLoss rootNormalizationLoss ≤
      rootNormalizationLoss / 2
  rootDelta_pos : 0 < rootDelta
  rootDelta_le_scaleCeiling : rootDelta ≤ cutoff.scaleCeiling
  aligned : Proposition63AlignedPowerRequestedScaleData rootDelta
    cutoff.sampledM8RootLosses.stickyLoss
  scale_le_outerScaleCeiling :
    aligned.requested.1 ≤ cutoff.outerScaleCeiling
  rootAxialMargin : ∀ index point,
    point ∈ normalization.frame '' normalization.ordinaryRefined.carrier index →
      |point (2 : Fin 3)| + aligned.requested.1 ≤ 1 / 8
  rich : Proposition63RichTerminalStickyData
    (outputLoss := cutoff.sampledM8RootLosses.stickyLoss)
    normalization.croppedRefined
    (normalization.toPropStickyReentryData
      rootSourceLoss_pos rootNormalizationLoss_pos) aligned.requested

namespace Proposition63M9AlignedSampledStickyData

/-- The reentrant projection of the exact rich terminal. -/
noncomputable def sticky
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    (data : Proposition63M9AlignedSampledStickyData cutoff) :
    PureWZ2ReentrantPropStickyData
      (sigma := sigma)
      (outputLoss := cutoff.sampledM8RootLosses.stickyLoss)
      data.normalization.croppedRefined data.aligned.requested 0 61 :=
  data.rich.toReentrant <|
    proposition63_reentry_axial_window_of_margin
      (data.normalization.toPropStickyReentryData
        data.rootSourceLoss_pos data.rootNormalizationLoss_pos)
      data.aligned.requested data.rootAxialMargin

/-- The exact coarse ordinary trace remains in the eighth-height window. -/
theorem coarseAxialEighth
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    (data : Proposition63M9AlignedSampledStickyData cutoff) :
    ∀ index point,
      point ∈ data.sticky.coarseReentry.geometry.frame ''
          data.sticky.coarseReentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8 := by
  simpa only [Proposition63M9AlignedSampledStickyData.sticky,
    Proposition63RichTerminalStickyData.toReentrant] using
      data.rich.coarse_reentry_axial_window_of_margin data.rootAxialMargin

end Proposition63M9AlignedSampledStickyData

/-- Construct the first aligned sticky output from the concrete, already
proved Node-3 kernel while retaining the stronger axial information omitted
by the public compatibility projection. -/
theorem Proposition63M9PreNode3CutoffData.alignedSampledSticky
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    (critical : PureWZ2CriticalPackage sigma)
    (hsigmaOne : sigma < 1) :
    Nonempty (Proposition63M9AlignedSampledStickyData cutoff) := by
  let stickyLoss := cutoff.sampledM8RootLosses.stickyLoss
  have stickyLossPos : 0 < stickyLoss :=
    cutoff.sampledM8RootLosses.stickyLoss_pos
  have stickyLossLeOne : stickyLoss ≤ 1 := by
    have stickyLtSigma : stickyLoss < sigma := by
      calc
        stickyLoss < cutoff.sampledM8RootLosses.planinessLoss := by
          rw [cutoff.sampledM8RootLosses.planinessLoss_eq]
          linarith [stickyLossPos]
        _ = cutoff.planinessLoss := cutoff.planinessLoss_eq.symm
        _ < sigma / 4 := cutoff.planinessLoss_lt_sigma_quarter
        _ < sigma := by linarith [critical.sigma_pos]
    linarith
  rcases
      Kakeya.Assouad.Prop62PaperAudit.V4.pureWZ2_prop_sticky_reentry_v4_rich_terminal_exact_source
        Kakeya.Assouad.Prop62PaperAudit.V4.fixed_grid_boundary_removal
        Kakeya.Assouad.Prop62PaperAudit.V4.one_pass_tree_cleanup
        sigma critical stickyLoss stickyLossPos stickyLossLeOne with
    ⟨normalizationLoss, continuationDelta, rootSourceLossPos,
      normalizationLossPos, rootSourceLossLeHalf, normalizationLossLt,
      continuationDeltaPos, _continuationDeltaLeOne, continuation⟩
  rcases pureWZ2_completeFiber_normalization_exact_with_axial_bound
      sigma normalizationLoss normalizationLossPos with
    ⟨initialLoss, normalizationDelta, initialLossPos,
      _rootSourceLossPos, _rootSourceLossLeHalf, normalizationDeltaPos,
      normalizationDeltaSmall, normalize⟩
  let threshold := min cutoff.scaleCeiling
    (min continuationDelta normalizationDelta)
  have thresholdPos : 0 < threshold := by
    dsimp only [threshold]
    exact lt_min cutoff.scaleCeiling_pos <|
      lt_min continuationDeltaPos normalizationDeltaPos
  rcases critical.extremal_sequence initialLoss threshold
      initialLossPos thresholdPos with
    ⟨delta, deltaPos, deltaLe, ⟨initialSource⟩⟩
  have deltaLeScale : delta ≤ cutoff.scaleCeiling :=
    deltaLe.trans (min_le_left _ _)
  have deltaLeContinuation : delta ≤ continuationDelta :=
    deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeNormalization : delta ≤ normalizationDelta :=
    deltaLe.trans <| (min_le_right _ _).trans (min_le_right _ _)
  rcases normalize delta deltaPos deltaLeNormalization initialSource with
    ⟨rootSource, ⟨axial⟩⟩
  let normalization := axial.leaves.toNormalizationData
  have deltaLeOuter : delta ≤ cutoff.outerScaleCeiling :=
    deltaLeScale.trans cutoff.scaleCeiling_le_outerScaleCeiling
  have deltaLeAligned : delta ≤ cutoff.alignedRootScale.delta₀ :=
    deltaLeOuter.trans cutoff.outerScaleCeiling_le_alignedRoot
  have stickyHalf : cutoff.preliminaryStickyLoss < 1 / 2 := by
    have planinessPos := cutoff.sampledM8RootLosses.stickyLoss_pos
    have planinessLt := cutoff.planinessLoss_lt_sigma_quarter
    rw [cutoff.planinessLoss_eq,
      cutoff.sampledM8RootLosses.planinessLoss_eq] at planinessLt
    rw [cutoff.preliminaryStickyLoss_eq]
    linarith
  rcases cutoff.alignedRootScale.requestedScale
      cutoff.preliminaryStickyLoss_pos stickyHalf deltaPos deltaLeAligned with
    ⟨alignedRaw⟩
  let aligned : Proposition63AlignedPowerRequestedScaleData delta
      cutoff.sampledM8RootLosses.stickyLoss := by
    rw [← cutoff.preliminaryStickyLoss_eq]
    exact alignedRaw
  have scaleLeOuter : aligned.requested.1 ≤ cutoff.outerScaleCeiling := by
    apply aligned.upper_window.trans
    rw [← cutoff.preliminaryStickyLoss_eq]
    have deltaLePower : delta ≤ Real.rpow cutoff.outerScaleCeiling
        (1 / cutoff.preliminaryStickyLoss) :=
      deltaLeScale.trans <| by
        unfold Proposition63M9PreNode3CutoffData.scaleCeiling
        exact min_le_right _ _
    calc
      Real.rpow delta cutoff.preliminaryStickyLoss ≤
          Real.rpow (Real.rpow cutoff.outerScaleCeiling
            (1 / cutoff.preliminaryStickyLoss))
            cutoff.preliminaryStickyLoss :=
        Real.rpow_le_rpow deltaPos.le deltaLePower
          cutoff.preliminaryStickyLoss_pos.le
      _ = Real.rpow cutoff.outerScaleCeiling
          ((1 / cutoff.preliminaryStickyLoss) *
            cutoff.preliminaryStickyLoss) :=
        (Real.rpow_mul cutoff.outerScaleCeiling_pos.le _ _).symm
      _ = Real.rpow cutoff.outerScaleCeiling 1 := by
        congr 1
        field_simp [cutoff.preliminaryStickyLoss_pos.ne']
      _ = cutoff.outerScaleCeiling := Real.rpow_one _
  let rootReentry := normalization.toPropStickyReentryData
    rootSourceLossPos normalizationLossPos
  rcases continuation delta deltaPos deltaLeContinuation
      normalization.croppedFamily normalization.croppedRefined rootReentry
      aligned.requested aligned.lower_window aligned.upper_window with ⟨rich⟩
  have deltaSmall : delta ≤ 1 / 1000 :=
    deltaLeNormalization.trans normalizationDeltaSmall
  have rhoSmall : aligned.requested.1 ≤ 1 / 10000 :=
    scaleLeOuter.trans cutoff.outerScaleCeiling_le_preliminaryPropertyP |>.trans
      cutoff.preliminaryAnalytic.propertyPScale_small
  have sqrtThreeLe : Real.sqrt 3 ≤ 7 / 4 := by
    have square : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have nonnegative := Real.sqrt_nonneg 3
    nlinarith
  have rootMargin : ∀ index point,
      point ∈ normalization.frame '' normalization.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| + aligned.requested.1 ≤ 1 / 8 := by
    intro index point pointMem
    have pointBound := axial.ordinary_axial_bound index point pointMem
    nlinarith
  exact ⟨{
    rootNormalizationLoss := normalizationLoss
    rootDelta := delta
    rootSource := rootSource
    normalization := normalization
    rootSourceLoss_pos := rootSourceLossPos
    rootNormalizationLoss_pos := normalizationLossPos
    rootNormalizationLoss_lt_sticky := normalizationLossLt
    rootSourceLoss_le_half := rootSourceLossLeHalf
    rootDelta_pos := deltaPos
    rootDelta_le_scaleCeiling := deltaLeScale
    aligned := aligned
    scale_le_outerScaleCeiling := scaleLeOuter
    rootAxialMargin := rootMargin
    rich := rich
  }⟩

end Kakeya.Assouad.PureWZ2

end
