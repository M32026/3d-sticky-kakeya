import MyLeanRepo.Kakeya.Assouad.PureWZ2.CompleteFiberNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4DirectUniversal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropStickyReentry

/-!
# Synchronized realization of WZ2 Proposition 6.2

This module composes the exact-loss complete-fiber normalizer with the
exact-source V4 continuation.  The resulting source, normalized data, scale,
and `prop: sticky` output are one dependent witness.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open Kakeya.Assouad

/--
The complete-fiber normalizer and V4 continuation provide one nonvacuous,
synchronized realization.
-/
theorem pureWZ2_prop_sticky_reentrant_realization_v4
    (hFixedGrid : FixedGridBoundaryRemovalStatement)
    (hTreeCleanup : OnePassTreeCleanupStatement) :
    PureWZ2PropStickyReentrantRootRealizationAt 0 61 := by
  intro sigma critical outputLoss scaleCeiling
    outputLossPos scaleCeilingPos
  let continuationLoss := min (outputLoss / 2) (1 / 4)
  have continuationLossPos : 0 < continuationLoss := by
    dsimp only [continuationLoss]
    exact lt_min (by positivity) (by norm_num)
  have continuationLossLtOutput :
      continuationLoss < outputLoss := by
    have continuationLossLeHalf :
        continuationLoss ≤ outputLoss / 2 :=
      min_le_left _ _
    nlinarith
  have continuationLossLeHalf :
      continuationLoss ≤ 1 / 2 := by
    exact (min_le_right _ _).trans (by norm_num)
  have continuationLossLeOne :
      continuationLoss ≤ 1 := by
    linarith
  rcases
      pureWZ2_prop_sticky_reentry_v4_core_exact_source
        hFixedGrid hTreeCleanup sigma critical
        continuationLoss continuationLossPos continuationLossLeOne
    with
    ⟨normalizationLoss, continuationDelta,
      normalizedSourceLossPos, normalizationLossPos,
      normalizedSourceLossLeHalf, normalizationLossLt,
      continuationDeltaPos, _continuationDeltaLeOne, continuation⟩
  rcases
      pureWZ2_completeFiber_normalization_exact
        sigma normalizationLoss normalizationLossPos
    with
    ⟨initialLoss, normalizationDelta,
      initialLossPos, _normalizedSourceLossPos,
      _normalizedSourceLossLeHalf, normalizationDeltaPos, normalize⟩
  let threshold :=
    min scaleCeiling
      (min continuationDelta (min normalizationDelta (1 / 2)))
  have thresholdPos : 0 < threshold := by
    dsimp only [threshold]
    positivity
  rcases
      critical.extremal_sequence
        initialLoss threshold initialLossPos thresholdPos
    with
    ⟨delta, deltaPos, deltaLe, ⟨initialSource⟩⟩
  have deltaLeScale : delta ≤ scaleCeiling :=
    deltaLe.trans (min_le_left _ _)
  have deltaLeContinuation : delta ≤ continuationDelta :=
    deltaLe.trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeNormalization : delta ≤ normalizationDelta :=
    deltaLe.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeHalf : delta ≤ 1 / 2 :=
    deltaLe.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
  have deltaLeOne : delta ≤ 1 := by
    linarith
  rcases
      normalize delta deltaPos deltaLeNormalization initialSource
    with
    ⟨source, ⟨leaves⟩⟩
  let normalized := leaves.toNormalizationData
  let rootReentry :=
    normalized.toPropStickyReentryData
      normalizedSourceLossPos normalizationLossPos
  have rootAxialWindow :
      ∀ index point,
        point ∈
            rootReentry.geometry.frame ''
              rootReentry.geometry.ordinaryRefined.carrier index →
          |point (2 : Fin 3)| ≤ 1 / 8 := by
    intro index point pointMem
    exact leaves.ordinary_axial_window index point pointMem
  let rhoValue := Real.rpow delta (1 / 2 : ℝ)
  have deltaLeRho : delta ≤ rhoValue := by
    calc
      delta = Real.rpow delta 1 := by simp
      _ ≤ Real.rpow delta (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge
          deltaPos deltaLeOne (by norm_num)
  have rhoLeOne : rhoValue ≤ 1 := by
    exact Real.rpow_le_one deltaPos.le deltaLeOne (by norm_num)
  let rho : WZ2PaperRequestedScale delta :=
    ⟨rhoValue, deltaLeRho, rhoLeOne⟩
  have rhoLower :
      Real.rpow delta (1 - continuationLoss) ≤ rho.1 := by
    change
      Real.rpow delta (1 - continuationLoss) ≤
        Real.rpow delta (1 / 2 : ℝ)
    exact
      Real.rpow_le_rpow_of_exponent_ge
        deltaPos deltaLeOne (by linarith)
  have rhoUpper :
      rho.1 ≤ Real.rpow delta continuationLoss := by
    change
      Real.rpow delta (1 / 2 : ℝ) ≤
        Real.rpow delta continuationLoss
    exact
      Real.rpow_le_rpow_of_exponent_ge
        deltaPos deltaLeOne continuationLossLeHalf
  rcases
      continuation delta deltaPos deltaLeContinuation
        normalized.croppedFamily normalized.croppedRefined
        rootReentry rho rhoLower rhoUpper
    with
    ⟨stickyCore⟩
  have allReentrant :
      ∀ requested : WZ2PaperRequestedScale delta,
        Real.rpow delta (1 - continuationLoss) ≤ requested.1 →
        requested.1 ≤ Real.rpow delta continuationLoss →
          Nonempty
            (PureWZ2ReentrantPropStickyData
              (sigma := sigma)
              (outputLoss := outputLoss)
              normalized.croppedRefined requested 0 61) := by
    intro requested requestedLower requestedUpper
    rcases
        continuation delta deltaPos deltaLeContinuation
          normalized.croppedFamily normalized.croppedRefined
          rootReentry requested requestedLower requestedUpper
      with
      ⟨requestedCore⟩
    exact
      ⟨requestedCore.toReentrant
        continuationLossLtOutput.le rootAxialWindow⟩
  have allScales :
      ∀ requested : WZ2PaperRequestedScale delta,
        Real.rpow delta (1 - continuationLoss) ≤ requested.1 →
        requested.1 ≤ Real.rpow delta continuationLoss →
          Nonempty
            (PureWZ2PropStickyData
              (sigma := sigma)
              (outputLoss := outputLoss)
              normalized.croppedRefined requested 61) := by
    intro requested requestedLower requestedUpper
    rcases allReentrant requested requestedLower requestedUpper with
      ⟨requested⟩
    exact ⟨requested.data⟩
  let realizedReentrant :=
    stickyCore.toReentrant continuationLossLtOutput.le rootAxialWindow
  let realization :
      PureWZ2PropStickyRealizationData
        (sigma := sigma)
        (outputLoss := outputLoss)
        (scaleCeiling := scaleCeiling) 0 61 :=
    {
      continuationLoss := continuationLoss
      sourceLoss :=
        pureWZ2CompleteNormalizationFinalLoss normalizationLoss
      normalizationLoss := normalizationLoss
      delta := delta
      continuationLoss_pos := continuationLossPos
      continuationLoss_lt_output := continuationLossLtOutput
      continuationLoss_le_half := continuationLossLeHalf
      sourceLoss_pos := normalizedSourceLossPos
      normalizationLoss_pos := normalizationLossPos
      sourceLoss_le_half := normalizedSourceLossLeHalf
      normalizationLoss_lt_continuation := normalizationLossLt
      delta_pos := deltaPos
      delta_le_ceiling := deltaLeScale
      source := source
      normalized := normalized
      normalized_ordinary_axial_window_eighth := by
        intro index point pointMem
        exact leaves.ordinary_axial_window index point pointMem
      output := allScales
      realizedRho := rho
      realizedRho_eq_sqrt := by
        change rhoValue = Real.sqrt delta
        dsimp only [rhoValue]
        exact (Real.sqrt_eq_rpow delta).symm
      realizedRho_lower := rhoLower
      realizedRho_upper := rhoUpper
      realizedOutput :=
        ⟨realizedReentrant.data⟩
    }
  exact
    ⟨{
      realization := realization
      rootReentry := rootReentry
      reentrantOutput := allReentrant
      realizedReentrantOutput := ⟨realizedReentrant⟩
    }⟩

/-- Compatibility projection to the original synchronized realization. -/
theorem pureWZ2_prop_sticky_realization_v4
    (hFixedGrid : FixedGridBoundaryRemovalStatement)
    (hTreeCleanup : OnePassTreeCleanupStatement) :
    PureWZ2PropStickyRealizationAt 0 61 := by
  intro sigma critical outputLoss scaleCeiling
    outputLossPos scaleCeilingPos
  rcases
      pureWZ2_prop_sticky_reentrant_realization_v4
        hFixedGrid hTreeCleanup sigma critical
        outputLoss scaleCeiling outputLossPos scaleCeilingPos
    with ⟨root⟩
  exact ⟨root.realization⟩

end Kakeya.Assouad.Prop62PaperAudit.V4

end
