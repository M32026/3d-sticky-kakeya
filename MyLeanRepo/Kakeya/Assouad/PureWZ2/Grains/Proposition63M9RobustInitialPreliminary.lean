import MyLeanRepo.Kakeya.Assouad.PureWZ2.CompleteFiberNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RobustRootAdapter
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9SecondCoarsePreliminary

/-!
# Proposition 6.3 M9: direct robust preliminary root

This is the quantifier-safe replacement for the obsolete sampled preliminary
route.  The rich schedule is frozen first.  Its exact source-loss equation is
then used to run complete-fibre normalization on a sufficiently small member
of the critical sequence.  The resulting normalization is the root of the
robust two-call middle, so no sampled-coarse body budget or extension budget
is involved.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- One exact normalized root, robust middle, and resulting `q`-scale
preliminary local-grain object, all selected after the loss-only schedules. -/
structure Proposition63M9RobustInitialPreliminaryData
    {sigma outputLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss)
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    (externalCutoff : ℝ) where
  inputLoss : ℝ
  r : ℝ
  inputLoss_pos : 0 < inputLoss
  r_pos : 0 < r
  r_le_external : r ≤ externalCutoff
  q_le_external :
    proposition63M9RobustLemma43Incidence r sigma ≤ externalCutoff
  r_le_scaleCeiling : r ≤ cutoff.scaleCeiling
  r_le_robustCutoff : r ≤ cutoff.twoCall.rootCutoff
  rootSource : PureWZ2ExtremalConfiguration sigma
    cutoff.twoCall.schedule.first.sourceLoss r
  root : Proposition63RootNormalizationData
    (outputLoss := cutoff.twoCall.schedule.first.normalizationLoss)
    rootSource 0 (cutoff.twoCall.schedule.second.sourceLoss / 8)
  root_axial_margin : ∀ index point,
    point ∈ root.normalization.frame ''
        root.normalization.ordinaryRefined.carrier index →
      |point (2 : Fin 3)| +
        (cutoff.twoCall.secondQRequested r_pos r_le_robustCutoff).1 ≤ 1 / 8
  middle : Proposition63M9RobustMiddleData cutoff root r_pos r_le_robustCutoff

namespace Proposition63M9RobustInitialPreliminaryData

variable
    {sigma outputLoss : ℝ}
    {critical : PureWZ2CriticalPackage sigma}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    {externalCutoff : ℝ}
    (data : Proposition63M9RobustInitialPreliminaryData
      critical hierarchy cutoff externalCutoff)

/-- The exact `q`-scale preliminary output of the direct robust root. -/
noncomputable def preliminary : Proposition63PreliminaryLocalGrainData
    (localLoss := hierarchy.preGrainLoss)
    (reentryLoss := hierarchy.preGrainLoss)
    data.middle.secondCoarseNormalization :=
  data.middle.secondCoarsePreliminary

end Proposition63M9RobustInitialPreliminaryData

/-- Construct the direct robust preliminary object before any first-chart
selection.  The extra power preimage makes the quantitative normalization
window leave room for the exact second-call scale `q = r^(sigma/2)`. -/
theorem proposition63_m9_robust_initial_preliminary
    {sigma outputLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss)
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    (externalCutoff : ℝ) (hexternalCutoff : 0 < externalCutoff) :
    Nonempty (Proposition63M9RobustInitialPreliminaryData
      critical hierarchy cutoff externalCutoff) := by
  have qExponentPos : 0 < sigma / 2 := by
    linarith [critical.sigma_pos]
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := externalCutoff) (s := sigma / 2)
      hexternalCutoff qExponentPos with
    ⟨externalQRootCutoff, externalQRootCutoffPos,
      _externalQRootCutoffOne, qExternal⟩
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := (1 / 10000 : ℝ)) (s := sigma / 2)
      (by norm_num) qExponentPos with
    ⟨qRootCutoff, qRootCutoffPos, _qRootCutoffOne, qSmall⟩
  rcases pureWZ2_completeFiber_normalization_exact_with_axial_bound
      sigma cutoff.twoCall.schedule.first.normalizationLoss
      cutoff.twoCall.schedule.first.normalizationLoss_pos with
    ⟨inputLoss, normalizationCutoff, inputLossPos,
      _rootSourceLossPos, _rootSourceLossHalf, normalizationCutoffPos,
      normalizationCutoffSmall, normalize⟩
  let threshold := min externalCutoff <|
    min cutoff.scaleCeiling <|
      min cutoff.twoCall.rootCutoff <| min externalQRootCutoff <|
        min qRootCutoff normalizationCutoff
  have thresholdPos : 0 < threshold := by
    dsimp only [threshold]
    exact lt_min hexternalCutoff <| lt_min cutoff.scaleCeiling_pos <|
      lt_min cutoff.twoCall.rootCutoff_pos <|
        lt_min externalQRootCutoffPos <|
          lt_min qRootCutoffPos normalizationCutoffPos
  rcases critical.extremal_sequence inputLoss threshold inputLossPos
      thresholdPos with
    ⟨r, rPos, rLe, ⟨inputSource⟩⟩
  have rLeExternal : r ≤ externalCutoff :=
    rLe.trans (min_le_left _ _)
  have rLeScale : r ≤ cutoff.scaleCeiling :=
    rLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
  have rLeRobust : r ≤ cutoff.twoCall.rootCutoff :=
    rLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have rLeQRoot : r ≤ qRootCutoff :=
    rLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have rLeExternalQRoot : r ≤ externalQRootCutoff :=
    rLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_left _ _)
  have rLeNormalization : r ≤ normalizationCutoff :=
    rLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))
  rcases normalize r rPos rLeNormalization inputSource with
    ⟨localized, ⟨axial⟩⟩
  have rOne : r ≤ 1 :=
    rLeNormalization.trans normalizationCutoffSmall |>.trans (by norm_num)
  have sourceLossLe :
      pureWZ2CompleteNormalizationFinalLoss
          cutoff.twoCall.schedule.first.normalizationLoss ≤
        cutoff.twoCall.schedule.first.sourceLoss :=
    cutoff.twoCall.schedule.first.sourceLoss_eq.symm.le
  let rootSource : PureWZ2ExtremalConfiguration sigma
      cutoff.twoCall.schedule.first.sourceLoss r :=
    weaken_extremal_configuration localized sourceLossLe
      cutoff.twoCall.schedule.first.sourceLoss_pos rPos rOne
  let normalization : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := cutoff.twoCall.schedule.first.normalizationLoss)
      rootSource 0 :=
    weaken_normalized_data axial.leaves.toNormalizationData sourceLossLe le_rfl
      cutoff.twoCall.schedule.first.sourceLoss_pos
      cutoff.twoCall.schedule.first.normalizationLoss_pos rPos rOne
      cutoff.twoCall.schedule.first.sourceLoss_le_half
  have densityAbsorb :=
    cutoff.twoCall.currentReentryAbsorption.density_absorb rPos
      (rLeRobust.trans cutoff.twoCall.rootCutoff_le_currentReentry)
  let root : Proposition63RootNormalizationData
      (outputLoss := cutoff.twoCall.schedule.first.normalizationLoss)
      rootSource 0 (cutoff.twoCall.schedule.second.sourceLoss / 8) :=
    Proposition63RootNormalizationData.ofNormalization normalization
      densityAbsorb
  have qLe : proposition63M9RobustLemma43Incidence r sigma ≤
      1 / 10000 := by
    exact qSmall r rPos rLeQRoot
  have rSmall : r ≤ 1 / 1000 :=
    rLeNormalization.trans normalizationCutoffSmall
  have sqrtThreeLe : Real.sqrt 3 ≤ 7 / 4 := by
    have square : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have nonnegative := Real.sqrt_nonneg 3
    nlinarith
  have rootAxialMargin : ∀ index point,
      point ∈ root.normalization.frame ''
          root.normalization.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| +
          (cutoff.twoCall.secondQRequested rPos rLeRobust).1 ≤ 1 / 8 := by
    intro index point pointMem
    have pointBound : |point (2 : Fin 3)| ≤ Real.sqrt 3 / 16 + 4 * r := by
      simpa only [root, normalization, rootSource,
        Proposition63RootNormalizationData.ofNormalization,
        weaken_normalized_data, weaken_extremal_configuration] using
          axial.ordinary_axial_bound index point pointMem
    rw [cutoff.twoCall.secondQRequested_value]
    unfold proposition63M9RobustLemma43Incidence
    unfold proposition63M9RobustLemma43Incidence at qLe
    nlinarith
  have qOuter := cutoff.robustIncidence_le_outerScaleCeiling rPos rLeScale
  rcases cutoff.runRobustMiddleOfAxialMargin root rPos rLeRobust
      rootAxialMargin qOuter with ⟨middle⟩
  exact ⟨{
    inputLoss := inputLoss
    r := r
    inputLoss_pos := inputLossPos
    r_pos := rPos
    r_le_external := rLeExternal
    q_le_external := qExternal r rPos rLeExternalQRoot
    r_le_scaleCeiling := rLeScale
    r_le_robustCutoff := rLeRobust
    rootSource := rootSource
    root := root
    root_axial_margin := rootAxialMargin
    middle := middle
  }⟩

end Kakeya.Assouad.PureWZ2

end
