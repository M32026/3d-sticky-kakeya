import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9FirstRobustStage
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RichLemma43CurrentReentryBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9SameExtremizerAssembly

/-!
# Proposition 6.3 M9: robust two-call middle assembly

This module composes the exact robust-kappa call, pointwise Lemma 4.3,
current-shading re-entry, the exact q call, Lemmas 4.4 and 4.7, and the generic
Lemma 4.12 runner.  The first coarse family is never reused as the second
coarse family.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- The complete repaired middle of M9, retaining the dependent provenance of
both rich calls and of the current-shading re-entry between them. -/
structure Proposition63M9RobustMiddleData
    {sigma outputLoss r : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    {source : PureWZ2ExtremalConfiguration sigma
      cutoff.twoCall.schedule.first.sourceLoss r}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := cutoff.twoCall.schedule.first.normalizationLoss) source
      normalizationExponent (cutoff.twoCall.schedule.second.sourceLoss / 8))
    (hr : 0 < r) (hrRobust : r ≤ cutoff.twoCall.rootCutoff) where
  first : Proposition63M9FirstRobustStageData cutoff.twoCall
    root.normalization.croppedRefined
    (root.normalization.toPropStickyReentryData
      cutoff.twoCall.schedule.first.sourceLoss_pos
      cutoff.twoCall.schedule.first.normalizationLoss_pos)
    hr hrRobust
  current : Proposition63CurrentShadingReentryData
    (reentryLoss := cutoff.twoCall.schedule.second.sourceLoss)
    root.normalization first.lemma43.shading
  current_normalization_loss : current.reentryNormalizationLoss =
    cutoff.twoCall.schedule.second.normalizationLoss
  preparation : Proposition63SecondCallPreparationData first.lemma43
    current.ordinary cutoff.twoCall.schedule.second.sourceLoss
    cutoff.twoCall.schedule.second.normalizationLoss normalizationExponent
    (cutoff.twoCall.secondQRequested hr hrRobust)
  secondTerminal : Proposition63RichTerminalStickyData
    (outputLoss := hierarchy.stickyLoss)
    preparation.prepared.restrictedLemma43.shading
    (preparation.prepared.normalization.toPropStickyReentryData
      preparation.prepared.target_loss_pos
      preparation.prepared.normalization_loss_pos)
    (cutoff.twoCall.secondQRequested hr hrRobust)
  second : Proposition63ThroughLemma412Data
    (delta := r) (sigma := sigma)
    (lemma43SourceLoss := cutoff.twoCall.schedule.first.normalizationLoss)
    (lemma43Loss := cutoff.twoCall.schedule.firstOutputLoss)
    (inputLoss := cutoff.twoCall.schedule.second.sourceLoss)
    (normalizationLoss := cutoff.twoCall.schedule.second.normalizationLoss)
    (family := root.normalization.croppedFamily)
    (source := root.normalization.croppedRefined)
    (rho := cutoff.twoCall.secondQRequested hr hrRobust)
    (normalizationExponent := normalizationExponent)
    (logExponent := 61) first.lemma43 current.ordinary preparation.prepared
    hierarchy.stickyLoss hierarchy.lemma44Loss hierarchy.lemma47Loss
    hierarchy.preGrainLoss
    (Real.rpow (cutoff.twoCall.secondQRequested hr hrRobust).1
      (-hierarchy.lemma47Loss))
  lemma44_planeMap_first_witness :
    ∀ point ∈ second.lemma44.coarseShading.union,
      ∃ finePoint ∈ first.lemma43.shading.union,
        second.lemma44.planeMap.planeMap point =
          first.lemma43.planeMap.planeMap finePoint
  second_sticky_eq : second.sticky = secondTerminal.data
  terminalCoarseReentry : PureWZ2PropStickyReentryData
    (sigma := sigma) second.sticky.croppedCoarseShading 0
    secondTerminal.coarseSourceLoss secondTerminal.coarseNormalizationLoss
  terminalCoarseAxialWindow : ∀ index point,
    point ∈ terminalCoarseReentry.geometry.frame ''
        terminalCoarseReentry.geometry.ordinaryRefined.carrier index →
      |point (2 : Fin 3)| ≤ 1 / 8
  coarse_midpoint_local : ∀ parent,
    ‖wz2PaperTubeMidpoint (second.sticky.coarse.tube parent)‖ ≤ 3

/-- Run the complete robust middle from one provenance-complete root whose
ordinary trace has enough axial room for the actual second-call scale.  This
is the intrinsic interface: the stronger fixed `1 / 25` window used by the
first-chart route is only one way to supply this margin. -/
theorem Proposition63M9PreNode3CutoffData.runRobustMiddleFromFirst
    {sigma outputLoss r : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    {source : PureWZ2ExtremalConfiguration sigma
      cutoff.twoCall.schedule.first.sourceLoss r}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := cutoff.twoCall.schedule.first.normalizationLoss) source
      normalizationExponent (cutoff.twoCall.schedule.second.sourceLoss / 8))
    (hr : 0 < r) (hrRobust : r ≤ cutoff.twoCall.rootCutoff)
    (rootAxialMargin : ∀ index point,
      point ∈ root.normalization.frame ''
          root.normalization.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| +
          (cutoff.twoCall.secondQRequested hr hrRobust).1 ≤ 1 / 8)
    (first : Proposition63M9FirstRobustStageData cutoff.twoCall
      root.normalization.croppedRefined
      (root.normalization.toPropStickyReentryData
        cutoff.twoCall.schedule.first.sourceLoss_pos
        cutoff.twoCall.schedule.first.normalizationLoss_pos)
      hr hrRobust)
    (hqOuter : proposition63M9RobustLemma43Incidence r sigma ≤
      cutoff.outerScaleCeiling) :
    ∃ middle : Proposition63M9RobustMiddleData cutoff root hr hrRobust,
      middle.first = first := by
  rcases proposition63_m9_rich_lemma43_current_reentry cutoff.twoCall root
      first.lemma43 hr hrRobust with
    ⟨current, _weight, _weightUpper, _levelCount, currentNormalization⟩
  let prepared : Proposition63RegularizedReentryData first.lemma43
      current.ordinary cutoff.twoCall.schedule.second.sourceLoss
      cutoff.twoCall.schedule.second.normalizationLoss normalizationExponent := by
    rw [← currentNormalization]
    exact current.toRegularizedReentry
      cutoff.twoCall.schedule.second.sourceLoss_pos
      cutoff.twoCall.schedule.firstOutputLoss_lt_secondSource.le
  have currentAxialMargin : ∀ index point,
      point ∈ current.ordinary.carrier index →
        |point (2 : Fin 3)| +
          (cutoff.twoCall.secondQRequested hr hrRobust).1 ≤ 1 / 8 :=
    fun index point pointMem =>
      rootAxialMargin
        (PureWZ2CroppedCriticalNormalizationData.ordinaryIndex
          root.normalization
          (proposition63IdentitySubfamily
            root.normalization.croppedFamily) index) point pointMem.1
  let preparation : Proposition63SecondCallPreparationData first.lemma43
      current.ordinary cutoff.twoCall.schedule.second.sourceLoss
      cutoff.twoCall.schedule.second.normalizationLoss normalizationExponent
      (cutoff.twoCall.secondQRequested hr hrRobust) := {
    prepared := prepared
    root_axial_margin := by
      intro index point pointMem
      change point ∈ (AffineIsometryEquiv.refl ℝ Point3) ''
          prepared.ordinarySource.shading.carrier index at pointMem
      rcases pointMem with ⟨sourcePoint, sourcePointMem, rfl⟩
      exact currentAxialMargin
        (prepared.regularized.selected.embedding index) sourcePoint
        sourcePointMem.1
  }
  let secondReentry := prepared.normalization.toPropStickyReentryData
    prepared.target_loss_pos prepared.normalization_loss_pos
  rcases cutoff.twoCall.second_runTerminal_exact_q hr hrRobust
      prepared.regularized.selected.family
      prepared.restrictedLemma43.shading secondReentry with ⟨rich⟩
  have rootAxialMargin := preparation.root_axial_margin
  let rootAxialWindow := proposition63_reentry_axial_window_of_margin
    secondReentry (cutoff.twoCall.secondQRequested hr hrRobust)
    rootAxialMargin
  have lemma44LossPos : 0 < hierarchy.lemma44Loss :=
    hierarchy.sticky_pos.trans hierarchy.sticky_lt_lemma44
  rcases proposition63_paper_lemma44_coarse_pair_of_terminal_with_map_witness
      (delta := r) (sigma := sigma)
      (lemma43SourceLoss := cutoff.twoCall.schedule.second.sourceLoss)
      (lemma43Loss := cutoff.twoCall.schedule.second.sourceLoss)
      (reentrySourceLoss := cutoff.twoCall.schedule.second.sourceLoss)
      (reentryNormalizationLoss :=
        cutoff.twoCall.schedule.second.normalizationLoss)
      (stickyLoss := hierarchy.stickyLoss)
      (outputLoss := hierarchy.lemma44Loss)
      (family := prepared.regularized.selected.family)
      (source := prepared.restrictedLemma43.shading)
      (rho := cutoff.twoCall.secondQRequested hr hrRobust)
      (normalizationExponent := normalizationExponent)
      (terminalLoss := rich.terminalLoss) prepared.restrictedLemma43
      secondReentry rich hierarchy.two_sticky_le_lemma44 lemma44LossPos with
    ⟨lemma44, lemma44MapWitness⟩
  rcases hierarchy.toTerminal.runLemma47
      (delta := r) (sigma := sigma)
      (outputLoss := outputLoss)
      (lemma43SourceLoss := cutoff.twoCall.schedule.second.sourceLoss)
      (lemma43Loss := cutoff.twoCall.schedule.second.sourceLoss)
      (reentrySourceLoss := cutoff.twoCall.schedule.second.sourceLoss)
      (reentryNormalizationLoss :=
        cutoff.twoCall.schedule.second.normalizationLoss)
      (family := prepared.regularized.selected.family)
      (source := prepared.restrictedLemma43.shading)
      (rho := cutoff.twoCall.secondQRequested hr hrRobust)
      (normalizationExponent := normalizationExponent)
      (lemma43 := prepared.restrictedLemma43)
      (reentry := secondReentry) rich lemma44
      (hqOuter.trans cutoff.outerScaleCeiling_le_lemma47)
      rootAxialWindow with ⟨lemma47⟩
  rcases cutoff.runLemma412OfAxialMargin
      (sigma := sigma) (outputLoss := outputLoss) (delta := r)
      (sourceLoss := cutoff.twoCall.schedule.second.sourceLoss)
      (normalizationLoss :=
        cutoff.twoCall.schedule.second.normalizationLoss)
      (lemma43SourceLoss := cutoff.twoCall.schedule.second.sourceLoss)
      (inputLoss := cutoff.twoCall.schedule.second.sourceLoss)
      (family := prepared.regularized.selected.family)
      (source := prepared.restrictedLemma43.shading)
      (rho := cutoff.twoCall.secondQRequested hr hrRobust)
      (lemma43 := prepared.restrictedLemma43)
      (normalizationExponent := normalizationExponent)
      (reentry := secondReentry) rich rootAxialMargin hqOuter
      lemma44 lemma47 cutoff.twoCall.scale.sigma_pos
      cutoff.twoCall.scale.sigma_lt_one with ⟨lemma412⟩
  let second : Proposition63ThroughLemma412Data
      (delta := r) (sigma := sigma)
      (lemma43SourceLoss := cutoff.twoCall.schedule.first.normalizationLoss)
      (lemma43Loss := cutoff.twoCall.schedule.firstOutputLoss)
      (inputLoss := cutoff.twoCall.schedule.second.sourceLoss)
      (normalizationLoss := cutoff.twoCall.schedule.second.normalizationLoss)
      (family := root.normalization.croppedFamily)
      (source := root.normalization.croppedRefined)
      (rho := cutoff.twoCall.secondQRequested hr hrRobust)
      (normalizationExponent := normalizationExponent)
      (logExponent := 61) first.lemma43 current.ordinary prepared
      hierarchy.stickyLoss hierarchy.lemma44Loss hierarchy.lemma47Loss
      hierarchy.preGrainLoss
      (Real.rpow (cutoff.twoCall.secondQRequested hr hrRobust).1
        (-hierarchy.lemma47Loss)) := {
    sticky := rich.data
    lemma44 := lemma44
    lemma47 := lemma47
    lemma412 := lemma412
  }
  refine ⟨{
    first := first
    current := current
    current_normalization_loss := currentNormalization
    preparation := preparation
    secondTerminal := rich
    second := second
    lemma44_planeMap_first_witness := by
      intro point hpoint
      rcases lemma44MapWitness point hpoint with
        ⟨finePoint, hfinePoint, hmap⟩
      refine ⟨finePoint, ?_, ?_⟩
      · rcases hfinePoint with ⟨index, hindex⟩
        exact ⟨prepared.regularized.selected.embedding index,
          prepared.denseSubshading index hindex⟩
      · exact hmap
    second_sticky_eq := rfl
    terminalCoarseReentry := rich.coarseReentry rootAxialWindow
    terminalCoarseAxialWindow :=
      rich.coarse_reentry_axial_window_of_margin rootAxialMargin
    coarse_midpoint_local := fun parent => rich.coarse_midpoint_local parent
  }, rfl⟩

/-- Run the complete robust middle from one provenance-complete root whose
ordinary trace has enough axial room for the actual second-call scale. -/
theorem Proposition63M9PreNode3CutoffData.runRobustMiddleOfAxialMargin
    {sigma outputLoss r : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    {source : PureWZ2ExtremalConfiguration sigma
      cutoff.twoCall.schedule.first.sourceLoss r}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := cutoff.twoCall.schedule.first.normalizationLoss) source
      normalizationExponent (cutoff.twoCall.schedule.second.sourceLoss / 8))
    (hr : 0 < r) (hrRobust : r ≤ cutoff.twoCall.rootCutoff)
    (rootAxialMargin : ∀ index point,
      point ∈ root.normalization.frame ''
          root.normalization.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| +
          (cutoff.twoCall.secondQRequested hr hrRobust).1 ≤ 1 / 8)
    (hqOuter : proposition63M9RobustLemma43Incidence r sigma ≤
      cutoff.outerScaleCeiling) :
    Nonempty (Proposition63M9RobustMiddleData cutoff root hr hrRobust) := by
  let firstReentry := root.normalization.toPropStickyReentryData
    cutoff.twoCall.schedule.first.sourceLoss_pos
    cutoff.twoCall.schedule.first.normalizationLoss_pos
  rcases cutoff.twoCall.runFirstRobustStage hr hrRobust
      root.normalization.croppedFamily root.normalization.croppedRefined
      firstReentry with ⟨first⟩
  rcases cutoff.runRobustMiddleFromFirst root hr hrRobust rootAxialMargin
      first hqOuter with ⟨middle, _⟩
  exact ⟨middle⟩

/-- Compatibility entry point for the first-chart route.  Its fixed
`1 / 25` window plus the frozen `q ≤ 1 / 24` bound supplies the intrinsic
axial-margin hypothesis of `runRobustMiddleOfAxialMargin`. -/
theorem Proposition63M9PreNode3CutoffData.runRobustMiddle
    {sigma outputLoss r : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    {source : PureWZ2ExtremalConfiguration sigma
      cutoff.twoCall.schedule.first.sourceLoss r}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := cutoff.twoCall.schedule.first.normalizationLoss) source
      normalizationExponent (cutoff.twoCall.schedule.second.sourceLoss / 8))
    (rootAxialTwentyFifth : ∀ index point,
      point ∈ root.normalization.frame ''
          root.normalization.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 25)
    (hr : 0 < r) (hrRobust : r ≤ cutoff.twoCall.rootCutoff)
    (hqOuter : proposition63M9RobustLemma43Incidence r sigma ≤
      cutoff.outerScaleCeiling) :
    Nonempty (Proposition63M9RobustMiddleData cutoff root hr hrRobust) := by
  have qSmall :
      (cutoff.twoCall.secondQRequested hr hrRobust).1 ≤ 1 / 24 := by
    exact cutoff.twoCall.scale.incidence_le_twentyFour hr
      (hrRobust.trans cutoff.twoCall.rootCutoff_le_scale)
  apply cutoff.runRobustMiddleOfAxialMargin root hr hrRobust
  · intro index point pointMem
    have hz := rootAxialTwentyFifth index point pointMem
    linarith
  · exact hqOuter

end Kakeya.Assouad.PureWZ2

end
