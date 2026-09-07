import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RobustMiddleAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PreliminaryLocalGrain

/-!
# Proposition 6.3 M9: the exact second coarse pair as a preliminary root

The second Proposition 6.2 call in the repaired robust middle is the genuine
`q`-scale call.  This module retains its terminal coarse re-entry and packages
the subsequent Lemma 4.12 shading as preliminary local-grain data on exactly
that normalized coarse family.  No coarse family is reselected here.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

namespace Proposition63M9RobustMiddleData

/-- The axial certificate used by the second rich call, before passing to its
coarse re-entry. -/
theorem secondRootAxialWindow
    {sigma outputLoss r : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    {source : PureWZ2ExtremalConfiguration sigma
      cutoff.twoCall.schedule.first.sourceLoss r}
    {normalizationExponent : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := cutoff.twoCall.schedule.first.normalizationLoss) source
      normalizationExponent (cutoff.twoCall.schedule.second.sourceLoss / 8)}
    {hr : 0 < r} {hrRobust : r ≤ cutoff.twoCall.rootCutoff}
    (middle : Proposition63M9RobustMiddleData cutoff root hr hrRobust) :
    ∀ index point,
      point ∈
          (middle.preparation.prepared.normalization.toPropStickyReentryData
            middle.preparation.prepared.target_loss_pos
            middle.preparation.prepared.normalization_loss_pos).geometry.frame ''
        (middle.preparation.prepared.normalization.toPropStickyReentryData
            middle.preparation.prepared.target_loss_pos
            middle.preparation.prepared.normalization_loss_pos).geometry.ordinaryRefined.carrier
          index →
        |point (2 : Fin 3)| ≤ 1 / 8 :=
  proposition63_reentry_axial_window_of_margin
    (middle.preparation.prepared.normalization.toPropStickyReentryData
      middle.preparation.prepared.target_loss_pos
      middle.preparation.prepared.normalization_loss_pos)
    (cutoff.twoCall.secondQRequested hr hrRobust)
    middle.preparation.root_axial_margin

/-- The exact coarse re-entry emitted by the second terminal call, rewritten
onto the sticky object retained by the dependent Lemma 4.12 output. -/
noncomputable def secondCoarseReentry
    {sigma outputLoss r : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    {source : PureWZ2ExtremalConfiguration sigma
      cutoff.twoCall.schedule.first.sourceLoss r}
    {normalizationExponent : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := cutoff.twoCall.schedule.first.normalizationLoss) source
      normalizationExponent (cutoff.twoCall.schedule.second.sourceLoss / 8)}
    {hr : 0 < r} {hrRobust : r ≤ cutoff.twoCall.rootCutoff}
    (middle : Proposition63M9RobustMiddleData cutoff root hr hrRobust) :
    PureWZ2PropStickyReentryData
      (sigma := sigma) middle.second.sticky.croppedCoarseShading 0
      middle.secondTerminal.coarseSourceLoss
      middle.secondTerminal.coarseNormalizationLoss :=
  middle.terminalCoarseReentry

/-- The coarse ordinary source of the second call retains the strict axial
window needed by a later current-shading re-entry. -/
theorem secondCoarseAxialWindow
    {sigma outputLoss r : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    {source : PureWZ2ExtremalConfiguration sigma
      cutoff.twoCall.schedule.first.sourceLoss r}
    {normalizationExponent : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := cutoff.twoCall.schedule.first.normalizationLoss) source
      normalizationExponent (cutoff.twoCall.schedule.second.sourceLoss / 8)}
    {hr : 0 < r} {hrRobust : r ≤ cutoff.twoCall.rootCutoff}
    (middle : Proposition63M9RobustMiddleData cutoff root hr hrRobust) :
    ∀ index point,
      point ∈ middle.secondCoarseReentry.geometry.frame ''
          middle.secondCoarseReentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8 := by
  exact middle.terminalCoarseAxialWindow

/-- The normalization carried by the actual second-call coarse family. -/
noncomputable def secondCoarseNormalization
    {sigma outputLoss r : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    {source : PureWZ2ExtremalConfiguration sigma
      cutoff.twoCall.schedule.first.sourceLoss r}
    {normalizationExponent : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := cutoff.twoCall.schedule.first.normalizationLoss) source
      normalizationExponent (cutoff.twoCall.schedule.second.sourceLoss / 8)}
    {hr : 0 < r} {hrRobust : r ≤ cutoff.twoCall.rootCutoff}
    (middle : Proposition63M9RobustMiddleData cutoff root hr hrRobust) :=
  middle.secondCoarseReentry.toNormalizationData

/-- Lemma 4.12 on the exact `q`-family is a preliminary local-grain package
for the next paper stage.  Its subshading proof follows the complete chain
`Lemma 4.12 -> Lemma 4.7 -> Lemma 4.4 -> second terminal coarse shading`. -/
noncomputable def secondCoarsePreliminary
    {sigma outputLoss r : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    {source : PureWZ2ExtremalConfiguration sigma
      cutoff.twoCall.schedule.first.sourceLoss r}
    {normalizationExponent : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := cutoff.twoCall.schedule.first.normalizationLoss) source
      normalizationExponent (cutoff.twoCall.schedule.second.sourceLoss / 8)}
    {hr : 0 < r} {hrRobust : r ≤ cutoff.twoCall.rootCutoff}
    (middle : Proposition63M9RobustMiddleData cutoff root hr hrRobust) :
    Proposition63PreliminaryLocalGrainData
      (localLoss := hierarchy.preGrainLoss)
      (reentryLoss := hierarchy.preGrainLoss)
      middle.secondCoarseNormalization where
  shading := middle.second.lemma412.shading
  subshading := by
    intro index point pointMem
    change point ∈ middle.second.sticky.croppedCoarseShading.carrier index
    exact middle.second.lemma44.coarse_subshading index
      (middle.second.lemma47.subshading index
        (middle.second.lemma412.subshading index pointMem))
  cubical := middle.second.lemma412.cubical
  extremal := middle.second.lemma412.extremal
  topLevelCWA := middle.second.lemma412.top_level_cwa
  incidence := (cutoff.twoCall.secondQRequested hr hrRobust).1
  lipschitz := Real.toNNReal
    (Real.rpow (cutoff.twoCall.secondQRequested hr hrRobust).1
      (-hierarchy.lemma47Loss))
  incidence_nonnegative :=
    hr.le.trans (cutoff.twoCall.secondQRequested hr hrRobust).2.1
  localGrains := Proposition63InitialWeakLocalGrainData.ofRelaxed
    middle.second.lemma412.localGrains

/-- The weak plane map carried by the exact `q`-scale preliminary object. -/
noncomputable def secondCoarsePreliminaryMap
    {sigma outputLoss r : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    {source : PureWZ2ExtremalConfiguration sigma
      cutoff.twoCall.schedule.first.sourceLoss r}
    {normalizationExponent : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := cutoff.twoCall.schedule.first.normalizationLoss) source
      normalizationExponent (cutoff.twoCall.schedule.second.sourceLoss / 8)}
    {hr : 0 < r} {hrRobust : r ≤ cutoff.twoCall.rootCutoff}
    (middle : Proposition63M9RobustMiddleData cutoff root hr hrRobust) :
    PaperWZ1WeakPlaneMapData middle.second.lemma412.shading
      (cutoff.twoCall.secondQRequested hr hrRobust).1 :=
  paperWeakPlaneMapRestrict middle.second.lemma47.planeMap
    middle.second.lemma412.subshading

/-- Lemma 4.12 keeps the Lemma-4.4 plane map, hence it is constant on the
actual `q`-grid cells. -/
theorem secondCoarsePreliminaryMap_cellwise
    {sigma outputLoss r : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    {source : PureWZ2ExtremalConfiguration sigma
      cutoff.twoCall.schedule.first.sourceLoss r}
    {normalizationExponent : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := cutoff.twoCall.schedule.first.normalizationLoss) source
      normalizationExponent (cutoff.twoCall.schedule.second.sourceLoss / 8)}
    {hr : 0 < r} {hrRobust : r ≤ cutoff.twoCall.rootCutoff}
    (middle : Proposition63M9RobustMiddleData cutoff root hr hrRobust) :
    ∀ first second,
      wz1PaperGridIndex
          (cutoff.twoCall.secondQRequested hr hrRobust).1 first =
        wz1PaperGridIndex
          (cutoff.twoCall.secondQRequested hr hrRobust).1 second →
      middle.secondCoarsePreliminaryMap.planeMap first =
        middle.secondCoarsePreliminaryMap.planeMap second := by
  intro first second sameCell
  change middle.second.lemma47.planeMap.planeMap first =
    middle.second.lemma47.planeMap.planeMap second
  rw [middle.second.lemma47.same_plane_map]
  exact middle.second.lemma44.planeMap_constant_on_cells first second sameCell

end Proposition63M9RobustMiddleData

end Kakeya.Assouad.PureWZ2

end
