import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RobustMiddleAssembly

/-!
# Proposition 6.3 M9: robust-root adapter

This module exposes the provenance-preserving adapter from the dense
pre-Lemma-4.3 package to the exact root consumed by the robust two-call
middle.  The density absorption is paid by the frozen two-call schedule, and
the stronger axial window is inherited from the same identity normalization.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- The root normalization carried by a dense pre-Lemma-4.3 package, with the
density loss fixed by the robust two-call schedule.  No family or shading is
reselected. -/
noncomputable def Proposition63PreLemma43DenseRootData.robustRoot
    {sigma outputLoss r sourceLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss r}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (pre : Proposition63PreLemma43DenseRootData source ambient
      cutoff.twoCall.schedule.first.sourceLoss
      cutoff.twoCall.schedule.first.normalizationLoss normalizationExponent)
    (hr : 0 < r) (hrRobust : r ≤ cutoff.twoCall.rootCutoff) :
    Proposition63RootNormalizationData
      (outputLoss := cutoff.twoCall.schedule.first.normalizationLoss)
      pre.ordinarySource normalizationExponent
      (cutoff.twoCall.schedule.second.sourceLoss / 8) :=
  pre.root <| cutoff.twoCall.currentReentryAbsorption.density_absorb hr <|
    hrRobust.trans cutoff.twoCall.rootCutoff_le_currentReentry

/-- The exact `1 / 25` axial certificate for `robustRoot`.  This is the
certificate stored by `pre`; it is not reconstructed from the weaker generic
normalization window. -/
theorem Proposition63PreLemma43DenseRootData.robustRootAxialTwentyFifth
    {sigma outputLoss r sourceLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss r}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (pre : Proposition63PreLemma43DenseRootData source ambient
      cutoff.twoCall.schedule.first.sourceLoss
      cutoff.twoCall.schedule.first.normalizationLoss normalizationExponent)
    (hr : 0 < r) (hrRobust : r ≤ cutoff.twoCall.rootCutoff) :
    ∀ index point,
      point ∈ (pre.robustRoot cutoff hr hrRobust).normalization.frame ''
          (pre.robustRoot cutoff hr hrRobust).normalization.ordinaryRefined.carrier
            index →
        |point (2 : Fin 3)| ≤ 1 / 25 := by
  change ∀ index point,
    point ∈ pre.normalization.frame ''
        pre.normalization.ordinaryRefined.carrier index →
      |point (2 : Fin 3)| ≤ 1 / 25
  exact pre.normalizationAxialWindowTwentyFifth

/-- The existing `scaleCeiling` already contains the power preimage needed
for the exact robust incidence scale `q = r^(sigma / 2)`. -/
theorem Proposition63M9PreNode3CutoffData.robustIncidence_le_outerScaleCeiling
    {sigma outputLoss r : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    (hr : 0 < r) (hrScale : r ≤ cutoff.scaleCeiling) :
    proposition63M9RobustLemma43Incidence r sigma ≤
      cutoff.outerScaleCeiling := by
  have hrOne : r ≤ 1 :=
    hrScale.trans cutoff.scaleCeiling_lt_one.le
  have preliminary_le_sigma_half :
      cutoff.preliminaryStickyLoss ≤ sigma / 2 := by
    linarith [cutoff.preliminaryStickyLoss_lt_planiness,
      cutoff.planinessLoss_lt_sigma_quarter, cutoff.twoCall.scale.sigma_pos]
  have q_le_preliminary :
      proposition63M9RobustLemma43Incidence r sigma ≤
        Real.rpow r cutoff.preliminaryStickyLoss := by
    exact Real.rpow_le_rpow_of_exponent_ge hr hrOne
      preliminary_le_sigma_half
  have r_le_power : r ≤ Real.rpow cutoff.outerScaleCeiling
      (1 / cutoff.preliminaryStickyLoss) :=
    hrScale.trans <| by
      unfold Proposition63M9PreNode3CutoffData.scaleCeiling
      exact min_le_right _ _
  have preliminary_power_le :
      Real.rpow r cutoff.preliminaryStickyLoss ≤
        cutoff.outerScaleCeiling := by
    calc
      Real.rpow r cutoff.preliminaryStickyLoss ≤
          Real.rpow
            (Real.rpow cutoff.outerScaleCeiling
              (1 / cutoff.preliminaryStickyLoss))
            cutoff.preliminaryStickyLoss :=
        Real.rpow_le_rpow hr.le r_le_power
          cutoff.preliminaryStickyLoss_pos.le
      _ = Real.rpow cutoff.outerScaleCeiling
            ((1 / cutoff.preliminaryStickyLoss) *
              cutoff.preliminaryStickyLoss) :=
        (Real.rpow_mul cutoff.outerScaleCeiling_pos.le
          (1 / cutoff.preliminaryStickyLoss)
          cutoff.preliminaryStickyLoss).symm
      _ = Real.rpow cutoff.outerScaleCeiling 1 := by
        congr 1
        field_simp [cutoff.preliminaryStickyLoss_pos.ne']
      _ = cutoff.outerScaleCeiling := Real.rpow_one _
  exact q_le_preliminary.trans preliminary_power_le

/-- Feed the root and its tight axial certificate directly to the repaired
robust middle.  The source is definitionally `pre.ordinarySource`, so the
first-chart and regularization provenance remains intact. -/
theorem Proposition63M9PreNode3CutoffData.runRobustMiddleOfPre
    {sigma outputLoss r sourceLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss r}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (pre : Proposition63PreLemma43DenseRootData source ambient
      cutoff.twoCall.schedule.first.sourceLoss
      cutoff.twoCall.schedule.first.normalizationLoss normalizationExponent)
    (hr : 0 < r) (hrRobust : r ≤ cutoff.twoCall.rootCutoff)
    (hqOuter : proposition63M9RobustLemma43Incidence r sigma ≤
      cutoff.outerScaleCeiling) :
    Nonempty (Proposition63M9RobustMiddleData cutoff
      (pre.robustRoot cutoff hr hrRobust) hr hrRobust) := by
  exact cutoff.runRobustMiddle (pre.robustRoot cutoff hr hrRobust)
    (pre.robustRootAxialTwentyFifth cutoff hr hrRobust)
    hr hrRobust hqOuter

/-- First-chart production runner retaining the construction-derived
vertical bound through the otherwise unchanged robust middle. -/
theorem Proposition63M9PreNode3CutoffData.runRobustMiddleOfPreVertical
    {sigma outputLoss r sourceLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss r}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (pre : Proposition63PreLemma43DenseRootData source ambient
      cutoff.twoCall.schedule.first.sourceLoss
      cutoff.twoCall.schedule.first.normalizationLoss normalizationExponent)
    (hr : 0 < r) (hrRobust : r ≤ cutoff.twoCall.rootCutoff)
    (hqOuter : proposition63M9RobustLemma43Incidence r sigma ≤
      cutoff.outerScaleCeiling) :
    ∃ middle : Proposition63M9RobustMiddleData cutoff
        (pre.robustRoot cutoff hr hrRobust) hr hrRobust,
      ∀ point ∈ middle.first.lemma43.shading.union,
        |middle.first.lemma43.planeMap.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
  let root := pre.robustRoot cutoff hr hrRobust
  let firstReentry := root.normalization.toPropStickyReentryData
    cutoff.twoCall.schedule.first.sourceLoss_pos
    cutoff.twoCall.schedule.first.normalizationLoss_pos
  have rootDirectionVertical : ∀ index, Real.sqrt 3 / 2 ≤
      wz1PaperDirection (root.normalization.croppedFamily.tube index)
        (2 : Fin 3) := by
    exact pre.normalizationDirectionVertical
  rcases cutoff.twoCall.runFirstRobustStageVertical hr hrRobust
      root.normalization.croppedFamily root.normalization.croppedRefined
      firstReentry rootDirectionVertical with ⟨firstVertical⟩
  have rootAxialMargin : ∀ index point,
      point ∈ root.normalization.frame ''
          root.normalization.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| +
          (cutoff.twoCall.secondQRequested hr hrRobust).1 ≤ 1 / 8 := by
    intro index point pointMem
    have hz := pre.robustRootAxialTwentyFifth cutoff hr hrRobust
      index point pointMem
    have qSmall := cutoff.twoCall.scale.incidence_le_twentyFour hr
      (hrRobust.trans cutoff.twoCall.rootCutoff_le_scale)
    rw [cutoff.twoCall.secondQRequested_value]
    linarith
  rcases cutoff.runRobustMiddleFromFirst root hr hrRobust rootAxialMargin
      firstVertical.stage hqOuter with ⟨middle, hfirst⟩
  refine ⟨middle, ?_⟩
  intro point hpoint
  rw [hfirst] at hpoint ⊢
  exact firstVertical.lemma43_planeMap_vertical_bound point hpoint

/-- Root-cutoff specialization of `runRobustMiddleOfPre`.  The exact robust
incidence scale is automatically below `outerScaleCeiling`; callers only
provide the canonical root-scale bound already produced by Node 3. -/
theorem Proposition63M9PreNode3CutoffData.runRobustMiddleOfPreAtScaleCeiling
    {sigma outputLoss r sourceLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss r}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (pre : Proposition63PreLemma43DenseRootData source ambient
      cutoff.twoCall.schedule.first.sourceLoss
      cutoff.twoCall.schedule.first.normalizationLoss normalizationExponent)
    (hr : 0 < r) (hrScale : r ≤ cutoff.scaleCeiling)
    (hrRobust : r ≤ cutoff.twoCall.rootCutoff) :
    Nonempty (Proposition63M9RobustMiddleData cutoff
      (pre.robustRoot cutoff hr hrRobust) hr hrRobust) := by
  exact cutoff.runRobustMiddleOfPre pre hr hrRobust
    (cutoff.robustIncidence_le_outerScaleCeiling hr hrScale)

end Kakeya.Assouad.PureWZ2

end
