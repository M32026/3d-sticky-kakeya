import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9TwoCallRobustSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RichLemma43AmbientRestore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RichLemma43CV

/-!
# Proposition 6.3 M9: complete first robust stage

This module runs the first rich Proposition 6.2 call at the exact robust scale
`kappa = r^(sigma/16)`, selects the terminal's actual multiplicity band, runs
the pointwise paper Lemma 4.3 argument with its independent broad threshold,
and zero-extends the result to the original cropped family before restoring
extremality.

The first rich coarse family is retained only as provenance inside `rich`; it
is not used as the target family for the later exact-`q` call.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- The complete output of the first robust call through ambient Lemma 4.3
restoration.  All three fields share the same exact rich terminal witness. -/
structure Proposition63M9FirstRobustStageData
    {sigma outputLoss r : ℝ}
    (twoCall : Proposition63M9TwoCallRobustScheduleData sigma outputLoss)
    {croppedFamily : Kakeya.Streamlined.TubeFamily r}
    {normalizationExponent : ℕ}
    (croppedShading : WZ1PaperTubeShading croppedFamily)
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      twoCall.schedule.first.sourceLoss
      twoCall.schedule.first.normalizationLoss)
    (hr : 0 < r) (hrCutoff : r ≤ twoCall.rootCutoff) where
  rich : Proposition63RichTerminalStickyData
    (outputLoss := twoCall.schedule.firstOutputLoss) croppedShading reentry
    (twoCall.firstKappaRequested hr hrCutoff)
  prepared : Proposition63M9RichLemma43Preparation
    (densityLoss := 2 - sigma + 3 * twoCall.schedule.firstOutputLoss) rich
  lemma43 : Proposition63Lemma43Data
    (sigma := sigma)
    (sourceLoss := twoCall.schedule.first.normalizationLoss)
    (targetLoss := twoCall.schedule.firstOutputLoss)
    croppedShading
    (proposition63M9RobustLemma43Incidence r sigma / 2)

/-- M9-private first-stage companion retaining the vertical bound derived
from the literal first-chart direction provenance. -/
structure Proposition63M9FirstRobustStageVerticalData
    {sigma outputLoss r : ℝ}
    (twoCall : Proposition63M9TwoCallRobustScheduleData sigma outputLoss)
    {croppedFamily : Kakeya.Streamlined.TubeFamily r}
    {normalizationExponent : ℕ}
    (croppedShading : WZ1PaperTubeShading croppedFamily)
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      twoCall.schedule.first.sourceLoss
      twoCall.schedule.first.normalizationLoss)
    (hr : 0 < r) (hrCutoff : r ≤ twoCall.rootCutoff) where
  stage : Proposition63M9FirstRobustStageData
    twoCall croppedShading reentry hr hrCutoff
  lemma43_planeMap_vertical_bound : ∀ point ∈ stage.lemma43.shading.union,
    |stage.lemma43.planeMap.planeMap point (2 : Fin 3)| ≤ 1 / 2

/-- Run the complete first robust stage from the one pre-runtime schedule and
its one root cutoff.  No family-dependent scalar hypothesis remains. -/
theorem Proposition63M9TwoCallRobustScheduleData.runFirstRobustStage
    {sigma outputLoss r : ℝ}
    (twoCall : Proposition63M9TwoCallRobustScheduleData sigma outputLoss)
    (hr : 0 < r) (hrCutoff : r ≤ twoCall.rootCutoff)
    (croppedFamily : Kakeya.Streamlined.TubeFamily r)
    (croppedShading : WZ1PaperTubeShading croppedFamily)
    {normalizationExponent : ℕ}
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      twoCall.schedule.first.sourceLoss
      twoCall.schedule.first.normalizationLoss) :
    Nonempty (Proposition63M9FirstRobustStageData
      twoCall croppedShading reentry hr hrCutoff) := by
  rcases twoCall.first_runTerminal_exact_kappa hr hrCutoff
      croppedFamily croppedShading reentry with ⟨rich⟩
  have hrScale : r ≤ twoCall.scale.cutoff :=
    hrCutoff.trans twoCall.rootCutoff_le_scale
  have hrSmall : r ≤ 1 / 24 :=
    hrScale.trans <| twoCall.scale.cutoff_le_tiny.trans (by norm_num)
  have hrLtOne : r < 1 :=
    hrSmall.trans_lt (by norm_num)
  have hdegree : (96 : ENNReal) * stickyCoarseCloseCount ≤
      (rich.terminal.fineDegreeFloor : ENNReal) :=
    twoCall.first_exact_kappa_degree hr hrCutoff rich
  have hdensity := twoCall.densityCutoff.density_scalar hr
    (hrCutoff.trans twoCall.rootCutoff_le_density) rich
  rcases proposition63_m9_rich_lemma43_preparation rich hdensity
      hrSmall hdegree with ⟨prepared⟩
  have hCV := proposition63_m9_rich_lemma43_cv
    twoCall.cvWitness twoCall.cvEnvelope
    (hrCutoff.trans twoCall.rootCutoff_le_cvEnvelope) rich
  have hbroad := prepared.broad_absorb rich rfl
    twoCall.schedule.first.normalizationLoss_lt_output.le
    (twoCall.scale.theta_power hr) twoCall.broadCutoff
    (hrCutoff.trans twoCall.rootCutoff_le_broad)
  have hrestore := twoCall.ambientRestoreCutoff.restore
    reentry.toNormalizationData rich.data.selected
    (hrCutoff.trans twoCall.rootCutoff_le_ambientRestore)
  rcases proposition63_m9_rich_lemma43_ambient_restore
      rich prepared hCV
      ((twoCall.kappa_le_degreeCutoff hr hrCutoff).trans
        (twoCall.degreeCutoff.delta₀_le_small.trans (by norm_num)))
      hdegree
      (twoCall.scale.theta_pos hr hrScale)
      (twoCall.scale.incidence_half hr hrScale)
      hbroad hrLtOne reentry.cropped_extremal
      twoCall.schedule.firstOutputLoss_pos
      twoCall.schedule.first.normalizationLoss_lt_output.le
      hrestore with ⟨lemma43⟩
  exact ⟨{ rich := rich, prepared := prepared, lemma43 := lemma43 }⟩

/-- Direction-aware first robust stage used by the first-chart M9 route. -/
theorem Proposition63M9TwoCallRobustScheduleData.runFirstRobustStageVertical
    {sigma outputLoss r : ℝ}
    (twoCall : Proposition63M9TwoCallRobustScheduleData sigma outputLoss)
    (hr : 0 < r) (hrCutoff : r ≤ twoCall.rootCutoff)
    (croppedFamily : Kakeya.Streamlined.TubeFamily r)
    (croppedShading : WZ1PaperTubeShading croppedFamily)
    {normalizationExponent : ℕ}
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      twoCall.schedule.first.sourceLoss
      twoCall.schedule.first.normalizationLoss)
    (hfamilyVertical : ∀ index, Real.sqrt 3 / 2 ≤
      wz1PaperDirection (croppedFamily.tube index) (2 : Fin 3)) :
    Nonempty (Proposition63M9FirstRobustStageVerticalData
      twoCall croppedShading reentry hr hrCutoff) := by
  rcases twoCall.first_runTerminal_exact_kappa hr hrCutoff
      croppedFamily croppedShading reentry with ⟨rich⟩
  have hrScale : r ≤ twoCall.scale.cutoff :=
    hrCutoff.trans twoCall.rootCutoff_le_scale
  have hrSmall : r ≤ 1 / 24 :=
    hrScale.trans <| twoCall.scale.cutoff_le_tiny.trans (by norm_num)
  have hrLtOne : r < 1 := hrSmall.trans_lt (by norm_num)
  have hdegree : (96 : ENNReal) * stickyCoarseCloseCount ≤
      (rich.terminal.fineDegreeFloor : ENNReal) :=
    twoCall.first_exact_kappa_degree hr hrCutoff rich
  have hdensity := twoCall.densityCutoff.density_scalar hr
    (hrCutoff.trans twoCall.rootCutoff_le_density) rich
  rcases proposition63_m9_rich_lemma43_preparation rich hdensity
      hrSmall hdegree with ⟨prepared⟩
  have hCV := proposition63_m9_rich_lemma43_cv
    twoCall.cvWitness twoCall.cvEnvelope
    (hrCutoff.trans twoCall.rootCutoff_le_cvEnvelope) rich
  have hbroad := prepared.broad_absorb rich rfl
    twoCall.schedule.first.normalizationLoss_lt_output.le
    (twoCall.scale.theta_power hr) twoCall.broadCutoff
    (hrCutoff.trans twoCall.rootCutoff_le_broad)
  have hrestore := twoCall.ambientRestoreCutoff.restore
    reentry.toNormalizationData rich.data.selected
    (hrCutoff.trans twoCall.rootCutoff_le_ambientRestore)
  rcases proposition63_m9_rich_lemma43_ambient_restore_vertical
      rich prepared hCV
      ((twoCall.kappa_le_degreeCutoff hr hrCutoff).trans
        (twoCall.degreeCutoff.delta₀_le_small.trans (by norm_num)))
      hdegree (twoCall.scale.theta_pos hr hrScale)
      (twoCall.scale.incidence_half hr hrScale) hbroad hrLtOne
      reentry.cropped_extremal twoCall.schedule.firstOutputLoss_pos
      twoCall.schedule.first.normalizationLoss_lt_output.le hrestore
      hfamilyVertical with ⟨vertical⟩
  let stage : Proposition63M9FirstRobustStageData
      twoCall croppedShading reentry hr hrCutoff := {
    rich := rich
    prepared := prepared
    lemma43 := vertical.lemma43 }
  exact ⟨{
    stage := stage
    lemma43_planeMap_vertical_bound := vertical.planeMap_vertical_bound
  }⟩

end Kakeya.Assouad.PureWZ2

end
