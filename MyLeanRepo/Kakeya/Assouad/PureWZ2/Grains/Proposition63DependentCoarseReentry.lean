import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentTwoLevelCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63InitialLocalGrainReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropStickyScheduledCoarseReentry

/-!
# Current-shading producer for the dependent Lemma 4.9 re-entry

Node 3's synchronized capability now supplies one scheduled first coarse pair
together with its exact ordinary normalization.  This file packages that pair
directly for the dependent second Proposition 6.2 call.  It also retains the
generic current-shading adapter used after later Node 4 refinements, with its
complete mass ledger.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- Identity-provenance adapter from an exact re-entry certificate on an
outer sticky coarse pair to the dependent Node 4 input. -/
noncomputable def exactCoarseDependentReentry
    {delta sigma outputLoss sourceLoss normalizationLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {outerLogExponent normalizationExponent : ℕ}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss) sourceShading rho
      outerLogExponent)
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) outer.croppedCoarseShading normalizationExponent
      sourceLoss normalizationLoss) :
    Proposition63DependentCoarseReentryData
      (reentryLoss := normalizationLoss) outer normalizationExponent :=
  { sourceLoss := sourceLoss
    source := reentry.ordinarySource
    normalization := reentry.toNormalizationData
    coarseEmbedding := Function.Embedding.refl _
    coarse_tube_eq := by
      intro index
      rfl
    normalized_subshading := by
      intro index point pointMem
      exact pointMem
    retentionFactor := 1
    retentionFactor_pos := by norm_num
    retentionFactor_ne_top := by norm_num
    retained_mass := by
      simp [PureWZ2PropStickyReentryData.toNormalizationData] }

/-- Node 3's scheduled first coarse output already carries the exact ordinary
normalization needed by the second Proposition 6.2 call.  Repackage it as the
dependent Node 4 input without changing the family or shading. -/
noncomputable def scheduledCoarseDependentReentry
    {capability : PureWZ2PropStickyCapability}
    {sigma nextOutputLoss : ℝ}
    (data : PureWZ2ScheduledCoarseReentryData
      capability sigma nextOutputLoss) :
    Proposition63DependentCoarseReentryData
      (reentryLoss := data.schedule.kernel.normalizationLoss)
      data.first.data capability.normalizationExponent :=
  exactCoarseDependentReentry data.first.data data.reentry

/-- Repackage the exact coarse certificate retained by any rich Node 3 call
as the dependent Node 4 input, without changing the coarse family or shading. -/
noncomputable def reentrantCoarseDependentReentry
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent logExponent : ℕ}
    (outer : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := outputLoss) sourceShading rho
      normalizationExponent logExponent) :
    Proposition63DependentCoarseReentryData
      (reentryLoss := outer.coarseNormalizationLoss) outer.data
      normalizationExponent :=
  exactCoarseDependentReentry outer.data outer.coarseReentry

/-- Package the plain second output of a preselected rich two-call schedule as
the dependent cover used by the Node 4 one-scale argument. -/
theorem richTwoCallDependentSecond
    {sigma outputLoss : ℝ}
    (schedule : Proposition63RichTwoCallScheduleData sigma outputLoss)
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    (firstOutput : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := schedule.firstOutputLoss)
      sourceShading rho 0 61)
    (hrhoBound : rho.1 ≤ schedule.second.delta₀)
    (tau : WZ2PaperRequestedScale rho.1)
    (tau_lower : Real.rpow rho.1 (1 - outputLoss) ≤ tau.1)
    (tau_upper : tau.1 ≤ Real.rpow rho.1 outputLoss) :
    Nonempty (Proposition63DependentTwoLevelCoverData
      (innerLoss := outputLoss) (innerLogExponent := 61)
      (exactCoarseDependentReentry firstOutput.data
        (schedule.reentryForSecond firstOutput)) tau) := by
  rcases schedule.runSecond firstOutput hrhoBound tau tau_lower tau_upper with
    ⟨secondOutput⟩
  exact ⟨{ inner := secondOutput }⟩

/-- Run the scheduled second Proposition 6.2 call on the exact first coarse
pair.  This is the direct Node 3 to Node 4 bridge: the second call consumes
the normalization carried by the first output, rather than an independently
chosen root configuration. -/
theorem scheduledCoarseDependentSecond
    {capability : PureWZ2PropStickyCapability}
    {sigma nextOutputLoss : ℝ}
    (data : PureWZ2ScheduledCoarseReentryData
      capability sigma nextOutputLoss)
    (tau : WZ2PaperRequestedScale data.scale)
    (tau_lower : Real.rpow data.scale (1 - nextOutputLoss) ≤ tau.1)
    (tau_upper : tau.1 ≤ Real.rpow data.scale nextOutputLoss) :
    Nonempty (Proposition63DependentTwoLevelCoverData
      (innerLoss := nextOutputLoss)
      (innerLogExponent := capability.logExponent)
      (scheduledCoarseDependentReentry data) tau) := by
  rcases data.schedule.kernel.run data.scale
      data.first.data.coarse_extremal.delta_pos data.firstScale_le_kernel
      data.family data.shading data.reentry tau tau_lower tau_upper with
    ⟨inner⟩
  exact ⟨{ inner := inner }⟩

/-- Turn a completed current-shading re-entry on the first cover's actual
coarse family into the provenance record consumed by the dependent second
Proposition 6.2 call. -/
noncomputable def proposition63DependentCoarseReentryOfCurrent
    {delta sigma outerLoss coarseInputLoss coarseNormalizationLoss
      reentryLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {outerLogExponent normalizationExponent : ℕ}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent)
    {coarseSource :
      PureWZ2ExtremalConfiguration sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      normalizationExponent)
    (current : WZ1PaperTubeShading coarseNormalized.croppedFamily)
    (currentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) coarseNormalized
      current)
    (ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      coarseNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index))
    (current_sub_outer : ∀ index, current.carrier index ⊆
      outer.croppedCoarseShading.carrier (ancestorEmbedding index))
    (ancestorRetentionFactor : ENNReal)
    (ancestorRetentionFactor_pos : 0 < ancestorRetentionFactor)
    (ancestorRetentionFactor_ne_top : ancestorRetentionFactor ≠ ⊤)
    (current_retained_mass :
      ancestorRetentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
        current.mass) :
    Proposition63DependentCoarseReentryData
      (reentryLoss := currentReentry.reentryNormalizationLoss) outer
        normalizationExponent := by
  let traceCoefficient : ENNReal :=
    currentReentry.regularized.regularizationLoss⁻¹ *
      ((73 / 100 : ENNReal) * currentReentry.normalizationWeight)
  let retainedCoefficient : ENNReal :=
    traceCoefficient * ancestorRetentionFactor⁻¹
  have hregularizationPos :
      0 < currentReentry.regularized.regularizationLoss := by
    rw [currentReentry.regularized.regularizationLoss_eq]
    positivity
  have hregularizationTop :
      currentReentry.regularized.regularizationLoss ≠ ⊤ := by
    rw [currentReentry.regularized.regularizationLoss_eq]
    exact ENNReal.mul_ne_top (by norm_num) (by simp)
  have htraceCoefficientPos : 0 < traceCoefficient := by
    apply ENNReal.mul_pos
    · exact ENNReal.inv_ne_zero.mpr hregularizationTop
    · exact (ENNReal.mul_pos
        (by norm_num : (73 / 100 : ENNReal) ≠ 0)
        currentReentry.normalization_weight_ne_zero).ne'
  have htraceCoefficientTop : traceCoefficient ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.inv_ne_top.mpr hregularizationPos.ne'
    · exact ENNReal.mul_ne_top
        (ENNReal.div_ne_top (by norm_num) (by norm_num))
        currentReentry.normalization_weight_ne_top
  have hcoefficientPos : 0 < retainedCoefficient := by
    apply ENNReal.mul_pos htraceCoefficientPos.ne'
    exact ENNReal.inv_ne_zero.mpr ancestorRetentionFactor_ne_top
  have hcoefficientTop : retainedCoefficient ≠ ⊤ := by
    apply ENNReal.mul_ne_top htraceCoefficientTop
    exact ENNReal.inv_ne_top.mpr ancestorRetentionFactor_pos.ne'
  have htraceRetained : traceCoefficient * current.mass ≤
      currentReentry.normalization.croppedRefined.mass := by
    have hscaled := mul_le_mul_left' currentReentry.reentryMassRetention
      currentReentry.regularized.regularizationLoss⁻¹
    calc
      traceCoefficient * current.mass =
          currentReentry.regularized.regularizationLoss⁻¹ *
            (((73 / 100 : ENNReal) *
                currentReentry.normalizationWeight) *
              current.mass) := by
        simp only [traceCoefficient]
        ring
      _ ≤ currentReentry.regularized.regularizationLoss⁻¹ *
          (currentReentry.regularized.regularizationLoss *
            currentReentry.normalization.croppedRefined.mass) := hscaled
      _ = currentReentry.normalization.croppedRefined.mass := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel
          hregularizationPos.ne' hregularizationTop, one_mul]
  have hretained : retainedCoefficient * outer.croppedCoarseShading.mass ≤
      currentReentry.normalization.croppedRefined.mass := by
    calc
      retainedCoefficient * outer.croppedCoarseShading.mass =
          traceCoefficient *
            (ancestorRetentionFactor⁻¹ *
              outer.croppedCoarseShading.mass) := by
        simp only [retainedCoefficient]
        ring
      _ ≤ traceCoefficient * current.mass := by gcongr
      _ ≤ currentReentry.normalization.croppedRefined.mass :=
        htraceRetained
  refine
    { sourceLoss := reentryLoss
      source := currentReentry.ordinarySource
      normalization := currentReentry.normalization
      coarseEmbedding :=
        currentReentry.regularized.selected.embedding.trans ancestorEmbedding
      coarse_tube_eq := ?_
      normalized_subshading := ?_
      retentionFactor := retainedCoefficient⁻¹
      retentionFactor_pos := ENNReal.inv_pos.mpr hcoefficientTop
      retentionFactor_ne_top := ENNReal.inv_ne_top.mpr hcoefficientPos.ne'
      retained_mass := ?_ }
  · intro index
    change currentReentry.regularized.selected.family.tube index = _
    exact (currentReentry.regularized.selected.tube_eq index).trans
      (ancestor_tube_eq
        (currentReentry.regularized.selected.embedding index))
  · intro index point hpoint
    exact current_sub_outer (currentReentry.regularized.selected.embedding index)
      (currentReentry.denseSubshading index hpoint)
  · simpa [retainedCoefficient] using hretained

end Kakeya.Assouad.PureWZ2

end
