import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9Lemma43RestoreAbsorption

/-!
# Proposition 6.3 M9 same-extremizer loss cutoff

The second rich call must use the ordinary shading produced by Lemma 4.3,
but this does not force its loss exponent to equal the later re-entry loss.
This module freezes a strict loss ladder before runtime.  For a re-entry loss
`R`, Lemma 4.3 outputs at `R / 4`, the density absorption uses `R / 8`, and
the re-entry weight uses `3 * R / 4`.  Thus the current/density cost lies
strictly below the weight, while the weight lies strictly below `R`.

The normalization hypothesis is the exact remaining scalar requirement for
the regularization absorption: two normalization losses must fit between the
weight and the re-entry loss.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- A pre-runtime loss choice for the same-extremizer second re-entry. -/
structure Proposition63M9SameExtremizerLossData
    (lemma43SourceLoss rootNormalizationLoss reentryLoss : ℝ) where
  lemma43OutputLoss : ℝ
  secondReentryDensityLoss : ℝ
  secondReentryWeightLoss : ℝ
  lemma43OutputLoss_eq : lemma43OutputLoss = reentryLoss / 4
  secondReentryDensityLoss_eq : secondReentryDensityLoss = reentryLoss / 8
  secondReentryWeightLoss_eq : secondReentryWeightLoss = 3 * reentryLoss / 4
  lemma43_output_pos : 0 < lemma43OutputLoss
  lemma43_output_le_reentry : lemma43OutputLoss ≤ reentryLoss
  lemma43_source_le_output : lemma43SourceLoss ≤ lemma43OutputLoss
  lemma43_source_lt_output : lemma43SourceLoss < lemma43OutputLoss
  source_lt_density : lemma43SourceLoss < secondReentryDensityLoss
  density_add_current_lt_weight :
    secondReentryDensityLoss + lemma43OutputLoss < secondReentryWeightLoss
  weight_lt_reentry : secondReentryWeightLoss < reentryLoss
  regularization_gap :
    0 < reentryLoss - secondReentryWeightLoss - 2 * rootNormalizationLoss

/-- The canonical quarter/eighth/three-quarter loss ladder. -/
def proposition63_m9_same_extremizer_losses
    (lemma43SourceLoss rootNormalizationLoss reentryLoss : ℝ)
    (hreentry : 0 < reentryLoss)
    (hsource : lemma43SourceLoss < reentryLoss / 8)
    (hnormalization : rootNormalizationLoss < reentryLoss / 8) :
    Proposition63M9SameExtremizerLossData
      lemma43SourceLoss rootNormalizationLoss reentryLoss where
  lemma43OutputLoss := reentryLoss / 4
  secondReentryDensityLoss := reentryLoss / 8
  secondReentryWeightLoss := 3 * reentryLoss / 4
  lemma43OutputLoss_eq := rfl
  secondReentryDensityLoss_eq := rfl
  secondReentryWeightLoss_eq := rfl
  lemma43_output_pos := by linarith
  lemma43_output_le_reentry := by linarith
  lemma43_source_le_output := by linarith
  lemma43_source_lt_output := by linarith
  source_lt_density := hsource
  density_add_current_lt_weight := by linarith
  weight_lt_reentry := by linarith
  regularization_gap := by linarith

/-- The loss ladder together with the uniform scalar cutoff needed by the
second current-shading re-entry. -/
structure Proposition63M9SameExtremizerCutoffData
    (lemma43SourceLoss rootNormalizationLoss reentryLoss : ℝ) where
  losses : Proposition63M9SameExtremizerLossData
    lemma43SourceLoss rootNormalizationLoss reentryLoss
  absorption : Proposition63CurrentReentryAbsorptionData
    lemma43SourceLoss rootNormalizationLoss
    losses.secondReentryDensityLoss losses.lemma43OutputLoss
    losses.secondReentryWeightLoss reentryLoss
    (proposition63CanonicalNearbyLevelCount rootNormalizationLoss)
  lemma43Restore : Proposition63M9Lemma43RestoreAbsorptionData
    lemma43SourceLoss losses.lemma43OutputLoss

/-- Freeze the loss ladder and all analytic absorption thresholds before the
runtime extremizer, nearby-scale schedule, or current shading is selected. -/
theorem proposition63_m9_same_extremizer_cutoff
    (lemma43SourceLoss rootNormalizationLoss reentryLoss : ℝ)
    (hreentry : 0 < reentryLoss)
    (hsource : lemma43SourceLoss < reentryLoss / 8)
    (hnormalizationPos : 0 < rootNormalizationLoss)
    (hnormalization : rootNormalizationLoss < reentryLoss / 8) :
    Nonempty (Proposition63M9SameExtremizerCutoffData
      lemma43SourceLoss rootNormalizationLoss reentryLoss) := by
  let losses := proposition63_m9_same_extremizer_losses
    lemma43SourceLoss rootNormalizationLoss reentryLoss
    hreentry hsource hnormalization
  rcases proposition63_current_reentry_absorption
      lemma43SourceLoss rootNormalizationLoss
      losses.secondReentryDensityLoss losses.lemma43OutputLoss
      losses.secondReentryWeightLoss reentryLoss
      (proposition63CanonicalNearbyLevelCount rootNormalizationLoss)
      losses.source_lt_density hnormalizationPos
      losses.density_add_current_lt_weight losses.weight_lt_reentry
      (proposition63CanonicalNearbyLevelCount_pos hnormalizationPos)
      hreentry losses.regularization_gap with
    ⟨absorption⟩
  rcases proposition63_m9_lemma43_restore_absorption
      lemma43SourceLoss losses.lemma43OutputLoss
      losses.lemma43_source_lt_output with
    ⟨lemma43Restore⟩
  exact ⟨⟨losses, absorption, lemma43Restore⟩⟩

theorem Proposition63M9SameExtremizerCutoffData.delta₀_pos
    {lemma43SourceLoss rootNormalizationLoss reentryLoss : ℝ}
    (data : Proposition63M9SameExtremizerCutoffData
      lemma43SourceLoss rootNormalizationLoss reentryLoss) :
    0 < data.absorption.delta₀ :=
  data.absorption.delta₀_pos

theorem Proposition63M9SameExtremizerCutoffData.delta₀_le_one
    {lemma43SourceLoss rootNormalizationLoss reentryLoss : ℝ}
    (data : Proposition63M9SameExtremizerCutoffData
      lemma43SourceLoss rootNormalizationLoss reentryLoss) :
    data.absorption.delta₀ ≤ 1 :=
  data.absorption.delta₀_le_one

end Kakeya.Assouad.PureWZ2
