import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedJointIncidenceSetup
import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicLogLossAbsorption
import MyLeanRepo.Kakeya.Cinematic.Section5.SmallJointFiberScaleAbsorptionInputs

/-!
# Small joint retained-fiber exit in one ambient bin

If the canonical retained scale is below the logarithmic threshold needed by
the separated-ball Lemma 47 branch, absorb it directly into the final
multiplicity budget.
-/

namespace Kakeya.Cinematic

theorem ambient_restricted_small_joint_fiber_exit
    (hSmall : SmallJointFiberScaleAbsorptionStatement)
    (K C_count metricExponent targetExponent : ℝ)
    (hK : 1 ≤ K)
    (hC_count : 0 ≤ C_count)
    (hmetric : 0 < metricExponent)
    (hmetric_le_quarter : metricExponent ≤ 1 / 4)
    (htarget : 0 < targetExponent)
    (hmetric_target : 4 * metricExponent ≤ targetExponent) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 / 2 ∧
      ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
        {D delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ},
        ∀ (data : DyadicFineAssignmentData
            family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
          (center : C2Function)
          (hE : MeasurableSet E)
          {C_R C_shading C_volume : ℝ}
          (fineSetup : AmbientRestrictedFSVSetupData
            data center hE C_R C_count C_shading C_volume)
          (coarseSetup : AmbientRestrictedCoarseSetupData
            data center hE fineSetup)
          {massExponent : ℝ}
          (refinement : AmbientRestrictedLargeBinRefinementData
            data center hE fineSetup coarseSetup massExponent)
          (incidence : AmbientRestrictedJointIncidenceSetupData
            data center hE fineSetup coarseSetup refinement),
          epsilon = metricExponent →
          eta = metricExponent ^ 2 →
          diameter = K →
          0 < delta →
          delta ≤ delta₀ →
          incidence.q_fiber < 8 * incidence.heavySetup.heavyLogLoss →
          1 ≤
            Real.rpow delta (-targetExponent) *
              Real.rpow (data.mu : ℝ) (-3 / 2 : ℝ) := by
  let tangencyExponent := metricExponent ^ 2
  let logExponent := metricExponent / 4
  have htangency : 0 < tangencyExponent := by
    dsimp only [tangencyExponent]
    positivity
  have hlogExponent : 0 < logExponent := by
    dsimp only [logExponent]
    positivity
  have hmargin :
      (3 / 2 : ℝ) *
          (metricExponent + tangencyExponent + logExponent) <
        targetExponent := by
    dsimp only [tangencyExponent, logExponent]
    nlinarith
  rcases hSmall K metricExponent tangencyExponent logExponent
      targetExponent hK hmetric htangency hlogExponent hmargin with
    ⟨deltaSmall, hdeltaSmall, hdeltaSmallOne, hsmallMain⟩
  rcases dyadic_log_loss_absorption C_count logExponent
      hC_count hlogExponent with
    ⟨deltaLog, hdeltaLog, hdeltaLogHalf, hlogMain⟩
  let delta₀ := min deltaSmall deltaLog
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀_half : delta₀ ≤ 1 / 2 := by
    dsimp only [delta₀]
    exact (min_le_right _ _).trans hdeltaLogHalf
  refine ⟨delta₀, hdelta₀, hdelta₀_half, ?_⟩
  intro family E D delta diameter epsilon eta tRep DeltaRep C_R₀
    data center hE C_R C_shading C_volume fineSetup coarseSetup
    massExponent refinement incidence hepsilon heta hdiameter
    hdelta hdeltaBound hqSmall
  have hdeltaSmall' : delta ≤ deltaSmall :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaLog' : delta ≤ deltaLog :=
    hdeltaBound.trans (min_le_right _ _)
  have hlogLoss :
      incidence.heavySetup.heavyLogLoss ≤
        Real.rpow delta (-logExponent) := by
    rw [incidence.heavySetup.heavyLogLoss_eq,
      incidence.heavySetup.degreeLoss_eq]
    have hfine :
        (fineSetup.fine.card : ℝ) ≤
          Real.rpow delta (-C_count) :=
      fineSetup.fine_card
    have hraw := hlogMain hdelta hdeltaLog' hfine
    simpa using hraw
  have hdeltaDelta : delta ≤ DeltaRep := data.delta_le_DeltaRep
  have hDeltaT : DeltaRep ≤ tRep := data.DeltaRep_le_tRep
  have htK : tRep ≤ 8 * K := by
    rcases refinement.selected_nonempty with ⟨i, hi⟩
    have h :=
      (ambientRestrictedData data center hE).tRep_le_eight_diameter
        hdelta (fineSetup.source i)
    rw [hdiameter] at h
    exact h
  have hepsilon' : epsilon = metricExponent := by
    exact hepsilon
  have heta' : eta = tangencyExponent := by
    simpa [tangencyExponent] using heta
  have hretention_eq :
      incidence.retention =
        Real.rpow (tRep / (8 * K)) metricExponent *
          Real.rpow (DeltaRep / (2 * tRep)) tangencyExponent := by
    rw [incidence.retention_eq]
    rw [hepsilon', heta', hdiameter]
  have hretention :
      Real.rpow (tRep / (8 * K)) metricExponent *
            Real.rpow (DeltaRep / (2 * tRep)) tangencyExponent *
            (data.mu : ℝ) <
          4 * ((incidence.q_fiber : ℝ) + 1) := by
    rw [← hretention_eq]
    exact incidence.retention_mu
  exact hsmallMain hdelta hdeltaSmall'
    hdeltaDelta hDeltaT htK data.mu_pos
    (by
      rw [incidence.heavySetup.heavyLogLoss_eq,
        incidence.heavySetup.degreeLoss_eq]
      have hdegree : 0 < Nat.log2 (Fintype.card (Fin fineSetup.fine.card)) + 1 := by
        omega
      exact_mod_cast (show
        1 ≤ 4 * (Nat.log2 (Fintype.card (Fin fineSetup.fine.card)) + 1) by
          omega))
    hlogLoss hqSmall hretention

end Kakeya.Cinematic
