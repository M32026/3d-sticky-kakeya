import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedAutomaticParentTangencyScaleInputs

/-!
# Automatic parent tangency scale

Connect the tangency-automatic parent pair-incidence output to the independent
parent multiplicity algebra with the safe fiber coefficient `4`.
-/

namespace Kakeya.Cinematic

theorem ambient_restricted_automatic_parent_tangency_scale :
    AmbientRestrictedAutomaticParentTangencyScaleStatement := by
  intro hCutoffs hAutoGoodPairs hPairIncidence hJoint hTangencyScale K D hK hD
  rcases hJoint hCutoffs hAutoGoodPairs hPairIncidence K D hK hD with
    ⟨C_inc, hC_inc_pos, hC_inc⟩
  refine' ⟨C_inc, hC_inc_pos, _⟩
  intro family E delta diameter epsilon eta tRep DeltaRep C_R₀
    data center hE C_R C_count C_shading C_volume
    fineSetup coarseSetup massExponent refinement incidence
    hCinematic hdelta hC_R hq_fiber hmetric htangencyCut hten hhundred hfiberUpper
  let incidenceScale : ℝ :=
    C_inc * Real.sqrt (delta * (C_R * tRep * DeltaRep / delta) /
      ((selectedIncidenceMetricCut incidence.heavySetup.heavyLogLoss
        (4 * Real.rpow (2 * tRep / DeltaRep) eta) epsilon * tRep / 8) * delta)) + 1
  have hpairs :=
    hC_inc data center hE fineSetup coarseSetup refinement incidence
      hCinematic hdelta hC_R hq_fiber hmetric htangencyCut hten hhundred
  have hfiberBound : incidence.fiberBound ≤ 4 * (data.mu : ℝ) :=
    incidence.fiberBound_le_four_mu hfiberUpper
  have hincidenceScale_nonneg : 0 ≤ incidenceScale := by
    dsimp only [incidenceScale]
    have h1 : 0 ≤ C_inc := hC_inc_pos.le
    have h2 : 0 ≤ Real.sqrt (delta * (C_R * tRep * DeltaRep / delta) /
        ((selectedIncidenceMetricCut incidence.heavySetup.heavyLogLoss
          (4 * Real.rpow (2 * tRep / DeltaRep) eta) epsilon * tRep / 8) * delta)) :=
      Real.sqrt_nonneg _
    have h3 : 0 ≤ C_inc * Real.sqrt (delta * (C_R * tRep * DeltaRep / delta) /
        ((selectedIncidenceMetricCut incidence.heavySetup.heavyLogLoss
          (4 * Real.rpow (2 * tRep / DeltaRep) eta) epsilon * tRep / 8) * delta)) :=
      mul_nonneg h1 h2
    linarith
  exact hTangencyScale data center hE fineSetup coarseSetup refinement
    incidence.degreeSetup incidence.q_fiber incidence.fiberBound
    incidence.heavySetup incidence.parentSetup
    incidence.retention 4 incidenceScale
    hq_fiber incidence.fiberBound_pos incidence.retention_pos
    (by norm_num) hincidenceScale_nonneg hfiberBound
    incidence.retention_mu hpairs

end Kakeya.Cinematic
