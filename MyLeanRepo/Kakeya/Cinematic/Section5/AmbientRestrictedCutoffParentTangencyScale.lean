import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedAutomaticParentTangencyScale
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedCutoffParentTangencyScaleInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedJointParentPairIncidence
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedIncidenceCanonicalCutoffs

/-!
# Parent tangency scale at the canonical cutoff

The general good-pair route and the tangency-automatic route may return
different incidence constants.  This caller takes their maximum and promotes
both branches to the same cutoff-based parent tangency scale.
-/

namespace Kakeya.Cinematic

lemma cutoff_incidence_quotient_eq
    {delta C_R tRep DeltaRep metricCut tangencyCut : ℝ}
    (hdelta : 0 < delta)
    (htRep : 0 < tRep)
    (hDeltaRep : 0 < DeltaRep)
    (hmetricCut : 0 < metricCut)
    (htangencyCut : 0 < tangencyCut) :
    delta * (C_R * tRep * DeltaRep / delta) /
          ((metricCut * tRep / 8) *
            (tangencyCut * DeltaRep / 2)) =
        16 * C_R / (metricCut * tangencyCut) := by
  field_simp
  ring

lemma cutoff_incidence_scale_eq
    {delta C_R tRep DeltaRep C_inc metricCut tangencyCut : ℝ}
    (hdelta : 0 < delta)
    (htRep : 0 < tRep)
    (hDeltaRep : 0 < DeltaRep)
    (hmetricCut : 0 < metricCut)
    (htangencyCut : 0 < tangencyCut) :
    C_inc *
          Real.sqrt
            (delta * (C_R * tRep * DeltaRep / delta) /
              ((metricCut * tRep / 8) *
                (tangencyCut * DeltaRep / 2))) +
        1 =
      C_inc *
          Real.sqrt
            (16 * C_R / (metricCut * tangencyCut)) +
        1 := by
  rw [cutoff_incidence_quotient_eq
    hdelta htRep hDeltaRep hmetricCut htangencyCut]

lemma automatic_incidence_scale_le_cutoff_incidence_scale
    (delta tRep DeltaRep C_R C_inc metricCut tangencyCut : ℝ)
    (hdelta : 0 < delta)
    (htRep : 0 < tRep)
    (hDeltaRep : 0 < DeltaRep)
    (hC_R : 0 < C_R)
    (hC_inc : 0 < C_inc)
    (hmetricCut : 0 < metricCut)
    (htangencyCut : 0 < tangencyCut)
    (hautomatic : tangencyCut * DeltaRep / 2 ≤ delta) :
    C_inc *
          Real.sqrt
            (delta * (C_R * tRep * DeltaRep / delta) /
              ((metricCut * tRep / 8) * delta)) +
        1 ≤
      C_inc *
          Real.sqrt
            (delta * (C_R * tRep * DeltaRep / delta) /
              ((metricCut * tRep / 8) *
                (tangencyCut * DeltaRep / 2))) +
        1 := by
  have hmetricScale : 0 < metricCut * tRep / 8 := by
    positivity
  have hcutoffScale : 0 < tangencyCut * DeltaRep / 2 := by
    positivity
  have hnumerator :
      0 ≤ delta * (C_R * tRep * DeltaRep / delta) := by
    positivity
  have hquotient :
      delta * (C_R * tRep * DeltaRep / delta) /
            ((metricCut * tRep / 8) * delta) ≤
        delta * (C_R * tRep * DeltaRep / delta) /
            ((metricCut * tRep / 8) *
              (tangencyCut * DeltaRep / 2)) := by
    apply (div_le_div_iff₀
      (mul_pos hmetricScale hdelta)
      (mul_pos hmetricScale hcutoffScale)).2
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hautomatic hmetricScale.le)
      hnumerator
  have hsqrt :
      Real.sqrt
          (delta * (C_R * tRep * DeltaRep / delta) /
            ((metricCut * tRep / 8) * delta)) ≤
        Real.sqrt
          (delta * (C_R * tRep * DeltaRep / delta) /
            ((metricCut * tRep / 8) *
              (tangencyCut * DeltaRep / 2))) :=
    Real.sqrt_le_sqrt hquotient
  gcongr

lemma ambientRestrictedParentTangencyScale_mono_incidenceScale
    (incidenceScale₁ incidenceScale₂ fiberCoefficient : ℝ)
    (degreeLoss : ℕ)
    (heavyLogLoss retention : ℝ)
    (hscale : incidenceScale₁ ≤ incidenceScale₂)
    (hfiberCoefficient : 0 ≤ fiberCoefficient)
    (hretention : 0 < retention) :
    ambientRestrictedParentTangencyScale
          incidenceScale₁ fiberCoefficient degreeLoss
          heavyLogLoss retention ≤
      ambientRestrictedParentTangencyScale
          incidenceScale₂ fiberCoefficient degreeLoss
          heavyLogLoss retention := by
  dsimp only [ambientRestrictedParentTangencyScale]
  have hdegreeLoss : 0 ≤ (degreeLoss : ℝ) := by positivity
  have hheavyLogLoss : 0 ≤ heavyLogLoss ^ 2 := sq_nonneg _
  have hretentionPower :
      0 ≤ Real.rpow retention (-3) :=
    Real.rpow_nonneg hretention.le _
  gcongr

theorem ambient_restricted_cutoff_parent_tangency_scale :
    AmbientRestrictedCutoffParentTangencyScaleStatement := by
  intro hCutoffs hGoodPairs hAutoGoodPairs hPairIncidence
    hJoint hJointAuto hAutomatic hTangencyScale K D hK hD
  rcases hJoint hCutoffs hGoodPairs hPairIncidence K D hK hD with
    ⟨C_general, hC_general_pos, hC_general⟩
  rcases hAutomatic hCutoffs hAutoGoodPairs hPairIncidence
      hJointAuto hTangencyScale K D hK hD with
    ⟨C_automatic, hC_automatic_pos, hC_automatic⟩
  let C_inc : ℝ := max C_general C_automatic
  have hC_general_le : C_general ≤ C_inc := by
    exact le_max_left _ _
  have hC_automatic_le : C_automatic ≤ C_inc := by
    exact le_max_right _ _
  have hC_inc_pos : 0 < C_inc :=
    hC_general_pos.trans_le hC_general_le
  refine' ⟨C_inc, hC_inc_pos, _⟩
  intro family E delta diameter epsilon eta tRep DeltaRep C_R₀
    data center hE C_R C_count C_shading C_volume
    fineSetup coarseSetup massExponent refinement incidence
    hCinematic hdelta hC_R hq_fiber hmetric hten hhundred hfiberUpper
  let fiberRatio : ℝ :=
    4 * Real.rpow (2 * tRep / DeltaRep) eta
  let metricCut : ℝ :=
    selectedIncidenceMetricCut
      incidence.heavySetup.heavyLogLoss fiberRatio epsilon
  let tangencyCut : ℝ :=
    selectedIncidenceTangencyCut
      incidence.heavySetup.heavyLogLoss eta
  let automaticScale : ℝ :=
    C_automatic *
        Real.sqrt
          (delta * (C_R * tRep * DeltaRep / delta) /
            ((metricCut * tRep / 8) * delta)) +
      1
  let cutoffScale : ℝ :=
    C_inc *
        Real.sqrt
          (delta * (C_R * tRep * DeltaRep / delta) /
            ((metricCut * tRep / 8) *
              (tangencyCut * DeltaRep / 2))) +
      1
  have htRep_pos : 0 < tRep := data.tRep_pos
  have hDeltaRep_pos : 0 < DeltaRep := by
    exact hdelta.trans_le data.delta_le_DeltaRep
  have heta_pos : 0 < eta := data.eta_pos
  have hepsilon_pos : 0 < epsilon := data.epsilon_pos
  have hdegreeLoss_pos :
      0 < incidence.heavySetup.degreeLoss := by
    rw [incidence.heavySetup.degreeLoss_eq]
    omega
  have hheavyLogLoss_pos :
      0 < incidence.heavySetup.heavyLogLoss := by
    rw [incidence.heavySetup.heavyLogLoss_eq]
    exact_mod_cast (show
      0 < 4 * incidence.heavySetup.degreeLoss by omega)
  have hfiberRatio_pos : 0 < fiberRatio := by
    dsimp only [fiberRatio]
    exact mul_pos (by norm_num)
      (Real.rpow_pos_of_pos
        (div_pos (mul_pos (by norm_num) htRep_pos) hDeltaRep_pos) _)
  have hmetricCut_pos : 0 < metricCut := by
    dsimp only [metricCut, fiberRatio, selectedIncidenceMetricCut]
    exact mul_pos (by norm_num)
      (Real.rpow_pos_of_pos (by positivity) _)
  have htangencyCut_pos : 0 < tangencyCut := by
    dsimp only [tangencyCut, selectedIncidenceTangencyCut]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hcutoffScale_nonneg : 0 ≤ cutoffScale := by
    dsimp only [cutoffScale]
    positivity
  by_cases hautomatic : tangencyCut * DeltaRep / 2 ≤ delta
  · have hautomaticResult :=
      hC_automatic data center hE fineSetup coarseSetup refinement incidence
        hCinematic hdelta hC_R hq_fiber hmetric hautomatic
        hten hhundred hfiberUpper
    have hautomaticScale_nonneg : 0 ≤ automaticScale := by
      dsimp only [automaticScale]
      positivity
    have hautomatic_to_own_cutoff :
        automaticScale ≤
          C_automatic *
              Real.sqrt
                (delta * (C_R * tRep * DeltaRep / delta) /
                  ((metricCut * tRep / 8) *
                    (tangencyCut * DeltaRep / 2))) +
            1 := by
      exact automatic_incidence_scale_le_cutoff_incidence_scale
        delta tRep DeltaRep C_R C_automatic metricCut tangencyCut
        hdelta htRep_pos hDeltaRep_pos hC_R hC_automatic_pos
        hmetricCut_pos htangencyCut_pos hautomatic
    have hown_cutoff_to_cutoff :
        C_automatic *
              Real.sqrt
                (delta * (C_R * tRep * DeltaRep / delta) /
                  ((metricCut * tRep / 8) *
                    (tangencyCut * DeltaRep / 2))) +
            1 ≤
          cutoffScale := by
      dsimp only [cutoffScale]
      gcongr
    have hscale : automaticScale ≤ cutoffScale :=
      hautomatic_to_own_cutoff.trans hown_cutoff_to_cutoff
    have hparentScale :
        ambientRestrictedParentTangencyScale
              automaticScale 4
              incidence.heavySetup.degreeLoss
              incidence.heavySetup.heavyLogLoss
              incidence.retention ≤
          ambientRestrictedParentTangencyScale
              cutoffScale 4
              incidence.heavySetup.degreeLoss
              incidence.heavySetup.heavyLogLoss
              incidence.retention :=
      ambientRestrictedParentTangencyScale_mono_incidenceScale
        automaticScale cutoffScale 4
        incidence.heavySetup.degreeLoss
        incidence.heavySetup.heavyLogLoss
        incidence.retention hscale (by norm_num)
        incidence.retention_pos
    calc
      ((incidence.heavySetup.M_parent : ℕ) : ℝ) ≤
          ambientRestrictedParentTangencyScale
              automaticScale 4
              incidence.heavySetup.degreeLoss
              incidence.heavySetup.heavyLogLoss
              incidence.retention *
            Real.rpow (data.mu : ℝ) (-2) *
            Real.rpow
              (2 ^ incidence.heavySetup.supportLevel : ℕ) 2 := by
        exact hautomaticResult
      _ ≤
          ambientRestrictedParentTangencyScale
              cutoffScale 4
              incidence.heavySetup.degreeLoss
              incidence.heavySetup.heavyLogLoss
              incidence.retention *
            Real.rpow (data.mu : ℝ) (-2) *
            Real.rpow
              (2 ^ incidence.heavySetup.supportLevel : ℕ) 2 := by
        have hmuRpow_nonneg :
            0 ≤ Real.rpow (data.mu : ℝ) (-2) :=
          Real.rpow_nonneg (by exact_mod_cast data.mu_pos.le) _
        have hsupportRpow_nonneg :
            0 ≤
              Real.rpow
                (2 ^ incidence.heavySetup.supportLevel : ℕ) 2 :=
          Real.rpow_nonneg (by positivity) _
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            hparentScale hmuRpow_nonneg)
          hsupportRpow_nonneg
  · have hgeneral : delta < tangencyCut * DeltaRep / 2 :=
      lt_of_not_ge hautomatic
    have htangencyPointwise :
        ∀ p : ambientRestrictedSet data center,
          delta /
              (ambientRestrictedData data center hE).exactDelta p <
            tangencyCut := by
      intro p
      have hexactDelta :
          0 <
            (ambientRestrictedData data center hE).exactDelta p := by
        exact hdelta.trans_le
          ((ambientRestrictedData data center hE).certificate
            p).delta_le_Delta
      exact pointwise_tangencyCut_of_representative_scale
        delta DeltaRep
        ((ambientRestrictedData data center hE).exactDelta p)
        tangencyCut hexactDelta htangencyCut_pos
        ((ambientRestrictedData data center hE).repDelta_le_two_exactDelta p)
        hgeneral
    have hpairsGeneral :=
      hC_general data center hE fineSetup coarseSetup refinement incidence
        hCinematic hdelta hC_R hq_fiber hmetric htangencyPointwise
        hten hhundred
    let generalScale : ℝ :=
      C_general *
          Real.sqrt
            (delta * (C_R * tRep * DeltaRep / delta) /
              ((metricCut * tRep / 8) *
                (tangencyCut * DeltaRep / 2))) +
        1
    have hgeneralScale_le : generalScale ≤ cutoffScale := by
      dsimp only [generalScale, cutoffScale]
      gcongr
    have hpairs :
        ∀ index :
            Fin
              (selectedCoarseSubfamily coarseSetup.coarseData
                incidence.heavySetup.selectedCoarse).card,
          ((incidence.parentSetup.selectedRectangles index).card : ℝ) *
                (incidence.parentSetup.pairLower index : ℝ) ^ 2 ≤
            3 *
                ((selectedCoarseIncidenceSupport
                  coarseSetup.coarseData
                    incidence.degreeSetup.selectedEdges
                    incidence.heavySetup.selectedCoarse index).card :
                  ℝ) ^ 2 *
              cutoffScale := by
      intro index
      calc
        ((incidence.parentSetup.selectedRectangles index).card : ℝ) *
              (incidence.parentSetup.pairLower index : ℝ) ^ 2 ≤
            3 *
                ((selectedCoarseIncidenceSupport
                  coarseSetup.coarseData
                    incidence.degreeSetup.selectedEdges
                    incidence.heavySetup.selectedCoarse index).card :
                  ℝ) ^ 2 *
              generalScale := by
          exact hpairsGeneral index
        _ ≤
            3 *
                ((selectedCoarseIncidenceSupport
                  coarseSetup.coarseData
                    incidence.degreeSetup.selectedEdges
                    incidence.heavySetup.selectedCoarse index).card :
                  ℝ) ^ 2 *
              cutoffScale := by
          gcongr
    have hfiberBound :
        incidence.fiberBound ≤ 4 * (data.mu : ℝ) :=
      incidence.fiberBound_le_four_mu hfiberUpper
    exact hTangencyScale data center hE fineSetup coarseSetup refinement
      incidence.degreeSetup incidence.q_fiber incidence.fiberBound
      incidence.heavySetup incidence.parentSetup
      incidence.retention 4 cutoffScale
      hq_fiber incidence.fiberBound_pos incidence.retention_pos
      (by norm_num) hcutoffScale_nonneg hfiberBound
      incidence.retention_mu hpairs

end Kakeya.Cinematic
