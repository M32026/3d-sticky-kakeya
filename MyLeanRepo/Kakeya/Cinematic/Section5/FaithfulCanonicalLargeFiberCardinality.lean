import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedJointClusterSetupInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedPaperClusterScale
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalActualCardinality
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedIncidenceCanonicalCutoffs

/-!
# Canonical large-fiber selected cardinality

This module assembles the success branch for one ambient bin after the four
global constants have already been fixed.  The cluster remains bin-dependent,
but the parent-measure, parent-tangency, and q-cluster constants do not.
-/

namespace Kakeya.Cinematic

theorem faithful_canonical_large_fiber_cardinality
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K D delta diameter metricExponent tRep DeltaRep C_R₀ : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter metricExponent (metricExponent ^ 2)
        tRep DeltaRep C_R₀)
    (center : C2Function)
    (hE : MeasurableSet E)
    {C_R C_count C_shading C_volume : ℝ}
    (fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume)
    (coarseSetup : AmbientRestrictedCoarseSetupData
      data center hE fineSetup)
    {massExponent : ℝ}
    (refinement : AmbientRestrictedLargeBinRefinementData
      data center hE fineSetup coarseSetup massExponent)
    (incidence : AmbientRestrictedJointIncidenceSetupData
      data center hE fineSetup coarseSetup refinement)
    (C_out C_inc C_positive C_singleton : ℝ)
    (hCluster :
      delta <
          11 *
            ambientRestrictedPaperClusterRadius
              tRep metricExponent incidence.heavySetup.heavyLogLoss
                (4 *
                  Real.rpow (2 * tRep / DeltaRep)
                    (metricExponent ^ 2)) →
        Nonempty
          (AmbientRestrictedJointClusterSetupData
            (D := D) data center hE fineSetup coarseSetup
              refinement incidence))
    (hParentMeasure :
      IsCinematicFamily family K D →
        0 < delta →
          1 ≤ C_R →
            ((2 ^ refinement.parentLevel : ℕ) : ℝ) ≤
              faithfulCanonicalParentArea
                  C_out DeltaRep C_R tRep /
                (((2 : ENNReal) ^ refinement.layer.val *
                  refinement.cutoff).toReal))
    (hParentTangency :
      IsCinematicFamily family K D →
        0 < delta →
          0 < C_R →
            2 ≤ incidence.q_fiber →
              (∀ p : ambientRestrictedSet data center,
                delta /
                    (ambientRestrictedData data center hE).exactT p <
                  selectedIncidenceMetricCut
                    incidence.heavySetup.heavyLogLoss
                    (4 *
                      Real.rpow (2 * tRep / DeltaRep)
                        (metricExponent ^ 2))
                    metricExponent) →
                10 * delta ≤
                  (selectedIncidenceMetricCut
                        incidence.heavySetup.heavyLogLoss
                        (4 *
                          Real.rpow (2 * tRep / DeltaRep)
                            (metricExponent ^ 2))
                        metricExponent *
                      tRep / 8) /
                    (6 * K) →
                  100 * delta ≤
                    C_R * tRep * DeltaRep / delta →
                    (∀ p : E,
                      ((data.assignment.fiber p).card : ℝ) <
                        2 * (data.mu : ℝ)) →
                      ((incidence.heavySetup.M_parent : ℕ) : ℝ) ≤
                        faithfulCanonicalCutoffParentScale
                            delta tRep DeltaRep C_R C_inc
                            incidence.heavySetup.heavyLogLoss
                            metricExponent incidence.retention
                            incidence.heavySetup.degreeLoss *
                          Real.rpow (data.mu : ℝ) (-2) *
                          Real.rpow
                            (2 ^ incidence.heavySetup.supportLevel : ℕ) 2)
    (hQCluster :
      ∀ cluster : AmbientRestrictedJointClusterSetupData
          (D := D) data center hE fineSetup coarseSetup refinement incidence,
        QClusterCoarseCardinalityResult
          incidence.heavySetup.selectedCoarse.card
          (2 ^ incidence.heavySetup.supportLevel)
          cluster.cover.centers.card
          (data.ambientSource.cluster center (3 * tRep)).card
          C_positive C_singleton coarseSetup.tangency cluster.A)
    (hInterpolate : CoarseMultiplicityInterpolationStatement)
    (hK : 1 ≤ K)
    (hfamily : IsCinematicFamily family K D)
    (hdelta : 0 < delta)
    (hhundred : 100 ≤ C_R)
    (hC_out : 0 < C_out)
    (hC_inc : 0 < C_inc)
    (hC_positive : 1 ≤ C_positive)
    (hC_singleton : 1 ≤ C_singleton)
    (hlarge :
      8 * incidence.heavySetup.heavyLogLoss ≤
        (incidence.q_fiber : ℝ))
    (hmetric :
      480 * K * delta ≤
        selectedIncidenceMetricCut
            incidence.heavySetup.heavyLogLoss
            (4 *
              Real.rpow (2 * tRep / DeltaRep)
                (metricExponent ^ 2))
            metricExponent *
          tRep)
    (hfiberUpper :
      ∀ p : E,
        ((data.assignment.fiber p).card : ℝ) <
          2 * (data.mu : ℝ)) :
    ∃ cluster : AmbientRestrictedJointClusterSetupData
        (D := D) data center hE fineSetup coarseSetup refinement incidence,
      AmbientRestrictedSelectedCardinalityResultOfFiber
        refinement.selected.card
        cluster.cover.centers.card
        (data.ambientSource.cluster center (3 * tRep)).card
        (2 ^ incidence.heavySetup.supportLevel)
        data.mu 4
        (Nat.log2 refinement.selected.card + 1)
        incidence.heavySetup.degreeLoss
        (Nat.log2 incidence.heavySetup.ambient.card + 1)
        incidence.retention
        (faithfulCanonicalParentArea C_out DeltaRep C_R tRep /
          (((2 : ENNReal) ^ refinement.layer.val *
            refinement.cutoff).toReal))
        (faithfulCanonicalCutoffParentScale
          delta tRep DeltaRep C_R C_inc
          incidence.heavySetup.heavyLogLoss metricExponent
          incidence.retention incidence.heavySetup.degreeLoss)
        C_positive C_singleton coarseSetup.tangency cluster.A := by
  have hC_R : 0 < C_R := by
    linarith
  have hC_R_one : 1 ≤ C_R := by
    linarith
  have hK_pos : 0 < K := by
    linarith
  have hlogLoss :
      1 ≤ incidence.heavySetup.heavyLogLoss := by
    rw [incidence.heavySetup.heavyLogLoss_eq]
    have hdegree :
        0 < incidence.heavySetup.degreeLoss := by
      rw [incidence.heavySetup.degreeLoss_eq]
      omega
    have hdegree' :
        (1 : ℝ) ≤ incidence.heavySetup.degreeLoss := by
      exact_mod_cast hdegree
    linarith
  have hlogLoss_pos :
      0 < incidence.heavySetup.heavyLogLoss :=
    zero_lt_one.trans_le hlogLoss
  have hDeltaRep : 0 < DeltaRep :=
    hdelta.trans_le data.delta_le_DeltaRep
  have hfiberRatio :
      0 <
        4 *
          Real.rpow (2 * tRep / DeltaRep)
            (metricExponent ^ 2) := by
    exact mul_pos (by norm_num) <|
      Real.rpow_pos_of_pos
        (div_pos (mul_pos (by norm_num) data.tRep_pos) hDeltaRep) _
  have hradius :
      delta <
        11 *
          ambientRestrictedPaperClusterRadius
            tRep metricExponent incidence.heavySetup.heavyLogLoss
              (4 *
                Real.rpow (2 * tRep / DeltaRep)
                  (metricExponent ^ 2)) :=
    delta_lt_eleven_paperClusterRadius_of_metricCut
      K delta tRep metricExponent
      incidence.heavySetup.heavyLogLoss
      (4 *
        Real.rpow (2 * tRep / DeltaRep)
          (metricExponent ^ 2))
      hK hdelta data.tRep_pos data.epsilon_pos hlogLoss_pos
      hfiberRatio hmetric
  rcases hCluster hradius with ⟨cluster⟩
  have hqReal : (2 : ℝ) ≤ incidence.q_fiber := by
    calc
      (2 : ℝ) ≤ 8 * incidence.heavySetup.heavyLogLoss := by
        nlinarith
      _ ≤ incidence.q_fiber := hlarge
  have hq : 2 ≤ incidence.q_fiber := by
    exact_mod_cast hqReal
  have hmetricPointwise :
      ∀ p : ambientRestrictedSet data center,
        delta /
            (ambientRestrictedData data center hE).exactT p <
          selectedIncidenceMetricCut
            incidence.heavySetup.heavyLogLoss
            (4 *
              Real.rpow (2 * tRep / DeltaRep)
                (metricExponent ^ 2))
            metricExponent := by
    intro p
    have hexactT :
        0 <
          (ambientRestrictedData data center hE).exactT p :=
      hdelta.trans_le
        ((ambientRestrictedData data center hE).certificate p).delta_le_t
    exact pointwise_metricCut_of_representative_scale
      K delta tRep
      ((ambientRestrictedData data center hE).exactT p)
      (selectedIncidenceMetricCut
        incidence.heavySetup.heavyLogLoss
        (4 *
          Real.rpow (2 * tRep / DeltaRep)
            (metricExponent ^ 2))
        metricExponent)
      hK hdelta data.tRep_pos hexactT
      ((ambientRestrictedData data center hE).rep_le_eight_exactT p)
      hmetric
  have hten :
      10 * delta ≤
        (selectedIncidenceMetricCut
              incidence.heavySetup.heavyLogLoss
              (4 *
                Real.rpow (2 * tRep / DeltaRep)
                  (metricExponent ^ 2))
              metricExponent *
            tRep / 8) /
          (6 * K) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hK_pos)).2
    nlinarith
  have hdeltaProduct :
      delta * delta ≤ tRep * DeltaRep := by
    exact mul_le_mul
      (data.delta_le_DeltaRep.trans data.DeltaRep_le_tRep)
      data.delta_le_DeltaRep
      hdelta.le data.tRep_pos.le
  have hhundredScale :
      100 * delta ≤ C_R * tRep * DeltaRep / delta := by
    apply (le_div_iff₀ hdelta).2
    calc
      100 * delta * delta =
          100 * (delta * delta) := by ring
      _ ≤ C_R * (delta * delta) := by
        gcongr
      _ ≤ C_R * (tRep * DeltaRep) := by
        gcongr
      _ = C_R * tRep * DeltaRep := by ring
  have hmeasure :=
    hParentMeasure hfamily hdelta hC_R_one
  have hmeasure' :
      ((incidence.heavySetup.M_parent : ℕ) : ℝ) ≤
        faithfulCanonicalParentArea C_out DeltaRep C_R tRep /
          (((2 : ENNReal) ^ refinement.layer.val *
            refinement.cutoff).toReal) := by
    rw [incidence.heavySetup.M_parent_eq]
    exact hmeasure
  have htangency :=
    hParentTangency hfamily hdelta hC_R hq hmetricPointwise
      hten hhundredScale hfiberUpper
  have hQ := hQCluster cluster
  refine ⟨cluster, ?_⟩
  exact faithful_canonical_actual_selected_cardinality
    data center hE fineSetup coarseSetup refinement incidence cluster
    C_out C_inc C_positive C_singleton hInterpolate hdelta hC_R
    hC_out hC_inc hq hC_positive hC_singleton hfiberUpper
    hmeasure' htangency hQ

end Kakeya.Cinematic
