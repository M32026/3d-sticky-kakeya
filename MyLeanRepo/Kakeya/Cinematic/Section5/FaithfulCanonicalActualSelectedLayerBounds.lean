import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientClusterKatzTaoCardinality
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedJointClusterSetupInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalSelectedLayerBounds

/-!
# Actual selected-layer data at the faithful canonical scales

This module binds the abstract positive and singleton selected-layer
coefficient bounds to the concrete Section 5 structures.  The tangency
exponent is fixed to the square of the metric exponent, as in the paper.
-/

namespace Kakeya.Cinematic

noncomputable local instance faithfulCanonicalActualSelectedLayerDecidableEq :
    DecidableEq C2Function := Classical.decEq _

noncomputable def faithfulCanonicalCutoffParentScale
    (delta tRep DeltaRep C_R C_inc heavyLogLoss metricExponent
      retention : ℝ)
    (degreeLoss : ℕ) : ℝ :=
  ambientRestrictedParentTangencyScale
    (C_inc *
        Real.sqrt
          (delta * (C_R * tRep * DeltaRep / delta) /
            ((selectedIncidenceMetricCut
                    heavyLogLoss
                    (4 *
                      Real.rpow (2 * tRep / DeltaRep)
                        (metricExponent ^ 2))
                    metricExponent *
                  tRep / 8) *
              (selectedIncidenceTangencyCut
                    heavyLogLoss (metricExponent ^ 2) *
                  DeltaRep / 2))) +
      1)
    4 degreeLoss heavyLogLoss retention

noncomputable def faithfulCanonicalParentArea
    (C_out DeltaRep C_R tRep : ℝ) : ℝ :=
  4 * C_out ^ 2 * DeltaRep *
    Real.sqrt (DeltaRep / (C_R * tRep))

noncomputable def faithfulCanonicalAmbientCardUpper
    (C_KT tRep delta : ℝ) : ℝ :=
  C_KT * (3 * tRep / delta)

noncomputable def faithfulCanonicalRetentionInverseConstant
    (diameter T metricExponent : ℝ) : ℝ :=
  Real.rpow (8 * diameter) metricExponent *
    Real.rpow (2 * T) (metricExponent ^ 2)

lemma ambientRestrictedParentTangencyScale_nonneg
    (incidenceScale fiberCoefficient heavyLogLoss retention : ℝ)
    (degreeLoss : ℕ)
    (hincidenceScale : 0 ≤ incidenceScale)
    (hfiberCoefficient : 0 ≤ fiberCoefficient)
    (hretention : 0 ≤ retention) :
    0 ≤
      ambientRestrictedParentTangencyScale
        incidenceScale fiberCoefficient degreeLoss heavyLogLoss
          retention := by
  dsimp only [ambientRestrictedParentTangencyScale]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (show (0 : ℝ) ≤ 5184 by norm_num)
            (mul_nonneg (by norm_num) hincidenceScale))
          hfiberCoefficient)
        (mul_nonneg (by norm_num) (Nat.cast_nonneg degreeLoss)))
      (sq_nonneg heavyLogLoss))
    (Real.rpow_nonneg hretention _)

lemma AmbientRestrictedLargeBinRefinementData.selected_card_le_fine_card
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    {data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀}
    {center : C2Function}
    {hE : MeasurableSet E}
    {C_R C_count C_shading C_volume : ℝ}
    {fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume}
    {coarseSetup : AmbientRestrictedCoarseSetupData
      data center hE fineSetup}
    {massExponent : ℝ}
    (refinement : AmbientRestrictedLargeBinRefinementData
      data center hE fineSetup coarseSetup massExponent) :
    refinement.selected.card ≤ fineSetup.fine.card := by
  calc
    refinement.selected.card ≤
        Fintype.card (Fin fineSetup.fine.card) :=
      Finset.card_le_univ _
    _ = fineSetup.fine.card := by simp

lemma RetainedHeavySupportSetupData.ambient_card_eq_cluster_card
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    {data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀}
    {center : C2Function}
    {hE : MeasurableSet E}
    {C_R C_count C_shading C_volume : ℝ}
    {fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume}
    {coarseSetup : AmbientRestrictedCoarseSetupData
      data center hE fineSetup}
    {massExponent : ℝ}
    {refinement : AmbientRestrictedLargeBinRefinementData
      data center hE fineSetup coarseSetup massExponent}
    {degreeSetup : RetainedIncidenceDegreeSetupData
      data center hE fineSetup coarseSetup refinement}
    {q_fiber : ℕ}
    {fiberBound : ℝ}
    (heavySetup : RetainedHeavySupportSetupData
      data center hE fineSetup coarseSetup refinement
        degreeSetup q_fiber fiberBound) :
    heavySetup.ambient.card =
      (data.ambientSource.cluster center (3 * tRep)).card := by
  rw [heavySetup.ambient_eq]
  exact
    (Set.ncard_eq_toFinset_card
      (data.ambientSource.cluster center (3 * tRep)).carrier
      (data.ambientSource.cluster center (3 * tRep)).finite).symm

lemma RetainedHeavySupportSetupData.ambient_card_le_source_card
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    {data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀}
    {center : C2Function}
    {hE : MeasurableSet E}
    {C_R C_count C_shading C_volume : ℝ}
    {fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume}
    {coarseSetup : AmbientRestrictedCoarseSetupData
      data center hE fineSetup}
    {massExponent : ℝ}
    {refinement : AmbientRestrictedLargeBinRefinementData
      data center hE fineSetup coarseSetup massExponent}
    {degreeSetup : RetainedIncidenceDegreeSetupData
      data center hE fineSetup coarseSetup refinement}
    {q_fiber : ℕ}
    {fiberBound : ℝ}
    (heavySetup : RetainedHeavySupportSetupData
      data center hE fineSetup coarseSetup refinement
        degreeSetup q_fiber fiberBound) :
    heavySetup.ambient.card ≤ data.ambientSource.card := by
  rw [heavySetup.ambient_card_eq_cluster_card]
  exact cluster_card_le data.ambientSource center (3 * tRep)

lemma RetainedHeavySupportSetupData.ambient_card_pos
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    {data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀}
    {center : C2Function}
    {hE : MeasurableSet E}
    {C_R C_count C_shading C_volume : ℝ}
    {fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume}
    {coarseSetup : AmbientRestrictedCoarseSetupData
      data center hE fineSetup}
    {massExponent : ℝ}
    {refinement : AmbientRestrictedLargeBinRefinementData
      data center hE fineSetup coarseSetup massExponent}
    {degreeSetup : RetainedIncidenceDegreeSetupData
      data center hE fineSetup coarseSetup refinement}
    {q_fiber : ℕ}
    {fiberBound : ℝ}
    (heavySetup : RetainedHeavySupportSetupData
      data center hE fineSetup coarseSetup refinement
        degreeSetup q_fiber fiberBound) :
    0 < heavySetup.ambient.card := by
  rcases heavySetup.selectedCoarse_nonempty with ⟨coarse, hcoarse⟩
  have hsupportPos :
      0 <
        (incidenceFunctionSupport degreeSetup.selectedEdges
          coarseSetup.coarseData.parent coarse).card := by
    have hrange := heavySetup.support_range coarse hcoarse
    have hpower :
        0 < (2 : ℕ) ^ heavySetup.supportLevel := by
      positivity
    exact hpower.trans_le hrange.1
  rcases Finset.card_pos.mp hsupportPos with ⟨function, hfunction⟩
  exact Finset.card_pos.mpr
    ⟨function,
      heavySetup.support_ambient coarse
        (heavySetup.selectedCoarse_subset hcoarse) hfunction⟩

lemma RetainedHeavySupportSetupData.support_power_le_ambient_card
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    {data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀}
    {center : C2Function}
    {hE : MeasurableSet E}
    {C_R C_count C_shading C_volume : ℝ}
    {fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume}
    {coarseSetup : AmbientRestrictedCoarseSetupData
      data center hE fineSetup}
    {massExponent : ℝ}
    {refinement : AmbientRestrictedLargeBinRefinementData
      data center hE fineSetup coarseSetup massExponent}
    {degreeSetup : RetainedIncidenceDegreeSetupData
      data center hE fineSetup coarseSetup refinement}
    {q_fiber : ℕ}
    {fiberBound : ℝ}
    (heavySetup : RetainedHeavySupportSetupData
      data center hE fineSetup coarseSetup refinement
        degreeSetup q_fiber fiberBound) :
    2 ^ heavySetup.supportLevel ≤ heavySetup.ambient.card := by
  calc
    2 ^ heavySetup.supportLevel ≤
        2 ^ Nat.log2 heavySetup.ambient.card := by
      exact Nat.pow_le_pow_right (by norm_num)
        heavySetup.supportLevel_bound
    _ ≤ heavySetup.ambient.card := by
      exact (Nat.le_log2 heavySetup.ambient_card_pos.ne').mp le_rfl

lemma faithful_canonical_positive_log_tail_nonneg
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K D delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    {data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀}
    {center : C2Function}
    {hE : MeasurableSet E}
    {C_R C_count C_shading C_volume : ℝ}
    {fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume}
    {coarseSetup : AmbientRestrictedCoarseSetupData
      data center hE fineSetup}
    {massExponent : ℝ}
    {refinement : AmbientRestrictedLargeBinRefinementData
      data center hE fineSetup coarseSetup massExponent}
    {incidence : AmbientRestrictedJointIncidenceSetupData
      data center hE fineSetup coarseSetup refinement}
    (cluster : AmbientRestrictedJointClusterSetupData
      (D := D) data center hE fineSetup coarseSetup refinement incidence) :
    0 ≤
      Real.log
        (8 * (cluster.cover.centers.card : ℝ) *
            ((data.ambientSource.cluster
              center (3 * tRep)).card : ℝ) /
          (2 ^ incidence.heavySetup.supportLevel : ℕ)) := by
  have hcenters : 1 ≤ (cluster.cover.centers.card : ℝ) := by
    exact_mod_cast
      (Finset.one_le_card.mpr cluster.cover.centers_nonempty)
  have hsupportPos :
      0 < ((2 ^ incidence.heavySetup.supportLevel : ℕ) : ℝ) := by
    positivity
  have hsupport :
      ((2 ^ incidence.heavySetup.supportLevel : ℕ) : ℝ) ≤
        ((data.ambientSource.cluster
          center (3 * tRep)).card : ℝ) := by
    rw [← incidence.heavySetup.ambient_card_eq_cluster_card]
    exact_mod_cast incidence.heavySetup.support_power_le_ambient_card
  apply Real.log_nonneg
  apply (le_div_iff₀ hsupportPos).2
  have hnumerator :
      ((2 ^ incidence.heavySetup.supportLevel : ℕ) : ℝ) ≤
        8 * (cluster.cover.centers.card : ℝ) *
          ((data.ambientSource.cluster
            center (3 * tRep)).card : ℝ) := by
    calc
      ((2 ^ incidence.heavySetup.supportLevel : ℕ) : ℝ) ≤
          ((data.ambientSource.cluster
            center (3 * tRep)).card : ℝ) := hsupport
      _ ≤
          8 * (cluster.cover.centers.card : ℝ) *
            ((data.ambientSource.cluster
              center (3 * tRep)).card : ℝ) := by
        have hfactor :
            1 ≤ 8 * (cluster.cover.centers.card : ℝ) := by
          nlinarith
        have hambientNonneg :
            0 ≤
              ((data.ambientSource.cluster
                center (3 * tRep)).card : ℝ) := by
          positivity
        have hscaled :
            1 *
                ((data.ambientSource.cluster
                  center (3 * tRep)).card : ℝ) ≤
              (8 * (cluster.cover.centers.card : ℝ)) *
                ((data.ambientSource.cluster
                  center (3 * tRep)).card : ℝ) :=
          mul_le_mul_of_nonneg_right hfactor hambientNonneg
        simpa only [one_mul] using hscaled
  simpa only [one_mul] using hnumerator

lemma faithful_canonical_singleton_log_tail_nonneg
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    {data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀}
    {center : C2Function}
    {hE : MeasurableSet E}
    {C_R C_count C_shading C_volume : ℝ}
    {fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume}
    {coarseSetup : AmbientRestrictedCoarseSetupData
      data center hE fineSetup}
    {massExponent : ℝ}
    {refinement : AmbientRestrictedLargeBinRefinementData
      data center hE fineSetup coarseSetup massExponent}
    {degreeSetup : RetainedIncidenceDegreeSetupData
      data center hE fineSetup coarseSetup refinement}
    {q_fiber : ℕ}
    {fiberBound : ℝ}
    (heavySetup : RetainedHeavySupportSetupData
      data center hE fineSetup coarseSetup refinement
        degreeSetup q_fiber fiberBound) :
    0 ≤
      Real.log
        (2 *
          ((data.ambientSource.cluster
            center (3 * tRep)).card : ℝ)) := by
  have hambient :
      1 ≤
        ((data.ambientSource.cluster
          center (3 * tRep)).card : ℝ) := by
    rw [← heavySetup.ambient_card_eq_cluster_card]
    exact_mod_cast heavySetup.ambient_card_pos
  exact Real.log_nonneg (by nlinarith)

lemma RetainedHeavySupportSetupData.one_le_heavyLogLoss
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    {data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀}
    {center : C2Function}
    {hE : MeasurableSet E}
    {C_R C_count C_shading C_volume : ℝ}
    {fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume}
    {coarseSetup : AmbientRestrictedCoarseSetupData
      data center hE fineSetup}
    {massExponent : ℝ}
    {refinement : AmbientRestrictedLargeBinRefinementData
      data center hE fineSetup coarseSetup massExponent}
    {degreeSetup : RetainedIncidenceDegreeSetupData
      data center hE fineSetup coarseSetup refinement}
    {q_fiber : ℕ}
    {fiberBound : ℝ}
    (heavySetup : RetainedHeavySupportSetupData
      data center hE fineSetup coarseSetup refinement
        degreeSetup q_fiber fiberBound) :
    1 ≤ heavySetup.heavyLogLoss := by
  rw [heavySetup.heavyLogLoss_eq, heavySetup.degreeLoss_eq]
  have hdegree :
      1 ≤ Nat.log2 (Fintype.card (Fin fineSetup.fine.card)) + 1 := by
    omega
  exact_mod_cast
    (show 1 ≤ 4 *
        (Nat.log2 (Fintype.card (Fin fineSetup.fine.card)) + 1) by
      omega)

theorem faithful_canonical_actual_selected_layer_coefficients_le
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
    (cluster : AmbientRestrictedJointClusterSetupData
      (D := D) data center hE fineSetup coarseSetup refinement incidence)
    (T C_KT C_out C_inc outerLoss positiveLogTail singletonLogTail
      C_positive C_singleton : ℝ)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hdiameter : 0 < diameter)
    (hT : 0 < T)
    (htT : tRep ≤ T)
    (hC_R : 0 < C_R)
    (hC_shading : 0 < C_shading)
    (hC_KT : 0 < C_KT)
    (hC_out : 0 < C_out)
    (hC_inc : 0 < C_inc)
    (hD : 1 ≤ D)
    (hmetric : 0 < metricExponent)
    (hC_positive : 0 ≤ C_positive)
    (hC_singleton : 0 ≤ C_singleton)
    (houterLoss : 0 ≤ outerLoss)
    (hpositiveLogTail : 0 ≤ positiveLogTail)
    (hsingletonLogTail : 0 ≤ singletonLogTail)
    (hlogLoss :
      incidence.heavySetup.heavyLogLoss ≤
        Real.rpow delta (-(metricExponent ^ 3)))
    (hpositiveOrdinary :
      faithfulCanonicalOrdinaryDyadicLoss
          outerLoss positiveLogTail refinement.layerCount
          data.ambientSource.card fineSetup.fine.card
          refinement.selected.card ≤
        Real.rpow delta
          (-faithfulCanonicalOrdinaryLoss metricExponent))
    (hsingletonOrdinary :
      faithfulCanonicalOrdinaryDyadicLoss
          outerLoss singletonLogTail refinement.layerCount
          data.ambientSource.card fineSetup.fine.card
          refinement.selected.card ≤
        Real.rpow delta
          (-faithfulCanonicalOrdinaryLoss metricExponent)) :
    let parentScale :=
      faithfulCanonicalCutoffParentScale
        delta tRep DeltaRep C_R C_inc
        incidence.heavySetup.heavyLogLoss metricExponent
        incidence.retention incidence.heavySetup.degreeLoss
    let parentArea :=
      faithfulCanonicalParentArea C_out DeltaRep C_R tRep
    let cardUpper :=
      faithfulCanonicalAmbientCardUpper C_KT tRep delta
    outerLoss *
        ambientRestrictedLayerLinearizedLocalCoefficient
          (ambientRestrictedPositiveLayerBaseCoefficientOfFiber
            4
            (((Nat.log2 refinement.selected.card + 1 : ℕ) : ℝ))
            (incidence.heavySetup.degreeLoss : ℝ)
            (((Nat.log2 incidence.heavySetup.ambient.card + 1 : ℕ) : ℝ))
            incidence.retention parentScale cluster.cover.centers.card
            C_positive coarseSetup.tangency cluster.A data.mu)
          (8 * (cluster.cover.centers.card : ℝ))
          cardUpper positiveLogTail
          (((2 * refinement.massFactor : ℕ) : ℝ))
          parentArea
          (ambientRestrictedSelectedFineGeometricArea
            C_shading delta C_R tRep DeltaRep) ≤
      (4 *
          faithfulCanonicalPositiveBranchConstant
            C_positive coarseSetup.tangency) *
          faithfulCanonicalFinalCoefficientConstant
            (faithfulCanonicalParentScaleConstant
              diameter T C_R C_inc metricExponent)
            (faithfulCanonicalRetentionInverseConstant
              diameter T metricExponent)
            (faithfulCanonicalClusterConstant
              T C_R metricExponent)
            D C_positive (Real.log D / Real.log 2) *
          Real.rpow delta
            (-(faithfulCanonicalStructuredScaleLoss
                  (C_positive +
                    (7 / 2 : ℝ) * (Real.log D / Real.log 2))
                  metricExponent +
                faithfulCanonicalOrdinaryLoss metricExponent)) *
          ((Real.sqrt (3 * C_KT) *
              Real.rpow (4 * C_out ^ 2) (1 / 4 : ℝ) *
              Real.rpow
                (2 * C_shading * Real.sqrt C_shading)
                (3 / 4 : ℝ) /
              Real.sqrt C_R) * delta) *
          Real.rpow (data.mu : ℝ) (-3 / 2 : ℝ) ∧
      outerLoss *
          ambientRestrictedLayerLinearizedLocalCoefficient
            (ambientRestrictedSingletonLayerBaseCoefficientOfFiber
              4
              (((Nat.log2 refinement.selected.card + 1 : ℕ) : ℝ))
              (incidence.heavySetup.degreeLoss : ℝ)
              (((Nat.log2 incidence.heavySetup.ambient.card + 1 : ℕ) : ℝ))
              incidence.retention parentScale cluster.cover.centers.card
              C_singleton coarseSetup.tangency cluster.A data.mu)
            2 cardUpper singletonLogTail
            (((2 * refinement.massFactor : ℕ) : ℝ))
            parentArea
            (ambientRestrictedSelectedFineGeometricArea
              C_shading delta C_R tRep DeltaRep) ≤
        (4 *
            faithfulCanonicalSingletonBranchConstant
              C_singleton coarseSetup.tangency) *
            faithfulCanonicalFinalCoefficientConstant
              (faithfulCanonicalParentScaleConstant
                diameter T C_R C_inc metricExponent)
              (faithfulCanonicalRetentionInverseConstant
                diameter T metricExponent)
              (faithfulCanonicalClusterConstant
                T C_R metricExponent)
              D C_singleton (Real.log D / Real.log 2) *
            Real.rpow delta
              (-(faithfulCanonicalStructuredScaleLoss
                    (C_singleton +
                      (7 / 2 : ℝ) * (Real.log D / Real.log 2))
                    metricExponent +
                  faithfulCanonicalOrdinaryLoss metricExponent)) *
            ((Real.sqrt (3 * C_KT) *
                Real.rpow (4 * C_out ^ 2) (1 / 4 : ℝ) *
                Real.rpow
                  (2 * C_shading * Real.sqrt C_shading)
                  (3 / 4 : ℝ) /
                Real.sqrt C_R) * delta) *
            Real.rpow (data.mu : ℝ) (-3 / 2 : ℝ) := by
  dsimp only
  let parentScale :=
    faithfulCanonicalCutoffParentScale
      delta tRep DeltaRep C_R C_inc
      incidence.heavySetup.heavyLogLoss metricExponent
      incidence.retention incidence.heavySetup.degreeLoss
  let parentArea :=
    faithfulCanonicalParentArea C_out DeltaRep C_R tRep
  let cardUpper :=
    faithfulCanonicalAmbientCardUpper C_KT tRep delta
  let parentConstant :=
    faithfulCanonicalParentScaleConstant
      diameter T C_R C_inc metricExponent
  let retentionConstant :=
    faithfulCanonicalRetentionInverseConstant
      diameter T metricExponent
  let clusterConstant :=
    faithfulCanonicalClusterConstant T C_R metricExponent
  let coverExponent := Real.log D / Real.log 2
  have hDelta : 0 < DeltaRep :=
    hdelta.trans_le data.delta_le_DeltaRep
  have hheavy : 0 < incidence.heavySetup.heavyLogLoss :=
    lt_of_lt_of_le zero_lt_one
      incidence.heavySetup.one_le_heavyLogLoss
  have hdegree :
      (incidence.heavySetup.degreeLoss : ℝ) ≤
        incidence.heavySetup.heavyLogLoss := by
    rw [incidence.heavySetup.heavyLogLoss_eq]
    have hdegreeNonneg :
        0 ≤ (incidence.heavySetup.degreeLoss : ℝ) := by
      positivity
    linarith
  have hparentScale : 0 ≤ parentScale := by
    have hincidenceScale :
        0 ≤
          C_inc *
              Real.sqrt
                (delta * (C_R * tRep * DeltaRep / delta) /
                  ((selectedIncidenceMetricCut
                          incidence.heavySetup.heavyLogLoss
                          (4 *
                            Real.rpow (2 * tRep / DeltaRep)
                              (metricExponent ^ 2))
                          metricExponent *
                        tRep / 8) *
                    (selectedIncidenceTangencyCut
                          incidence.heavySetup.heavyLogLoss
                          (metricExponent ^ 2) *
                        DeltaRep / 2))) +
            1 := by
      exact add_nonneg
        (mul_nonneg hC_inc.le (Real.sqrt_nonneg _))
        (by norm_num)
    dsimp only [parentScale, faithfulCanonicalCutoffParentScale]
    exact ambientRestrictedParentTangencyScale_nonneg
      _ 4 incidence.heavySetup.heavyLogLoss incidence.retention
      incidence.heavySetup.degreeLoss hincidenceScale
      (by norm_num) incidence.retention_pos.le
  have hparentArea : 0 ≤ parentArea := by
    dsimp only [parentArea, faithfulCanonicalParentArea]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg C_out))
        hDelta.le)
      (Real.sqrt_nonneg _)
  have hcardUpper : 0 ≤ cardUpper := by
    dsimp only [cardUpper, faithfulCanonicalAmbientCardUpper]
    exact mul_nonneg hC_KT.le <|
      div_nonneg
        (mul_nonneg (by norm_num) data.tRep_pos.le)
        hdelta.le
  have hparentConstant : 0 < parentConstant := by
    have hincidenceConstant :
        0 <
          faithfulCanonicalIncidenceConstant
            T C_R C_inc metricExponent := by
      dsimp only [faithfulCanonicalIncidenceConstant]
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg hC_inc.le (Real.sqrt_nonneg _))
        zero_lt_one
    have hretentionScaleConstant :
        0 <
          faithfulCanonicalRetentionConstant
            diameter T metricExponent := by
      dsimp only [faithfulCanonicalRetentionConstant]
      exact mul_pos
        (Real.rpow_pos_of_pos
          (mul_pos (by norm_num) hdiameter) _)
        (Real.rpow_pos_of_pos
          (mul_pos (by norm_num) hT) _)
    dsimp only [parentConstant, faithfulCanonicalParentScaleConstant]
    exact mul_pos
      (mul_pos (by norm_num) hincidenceConstant)
      hretentionScaleConstant
  have hretentionConstant : 0 < retentionConstant := by
    dsimp only [retentionConstant,
      faithfulCanonicalRetentionInverseConstant]
    exact mul_pos
      (Real.rpow_pos_of_pos
        (mul_pos (by norm_num) hdiameter) _)
      (Real.rpow_pos_of_pos
        (mul_pos (by norm_num) hT) _)
  have hclusterConstant : 0 < clusterConstant := by
    dsimp only [clusterConstant, faithfulCanonicalClusterConstant]
    exact mul_pos
      (mul_pos (by norm_num) hC_R)
      (Real.rpow_pos_of_pos
        (mul_pos (by norm_num)
          (Real.rpow_pos_of_pos
            (mul_pos (by norm_num) hT) _)) _)
  have hD_pos : 0 < D := zero_lt_one.trans_le hD
  have hcoverExponent : 0 ≤ coverExponent := by
    dsimp only [coverExponent]
    exact div_nonneg (Real.log_nonneg hD) (Real.log_nonneg (by norm_num))
  have hparentBound :
      parentScale ≤ parentConstant *
        Real.rpow delta
          (-faithfulCanonicalParentScaleLoss metricExponent) := by
    dsimp only [parentScale, parentConstant,
      faithfulCanonicalCutoffParentScale]
    rw [incidence.retention_eq]
    exact canonical_parent_tangency_scale_le
      delta tRep DeltaRep diameter T C_R C_inc
      incidence.heavySetup.heavyLogLoss metricExponent
      incidence.heavySetup.degreeLoss hdelta hdeltaOne hDelta
      hdiameter hT hC_R hC_inc hheavy hmetric
      data.delta_le_DeltaRep data.DeltaRep_le_tRep htT
      hdegree hlogLoss
  have hretentionBound :
      Real.rpow incidence.retention (-1) ≤
        retentionConstant *
          Real.rpow delta
            (-(metricExponent + metricExponent ^ 2)) := by
    dsimp only [retentionConstant,
      faithfulCanonicalRetentionInverseConstant]
    rw [incidence.retention_eq]
    exact canonical_retention_inv_le
      delta tRep DeltaRep diameter T metricExponent
      hdelta hdiameter hT hmetric.le data.delta_le_DeltaRep
      data.DeltaRep_le_tRep htT
  have hA_bound :
      cluster.A ≤ clusterConstant *
        Real.rpow delta
          (-(metricExponent + metricExponent ^ 2)) := by
    dsimp only [clusterConstant]
    rw [cluster.A_eq, cluster.fiberRatio_eq]
    exact canonical_paper_cluster_parameter_le
      delta tRep DeltaRep T C_R
      incidence.heavySetup.heavyLogLoss metricExponent
      hdelta hDelta hT hC_R hheavy hmetric
      data.delta_le_DeltaRep data.DeltaRep_le_tRep htT hlogLoss
  have hcenters :
      (cluster.cover.centers.card : ℝ) ≤
        D * Real.rpow (48 * cluster.A) coverExponent := by
    dsimp only [coverExponent]
    exact cluster.cover.centers_card_le_paper_parameter
      cluster.radius_pos cluster.A_ge_one cluster.scale_identity
  have hcentersPos : 0 < cluster.cover.centers.card :=
    cluster.cover.centers_nonempty.card_pos
  have hdegreeLoss :
      incidence.heavySetup.degreeLoss =
        Nat.log2 fineSetup.fine.card + 1 := by
    simpa using incidence.heavySetup.degreeLoss_eq
  have hsupportCard :
      incidence.heavySetup.ambient.card ≤
        data.ambientSource.card :=
    incidence.heavySetup.ambient_card_le_source_card
  have hparentAreaBound :
      parentArea ≤
        (4 * C_out ^ 2) * DeltaRep *
          Real.sqrt (DeltaRep / (C_R * tRep)) := by
    dsimp only [parentArea, faithfulCanonicalParentArea]
    rfl
  have hcardUpperBound :
      cardUpper ≤ C_KT * 3 * tRep / delta := by
    dsimp only [cardUpper, faithfulCanonicalAmbientCardUpper]
    ring_nf
    exact le_rfl
  have htangency : 0 ≤ coarseSetup.tangency := by
    linarith [coarseSetup.tangency_ge_five]
  constructor
  · have hbase :=
      positive_layer_canonical_local_coefficient_le
        delta tRep DeltaRep C_R C_shading C_KT (4 * C_out ^ 2)
        outerLoss 1 positiveLogTail parentScale
        incidence.retention cluster.A parentConstant retentionConstant
        clusterConstant D metricExponent coverExponent C_positive
        coarseSetup.tangency parentArea cardUpper
        refinement.layerCount refinement.fiberLoss refinement.massFactor
        refinement.selected.card incidence.heavySetup.degreeLoss
        incidence.heavySetup.ambient.card data.ambientSource.card
        fineSetup.fine.card cluster.cover.centers.card data.mu
        hdelta data.tRep_pos hDelta hC_R hC_shading hC_KT
        (by positivity) hparentArea hcardUpper hparentAreaBound
        hcardUpperBound hparentScale incidence.retention_pos
        (by linarith [cluster.A_ge_one]) hparentConstant
        hretentionConstant hclusterConstant hD_pos hcoverExponent
        hC_positive htangency hcentersPos hparentBound hretentionBound
        hA_bound hcenters houterLoss (by norm_num) hpositiveLogTail
        refinement.fiberLoss_eq refinement.massFactor_eq hdegreeLoss
        hsupportCard hpositiveOrdinary
    calc
      outerLoss *
          ambientRestrictedLayerLinearizedLocalCoefficient
            (ambientRestrictedPositiveLayerBaseCoefficientOfFiber
              4
              (((Nat.log2 refinement.selected.card + 1 : ℕ) : ℝ))
              (incidence.heavySetup.degreeLoss : ℝ)
              (((Nat.log2 incidence.heavySetup.ambient.card + 1 : ℕ) : ℝ))
              incidence.retention parentScale cluster.cover.centers.card
              C_positive coarseSetup.tangency cluster.A data.mu)
            (8 * (cluster.cover.centers.card : ℝ))
            cardUpper positiveLogTail
            (((2 * refinement.massFactor : ℕ) : ℝ))
            parentArea
            (ambientRestrictedSelectedFineGeometricArea
              C_shading delta C_R tRep DeltaRep) =
          4 *
            (outerLoss *
              ambientRestrictedLayerLinearizedLocalCoefficient
                (ambientRestrictedPositiveLayerBaseCoefficientOfFiber
                  1
                  (((Nat.log2 refinement.selected.card + 1 : ℕ) : ℝ))
                  (incidence.heavySetup.degreeLoss : ℝ)
                  (((Nat.log2 incidence.heavySetup.ambient.card + 1 : ℕ) : ℝ))
                  incidence.retention parentScale cluster.cover.centers.card
                  C_positive coarseSetup.tangency cluster.A data.mu)
                (8 * (cluster.cover.centers.card : ℝ))
                cardUpper positiveLogTail
                (((2 * refinement.massFactor : ℕ) : ℝ))
                parentArea
                (ambientRestrictedSelectedFineGeometricArea
                  C_shading delta C_R tRep DeltaRep)) := by
            dsimp only [ambientRestrictedLayerLinearizedLocalCoefficient,
              ambientRestrictedPositiveLayerBaseCoefficientOfFiber]
            ring
      _ ≤
          4 *
            (faithfulCanonicalPositiveBranchConstant
                C_positive coarseSetup.tangency *
              faithfulCanonicalFinalCoefficientConstant
                parentConstant retentionConstant clusterConstant D
                C_positive coverExponent *
              Real.rpow delta
                (-(faithfulCanonicalStructuredScaleLoss
                      (C_positive +
                        (7 / 2 : ℝ) * coverExponent)
                      metricExponent +
                    faithfulCanonicalOrdinaryLoss metricExponent)) *
              ((Real.sqrt (3 * C_KT) *
                  Real.rpow (4 * C_out ^ 2) (1 / 4 : ℝ) *
                  Real.rpow
                    (2 * C_shading * Real.sqrt C_shading)
                    (3 / 4 : ℝ) /
                  Real.sqrt C_R) * delta) *
              Real.rpow (data.mu : ℝ) (-3 / 2 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ =
          (4 *
              faithfulCanonicalPositiveBranchConstant
                C_positive coarseSetup.tangency) *
            faithfulCanonicalFinalCoefficientConstant
              parentConstant retentionConstant clusterConstant D
              C_positive coverExponent *
            Real.rpow delta
              (-(faithfulCanonicalStructuredScaleLoss
                    (C_positive +
                      (7 / 2 : ℝ) * coverExponent)
                    metricExponent +
                  faithfulCanonicalOrdinaryLoss metricExponent)) *
            ((Real.sqrt (3 * C_KT) *
                Real.rpow (4 * C_out ^ 2) (1 / 4 : ℝ) *
                Real.rpow
                  (2 * C_shading * Real.sqrt C_shading)
                  (3 / 4 : ℝ) /
                Real.sqrt C_R) * delta) *
            Real.rpow (data.mu : ℝ) (-3 / 2 : ℝ) := by ring
  · have hbase :=
      singleton_layer_canonical_local_coefficient_le
        delta tRep DeltaRep C_R C_shading C_KT (4 * C_out ^ 2)
        outerLoss 1 singletonLogTail parentScale
        incidence.retention cluster.A parentConstant retentionConstant
        clusterConstant D metricExponent coverExponent C_singleton
        coarseSetup.tangency parentArea cardUpper
        refinement.layerCount refinement.fiberLoss refinement.massFactor
        refinement.selected.card incidence.heavySetup.degreeLoss
        incidence.heavySetup.ambient.card data.ambientSource.card
        fineSetup.fine.card cluster.cover.centers.card data.mu
        hdelta data.tRep_pos hDelta hC_R hC_shading hC_KT
        (by positivity) hparentArea hcardUpper hparentAreaBound
        hcardUpperBound hparentScale incidence.retention_pos
        (by linarith [cluster.A_ge_one]) hparentConstant
        hretentionConstant hclusterConstant hD_pos hcoverExponent
        hC_singleton htangency hcentersPos hparentBound hretentionBound
        hA_bound hcenters houterLoss (by norm_num) hsingletonLogTail
        refinement.fiberLoss_eq refinement.massFactor_eq hdegreeLoss
        hsupportCard hsingletonOrdinary
    calc
      outerLoss *
          ambientRestrictedLayerLinearizedLocalCoefficient
            (ambientRestrictedSingletonLayerBaseCoefficientOfFiber
              4
              (((Nat.log2 refinement.selected.card + 1 : ℕ) : ℝ))
              (incidence.heavySetup.degreeLoss : ℝ)
              (((Nat.log2 incidence.heavySetup.ambient.card + 1 : ℕ) : ℝ))
              incidence.retention parentScale cluster.cover.centers.card
              C_singleton coarseSetup.tangency cluster.A data.mu)
            2 cardUpper singletonLogTail
            (((2 * refinement.massFactor : ℕ) : ℝ))
            parentArea
            (ambientRestrictedSelectedFineGeometricArea
              C_shading delta C_R tRep DeltaRep) =
          4 *
            (outerLoss *
              ambientRestrictedLayerLinearizedLocalCoefficient
                (ambientRestrictedSingletonLayerBaseCoefficientOfFiber
                  1
                  (((Nat.log2 refinement.selected.card + 1 : ℕ) : ℝ))
                  (incidence.heavySetup.degreeLoss : ℝ)
                  (((Nat.log2 incidence.heavySetup.ambient.card + 1 : ℕ) : ℝ))
                  incidence.retention parentScale cluster.cover.centers.card
                  C_singleton coarseSetup.tangency cluster.A data.mu)
                2 cardUpper singletonLogTail
                (((2 * refinement.massFactor : ℕ) : ℝ))
                parentArea
                (ambientRestrictedSelectedFineGeometricArea
                  C_shading delta C_R tRep DeltaRep)) := by
            dsimp only [ambientRestrictedLayerLinearizedLocalCoefficient,
              ambientRestrictedSingletonLayerBaseCoefficientOfFiber]
            ring
      _ ≤
          4 *
            (faithfulCanonicalSingletonBranchConstant
                C_singleton coarseSetup.tangency *
              faithfulCanonicalFinalCoefficientConstant
                parentConstant retentionConstant clusterConstant D
                C_singleton coverExponent *
              Real.rpow delta
                (-(faithfulCanonicalStructuredScaleLoss
                      (C_singleton +
                        (7 / 2 : ℝ) * coverExponent)
                      metricExponent +
                    faithfulCanonicalOrdinaryLoss metricExponent)) *
              ((Real.sqrt (3 * C_KT) *
                  Real.rpow (4 * C_out ^ 2) (1 / 4 : ℝ) *
                  Real.rpow
                    (2 * C_shading * Real.sqrt C_shading)
                    (3 / 4 : ℝ) /
                  Real.sqrt C_R) * delta) *
              Real.rpow (data.mu : ℝ) (-3 / 2 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ =
          (4 *
              faithfulCanonicalSingletonBranchConstant
                C_singleton coarseSetup.tangency) *
            faithfulCanonicalFinalCoefficientConstant
              parentConstant retentionConstant clusterConstant D
              C_singleton coverExponent *
            Real.rpow delta
              (-(faithfulCanonicalStructuredScaleLoss
                    (C_singleton +
                      (7 / 2 : ℝ) * coverExponent)
                    metricExponent +
                  faithfulCanonicalOrdinaryLoss metricExponent)) *
            ((Real.sqrt (3 * C_KT) *
                Real.rpow (4 * C_out ^ 2) (1 / 4 : ℝ) *
                Real.rpow
                  (2 * C_shading * Real.sqrt C_shading)
                  (3 / 4 : ℝ) /
                Real.sqrt C_R) * delta) *
            Real.rpow (data.mu : ℝ) (-3 / 2 : ℝ) := by ring

end Kakeya.Cinematic
