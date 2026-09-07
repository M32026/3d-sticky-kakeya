import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedSelectedCardinalityBranches
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalActualSelectedLayerBounds

/-!
# Actual selected cardinality at the faithful canonical scales

This module keeps the parent measure, parent tangency, and q-cluster
construction separate from the purely algebraic selected-cardinality
transport.  The full retained fiber has the fixed coefficient `4`; the
paper-radius cluster coefficient is used only for local nonconcentration.
-/

namespace Kakeya.Cinematic

theorem faithful_canonical_actual_selected_cardinality
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
    (C_out C_inc C_positive C_singleton : ℝ)
    (hInterpolate : CoarseMultiplicityInterpolationStatement)
    (hdelta : 0 < delta)
    (hC_R : 0 < C_R)
    (hC_out : 0 < C_out)
    (hC_inc : 0 < C_inc)
    (hq : 2 ≤ incidence.q_fiber)
    (hC_positive : 1 ≤ C_positive)
    (hC_singleton : 1 ≤ C_singleton)
    (hfiberUpper :
      ∀ p : E,
        ((data.assignment.fiber p).card : ℝ) <
          2 * (data.mu : ℝ))
    (hmeasure :
      ((incidence.heavySetup.M_parent : ℕ) : ℝ) ≤
        faithfulCanonicalParentArea C_out DeltaRep C_R tRep /
          (((2 : ENNReal) ^ refinement.layer.val *
            refinement.cutoff).toReal))
    (htangency :
      ((incidence.heavySetup.M_parent : ℕ) : ℝ) ≤
        faithfulCanonicalCutoffParentScale
            delta tRep DeltaRep C_R C_inc
            incidence.heavySetup.heavyLogLoss metricExponent
            incidence.retention incidence.heavySetup.degreeLoss *
          Real.rpow (data.mu : ℝ) (-2) *
          Real.rpow
            (2 ^ incidence.heavySetup.supportLevel : ℕ) 2)
    (hQ :
      QClusterCoarseCardinalityResult
        incidence.heavySetup.selectedCoarse.card
        (2 ^ incidence.heavySetup.supportLevel)
        cluster.cover.centers.card
        (data.ambientSource.cluster center (3 * tRep)).card
        C_positive C_singleton coarseSetup.tangency cluster.A) :
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
  have hDelta : 0 < DeltaRep :=
    hdelta.trans_le data.delta_le_DeltaRep
  have hlayerMass :
      0 <
        (((2 : ENNReal) ^ refinement.layer.val *
          refinement.cutoff).toReal) := by
    rw [ENNReal.toReal_pos_iff]
    exact
      ⟨ENNReal.mul_pos (by simp) refinement.cutoff_pos.ne',
        ENNReal.mul_lt_top (by simp)
          (lt_top_iff_ne_top.mpr refinement.cutoff_ne_top)⟩
  have hmeasureScale :
      0 ≤
        faithfulCanonicalParentArea C_out DeltaRep C_R tRep /
          (((2 : ENNReal) ^ refinement.layer.val *
            refinement.cutoff).toReal) := by
    apply div_nonneg
    · dsimp only [faithfulCanonicalParentArea]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (sq_nonneg C_out))
          hDelta.le)
        (Real.sqrt_nonneg _)
    · exact hlayerMass.le
  have hparentScale :
      0 ≤
        faithfulCanonicalCutoffParentScale
          delta tRep DeltaRep C_R C_inc
          incidence.heavySetup.heavyLogLoss metricExponent
          incidence.retention incidence.heavySetup.degreeLoss := by
    dsimp only [faithfulCanonicalCutoffParentScale]
    exact ambientRestrictedParentTangencyScale_nonneg
      _ 4 incidence.heavySetup.heavyLogLoss incidence.retention
      incidence.heavySetup.degreeLoss
      (add_nonneg
        (mul_nonneg hC_inc.le (Real.sqrt_nonneg _))
        (by norm_num))
      (by norm_num) incidence.retention_pos.le
  have hfiberScale :
      incidence.fiberBound ≤ 4 * (data.mu : ℝ) :=
    incidence.fiberBound_le_four_mu hfiberUpper
  exact ambient_restricted_selected_cardinality_branches_of_fiber
    hInterpolate data center hE fineSetup coarseSetup refinement
    incidence.degreeSetup incidence.q_fiber incidence.fiberBound 4
    incidence.heavySetup cluster.radius cluster.A cluster.cover
    C_positive C_singleton incidence.retention
    (faithfulCanonicalParentArea C_out DeltaRep C_R tRep /
      (((2 : ENNReal) ^ refinement.layer.val *
        refinement.cutoff).toReal))
    (faithfulCanonicalCutoffParentScale
      delta tRep DeltaRep C_R C_inc
      incidence.heavySetup.heavyLogLoss metricExponent
      incidence.retention incidence.heavySetup.degreeLoss)
    hq cluster.A_ge_one hC_positive hC_singleton
    incidence.fiberBound_pos incidence.retention_pos
    (by norm_num) hmeasureScale hparentScale hfiberScale
    incidence.retention_mu
    (fun rectangle hrectangle =>
      (incidence.retained_fiber_range rectangle hrectangle).1)
    hmeasure htangency hQ

end Kakeya.Cinematic
