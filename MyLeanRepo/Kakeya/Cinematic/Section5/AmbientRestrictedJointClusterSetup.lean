import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedJointClusterSetupInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedPaperClusterScale
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedSelectedFiberBallBound
import MyLeanRepo.Kakeya.Cinematic.Section5.FiniteTangentBallCover
import MyLeanRepo.Kakeya.Cinematic.Section5.IncidenceCoarseFiberNonconcentrationAt
import MyLeanRepo.Kakeya.Cinematic.Section5.SeparatedBallCardinality
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedSupportNonconcentrationSetup
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedSupportTangentBallCover

/-!
# Canonical paper-radius cluster setup in one ambient bin
-/

noncomputable section

namespace Kakeya.Cinematic

local instance ambientRestrictedJointClusterSetupDecidableEq :
    DecidableEq C2Function := Classical.decEq _

theorem ambient_restricted_joint_cluster_setup :
    AmbientRestrictedJointClusterSetupStatement := by
  intro hScale hFiberBall hNonconcentration hCover
  intro family E K D delta diameter epsilon eta tRep DeltaRep C_R₀
    data center hE C_R C_count C_shading C_volume
    fineSetup coarseSetup massExponent refinement incidence
    hC_R hD hfamily hdelta hdelta_radius
  let fiberRatio : ℝ :=
    4 * Real.rpow (2 * tRep / DeltaRep) eta
  have hDelta : 0 < DeltaRep :=
    hdelta.trans_le data.delta_le_DeltaRep
  have hratio_nonneg : 0 ≤ 2 * tRep / DeltaRep := by
    exact div_nonneg
      (mul_nonneg (by norm_num) data.tRep_pos.le) hDelta.le
  have hfiberRatio : 1 ≤ fiberRatio := by
    dsimp only [fiberRatio]
    have hbase : 1 ≤ 2 * tRep / DeltaRep := by
      have hDelta_le : DeltaRep ≤ tRep := data.DeltaRep_le_tRep
      apply (le_div_iff₀ hDelta).2
      linarith [data.tRep_pos]
    have hrpow :
        1 ≤ Real.rpow (2 * tRep / DeltaRep) eta :=
      Real.one_le_rpow hbase data.eta_pos.le
    nlinarith
  have hlogLoss :
      1 ≤ incidence.heavySetup.heavyLogLoss := by
    rw [incidence.heavySetup.heavyLogLoss_eq]
    have hdegree : 0 < incidence.heavySetup.degreeLoss := by
      rw [incidence.heavySetup.degreeLoss_eq]
      omega
    have hdegree' :
        (1 : ℝ) ≤ incidence.heavySetup.degreeLoss := by
      exact_mod_cast hdegree
    linarith
  have hscale :=
    hScale C_R delta tRep DeltaRep epsilon
      incidence.heavySetup.heavyLogLoss fiberRatio
      hC_R hdelta data.tRep_pos hDelta data.delta_le_DeltaRep
      data.DeltaRep_le_tRep data.epsilon_pos hlogLoss hfiberRatio
  dsimp only at hscale
  rcases hscale with
    ⟨hradius, hradiusUpper, hA, hidentity, hadmissible, hsmall⟩
  let radius :=
    ambientRestrictedPaperClusterRadius
      tRep epsilon incidence.heavySetup.heavyLogLoss fiberRatio
  let A :=
    ambientRestrictedPaperClusterParameter
      C_R tRep epsilon incidence.heavySetup.heavyLogLoss fiberRatio
  let coefficient :=
    ambientRestrictedPaperFiberCoefficient
      tRep epsilon incidence.heavySetup.heavyLogLoss fiberRatio
  have hmetricBound :
      incidence.metricBound =
        fiberRatio * (incidence.q_fiber : ℝ) := by
    rw [incidence.metricBound_eq]
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient, ambientRestrictedPaperFiberCoefficient]
    have hbase :
        0 ≤ 176 * radius / tRep := by
      exact div_nonneg
        (mul_nonneg (by norm_num) hradius.le)
        data.tRep_pos.le
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hbase epsilon))
      (by linarith)
  have hcoefficient_eq :
      coefficient =
        4 * Real.rpow (176 * radius / tRep) epsilon * fiberRatio := by
    rfl
  have hball :
      ∀ coarse rectangle,
        rectangle ∈
          incidenceRectangleSupport incidence.degreeSetup.selectedEdges
            coarseSetup.coarseData.parent coarse →
        ∀ testCenter,
          (((incidenceRectangleFiber incidence.degreeSetup.selectedEdges
                rectangle : Set C2Function) ∩
              c2Ball testCenter (11 * radius)).ncard : ℝ) ≤
            coefficient * (incidence.q_fiber : ℝ) := by
    intro coarse rectangle hrectangle testCenter
    have hraw :=
      hFiberBall data center hE fineSetup coarseSetup refinement
        incidence.degreeSetup radius incidence.metricBound
        hdelta hradius hdelta_radius hradiusUpper
        incidence.metricBound_nonneg incidence.retained_metric_bound
        coarse rectangle hrectangle testCenter
    rw [incidence.metricBound_eq] at hraw
    change
      (((incidenceRectangleFiber incidence.degreeSetup.selectedEdges
            rectangle : Set C2Function) ∩
          c2Ball testCenter (11 * radius)).ncard : ℝ) ≤
        coefficient * (incidence.q_fiber : ℝ)
    rw [hcoefficient_eq]
    simpa [fiberRatio, mul_assoc, mul_left_comm, mul_comm] using hraw
  rcases hNonconcentration
      incidence_coarse_fiber_nonconcentration_at
      data center hE fineSetup coarseSetup refinement
      incidence.degreeSetup incidence.q_fiber incidence.fiberBound
      incidence.heavySetup
      (coefficient * (incidence.q_fiber : ℝ))
      coefficient radius
      incidence.q_fiber_pos hcoefficient (by rfl)
      (fun coarse _ rectangle hrectangle testCenter =>
        hball coarse rectangle hrectangle testCenter) with
    ⟨nonconcentration⟩
  have hballSmall :
      2 * ((2 * incidence.heavySetup.heavyLogLoss) * coefficient) ≤ 1 := by
    have h :
        2 * ((2 * incidence.heavySetup.heavyLogLoss) * coefficient) =
          4 * incidence.heavySetup.heavyLogLoss * coefficient := by
      ring
    rw [h]
    exact hsmall
  rcases hCover finite_tangent_ball_cover
      data center hE fineSetup coarseSetup refinement
      incidence.degreeSetup incidence.q_fiber incidence.fiberBound
      incidence.heavySetup radius
      hD hfamily (by linarith) hradius with
    ⟨cover⟩
  exact
    ⟨⟨fiberRatio, rfl, hfiberRatio,
      radius, rfl, A, rfl, coefficient, rfl,
      hradius, hradiusUpper, hA, hidentity, hadmissible, hsmall,
      nonconcentration, hballSmall, cover⟩⟩

theorem ambient_restricted_joint_cluster_setup_from_separation :
    AmbientRestrictedJointClusterSetupFromSeparationStatement := by
  intro hScale hNonconcentration hCover
  intro family E K D delta diameter epsilon eta tRep DeltaRep C_R₀
    data center hE C_R C_count C_shading C_volume
    fineSetup coarseSetup massExponent refinement incidence
    hC_R hD hfamily hdelta hseparation hqLarge
  let fiberRatio : ℝ :=
    4 * Real.rpow (2 * tRep / DeltaRep) eta
  have hDelta : 0 < DeltaRep :=
    hdelta.trans_le data.delta_le_DeltaRep
  have hfiberRatio : 1 ≤ fiberRatio := by
    dsimp only [fiberRatio]
    have hbase : 1 ≤ 2 * tRep / DeltaRep := by
      apply (le_div_iff₀ hDelta).2
      linarith [data.DeltaRep_le_tRep, data.tRep_pos]
    have hrpow :
        1 ≤ Real.rpow (2 * tRep / DeltaRep) eta :=
      Real.one_le_rpow hbase data.eta_pos.le
    nlinarith
  have hlogLoss :
      1 ≤ incidence.heavySetup.heavyLogLoss := by
    rw [incidence.heavySetup.heavyLogLoss_eq]
    have hdegree : 0 < incidence.heavySetup.degreeLoss := by
      rw [incidence.heavySetup.degreeLoss_eq]
      omega
    have hdegree' :
        (1 : ℝ) ≤ incidence.heavySetup.degreeLoss := by
      exact_mod_cast hdegree
    linarith
  have hscale :=
    hScale C_R delta tRep DeltaRep epsilon
      incidence.heavySetup.heavyLogLoss fiberRatio
      hC_R hdelta data.tRep_pos hDelta data.delta_le_DeltaRep
      data.DeltaRep_le_tRep data.epsilon_pos hlogLoss hfiberRatio
  dsimp only at hscale
  rcases hscale with
    ⟨hradius, hradiusUpper, hA, hidentity, hadmissible, hsmall⟩
  let radius :=
    ambientRestrictedPaperClusterRadius
      tRep epsilon incidence.heavySetup.heavyLogLoss fiberRatio
  let A :=
    ambientRestrictedPaperClusterParameter
      C_R tRep epsilon incidence.heavySetup.heavyLogLoss fiberRatio
  let coefficient :=
    ambientRestrictedPaperFiberCoefficient
      tRep epsilon incidence.heavySetup.heavyLogLoss fiberRatio
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient, ambientRestrictedPaperFiberCoefficient]
    have hbase : 0 ≤ 176 * radius / tRep := by
      exact div_nonneg
        (mul_nonneg (by norm_num) hradius.le)
        data.tRep_pos.le
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hbase epsilon))
      (by linarith)
  have hsmallBall :
      2 * (11 * radius) < data.separationScale := by
    dsimp only [radius, fiberRatio]
    nlinarith
  have hselectedEdges :
      incidence.degreeSetup.selectedEdges ⊆
        fineFiberIncidenceEdgesOn incidence.degreeSetup.retained
          incidence.degreeSetup.fiber := by
    rw [← incidence.degreeSetup.rawEdges_eq]
    exact incidence.degreeSetup.selectedEdges_subset
  have hfiberAmbient :
      ∀ rectangle ∈ incidence.degreeSetup.retained,
        (incidence.degreeSetup.fiber rectangle).carrier ⊆
          data.ambientSource.carrier := by
    intro rectangle _
    rw [incidence.degreeSetup.fiber_eq]
    change
      (fineSetup.pointData.fiber
        (fineSetup.source rectangle)).carrier ⊆
          data.ambientSource.carrier
    rw [fineSetup.pointData_fiber]
    exact
      (ambientRestrictedData data center hE).fiber_subset_ambient
        (fineSetup.source rectangle)
  have hball :
      ∀ coarse ∈ incidence.heavySetup.heavy,
        ∀ rectangle ∈
          incidenceRectangleSupport incidence.degreeSetup.selectedEdges
            coarseSetup.coarseData.parent coarse,
          ∀ testCenter,
            (((incidenceRectangleFiber incidence.degreeSetup.selectedEdges
                  rectangle : Set C2Function) ∩
                c2Ball testCenter (11 * radius)).ncard : ℝ) ≤
              coefficient * (incidence.q_fiber : ℝ) := by
    intro coarse _ rectangle hrectangle testCenter
    have hone :=
      selected_incidence_fiber_small_ball_ncard_le_one
        data.ambientSource data.ambientSource_separated hsmallBall
        incidence.degreeSetup.retained incidence.degreeSetup.fiber
        incidence.degreeSetup.selectedEdges hselectedEdges hfiberAmbient
        coarseSetup.coarseData.parent coarse rectangle hrectangle testCenter
    have hright : 1 ≤ coefficient * (incidence.q_fiber : ℝ) := by
      have hcoefficient_eq :
          coefficient =
            1 / (6 * incidence.heavySetup.heavyLogLoss) := by
        dsimp only [coefficient]
        exact
          ambientRestrictedPaperFiberCoefficient_eq_inv_six_logLoss
            tRep epsilon incidence.heavySetup.heavyLogLoss fiberRatio
            data.tRep_pos data.epsilon_pos
            (lt_of_lt_of_le zero_lt_one hlogLoss)
            (lt_of_lt_of_le zero_lt_one hfiberRatio)
      rw [hcoefficient_eq]
      have hdenom :
          0 < 6 * incidence.heavySetup.heavyLogLoss := by
        positivity
      calc
        1 ≤
            (incidence.q_fiber : ℝ) /
              (6 * incidence.heavySetup.heavyLogLoss) := by
          apply (le_div_iff₀ hdenom).2
          linarith
        _ =
            (1 / (6 * incidence.heavySetup.heavyLogLoss)) *
              (incidence.q_fiber : ℝ) := by
          ring
    exact hone.trans hright
  rcases hNonconcentration
      incidence_coarse_fiber_nonconcentration_at
      data center hE fineSetup coarseSetup refinement
      incidence.degreeSetup incidence.q_fiber incidence.fiberBound
      incidence.heavySetup
      (coefficient * (incidence.q_fiber : ℝ))
      coefficient radius
      incidence.q_fiber_pos hcoefficient (by rfl) hball with
    ⟨nonconcentration⟩
  have hballSmall :
      2 * ((2 * incidence.heavySetup.heavyLogLoss) * coefficient) ≤ 1 := by
    have h :
        2 * ((2 * incidence.heavySetup.heavyLogLoss) * coefficient) =
          4 * incidence.heavySetup.heavyLogLoss * coefficient := by
      ring
    rw [h]
    exact hsmall
  rcases hCover finite_tangent_ball_cover
      data center hE fineSetup coarseSetup refinement
      incidence.degreeSetup incidence.q_fiber incidence.fiberBound
      incidence.heavySetup radius
      hD hfamily (by linarith) hradius with
    ⟨cover⟩
  exact
    ⟨⟨fiberRatio, rfl, hfiberRatio,
      radius, rfl, A, rfl, coefficient, rfl,
      hradius, hradiusUpper, hA, hidentity, hadmissible, hsmall,
      nonconcentration, hballSmall, cover⟩⟩

end Kakeya.Cinematic
