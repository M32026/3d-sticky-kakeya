import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedJointIncidenceSetup
import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicLogLossAbsorption
import MyLeanRepo.Kakeya.Cinematic.Section5.JointMetricCutoffScaleExitInputs

/-!
# Apply the joint metric-cutoff scale exit in one ambient bin

The original Katz--Tao scale and the local vertical scale differ by one fixed
factor.  This caller transports the pointwise fiber bound across that factor,
absorbs the heavy dyadic logarithm, and feeds the canonical joint incidence
data to the pure metric-cutoff exit.
-/

namespace Kakeya.Cinematic

theorem ambient_restricted_joint_metric_cutoff_exit
    (hExit : JointMetricCutoffScaleExitStatement)
    (K C_KT scaleFactor C_count metricExponent targetExponent : ℝ)
    (hK : 1 ≤ K)
    (hC_KT : 1 ≤ C_KT)
    (hscaleFactor : 1 ≤ scaleFactor)
    (hC_count : 0 ≤ C_count)
    (hmetric : 0 < metricExponent)
    (hmetric_le_quarter : metricExponent ≤ 1 / 4)
    (htarget : 0 < targetExponent)
    (hmetric_target : 8 * metricExponent ≤ targetExponent) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 / 2 ∧
      ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
        {delta diameter epsilon eta tRep DeltaRep C_R₀ baseDelta : ℝ},
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
          0 < delta →
          delta ≤ delta₀ →
          0 < baseDelta →
          delta = scaleFactor * baseDelta →
          data.ambientSource.HasKatzTaoBound baseDelta C_KT →
          diameter = K →
          epsilon = metricExponent →
          eta = metricExponent ^ 2 →
          selectedIncidenceMetricCut
                incidence.heavySetup.heavyLogLoss
                (4 * Real.rpow (2 * tRep / DeltaRep) eta)
                epsilon *
              tRep <
            480 * K * delta →
          1 ≤
            Real.rpow delta (-targetExponent) *
              Real.rpow (data.mu : ℝ) (-3 / 2 : ℝ) := by
  let B : ℝ := C_KT * scaleFactor
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  rcases hExit K B targetExponent metricExponent
      hK hB htarget hmetric hmetric_le_quarter hmetric_target with
    ⟨deltaExit, hdeltaExit, hdeltaExitOne, hExitMain⟩
  rcases dyadic_log_loss_absorption
      C_count (metricExponent ^ 2) hC_count (sq_pos_of_pos hmetric) with
    ⟨deltaLog, hdeltaLog, hdeltaLogHalf, hLogMain⟩
  let delta₀ := min deltaExit deltaLog
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀_half : delta₀ ≤ 1 / 2 := by
    dsimp only [delta₀]
    exact (min_le_right _ _).trans hdeltaLogHalf
  refine ⟨delta₀, hdelta₀, hdelta₀_half, ?_⟩
  intro family E delta diameter epsilon eta tRep DeltaRep C_R₀ baseDelta
    data center hE C_R C_shading C_volume fineSetup coarseSetup
    massExponent refinement incidence hdelta hdeltaBound hbaseDelta
    hdeltaEq hKT hdiameter hepsilon heta hmetricFailure
  subst diameter
  subst epsilon
  subst eta
  have hdeltaExit' : delta ≤ deltaExit :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaLog' : delta ≤ deltaLog :=
    hdeltaBound.trans (min_le_right _ _)
  have hDeltaRep : 0 < DeltaRep :=
    hdelta.trans_le data.delta_le_DeltaRep
  have hscaleFactorPos : 0 < scaleFactor := by linarith
  have hC_KT_nonneg : 0 ≤ C_KT := by linarith
  have hbase_le_delta : baseDelta ≤ delta := by
    rw [hdeltaEq]
    have hscaled :=
      mul_le_mul_of_nonneg_right hscaleFactor hbaseDelta.le
    simpa using hscaled
  have hbase_le_tRep : baseDelta ≤ tRep :=
    hbase_le_delta.trans data.delta_le_DeltaRep
      |>.trans data.DeltaRep_le_tRep

  have hretainedNonempty : incidence.degreeSetup.retained.Nonempty := by
    rcases incidence.degreeSetup.rawEdges_nonempty with ⟨edge, hedge⟩
    have hedge' := hedge
    rw [incidence.degreeSetup.rawEdges_eq] at hedge'
    exact
      ⟨edge.2,
        (mem_fineFiberIncidenceEdgesOn
          incidence.degreeSetup.retained incidence.degreeSetup.fiber
          edge.1 edge.2).mp hedge' |>.1⟩
  rcases hretainedNonempty with ⟨rectangle, hrectangle⟩
  let p := fineSetup.source rectangle
  have hqFiber :
      (incidence.q_fiber : ℝ) ≤
        (((ambientRestrictedData data center hE).assignment.fiber p).card :
          ℝ) := by
    have hlower :=
      (incidence.retained_fiber_range rectangle hrectangle).1
    have hfiber :
        incidence.degreeSetup.fiber rectangle =
          (ambientRestrictedData data center hE).assignment.fiber p := by
      rw [incidence.degreeSetup.fiber_eq]
      exact fineSetup.pointData_fiber p
    rw [hfiber] at hlower
    exact_mod_cast hlower
  have hfiberKT :
      (((ambientRestrictedData data center hE).assignment.fiber p).card :
          ℝ) ≤
        C_KT * (tRep / baseDelta) :=
    (ambientRestrictedData data center hE).fiber_card_le_katz_tao_all_scales
      hdelta hKT hbaseDelta hC_KT_nonneg hbase_le_tRep p
  have hqRaw :
      (incidence.q_fiber : ℝ) ≤
        C_KT * (tRep / baseDelta) :=
    hqFiber.trans hfiberKT
  have hqScale :
      (incidence.q_fiber : ℝ) ≤
        B * (tRep / delta) := by
    calc
      (incidence.q_fiber : ℝ) ≤
          C_KT * (tRep / baseDelta) := hqRaw
      _ = B * (tRep / delta) := by
        dsimp only [B]
        rw [hdeltaEq]
        field_simp [hbaseDelta.ne', hscaleFactorPos.ne']

  have hlogLoss :
      incidence.heavySetup.heavyLogLoss ≤
        Real.rpow delta (-(metricExponent ^ 2)) := by
    rw [incidence.heavySetup.heavyLogLoss_eq,
      incidence.heavySetup.degreeLoss_eq]
    have hfine :
        (fineSetup.fine.card : ℝ) ≤
          Real.rpow delta (-C_count) :=
      fineSetup.fine_card
    have hraw := hLogMain hdelta hdeltaLog' hfine
    simpa using hraw
  have htK : tRep ≤ 8 * K := by
    have h :=
      (ambientRestrictedData data center hE).tRep_le_eight_diameter
        hdelta p
    exact h
  have hretention :
      Real.rpow (tRep / (8 * K)) metricExponent *
            Real.rpow (DeltaRep / (2 * tRep)) (metricExponent ^ 2) *
            (data.mu : ℝ) <
          4 * ((incidence.q_fiber : ℝ) + 1) := by
    calc
      Real.rpow (tRep / (8 * K)) metricExponent *
              Real.rpow (DeltaRep / (2 * tRep)) (metricExponent ^ 2) *
              (data.mu : ℝ) =
          incidence.retention * (data.mu : ℝ) := by
        rw [incidence.retention_eq]
      _ < 4 * ((incidence.q_fiber : ℝ) + 1) :=
        incidence.retention_mu
  exact hExitMain hdelta hdeltaExit'
    data.delta_le_DeltaRep data.DeltaRep_le_tRep htK
    data.mu_pos rfl
    (by
      rw [incidence.heavySetup.heavyLogLoss_eq,
        incidence.heavySetup.degreeLoss_eq]
      exact_mod_cast (show
        1 ≤ 4 *
          (Nat.log2 (Fintype.card (Fin fineSetup.fine.card)) + 1) by
            omega))
    hlogLoss rfl hqScale hretention
    hmetricFailure

end Kakeya.Cinematic
