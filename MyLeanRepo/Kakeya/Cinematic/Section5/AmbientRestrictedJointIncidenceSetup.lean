import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedJointIncidenceSetupInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedLargeBinRefinement
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedParentFiberRegularization
import MyLeanRepo.Kakeya.Cinematic.Section5.IncidenceDegreeRegularization
import MyLeanRepo.Kakeya.Cinematic.Section5.IncidenceRectangleFiberRegularization
import MyLeanRepo.Kakeya.Cinematic.Section5.RetainedHeavySupportSetup
import MyLeanRepo.Kakeya.Cinematic.Section5.RetainedIncidenceDegreeSetup

/-!
# Canonical incidence setup from the joint retained-fiber scale
-/

noncomputable section

namespace Kakeya.Cinematic

theorem ambient_restricted_joint_incidence_setup :
    AmbientRestrictedJointIncidenceSetupStatement := by
  intro hDegree hHeavy hParent
  intro family E K delta diameter epsilon eta tRep DeltaRep C_R₀
    data center hE C_R C_count C_shading C_volume
    fineSetup coarseSetup massExponent refinement hdelta
  let q_fiber := refinement.retainedScale
  have hq_fiber : 0 < q_fiber := refinement.retainedScale_pos
  let fiberBound : ℝ := 2 * (q_fiber : ℝ)
  have hfiberBound : 0 < fiberBound := by
    dsimp only [fiberBound]
    positivity
  have hfiberNonempty :
      ∀ i ∈
        rectanglesOverParents refinement.selected
          coarseSetup.coarseData.parent refinement.selectedParents,
        (fineSetup.pointData.fiber (fineSetup.source i)).carrier.Nonempty := by
    intro i _
    rw [fineSetup.pointData_fiber]
    exact
      (ambientRestrictedData data center hE).fiber_nonempty
        hdelta (fineSetup.source i)
  rcases hDegree incidence_degree_regularization
      data center hE fineSetup coarseSetup refinement
      hfiberNonempty with
    ⟨degreeSetup⟩
  have hretainedNonempty : degreeSetup.retained.Nonempty := by
    rcases degreeSetup.rawEdges_nonempty with ⟨edge, hedge⟩
    have hedge' := hedge
    rw [degreeSetup.rawEdges_eq] at hedge'
    exact
      ⟨edge.2,
        (mem_fineFiberIncidenceEdgesOn
          degreeSetup.retained degreeSetup.fiber
          edge.1 edge.2).mp hedge' |>.1⟩
  have hretained_selected :
      ∀ rectangle ∈ degreeSetup.retained,
        rectangle ∈ refinement.selected := by
    intro rectangle hrectangle
    rw [degreeSetup.retained_eq] at hrectangle
    exact (Finset.mem_filter.mp hrectangle).1
  have hfiberLower :
      ∀ rectangle ∈ degreeSetup.retained,
        q_fiber ≤ (degreeSetup.fiber rectangle).card := by
    intro rectangle hrectangle
    rw [degreeSetup.fiber_eq]
    exact
      (refinement.retained_scale_range rectangle
        (hretained_selected rectangle hrectangle)).1
  have hfiberUpper :
      ∀ rectangle ∈ degreeSetup.retained,
        ((degreeSetup.fiber rectangle).card : ℝ) ≤ fiberBound := by
    intro rectangle hrectangle
    have hrange :=
      refinement.retained_scale_range rectangle
        (hretained_selected rectangle hrectangle)
    have hnat :
        (fineSetup.pointData.fiber
          (fineSetup.source rectangle)).card ≤ 2 * q_fiber :=
      Nat.le_of_lt hrange.2
    rw [degreeSetup.fiber_eq]
    dsimp only [fiberBound]
    exact_mod_cast hnat
  rcases hHeavy
      data center hE fineSetup coarseSetup refinement degreeSetup
      q_fiber fiberBound hq_fiber hfiberBound
      hfiberLower hfiberUpper with
    ⟨heavySetup⟩
  have hheavyLogLoss : 1 ≤ heavySetup.heavyLogLoss := by
    rw [heavySetup.heavyLogLoss_eq]
    have hdegree : 0 < heavySetup.degreeLoss := by
      rw [heavySetup.degreeLoss_eq]
      omega
    have hdegree' : (1 : ℝ) ≤ (heavySetup.degreeLoss : ℝ) := by
      exact_mod_cast hdegree
    linarith
  rcases hParent incidence_rectangle_fiber_regularization
      data center hE fineSetup coarseSetup refinement degreeSetup
      q_fiber fiberBound heavySetup
      hq_fiber hheavyLogLoss hfiberBound hfiberUpper with
    ⟨parentSetup⟩
  let retention : ℝ :=
    Real.rpow (tRep / (8 * diameter)) epsilon *
      Real.rpow (DeltaRep / (2 * tRep)) eta
  have hretention : 0 < retention := by
    dsimp only [retention]
    have hdiameter : 0 < diameter := by
      rcases hretainedNonempty with ⟨rectangle, _⟩
      have hcert :=
        (ambientRestrictedData data center hE).certificate
          (fineSetup.source rectangle)
      exact
        (hdelta.trans_le hcert.delta_le_t).trans_le
          hcert.t_le_diameter
    have hmetricRatio : 0 < tRep / (8 * diameter) := by
      exact div_pos data.tRep_pos
        (mul_pos (by norm_num) hdiameter)
    have htangencyRatio : 0 < DeltaRep / (2 * tRep) := by
      have hDelta : 0 < DeltaRep :=
        hdelta.trans_le data.delta_le_DeltaRep
      exact div_pos hDelta
        (mul_pos (by norm_num) data.tRep_pos)
    exact mul_pos
      (Real.rpow_pos_of_pos hmetricRatio epsilon)
      (Real.rpow_pos_of_pos htangencyRatio eta)
  have hretention_mu :
      retention * (data.mu : ℝ) <
        4 * ((q_fiber : ℝ) + 1) := by
    rcases hretainedNonempty with
      ⟨rectangle, hrectangle⟩
    have hselected := hretained_selected rectangle hrectangle
    have hlower :=
      DyadicFineAssignmentData.retained_fiber_lower_at_representatives
        (ambientRestrictedData data center hE)
        hdelta (fineSetup.source rectangle)
    have hpointData :
        (fineSetup.pointData.fiber
          (fineSetup.source rectangle)).card =
          ((ambientRestrictedData data center hE).assignment.fiber
            (fineSetup.source rectangle)).card := by
      rw [fineSetup.pointData_fiber]
    have hupper :=
      (refinement.retained_scale_range rectangle hselected).2
    have hupperReal :
        2 *
            (((ambientRestrictedData data center hE).assignment.fiber
              (fineSetup.source rectangle)).card : ℝ) <
          4 * (q_fiber : ℝ) := by
      rw [← hpointData]
      have hupper' :
          ((fineSetup.pointData.fiber
            (fineSetup.source rectangle)).card : ℝ) <
            2 * (q_fiber : ℝ) := by
        change
          (fineSetup.pointData.fiber
              (fineSetup.source rectangle)).card <
            2 * q_fiber at hupper
        exact_mod_cast hupper
      linarith
    have hlower' :
        retention * (data.mu : ℝ) ≤
          2 *
            (((ambientRestrictedData data center hE).assignment.fiber
              (fineSetup.source rectangle)).card : ℝ) := by
      simpa [retention, ambientRestrictedData] using hlower
    linarith
  let metricBound : ℝ :=
    (4 * Real.rpow (2 * tRep / DeltaRep) eta) *
      (q_fiber : ℝ)
  have hmetricBound : 0 ≤ metricBound := by
    dsimp only [metricBound]
    have hDelta : 0 < DeltaRep :=
      hdelta.trans_le data.delta_le_DeltaRep
    have hratio : 0 ≤ 2 * tRep / DeltaRep := by
      exact div_nonneg
        (mul_nonneg (by norm_num) data.tRep_pos.le)
        hDelta.le
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hratio eta))
      (by positivity)
  have hmetric :
      ∀ rectangle ∈ degreeSetup.retained,
        (((ambientRestrictedData data center hE).metricFiber
          (fineSetup.source rectangle)).card : ℝ) ≤ metricBound := by
    intro rectangle hrectangle
    have hselected := hretained_selected rectangle hrectangle
    dsimp only [metricBound, q_fiber]
    exact refinement.metric_card_bound hdelta rectangle hselected
  exact
    ⟨⟨q_fiber, rfl, fiberBound, rfl, retention, rfl,
      degreeSetup, heavySetup, parentSetup,
      hq_fiber, hfiberBound,
      fun rectangle hrectangle =>
        ⟨hfiberLower rectangle hrectangle,
          hfiberUpper rectangle hrectangle⟩,
      hretention, hretention_mu,
      metricBound, rfl, hmetricBound, hmetric⟩⟩

lemma AmbientRestrictedJointIncidenceSetupData.fiberBound_le_four_mu
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
    (incidence : AmbientRestrictedJointIncidenceSetupData
      data center hE fineSetup coarseSetup refinement)
    (hfiberUpper :
      ∀ p : E,
        ((data.assignment.fiber p).card : ℝ) <
          2 * (data.mu : ℝ)) :
    incidence.fiberBound ≤ 4 * (data.mu : ℝ) := by
  rcases incidence.degreeSetup.selectedEdges_nonempty with
    ⟨edge, hedge⟩
  have hraw :
      edge ∈ incidence.degreeSetup.rawEdges :=
    incidence.degreeSetup.selectedEdges_subset hedge
  rw [incidence.degreeSetup.rawEdges_eq] at hraw
  have hmem :
      edge.2 ∈ incidence.degreeSetup.retained ∧
        edge.1 ∈ (incidence.degreeSetup.fiber edge.2).carrier :=
    (mem_fineFiberIncidenceEdgesOn
      incidence.degreeSetup.retained incidence.degreeSetup.fiber
      edge.1 edge.2).mp hraw
  let p' := fineSetup.source edge.2
  let p : E := ⟨p'.1, p'.2.1⟩
  have hfiberEq :
      (incidence.degreeSetup.fiber edge.2).card =
        (data.assignment.fiber p).card := by
    rw [incidence.degreeSetup.fiber_eq]
    change
      (fineSetup.pointData.fiber p').card =
        (data.assignment.fiber p).card
    have hpoint :
        fineSetup.pointData.fiber p' =
          (ambientRestrictedData data center hE).assignment.fiber p' :=
      fineSetup.pointData_fiber p'
    rw [hpoint]
    rfl
  have hq :
      (incidence.q_fiber : ℝ) ≤
        ((data.assignment.fiber p).card : ℝ) := by
    have h :=
      (incidence.retained_fiber_range edge.2 hmem.1).1
    rw [hfiberEq] at h
    exact_mod_cast h
  rw [incidence.fiberBound_eq]
  nlinarith [hfiberUpper p]

end Kakeya.Cinematic
