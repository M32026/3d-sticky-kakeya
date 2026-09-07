import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedSelectedFiberBallBoundInputs

/-!
# Fixed-ball upper bound for selected incidence fibers

At the one radius consumed by the cluster argument, transfer the pointwise
metric two-ends estimate from the ambient-restricted source point to every
selected incidence subfiber.  The explicit worst-case representative-scale
factor remains visible for the later comparison with the retained fiber scale.
-/

namespace Kakeya.Cinematic

noncomputable section

local instance ambientRestrictedSelectedFiberBallBoundProofDecidableEq :
    DecidableEq C2Function := Classical.decEq _

theorem ambient_restricted_selected_fiber_ball_bound_on_retained :
    AmbientRestrictedSelectedFiberBallBoundOnRetainedStatement := by
  intro family E K delta diameter epsilon eta tRep DeltaRep C_R₀
    data center hE C_R C_count C_shading C_volume
    fineSetup coarseSetup massExponent refinement degreeSetup
    radius metricBound hdelta_pos hradius_pos hdelta_lt hradius_lt
    hmetricBound_nonneg hmetricBound coarse rectangle hrect testCenter
  set ardata := ambientRestrictedData data center hE with hardata_def
  set p := fineSetup.source rectangle with hp_def
  have hselected_edges :
      degreeSetup.selectedEdges ⊆
        fineFiberIncidenceEdgesOn degreeSetup.retained degreeSetup.fiber := by
    have h : degreeSetup.selectedEdges ⊆ degreeSetup.rawEdges :=
      degreeSetup.selectedEdges_subset
    have h' : degreeSetup.rawEdges =
        fineFiberIncidenceEdgesOn degreeSetup.retained degreeSetup.fiber :=
      degreeSetup.rawEdges_eq
    rw [h'] at h
    exact h
  have hfiber_subset :
      incidenceRectangleFiber degreeSetup.selectedEdges rectangle ⊆
        (degreeSetup.fiber rectangle).toFinset :=
    incidenceRectangleFiber_subset_fiber_on
      degreeSetup.retained degreeSetup.fiber
      degreeSetup.selectedEdges hselected_edges rectangle
  have hrect_retained : rectangle ∈ degreeSetup.retained :=
    incidenceRectangleSupport_subset_selected
      degreeSetup.retained degreeSetup.fiber
      degreeSetup.selectedEdges hselected_edges
      coarseSetup.coarseData.parent coarse hrect
  have hfiber_eq1 :
      degreeSetup.fiber rectangle = fineSetup.pointData.fiber p := by
    rw [degreeSetup.fiber_eq]
  have hfiber_eq2 :
      fineSetup.pointData.fiber p = ardata.assignment.fiber p :=
    fineSetup.pointData_fiber p
  have hfiber_metric :
      (ardata.assignment.fiber p).carrier ⊆
        (ardata.metricFiber p).carrier :=
    ardata.fiber_subset_metric p
  have hcarrier_subset :
      (incidenceRectangleFiber degreeSetup.selectedEdges rectangle :
          Set C2Function) ⊆
        (ardata.metricFiber p).carrier := by
    calc
      (incidenceRectangleFiber degreeSetup.selectedEdges rectangle :
          Set C2Function)
        ⊆ (degreeSetup.fiber rectangle).toFinset := by
          exact_mod_cast hfiber_subset
      _ = (degreeSetup.fiber rectangle).carrier := by
          simp [FiniteFunctionFamily.toFinset]
      _ = (fineSetup.pointData.fiber p).carrier := by
          rw [hfiber_eq1]
      _ = (ardata.assignment.fiber p).carrier := by
          rw [hfiber_eq2]
      _ ⊆ (ardata.metricFiber p).carrier := hfiber_metric
  have hinter_subset :
      ((incidenceRectangleFiber degreeSetup.selectedEdges rectangle :
          Set C2Function) ∩ c2Ball testCenter (11 * radius)) ⊆
        ((ardata.metricFiber p).carrier ∩
          c2Ball testCenter (11 * radius)) := by
    exact Set.inter_subset_inter hcarrier_subset (Set.Subset.refl _)
  set scale := (11 * radius) / ardata.exactT p with hscale_def
  have hexactT_pos : 0 < ardata.exactT p := by
    have h : delta ≤ ardata.exactT p :=
      (ardata.certificate p).delta_le_t
    linarith
  have hscale_pos : 0 < scale := by
    rw [hscale_def]
    apply div_pos
    · positivity
    · exact hexactT_pos
  have h1 : delta / ardata.exactT p < scale := by
    rw [hscale_def]
    apply div_lt_div_of_pos_right hdelta_lt hexactT_pos
  have h2 : scale < 1 := by
    rw [hscale_def]
    have h3 : 11 * radius < ardata.exactT p := by
      have h4 : 11 * radius < tRep / 8 := hradius_lt
      have h5 : tRep / 8 ≤ ardata.exactT p := by
        have h6 : tRep ≤ 8 * ardata.exactT p :=
          ardata.rep_le_eight_exactT p
        linarith
      linarith
    rw [div_lt_one hexactT_pos]
    exact h3
  have hscale_mul : scale * ardata.exactT p = 11 * radius := by
    rw [hscale_def]
    field_simp [hexactT_pos.ne']
  let cert := ardata.certificate p
  have hnonconc :
      (((ardata.metricFiber p).carrier ∩
          c2Ball testCenter (scale * ardata.exactT p)).ncard : ℝ) ≤
        4 * Real.rpow (2 * scale) epsilon *
          ((ardata.metricFiber p).card : ℝ) :=
    cert.metric_nonconcentration testCenter scale h1 h2
  rw [hscale_mul] at hnonconc
  have hfinite :
      ((ardata.metricFiber p).carrier ∩
        c2Ball testCenter (11 * radius)).Finite := by
    apply (ardata.metricFiber p).finite.subset
    intro x hx
    exact hx.1
  have hncard_le_nat :
      ((incidenceRectangleFiber degreeSetup.selectedEdges rectangle :
          Set C2Function) ∩ c2Ball testCenter (11 * radius)).ncard ≤
      ((ardata.metricFiber p).carrier ∩
        c2Ball testCenter (11 * radius)).ncard :=
    Set.ncard_le_ncard hinter_subset hfinite
  have hncard_le :
      (((incidenceRectangleFiber degreeSetup.selectedEdges rectangle :
          Set C2Function) ∩ c2Ball testCenter (11 * radius)).ncard : ℝ) ≤
        (((ardata.metricFiber p).carrier ∩
            c2Ball testCenter (11 * radius)).ncard : ℝ) := by
    exact_mod_cast hncard_le_nat
  have h9 : 2 * scale ≤ 176 * radius / tRep := by
    rw [hscale_def]
    have h10 : tRep ≤ 8 * ardata.exactT p :=
      ardata.rep_le_eight_exactT p
    have h11 : 0 < tRep := data.tRep_pos
    have h12 : 0 < ardata.exactT p := hexactT_pos
    calc
      2 * ((11 * radius) / ardata.exactT p)
        = 22 * radius / ardata.exactT p := by ring
      _ ≤ 22 * radius / (tRep / 8) := by
        gcongr
        <;> linarith
      _ = 176 * radius / tRep := by
        field_simp [h11.ne']
        ring
  have h14 : 0 ≤ 2 * scale := by
    exact mul_nonneg (by norm_num) (le_of_lt hscale_pos)
  have h15 : 0 ≤ 176 * radius / tRep := by
    have h11 : 0 < tRep := data.tRep_pos
    exact div_nonneg (by positivity) h11.le
  have hfactor_le :
      Real.rpow (2 * scale) epsilon ≤
        Real.rpow (176 * radius / tRep) epsilon :=
    Real.rpow_le_rpow h14 h9 data.epsilon_pos.le
  have hcard_le :
      ((ardata.metricFiber p).card : ℝ) ≤ metricBound :=
    hmetricBound rectangle hrect_retained
  have h_rpow_nonneg :
      0 ≤ Real.rpow (176 * radius / tRep) epsilon :=
    Real.rpow_nonneg h15 epsilon
  calc
    (((incidenceRectangleFiber degreeSetup.selectedEdges rectangle :
        Set C2Function) ∩ c2Ball testCenter (11 * radius)).ncard : ℝ)
      ≤ (((ardata.metricFiber p).carrier ∩
            c2Ball testCenter (11 * radius)).ncard : ℝ) := hncard_le
    _ ≤ 4 * Real.rpow (2 * scale) epsilon *
          ((ardata.metricFiber p).card : ℝ) := hnonconc
    _ ≤ 4 * Real.rpow (176 * radius / tRep) epsilon *
          ((ardata.metricFiber p).card : ℝ) := by
      gcongr
    _ ≤
        4 * Real.rpow (176 * radius / tRep) epsilon *
          metricBound := by
      gcongr

theorem ambient_restricted_selected_fiber_ball_bound :
    AmbientRestrictedSelectedFiberBallBoundStatement := by
  intro family E K delta diameter epsilon eta tRep DeltaRep C_R₀
    data center hE C_R C_count C_shading C_volume
    fineSetup coarseSetup massExponent refinement degreeSetup
    radius metricBound hdelta_pos hradius_pos hdelta_lt hradius_lt
    hmetricBound_nonneg hmetricBound
  exact
    ambient_restricted_selected_fiber_ball_bound_on_retained
      data center hE fineSetup coarseSetup refinement degreeSetup
      radius metricBound hdelta_pos hradius_pos hdelta_lt hradius_lt
      hmetricBound_nonneg
      (fun rectangle _ =>
        hmetricBound (fineSetup.source rectangle))

end

end Kakeya.Cinematic
