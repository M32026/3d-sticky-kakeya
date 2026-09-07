import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSParameterFrostmanEstimateStatements

/-!
WZ2 Theorem 5.2: complete the explicit parameter-Frostman Section 7 estimate
by executing the corrected finite terminal-cell grid OS iteration.
-/

namespace Kakeya.Assouad

theorem grid_os_parameter_frostman_estimate :
    GridOSParameterFrostmanEstimateStatement := by
  intro hBoundedOneScale hInitialState hLossSchedule hInitialReadyState
        hStateDichotomy hTransitionReadyState hFiniteStepSchedule
        hFiniteRun hTermination hTerminalClosure hFinalAbsorption
  intro epsilon hepsilon_pos
  let innerEpsilon : ℝ := min (epsilon / 4) (1 / 200)
  have h_ie_pos : 0 < innerEpsilon := by positivity
  have h_ie_lt_hundredth : innerEpsilon < 1 / 100 := by
    have h : innerEpsilon ≤ 1 / 200 := min_le_right _ _
    linarith
  have h_ie_lt_one : innerEpsilon < 1 := by
    exact h_ie_lt_hundredth.trans (by norm_num)
  have h_ie_le_eps : innerEpsilon ≤ epsilon / 4 := by
    exact min_le_left _ _
  have h_gap : innerEpsilon + innerEpsilon ^ 2 * (2 - innerEpsilon) < epsilon := by
    have h1 : innerEpsilon ≤ 1 / 200 := min_le_right _ _
    have h2 : innerEpsilon + innerEpsilon ^ 2 * (2 - innerEpsilon) ≤ innerEpsilon + 2 * innerEpsilon ^ 2 := by
      have h3 : innerEpsilon ^ 2 * (2 - innerEpsilon) ≤ 2 * innerEpsilon ^ 2 := by
        have h4 : 0 ≤ innerEpsilon ^ 2 := by positivity
        have h5 : 2 - innerEpsilon ≤ 2 := by linarith
        nlinarith
      linarith
    have h6 : innerEpsilon ≤ epsilon / 4 := h_ie_le_eps
    nlinarith
  rcases hTermination innerEpsilon h_ie_pos h_ie_lt_one with ⟨steps, h_steps_cond, h_steps_growth⟩
  rcases hFiniteStepSchedule innerEpsilon h_ie_pos h_ie_lt_hundredth with
    ⟨etaMax, h_etaMax_pos, h_etaMax_le, h_fsp⟩
  have h_schedule_nonempty : Nonempty (GridOSEffectiveLossScheduleData innerEpsilon etaMax steps) :=
    hLossSchedule innerEpsilon etaMax h_ie_pos h_ie_lt_one h_etaMax_pos steps
  rcases h_schedule_nonempty with ⟨schedule⟩
  let eta : ℝ := schedule.sourceEta
  have h_eta_pos : 0 < eta := schedule.sourceEta_pos
  have h_eta0_formula : schedule.eta 0 = 4 * eta := by
    have h := schedule.eta_formula 0
    simpa using h
  have h_eta0_le_etaMax : schedule.eta 0 ≤ etaMax := schedule.eta_le 0 (by linarith)
  have h_eta_le_eps : eta ≤ epsilon := by
    have h7 : schedule.eta 0 = 4 * eta := h_eta0_formula
    have h8 : 4 * eta ≤ etaMax := by linarith [h_eta0_le_etaMax]
    have h9 : etaMax ≤ innerEpsilon := h_etaMax_le
    nlinarith
  rcases hInitialState eta h_eta_pos with ⟨base, h_base_ge_three, delta₀_initial, h_di_pos, h_di_lt_one, h_initial_producer⟩
  have h_base_ge_two : 2 ≤ base := by linarith
  have h_finite_steps : Nonempty (GridOSFiniteStepScheduleData innerEpsilon etaMax steps schedule base) :=
    h_fsp steps h_steps_cond schedule base h_base_ge_two
  rcases h_finite_steps with ⟨finiteSteps⟩
  rcases hFinalAbsorption innerEpsilon epsilon h_ie_pos h_ie_lt_one h_gap steps with ⟨delta₀_absorb, h_da_pos, h_da_le_one, h_absorb⟩
  let scaleCapRoot : ℝ := Real.rpow finiteSteps.scaleCap (innerEpsilon ^ 2)⁻¹
  have h_scaleCap_pos : 0 < finiteSteps.scaleCap := finiteSteps.scaleCap_pos
  have h_scaleCapRoot_pos : 0 < scaleCapRoot := Real.rpow_pos_of_pos h_scaleCap_pos _
  let delta₀ : ℝ := min (min schedule.delta₀ delta₀_initial) (min delta₀_absorb scaleCapRoot)
  have h_delta₀_pos : 0 < delta₀ := by
    apply lt_min
    · apply lt_min <;> linarith [schedule.delta₀_pos, h_di_pos]
    · apply lt_min <;> linarith [h_da_pos, h_scaleCapRoot_pos]
  have h_delta₀_lt_one : delta₀ < 1 := by
    have h : delta₀ ≤ schedule.delta₀ := by
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    have h2 : schedule.delta₀ < 1 := schedule.delta₀_lt_one
    linarith
  refine ⟨eta, delta₀, h_eta_pos, h_eta_le_eps, h_delta₀_pos, h_delta₀_lt_one, ?_⟩
  intro delta hdelta_pos hdelta_le F hF_nonempty hF_bounded hF_distinct hF_vertical hF_tubeWolff hF_paramFrost hF_extremal Y hY_dense hY_slope f hf_nonsing hf_zero
  have h_delta_le_schedule : delta ≤ schedule.delta₀ := by
    have h : delta₀ ≤ schedule.delta₀ := by
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    exact le_trans hdelta_le h
  have h_delta_le_initial : delta ≤ delta₀_initial := by
    have h : delta₀ ≤ delta₀_initial := by
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    exact le_trans hdelta_le h
  have h_delta_le_absorb : delta ≤ delta₀_absorb := by
    have h : delta₀ ≤ delta₀_absorb := by
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    exact le_trans hdelta_le h
  have h_delta_le_scaleCapRoot : delta ≤ scaleCapRoot := by
    have h : delta₀ ≤ scaleCapRoot := by
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    exact le_trans hdelta_le h
  have h_delta_lt_one : delta < 1 := by
    have h : delta ≤ delta₀ := hdelta_le
    linarith [h_delta₀_lt_one]
  have h_card : F.enncard ≤ Kakeya.realRpowENN delta (-3) := by
    have h1 : F.enncard ≤ Kakeya.realRpowENN delta (-2 - eta / 10) := hF_extremal
    have h2 : Kakeya.realRpowENN delta (-2 - eta / 10) ≤ Kakeya.realRpowENN delta (-3) := by
      simp only [Kakeya.realRpowENN]
      apply ENNReal.ofReal_le_ofReal
      have h3 : -2 - eta / 10 ≥ -3 := by
        have h4 : eta / 10 ≤ 1 := by linarith [h_eta_le_eps]
        linarith
      have h5 : Real.rpow delta (-2 - eta / 10) ≤ Real.rpow delta (-3) := by
        apply Real.rpow_le_rpow_of_exponent_le_or_ge
        exact Or.inr ⟨hdelta_pos, by linarith, by linarith⟩
      exact h5
    exact le_trans h1 h2
  let sourceConstant : ENNReal := Kakeya.realRpowENN delta (-eta)
  have h_sc_pos : 1 ≤ sourceConstant := by
    have h : Real.rpow delta 0 ≤ Real.rpow delta (-eta) :=
      Real.rpow_le_rpow_of_exponent_le_or_ge (Or.inr ⟨hdelta_pos, by linarith, by linarith⟩)
    have h' : (1 : ℝ) ≤ Real.rpow delta (-eta) := by simpa using h
    simp [sourceConstant, Kakeya.realRpowENN]
    exact_mod_cast h'
  have h_sc_ne_top : sourceConstant ≠ ⊤ := by
    simp [sourceConstant, Kakeya.realRpowENN]
  have h_sc_le : sourceConstant ≤ Kakeya.realRpowENN delta (-eta) := by rfl
  have h_initial : ∃ (initial : TubeParameterGridOSInitialStateData (eta := eta) F Y sourceConstant), initial.base = base :=
    h_initial_producer delta hdelta_pos h_delta_le_initial F hF_nonempty hF_vertical
      (fun i => tubeParams_bounds hF_bounded hF_vertical i) h_card sourceConstant h_sc_pos h_sc_ne_top hF_paramFrost
      Y hY_dense hY_slope
  rcases h_initial with ⟨initial, h_initial_base⟩
  subst h_initial_base
  have h_ready : Nonempty (GridOSReadyStateData schedule 0 initial.state) ∧
      ∀ (g : SlopeFunction), twistedUnion initial.selectedShading g ⊆ twistedUnion Y g :=
    hInitialReadyState schedule hdelta_pos h_delta_le_schedule F Y initial
  rcases h_ready with ⟨⟨readyState⟩, h_containment⟩
  have h_scaleCap_cond : Real.rpow delta (innerEpsilon ^ 2) ≤ finiteSteps.scaleCap := by
    have h1 : delta ≤ scaleCapRoot := h_delta_le_scaleCapRoot
    have h2 : Real.rpow delta (innerEpsilon ^ 2) ≤ Real.rpow scaleCapRoot (innerEpsilon ^ 2) :=
      Real.rpow_le_rpow (by linarith) h1 (by positivity)
    have h3 : Real.rpow scaleCapRoot (innerEpsilon ^ 2) = finiteSteps.scaleCap := by
      have h_pos : 0 ≤ finiteSteps.scaleCap := by linarith
      have h5 : scaleCapRoot = Real.rpow finiteSteps.scaleCap ((innerEpsilon ^ 2)⁻¹) := by rfl
      rw [h5]
      have h7 : Real.rpow (Real.rpow finiteSteps.scaleCap ((innerEpsilon ^ 2)⁻¹)) (innerEpsilon ^ 2) =
          Real.rpow finiteSteps.scaleCap (((innerEpsilon ^ 2)⁻¹) * innerEpsilon ^ 2) := by
        exact (Real.rpow_mul h_pos ((innerEpsilon ^ 2)⁻¹) (innerEpsilon ^ 2)).symm
      rw [h7]
      have h6 : (innerEpsilon ^ 2)⁻¹ * innerEpsilon ^ 2 = 1 := by
        field_simp [h_ie_pos.ne']
      rw [h6]
      simp
    rw [h3] at h2
    exact h2
  have h_delta_le_scaleCap : delta ≤ finiteSteps.scaleCap := by
    have h4 : Real.rpow delta (innerEpsilon ^ 2) ≤ finiteSteps.scaleCap := h_scaleCap_cond
    have h5 : Real.rpow delta 1 ≤ Real.rpow delta (innerEpsilon ^ 2) :=
      Real.rpow_le_rpow_of_exponent_le_or_ge (Or.inr ⟨hdelta_pos, by linarith, by nlinarith⟩)
    have h6 : delta ≤ Real.rpow delta (innerEpsilon ^ 2) := by simpa using h5
    linarith
  have h_mesh : ((initial.base ^ initial.levels : ℝ)⁻¹) < (initial.base : ℝ) * delta :=
    initial.mesh_upper
  have h_trace : Nonempty (GridOSTerminalTraceData schedule 0 initial.state f) :=
    hFiniteRun hdelta_pos h_delta_lt_one h_ie_pos h_ie_lt_one schedule initial.base h_base_ge_two
      finiteSteps h_scaleCap_cond F initial.active initial.levels h_mesh
      initial.terminal initial.representatives initial.uniform 0 (by linarith)
      initial.selectedFamily initial.selectedShading initial.state readyState
      (by linarith) h_delta_le_scaleCap
      (by simp)
      f hf_nonsing hf_zero
  rcases h_trace with ⟨trace⟩
  let tc : ℕ := trace.transitionCount
  have h_closure : Kakeya.realRpowENN delta (innerEpsilon + innerEpsilon ^ 2 * (2 - innerEpsilon)) ≤
      (6889 : ENNReal) ^ tc * trace.projectedVolume 0 :=
    hTerminalClosure hdelta_pos h_delta_lt_one h_ie_pos h_ie_lt_one tc
      trace.scale trace.projectedVolume
      trace.scale_zero
      trace.scale_pos
      trace.transition_step
      trace.terminalRho trace.terminalRho_pos trace.terminal_threshold
      trace.terminalSet trace.terminalSet_nonempty
      trace.terminal_step
  have h_tc_le_steps : tc ≤ steps := by
    have h := trace.final_index_le
    simpa using h
  have h_closure_steps : Kakeya.realRpowENN delta (innerEpsilon + innerEpsilon ^ 2 * (2 - innerEpsilon)) ≤
      (6889 : ENNReal) ^ steps * trace.projectedVolume 0 := by
    have h_exp : (6889 : ENNReal) ^ tc ≤ (6889 : ENNReal) ^ steps := by
      gcongr
      <;> norm_num
    calc
      Kakeya.realRpowENN delta (innerEpsilon + innerEpsilon ^ 2 * (2 - innerEpsilon))
        ≤ (6889 : ENNReal) ^ tc * trace.projectedVolume 0 := h_closure
      _ ≤ (6889 : ENNReal) ^ steps * trace.projectedVolume 0 := by
        gcongr
  have h_absorbed : Kakeya.realRpowENN delta epsilon ≤ trace.projectedVolume 0 :=
    h_absorb delta hdelta_pos h_delta_le_absorb (trace.projectedVolume 0) h_closure_steps
  have h_vol0 : trace.projectedVolume 0 = MeasureTheory.volume (twistedUnion initial.selectedShading f) :=
    trace.volume_zero
  have h_contain : twistedUnion initial.selectedShading f ⊆ twistedUnion Y f := h_containment f
  have h_vol_le : trace.projectedVolume 0 ≤ MeasureTheory.volume (twistedUnion Y f) := by
    rw [h_vol0]
    exact MeasureTheory.measure_mono h_contain
  exact le_trans h_absorbed h_vol_le

end Kakeya.Assouad
