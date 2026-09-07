import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSFiniteStepScheduleStatements

/-!
WZ2 Theorem 5.2 parameter-Frostman specialization: choose one common
small-scale threshold and assemble the total finite step oracle.
-/

namespace Kakeya.Assouad

theorem grid_os_finite_step_schedule :
    GridOSFiniteStepScheduleStatement := by
  intro h_finite_threshold h_last_terminal h_bounded_one_scale h_dichotomy h_transition_ready
  intro epsilon hε_pos hε_lt_one
  have hε_lt_one' : epsilon < 1 :=
    hε_lt_one.trans (by norm_num)

  -- Step 1: Choose etaMax by applying bounded one-scale with rhoMax = 1/8,
  -- then shrinking to ensure 4 * etaMax < epsilon^2.
  rcases h_bounded_one_scale epsilon (1 / 8) hε_pos hε_lt_one
      (by norm_num) (by norm_num) (by norm_num) with
    ⟨etaMax_raw, h_etaRaw_pos, h_etaRaw_le_eps, h_one_scale_raw⟩
  let etaMax := min etaMax_raw (epsilon ^ 2 / 8)
  have h_etaMax_pos : 0 < etaMax := by
    apply lt_min h_etaRaw_pos
    positivity
  have h_etaMax_le_eps : etaMax ≤ epsilon := by
    calc etaMax ≤ etaMax_raw := min_le_left _ _
         _ ≤ epsilon := h_etaRaw_le_eps
  have h_four_etaMax : 4 * etaMax < epsilon ^ 2 := by
    calc 4 * etaMax ≤ 4 * (epsilon ^ 2 / 8) := by gcongr <;> exact min_le_right _ _
         _ = epsilon ^ 2 / 2 := by ring
         _ < epsilon ^ 2 := by
           have h : 0 < epsilon ^ 2 := by positivity
           linarith
  have h_one_scale_main : ∀ (eta : ℝ), 0 < eta → eta ≤ etaMax →
      ∃ (delta₀ : ℝ), 0 < delta₀ ∧ delta₀ < 1 ∧
        ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
          ∀ (F : Kakeya.Streamlined.TubeFamily delta),
            F.Nonempty → IsInVerticalChart F →
            (∀ i : Fin F.card, |(tubeParams i).a| ≤ 12 ∧ |(tubeParams i).b| ≤ 12 ∧
              |(tubeParams i).c| ≤ 2 ∧ |(tubeParams i).d| ≤ 2) →
            ∀ (C : ENNReal), 1 ≤ C → C ≠ ⊤ →
              C ≤ Kakeya.realRpowENN delta (-eta) →
              TubeParameterFrostmanBound F C →
              ∀ (Y : Kakeya.Streamlined.TubeShading F),
                Y.IsLambdaDense (Kakeya.realRpowENN delta (eta / 2)) →
                IsInSlopeWindow Y →
                ∀ (f : SlopeFunction), f.IsNonsingular → f 0 = 0 →
                  ∃ (rho : ℝ), Real.rpow delta (1 - epsilon ^ 2) < rho ∧ rho ≤ (1 / 8) ∧
                    ∃ (Z : Kakeya.Streamlined.TubeShading F),
                      IsSubshading Z Y ∧
                      Z.IsLambdaDense (Kakeya.realRpowENN delta (4 * eta)) ∧
                      MeasureTheory.volume (twistedUnion Z f) ≥
                        Kakeya.realRpowENN (delta / rho) epsilon *
                          MeasureTheory.volume (Metric.cthickening rho (twistedUnion Z f)) := by
    intro eta hpos hle
    exact h_one_scale_raw eta hpos (hle.trans (min_le_left _ _))
  choose delta₀ hδ₀_pos hδ₀_lt_one h_bounded using h_one_scale_main

  refine' ⟨etaMax, h_etaMax_pos, h_etaMax_le_eps, _⟩
  intro steps h_steps schedule base hbase

  -- Step 2: For each eta, extract scale₀ from dichotomy.
  have h_dichotomy_main : ∀ (eta : ℝ), 0 < eta → 4 * eta < epsilon ^ 2 →
      ∃ (scale₀ : ℝ), 0 < scale₀ ∧ scale₀ ≤ 1 ∧
        ∀ {delta : ℝ}, 0 < delta →
          ∀ (source : Kakeya.Streamlined.TubeFamily delta),
            ∀ (active : Finset (Fin source.card)),
              ∀ (levels : ℕ),
                ((base ^ levels : ℝ)⁻¹) < (base : ℝ) * delta →
                ∀ (terminal : TubeParameterTerminalCellFiberRegularizationData source active base levels),
                  ∀ (representatives : TubeParameterTerminalCellRepresentativesData terminal),
                    ∀ (uniform : TubeParameterTerminalCellOSLiftData terminal representatives),
                      ∀ {currentScale : ℝ},
                        ∀ {currentLevel : ℕ},
                          ∀ (currentFamily : Kakeya.Streamlined.TubeFamily currentScale),
                            ∀ (currentShading : Kakeya.Streamlined.TubeShading currentFamily),
                              ∀ (state : TubeParameterGridOSStateData terminal representatives uniform currentScale currentLevel currentFamily currentShading),
                                delta ≤ currentScale →
                                currentScale ≤ scale₀ →
                                ∀ (fineShading : Kakeya.Streamlined.TubeShading currentFamily),
                                  IsSubshading fineShading currentShading →
                                  IsInSlopeWindow fineShading →
                                  fineShading.IsLambdaDense (Kakeya.realRpowENN currentScale (4 * eta)) →
                                  ∀ (rho : ℝ),
                                    Real.rpow currentScale (1 - epsilon ^ 2) < rho →
                                    rho ≤ 1 / 8 →
                                    ∀ (f : SlopeFunction),
                                      f.IsNonsingular → f 0 = 0 →
                                      MeasureTheory.volume (twistedUnion fineShading f) ≥
                                        Kakeya.realRpowENN (currentScale / rho) epsilon *
                                          MeasureTheory.volume (Metric.cthickening rho (twistedUnion fineShading f)) →
                                      Real.rpow delta (epsilon ^ 2) ≤ rho ∨
                                        ∃ (nextLevel : ℕ), Nonempty (TubeParameterGridOSStateTransitionData
                                          state fineShading rho nextLevel f epsilon
                                            (Kakeya.realRpowENN currentScale (4 * eta))) := by
    intro eta hpos hfour
    exact h_dichotomy epsilon eta hε_pos hε_lt_one' hpos hfour base hbase
  choose scale₀ hscale₀_pos hscale₀_le_one h_dichotomy_scale using h_dichotomy_main

  -- Helper functions for thresholds.
  let d0 (i : Fin (steps + 1)) : ℝ :=
    delta₀ (schedule.eta i) (schedule.eta_pos i (by omega)) (schedule.eta_le i (by omega))
  let s0 (i : Fin (steps + 1)) : ℝ :=
    scale₀ (schedule.eta i) (schedule.eta_pos i (by omega)) (by
      calc 4 * schedule.eta i ≤ 4 * etaMax := by gcongr <;> exact schedule.eta_le i (by omega)
           _ < epsilon ^ 2 := h_four_etaMax)
  let threshold : Fin (steps + 1) → ℝ := fun i => min (min (d0 i) (s0 i)) schedule.delta₀

  have h_threshold_pos : ∀ (i : Fin (steps + 1)), 0 < threshold i := by
    intro i
    have h1 : 0 < d0 i := hδ₀_pos (schedule.eta i) (schedule.eta_pos i (by omega)) (schedule.eta_le i (by omega))
    have h2 : 0 < s0 i := hscale₀_pos (schedule.eta i) (schedule.eta_pos i (by omega)) (by
      calc 4 * schedule.eta i ≤ 4 * etaMax := by gcongr <;> exact schedule.eta_le i (by omega)
           _ < epsilon ^ 2 := h_four_etaMax)
    have h3 : 0 < schedule.delta₀ := schedule.delta₀_pos
    simp only [threshold]
    positivity

  -- Get common positive lower bound.
  rcases h_finite_threshold steps threshold h_threshold_pos with ⟨common, h_common_pos, h_common_le⟩
  let scaleCap := min common (1 / 8)
  have h_scaleCap_pos : 0 < scaleCap := by positivity
  have h_scaleCap_le_eighth : scaleCap ≤ 1 / 8 := min_le_right _ _

  -- Step 3: Construct the step function.
  refine' ⟨scaleCap, h_scaleCap_pos, h_scaleCap_le_eighth, _⟩
  intro delta hδ_pos hδ_lt_one source active levels hlevels terminal representatives uniform
    index hindex currentScale currentLevel currentFamily currentShading state
    hready hδ_le_scale hscale_le_cap hgrowth f hf_nonsing hf_zero

  let eta := schedule.eta index
  have h_eta_pos : 0 < eta := schedule.eta_pos index hindex
  have h_eta_le : eta ≤ etaMax := schedule.eta_le index hindex
  have h_four_eta : 4 * eta < epsilon ^ 2 := by
    calc 4 * eta ≤ 4 * etaMax := by gcongr
         _ < epsilon ^ 2 := h_four_etaMax
  have h_scale_pos : 0 < currentScale := lt_of_lt_of_le hδ_pos hδ_le_scale

  have h_index_lt_succ : index < steps + 1 := by omega
  let i_fin : Fin (steps + 1) := ⟨index, h_index_lt_succ⟩
  have h_le_common : currentScale ≤ common := by
    calc currentScale ≤ scaleCap := hscale_le_cap
         _ ≤ common := min_le_left _ _
  have h_le_threshold : currentScale ≤ threshold i_fin :=
    le_trans h_le_common (h_common_le i_fin)

  have h_le_min : currentScale ≤ min (d0 i_fin) (s0 i_fin) :=
    le_trans h_le_threshold (min_le_left (min (d0 i_fin) (s0 i_fin)) schedule.delta₀)
  have h_le_d0 : currentScale ≤ d0 i_fin :=
    le_trans h_le_min (min_le_left (d0 i_fin) (s0 i_fin))
  have h_le_s0 : currentScale ≤ s0 i_fin :=
    le_trans h_le_min (min_le_right (d0 i_fin) (s0 i_fin))
  have h_le_schedule_delta₀ : currentScale ≤ schedule.delta₀ :=
    le_trans h_le_threshold (min_le_right (min (d0 i_fin) (s0 i_fin)) schedule.delta₀)
  have hδ_le_schedule_delta₀ : delta ≤ schedule.delta₀ := by
    calc delta ≤ currentScale := hδ_le_scale
         _ ≤ schedule.delta₀ := h_le_schedule_delta₀

  -- Apply bounded one-scale theorem.
  rcases h_bounded eta h_eta_pos h_eta_le currentScale h_scale_pos h_le_d0
      currentFamily state.family_nonempty state.vertical state.parameter_bounds
      state.parameterConstant state.parameter_one state.parameter_ne_top
      hready.parameter_bound state.parameter_frostman
      currentShading hready.density state.slope_window f hf_nonsing hf_zero
    with ⟨rho, h_rho_growth, h_rho_le_max, fineShading, h_fine_sub, h_fine_density, h_projection⟩

  have h_rho_pos : 0 < rho := by
    have h1 : 0 < Real.rpow currentScale (1 - epsilon ^ 2) := Real.rpow_pos_of_pos h_scale_pos _
    linarith
  have h_rho_le_eighth : rho ≤ 1 / 8 := h_rho_le_max
  have h_fine_slope_window : IsInSlopeWindow fineShading := by
    have h1 : fineShading.union ⊆ currentShading.union := by
      intro x hx
      rcases hx with ⟨j, hj⟩
      exact ⟨j, h_fine_sub j hj⟩
    have h2 : currentShading.union ⊆ horizontalSlab (-1) 1 := state.slope_window
    exact subset_trans h1 h2

  -- Prove fine_twisted_nonempty from density.
  have h_lambda_pos : 0 < Kakeya.realRpowENN currentScale (4 * eta) := by
    simp only [Kakeya.realRpowENN]
    have h1 : 0 < Real.rpow currentScale (4 * eta) := Real.rpow_pos_of_pos h_scale_pos _
    exact ENNReal.ofReal_pos.mpr h1

  have h_family_mass_pos : 0 < currentFamily.toBodyFamily.mass := by
    have h_card : 0 < currentFamily.card := state.family_nonempty
    rcases Fin.pos_iff_nonempty.mp h_card with ⟨j⟩
    let T := currentFamily.tube j
    have h_base_in_seg : T.base ∈ unitSegment T.base T.direction := by
      simp only [unitSegment, Set.mem_image]
      refine' ⟨0, by norm_num, _⟩
      simp
    have h_ball_sub : Metric.ball T.base currentScale ⊆ T.carrier := by
      intro x hx
      have h_dist : dist x T.base < currentScale := hx
      exact Metric.mem_cthickening_of_dist_le x T.base currentScale (unitSegment T.base T.direction) h_base_in_seg h_dist.le
    have h_ball_pos : 0 < MeasureTheory.volume (Metric.ball T.base currentScale) := by
      rw [EuclideanSpace.volume_ball_fin_three T.base currentScale]
      positivity
    have h_tube_pos : 0 < MeasureTheory.volume T.carrier :=
      lt_of_lt_of_le h_ball_pos (MeasureTheory.measure_mono h_ball_sub)
    have h_body_vol : (currentFamily.toBodyFamily.body j).volume = MeasureTheory.volume T.carrier := by
      rfl
    have h_sum_ge : (currentFamily.toBodyFamily.body j).volume ≤ currentFamily.toBodyFamily.mass := by
      apply Finset.single_le_sum (fun i _ => by positivity) (Finset.mem_univ j)
    rw [h_body_vol] at h_sum_ge
    exact lt_of_lt_of_le h_tube_pos h_sum_ge

  have h_fine_mass_pos : 0 < fineShading.mass := by
    have h_dens : Kakeya.realRpowENN currentScale (4 * eta) * currentFamily.toBodyFamily.mass ≤ fineShading.mass :=
      h_fine_density
    have h_pos : 0 < Kakeya.realRpowENN currentScale (4 * eta) * currentFamily.toBodyFamily.mass :=
      ENNReal.mul_pos h_lambda_pos.ne' h_family_mass_pos.ne'
    exact lt_of_lt_of_le h_pos h_dens

  have h_fine_union_nonempty : fineShading.union.Nonempty := by
    by_contra h
    have h_empty : fineShading.union = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have h_all_empty : ∀ (j : Fin currentFamily.card), fineShading.carrier j = ∅ := by
      intro j
      by_contra hj
      have hne : (fineShading.carrier j).Nonempty := Set.nonempty_iff_ne_empty.mpr hj
      rcases hne with ⟨x, hx⟩
      have h_in_union : x ∈ fineShading.union := ⟨j, hx⟩
      rw [h_empty] at h_in_union
      simpa using h_in_union
    have h_mass_zero : fineShading.mass = 0 := by
      have h : fineShading.mass = ∑ i : Fin currentFamily.card, MeasureTheory.volume (fineShading.carrier i) := by rfl
      rw [h]
      apply Finset.sum_eq_zero
      intro i _
      rw [h_all_empty i]
      simp
    rw [h_mass_zero] at h_fine_mass_pos
    simpa using h_fine_mass_pos

  have h_fine_twisted_nonempty : (twistedUnion fineShading f).Nonempty := by
    rcases h_fine_union_nonempty with ⟨x, hx⟩
    refine' ⟨twistedProjection f x, _⟩
    exact ⟨x, hx, rfl⟩

  -- Apply dichotomy.
  have h_dich_result : Real.rpow delta (epsilon ^ 2) ≤ rho ∨
      ∃ (nextLevel : ℕ), Nonempty (TubeParameterGridOSStateTransitionData
        state fineShading rho nextLevel f epsilon
          (Kakeya.realRpowENN currentScale (4 * eta))) :=
    h_dichotomy_scale eta h_eta_pos h_four_eta
      (delta := delta) hδ_pos
      source active levels hlevels terminal representatives uniform
      (currentScale := currentScale) (currentLevel := currentLevel)
      currentFamily currentShading state
      hδ_le_scale h_le_s0
      fineShading h_fine_sub h_fine_slope_window h_fine_density
      rho h_rho_growth h_rho_le_eighth
      f hf_nonsing hf_zero h_projection

  let threshold_val : ℝ := Real.rpow delta (epsilon ^ 2)

  -- Construct terminal_or_transition.
  have h_terminal_or_transition : threshold_val ≤ rho ∨
      ∃ (hindex : index < steps),
        ∃ (nextLevel : ℕ),
          ∃ (transition : TubeParameterGridOSStateTransitionData
              state fineShading rho nextLevel f epsilon
                (Kakeya.realRpowENN currentScale (4 * eta))),
            Nonempty (GridOSReadyStateData schedule (index + 1) transition.nextState) := by
    by_cases h_term : threshold_val ≤ rho
    · exact Or.inl h_term
    · -- rho < threshold_val
      have h_rho_lt : rho < threshold_val := by linarith
      -- At index = steps, last step terminal would force threshold_val ≤ rho.
      have h_index_lt_steps : index < steps := by
        by_contra h_not_lt
        have h_eq : index = steps := by omega
        have h_last : threshold_val ≤ rho := h_last_terminal
          (delta := delta) (epsilon := epsilon) (currentScale := currentScale) (rho := rho)
          hδ_pos hδ_lt_one hε_pos hε_lt_one' steps h_steps
          (by rw [h_eq] at hgrowth; exact hgrowth)
          h_rho_growth
        exact h_term h_last
      -- Dichotomy must give transition branch.
      cases h_dich_result with
      | inl h_left =>
        exfalso
        exact h_term h_left
      | inr h_right =>
        rcases h_right with ⟨nextLevel, ⟨transition⟩⟩
        have h_ready_next : Nonempty (GridOSReadyStateData schedule (index + 1) transition.nextState) :=
          h_transition_ready
            (delta := delta) (epsilon := epsilon) (etaMax := etaMax)
            (steps := steps) schedule
            hδ_pos hδ_le_schedule_delta₀ index h_index_lt_steps
            source active base levels terminal representatives uniform
            (currentScale := currentScale) (currentLevel := currentLevel)
            currentFamily currentShading state hready hδ_le_scale
            fineShading rho h_rho_pos h_rho_lt nextLevel f transition
        exact Or.inr ⟨h_index_lt_steps, nextLevel, transition, h_ready_next⟩

  exact ⟨{
    fineShading := fineShading
    fine_subshading := h_fine_sub
    fine_slope_window := h_fine_slope_window
    fine_density := h_fine_density
    rho := rho
    rho_pos := h_rho_pos
    rho_growth := h_rho_growth
    rho_le_eighth := h_rho_le_eighth
    projection_step := h_projection
    fine_twisted_nonempty := h_fine_twisted_nonempty
    terminal_or_transition := h_terminal_or_transition
  }⟩

end Kakeya.Assouad
