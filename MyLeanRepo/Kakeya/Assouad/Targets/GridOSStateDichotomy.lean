import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSStateDichotomyStatement

/-!
WZ2 Proposition 7.1 / Theorem 5.2 specialization: turn one analytic
selected-scale output into either a terminal certificate or one corrected
delta-grid OS transition.
-/

namespace Kakeya.Assouad

theorem grid_os_state_dichotomy :
    GridOSStateDichotomyStatement := by
  intro scaleGrowth windowBudget coarsening transition epsilon eta h_eps_pos h_eps_lt_one h_eta_pos h_eta_lt base h_base
  -- Step 1: Obtain scale thresholds from scale growth and window budget
  have h1 := scaleGrowth epsilon (6 * (base : ℝ)) h_eps_pos h_eps_lt_one (by positivity)
  rcases h1 with ⟨scaleGrow₀, hGrow_pos, hGrow_le_one, hGrow⟩
  have h2 := windowBudget epsilon eta h_eps_pos h_eps_lt_one h_eta_pos h_eta_lt
  rcases h2 with ⟨scaleWindow₀, hWindow_pos, hWindow_le_one, hWindowBudget⟩
  set scale₀ : ℝ := min scaleGrow₀ scaleWindow₀ with hscale₀_def
  have h_scale₀_pos : 0 < scale₀ := by
    exact lt_min hGrow_pos hWindow_pos
  have h_scale₀_le_one : scale₀ ≤ 1 := by
    exact (min_le_iff).mpr (Or.inl hGrow_le_one)
  refine' ⟨scale₀, h_scale₀_pos, h_scale₀_le_one, _⟩
  intro delta hdelta_pos source active levels h_terminal_mesh terminal representatives uniform
        currentScale currentLevel currentFamily currentShading state
        h_delta_le_scale h_scale_le_scale₀
        fineShading h_sub h_slope_window h_dense rho h_rpow_lt h_rho_le_eighth
        f h_f_nonsing h_f0 h_volume
  -- rho > 0
  have h_rho_pos : 0 < rho := by
    have h_pos1 : 0 < Real.rpow currentScale (1 - epsilon ^ 2) :=
      Real.rpow_pos_of_pos state.scale_pos _
    linarith
  have h_rho_le_one : rho ≤ 1 := by linarith
  -- Step 3: Scale growth gives 6 * base * currentScale ≤ rho
  have h_scale_le_grow : currentScale ≤ scaleGrow₀ := by
    calc currentScale ≤ scale₀ := h_scale_le_scale₀
         _ ≤ scaleGrow₀ := min_le_left _ _
  have h_grow_result : (6 * (base : ℝ)) * currentScale ≤ rho :=
    hGrow currentScale rho state.scale_pos h_scale_le_grow h_rpow_lt
  have h6_scale : 6 * currentScale ≤ rho := by
    have h_base' : (1 : ℝ) ≤ (base : ℝ) := by exact_mod_cast (by linarith)
    have h : 6 * currentScale ≤ (6 * (base : ℝ)) * currentScale := by
      gcongr <;> linarith
    linarith
  -- Step 4: Window budget dichotomy at currentScale
  have h_scale_le_window : currentScale ≤ scaleWindow₀ := by
    calc currentScale ≤ scale₀ := h_scale_le_scale₀
         _ ≤ scaleWindow₀ := min_le_right _ _
  have h_dichotomy : Real.rpow currentScale (epsilon ^ 2) ≤ rho ∨
      ENNReal.ofReal (400 * rho) ≤
        ENNReal.ofReal (1 / 800 : ℝ) * Kakeya.realRpowENN currentScale (4 * eta) :=
    hWindowBudget currentScale state.scale_pos h_scale_le_window rho h_rho_pos.le
  cases h_dichotomy with
  | inl h_terminal =>
    -- Case 1: terminal — Real.rpow delta (epsilon^2) ≤ rho
    have h_monotone : Real.rpow delta (epsilon ^ 2) ≤ Real.rpow currentScale (epsilon ^ 2) :=
      Real.rpow_le_rpow (by linarith) h_delta_le_scale (by positivity)
    have h_final : Real.rpow delta (epsilon ^ 2) ≤ rho := by
      calc Real.rpow delta (epsilon ^ 2) ≤ Real.rpow currentScale (epsilon ^ 2) := h_monotone
           _ ≤ rho := h_terminal
    exact Or.inl h_final
  | inr h_budget =>
    -- Case 2: budget — produce a transition
    set fineDensity : ENNReal := Kakeya.realRpowENN currentScale (4 * eta) with hfineDensity_def
    have h_budget' : ENNReal.ofReal (400 * rho) ≤ gridOSRawDensity fineDensity := by
      simpa [gridOSRawDensity, hfineDensity_def] using h_budget
    -- Step 5: Mesh control at current level
    have h_mesh_current : 6 * ((base ^ currentLevel : ℝ)⁻¹) ≤ rho := by
      cases state.terminal_or_mesh_control with
      | inl h_eq =>
        -- currentLevel = levels: use terminal mesh bound and scale growth
        rw [h_eq]
        have h2 : ((base ^ levels : ℝ)⁻¹) < (base : ℝ) * currentScale := by
          calc ((base ^ levels : ℝ)⁻¹) < (base : ℝ) * delta := h_terminal_mesh
               _ ≤ (base : ℝ) * currentScale := by gcongr
        have h3 : 6 * ((base ^ levels : ℝ)⁻¹) < 6 * ((base : ℝ) * currentScale) :=
          mul_lt_mul_of_pos_left h2 (by norm_num)
        have h4 : 6 * ((base : ℝ) * currentScale) = 6 * (base : ℝ) * currentScale := by ring
        rw [h4] at h3
        have h5 : 6 * (base : ℝ) * currentScale ≤ rho := h_grow_result
        linarith
      | inr h_mesh =>
        -- 6 * mesh ≤ currentScale, and currentScale ≤ rho
        have h_cs_le_rho : currentScale ≤ rho := by linarith
        linarith
    -- Step 6: Apply coarsening to get nextLevel
    have h_coarsen := coarsening base levels currentLevel h_base state.level_le
                         rho h_rho_pos h_rho_le_one h_mesh_current
    rcases h_coarsen with ⟨nextLevel, h_next_le_current, h_next_le_levels, h_mesh_next, _⟩
    -- Step 7: fineDensity properties
    have h_fineDensity_ne_zero : fineDensity ≠ 0 := by
      rw [hfineDensity_def, Kakeya.realRpowENN]
      have h_pos : 0 < Real.rpow currentScale (4 * eta) :=
        Real.rpow_pos_of_pos state.scale_pos (4 * eta)
      have h : ENNReal.ofReal (Real.rpow currentScale (4 * eta)) ≠ 0 := by
        intro h0
        have h' : Real.rpow currentScale (4 * eta) ≤ 0 := by
          exact (ENNReal.ofReal_eq_zero).mp h0
        linarith
      exact h
    have h_fineDensity_ne_top : fineDensity ≠ ⊤ := by
      rw [hfineDensity_def, Kakeya.realRpowENN]
      exact ENNReal.ofReal_ne_top
    -- Apply transition producer
    have h_result := transition
      source active base levels h_base terminal representatives uniform
      currentFamily currentShading state
      fineShading h_sub h_slope_window
      fineDensity h_fineDensity_ne_zero h_fineDensity_ne_top h_dense
      rho h_rho_pos h_rho_le_eighth h6_scale
      nextLevel h_next_le_current h_mesh_next h_budget'
      f h_f_nonsing h_f0 epsilon h_eps_pos h_volume
    exact Or.inr ⟨nextLevel, h_result⟩

end Kakeya.Assouad
