import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSFiniteRunStatements

/-!
WZ2 Theorem 5.2 parameter-Frostman specialization: execute the total finite
grid OS oracle and return the terminal numerical trace.

## Proof route

Induct on `steps - index`.  At each scheduled state, the finite step oracle
produces a selected radius `rho` and either a terminal certificate or one
corrected transition.

* If `delta^(epsilon^2) ≤ rho`, the run is terminal: build a trace with
  `transitionCount = 0`, using the fine shading's twisted projection as the
  terminal thickened set.
* If `rho < delta^(epsilon^2)`, the global premise
  `delta^(epsilon^2) ≤ finiteSteps.scaleCap` gives `rho < scaleCap`, so the
  next state satisfies the scale-cap hypothesis.  The growth invariant
  `delta^((1-epsilon^2)^index) ≤ currentScale` is preserved through
  `rho > currentScale^(1-epsilon^2)` and `Real.rpow_mul`.  Recurse at
  `index + 1` and prepend the current transition to the returned trace.
-/

namespace Kakeya.Assouad

theorem grid_os_finite_run :
    GridOSFiniteRunStatement := by
  intro delta epsilon etaMax hδ_pos hδ_lt_one hε_pos hε_lt_one
  intro steps schedule base hbase finiteSteps h_cap
  intro source active levels hlevels terminal representatives uniform
  intro index hindex currentScale currentLevel currentFamily currentShading state
  intro hready hδ_le_scale hscale_le_cap hscale_growth f hf_nonsing hf_zero

  let a : ℝ := 1 - epsilon ^ 2
  have ha_pos : 0 < a := by nlinarith
  have ha_lt_one : a < 1 := by nlinarith
  let threshold : ℝ := Real.rpow delta (epsilon ^ 2)

  -- For `0 < x < 1` and `0 < a < 1`, we have `x < x^a`.
  have h_rpow_gt_self : ∀ (x : ℝ), 0 < x → x < 1 → x < Real.rpow x a := by
    intro x hx_pos hx_lt_one
    have hlog : Real.log x < 0 := Real.log_neg hx_pos hx_lt_one
    have hmul : a * Real.log x > Real.log x := by
      have h : (a - 1) * Real.log x > 0 := by
        have h1 : a - 1 < 0 := by linarith
        exact mul_pos_of_neg_of_neg h1 hlog
      linarith
    have h_exp : Real.exp (a * Real.log x) > Real.exp (Real.log x) :=
      Real.exp_strictMono hmul
    have h1 : Real.exp (Real.log x) = x := by
      rw [Real.exp_log] <;> linarith
    have h2 : Real.exp (a * Real.log x) = Real.rpow x a := by
      have h3 : a * Real.log x = Real.log x * a := by ring
      rw [h3]
      exact (Real.rpow_def_of_pos hx_pos a).symm
    rw [h1, h2] at h_exp
    exact h_exp

  -- Subshading containment lifts to twisted projection images.
  have h_twisted_mono : ∀ {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
      {Z Y : Kakeya.Streamlined.TubeShading F} {f : SlopeFunction},
      IsSubshading Z Y → twistedUnion Z f ⊆ twistedUnion Y f := by
    intro δ F Z Y f hsub
    have h1 : Z.union ⊆ Y.union := hsub.union_subset
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, h1 hx, rfl⟩

  -- Main induction on `steps - idx`.
  have h_ind : ∀ (k : ℕ), ∀ (idx : ℕ), steps - idx = k → idx ≤ steps →
    ∀ (cScale : ℝ) (cLevel : ℕ) (cFamily : Kakeya.Streamlined.TubeFamily cScale)
      (cShading : Kakeya.Streamlined.TubeShading cFamily)
      (cState : TubeParameterGridOSStateData terminal representatives uniform cScale cLevel cFamily cShading),
      GridOSReadyStateData schedule idx cState →
      delta ≤ cScale →
      cScale ≤ finiteSteps.scaleCap →
      Real.rpow delta (a ^ idx) ≤ cScale →
      Nonempty (GridOSTerminalTraceData schedule idx cState f) := by
    intro k
    induction k with
    | zero =>
      -- Base case: steps - idx = 0, so idx = steps.  Only terminal branch possible.
      intro idx h_eq h_idx_le cScale cLevel cFamily cShading cState hready' hδ_le hscale_le hgrowth
      have h_idx_eq : idx = steps := by omega
      have h_outcome : Nonempty (GridOSStepOutcomeData schedule idx cState f) :=
        finiteSteps.step hδ_pos hδ_lt_one source active levels hlevels terminal representatives uniform idx h_idx_le cFamily cShading cState hready' hδ_le hscale_le hgrowth f hf_nonsing hf_zero
      rcases h_outcome with ⟨outcome⟩
      let rho := outcome.rho
      have h_term : threshold ≤ rho := by
        cases outcome.terminal_or_transition with
        | inl h => exact h
        | inr h =>
          rcases h with ⟨hlt, _, _, _⟩
          omega
      let terminalSet : Set Point2 := twistedUnion outcome.fineShading f
      have h_terminalSet_nonempty : terminalSet.Nonempty := outcome.fine_twisted_nonempty
      have h_volume_le : MeasureTheory.volume (twistedUnion outcome.fineShading f) ≤
          MeasureTheory.volume (twistedUnion cShading f) :=
        MeasureTheory.measure_mono (h_twisted_mono outcome.fine_subshading)
      have h_cScale_pos : 0 < cScale := by linarith
      refine ⟨{
        transitionCount := 0
        final_index_le := by simpa using h_idx_le
        scale := fun _ => cScale
        projectedVolume := fun _ => MeasureTheory.volume (twistedUnion cShading f)
        scale_zero := by rfl
        volume_zero := by rfl
        scale_pos := fun i hi => by
          have h_i_zero : i = 0 := by omega
          subst h_i_zero
          <;> linarith [hδ_pos, hδ_le]
        transition_step := by
          intro i hi
          exfalso
          omega
        terminalRho := rho
        terminalRho_pos := outcome.rho_pos
        terminal_threshold := h_term
        terminalSet := terminalSet
        terminalSet_nonempty := h_terminalSet_nonempty
        terminal_step := by
          have h1 := outcome.projection_step
          exact h1.trans h_volume_le
      }⟩
    | succ k ih =>
      intro idx h_eq h_idx_le cScale cLevel cFamily cShading cState hready' hδ_le hscale_le hgrowth
      have h_outcome : Nonempty (GridOSStepOutcomeData schedule idx cState f) :=
        finiteSteps.step hδ_pos hδ_lt_one source active levels hlevels terminal representatives uniform idx h_idx_le cFamily cShading cState hready' hδ_le hscale_le hgrowth f hf_nonsing hf_zero
      rcases h_outcome with ⟨outcome⟩
      let rho := outcome.rho
      by_cases h_term : threshold ≤ rho
      · -- Terminal branch: selected radius already reaches global threshold.
        let terminalSet : Set Point2 := twistedUnion outcome.fineShading f
        have h_terminalSet_nonempty : terminalSet.Nonempty := outcome.fine_twisted_nonempty
        have h_volume_le : MeasureTheory.volume (twistedUnion outcome.fineShading f) ≤
            MeasureTheory.volume (twistedUnion cShading f) :=
          MeasureTheory.measure_mono (h_twisted_mono outcome.fine_subshading)
        have h_cScale_pos : 0 < cScale := by linarith
        refine ⟨{
          transitionCount := 0
          final_index_le := by simpa using h_idx_le
          scale := fun _ => cScale
          projectedVolume := fun _ => MeasureTheory.volume (twistedUnion cShading f)
          scale_zero := by rfl
          volume_zero := by rfl
          scale_pos := fun i hi => by
            have h_i_zero : i = 0 := by omega
            subst h_i_zero
            <;> linarith [hδ_pos, hδ_le]
          transition_step := by
            intro i hi
            exfalso
            omega
          terminalRho := rho
          terminalRho_pos := outcome.rho_pos
          terminal_threshold := h_term
          terminalSet := terminalSet
          terminalSet_nonempty := h_terminalSet_nonempty
          terminal_step := by
            have h1 := outcome.projection_step
            exact h1.trans h_volume_le
        }⟩
      · -- Nonterminal branch: rho < threshold ≤ scaleCap, recurse.
        have h_rho_lt_threshold : rho < threshold := by linarith
        have h_not_term : ¬(threshold ≤ rho) := by linarith
        rcases outcome.terminal_or_transition.resolve_left h_not_term with
          ⟨hidx_lt_steps, nextLevel, transition, ⟨readyNext⟩⟩
        have h_cScale_pos : 0 < cScale := by linarith
        have h_cScale_lt_one : cScale < 1 := by
          have h : cScale ≤ finiteSteps.scaleCap := hscale_le
          have h2 : finiteSteps.scaleCap ≤ 1 / 8 := finiteSteps.scaleCap_le_eighth
          linarith
        have h_rpow_gt : cScale < Real.rpow cScale a :=
          h_rpow_gt_self cScale h_cScale_pos h_cScale_lt_one
        have hδ_le_rho : delta ≤ rho := by
          have h : delta < rho := by
            calc delta ≤ cScale := hδ_le
              _ < Real.rpow cScale a := h_rpow_gt
              _ < rho := outcome.rho_growth
          exact le_of_lt h
        have hrho_le_cap : rho ≤ finiteSteps.scaleCap := by
          have h : rho < finiteSteps.scaleCap := by
            calc rho < threshold := h_rho_lt_threshold
              _ ≤ finiteSteps.scaleCap := h_cap
          exact le_of_lt h
        have hgrowth_next : Real.rpow delta (a ^ (idx + 1)) ≤ rho := by
          have h1 : a ^ (idx + 1) = (a ^ idx) * a := by ring
          rw [h1]
          have h2 : Real.rpow delta ((a ^ idx) * a) =
              Real.rpow (Real.rpow delta (a ^ idx)) a :=
            Real.rpow_mul hδ_pos.le (a ^ idx) a
          rw [h2]
          have h3 : 0 ≤ Real.rpow delta (a ^ idx) := Real.rpow_nonneg hδ_pos.le _
          have h4 : Real.rpow (Real.rpow delta (a ^ idx)) a ≤ Real.rpow cScale a :=
            Real.rpow_le_rpow h3 hgrowth ha_pos.le
          exact le_of_lt (h4.trans_lt outcome.rho_growth)
        have h_rec : Nonempty (GridOSTerminalTraceData schedule (idx + 1) transition.nextState f) :=
          ih (idx + 1) (by omega) (by omega)
            rho nextLevel
            transition.package.blocks.coarse transition.nextShading
            transition.nextState readyNext
            hδ_le_rho hrho_le_cap hgrowth_next
        rcases h_rec with ⟨trace'⟩
        let newScale : ℕ → ℝ := fun i =>
          match i with
          | 0 => cScale
          | i + 1 => trace'.scale i
        let newVolume : ℕ → ENNReal := fun i =>
          match i with
          | 0 => MeasureTheory.volume (twistedUnion cShading f)
          | i + 1 => trace'.projectedVolume i
        have h_final_index_le : idx + (trace'.transitionCount + 1) ≤ steps := by
          have h : (idx + 1) + trace'.transitionCount ≤ steps := trace'.final_index_le
          omega
        have h_scale_pos : ∀ i, i ≤ trace'.transitionCount + 1 → 0 < newScale i := by
          intro i hi
          cases i with
          | zero =>
            simpa [newScale] using h_cScale_pos
          | succ i' =>
            have h_i'_le : i' ≤ trace'.transitionCount := by omega
            simpa [newScale] using trace'.scale_pos i' h_i'_le
        have h_transition_step : ∀ i, i < trace'.transitionCount + 1 →
            Kakeya.realRpowENN (newScale i / newScale (i + 1)) epsilon *
              newVolume (i + 1) ≤ (6889 : ENNReal) * newVolume i := by
          intro i hi
          cases i with
          | zero =>
            simpa [newScale, newVolume, trace'.scale_zero, trace'.volume_zero]
              using transition.telescoping_step
          | succ i' =>
            have h_i'_lt : i' < trace'.transitionCount := by omega
            simpa [newScale, newVolume] using trace'.transition_step i' h_i'_lt
        have h_terminal_step :
            Kakeya.realRpowENN (newScale (trace'.transitionCount + 1) / trace'.terminalRho) epsilon *
              MeasureTheory.volume (Metric.cthickening trace'.terminalRho trace'.terminalSet) ≤
            newVolume (trace'.transitionCount + 1) := by
          simpa [newScale, newVolume] using trace'.terminal_step
        refine ⟨{
          transitionCount := trace'.transitionCount + 1
          final_index_le := h_final_index_le
          scale := newScale
          projectedVolume := newVolume
          scale_zero := by rfl
          volume_zero := by rfl
          scale_pos := h_scale_pos
          transition_step := h_transition_step
          terminalRho := trace'.terminalRho
          terminalRho_pos := trace'.terminalRho_pos
          terminal_threshold := trace'.terminal_threshold
          terminalSet := trace'.terminalSet
          terminalSet_nonempty := trace'.terminalSet_nonempty
          terminal_step := h_terminal_step
        }⟩

  exact h_ind (steps - index) index rfl hindex
    currentScale currentLevel currentFamily currentShading state
    hready hδ_le_scale hscale_le_cap hscale_growth

end Kakeya.Assouad
