import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSReadyStateStatements

/-!
WZ2 Theorem 5.2 parameter-Frostman specialization: upgrade one corrected
transition to the next scheduled one-scale hypotheses.
-/

namespace Kakeya.Assouad

theorem grid_os_transition_ready_state :
    GridOSTransitionReadyStateStatement := by
  intro delta epsilon etaMax steps schedule hdelta hdelta0 index hindex
    source active base levels terminal representatives uniform
    currentScale currentLevel currentFamily currentShading state ready hscale
    fineShading rho hrho hrhobound nextLevel f transition
  have h_density_scheduled :
      Kakeya.realRpowENN rho (schedule.eta (index + 1) / 2) ≤
        gridOSNextDensity (Kakeya.realRpowENN currentScale (4 * schedule.eta index)) :=
    schedule.transition_density_ready delta hdelta hdelta0 index hindex
      currentScale rho hscale state.scale_le_one hrho hrhobound
  have h_parameter_scheduled :
      (8 : ENNReal) * Kakeya.realRpowENN currentScale (-schedule.eta index) ≤
        Kakeya.realRpowENN rho (-schedule.eta (index + 1)) :=
    schedule.transition_parameter_ready delta hdelta hdelta0 index hindex
      currentScale rho hscale state.scale_le_one hrho hrhobound
  have h_density :
      transition.nextShading.IsLambdaDense
        (Kakeya.realRpowENN rho (schedule.eta (index + 1) / 2)) := by
    have h1 : transition.nextState.densityConstant =
        gridOSNextDensity (Kakeya.realRpowENN currentScale (4 * schedule.eta index)) :=
      transition.next_density_eq
    have h2 : transition.nextShading.IsLambdaDense transition.nextState.densityConstant :=
      transition.nextState.density
    rw [h1] at h2
    exact le_trans (mul_le_mul_right' h_density_scheduled _) h2
  have h_parameter_bound :
      transition.nextState.parameterConstant ≤
        Kakeya.realRpowENN rho (-schedule.eta (index + 1)) := by
    have h1 : transition.nextState.parameterConstant = 8 * state.parameterConstant :=
      transition.next_parameter_eq
    rw [h1]
    have h2 : state.parameterConstant ≤
        Kakeya.realRpowENN currentScale (-schedule.eta index) := ready.parameter_bound
    have h3 : (8 : ENNReal) * state.parameterConstant ≤
        (8 : ENNReal) * Kakeya.realRpowENN currentScale (-schedule.eta index) :=
      mul_le_mul_left' h2 8
    exact le_trans h3 h_parameter_scheduled
  exact ⟨h_density, h_parameter_bound⟩

end Kakeya.Assouad
