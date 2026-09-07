import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSReadyStateStatements

/-!
WZ2 Theorem 5.2 parameter-Frostman specialization: absorb the initial
terminal-grid losses and retain projection containment.
-/

namespace Kakeya.Assouad

theorem grid_os_initial_ready_state :
    GridOSInitialReadyStateStatement := by
  intro hParameter hProjection epsilon etaMax steps schedule delta
    hdelta hdelta0 family shading initial
  have hDensityCoefficient :
      Kakeya.realRpowENN delta (schedule.eta 0 / 2) ≤
        terminalCellInitialDensity delta schedule.sourceEta :=
    schedule.initial_density_ready delta hdelta hdelta0
  have hExactDensity :
      initial.selectedShading.IsLambdaDense
        (terminalCellInitialDensity delta schedule.sourceEta) := by
    have h := initial.state.density
    rw [initial.state_density_eq] at h
    exact h
  have hDensity :
      initial.selectedShading.IsLambdaDense
        (Kakeya.realRpowENN delta (schedule.eta 0 / 2)) :=
    (mul_le_mul_right' hDensityCoefficient
      initial.selectedFamily.toBodyFamily.mass).trans hExactDensity
  have hParameterBound :
      initial.state.parameterConstant ≤
        Kakeya.realRpowENN delta (-schedule.eta 0) :=
    hParameter schedule hdelta hdelta0 family shading initial
  exact
    ⟨⟨hDensity, hParameterBound⟩,
      hProjection family shading
        (Kakeya.realRpowENN delta (-schedule.sourceEta))
        initial⟩

end Kakeya.Assouad
