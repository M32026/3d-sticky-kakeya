import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSEffectiveLossScheduleStatement

/-!
# Ready states for the corrected finite grid OS iteration

The geometric state stores its exact density and parameter-Frostman
constants.  The finite iteration additionally needs those exact constants to
meet the effective loss scheduled for the current step.
-/

noncomputable section

namespace Kakeya.Assouad

/-- A corrected grid OS state ready for the one-scale theorem at step `index`. -/
structure GridOSReadyStateData
    {delta epsilon etaMax : ℝ}
    {steps : ℕ}
    (schedule : GridOSEffectiveLossScheduleData epsilon etaMax steps)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {active : Finset (Fin source.card)}
    {base levels : ℕ}
    {terminal :
      TubeParameterTerminalCellFiberRegularizationData
        source active base levels}
    {representatives :
      TubeParameterTerminalCellRepresentativesData terminal}
    {uniform :
      TubeParameterTerminalCellOSLiftData terminal representatives}
    {scale : ℝ}
    {level : ℕ}
    {family : Kakeya.Streamlined.TubeFamily scale}
    {shading : Kakeya.Streamlined.TubeShading family}
    (index : ℕ)
    (state :
      TubeParameterGridOSStateData
        terminal representatives uniform scale level family shading) where
  density :
    shading.IsLambdaDense
      (Kakeya.realRpowENN scale (schedule.eta index / 2))
  parameter_bound :
    state.parameterConstant ≤
      Kakeya.realRpowENN scale (-schedule.eta index)

/--
The corrected initial state is ready at step zero, and its selected twisted
projection is contained in the original source projection.
-/
def GridOSInitialParameterAbsorptionStatement : Prop :=
  ∀ {epsilon etaMax : ℝ},
    ∀ {steps : ℕ},
      ∀ schedule :
          GridOSEffectiveLossScheduleData epsilon etaMax steps,
        ∀ {delta : ℝ},
          0 < delta →
          delta ≤ schedule.delta₀ →
          ∀ family : Kakeya.Streamlined.TubeFamily delta,
            ∀ shading : Kakeya.Streamlined.TubeShading family,
              ∀ initial :
                  TubeParameterGridOSInitialStateData
                    (eta := schedule.sourceEta)
                    family shading
                    (Kakeya.realRpowENN
                      delta (-schedule.sourceEta)),
                initial.state.parameterConstant ≤
                  Kakeya.realRpowENN delta (-schedule.eta 0)

/-- The selected initial twisted projection lies in the source projection. -/
def GridOSInitialProjectionContainmentStatement : Prop :=
  ∀ {delta eta : ℝ},
    ∀ family : Kakeya.Streamlined.TubeFamily delta,
      ∀ shading : Kakeya.Streamlined.TubeShading family,
        ∀ sourceConstant : ENNReal,
          ∀ initial :
              TubeParameterGridOSInitialStateData
                (eta := eta) family shading sourceConstant,
            ∀ f : SlopeFunction,
              twistedUnion initial.selectedShading f ⊆
                twistedUnion shading f

/--
Direct callable step-zero ready-state producer.
-/
def GridOSInitialReadyStateInput : Prop :=
  ∀ {epsilon etaMax : ℝ},
        ∀ {steps : ℕ},
          ∀ schedule :
              GridOSEffectiveLossScheduleData epsilon etaMax steps,
            ∀ {delta : ℝ},
              0 < delta →
              delta ≤ schedule.delta₀ →
              ∀ family : Kakeya.Streamlined.TubeFamily delta,
                ∀ shading : Kakeya.Streamlined.TubeShading family,
                  ∀ initial :
                      TubeParameterGridOSInitialStateData
                        (eta := schedule.sourceEta)
                        family shading
                        (Kakeya.realRpowENN
                          delta (-schedule.sourceEta)),
                    Nonempty
                      (GridOSReadyStateData schedule 0 initial.state) ∧
                      ∀ f : SlopeFunction,
                        twistedUnion initial.selectedShading f ⊆
                          twistedUnion shading f

/--
Assemble the direct step-zero ready state from the two nontrivial initial
adapters.
-/
def GridOSInitialReadyStateStatement : Prop :=
  GridOSInitialParameterAbsorptionStatement →
    GridOSInitialProjectionContainmentStatement →
      GridOSInitialReadyStateInput

/--
Upgrade the exact constants in one nonterminal transition to the scheduled
hypotheses for the next one-scale call.
-/
def GridOSTransitionReadyStateStatement : Prop :=
  ∀ {delta epsilon etaMax : ℝ},
    ∀ {steps : ℕ},
      ∀ schedule :
          GridOSEffectiveLossScheduleData epsilon etaMax steps,
        0 < delta →
        delta ≤ schedule.delta₀ →
        ∀ index : ℕ,
          index < steps →
          ∀ source : Kakeya.Streamlined.TubeFamily delta,
            ∀ active : Finset (Fin source.card),
              ∀ base levels : ℕ,
                ∀ terminal :
                    TubeParameterTerminalCellFiberRegularizationData
                      source active base levels,
                  ∀ representatives :
                      TubeParameterTerminalCellRepresentativesData terminal,
                    ∀ uniform :
                        TubeParameterTerminalCellOSLiftData
                          terminal representatives,
                      ∀ {currentScale : ℝ},
                        ∀ {currentLevel : ℕ},
                          ∀ currentFamily :
                              Kakeya.Streamlined.TubeFamily currentScale,
                            ∀ currentShading :
                                Kakeya.Streamlined.TubeShading currentFamily,
                              ∀ state :
                                  TubeParameterGridOSStateData
                                    terminal representatives uniform
                                    currentScale currentLevel
                                    currentFamily currentShading,
                                GridOSReadyStateData
                                  schedule index state →
                                delta ≤ currentScale →
                                ∀ fineShading :
                                    Kakeya.Streamlined.TubeShading
                                      currentFamily,
                                  ∀ rho : ℝ,
                                    0 < rho →
                                    rho < Real.rpow delta (epsilon ^ 2) →
                                    ∀ nextLevel : ℕ,
                                      ∀ f : SlopeFunction,
                                        ∀ transition :
                                            TubeParameterGridOSStateTransitionData
                                              state fineShading rho nextLevel
                                                f epsilon
                                                (Kakeya.realRpowENN
                                                  currentScale
                                                  (4 * schedule.eta index)),
                                          Nonempty
                                            (GridOSReadyStateData
                                              schedule (index + 1)
                                                transition.nextState)

end Kakeya.Assouad
