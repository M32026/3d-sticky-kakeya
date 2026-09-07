import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSReadyStateStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSStateDichotomyStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.PositiveWindowStatements

/-!
# A common finite step oracle for the corrected grid OS iteration

The signed one-scale theorem and the terminal-or-transition theorem each
return a small-scale threshold after the effective loss is fixed.  A finite
iteration uses only the losses `eta 0, ..., eta steps`, so one common positive
threshold is obtained by taking the minimum of these finitely many thresholds.

At the last allowed index, the scale-growth invariant and
`(1 - epsilon²)^steps ≤ epsilon²` force the selected radius into the terminal
branch.  Earlier nonterminal branches return a transition already upgraded to
the next scheduled ready state.
-/

noncomputable section

namespace Kakeya.Assouad

/-- A finite family of positive thresholds has one positive common lower bound. -/
def GridOSFiniteThresholdStatement : Prop :=
  ∀ steps : ℕ,
    ∀ threshold : Fin (steps + 1) → ℝ,
      (∀ index, 0 < threshold index) →
        ∃ common : ℝ,
          0 < common ∧
            ∀ index, common ≤ threshold index

/--
At the last scheduled index, the scale-growth lower bound forces every
one-scale selected radius into the global terminal branch.
-/
def GridOSLastStepTerminalStatement : Prop :=
  ∀ {delta epsilon currentScale rho : ℝ},
    0 < delta →
    delta < 1 →
    0 < epsilon →
    epsilon < 1 →
    ∀ steps : ℕ,
      (1 - epsilon ^ 2) ^ steps ≤ epsilon ^ 2 →
      Real.rpow delta ((1 - epsilon ^ 2) ^ steps) ≤ currentScale →
      Real.rpow currentScale (1 - epsilon ^ 2) < rho →
        Real.rpow delta (epsilon ^ 2) ≤ rho

/--
The bounded signed one-scale conclusion after all analytic predecessors have
been discharged.
-/
def GridOSBoundedOneScaleInput : Prop :=
  ∀ epsilon rhoMax : ℝ,
    0 < epsilon →
    epsilon < 1 / 100 →
    0 < rhoMax →
    rhoMax ≤ 1 →
    1 / 100 ≤ rhoMax →
      ∃ etaMax : ℝ,
        0 < etaMax ∧
        etaMax ≤ epsilon ∧
        ∀ eta : ℝ,
          0 < eta →
          eta ≤ etaMax →
            ∃ delta₀ : ℝ,
              0 < delta₀ ∧
              delta₀ < 1 ∧
              ∀ delta : ℝ,
                0 < delta →
                delta ≤ delta₀ →
                ∀ F : Kakeya.Streamlined.TubeFamily delta,
                  F.Nonempty →
                  IsInVerticalChart F →
                  (∀ i : Fin F.card,
                    |(tubeParams i).a| ≤ 12 ∧
                      |(tubeParams i).b| ≤ 12 ∧
                      |(tubeParams i).c| ≤ 2 ∧
                      |(tubeParams i).d| ≤ 2) →
                  ∀ C : ENNReal,
                    1 ≤ C →
                    C ≠ ⊤ →
                    C ≤ Kakeya.realRpowENN delta (-eta) →
                    TubeParameterFrostmanBound F C →
                    ∀ Y : Kakeya.Streamlined.TubeShading F,
                      Y.IsLambdaDense
                        (Kakeya.realRpowENN delta (eta / 2)) →
                      IsInSlopeWindow Y →
                      ∀ f : SlopeFunction,
                        f.IsNonsingular →
                        f 0 = 0 →
                          ∃ rho : ℝ,
                            Real.rpow delta
                                (1 - epsilon ^ 2) < rho ∧
                            rho ≤ rhoMax ∧
                            ∃ Z : Kakeya.Streamlined.TubeShading F,
                              IsSubshading Z Y ∧
                              Z.IsLambdaDense
                                (Kakeya.realRpowENN delta (4 * eta)) ∧
                              MeasureTheory.volume (twistedUnion Z f) ≥
                                Kakeya.realRpowENN
                                    (delta / rho) epsilon *
                                  MeasureTheory.volume
                                    (Metric.cthickening rho
                                      (twistedUnion Z f))

/-- One complete analytic and tree-bookkeeping result at a scheduled state. -/
structure GridOSStepOutcomeData
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
    {currentScale : ℝ}
    {currentLevel : ℕ}
    {currentFamily : Kakeya.Streamlined.TubeFamily currentScale}
    {currentShading : Kakeya.Streamlined.TubeShading currentFamily}
    (index : ℕ)
    (state :
      TubeParameterGridOSStateData
        terminal representatives uniform currentScale currentLevel
          currentFamily currentShading)
    (f : SlopeFunction) where
  fineShading : Kakeya.Streamlined.TubeShading currentFamily
  fine_subshading : IsSubshading fineShading currentShading
  fine_slope_window : IsInSlopeWindow fineShading
  fine_density :
    fineShading.IsLambdaDense
      (Kakeya.realRpowENN currentScale (4 * schedule.eta index))
  rho : ℝ
  rho_pos : 0 < rho
  rho_growth :
    Real.rpow currentScale (1 - epsilon ^ 2) < rho
  rho_le_eighth : rho ≤ 1 / 8
  projection_step :
    Kakeya.realRpowENN (currentScale / rho) epsilon *
        MeasureTheory.volume
          (Metric.cthickening rho (twistedUnion fineShading f)) ≤
      MeasureTheory.volume (twistedUnion fineShading f)
  fine_twisted_nonempty : (twistedUnion fineShading f).Nonempty
  terminal_or_transition :
    Real.rpow delta (epsilon ^ 2) ≤ rho ∨
      ∃ hindex : index < steps,
        ∃ nextLevel : ℕ,
          ∃ transition :
              TubeParameterGridOSStateTransitionData
                state fineShading rho nextLevel f epsilon
                  (Kakeya.realRpowENN
                    currentScale (4 * schedule.eta index)),
            Nonempty
              (GridOSReadyStateData
                schedule (index + 1) transition.nextState)

/--
One common threshold and a total scheduled step operation for a finite
corrected grid OS run.
-/
structure GridOSFiniteStepScheduleData
    (epsilon etaMax : ℝ)
    (steps : ℕ)
    (schedule : GridOSEffectiveLossScheduleData epsilon etaMax steps)
    (base : ℕ) where
  scaleCap : ℝ
  scaleCap_pos : 0 < scaleCap
  scaleCap_le_eighth : scaleCap ≤ 1 / 8
  step :
    ∀ {delta : ℝ},
      0 < delta →
      delta < 1 →
      ∀ source : Kakeya.Streamlined.TubeFamily delta,
        ∀ active : Finset (Fin source.card),
          ∀ levels : ℕ,
            ((base ^ levels : ℝ)⁻¹) < (base : ℝ) * delta →
            ∀ terminal :
                TubeParameterTerminalCellFiberRegularizationData
                  source active base levels,
              ∀ representatives :
                  TubeParameterTerminalCellRepresentativesData terminal,
                ∀ uniform :
                    TubeParameterTerminalCellOSLiftData
                      terminal representatives,
                  ∀ index : ℕ,
                    index ≤ steps →
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
                              GridOSReadyStateData schedule index state →
                              delta ≤ currentScale →
                              currentScale ≤ scaleCap →
                              Real.rpow delta
                                  ((1 - epsilon ^ 2) ^ index) ≤
                                currentScale →
                              ∀ f : SlopeFunction,
                                f.IsNonsingular →
                                f 0 = 0 →
                                  Nonempty
                                    (GridOSStepOutcomeData
                                      schedule index state f)

/--
Direct callable producer for the common finite step oracle.
-/
def GridOSFiniteStepScheduleInput : Prop :=
  ∀ epsilon : ℝ,
          0 < epsilon →
          epsilon < 1 / 100 →
            ∃ etaMax : ℝ,
              0 < etaMax ∧
              etaMax ≤ epsilon ∧
              ∀ steps : ℕ,
                (1 - epsilon ^ 2) ^ steps ≤ epsilon ^ 2 →
                ∀ schedule :
                    GridOSEffectiveLossScheduleData
                      epsilon etaMax steps,
                  ∀ base : ℕ,
                    2 ≤ base →
                      Nonempty
                        (GridOSFiniteStepScheduleData
                          epsilon etaMax steps schedule base)

/--
Build the direct common finite step oracle from its finite arithmetic,
bounded one-scale, dichotomy, and ready-state producers.
-/
def GridOSFiniteStepScheduleStatement : Prop :=
  GridOSFiniteThresholdStatement →
    GridOSLastStepTerminalStatement →
      GridOSBoundedOneScaleInput →
        GridOSStateDichotomyInput →
          GridOSTransitionReadyStateStatement →
            GridOSFiniteStepScheduleInput

end Kakeya.Assouad
