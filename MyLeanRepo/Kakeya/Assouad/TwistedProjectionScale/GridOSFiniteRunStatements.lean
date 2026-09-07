import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSFiniteStepScheduleStatements

/-!
# Execute the finite corrected grid OS recursion

The dependent tube families and grid states change at each transition.  The
final projection argument only needs their numerical trace:

* the scale at each state;
* the twisted-projection volume at each state;
* one `6889`-loss transition inequality between consecutive entries;
* a terminal one-scale thickening inequality at the last state.

This module packages exactly that trace.  Intermediate dependent states remain
internal to the recursion proof.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Numerical terminal trace produced from one ready state. -/
structure GridOSTerminalTraceData
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
  transitionCount : ℕ
  final_index_le : index + transitionCount ≤ steps
  scale : ℕ → ℝ
  projectedVolume : ℕ → ENNReal
  scale_zero : scale 0 = currentScale
  volume_zero :
    projectedVolume 0 =
      MeasureTheory.volume (twistedUnion currentShading f)
  scale_pos :
    ∀ traceIndex : ℕ,
      traceIndex ≤ transitionCount →
        0 < scale traceIndex
  transition_step :
    ∀ traceIndex : ℕ,
      traceIndex < transitionCount →
        Kakeya.realRpowENN
            (scale traceIndex / scale (traceIndex + 1)) epsilon *
          projectedVolume (traceIndex + 1) ≤
            (6889 : ENNReal) * projectedVolume traceIndex
  terminalRho : ℝ
  terminalRho_pos : 0 < terminalRho
  terminal_threshold :
    Real.rpow delta (epsilon ^ 2) ≤ terminalRho
  terminalSet : Set Point2
  terminalSet_nonempty : terminalSet.Nonempty
  terminal_step :
    Kakeya.realRpowENN
        (scale transitionCount / terminalRho) epsilon *
      MeasureTheory.volume
        (Metric.cthickening terminalRho terminalSet) ≤
      projectedVolume transitionCount

/--
Execute the total finite step oracle from any scheduled ready state until its
terminal branch is reached.
-/
def GridOSFiniteRunStatement : Prop :=
  ∀ {delta epsilon etaMax : ℝ},
    0 < delta →
    delta < 1 →
    0 < epsilon →
    epsilon < 1 →
    ∀ {steps : ℕ},
      ∀ schedule :
          GridOSEffectiveLossScheduleData epsilon etaMax steps,
        ∀ base : ℕ,
          2 ≤ base →
          ∀ finiteSteps :
              GridOSFiniteStepScheduleData
                epsilon etaMax steps schedule base,
            Real.rpow delta (epsilon ^ 2) ≤ finiteSteps.scaleCap →
            ∀ source : Kakeya.Streamlined.TubeFamily delta,
              ∀ active : Finset (Fin source.card),
                ∀ levels : ℕ,
                  ((base ^ levels : ℝ)⁻¹) <
                    (base : ℝ) * delta →
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
                                    Kakeya.Streamlined.TubeShading
                                      currentFamily,
                                  ∀ state :
                                      TubeParameterGridOSStateData
                                        terminal representatives uniform
                                        currentScale currentLevel
                                        currentFamily currentShading,
                                    GridOSReadyStateData
                                      schedule index state →
                                    delta ≤ currentScale →
                                    currentScale ≤ finiteSteps.scaleCap →
                                    Real.rpow delta
                                        ((1 - epsilon ^ 2) ^ index) ≤
                                      currentScale →
                                    ∀ f : SlopeFunction,
                                      f.IsNonsingular →
                                      f 0 = 0 →
                                        Nonempty
                                          (GridOSTerminalTraceData
                                            schedule index state f)

end Kakeya.Assouad
