import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSScaleGrowthStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSWindowBudgetDichotomyStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridCoarseningLevelStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridOSStateTransitionStatements

/-!
# Terminal-or-transition dichotomy for one corrected grid OS state

The analytic one-scale theorem has already selected a radius `rho` and a
same-family subshading.  This boundary performs only the finite-tree and
fixed-constant bookkeeping needed to continue the iteration:

* compare `rho` with the global terminal threshold `delta ^ epsilon²`;
* absorb `6 * currentScale` below the selected radius;
* in the initial terminal-grid state, absorb the extra factor `base` in the
  terminal mesh bound;
* choose a no-finer grid level with mesh at most `rho / 6`;
* use the corrected two-sided window budget;
* invoke the frozen corrected state transition.

No Tube-Wolff-to-parameter-Frostman implication is asserted here.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Every sufficiently small corrected state is either terminal at the global
threshold or admits one corrected transition on the same frozen grid tree.
-/
def GridOSStateDichotomyInput : Prop :=
  ∀ epsilon eta : ℝ,
            0 < epsilon →
            epsilon < 1 →
            0 < eta →
            4 * eta < epsilon ^ 2 →
            ∀ base : ℕ,
              2 ≤ base →
                ∃ scale₀ : ℝ,
                  0 < scale₀ ∧
                  scale₀ ≤ 1 ∧
                  ∀ {delta : ℝ},
                    0 < delta →
                    ∀ source :
                        Kakeya.Streamlined.TubeFamily delta,
                      ∀ active : Finset (Fin source.card),
                        ∀ levels : ℕ,
                          ((base ^ levels : ℝ)⁻¹) <
                              (base : ℝ) * delta →
                          ∀ terminal :
                              TubeParameterTerminalCellFiberRegularizationData
                                source active base levels,
                            ∀ representatives :
                                TubeParameterTerminalCellRepresentativesData
                                  terminal,
                              ∀ uniform :
                                  TubeParameterTerminalCellOSLiftData
                                    terminal representatives,
                                ∀ {currentScale : ℝ},
                                  ∀ {currentLevel : ℕ},
                                    ∀ currentFamily :
                                        Kakeya.Streamlined.TubeFamily
                                          currentScale,
                                      ∀ currentShading :
                                          Kakeya.Streamlined.TubeShading
                                            currentFamily,
                                        ∀ state :
                                            TubeParameterGridOSStateData
                                              terminal representatives uniform
                                              currentScale currentLevel
                                              currentFamily currentShading,
                                          delta ≤ currentScale →
                                          currentScale ≤ scale₀ →
                                          ∀ fineShading :
                                              Kakeya.Streamlined.TubeShading
                                                currentFamily,
                                            IsSubshading
                                              fineShading currentShading →
                                            IsInSlopeWindow fineShading →
                                            fineShading.IsLambdaDense
                                              (Kakeya.realRpowENN
                                                currentScale (4 * eta)) →
                                            ∀ rho : ℝ,
                                              Real.rpow currentScale
                                                  (1 - epsilon ^ 2) < rho →
                                              rho ≤ 1 / 8 →
                                              ∀ f : SlopeFunction,
                                                f.IsNonsingular →
                                                f 0 = 0 →
                                                MeasureTheory.volume
                                                    (twistedUnion
                                                      fineShading f) ≥
                                                  Kakeya.realRpowENN
                                                      (currentScale / rho)
                                                      epsilon *
                                                    MeasureTheory.volume
                                                      (Metric.cthickening rho
                                                        (twistedUnion
                                                          fineShading f)) →
                                                  Real.rpow delta
                                                      (epsilon ^ 2) ≤ rho ∨
                                                    ∃ nextLevel : ℕ,
                                                      Nonempty
                                                        (TubeParameterGridOSStateTransitionData
                                                          state fineShading rho
                                                            nextLevel f epsilon
                                                            (Kakeya.realRpowENN
                                                              currentScale
                                                              (4 * eta)))

/--
Assemble the direct terminal-or-transition producer from the corrected
arithmetic, level-selection, and transition producers.
-/
def GridOSStateDichotomyStatement : Prop :=
  GridOSScaleGrowthStatement →
    GridOSWindowBudgetDichotomyStatement →
      TubeParameterGridCoarseningLevelStatement →
        TubeParameterGridOSStateTransitionInput →
          GridOSStateDichotomyInput

end Kakeya.Assouad
