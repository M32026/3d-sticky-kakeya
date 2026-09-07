import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.FullWindowLiftedDensityAbsorptionStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridOSFourBlockPackageStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.UniformFourBlockParameterFrostmanTransferStatement

/-!
# One corrected transition on the delta-grid parameter OS tree

This is the nonterminal state transition used in the finite Section 7
iteration.  It never refines to exact parameter-point singletons.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Raw coarse density after the uniform four-block Fubini transfer. -/
def gridOSRawDensity (lambda : ENNReal) : ENNReal :=
  ENNReal.ofReal (1 / 800 : ℝ) * lambda

/-- Density after clipping both sides of the slope window. -/
def gridOSNextDensity (lambda : ENNReal) : ENNReal :=
  (2 : ENNReal)⁻¹ * gridOSRawDensity lambda

/-- Complete output of one corrected nonterminal transition. -/
structure TubeParameterGridOSStateTransitionData
    {delta : ℝ}
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
    (state :
      TubeParameterGridOSStateData
        terminal representatives uniform currentScale currentLevel
          currentFamily currentShading)
    (fineShading : Kakeya.Streamlined.TubeShading currentFamily)
    (rho : ℝ)
    (nextLevel : ℕ)
    (f : SlopeFunction)
    (epsilon : ℝ)
    (fineDensity : ENNReal) where
  package :
    TubeParameterGridOSFourBlockPackageData
      state fineShading rho nextLevel
  rawShading :
    Kakeya.Streamlined.TubeShading package.blocks.coarse
  rawShading_eq :
    rawShading = package.blocks.exactShading rho
  nextShading :
    Kakeya.Streamlined.TubeShading package.blocks.coarse
  nextShading_eq :
    nextShading = slabRestriction rawShading (-1) 1
  fine_subshading :
    IsSubshading fineShading currentShading
  raw_union_subset :
    rawShading.union ⊆
      Metric.cthickening rho fineShading.union
  windowed_exact :
    IsWindowedExactRelationInducedShading
      package.blocks.relation fineShading nextShading rho
  nextState :
    TubeParameterGridOSStateData
      terminal representatives uniform rho nextLevel
        package.blocks.coarse nextShading
  next_mesh_control :
    6 * ((base ^ nextLevel : ℝ)⁻¹) ≤ rho
  next_density_eq :
    nextState.densityConstant = gridOSNextDensity fineDensity
  next_parameter_eq :
    nextState.parameterConstant = 8 * state.parameterConstant
  next_twisted_subset :
    twistedUnion nextShading f ⊆
      Metric.cthickening (40 * rho)
        (twistedUnion fineShading f)
  next_twisted_volume :
    MeasureTheory.volume (twistedUnion nextShading f) ≤
      (6889 : ENNReal) *
        MeasureTheory.volume
          (Metric.cthickening rho
            (twistedUnion fineShading f))
  telescoping_step :
    Kakeya.realRpowENN (currentScale / rho) epsilon *
        MeasureTheory.volume (twistedUnion nextShading f) ≤
      (6889 : ENNReal) *
        MeasureTheory.volume (twistedUnion currentShading f)

/--
Direct callable producer for one corrected state transition.
-/
def TubeParameterGridOSStateTransitionInput : Prop :=
  ∀ {delta : ℝ},
                ∀ source : Kakeya.Streamlined.TubeFamily delta,
                  ∀ active : Finset (Fin source.card),
                    ∀ base levels : ℕ,
                      2 ≤ base →
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
                                    Kakeya.Streamlined.TubeFamily currentScale,
                                  ∀ currentShading :
                                      Kakeya.Streamlined.TubeShading
                                        currentFamily,
                                    ∀ state :
                                        TubeParameterGridOSStateData
                                          terminal representatives uniform
                                          currentScale currentLevel
                                          currentFamily currentShading,
                                      ∀ fineShading :
                                          Kakeya.Streamlined.TubeShading
                                            currentFamily,
                                        IsSubshading
                                          fineShading currentShading →
                                        IsInSlopeWindow fineShading →
                                        ∀ fineDensity : ENNReal,
                                          fineDensity ≠ 0 →
                                          fineDensity ≠ ⊤ →
                                          fineShading.IsLambdaDense
                                            fineDensity →
                                          ∀ rho : ℝ,
                                            0 < rho →
                                            rho ≤ 1 / 8 →
                                            6 * currentScale ≤ rho →
                                            ∀ nextLevel : ℕ,
                                              nextLevel ≤ currentLevel →
                                              let mesh :=
                                                (base ^ nextLevel : ℝ)⁻¹
                                              6 * mesh ≤ rho →
                                              ENNReal.ofReal (400 * rho) ≤
                                                gridOSRawDensity fineDensity →
                                              ∀ f : SlopeFunction,
                                                f.IsNonsingular →
                                                f 0 = 0 →
                                                ∀ epsilon : ℝ,
                                                  0 < epsilon →
                                                  MeasureTheory.volume
                                                      (twistedUnion
                                                        fineShading f) ≥
                                                    Kakeya.realRpowENN
                                                        (currentScale / rho)
                                                        epsilon *
                                                      MeasureTheory.volume
                                                        (Metric.cthickening
                                                          rho
                                                          (twistedUnion
                                                            fineShading f)) →
                                                  Nonempty
                                                    (TubeParameterGridOSStateTransitionData
                                                      state fineShading rho
                                                        nextLevel f epsilon
                                                        fineDensity)

/--
Assemble the direct transition producer from the separated finite-tree,
four-block, density, nonconcentration, and projection leaves.
-/
def TubeParameterGridOSStateTransitionStatement : Prop :=
  TubeParameterGridOSFourBlockPackageInput →
    UniformFourBlockRelationDensityInput →
      UniformFourBlockParameterFrostmanTransferStatement →
        FullWindowLiftedDensityAbsorptionStatement →
          TwistedProjectionRelationInducedShadingFromParametersStatement →
            PlanarThickeningFortyVolumeStatement →
              TubeParameterGridOSStateTransitionInput

end Kakeya.Assouad
