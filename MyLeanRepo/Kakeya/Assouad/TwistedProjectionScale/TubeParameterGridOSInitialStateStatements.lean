import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridOSStateStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridParameterSelectionStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterTerminalCellOSSelectionTransferStatement

/-!
# Initial state on the corrected delta-grid parameter tree

The initial state uses a terminal parameter mesh comparable to the fine tube
radius.  It never separates arbitrarily close exact parameter points.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Density left by the initial per-tube pruning. -/
def terminalCellInitialDensity (delta eta : ℝ) : ENNReal :=
  (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta

/-- Complete output of corrected initial-state preparation. -/
structure TubeParameterGridOSInitialStateData
    {delta eta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (shading : Kakeya.Streamlined.TubeShading family)
    (sourceConstant : ENNReal) where
  base : ℕ
  base_ge_three : 3 ≤ base
  levels : ℕ
  mesh_lower :
    delta ≤ ((base ^ levels : ℝ)⁻¹)
  mesh_upper :
    ((base ^ levels : ℝ)⁻¹) < (base : ℝ) * delta
  pruned : Kakeya.Streamlined.TubeShading family
  pruned_subshading : IsSubshading pruned shading
  pruned_mass :
    terminalCellInitialDensity delta eta *
        family.toBodyFamily.mass ≤
      pruned.mass
  pruned_full :
    HasPerTubeMass pruned
      (terminalCellInitialDensity delta eta *
        Kakeya.deltaTubeVolume delta)
  active : Finset (Fin family.card)
  active_eq : active = positiveMassIndices pruned
  terminal :
    TubeParameterTerminalCellFiberRegularizationData
      family active base levels
  representatives :
    TubeParameterTerminalCellRepresentativesData terminal
  uniform :
    TubeParameterTerminalCellOSLiftData terminal representatives
  selectedFamily : Kakeya.Streamlined.TubeFamily delta
  selectedFamily_eq :
    selectedFamily = selectedTubeFamily family uniform.selected
  selectedShading :
    Kakeya.Streamlined.TubeShading selectedFamily
  selectedShading_eq :
    HEq selectedShading
      (selectedTubeShading pruned uniform.selected)
  loss : ENNReal
  loss_eq :
    loss = tubeParameterTerminalCellOSLoss active.card base levels
  loss_bound :
    loss ≤ Kakeya.realRpowENN delta (-eta)
  cardinalityFraction : ENNReal
  cardinalityFraction_eq :
    cardinalityFraction =
      terminalCellInitialDensity delta eta * loss⁻¹
  cardinalityFraction_ne_zero : cardinalityFraction ≠ 0
  cardinalityFraction_ne_top : cardinalityFraction ≠ ⊤
  selected_cardinality :
    cardinalityFraction * family.enncard ≤ selectedFamily.enncard
  parameterConstant : ENNReal
  parameterConstant_eq :
    parameterConstant = sourceConstant * cardinalityFraction⁻¹
  state :
    TubeParameterGridOSStateData
      terminal representatives uniform delta levels
        selectedFamily selectedShading
  state_density_eq :
    state.densityConstant = terminalCellInitialDensity delta eta
  state_parameter_eq :
    state.parameterConstant = parameterConstant

/-- Direct callable producer for the corrected terminal initial state. -/
def TubeParameterGridOSInitialStateInput : Prop :=
  ∀ eta : ℝ,
                  0 < eta →
                    ∃ base : ℕ,
                      3 ≤ base ∧
                      ∃ delta₀ : ℝ,
                        0 < delta₀ ∧
                        delta₀ < 1 ∧
                        ∀ delta : ℝ,
                          0 < delta →
                          delta ≤ delta₀ →
                          ∀ family : Kakeya.Streamlined.TubeFamily delta,
                            family.Nonempty →
                            IsInVerticalChart family →
                            (∀ index : Fin family.card,
                              |(tubeParams index).a| ≤ 12 ∧
                                |(tubeParams index).b| ≤ 12 ∧
                                |(tubeParams index).c| ≤ 2 ∧
                                |(tubeParams index).d| ≤ 2) →
                            family.enncard ≤
                              Kakeya.realRpowENN delta (-3) →
                            ∀ sourceConstant : ENNReal,
                              1 ≤ sourceConstant →
                              sourceConstant ≠ ⊤ →
                              TubeParameterFrostmanBound
                                family sourceConstant →
                              ∀ shading :
                                  Kakeya.Streamlined.TubeShading family,
                                shading.IsLambdaDense
                                  (Kakeya.realRpowENN delta eta) →
                                IsInSlopeWindow shading →
                                  ∃ initial :
                                      TubeParameterGridOSInitialStateData
                                        (eta := eta) family shading
                                          sourceConstant,
                                    initial.base = base

/-- Assemble the direct initial-state producer from its closed leaves. -/
def TubeParameterGridOSInitialStateStatement : Prop :=
  TubeParameterGridParameterSelectionStatement →
    PerTubeMassPruningStatement →
      TubeParameterTerminalCellFiberRegularizationStatement →
        TubeParameterTerminalCellRepresentativesStatement →
          TubeParameterTerminalCellOSLiftInput →
            TubeParameterTerminalCellOSSelectionTransferInput →
              SelectedTubeNonconcentrationTransferStatement →
                TubeParameterGridOSInitialStateInput

end Kakeya.Assouad
