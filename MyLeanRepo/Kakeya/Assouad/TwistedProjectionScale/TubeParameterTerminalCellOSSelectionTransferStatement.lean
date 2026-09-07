import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SelectedScaleStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterTerminalCellOSLiftStatement

/-!
# Density and cardinality transfer to the terminal-cell OS selection

Per-tube fullness is hereditary under selecting tube indices: every surviving
tube still carries the same shaded-mass fraction of its common tube volume.

The two finite cardinality losses are used only to normalize hereditary
parameter Frostman control:

* one dyadic class of complete terminal-cell fibers;
* one locally bounded OS branching refinement of the representative tree.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Combined terminal-cell fiber and OS branching cardinality loss. -/
def tubeParameterTerminalCellOSLoss
    (activeCard base levels : ℕ) : ENNReal :=
  (Nat.log 2 activeCard + 1 : ENNReal) *
    (2 : ENNReal) *
      ((((2 * (Nat.log 2 ((base + 1) ^ 4) + 1)) ^ levels :
        ℕ)) : ENNReal)

/--
Direct callable density and indexed-cardinality transfer.
-/
def TubeParameterTerminalCellOSSelectionTransferInput : Prop :=
  ∀ {delta : ℝ},
      0 < delta →
      delta ≤ 1 →
      ∀ family : Kakeya.Streamlined.TubeFamily delta,
        ∀ shading : Kakeya.Streamlined.TubeShading family,
          ∀ lambda q : ENNReal,
            HasPerTubeMass shading
              (lambda * Kakeya.deltaTubeVolume delta) →
            q * family.toBodyFamily.mass ≤ shading.mass →
            let active := positiveMassIndices shading
            ∀ base levels : ℕ,
              ∀ terminal :
                  TubeParameterTerminalCellFiberRegularizationData
                    family active base levels,
                ∀ representatives :
                    TubeParameterTerminalCellRepresentativesData terminal,
                  ∀ uniform :
                      TubeParameterTerminalCellOSLiftData
                        terminal representatives,
                    let selectedFamily :=
                      selectedTubeFamily family uniform.selected
                    let selectedShading :=
                      selectedTubeShading shading uniform.selected
                    let loss :=
                      tubeParameterTerminalCellOSLoss
                        active.card base levels
                    selectedFamily.Nonempty ∧
                      selectedShading.IsLambdaDense lambda ∧
                      (q * loss⁻¹) * family.enncard ≤
                        selectedFamily.enncard

/--
Expose the direct selection-transfer producer from the tube-volume scaling
leaf.
-/
def TubeParameterTerminalCellOSSelectionTransferStatement : Prop :=
  TubeVolumeScalingStatement →
    TubeParameterTerminalCellOSSelectionTransferInput

end Kakeya.Assouad
