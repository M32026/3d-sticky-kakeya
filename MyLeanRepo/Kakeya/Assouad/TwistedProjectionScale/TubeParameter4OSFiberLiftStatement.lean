import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameter4FiberRegularizationStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridPartitionTreeStatement

/-!
# Lift OS-uniform parameter points back to complete indexed tube fibers

After exact four-parameter fibers have been dyadically regularized, apply the
Orponen--Shmerkin tree pruning to the distinct parameter image.  The retained
tube indices are then all indices in every retained parameter fiber, not one
arbitrary representative.

This is the paper's multiset-compatible replacement for assuming that the
indexed parameter map is injective.
-/

noncomputable section

namespace Kakeya.Assouad

/--
An OS-uniform set of distinct four-parameter points together with all indexed
tubes in their complete regularized fibers.
-/
structure TubeParameter4OSFiberLiftData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {active : Finset (Fin family.card)}
    (regularized : TubeParameter4FiberRegularizationData family active)
    (base levels : ℕ) where
  selected : Finset (Fin family.card)
  selected_nonempty : selected.Nonempty
  selected_subset : selected ⊆ regularized.selected
  selectedParameters : DiscreteSet 4
  selectedParameters_eq :
    selectedParameters =
      selected.image indexedTubeParameterPoint4
  selectedParameters_nonempty : selectedParameters.Nonempty
  selected_complete_fibers :
    ∀ index ∈ regularized.selected,
      indexedTubeParameterPoint4 index ∈ selectedParameters →
        index ∈ selected
  fiber_lower :
    ∀ point ∈ selectedParameters,
      regularized.fiberMultiplicity ≤
        (selected.filter fun index =>
          indexedTubeParameterPoint4 index = point).card
  fiber_upper :
    ∀ point ∈ selectedParameters,
      (selected.filter fun index =>
        indexedTubeParameterPoint4 index = point).card <
          2 * regularized.fiberMultiplicity
  retention :
    (regularized.selected.card : ℝ) ≤
      2 *
        (2 * (Nat.log 2 ((base + 1) ^ 4) + 1) : ℝ) ^ levels *
          (selected.card : ℝ)
  branchExponent : Fin levels → ℕ
  branch_bound :
    ∀ level : Fin levels,
      2 ^ branchExponent level ≤ (base + 1) ^ 4
  branch_uniform :
    let ambientParameters :=
      indexedTubeParameterSet4 regularized.selected
    let partition : ℕ → Finset (Finset (Point 4)) :=
      fun level =>
        tubeParameterGridPartition base level ambientParameters
    ∀ level : Fin levels,
      ∀ parent ∈ partition level,
        (selectedParameters ∩ parent).Nonempty →
          (occupiedPartitionChildren
            selectedParameters partition level parent).card =
              2 ^ branchExponent level

/--
Run the closed 4D grid and generic OS refinement on the distinct parameter
image, then lift every retained point to its complete regularized index fiber.
-/
def TubeParameter4OSFiberLiftStatement : Prop :=
  TubeParameterGridPartitionTreeStatement →
    OSBranchingUniformRefinementStatement →
      ∀ {delta : ℝ},
        ∀ family : Kakeya.Streamlined.TubeFamily delta,
          ∀ active : Finset (Fin family.card),
            ∀ regularized :
                TubeParameter4FiberRegularizationData family active,
              ∀ base levels : ℕ,
                2 ≤ base →
                ∀ fineScale : ℝ,
                  0 < fineScale →
                  (indexedTubeParameterSet4
                      regularized.selected).IsDeltaSeparated
                    fineScale →
                  4 < fineScale * (base ^ levels : ℝ) →
                    Nonempty
                      (TubeParameter4OSFiberLiftData
                        regularized base levels)

end Kakeya.Assouad
