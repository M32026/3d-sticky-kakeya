import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridPartitionTreeStatement

/-!
# Coordinate diameter of one four-parameter floor-grid cell

Two points in one occupied level-`k` parameter cell have equal coordinatewise
floors after multiplication by `base^k`.  Hence every coordinate differs by
strictly less than the grid width `(base^k)⁻¹`.
-/

namespace Kakeya.Assouad

/-- Coordinatewise diameter bound for one occupied 4D tube-parameter cell. -/
def TubeParameterGridCellDiameterStatement : Prop :=
  ∀ base level : ℕ,
    0 < base →
      ∀ parameters : DiscreteSet 4,
        ∀ cell ∈ tubeParameterGridPartition base level parameters,
          ∀ first ∈ cell,
            ∀ second ∈ cell,
              ∀ coordinate : Fin 4,
                |first coordinate - second coordinate| <
                  (base ^ level : ℝ)⁻¹

end Kakeya.Assouad
