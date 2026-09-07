import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridPartitionTreeStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterTerminalCellRepresentativesStatement

/-!
# Singleton terminal cells for terminal-cell representatives

The representative set has exactly one point for each occupied terminal grid
index.  Therefore every occupied terminal cell in its floor-grid partition is
a singleton.
-/

namespace Kakeya.Assouad

/-- Every terminal grid cell of the representative parameter set has one point. -/
def TubeParameterRepresentativeTerminalSingletonStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ family : Kakeya.Streamlined.TubeFamily delta,
      ∀ active : Finset (Fin family.card),
        ∀ base levels : ℕ,
          ∀ regularized :
              TubeParameterTerminalCellFiberRegularizationData
                family active base levels,
            ∀ representatives :
                TubeParameterTerminalCellRepresentativesData regularized,
              ∀ cell ∈
                  tubeParameterGridPartition
                    base levels representatives.parameters,
                cell.card = 1

end Kakeya.Assouad
