import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridPartitionTreeStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterTerminalCellRepresentativesStatement

/-!
# Atomic grid tree on terminal-cell parameter representatives

The representative set contains exactly one actual parameter point from each
occupied terminal grid cell.  Therefore the ordinary nested floor-grid
partitions are atomic at `levels` without any lower bound on the exact
off-diagonal parameter distance.
-/

namespace Kakeya.Assouad

/--
The representative parameter set has a locally bounded atomic grid tree.
-/
def TubeParameterRepresentativeGridTreeStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ family : Kakeya.Streamlined.TubeFamily delta,
      ∀ active : Finset (Fin family.card),
        ∀ base levels : ℕ,
          2 ≤ base →
          ∀ regularized :
              TubeParameterTerminalCellFiberRegularizationData
                family active base levels,
            ∀ representatives :
                TubeParameterTerminalCellRepresentativesData regularized,
              let parameters := representatives.parameters
              let partition : ℕ → Finset (Finset (Point 4)) :=
                fun level =>
                  tubeParameterGridPartition base level parameters
              (∀ level ≤ levels,
                (∀ cell ∈ partition level,
                  cell.Nonempty ∧ cell ⊆ parameters) ∧
                (∀ cell₁ ∈ partition level,
                  ∀ cell₂ ∈ partition level,
                    cell₁ ≠ cell₂ → Disjoint cell₁ cell₂) ∧
                parameters ⊆ Finset.biUnion (partition level) id) ∧
              (∀ cell ∈ partition levels, cell.card = 1) ∧
              (∀ level, level < levels →
                ∀ child ∈ partition (level + 1),
                  ∃ parent ∈ partition level, child ⊆ parent) ∧
              ∀ level, level < levels →
                ∀ parent ∈ partition level,
                  (partitionChildren partition level parent).card ≤
                    (base + 1) ^ 4

end Kakeya.Assouad
