import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridPartitionTree
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterRepresentativeGridTreeFromSingletonStatement

/-!
WZ2 Proposition 7.1: assemble the representative parameter grid tree from
the terminal singleton leaf and existing public grid geometry.
-/

namespace Kakeya.Assouad

theorem tube_parameter_representative_grid_tree_from_singleton :
    TubeParameterRepresentativeGridTreeFromSingletonStatement := by
  intro hSingleton delta family active base levels hbase regularized
    representatives
  dsimp only
  refine ⟨?_, hSingleton family active base levels regularized
    representatives, ?_, ?_⟩
  · intro level _hlevel
    refine ⟨?_, ?_, tubeParameterGridPartition_cover⟩
    · intro cell hcell
      exact tubeParameterGridPartition_cell_nonempty_subset hcell
    · intro cell₁ hcell₁ cell₂ hcell₂ hne
      exact tubeParameterGridPartition_disjoint hcell₁ hcell₂ hne
  · intro level _hlevel child hchild
    exact tubeParameterGridPartition_nesting (by omega) hchild
  · intro level _hlevel parent hparent
    exact
      (tube_parameter_grid_partition_child_bound hbase parent hparent).trans
        (Nat.pow_le_pow_left (by omega) 4)

end Kakeya.Assouad
