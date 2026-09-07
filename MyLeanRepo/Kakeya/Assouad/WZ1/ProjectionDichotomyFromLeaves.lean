import MyLeanRepo.Kakeya.Assouad.WZ1.AnisotropicFrostmanRescaling
import MyLeanRepo.Kakeya.Assouad.WZ1.HypergraphRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.LineNonconcentrationProjection
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFinalStatements

/-!
# Assemble WZ1 Theorem 22 from its final paper leaves
-/

namespace Kakeya.Assouad

theorem wz1_tripartite_hypergraph_refinement :
    WZ1TripartiteHypergraphRefinementStatement := by
  intro A H hH epsilon hepsilon_pos hepsilon_lt
  exact
    wz1_hypergraph_refinement A H hH epsilon
      hepsilon_pos hepsilon_lt

theorem wz1_projection_dichotomy_from_leaves :
    WZ1ProjectionDichotomyFromLeavesStatement := by
  intro hWellSeparated hRemoveSeparation hStrip hOSW
  have hSeparated : WZ1WellSeparatedProjectionConclusion :=
    hWellSeparated
      wz1_tripartite_hypergraph_refinement
      wz1_anisotropic_frostman_rescaling
      wz1_line_nonconcentration_projection
      hStrip hOSW
  exact
    hRemoveSeparation wz1_tripartite_hypergraph_refinement hSeparated

end Kakeya.Assouad
