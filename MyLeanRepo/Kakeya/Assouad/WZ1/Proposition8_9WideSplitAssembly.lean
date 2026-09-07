import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9WideSplitStatements

/-!
# Mechanical assembly of the split wide branch
-/

namespace Kakeya.Assouad

theorem wz1_proposition8_9_wide_split_assembly :
    WZ1Proposition8_9WideSplitAssemblyStatement := by
  intro hCoarse hFromCoarse
  exact hFromCoarse hCoarse

end Kakeya.Assouad
