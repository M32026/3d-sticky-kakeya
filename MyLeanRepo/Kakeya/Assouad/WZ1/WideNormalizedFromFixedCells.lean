import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedCellNormalizationStatements

/-!
# Assemble wide normalization from fixed-cell leaves
-/

namespace Kakeya.Assouad

theorem wz1_proposition8_9_wide_normalized_from_fixed_cells :
    WZ1Proposition8_9WideNormalizedFromFixedCellsStatement := by
  intro hSelect hNormalize hTransport hCoarse
  have hFixed : WZ1Proposition8_9WideFixedCellProducer :=
    hSelect hCoarse
  have hCore : WZ1Proposition8_9WideNormalizedCoreProducer :=
    hNormalize hFixed
  exact hTransport hCoarse hFixed hCore

end Kakeya.Assouad
