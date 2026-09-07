import MyLeanRepo.Kakeya.Assouad.Multiplicity.MassRetention

/-! WZ2 Section 6 per-tube fullness pruning. -/

namespace Kakeya.Assouad

theorem per_tube_mass_pruning :
    PerTubeMassPruningStatement := by
  intro delta eta hdelta hdelta_one heta F Y hY_dense
  exact mass_retention_under_pruning_full hdelta hdelta_one (heta := heta) hY_dense

end Kakeya.Assouad
