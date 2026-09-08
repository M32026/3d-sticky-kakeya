import MyLeanRepo.Kakeya.Streamlined.DistinctDilatedCoverUniformization

/-!
# Distinct one-scale uniformization of a dilated tube cover
-/

namespace Kakeya.Streamlined

theorem assigned_distinct_dilated_cover_uniformization_main :
    AssignedDistinctDilatedCoverUniformizationStatement := by
  intro δ ρ A fine coarse hcoarse P Y hY
  have h_main :=
    assigned_dilated_cover_uniformization_main (P := P) (Y := Y) hY
  rcases h_main with ⟨S, hS_nonempty, h_mass, C, Q, hQ_uniform⟩
  have hC_distinct : C.family.IsEssentiallyDistinct :=
    C.isEssentiallyDistinct hcoarse
  exact ⟨S, hS_nonempty, h_mass, C, hC_distinct, Q, hQ_uniform⟩

/-- Legacy compatibility theorem for internal assigned-cell consumers. -/
theorem legacy_distinct_dilated_cover_uniformization_main :
    LegacyDistinctDilatedCoverUniformizationStatement :=
  assigned_distinct_dilated_cover_uniformization_main

end Kakeya.Streamlined
