import MyLeanRepo.Kakeya.Streamlined.RestrictDistinctDilatedTubeCover

/-!
# Restrict a distinct dilated tube cover
-/

namespace Kakeya.Streamlined

theorem restrict_distinct_dilated_tube_cover_main :
    RestrictDistinctDilatedTubeCoverStatement := by
  intro δ ρ A fine coarse hcoarse P S
  rcases restrict_dilated_tube_cover_main (P := P) (S := S) with ⟨C, Q, h_compat⟩
  have h_distinct : C.family.IsEssentiallyDistinct := C.isEssentiallyDistinct hcoarse
  exact ⟨C, h_distinct, Q, h_compat⟩

end Kakeya.Streamlined
