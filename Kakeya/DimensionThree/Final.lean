import Kakeya.DimensionThree.KakeyaConjecture
import MyLeanRepo.Kakeya.Integration.CompetitorSticky

/-!
# The unconditional three-dimensional Kakeya theorem

This legacy file is the compatibility boundary between the modular consumer
chain and the proved competitor Sticky theorem.
-/

/-- Every Kakeya set in three-dimensional Euclidean space has Hausdorff
dimension three. -/
theorem KakeyaDimensionThree : KakeyaSetConjecture 3 := by
  apply KakeyaDimensionThree_of_stickyFrostmanEstimate
  exact Kakeya.Integration.stickyFrostmanEstimate_of_finrank_three (by simp)
