import MyLeanRepo.Kakeya.Cinematic.Section5.SingletonClusterCoarseCardinalityWitnessInputs

/-!
# Singleton cluster coarse cardinality from a witness subfamily
-/

namespace Kakeya.Cinematic

theorem singleton_cluster_coarse_cardinality_witness :
    SingletonClusterCoarseCardinalityWitnessStatement := by
  intro delta t witness coarseCard H leftCenter rightCenter radius tangency coefficient
    hwitness_nonempty hcounts hcoefficient hbound
  set W : FiniteFunctionFamily := H.cluster leftCenter radius with hW_def
  set B : FiniteFunctionFamily := H.cluster rightCenter radius with hB_def
  set x : ℝ := RectangleFamily.bipartiteNormalizedCount W B 1 1 with hx_def
  set y : ℝ := 2 * (H.card : ℝ) with hy_def
  have hWsub : W.carrier ⊆ H.carrier := by
    exact Set.inter_subset_left
  have hBsub : B.carrier ⊆ H.carrier := by
    exact Set.inter_subset_left
  have hlower : 2 ≤ x :=
    RectangleFamily.two_le_bipartiteNormalizedCount_of_tangentCounts
      (hR := hwitness_nonempty) (hmu := by norm_num) (hnu := by norm_num)
      (hcounts := hcounts)
  have hupper : x ≤ y :=
    bipartiteNormalizedCount_one_le_ambient H W B hWsub hBsub
  have hone : 1 ≤ x := by
    linarith
  have hmono :
      Real.rpow x (3 / 2 : ℝ) * Real.log x ≤
      Real.rpow y (3 / 2 : ℝ) * Real.log y :=
    rpow_log_mono hone hupper
  have hscaled :
      coefficient * (Real.rpow x (3 / 2 : ℝ) * Real.log x) ≤
      coefficient * (Real.rpow y (3 / 2 : ℝ) * Real.log y) :=
    mul_le_mul_of_nonneg_left hmono hcoefficient
  have hmain : (coarseCard : ℝ) ≤
      coefficient * (Real.rpow y (3 / 2 : ℝ) * Real.log y) :=
    hbound.trans hscaled
  simpa [hy_def, mul_assoc] using hmain

end Kakeya.Cinematic
