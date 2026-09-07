import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet.SmallDeltaTestNet

/-!
Paper reference:
`reference/streamlined_kakeya_2601.14411/appendix-a-appendix-probability-lemmas.md`,
the polynomial-size discretization of relevant convex test bodies in the
random-motion union bound.
-/

namespace Kakeya.Streamlined

theorem tube_density_test_net_main :
    RandomTranslation.TubeDensityTestNetStatement := by
  use 200, by norm_num
  use (10^7 : ENNReal)
  constructor
  · norm_num
  constructor
  · exact ENNReal.coe_ne_top
  intro δ hδ hδ_le_one
  by_cases h_large : δ ≥ 1 / 2
  · -- Large δ case: single test set B(0,20)
    have hL_big_large : (64000 : ENNReal) ≤ (10^7 : ENNReal) := by norm_num
    let net := large_delta_test_net hδ hδ_le_one h_large (10^7 : ENNReal)
      (by norm_num) ENNReal.coe_ne_top hL_big_large
    refine ⟨net, ?_, ?_⟩
    · simpa [net, large_delta_test_net] using le_refl (10^7 : ENNReal)
    · have h1 : (net.testSets.card : ℝ) = 1 := by
        simp [net, large_delta_test_net] <;> norm_num
      rw [h1]
      have h3 : 1 ≤ 1 / δ := by
        apply one_le_one_div <;> linarith
      have h4 : (1 : ℝ) ≤ (1 / δ) ^ 200 := by
        calc (1 : ℝ) = 1 ^ 200 := by norm_num
          _ ≤ (1 / δ) ^ 200 := by gcongr <;> linarith
      exact h4
  · -- Small δ case: grid test family
    have h_small : δ < 1 / 2 := by linarith
    have hL_big_small : (10^7 : ENNReal) ≤ (10^7 : ENNReal) := by rfl
    let net := small_delta_test_net hδ hδ_le_one h_small (10^7 : ENNReal)
      (by norm_num) ENNReal.coe_ne_top hL_big_small
    refine ⟨net, ?_, ?_⟩
    · simpa [net, small_delta_test_net] using le_refl (10^7 : ENNReal)
    · have h_eq : net.testSets = smallDeltaTestSets δ hδ := by rfl
      rw [h_eq]
      exact smallDeltaTestSets_card_bound hδ h_small

end Kakeya.Streamlined
