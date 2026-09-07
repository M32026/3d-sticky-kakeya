import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet.Proof

/-! # Explicit polynomial density-test net without unrelated target imports -/

noncomputable section

open Kakeya.Streamlined.RandomTranslation
open Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet

namespace Kakeya.Assouad

lemma pure_wz2_tube_density_test_net_explicit
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1) :
    ∃ net : TubeDensityTestNet delta,
      net.lossFactor ≤ (10^7 : ENNReal) ∧
      (net.testSets.card : ℝ) ≤ (1 / delta) ^ (200 : ℕ) := by
  by_cases hlarge : delta ≥ 1 / 2
  · let net := Kakeya.Streamlined.large_delta_test_net hdelta hdelta_one hlarge
      (10^7 : ENNReal) (by norm_num) ENNReal.coe_ne_top (by norm_num)
    refine ⟨net, ?_, ?_⟩
    · simpa [net, Kakeya.Streamlined.large_delta_test_net] using le_rfl
    · have hcard : (net.testSets.card : ℝ) = 1 := by
        simp [net, Kakeya.Streamlined.large_delta_test_net]
      rw [hcard]
      have hone : 1 ≤ 1 / delta := by
        apply one_le_one_div <;> linarith
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hone 200
  · have hsmall : delta < 1 / 2 := by linarith
    let net := Kakeya.Streamlined.small_delta_test_net hdelta hdelta_one hsmall
      (10^7 : ENNReal) (by norm_num) ENNReal.coe_ne_top (by norm_num)
    refine ⟨net, ?_, ?_⟩
    · simpa [net, Kakeya.Streamlined.small_delta_test_net] using le_rfl
    · have hset : net.testSets =
          Kakeya.Streamlined.smallDeltaTestSets delta hdelta := rfl
      rw [hset]
      exact Kakeya.Streamlined.smallDeltaTestSets_card_bound hdelta hsmall

end Kakeya.Assouad

end
