module

/-
  Adapter: theorem6_1_uniform_data → section9_main → improved_incidence_correct_Ncover

  Wiring:
    theorem6_1_uniform_data provides UniformIncidenceData
    section9_main consumes it and produces the exact Ncover conclusion
    improved_incidence_correct_Ncover just needs ε_G, η (η unused in conclusion)

  Whiteprint node: improved_incidence_general / ncover_adapter
  Dependencies: Section9Main, Contracts.Theorem61UniformData
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.Section9Main
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Contracts.Theorem61UniformData
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace DirecretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheoremRework



/-- Adapter proof for improved_incidence_correct_Ncover.

    Uses theorem6_1_uniform_data to obtain UniformIncidenceData,
    then applies section9_main to get the exact conclusion. -/
theorem improved_incidence_correct_Ncover_adapter
    (s t : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2) :
    ∃ (ε_G η : ℝ), 0 < ε_G ∧ 0 < η ∧
      ∃ (δ₀ : ℝ), 0 < δ₀ ∧
        ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
          ∀ (P : Set EuclideanPlane),
            P ⊆ Metric.closedBall 0 1 →
            IsDeltaSSet δ t (Real.rpow δ (-ε_G)) P →
            ∀ (T : Set AffineLine)
              (Tp : ∀ (p : EuclideanPlane), p ∈ P → Set AffineLine),
              (∀ p hp, Tp p hp ⊆ T) →
              (∀ p hp, IsDeltaSSet δ s (Real.rpow δ (-ε_G)) (Tp p hp)) →
              (∀ p hp, ∀ ℓ ∈ Tp p hp, p ∈ Metric.cthickening δ ℓ.1) →
              _root_.Ncover δ T ≥
                ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_G))) := by
  -- Step 1: Obtain UniformIncidenceData from the Theorem 6.1 contract axiom
  rcases theorem6_1_uniform_data s t hs hs1 hst ht2
    with ⟨ε_inc, _hε_inc_lt_one, ⟨h_data⟩⟩
  have hε_inc_pos : 0 < ε_inc := h_data.hε_inc_pos

  -- Step 2: Apply section9_main with the uniform incidence data
  rcases DirecretisedFurstenbergEstimate.Section9Assembly.section9_main
      s t hs hs1 hst ht2 ε_inc hε_inc_pos h_data
    with ⟨ε_final, hε_final_pos, δ₀, hδ₀_pos, h_main⟩

  -- Step 3: Match conclusion.
  --   ε_G := ε_final
  --   η := ε_final (any positive value works; η is not used in the conclusion)
  exact ⟨ε_final, ε_final, hε_final_pos, hε_final_pos, δ₀, hδ₀_pos, h_main⟩

end DirecretisedFurstenbergEstimate.ImprovedIncidenceGeneral
