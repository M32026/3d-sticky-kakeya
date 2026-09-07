module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FinalProof
public import MyLeanRepo.DiscretisedFurstenbergEstimate.TargetAssembly

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

open DirecretisedFurstenbergEstimate

-- Disambiguate: ProductStructureRescaling.Basics also defines _root_.EuclideanPlane
local notation "EuclideanPlane" => DirecretisedFurstenbergEstimate.EuclideanPlane

/--
[thm.discretised_furstenberg_estimate.467] Given `s ∈ (0,1)` and `t ∈ (s,2)`,
there is an exponent `ε = ε(s,t) > 0` such that, for all sufficiently small
`0 < δ ≤ δ₀(s,t)`, if `X ⊆ B²` is a `(δ,t,δ^{-ε})`-set and for each `x ∈ X`
there is a `(δ,s,δ^{-ε})`-set of `δ`-tubes passing through `x`, then the
`δ`-covering number of the union of these tube families is at least
`δ^{-2s-ε}`.  Moreover, `ε` can be chosen uniformly positive on compact subsets
of the parameter range.
-/
theorem discretised_furstenberg_estimate :
    ∃ ε : ℝ × ℝ → ℝ,
      (∀ p ∈ parameterRange, 0 < ε p) ∧
        (∀ A : Set (ℝ × ℝ), IsCompact A →
          A ⊆ parameterRange →
            ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ p ∈ A, ε₀ ≤ ε p) ∧
          ∀ s t : ℝ,
            (s, t) ∈ parameterRange →
              ∃ δ₀ : ℝ, 0 < δ₀ ∧
                ∀ δ : ℝ, δ ∈ Set.Ioc (0 : ℝ) δ₀ →
                  ∀ X : Set EuclideanPlane,
                    X ⊆ Metric.closedBall 0 1 →
                      IsDeltaSSet δ t (Real.rpow δ (-(ε (s, t)))) X →
                        ∀ 𝓣 : ∀ x : EuclideanPlane, x ∈ X → Set AffineLine,
                          (∀ x hx,
                            IsDeltaSSet δ s
                              (Real.rpow δ (-(ε (s, t)))) (𝓣 x hx)) →
                            (∀ x hx, ∀ ℓ ∈ 𝓣 x hx, x ∈ Metric.cthickening δ ℓ.1) →
                              ENNReal.ofReal (Real.rpow δ (-(2 * s + ε (s, t)))) ≤
                                (Metric.externalCoveringNumber δ.toNNReal
                                  (⋃ (x : EuclideanPlane) (hx : x ∈ X), 𝓣 x hx) : ℝ≥0∞) := by
  let h_core : DirecretisedFurstenbergEstimate.FinalProof.CoreEstimateHypothesis := by
    intro s t hp
    have hs : 0 < s := hp.1.1
    have hs1 : s < 1 := hp.1.2
    have hst : s < t := hp.2.1
    have ht2 : t < 2 := hp.2.2
    rcases DirecretisedFurstenbergEstimate.FinalProof.core_estimate
        s t hs hs1 hst ht2
      with ⟨ε, δ₀, hε_pos, hδ₀_pos, h_main⟩
    refine' ⟨ε, δ₀, hε_pos, hδ₀_pos, _⟩
    exact ⟨hε_pos, δ₀, hδ₀_pos, h_main⟩
  exact DirecretisedFurstenbergEstimate.FinalProof.target_theorem_of_core_estimate h_core

end
