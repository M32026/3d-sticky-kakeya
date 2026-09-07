module

public import MyLeanRepo.OSWPrelude
public import MyLeanRepo.RadialBootstrapping.HasMeasureThinTubes
public import MyLeanRepo.discretised_furstenberg_estimate
public import MyLeanRepo.RadialBootstrapping.FinalWiring

@[expose] public section

open MeasureTheory

noncomputable section

open scoped ENNReal NNReal

/--
[prop.radial_bootstrapping_measure_thin_tubes.2673] Let `β, ε > 0`. Then there are
constants `τ = τ(β, ε) > 0` and `M = M(β, ε) ≥ 1` such that whenever
`σ ∈ [β, 1 - ε]`, `c ∈ (0, 1 / 10)`, and `K, C ≥ 1`, the following holds. If
`ν₁, ν₂` are Borel probability measures on `ℝ²` whose supports have mutual distance at
least `1 / 2`, both measures obey the ball growth estimates `νᵢ(B(x, r)) ≤ C r` for all
`x` and all `r > 0`, and both ordered pairs have `(σ, K, 1 - c)`-thin tubes, then both
ordered pairs have `(σ + τ, K', 1 - 3c)`-thin tubes, where
`K' = max {K, C^2 M / c}^M`.

Here `ℝ²` is represented as `EuclideanSpace ℝ (Fin 2)`, mutual support distance is
formalized as the infimum of pointwise distances between the two supports, and the real
power in the definition of `K'` is `Real.rpow`.
-/
theorem radial_bootstrapping_measure_thin_tubes :
    ∀ β ε : ℝ, 0 < β → 0 < ε →
      ∃ τ : ℝ, 0 < τ ∧
        ∃ M : ℝ, 1 ≤ M ∧
          ∀ (σ c K C : ℝ) (ν₁ ν₂ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))),
            (ν₁ : Measure (EuclideanSpace ℝ (Fin 2))).support ⊆ Metric.closedBall 0 1 →
              (ν₂ : Measure (EuclideanSpace ℝ (Fin 2))).support ⊆ Metric.closedBall 0 1 →
                σ ∈ Set.Icc β (1 - ε) →
              c ∈ Set.Ioo (0 : ℝ) (1 / 10) →
                1 ≤ K →
                  1 ≤ C →
                    (1 : ℝ) / 2 ≤
                      sInf {d : ℝ |
                        ∃ x ∈ (ν₁ : Measure (EuclideanSpace ℝ (Fin 2))).support,
                          ∃ y ∈ (ν₂ : Measure (EuclideanSpace ℝ (Fin 2))).support,
                            dist x y = d} →
                      (∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), 0 < r →
                        ν₁ (Metric.ball x r) ≤ Real.toNNReal (C * r)) →
                        (∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), 0 < r →
                          ν₂ (Metric.ball x r) ≤ Real.toNNReal (C * r)) →
                          HasMeasureThinTubes σ K c ν₁ ν₂ →
                            HasMeasureThinTubes σ K c ν₂ ν₁ →
                              let K' : ℝ := Real.rpow (max K (C ^ 2 * M / c)) M
                              HasMeasureThinTubes (σ + τ) K' (3 * c) ν₁ ν₂ ∧
                                HasMeasureThinTubes (σ + τ) K' (3 * c) ν₂ ν₁ := by
  intro β ε hβ hε
  rcases RadialBootstrapping.radial_bootstrapping_measure_thin_tubes_draft
      β ε hβ hε with ⟨τ, hτ, M, hM, h_main⟩
  refine' ⟨τ, hτ, M, hM, _⟩
  intro σ c K C ν₁ ν₂ h_supp1 h_supp2 hσ hc hK hC h_dist hν₁_growth hν₂_growth h_thin12 h_thin21
  exact h_main σ c K C ν₁ ν₂ h_supp1 h_supp2 hσ hc hK hC h_dist hν₁_growth hν₂_growth h_thin12 h_thin21
