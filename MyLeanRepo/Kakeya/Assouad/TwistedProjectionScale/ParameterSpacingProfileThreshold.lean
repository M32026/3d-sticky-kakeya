import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterSpacingAverageAbsorption
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterSpacingStartDepth

/-!
# Quantitative threshold for the complete spacing profile
-/

noncomputable section

namespace Kakeya.Assouad

theorem exists_parameterSpacing_profile_threshold
    (base : ℕ)
    (hbase : 3 ≤ base)
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_small : epsilon < 1 / 10) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ eta : ℝ,
        0 < eta →
        eta ≤ epsilon ^ 2 / 1000 →
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              ∀ C lambda : ENNReal,
                ∀ clustered :
                    TubeParameterClusterFrostmanData
                      F Y C lambda delta,
                  ∀ tree :
                      ParameterSpacingUniformTreeData
                        clustered epsilon,
                    tree.base = base →
                    Kakeya.realRpowENN
                        delta (-1 + eta) ≤
                      100000 *
                        clustered.points.enncard →
                    ((cellCount tree.base
                          tree.refinedPoints 0 : ℝ) *
                          Real.rpow (tree.base : ℝ)
                            ((tree.levels : ℝ) *
                              parameterSpacingAverageThreshold
                                epsilon) ≤
                        (tree.refinedPoints.card : ℝ)) ∧
                      parameterSpacingStartIndex <
                        tree.levels ∧
                      (parameterSpacingStartIndex : ℝ) /
                          (tree.levels : ℝ) ≤
                        epsilon ^ 2 / 100 := by
  rcases exists_parameterSpacing_average_cardinality_bound
      base hbase epsilon hepsilon hepsilon_small with
    ⟨deltaAverage, hdeltaAverage,
      hdeltaAverageOne, haverage⟩
  rcases exists_parameterSpacing_start_depth
      base hbase epsilon hepsilon hepsilon_small with
    ⟨deltaStart, hdeltaStart,
      hdeltaStartOne, hstart⟩
  let delta₀ := min deltaAverage deltaStart
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀_one : delta₀ ≤ 1 :=
    (min_le_left _ _).trans hdeltaAverageOne
  refine ⟨delta₀, hdelta₀, hdelta₀_one, ?_⟩
  intro eta heta heta_le delta hdelta hdelta_le
    F Y C lambda clustered tree htree_base hglobal
  have hdelta_average : delta ≤ deltaAverage :=
    hdelta_le.trans (min_le_left _ _)
  have hdelta_start : delta ≤ deltaStart :=
    hdelta_le.trans (min_le_right _ _)
  exact ⟨
    haverage eta heta heta_le
      delta hdelta hdelta_average
      F Y C lambda clustered tree htree_base hglobal,
    (hstart delta hdelta hdelta_start
      F Y C lambda clustered tree htree_base).1,
    (hstart delta hdelta hdelta_start
      F Y C lambda clustered tree htree_base).2
  ⟩

end Kakeya.Assouad
