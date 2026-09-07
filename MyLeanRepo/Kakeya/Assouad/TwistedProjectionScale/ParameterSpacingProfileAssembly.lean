import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterSpacingAverageAbsorption
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterSpacingStartLevel

/-!
# Assemble the selected spacing profile
-/

noncomputable section

namespace Kakeya.Assouad

structure ParameterSpacingProfileAssemblyData
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    (clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta) where
  tree :
    ParameterSpacingUniformTreeData
      clustered epsilon
  start :
    ParameterSpacingStartLevelData tree
  selected :
    ParameterSpacingSelectedProfileData tree
  selected_starts_at_start :
    selected.startLevel = start.level

theorem parameter_spacing_profile_assembly
    {delta epsilon eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (base : ℕ)
    (hbase : 3 ≤ base)
    (hlocal_loss :
      (2 *
          (Nat.log 2 ((base + 1) ^ 3) + 1) :
        ℝ) ≤
        Real.rpow (base : ℝ)
          (epsilon ^ 2 / 1000))
    (hepsilon : 0 < epsilon)
    (hepsilon_small : epsilon < 1 / 10)
    (heta : 0 < eta)
    (heta_le : eta ≤ epsilon ^ 2 / 1000)
    (hdelta : 0 < delta)
    (hdelta_small : delta < 1 / 1000)
    (haverage_bound :
      ∀ tree :
          ParameterSpacingUniformTreeData
            clustered epsilon,
        tree.base = base →
        (cellCount tree.base
            tree.refinedPoints 0 : ℝ) *
            Real.rpow (tree.base : ℝ)
              ((tree.levels : ℝ) *
                parameterSpacingAverageThreshold epsilon) ≤
          (tree.refinedPoints.card : ℝ))
    (hstart_available :
      ∀ tree :
          ParameterSpacingUniformTreeData
            clustered epsilon,
        tree.base = base →
        parameterSpacingStartIndex < tree.levels)
    (hstart_normalized :
      ∀ tree :
          ParameterSpacingUniformTreeData
            clustered epsilon,
        tree.base = base →
        (parameterSpacingStartIndex : ℝ) /
            (tree.levels : ℝ) ≤
          epsilon ^ 2 / 100)
    (hglobal :
      Kakeya.realRpowENN delta (-1 + eta) ≤
        100000 * clustered.points.enncard) :
    ∃ profile :
        ParameterSpacingProfileAssemblyData
          (epsilon := epsilon) clustered,
      profile.tree.base = base := by
  rcases parameter_spacing_uniform_tree_of_base
      base hbase hlocal_loss hdelta hdelta_small with
    ⟨tree, htree_base⟩
  have haverage :
      parameterSpacingAverageThreshold epsilon ≤
        ∑ i : Fin tree.levels,
          localDim tree.base tree.refinedPoints i *
            (scaleWeight tree.levels i.succ -
              scaleWeight tree.levels i.castSucc) :=
    parameter_spacing_average_profile
      tree hdelta
      (haverage_bound tree htree_base)
  rcases parameter_spacing_start_level
      tree (hstart_available tree htree_base)
      (hstart_normalized tree htree_base) with
    ⟨start⟩
  have hstart_scale :
      scaleWeight tree.levels
          start.level.castSucc ≤
        epsilon ^ 2 / 100 := by
    exact start.normalized_small
  have hstart_gap :
      (3 - parameterSpacingSuffixDimension epsilon) *
          (epsilon ^ 2 +
            scaleWeight tree.levels
              start.level.castSucc) <
        parameterSpacingAverageThreshold epsilon -
          parameterSpacingSuffixDimension epsilon := by
    have heps_sq : epsilon ^ 2 < 1 / 100 := by
      nlinarith
    simp only [parameterSpacingSuffixDimension,
      parameterSpacingAverageThreshold]
    nlinarith [sq_pos_of_pos hepsilon]
  rcases parameter_spacing_selected_profile
      tree hepsilon hepsilon_small start.level
      haverage hstart_gap with
    ⟨selected, hselected_start⟩
  refine ⟨{
    tree := tree
    start := start
    selected := selected
    selected_starts_at_start := hselected_start
  }, htree_base⟩

end Kakeya.Assouad
