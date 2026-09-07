import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.LocalDimensionCumulative
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterSpacingUniformTree
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ScaleWeightSuffixBranching
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ScaleWeightSuffixBranchingFrom

/-!
# Selected suffix of the parameter-spacing profile

This is the exact finite-profile consequence of paper Lemma 7.10 used by the
local Frostman argument.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The dimension retained after the profile-merging loss. -/
def parameterSpacingSuffixDimension
    (epsilon : ℝ) : ℝ :=
  1 - 12 * epsilon ^ 2

/-- The average dimension threshold supplied by cardinality retention. -/
def parameterSpacingAverageThreshold
    (epsilon : ℝ) : ℝ :=
  1 - 3 * epsilon ^ 2

structure ParameterSpacingSelectedProfileData
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (tree :
      ParameterSpacingUniformTreeData
        clustered epsilon) where
  startLevel : Fin tree.levels
  selectedLevel : Fin tree.levels
  start_le_selected :
    startLevel.val ≤ selectedLevel.val
  selected_early :
    scaleWeight tree.levels
        selectedLevel.castSucc <
      1 - epsilon ^ 2
  prefix_upper :
    suffixProfileCumulative
        (scaleWeight tree.levels)
        (fun i : Fin tree.levels =>
          localDim tree.base tree.refinedPoints i)
        selectedLevel.castSucc ≤
      parameterSpacingSuffixDimension epsilon *
        scaleWeight tree.levels
          selectedLevel.castSucc +
        (3 - parameterSpacingSuffixDimension epsilon) *
          scaleWeight tree.levels
            startLevel.castSucc
  suffix_lower :
    ∀ j : Fin (tree.levels + 1),
      selectedLevel.val ≤ j.val →
        parameterSpacingSuffixDimension epsilon *
            (scaleWeight tree.levels j -
              scaleWeight tree.levels
                selectedLevel.castSucc) ≤
          suffixProfileCumulative
              (scaleWeight tree.levels)
              (fun i : Fin tree.levels =>
                localDim tree.base
                  tree.refinedPoints i)
              j -
            suffixProfileCumulative
              (scaleWeight tree.levels)
              (fun i : Fin tree.levels =>
                localDim tree.base
                  tree.refinedPoints i)
              selectedLevel.castSucc
  cellCount_growth :
    ∀ j : Fin (tree.levels + 1),
      selectedLevel.val ≤ j.val →
        Real.rpow (tree.base : ℝ)
              (((j.val - selectedLevel.val : ℕ) : ℝ) *
                parameterSpacingSuffixDimension epsilon) *
            (cellCount tree.base tree.refinedPoints
              selectedLevel.val : ℝ) ≤
          (cellCount tree.base tree.refinedPoints
            j.val : ℝ)

theorem parameter_spacing_selected_profile
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (tree :
      ParameterSpacingUniformTreeData
        clustered epsilon)
    (hepsilon : 0 < epsilon)
    (hepsilon_small : epsilon < 1 / 10)
    (startLevel : Fin tree.levels)
    (haverage :
      parameterSpacingAverageThreshold epsilon ≤
        ∑ i : Fin tree.levels,
          localDim tree.base tree.refinedPoints i *
            (scaleWeight tree.levels i.succ -
              scaleWeight tree.levels i.castSucc))
    (hstart_gap :
      (3 - parameterSpacingSuffixDimension epsilon) *
          (epsilon ^ 2 +
            scaleWeight tree.levels
              startLevel.castSucc) <
        parameterSpacingAverageThreshold epsilon -
          parameterSpacingSuffixDimension epsilon) :
    ∃ selected :
        ParameterSpacingSelectedProfileData tree,
      selected.startLevel = startLevel := by
  let dimension :=
    parameterSpacingSuffixDimension epsilon
  let average :=
    parameterSpacingAverageThreshold epsilon
  have hdimension_nonneg : 0 ≤ dimension := by
    dsimp only [dimension,
      parameterSpacingSuffixDimension]
    nlinarith [sq_nonneg epsilon]
  have hdimension_lt_three : dimension < 3 := by
    dsimp only [dimension,
      parameterSpacingSuffixDimension]
    nlinarith [sq_nonneg epsilon]
  have hepsilon_one : epsilon < 1 := by
    linarith
  have hbounds :
      ∀ i : Fin tree.levels,
        0 ≤ localDim tree.base
            tree.refinedPoints i ∧
          localDim tree.base
            tree.refinedPoints i ≤ 3 := by
    intro i
    exact localDim_bound
      (tree.base_ge_three.trans' (by omega))
  rcases
      scaleWeight_suffix_branching_from
        tree.levels tree.levels_pos
        3 dimension epsilon average
        hdimension_nonneg hdimension_lt_three
        hepsilon hepsilon_one
        (fun i : Fin tree.levels =>
          localDim tree.base tree.refinedPoints i)
        hbounds haverage startLevel
        (by simpa [dimension, average] using hstart_gap) with
    ⟨selectedLevel, hstart_le, hearly,
      hprefix, hsuffix⟩
  have hgrowth :
      ∀ j : Fin (tree.levels + 1),
        selectedLevel.val ≤ j.val →
          Real.rpow (tree.base : ℝ)
                (((j.val - selectedLevel.val : ℕ) : ℝ) *
                  dimension) *
              (cellCount tree.base tree.refinedPoints
                selectedLevel.val : ℝ) ≤
            (cellCount tree.base tree.refinedPoints
              j.val : ℝ) := by
    intro j hj
    have hbase_two : 2 ≤ tree.base :=
      tree.base_ge_three.trans' (by omega)
    have hj_cast :
        selectedLevel.castSucc.val ≤ j.val := by
      simpa using hj
    exact
      localDim_suffix_cellCount_growth
        hbase_two tree.levels_pos
        tree.refined_nonempty
        dimension selectedLevel.castSucc j
        hj_cast (hsuffix j hj)
  refine ⟨{
    startLevel := startLevel
    selectedLevel := selectedLevel
    start_le_selected := hstart_le
    selected_early := hearly
    prefix_upper := hprefix
    suffix_lower := hsuffix
    cellCount_growth := hgrowth
  }, rfl⟩

end Kakeya.Assouad
