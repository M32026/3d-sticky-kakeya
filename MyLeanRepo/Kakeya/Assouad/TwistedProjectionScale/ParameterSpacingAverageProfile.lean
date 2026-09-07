import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.LocalDimensionCumulative
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterSpacingSelectedProfile

/-!
# Average dimension of the retained spacing tree

This isolates the analytic profile lower bound from the exponent absorption
that produces its cardinality premise.
-/

noncomputable section

namespace Kakeya.Assouad

lemma parameterSpacing_refined_terminal_atomic
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
    (hdelta : 0 < delta) :
    ∀ cell ∈
        cubicGridPartition tree.base tree.levels
          tree.refinedPoints,
      cell.card = 1 := by
  have hseparated :
      tree.refinedPoints.IsDeltaSeparated delta := by
    intro p hp q hq hpq
    exact clustered.points_separated
      (tree.refined_subset hp)
      (tree.refined_subset hq) hpq
  have hmesh :
      3 <
        delta *
          (tree.base ^ tree.levels : ℝ) := by
    have hpow :
        0 < (tree.base ^ tree.levels : ℝ) := by
      have hbase_pos : (0 : ℝ) < tree.base := by
        exact_mod_cast
          (show 0 < tree.base from
            lt_of_lt_of_le (by norm_num)
              tree.base_ge_three)
      exact pow_pos hbase_pos _
    have h :=
      mul_lt_mul_of_pos_right
        tree.terminal_mesh_upper hpow
    have hcancel :
        3 * (tree.base ^ tree.levels : ℝ)⁻¹ *
            (tree.base ^ tree.levels : ℝ) =
          3 := by
      rw [mul_assoc,
        inv_mul_cancel₀ hpow.ne', mul_one]
    calc
      3 =
          3 * (tree.base ^ tree.levels : ℝ)⁻¹ *
            (tree.base ^ tree.levels : ℝ) :=
        hcancel.symm
      _ <
          delta *
            (tree.base ^ tree.levels : ℝ) := h
  have htree :=
    cubic_grid_partition_tree
      tree.refinedPoints tree.refined_nonempty
      tree.base tree.levels
      (tree.base_ge_three.trans' (by omega))
      delta hdelta hseparated hmesh
  exact htree.2.1

lemma parameterSpacing_terminal_cellCount
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
    (hdelta : 0 < delta) :
    cellCount tree.base tree.refinedPoints
        tree.levels =
      tree.refinedPoints.card := by
  exact cubicGridPartition_card_eq_of_atomic
    tree.refined_nonempty
    (parameterSpacing_refined_terminal_atomic
      tree hdelta)

lemma parameterSpacing_root_cellCount_le
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (tree :
      ParameterSpacingUniformTreeData
        clustered epsilon) :
    cellCount tree.base tree.refinedPoints 0 ≤
      (2 * tree.base + 1) ^ 3 := by
  apply cubicGridPartition_zero_card_le
    (tree.base_ge_three.trans' (by omega))
  intro p hp
  exact clustered.points_in_unitBall p
    (tree.refined_subset hp)

theorem parameter_spacing_average_profile
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
    (hdelta : 0 < delta)
    (hcard :
      (cellCount tree.base tree.refinedPoints 0 : ℝ) *
          Real.rpow (tree.base : ℝ)
            ((tree.levels : ℝ) *
              parameterSpacingAverageThreshold epsilon) ≤
        (tree.refinedPoints.card : ℝ)) :
    parameterSpacingAverageThreshold epsilon ≤
      ∑ i : Fin tree.levels,
        localDim tree.base tree.refinedPoints i *
          (scaleWeight tree.levels i.succ -
            scaleWeight tree.levels i.castSucc) := by
  apply localDim_average_lower_of_cellCount
    (tree.base_ge_three.trans' (by omega))
    tree.levels_pos tree.refined_nonempty
    (parameterSpacingAverageThreshold epsilon)
  rwa [parameterSpacing_terminal_cellCount
    tree hdelta]

end Kakeya.Assouad
