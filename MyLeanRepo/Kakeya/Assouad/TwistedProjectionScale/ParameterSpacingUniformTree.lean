import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.BranchingProfile
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingCellCardinality
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingIntervalCellCount
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingUniformRefinement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalSpacingCandidateStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterSpacingGridHelpers
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberGridParameterSelectionHelpers

/-!
# Uniform cubic-grid tree for the parameter spacing lemma

This packages the large-base, logarithmic-depth OS refinement used before the
suffix-profile selection.
-/

noncomputable section

namespace Kakeya.Assouad

structure ParameterSpacingUniformTreeData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    (clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta)
    (epsilon : ℝ) where
  base : ℕ
  base_ge_three : 3 ≤ base
  local_loss :
    (2 * (Nat.log 2 ((base + 1) ^ 3) + 1) : ℝ) ≤
      Real.rpow (base : ℝ) (epsilon ^ 2 / 1000)
  levels : ℕ
  levels_pos : 0 < levels
  terminal_mesh_lower :
    delta / (3 * (base : ℝ)) ≤
      (base ^ levels : ℝ)⁻¹
  terminal_mesh_upper :
    3 * (base ^ levels : ℝ)⁻¹ < delta
  partition : ℕ → Finset (DiscreteSet 3)
  partition_eq :
    partition =
      fun level =>
        cubicGridPartition base level clustered.points
  partition_tree :
    ∀ level ≤ levels,
      (∀ cell ∈ partition level,
        cell.Nonempty ∧ cell ⊆ clustered.points) ∧
      (∀ cell₁ ∈ partition level,
        ∀ cell₂ ∈ partition level,
          cell₁ ≠ cell₂ → Disjoint cell₁ cell₂) ∧
      clustered.points ⊆
        Finset.biUnion (partition level) id
  terminal_atomic :
    ∀ cell ∈ partition levels,
      cell.card = 1
  child_parent :
    ∀ level, level < levels →
      ∀ child ∈ partition (level + 1),
        ∃ parent ∈ partition level,
          child ⊆ parent
  child_bound :
    ∀ level, level < levels →
      ∀ parent ∈ partition level,
        (partitionChildren
          partition level parent).card ≤
            (base + 1) ^ 3
  refinedPoints : DiscreteSet 3
  refined_nonempty : refinedPoints.Nonempty
  refined_subset :
    refinedPoints ⊆ clustered.points
  retention :
    (clustered.points.card : ℝ) ≤
      (2 *
          (Nat.log 2 ((base + 1) ^ 3) + 1) :
        ℝ) ^ levels *
        (refinedPoints.card : ℝ)
  branchExponent : Fin levels → ℕ
  branch_bound :
    ∀ level : Fin levels,
      2 ^ branchExponent level ≤
        (base + 1) ^ 3
  exact_branching :
    ∀ level : Fin levels,
      ∀ parent ∈ partition level,
        (refinedPoints ∩ parent).Nonempty →
          (occupiedPartitionChildren
            refinedPoints partition level parent).card =
              2 ^ branchExponent level

theorem parameter_spacing_uniform_tree_of_base
    {delta epsilon : ℝ}
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
    (hdelta : 0 < delta)
    (hdelta_small : delta < 1 / 1000) :
    ∃ tree :
        ParameterSpacingUniformTreeData
          clustered epsilon,
      tree.base = base := by
  rcases exists_atomic_cubic_levels
      base hbase delta hdelta
      (hdelta_small.trans (by norm_num)) with
    ⟨levels, hlevels_pos,
      hmesh_lower, hmesh_upper⟩
  let partition : ℕ → Finset (DiscreteSet 3) :=
    fun level =>
      cubicGridPartition base level clustered.points
  have hmesh_atomic :
      3 <
        delta * (base ^ levels : ℝ) := by
    have hpow_pos :
        0 < (base ^ levels : ℝ) := by positivity
    have h :=
      mul_lt_mul_of_pos_right
        hmesh_upper hpow_pos
    have hcancel :
        3 * (base ^ levels : ℝ)⁻¹ *
            (base ^ levels : ℝ) =
          3 := by
      rw [mul_assoc,
        inv_mul_cancel₀ hpow_pos.ne', mul_one]
    calc
      3 =
          3 * (base ^ levels : ℝ)⁻¹ *
            (base ^ levels : ℝ) := hcancel.symm
      _ <
          delta * (base ^ levels : ℝ) := by
            exact h
  have htree :=
    cubic_grid_partition_tree
      clustered.points clustered.points_nonempty
      base levels (by omega)
      delta hdelta clustered.points_separated
      hmesh_atomic
  rcases htree with
    ⟨hpartition, hatomic, hchild_parent,
      hchild_bound⟩
  have hos :=
    os_branching_uniform_refinement
      (α := Point 3)
      clustered.points clustered.points_nonempty
      levels ((base + 1) ^ 3)
      (by positivity)
      partition
      hpartition hatomic hchild_parent
      hchild_bound
  rcases hos with
    ⟨refinedPoints, hrefined_nonempty,
      hrefined_subset, hretention,
      branchExponent, hbranch_bound,
      hexact_branching⟩
  refine ⟨{
    base := base
    base_ge_three := hbase
    local_loss := hlocal_loss
    levels := levels
    levels_pos := hlevels_pos
    terminal_mesh_lower := hmesh_lower
    terminal_mesh_upper := hmesh_upper
    partition := partition
    partition_eq := rfl
    partition_tree := hpartition
    terminal_atomic := hatomic
    child_parent := hchild_parent
    child_bound := hchild_bound
    refinedPoints := refinedPoints
    refined_nonempty := hrefined_nonempty
    refined_subset := hrefined_subset
    retention := hretention
    branchExponent := branchExponent
    branch_bound := hbranch_bound
    exact_branching := hexact_branching
  }, rfl⟩

theorem parameter_spacing_uniform_tree
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (hepsilon : 0 < epsilon)
    (hepsilon_small : epsilon < 1 / 10)
    (hdelta : 0 < delta)
    (hdelta_small : delta < 1 / 1000) :
    Nonempty
      (ParameterSpacingUniformTreeData
        clustered epsilon) := by
  have heta :
      0 < epsilon ^ 2 / 1000 := by positivity
  rcases exists_large_base3
      (epsilon ^ 2 / 1000) heta with
    ⟨base, hbase, hlocal_loss⟩
  rcases parameter_spacing_uniform_tree_of_base
      base hbase hlocal_loss hdelta hdelta_small with
    ⟨tree, _hbase_eq⟩
  exact ⟨tree⟩

end Kakeya.Assouad
