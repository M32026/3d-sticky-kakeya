import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingInduction

/-!
# Orponen--Shmerkin local-branching uniform refinement

Final closed theorem obtained by applying the fine-to-coarse induction at all
levels of the partition tree.
-/

namespace Kakeya.Assouad

theorem os_branching_uniform_refinement :
    OSBranchingUniformRefinementStatement := by
  intro α _ A hA levels childBound hcb_pos P h_partition h_atomic
    h_child_parent h_children_bound
  rcases os_branching_induction A hA levels childBound hcb_pos P h_partition
      h_atomic h_child_parent h_children_bound levels (by linarith) with
    ⟨A', branchExponent', hA'_nonempty, hA'_sub, h_ret,
      h_branch_bound, h_branch_unif, _⟩
  let branchExponent : Fin levels → ℕ := fun level =>
    branchExponent' level
  have h_branch_bound' :
      ∀ level : Fin levels,
        2 ^ branchExponent level ≤ childBound := by
    intro level
    exact h_branch_bound level (by simp) level.is_lt
  have h_branch_unif' :
      ∀ level : Fin levels,
        ∀ parent ∈ P level,
          (A' ∩ parent).Nonempty →
            (occupiedPartitionChildren A' P level parent).card =
              2 ^ branchExponent level := by
    intro level parent hparent hne
    exact h_branch_unif level (by simp) level.is_lt parent hparent hne
  exact
    ⟨A', hA'_nonempty, hA'_sub, h_ret, branchExponent,
      h_branch_bound', h_branch_unif'⟩

end Kakeya.Assouad
