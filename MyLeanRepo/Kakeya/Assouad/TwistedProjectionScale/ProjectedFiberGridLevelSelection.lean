import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberGridLevelSelectionStatement

/-!
# Match a local scale to one projected grid level

Choose the least grid level whose mesh is no larger than the requested local
scale.  Minimality gives the strict upper comparison by one base factor.
-/

namespace Kakeya.Assouad

theorem projected_fiber_grid_level_selection :
    ProjectedFiberGridLevelSelectionStatement := by
  classical
  intro base levels hbase delta hdelta hterm rho hrho_low hrho_high
  let p : ℕ → Prop :=
    fun k => k ≤ levels + 1 ∧ ((base ^ k : ℝ)⁻¹) ≤ rho
  have h_exists : ∃ k, p k := by
    have h1 : levels + 1 ≤ levels + 1 := by rfl
    have h2 : ((base ^ (levels + 1) : ℝ)⁻¹) ≤ rho := by
      have h_strict : ((base ^ (levels + 1) : ℝ)⁻¹) < rho := by
        calc
          ((base ^ (levels + 1) : ℝ)⁻¹) < delta := hterm
          _ ≤ rho := hrho_low
      exact le_of_lt h_strict
    exact ⟨levels + 1, h1, h2⟩
  let level : ℕ := Nat.find h_exists
  have h_spec : p level := Nat.find_spec h_exists
  have h1 : level ≤ levels + 1 := h_spec.1
  have h2 : ((base ^ level : ℝ)⁻¹) ≤ rho := h_spec.2
  have h3 :
      rho < (base : ℝ) * ((base ^ level : ℝ)⁻¹) := by
    by_cases h : level = 0
    · have h_base_real : (2 : ℝ) ≤ (base : ℝ) := by
        exact_mod_cast hbase
      have h_goal : rho < (base : ℝ) := by linarith
      have h_simp :
          (base : ℝ) * ((base ^ level : ℝ)⁻¹) =
            (base : ℝ) := by
        rw [h]
        simp
      rw [h_simp]
      exact h_goal
    · have h4 : level - 1 < level := by omega
      have h5 : level - 1 ≤ levels + 1 := by omega
      have h6 : ¬p (level - 1) := Nat.find_min h_exists h4
      have h7 :
          ¬(((base ^ (level - 1) : ℝ)⁻¹) ≤ rho) := by
        by_contra h8
        exact h6 ⟨h5, h8⟩
      have h8 : rho < ((base ^ (level - 1) : ℝ)⁻¹) :=
        lt_of_not_ge h7
      have h9 : ∃ n : ℕ, level = n + 1 :=
        Nat.exists_eq_succ_of_ne_zero h
      rcases h9 with ⟨n, hn⟩
      have h10 :
          ((base ^ (level - 1) : ℝ)⁻¹) =
            (base : ℝ) * ((base ^ level : ℝ)⁻¹) := by
        rw [hn]
        simp [pow_succ]
        field_simp
      rw [h10] at h8
      exact h8
  exact ⟨level, h1, h2, h3⟩

end Kakeya.Assouad
