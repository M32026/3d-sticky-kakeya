import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridCoarseningLevelStatement

/-!
WZ2 Proposition 7.1: choose the no-finer delta-grid parameter level matching
one selected coarse radius.
-/

namespace Kakeya.Assouad

theorem tube_parameter_grid_coarsening_level :
    TubeParameterGridCoarseningLevelStatement := by
  classical
  intro base levels currentLevel hbase hcur rho hrho_pos hrho_one hmesh
  let p : ℕ → Prop := fun k => 6 * ((base ^ k : ℝ)⁻¹) ≤ rho
  have h_exists : ∃ k, p k := ⟨currentLevel, hmesh⟩
  let nextLevel : ℕ := Nat.find h_exists
  have h_spec : p nextLevel := Nat.find_spec h_exists
  have h_le_current : nextLevel ≤ currentLevel := Nat.find_min' h_exists hmesh
  have h_le_levels : nextLevel ≤ levels := by
    linarith
  have h4 : rho < 6 * (base : ℝ) * ((base ^ nextLevel : ℝ)⁻¹) := by
    by_cases h : nextLevel = 0
    · -- Case nextLevel = 0
      have h_base_real : (2 : ℝ) ≤ (base : ℝ) := by exact_mod_cast hbase
      have h_goal : rho < 6 * (base : ℝ) := by linarith
      have h_simp : 6 * (base : ℝ) * ((base ^ nextLevel : ℝ)⁻¹) = 6 * (base : ℝ) := by
        rw [h]
        simp
      rw [h_simp]
      exact h_goal
    · -- Case nextLevel > 0
      have h_pos : 0 < nextLevel := Nat.pos_of_ne_zero h
      have h5 : nextLevel - 1 < nextLevel := by omega
      have h6 : ¬p (nextLevel - 1) := Nat.find_min h_exists h5
      have h7 : ¬(6 * ((base ^ (nextLevel - 1) : ℝ)⁻¹) ≤ rho) := h6
      have h8 : rho < 6 * ((base ^ (nextLevel - 1) : ℝ)⁻¹) := by
        exact lt_of_not_ge h7
      have h9 : ∃ n : ℕ, nextLevel = n + 1 := Nat.exists_eq_succ_of_ne_zero h
      rcases h9 with ⟨n, hn⟩
      have h10 : ((base ^ (nextLevel - 1) : ℝ)⁻¹) = (base : ℝ) * ((base ^ nextLevel : ℝ)⁻¹) := by
        rw [hn]
        simp [pow_succ]
        field_simp
      rw [h10] at h8
      have h11 : 6 * ((base : ℝ) * ((base ^ nextLevel : ℝ)⁻¹)) =
          6 * (base : ℝ) * ((base ^ nextLevel : ℝ)⁻¹) := by ring
      rw [h11] at h8
      exact h8
  exact ⟨nextLevel, h_le_current, h_le_levels, h_spec, h4⟩

end Kakeya.Assouad
