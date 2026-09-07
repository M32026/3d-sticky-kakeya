import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSTerminationStatement

/-!
WZ2 Proposition 7.1: prove finite termination of the corrected selected-scale
grid OS iteration.
-/

namespace Kakeya.Assouad

theorem grid_os_termination :
    GridOSTerminationStatement := by
  intro epsilon hε_pos hε_lt_one
  set a : ℝ := 1 - epsilon ^ 2 with ha_def
  have ha_pos : 0 < a := by nlinarith
  have ha_lt_one : a < 1 := by nlinarith
  have hε2_pos : 0 < epsilon ^ 2 := by positivity
  have hε2_le_one : epsilon ^ 2 ≤ 1 := by nlinarith
  have h_main : ∃ n : ℕ, a ^ (n + 1) < epsilon ^ 2 ∧ epsilon ^ 2 ≤ a ^ n :=
    exists_nat_pow_near_of_lt_one hε2_pos hε2_le_one ha_pos ha_lt_one
  rcases h_main with ⟨n, h1, _⟩
  let steps : ℕ := n + 1
  have h_steps_def : steps = n + 1 := by rfl
  have h_steps_pos : 0 < steps := by simp [steps]
  have h3 : a ^ steps ≤ epsilon ^ 2 := by
    simpa [steps] using h1.le
  refine ⟨steps, h3, ?_⟩
  intro delta hδ_pos hδ_lt_one scale hscale0 hscale_pos hrec
  have h_ind : ∀ k : ℕ, k ≤ steps → scale k ≥ Real.rpow delta (a ^ k) := by
    intro k hk
    induction k with
    | zero =>
      simp [hscale0]
    | succ k ih =>
      have h_k_lt_steps : k < steps := by omega
      have h_rec : Real.rpow (scale k) a < scale (k + 1) := hrec k h_k_lt_steps
      have h_ih' : scale k ≥ Real.rpow delta (a ^ k) := ih (by omega)
      have h_rpow_pos : 0 ≤ Real.rpow delta (a ^ k) :=
        Real.rpow_nonneg hδ_pos.le (a ^ k)
      have h_mono : Real.rpow (Real.rpow delta (a ^ k)) a ≤ Real.rpow (scale k) a :=
        Real.rpow_le_rpow h_rpow_pos h_ih' ha_pos.le
      have h_mul : Real.rpow (Real.rpow delta (a ^ k)) a = Real.rpow delta (a ^ (k + 1)) := by
        have h_eq1 : Real.rpow (Real.rpow delta (a ^ k)) a =
            Real.rpow delta ((a ^ k) * a) :=
          (Real.rpow_mul hδ_pos.le (a ^ k) a).symm
        rw [h_eq1]
        have h2 : (a ^ k) * a = a ^ (k + 1) := by ring
        rw [h2]
      rw [h_mul] at h_mono
      exact le_of_lt (h_mono.trans_lt h_rec)
  have h_strict : Real.rpow delta (a ^ steps) < scale steps := by
    have h_rec : Real.rpow (scale n) a < scale steps := by
      simpa [h_steps_def] using hrec n (by simp [h_steps_def])
    have h_ih : scale n ≥ Real.rpow delta (a ^ n) :=
      h_ind n (by simp [h_steps_def])
    have h_rpow_pos : 0 ≤ Real.rpow delta (a ^ n) :=
      Real.rpow_nonneg hδ_pos.le (a ^ n)
    have h_mono : Real.rpow (Real.rpow delta (a ^ n)) a ≤ Real.rpow (scale n) a :=
      Real.rpow_le_rpow h_rpow_pos h_ih ha_pos.le
    have h_mul : Real.rpow (Real.rpow delta (a ^ n)) a = Real.rpow delta (a ^ steps) := by
      have h_eq1 : Real.rpow (Real.rpow delta (a ^ n)) a =
          Real.rpow delta ((a ^ n) * a) :=
        (Real.rpow_mul hδ_pos.le (a ^ n) a).symm
      rw [h_eq1]
      have h2 : (a ^ n) * a = a ^ steps := by
        simp [h_steps_def, pow_succ]
      rw [h2]
    rw [h_mul] at h_mono
    exact h_mono.trans_lt h_rec
  have h13 : Real.rpow delta (epsilon ^ 2) ≤ Real.rpow delta (a ^ steps) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h3
  exact h13.trans_lt h_strict

end Kakeya.Assouad
