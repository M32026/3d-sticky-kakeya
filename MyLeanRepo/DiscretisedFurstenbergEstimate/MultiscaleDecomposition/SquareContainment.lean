module

/-
  Dyadic square containment: a Δ^(a+k)-square that intersects a Δ^a-square is contained in it.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.LinearToRegular
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.MultiscaleDecomposition

namespace DirecretisedFurstenbergEstimate.MultiscaleDecomposition

/-- If a `Δ^(a+k)`-square with indices `(c,d)` intersects the `Δ^a`-square `(i,j)`,
    then it is contained in it. -/
lemma dyadic_square_containment
    {Δ : ℝ} {a k : ℕ} {n : ℕ} (hn_pos : 0 < n)
    (h1 : (1 : ℝ) = (n : ℝ) * Δ)
    (i j c d : ℤ) (hk_pos : 0 < k)
    (h_int1 : Set.Nonempty (Set.Ico ((c : ℝ) * Δ ^ (a + k)) ((c + 1 : ℝ) * Δ ^ (a + k)) ∩
        Set.Ico ((i : ℝ) * (Δ ^ a)) (((i + 1 : ℝ) * (Δ ^ a)))))
    (h_int2 : Set.Nonempty (Set.Ico ((d : ℝ) * Δ ^ (a + k)) ((d + 1 : ℝ) * Δ ^ (a + k)) ∩
        Set.Ico ((j : ℝ) * (Δ ^ a)) (((j + 1 : ℝ) * (Δ ^ a))))) :
    dyadicSquare (Δ ^ (a + k)) c d ⊆ dyadicSquare (Δ ^ a) i j := by
  have hΔa_pos : 0 < Δ ^ a := by
    have hΔ : 0 < Δ := by
      have h : (n : ℝ) * Δ = 1 := by linarith
      have h' : 0 < (n : ℝ) := by exact_mod_cast hn_pos
      nlinarith
    positivity
  have h_scale1 : Set.Nonempty (Set.Ico ((c : ℝ) * Δ ^ k) ((c + 1 : ℝ) * Δ ^ k) ∩
      Set.Ico (i : ℝ) (i + 1)) := by
    rcases h_int1 with ⟨z, hz1, hz2⟩
    let w := z / (Δ ^ a)
    have hw1 : w ∈ Set.Ico ((c : ℝ) * Δ ^ k) ((c + 1 : ℝ) * Δ ^ k) := by
      dsimp only [w]
      have h_eq1 : (c : ℝ) * Δ ^ k = (c : ℝ) * Δ ^ (a + k) / (Δ ^ a) := by
        rw [pow_add] <;> field_simp [hΔa_pos.ne'] <;> ring
      have h_eq2 : (c + 1 : ℝ) * Δ ^ k = (c + 1 : ℝ) * Δ ^ (a + k) / (Δ ^ a) := by
        rw [pow_add] <;> field_simp [hΔa_pos.ne'] <;> ring
      have h1 : (c : ℝ) * Δ ^ (a + k) ≤ z := hz1.1
      have h2 : z < (c + 1 : ℝ) * Δ ^ (a + k) := hz1.2
      exact ⟨by rw [h_eq1]; exact div_le_div_of_nonneg_right h1 (by positivity),
        by rw [h_eq2]; exact div_lt_div_of_pos_right h2 hΔa_pos⟩
    have hw2 : w ∈ Set.Ico (i : ℝ) (i + 1) := by
      dsimp only [w]
      have h_eq1 : (i : ℝ) = (i : ℝ) * (Δ ^ a) / (Δ ^ a) := by
        field_simp [hΔa_pos.ne'] <;> ring
      have h_eq2 : (i + 1 : ℝ) = (i + 1 : ℝ) * (Δ ^ a) / (Δ ^ a) := by
        field_simp [hΔa_pos.ne'] <;> ring
      have h1 : (i : ℝ) * (Δ ^ a) ≤ z := hz2.1
      have h2 : z < (i + 1 : ℝ) * (Δ ^ a) := hz2.2
      exact ⟨by rw [h_eq1]; exact div_le_div_of_nonneg_right h1 (by positivity),
        by rw [h_eq2]; exact div_lt_div_of_pos_right h2 hΔa_pos⟩
    exact ⟨w, hw1, hw2⟩
  have h_scale2 : Set.Nonempty (Set.Ico ((d : ℝ) * Δ ^ k) ((d + 1 : ℝ) * Δ ^ k) ∩
      Set.Ico (j : ℝ) (j + 1)) := by
    rcases h_int2 with ⟨z, hz1, hz2⟩
    let w := z / (Δ ^ a)
    have hw1 : w ∈ Set.Ico ((d : ℝ) * Δ ^ k) ((d + 1 : ℝ) * Δ ^ k) := by
      dsimp only [w]
      have h_eq1 : (d : ℝ) * Δ ^ k = (d : ℝ) * Δ ^ (a + k) / (Δ ^ a) := by
        rw [pow_add] <;> field_simp [hΔa_pos.ne'] <;> ring
      have h_eq2 : (d + 1 : ℝ) * Δ ^ k = (d + 1 : ℝ) * Δ ^ (a + k) / (Δ ^ a) := by
        rw [pow_add] <;> field_simp [hΔa_pos.ne'] <;> ring
      have h1 : (d : ℝ) * Δ ^ (a + k) ≤ z := hz1.1
      have h2 : z < (d + 1 : ℝ) * Δ ^ (a + k) := hz1.2
      exact ⟨by rw [h_eq1]; exact div_le_div_of_nonneg_right h1 (by positivity),
        by rw [h_eq2]; exact div_lt_div_of_pos_right h2 hΔa_pos⟩
    have hw2 : w ∈ Set.Ico (j : ℝ) (j + 1) := by
      dsimp only [w]
      have h_eq1 : (j : ℝ) = (j : ℝ) * (Δ ^ a) / (Δ ^ a) := by
        field_simp [hΔa_pos.ne'] <;> ring
      have h_eq2 : (j + 1 : ℝ) = (j + 1 : ℝ) * (Δ ^ a) / (Δ ^ a) := by
        field_simp [hΔa_pos.ne'] <;> ring
      have h1 : (j : ℝ) * (Δ ^ a) ≤ z := hz2.1
      have h2 : z < (j + 1 : ℝ) * (Δ ^ a) := hz2.2
      exact ⟨by rw [h_eq1]; exact div_le_div_of_nonneg_right h1 (by positivity),
        by rw [h_eq2]; exact div_lt_div_of_pos_right h2 hΔa_pos⟩
    exact ⟨w, hw1, hw2⟩
  rcases dyadic_square_contained_in_one_square hn_pos h1 hk_pos (a := c) (i := i) h_scale1 with ⟨h_left1, h_right1⟩
  rcases dyadic_square_contained_in_one_square hn_pos h1 hk_pos (a := d) (i := j) h_scale2 with ⟨h_left2, h_right2⟩
  intro z hz
  simp only [dyadicSquare, Set.mem_setOf_eq, Set.mem_Ico] at hz
  have h_goal1 : (i : ℝ) * (Δ ^ a) ≤ z 0 := by
    calc (i : ℝ) * (Δ ^ a)
      ≤ (c : ℝ) * Δ ^ k * (Δ ^ a) := by gcongr <;> exact h_left1
    _ = (c : ℝ) * Δ ^ (a + k) := by rw [pow_add] <;> ring
    _ ≤ z 0 := hz.1.1
  have h_goal2 : z 0 < (i + 1 : ℝ) * (Δ ^ a) := by
    calc z 0
      < (c + 1 : ℝ) * Δ ^ (a + k) := hz.1.2
    _ = (c + 1 : ℝ) * Δ ^ k * (Δ ^ a) := by rw [pow_add] <;> ring
    _ ≤ (i + 1 : ℝ) * (Δ ^ a) := by gcongr <;> exact h_right1
  have h_goal3 : (j : ℝ) * (Δ ^ a) ≤ z 1 := by
    calc (j : ℝ) * (Δ ^ a)
      ≤ (d : ℝ) * Δ ^ k * (Δ ^ a) := by gcongr <;> exact h_left2
    _ = (d : ℝ) * Δ ^ (a + k) := by rw [pow_add] <;> ring
    _ ≤ z 1 := hz.2.1
  have h_goal4 : z 1 < (j + 1 : ℝ) * (Δ ^ a) := by
    calc z 1
      < (d + 1 : ℝ) * Δ ^ (a + k) := hz.2.2
    _ = (d + 1 : ℝ) * Δ ^ k * (Δ ^ a) := by rw [pow_add] <;> ring
    _ ≤ (j + 1 : ℝ) * (Δ ^ a) := by gcongr <;> exact h_right2
  simp only [dyadicSquare, Set.mem_setOf_eq, Set.mem_Ico]
  exact ⟨⟨h_goal1, h_goal2⟩, ⟨h_goal3, h_goal4⟩⟩

end DirecretisedFurstenbergEstimate.MultiscaleDecomposition
