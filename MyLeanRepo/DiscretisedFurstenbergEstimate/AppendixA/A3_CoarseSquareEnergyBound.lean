module

/-
  Energy bound for coarse square centers.

  Since distinct coarse squares have centers at Euclidean distance ≥ Δ,
  the s-energy is trivially bounded by Δ^{-s} * |Qset|^2.

  For global_2s_bound, set K_energy = Δ^{-s} / C_P.
  Then K_energy * C_P = Δ^{-s}, and K_energy * Δ^s = 1,
  so hP_large reduces to C_common * C_T * |Qset| ≥ 2.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HeavySquareRefinement
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA3

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.Lagoon (squareCenter)

/-- If two integers differ, their absolute difference is at least 1. -/
lemma int_abs_diff_ge_one {a b : ℤ} (h : a ≠ b) : (1 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| := by
  have h1 : a - b ≠ 0 := by
    intro h2
    have h3 : a = b := by linarith
    exact h h3
  have h4 : 1 ≤ |a - b| := Int.one_le_abs h1
  exact_mod_cast h4

/-- Distinct coarse square centers are at least Δ apart in Euclidean metric. -/
lemma square_center_dist_ge {Δ : ℝ} (hΔ_pos : 0 < Δ)
    {Q R : CoarseSquare Δ} (hne : Q ≠ R) :
    Δ ≤ dist (squareCenter Δ Q) (squareCenter Δ R) := by
  have h1 : (Q.1 : ℝ) ≠ (R.1 : ℝ) ∨ (Q.2 : ℝ) ≠ (R.2 : ℝ) := by
    by_contra h
    push Not at h
    have hQ1 : Q.1 = R.1 := by
      have h' : (Q.1 : ℝ) = (R.1 : ℝ) := h.1
      exact_mod_cast h'
    have hQ2 : Q.2 = R.2 := by
      have h' : (Q.2 : ℝ) = (R.2 : ℝ) := h.2
      exact_mod_cast h'
    apply hne
    ext <;> tauto
  have h_sq_ge_one : (1 : ℝ) ≤ (Q.1 - R.1 : ℝ)^2 + (Q.2 - R.2 : ℝ)^2 := by
    rcases h1 with (h1 | h1)
    · have h1' : Q.1 ≠ R.1 := by
        intro h
        apply h1
        exact_mod_cast h
      have h2 : (1 : ℝ) ≤ |(Q.1 : ℝ) - (R.1 : ℝ)| := int_abs_diff_ge_one h1'
      have h3 : (1 : ℝ) ≤ ((Q.1 : ℝ) - (R.1 : ℝ))^2 := by
        have h4 : |(Q.1 : ℝ) - (R.1 : ℝ)| ^ 2 = ((Q.1 : ℝ) - (R.1 : ℝ))^2 := by
          simp [sq_abs]
        nlinarith [abs_nonneg ((Q.1 : ℝ) - (R.1 : ℝ))]
      have h5 : 0 ≤ ((Q.2 : ℝ) - (R.2 : ℝ))^2 := by positivity
      linarith
    · have h1' : Q.2 ≠ R.2 := by
        intro h
        apply h1
        exact_mod_cast h
      have h2 : (1 : ℝ) ≤ |(Q.2 : ℝ) - (R.2 : ℝ)| := int_abs_diff_ge_one h1'
      have h3 : (1 : ℝ) ≤ ((Q.2 : ℝ) - (R.2 : ℝ))^2 := by
        have h4 : |(Q.2 : ℝ) - (R.2 : ℝ)| ^ 2 = ((Q.2 : ℝ) - (R.2 : ℝ))^2 := by
          simp [sq_abs]
        nlinarith [abs_nonneg ((Q.2 : ℝ) - (R.2 : ℝ))]
      have h5 : 0 ≤ ((Q.1 : ℝ) - (R.1 : ℝ))^2 := by positivity
      linarith
  set S : ℝ := (Q.1 - R.1 : ℝ)^2 + (Q.2 - R.2 : ℝ)^2 with hS
  have hS_nonneg : 0 ≤ S := by positivity
  have hS_ge_one : 1 ≤ S := h_sq_ge_one
  have h_sqrt_ge_one : (1 : ℝ) ≤ Real.sqrt S := by
    have h : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS_nonneg
    nlinarith [Real.sqrt_nonneg S]
  have h_coord0 : (squareCenter Δ Q - squareCenter Δ R) 0 = Δ * ((Q.1 : ℝ) - (R.1 : ℝ)) := by
    simp [squareCenter] <;> ring
  have h_coord1 : (squareCenter Δ Q - squareCenter Δ R) 1 = Δ * ((Q.2 : ℝ) - (R.2 : ℝ)) := by
    simp [squareCenter] <;> ring
  have h_norm2 : ‖squareCenter Δ Q - squareCenter Δ R‖ ^ 2 =
      ((squareCenter Δ Q - squareCenter Δ R) 0)^2 + ((squareCenter Δ Q - squareCenter Δ R) 1)^2 := by
    let v := squareCenter Δ Q - squareCenter Δ R
    have h_nonneg : 0 ≤ (v 0)^2 + (v 1)^2 := by positivity
    have h_norm : ‖v‖ = Real.sqrt ((v 0)^2 + (v 1)^2) := by
      simpa [EuclideanSpace.norm_eq] using rfl
    rw [h_norm]
    rw [Real.sq_sqrt h_nonneg]
  have h_main : ‖squareCenter Δ Q - squareCenter Δ R‖ ^ 2 = Δ^2 * S := by
    rw [h_norm2, h_coord0, h_coord1, hS] <;> ring
  have h_dist : dist (squareCenter Δ Q) (squareCenter Δ R) = ‖squareCenter Δ Q - squareCenter Δ R‖ := by
    rfl
  rw [h_dist]
  have h6 : ‖squareCenter Δ Q - squareCenter Δ R‖ ^ 2 ≥ Δ^2 := by
    rw [h_main]
    have h7 : Δ^2 * S ≥ Δ^2 := by
      have h8 : 0 ≤ Δ^2 := by positivity
      nlinarith
    exact h7
  have h9 : 0 ≤ ‖squareCenter Δ Q - squareCenter Δ R‖ := by positivity
  nlinarith [hΔ_pos]

/-- For x ≥ y > 0 and s > 0, x^{-s} ≤ y^{-s}. -/
lemma rpow_neg_le_of_le {x y s : ℝ} (hx_pos : 0 < x) (hy_pos : 0 < y)
    (h : y ≤ x) (hs_pos : 0 < s) :
    Real.rpow x (-s) ≤ Real.rpow y (-s) := by
  have h1 : Real.rpow y s ≤ Real.rpow x s := Real.rpow_le_rpow hy_pos.le h hs_pos.le
  have h2 : 0 < Real.rpow x s := Real.rpow_pos_of_pos hx_pos _
  have h3 : 0 < Real.rpow y s := Real.rpow_pos_of_pos hy_pos _
  have h4 : (Real.rpow x s)⁻¹ ≤ (Real.rpow y s)⁻¹ := by
    have h41 : 1 / (Real.rpow x s) ≤ 1 / (Real.rpow y s) := one_div_le_one_div_of_le h3 h1
    simpa [one_div] using h41
  have h5 : Real.rpow x (-s) = (Real.rpow x s)⁻¹ := by
    have h51 : x ^ ((-s) + s) = (x ^ (-s)) * (x ^ s) := Real.rpow_add hx_pos (-s) s
    have h52 : (-s) + s = 0 := by ring
    rw [h52] at h51
    have h53 : x ^ (0 : ℝ) = 1 := by simp
    rw [h53] at h51
    have h54 : (x ^ (-s)) * (x ^ s) = 1 := h51.symm
    have h_goal : Real.rpow x (-s) * Real.rpow x s = 1 := by
      have h1 : (x ^ (-s)) = Real.rpow x (-s) := Eq.symm (Real.rpow_eq_pow x (-s))
      have h2 : (x ^ s) = Real.rpow x s := Eq.symm (Real.rpow_eq_pow x s)
      rw [h1, h2] at h54
      exact h54
    field_simp [h2.ne'] at h_goal ⊢ <;> exact h_goal
  have h7 : Real.rpow y (-s) = (Real.rpow y s)⁻¹ := by
    have h71 : y ^ ((-s) + s) = (y ^ (-s)) * (y ^ s) := Real.rpow_add hy_pos (-s) s
    have h72 : (-s) + s = 0 := by ring
    rw [h72] at h71
    have h73 : y ^ (0 : ℝ) = 1 := by simp
    rw [h73] at h71
    have h74 : (y ^ (-s)) * (y ^ s) = 1 := h71.symm
    have h_goal : Real.rpow y (-s) * Real.rpow y s = 1 := by
      have h1 : (y ^ (-s)) = Real.rpow y (-s) := Eq.symm (Real.rpow_eq_pow y (-s))
      have h2 : (y ^ s) = Real.rpow y s := Eq.symm (Real.rpow_eq_pow y s)
      rw [h1, h2] at h74
      exact h74
    field_simp [h3.ne'] at h_goal ⊢ <;> exact h_goal
  rw [h5, h7]
  exact h4

/-- Energy bound for coarse square centers.
    Returns K_energy = Δ^{-s} / C_P so that K_energy * C_P = Δ^{-s}. -/
lemma coarse_square_energy_bound
    {Δ s C_P : ℝ} (hΔ_pos : 0 < Δ) (hs_pos : 0 < s) (hCP_pos : 0 < C_P)
    {Qset : Finset (CoarseSquare Δ)} :
    ∃ (K_energy : ℝ), 0 < K_energy ∧
      ∑ Q ∈ Qset, ∑ R ∈ Qset.erase Q,
        Real.rpow (dist (squareCenter Δ Q) (squareCenter Δ R)) (-s) ≤
        K_energy * C_P * (Qset.card : ℝ)^2 := by
  let K_energy : ℝ := Real.rpow Δ (-s) / C_P
  have hK_pos : 0 < K_energy := by
    have h1 : 0 < Real.rpow Δ (-s) := Real.rpow_pos_of_pos hΔ_pos _
    positivity
  have h_rpow_le : ∀ (Q R : CoarseSquare Δ), (hne : Q ≠ R) →
      Real.rpow (dist (squareCenter Δ Q) (squareCenter Δ R)) (-s) ≤ Real.rpow Δ (-s) := by
    intro Q R hne
    set d := dist (squareCenter Δ Q) (squareCenter Δ R) with hd
    have h3 : Δ ≤ d := square_center_dist_ge hΔ_pos hne
    have h4 : 0 < d := by linarith [hΔ_pos]
    exact rpow_neg_le_of_le h4 hΔ_pos h3 hs_pos
  have h_inner : ∀ Q ∈ Qset,
      ∑ R ∈ Qset.erase Q, Real.rpow (dist (squareCenter Δ Q) (squareCenter Δ R)) (-s) ≤
        Real.rpow Δ (-s) * (Qset.card : ℝ) := by
    intro Q hQ
    have h2 : ∀ R ∈ Qset.erase Q,
        Real.rpow (dist (squareCenter Δ Q) (squareCenter Δ R)) (-s) ≤ Real.rpow Δ (-s) := by
      intro R hR
      have hne : R ≠ Q := (Finset.mem_erase.mp hR).1
      exact h_rpow_le Q R (Ne.symm hne)
    calc ∑ R ∈ Qset.erase Q, Real.rpow (dist (squareCenter Δ Q) (squareCenter Δ R)) (-s)
      ≤ ∑ R ∈ Qset.erase Q, Real.rpow Δ (-s) := Finset.sum_le_sum h2
    _ = Real.rpow Δ (-s) * ((Qset.erase Q).card : ℝ) := by
        simp [Finset.sum_const] <;> ring
    _ ≤ Real.rpow Δ (-s) * (Qset.card : ℝ) := by
        have h3 : ((Qset.erase Q).card : ℝ) ≤ (Qset.card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.erase_subset Q Qset)
        have h4 : 0 ≤ Real.rpow Δ (-s) := Real.rpow_nonneg hΔ_pos.le _
        nlinarith
  have h_main : ∑ Q ∈ Qset, ∑ R ∈ Qset.erase Q,
        Real.rpow (dist (squareCenter Δ Q) (squareCenter Δ R)) (-s) ≤
      Real.rpow Δ (-s) * (Qset.card : ℝ)^2 := by
    calc ∑ Q ∈ Qset, ∑ R ∈ Qset.erase Q, Real.rpow (dist (squareCenter Δ Q) (squareCenter Δ R)) (-s)
      ≤ ∑ Q ∈ Qset, (Real.rpow Δ (-s) * (Qset.card : ℝ)) :=
        Finset.sum_le_sum h_inner
    _ = Real.rpow Δ (-s) * (Qset.card : ℝ) * (Qset.card : ℝ) := by
        rw [Finset.sum_const] <;> ring
    _ = Real.rpow Δ (-s) * (Qset.card : ℝ)^2 := by ring
  refine ⟨K_energy, hK_pos, ?_⟩
  have h5 : K_energy * C_P = Real.rpow Δ (-s) := by
    dsimp only [K_energy]
    field_simp [hCP_pos.ne'] <;> ring
  rw [h5]
  exact h_main

end DirecretisedFurstenbergEstimate.AppendixA3
