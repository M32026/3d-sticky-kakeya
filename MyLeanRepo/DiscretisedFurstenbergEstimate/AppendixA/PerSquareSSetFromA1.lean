module

/-
  Helper: derive per-square S-set from A1_Output using per_square_sset_restriction.

  Given a1 : A1_Output Δ δ u s ε and Q ∈ a1.Qset, produces
  IsDeltaSSet δ u (9 * Δ^{-u-29ε/4}) (a1.points Q hQ).

  Also proves the absorption C_P * 81 ≤ Δ^{-u-8ε} where
  C_P = 9 * Δ^{-u-29ε/4}.

  Whiteprint node: per_square_sset_from_a1
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.SSetRestriction
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

/-- Derive per-square S-set from A1_Output global S-set.

    Uses `per_square_sset_restriction` with:
    - S = a1.P_all (global S-set)
    - S' = a1.points Q hQ (per-square points)
    - Card bounds from A1_Output fields. -/
lemma per_square_sset_from_a1
    {Δ δ u s ε : ℝ}
    (hΔ_pos : 0 < Δ)
    (hδ_pos : 0 < δ)
    (hδ_eq : δ = Δ ^ 2)
    (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    (hε_pos : 0 < ε)
    (hu_nonneg : 0 ≤ u)
    (a1 : A1_Output Δ δ u s ε)
    (Q : CoarseSquare Δ) (hQ : Q ∈ a1.Qset) :
    IsDeltaSSet δ u (9 * Real.rpow Δ (-u - 29 * ε / 4))
      (a1.points Q hQ : Set Plane) := by
  let S := a1.P_all
  let S' := a1.points Q hQ

  have hS'_nonempty : S'.Nonempty := by
    have h1 : (S'.card : ℝ) ≥ Real.rpow Δ (-u + 3 * ε) :=
      a1.h_points_card_lower Q hQ
    have h2 : 0 < Real.rpow Δ (-u + 3 * ε) :=
      Real.rpow_pos_of_pos hΔ_pos (-u + 3 * ε)
    have h3 : 0 < (S'.card : ℝ) := by linarith
    exact Finset.card_pos.mp (by exact_mod_cast h3)

  exact per_square_sset_restriction
    hδ_pos hΔ_pos hδ_eq h_small hε_pos
    (S := S) (S' := S')
    a1.hP_all_sset
    (a1.h_points_sub_all Q hQ)
    (a1.h_separated Q hQ)
    a1.hP_all_card_upper
    (a1.h_points_card_lower Q hQ)
    hS'_nonempty

/-- Absorption: C_P * 81 ≤ Δ^{-u-8ε} where C_P = 9 * Δ^{-u-29ε/4}.

    Derived from h_small : Δ^{ε/4} ≤ 1/100:
    Δ^{3ε/4} = Δ^{ε/4} * Δ^{ε/4} * Δ^{ε/4} ≤ 10^{-6} < 1/729,
    so 729 ≤ Δ^{-3ε/4}, hence
    729 * Δ^{-u-29ε/4} ≤ Δ^{-u-8ε}. -/
lemma absorb_C_P_times_81
    {Δ u ε : ℝ}
    (hΔ_pos : 0 < Δ)
    (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    (hε_pos : 0 < ε) :
    (9 * Real.rpow Δ (-u - 29 * ε / 4)) * 81 ≤ Real.rpow Δ (-u - 8 * ε) := by
  set x := Real.rpow Δ (ε / 4) with hx_def
  have hx_nonneg : 0 ≤ x := Real.rpow_nonneg hΔ_pos.le _
  have hx_pos : 0 < x := Real.rpow_pos_of_pos hΔ_pos (ε / 4)
  have hx_le : x ≤ 1 / 100 := h_small

  -- Δ^{3ε/4} = Δ^{ε/4} * Δ^{ε/4} * Δ^{ε/4}
  have h_rpow3 : Real.rpow Δ (3 * ε / 4) = x * x * x := by
    have h1 : Real.rpow Δ (ε / 2) = x * x := by
      have h_add := Real.rpow_add hΔ_pos (ε / 4) (ε / 4)
      have h_eq : (ε / 4 : ℝ) + (ε / 4) = ε / 2 := by ring
      rw [h_eq] at h_add
      exact h_add
    have h2 : Real.rpow Δ (3 * ε / 4) = Real.rpow Δ (ε / 2) * x := by
      have h_add := Real.rpow_add hΔ_pos (ε / 2) (ε / 4)
      have h_eq : (ε / 2 : ℝ) + (ε / 4) = 3 * ε / 4 := by ring
      rw [h_eq] at h_add
      exact h_add
    rw [h2, h1] <;> ring

  -- Δ^{3ε/4} ≤ 1/1000000
  have h1 : Real.rpow Δ (3 * ε / 4) ≤ 1 / 1000000 := by
    rw [h_rpow3]
    have h3 : x * x * x ≤ (1 / 100 : ℝ) * (1 / 100 : ℝ) * (1 / 100 : ℝ) := by
      gcongr <;> linarith
    have h4 : (1 / 100 : ℝ) * (1 / 100 : ℝ) * (1 / 100 : ℝ) = (1 / 1000000 : ℝ) := by norm_num
    rw [h4] at h3
    exact h3

  -- 0 < Δ^{3ε/4}
  have h_pos3 : 0 < Real.rpow Δ (3 * ε / 4) := Real.rpow_pos_of_pos hΔ_pos (3 * ε / 4)

  -- 729 ≤ Δ^{-3ε/4}
  have h5 : (729 : ℝ) ≤ Real.rpow Δ (-3 * ε / 4) := by
    have h6 : Real.rpow Δ (-3 * ε / 4) * Real.rpow Δ (3 * ε / 4) = 1 := by
      have h_add : Real.rpow Δ ((-3 * ε / 4) + (3 * ε / 4)) =
          Real.rpow Δ (-3 * ε / 4) * Real.rpow Δ (3 * ε / 4) :=
        Real.rpow_add hΔ_pos (-3 * ε / 4) (3 * ε / 4)
      have h_sum : (-3 * ε / 4 : ℝ) + (3 * ε / 4) = 0 := by ring
      have h7 : Real.rpow Δ ((-3 * ε / 4) + (3 * ε / 4)) = 1 := by
        rw [h_sum]
        <;> simp
      have h8 : Real.rpow Δ (-3 * ε / 4) * Real.rpow Δ (3 * ε / 4) =
          Real.rpow Δ ((-3 * ε / 4) + (3 * ε / 4)) := h_add.symm
      rw [h8, h7]
    have h9 : Real.rpow Δ (-3 * ε / 4) = 1 / Real.rpow Δ (3 * ε / 4) := by
      apply mul_left_cancel₀ h_pos3.ne'
      have h_left : Real.rpow Δ (3 * ε / 4) * Real.rpow Δ (-3 * ε / 4) = 1 := by
        rw [mul_comm]
        exact h6
      have h_right : Real.rpow Δ (3 * ε / 4) * (1 / Real.rpow Δ (3 * ε / 4)) = 1 := by
        field_simp [h_pos3.ne'] <;> ring
      rw [h_left, h_right]
    rw [h9]
    have h10 : 0 < Real.rpow Δ (3 * ε / 4) := h_pos3
    have h11 : Real.rpow Δ (3 * ε / 4) ≤ 1 / 729 := by
      calc Real.rpow Δ (3 * ε / 4)
        ≤ 1 / 1000000 := h1
      _ ≤ 1 / 729 := by norm_num
    have h12 : (729 : ℝ) ≤ 1 / Real.rpow Δ (3 * ε / 4) := by
      calc (729 : ℝ)
        = 1 / (1 / 729 : ℝ) := by norm_num
      _ ≤ 1 / Real.rpow Δ (3 * ε / 4) := by
        gcongr
        <;> exact h11
    exact h12

  -- 729 * Δ^{-u-29ε/4} ≤ Δ^{-3ε/4} * Δ^{-u-29ε/4}
  have h13 : (729 : ℝ) * Real.rpow Δ (-u - 29 * ε / 4) ≤
      Real.rpow Δ (-3 * ε / 4) * Real.rpow Δ (-u - 29 * ε / 4) := by
    have h14 : 0 ≤ Real.rpow Δ (-u - 29 * ε / 4) := Real.rpow_nonneg hΔ_pos.le _
    exact mul_le_mul_of_nonneg_right h5 h14

  -- Δ^{-3ε/4} * Δ^{-u-29ε/4} = Δ^{-u-8ε}
  have h15 : Real.rpow Δ (-3 * ε / 4) * Real.rpow Δ (-u - 29 * ε / 4) =
      Real.rpow Δ (-u - 8 * ε) := by
    have h_sum : (-3 * ε / 4 : ℝ) + (-u - 29 * ε / 4) = -u - 8 * ε := by ring
    have h16 := Real.rpow_add hΔ_pos (-3 * ε / 4) (-u - 29 * ε / 4)
    rw [h_sum] at h16
    exact h16.symm

  have h_main : (9 * Real.rpow Δ (-u - 29 * ε / 4)) * 81 =
      (729 : ℝ) * Real.rpow Δ (-u - 29 * ε / 4) := by ring
  rw [h_main]
  rw [h15] at h13
  exact h13

end DirecretisedFurstenbergEstimate.AppendixA
