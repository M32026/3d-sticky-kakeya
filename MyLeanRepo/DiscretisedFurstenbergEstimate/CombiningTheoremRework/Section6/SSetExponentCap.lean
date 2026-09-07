module

/-
  u0 Cap Interface for Coarse Branch

  Corollary 2.5 and the coarse ratio require the point-set exponent u0 ≤ 1.
  Given a u-dimensional S-set bound, construct a u0 = min(u, 1)-dimensional
  bound that works for all radii.

  Strategy:
  - If u ≤ 1, then u0 = u and the bound is unchanged.
  - If u > 1, then u0 = 1 < u, and we apply IsDeltaSSet.cap_exponent.
    For radii r ≤ 1: r^u ≤ r^1 (since base ≤ 1 and exponent larger means smaller).
    For radii r > 1: use the trivial bound A ∩ B(x,r) ⊆ A, and C * r^1 ≥ 1
    (since C ≥ 1 and r > 1), so the covering number of A is ≤ C * r * |A|_δ.

  This is a thin wrapper around IsDeltaSSet.cap_exponent from
  MultiscaleDecomposition/ExponentWeakening.lean.

  Whiteprint node: u0_cap_interface
  Status: IMPLEMENTED
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.ExponentWeakening
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate

/-- Cap the S-set exponent at u0 = min(u, 1).

    Given `IsDeltaSSet δ u C A` with `C ≥ 1`, produce
    `IsDeltaSSet δ (min u 1) C A`.

    This is needed by the coarse branch (CoarseRatioClean, CoarseBranchAdapters)
    which requires exponent u0 ≤ 1.

    The proof delegates to `IsDeltaSSet.cap_exponent`:
    - If u ≤ 1, min u 1 = u, so the statement is identical.
    - If u > 1, min u 1 = 1 ≤ u, and cap_exponent weakens the exponent. -/
lemma sset_cap_exponent_at_one {X : Type*} [PseudoMetricSpace X]
    {δ u C : ℝ} {A : Set X}
    (h : IsDeltaSSet δ u C A)
    (hC_one : 1 ≤ C) :
    IsDeltaSSet δ (min u 1) C A := by
  by_cases h_u_le_one : u ≤ 1
  · -- u ≤ 1: min u 1 = u
    have h_eq : min u 1 = u := by
      rw [min_eq_left] <;> linarith
    rw [h_eq]
    exact h
  · -- u > 1: min u 1 = 1 ≤ u
    have h_u_gt_one : 1 < u := by linarith
    have h_eq : min u 1 = 1 := by
      rw [min_eq_right] <;> linarith
    rw [h_eq]
    exact h.cap_exponent (by norm_num) (by linarith) hC_one

/-- Version with explicit u0 parameter: if u0 = min(u, 1), then
    `IsDeltaSSet δ u C A` implies `IsDeltaSSet δ u0 C A`. -/
lemma sset_cap_to_u0 {X : Type*} [PseudoMetricSpace X]
    {δ u u0 C : ℝ} {A : Set X}
    (h : IsDeltaSSet δ u C A)
    (hC_one : 1 ≤ C)
    (hu0_def : u0 = min u 1) :
    IsDeltaSSet δ u0 C A := by
  rw [hu0_def]
  exact sset_cap_exponent_at_one h hC_one

/-- Properties of u0 = min(u, 1) needed by the coarse branch:
    - u0 ≤ 1
    - u0 ≤ u
    - If s < u and u > 1, then s < u0 (since u0 = 1 and s < 1 is given separately)
    - If s < u and u ≤ 1, then s < u0 (since u0 = u) -/
lemma u0_cap_properties (u s : ℝ) (hs_one : s < 1) (hsu : s < u) :
    let u0 := min u 1
    u0 ≤ 1 ∧ u0 ≤ u ∧ s < u0 := by
  let u0 := min u 1
  have h_u0_le_one : u0 ≤ 1 := min_le_right _ _
  have h_u0_le_u : u0 ≤ u := min_le_left _ _
  have h_s_lt_u0 : s < u0 := by
    dsimp only [u0]
    by_cases h : u ≤ 1
    · rw [min_eq_left h] <;> linarith
    · rw [min_eq_right (by linarith)] <;> linarith
  exact ⟨h_u0_le_one, h_u0_le_u, h_s_lt_u0⟩

end DiscretisedFurstenbergEstimate

end
