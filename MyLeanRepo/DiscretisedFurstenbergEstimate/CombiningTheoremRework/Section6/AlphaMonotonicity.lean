module

/-
  Alpha Monotonicity Lemmas

  Properties of α(t) = (min(t, 1) - s) / (1 - s) used by the coarse branch.

  - α is monotone in t: t ≤ u → α(t) ≤ α(u)
  - α > 0 when s < t
  - α ≤ 1 always (since min(t,1) ≤ 1)

  Whiteprint node: alpha_monotonicity
  Status: IMPLEMENTED
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

namespace DiscretisedFurstenbergEstimate

/-- α(t) = (min(t, 1) - s) / (1 - s) is monotone in t. -/
lemma alpha_monotonicity (s t u : ℝ) (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (htu : t ≤ u) :
    (min t 1 - s) / (1 - s) ≤ (min u 1 - s) / (1 - s) := by
  have h1 : min t 1 ≤ min u 1 := by
    gcongr <;> linarith
  have h2 : 0 < 1 - s := by linarith
  have h3 : min t 1 - s ≤ min u 1 - s := by linarith
  exact div_le_div_of_nonneg_right h3 (by linarith)

/-- α(t) > 0 when s < t. -/
lemma alpha_pos (s t : ℝ) (hs : 0 < s) (hs1 : s < 1) (hst : s < t) :
    0 < (min t 1 - s) / (1 - s) := by
  have h1 : s < min t 1 := by
    apply lt_min hst hs1
  have h2 : 0 < min t 1 - s := by linarith
  have h3 : 0 < 1 - s := by linarith
  exact div_pos h2 h3

/-- α(t) ≤ 1 since min(t, 1) ≤ 1. -/
lemma alpha_le_one (s t : ℝ) (hs : 0 < s) (hs1 : s < 1) (hst : s < t) :
    (min t 1 - s) / (1 - s) ≤ 1 := by
  have h1 : min t 1 ≤ 1 := min_le_right _ _
  have h2 : min t 1 - s ≤ 1 - s := by linarith
  have h3 : 0 < 1 - s := by linarith
  have h4 : (min t 1 - s) / (1 - s) ≤ (1 - s) / (1 - s) := by
    gcongr <;> linarith
  have h5 : (1 - s) / (1 - s) = 1 := by
    field_simp [h3.ne'] <;> ring
  rw [h5] at h4
  exact h4

end DiscretisedFurstenbergEstimate

end
