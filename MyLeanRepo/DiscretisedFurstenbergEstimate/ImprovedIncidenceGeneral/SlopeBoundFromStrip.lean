module

/-
  Phase 1 utility: Slope bound from a-index strip constraint.

  Given the B1 bridge hypothesis `h_tubes_strip` (a-index in [-2^n, 2^n)),
  proves |T.slope| ≤ 1 for any DyadicTube.

  Dependencies: DyadicTubes (DyadicTube, slope, dyadicDelta).
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DiscretisedFurstenbergEstimate

variable {n : ℕ}

/-- From the a-index strip constraint |T.a| < 2^n, derive |T.slope| ≤ 1. -/
lemma slope_bound_from_strip (T : DyadicTube n)
    (h_strip : -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ)) :
    |T.slope| ≤ 1 := by
  set δ := dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_eq : δ = 1 / (2 ^ n : ℝ) := by
    simp [hδ, dyadicDelta] <;> field_simp <;> ring
  have h1 : -(2 ^ n : ℝ) ≤ (T.a : ℝ) := by exact_mod_cast h_strip.1
  have h2 : (T.a : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast h_strip.2
  have h3 : |(T.a : ℝ)| ≤ (2 ^ n : ℝ) := by
    rw [abs_le] <;> constructor <;> linarith
  have h4 : T.slope = (T.a : ℝ) * δ := by rfl
  rw [h4, hδ_eq]
  have h5 : |(T.a : ℝ) * (1 / (2 ^ n : ℝ))| = |(T.a : ℝ)| / (2 ^ n : ℝ) := by
    rw [abs_mul, abs_div, abs_of_pos (show (0 : ℝ) < 2 ^ n by positivity)]
    <;> ring
  rw [h5]
  have h6 : 0 < (2 ^ n : ℝ) := by positivity
  have h7 : |(T.a : ℝ)| / (2 ^ n : ℝ) ≤ 1 := by
    apply (div_le_one h6).mpr
    exact h3
  exact h7

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
