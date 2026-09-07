module

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set Classical

namespace IsDeltaSCSet

/-- Exponent monotonicity for `(δ,s,C)`-sets: if `s₂ ≤ s₁`, then a
`(δ,s₁,C)`-set is automatically a `(δ,s₂,C)`-set with the same constant.

Reason: for dyadic side length `0 < r ≤ 1`, we have `r^s₁ ≤ r^s₂`, so the
non-concentration bound with the larger exponent implies the bound with the
smaller exponent. -/
lemma monotone_exponent
    {d : ℕ} {δ s₁ s₂ C : ℝ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    (h : IsDeltaSCSet δ s₁ C P)
    (h_le : s₂ ≤ s₁) (hs₂_nonneg : 0 ≤ s₂) :
    IsDeltaSCSet δ s₂ C P := by
  rcases h with ⟨h_bdd, h_nonempty, h_d, h_δ_dyadic, h_δ_pos,
    h_s₁_nonneg, h_s₁_le_d, h_C_pos, h_main⟩
  have h_s₂_le_d : s₂ ≤ (d : ℝ) := by linarith
  refine' ⟨h_bdd, h_nonempty, h_d, h_δ_dyadic, h_δ_pos,
    hs₂_nonneg, h_s₂_le_d, h_C_pos, _⟩
  intro r Q hr_dyadic hQ hδ_le hr_le_one
  have h1 := h_main hr_dyadic hQ hδ_le hr_le_one
  have h_r_pos : 0 < r := by linarith [h_δ_pos]
  have h2 : r ^ s₁ ≤ r ^ s₂ := by
    apply Real.rpow_le_rpow_of_exponent_le_or_ge
    exact Or.inr ⟨h_r_pos, hr_le_one, h_le⟩
  have h3 : ENNReal.ofReal (r ^ s₁) ≤ ENNReal.ofReal (r ^ s₂) := by
    exact ENNReal.ofReal_le_ofReal h2
  calc ENat.toENNReal (dyadicCoveringNumber δ (P ∩ Q))
    ≤ ENNReal.ofReal C * ENat.toENNReal (dyadicCoveringNumber δ P) *
        ENNReal.ofReal (r ^ s₁) := h1
  _ ≤ ENNReal.ofReal C * ENat.toENNReal (dyadicCoveringNumber δ P) *
        ENNReal.ofReal (r ^ s₂) := by
    exact mul_le_mul_of_nonneg_left h3 (by positivity)

end IsDeltaSCSet

namespace IsRealDeltaSet

/-- Exponent monotonicity for real-line `(δ,s,C)`-sets. -/
lemma monotone_exponent
    {δ s₁ s₂ C : ℝ} {A : Set ℝ}
    (h : IsRealDeltaSet δ s₁ C A)
    (h_le : s₂ ≤ s₁) (hs₂_nonneg : 0 ≤ s₂) :
    IsRealDeltaSet δ s₂ C A :=
  IsDeltaSCSet.monotone_exponent h h_le hs₂_nonneg

end IsRealDeltaSet
