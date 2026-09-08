/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDescentSite

/-!
# Discharging `hsite`: the rows the descent block can produce

`Kakeya.ML2Core.geometricCoreAt_of_site` reduces `ML2Assembly.GeometricCoreAt` to one hypothesis.
 the parameter comparison classifies every row of it; this file compiles the rows marked
PRODUCIBLE-now, so that what is left of the closure is the two rows marked WAITING.

## The outer transfer — a gap in the site wiring, found by measuring the producer

`Kakeya.ML2Core.exists_dichotomyLeft_or_window_spine_levels` hands back a hierarchy on the
**retained** family `u' ⊆ s`, not on `s`, while `Kakeya.ML2Assembly.Dichotomy`'s conclusion is about
`s`.  One outer step is therefore missing from `hsite` as first cut, and the chain supplies exactly
what closes it: a mass ledger `s → u'` and `u' ⊆ s`.  An exit proved at `u'` transfers to `s` at one
further loss factor, of exactly the shape the two absorptions already spend
(`Kakeya.ML2Core.descent_disjuncts_transfer_to_ambient`).

Recorded as a defect of the site wiring, not of the chain: both readings typecheck at the level of
the existential, so it would not have surfaced until the discharge.

## And the top state carries `T`, not `W`

The chain gives `ML2Shaded.HasDenseShading lam u' (fun i ↦ (T i).toShadedBody)` — on the **ambient**
shading — and only an *aggregate* bound for the refined `W`.  So the descent's top state is
`(u', T, lam)`; `W` appears only inside the trial.  The window transports because
`(W i).toTube = (T i).toTube`.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Core


/-! ## The arithmetic rows of `hsite` -/

section ArithmeticRows

variable {ι : Type*} {δ : NNReal}

/-- **The absorption shape, once.**  Every ledger row of `hsite` is this lemma at a different
exponent: `Λ ^ P ≤ δ^{-α}` (which is `T-D5`) moves any `δ^x` down by exactly the margin `α`. -/
theorem absorb_of_loss_le {Λ : ℝ≥0∞} {P : ℕ} {α x : ℝ} (hδ0 : 0 < δ)
    (hΛ : Λ ^ P ≤ (δ : ℝ≥0∞) ^ (-α)) :
    Λ ^ P * (δ : ℝ≥0∞) ^ x ≤ (δ : ℝ≥0∞) ^ (x - α) := by
  have hne : (δ : ℝ≥0∞) ≠ 0 := by simpa using hδ0.ne'
  calc Λ ^ P * (δ : ℝ≥0∞) ^ x ≤ (δ : ℝ≥0∞) ^ (-α) * (δ : ℝ≥0∞) ^ x :=
        mul_le_mul' hΛ le_rfl
    _ = (δ : ℝ≥0∞) ^ (-α + x) := (ENNReal.rpow_add _ _ hne ENNReal.coe_ne_top).symm
    _ = (δ : ℝ≥0∞) ^ (x - α) := by ring_nf

/-- **`hsite` row 16, the left absorption**, at the trial's exit `ε₀ = β/2 − α`. -/
theorem absorbL_of_loss_le {Λ : ℝ≥0∞} {P : ℕ} {α β : ℝ} (hδ0 : 0 < δ)
    (hΛ : Λ ^ P ≤ (δ : ℝ≥0∞) ^ (-α)) :
    Λ ^ P * (δ : ℝ≥0∞) ^ (-(β / 2 - α)) ≤ (δ : ℝ≥0∞) ^ (-(β / 2)) := by
  have h := absorb_of_loss_le (δ := δ) (Λ := Λ) (P := P) (α := α) (x := -(β / 2 - α)) hδ0 hΛ
  have he : -(β / 2 - α) - α = -(β / 2) := by ring
  rwa [he] at h

/-- **`hsite` row 17, the right absorption**, at the trial's exit `g = 4ν + α`. -/
theorem absorbR_of_loss_le {Λ : ℝ≥0∞} {P : ℕ} {α ν : ℝ} (hδ0 : 0 < δ)
    (hΛ : Λ ^ P ≤ (δ : ℝ≥0∞) ^ (-α)) :
    Λ ^ P * (δ : ℝ≥0∞) ^ (4 * ν + α) ≤ (δ : ℝ≥0∞) ^ (4 * ν) := by
  have h := absorb_of_loss_le (δ := δ) (Λ := Λ) (P := P) (α := α) (x := 4 * ν + α) hδ0 hΛ
  have he : 4 * ν + α - α = 4 * ν := by ring
  rwa [he] at h

/-- **`hsite` row 7** — the descent's ambient family is the *retained* `u' ⊆ s`, so the block's
cardinality binder passes to it for free. -/
theorem card_le_of_subset_of_card_le {s u' : Finset ι} (hsub : u' ⊆ s) {x : ℝ}
    (hs : (s.card : ℝ) ≤ (δ : ℝ) ^ x) : (u'.card : ℝ) ≤ (δ : ℝ) ^ x :=
  le_trans (by exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hsub)) hs

/-- **`hsite` row 8:** the hierarchy constant is independent of `δ`.
`exists_dichotomyLeft_or_window_spine_levels` chooses `C` before `∀ᶠ δ` and
returns `Cu = max C 4`, so the condition depending on `δ` is a threshold. -/
theorem exists_threshold_const_le_rpow_neg_one (Cu₀ : NNReal) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ → ∀ Cu : NNReal, Cu ≤ Cu₀ →
        (Cu : ℝ) ≤ (δ : ℝ) ^ (-(1 : ℝ)) := by
  refine ⟨min 1 (max 1 Cu₀)⁻¹, ?_, min_le_left _ _, ?_⟩
  · refine lt_min zero_lt_one (inv_pos.mpr ?_)
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  intro δ hδ hδle Cu hCu
  have hM1 : (1 : NNReal) ≤ max 1 Cu₀ := le_max_left _ _
  have hMR : (1 : ℝ) ≤ ((max 1 Cu₀ : NNReal) : ℝ) := by exact_mod_cast hM1
  have hδR : (0 : ℝ) < (δ : ℝ) := hδ
  have hδinv : (δ : ℝ) ≤ ((max 1 Cu₀ : NNReal) : ℝ)⁻¹ := by
    have := le_trans hδle (min_le_right (1 : NNReal) (max 1 Cu₀)⁻¹)
    have hc : ((((max 1 Cu₀ : NNReal))⁻¹ : NNReal) : ℝ) = ((max 1 Cu₀ : NNReal) : ℝ)⁻¹ := by
      push_cast; ring
    rw [← hc]; exact_mod_cast this
  have hrw : (δ : ℝ) ^ (-(1 : ℝ)) = ((δ : ℝ))⁻¹ := by
    rw [Real.rpow_neg_one]
  rw [hrw]
  have hCuR : (Cu : ℝ) ≤ ((max 1 Cu₀ : NNReal) : ℝ) :=
    le_trans (by exact_mod_cast hCu) (by exact_mod_cast le_max_right (1 : NNReal) Cu₀)
  refine le_trans hCuR ?_
  rw [le_inv_comm₀ (lt_of_lt_of_le zero_lt_one hMR) hδR]
  exact hδinv

end ArithmeticRows


end Kakeya.ML2Core
