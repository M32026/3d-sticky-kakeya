/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Real.Basic

/-!
# Ordered field helpers

Cancellation lemmas for inequalities involving a division, in the degenerate-denominator
form in which they arise from volume comparisons.
-/

@[expose] public section

/-- A lower bound `A > 0` competing against the upper bound `A * c / M` forces `M < c`,
the case `M = 0` being vacuous. -/
theorem lt_of_lt_mul_div {A c M : ℝ} (hA : 0 < A) (hc : 0 < c)
    (hM : 0 ≤ M) (h : 0 < M → A < A * c / M) : M < c :=
  hM.eq_or_lt.elim (· ▸ hc) fun hM ↦ lt_of_mul_lt_mul_left ((lt_div_iff₀ hM).1 (h hM)) hA.le

/-- Rescaling by `t⁻¹` trades a `t`-scaled bound for an absolute one. -/
lemma abs_inv_mul_le_iff {t : ℝ} (ht : 0 < t) (a K : ℝ) :
    |t⁻¹ * a| ≤ K ↔ |a| ≤ t * K := by
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr ht.le), inv_mul_le_iff₀ ht]
