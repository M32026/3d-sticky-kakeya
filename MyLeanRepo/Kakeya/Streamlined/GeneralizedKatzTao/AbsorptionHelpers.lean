import MyLeanRepo.Kakeya.Streamlined.Basic
import MyLeanRepo.Kakeya.Streamlined.Estimates
import MyLeanRepo.Kakeya.Streamlined.Families
import Mathlib.Tactic

/-!
# Absorption helpers for the generalized Katz-Tao theorem

Provides lemmas for absorbing constants and extraction factors into
subpolynomial `δ`-powers.

## Main lemma

`absorb_extraction_factor`: given `D ≤ δ^(-η)`, `C` a constant, and
`η*β < ε - ε'`, then for small enough `δ`:

    C * D * δ^(-ε') ≤ δ^(-ε) * D^(1-β)

The key intermediate step is `C * D^β ≤ δ^(-(ε-ε'))`, which follows from
`D^β ≤ δ^(-ηβ)` and `C ≤ δ^(-((ε-ε') - ηβ))`.
-/

noncomputable section

namespace Kakeya.Streamlined

open MeasureTheory

/-! ### Helper lemmas for realRpowENN -/

/-- `(δ^a)^b = δ^(a*b)` in ENNReal, for `δ > 0` and `b ≥ 0`. -/
lemma realRpowENN_rpow {δ a b : ℝ} (hδ_pos : 0 < δ) (hb_nonneg : 0 ≤ b) :
    ENNReal.rpow (Kakeya.realRpowENN δ a) b = Kakeya.realRpowENN δ (a * b) := by
  have h1 : 0 ≤ Real.rpow δ a := Real.rpow_nonneg (by linarith) a
  have h2 : ENNReal.rpow (ENNReal.ofReal (Real.rpow δ a)) b =
      ENNReal.ofReal ((Real.rpow δ a) ^ b) :=
    ENNReal.ofReal_rpow_of_nonneg h1 hb_nonneg
  have h3 : (Real.rpow δ a) ^ b = Real.rpow δ (a * b) := by
    exact (Real.rpow_mul (by linarith) a b).symm
  simp only [Kakeya.realRpowENN, h2, h3]
  <;> rfl

/-- `δ^(a+b) = δ^a * δ^b` in ENNReal. -/
lemma realRpowENN_add' {δ a b : ℝ} (hδ_pos : 0 < δ) :
    Kakeya.realRpowENN δ (a + b) = Kakeya.realRpowENN δ a * Kakeya.realRpowENN δ b := by
  simp only [Kakeya.realRpowENN]
  have h1 : Real.rpow δ (a + b) = Real.rpow δ a * Real.rpow δ b :=
    Real.rpow_add (by linarith) a b
  rw [h1]
  have h2 : 0 ≤ Real.rpow δ a := Real.rpow_nonneg (by linarith) a
  rw [← ENNReal.ofReal_mul h2]
  <;> rfl

/-! ### Absorption lemma -/

/-- Absorb an extraction factor into a subpolynomial δ-power.

Given `D ≤ δ^(-η)`, `C` a constant, and `η*β < ε - ε'`, then
`C * D * δ^(-ε') ≤ δ^(-ε) * D^(1-β)`, provided
`C ≤ δ^(-((ε-ε') - ηβ))`.

The proof goes through `C * D^β ≤ δ^(-(ε-ε'))`, then multiplies by
`D^(1-β) * δ^(-ε')` and combines exponents. -/
lemma absorb_extraction_factor
    {δ eta epsilon epsilon' beta : ℝ} (hβ : 0 ≤ beta) (hβ1 : beta ≤ 1)
    {D : ENNReal} {C : ENNReal}
    (hD_small : D ≤ Kakeya.realRpowENN δ (-eta))
    (hC_ne_top : C ≠ ⊤) (hD_ne_top : D ≠ ⊤)
    (h_gap : eta * beta < epsilon - epsilon')
    (hδ_pos : 0 < δ) (hδ1 : δ ≤ 1)
    (hC_absorb : C ≤ Kakeya.realRpowENN δ (-(epsilon - epsilon' - eta * beta))) :
    C * D * Kakeya.realRpowENN δ (-epsilon') ≤
    Kakeya.realRpowENN δ (-epsilon) * ENNReal.rpow D (1 - beta) := by
  have h1mbeta_nonneg : 0 ≤ 1 - beta := by linarith

  -- Step 1: D^β ≤ (δ^(-η))^β = δ^(-ηβ)
  have h_D_rpow_le : ENNReal.rpow D beta ≤ Kakeya.realRpowENN δ (-eta * beta) := by
    have h1a : ENNReal.rpow D beta ≤ ENNReal.rpow (Kakeya.realRpowENN δ (-eta)) beta :=
      ENNReal.rpow_le_rpow hD_small hβ
    have h1b : ENNReal.rpow (Kakeya.realRpowENN δ (-eta)) beta =
        Kakeya.realRpowENN δ (-eta * beta) :=
      realRpowENN_rpow hδ_pos hβ
    rw [h1b] at h1a
    exact h1a

  -- Step 2: C * D^β ≤ δ^(-(ε-ε'))
  have h_gap_pos : 0 < epsilon - epsilon' - eta * beta := by linarith
  have h_C_D_rpow_le : C * ENNReal.rpow D beta ≤
      Kakeya.realRpowENN δ (-(epsilon - epsilon')) := by
    calc C * ENNReal.rpow D beta
      ≤ C * Kakeya.realRpowENN δ (-eta * beta) := by gcongr
    _ ≤ Kakeya.realRpowENN δ (-(epsilon - epsilon' - eta * beta)) *
          Kakeya.realRpowENN δ (-eta * beta) := by gcongr
    _ = Kakeya.realRpowENN δ ((-(epsilon - epsilon' - eta * beta)) + (-eta * beta)) := by
      rw [← realRpowENN_add' hδ_pos]
    _ = Kakeya.realRpowENN δ (-(epsilon - epsilon')) := by
      have h : (-(epsilon - epsilon' - eta * beta)) + (-eta * beta) = -(epsilon - epsilon') := by ring
      rw [h]

  -- Step 3: D = D^β * D^(1-β) (handle D = 0 separately)
  by_cases hD_zero : D = 0
  · -- D = 0: LHS is 0, trivial
    rw [hD_zero]
    <;> simp
  · have hD_pos : 0 < D := zero_lt_iff.mpr hD_zero
    have h3 : D = ENNReal.rpow D beta * ENNReal.rpow D (1 - beta) := by
      have h3a : ENNReal.rpow D (beta + (1 - beta)) =
          ENNReal.rpow D beta * ENNReal.rpow D (1 - beta) :=
        ENNReal.rpow_add beta (1 - beta) hD_zero hD_ne_top
      have h3b : beta + (1 - beta) = 1 := by linarith
      rw [h3b] at h3a
      have h3c : ENNReal.rpow D 1 = D := by simp
      rw [h3c] at h3a
      exact h3a
    have h4 : C * D = C * (ENNReal.rpow D beta * ENNReal.rpow D (1 - beta)) :=
      congr_arg (fun x => C * x) h3
    have h_mul_exp : Kakeya.realRpowENN δ (-(epsilon - epsilon')) * Kakeya.realRpowENN δ (-epsilon') =
        Kakeya.realRpowENN δ ((-(epsilon - epsilon')) + (-epsilon')) := by
      exact (realRpowENN_add' hδ_pos).symm

    -- Main calculation
    calc C * D * Kakeya.realRpowENN δ (-epsilon')
      = (C * D) * Kakeya.realRpowENN δ (-epsilon') := by ring
    _ = (C * (ENNReal.rpow D beta * ENNReal.rpow D (1 - beta))) * Kakeya.realRpowENN δ (-epsilon') := by
        rw [h4]
    _ = (C * ENNReal.rpow D beta) *
          (ENNReal.rpow D (1 - beta) * Kakeya.realRpowENN δ (-epsilon')) := by ring
    _ ≤ Kakeya.realRpowENN δ (-(epsilon - epsilon')) *
          (ENNReal.rpow D (1 - beta) * Kakeya.realRpowENN δ (-epsilon')) := by gcongr
    _ = (Kakeya.realRpowENN δ (-(epsilon - epsilon')) * Kakeya.realRpowENN δ (-epsilon')) *
          ENNReal.rpow D (1 - beta) := by ring
    _ = Kakeya.realRpowENN δ ((-(epsilon - epsilon')) + (-epsilon')) *
          ENNReal.rpow D (1 - beta) := by rw [h_mul_exp]
    _ = Kakeya.realRpowENN δ (-epsilon) * ENNReal.rpow D (1 - beta) := by
      have h : (-(epsilon - epsilon')) + (-epsilon') = -epsilon := by ring
      rw [h]

end Kakeya.Streamlined
