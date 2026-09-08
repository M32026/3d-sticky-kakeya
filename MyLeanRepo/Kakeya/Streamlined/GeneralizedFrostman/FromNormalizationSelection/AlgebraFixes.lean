import MyLeanRepo.Kakeya.Streamlined.Basic
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.AlgebraHelpers
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# ENNReal algebra fixes for the normalization-selection proof

This module provides robust helper lemmas for ENNReal operations that are
error-prone in the main proof: negative exponent inverse, division
associativity, three-way product positivity, and Fin cardinality conversion.

## Main results

- `realRpowENN_neg`: `δ^(-x) = (δ^x)⁻¹`
- `ennreal_div_mul_assoc`: `(a * b / c) * d = a * b * d / c`
- `ennreal_mul_pos3`: positivity for three-way products
- `ennreal_mul_rpow3`: rpow distributes over three-way multiplication
- `fin_card_le_nat`: convert `Fintype.card (Fin n) ≤ Fintype.card (Fin m)` to `n ≤ m`
-/

noncomputable section

open MeasureTheory Kakeya.Streamlined Kakeya.Streamlined.GeneralizedFrostman

namespace Kakeya.Streamlined.GeneralizedFrostman

/-! ### realRpowENN negative exponent -/

/-- Negative power is the inverse: `realRpowENN δ (-x) = (realRpowENN δ x)⁻¹`. -/
lemma realRpowENN_neg {δ x : ℝ} (hδ_pos : 0 < δ) :
    Kakeya.realRpowENN δ (-x) = (Kakeya.realRpowENN δ x)⁻¹ := by
  have h1 : 0 < Real.rpow δ x := Real.rpow_pos_of_pos hδ_pos x
  simp only [Kakeya.realRpowENN]
  have h2 : Real.rpow δ (-x) = (Real.rpow δ x)⁻¹ :=
    Real.rpow_neg (by linarith) x
  rw [h2, ENNReal.ofReal_inv_of_pos h1]

/-! ### ENNReal division associativity -/

/-- Reassociate division through multiplication:
`(a * b / c) * d = a * b * d / c`. -/
lemma ennreal_div_mul_assoc {a b c d : ENNReal}
    (hc0 : c ≠ 0) (hctop : c ≠ ⊤) :
    (a * b / c) * d = a * b * d / c := by
  simp only [div_eq_mul_inv]
  have h : (a * b * c⁻¹) * d = a * b * d * c⁻¹ := by
    ring
  exact h

/-- Move a multiplier inside division:
`c * (a / b) = c * a / b`. -/
lemma ennreal_mul_div_assoc {a b c : ENNReal}
    (hb0 : b ≠ 0) (hbtop : b ≠ ⊤) :
    c * (a / b) = c * a / b := by
  simp only [div_eq_mul_inv]
  ring

/-! ### Positivity for products -/

/-- Positivity for a three-way ENNReal product. -/
lemma ennreal_mul_pos3 {a b c : ENNReal}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    0 < a * b * c := by
  have h1 : 0 < a * b := ENNReal.mul_pos ha0 hb0
  exact ENNReal.mul_pos h1.ne' hc0

/-- Positivity for a four-way ENNReal product. -/
lemma ennreal_mul_pos4 {a b c d : ENNReal}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0) :
    0 < a * b * c * d := by
  have h1 : 0 < a * b * c := ennreal_mul_pos3 ha0 hb0 hc0
  exact ENNReal.mul_pos h1.ne' hd0

/-! ### rpow over products -/

/-- rpow distributes over a three-way product. -/
lemma ennreal_mul_rpow3 {a b c : ENNReal} {p : ℝ} (hp : 0 ≤ p) :
    (a * b * c) ^ p = a ^ p * b ^ p * c ^ p := by
  have h1 : (a * b * c) ^ p = (a * b) ^ p * c ^ p :=
    ENNReal.mul_rpow_of_nonneg _ _ hp
  rw [h1]
  have h2 : (a * b) ^ p = a ^ p * b ^ p :=
    ENNReal.mul_rpow_of_nonneg _ _ hp
  rw [h2] <;> ring

/-! ### Fin cardinality conversion -/

/-- Convert `Fintype.card (Fin n) ≤ Fintype.card (Fin m)` to `n ≤ m`. -/
lemma fin_card_le_nat {n m : ℕ}
    (h : Fintype.card (Fin n) ≤ Fintype.card (Fin m)) : n ≤ m := by
  simpa [Fintype.card_fin] using h

/-! ### Constant power nonzero/ne_top -/

/-- A positive natural constant power is nonzero. -/
lemma ennreal_pow_pos {n : ℕ} (hn : 0 < n) : (0 : ENNReal) < (n : ENNReal) := by
  exact_mod_cast hn

/-- `(41^3 : ENNReal)` is nonzero. -/
lemma fortyone_cubed_ne_zero : (41 ^ 3 : ENNReal) ≠ 0 := by
  positivity

/-- `(41^3 : ENNReal)` is not top. -/
lemma fortyone_cubed_ne_top : (41 ^ 3 : ENNReal) ≠ ⊤ :=
  ENNReal.pow_ne_top (ENNReal.natCast_ne_top 41)

/-! ### Specific cancellation patterns -/

/-- Cancel `J` from numerator and denominator:
`J / (a * J / c) = c * a⁻¹`, when all terms are nonzero and not top. -/
lemma ennreal_div_cancel_mul {J a c : ENNReal}
    (hJ0 : J ≠ 0) (hJtop : J ≠ ⊤)
    (ha0 : a ≠ 0) (hatop : a ≠ ⊤)
    (hc0 : c ≠ 0) (hctop : c ≠ ⊤) :
    J / (a * J / c) = c * a⁻¹ := by
  have h_aj0 : a * J ≠ 0 := by
    intro h
    have : a = 0 ∨ J = 0 := (mul_eq_zero.mp h)
    tauto
  have h_ajtop : a * J ≠ ⊤ := ENNReal.mul_ne_top hatop hJtop
  have h_main : J / (a * J / c) = J / ((a * J) * c⁻¹) := by
    have h : a * J / c = (a * J) * c⁻¹ := by
      simp [div_eq_mul_inv]
    rw [h]
  rw [h_main]
  have h4 : J / ((a * J) * c⁻¹) = J * ((a * J) * c⁻¹)⁻¹ := by
    simp [div_eq_mul_inv]
  rw [h4]
  have h5 : ((a * J) * c⁻¹)⁻¹ = c * (a * J)⁻¹ := by
    have h51 : c⁻¹ ≠ 0 := by
      exact ENNReal.inv_ne_zero.mpr hctop
    have h52 : c⁻¹ ≠ ⊤ := by
      exact ENNReal.inv_ne_top.mpr hc0
    rw [ENNReal.mul_inv (Or.inl h_aj0) (Or.inl h_ajtop)]
    have h53 : (c⁻¹)⁻¹ = c := by
      exact inv_inv c
    rw [h53] <;> ring
  rw [h5]
  have h6 : (a * J)⁻¹ = a⁻¹ * J⁻¹ :=
    ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop)
  rw [h6]
  have h7 : J * (c * (a⁻¹ * J⁻¹)) = c * a⁻¹ := by
    calc J * (c * (a⁻¹ * J⁻¹))
      = c * a⁻¹ * (J * J⁻¹) := by ring
    _ = c * a⁻¹ * 1 := by
      rw [ENNReal.mul_inv_cancel hJ0 hJtop]
    _ = c * a⁻¹ := by ring
  exact h7

end Kakeya.Streamlined.GeneralizedFrostman
