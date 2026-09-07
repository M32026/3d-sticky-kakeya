module

/-
# Pbar Product Upper Bound

Rearranges the output of `product_bound_wiring_coord` to give an upper bound
on `Nplane δ Pbar` in terms of `Nreal δ S1 * Nreal δ S2`.

From `(1/2) · δ^{3ρ_sel+qMassV4} · N(Pbar) ≤ N(S1)·N(S2)`,
derive `N(Pbar) ≤ 2 · δ^{-(3ρ_sel+qMassV4)} · N(S1)·N(S2)`.

## Dependencies
- `MyLeanRepo.CoreDefinitions`
- `MyLeanRepo.ProductLikeBasic`
- `MyLeanRepo.ProjectionBasic`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section


noncomputable section

open Set ENNReal Bornology Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- **Product upper bound corollary**: rearranges the output of
`product_bound_wiring_coord` to give an upper bound on `Nplane δ Pbar`
in terms of `Nreal δ S1 * Nreal δ S2`.

From `(1/2) · δ^{3ρ_sel+qMassV4} · N(Pbar) ≤ N(S1)·N(S2)`,
derive `N(Pbar) ≤ 2 · δ^{-(3ρ_sel+qMassV4)} · N(S1)·N(S2)`. -/
lemma product_upper_from_wiring
    {δ rho_sel qMassV4 : ℝ}
    (hδ_pos : 0 < δ)
    (hrho_sel_pos : 0 < rho_sel)
    (hqMassV4_nonneg : 0 ≤ qMassV4)
    {Pbar : Set (EuclideanSpace ℝ (Fin 2))}
    {S1 S2 : Set ℝ}
    (hPbar_ne_top : Nplane δ Pbar ≠ ⊤)
    (hS1_ne_top : Nreal δ S1 ≠ ⊤)
    (hS2_ne_top : Nreal δ S2 ≠ ⊤)
    (h_product_lower :
      (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) * Nplane δ Pbar ≤
        Nreal δ S1 * Nreal δ S2) :
    Nplane δ Pbar ≤
      (2 : ENNReal) * ENNReal.ofReal (δ ^ (-(3 * rho_sel + qMassV4))) *
        Nreal δ S1 * Nreal δ S2 := by
  set a : ℝ := δ ^ (3 * rho_sel + qMassV4) with ha_def
  have ha_pos : 0 < a := by positivity
  set X : ENNReal := Nplane δ Pbar with hX_def
  set Y : ENNReal := Nreal δ S1 * Nreal δ S2 with hY_def
  have hY_ne_top : Y ≠ ⊤ := ENNReal.mul_ne_top hS1_ne_top hS2_ne_top
  set c : ENNReal := (1 / 2 : ENNReal) * ENNReal.ofReal a with hc_def
  have hc_ne_top : c ≠ ⊤ := by
    rw [hc_def]; exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have h_main : c * X ≤ Y := h_product_lower
  have h_lhs_ne_top : c * X ≠ ⊤ := ENNReal.mul_ne_top hc_ne_top hPbar_ne_top
  have h_real : (c * X).toReal ≤ Y.toReal := ENNReal.toReal_mono hY_ne_top h_main
  have h_c_real : c.toReal = (1 / 2 : ℝ) * a := by
    rw [hc_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] <;> norm_num
  have h_x_real : (c * X).toReal = c.toReal * X.toReal := by
    rw [ENNReal.toReal_mul]
  rw [h_x_real] at h_real
  rw [h_c_real] at h_real
  have h1 : (1 / 2 : ℝ) * a * X.toReal ≤ Y.toReal := h_real
  have ha_ne_zero : a ≠ 0 := ha_pos.ne'
  have h_factor : ((1 / 2 : ℝ) * a)⁻¹ * ((1 / 2 : ℝ) * a * X.toReal) = X.toReal := by
    have h_pos2 : 0 < (1 / 2 : ℝ) * a := by positivity
    field_simp [ha_ne_zero, h_pos2.ne'] <;> ring
  have h2 : X.toReal ≤ (2 * a⁻¹) * Y.toReal := by
    calc X.toReal
      = ((1 / 2 : ℝ) * a)⁻¹ * ((1 / 2 : ℝ) * a * X.toReal) := h_factor.symm
    _ ≤ ((1 / 2 : ℝ) * a)⁻¹ * Y.toReal := by gcongr
    _ = (2 * a⁻¹) * Y.toReal := by
      have h_eq : ((1 / 2 : ℝ) * a)⁻¹ = 2 * a⁻¹ := by
        field_simp [ha_ne_zero] <;> ring
      rw [h_eq]
  have h3 : a⁻¹ = δ ^ (-(3 * rho_sel + qMassV4)) := by
    rw [ha_def]
    have h4 : (δ ^ (3 * rho_sel + qMassV4))⁻¹ = δ ^ (-(3 * rho_sel + qMassV4)) := by
      rw [← Real.rpow_neg hδ_pos.le] <;> ring
    exact h4
  rw [h3] at h2
  have h4 : X.toReal ≤ (2 * δ ^ (-(3 * rho_sel + qMassV4))) * Y.toReal := h2
  have h5 : 0 ≤ (2 * δ ^ (-(3 * rho_sel + qMassV4))) * Y.toReal := by positivity
  have h6 : X ≤ ENNReal.ofReal ((2 * δ ^ (-(3 * rho_sel + qMassV4))) * Y.toReal) := by
    have h7 : X = ENNReal.ofReal X.toReal := by
      rw [ENNReal.ofReal_toReal hPbar_ne_top]
    rw [h7]
    exact ENNReal.ofReal_le_ofReal h4
  have h_pos1 : 0 ≤ 2 * δ ^ (-(3 * rho_sel + qMassV4)) := by positivity
  have h_pos2 : 0 ≤ Y.toReal := by positivity
  have h8 : ENNReal.ofReal ((2 * δ ^ (-(3 * rho_sel + qMassV4))) * Y.toReal) =
      ENNReal.ofReal (2 * δ ^ (-(3 * rho_sel + qMassV4))) * Y := by
    have h81 : ENNReal.ofReal ((2 * δ ^ (-(3 * rho_sel + qMassV4))) * Y.toReal) =
        ENNReal.ofReal (2 * δ ^ (-(3 * rho_sel + qMassV4))) * ENNReal.ofReal (Y.toReal) := by
      rw [← ENNReal.ofReal_mul h_pos1]
    rw [h81]
    have h82 : ENNReal.ofReal (Y.toReal) = Y := ENNReal.ofReal_toReal hY_ne_top
    rw [h82]
  rw [h8] at h6
  have h_pos3 : (0 : ℝ) ≤ 2 := by norm_num
  have h9 : ENNReal.ofReal (2 * δ ^ (-(3 * rho_sel + qMassV4))) =
      (2 : ENNReal) * ENNReal.ofReal (δ ^ (-(3 * rho_sel + qMassV4))) := by
    have h_eq1 : ENNReal.ofReal (2 * δ ^ (-(3 * rho_sel + qMassV4))) =
        ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (δ ^ (-(3 * rho_sel + qMassV4))) := by
      rw [← ENNReal.ofReal_mul h_pos3]
    rw [h_eq1]
    have h_eq2 : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by simp
    rw [h_eq2]
  rw [h9] at h6
  have h10 : (2 : ENNReal) * ENNReal.ofReal (δ ^ (-(3 * rho_sel + qMassV4))) * Y =
      (2 : ENNReal) * ENNReal.ofReal (δ ^ (-(3 * rho_sel + qMassV4))) * Nreal δ S1 * Nreal δ S2 := by
    rw [hY_def]
    simp only [mul_assoc]
  rw [h10] at h6
  exact h6

end ProductLikeIncidence.ProductReduction
