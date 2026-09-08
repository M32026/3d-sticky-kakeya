import MyLeanRepo.Kakeya.Streamlined.Estimates
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.AlgebraHelpers

/-!
# FrostmanEstimate monotonicity and exponent absorption helpers

## Main results

- `realRpowENN_anti`: for `0 < δ ≤ 1`, `x ≤ y` implies `δ^x ≥ δ^y` in ENNReal.
- `pow_absorb`: for finite `K` and `b > a ≥ 0`, `K * δ^(-a) ≤ δ^(-b)` for δ small.
-/

noncomputable section

open MeasureTheory Kakeya.Streamlined Kakeya.Streamlined.GeneralizedFrostman

namespace Kakeya.Streamlined.GeneralizedFrostman

/-- For `0 < δ ≤ 1`, `realRpowENN δ` is antitone in the exponent. -/
lemma realRpowENN_anti {δ x y : ℝ} (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (h : x ≤ y) : Kakeya.realRpowENN δ x ≥ Kakeya.realRpowENN δ y := by
  have h1 : Real.rpow δ y ≤ Real.rpow δ x :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h
  simp only [Kakeya.realRpowENN]
  exact ENNReal.ofReal_le_ofReal h1

/-- Absorb a constant times a negative power into a more negative power.

For finite `K` and `b > a ≥ 0`, there exists `delta₀ > 0` such that
`K * δ^(-a) ≤ δ^(-b)` for all `0 < δ ≤ delta₀`.
-/
lemma pow_absorb {K : ENNReal} (hK_ne_top : K ≠ ⊤)
    {a b : ℝ} (ha_nonneg : 0 ≤ a) (hba : a < b) :
    ∃ (delta₀ : ℝ), 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ delta₀ →
        K * Kakeya.realRpowENN δ (-a) ≤ Kakeya.realRpowENN δ (-b) := by
  have h_diff_pos : 0 < b - a := by linarith
  rcases absorb_const hK_ne_top h_diff_pos with
    ⟨delta₀, hδ₀_pos, hδ₀_le_one, h_absorb⟩
  refine ⟨delta₀, hδ₀_pos, hδ₀_le_one, ?_⟩
  intro δ hδ hδ₀
  have h1 : K ≤ Kakeya.realRpowENN δ (-(b - a)) := h_absorb δ hδ hδ₀
  have h2 : -(b - a) = -b + a := by ring
  rw [h2] at h1
  have h3 : Kakeya.realRpowENN δ (-b + a) =
      Kakeya.realRpowENN δ (-b) * Kakeya.realRpowENN δ a :=
    realRpowENN_add hδ
  rw [h3] at h1
  have h4 : K * Kakeya.realRpowENN δ (-a) ≤
      (Kakeya.realRpowENN δ (-b) * Kakeya.realRpowENN δ a) * Kakeya.realRpowENN δ (-a) := by
    gcongr
  have h5 : Kakeya.realRpowENN δ a * Kakeya.realRpowENN δ (-a) = 1 := by
    have h6 : Kakeya.realRpowENN δ a * Kakeya.realRpowENN δ (-a) =
        Kakeya.realRpowENN δ (a + (-a)) := by
      rw [← realRpowENN_add hδ] <;> ring
    rw [h6]
    have h7 : a + (-a) = 0 := by ring
    rw [h7]
    simp [Kakeya.realRpowENN]
  have h8 : (Kakeya.realRpowENN δ (-b) * Kakeya.realRpowENN δ a) * Kakeya.realRpowENN δ (-a) =
      Kakeya.realRpowENN δ (-b) := by
    rw [mul_assoc, h5, mul_one]
  rw [h8] at h4
  exact h4

/-- Monotonicity of the Frostman multiplicity bound in the exponent.

Given `0 ≤ β ≤ α ≤ 1`, `ε > 0`, and `δ^5 * #F ≤ 1`, the `K_F(β)` bound
with slack `ε + (α-β)/2` is bounded by the `K_F(α)` bound with slack `ε`.
-/
lemma frostman_bound_monotone {δ : ℝ} (hδ_pos : 0 < δ)
    {F : TubeFamily δ} {β α ε : ℝ}
    (hβ : 0 ≤ β) (hβα : β ≤ α) (hα : α ≤ 1) (hε : 0 < ε)
    (h_card : Kakeya.realRpowENN δ 5 * F.enncard ≤ 1) :
    Kakeya.realRpowENN δ (-(ε + (α - β) / 2) - 2 * β) *
      ENNReal.rpow (Kakeya.realRpowENN δ 2 * F.enncard) (1 - β / 2) ≤
    Kakeya.realRpowENN δ (-ε - 2 * α) *
      ENNReal.rpow (Kakeya.realRpowENN δ 2 * F.enncard) (1 - α / 2) := by
  set d : ℝ := α - β with hd_def
  have hd_nonneg : 0 ≤ d := by linarith
  have hd2_nonneg : 0 ≤ d / 2 := by linarith
  set X : ENNReal := Kakeya.realRpowENN δ 2 * F.enncard with hX_def
  by_cases hF_empty : F.enncard = 0
  · have hX_zero : X = 0 := by
      rw [hX_def, hF_empty] <;> ring
    have hβ_pos : 0 < 1 - β / 2 := by linarith
    have hα_pos : 0 < 1 - α / 2 := by linarith
    simp [hX_zero, ENNReal.zero_rpow_of_pos hβ_pos,
      ENNReal.zero_rpow_of_pos hα_pos]
  · have hX_ne_zero : X ≠ 0 := by
      rw [hX_def]
      have h1 : 0 < Kakeya.realRpowENN δ 2 := by
        simp [Kakeya.realRpowENN]
        positivity
      exact mul_ne_zero h1.ne' hF_empty
    have hX_ne_top : X ≠ ⊤ := by
      rw [hX_def]
      exact ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN])
        (by simp [TubeFamily.enncard])
    have h_delta3_X : Kakeya.realRpowENN δ 3 * X =
        Kakeya.realRpowENN δ 5 * F.enncard := by
      rw [hX_def]
      have h_assoc :
          Kakeya.realRpowENN δ 3 *
              (Kakeya.realRpowENN δ 2 * F.enncard) =
            (Kakeya.realRpowENN δ 3 * Kakeya.realRpowENN δ 2) *
              F.enncard := by ring
      rw [h_assoc]
      have h_add : Kakeya.realRpowENN δ 3 *
          Kakeya.realRpowENN δ 2 =
          Kakeya.realRpowENN δ (3 + 2) := by
        rw [← realRpowENN_add hδ_pos]
      rw [h_add] <;> norm_num
    have h_exp1 :
        -(ε + d / 2) - 2 * β = -ε - 2 * α + 3 * d / 2 := by
      simp [hd_def]
      ring
    have h_exp2 : 1 - β / 2 = 1 - α / 2 + d / 2 := by
      simp [hd_def]
      ring
    have h_rpow_X : ENNReal.rpow X (1 - β / 2) =
        ENNReal.rpow X (1 - α / 2) * ENNReal.rpow X (d / 2) := by
      rw [h_exp2]
      exact ENNReal.rpow_add (1 - α / 2) (d / 2) hX_ne_zero hX_ne_top
    have h_mul_rpow :
        ENNReal.rpow (Kakeya.realRpowENN δ 3 * X) (d / 2) =
          Kakeya.realRpowENN δ (3 * d / 2) *
            ENNReal.rpow X (d / 2) := by
      have h_mul : (Kakeya.realRpowENN δ 3 * X) ^ (d / 2) =
          (Kakeya.realRpowENN δ 3) ^ (d / 2) * X ^ (d / 2) :=
        ENNReal.mul_rpow_of_nonneg _ _ hd2_nonneg
      have h4 : (Kakeya.realRpowENN δ 3) ^ (d / 2) =
          Kakeya.realRpowENN δ (3 * d / 2) := by
        rw [realRpowENN_rpow hδ_pos]
        congr 1 <;> ring
      calc
        ENNReal.rpow (Kakeya.realRpowENN δ 3 * X) (d / 2)
            = (Kakeya.realRpowENN δ 3 * X) ^ (d / 2) := by rfl
        _ = (Kakeya.realRpowENN δ 3) ^ (d / 2) * X ^ (d / 2) := h_mul
        _ = Kakeya.realRpowENN δ (3 * d / 2) * X ^ (d / 2) := by
          rw [h4]
        _ = Kakeya.realRpowENN δ (3 * d / 2) *
            ENNReal.rpow X (d / 2) := by rfl
    have h_factor :
        Kakeya.realRpowENN δ (-(ε + d / 2) - 2 * β) *
            ENNReal.rpow X (1 - β / 2) =
          (Kakeya.realRpowENN δ (-ε - 2 * α) *
              ENNReal.rpow X (1 - α / 2)) *
            ENNReal.rpow (Kakeya.realRpowENN δ 3 * X) (d / 2) := by
      have h1 : Kakeya.realRpowENN δ (-(ε + d / 2) - 2 * β) =
          Kakeya.realRpowENN δ (-ε - 2 * α) *
            Kakeya.realRpowENN δ (3 * d / 2) := by
        rw [h_exp1, ← realRpowENN_add hδ_pos]
      rw [h1, h_rpow_X, h_mul_rpow] <;> ring
    have h_le :
        ENNReal.rpow (Kakeya.realRpowENN δ 5 * F.enncard) (d / 2) ≤ 1 :=
      ENNReal.rpow_le_one h_card hd2_nonneg
    calc
      Kakeya.realRpowENN δ (-(ε + d / 2) - 2 * β) *
          ENNReal.rpow X (1 - β / 2)
          = (Kakeya.realRpowENN δ (-ε - 2 * α) *
              ENNReal.rpow X (1 - α / 2)) *
            ENNReal.rpow (Kakeya.realRpowENN δ 3 * X) (d / 2) :=
              h_factor
      _ = (Kakeya.realRpowENN δ (-ε - 2 * α) *
              ENNReal.rpow X (1 - α / 2)) *
            ENNReal.rpow
              (Kakeya.realRpowENN δ 5 * F.enncard) (d / 2) := by
            rw [h_delta3_X]
      _ ≤ (Kakeya.realRpowENN δ (-ε - 2 * α) *
              ENNReal.rpow X (1 - α / 2)) * 1 := by
            gcongr
      _ = Kakeya.realRpowENN δ (-ε - 2 * α) *
            ENNReal.rpow X (1 - α / 2) := by ring

end Kakeya.Streamlined.GeneralizedFrostman
