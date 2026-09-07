import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Polylog absorption

For any `C > 0`, `gap > 0`, and `k : ℕ`, there exists `δ₀ > 0` such that
for all `0 < δ ≤ δ₀`:
`C * (log(1/δ))^k ≤ δ^(-gap)`.

## Proof sketch

Elementary proof (no asymptotics API needed):
1. For `x > 0`, `exp(gap * x) ≥ (gap * x / (k+1))^(k+1)`
   since `exp(y) ≥ 1 + y ≥ y` and `exp((k+1)*y) = (exp y)^(k+1)`.
2. Choose `x₀ = C / (gap/(k+1))^(k+1) + 1`.
3. For `x ≥ x₀`, `(gap/(k+1))^(k+1) * x^(k+1) ≥ C * x^k`.
4. Set `δ₀ = exp(-x₀)`; then `δ ≤ δ₀` implies `log(1/δ) ≥ x₀`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

attribute [local instance] Classical.propDecidable

/--
Polylog bound: for any `s_loss > 0` and `n : ℕ`, there exists `X > 0` with `1 ≤ X`
such that for all `x ≥ X`, `(Real.log x)^n ≤ Real.rpow x s_loss`.
-/
lemma polylog_absorption_bound (s_loss : ℝ) (n : ℕ) (hs_loss_pos : 0 < s_loss) :
    ∃ (X : ℝ), 0 < X ∧ 1 ≤ X ∧ ∀ (x : ℝ), x ≥ X →
      (Real.log x)^n ≤ Real.rpow x s_loss := by
  have h_littleO : (fun x : ℝ => Real.rpow (Real.log x) (n : ℝ)) =o[Filter.atTop]
      (fun x : ℝ => Real.rpow x s_loss) :=
    isLittleO_log_rpow_rpow_atTop (r := (n : ℝ)) (s := s_loss) hs_loss_pos
  have h1 : ∀ᶠ (x : ℝ) in Filter.atTop,
      ‖Real.rpow (Real.log x) (n : ℝ)‖ ≤ ‖Real.rpow x s_loss‖ :=
    h_littleO.eventuallyLE
  rcases Filter.mem_atTop_sets.mp h1 with ⟨X0, hX0⟩
  let X : ℝ := max X0 1
  have hX_pos : 0 < X := by positivity
  have hX_ge_one : 1 ≤ X := le_max_right _ _
  refine ⟨X, hX_pos, hX_ge_one, ?_⟩
  intro x hx
  have h2 : x ≥ X0 := le_trans (le_max_left _ _) hx
  have h3 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have h4 : ‖Real.rpow (Real.log x) (n : ℝ)‖ ≤ ‖Real.rpow x s_loss‖ := hX0 x h2
  have h5 : 0 ≤ Real.log x := Real.log_nonneg h3
  have h5a : 0 ≤ Real.rpow (Real.log x) (n : ℝ) := Real.rpow_nonneg h5 _
  have h5b : 0 ≤ Real.rpow x s_loss := Real.rpow_nonneg (by linarith) _
  have h6 : ‖Real.rpow (Real.log x) (n : ℝ)‖ = Real.rpow (Real.log x) (n : ℝ) := by
    have h_norm : ‖(Real.rpow (Real.log x) (n : ℝ))‖ = |Real.rpow (Real.log x) (n : ℝ)| :=
      Real.norm_eq_abs _
    rw [h_norm, abs_of_nonneg h5a]
  have h7 : ‖Real.rpow x s_loss‖ = Real.rpow x s_loss := by
    have h_norm : ‖(Real.rpow x s_loss)‖ = |Real.rpow x s_loss| :=
      Real.norm_eq_abs _
    rw [h_norm, abs_of_nonneg h5b]
  rw [h6, h7] at h4
  have h8 : Real.rpow (Real.log x) (n : ℝ) = (Real.log x)^n := by
    simp
  rw [h8] at h4
  exact h4

/--
Phase 1 slack condition:
`(wz2PaperPureRefinementFraction delta logExponent)⁻¹ * δ^midLoss ≤ δ^inputLoss`

Given `0 < inputLoss < midLoss`, `0 < delta < 1`, and `delta` small enough that
`1/delta` exceeds the polylog threshold `X`.
-/
lemma phase1_hslack
    (delta midLoss inputLoss : ℝ)
    (logExponent : ℕ)
    (hdelta_pos : 0 < delta)
    (hdelta_lt_one : delta < 1)
    (hinput_pos : 0 < inputLoss)
    (hinput_lt_mid : inputLoss < midLoss)
    (X_polylog : ℝ)
    (hX_polylog_pos : 0 < X_polylog)
    (hX_polylog_bound : ∀ (x : ℝ), x ≥ X_polylog →
      (Real.log x)^logExponent ≤ Real.rpow x (midLoss - inputLoss))
    (h_inv_delta_ge_X : 1 / delta ≥ X_polylog) :
    (wz2PaperPureRefinementFraction delta logExponent)⁻¹ *
      Kakeya.realRpowENN delta midLoss ≤
      Kakeya.realRpowENN delta inputLoss := by
  set s_loss : ℝ := midLoss - inputLoss with hs_loss_def
  have hs_loss_pos : 0 < s_loss := by linarith
  have hlog_pos : 0 < Real.log (1 / delta) := by
    have h1 : 1 < 1 / delta := by
      apply one_lt_one_div <;> linarith
    exact Real.log_pos h1
  have hlog_nonneg : 0 ≤ Real.log (1 / delta) := by linarith
  have h_bound_real : (Real.log (1 / delta))^logExponent ≤ Real.rpow (1 / delta) s_loss :=
    hX_polylog_bound (1 / delta) h_inv_delta_ge_X
  have h_rpow_inv : Real.rpow (1 / delta) s_loss = Real.rpow delta (-s_loss) := by
    have h_pos1 : 0 < delta := hdelta_pos
    have h1 : 0 < 1 / delta := by positivity
    have h_log_div : Real.log (1 / delta) = -Real.log delta := by
      simp [Real.log_div, h_pos1.ne'] <;> ring
    have h2 : Real.rpow (1 / delta) s_loss = Real.exp (s_loss * Real.log (1 / delta)) := by
      have h_def : Real.rpow (1 / delta) s_loss = Real.exp (Real.log (1 / delta) * s_loss) :=
        Real.rpow_def_of_pos h1 s_loss
      have h_comm : Real.log (1 / delta) * s_loss = s_loss * Real.log (1 / delta) := by ring
      rw [h_def, h_comm]
    have h6 : Real.rpow delta s_loss = Real.exp (s_loss * Real.log delta) := by
      have h_def : Real.rpow delta s_loss = Real.exp (Real.log delta * s_loss) :=
        Real.rpow_def_of_pos h_pos1 s_loss
      have h_comm : Real.log delta * s_loss = s_loss * Real.log delta := by ring
      rw [h_def, h_comm]
    have h5 : Real.rpow delta (-s_loss) = (Real.rpow delta s_loss)⁻¹ :=
      Real.rpow_neg h_pos1.le s_loss
    rw [h2, h_log_div]
    have h4 : Real.exp (s_loss * (-Real.log delta)) = Real.exp (-(s_loss * Real.log delta)) := by ring_nf
    rw [h4, Real.exp_neg]
    have h7 : (Real.exp (s_loss * Real.log delta))⁻¹ = (Real.rpow delta s_loss)⁻¹ := by
      rw [← h6]
    rw [h7]
    exact h5.symm
  have h_mid_nonneg : 0 ≤ Real.rpow delta midLoss := Real.rpow_nonneg hdelta_pos.le _
  have h_mul_bound : (Real.log (1 / delta))^logExponent * Real.rpow delta midLoss ≤ Real.rpow delta inputLoss := by
    calc (Real.log (1 / delta))^logExponent * Real.rpow delta midLoss
        ≤ Real.rpow (1 / delta) s_loss * Real.rpow delta midLoss := by
          exact mul_le_mul_of_nonneg_right h_bound_real h_mid_nonneg
      _ = Real.rpow delta (-s_loss) * Real.rpow delta midLoss := by rw [h_rpow_inv]
      _ = Real.rpow delta (-s_loss + midLoss) := by
        have h_add : Real.rpow delta (-s_loss + midLoss) =
            Real.rpow delta (-s_loss) * Real.rpow delta midLoss :=
          Real.rpow_add hdelta_pos (-s_loss) midLoss
        exact h_add.symm
      _ = Real.rpow delta inputLoss := by
        have h4 : -s_loss + midLoss = inputLoss := by
          dsimp only [s_loss] <;> linarith
        rw [h4]
  let a : ℝ := Real.log (1 / delta)
  have ha_pos : 0 < a := hlog_pos
  have ha_nonneg : 0 ≤ a := by linarith
  have h_frac_inv : (wz2PaperPureRefinementFraction delta logExponent)⁻¹ =
      ENNReal.ofReal (a^logExponent) := by
    dsimp only [wz2PaperPureRefinementFraction]
    have h_inv_pow : (ENNReal.ofReal a)⁻¹ ^ logExponent = ((ENNReal.ofReal a) ^ logExponent)⁻¹ :=
      ENNReal.inv_pow.symm
    have h21 : ((ENNReal.ofReal a)⁻¹ ^ logExponent)⁻¹ = (((ENNReal.ofReal a) ^ logExponent)⁻¹)⁻¹ := by
      rw [h_inv_pow]
    rw [h21]
    have h22 : (((ENNReal.ofReal a) ^ logExponent)⁻¹)⁻¹ = (ENNReal.ofReal a) ^ logExponent := by simp
    rw [h22]
    have h8 : (ENNReal.ofReal a) ^ logExponent = ENNReal.ofReal (a^logExponent) := by
      rw [← ENNReal.ofReal_pow ha_nonneg logExponent] <;> rfl
    exact h8
  rw [h_frac_inv]
  have h7 : ENNReal.ofReal ((Real.log (1 / delta))^logExponent) * Kakeya.realRpowENN delta midLoss ≤
      Kakeya.realRpowENN delta inputLoss := by
    simp only [Kakeya.realRpowENN]
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal h_mul_bound
  exact h7

end Kakeya.Assouad.PureWZ2

namespace Kakeya.Assouad

open Real ENNReal Filter
open scoped ENNReal

/-- Exponential beats polynomial: for large enough `x`, `C * x^k ≤ exp(gap * x)`. -/
lemma exp_beats_polynomial
    (C gap : ℝ) (k : ℕ) (hC : 0 < C) (hgap : 0 < gap) :
    ∃ (x₀ : ℝ), 0 < x₀ ∧ ∀ x ≥ x₀, C * x^k ≤ Real.exp (gap * x) := by
  set a : ℝ := gap / (k + 1) with ha_def
  have ha_pos : 0 < a := by positivity
  set x₀ : ℝ := C / a^(k + 1) + 1 with hx₀_def
  have hx₀_pos : 0 < x₀ := by positivity
  have h_main : ∀ x ≥ x₀, C * x^k ≤ Real.exp (gap * x) := by
    intro x hx
    have hx_pos : 0 < x := by linarith
    have h1 : Real.exp (gap * x) ≥ (a * x)^(k + 1) := by
      have h2 : Real.exp (a * x) ≥ 1 + a * x := by
        linarith [Real.add_one_le_exp (a * x)]
      have h4 : gap * x = ((k + 1 : ℕ) : ℝ) * (a * x) := by
        have h5 : ((k + 1 : ℕ) : ℝ) * a = gap := by
          simp [ha_def] <;> field_simp <;> ring
        calc
          gap * x = ((k + 1 : ℕ) : ℝ) * a * x := by rw [h5]
          _ = ((k + 1 : ℕ) : ℝ) * (a * x) := by ring
      have h3 : Real.exp (gap * x) = (Real.exp (a * x))^(k + 1) := by
        rw [h4]
        exact Real.exp_nat_mul (a * x) (k + 1)
      rw [h3]
      have h5 : (Real.exp (a * x))^(k + 1) ≥ (1 + a * x)^(k + 1) := by
        gcongr <;> linarith
      have h6 : (1 + a * x)^(k + 1) ≥ (a * x)^(k + 1) := by
        have h7 : 0 ≤ a * x := by positivity
        have h8 : 1 + a * x ≥ a * x := by linarith
        gcongr
      linarith
    have h9 : (a * x)^(k + 1) = a^(k + 1) * x^(k + 1) := by ring
    rw [h9] at h1
    have h10 : a^(k + 1) * x^(k + 1) ≥ C * x^k := by
      have h11 : x^(k + 1) = x * x^k := by
        simp [pow_succ] <;> ring
      rw [h11]
      have h12 : a^(k + 1) * x ≥ C := by
        have h13 : x ≥ C / a^(k + 1) := by linarith [hx₀_def]
        have h14 : 0 < a^(k + 1) := by positivity
        calc
          a^(k + 1) * x ≥ a^(k + 1) * (C / a^(k + 1)) := by gcongr
          _ = C := by field_simp [h14.ne'] <;> ring
      have h15 : 0 ≤ x^k := by positivity
      nlinarith
    linarith
  exact ⟨x₀, hx₀_pos, h_main⟩

/-- Polylog absorption: for small enough `δ`, `C * (log(1/δ))^k ≤ δ^(-gap)`. -/
lemma polylog_absorption
    (C gap : ℝ) (k : ℕ) (hC : 0 < C) (hgap : 0 < gap) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ →
      C * (Real.log (1 / δ))^k ≤ δ^(-gap) := by
  rcases exp_beats_polynomial C gap k hC hgap with ⟨x₀, hx₀_pos, h_main⟩
  let δ₀ : ℝ := Real.exp (-x₀)
  have hδ₀_pos : 0 < δ₀ := by positivity
  have h_log_ge : ∀ {δ : ℝ}, 0 < δ → δ ≤ δ₀ → Real.log (1 / δ) ≥ x₀ := by
    intro δ hδ_pos hδ_le
    have h1 : 0 < δ₀ := hδ₀_pos
    have h2 : 0 < δ := hδ_pos
    have h3 : 1 / δ ≥ 1 / δ₀ := by gcongr
    have h4 : Real.log (1 / δ) ≥ Real.log (1 / δ₀) :=
      Real.log_le_log (by positivity) h3
    have h5 : Real.log (1 / δ₀) = x₀ := by
      dsimp only [δ₀]
      have h6 : 1 / Real.exp (-x₀) = Real.exp x₀ := by
        rw [Real.exp_neg]
        field_simp
      rw [h6]
      exact Real.log_exp x₀
    rw [h5] at h4
    exact h4
  refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_le => ?_⟩
  set x := Real.log (1 / δ) with hx_def
  have h4 : x ≥ x₀ := h_log_ge hδ_pos hδ_le
  have h5 : C * x^k ≤ Real.exp (gap * x) := h_main x h4
  have h_pos : 0 < 1 / δ := by positivity
  have h6 : Real.exp (gap * x) = (1 / δ)^gap := by
    have h7 : x = Real.log (1 / δ) := by rfl
    rw [h7]
    have h8 : Real.exp (gap * Real.log (1 / δ)) = (1 / δ)^gap := by
      have h9 : Real.exp (gap * Real.log (1 / δ)) = Real.exp (Real.log ((1 / δ)^gap)) := by
        rw [Real.log_rpow (by positivity)] <;> ring
      rw [h9]
      rw [Real.exp_log (by positivity)]
    exact h8
  have h9 : (1 / δ)^gap = δ^(-gap) := by
    have hδ_pos' : 0 < δ := hδ_pos
    have h_pos1 : 0 < 1 / δ := by positivity
    have h1 : (1 / δ)^gap = Real.exp (gap * Real.log (1 / δ)) := by
      rw [Real.rpow_def_of_pos h_pos1] <;> ring
    have h2 : δ^(-gap) = Real.exp ((-gap) * Real.log δ) := by
      rw [Real.rpow_def_of_pos hδ_pos'] <;> ring
    rw [h1, h2]
    have h3 : Real.log (1 / δ) = -Real.log δ := by
      have h4 : (1 / δ) = δ⁻¹ := by field_simp [hδ_pos'.ne']
      rw [h4, Real.log_inv]
    rw [h3] <;> ring
  have h12 : C * x^k ≤ δ^(-gap) := by
    calc C * x^k
      ≤ Real.exp (gap * x) := h5
    _ = (1 / δ)^gap := h6
    _ = δ^(-gap) := h9
  exact h12

end Kakeya.Assouad

end
