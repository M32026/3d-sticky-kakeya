import MyLeanRepo.Kakeya.Cinematic.Statements
import MyLeanRepo.Kakeya.Cinematic.WZ2Input
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integral to eLpNorm conversion lemma
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Cinematic

lemma integral_to_elpnorm {m : ℝ × ℝ → ℝ} (hm_nonneg : ∀ x, 0 ≤ m x)
    (hm_meas : Measurable m) (E : Set (ℝ × ℝ)) (hE_meas : MeasurableSet E)
    (hE : ∀ x, m x ≠ 0 → x ∈ E) (B : ℝ) (hB : 0 ≤ B)
    (h_integrable : Integrable (fun x => Real.rpow (m x) (3 / 2 : ℝ)) MeasureTheory.volume)
    (h_int : ∫ x in E, Real.rpow (m x) (3 / 2 : ℝ) ≤ B) :
    eLpNorm m (3 / 2 : ENNReal) MeasureTheory.volume ≤
      ENNReal.ofReal (Real.rpow B (2 / 3 : ℝ)) := by
  let g : ℝ × ℝ → ℝ := fun x => m x * Real.sqrt (m x)
  have hg_meas : Measurable g :=
    hm_meas.mul (Measurable.sqrt hm_meas)
  have h_rpow_eq : ∀ (y : ℝ), 0 ≤ y → y * Real.sqrt y = Real.rpow y (3 / 2 : ℝ) := by
    intro y hy
    have h1 : 0 ≤ y * Real.sqrt y := by positivity
    have h2 : 0 ≤ Real.rpow y (3 / 2 : ℝ) := Real.rpow_nonneg hy _
    have h3 : (y * Real.sqrt y) ^ 2 = y ^ 3 := by
      calc (y * Real.sqrt y) ^ 2
          = y ^ 2 * (Real.sqrt y) ^ 2 := by ring
        _ = y ^ 2 * y := by rw [Real.sq_sqrt hy]
        _ = y ^ 3 := by ring
    have h4 : (Real.rpow y (3 / 2 : ℝ)) ^ 2 = y ^ 3 := by
      have h5 : (Real.rpow y (3 / 2 : ℝ)) ^ 2 = Real.rpow y ((3 / 2 : ℝ) * 2) := by
        have h6 := Real.rpow_mul hy (3 / 2 : ℝ) 2
        simpa using h6.symm
      rw [h5]
      have h7 : (3 / 2 : ℝ) * 2 = 3 := by norm_num
      rw [h7] <;> simp
    nlinarith [sq_nonneg (y * Real.sqrt y - Real.rpow y (3 / 2 : ℝ))]
  have hg_nonneg : ∀ x, 0 ≤ g x := by
    intro x; have h := hm_nonneg x; positivity
  have h1 : ∀ x, g x = ‖m x‖ ^ (3 / 2 : ℝ) := by
    intro x
    have hnonneg : 0 ≤ m x := hm_nonneg x
    have h_eq1 : g x = Real.rpow (m x) (3 / 2 : ℝ) := h_rpow_eq (m x) hnonneg
    have h2 : ‖m x‖ = m x := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    have h3 : ‖m x‖ ^ (3 / 2 : ℝ) = Real.rpow (m x) (3 / 2 : ℝ) := by
      rw [h2] <;> rfl
    rw [h_eq1, h3]
  have h3 : ∫ x in E, g x ≤ B := by
    have h_eq_integral : ∫ x in E, g x = ∫ x in E, Real.rpow (m x) (3 / 2 : ℝ) := by
      congr with x
      exact h_rpow_eq (m x) (hm_nonneg x)
    rw [h_eq_integral]
    exact h_int
  have h4 : ∀ x, x ∉ E → g x = 0 := by
    intro x hnx
    have hmx : m x = 0 := by
      by_contra h
      exact hnx (hE x h)
    simp [g, hmx]
  have h6 : ∫ x, g x = ∫ x in E, g x := by
    have h9 : g =ᵐ[MeasureTheory.volume] E.indicator g := by
      filter_upwards with x
      by_cases hxE : x ∈ E
      · simp [hxE]
      · have hgx : g x = 0 := h4 x hxE
        simp [hxE, hgx]
    have h8 : ∫ x, g x = ∫ x, E.indicator g x :=
      MeasureTheory.integral_congr_ae h9
    rw [h8]
    exact integral_indicator₀ hE_meas.nullMeasurableSet
  have h_int2 : ∫ x, g x ≤ B := by
    calc ∫ x, g x = ∫ x in E, g x := h6
      _ ≤ B := h3
  have hg_nonneg_ae : 0 ≤ᵐ[MeasureTheory.volume] g := by
    filter_upwards with x; exact hg_nonneg x
  have h_integrable' : Integrable g MeasureTheory.volume := by
    have h_eq : g = fun x => Real.rpow (m x) (3 / 2 : ℝ) := by
      funext x
      exact h_rpow_eq (m x) (hm_nonneg x)
    rw [h_eq]
    exact h_integrable
  by_cases hB0 : B = 0
  · -- B = 0 case
    have h_int0 : ∫ x, g x = 0 := by
      have h_le : ∫ x, g x ≤ 0 := by rw [hB0] at h_int2; exact h_int2
      have h_ge : 0 ≤ ∫ x, g x := integral_nonneg hg_nonneg
      linarith
    have h_iff : (∫ x, g x = 0) ↔ (g =ᵐ[MeasureTheory.volume] 0) :=
      integral_eq_zero_iff_of_nonneg hg_nonneg h_integrable'
    have h_eq0 : g =ᵐ[MeasureTheory.volume] 0 := h_iff.mp h_int0
    have h_m0 : m =ᵐ[MeasureTheory.volume] 0 := by
      filter_upwards [h_eq0] with x hx
      have h9 : g x = 0 := hx
      have h10 : m x = 0 := by
        have h11 : m x * Real.sqrt (m x) = 0 := by simpa [g] using h9
        have h12 : m x = 0 ∨ Real.sqrt (m x) = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h11
        cases h12 with
        | inl h13 => exact h13
        | inr h13 =>
          have h14 : m x ≤ 0 := by simpa [Real.sqrt_eq_zero'] using h13
          have h15 : 0 ≤ m x := hm_nonneg x
          linarith
      simpa using h10
    have h_elp : eLpNorm m (3 / 2 : ENNReal) MeasureTheory.volume = 0 := by
      have hne1 : (3 / 2 : ENNReal) ≠ 0 := by simp
      have hne2 : (3 / 2 : ENNReal) ≠ ⊤ := by
        intro h
        have h' : (3 / 2 : ENNReal).toReal = 0 := by rw [h] <;> simp
        have h'' : (3 / 2 : ENNReal).toReal = (3 / 2 : ℝ) := by simp
        rw [h''] at h'
        norm_num at h'
      have h_toReal : (3 / 2 : ENNReal).toReal = (3 / 2 : ℝ) := by simp
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne1 hne2, h_toReal]
      have h_eq_ae : (fun x : ℝ × ℝ => ‖m x‖ₑ ^ (3 / 2 : ℝ)) =ᵐ[MeasureTheory.volume] (fun _ => 0) := by
        filter_upwards [h_m0] with x hx
        have h12 : m x = 0 := hx
        simp [h12]
      have h11 : ∫⁻ x, ‖m x‖ₑ ^ (3 / 2 : ℝ) = 0 := by
        rw [lintegral_congr_ae h_eq_ae]
        simp
      rw [h11]
      simp
    rw [h_elp]
    <;> simp [hB0]
  · -- B > 0 case
    have hB_pos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    have h9 : ENNReal.ofReal (∫ x, g x) = ∫⁻ x, ENNReal.ofReal (g x) := by
      rw [ofReal_integral_eq_lintegral_ofReal h_integrable' hg_nonneg_ae]
    have h10 : ∫⁻ x, ‖m x‖ₑ ^ (3 / 2 : ℝ) = ∫⁻ x, ENNReal.ofReal (g x) := by
      congr with x
      have h11 : ‖m x‖ₑ ^ (3 / 2 : ℝ) = ENNReal.ofReal (g x) := by
        have h12 : g x = ‖m x‖ ^ (3 / 2 : ℝ) := h1 x
        have hnonneg : 0 ≤ m x := hm_nonneg x
        have h13 : ‖m x‖ₑ = ENNReal.ofReal (m x) := by
          rw [Real.enorm_eq_ofReal hnonneg]
        rw [h13, h12]
        have h14 : ‖m x‖ = m x := by
          rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        rw [h14]
        rw [ENNReal.ofReal_rpow_of_nonneg hnonneg (by norm_num)]
      exact h11
    have hne2 : (3 / 2 : ENNReal) ≠ ⊤ := by
      intro h
      have h' : (3 / 2 : ENNReal).toReal = 0 := by rw [h] <;> simp
      have h'' : (3 / 2 : ENNReal).toReal = (3 / 2 : ℝ) := by simp
      rw [h''] at h'
      norm_num at h'
    have h12 : eLpNorm m (3 / 2 : ENNReal) MeasureTheory.volume =
        (∫⁻ x, ‖m x‖ₑ ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) hne2]
      simp
    rw [h12, h10, ← h9]
    have h13 : ENNReal.ofReal (∫ x, g x) ≤ ENNReal.ofReal B :=
      ENNReal.ofReal_le_ofReal h_int2
    have h14 : (ENNReal.ofReal (∫ x, g x)) ^ (2 / 3 : ℝ) ≤
        (ENNReal.ofReal B) ^ (2 / 3 : ℝ) :=
      ENNReal.rpow_le_rpow h13 (by norm_num)
    have h15 : (ENNReal.ofReal B) ^ (2 / 3 : ℝ) = ENNReal.ofReal (Real.rpow B (2 / 3 : ℝ)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hB (by norm_num)]
      congr 1
    rw [h15] at h14
    exact h14

end Kakeya.Cinematic
