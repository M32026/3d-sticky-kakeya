import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Hölder volume lower bound and multiplicity monotonicity

Given a non-negative function `m` with total mass `S` and L^{3/2} norm
at most `M`, the volume of its support is at least `(S / M)^3`.

Uses conjugate exponents p = 3/2, q = 3, so `||1_U||_3 = V^{1/3}`.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/--
Hölder inequality: if total mass `S` and L^{3/2} norm ≤ `M`,
then support volume `V ≥ (S/M)^3`.

Uses p = 3/2, q = 3, so ||1_U||_3 = V^{1/3}.
-/
lemma holder_volume_lower_bound
    {α : Type*} [MeasureSpace α] {m : α → ENNReal}
    (hm : Measurable m)
    (S M : ENNReal)
    (hS : (∫⁻ p, m p) = S)
    (hM : eLpNorm m (3 / 2 : ENNReal) volume ≤ M) :
    volume {p | m p ≠ 0} ≥ (S / M) ^ 3 := by
  let U : Set α := {p | m p ≠ 0}
  have hU_meas : MeasurableSet U := by
    have h1 : MeasurableSet ({0} : Set ENNReal) := measurableSet_singleton 0
    exact (hm h1).compl
  let g : α → ENNReal := U.indicator (fun _ => 1)
  have hg : Measurable g := measurable_const.indicator hU_meas
  let p : ℝ := 3 / 2
  let q : ℝ := 3
  have hpq : Real.HolderConjugate p q :=
    { inv_add_inv_eq_inv := by norm_num
      left_pos := by norm_num
      right_pos := by norm_num }
  have h_holder_raw : (∫⁻ x, (m * g) x) ≤
      (∫⁻ x, (m x) ^ p) ^ (1 / p) * (∫⁻ x, (g x) ^ q) ^ (1 / q) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hm.aemeasurable hg.aemeasurable
  have h_p_ne_zero : (3 / 2 : ENNReal) ≠ 0 := by simp
  have h_p_ne_top : (3 / 2 : ENNReal) ≠ ⊤ := by
    have h1 : (1 : ENNReal) ≤ (2 : ENNReal) := by norm_num
    have h2 : (3 : ENNReal) / (2 : ENNReal) ≤ (3 : ENNReal) / (1 : ENNReal) :=
      ENNReal.div_le_div_left h1 (3 : ENNReal)
    have h3 : (3 : ENNReal) / (1 : ENNReal) = (3 : ENNReal) := by simp
    have h4 : (3 / 2 : ENNReal) ≤ (3 : ENNReal) := by
      simpa [div_eq_mul_inv] using h2.trans_eq h3
    have h' : (3 : ENNReal) < ⊤ := ENNReal.ofNat_lt_top
    exact (h4.trans_lt h').ne
  have h_q_ne_zero : (3 : ENNReal) ≠ 0 := by simp
  have h_q_ne_top : (3 : ENNReal) ≠ ⊤ := by
    have h' : (3 : ENNReal) < ⊤ := ENNReal.ofNat_lt_top
    exact h'.ne
  have h_eLp_m : eLpNorm m (3 / 2 : ENNReal) volume =
      (∫⁻ x, (m x) ^ p) ^ (1 / p) := by
    have h : eLpNorm m (3 / 2 : ENNReal) volume =
        (∫⁻ x, ‖m x‖ₑ ^ (3 / 2 : ENNReal).toReal) ^ (1 / (3 / 2 : ENNReal).toReal) :=
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal h_p_ne_zero h_p_ne_top
    rw [h]
    have h3 : ∀ x, ‖m x‖ₑ = m x := by intro x; rfl
    simp [h3, p]
  have h_eLp_g : eLpNorm g 3 volume =
      (∫⁻ x, (g x) ^ q) ^ (1 / q) := by
    have h : eLpNorm g 3 volume =
        (∫⁻ x, ‖g x‖ₑ ^ (3 : ENNReal).toReal) ^ (1 / (3 : ENNReal).toReal) :=
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal h_q_ne_zero h_q_ne_top
    rw [h]
    have h3 : ∀ x, ‖g x‖ₑ = g x := by intro x; rfl
    simp [h3, q]
  have h_holder : (∫⁻ x, (m * g) x) ≤
      eLpNorm m (3 / 2 : ENNReal) volume * eLpNorm g 3 volume := by
    rw [h_eLp_m, h_eLp_g]
    exact h_holder_raw
  have h_mul : (∫⁻ x, (m * g) x) = S := by
    have h1 : ∀ x, (m * g) x = m x := by
      intro x
      by_cases hx : m x ≠ 0
      · simp [g, U, hx]
      · have h2 : m x = 0 := by tauto
        simp [g, U, h2]
    have h3 : (∫⁻ x, (m * g) x) = ∫⁻ x, m x := by
      congr with x; exact h1 x
    rw [h3, hS]
  have h_g_norm : eLpNorm g 3 volume = volume U ^ (1 / (3 : ℝ)) := by
    rw [MeasureTheory.eLpNorm_indicator_const hU_meas h_q_ne_zero h_q_ne_top]
    <;> simp
  rw [h_mul, h_g_norm] at h_holder
  have h_main : S ≤ M * (volume U ^ (1 / (3 : ℝ))) :=
    h_holder.trans (by gcongr)
  by_cases hM0 : M = 0
  · have hS0 : S = 0 := by
      rw [hM0] at h_main
      simp at h_main <;> exact h_main
    rw [hS0, hM0] <;> simp
  · have h_div : S / M ≤ volume U ^ (1 / (3 : ℝ)) :=
      ENNReal.div_le_of_le_mul' h_main
    have h_pow : (S / M) ^ 3 ≤ (volume U ^ (1 / (3 : ℝ))) ^ 3 := by gcongr
    have h_rpow3 : ∀ (x : ENNReal), (x ^ (1 / (3 : ℝ))) ^ 3 = x := by
      intro x
      have h1 : (x ^ (1 / (3 : ℝ))) ^ 3 = (x ^ (1 / (3 : ℝ))) ^ (3 : ℝ) := by
        exact (ENNReal.rpow_natCast (x ^ (1 / (3 : ℝ))) 3).symm
      rw [h1]
      have h2 : (x ^ (1 / (3 : ℝ))) ^ (3 : ℝ) = x ^ ((1 / (3 : ℝ)) * (3 : ℝ)) := by
        rw [← ENNReal.rpow_mul] <;> norm_num
      rw [h2]
      have h3 : (1 / (3 : ℝ)) * (3 : ℝ) = 1 := by norm_num
      rw [h3]
      simp
    have h_cancel : (volume U ^ (1 / (3 : ℝ))) ^ 3 = volume U := h_rpow3 (volume U)
    rw [h_cancel] at h_pow
    exact h_pow

/--
If each A_i ⊆ B_i, then sum of indicators of A_i ≤ sum of indicators of B_i.
-/
lemma multiplicity_mono {α : Type*} {ι : Type*} [Fintype ι]
    (A B : ι → Set α) (h : ∀ i, A i ⊆ B i) (p : α) :
    (∑ i : ι, (A i).indicator (fun _ => (1 : ℝ)) p) ≤
    (∑ i : ι, (B i).indicator (fun _ => (1 : ℝ)) p) := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hp : p ∈ A i
  · have hp' : p ∈ B i := h i hp
    have h_left : (A i).indicator (fun _ => (1 : ℝ)) p = 1 := by
      rw [Set.indicator_of_mem hp]
    have h_right : (B i).indicator (fun _ => (1 : ℝ)) p = 1 := by
      rw [Set.indicator_of_mem hp']
    rw [h_left, h_right]
  · have h_left : (A i).indicator (fun _ => (1 : ℝ)) p = 0 := by
      simp [hp]
    rw [h_left]
    have h_nonneg : 0 ≤ (B i).indicator (fun _ => (1 : ℝ)) p := by
      apply Set.indicator_nonneg
      intro _ _; norm_num
    exact h_nonneg

end Kakeya.Assouad
