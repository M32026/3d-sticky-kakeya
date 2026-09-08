import MyLeanRepo.Topology.MetricSpace.MinkowskiDimension
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# Exponential decay estimate for the Hausdorff–Minkowski comparison

This module proves the key technical estimate: if `b < d * log 2`, then
`exp(b*n) * (2 * 2^{-n})^d → 0` as `n → ∞` in `ENNReal`.
-/

noncomputable section

open scoped ENNReal NNReal Topology

namespace Metric

/-- The key exponential decay estimate.

If `b < d * Real.log 2` and `0 ≤ d`, then the sequence
`EReal.exp (b * n) * (2 * 2^{-n})^d` tends to `0` in `ENNReal`. -/
lemma exp_decay_estimate {b d : ℝ} (h : b < d * Real.log 2) (hd : 0 ≤ d) :
    Filter.Tendsto
      (fun n : ℕ =>
        EReal.exp ((b : EReal) * ↑n) *
        (2 * ↑((2 : NNReal)^n)⁻¹ : ENNReal)^d)
      Filter.atTop (nhds 0) := by
  let c : ENNReal := EReal.exp (b : EReal) * ((2 : ENNReal)^d)⁻¹
  have h2_ne_top : (2 : ENNReal)^d ≠ ⊤ := by
    apply ENNReal.rpow_ne_top_of_nonneg hd <;> norm_num
  have h2_pos : (0 : ENNReal) < (2 : ENNReal)^d := by positivity
  have h2_ne_zero : (2 : ENNReal)^d ≠ 0 := h2_pos.ne'
  have hlog : ENNReal.log (2 : ENNReal) = ↑(Real.log 2) := by
    have h : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_num
    rw [h]
    exact ENNReal.log_ofReal_of_pos (by norm_num)
  have h1 : EReal.exp (b : EReal) < (2 : ENNReal)^d := by
    have h3 : (2 : ENNReal)^d = EReal.exp ((d : EReal) * ENNReal.log (2 : ENNReal)) := by
      rw [EReal.ENNReal.rpow_eq_exp_mul_log]
    rw [h3, hlog]
    have h4 : (b : EReal) < ↑(d * Real.log 2) := by exact_mod_cast h
    exact EReal.exp_strictMono h4
  have hmul : (2 : ENNReal)^d * ((2 : ENNReal)^d)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel h2_ne_zero h2_ne_top
  have hinv_ne_zero : ((2 : ENNReal)^d)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr h2_ne_top
  have hinv_ne_top : ((2 : ENNReal)^d)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr h2_ne_zero
  have hc_lt_one : c < 1 := by
    have h51 : ((2 : ENNReal)^d)⁻¹ * EReal.exp (b : EReal) < ((2 : ENNReal)^d)⁻¹ * (2 : ENNReal)^d :=
      ENNReal.mul_lt_mul_right hinv_ne_zero hinv_ne_top h1
    have h52 : EReal.exp (b : EReal) * ((2 : ENNReal)^d)⁻¹ = ((2 : ENNReal)^d)⁻¹ * EReal.exp (b : EReal) := by
      rw [mul_comm]
    have h53 : (2 : ENNReal)^d * ((2 : ENNReal)^d)⁻¹ = ((2 : ENNReal)^d)⁻¹ * (2 : ENNReal)^d := by
      rw [mul_comm]
    have h5 : EReal.exp (b : EReal) * ((2 : ENNReal)^d)⁻¹ < (2 : ENNReal)^d * ((2 : ENNReal)^d)⁻¹ := by
      rw [h52, h53]
      exact h51
    have h6 : EReal.exp (b : EReal) * ((2 : ENNReal)^d)⁻¹ < 1 := by
      rw [hmul] at h5
      exact h5
    exact h6
  have h_coe_inv : ∀ n : ℕ,
      (↑(((2 : NNReal)^n)⁻¹) : ENNReal) = (((2 : ENNReal)^n)⁻¹) := by
    intro n
    let x : NNReal := (2 : NNReal)^n
    have hx_pos : 0 < x := by positivity
    have h_eq : (↑(x⁻¹) : ENNReal) = (↑x : ENNReal)⁻¹ :=
      ENNReal.coe_inv'
    exact h_eq
  have h_main : ∀ n : ℕ,
      EReal.exp ((b : EReal) * ↑n) * (2 * ↑((2 : NNReal)^n)⁻¹ : ENNReal)^d
      = (2 : ENNReal)^d * c^n := by
    intro n
    have h4 : EReal.exp ((b : EReal) * ↑n) = (EReal.exp (b : EReal))^n := by
      have h5 : (b : EReal) * ↑n = (↑n : EReal) * (b : EReal) := by
        simp [mul_comm]
      rw [h5]
      exact EReal.exp_nmul (b : EReal) n
    rw [h4]
    have h6 : (2 * ↑((2 : NNReal)^n)⁻¹ : ENNReal)^d
        = (2 : ENNReal)^d * (((2 : ENNReal)^n)^d)⁻¹ := by
      have h7 : (2 * ↑((2 : NNReal)^n)⁻¹ : ENNReal)
          = (2 : ENNReal) * ((2 : ENNReal)^n)⁻¹ := by
        rw [h_coe_inv n]
      rw [h7, ENNReal.mul_rpow_of_nonneg _ _ hd, ENNReal.inv_rpow]
    rw [h6]
    have h8 : (((2 : ENNReal)^n)^d)⁻¹ = ((2 : ENNReal)^(d * ↑n))⁻¹ := by
      have h9 : ((2 : ENNReal)^n)^d = (2 : ENNReal)^(↑n * d) :=
        (ENNReal.rpow_natCast_mul (2 : ENNReal) n d).symm
      rw [h9]
      have h10 : (↑n * d : ℝ) = d * ↑n := by ring
      rw [h10]
    rw [h8]
    have h10 : c^n = (EReal.exp (b : EReal))^n * ((2 : ENNReal)^(d * ↑n))⁻¹ := by
      have h11 : c^n = (EReal.exp (b : EReal))^n * (((2 : ENNReal)^d)⁻¹)^n := by
        simp [c, mul_pow]
      rw [h11]
      have h12 : (((2 : ENNReal)^d)⁻¹)^n = (((2 : ENNReal)^d)^n)⁻¹ := by
        rw [ENNReal.inv_pow]
      rw [h12]
      have h13 : ((2 : ENNReal)^d)^n = (2 : ENNReal)^(d * ↑n) :=
        (ENNReal.rpow_mul_natCast (2 : ENNReal) d n).symm
      rw [h13]
    rw [h10] <;> ring
  have h11 : Filter.Tendsto (fun x : ℝ => c^x) Filter.atTop (nhds 0) :=
    ENNReal.tendsto_rpow_atTop_of_base_lt_one hc_lt_one
  have h12 : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have h13 : Filter.Tendsto (fun n : ℕ => c ^ (n : ℝ)) Filter.atTop (nhds 0) :=
    h11.comp h12
  have h14 : Filter.Tendsto (fun n : ℕ => c^n) Filter.atTop (nhds 0) := by
    have h15 : (fun n : ℕ => c ^ (n : ℝ)) = (fun n : ℕ => c^n) := by
      funext n; rw [ENNReal.rpow_natCast]
    rw [h15] at h13
    exact h13
  have h15 : Filter.Tendsto (fun n : ℕ => (2 : ENNReal)^d * c^n) Filter.atTop (nhds 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    let δ : ENNReal := ε * ((2 : ENNReal)^d)⁻¹
    have hδ_pos : 0 < δ := ENNReal.mul_pos hε.ne' hinv_ne_zero
    have h_event : ∀ᶠ n in Filter.atTop, c^n < δ := h14 (Iio_mem_nhds hδ_pos)
    filter_upwards [h_event] with n hn
    have h6 : (2 : ENNReal)^d * c^n < ε := by
      calc
        (2 : ENNReal)^d * c^n
          < (2 : ENNReal)^d * δ := ENNReal.mul_lt_mul_right h2_ne_zero h2_ne_top hn
        _ = (2 : ENNReal)^d * (ε * ((2 : ENNReal)^d)⁻¹) := by rfl
        _ = ε * ((2 : ENNReal)^d * ((2 : ENNReal)^d)⁻¹) := by
          have h71 : (2 : ENNReal)^d * (ε * ((2 : ENNReal)^d)⁻¹)
              = ((2 : ENNReal)^d * ε) * ((2 : ENNReal)^d)⁻¹ := by
            rw [mul_assoc]
          rw [h71]
          have h72 : (2 : ENNReal)^d * ε = ε * (2 : ENNReal)^d := by
            exact mul_comm _ _
          rw [h72, ← mul_assoc]
        _ = ε := by rw [hmul, mul_one]
    exact h6.le
  have h_final : Filter.Tendsto (fun n : ℕ => EReal.exp ((b : EReal) * ↑n) * (2 * ↑((2 : NNReal)^n)⁻¹ : ENNReal)^d) Filter.atTop (nhds 0) := by
    convert h15 using 1
    funext n
    exact h_main n
  exact h_final

end Metric
