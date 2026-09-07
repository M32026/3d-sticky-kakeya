module

public import MyLeanRepo.robust_kaufman_projection.Base

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Metric Set Classical

namespace RobustKaufmanProjection.EnergyToDeltaSet

/-!
# Regularized kernel and Frostman lemma

Shared definitions for the EnergyToDeltaSet extraction.
-/

noncomputable section

/-- Regularized 1D Riesz kernel: max(|d|, δ)^{-s}. -/
def regularizedKernel (s δ : ℝ) (d : ℝ) : ENNReal :=
  ENNReal.ofReal ((max |d| δ) ^ (-s))

/-- Regularized 1D Riesz energy. -/
def regularizedEnergy (μ : Measure ℝ) (s δ : ℝ) : ENNReal :=
  ∫⁻ x, ∫⁻ y, regularizedKernel s δ (x - y) ∂μ ∂μ

/-- For r ≥ δ and |d| ≤ r, regularizedKernel s δ d ≥ r^{-s}. -/
lemma regularized_kernel_lower_bound {s δ r d : ℝ}
    (hs : 0 < s) (hδ : 0 < δ) (hr : δ ≤ r) (hd : |d| ≤ r) :
    ENNReal.ofReal (r ^ (-s)) ≤ regularizedKernel s δ d := by
  have h1 : max |d| δ ≤ r := max_le hd hr
  have h2 : 0 < max |d| δ := by positivity
  have h3 : (max |d| δ) ^ (-s) ≥ r ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos h2 h1 (by linarith)
  simpa [regularizedKernel] using ENNReal.ofReal_le_ofReal h3

/-- If regularized potential U(x) ≤ E, then μ(B(x,r)) ≤ E·r^s for r ≥ δ. -/
lemma potential_frostman_regularized {μ : Measure ℝ} {s δ E x r : ℝ}
    (hs : 0 < s) (hδ : 0 < δ) (hr : δ ≤ r) (hE : 0 ≤ E)
    (hU : (∫⁻ y, regularizedKernel s δ (x - y) ∂μ) ≤ ENNReal.ofReal E) :
    μ (closedBall x r) ≤ ENNReal.ofReal (E * r ^ s) := by
  let B := closedBall x r
  have hB_meas : MeasurableSet B := by exact measurableSet_closedBall
  have h_ae : ∀ᵐ (y : ℝ) ∂(μ.restrict B),
      ENNReal.ofReal (r ^ (-s)) ≤ regularizedKernel s δ (x - y) := by
    filter_upwards [ae_restrict_mem hB_meas] with y hy
    have h2 : dist y x ≤ r := by simpa [B, Metric.mem_closedBall] using hy
    have h3 : |y - x| ≤ r := by simpa [dist_eq_norm] using h2
    have h4 : |x - y| ≤ r := by rw [abs_sub_comm] <;> exact h3
    exact regularized_kernel_lower_bound hs hδ hr h4
  have h_main1 : ∫⁻ y, regularizedKernel s δ (x - y) ∂μ ≥
      ∫⁻ y in B, regularizedKernel s δ (x - y) ∂μ :=
    lintegral_mono' Measure.restrict_le_self le_rfl
  have h_main2 : ∫⁻ y in B, regularizedKernel s δ (x - y) ∂μ ≥
      ∫⁻ y in B, ENNReal.ofReal (r ^ (-s)) ∂μ :=
    lintegral_mono_ae h_ae
  have h_const : ∫⁻ y in B, ENNReal.ofReal (r ^ (-s)) ∂μ =
      ENNReal.ofReal (r ^ (-s)) * μ B := by
    simp [lintegral_const] <;> rfl
  have h6 : ENNReal.ofReal (r ^ (-s)) * μ B ≤ ENNReal.ofReal E := by
    calc ENNReal.ofReal (r ^ (-s)) * μ B
      = ∫⁻ y in B, ENNReal.ofReal (r ^ (-s)) ∂μ := h_const.symm
    _ ≤ ∫⁻ y in B, regularizedKernel s δ (x - y) ∂μ := h_main2
    _ ≤ ∫⁻ y, regularizedKernel s δ (x - y) ∂μ := h_main1
    _ ≤ ENNReal.ofReal E := hU
  have h7 : 0 < r ^ (-s) := Real.rpow_pos_of_pos (by linarith) (-s)
  have h8 : ENNReal.ofReal (r ^ (-s)) ≠ 0 := by
    have h_pos : 0 < r ^ (-s) := h7
    exact ENNReal.ofReal_ne_zero_iff.mpr h7
  have h9 : ENNReal.ofReal (r ^ (-s)) ≠ ⊤ := by simp
  set a : ENNReal := ENNReal.ofReal (r ^ (-s)) with ha
  have h10 : μ B ≤ a⁻¹ * ENNReal.ofReal E := by
    have h11 : a * μ B ≤ ENNReal.ofReal E := h6
    have h12 : a⁻¹ * (a * μ B) ≤ a⁻¹ * ENNReal.ofReal E := by gcongr
    have h13 : a⁻¹ * (a * μ B) = μ B := by
      have h14 : a⁻¹ * (a * μ B) = (a⁻¹ * a) * μ B := by rw [mul_assoc]
      rw [h14]
      have h15 : a⁻¹ * a = 1 := by exact ENNReal.inv_mul_cancel h8 h9
      rw [h15, one_mul]
    rw [h13] at h12
    exact h12
  have h13 : a⁻¹ = ENNReal.ofReal (r ^ s) := by
    have h14 : a = ENNReal.ofReal (r ^ (-s)) := by simp [a]
    rw [h14]
    have h15 : (ENNReal.ofReal (r ^ (-s)))⁻¹ = ENNReal.ofReal ((r ^ (-s))⁻¹) :=
      (ENNReal.ofReal_inv_of_pos h7).symm
    rw [h15]
    have h16 : (r ^ (-s))⁻¹ = r ^ s := by
      have h17 : 0 ≤ r := by linarith
      have h18 : r ^ (-s) = (r ^ s)⁻¹ := by
        rw [Real.rpow_neg h17] <;> ring
      rw [h18] <;> field_simp
    rw [h16]
  rw [h13] at h10
  have h16 : 0 ≤ r ^ s := Real.rpow_nonneg (by linarith) s
  have h15 : ENNReal.ofReal (r ^ s) * ENNReal.ofReal E = ENNReal.ofReal (E * r ^ s) := by
    have h17 : ENNReal.ofReal (r ^ s) * ENNReal.ofReal E = ENNReal.ofReal ((r ^ s) * E) := by
      rw [← ENNReal.ofReal_mul h16] <;> ring
    rw [h17]
    have h18 : (r ^ s) * E = E * r ^ s := by ring
    rw [h18]
  rw [h15] at h10
  exact h10

/-- Markov: if ∫⁻ f dμ ≤ E and f measurable, then μ({x : f x ≤ 2E}) ≥ 1/2. -/
lemma markov_half {μ : Measure ℝ} {f : ℝ → ENNReal} {E : ℝ} (hE : 0 < E)
    (hf_meas : Measurable f)
    (hμ_univ : μ Set.univ = 1)
    (h_int : ∫⁻ x, f x ∂μ ≤ ENNReal.ofReal E) :
    μ {x | f x ≤ ENNReal.ofReal (2 * E)} ≥ ENNReal.ofReal (1 / 2 : ℝ) := by
  let S := {x | f x > ENNReal.ofReal (2 * E)}
  have hS_meas : MeasurableSet S := by
    have h1 : MeasurableSet (Set.Ioi (ENNReal.ofReal (2 * E))) := by
      exact isOpen_Ioi.measurableSet
    exact hf_meas h1
  have h1 : ∫⁻ x, f x ∂μ ≥ ∫⁻ x in S, f x ∂μ :=
    lintegral_mono' Measure.restrict_le_self le_rfl
  have h2 : ∫⁻ x in S, f x ∂μ ≥ ENNReal.ofReal (2 * E) * μ S := by
    have h3 : ∀ᵐ (x : ℝ) ∂(μ.restrict S), ENNReal.ofReal (2 * E) ≤ f x := by
      filter_upwards [ae_restrict_mem hS_meas] with x hx
      exact le_of_lt hx
    have h4 : ∫⁻ x in S, ENNReal.ofReal (2 * E) ∂μ ≤ ∫⁻ x in S, f x ∂μ :=
      lintegral_mono_ae h3
    have h5 : ∫⁻ x in S, ENNReal.ofReal (2 * E) ∂μ =
        ENNReal.ofReal (2 * E) * μ S := by
      simp [lintegral_const] <;> rfl
    calc ENNReal.ofReal (2 * E) * μ S
      = ∫⁻ x in S, ENNReal.ofReal (2 * E) ∂μ := h5.symm
    _ ≤ ∫⁻ x in S, f x ∂μ := h4
  have h5 : ENNReal.ofReal (2 * E) * μ S ≤ ENNReal.ofReal E := by
    calc ENNReal.ofReal (2 * E) * μ S
      ≤ ∫⁻ x in S, f x ∂μ := h2
    _ ≤ ∫⁻ x, f x ∂μ := h1
    _ ≤ ENNReal.ofReal E := h_int
  have h7 : ENNReal.ofReal (2 * E) ≠ 0 := by positivity
  have h8 : ENNReal.ofReal (2 * E) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h9 : μ S ≤ (ENNReal.ofReal (2 * E))⁻¹ * ENNReal.ofReal E := by
    set a : ENNReal := ENNReal.ofReal (2 * E) with ha
    have h10 : a * μ S ≤ ENNReal.ofReal E := h5
    have h11 : a⁻¹ * (a * μ S) ≤ a⁻¹ * ENNReal.ofReal E := by gcongr
    have h12 : a⁻¹ * (a * μ S) = (a⁻¹ * a) * μ S := by rw [mul_assoc]
    have h13 : a⁻¹ * a = 1 := by exact ENNReal.inv_mul_cancel h7 h8
    have h14 : a⁻¹ * (a * μ S) = μ S := by
      rw [h12, h13, one_mul]
    rw [h14] at h11
    exact h11
  have h10 : (ENNReal.ofReal (2 * E))⁻¹ * ENNReal.ofReal E = ENNReal.ofReal (1 / 2 : ℝ) := by
    have h11 : (ENNReal.ofReal (2 * E))⁻¹ = ENNReal.ofReal ((2 * E)⁻¹) :=
      (ENNReal.ofReal_inv_of_pos (by positivity)).symm
    rw [h11]
    have h12 : ENNReal.ofReal ((2 * E)⁻¹) * ENNReal.ofReal E =
        ENNReal.ofReal (((2 * E)⁻¹) * E) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
    rw [h12]
    have h13 : ((2 * E)⁻¹) * E = 1 / 2 := by
      field_simp [hE.ne'] <;> ring
    rw [h13] <;> norm_cast
  have h6 : μ S ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [h10] at h9; exact h9
  let T := {x | f x ≤ ENNReal.ofReal (2 * E)}
  have hT_meas : MeasurableSet T := by
    have h1 : MeasurableSet (Set.Iic (ENNReal.ofReal (2 * E))) := by
      exact isClosed_Iic.measurableSet
    exact hf_meas h1
  have h_disj : Disjoint T S := by
    rw [Set.disjoint_left]
    intro x hxT hxS
    have h_cont : f x ≤ ENNReal.ofReal (2 * E) := hxT
    have h_cont2 : f x > ENNReal.ofReal (2 * E) := hxS
    exact False.elim (not_le.mpr h_cont2 h_cont)
  have h_union : T ∪ S = Set.univ := by
    ext x
    simp only [T, S, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    by_cases h : f x ≤ ENNReal.ofReal (2 * E)
    · exact Or.inl h
    · exact Or.inr (not_le.mp h)
  have h_sum : μ T + μ S = μ Set.univ := by
    rw [← measure_union h_disj hS_meas, h_union, hμ_univ]
  have h_goal : μ T ≥ ENNReal.ofReal (1 / 2 : ℝ) := by
    have h_eq : μ T + μ S = 1 := by
      rw [h_sum, hμ_univ] <;> norm_cast
    by_contra h
    have h_lt : μ T < ENNReal.ofReal (1 / 2 : ℝ) := lt_of_not_ge h
    have hS_ne_top : μ S ≠ ⊤ := by
      have h : μ S ≤ μ Set.univ := measure_mono (subset_univ S)
      rw [hμ_univ] at h
      exact ne_top_of_le_ne_top (by simp) h
    have h_cont : μ T + μ S < ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) :=
      ENNReal.add_lt_add_of_lt_of_le hS_ne_top h_lt h6
    have h_eq2 : ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) = 1 := by
      have h : ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) =
          ENNReal.ofReal ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
        rw [← ENNReal.ofReal_add] <;> norm_num
      rw [h]
      have h2 : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
      rw [h2] <;> simp
    rw [h_eq2] at h_cont
    rw [h_eq] at h_cont
    simpa using h_cont
  exact h_goal

end

end RobustKaufmanProjection.EnergyToDeltaSet
