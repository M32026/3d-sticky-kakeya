import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Inequality utilities for John ellipsoid proofs

This module provides basic real-analysis and inequality lemmas used by the
symmetric inclusion and uniqueness teams.

## Main results
- `sqrt_pos_nat`, `inv_sqrt_pos`: positivity of square roots
- `sq_le_of_norm_le`: norm squaring bound
- `real_log_det_concave`: log-determinant concavity via log concavity
- `exp_strict_mono`: strict monotonicity of `Real.exp`
- `small_t_exists`: positive derivative at zero implies local positivity
- `polynomial_positive_at_zero`: polynomial special case
- `log_det_expansion`: first-order positivity of a specific log-expression
-/

namespace JohnEllipsoid

/-- For `n > 0`, `Real.sqrt (n : ℝ)` is positive. -/
lemma sqrt_pos_nat {n : ℕ} (hn : 0 < n) : 0 < Real.sqrt (n : ℝ) :=
  Real.sqrt_pos.mpr (by exact_mod_cast hn)

/-- For `n > 0`, the inverse of `Real.sqrt (n : ℝ)` is positive. -/
lemma inv_sqrt_pos {n : ℕ} (hn : 0 < n) : 0 < (Real.sqrt (n : ℝ))⁻¹ := by
  positivity

/-- If `‖x‖ ≤ 1 / Real.sqrt n`, then `‖x‖^2 ≤ 1 / n`. -/
lemma sq_le_of_norm_le {n : ℕ} {x : EuclideanSpace ℝ (Fin n)}
    (h : ‖x‖ ≤ 1 / Real.sqrt (n : ℝ)) : ‖x‖ ^ 2 ≤ 1 / (n : ℝ) := by
  have h₁ : 0 ≤ ‖x‖ := by positivity
  by_cases hn : n = 0
  · subst hn
    have h₄ : ‖x‖ ≤ 0 := by simpa using h
    have h₅ : ‖x‖ = 0 := by linarith
    simp [h₅]
  · have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hpos
    have hsqrt : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
    have h₂ : (1 / Real.sqrt (n : ℝ)) ^ 2 = 1 / (n : ℝ) := by
      calc
        (1 / Real.sqrt (n : ℝ)) ^ 2
          = 1 / (Real.sqrt (n : ℝ) ^ 2) := by
            field_simp [hsqrt_pos.ne'] <;> ring
        _ = 1 / (n : ℝ) := by rw [hsqrt]
    have h₃ : ‖x‖ ^ 2 ≤ (1 / Real.sqrt (n : ℝ)) ^ 2 := by
      gcongr <;> linarith [h₁]
    rw [h₂] at h₃
    exact h₃

/-- Two-point weighted concavity of `Real.log` on positive reals. -/
lemma log_concave_two_point {x y : ℝ} (hx : 0 < x) (hy : 0 < y) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1 - t) * Real.log x + t * Real.log y ≤ Real.log ((1 - t) * x + t * y) := by
  let s2 : Finset Bool := {false, true}
  let w : Bool → ℝ := fun b => if b then t else 1 - t
  let p : Bool → ℝ := fun b => if b then y else x
  have h_t_nonneg : 0 ≤ t := ht.1
  have h_t_le_one : t ≤ 1 := ht.2
  have h₀ : ∀ b ∈ s2, 0 ≤ w b := by
    intro b _
    simp only [w]
    split_ifs <;> linarith
  have h₁ : ∑ b ∈ s2, w b = 1 := by
    simp [s2, w, Finset.sum_insert, Finset.sum_singleton] <;> ring
  have hmem : ∀ b ∈ s2, p b ∈ Set.Ioi (0 : ℝ) := by
    intro b _
    simp only [p, Set.mem_Ioi]
    split_ifs <;> tauto
  have h_jensen : ∑ b ∈ s2, w b • Real.log (p b) ≤ Real.log (∑ b ∈ s2, w b • p b) :=
    strictConcaveOn_log_Ioi.concaveOn.le_map_sum h₀ h₁ hmem
  simpa [s2, w, p, Finset.sum_insert, Finset.sum_singleton, smul_eq_mul] using h_jensen

/-- Log-concavity of products: for positive `a i, b i` and `t ∈ [0,1]`,
`log (∏ ((1-t)*a i + t*b i)) ≥ (1-t)*log(∏ a i) + t*log(∏ b i)`. -/
lemma real_log_det_concave {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hb : ∀ i ∈ s, 0 < b i) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Real.log (∏ i ∈ s, ((1 - t) * a i + t * b i)) ≥
    (1 - t) * Real.log (∏ i ∈ s, a i) + t * Real.log (∏ i ∈ s, b i) := by
  have h_pos : ∀ i ∈ s, 0 < (1 - t) * a i + t * b i := by
    intro i hi
    have h₂ : 0 ≤ 1 - t := by linarith [ht.2]
    have h₃ : 0 ≤ t := by linarith [ht.1]
    have h₄ : 0 < a i := ha i hi
    have h₅ : 0 < b i := hb i hi
    by_cases h₆ : 0 < 1 - t
    · have h₇ : 0 < (1 - t) * a i := mul_pos h₆ h₄
      have h₈ : 0 ≤ t * b i := by positivity
      linarith
    · have h₉ : 1 - t = 0 := by linarith
      have h₁₀ : t = 1 := by linarith
      rw [h₁₀] <;> simpa using h₅
  have h_ne_zero : ∀ i ∈ s, ((1 - t) * a i + t * b i) ≠ 0 := fun i hi => (h_pos i hi).ne'
  have h_main : ∀ i ∈ s, Real.log ((1 - t) * a i + t * b i) ≥
      (1 - t) * Real.log (a i) + t * Real.log (b i) := by
    intro i hi
    exact log_concave_two_point (ha i hi) (hb i hi) ht
  have h₄ : ∑ i ∈ s, Real.log ((1 - t) * a i + t * b i) ≥
      ∑ i ∈ s, ((1 - t) * Real.log (a i) + t * Real.log (b i)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact h_main i hi
  have h₅ : Real.log (∏ i ∈ s, ((1 - t) * a i + t * b i)) =
      ∑ i ∈ s, Real.log ((1 - t) * a i + t * b i) := by
    rw [Real.log_prod (hf := h_ne_zero)]
  have h₆ : Real.log (∏ i ∈ s, a i) = ∑ i ∈ s, Real.log (a i) := by
    rw [Real.log_prod (hf := fun i hi => (ha i hi).ne')]
  have h₇ : Real.log (∏ i ∈ s, b i) = ∑ i ∈ s, Real.log (b i) := by
    rw [Real.log_prod (hf := fun i hi => (hb i hi).ne')]
  have h₈ : ∑ i ∈ s, ((1 - t) * Real.log (a i) + t * Real.log (b i)) =
      (1 - t) * ∑ i ∈ s, Real.log (a i) + t * ∑ i ∈ s, Real.log (b i) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum] <;> ring
  calc
    Real.log (∏ i ∈ s, ((1 - t) * a i + t * b i))
      = ∑ i ∈ s, Real.log ((1 - t) * a i + t * b i) := h₅
    _ ≥ ∑ i ∈ s, ((1 - t) * Real.log (a i) + t * Real.log (b i)) := h₄
    _ = (1 - t) * ∑ i ∈ s, Real.log (a i) + t * ∑ i ∈ s, Real.log (b i) := h₈
    _ = (1 - t) * Real.log (∏ i ∈ s, a i) + t * Real.log (∏ i ∈ s, b i) := by
      rw [h₆, h₇] <;> ring

/-- `Real.exp` is strictly monotone. -/
lemma exp_strict_mono : StrictMono Real.exp :=
  Real.exp_strictMono

/-- If `f(0) = 0` and `f'(0) = a > 0`, then `f(t) > 0` for all sufficiently small `t > 0`. -/
lemma small_t_exists (f : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hderiv : HasDerivAt f a 0) (h0 : f 0 = 0) :
    ∃ ε > 0, ∀ t ∈ Set.Ioo 0 ε, 0 < f t := by
  have h_slope : Filter.Tendsto (fun t : ℝ => f t / t) (nhdsWithin 0 {0}ᶜ) (nhds a) := by
    have h : Filter.Tendsto (slope f 0) (nhdsWithin 0 {0}ᶜ) (nhds a) := hderiv.tendsto_slope
    have h_eq : slope f 0 = fun t : ℝ => f t / t := by
      funext t
      simp [slope, h0]
      <;> ring
    rw [h_eq] at h
    exact h
  have h_nhds : ∀ᶠ (y : ℝ) in nhds a, 0 < y := Ioi_mem_nhds ha
  have h₂ : ∀ᶠ t in nhdsWithin 0 {0}ᶜ, 0 < f t / t := h_slope.eventually h_nhds
  rcases Metric.mem_nhdsWithin_iff.mp h₂ with ⟨ε, hε, h₃⟩
  refine ⟨ε, hε, fun t ht => ?_⟩
  have h₄ : t ≠ 0 := ht.1.ne'
  have h₅ : dist t 0 < ε := by
    simpa [Real.dist_eq, abs_lt] using ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h_ball : t ∈ Metric.ball 0 ε := by simpa [Metric.mem_ball] using h₅
  have h_set : t ∈ ({0} : Set ℝ)ᶜ := by simpa using h₄
  have h₆ : 0 < f t / t := h₃ ⟨h_ball, h_set⟩
  have h₇ : 0 < t := ht.1
  have h₈ : 0 < f t := by
    by_contra h
    have h₉ : f t ≤ 0 := by linarith
    have h₁₀ : f t / t ≤ 0 := div_nonpos_of_nonpos_of_nonneg h₉ (by linarith)
    linarith
  exact h₈

/-- If a real polynomial `p` satisfies `p(0) = 0` and `p'(0) > 0`, then
`p(t) > 0` for all sufficiently small `t > 0`. -/
lemma polynomial_positive_at_zero (p : Polynomial ℝ) (h0 : p.eval 0 = 0)
    (hderiv : 0 < (Polynomial.derivative p).eval 0) :
    ∃ ε > 0, ∀ t ∈ Set.Ioo 0 ε, 0 < p.eval t := by
  let f : ℝ → ℝ := fun t => p.eval t
  have hderiv' : HasDerivAt f ((Polynomial.derivative p).eval 0) 0 := by
    exact Polynomial.hasDerivAt p 0
  exact small_t_exists f ((Polynomial.derivative p).eval 0) hderiv hderiv' h0

/-- For `a > n`, there exists `ε > 0` such that for `0 < t < ε`,
`Real.log ((1 - t)^((n : ℝ) - 1) * (1 + t * (a - 1))) > 0`.
This follows because the expression equals `0` at `t = 0` and its derivative
there is `a - n > 0`. -/
lemma log_det_expansion {n : ℕ} {a : ℝ} (ha : (n : ℝ) < a) :
    ∃ ε > 0, ∀ t ∈ Set.Ioo 0 ε,
    0 < Real.log ((1 - t) ^ ((n : ℝ) - 1) * (1 + t * (a - 1))) := by
  let f : ℝ → ℝ := fun t =>
    ((n : ℝ) - 1) * Real.log (1 - t) + Real.log (1 + t * (a - 1))
  have h_f0 : f 0 = 0 := by
    simp [f] <;> norm_num
  have h_inner1 : HasDerivAt (fun t : ℝ => 1 - t) (-1 : ℝ) 0 := by
    have h : HasDerivAt (fun t : ℝ => -t) (-1 : ℝ) 0 := (hasDerivAt_id (0 : ℝ)).neg
    simpa [sub_eq_add_neg] using h.add_const 1
  have h_log1 : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-1 : ℝ) 0 := by
    have h : HasDerivAt (fun y : ℝ => Real.log (1 - y)) ((-1 : ℝ) / (1 - 0)) 0 := h_inner1.log (by norm_num)
    convert h using 1 <;> norm_num
  have h1 : HasDerivAt (fun t : ℝ => ((n : ℝ) - 1) * Real.log (1 - t))
      (((n : ℝ) - 1) * (-1 : ℝ)) 0 := h_log1.const_mul ((n : ℝ) - 1)
  have h_inner2 : HasDerivAt (fun t : ℝ => 1 + t * (a - 1)) (a - 1) 0 := by
    have h : HasDerivAt (fun t : ℝ => t * (a - 1)) (a - 1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const (a - 1)
    have h' : HasDerivAt (fun t : ℝ => t * (a - 1) + 1) (a - 1) 0 := h.add_const 1
    convert h' using 1 <;> funext x <;> ring
  have h_log2 : HasDerivAt (fun t : ℝ => Real.log (1 + t * (a - 1))) (a - 1) 0 := by
    have h : HasDerivAt (fun y : ℝ => Real.log (1 + y * (a - 1))) ((a - 1) / (1 + 0 * (a - 1))) 0 := h_inner2.log (by norm_num)
    convert h using 1 <;> norm_num
  have h_total : HasDerivAt f (((n : ℝ) - 1) * (-1 : ℝ) + (a - 1)) 0 := h1.add h_log2
  have h_eq : ((n : ℝ) - 1) * (-1 : ℝ) + (a - 1) = a - (n : ℝ) := by ring
  have h_deriv : HasDerivAt f (a - (n : ℝ)) 0 := by
    rw [h_eq] at h_total
    exact h_total
  have ha' : 0 < a - (n : ℝ) := by linarith
  rcases small_t_exists f (a - (n : ℝ)) ha' h_deriv h_f0 with ⟨ε1, hε1, hpos⟩
  have h_cont2 : ContinuousAt (fun t : ℝ => 1 + t * (a - 1)) 0 := by
    exact (continuous_const.add (continuous_id.mul continuous_const)).continuousAt
  have h_image_pos : 0 < (fun t : ℝ => 1 + t * (a - 1)) 0 := by norm_num
  have h_pos2_ev : ∀ᶠ t in nhds 0, 0 < 1 + t * (a - 1) :=
    h_cont2.eventually (Ioi_mem_nhds h_image_pos)
  rcases Metric.mem_nhds_iff.mp h_pos2_ev with ⟨δ2, hδ2, h₂⟩
  let ε := min ε1 (min (1 / 2 : ℝ) δ2)
  have hε : 0 < ε := by positivity
  have h_ε_le_ε1 : ε ≤ ε1 := min_le_left ε1 (min (1 / 2 : ℝ) δ2)
  have h_ε_le_half : ε ≤ 1 / 2 := by
    calc ε ≤ min (1 / 2 : ℝ) δ2 := min_le_right _ _
         _ ≤ 1 / 2 := min_le_left _ _
  have h_ε_le_δ2 : ε ≤ δ2 := by
    calc ε ≤ min (1 / 2 : ℝ) δ2 := min_le_right _ _
         _ ≤ δ2 := min_le_right _ _
  refine ⟨ε, hε, fun t ht => ?_⟩
  have h_t1 : t ∈ Set.Ioo 0 ε1 := by
    exact ⟨ht.1, lt_of_lt_of_le ht.2 h_ε_le_ε1⟩
  have h_pos_f : 0 < f t := hpos t h_t1
  have h_1mt : 0 < 1 - t := by
    have h : t < 1 / 2 := lt_of_lt_of_le ht.2 h_ε_le_half
    linarith
  have h_abs : |t| < δ2 := by
    have h_pos : 0 < t := ht.1
    have h_lt : t < δ2 := lt_of_lt_of_le ht.2 h_ε_le_δ2
    rw [abs_of_pos h_pos] <;> linarith
  have h_2 : 0 < 1 + t * (a - 1) := h₂ (by simpa [Real.dist_eq] using h_abs)
  have h_f_eq : f t = Real.log ((1 - t) ^ ((n : ℝ) - 1) * (1 + t * (a - 1))) := by
    have h₃ : Real.log ((1 - t) ^ ((n : ℝ) - 1)) =
        ((n : ℝ) - 1) * Real.log (1 - t) := by
      rw [Real.log_rpow (by linarith)] <;> ring
    have h_base_pos : 0 < (1 - t) ^ ((n : ℝ) - 1) := Real.rpow_pos_of_pos h_1mt _
    have h₄ : Real.log ((1 - t) ^ ((n : ℝ) - 1) * (1 + t * (a - 1))) =
        Real.log ((1 - t) ^ ((n : ℝ) - 1)) + Real.log (1 + t * (a - 1)) := by
      exact Real.log_mul (ne_of_gt h_base_pos) (ne_of_gt h_2)
    have h₅ : f t = ((n : ℝ) - 1) * Real.log (1 - t) + Real.log (1 + t * (a - 1)) := by rfl
    rw [h₅, h₄, h₃] <;> rfl
  rw [h_f_eq] at h_pos_f
  exact h_pos_f

end JohnEllipsoid
