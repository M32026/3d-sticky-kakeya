import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exponential domination lemmas

For the `h_union_bound` hypothesis of `probabilistic_thinning`.
-/

noncomputable section

namespace Kakeya.Assouad.Subunit

/--
For real `s`, `c > 0`, `ε > 0`, there exists `X > 0` such that for all `x ≥ X`:
`x^s * Real.exp (-c * x) < ε`.
-/
lemma rpow_mul_exp_neg_tends_to_zero
    {s c : ℝ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∃ (X : ℝ), 0 < X ∧ ∀ (x : ℝ), x ≥ X → x ^ s * Real.exp (-c * x) < ε := by
  have h1 : (fun x : ℝ => x ^ s) =o[Filter.atTop] (fun x : ℝ => Real.exp (c * x)) :=
    isLittleO_rpow_exp_pos_mul_atTop s hc
  have h2 : Filter.Tendsto (fun x : ℝ => x ^ s / Real.exp (c * x)) Filter.atTop (nhds 0) :=
    h1.tendsto_div_nhds_zero
  have h3 : (fun x : ℝ => x ^ s / Real.exp (c * x)) = (fun x : ℝ => x ^ s * Real.exp (-c * x)) := by
    funext x
    have h4 : Real.exp (c * x) ≠ 0 := Real.exp_ne_zero _
    have h5 : x ^ s / Real.exp (c * x) = x ^ s * (Real.exp (c * x))⁻¹ := by
      field_simp [h4] <;> ring
    rw [h5]
    have h6 : (Real.exp (c * x))⁻¹ = Real.exp (-c * x) := by
      rw [← Real.exp_neg]
      <;> ring
    rw [h6]
  rw [h3] at h2
  have h4 : ∃ (X : ℝ), ∀ (x : ℝ), x ≥ X → dist (x ^ s * Real.exp (-c * x)) 0 < ε :=
    Metric.tendsto_atTop.mp h2 ε hε
  rcases h4 with ⟨X, hX⟩
  let X' := max X 1
  have hX'_pos : 0 < X' := by positivity
  have h5 : ∀ (x : ℝ), x ≥ X' → x ^ s * Real.exp (-c * x) < ε := by
    intro x hx
    have h6 : x ≥ X := le_trans (le_max_left X 1) hx
    have h7 : dist (x ^ s * Real.exp (-c * x)) 0 < ε := hX x h6
    have h_pos : 0 ≤ x := by linarith [show (1 : ℝ) ≤ X' from le_max_right X 1]
    have h8 : 0 ≤ x ^ s * Real.exp (-c * x) := by positivity
    have h9 : dist (x ^ s * Real.exp (-c * x)) 0 = x ^ s * Real.exp (-c * x) := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg h8]
    rw [h9] at h7
    exact h7
  exact ⟨X', hX'_pos, h5⟩

/--
Given `A > 0`, `c > 0`, `η' > 0`, there exists `delta₀ > 0` such that for all
`0 < δ ≤ delta₀`: `(1/δ)^A * Real.exp (-c * δ^{-η'}) < 1 / 16`.
-/
lemma union_bound_small_delta
    {A c η' : ℝ} (hA : 0 < A) (hc : 0 < c) (hη : 0 < η') :
    ∃ (delta₀ : ℝ), 0 < delta₀ ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ delta₀ →
      (1 / δ) ^ A * Real.exp (-c * δ ^ (-η')) < 1 / 16 := by
  set s : ℝ := A / η' with hs_def
  have hs_pos : 0 < s := by positivity
  rcases rpow_mul_exp_neg_tends_to_zero hc (by norm_num : (0 : ℝ) < 1 / 16) with ⟨X, hX_pos, hX⟩
  set delta₀ : ℝ := X ^ (-1 / η') with hdelta₀_def
  have hdelta₀_pos : 0 < delta₀ := Real.rpow_pos_of_pos hX_pos _
  have h_key : ∀ (δ : ℝ), 0 < δ → δ ≤ delta₀ → δ ^ (-η') ≥ X := by
    intro δ hδ hδle
    have h1 : 0 < δ ^ η' := by positivity
    have h2 : δ ^ η' ≤ delta₀ ^ η' := by gcongr
    have h3 : delta₀ ^ η' = X⁻¹ := by
      rw [hdelta₀_def]
      have h4 : (X ^ (-1 / η')) ^ η' = X ^ ((-1 / η') * η') := by
        rw [← Real.rpow_mul (by linarith)] <;> ring
      rw [h4]
      have h5 : (-1 / η') * η' = -1 := by
        field_simp [hη.ne'] <;> ring
      rw [h5]
      have h6 : X ^ (-1 : ℝ) = X⁻¹ := by
        rw [Real.rpow_neg (by linarith)] <;> simp
      rw [h6]
    rw [h3] at h2
    have h6 : (δ ^ η')⁻¹ ≥ (X⁻¹)⁻¹ := by
      gcongr
      <;> linarith
    have h7 : (X⁻¹)⁻¹ = X := by
      field_simp [hX_pos.ne'] <;> ring
    rw [h7] at h6
    have h8 : δ ^ (-η') = (δ ^ η')⁻¹ := by
      rw [Real.rpow_neg (by linarith)] <;> ring
    rw [h8]
    exact h6
  refine' ⟨delta₀, hdelta₀_pos, _⟩
  intro δ hδ hδle
  set x : ℝ := δ ^ (-η') with hx_def
  have hx_ge : x ≥ X := h_key δ hδ hδle
  have h10 : x ^ s = (1 / δ) ^ A := by
    have h11 : x = δ ^ (-η') := rfl
    rw [h11]
    have h12 : (δ ^ (-η')) ^ s = δ ^ ((-η') * s) := by
      rw [← Real.rpow_mul (by linarith)] <;> ring
    rw [h12]
    have h13 : (-η') * s = -A := by
      rw [hs_def] <;> field_simp [hη.ne'] <;> ring
    rw [h13]
    have h14 : δ ^ (-A) = (1 / δ) ^ A := by
      have h141 : δ ^ (-A) = (δ ^ A)⁻¹ := by
        rw [Real.rpow_neg (by linarith)] <;> ring
      have h142 : (1 / δ) ^ A = (δ⁻¹) ^ A := by
        have h : (1 / δ) = δ⁻¹ := by ring
        rw [h]
      rw [h141, h142]
      have h143 : (δ ^ A)⁻¹ = (δ⁻¹) ^ A := by
        rw [← Real.inv_rpow (by linarith)]
        <;> ring
      exact h143
    exact h14
  have h15 : x ^ s * Real.exp (-c * x) < 1 / 16 := hX x hx_ge
  rw [h10] at h15
  exact h15

/--
Given `c > 0`, `e < 0`, there exists `delta₀ > 0` such that for all
`0 < δ ≤ delta₀`: `c * Real.rpow δ e > Real.log 16`.
-/
lemma rpow_negative_tends_to_inf
    {c e : ℝ} (hc : 0 < c) (he : e < 0) :
    ∃ (delta₀ : ℝ), 0 < delta₀ ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ delta₀ →
      c * Real.rpow δ e > Real.log 16 := by
  set y : ℝ := -e with hy_def
  have hy_pos : 0 < y := by linarith
  have hlog_pos : 0 < Real.log 16 := by
    apply Real.log_pos
    norm_num
  set target : ℝ := c / (Real.log 16 + 1) with htarget_def
  have htarget_pos : 0 < target := by positivity
  set delta₀ : ℝ := target ^ (1 / y) with hdelta₀_def
  have hdelta₀_pos : 0 < delta₀ := Real.rpow_pos_of_pos htarget_pos _
  have h_key : ∀ (δ : ℝ), 0 < δ → δ ≤ delta₀ → δ ^ y ≤ target := by
    intro δ hδ hδle
    have h1 : δ ^ y ≤ delta₀ ^ y := by gcongr
    have h2 : delta₀ ^ y = target := by
      rw [hdelta₀_def]
      have h3 : (target ^ (1 / y)) ^ y = target ^ ((1 / y) * y) := by
        rw [← Real.rpow_mul (by linarith)] <;> ring
      rw [h3]
      have h4 : (1 / y) * y = 1 := by field_simp [hy_pos.ne'] <;> ring
      rw [h4] <;> simp
    rw [h2] at h1
    exact h1
  refine' ⟨delta₀, hdelta₀_pos, _⟩
  intro δ hδ hδle
  have h1 : δ ^ y ≤ target := h_key δ hδ hδle
  have h2 : 0 < δ ^ y := by positivity
  have h3 : δ ^ e = (δ ^ y)⁻¹ := by
    have h4 : e = -y := by linarith
    rw [h4, Real.rpow_neg (by linarith)] <;> ring
  have h_goal : c * (δ ^ e) > Real.log 16 := by
    rw [h3]
    have h5 : c * (δ ^ y)⁻¹ ≥ c * target⁻¹ := by
      gcongr <;> linarith
    have h6 : c * target⁻¹ = Real.log 16 + 1 := by
      rw [htarget_def]
      field_simp [hlog_pos.ne'] <;> ring
    rw [h6] at h5
    linarith
  exact h_goal

end Kakeya.Assouad.Subunit
