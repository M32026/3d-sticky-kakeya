import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions


/-!
# Angular factorization for Kaufman energy bound

Factorizes `max(|inner θ (x-y)|, δ)^(-γ)` into a radial part `‖x-y‖^(-γ)`
and an angular part `max(|inner θ v|, δ)^(-γ)`, where `v = (x-y)/‖x-y‖`.

The factorization holds when `‖x-y‖ ≤ 1`, which is the standard regime for
Frostman sets of diameter at most 1.
-/

namespace Kakeya.Assouad

/-- Angular factorization inequality for distinct points.

Given unit vector θ, distinct points x, y with `‖x-y‖ ≤ 1`, and
`v = (x-y)/‖x-y‖`, we have:
`max(|inner θ (x-y)|, δ)^(-γ) ≤ ‖x-y‖^(-γ) * max(|inner θ v|, δ)^(-γ)`

The key step is `max(d*a, δ) ≥ d * max(a, δ)` when `0 < d ≤ 1`, which
reverses under the negative exponent `-γ`.
-/
lemma angular_factorization {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ)
    {θ x y : Point2} (hθ : ‖θ‖ = 1) (hne : x ≠ y) (hdist : ‖x - y‖ ≤ 1) :
    let v := ‖x - y‖⁻¹ • (x - y)
    (max (|inner ℝ θ (x - y)|) δ)^(-γ) ≤
    ‖x - y‖^(-γ) * (max (|inner ℝ θ v|) δ)^(-γ) := by
  set d : ℝ := ‖x - y‖ with hd_def
  have hd_pos : 0 < d := by
    rw [hd_def]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hd_le_one : d ≤ 1 := hdist
  set v : Point2 := d⁻¹ • (x - y) with hv_def
  have h_inner : inner ℝ θ (x - y) = d * inner ℝ θ v := by
    have h : inner ℝ θ v = (1 / d) * inner ℝ θ (x - y) := by
      rw [hv_def, inner_smul_right] <;> ring
    calc inner ℝ θ (x - y)
      = d * ((1 / d) * inner ℝ θ (x - y)) := by field_simp [hd_pos.ne'] <;> ring
    _ = d * inner ℝ θ v := by rw [h]
  have h_abs : |inner ℝ θ (x - y)| = d * |inner ℝ θ v| := by
    rw [h_inner]
    rw [abs_mul]
    <;> rw [abs_of_pos hd_pos]
    <;> ring
  set a : ℝ := |inner ℝ θ v| with ha_def
  have h_main : max (d * a) δ ≥ d * max a δ := by
    by_cases h : a ≥ δ
    · -- a ≥ δ
      have h1 : max a δ = a := by
        rw [max_eq_left] <;> linarith
      rw [h1]
      exact le_max_left (d * a) δ
    · -- a < δ
      have h2 : a < δ := by linarith
      have h3 : max a δ = δ := by
        rw [max_eq_right] <;> linarith
      rw [h3]
      have h4 : d * δ ≤ δ := by
        have h5 : d ≤ 1 := hd_le_one
        have h6 : 0 ≤ δ := by linarith
        nlinarith
      have h7 : d * δ ≤ max (d * a) δ := h4.trans (le_max_right (d * a) δ)
      exact h7
  have h_neg : -γ < 0 := by linarith
  have h_pos1 : 0 ≤ max (d * a) δ := by positivity
  have h_pos2 : 0 ≤ d * max a δ := by positivity
  have h_rpow : (max (d * a) δ)^(-γ) ≤ (d * max a δ)^(-γ) := by
    have hx_pos : 0 < d * max a δ := by positivity
    have hy_pos : 0 < max (d * a) δ := by positivity
    have h_le : d * max a δ ≤ max (d * a) δ := h_main
    have h1 : (d * max a δ)^γ ≤ (max (d * a) δ)^γ := Real.rpow_le_rpow (by positivity) h_le (by linarith)
    have h2 : (max (d * a) δ)^(-γ) = 1 / (max (d * a) δ)^γ := by
      rw [Real.rpow_neg (by positivity)] <;> field_simp
    have h3 : (d * max a δ)^(-γ) = 1 / (d * max a δ)^γ := by
      rw [Real.rpow_neg (by positivity)] <;> field_simp
    rw [h2, h3]
    exact one_div_le_one_div_of_le (by positivity) h1
  have h_mul_rpow : (d * max a δ)^(-γ) = d^(-γ) * (max a δ)^(-γ) := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    <;> ring
  rw [h_abs]
  rw [h_mul_rpow] at h_rpow
  exact h_rpow

/-- Diagonal case: when x = y, the angular term simplifies to `δ^(-γ)`. -/
lemma angular_factorization_diagonal {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ)
    {θ x : Point2} :
    (max (|inner ℝ θ (x - x)|) δ)^(-γ) = δ^(-γ) := by
  have h1 : x - x = 0 := by simp
  have h2 : inner ℝ θ (x - x) = 0 := by
    rw [h1] <;> simp
  have h3 : |inner ℝ θ (x - x)| = 0 := by
    rw [h2] <;> simp
  rw [h3]
  have h4 : max (0 : ℝ) δ = δ := by
    rw [max_eq_right] <;> linarith
  rw [h4]

end Kakeya.Assouad
