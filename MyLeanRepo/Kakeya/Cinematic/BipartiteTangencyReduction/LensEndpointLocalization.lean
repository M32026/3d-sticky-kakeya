import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.ConvexTwoZeros
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.LensNonOverlap
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.MinimizerBounds

/-!
# Localization of graph-lens endpoints

The two intersections produced from a common tangent rectangle need not lie
over the rectangle's fine parameter interval.  This module localizes them in
a fixed enlargement.  The hypotheses separate the geometric inputs used in
the PYZ application: a value bound on the rectangle core, upper and lower
curvature bounds, sign change at controlled outer endpoints, and the exact
core length `sqrt (delta / t)`.
-/

noncomputable section

namespace Kakeya.Cinematic

open Set

/--
The exact endpoint-localization factor is bounded uniformly once the two
curve groups are separated by at least `2 * t`.
-/
lemma lens_endpoint_factor_le_uniform
    {K t d V : ℝ}
    (hK : 1 ≤ K)
    (ht : 0 < t)
    (hd : 2 * t ≤ d)
    (hV : 0 ≤ V) :
    24 * K * t * V / d + 12 * K +
        Real.sqrt (12 * K * t * V / d) ≤
      12 * K * (V + 1) + Real.sqrt (6 * K * V) := by
  have hK_pos : 0 < K := by linarith
  have hd_pos : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hratio : t / d ≤ 1 / 2 := by
    rw [div_le_iff₀ hd_pos]
    linarith
  have hlinear :
      24 * K * t * V / d ≤ 12 * K * V := by
    have hnonneg : 0 ≤ 24 * K * V := by positivity
    calc
      24 * K * t * V / d =
          (24 * K * V) * (t / d) := by ring
      _ ≤ (24 * K * V) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hratio hnonneg
      _ = 12 * K * V := by ring
  have hsqrt_arg :
      12 * K * t * V / d ≤ 6 * K * V := by
    have hnonneg : 0 ≤ 12 * K * V := by positivity
    calc
      12 * K * t * V / d =
          (12 * K * V) * (t / d) := by ring
      _ ≤ (12 * K * V) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hratio hnonneg
      _ = 6 * K * V := by ring
  have hsqrt :
      Real.sqrt (12 * K * t * V / d) ≤
        Real.sqrt (6 * K * V) :=
    Real.sqrt_le_sqrt hsqrt_arg
  nlinarith

/--
A value bound and a second-derivative bound on an interval control the first
derivative everywhere on that interval.
-/
lemma core_deriv_bound
    {h h' h'' : ℝ → ℝ} {p q M B : ℝ}
    (hpq : p < q)
    (h_cont : ContinuousOn h (Icc p q))
    (h_deriv : ∀ x ∈ Ioo p q, HasDerivAt h (h' x) x)
    (h'_cont : ContinuousOn h' (Icc p q))
    (h'_deriv : ∀ x ∈ Ioo p q, HasDerivAt h' (h'' x) x)
    (hM : ∀ x ∈ Icc p q, |h x| ≤ M)
    (hB : ∀ x ∈ Icc p q, |h'' x| ≤ B) :
    ∀ x ∈ Icc p q,
      |h' x| ≤ 2 * M / (q - p) + B * (q - p) := by
  have hB_nonneg : 0 ≤ B := by
    have hp_mem : p ∈ Icc p q := ⟨le_rfl, hpq.le⟩
    exact (abs_nonneg (h'' p)).trans (hB p hp_mem)
  have h_diff_on : DifferentiableOn ℝ h (Ioo p q) := by
    intro x hx
    exact (h_deriv x hx).differentiableAt.differentiableWithinAt
  obtain ⟨ξ, hξ, hξ_slope⟩ :=
    exists_deriv_eq_slope h hpq h_cont h_diff_on
  have hξ_deriv : deriv h ξ = h' ξ := (h_deriv ξ hξ).deriv
  have hξ_mem : ξ ∈ Icc p q := ⟨hξ.1.le, hξ.2.le⟩
  have hlength_pos : 0 < q - p := sub_pos.mpr hpq
  have hξ_bound : |h' ξ| ≤ 2 * M / (q - p) := by
    rw [← hξ_deriv, hξ_slope, abs_div, abs_of_pos hlength_pos]
    have hsub : |h q - h p| ≤ 2 * M := by
      calc
        |h q - h p| ≤ |h q| + |h p| := abs_sub _ _
        _ ≤ M + M := by
          gcongr
          · exact hM q ⟨hpq.le, le_rfl⟩
          · exact hM p ⟨le_rfl, hpq.le⟩
        _ = 2 * M := by ring
    exact div_le_div_of_nonneg_right hsub hlength_pos.le
  have h_lipschitz_forward :
      ∀ x ∈ Icc p q, ∀ y ∈ Icc p q, x < y →
        |h' x - h' y| ≤ B * |x - y| := by
    intro x hx y hy hlt
    have hcont : ContinuousOn h' (Icc x y) :=
      h'_cont.mono (Icc_subset_Icc hx.1 hy.2)
    have hdiff : DifferentiableOn ℝ h' (Ioo x y) := by
      intro z hz
      have hz' : z ∈ Ioo p q := ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩
      exact (h'_deriv z hz').differentiableAt.differentiableWithinAt
    obtain ⟨z, hz, hz_slope⟩ :=
      exists_deriv_eq_slope h' hlt hcont hdiff
    have hz_mem : z ∈ Icc p q :=
      ⟨hx.1.trans (hz.1.le), hz.2.le.trans hy.2⟩
    have hz_deriv : deriv h' z = h'' z :=
      (h'_deriv z ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩).deriv
    have hlen : 0 < y - x := sub_pos.mpr hlt
    have heq : h' y - h' x = h'' z * (y - x) := by
      rw [← hz_deriv, hz_slope]
      field_simp [hlen.ne']
    rw [show |x - y| = y - x by rw [abs_of_neg (sub_neg.mpr hlt)]; ring]
    calc
      |h' x - h' y| = |h'' z| * (y - x) := by
        rw [abs_sub_comm, heq, abs_mul, abs_of_pos hlen]
      _ ≤ B * (y - x) :=
        mul_le_mul_of_nonneg_right (hB z hz_mem) hlen.le
  have h_lipschitz :
      ∀ x ∈ Icc p q, ∀ y ∈ Icc p q,
        |h' x - h' y| ≤ B * |x - y| := by
    intro x hx y hy
    rcases lt_trichotomy x y with hlt | rfl | hgt
    · exact h_lipschitz_forward x hx y hy hlt
    · simp
    · simpa [abs_sub_comm] using h_lipschitz_forward y hy x hx hgt
  intro x hx
  have hdist : |x - ξ| ≤ q - p := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hξ_mem.1, hξ_mem.2]
  have hvariation : |h' x - h' ξ| ≤ B * (q - p) := by
    calc
      |h' x - h' ξ| ≤ B * |x - ξ| := h_lipschitz x hx ξ hξ_mem
      _ ≤ B * (q - p) := mul_le_mul_of_nonneg_left hdist hB_nonneg
  have htriangle : |h' x| ≤ |h' ξ| + |h' x - h' ξ| := by
    calc
      |h' x| = |h' ξ + (h' x - h' ξ)| := by ring_nf
      _ ≤ |h' ξ| + |h' x - h' ξ| := abs_add_le _ _
  linarith

/--
Quantitative localization of a zero of a strongly convex function from one
negative reference value and one derivative bound.
-/
lemma convex_zero_distance
    {h h' h'' : ℝ → ℝ} {a b c x₀ y M S : ℝ}
    (hab : a < b) (hc : 0 < c)
    (h_cont : ContinuousOn h (Icc a b))
    (h'_cont : ContinuousOn h' (Icc a b))
    (h_deriv : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x)
    (h'_deriv : ∀ x ∈ Ioo a b, HasDerivAt h' (h'' x) x)
    (h''_ge : ∀ x ∈ Ioo a b, c ≤ h'' x)
    (hx₀ : x₀ ∈ Ioo a b) (hy : y ∈ Icc a b)
    (hx₀_neg : h x₀ < 0) (hy_zero : h y = 0)
    (hdepth : -h x₀ ≤ M) (hslope : |h' x₀| ≤ S) :
    |y - x₀| ≤ 2 * S / c + Real.sqrt (2 * M / c) := by
  have hM : 0 ≤ M := by linarith
  have hS : 0 ≤ S := (abs_nonneg (h' x₀)).trans hslope
  have hlower :=
    convex_value_lower_bound hab hc h_cont h'_cont h_deriv h'_deriv
      h''_ge hx₀ hy
  have hlinear :
      -S * |y - x₀| ≤ h' x₀ * (y - x₀) := by
    have habs :
        |h' x₀ * (y - x₀)| ≤ S * |y - x₀| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hslope (abs_nonneg _)
    simpa only [neg_mul] using neg_le_of_abs_le habs
  have hquadratic :
      c / 2 * |y - x₀| ^ 2 ≤ M + S * |y - x₀| := by
    rw [sq_abs]
    rw [hy_zero] at hlower
    nlinarith
  let q := Real.sqrt (2 * M / c)
  have hq_nonneg : 0 ≤ q := Real.sqrt_nonneg _
  have hq_sq : q ^ 2 = 2 * M / c := by
    dsimp only [q]
    rw [Real.sq_sqrt]
    positivity
  by_contra hbound
  have hstrict :
      2 * S / c + q < |y - x₀| := lt_of_not_ge hbound
  have hdist_nonneg : 0 ≤ |y - x₀| := abs_nonneg _
  have hcq : c * q ^ 2 = 2 * M := by
    rw [hq_sq]
    field_simp [hc.ne']
  have hscaled : 2 * S + c * q < c * |y - x₀| := by
    calc
      2 * S + c * q = c * (2 * S / c + q) := by
        field_simp [hc.ne']
      _ < c * |y - x₀| := mul_lt_mul_of_pos_left hstrict hc
  have hq_lt_distance : q < |y - x₀| := by
    have hdiv_nonneg : 0 ≤ 2 * S / c := div_nonneg (by positivity) hc.le
    linarith
  have hsecond_factor :
      0 < c * (|y - x₀| + q) - 2 * S := by
    have hcq_nonneg : 0 ≤ c * q := mul_nonneg hc.le hq_nonneg
    linarith
  have hproduct :
      0 <
        (|y - x₀| - q) *
          (c * (|y - x₀| + q) - 2 * S) :=
    mul_pos (sub_pos.mpr hq_lt_distance) hsecond_factor
  have htoo_large :
      M + S * |y - x₀| <
        c / 2 * |y - x₀| ^ 2 := by
    nlinarith [hproduct]
  exact (not_lt_of_ge hquadratic) htoo_large

/--
Strong convexity and the common-tangency scale bounds localize both transverse
zeros to a fixed enlargement of the rectangle core.

The outer endpoints `a,b` are only required to surround the core and carry
positive values.  They are not assumed to lie in the fine interval `[p,q]`.
-/
lemma convex_two_zeros_localized_to_rectangle_core
    {h : ℝ → ℝ} {a b p q delta t curvature valueConstant secondConstant : ℝ}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hcurvature : 0 < curvature)
    (hvalueConstant : 0 ≤ valueConstant)
    (hsecondConstant : 0 ≤ secondConstant)
    (hap : a < p) (hpq : p < q) (hqb : q < b)
    (hcore_length : q - p = Real.sqrt (delta / t))
    (h_diff1 : Differentiable ℝ h)
    (h_diff2 : Differentiable ℝ (deriv h))
    (h''_lower : ∀ x ∈ Icc a b,
      curvature * t ≤ deriv (deriv h) x)
    (h''_upper : ∀ x ∈ Icc p q,
      |deriv (deriv h) x| ≤ secondConstant * t)
    (hcore_bound : ∀ x ∈ Icc p q,
      |h x| ≤ valueConstant * delta)
    (hcore_negative : ∀ x ∈ Icc p q, h x < 0)
    (ha_positive : 0 < h a) (hb_positive : 0 < h b) :
    let C :=
      2 * (2 * valueConstant + secondConstant) / curvature +
        Real.sqrt (2 * valueConstant / curvature)
    ∃ z₁ z₂ : ℝ,
      a < z₁ ∧ z₁ < z₂ ∧ z₂ < b ∧
      h z₁ = 0 ∧ h z₂ = 0 ∧
      deriv h z₁ < 0 ∧ 0 < deriv h z₂ ∧
      (∀ x, z₁ < x → x < z₂ → h x < 0) ∧
      z₁ ∈ Icc (p - C * Real.sqrt (delta / t))
        (q + C * Real.sqrt (delta / t)) ∧
      z₂ ∈ Icc (p - C * Real.sqrt (delta / t))
        (q + C * Real.sqrt (delta / t)) := by
  dsimp only
  let x₀ := (p + q) / 2
  have hratio : 0 < delta / t := div_pos hdelta ht
  let L := Real.sqrt (delta / t)
  have hL : 0 < L := Real.sqrt_pos.mpr hratio
  have hlength : q - p = L := hcore_length
  have hx₀_core : x₀ ∈ Icc p q := by
    dsimp only [x₀]
    constructor <;> linarith
  have hx₀_outer : x₀ ∈ Ioo a b := by
    exact ⟨hap.trans_le hx₀_core.1, hx₀_core.2.trans_lt hqb⟩
  have hx₀_negative : h x₀ < 0 := hcore_negative x₀ hx₀_core
  have houter : a < b := hap.trans (hpq.trans hqb)
  have hsecond_positive :
      ∀ x ∈ Icc a b, 0 < deriv (deriv h) x := by
    intro x hx
    exact (mul_pos hcurvature ht).trans_le (h''_lower x hx)
  obtain ⟨z₁, z₂, haz₁, hz₁x₀, hx₀z₂, hz₂b, hz₁_zero, hz₂_zero,
      hbetween, hz₁_deriv, hz₂_deriv⟩ :=
    convex_two_zeros houter hx₀_outer.1 hx₀_outer.2 h_diff1 h_diff2
      hsecond_positive ha_positive hb_positive hx₀_negative
  have hcore_deriv :
      |deriv h x₀| ≤
        2 * (valueConstant * delta) / (q - p) +
          (secondConstant * t) * (q - p) := by
    exact core_deriv_bound hpq h_diff1.continuous.continuousOn
      (fun x _ => (h_diff1 x).hasDerivAt)
      h_diff2.continuous.continuousOn
      (fun x _ => (h_diff2 x).hasDerivAt)
      hcore_bound h''_upper x₀ hx₀_core
  have hL_sq : L ^ 2 = delta / t := by
    dsimp only [L]
    exact Real.sq_sqrt hratio.le
  have hdelta_eq : delta = t * L ^ 2 := by
    calc
      delta = t * (delta / t) := by field_simp [ht.ne']
      _ = t * L ^ 2 := by rw [hL_sq]
  let slopeConstant := 2 * valueConstant + secondConstant
  have hslope :
      |deriv h x₀| ≤ slopeConstant * t * L := by
    calc
      |deriv h x₀| ≤
          2 * (valueConstant * delta) / (q - p) +
            (secondConstant * t) * (q - p) := hcore_deriv
      _ = slopeConstant * t * L := by
        rw [hlength, hdelta_eq]
        dsimp only [slopeConstant]
        field_simp [hL.ne'] <;> ring
  have hdepth : -h x₀ ≤ valueConstant * delta := by
    have habs := hcore_bound x₀ hx₀_core
    linarith [(abs_le.mp habs).1]
  have hroot_bound (z : ℝ) (hz : z ∈ Icc a b) (hzero : h z = 0) :
      |z - x₀| ≤
        2 * (slopeConstant * t * L) / (curvature * t) +
          Real.sqrt
            (2 * (valueConstant * delta) / (curvature * t)) := by
    exact convex_zero_distance houter (mul_pos hcurvature ht)
      h_diff1.continuous.continuousOn h_diff2.continuous.continuousOn
      (fun x _ => (h_diff1 x).hasDerivAt)
      (fun x _ => (h_diff2 x).hasDerivAt)
      (fun x hx => h''_lower x ⟨hx.1.le, hx.2.le⟩)
      hx₀_outer hz hx₀_negative hzero
      hdepth hslope
  let C :=
    2 * slopeConstant / curvature +
      Real.sqrt (2 * valueConstant / curvature)
  have hraw_eq :
      2 * (slopeConstant * t * L) / (curvature * t) +
          Real.sqrt
            (2 * (valueConstant * delta) / (curvature * t)) =
        C * L := by
    have hratio_nonneg : 0 ≤ 2 * valueConstant / curvature := by positivity
    have hsqrt :
        Real.sqrt
            (2 * (valueConstant * delta) / (curvature * t)) =
          Real.sqrt (2 * valueConstant / curvature) * L := by
      have hinside :
          2 * (valueConstant * delta) / (curvature * t) =
            (2 * valueConstant / curvature) * L ^ 2 := by
        rw [hdelta_eq]
        field_simp [ht.ne', hcurvature.ne'] <;> ring
      rw [hinside, Real.sqrt_mul hratio_nonneg, Real.sqrt_sq_eq_abs,
        abs_of_pos hL]
    rw [hsqrt]
    dsimp only [C]
    field_simp [ht.ne', hcurvature.ne'] <;> ring
  have hz₁_distance : |z₁ - x₀| ≤ C * L := by
    rw [← hraw_eq]
    exact hroot_bound z₁
      ⟨haz₁.le, (hz₁x₀.trans (hx₀z₂.trans hz₂b)).le⟩
      hz₁_zero
  have hz₂_distance : |z₂ - x₀| ≤ C * L := by
    rw [← hraw_eq]
    exact hroot_bound z₂
      ⟨(haz₁.trans (hz₁x₀.trans hx₀z₂)).le, hz₂b.le⟩
      hz₂_zero
  have hC_nonneg : 0 ≤ C := by
    dsimp only [C, slopeConstant]
    positivity
  have hCL_nonneg : 0 ≤ C * L := mul_nonneg hC_nonneg hL.le
  have hz₁_enlarged :
      z₁ ∈ Icc (p - C * L) (q + C * L) := by
    have hz₁_abs := abs_le.mp hz₁_distance
    constructor <;> dsimp only [x₀] at hz₁_abs ⊢ <;> linarith
  have hz₂_enlarged :
      z₂ ∈ Icc (p - C * L) (q + C * L) := by
    have hz₂_abs := abs_le.mp hz₂_distance
    constructor <;> dsimp only [x₀] at hz₂_abs ⊢ <;> linarith
  change ∃ z₁ z₂ : ℝ,
    a < z₁ ∧ z₁ < z₂ ∧ z₂ < b ∧
    h z₁ = 0 ∧ h z₂ = 0 ∧
    deriv h z₁ < 0 ∧ 0 < deriv h z₂ ∧
    (∀ x, z₁ < x → x < z₂ → h x < 0) ∧
    z₁ ∈ Icc
      (p - (2 * (2 * valueConstant + secondConstant) / curvature +
        Real.sqrt (2 * valueConstant / curvature)) *
          Real.sqrt (delta / t))
      (q + (2 * (2 * valueConstant + secondConstant) / curvature +
        Real.sqrt (2 * valueConstant / curvature)) *
          Real.sqrt (delta / t)) ∧
    z₂ ∈ Icc
      (p - (2 * (2 * valueConstant + secondConstant) / curvature +
        Real.sqrt (2 * valueConstant / curvature)) *
          Real.sqrt (delta / t))
      (q + (2 * (2 * valueConstant + secondConstant) / curvature +
        Real.sqrt (2 * valueConstant / curvature)) *
          Real.sqrt (delta / t))
  dsimp only [C, slopeConstant, L] at hz₁_enlarged hz₂_enlarged
  exact ⟨z₁, z₂, haz₁, hz₁x₀.trans hx₀z₂, hz₂b, hz₁_zero, hz₂_zero,
    hz₁_deriv, hz₂_deriv, hbetween, hz₁_enlarged, hz₂_enlarged⟩

/--
The concave counterpart of
`convex_two_zeros_localized_to_rectangle_core`, obtained by applying the
convex result to `-h`.
-/
lemma concave_two_zeros_localized_to_rectangle_core
    {h : ℝ → ℝ} {a b p q delta t curvature valueConstant secondConstant : ℝ}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hcurvature : 0 < curvature)
    (hvalueConstant : 0 ≤ valueConstant)
    (hsecondConstant : 0 ≤ secondConstant)
    (hap : a < p) (hpq : p < q) (hqb : q < b)
    (hcore_length : q - p = Real.sqrt (delta / t))
    (h_diff1 : Differentiable ℝ h)
    (h_diff2 : Differentiable ℝ (deriv h))
    (h''_upper : ∀ x ∈ Icc a b,
      deriv (deriv h) x ≤ -(curvature * t))
    (h''_abs : ∀ x ∈ Icc p q,
      |deriv (deriv h) x| ≤ secondConstant * t)
    (hcore_bound : ∀ x ∈ Icc p q,
      |h x| ≤ valueConstant * delta)
    (hcore_positive : ∀ x ∈ Icc p q, 0 < h x)
    (ha_negative : h a < 0) (hb_negative : h b < 0) :
    let C :=
      2 * (2 * valueConstant + secondConstant) / curvature +
        Real.sqrt (2 * valueConstant / curvature)
    ∃ z₁ z₂ : ℝ,
      a < z₁ ∧ z₁ < z₂ ∧ z₂ < b ∧
      h z₁ = 0 ∧ h z₂ = 0 ∧
      0 < deriv h z₁ ∧ deriv h z₂ < 0 ∧
      (∀ x, z₁ < x → x < z₂ → 0 < h x) ∧
      z₁ ∈ Icc (p - C * Real.sqrt (delta / t))
        (q + C * Real.sqrt (delta / t)) ∧
      z₂ ∈ Icc (p - C * Real.sqrt (delta / t))
        (q + C * Real.sqrt (delta / t)) := by
  let negH : ℝ → ℝ := fun x => -h x
  have hneg_deriv (x : ℝ) : deriv negH x = -deriv h x := by
    exact (h_diff1 x).hasDerivAt.neg.deriv
  have hneg_deriv_fun : deriv negH = fun x => -deriv h x := by
    funext x
    exact hneg_deriv x
  have hneg_diff1 : Differentiable ℝ negH := h_diff1.neg
  have hneg_diff2 : Differentiable ℝ (deriv negH) := by
    rw [hneg_deriv_fun]
    exact h_diff2.neg
  have hneg_second (x : ℝ) :
      deriv (deriv negH) x = -deriv (deriv h) x := by
    rw [hneg_deriv_fun]
    exact (h_diff2 x).hasDerivAt.neg.deriv
  have hneg_lower :
      ∀ x ∈ Icc a b, curvature * t ≤ deriv (deriv negH) x := by
    intro x hx
    rw [hneg_second]
    linarith [h''_upper x hx]
  have hneg_abs :
      ∀ x ∈ Icc p q,
        |deriv (deriv negH) x| ≤ secondConstant * t := by
    intro x hx
    rw [hneg_second, abs_neg]
    exact h''_abs x hx
  have hneg_core_bound :
      ∀ x ∈ Icc p q, |negH x| ≤ valueConstant * delta := by
    intro x hx
    simpa only [negH, abs_neg] using hcore_bound x hx
  have hneg_core_negative : ∀ x ∈ Icc p q, negH x < 0 := by
    intro x hx
    dsimp only [negH]
    linarith [hcore_positive x hx]
  have hneg_a : 0 < negH a := by
    dsimp only [negH]
    linarith
  have hneg_b : 0 < negH b := by
    dsimp only [negH]
    linarith
  obtain ⟨z₁, z₂, haz₁, hz₁z₂, hz₂b, hz₁_zero, hz₂_zero,
      hz₁_deriv, hz₂_deriv, hbetween, hz₁_local, hz₂_local⟩ :=
    convex_two_zeros_localized_to_rectangle_core
      hdelta ht hcurvature hvalueConstant hsecondConstant
      hap hpq hqb hcore_length hneg_diff1 hneg_diff2 hneg_lower hneg_abs
      hneg_core_bound hneg_core_negative hneg_a hneg_b
  have hz₁_zero' : h z₁ = 0 := by
    dsimp only [negH] at hz₁_zero
    linarith
  have hz₂_zero' : h z₂ = 0 := by
    dsimp only [negH] at hz₂_zero
    linarith
  have hz₁_deriv' : 0 < deriv h z₁ := by
    rw [hneg_deriv] at hz₁_deriv
    linarith
  have hz₂_deriv' : deriv h z₂ < 0 := by
    rw [hneg_deriv] at hz₂_deriv
    linarith
  have hbetween' : ∀ x, z₁ < x → x < z₂ → 0 < h x := by
    intro x hx₁ hx₂
    have hneg := hbetween x hx₁ hx₂
    dsimp only [negH] at hneg
    linarith
  exact ⟨z₁, z₂, haz₁, hz₁z₂, hz₂b, hz₁_zero', hz₂_zero',
    hz₁_deriv', hz₂_deriv', hbetween', hz₁_local, hz₂_local⟩

/--
Rectangle-form convex endpoint localization.  This is the direct bridge from
common-tangency estimates on `R.interval` to the enlarged endpoint condition
used by graph-lens non-overlap arguments.
-/
lemma convex_two_zeros_localized_to_rectangle
    {h : ℝ → ℝ} {delta t curvature valueConstant secondConstant : ℝ}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hcurvature : 0 < curvature)
    (hvalueConstant : 0 ≤ valueConstant)
    (hsecondConstant : 0 ≤ secondConstant)
    (R : CurvilinearRectangle delta t) {a b : ℝ}
    (ha : a < R.interval.left) (hb : R.interval.right < b)
    (h_diff1 : Differentiable ℝ h)
    (h_diff2 : Differentiable ℝ (deriv h))
    (h''_lower : ∀ x ∈ Icc a b,
      curvature * t ≤ deriv (deriv h) x)
    (h''_upper : ∀ x ∈ Icc R.interval.left R.interval.right,
      |deriv (deriv h) x| ≤ secondConstant * t)
    (hcore_bound : ∀ x ∈ Icc R.interval.left R.interval.right,
      |h x| ≤ valueConstant * delta)
    (hcore_negative : ∀ x ∈ Icc R.interval.left R.interval.right, h x < 0)
    (ha_positive : 0 < h a) (hb_positive : 0 < h b) :
    let C :=
      2 * (2 * valueConstant + secondConstant) / curvature +
        Real.sqrt (2 * valueConstant / curvature)
    ∃ z₁ z₂ : ℝ,
      a < z₁ ∧ z₁ < z₂ ∧ z₂ < b ∧
      h z₁ = 0 ∧ h z₂ = 0 ∧
      deriv h z₁ < 0 ∧ 0 < deriv h z₂ ∧
      (∀ x, z₁ < x → x < z₂ → h x < 0) ∧
      z₁ ∈ Icc
        (R.interval.left - C * Real.sqrt (delta / t))
        (R.interval.right + C * Real.sqrt (delta / t)) ∧
      z₂ ∈ Icc
        (R.interval.left - C * Real.sqrt (delta / t))
        (R.interval.right + C * Real.sqrt (delta / t)) := by
  have hinterval :
      R.interval.left < R.interval.right := by
    rw [← sub_pos]
    change 0 < R.interval.length
    rw [R.interval_length]
    positivity
  exact convex_two_zeros_localized_to_rectangle_core
    hdelta ht hcurvature hvalueConstant hsecondConstant
    ha hinterval hb R.interval_length h_diff1 h_diff2 h''_lower h''_upper
    hcore_bound hcore_negative ha_positive hb_positive

/-- Rectangle-form concave endpoint localization. -/
lemma concave_two_zeros_localized_to_rectangle
    {h : ℝ → ℝ} {delta t curvature valueConstant secondConstant : ℝ}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hcurvature : 0 < curvature)
    (hvalueConstant : 0 ≤ valueConstant)
    (hsecondConstant : 0 ≤ secondConstant)
    (R : CurvilinearRectangle delta t) {a b : ℝ}
    (ha : a < R.interval.left) (hb : R.interval.right < b)
    (h_diff1 : Differentiable ℝ h)
    (h_diff2 : Differentiable ℝ (deriv h))
    (h''_upper : ∀ x ∈ Icc a b,
      deriv (deriv h) x ≤ -(curvature * t))
    (h''_abs : ∀ x ∈ Icc R.interval.left R.interval.right,
      |deriv (deriv h) x| ≤ secondConstant * t)
    (hcore_bound : ∀ x ∈ Icc R.interval.left R.interval.right,
      |h x| ≤ valueConstant * delta)
    (hcore_positive : ∀ x ∈ Icc R.interval.left R.interval.right, 0 < h x)
    (ha_negative : h a < 0) (hb_negative : h b < 0) :
    let C :=
      2 * (2 * valueConstant + secondConstant) / curvature +
        Real.sqrt (2 * valueConstant / curvature)
    ∃ z₁ z₂ : ℝ,
      a < z₁ ∧ z₁ < z₂ ∧ z₂ < b ∧
      h z₁ = 0 ∧ h z₂ = 0 ∧
      0 < deriv h z₁ ∧ deriv h z₂ < 0 ∧
      (∀ x, z₁ < x → x < z₂ → 0 < h x) ∧
      z₁ ∈ Icc
        (R.interval.left - C * Real.sqrt (delta / t))
        (R.interval.right + C * Real.sqrt (delta / t)) ∧
      z₂ ∈ Icc
        (R.interval.left - C * Real.sqrt (delta / t))
        (R.interval.right + C * Real.sqrt (delta / t)) := by
  have hinterval :
      R.interval.left < R.interval.right := by
    rw [← sub_pos]
    change 0 < R.interval.length
    rw [R.interval_length]
    positivity
  exact concave_two_zeros_localized_to_rectangle_core
    hdelta ht hcurvature hvalueConstant hsecondConstant
    ha hinterval hb R.interval_length h_diff1 h_diff2 h''_upper h''_abs
    hcore_bound hcore_positive ha_negative hb_negative

end Kakeya.Cinematic
