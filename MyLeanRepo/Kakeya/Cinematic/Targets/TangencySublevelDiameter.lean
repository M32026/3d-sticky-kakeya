import MyLeanRepo.Kakeya.Cinematic.Targets.TangencySublevelDiameter.Helpers
import MyLeanRepo.Kakeya.Cinematic.Statements

/-!
# PYZ Lemma 16(2a): tangency sublevel localization

The small-value set of the difference of two cinematic functions is localized
to one interval at the scale dictated by `Δ`, `δ`, and the `C²` distance.
-/

namespace Kakeya.Cinematic

theorem tangency_sublevel_diameter
    (_hPreliminary : PreliminaryDichotomyStatement)
    (_hTwoZeros : TwoZerosStatement) :
    TangencySublevelDiameterStatement := by
  intro K D hK hD
  use 2 * Real.sqrt (12 * K)
  constructor
  · have h1 : 0 < 12 * K := by positivity
    have h2 : 0 < Real.sqrt (12 * K) := Real.sqrt_pos.mpr h1
    positivity
  intro family hfam I hI f hf g hg hfg δ hδ hδ2 x hx y hy
  set t : ℝ := c2Distance f g with ht_def
  set Δ : ℝ := tangencyParameterOn I f g with hΔ_def
  have ht_pos : 0 < t := by
    have h : 0 < dist f g := dist_pos.mpr hfg
    simpa [ht_def, c2Distance_eq_dist] using h
  have hK_pos : 0 < K := by linarith
  have hcurv : ∀ (z : UnitPoint),
      K⁻¹ * t ≤ |f z - g z| + |f.firstDeriv z - g.firstDeriv z| +
        |f.secondDeriv z - g.secondDeriv z| := by
    intro z; exact hfam.2.2 hf hg z
  have hx_carrier : x ∈ I.carrier :=
    I.centeredCarrier_subset_carrier (by norm_num) (by norm_num) hx.1
  have hy_carrier : y ∈ I.carrier :=
    I.centeredCarrier_subset_carrier (by norm_num) (by norm_num) hy.1
  have hx_val : |f x - g x| ≤ δ := hx.2
  have hy_val : |f y - g y| ≤ δ := hy.2
  have hI_len : I.length ≤ (6 * K)⁻¹ := hI
  have h_diam : ∀ (z w : UnitPoint), z ∈ I.carrier → w ∈ I.carrier →
      |(z : ℝ) - (w : ℝ)| ≤ I.length := by
    intro z w hz hw
    have hz1 : I.left ≤ (z : ℝ) := hz.1
    have hz2 : (z : ℝ) ≤ I.right := hz.2
    have hw1 : I.left ≤ (w : ℝ) := hw.1
    have hw2 : (w : ℝ) ≤ I.right := hw.2
    have hlen : I.length = I.right - I.left := by simp [ParameterInterval.length]
    have h5 : (z : ℝ) - (w : ℝ) ≤ I.length := by rw [hlen]; linarith
    have h7 : -(I.length) ≤ (z : ℝ) - (w : ℝ) := by rw [hlen]; linarith
    exact abs_le.mpr ⟨h7, h5⟩
  have h_triangle1 : ∀ (a b : ℝ), |a| ≤ |a - b| + |b| := by
    intro a b
    have h : |(a - b) + b| ≤ |a - b| + |b| := norm_add_le (a - b) b
    have h2 : (a - b) + b = a := by ring
    rw [h2] at h; exact h
  have h_triangle2 : ∀ (a b c : ℝ), |a - b| ≤ |a - c| + |b - c| := by
    intro a b c
    have h1 : a - b = (a - c) + (c - b) := by abel
    rw [h1]
    have h2 : |(a - c) + (c - b)| ≤ |a - c| + |c - b| := norm_add_le (a - c) (c - b)
    have h3 : |c - b| = |b - c| := by
      have h4 : c - b = -(b - c) := by abel
      rw [h4, abs_neg]
    rw [h3] at h2; exact h2
  have h_abs_prod : ∀ (a b : ℝ), -|a| * |b| ≤ a * b := by
    intro a b
    have h2 : |a * b| = |a| * |b| := abs_mul a b
    by_cases h : 0 ≤ a * b
    · have h3 : |a * b| = a * b := abs_of_nonneg h
      rw [h3] at h2; linarith
    · have h3 : |a * b| = -(a * b) := abs_of_neg (by linarith)
      rw [h3] at h2; linarith
  by_cases h_case1 : Δ > t / (12 * K)
  · -- Case 1: Δ > t / (12K), trivial diameter bound
    have h1 : |(x : ℝ) - (y : ℝ)| ≤ I.length := h_diam x y hx_carrier hy_carrier
    have h2 : I.length ≤ 1 / (6 * K) := by simpa [ParameterInterval.IsShort] using hI_len
    have h3 : (Δ + δ) / t > 1 / (12 * K) := by
      have h4 : Δ > t / (12 * K) := h_case1
      have h5 : Δ + δ > t / (12 * K) := by linarith
      have h6 : (Δ + δ) / t > (t / (12 * K)) / t := by gcongr
      have h7 : (t / (12 * K)) / t = 1 / (12 * K) := by
        field_simp [ht_pos.ne'] <;> ring
      rw [h7] at h6; exact h6
    have h8 : 0 < 1 / (12 * K) := by positivity
    have h9 : Real.sqrt ((Δ + δ) / t) > Real.sqrt (1 / (12 * K)) :=
      Real.sqrt_lt_sqrt (by positivity) h3
    have h10 : Real.sqrt (1 / (12 * K)) = 1 / Real.sqrt (12 * K) := by
      rw [Real.sqrt_div (by positivity)]
      have h11 : Real.sqrt 1 = (1 : ℝ) := by simp
      rw [h11]
    rw [h10] at h9
    have hsqrt_pos : 0 < Real.sqrt (12 * K) := Real.sqrt_pos.mpr (by positivity)
    have h11 : (2 * Real.sqrt (12 * K)) * Real.sqrt ((Δ + δ) / t) > 2 := by
      calc (2 * Real.sqrt (12 * K)) * Real.sqrt ((Δ + δ) / t)
        > (2 * Real.sqrt (12 * K)) * (1 / Real.sqrt (12 * K)) := by gcongr
      _ = 2 := by field_simp [hsqrt_pos.ne'] <;> ring
    have h12 : |(x : ℝ) - (y : ℝ)| ≤ 1 / (6 * K) := by linarith
    have h13 : 1 / (6 * K) ≤ 2 := by
      have h14 : 1 ≤ 6 * K := by linarith
      have h15 : 1 / (6 * K) ≤ 1 := by apply (div_le_one (by positivity)).mpr; linarith
      linarith
    have h14 : |(x : ℝ) - (y : ℝ)| ≤ 2 := by linarith
    have h15 : 2 < (2 * Real.sqrt (12 * K)) * Real.sqrt ((Δ + δ) / t) := h11
    exact le_trans h14 (le_of_lt h15)
  · -- Case 2: Δ ≤ t / (12K)
    have hΔ_le : Δ ≤ t / (12 * K) := by linarith
    rcases tangency_parameter_attained I f g with ⟨xΔ, hxΔ_centered, hxΔ_eq⟩
    have hxΔ_carrier : xΔ ∈ I.carrier :=
      I.centeredCarrier_subset_carrier (by norm_num) (by norm_num) hxΔ_centered
    have hxΔ_h : |f xΔ - g xΔ| ≤ Δ := by
      have h : |f xΔ - g xΔ| + |f.firstDeriv xΔ - g.firstDeriv xΔ| = Δ := hxΔ_eq
      have hnonneg : 0 ≤ |f.firstDeriv xΔ - g.firstDeriv xΔ| := by positivity
      linarith
    have hxΔ_h' : |f.firstDeriv xΔ - g.firstDeriv xΔ| ≤ Δ := by
      have h : |f xΔ - g xΔ| + |f.firstDeriv xΔ - g.firstDeriv xΔ| = Δ := hxΔ_eq
      have hnonneg : 0 ≤ |f xΔ - g xΔ| := by positivity
      linarith
    have h_lip1 : ∀ (z : UnitPoint), z ∈ I.carrier →
        |(f z - g z) - (f xΔ - g xΔ)| ≤ t * |(z : ℝ) - (xΔ : ℝ)| :=
      fun z _ => lipschitz_value f g z xΔ
    have h_lip2 : ∀ (z : UnitPoint), z ∈ I.carrier →
        |(f.firstDeriv z - g.firstDeriv z) - (f.firstDeriv xΔ - g.firstDeriv xΔ)| ≤
          t * |(z : ℝ) - (xΔ : ℝ)| :=
      fun z _ => lipschitz_deriv f g z xΔ
    have h_dist : ∀ (z : UnitPoint), z ∈ I.carrier →
        |(z : ℝ) - (xΔ : ℝ)| ≤ 1 / (6 * K) := by
      intro z hz
      have h1 : |(z : ℝ) - (xΔ : ℝ)| ≤ I.length := h_diam z xΔ hz hxΔ_carrier
      have h2 : I.length ≤ 1 / (6 * K) := by simpa [ParameterInterval.IsShort] using hI_len
      linarith
    have h_h_small : ∀ (z : UnitPoint), z ∈ I.carrier → |f z - g z| < t / (3 * K) := by
      intro z hz
      set a : ℝ := f z - g z with ha_def
      set b : ℝ := f xΔ - g xΔ with hb_def
      have h1 : |a| ≤ |a - b| + |b| := h_triangle1 a b
      have h2 : |a - b| ≤ t * |(z : ℝ) - (xΔ : ℝ)| := h_lip1 z hz
      have h3 : |b| ≤ Δ := hxΔ_h
      have h4 : |(z : ℝ) - (xΔ : ℝ)| ≤ 1 / (6 * K) := h_dist z hz
      have h51 : |a - b| + |b| ≤ t * |(z : ℝ) - (xΔ : ℝ)| + Δ := by gcongr
      have h52 : t * |(z : ℝ) - (xΔ : ℝ)| + Δ ≤ t * (1 / (6 * K)) + Δ := by gcongr
      have h5 : |a| ≤ Δ + t * (1 / (6 * K)) := by linarith
      have h8 : t * (1 / (6 * K)) = t / (6 * K) := by field_simp [hK_pos.ne'] <;> ring
      have h9 : |a| ≤ Δ + t / (6 * K) := by rw [h8] at h5; exact h5
      have h10 : Δ + t / (6 * K) < t / (3 * K) := by
        have h11 : Δ ≤ t / (12 * K) := hΔ_le
        calc Δ + t / (6 * K) ≤ t / (12 * K) + t / (6 * K) := by gcongr
          _ = t / (4 * K) := by field_simp [hK_pos.ne'] <;> ring
          _ < t / (3 * K) := by
            have h12 : 0 < t := ht_pos
            have h13 : 0 < K := hK_pos
            gcongr <;> norm_num
      exact lt_of_le_of_lt h9 h10
    have h_h'_small : ∀ (z : UnitPoint), z ∈ I.carrier →
        |f.firstDeriv z - g.firstDeriv z| < t / (3 * K) := by
      intro z hz
      set a : ℝ := f.firstDeriv z - g.firstDeriv z with ha_def
      set b : ℝ := f.firstDeriv xΔ - g.firstDeriv xΔ with hb_def
      have h1 : |a| ≤ |a - b| + |b| := h_triangle1 a b
      have h2 : |a - b| ≤ t * |(z : ℝ) - (xΔ : ℝ)| := h_lip2 z hz
      have h3 : |b| ≤ Δ := hxΔ_h'
      have h4 : |(z : ℝ) - (xΔ : ℝ)| ≤ 1 / (6 * K) := h_dist z hz
      have h51 : |a - b| + |b| ≤ t * |(z : ℝ) - (xΔ : ℝ)| + Δ := by gcongr
      have h52 : t * |(z : ℝ) - (xΔ : ℝ)| + Δ ≤ t * (1 / (6 * K)) + Δ := by gcongr
      have h5 : |a| ≤ Δ + t * (1 / (6 * K)) := by linarith
      have h8 : t * (1 / (6 * K)) = t / (6 * K) := by field_simp [hK_pos.ne'] <;> ring
      have h9 : |a| ≤ Δ + t / (6 * K) := by rw [h8] at h5; exact h5
      have h10 : Δ + t / (6 * K) < t / (3 * K) := by
        have h11 : Δ ≤ t / (12 * K) := hΔ_le
        calc Δ + t / (6 * K) ≤ t / (12 * K) + t / (6 * K) := by gcongr
          _ = t / (4 * K) := by field_simp [hK_pos.ne'] <;> ring
          _ < t / (3 * K) := by
            have h12 : 0 < t := ht_pos
            have h13 : 0 < K := hK_pos
            gcongr <;> norm_num
      exact lt_of_le_of_lt h9 h10
    have h_h''_large : ∀ (z : UnitPoint), z ∈ I.carrier →
        |f.secondDeriv z - g.secondDeriv z| > t / (3 * K) := by
      intro z hz
      have h1 : K⁻¹ * t ≤ |f z - g z| + |f.firstDeriv z - g.firstDeriv z| +
            |f.secondDeriv z - g.secondDeriv z| := hcurv z
      have h2 : |f z - g z| < t / (3 * K) := h_h_small z hz
      have h3 : |f.firstDeriv z - g.firstDeriv z| < t / (3 * K) := h_h'_small z hz
      have h4 : K⁻¹ * t = t / K := by field_simp [hK_pos.ne'] <;> ring
      rw [h4] at h1
      have h5 : |f z - g z| + |f.firstDeriv z - g.firstDeriv z| < 2 * (t / (3 * K)) := by linarith
      have h6 : |f.secondDeriv z - g.secondDeriv z| ≥ t / K - (|f z - g z| + |f.firstDeriv z - g.firstDeriv z|) := by linarith
      have h7 : t / K - (|f z - g z| + |f.firstDeriv z - g.firstDeriv z|) > t / (3 * K) := by
        have h8 : |f z - g z| + |f.firstDeriv z - g.firstDeriv z| < 2 * (t / (3 * K)) := h5
        have h9 : t / K - (|f z - g z| + |f.firstDeriv z - g.firstDeriv z|) > t / K - 2 * (t / (3 * K)) := by gcongr
        have h10 : t / K - 2 * (t / (3 * K)) = t / (3 * K) := by
          field_simp [hK_pos.ne'] <;> ring
        rw [h10] at h9
        exact h9
      linarith
    let H : ℝ → ℝ := f.extension - g.extension
    have h_f_c2 : ContDiff ℝ 2 f.extension := f.extension_contDiff
    have h_g_c2 : ContDiff ℝ 2 g.extension := g.extension_contDiff
    have hH_c2 : ContDiff ℝ 2 H := h_f_c2.add h_g_c2.neg
    have hH_diff1 : Differentiable ℝ H := ContDiff.differentiable hH_c2 (by norm_num)
    have hH2_c2 : ContDiff ℝ 1 (deriv H) := hH_c2.deriv'
    have hH_diff2 : Differentiable ℝ (deriv H) := ContDiff.differentiable hH2_c2 (by norm_num)
    have h_f_diff : Differentiable ℝ f.extension := ContDiff.differentiable h_f_c2 (by norm_num)
    have h_g_diff : Differentiable ℝ g.extension := ContDiff.differentiable h_g_c2 (by norm_num)
    have h_f2_c2 : ContDiff ℝ 1 (deriv f.extension) := h_f_c2.deriv'
    have h_g2_c2 : ContDiff ℝ 1 (deriv g.extension) := h_g_c2.deriv'
    have h_df2 : Differentiable ℝ (deriv f.extension) := ContDiff.differentiable h_f2_c2 (by norm_num)
    have h_dg2 : Differentiable ℝ (deriv g.extension) := ContDiff.differentiable h_g2_c2 (by norm_num)
    have hH''_eq : ∀ (z : UnitPoint),
        deriv (deriv H) z = f.secondDeriv z - g.secondDeriv z := by
      intro z
      have h_eq1 : deriv H = deriv f.extension - deriv g.extension := by
        funext w; exact deriv_sub (h_f_diff w) (h_g_diff w)
      have h1 : deriv (deriv H) z = deriv (deriv f.extension - deriv g.extension) z := by
        rw [h_eq1]
      rw [h1]
      have h2 : deriv (deriv f.extension - deriv g.extension) z =
          deriv (deriv f.extension) z - deriv (deriv g.extension) z :=
        deriv_sub (h_df2 z) (h_dg2 z)
      rw [h2]
      have h3 : deriv (deriv f.extension) z = f.secondDeriv z :=
        C2Function.secondDeriv_extension_eq_secondDeriv f z
      have h4 : deriv (deriv g.extension) z = g.secondDeriv z :=
        C2Function.secondDeriv_extension_eq_secondDeriv g z
      rw [h3, h4] <;> abel
    have hH''_never_zero : ∀ (r : ℝ), r ∈ Set.Icc I.left I.right →
        deriv (deriv H) r ≠ 0 := by
      intro r hr
      have hr1 : 0 ≤ r := by have h : 0 ≤ I.left := I.left_mem.1; linarith [hr.1]
      have hr2 : r ≤ 1 := by have h : I.right ≤ 1 := I.right_mem.2; linarith [hr.2]
      let z : UnitPoint := ⟨r, ⟨hr1, hr2⟩⟩
      have hz_carrier : z ∈ I.carrier := ⟨hr.1, hr.2⟩
      have h5 : deriv (deriv H) r = f.secondDeriv z - g.secondDeriv z := hH''_eq z
      rw [h5]
      have h6 : |f.secondDeriv z - g.secondDeriv z| > t / (3 * K) := h_h''_large z hz_carrier
      have h7 : 0 < t / (3 * K) := by positivity
      exact abs_pos.mp (show 0 < |f.secondDeriv z - g.secondDeriv z| from by linarith)
    have hderiv_cont : Continuous (deriv (deriv H)) := hH2_c2.continuous_deriv_one
    have hH_cont : ContinuousOn (deriv (deriv H)) (Set.Icc I.left I.right) :=
      hderiv_cont.continuousOn
    have h_sign : (∀ r ∈ Set.Icc I.left I.right, 0 < deriv (deriv H) r) ∨
        (∀ r ∈ Set.Icc I.left I.right, deriv (deriv H) r < 0) :=
      constant_sign_of_never_zero I.left_le_right hH_cont hH''_never_zero
    have hb : 0 ≤ Δ := by
      have h_nonneg : 0 ≤ |f xΔ - g xΔ| + |f.firstDeriv xΔ - g.firstDeriv xΔ| := by positivity
      linarith [hxΔ_eq]
    have h_bound : ∀ (H' : ℝ → ℝ),
        Differentiable ℝ H' → Differentiable ℝ (deriv H') →
        (∀ r ∈ Set.Icc I.left I.right, t / (3 * K) ≤ deriv (deriv H') r) →
        |H' (xΔ : ℝ)| ≤ Δ → |deriv H' (xΔ : ℝ)| ≤ Δ →
        ∀ (z : UnitPoint), z ∈ I.carrier → |H' z| ≤ δ →
          |(z : ℝ) - (xΔ : ℝ)| ≤ Real.sqrt (12 * K) * Real.sqrt ((Δ + δ) / t) := by
      intro H' hH'_diff1 hH'_diff2 hH''_pos hH'_xΔ hH'_xΔ' z hz hH'_z
      have hxΔ_in : (xΔ : ℝ) ∈ Set.Icc I.left I.right := ⟨hxΔ_carrier.1, hxΔ_carrier.2⟩
      have hz_in : (z : ℝ) ∈ Set.Icc I.left I.right := ⟨hz.1, hz.2⟩
      have h_taylor : H' (z : ℝ) ≥ H' (xΔ : ℝ) +
          deriv H' (xΔ : ℝ) * ((z : ℝ) - (xΔ : ℝ)) +
          (t / (3 * K) / 2) * ((z : ℝ) - (xΔ : ℝ))^2 :=
        taylor_quadratic_lower_bound hH'_diff1 hH'_diff2 I.left_le_right
          hxΔ_in hz_in hH''_pos
      set u : ℝ := |(z : ℝ) - (xΔ : ℝ)| with hu_def
      have h_u2 : ((z : ℝ) - (xΔ : ℝ))^2 = u^2 := by
        rw [hu_def]; rw [sq_abs]
      have h2 : H' (xΔ : ℝ) ≥ -Δ := (abs_le.mp hH'_xΔ).1
      have h3 : deriv H' (xΔ : ℝ) * ((z : ℝ) - (xΔ : ℝ)) ≥ -Δ * u := by
        have h4 : deriv H' (xΔ : ℝ) * ((z : ℝ) - (xΔ : ℝ)) ≥
            -|deriv H' (xΔ : ℝ)| * |(z : ℝ) - (xΔ : ℝ)| := h_abs_prod _ _
        have h5 : |deriv H' (xΔ : ℝ)| * |(z : ℝ) - (xΔ : ℝ)| ≤ Δ * u := by
          have h51 : |deriv H' (xΔ : ℝ)| ≤ Δ := hH'_xΔ'
          have h52 : |deriv H' (xΔ : ℝ)| * |(z : ℝ) - (xΔ : ℝ)| ≤ Δ * |(z : ℝ) - (xΔ : ℝ)| :=
            mul_le_mul_of_nonneg_right h51 (abs_nonneg _)
          have h53 : |(z : ℝ) - (xΔ : ℝ)| = u := by rw [hu_def]
          rw [h53] at h52
          exact h52
        linarith
      have h_taylor2 : H' (z : ℝ) ≥ -Δ - Δ * u + (t / (6 * K)) * u^2 := by
        have h_eq : (t / (3 * K) / 2) = t / (6 * K) := by ring
        rw [h_eq] at h_taylor
        rw [h_u2] at h_taylor
        linarith [h2, h3, h_taylor]
      have h4 : H' (z : ℝ) ≤ δ := by
        have h41 : H' (z : ℝ) ≤ |H' (z : ℝ)| := le_abs_self (H' (z : ℝ))
        have h42 : |H' (z : ℝ)| ≤ δ := hH'_z
        linarith
      have h5 : (t / (6 * K)) * u^2 - Δ * u - (Δ + δ) ≤ 0 := by linarith
      have ha : 0 < t / (6 * K) := by positivity
      have hc : 0 ≤ Δ + δ := by positivity
      have h6 : Δ^2 ≤ (t / (6 * K)) * (Δ + δ) / 2 := by
        have h7 : Δ ≤ t / (12 * K) := hΔ_le
        have h8 : Δ^2 ≤ Δ * (t / (12 * K)) := by nlinarith [hb]
        have h9 : Δ * (t / (12 * K)) = (t / (6 * K)) * Δ / 2 := by
          field_simp [hK_pos.ne'] <;> ring
        have h10 : (t / (6 * K)) * Δ / 2 ≤ (t / (6 * K)) * (Δ + δ) / 2 := by
          gcongr <;> linarith
        linarith
      have h11 : u ≤ Real.sqrt 2 * Real.sqrt ((Δ + δ) / (t / (6 * K))) :=
        quadratic_inequality_bound ha hb hc h6 h5
      have h12 : Real.sqrt 2 * Real.sqrt ((Δ + δ) / (t / (6 * K))) =
          Real.sqrt (12 * K) * Real.sqrt ((Δ + δ) / t) := by
        have h14 : (Δ + δ) / (t / (6 * K)) = (6 * K) * ((Δ + δ) / t) := by
          field_simp [ht_pos.ne', hK_pos.ne'] <;> ring
        rw [h14]
        have h15 : 0 ≤ (6 * K) := by positivity
        have h16 : 0 ≤ (Δ + δ) / t := by positivity
        have h17 : Real.sqrt ((6 * K) * ((Δ + δ) / t)) =
            Real.sqrt (6 * K) * Real.sqrt ((Δ + δ) / t) := by
          rw [Real.sqrt_mul h15]
        rw [h17]
        have h18 : Real.sqrt 2 * Real.sqrt (6 * K) = Real.sqrt (12 * K) := by
          have h19 : Real.sqrt 2 * Real.sqrt (6 * K) = Real.sqrt (2 * (6 * K)) := by
            rw [←Real.sqrt_mul (by positivity)] <;> ring
          rw [h19]
          have h20 : 2 * (6 * K) = 12 * K := by ring
          rw [h20]
        have h_goal : Real.sqrt 2 * (Real.sqrt (6 * K) * Real.sqrt ((Δ + δ) / t)) =
            Real.sqrt (12 * K) * Real.sqrt ((Δ + δ) / t) := by
          rw [←mul_assoc, h18]
        exact h_goal
      rw [h12] at h11
      exact h11
    rcases h_sign with (h_pos | h_neg)
    · -- Case H'' > 0
      have hH''_pos : ∀ r ∈ Set.Icc I.left I.right, t / (3 * K) ≤ deriv (deriv H) r := by
        intro r hr
        have h1 : 0 < deriv (deriv H) r := h_pos r hr
        have hr1 : 0 ≤ r := by have h : 0 ≤ I.left := I.left_mem.1; linarith [hr.1]
        have hr2 : r ≤ 1 := by have h : I.right ≤ 1 := I.right_mem.2; linarith [hr.2]
        let z : UnitPoint := ⟨r, ⟨hr1, hr2⟩⟩
        have hz_carrier : z ∈ I.carrier := ⟨hr.1, hr.2⟩
        have h3 : deriv (deriv H) r = f.secondDeriv z - g.secondDeriv z := hH''_eq z
        have h4 : |f.secondDeriv z - g.secondDeriv z| > t / (3 * K) := h_h''_large z hz_carrier
        have h5 : 0 < f.secondDeriv z - g.secondDeriv z := by
          rw [←h3]; exact h1
        have h6 : |f.secondDeriv z - g.secondDeriv z| = f.secondDeriv z - g.secondDeriv z :=
          abs_of_pos h5
        have h7 : f.secondDeriv z - g.secondDeriv z > t / (3 * K) := by
          rw [h6] at h4; exact h4
        have h8 : t / (3 * K) ≤ deriv (deriv H) r := by
          rw [h3]; exact le_of_lt h7
        exact h8
      have hH_xΔ : |H (xΔ : ℝ)| ≤ Δ := by
        have h_eq1 : H (xΔ : ℝ) = f.extension (xΔ : ℝ) - g.extension (xΔ : ℝ) := by
          simp [H] <;> rfl
        have h_eq2 : f.extension (xΔ : ℝ) = f xΔ := C2Function.extension_eq_value f xΔ
        have h_eq3 : g.extension (xΔ : ℝ) = g xΔ := C2Function.extension_eq_value g xΔ
        rw [h_eq1, h_eq2, h_eq3] <;> exact hxΔ_h
      have hH'_xΔ : |deriv H (xΔ : ℝ)| ≤ Δ := by
        have h_eq1 : deriv H (xΔ : ℝ) = deriv f.extension (xΔ : ℝ) - deriv g.extension (xΔ : ℝ) := by
          have h_eq : deriv H = deriv f.extension - deriv g.extension := by
            funext w; exact deriv_sub (h_f_diff w) (h_g_diff w)
          rw [h_eq] <;> rfl
        have h_eq2 : deriv f.extension (xΔ : ℝ) = f.firstDeriv xΔ :=
          C2Function.deriv_extension_eq_firstDeriv f xΔ
        have h_eq3 : deriv g.extension (xΔ : ℝ) = g.firstDeriv xΔ :=
          C2Function.deriv_extension_eq_firstDeriv g xΔ
        rw [h_eq1, h_eq2, h_eq3] <;> exact hxΔ_h'
      have hH_x_val : |H x| ≤ δ := by
        have h_eq1 : H x = f.extension x - g.extension x := by simp [H] <;> rfl
        have h_eq2 : f.extension x = f x := C2Function.extension_eq_value f x
        have h_eq3 : g.extension x = g x := C2Function.extension_eq_value g x
        rw [h_eq1, h_eq2, h_eq3] <;> exact hx_val
      have hH_y_val : |H y| ≤ δ := by
        have h_eq1 : H y = f.extension y - g.extension y := by simp [H] <;> rfl
        have h_eq2 : f.extension y = f y := C2Function.extension_eq_value f y
        have h_eq3 : g.extension y = g y := C2Function.extension_eq_value g y
        rw [h_eq1, h_eq2, h_eq3] <;> exact hy_val
      have h_x_bound : |(x : ℝ) - (xΔ : ℝ)| ≤ Real.sqrt (12 * K) * Real.sqrt ((Δ + δ) / t) :=
        h_bound H hH_diff1 hH_diff2 hH''_pos hH_xΔ hH'_xΔ x hx_carrier hH_x_val
      have h_y_bound : |(y : ℝ) - (xΔ : ℝ)| ≤ Real.sqrt (12 * K) * Real.sqrt ((Δ + δ) / t) :=
        h_bound H hH_diff1 hH_diff2 hH''_pos hH_xΔ hH'_xΔ y hy_carrier hH_y_val
      have h_final : |(x : ℝ) - (y : ℝ)| ≤ |(x : ℝ) - (xΔ : ℝ)| + |(y : ℝ) - (xΔ : ℝ)| :=
        h_triangle2 (x : ℝ) (y : ℝ) (xΔ : ℝ)
      calc |(x : ℝ) - (y : ℝ)|
        ≤ |(x : ℝ) - (xΔ : ℝ)| + |(y : ℝ) - (xΔ : ℝ)| := h_final
      _ ≤ 2 * (Real.sqrt (12 * K) * Real.sqrt ((Δ + δ) / t)) := by linarith
      _ = (2 * Real.sqrt (12 * K)) * Real.sqrt ((Δ + δ) / t) := by ring
    · -- Case H'' < 0, apply to -H
      let H' : ℝ → ℝ := -H
      have hH'_diff1 : Differentiable ℝ H' := hH_diff1.neg
      have hH'_diff2 : Differentiable ℝ (deriv H') := by
        have h_eq : deriv H' = -deriv H := by funext r; simp [H'] <;> rfl
        rw [h_eq]; exact hH_diff2.neg
      have hH'_pos : ∀ r ∈ Set.Icc I.left I.right, t / (3 * K) ≤ deriv (deriv H') r := by
        intro r hr
        have h1 : deriv (deriv H') r = -deriv (deriv H) r := by simp [H'] <;> rfl
        rw [h1]
        have h2 : deriv (deriv H) r < 0 := h_neg r hr
        have h3 : -deriv (deriv H) r = |deriv (deriv H) r| := by
          rw [abs_of_neg h2] <;> ring
        rw [h3]
        have hr1 : 0 ≤ r := by have h : 0 ≤ I.left := I.left_mem.1; linarith [hr.1]
        have hr2 : r ≤ 1 := by have h : I.right ≤ 1 := I.right_mem.2; linarith [hr.2]
        let z : UnitPoint := ⟨r, ⟨hr1, hr2⟩⟩
        have hz_carrier : z ∈ I.carrier := ⟨hr.1, hr.2⟩
        have h4 : deriv (deriv H) r = f.secondDeriv z - g.secondDeriv z := hH''_eq z
        rw [h4] at *
        <;> linarith [h_h''_large z hz_carrier]
      have hH'_xΔ : |H' (xΔ : ℝ)| ≤ Δ := by
        have h_eq : H' (xΔ : ℝ) = -H (xΔ : ℝ) := by simp [H'] <;> rfl
        rw [h_eq, abs_neg]
        have h_eq2 : H (xΔ : ℝ) = f.extension (xΔ : ℝ) - g.extension (xΔ : ℝ) := by
          simp [H] <;> rfl
        rw [h_eq2]
        have h_eq3 : f.extension (xΔ : ℝ) = f xΔ := C2Function.extension_eq_value f xΔ
        have h_eq4 : g.extension (xΔ : ℝ) = g xΔ := C2Function.extension_eq_value g xΔ
        rw [h_eq3, h_eq4] <;> exact hxΔ_h
      have hH'_xΔ' : |deriv H' (xΔ : ℝ)| ≤ Δ := by
        have h_eq : deriv H' (xΔ : ℝ) = -deriv H (xΔ : ℝ) := by
          have h_eq2 : deriv H' = -deriv H := by funext r; simp [H'] <;> rfl
          rw [h_eq2] <;> rfl
        rw [h_eq, abs_neg]
        have h_eq2 : deriv H (xΔ : ℝ) = deriv f.extension (xΔ : ℝ) - deriv g.extension (xΔ : ℝ) := by
          have h_eq3 : deriv H = deriv f.extension - deriv g.extension := by
            funext w; exact deriv_sub (h_f_diff w) (h_g_diff w)
          rw [h_eq3] <;> rfl
        rw [h_eq2]
        have h_eq3 : deriv f.extension (xΔ : ℝ) = f.firstDeriv xΔ :=
          C2Function.deriv_extension_eq_firstDeriv f xΔ
        have h_eq4 : deriv g.extension (xΔ : ℝ) = g.firstDeriv xΔ :=
          C2Function.deriv_extension_eq_firstDeriv g xΔ
        rw [h_eq3, h_eq4] <;> exact hxΔ_h'
      have h_x_val' : |H' x| ≤ δ := by
        have h_eq : H' x = -H x := by simp [H'] <;> rfl
        rw [h_eq, abs_neg]
        have h_eq2 : H x = f.extension x - g.extension x := by simp [H] <;> rfl
        rw [h_eq2]
        have h_eq3 : f.extension x = f x := C2Function.extension_eq_value f x
        have h_eq4 : g.extension x = g x := C2Function.extension_eq_value g x
        rw [h_eq3, h_eq4] <;> exact hx_val
      have h_y_val' : |H' y| ≤ δ := by
        have h_eq : H' y = -H y := by simp [H'] <;> rfl
        rw [h_eq, abs_neg]
        have h_eq2 : H y = f.extension y - g.extension y := by simp [H] <;> rfl
        rw [h_eq2]
        have h_eq3 : f.extension y = f y := C2Function.extension_eq_value f y
        have h_eq4 : g.extension y = g y := C2Function.extension_eq_value g y
        rw [h_eq3, h_eq4] <;> exact hy_val
      have h_x_bound : |(x : ℝ) - (xΔ : ℝ)| ≤ Real.sqrt (12 * K) * Real.sqrt ((Δ + δ) / t) :=
        h_bound H' hH'_diff1 hH'_diff2 hH'_pos hH'_xΔ hH'_xΔ' x hx_carrier h_x_val'
      have h_y_bound : |(y : ℝ) - (xΔ : ℝ)| ≤ Real.sqrt (12 * K) * Real.sqrt ((Δ + δ) / t) :=
        h_bound H' hH'_diff1 hH'_diff2 hH'_pos hH'_xΔ hH'_xΔ' y hy_carrier h_y_val'
      have h_final : |(x : ℝ) - (y : ℝ)| ≤ |(x : ℝ) - (xΔ : ℝ)| + |(y : ℝ) - (xΔ : ℝ)| :=
        h_triangle2 (x : ℝ) (y : ℝ) (xΔ : ℝ)
      calc |(x : ℝ) - (y : ℝ)|
        ≤ |(x : ℝ) - (xΔ : ℝ)| + |(y : ℝ) - (xΔ : ℝ)| := h_final
      _ ≤ 2 * (Real.sqrt (12 * K) * Real.sqrt ((Δ + δ) / t)) := by linarith
      _ = (2 * Real.sqrt (12 * K)) * Real.sqrt ((Δ + δ) / t) := by ring

end Kakeya.Cinematic
