import MyLeanRepo.Kakeya.Cinematic.Statements
import MyLeanRepo.Kakeya.Cinematic.TangencySublevelStructure.Basic
import MyLeanRepo.Kakeya.Cinematic.TangencySublevelStructure.LowerBounds
import MyLeanRepo.Kakeya.Cinematic.TangencySublevelStructure.ConvexEndpointCase
import MyLeanRepo.Kakeya.Cinematic.TangencySublevelStructure.ConvexLengthBound
import MyLeanRepo.Kakeya.Cinematic.TangencySublevelStructure.ConvexLowerBound
import MyLeanRepo.Kakeya.Cinematic.TangencySublevelStructure.ConvexDecompose
import MyLeanRepo.Kakeya.Cinematic.Targets.TangencySublevelDiameter.Helpers
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Convex.Deriv

/-!
# Convex tangency sublevel case

Strictly convex/concave real-analysis branch of PYZ Lemma 16(2b)--(2c).
-/

namespace Kakeya.Cinematic

open Set

/-! ## Helper lemmas -/

/-- A continuous function on a closed interval that is never zero has constant sign. -/
private lemma constant_sign_of_ne_zero
    {a b : ℝ} (hab : a ≤ b) {H : ℝ → ℝ}
    (H_cont : ContinuousOn H (Set.Icc a b))
    (H_ne_zero : ∀ x ∈ Set.Icc a b, H x ≠ 0) :
    (∀ x ∈ Set.Icc a b, 0 < H x) ∨ (∀ x ∈ Set.Icc a b, H x < 0) := by
  by_cases h_pos : ∃ x ∈ Set.Icc a b, 0 < H x
  · refine' Or.inl (fun x hx => _)
    by_cases h2 : H x < 0
    · rcases h_pos with ⟨y, hy, hy_pos⟩
      have h_ivt : ∃ z ∈ Set.Icc a b, H z = 0 := by
        by_cases hxy : x ≤ y
        · have h_cont' : ContinuousOn H (Set.Icc x y) := H_cont.mono (Set.Icc_subset_Icc hx.1 hy.2)
          have h6 : H x ≤ 0 := by linarith
          have h7 : 0 ≤ H y := by linarith
          have h8 : 0 ∈ Set.Icc (H x) (H y) := ⟨h6, h7⟩
          have h9 : 0 ∈ H '' Set.Icc x y := intermediate_value_Icc hxy h_cont' h8
          rcases h9 with ⟨z, hz, hz0⟩
          exact ⟨z, Set.Icc_subset_Icc hx.1 hy.2 hz, hz0⟩
        · have hyx : y ≤ x := by linarith
          have h_cont' : ContinuousOn H (Set.Icc y x) := H_cont.mono (Set.Icc_subset_Icc hy.1 hx.2)
          have h6 : H x ≤ 0 := by linarith
          have h7 : 0 ≤ H y := by linarith
          have h8 : 0 ∈ Set.Icc (H x) (H y) := ⟨h6, h7⟩
          have h9 : 0 ∈ H '' Set.Icc y x := intermediate_value_Icc' hyx h_cont' h8
          rcases h9 with ⟨z, hz, hz0⟩
          exact ⟨z, Set.Icc_subset_Icc hy.1 hx.2 hz, hz0⟩
      rcases h_ivt with ⟨z, hz, hz0⟩
      exact False.elim (H_ne_zero z hz hz0)
    · have h3 : 0 ≤ H x := by linarith
      have h4 : H x ≠ 0 := H_ne_zero x hx
      exact lt_of_le_of_ne h3 h4.symm
  · have h' : ∀ x ∈ Set.Icc a b, H x ≤ 0 := by
      intro x hx
      by_contra h2
      exact h_pos ⟨x, hx, by linarith⟩
    refine' Or.inr (fun x hx => _)
    have h3 : H x ≤ 0 := h' x hx
    have h4 : H x ≠ 0 := H_ne_zero x hx
    exact lt_of_le_of_ne h3 h4

/-- If H'' ≥ m > 0 on [a,b] and |H| ≤ δ on [a,b], then b-a ≤ 4√(δ/m).

Proof: if H' has a zero c, Taylor from c to each endpoint gives each half ≤ 2√(δ/m).
If H' has constant sign, Taylor across the whole interval gives ≤ 2√(δ/m). -/
private lemma component_convexity_bound
    {m delta a b : ℝ} {H : ℝ → ℝ}
    (hm_pos : 0 < m) (hdelta : 0 < delta)
    (hH1 : Differentiable ℝ H) (hH2 : Differentiable ℝ (deriv H))
    (hH''_ge : ∀ x ∈ Set.Icc a b, m ≤ deriv (deriv H) x)
    (hab : a ≤ b) (hH_bound : ∀ x ∈ Set.Icc a b, |H x| ≤ delta) :
    b - a ≤ 4 * Real.sqrt (delta / m) := by
  have ha_in : a ∈ Set.Icc a b := ⟨by linarith, hab⟩
  have hb_in : b ∈ Set.Icc a b := ⟨hab, by linarith⟩
  have hpos_dm : 0 ≤ delta / m := by positivity
  have h_sqrt4 : Real.sqrt (4 * delta / m) = 2 * Real.sqrt (delta / m) := by
    have h1 : Real.sqrt (4 * delta / m) = Real.sqrt 4 * Real.sqrt (delta / m) := by
      have h_eq : 4 * delta / m = 4 * (delta / m) := by field_simp
      rw [h_eq, Real.sqrt_mul (by positivity)]
    rw [h1]
    have h2 : Real.sqrt 4 = 2 := by
      rw [Real.sqrt_eq_cases] <;> norm_num
    rw [h2] <;> ring
  have h_half_sq : ∀ (x : ℝ), 0 ≤ x → m / 2 * x^2 ≤ 2 * delta → x ≤ 2 * Real.sqrt (delta / m) := by
    intro x hx_nonneg h
    have h6 : m * x^2 ≤ 4 * delta := by linarith
    have hsq : x^2 ≤ 4 * delta / m := by
      calc x^2 = (m * x^2) / m := by field_simp [hm_pos.ne'] <;> ring
        _ ≤ (4 * delta) / m := by gcongr
    have h3 : x ≤ Real.sqrt (4 * delta / m) := Real.le_sqrt_of_sq_le hsq
    rw [h_sqrt4] at h3; exact h3
  by_cases h_zero : ∃ c ∈ Set.Icc a b, deriv H c = 0
  · rcases h_zero with ⟨c, hc_Icc, hc_zero⟩
    have hc_in : c ∈ Set.Icc a b := hc_Icc
    have h_left_raw : H a ≥ H c + deriv H c * (a - c) + m / 2 * (a - c)^2 :=
      taylor_quadratic_lower_bound hH1 hH2 hab hc_in ha_in hH''_ge
    have h_right_raw : H b ≥ H c + deriv H c * (b - c) + m / 2 * (b - c)^2 :=
      taylor_quadratic_lower_bound hH1 hH2 hab hc_in hb_in hH''_ge
    have h_left : H a ≥ H c + m / 2 * (a - c)^2 := by
      rw [hc_zero] at h_left_raw; ring_nf at h_left_raw ⊢; exact h_left_raw
    have h_right : H b ≥ H c + m / 2 * (b - c)^2 := by
      rw [hc_zero] at h_right_raw; ring_nf at h_right_raw ⊢; exact h_right_raw
    have h1 : m / 2 * (c - a)^2 ≤ 2 * delta := by
      have h2 : (a - c)^2 = (c - a)^2 := by ring
      rw [h2] at h_left
      have h3 : H a ≤ delta := (abs_le.mp (hH_bound a ha_in)).2
      have h4 : H c ≥ -delta := (abs_le.mp (hH_bound c hc_in)).1
      linarith
    have h2 : m / 2 * (b - c)^2 ≤ 2 * delta := by
      have h3 : H b ≤ delta := (abs_le.mp (hH_bound b hb_in)).2
      have h4 : H c ≥ -delta := (abs_le.mp (hH_bound c hc_in)).1
      linarith
    have h3 : c - a ≤ 2 * Real.sqrt (delta / m) :=
      h_half_sq (c - a) (by linarith [hc_Icc.1]) h1
    have h4 : b - c ≤ 2 * Real.sqrt (delta / m) :=
      h_half_sq (b - c) (by linarith [hc_Icc.2]) h2
    have h5 : b - a = (c - a) + (b - c) := by linarith
    rw [h5]; linarith
  · have h_no_zero : ∀ x ∈ Set.Icc a b, deriv H x ≠ 0 := by
      intro x hx h
      exact h_zero ⟨x, hx, h⟩
    have h_cont : ContinuousOn (deriv H) (Set.Icc a b) := hH2.continuous.continuousOn
    have h_sign : (∀ x ∈ Set.Icc a b, 0 < deriv H x) ∨ (∀ x ∈ Set.Icc a b, deriv H x < 0) := by
      by_cases h_pos_a : 0 < deriv H a
      · left
        intro x hx
        by_contra h
        have h' : deriv H x ≤ 0 := by linarith
        have h_ax : a ≤ x := hx.1
        have h_cont' : ContinuousOn (deriv H) (Set.Icc a x) :=
          h_cont.mono (Set.Icc_subset_Icc (by linarith) hx.2)
        have h_ivt : ∃ z ∈ Set.Icc a x, deriv H z = 0 :=
          intermediate_value_Icc' h_ax h_cont' ⟨h', h_pos_a.le⟩
        rcases h_ivt with ⟨z, hz, hz0⟩
        exact h_no_zero z (Set.Icc_subset_Icc (by linarith) hx.2 hz) hz0
      · right
        have h_neg_a : deriv H a < 0 := by
          have h' : deriv H a ≠ 0 := h_no_zero a ha_in
          exact lt_of_le_of_ne (by linarith) h'
        intro x hx
        by_contra h
        have h' : 0 ≤ deriv H x := by linarith
        have h_ax : a ≤ x := hx.1
        have h_cont' : ContinuousOn (deriv H) (Set.Icc a x) :=
          h_cont.mono (Set.Icc_subset_Icc (by linarith) hx.2)
        have h_ivt : ∃ z ∈ Set.Icc a x, deriv H z = 0 :=
          intermediate_value_Icc h_ax h_cont' ⟨h_neg_a.le, h'⟩
        rcases h_ivt with ⟨z, hz, hz0⟩
        exact h_no_zero z (Set.Icc_subset_Icc (by linarith) hx.2 hz) hz0
    rcases h_sign with (h_pos | h_neg)
    · have h_taylor_raw : H b ≥ H a + deriv H a * (b - a) + m / 2 * (b - a)^2 :=
        taylor_quadratic_lower_bound hH1 hH2 hab ha_in hb_in hH''_ge
      have h_linear_nonneg : 0 ≤ deriv H a * (b - a) := by
        have h4 : 0 < deriv H a := h_pos a ha_in
        have h5 : 0 ≤ b - a := sub_nonneg.mpr hab
        exact mul_nonneg h4.le h5
      have h_taylor : H b ≥ H a + m / 2 * (b - a)^2 := by linarith
      have h1 : H a ≥ -delta := (abs_le.mp (hH_bound a ha_in)).1
      have h2 : H b ≤ delta := (abs_le.mp (hH_bound b hb_in)).2
      have h3 : m / 2 * (b - a)^2 ≤ 2 * delta := by linarith
      have h4 : m * (b - a)^2 ≤ 4 * delta := by linarith
      have h5 : (b - a)^2 ≤ 4 * delta / m := by
        calc (b - a)^2 = (m * (b - a)^2) / m := by field_simp [hm_pos.ne'] <;> ring
          _ ≤ (4 * delta) / m := by gcongr
      have h6 : 0 ≤ b - a := sub_nonneg.mpr hab
      have h7 : b - a ≤ Real.sqrt (4 * delta / m) := Real.le_sqrt_of_sq_le h5
      rw [h_sqrt4] at h7; linarith
    · have h_taylor_raw : H a ≥ H b + deriv H b * (a - b) + m / 2 * (a - b)^2 :=
        taylor_quadratic_lower_bound hH1 hH2 hab hb_in ha_in hH''_ge
      have h_linear_nonneg : 0 ≤ deriv H b * (a - b) := by
        have h4 : deriv H b < 0 := h_neg b hb_in
        have h5 : a - b ≤ 0 := sub_nonpos.mpr hab
        exact mul_nonneg_of_nonpos_of_nonpos h4.le h5
      have h_taylor : H a ≥ H b + m / 2 * (a - b)^2 := by linarith
      have h1 : H b ≥ -delta := (abs_le.mp (hH_bound b hb_in)).1
      have h2 : H a ≤ delta := (abs_le.mp (hH_bound a ha_in)).2
      have h3 : m / 2 * (a - b)^2 ≤ 2 * delta := by linarith
      have h4 : m * (a - b)^2 ≤ 4 * delta := by linarith
      have h5 : (b - a)^2 = (a - b)^2 := by ring
      have h6 : (b - a)^2 ≤ 4 * delta / m := by
        calc (b - a)^2 = (a - b)^2 := h5
          _ = (m * (a - b)^2) / m := by field_simp [hm_pos.ne'] <;> ring
          _ ≤ (4 * delta) / m := by gcongr
      have h7 : 0 ≤ b - a := sub_nonneg.mpr hab
      have h8 : b - a ≤ Real.sqrt (4 * delta / m) := Real.le_sqrt_of_sq_le h6
      rw [h_sqrt4] at h8; linarith

/-- Per-component length bound for the convex case.

Takes `hH2 : ContDiff ℝ 1 (deriv H)` so reflection is easy. -/
private lemma component_length_bound
    {K C t delta Δ scale m : ℝ}
    {I : ParameterInterval} {H : ℝ → ℝ}
    (hK : 1 ≤ K) (hC_large : C ≥ 1000 * K^2)
    (ht_pos : 0 < t) (hdelta : 0 < delta) (hΔ_nonneg : 0 ≤ Δ)
    (hscale : scale = Real.sqrt ((Δ + delta) * t))
    (hm_def : m = t / (6 * K))
    (hI_controlled : I.IsControlled K)
    (hH1 : Differentiable ℝ H) (hH2 : ContDiff ℝ 1 (deriv H))
    (hH''_ge : ∀ x ∈ Set.Icc I.left I.right, m ≤ deriv (deriv H) x)
    (hH'_min : ∀ (x : UnitPoint), x ∈ I.centeredCarrier (1 / 2) →
        |H (x : ℝ)| + |deriv H (x : ℝ)| ≥ Δ)
    (hdelta_le : delta ≤ t / (6 * K))
    {a b : ℝ} (hab : a ≤ b)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (ha_c4 : |a - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2)
    (hb_c4 : |b - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2)
    (hH_bound : ∀ x ∈ Set.Icc a b, |H x| ≤ delta) :
    b - a ≤ C * delta / scale := by
  have hm_pos : 0 < m := by rw [hm_def] <;> positivity
  let aP : UnitPoint := ⟨a, ⟨ha0, ha1⟩⟩
  let bP : UnitPoint := ⟨b, ⟨hb0, hb1⟩⟩
  have ha_c4_mem : aP ∈ I.centeredCarrier (1 / 4) := by
    simp only [ParameterInterval.centeredCarrier, Set.mem_setOf_eq]; exact ha_c4
  have hb_c4_mem : bP ∈ I.centeredCarrier (1 / 4) := by
    simp only [ParameterInterval.centeredCarrier, Set.mem_setOf_eq]; exact hb_c4
  have hH2diff : Differentiable ℝ (deriv H) := hH2.differentiable (by norm_num)
  have hH''_ge_J : ∀ x ∈ Set.Icc a b, m ≤ deriv (deriv H) x := by
    intro x hx
    have ha_I : a ∈ Set.Icc I.left I.right := by
      have h : aP ∈ I.carrier := I.centeredCarrier_subset_carrier (by norm_num) (by norm_num) ha_c4_mem
      simpa [ParameterInterval.carrier, aP] using h
    have hb_I : b ∈ Set.Icc I.left I.right := by
      have h : bP ∈ I.carrier := I.centeredCarrier_subset_carrier (by norm_num) (by norm_num) hb_c4_mem
      simpa [ParameterInterval.carrier, bP] using h
    have h1 : x ∈ Set.Icc I.left I.right :=
      ⟨by linarith [ha_I.1, hx.1], by linarith [hb_I.2, hx.2]⟩
    exact hH''_ge x h1

  by_cases hΔ_leδ : Δ ≤ delta
  · -- Case Δ ≤ δ: convexity bound 4√(δ/m) and algebra
    have h_len : b - a ≤ 4 * Real.sqrt (delta / m) :=
      component_convexity_bound hm_pos hdelta hH1 hH2diff hH''_ge_J hab hH_bound
    have h_scale_pos : 0 < scale := by
      rw [hscale]
      have h : 0 < (Δ + delta) * t := by positivity
      exact Real.sqrt_pos.mpr h
    have hK_pos : 0 < K := by linarith
    have hC_pos : 0 < C := by
      have h : C ≥ 1000 * K^2 := hC_large
      have h' : 0 < K := hK_pos
      nlinarith
    have h3 : C^2 ≥ 192 * K := by
      have h4 : C ≥ 1000 * K^2 := hC_large
      have h5 : K ≥ 1 := hK
      nlinarith [sq_nonneg (K - 1), sq_nonneg (C - 1000 * K^2)]
    have h_goal2 : 96 * K * delta * (Δ + delta) ≤ C^2 * delta^2 := by
      have h4 : Δ + delta ≤ 2 * delta := by linarith
      have h5 : 96 * K * delta * (Δ + delta) ≤ 192 * K * delta^2 := by
        calc 96 * K * delta * (Δ + delta)
          ≤ 96 * K * delta * (2 * delta) := by gcongr <;> linarith
        _ = 192 * K * delta^2 := by ring
      have h6 : 192 * K * delta^2 ≤ C^2 * delta^2 := by
        have h7 : 0 ≤ delta^2 := by positivity
        nlinarith
      linarith
    have h_alg : 16 * delta / m ≤ C^2 * delta^2 / ((Δ + delta) * t) := by
      have h1 : 16 * delta / m = 96 * K * delta / t := by
        rw [hm_def]; field_simp [hK_pos.ne', ht_pos.ne'] <;> ring
      rw [h1]
      have h4 : 0 < t := ht_pos
      have h5 : 0 < Δ + delta := by linarith
      have h6 : 0 < delta := hdelta
      have h7 : 0 ≤ (Δ + delta) * t := by positivity
      have h_eq : 96 * K * delta / t =
          (96 * K * delta * (Δ + delta)) / ((Δ + delta) * t) := by
        field_simp [h5.ne', h4.ne'] <;> ring
      rw [h_eq]
      exact div_le_div_of_nonneg_right h_goal2 h7
    have h_sq1 : (4 * Real.sqrt (delta / m))^2 = 16 * delta / m := by
      have hpos : 0 ≤ delta / m := by positivity
      have h : (Real.sqrt (delta / m))^2 = delta / m := Real.sq_sqrt hpos
      have h9 : (4 * Real.sqrt (delta / m))^2 =
          16 * (Real.sqrt (delta / m))^2 := by ring
      rw [h9, h] <;> ring
    have h_sq2 : (C * delta / scale)^2 =
        C^2 * delta^2 / ((Δ + delta) * t) := by
      have hpos : 0 ≤ (Δ + delta) * t := by positivity
      have hsqrt : scale^2 = (Δ + delta) * t := by
        rw [hscale]
        exact Real.sq_sqrt hpos
      calc (C * delta / scale)^2
        = C^2 * delta^2 / scale^2 := by ring
      _ = C^2 * delta^2 / ((Δ + delta) * t) := by rw [hsqrt]
    have h_sq : (4 * Real.sqrt (delta / m))^2 ≤
        (C * delta / scale)^2 := by
      rw [h_sq1, h_sq2]; exact h_alg
    have h_pos1 : 0 ≤ 4 * Real.sqrt (delta / m) := by positivity
    have h_pos2 : 0 ≤ C * delta / scale := by positivity
    have h_goal : 4 * Real.sqrt (delta / m) ≤ C * delta / scale := by
      nlinarith [sq_nonneg
        (4 * Real.sqrt (delta / m) - C * delta / scale)]
    exact h_len.trans h_goal
  · -- Case Δ > δ: H' cannot vanish, use endpoint case + length bound
    have hΔ_gtδ : Δ > delta := by linarith
    have h_ab_center2 : ∀ (xP : UnitPoint), (xP : ℝ) ∈ Set.Icc a b →
        xP ∈ I.centeredCarrier (1 / 2) := by
      intro xP hx
      have hx0 : 0 ≤ (xP : ℝ) := by linarith [ha0, hx.1]
      have hx1 : (xP : ℝ) ≤ 1 := by linarith [hb1, hx.2]
      have h1 : |(xP : ℝ) - I.midpoint| ≤ I.length / 8 := by
        have h2 : |a - I.midpoint| ≤ I.length / 8 := by
          have h3 : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
          exact ha_c4.trans_eq h3
        have h4 : |b - I.midpoint| ≤ I.length / 8 := by
          have h5 : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
          exact hb_c4.trans_eq h5
        have h6 : a ≤ (xP : ℝ) := hx.1
        have h7 : (xP : ℝ) ≤ b := hx.2
        by_cases h8 : (xP : ℝ) ≤ I.midpoint
        · have h9 : -I.length / 8 ≤ (xP : ℝ) - I.midpoint := by
            linarith [(abs_le.mp h2).1]
          have h10 : (xP : ℝ) - I.midpoint ≤ 0 := by linarith
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        · have h9 : 0 ≤ (xP : ℝ) - I.midpoint := by linarith
          have h10 : (xP : ℝ) - I.midpoint ≤ I.length / 8 := by
            linarith [(abs_le.mp h4).2]
          exact abs_le.mpr ⟨by linarith, by linarith⟩
      simp only [ParameterInterval.centeredCarrier, Set.mem_setOf_eq]
      have h11 : I.length / 8 ≤ (1 / 2 : ℝ) * I.length / 2 := by
        have h12 : (1 / 2 : ℝ) * I.length / 2 = I.length / 4 := by ring
        rw [h12]
        have h13 : 0 ≤ I.length := I.length_nonneg
        linarith
      exact h1.trans h11
    have h_no_zero : ∀ x ∈ Set.Icc a b, deriv H x ≠ 0 := by
      intro x hx h_zero
      have hx0 : 0 ≤ x := by linarith [ha0, hx.1]
      have hx1 : x ≤ 1 := by linarith [hb1, hx.2]
      let xP : UnitPoint := ⟨x, ⟨hx0, hx1⟩⟩
      have hxP_in : (xP : ℝ) ∈ Set.Icc a b := by simpa [xP] using hx
      have hx_center2 : xP ∈ I.centeredCarrier (1 / 2) :=
        h_ab_center2 xP hxP_in
      have h1 : |H x| + |deriv H x| ≥ Δ := hH'_min xP hx_center2
      have h1' : |H x| + 0 ≥ Δ := by
        rw [h_zero] at h1
        simpa using h1
      have h1'' : |H x| ≥ Δ := by simpa using h1'
      have h2 : |H x| ≤ delta := hH_bound x hx
      have h_contra : Δ ≤ delta := by linarith
      exact False.elim (not_le.mpr hΔ_gtδ h_contra)
    have h_cont : ContinuousOn (deriv H) (Set.Icc a b) :=
      hH2diff.continuous.continuousOn
    have h_sign : (∀ x ∈ Set.Icc a b, 0 < deriv H x) ∨
        (∀ x ∈ Set.Icc a b, deriv H x < 0) :=
      constant_sign_of_never_zero hab h_cont h_no_zero
    rcases h_sign with (h_pos | h_neg)
    · -- H' > 0 case
      have ha_in' : a ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
      set A : ℝ := deriv H a with hA_def
      have hA_pos : 0 < A := h_pos a ha_in'
      have hA_nonneg : 0 ≤ A := by linarith
      have ha_center2 : aP ∈ I.centeredCarrier (1 / 2) :=
        h_ab_center2 aP ha_in'
      have hDelta_le_A : Δ ≤ delta + A := by
        have h1 : |H a| + |deriv H a| ≥ Δ := hH'_min aP ha_center2
        have h2 : |deriv H a| = deriv H a := abs_of_pos hA_pos
        rw [h2] at h1
        have h3 : |H a| ≤ delta := hH_bound a ha_in'
        linarith
      set ell : ℝ := I.midpoint - I.length / 4 with hell_def
      have h_a_ge_ell : ell ≤ a := by
        have h4 : a ≥ I.midpoint - I.length / 8 := by
          have h5 := (abs_le.mp ha_c4).1
          have h7 : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
          rw [h7] at h5
          linarith
        rw [hell_def]
        linarith [I.length_nonneg]
      have hK_pos : 0 < K := by linarith
      have hgap : 1 / (96 * K) ≤ a - ell := by
        have h1 : I.length ≥ (12 * K)⁻¹ := hI_controlled.1
        have h2 : a - ell ≥ I.length / 8 := by
          have h3 : a ≥ I.midpoint - I.length / 8 := by
            have h4 := (abs_le.mp ha_c4).1
            have h5 : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
            rw [h5] at h4; linarith
          rw [hell_def]
          linarith [I.length_nonneg]
        have h3 : I.length / 8 ≥ 1 / (96 * K) := by
          calc I.length / 8
            ≥ ((12 * K)⁻¹) / 8 := by gcongr
          _ = 1 / (96 * K) := by
            field_simp [hK_pos.ne'] <;> ring
        linarith
      have h_ell_center : ∀ (yP : UnitPoint),
          (yP : ℝ) ∈ Set.Icc ell a → yP ∈ I.centeredCarrier (1 / 2) := by
        intro yP hy
        have h3 : |(yP : ℝ) - I.midpoint| ≤ I.length / 4 := by
          have h_ell_eq : ell = I.midpoint - I.length / 4 := by
            simp [ell, hell_def]
          have h4 : (yP : ℝ) ≥ I.midpoint - I.length / 4 := by
            linarith [hy.1, h_ell_eq]
          have h5 : (yP : ℝ) - I.midpoint ≤ I.length / 8 := by
            have h6 : a - I.midpoint ≤ I.length / 8 := by
              have h7 : (1 / 4 : ℝ) * I.length / 2 =
                  I.length / 8 := by ring
              exact (abs_le.mp (ha_c4.trans_eq h7)).2
            linarith [hy.2, h6]
          have h7 : -I.length / 4 ≤ (yP : ℝ) - I.midpoint := by
            linarith
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        simp only [ParameterInterval.centeredCarrier, Set.mem_setOf_eq]
        have h9 : (1 / 2 : ℝ) * I.length / 2 = I.length / 4 := by ring
        rw [h9]; exact h3
      have h_ell_ge_left : ell ≥ I.left := by
        rw [hell_def]
        simp [ParameterInterval.midpoint, ParameterInterval.length]
        <;> linarith [I.left_le_right]
      have hDelta : ∀ (x : ℝ), x ∈ Set.Icc ell a →
          Δ ≤ |H x| + |deriv H x| := by
        intro x hx
        have hx0 : 0 ≤ x := by
          linarith [I.left_mem.1, h_ell_ge_left, hx.1]
        have hx1 : x ≤ 1 := by linarith [ha1, hx.2]
        let xP : UnitPoint := ⟨x, ⟨hx0, hx1⟩⟩
        have hxP_in : (xP : ℝ) ∈ Set.Icc ell a := by
          simpa [xP] using hx
        have hx_center2 : xP ∈ I.centeredCarrier (1 / 2) :=
          h_ell_center xP hxP_in
        exact hH'_min xP hx_center2
      have hH''_ge_ell : ∀ x ∈ Set.Icc ell a,
          m ≤ deriv (deriv H) x := by
        intro x hx
        have h_a_right : a ≤ I.right := by
          have h : aP ∈ I.carrier :=
            I.centeredCarrier_subset_carrier (by norm_num) (by norm_num)
              ha_c4_mem
          have h' : (aP : ℝ) ∈ Set.Icc I.left I.right := by
            simpa [ParameterInterval.carrier, aP] using h
          exact h'.2
        have h1 : x ∈ Set.Icc I.left I.right :=
          ⟨by linarith [h_ell_ge_left, hx.1],
            by linarith [h_a_right, hx.2]⟩
        exact hH''_ge x h1
      have h_case : (Δ ≤ delta + A^2 / m) ∨
          (A ≥ t / (576 * K^2)) :=
        convex_endpoint_case hK ht_pos hm_def hgap hH1 hH2diff
          hH''_ge_ell (by simp [hA_def]) hA_pos
          (hH_bound a ha_in') hDelta
      have hA_nonneg' : 0 ≤ deriv H a := by
        simpa [hA_def] using hA_nonneg
      have hDelta_le_A' : Δ ≤ delta + deriv H a := by
        simpa [hA_def] using hDelta_le_A
      have h_case' : (Δ ≤ delta + (deriv H a)^2 / m) ∨
          (deriv H a ≥ t / (576 * K^2)) := by
        simpa [hA_def] using h_case
      exact convex_case_length_bound hK ht_pos hdelta hdelta_le
        H hH1 hH2diff m hm_def a b hab hH''_ge_J hH_bound
        hA_nonneg' Δ hΔ_nonneg hDelta_le_A' h_case'
        C hC_large hscale
    · -- H' < 0: reflect F(x) = H(a+b-x)
      let g : ℝ → ℝ := fun x => a + b - x
      let F : ℝ → ℝ := H ∘ g
      have hg : Differentiable ℝ g :=
        (differentiable_const (a + b)).sub differentiable_id
      have hg_cd : ContDiff ℝ 1 g := by
        have h1 : ContDiff ℝ 1 (fun _ : ℝ => a + b) := contDiff_const
        exact h1.sub contDiff_id
      have hF1 : Differentiable ℝ F := hH1.comp hg
      have h_derivF : deriv F = fun x => -deriv H (g x) := by
        funext z
        have h1 : HasDerivAt H (deriv H (g z)) (g z) :=
          (hH1 (g z)).hasDerivAt
        have h2 : HasDerivAt g (deriv g z) z := (hg z).hasDerivAt
        have h3 : HasDerivAt F (deriv H (g z) * deriv g z) z :=
          h1.comp z h2
        have h4 : deriv F z = deriv H (g z) * deriv g z := h3.deriv
        rw [h4]
        have hg' : deriv g z = -1 := by simp [g]
        rw [hg'] <;> ring
      have hF2_cd : ContDiff ℝ 1 (deriv F) := by
        rw [h_derivF]; exact (hH2.comp hg_cd).neg
      have hF2 : Differentiable ℝ (deriv F) :=
        hF2_cd.differentiable (by norm_num)
      have hF''_eq : ∀ x, deriv (deriv F) x =
          deriv (deriv H) (g x) := by
        intro x
        have h1 : deriv (deriv F) x =
            -(deriv (deriv H) (g x) * deriv g x) := by
          rw [h_derivF]
          have h2 : HasDerivAt (fun y => deriv H (g y))
              (deriv (deriv H) (g x) * deriv g x) x := by
            have hhd : HasDerivAt (deriv H)
                (deriv (deriv H) (g x)) (g x) :=
              (hH2diff (g x)).hasDerivAt
            have hgd : HasDerivAt g (deriv g x) x :=
              (hg x).hasDerivAt
            exact hhd.comp x hgd
          have h3 : HasDerivAt (fun y => -deriv H (g y))
              (-(deriv (deriv H) (g x) * deriv g x)) x :=
            h2.neg
          exact h3.deriv
        rw [h1]
        have hg' : deriv g x = -1 := by simp [g]
        rw [hg'] <;> ring
      have hF''_ge : ∀ x ∈ Set.Icc a b,
          m ≤ deriv (deriv F) x := by
        intro x hx
        have h1 : deriv (deriv F) x =
            deriv (deriv H) (g x) := hF''_eq x
        rw [h1]
        have h2 : g x ∈ Set.Icc a b := by
          have hgx : g x = a + b - x := by simp [g]
          rw [hgx]
          constructor <;> linarith [hx.1, hx.2]
        exact hH''_ge_J (g x) h2
      have hF_bound : ∀ x ∈ Set.Icc a b, |F x| ≤ delta := by
        intro x hx
        have h2 : g x ∈ Set.Icc a b := by
          have hgx : g x = a + b - x := by simp [g]
          rw [hgx]
          constructor <;> linarith [hx.1, hx.2]
        simpa [F] using hH_bound (g x) h2
      have hH'_neg : ∀ x ∈ Set.Icc a b, deriv H x < 0 := h_neg
      have hb_Icc : b ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
      have ha_Icc : a ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
      set A : ℝ := deriv F a with hA_def
      have hA_pos : 0 < A := by
        have h1 : deriv F a = -deriv H b := by
          rw [h_derivF] <;> simp [g] <;> ring
        rw [hA_def, h1]
        exact neg_pos.mpr (hH'_neg b hb_Icc)
      have hA_nonneg : 0 ≤ A := by linarith
      have hb_center2 : bP ∈ I.centeredCarrier (1 / 2) := by
        have hb_in' : (bP : ℝ) ∈ Set.Icc a b :=
          ⟨by linarith, by linarith⟩
        exact h_ab_center2 bP hb_in'
      have hDelta_le_A : Δ ≤ delta + A := by
        have h1 : |H b| + |deriv H b| ≥ Δ :=
          hH'_min bP hb_center2
        have h2 : |deriv H b| = -deriv H b :=
          abs_of_neg (hH'_neg b hb_Icc)
        have h3 : deriv F a = -deriv H b := by
          rw [h_derivF] <;> simp [g] <;> ring
        rw [hA_def, h3]
        rw [h2] at h1
        have h4 : |H b| ≤ delta := hH_bound b hb_Icc
        linarith
      set urr : ℝ := I.midpoint + I.length / 4 with hurr_def
      set ell_F : ℝ := a + b - urr with hell_F_def
      have h_b_le_urr : b ≤ urr := by
        have h4 := (abs_le.mp hb_c4).2
        have h5 : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by
          ring
        rw [h5] at h4
        rw [hurr_def]
        linarith [I.length_nonneg]
      have hK_pos : 0 < K := by linarith
      have hgap_F : 1 / (96 * K) ≤ a - ell_F := by
        have h1 : I.length ≥ (12 * K)⁻¹ := hI_controlled.1
        have h2 : a - ell_F = urr - b := by
          dsimp only [ell_F, urr, hell_F_def, hurr_def] <;> ring
        rw [h2]
        have h3 : urr - b ≥ I.length / 8 := by
          rw [hurr_def]
          have h4 := (abs_le.mp hb_c4).2
          have h5 : (1 / 4 : ℝ) * I.length / 2 =
              I.length / 8 := by ring
          rw [h5] at h4
          linarith [I.length_nonneg]
        have h4 : I.length / 8 ≥ 1 / (96 * K) := by
          calc I.length / 8
            ≥ ((12 * K)⁻¹) / 8 := by gcongr
          _ = 1 / (96 * K) := by
            field_simp [hK_pos.ne'] <;> ring
        linarith
      have h_ellF_center : ∀ (y : ℝ), y ∈ Set.Icc ell_F a →
          ∃ (yP : UnitPoint), (yP : ℝ) = g y ∧
            yP ∈ I.centeredCarrier (1 / 2) := by
        intro y hy
        have h1 : g y ∈ Set.Icc b urr := by
          have hgy : g y = a + b - y := by simp [g]
          rw [hgy]
          constructor
          · linarith [hy.2]
          · have h9 : a + b - y ≤ urr := by
              have h10 : a + b - ell_F = urr := by
                linarith [hell_F_def]
              linarith [hy.1]
            exact h9
        have h2 : |g y - I.midpoint| ≤ I.length / 4 := by
          have h3 : g y ≥ b := h1.1
          have h4 : g y ≤ urr := h1.2
          have h5 : b - I.midpoint ≥ -I.length / 8 := by
            have h6 := (abs_le.mp hb_c4).1
            have h7 : (1 / 4 : ℝ) * I.length / 2 =
                I.length / 8 := by ring
            rw [h7] at h6
            linarith
          have h6 : g y ≤ I.midpoint + I.length / 4 := by
            have h7 : urr = I.midpoint + I.length / 4 := hurr_def
            linarith [h4, h7]
          have h7 : g y ≥ I.midpoint - I.length / 4 := by linarith
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        have hgy0 : 0 ≤ g y := by
          have h3 : g y ≥ b := h1.1
          linarith [hb0]
        have hgy1 : g y ≤ 1 := by
          have h3 : g y ≤ urr := h1.2
          have h4 : urr ≤ I.right := by
            rw [hurr_def]
            simp [ParameterInterval.midpoint, ParameterInterval.length]
            <;> linarith [I.left_le_right]
          linarith [I.right_mem.2, h4]
        let yP : UnitPoint := ⟨g y, ⟨hgy0, hgy1⟩⟩
        have h_center : yP ∈ I.centeredCarrier (1 / 2) := by
          simp only [ParameterInterval.centeredCarrier,
            Set.mem_setOf_eq, yP]
          have h9 : (1 / 2 : ℝ) * I.length / 2 =
              I.length / 4 := by ring
          rw [h9]
          exact h2
        have h_eq : (yP : ℝ) = g y := by
          dsimp only [yP] <;> rfl
        exact ⟨yP, h_eq, h_center⟩
      have hDelta_F : ∀ (x : ℝ), x ∈ Set.Icc ell_F a →
          Δ ≤ |F x| + |deriv F x| := by
        intro x hx
        rcases h_ellF_center x hx with ⟨xP, hxP_eq, hxP_center⟩
        have h1' : |F x| = |H (g x)| := by simp [F] <;> rfl
        have h_deriv_at : deriv F x = -deriv H (g x) := by
          rw [h_derivF] <;> ring
        have h2' : |deriv F x| = |deriv H (g x)| := by
          rw [h_deriv_at, abs_neg]
        rw [h1', h2']
        simpa [hxP_eq] using hH'_min xP hxP_center
      have hF''_ge_ellF : ∀ x ∈ Set.Icc ell_F a,
          m ≤ deriv (deriv F) x := by
        intro x hx
        have h1 : deriv (deriv F) x =
            deriv (deriv H) (g x) := hF''_eq x
        rw [h1]
        have h1' : g x ∈ Set.Icc b urr := by
          have hgx : g x = a + b - x := by simp [g]
          rw [hgx]
          constructor
          · linarith [hx.2]
          · have h9 : a + b - x ≤ urr := by
              have h10 : a + b - ell_F = urr := by
                linarith [hell_F_def]
              linarith [hx.1]
            exact h9
        have h_b_left : I.left ≤ b := by
          have h_b_carrier : bP ∈ I.carrier :=
            I.centeredCarrier_subset_carrier (by norm_num) (by norm_num)
              hb_c4_mem
          have h_b_Icc : (bP : ℝ) ∈ Set.Icc I.left I.right := by
            simpa [ParameterInterval.carrier, bP] using h_b_carrier
          exact h_b_Icc.1
        have h3 : g x ≥ I.left := by
          have h4 : g x ≥ b := h1'.1
          linarith [h_b_left]
        have h6 : g x ≤ I.right := by
          have h7 : g x ≤ urr := h1'.2
          have h8 : urr ≤ I.right := by
            rw [hurr_def]
            simp [ParameterInterval.midpoint, ParameterInterval.length]
            <;> linarith [I.left_le_right]
          linarith
        have h2 : g x ∈ Set.Icc I.left I.right := ⟨h3, h6⟩
        exact hH''_ge (g x) h2
      have h_case : (Δ ≤ delta + A^2 / m) ∨
          (A ≥ t / (576 * K^2)) :=
        convex_endpoint_case hK ht_pos hm_def hgap_F hF1 hF2
          hF''_ge_ellF (by simp [hA_def]) hA_pos
          (hF_bound a ha_Icc) hDelta_F
      have hA_nonneg' : 0 ≤ deriv F a := by
        simpa [hA_def] using hA_nonneg
      have hDelta_le_A' : Δ ≤ delta + deriv F a := by
        simpa [hA_def] using hDelta_le_A
      have h_case' : (Δ ≤ delta + (deriv F a)^2 / m) ∨
          (deriv F a ≥ t / (576 * K^2)) := by
        simpa [hA_def] using h_case
      exact convex_case_length_bound hK ht_pos hdelta hdelta_le
        F hF1 hF2 m hm_def a b hab hF''_ge hF_bound
        hA_nonneg' Δ hΔ_nonneg hDelta_le_A' h_case'
        C hC_large hscale

/-! ## Main theorem -/

theorem convex_tangency_sublevel_case :
    ConvexTangencySublevelCaseStatement := by
  intro K Cdiam hK hCdiam_pos
  let C : ℝ := max (1000 * K^2) (1000 * K) + 1
  have hC_pos : 0 < C := by positivity
  have hC_large1 : C ≥ 1000 * K^2 := by
    have h1 : C ≥ max (1000 * K^2) (1000 * K) := by linarith
    have h2 : max (1000 * K^2) (1000 * K) ≥ 1000 * K^2 := le_max_left _ _
    linarith
  have hC_large2 : C ≥ 1000 * K := by
    have h1 : C ≥ max (1000 * K^2) (1000 * K) := by linarith
    have h2 : max (1000 * K^2) (1000 * K) ≥ 1000 * K := le_max_right _ _
    linarith
  refine' ⟨C, hC_pos, _⟩
  intro I hI f g hfg delta hdelta hdelta_le h_small h_small' h_large''
  intro E Ehalf h_diam
  set t : ℝ := c2Distance f g with ht_eq
  set Δ : ℝ := tangencyParameterOn I f g with hΔ_def
  set scale : ℝ := Real.sqrt ((Δ + delta) * t) with hscale_def
  set H : ℝ → ℝ := f.extension - g.extension with hH_def

  have ht_pos : 0 < t := by
    have h_eq : c2Distance f g = dist f g := by simp [c2Distance]
    have h_pos : 0 < c2Distance f g := by
      rw [h_eq]
      exact dist_pos.mpr hfg
    rw [ht_eq]
    exact h_pos

  have hH_c2 : ContDiff ℝ 2 H := ContDiff.sub f.extension_contDiff g.extension_contDiff
  have hH1 : Differentiable ℝ H := hH_c2.differentiable (by norm_num)
  have hH2 : ContDiff ℝ 1 (deriv H) := hH_c2.deriv'
  have hH2diff : Differentiable ℝ (deriv H) := hH2.differentiable (by norm_num)
  have hH''_cont : Continuous (deriv (deriv H)) := hH2.continuous_deriv (by norm_num)
  have hH_cont : Continuous H := hH1.continuous

  have h_eval : ∀ (z : UnitPoint), H (z : ℝ) = f z - g z := by
    intro z; simp [H]
  have h_deriv_eval : ∀ (z : UnitPoint), deriv H (z : ℝ) = f.firstDeriv z - g.firstDeriv z := by
    intro z
    have h_f_diff : Differentiable ℝ f.extension := f.extension_contDiff.differentiable (by norm_num)
    have h_g_diff : Differentiable ℝ g.extension := g.extension_contDiff.differentiable (by norm_num)
    have h1 : deriv H (z : ℝ) = deriv f.extension (z : ℝ) - deriv g.extension (z : ℝ) :=
      deriv_sub (h_f_diff (z : ℝ)) (h_g_diff (z : ℝ))
    rw [h1, C2Function.deriv_extension_eq_firstDeriv, C2Function.deriv_extension_eq_firstDeriv] <;> abel
  have h_deriv2_eval : ∀ (z : UnitPoint), deriv (deriv H) (z : ℝ) = f.secondDeriv z - g.secondDeriv z := by
    intro z
    have h_eq_fun : deriv H = deriv f.extension - deriv g.extension := by
      funext w
      exact deriv_sub ((f.extension_contDiff.differentiable (by norm_num)) w)
                      ((g.extension_contDiff.differentiable (by norm_num)) w)
    rw [h_eq_fun]
    have h_f_diff2 : Differentiable ℝ (deriv f.extension) :=
      ContDiff.differentiable (ContDiff.deriv' (n := 1) f.extension_contDiff) (by norm_num)
    have h_g_diff2 : Differentiable ℝ (deriv g.extension) :=
      ContDiff.differentiable (ContDiff.deriv' (n := 1) g.extension_contDiff) (by norm_num)
    have h2 : deriv (deriv f.extension - deriv g.extension) (z : ℝ) =
               deriv (deriv f.extension) (z : ℝ) - deriv (deriv g.extension) (z : ℝ) :=
      deriv_sub (h_f_diff2 (z : ℝ)) (h_g_diff2 (z : ℝ))
    rw [h2, C2Function.secondDeriv_extension_eq_secondDeriv, C2Function.secondDeriv_extension_eq_secondDeriv] <;> abel

  have hH'_min : ∀ (x : UnitPoint), x ∈ I.centeredCarrier (1 / 2) →
      |H (x : ℝ)| + |deriv H (x : ℝ)| ≥ Δ := by
    intro x hx
    have h_bdd : BddBelow {r : ℝ | ∃ (y : UnitPoint), y ∈ I.centeredCarrier (1 / 2) ∧
        r = |f y - g y| + |f.firstDeriv y - g.firstDeriv y|} := by
      refine' ⟨0, _⟩
      intro r hr; rcases hr with ⟨y, _, rfl⟩; positivity
    have h3 : |f x - g x| + |f.firstDeriv x - g.firstDeriv x| ∈ {r : ℝ | ∃ (y : UnitPoint), y ∈ I.centeredCarrier (1 / 2) ∧
        r = |f y - g y| + |f.firstDeriv y - g.firstDeriv y|} := ⟨x, hx, by ring⟩
    have h4 : Δ ≤ |f x - g x| + |f.firstDeriv x - g.firstDeriv x| := by
      rw [hΔ_def, tangencyParameterOn]
      exact csInf_le h_bdd h3
    have h5 : |H (x : ℝ)| = |f x - g x| := by rw [h_eval]
    have h6 : |deriv H (x : ℝ)| = |f.firstDeriv x - g.firstDeriv x| := by rw [h_deriv_eval]
    rw [h5, h6]; exact h4

  have hΔ_nonneg : 0 ≤ Δ := by
    rw [hΔ_def, tangencyParameterOn]
    let S : Set ℝ := {r | ∃ (y : UnitPoint), y ∈ I.centeredCarrier (1 / 2) ∧
        r = |f y - g y| + |f.firstDeriv y - g.firstDeriv y|}
    have hS_bdd : BddBelow S := ⟨0, fun r hr => by
      rcases hr with ⟨y, _, rfl⟩; positivity⟩
    have hmid_eq : I.midpoint = (I.left + I.right) / 2 := by simp [ParameterInterval.midpoint]
    have hmid0 : 0 ≤ I.midpoint := by
      rw [hmid_eq]; have h1 : 0 ≤ I.left := I.left_mem.1; have h2 : 0 ≤ I.right := I.right_mem.1; linarith
    have hmid1 : I.midpoint ≤ 1 := by
      rw [hmid_eq]; have h1 : I.left ≤ 1 := I.left_mem.2; have h2 : I.right ≤ 1 := I.right_mem.2; linarith
    let midP : UnitPoint := ⟨I.midpoint, hmid0, hmid1⟩
    have hlen_nonneg : 0 ≤ I.length := by
      simp [ParameterInterval.length, I.left_le_right] <;> linarith
    have hmid_in : midP ∈ I.centeredCarrier (1 / 2) := by
      simp only [ParameterInterval.centeredCarrier, Set.mem_setOf_eq]
      have h : |I.midpoint - I.midpoint| ≤ (1 / 2 : ℝ) * I.length / 2 := by
        have h2 : (1 / 2 : ℝ) * I.length / 2 ≥ 0 := by positivity
        simpa using h2
      exact h
    have hS_nonempty : S.Nonempty :=
      ⟨|f midP - g midP| + |f.firstDeriv midP - g.firstDeriv midP|, midP, hmid_in, rfl⟩
    have h0 : ∀ r ∈ S, 0 ≤ r := fun r hr => by
      rcases hr with ⟨y, _, rfl⟩
      positivity
    exact le_csInf hS_nonempty h0

  have hH''_abs : ∀ r ∈ Set.Icc I.left I.right, t / (6 * K) ≤ |deriv (deriv H) r| := by
    intro r hr
    let z : UnitPoint := ⟨r, ⟨by linarith [I.left_mem.1, hr.1], by linarith [I.right_mem.2, hr.2]⟩⟩
    have hz : z ∈ I.carrier := by
      simp only [ParameterInterval.carrier, Set.mem_setOf_eq] <;> exact hr
    have h1 : deriv (deriv H) r = f.secondDeriv z - g.secondDeriv z := h_deriv2_eval z
    rw [h1]
    have h9 : t / (6 * K) = (6 * K)⁻¹ * t := by
      field_simp [show (0 : ℝ) < K by linarith] <;> ring
    rw [h9]; exact h_large'' z hz

  have hH''_ne_zero : ∀ r ∈ Set.Icc I.left I.right, deriv (deriv H) r ≠ 0 := by
    intro r hr h
    have h1 : t / (6 * K) ≤ |deriv (deriv H) r| := hH''_abs r hr
    rw [h] at h1
    have h2 : 0 < t / (6 * K) := by positivity
    linarith
  have hH''_sign : (∀ r ∈ Set.Icc I.left I.right, 0 < deriv (deriv H) r) ∨
      (∀ r ∈ Set.Icc I.left I.right, deriv (deriv H) r < 0) :=
    constant_sign_of_never_zero I.left_le_right
      hH''_cont.continuousOn hH''_ne_zero

  let E : Set UnitPoint := tangencySublevelSetOn I f g delta
  let Ehalf : Set UnitPoint := tangencySublevelSetOn I f g (delta / 2)

  rcases hH''_sign with (hH''_pos | hH''_neg)

  · -- Case 1: H'' > 0 (convex)
    set m : ℝ := t / (6 * K) with hm_def
    have hH''_ge : ∀ r ∈ Set.Icc I.left I.right, m ≤ deriv (deriv H) r := by
      intro r hr
      have h_pos : 0 < deriv (deriv H) r := hH''_pos r hr
      have h2 : m ≤ |deriv (deriv H) r| := hH''_abs r hr
      rw [abs_of_pos h_pos] at h2; exact h2
    have H_conv : ConvexOn ℝ (Set.Icc I.left I.right) H :=
      convexOn_of_deriv2_nonneg' (convex_Icc I.left I.right)
        hH1.differentiableOn hH2diff.differentiableOn
        (fun x hx => le_trans (show 0 ≤ m by positivity) (hH''_ge x hx))

    let c : ℝ := I.midpoint - I.length / 8
    let d : ℝ := I.midpoint + I.length / 8
    have hmid : I.midpoint = (I.left + I.right) / 2 := by rfl
    have hlen : I.length = I.right - I.left := by rfl
    have hcd : c ≤ d := by
      dsimp only [c, d]; linarith [I.length_nonneg]
    have hc : I.left ≤ c := by
      dsimp only [c]; rw [hmid, hlen]; linarith [I.left_le_right]
    have hd : d ≤ I.right := by
      dsimp only [d]; rw [hmid, hlen]; linarith [I.left_le_right]
    have hc0 : 0 ≤ c := by
      dsimp only [c]; rw [hmid, hlen]; linarith [I.left_mem.1, I.right_mem.1]
    have hd1 : d ≤ 1 := by
      dsimp only [d]; rw [hmid, hlen]; linarith [I.left_mem.2, I.right_mem.2]

    rcases convex_sublevel_decompose I.left_le_right hcd hc hd hH_cont H_conv hdelta hc0 hd1
      with ⟨pieces, h_card, h_union_eq, h_disjoint⟩

    have hE_eq : E = pieces.union := by
      ext x
      simp only [E, tangencySublevelSetOn, Set.mem_setOf_eq]
      have h1 : x ∈ pieces.union ↔ (x : ℝ) ∈ Set.Icc c d ∧ |H (x : ℝ)| ≤ delta := h_union_eq x
      have h2 : (x : ℝ) ∈ Set.Icc c d ↔ x ∈ I.centeredCarrier (1 / 4) := by
        simp only [ParameterInterval.centeredCarrier, Set.mem_setOf_eq, c, d]
        constructor
        · intro h
          have h5 : |(x : ℝ) - I.midpoint| ≤ I.length / 8 := by
            rw [abs_le] <;> constructor <;> linarith [h.1, h.2]
          have h6 : I.length / 8 = (1 / 4 : ℝ) * I.length / 2 := by ring
          rw [h6] at h5; exact h5
        · intro h
          have h5 : |(x : ℝ) - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := h
          have h6 : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
          rw [h6] at h5
          rw [abs_le] at h5; constructor <;> linarith
      have h3 : |H (x : ℝ)| = |f x - g x| := by rw [h_eval]
      have h4 : x ∈ pieces.union ↔ x ∈ I.centeredCarrier (1 / 4) ∧ |f x - g x| ≤ delta := by
        rw [h1]
        constructor
        · rintro ⟨h5, h6⟩
          have h7 : |f x - g x| ≤ delta := by
            rw [←h3]; exact h6
          exact ⟨h2.mp h5, h7⟩
        · rintro ⟨h5, h6⟩
          have h7 : |H (x : ℝ)| ≤ delta := by
            rw [h3]; exact h6
          exact ⟨h2.mpr h5, h7⟩
      exact h4.symm

    have h_lengths : pieces.AllLengthsLE (C * delta / scale) := by
      intro j
      let J : ParameterInterval := pieces.interval j
      let a : ℝ := J.left
      let b : ℝ := J.right
      have hab : a ≤ b := J.left_le_right
      have ha0 : 0 ≤ a := J.left_mem.1
      have ha1 : a ≤ 1 := J.left_mem.2
      have hb0 : 0 ≤ b := J.right_mem.1
      have hb1 : b ≤ 1 := J.right_mem.2
      have ha_in_union : a ∈ Set.Icc c d := by
        let aP : UnitPoint := ⟨a, ⟨ha0, ha1⟩⟩
        have h_aP_in : aP ∈ J.carrier := by simp [ParameterInterval.carrier] <;> exact ⟨by linarith, by linarith⟩
        have h_in_union : aP ∈ pieces.union := ⟨j, h_aP_in⟩
        exact (h_union_eq _).mp h_in_union |>.1
      have hb_in_union : b ∈ Set.Icc c d := by
        let bP : UnitPoint := ⟨b, ⟨hb0, hb1⟩⟩
        have h_bP_in : bP ∈ J.carrier := by simp [ParameterInterval.carrier] <;> exact ⟨by linarith, by linarith⟩
        have h_in_union : bP ∈ pieces.union := ⟨j, h_bP_in⟩
        exact (h_union_eq _).mp h_in_union |>.1
      have ha_c4 : |a - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := by
        have h7 : a ∈ Set.Icc c d := ha_in_union
        have h8 : |a - I.midpoint| ≤ I.length / 8 := by
          have h9 : c = I.midpoint - I.length / 8 := by rfl
          have h10 : d = I.midpoint + I.length / 8 := by rfl
          rw [abs_le]
          constructor
          · rw [h9] at h7; linarith [h7.1]
          · rw [h10] at h7; linarith [h7.2]
        have h11 : I.length / 8 = (1 / 4 : ℝ) * I.length / 2 := by ring
        rw [h11] at h8; exact h8
      have hb_c4 : |b - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := by
        have h7 : b ∈ Set.Icc c d := hb_in_union
        have h8 : |b - I.midpoint| ≤ I.length / 8 := by
          have h9 : c = I.midpoint - I.length / 8 := by rfl
          have h10 : d = I.midpoint + I.length / 8 := by rfl
          rw [abs_le]
          constructor
          · rw [h9] at h7; linarith [h7.1]
          · rw [h10] at h7; linarith [h7.2]
        have h11 : I.length / 8 = (1 / 4 : ℝ) * I.length / 2 := by ring
        rw [h11] at h8; exact h8
      have hH_bound_J : ∀ x ∈ Set.Icc a b, |H x| ≤ delta := by
        intro x hx
        have hx0 : 0 ≤ x := by linarith [ha0, hx.1]
        have hx1 : x ≤ 1 := by linarith [hb1, hx.2]
        let xP : UnitPoint := ⟨x, ⟨hx0, hx1⟩⟩
        have h_xP_in_J : xP ∈ J.carrier := by simp [ParameterInterval.carrier] <;> exact hx
        have h_xP_in_union : xP ∈ pieces.union := ⟨j, h_xP_in_J⟩
        exact (h_union_eq _).mp h_xP_in_union |>.2
      exact component_length_bound hK hC_large1 ht_pos hdelta hΔ_nonneg
        hscale_def hm_def hI hH1 hH2 hH''_ge hH'_min hdelta_le hab ha0 ha1 hb0 hb1 ha_c4 hb_c4 hH_bound_J

    have hdelta_le' : delta ≤ (6 * K)⁻¹ * t := by
      have h_eq : (6 * K)⁻¹ * t = t / (6 * K) := by
        field_simp [(show (0 : ℝ) < K by linarith).ne'] <;> ring
      rw [h_eq]
      exact hdelta_le
    have h_lower : ∀ (x : UnitPoint), x ∈ Ehalf →
        ∃ (j : Fin pieces.card), x ∈ (pieces.interval j).carrier ∧
          delta ≤ C * scale * (pieces.interval j).length :=
      convex_case_lower_bound hK ht_pos ht_eq hdelta hI h_small h_small' h_large''
        C hC_large2 hscale_def hdelta_le' E Ehalf rfl rfl pieces hE_eq.symm h_card h_disjoint

    refine' ⟨pieces, h_card, hE_eq, h_lengths, h_lower⟩

  · -- Case 2: H'' < 0 (concave), use G = -H
    let G : ℝ → ℝ := fun x => -H x
    have hG1 : Differentiable ℝ G := hH1.neg
    have hG2 : ContDiff ℝ 1 (deriv G) := by
      have h1 : deriv G = fun x => -deriv H x := by
        funext y
        simp [G, deriv_neg]
      rw [h1]; exact hH2.neg
    have hG2diff : Differentiable ℝ (deriv G) := hG2.differentiable (by norm_num)
    have hG_cont : Continuous G := hG1.continuous
    have hG''_eq : ∀ x, deriv (deriv G) x = -deriv (deriv H) x := by
      intro x
      have h1 : deriv G = fun y => -deriv H y := by
        funext y; simp [G, deriv_neg]
      rw [h1]
      simp [deriv_neg]
    set m : ℝ := t / (6 * K) with hm_def
    have hG''_ge : ∀ r ∈ Set.Icc I.left I.right, m ≤ deriv (deriv G) r := by
      intro r hr
      have h_neg : deriv (deriv H) r < 0 := hH''_neg r hr
      have h2 : m ≤ |deriv (deriv H) r| := hH''_abs r hr
      have h3 : deriv (deriv G) r = -deriv (deriv H) r := hG''_eq r
      rw [h3]
      rw [abs_of_neg h_neg] at h2; linarith
    have G_conv : ConvexOn ℝ (Set.Icc I.left I.right) G :=
      convexOn_of_deriv2_nonneg' (convex_Icc I.left I.right)
        hG1.differentiableOn hG2diff.differentiableOn
        (fun x hx => le_trans (show 0 ≤ m by positivity) (hG''_ge x hx))

    let c : ℝ := I.midpoint - I.length / 8
    let d : ℝ := I.midpoint + I.length / 8
    have hmid : I.midpoint = (I.left + I.right) / 2 := by rfl
    have hlen : I.length = I.right - I.left := by rfl
    have hcd : c ≤ d := by
      dsimp only [c, d]; linarith [I.length_nonneg]
    have hc : I.left ≤ c := by
      dsimp only [c]; rw [hmid, hlen]; linarith [I.left_le_right]
    have hd : d ≤ I.right := by
      dsimp only [d]; rw [hmid, hlen]; linarith [I.left_le_right]
    have hc0 : 0 ≤ c := by
      dsimp only [c]; rw [hmid, hlen]; linarith [I.left_mem.1, I.right_mem.1]
    have hd1 : d ≤ 1 := by
      dsimp only [d]; rw [hmid, hlen]; linarith [I.left_mem.2, I.right_mem.2]

    rcases convex_sublevel_decompose I.left_le_right hcd hc hd hG_cont G_conv hdelta hc0 hd1
      with ⟨pieces, h_card, h_union_eq, h_disjoint⟩

    have h_abs_G : ∀ x, |G x| = |H x| := by intro x; simp [G] <;> rfl

    have hE_eq : E = pieces.union := by
      ext x
      simp only [E, tangencySublevelSetOn, Set.mem_setOf_eq]
      have h1 : x ∈ pieces.union ↔ (x : ℝ) ∈ Set.Icc c d ∧ |G (x : ℝ)| ≤ delta := h_union_eq x
      have h2 : (x : ℝ) ∈ Set.Icc c d ↔ x ∈ I.centeredCarrier (1 / 4) := by
        simp only [ParameterInterval.centeredCarrier, Set.mem_setOf_eq, c, d]
        constructor
        · intro h
          have h5 : |(x : ℝ) - I.midpoint| ≤ I.length / 8 := by
            rw [abs_le] <;> constructor <;> linarith [h.1, h.2]
          have h6 : I.length / 8 = (1 / 4 : ℝ) * I.length / 2 := by ring
          rw [h6] at h5; exact h5
        · intro h
          have h5 : |(x : ℝ) - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := h
          have h6 : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
          rw [h6] at h5
          rw [abs_le] at h5; constructor <;> linarith
      have h3 : |G (x : ℝ)| = |f x - g x| := by
        rw [h_abs_G, h_eval]
      have h4 : x ∈ pieces.union ↔ x ∈ I.centeredCarrier (1 / 4) ∧ |f x - g x| ≤ delta := by
        rw [h1]
        constructor
        · rintro ⟨h5, h6⟩
          have h7 : |f x - g x| ≤ delta := by
            rw [←h3]; exact h6
          exact ⟨h2.mp h5, h7⟩
        · rintro ⟨h5, h6⟩
          have h7 : |G (x : ℝ)| ≤ delta := by
            rw [h3]; exact h6
          exact ⟨h2.mpr h5, h7⟩
      exact h4.symm

    have hG'_min : ∀ (x : UnitPoint), x ∈ I.centeredCarrier (1 / 2) →
        |G (x : ℝ)| + |deriv G (x : ℝ)| ≥ Δ := by
      intro x hx
      have h1 : |G (x : ℝ)| = |H (x : ℝ)| := by simp [G] <;> rfl
      have h2 : |deriv G (x : ℝ)| = |deriv H (x : ℝ)| := by
        have h_derivG : deriv G = fun y => -deriv H y := by
          funext y
          simp [G, deriv_neg]
        have h3 : deriv G (x : ℝ) = -deriv H (x : ℝ) := by
          rw [h_derivG] <;> rfl
        rw [h3, abs_neg]
      rw [h1, h2]; exact hH'_min x hx

    have h_lengths : pieces.AllLengthsLE (C * delta / scale) := by
      intro j
      let J : ParameterInterval := pieces.interval j
      let a : ℝ := J.left
      let b : ℝ := J.right
      have hab : a ≤ b := J.left_le_right
      have ha0 : 0 ≤ a := J.left_mem.1
      have ha1 : a ≤ 1 := J.left_mem.2
      have hb0 : 0 ≤ b := J.right_mem.1
      have hb1 : b ≤ 1 := J.right_mem.2
      have ha_in_union : a ∈ Set.Icc c d := by
        let aP : UnitPoint := ⟨a, ⟨ha0, ha1⟩⟩
        have h_aP_in : aP ∈ J.carrier := by simp [ParameterInterval.carrier] <;> exact ⟨by linarith, by linarith⟩
        have h_in_union : aP ∈ pieces.union := ⟨j, h_aP_in⟩
        exact (h_union_eq _).mp h_in_union |>.1
      have hb_in_union : b ∈ Set.Icc c d := by
        let bP : UnitPoint := ⟨b, ⟨hb0, hb1⟩⟩
        have h_bP_in : bP ∈ J.carrier := by simp [ParameterInterval.carrier] <;> exact ⟨by linarith, by linarith⟩
        have h_in_union : bP ∈ pieces.union := ⟨j, h_bP_in⟩
        exact (h_union_eq _).mp h_in_union |>.1
      have ha_c4 : |a - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := by
        have h7 : a ∈ Set.Icc c d := ha_in_union
        have h8 : |a - I.midpoint| ≤ I.length / 8 := by
          have h9 : c = I.midpoint - I.length / 8 := by rfl
          have h10 : d = I.midpoint + I.length / 8 := by rfl
          rw [abs_le]
          constructor
          · rw [h9] at h7; linarith [h7.1]
          · rw [h10] at h7; linarith [h7.2]
        have h11 : I.length / 8 = (1 / 4 : ℝ) * I.length / 2 := by ring
        rw [h11] at h8; exact h8
      have hb_c4 : |b - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := by
        have h7 : b ∈ Set.Icc c d := hb_in_union
        have h8 : |b - I.midpoint| ≤ I.length / 8 := by
          have h9 : c = I.midpoint - I.length / 8 := by rfl
          have h10 : d = I.midpoint + I.length / 8 := by rfl
          rw [abs_le]
          constructor
          · rw [h9] at h7; linarith [h7.1]
          · rw [h10] at h7; linarith [h7.2]
        have h11 : I.length / 8 = (1 / 4 : ℝ) * I.length / 2 := by ring
        rw [h11] at h8; exact h8
      have hG_bound_J : ∀ x ∈ Set.Icc a b, |G x| ≤ delta := by
        intro x hx
        have hx0 : 0 ≤ x := by linarith [ha0, hx.1]
        have hx1 : x ≤ 1 := by linarith [hb1, hx.2]
        let xP : UnitPoint := ⟨x, ⟨hx0, hx1⟩⟩
        have h_xP_in_J : xP ∈ J.carrier := by simp [ParameterInterval.carrier] <;> exact hx
        have h_xP_in_union : xP ∈ pieces.union := ⟨j, h_xP_in_J⟩
        exact (h_union_eq _).mp h_xP_in_union |>.2
      exact component_length_bound hK hC_large1 ht_pos hdelta hΔ_nonneg
        hscale_def hm_def hI hG1 hG2 hG''_ge hG'_min hdelta_le hab ha0 ha1 hb0 hb1 ha_c4 hb_c4 hG_bound_J

    have hdelta_le' : delta ≤ (6 * K)⁻¹ * t := by
      have h_eq : (6 * K)⁻¹ * t = t / (6 * K) := by
        field_simp [(show (0 : ℝ) < K by linarith).ne'] <;> ring
      rw [h_eq]
      exact hdelta_le
    have h_lower : ∀ (x : UnitPoint), x ∈ Ehalf →
        ∃ (j : Fin pieces.card), x ∈ (pieces.interval j).carrier ∧
          delta ≤ C * scale * (pieces.interval j).length :=
      convex_case_lower_bound hK ht_pos ht_eq hdelta hI h_small h_small' h_large''
        C hC_large2 hscale_def hdelta_le' E Ehalf rfl rfl pieces hE_eq.symm h_card h_disjoint

    refine' ⟨pieces, h_card, hE_eq, h_lengths, h_lower⟩

end Kakeya.Cinematic
