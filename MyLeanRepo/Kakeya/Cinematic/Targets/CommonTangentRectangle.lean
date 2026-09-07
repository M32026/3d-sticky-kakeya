import MyLeanRepo.Kakeya.Cinematic.Targets.TangencySublevelDiameter.Helpers
import MyLeanRepo.Kakeya.Cinematic.Targets.CommonTangentRectangleHelpers
import MyLeanRepo.Kakeya.Cinematic.Targets.CommonTangentRectangleMain
import MyLeanRepo.Kakeya.Cinematic.Targets.CommonTangentRectangleRobust
import MyLeanRepo.Kakeya.Cinematic.Statements

/-!
# PYZ Lemma 17: a common tangent rectangle controls tangency (corrected proof)

Proof structure:
1. Setup
2. Case 1: d ≤ 360K*sqrt(δt)
3. Case 2a: Δ > d/(12K) → contradiction
4. Case 2b: Δ ≤ d/(12K)
   a. H'' constant sign, |H''| ≥ d/(2K)
   b. H' has zero in J: bound via Taylor
   c. H' constant sign on J: geometric constraint + algebra
-/

namespace Kakeya.Cinematic

/-
theorem common_tangent_rectangle_controls_parameter :
    CommonTangentRectangleStatement := by
  intro K D hK hD
  use 270000 * K^2
  constructor
  · have h1 : 0 < K := by linarith
    positivity
  intro family hfam I hI delta t hδ hδt ht R hRfam hRcentral f hf g hg hfg hftan hgtan

  set d : ℝ := c2Distance f g with hd_def
  set Δ : ℝ := tangencyParameterOn I f g with hΔ_def
  set L : ℝ := R.interval.length with hL_def

  have hK_pos : 0 < K := by linarith
  have hδ_pos : 0 < delta := hδ
  have ht_pos : 0 < t := by linarith

  have hd_pos : 0 < d := by
    have h : 0 < dist f g := dist_pos.mpr hfg
    simpa [hd_def, c2Distance_eq_dist] using h

  have hd_le_K : d ≤ K := hfam.1 hf hg
  have hL_eq : L = Real.sqrt (delta / t) := R.interval_length
  have hL_pos : 0 < L := by
    rw [hL_eq]; apply Real.sqrt_pos.mpr; positivity

  -- R.interval.length ≤ I.length / 4
  have hL_le_I4 : L ≤ I.length / 4 := by
    let a_lp : UnitPoint := ⟨R.interval.left, R.interval.left_mem⟩
    let b_lp : UnitPoint := ⟨R.interval.right, R.interval.right_mem⟩
    have ha_in : a_lp ∈ R.interval.carrier := by
      exact ⟨by simp [a_lp], R.interval.left_le_right⟩
    have hb_in : b_lp ∈ R.interval.carrier := by
      exact ⟨R.interval.left_le_right, by simp [b_lp]⟩
    have ha_center : a_lp ∈ I.centeredCarrier (1 / 4) := hRcentral ha_in
    have hb_center : b_lp ∈ I.centeredCarrier (1 / 4) := hRcentral hb_in
    have h1 : |R.interval.left - I.midpoint| ≤ I.length / 8 := by
      have h_raw : |(a_lp : ℝ) - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := ha_center
      have h_eq1 : (a_lp : ℝ) = R.interval.left := by simp [a_lp]
      have h_eq2 : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
      rw [h_eq1, h_eq2] at h_raw
      exact h_raw
    have h2 : |R.interval.right - I.midpoint| ≤ I.length / 8 := by
      have h_raw : |(b_lp : ℝ) - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := hb_center
      have h_eq1 : (b_lp : ℝ) = R.interval.right := by simp [b_lp]
      have h_eq2 : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
      rw [h_eq1, h_eq2] at h_raw
      exact h_raw
    have h9 : L = R.interval.right - R.interval.left := by
      simp [hL_def, ParameterInterval.length]
    rw [h9]
    have h_left_ge : R.interval.left ≥ I.midpoint - I.length / 8 := by
      have h4 : -(I.length / 8) ≤ R.interval.left - I.midpoint := (abs_le.mp h1).1
      linarith
    have h_right_le : R.interval.right ≤ I.midpoint + I.length / 8 := by
      have h5 : R.interval.right - I.midpoint ≤ I.length / 8 := (abs_le.mp h2).2
      linarith
    have h_main : R.interval.right - R.interval.left ≤ I.length / 4 := by linarith
    exact h_main

  have hI_short : I.length ≤ 1 / (6 * K) := by
    have h : I.IsShort K := hI.2
    simpa [ParameterInterval.IsShort] using h

  have hI_long : I.length ≥ 1 / (12 * K) := by
    have h : I.IsControlled K := hI
    simpa [ParameterInterval.IsControlled] using h.1

  have hL_le : L ≤ 1 / (24 * K) := by
    calc L ≤ I.length / 4 := hL_le_I4
         _ ≤ (1 / (6 * K)) / 4 := by gcongr
         _ = 1 / (24 * K) := by ring

  -- |f x - g x| ≤ 10δ on R.interval
  have hfg_bound : ∀ (x : UnitPoint), x ∈ R.interval.carrier → |f x - g x| ≤ 10 * delta := by
    intro x hx
    let p : UnitPoint × ℝ := (x, R.function x)
    have hp_in_R : p ∈ R.carrier := by
      simp only [CurvilinearRectangle.carrier, Set.mem_setOf_eq]
      have h_abs : |R.function x - R.function x| ≤ delta := by
        have h : R.function x - R.function x = 0 := by simp
        rw [h]
        simpa using hδ_pos.le
      exact ⟨hx, h_abs⟩
    have h1 : |R.function x - f x| ≤ 5 * delta := hftan p hp_in_R
    have h2 : |R.function x - g x| ≤ 5 * delta := hgtan p hp_in_R
    have h3 : |f x - g x| ≤ |f x - R.function x| + |R.function x - g x| := by
      set a := f x - R.function x with ha
      set b := R.function x - g x with hb
      have h_eq : f x - g x = a + b := by simp [ha, hb] <;> ring
      rw [h_eq]
      have h1 : a + b ≤ |a| + |b| := by linarith [le_abs_self a, le_abs_self b]
      have h2 : -(a + b) ≤ |a| + |b| := by linarith [neg_abs_le a, neg_abs_le b]
      have h2' : -(|a| + |b|) ≤ a + b := by linarith
      exact abs_le.mpr ⟨h2', h1⟩
    have h4 : |f x - R.function x| = |R.function x - f x| := by rw [abs_sub_comm]
    rw [h4] at h3
    linarith

  have hΔ_le_2d : Δ ≤ 2 * d := by
    rcases tangency_parameter_attained I f g with ⟨x0, hx0, h_eq⟩
    have h1 : |f x0 - g x0| ≤ d := abs_value_sub_le_c2Distance f g x0
    have h2 : |f.firstDeriv x0 - g.firstDeriv x0| ≤ d := abs_firstDeriv_sub_le_c2Distance f g x0
    linarith [h_eq]

  have hΔ_nonneg : 0 ≤ Δ := by
    rcases tangency_parameter_attained I f g with ⟨x0, _, h_eq⟩
    have h : 0 ≤ |f x0 - g x0| + |f.firstDeriv x0 - g.firstDeriv x0| := by positivity
    linarith [h_eq]

  -- Common differentiability facts
  let H : ℝ → ℝ := f.extension - g.extension
  have hH_c2 : ContDiff ℝ 2 H := f.extension_contDiff.sub g.extension_contDiff
  have hH_diff1 : Differentiable ℝ H := hH_c2.differentiable (by norm_num)
  have hH2_c2 : ContDiff ℝ 1 (deriv H) := hH_c2.deriv'
  have hH_diff2 : Differentiable ℝ (deriv H) := hH2_c2.differentiable (by norm_num)
  have h_f_diff : Differentiable ℝ f.extension := f.extension_contDiff.differentiable (by norm_num)
  have h_g_diff : Differentiable ℝ g.extension := g.extension_contDiff.differentiable (by norm_num)
  have h_f2_diff : Differentiable ℝ (deriv f.extension) :=
    (ContDiff.deriv' (n := 1) f.extension_contDiff).differentiable (by norm_num)
  have h_g2_diff : Differentiable ℝ (deriv g.extension) :=
    (ContDiff.deriv' (n := 1) g.extension_contDiff).differentiable (by norm_num)
  have h_deriv_eq : ∀ (z : ℝ), deriv H z = deriv f.extension z - deriv g.extension z := by
    intro z; exact deriv_sub (h_f_diff z) (h_g_diff z)
  have hH''_eq : ∀ (z : UnitPoint), deriv (deriv H) (z : ℝ) = f.secondDeriv z - g.secondDeriv z := by
    have h1 : deriv H = deriv f.extension - deriv g.extension := by
      funext w; exact deriv_sub (h_f_diff w) (h_g_diff w)
    have h2 : deriv (deriv H) = deriv (deriv f.extension) - deriv (deriv g.extension) := by
      rw [h1]
      funext x
      exact deriv_sub (h_f2_diff x) (h_g2_diff x)
    intro z
    have h3 : deriv (deriv H) (z : ℝ) = deriv (deriv f.extension) (z : ℝ) - deriv (deriv g.extension) (z : ℝ) := by
      rw [h2] <;> rfl
    rw [h3]
    have h4 : deriv (deriv f.extension) (z : ℝ) = f.secondDeriv z :=
      C2Function.secondDeriv_extension_eq_secondDeriv f z
    have h5 : deriv (deriv g.extension) (z : ℝ) = g.secondDeriv z :=
      C2Function.secondDeriv_extension_eq_secondDeriv g z
    rw [h4, h5] <;> abel

  -- |H''(x)| ≤ d for x ∈ I
  have hH''_abs_le_d : ∀ (x : ℝ), x ∈ Set.Icc I.left I.right → |deriv (deriv H) x| ≤ d := by
    intro x hx
    have hx1 : 0 ≤ x := by linarith [I.left_mem.1, hx.1]
    have hx2 : x ≤ 1 := by linarith [I.right_mem.2, hx.2]
    let xp : UnitPoint := ⟨x, ⟨hx1, hx2⟩⟩
    have h5 : deriv (deriv H) x = f.secondDeriv xp - g.secondDeriv xp := hH''_eq xp
    rw [h5]
    exact abs_secondDeriv_sub_le_c2Distance f g xp

  -- Pointwise lower bound from Δ
  have hΔ_pointwise : ∀ (x : UnitPoint), x ∈ I.centeredCarrier (1 / 2) →
      |f x - g x| + |f.firstDeriv x - g.firstDeriv x| ≥ Δ := by
    intro x hx
    let S := I.centeredCarrier (1 / 2)
    let F : UnitPoint → ℝ := fun y => |f y - g y| + |f.firstDeriv y - g.firstDeriv y|
    have hS_nonempty : S.Nonempty := ⟨x, hx⟩
    have h_bdd : BddBelow (F '' S) := by
      use 0; intro r hr; rcases hr with ⟨y, _, rfl⟩; positivity
    have h_in : F x ∈ F '' S := ⟨x, hx, rfl⟩
    have h_eq1 : tangencyParameterOn I f g = sInf (F '' S) := by
      unfold tangencyParameterOn
      congr
      ext r
      simp [F, S, Set.mem_image, Set.mem_setOf_eq] <;> aesop
    rw [hΔ_def, h_eq1]
    exact csInf_le h_bdd h_in

  have hR_sub_half : R.interval.carrier ⊆ I.centeredCarrier (1 / 2) := by
    intro x hx
    have h1 : x ∈ I.centeredCarrier (1 / 4) := hRcentral hx
    have h3 : |(x : ℝ) - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := h1
    have h4 : (1 / 4 : ℝ) * I.length / 2 ≤ (1 / 2 : ℝ) * I.length / 2 := by gcongr <;> linarith
    have h5 : |(x : ℝ) - I.midpoint| ≤ (1 / 2 : ℝ) * I.length / 2 := le_trans h3 h4
    exact h5

  -- Endpoint values of H
  let a : ℝ := R.interval.left
  let b : ℝ := R.interval.right
  have hab : a ≤ b := R.interval.left_le_right
  have h_ab_lt : a < b := by
    have h1 : b - a = L := by simp [a, b, hL_def, ParameterInterval.length] <;> ring
    have h2 : 0 < b - a := by rw [h1] <;> exact hL_pos
    linarith

  have ha_in_I : a ∈ Set.Icc I.left I.right := by
    let a_lp : UnitPoint := ⟨a, R.interval.left_mem⟩
    have a_lp_in_R : a_lp ∈ R.interval.carrier := by exact ⟨by linarith, R.interval.left_le_right⟩
    have a_lp_center : a_lp ∈ I.centeredCarrier (1 / 4) := hRcentral a_lp_in_R
    have h : a_lp ∈ I.carrier :=
      I.centeredCarrier_subset_carrier (by norm_num) (by norm_num) a_lp_center
    exact ⟨h.1, h.2⟩

  have hb_in_I : b ∈ Set.Icc I.left I.right := by
    let b_lp : UnitPoint := ⟨b, R.interval.right_mem⟩
    have b_lp_in_R : b_lp ∈ R.interval.carrier := by exact ⟨R.interval.left_le_right, by linarith⟩
    have b_lp_center : b_lp ∈ I.centeredCarrier (1 / 4) := hRcentral b_lp_in_R
    have h : b_lp ∈ I.carrier :=
      I.centeredCarrier_subset_carrier (by norm_num) (by norm_num) b_lp_center
    exact ⟨h.1, h.2⟩

  have hHa_bound : |H a| ≤ 10 * delta := by
    have ha1 : 0 ≤ a := R.interval.left_mem.1
    have ha2 : a ≤ 1 := R.interval.left_mem.2
    let ap : UnitPoint := ⟨a, ⟨ha1, ha2⟩⟩
    have hap_in : ap ∈ R.interval.carrier := ⟨by linarith, by linarith⟩
    have hHa : H a = f ap - g ap := by
      have h : H a = f.extension a - g.extension a := by simp [H] <;> rfl
      rw [h]
      have hf : f.extension a = f ap := C2Function.extension_eq_value f ap
      have hg : g.extension a = g ap := C2Function.extension_eq_value g ap
      rw [hf, hg] <;> abel
    rw [hHa]
    exact hfg_bound ap hap_in

  have hHb_bound : |H b| ≤ 10 * delta := by
    have hb1 : 0 ≤ b := R.interval.right_mem.1
    have hb2 : b ≤ 1 := R.interval.right_mem.2
    let bp : UnitPoint := ⟨b, ⟨hb1, hb2⟩⟩
    have hbp_in : bp ∈ R.interval.carrier := ⟨by linarith, by linarith⟩
    have hHb : H b = f bp - g bp := by
      have h : H b = f.extension b - g.extension b := by simp [H] <;> rfl
      rw [h]
      have hf : f.extension b = f bp := C2Function.extension_eq_value f bp
      have hg : g.extension b = g bp := C2Function.extension_eq_value g bp
      rw [hf, hg] <;> abel
    rw [hHb]
    exact hfg_bound bp hbp_in

  have h_var_bound : |H b - H a| ≤ 20 * delta := by
    have h3 : |H b - H a| ≤ |H b| + |H a| := by
      have h : |H b - H a| ≤ |H b| + |(-H a)| := by
        exact abs_add_le (H b) (-H a)
      have h' : |(-H a)| = |H a| := by rw [abs_neg]
      rw [h'] at h
      exact h
    linarith [hHa_bound, hHb_bound]

  by_cases hCase1 : d ≤ 360 * K * Real.sqrt (delta * t)

  · -- Case 1: d small
    have h1 : 2 * d^2 ≤ 259200 * K^2 * delta * t := by
      have h2 : d ≤ 360 * K * Real.sqrt (delta * t) := hCase1
      have h3 : 0 ≤ delta * t := by positivity
      nlinarith [Real.sq_sqrt h3]
    have h_sqrt_le : Real.sqrt (delta / t) ≤ 1 / (24 * K) := by
      rw [hL_eq.symm] <;> exact hL_le
    have h5 : delta * d ≤ 15 * delta * t := by
      have h6 : d ≤ 360 * K * Real.sqrt (delta * t) := hCase1
      have h7 : Real.sqrt (delta * t) = Real.sqrt (delta / t) * t := by
        have h8 : 0 < t := ht_pos
        have h9 : delta * t = delta / t * t^2 := by field_simp [h8.ne'] <;> ring
        rw [h9]
        rw [Real.sqrt_mul (by positivity)]
        have h10 : Real.sqrt (t^2) = t := by
          rw [Real.sqrt_sq_eq_abs] <;> rw [abs_of_pos h8]
        rw [h10] <;> ring
      have h8 : delta * d ≤ 360 * K * Real.sqrt (delta / t) * (delta * t) := by
        calc
          delta * d ≤ delta * (360 * K * Real.sqrt (delta * t)) := by gcongr
          _ = 360 * K * delta * (Real.sqrt (delta / t) * t) := by rw [h7] <;> ring
          _ = 360 * K * Real.sqrt (delta / t) * (delta * t) := by ring
      have h10 : Real.sqrt (delta / t) ≤ 1 / (24 * K) := h_sqrt_le
      calc
        delta * d
          ≤ 360 * K * Real.sqrt (delta / t) * (delta * t) := h8
        _ ≤ 360 * K * (1 / (24 * K)) * (delta * t) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h10 (by positivity)) (by positivity)
        _ = 15 * (delta * t) := by field_simp [hK_pos.ne'] <;> ring
        _ = 15 * delta * t := by ring
    have h11 : (Δ + delta) * d ≤ (2 * d + delta) * d := by gcongr <;> linarith [hΔ_le_2d]
    have h12 : (2 * d + delta) * d = 2 * d^2 + delta * d := by ring
    rw [h12] at h11
    have h13 : 2 * d^2 + delta * d ≤ 270000 * K^2 * delta * t := by
      have h14 : delta * d ≤ 15 * K^2 * delta * t := by
        have h15 : delta * d ≤ 15 * delta * t := h5
        have h16 : 1 ≤ K^2 := by nlinarith
        have h17 : 0 ≤ delta * t := by positivity
        have h18 : 15 * delta * t ≤ 15 * K^2 * delta * t := by
          calc 15 * delta * t = 15 * 1 * (delta * t) := by ring
               _ ≤ 15 * K^2 * (delta * t) := by gcongr <;> nlinarith
               _ = 15 * K^2 * delta * t := by ring
        linarith
      have h19 : 2 * d^2 + delta * d ≤ 259200 * K^2 * delta * t + 15 * K^2 * delta * t := by linarith
      have h20 : 259200 * K^2 * delta * t + 15 * K^2 * delta * t ≤ 270000 * K^2 * delta * t := by
        have h21 : 0 ≤ K^2 * delta * t := by positivity
        linarith
      linarith
    linarith

  · -- Case 2: d > 360K * sqrt(delta * t)
    have hCase2 : d > 360 * K * Real.sqrt (delta * t) := by linarith

    have h_sqrt_ge_delta : Real.sqrt (delta * t) ≥ delta := by
      have h2 : delta^2 ≤ delta * t := by nlinarith
      have h3 : 0 ≤ delta := by linarith
      have h4 : Real.sqrt (delta^2) ≤ Real.sqrt (delta * t) := Real.sqrt_le_sqrt h2
      have h5 : Real.sqrt (delta^2) = delta := by
        rw [Real.sqrt_sq_eq_abs] <;> rw [abs_of_nonneg (by linarith)]
      linarith

    have h10δ_lt : 10 * delta < d / (12 * K) := by
      have h1 : d > 360 * K * delta := by
        calc d > 360 * K * Real.sqrt (delta * t) := hCase2
             _ ≥ 360 * K * delta := by gcongr <;> exact h_sqrt_ge_delta
      have h2 : d / (12 * K) > 30 * delta := by
        calc d / (12 * K) > (360 * K * delta) / (12 * K) := by gcongr
                      _ = 30 * delta := by field_simp [hK_pos.ne'] <;> ring
      linarith

    by_cases h2a : Δ > d / (12 * K)

    · -- Sub-case 2a: contradiction
      have hH'_cont : ContinuousOn (deriv H) (Set.Icc a b) := hH2_c2.continuous.continuousOn

      have hH'_ne : ∀ (x : ℝ), x ∈ Set.Icc a b → deriv H x ≠ 0 := by
        intro x hx
        have hx1 : 0 ≤ x := by linarith [R.interval.left_mem.1, hx.1]
        have hx2 : x ≤ 1 := by linarith [R.interval.right_mem.2, hx.2]
        let xp : UnitPoint := ⟨x, ⟨hx1, hx2⟩⟩
        have hxp_in : xp ∈ R.interval.carrier := ⟨hx.1, hx.2⟩
        have hderiv : deriv H x = f.firstDeriv xp - g.firstDeriv xp := by
          rw [h_deriv_eq x]
          have h1 : deriv f.extension x = f.firstDeriv xp := C2Function.deriv_extension_eq_firstDeriv f xp
          have h2 : deriv g.extension x = g.firstDeriv xp := C2Function.deriv_extension_eq_firstDeriv g xp
          rw [h1, h2]
        rw [hderiv]
        have h3 : |f xp - g xp| + |f.firstDeriv xp - g.firstDeriv xp| ≥ Δ :=
          hΔ_pointwise xp (hR_sub_half hxp_in)
        have h4 : |f xp - g xp| ≤ 10 * delta := hfg_bound xp hxp_in
        have h5 : |f.firstDeriv xp - g.firstDeriv xp| ≥ Δ - 10 * delta := by linarith
        have h6 : 0 < |f.firstDeriv xp - g.firstDeriv xp| := by
          have h7 : Δ - 10 * delta > 0 := by linarith [h10δ_lt, h2a]
          linarith
        exact abs_pos.mp h6

      have h_sign : (∀ x ∈ Set.Icc a b, 0 < deriv H x) ∨
          (∀ x ∈ Set.Icc a b, deriv H x < 0) :=
        constant_sign_of_never_zero hab hH'_cont hH'_ne

      have h_abs_diff : |H b - H a| ≥ (Δ - 10 * delta) * L := by
        rcases h_sign with (h_pos | h_neg)
        · rcases exists_hasDerivAt_eq_slope (f := H) (f' := deriv H)
              h_ab_lt hH_diff1.continuous.continuousOn
              (fun z _ => hH_diff1.differentiableAt.hasDerivAt)
            with ⟨c, hc, hderiv⟩
          have hc' : c ∈ Set.Icc a b := ⟨by linarith [hc.1], by linarith [hc.2]⟩
          have hc1 : 0 ≤ c := by linarith [R.interval.left_mem.1, hc.1]
          have hc2 : c ≤ 1 := by linarith [R.interval.right_mem.2, hc.2]
          let cp : UnitPoint := ⟨c, ⟨hc1, hc2⟩⟩
          have hcp_in : cp ∈ R.interval.carrier := ⟨by linarith [hc.1], by linarith [hc.2]⟩
          have h2 : |f.firstDeriv cp - g.firstDeriv cp| ≥ Δ - 10 * delta := by
            have h3 : |f cp - g cp| + |f.firstDeriv cp - g.firstDeriv cp| ≥ Δ :=
              hΔ_pointwise cp (hR_sub_half hcp_in)
            have h4 : |f cp - g cp| ≤ 10 * delta := hfg_bound cp hcp_in
            linarith
          have h5 : deriv H c = f.firstDeriv cp - g.firstDeriv cp := by
            rw [h_deriv_eq c]
            have h6 : deriv f.extension c = f.firstDeriv cp := C2Function.deriv_extension_eq_firstDeriv f cp
            have h7 : deriv g.extension c = g.firstDeriv cp := C2Function.deriv_extension_eq_firstDeriv g cp
            rw [h6, h7]
          have h7 : 0 < f.firstDeriv cp - g.firstDeriv cp := by rw [←h5] <;> exact h_pos c hc'
          have h8 : |f.firstDeriv cp - g.firstDeriv cp| = f.firstDeriv cp - g.firstDeriv cp := abs_of_pos h7
          have h9 : f.firstDeriv cp - g.firstDeriv cp ≥ Δ - 10 * delta := by rw [←h8] <;> exact h2
          have h10 : deriv H c ≥ Δ - 10 * delta := by linarith [h5]
          have h_ne : b - a ≠ 0 := by linarith
          have h11 : H b - H a = deriv H c * (b - a) := by
            have h12 : deriv H c * (b - a) = (H b - H a) / (b - a) * (b - a) := by rw [hderiv]
            have h13 : (H b - H a) / (b - a) * (b - a) = H b - H a := by field_simp [h_ne] <;> ring
            linarith
          have h14 : b - a = L := by simp [a, b, hL_def, ParameterInterval.length] <;> ring
          rw [h11, h14]
          have h15 : 0 ≤ deriv H c := by linarith
          have h16 : |deriv H c * L| = deriv H c * L := by rw [abs_of_nonneg (by positivity)]
          rw [h16]; gcongr
        · rcases exists_hasDerivAt_eq_slope (f := H) (f' := deriv H)
              h_ab_lt hH_diff1.continuous.continuousOn
              (fun z _ => hH_diff1.differentiableAt.hasDerivAt)
            with ⟨c, hc, hderiv⟩
          have hc' : c ∈ Set.Icc a b := ⟨by linarith [hc.1], by linarith [hc.2]⟩
          have hc1 : 0 ≤ c := by linarith [R.interval.left_mem.1, hc.1]
          have hc2 : c ≤ 1 := by linarith [R.interval.right_mem.2, hc.2]
          let cp : UnitPoint := ⟨c, ⟨hc1, hc2⟩⟩
          have hcp_in : cp ∈ R.interval.carrier := ⟨by linarith [hc.1], by linarith [hc.2]⟩
          have h2 : |f.firstDeriv cp - g.firstDeriv cp| ≥ Δ - 10 * delta := by
            have h3 : |f cp - g cp| + |f.firstDeriv cp - g.firstDeriv cp| ≥ Δ :=
              hΔ_pointwise cp (hR_sub_half hcp_in)
            have h4 : |f cp - g cp| ≤ 10 * delta := hfg_bound cp hcp_in
            linarith
          have h5 : deriv H c = f.firstDeriv cp - g.firstDeriv cp := by
            rw [h_deriv_eq c]
            have h6 : deriv f.extension c = f.firstDeriv cp := C2Function.deriv_extension_eq_firstDeriv f cp
            have h7 : deriv g.extension c = g.firstDeriv cp := C2Function.deriv_extension_eq_firstDeriv g cp
            rw [h6, h7]
          have h7 : f.firstDeriv cp - g.firstDeriv cp < 0 := by rw [←h5] <;> exact h_neg c hc'
          have h8 : |f.firstDeriv cp - g.firstDeriv cp| = -(f.firstDeriv cp - g.firstDeriv cp) := abs_of_neg h7
          have h9 : f.firstDeriv cp - g.firstDeriv cp ≤ -(Δ - 10 * delta) := by
            have h10 : |f.firstDeriv cp - g.firstDeriv cp| ≥ Δ - 10 * delta := h2
            have h11 : |f.firstDeriv cp - g.firstDeriv cp| = -(f.firstDeriv cp - g.firstDeriv cp) := h8
            linarith
          have h10 : deriv H c ≤ -(Δ - 10 * delta) := by linarith [h5]
          have h_ne : b - a ≠ 0 := by linarith
          have h11 : H b - H a = deriv H c * (b - a) := by
            have h12 : deriv H c * (b - a) = (H b - H a) / (b - a) * (b - a) := by rw [hderiv]
            have h13 : (H b - H a) / (b - a) * (b - a) = H b - H a := by field_simp [h_ne] <;> ring
            linarith
          have h14 : b - a = L := by simp [a, b, hL_def, ParameterInterval.length] <;> ring
          have h15 : |H b - H a| = |deriv H c| * L := by
            rw [h11, h14, abs_mul]
            have h16 : |L| = L := abs_of_pos hL_pos
            rw [h16] <;> ring
          rw [h15]
          have h16 : |deriv H c| ≥ Δ - 10 * delta := by
            have h17 : |deriv H c| = -(deriv H c) := abs_of_neg (h_neg c hc')
            rw [h17]; linarith [h10]
          exact mul_le_mul_of_nonneg_right h16 (by linarith)

      have h_contra : (Δ - 10 * delta) * L ≤ 20 * delta := by
        linarith [h_abs_diff, h_var_bound]

      have h_pos : 0 < Δ - 10 * delta := by linarith [h2a, h10δ_lt]
      have h2 : Δ - 10 * delta ≤ 20 * delta / L := by
        calc Δ - 10 * delta
          = ((Δ - 10 * delta) * L) / L := by field_simp [hL_pos.ne'] <;> ring
        _ ≤ (20 * delta) / L := by gcongr
      have h3 : 20 * delta / L = 20 * Real.sqrt (delta * t) := by
        have h4 : L = Real.sqrt (delta / t) := hL_eq
        rw [h4]
        have h5 : 0 < delta := hδ_pos
        have h6 : 0 < t := ht_pos
        have h7 : 0 < Real.sqrt (delta / t) := Real.sqrt_pos.mpr (by positivity)
        have h_sqrt_prod : Real.sqrt (delta / t) * Real.sqrt (delta * t) = delta := by
          have h_prod : (delta / t) * (delta * t) = delta^2 := by field_simp [h6.ne'] <;> ring
          calc
            Real.sqrt (delta / t) * Real.sqrt (delta * t)
              = Real.sqrt ((delta / t) * (delta * t)) := by rw [←Real.sqrt_mul (by positivity)]
            _ = Real.sqrt (delta^2) := by rw [h_prod]
            _ = delta := by rw [Real.sqrt_sq_eq_abs] <;> rw [abs_of_pos h5]
        have h_main : 20 * delta / Real.sqrt (delta / t) = 20 * Real.sqrt (delta * t) := by
          have h8 : 20 * delta = 20 * (Real.sqrt (delta / t) * Real.sqrt (delta * t)) := by rw [h_sqrt_prod] <;> ring
          rw [h8]
          field_simp [h7.ne'] <;> ring
        exact h_main
      have hΔ_le : Δ ≤ 30 * Real.sqrt (delta * t) := by linarith [h2, h3]
      have h_contra2 : d < 360 * K * Real.sqrt (delta * t) := by
        have h9 : d / (12 * K) < Δ := h2a
        have h10 : Δ ≤ 30 * Real.sqrt (delta * t) := hΔ_le
        have h11 : d / (12 * K) < 30 * Real.sqrt (delta * t) := by linarith
        have h12 : d < 360 * K * Real.sqrt (delta * t) := by
          calc d
            = (d / (12 * K)) * (12 * K) := by field_simp [hK_pos.ne'] <;> ring
          _ < (30 * Real.sqrt (delta * t)) * (12 * K) := by gcongr
          _ = 360 * K * Real.sqrt (delta * t) := by ring
        exact h12
      have h_contra : False := by linarith [hCase2, h_contra2]
      exact False.elim h_contra

    · -- Sub-case 2b: Δ ≤ d / (12 * K)
      have h2b : Δ ≤ d / (12 * K) := by linarith

      rcases tangency_parameter_attained I f g with ⟨xΔ, hxΔ_centered, hxΔ_eq⟩
      have hxΔ_carrier : xΔ ∈ I.carrier :=
        I.centeredCarrier_subset_carrier (by norm_num) (by norm_num) hxΔ_centered
      have h_val : |f xΔ - g xΔ| ≤ Δ := by
        have h : |f xΔ - g xΔ| + |f.firstDeriv xΔ - g.firstDeriv xΔ| = Δ := hxΔ_eq
        have hnonneg : 0 ≤ |f.firstDeriv xΔ - g.firstDeriv xΔ| := by positivity
        linarith
      have h_der : |f.firstDeriv xΔ - g.firstDeriv xΔ| ≤ Δ := by
        have h_eq : |f xΔ - g xΔ| + |f.firstDeriv xΔ - g.firstDeriv xΔ| = Δ := hxΔ_eq
        have h_nonneg : 0 ≤ |f xΔ - g xΔ| := abs_nonneg _
        calc |f.firstDeriv xΔ - g.firstDeriv xΔ|
          = |f xΔ - g xΔ| + |f.firstDeriv xΔ - g.firstDeriv xΔ| - |f xΔ - g xΔ| := by ring
        _ = Δ - |f xΔ - g xΔ| := by rw [h_eq] <;> ring
        _ ≤ Δ := sub_le_self Δ h_nonneg

      have h_len : I.length = I.right - I.left := by simp [ParameterInterval.length]
      have h_dist : ∀ (z : UnitPoint), z ∈ I.carrier → |(z : ℝ) - (xΔ : ℝ)| ≤ I.length := by
        intro z hz
        have hz1 : I.left ≤ (z : ℝ) := hz.1
        have hz2 : (z : ℝ) ≤ I.right := hz.2
        have hx1 : I.left ≤ (xΔ : ℝ) := hxΔ_carrier.1
        have hx2 : (xΔ : ℝ) ≤ I.right := hxΔ_carrier.2
        have h5 : (z : ℝ) - (xΔ : ℝ) ≤ I.length := by rw [h_len] <;> linarith
        have h7 : -(I.length) ≤ (z : ℝ) - (xΔ : ℝ) := by rw [h_len] <;> linarith
        exact abs_le.mpr ⟨h7, h5⟩

      have h_H_bound : ∀ (z : UnitPoint), z ∈ I.carrier → |f z - g z| ≤ d / (4 * K) := by
        intro z hz
        have h1 : |(f z - g z) - (f xΔ - g xΔ)| ≤ d * |(z : ℝ) - (xΔ : ℝ)| := lipschitz_value f g z xΔ
        have h2 : |(z : ℝ) - (xΔ : ℝ)| ≤ I.length := h_dist z hz
        have h3 : I.length ≤ 1 / (6 * K) := hI_short
        have h4 : |(f z - g z) - (f xΔ - g xΔ)| ≤ d / (6 * K) := by
          calc
            _ ≤ d * |(z : ℝ) - (xΔ : ℝ)| := h1
            _ ≤ d * I.length := by gcongr
            _ ≤ d * (1 / (6 * K)) := by gcongr
            _ = d / (6 * K) := by ring
        have h5 : |f z - g z| ≤ |f xΔ - g xΔ| + |(f z - g z) - (f xΔ - g xΔ)| := by
          set a := f xΔ - g xΔ with ha
          set b := (f z - g z) - (f xΔ - g xΔ) with hb
          have h_eq : f z - g z = a + b := by simp [ha, hb] <;> ring
          have h_abs : |a + b| ≤ |a| + |b| := abs_add_le a b
          have h' : |f z - g z| = |a + b| := by rw [h_eq]
          rw [h']; exact h_abs
        calc
          |f z - g z|
            ≤ |f xΔ - g xΔ| + |(f z - g z) - (f xΔ - g xΔ)| := h5
          _ ≤ Δ + d / (6 * K) := by gcongr
          _ ≤ d / (12 * K) + d / (6 * K) := by gcongr <;> linarith
          _ = d / (4 * K) := by ring

      have h_H'_bound : ∀ (z : UnitPoint), z ∈ I.carrier → |f.firstDeriv z - g.firstDeriv z| ≤ d / (4 * K) := by
        intro z hz
        have h1 : |(f.firstDeriv z - g.firstDeriv z) - (f.firstDeriv xΔ - g.firstDeriv xΔ)| ≤ d * |(z : ℝ) - (xΔ : ℝ)| :=
          lipschitz_deriv f g z xΔ
        have h2 : |(z : ℝ) - (xΔ : ℝ)| ≤ I.length := h_dist z hz
        have h3 : I.length ≤ 1 / (6 * K) := hI_short
        have h4 : |(f.firstDeriv z - g.firstDeriv z) - (f.firstDeriv xΔ - g.firstDeriv xΔ)| ≤ d / (6 * K) := by
          calc
            _ ≤ d * |(z : ℝ) - (xΔ : ℝ)| := h1
            _ ≤ d * I.length := by gcongr
            _ ≤ d * (1 / (6 * K)) := by gcongr
            _ = d / (6 * K) := by ring
        have h5 : |f.firstDeriv z - g.firstDeriv z| ≤ |f.firstDeriv xΔ - g.firstDeriv xΔ| + |(f.firstDeriv z - g.firstDeriv z) - (f.firstDeriv xΔ - g.firstDeriv xΔ)| := by
          set a := f.firstDeriv xΔ - g.firstDeriv xΔ with ha
          set b := (f.firstDeriv z - g.firstDeriv z) - (f.firstDeriv xΔ - g.firstDeriv xΔ) with hb
          have h_eq : f.firstDeriv z - g.firstDeriv z = a + b := by simp [ha, hb] <;> ring
          have h_abs : |a + b| ≤ |a| + |b| := abs_add_le a b
          have h' : |f.firstDeriv z - g.firstDeriv z| = |a + b| := by rw [h_eq]
          rw [h']; exact h_abs
        calc
          |f.firstDeriv z - g.firstDeriv z|
            ≤ |f.firstDeriv xΔ - g.firstDeriv xΔ| + |(f.firstDeriv z - g.firstDeriv z) - (f.firstDeriv xΔ - g.firstDeriv xΔ)| := h5
          _ ≤ Δ + d / (6 * K) := by gcongr
          _ ≤ d / (12 * K) + d / (6 * K) := by gcongr <;> linarith
          _ = d / (4 * K) := by ring

      have h_H''_bound : ∀ (z : UnitPoint), z ∈ I.carrier → |f.secondDeriv z - g.secondDeriv z| ≥ d / (2 * K) := by
        intro z hz
        have hcurv : K⁻¹ * d ≤ |f z - g z| + |f.firstDeriv z - g.firstDeriv z| + |f.secondDeriv z - g.secondDeriv z| :=
          hfam.2.2 hf hg z
        have h1 : |f z - g z| ≤ d / (4 * K) := h_H_bound z hz
        have h2 : |f.firstDeriv z - g.firstDeriv z| ≤ d / (4 * K) := h_H'_bound z hz
        have h3 : K⁻¹ * d = d / K := by field_simp [hK_pos.ne'] <;> ring
        rw [h3] at hcurv
        have h4 : |f z - g z| + |f.firstDeriv z - g.firstDeriv z| ≤ d / (2 * K) := by
          calc
            |f z - g z| + |f.firstDeriv z - g.firstDeriv z|
              ≤ d / (4 * K) + d / (4 * K) := by gcongr
            _ = d / (2 * K) := by ring
        have h5 : |f.secondDeriv z - g.secondDeriv z| ≥ d / (2 * K) := by
          have h6 : d / K ≤ |f z - g z| + |f.firstDeriv z - g.firstDeriv z| + |f.secondDeriv z - g.secondDeriv z| := hcurv
          have h7 : |f z - g z| + |f.firstDeriv z - g.firstDeriv z| ≤ d / (2 * K) := h4
          have h8 : d / K = d / (2 * K) + d / (2 * K) := by field_simp [hK_pos.ne'] <;> ring
          rw [h8] at h6
          linarith
        exact h5

      have hH''_ne_zero : ∀ (x : ℝ), x ∈ Set.Icc I.left I.right → deriv (deriv H) x ≠ 0 := by
        intro x hx
        have hx1 : 0 ≤ x := by linarith [I.left_mem.1, hx.1]
        have hx2 : x ≤ 1 := by linarith [I.right_mem.2, hx.2]
        let xp : UnitPoint := ⟨x, ⟨hx1, hx2⟩⟩
        have hxp_in : xp ∈ I.carrier := ⟨hx.1, hx.2⟩
        have h5 : deriv (deriv H) x = f.secondDeriv xp - g.secondDeriv xp := hH''_eq xp
        rw [h5]
        have h6 : |f.secondDeriv xp - g.secondDeriv xp| ≥ d / (2 * K) := h_H''_bound xp hxp_in
        have h7 : 0 < d / (2 * K) := by positivity
        exact abs_pos.mp (show 0 < |f.secondDeriv xp - g.secondDeriv xp| from by linarith)

      have hderiv_cont : Continuous (deriv (deriv H)) := hH2_c2.continuous_deriv_one
      have hH_cont : ContinuousOn (deriv (deriv H)) (Set.Icc I.left I.right) := hderiv_cont.continuousOn

      have h_sign : (∀ x ∈ Set.Icc I.left I.right, 0 < deriv (deriv H) x) ∨
          (∀ x ∈ Set.Icc I.left I.right, deriv (deriv H) x < 0) :=
        constant_sign_of_never_zero I.left_le_right hH_cont hH''_ne_zero

      let a_J : ℝ := I.midpoint - I.length / 4
      let b_J : ℝ := I.midpoint + I.length / 4

      have haJ_in_I : a_J ∈ Set.Icc I.left I.right := by
        have h1 : I.left ≤ a_J := by
          dsimp only [a_J, ParameterInterval.midpoint, ParameterInterval.length] <;> linarith
        have h2 : a_J ≤ I.right := by
          dsimp only [a_J, ParameterInterval.midpoint, ParameterInterval.length] <;> linarith
        exact ⟨h1, h2⟩
      have hbJ_in_I : b_J ∈ Set.Icc I.left I.right := by
        have h1 : I.left ≤ b_J := by
          dsimp only [b_J, ParameterInterval.midpoint, ParameterInterval.length] <;> linarith
        have h2 : b_J ≤ I.right := by
          dsimp only [b_J, ParameterInterval.midpoint, ParameterInterval.length] <;> linarith
        exact ⟨h1, h2⟩

      have h_geom1 : a - a_J ≥ I.length / 8 := by
        have h1 : |a - I.midpoint| ≤ I.length / 8 := by
          let a_lp : UnitPoint := ⟨a, R.interval.left_mem⟩
          have a_lp_in_R : a_lp ∈ R.interval.carrier := by exact ⟨by linarith, R.interval.left_le_right⟩
          have a_lp_center : a_lp ∈ I.centeredCarrier (1 / 4) := hRcentral a_lp_in_R
          have h_raw : |(a_lp : ℝ) - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := a_lp_center
          have h_eq1 : (a_lp : ℝ) = a := by simp [a_lp]
          have h_eq2 : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
          rw [h_eq1, h_eq2] at h_raw; exact h_raw
        have h2 : -(I.length / 8) ≤ a - I.midpoint := (abs_le.mp h1).1
        dsimp only [a_J] <;> linarith

      have h_geom3 : b_J - b ≥ I.length / 8 := by
        have h1 : |b - I.midpoint| ≤ I.length / 8 := by
          let b_lp : UnitPoint := ⟨b, R.interval.right_mem⟩
          have b_lp_in_R : b_lp ∈ R.interval.carrier := by exact ⟨R.interval.left_le_right, by linarith⟩
          have b_lp_center : b_lp ∈ I.centeredCarrier (1 / 4) := hRcentral b_lp_in_R
          have h_raw : |(b_lp : ℝ) - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := b_lp_center
          have h_eq1 : (b_lp : ℝ) = b := by simp [b_lp]
          have h_eq2 : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
          rw [h_eq1, h_eq2] at h_raw; exact h_raw
        have h2 : b - I.midpoint ≤ I.length / 8 := (abs_le.mp h1).2
        dsimp only [b_J] <;> linarith

      have h_geom5 : a - a_J ≥ 1 / (96 * K) := by
        calc a - a_J ≥ I.length / 8 := h_geom1
             _ ≥ (1 / (12 * K)) / 8 := by gcongr
             _ = 1 / (96 * K) := by field_simp [hK_pos.ne'] <;> ring

      have h_geom7 : b_J - b ≥ 1 / (96 * K) := by
        calc b_J - b ≥ I.length / 8 := h_geom3
             _ ≥ (1 / (12 * K)) / 8 := by gcongr
             _ = 1 / (96 * K) := by field_simp [hK_pos.ne'] <;> ring

      have h_geom8 : b_J - b ≤ 1 / (16 * K) := by
        have h_geom4 : b_J - b ≤ 3 * I.length / 8 := by
          have h1 : |b - I.midpoint| ≤ I.length / 8 := by
            let b_lp : UnitPoint := ⟨b, R.interval.right_mem⟩
            have b_lp_in_R : b_lp ∈ R.interval.carrier := by exact ⟨R.interval.left_le_right, by linarith⟩
            have b_lp_center : b_lp ∈ I.centeredCarrier (1 / 4) := hRcentral b_lp_in_R
            have h_raw : |(b_lp : ℝ) - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := b_lp_center
            have h_eq1 : (b_lp : ℝ) = b := by simp [b_lp]
            have h_eq2 : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
            rw [h_eq1, h_eq2] at h_raw; exact h_raw
          have h2 : -(I.length / 8) ≤ b - I.midpoint := (abs_le.mp h1).1
          dsimp only [b_J] <;> linarith
        calc b_J - b ≤ 3 * I.length / 8 := h_geom4
             _ ≤ 3 * (1 / (6 * K)) / 8 := by gcongr
             _ = 1 / (16 * K) := by field_simp [hK_pos.ne'] <;> ring

      let J_set : Set ℝ := Set.Icc a_J b_J

      have hJ_sub_I : J_set ⊆ Set.Icc I.left I.right := by
        intro x hx
        exact ⟨by linarith [haJ_in_I.1, hx.1], by linarith [hbJ_in_I.2, hx.2]⟩

      have hR_sub_J : Set.Icc a b ⊆ J_set := by
        intro x hx
        have h1 : a_J ≤ x := by
          have h2 : a_J ≤ a := by linarith [h_geom1]
          linarith [hx.1]
        have h3 : x ≤ b_J := by
          have h4 : b ≤ b_J := by linarith [h_geom3]
          linarith [hx.2]
        exact ⟨h1, h3⟩

      have h_geom6 : a - a_J ≤ 1 := by
        have h1 : a ≤ 1 := by linarith [ha_in_I.2, I.right_mem.2]
        have h2 : 0 ≤ a_J := by linarith [haJ_in_I.1, I.left_mem.1]
        linarith
      have h_ab_L : b - a = L := by simp [a, b, hL_def, ParameterInterval.length] <;> ring

      have h_main_proof : ∀ (Hfunc : ℝ → ℝ),
          Differentiable ℝ Hfunc → Differentiable ℝ (deriv Hfunc) →
          (∀ x ∈ Set.Icc I.left I.right, d / (2 * K) ≤ deriv (deriv Hfunc) x) →
          (∀ x ∈ Set.Icc I.left I.right, |deriv (deriv Hfunc) x| ≤ d) →
          |Hfunc a| ≤ 10 * delta → |Hfunc b| ≤ 10 * delta →
          (∀ (x0 : ℝ), x0 ∈ Set.Icc a b → |Hfunc x0| ≤ 10 * delta) →
          (∀ (x0 : ℝ), x0 ∈ J_set → Δ ≤ |Hfunc x0| + |deriv Hfunc x0|) →
          (Δ + delta) * d ≤ 270000 * K^2 * delta * t := by
        intro Hfunc hdiff1 hdiff2 hpos habs hfa hfb hint hΔ_J
        exact common_tangent_main_proof K d delta t L a b a_J b_J Δ I hK hK_pos hd_pos hδ_pos ht_pos hδt ht hL_eq hL_le hL_pos h_ab_L hab ha_in_I hb_in_I hJ_sub_I hR_sub_J h_geom5 h_geom6 h_geom7 h_geom8 Hfunc hdiff1 hdiff2 hpos habs hfa hfb hint hΔ_J

      have h_int_bound_H : ∀ (x0 : ℝ), x0 ∈ Set.Icc a b → |H x0| ≤ 10 * delta := by
        intro x0 hx0
        have hx01 : 0 ≤ x0 := by linarith [hx0.1, R.interval.left_mem.1]
        have hx02 : x0 ≤ 1 := by linarith [hx0.2, R.interval.right_mem.2]
        let x0p : UnitPoint := ⟨x0, ⟨hx01, hx02⟩⟩
        have hxp_in : x0p ∈ R.interval.carrier := ⟨hx0.1, hx0.2⟩
        have h12 : H x0 = f x0p - g x0p := by
          have h14 : H x0 = f.extension x0 - g.extension x0 := by simp [H] <;> rfl
          rw [h14]
          have h15 : f.extension x0 = f x0p := C2Function.extension_eq_value f x0p
          have h16 : g.extension x0 = g x0p := C2Function.extension_eq_value g x0p
          rw [h15, h16] <;> abel
        rw [h12]
        exact hfg_bound x0p hxp_in

      have hΔ_J_H : ∀ (x0 : ℝ), x0 ∈ J_set → Δ ≤ |H x0| + |deriv H x0| := by
        intro x0 hx0
        have hx01 : 0 ≤ x0 := by
          have h1 : 0 ≤ I.left := I.left_mem.1
          have h2 : I.left ≤ a_J := haJ_in_I.1
          have h3 : a_J ≤ x0 := hx0.1
          linarith
        have hx02 : x0 ≤ 1 := by
          have h1 : b_J ≤ I.right := hbJ_in_I.2
          have h2 : x0 ≤ b_J := hx0.2
          have h3 : I.right ≤ 1 := I.right_mem.2
          linarith
        let x0p : UnitPoint := ⟨x0, ⟨hx01, hx02⟩⟩
        have h_left : I.left ≤ x0 := by
          have h1 : I.left ≤ a_J := haJ_in_I.1
          have h2 : a_J ≤ x0 := hx0.1
          linarith
        have h_right : x0 ≤ I.right := by
          have h1 : x0 ≤ b_J := hx0.2
          have h2 : b_J ≤ I.right := hbJ_in_I.2
          linarith
        have hxp_in_I : x0p ∈ I.carrier := ⟨h_left, h_right⟩
        have hxp_in_half : x0p ∈ I.centeredCarrier (1 / 2) := by
          have h_aJ_eq : a_J = I.midpoint - I.length / 4 := by simp [a_J]
          have h_bJ_eq : b_J = I.midpoint + I.length / 4 := by simp [b_J]
          have h2 : a_J ≤ x0 := hx0.1
          have h3 : x0 ≤ b_J := hx0.2
          have h4 : |x0 - I.midpoint| ≤ I.length / 4 := by
            rw [h_aJ_eq] at h2; rw [h_bJ_eq] at h3
            exact abs_le.mpr ⟨by linarith, by linarith⟩
          have h5 : |x0 - I.midpoint| ≤ (1 / 2 : ℝ) * I.length / 2 := by
            have h6 : (1 / 2 : ℝ) * I.length / 2 = I.length / 4 := by ring
            rw [h6]; exact h4
          exact h5
        have h3 : |f x0p - g x0p| + |f.firstDeriv x0p - g.firstDeriv x0p| ≥ Δ :=
          hΔ_pointwise x0p hxp_in_half
        have hH_x0 : H x0 = f x0p - g x0p := by
          have h : H x0 = f.extension x0 - g.extension x0 := by simp [H] <;> rfl
          rw [h]
          have hf : f.extension x0 = f x0p := C2Function.extension_eq_value f x0p
          have hg : g.extension x0 = g x0p := C2Function.extension_eq_value g x0p
          rw [hf, hg] <;> abel
        have hderiv_x0 : deriv H x0 = f.firstDeriv x0p - g.firstDeriv x0p := by
          rw [h_deriv_eq x0]
          have h1 : deriv f.extension x0 = f.firstDeriv x0p := C2Function.deriv_extension_eq_firstDeriv f x0p
          have h2 : deriv g.extension x0 = g.firstDeriv x0p := C2Function.deriv_extension_eq_firstDeriv g x0p
          rw [h1, h2]
        rw [hH_x0, hderiv_x0]
        exact h3

      rcases h_sign with (h_pos | h_neg)
      · exact h_main_proof H hH_diff1 hH_diff2 (fun x hx => by
          have h1 : 0 < deriv (deriv H) x := h_pos x hx
          have h2 : d / (2 * K) ≤ deriv (deriv H) x := by
            have hx1 : 0 ≤ x := by linarith [I.left_mem.1, hx.1]
            have hx2 : x ≤ 1 := by linarith [I.right_mem.2, hx.2]
            let xp : UnitPoint := ⟨x, ⟨hx1, hx2⟩⟩
            have hxp_in : xp ∈ I.carrier := ⟨hx.1, hx.2⟩
            have h6 : deriv (deriv H) x = f.secondDeriv xp - g.secondDeriv xp := hH''_eq xp
            have h7 : 0 < f.secondDeriv xp - g.secondDeriv xp := by
              rw [←h6]; exact h1
            have h8 : |f.secondDeriv xp - g.secondDeriv xp| = f.secondDeriv xp - g.secondDeriv xp :=
              abs_of_pos h7
            have h9 : |f.secondDeriv xp - g.secondDeriv xp| ≥ d / (2 * K) := h_H''_bound xp hxp_in
            have h10 : f.secondDeriv xp - g.secondDeriv xp ≥ d / (2 * K) := by
              rw [h8] at h9; exact h9
            have h11 : d / (2 * K) ≤ deriv (deriv H) x := by
              rw [h6]; exact h10
            exact h11
          linarith) hH''_abs_le_d hHa_bound hHb_bound h_int_bound_H hΔ_J_H
      · let H2 : ℝ → ℝ := fun x => -H x
        have hH2_diff1 : Differentiable ℝ H2 := hH_diff1.neg
        have hH2_diff2 : Differentiable ℝ (deriv H2) := by
          have h_eq : deriv H2 = fun z => -deriv H z := by funext z; simp [H2, deriv_neg]
          rw [h_eq]; exact hH_diff2.neg
        have hH2''_pos : ∀ x ∈ Set.Icc I.left I.right, d / (2 * K) ≤ deriv (deriv H2) x := by
          intro x hx
          have h1 : deriv (deriv H2) x = -deriv (deriv H) x := by
            have h2 : deriv H2 = -deriv H := by funext w; simp [H2, deriv_neg]
            rw [h2]
            have h3 : deriv (-deriv H) x = -deriv (deriv H) x := by
              simpa [deriv_neg] using rfl
            exact h3
          rw [h1]
          have h4 : deriv (deriv H) x < 0 := h_neg x hx
          have h5 : |deriv (deriv H) x| ≥ d / (2 * K) := by
            have hx1 : 0 ≤ x := by linarith [I.left_mem.1, hx.1]
            have hx2 : x ≤ 1 := by linarith [I.right_mem.2, hx.2]
            let xp : UnitPoint := ⟨x, ⟨hx1, hx2⟩⟩
            have hxp_in : xp ∈ I.carrier := ⟨hx.1, hx.2⟩
            have h6 : deriv (deriv H) x = f.secondDeriv xp - g.secondDeriv xp := hH''_eq xp
            have h7 : f.secondDeriv xp - g.secondDeriv xp < 0 := by rw [←h6]; exact h4
            have h8 : |f.secondDeriv xp - g.secondDeriv xp| = -(f.secondDeriv xp - g.secondDeriv xp) :=
              abs_of_neg h7
            have h9 : |f.secondDeriv xp - g.secondDeriv xp| ≥ d / (2 * K) := h_H''_bound xp hxp_in
            have h10 : -(f.secondDeriv xp - g.secondDeriv xp) ≥ d / (2 * K) := by
              rw [h8] at h9; exact h9
            have h11 : d / (2 * K) ≤ -deriv (deriv H) x := by
              have h12 : -deriv (deriv H) x = -(f.secondDeriv xp - g.secondDeriv xp) := by rw [h6]
              rw [h12]
              exact h10
            have h13 : |deriv (deriv H) x| = -deriv (deriv H) x := abs_of_neg h4
            rw [h13]
            exact h11
          have h7 : -deriv (deriv H) x = |deriv (deriv H) x| := by
            rw [abs_of_neg h4] <;> ring
          rw [h7]; exact h5
        have hH2''_abs : ∀ x ∈ Set.Icc I.left I.right, |deriv (deriv H2) x| ≤ d := by
          intro x hx
          have h1 : deriv (deriv H2) x = -deriv (deriv H) x := by
            have h2 : deriv H2 = -deriv H := by funext w; simp [H2, deriv_neg]
            rw [h2]
            have h3 : deriv (-deriv H) x = -deriv (deriv H) x := by
              simpa [deriv_neg] using rfl
            exact h3
          rw [h1, abs_neg]; exact hH''_abs_le_d x hx
        have hH2a : |H2 a| ≤ 10 * delta := by
          have h1 : H2 a = -H a := by simp [H2]
          rw [h1, abs_neg]; exact hHa_bound
        have hH2b : |H2 b| ≤ 10 * delta := by
          have h1 : H2 b = -H b := by simp [H2]
          rw [h1, abs_neg]; exact hHb_bound
        have hΔ_J2 : ∀ (x0 : ℝ), x0 ∈ J_set → Δ ≤ |H2 x0| + |deriv H2 x0| := by
          intro x0 hx0
          have h1 : H2 x0 = -H x0 := by simp [H2]
          have h2 : deriv H2 x0 = -deriv H x0 := by
            have h3 : deriv H2 = fun w => -deriv H w := by funext w; simp [H2, deriv_neg]
            rw [h3] <;> rfl
          rw [h1, h2]
          have h4 : |(-H x0)| + |(-deriv H x0)| = |H x0| + |deriv H x0| := by rw [abs_neg, abs_neg]
          rw [h4]
          exact hΔ_J_H x0 hx0
        have h_int_bound_H2 : ∀ (x0 : ℝ), x0 ∈ Set.Icc a b → |H2 x0| ≤ 10 * delta := by
          intro x0 hx0
          have h1 : |H2 x0| = |H x0| := by
            have h2 : H2 x0 = -H x0 := by simp [H2]
            rw [h2, abs_neg]
          rw [h1]
          exact h_int_bound_H x0 hx0
        exact h_main_proof H2 hH2_diff1 hH2_diff2 hH2''_pos hH2''_abs hH2a hH2b h_int_bound_H2 hΔ_J2
-/

theorem common_tangent_rectangle_controls_parameter :
    CommonTangentRectangleStatement := by
  intro K D hK hD
  rcases common_tangent_rectangle_robust K D hK hD with
    ⟨C, hC, hrobust⟩
  let C5 : ℝ := C * Real.rpow 5 C
  use C5
  constructor
  · have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC
    have hrpow_pos : 0 < Real.rpow (5 : ℝ) C :=
      Real.rpow_pos_of_pos (by norm_num) C
    dsimp only [C5]
    positivity
  · intro family hfam I hI delta t hdelta hdelta_t ht R hR hcentral
      f hf g hg hfg hftan hgtan
    simpa only [C5] using
      hrobust 5 (by norm_num) family hfam I hI delta t hdelta hdelta_t ht
        R hR hcentral f hf g hg hfg hftan hgtan

end Kakeya.Cinematic
