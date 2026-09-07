import MyLeanRepo.Kakeya.Cinematic.Statements
import MyLeanRepo.Kakeya.Cinematic.Targets.TangencySublevelDiameter.Helpers
import MyLeanRepo.Kakeya.Cinematic.Targets.CommonTangentRectangleHelpers


/-!
# Relaxed fine rectangle assignment

This local construction follows the proof route of PYZ Lemma 41 and is useful
in later WZ2-facing work. Its current frozen statement has wider interval and
constant dependencies than the literal paper lemma, so it is not exported as
the final WZ2 cinematic input.
-/

namespace Kakeya.Cinematic

lemma sum_ge_half {a b c : ℝ} (h : a + b = c) : a ≥ c / 2 ∨ b ≥ c / 2 := by
  by_cases h1 : a ≥ c / 2
  · exact Or.inl h1
  · have h2 : a < c / 2 := lt_of_not_ge h1
    have h3 : b ≥ c / 2 := by
      calc b
        = c - a := by linarith
      _ ≥ c - c / 2 := by gcongr
      _ = c / 2 := by ring
    exact Or.inr h3

lemma parameter_interval_one_side_ge_half
    (J : ParameterInterval) (p ℓ : ℝ)
    (hp : J.left ≤ p ∧ p ≤ J.right)
    (hℓ : J.length = ℓ) :
    J.right - p ≥ ℓ / 2 ∨ p - J.left ≥ ℓ / 2 := by
  have hsum :
      (J.right - p) + (p - J.left) = ℓ := by
    rw [← hℓ]
    simp only [ParameterInterval.length]
    ring
  exact sum_ge_half hsum

/-- Helper: derivative Lipschitz bound at two UnitPoints, in a clean context. -/
lemma deriv_lipschitz_helper
    {f k : C2Function} {h_ext : ℝ → ℝ} {d : ℝ}
    (h_deriv_ext : ∀ (z : UnitPoint), deriv h_ext z = f.firstDeriv z - k.firstDeriv z)
    (hd_def : d = c2Distance f k)
    (x y : UnitPoint) :
    |deriv h_ext x - deriv h_ext y| ≤ d * |(x : ℝ) - (y : ℝ)| := by
  have h3 := lipschitz_deriv f k x y
  rw [←h_deriv_ext x, ←h_deriv_ext y, ←hd_def] at h3
  exact h3

/-- Taylor remainder bound: if |H''| ≤ d on [a,b], then
|H(x) - H(y) - H'(y)*(x-y)| ≤ d/2 * (x-y)^2. -/
lemma taylor_remainder_bound {H : ℝ → ℝ} {d a b x y : ℝ}
    (hH1 : Differentiable ℝ H)
    (hH2 : Differentiable ℝ (deriv H))
    (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b)
    (hy : y ∈ Set.Icc a b)
    (hH'' : ∀ z ∈ Set.Icc a b, |deriv (deriv H) z| ≤ d) :
    |H x - H y - deriv H y * (x - y)| ≤ d / 2 * (x - y)^2 := by
  have h1 : ∀ z ∈ Set.Icc a b, -d ≤ deriv (deriv H) z := by
    intro z hz; exact (abs_le.mp (hH'' z hz)).1
  have h2 : ∀ z ∈ Set.Icc a b, deriv (deriv H) z ≤ d := by
    intro z hz; exact (abs_le.mp (hH'' z hz)).2
  have h_lower : H x - H y - deriv H y * (x - y) ≥ -d / 2 * (x - y)^2 := by
    have h_raw := taylor_quadratic_lower_bound hH1 hH2 hab hy hx h1
    linarith
  have hH1_neg : Differentiable ℝ (-H) := hH1.neg
  have hH2_neg : Differentiable ℝ (deriv (-H)) := by
    have h_eq : deriv (-H) = -deriv H := by funext z; simp
    rw [h_eq]; exact hH2.neg
  have h_neg2 : ∀ z ∈ Set.Icc a b, -d ≤ deriv (deriv (-H)) z := by
    intro z hz
    have h3 : deriv (deriv (-H)) z = -deriv (deriv H) z := by
      have h4 : deriv (-H) = -deriv H := by funext w; simp
      rw [h4]; simp
    rw [h3]; linarith [h2 z hz]
  have h_upper_raw : (-H) x ≥ (-H) y + deriv (-H) y * (x - y) + (-d / 2) * (x - y)^2 :=
    taylor_quadratic_lower_bound hH1_neg hH2_neg hab hy hx h_neg2
  have h_upper : H x - H y - deriv H y * (x - y) ≤ d / 2 * (x - y)^2 := by
    have h_exp1 : (-H) x = -H x := by simp
    have h_exp2 : (-H) y = -H y := by simp
    have h_exp3 : deriv (-H) y = -deriv H y := by simp
    rw [h_exp1, h_exp2, h_exp3] at h_upper_raw; linarith
  have h_lower' : -(d / 2 * (x - y)^2) ≤ H x - H y - deriv H y * (x - y) := by
    have h_eq : -(d / 2 * (x - y)^2) = -d / 2 * (x - y)^2 := by ring
    rw [h_eq]; exact h_lower
  exact abs_le.mpr ⟨h_lower', h_upper⟩

/--
Mean Value Theorem derivative bound.

If `H` is C¹ on `J = [J.left, J.right]`, `p ∈ J`, one side of `p` in `J` has
length at least `L`, `|H x| ≤ B` on `J`, `|H p| ≤ A`, and `deriv H` is
`d`-Lipschitz on `J`, then
`|deriv H p| ≤ (B + A) / L + d * J.length`.
-/
lemma mvt_deriv_bound_interval
    {H : ℝ → ℝ} {J : ParameterInterval} {p B A L d : ℝ}
    (hp : p ∈ Set.Icc J.left J.right)
    (h_cont : ContinuousOn H (Set.Icc J.left J.right))
    (h_diff : DifferentiableOn ℝ H (Set.Ioo J.left J.right))
    (hB : ∀ x ∈ Set.Icc J.left J.right, |H x| ≤ B)
    (hA : |H p| ≤ A)
    (hL : J.right - p ≥ L ∨ p - J.left ≥ L)
    (hLpos : 0 < L)
    (hd : 0 ≤ d)
    (h_deriv_lipschitz :
      ∀ x ∈ Set.Icc J.left J.right,
        ∀ y ∈ Set.Icc J.left J.right,
          |deriv H x - deriv H y| ≤ d * |x - y|) :
    |deriv H p| ≤ (B + A) / L + d * J.length := by
  have hB_nonneg : 0 ≤ B := by
    have h1 : 0 ≤ |H p| := by positivity
    have h2 : |H p| ≤ B := hB p hp
    linarith
  have hA_nonneg : 0 ≤ A := by
    have h1 : 0 ≤ |H p| := by positivity
    linarith [hA]
  rcases hL with (hL_right | hL_left)
  · -- Case 1: right side of p is long
    have hpb : p < J.right := by linarith
    have hpleft : J.left ≤ p := hp.1
    have h_sub1 : Set.Icc p J.right ⊆ Set.Icc J.left J.right := by
      intro x hx; exact ⟨by linarith [hpleft, hx.1], by linarith [hx.2]⟩
    have h_cont' : ContinuousOn H (Set.Icc p J.right) := h_cont.mono h_sub1
    have h_sub2 : Set.Ioo p J.right ⊆ Set.Ioo J.left J.right := by
      intro x hx; exact ⟨by linarith [hpleft, hx.1], by linarith [hx.2]⟩
    have h_diff' : DifferentiableOn ℝ H (Set.Ioo p J.right) := h_diff.mono h_sub2
    rcases exists_deriv_eq_slope H hpb h_cont' h_diff' with ⟨z, hz, hz_eq⟩
    have hz1 : p < z := hz.1
    have hz2 : z < J.right := hz.2
    have h_deriv_z_bound : |deriv H z| ≤ (B + A) / L := by
      have h_eq : |deriv H z| = |H J.right - H p| / (J.right - p) := by
        rw [hz_eq, abs_div, abs_of_pos (show 0 < J.right - p by linarith)]
      rw [h_eq]
      have h2 : |H J.right - H p| ≤ B + A := by
        calc |H J.right - H p|
          ≤ |H J.right| + |H p| := abs_sub (H J.right) (H p)
        _ ≤ B + A := by
          have hBr := hB J.right ⟨by linarith, by linarith⟩
          linarith
      have hden : 0 < J.right - p := by linarith
      calc |H J.right - H p| / (J.right - p)
        ≤ (B + A) / (J.right - p) := by gcongr
      _ ≤ (B + A) / L := by gcongr
    have h_pz_in : p ∈ Set.Icc J.left J.right := hp
    have h_z_in : z ∈ Set.Icc J.left J.right := ⟨by linarith [hpleft, hz1], by linarith [hz2]⟩
    have h4 : |deriv H p - deriv H z| ≤ d * |p - z| :=
      h_deriv_lipschitz p h_pz_in z h_z_in
    have h5 : |p - z| ≤ J.length := by
      have h6 : 0 ≤ z - p := by linarith [hz1]
      have h7 : |p - z| = z - p := by
        rw [abs_of_nonpos (show p - z ≤ 0 by linarith [hz1])] <;> linarith
      rw [h7]
      simp [ParameterInterval.length] <;> linarith
    have h7 : |deriv H p - deriv H z| ≤ d * J.length := by
      calc |deriv H p - deriv H z|
        ≤ d * |p - z| := h4
      _ ≤ d * J.length := by gcongr
    have h9 : |deriv H z + (deriv H p - deriv H z)| ≤ |deriv H z| + |deriv H p - deriv H z| :=
      abs_add_le (deriv H z) (deriv H p - deriv H z)
    have h10 : deriv H z + (deriv H p - deriv H z) = deriv H p := by ring
    rw [h10] at h9
    have h8 : |deriv H p| ≤ |deriv H z| + |deriv H p - deriv H z| := h9
    linarith [h_deriv_z_bound, h7, h8]
  · -- Case 2: left side of p is long
    have hlp : J.left < p := by linarith
    have hpright : p ≤ J.right := hp.2
    have h_sub1 : Set.Icc J.left p ⊆ Set.Icc J.left J.right := by
      intro x hx; exact ⟨by linarith [hx.1], by linarith [hpright, hx.2]⟩
    have h_cont' : ContinuousOn H (Set.Icc J.left p) := h_cont.mono h_sub1
    have h_sub2 : Set.Ioo J.left p ⊆ Set.Ioo J.left J.right := by
      intro x hx; exact ⟨by linarith [hx.1], by linarith [hpright, hx.2]⟩
    have h_diff' : DifferentiableOn ℝ H (Set.Ioo J.left p) := h_diff.mono h_sub2
    rcases exists_deriv_eq_slope H hlp h_cont' h_diff' with ⟨z, hz, hz_eq⟩
    have hz1 : J.left < z := hz.1
    have hz2 : z < p := hz.2
    have h_deriv_z_bound : |deriv H z| ≤ (B + A) / L := by
      have h_eq : |deriv H z| = |H p - H J.left| / (p - J.left) := by
        rw [hz_eq, abs_div, abs_of_pos (show 0 < p - J.left by linarith)]
      rw [h_eq]
      have h2 : |H p - H J.left| ≤ B + A := by
        calc |H p - H J.left|
          ≤ |H p| + |H J.left| := abs_sub (H p) (H J.left)
        _ ≤ B + A := by
          have hBl := hB J.left ⟨by linarith, by linarith⟩
          linarith
      have hden : 0 < p - J.left := by linarith
      calc |H p - H J.left| / (p - J.left)
        ≤ (B + A) / (p - J.left) := by gcongr
      _ ≤ (B + A) / L := by gcongr
    have h_pz_in : p ∈ Set.Icc J.left J.right := hp
    have h_z_in : z ∈ Set.Icc J.left J.right := ⟨by linarith [hz1], by linarith [hpright, hz2]⟩
    have h4 : |deriv H p - deriv H z| ≤ d * |p - z| :=
      h_deriv_lipschitz p h_pz_in z h_z_in
    have h5 : |p - z| ≤ J.length := by
      have h6 : 0 ≤ p - z := by linarith [hz2]
      have h7 : |p - z| = p - z := by
        rw [abs_of_nonneg h6]
      rw [h7]
      simp [ParameterInterval.length] <;> linarith
    have h7 : |deriv H p - deriv H z| ≤ d * J.length := by
      calc |deriv H p - deriv H z|
        ≤ d * |p - z| := h4
      _ ≤ d * J.length := by gcongr
    have h9 : |deriv H z + (deriv H p - deriv H z)| ≤ |deriv H z| + |deriv H p - deriv H z| :=
      abs_add_le (deriv H z) (deriv H p - deriv H z)
    have h10 : deriv H z + (deriv H p - deriv H z) = deriv H p := by ring
    rw [h10] at h9
    have h8 : |deriv H p| ≤ |deriv H z| + |deriv H p - deriv H z| := h9
    linarith [h_deriv_z_bound, h7, h8]

/-- Apply MVT derivative bound in a clean context to avoid large-context timeouts. -/
lemma apply_mvt_bound
    {h_ext : ℝ → ℝ} {J_p : ParameterInterval} {pval d delta ℓ : ℝ}
    (hH1 : Differentiable ℝ h_ext)
    (h_bound_Jp : ∀ x ∈ Set.Icc J_p.left J_p.right, |h_ext x| ≤ 4 * delta)
    (hA : |h_ext pval| ≤ 2 * delta)
    (h_side : J_p.right - pval ≥ ℓ / 2 ∨ pval - J_p.left ≥ ℓ / 2)
    (hℓ_pos : 0 < ℓ)
    (hd_nonneg : 0 ≤ d)
    (h_deriv_lipschitz_Jp : ∀ x ∈ Set.Icc J_p.left J_p.right,
      ∀ y ∈ Set.Icc J_p.left J_p.right, |deriv h_ext x - deriv h_ext y| ≤ d * |x - y|)
    (h_p1_bounds : J_p.left ≤ pval ∧ pval ≤ J_p.right) :
    |deriv h_ext pval| ≤ (4 * delta + 2 * delta) / (ℓ / 2) + d * J_p.length := by
  have h_cont : ContinuousOn h_ext (Set.Icc J_p.left J_p.right) := hH1.continuous.continuousOn
  have h_diff : DifferentiableOn ℝ h_ext (Set.Ioo J_p.left J_p.right) := hH1.differentiableOn
  exact mvt_deriv_bound_interval
    (hp := ⟨h_p1_bounds.1, h_p1_bounds.2⟩)
    (h_cont := h_cont)
    (h_diff := h_diff)
    (hB := h_bound_Jp)
    (hA := hA)
    (hL := h_side)
    (hLpos := by linarith [hℓ_pos])
    (hd := hd_nonneg)
    (h_deriv_lipschitz := h_deriv_lipschitz_Jp)

/-- Final Taylor bound: |h_ext xval| ≤ 4 * delta, in a clean context to avoid
large-context timeouts from hTangency_main. -/
lemma taylor_final_bound
    {h_ext : ℝ → ℝ} {C C_R K delta t Delta d L pval xval : ℝ}
    (hC_pos : 0 < C)
    (hK : 1 ≤ K)
    (hC_R_pos : 0 < C_R)
    (hdelta : 0 < delta)
    (hdelta_Delta : delta ≤ Delta)
    (ht_pos : 0 < t)
    (hd_nonneg : 0 ≤ d)
    (hsqrt_C_R_ge_12C : Real.sqrt C_R ≥ 12 * C)
    (hsqrt_C_R_ge_96K : Real.sqrt C_R ≥ 96 * K)
    (hL_eq : L = delta / Real.sqrt (C_R * t * Delta))
    (h_abs_h_p : |h_ext pval| ≤ 2 * delta)
    (h_abs_h'_bound : |deriv h_ext pval| ≤ (5 + (43 / 2 : ℝ) * C) * Real.sqrt (t * Delta))
    (h_x_abs_diff : |xval - pval| ≤ L / 2)
    (h_taylor2 : |h_ext xval - h_ext pval - deriv h_ext pval * (xval - pval)| ≤ d / 2 * (xval - pval)^2)
    (h_d2_le_3t : d / 2 ≤ 3 * t) :
    |h_ext xval| ≤ 4 * delta := by
  have hDelta_pos : 0 < Delta := by linarith
  have hsqrt_tDelta_pos : 0 < Real.sqrt (t * Delta) := by positivity
  have h_sqrt_mul : Real.sqrt (C_R * t * Delta) = Real.sqrt C_R * Real.sqrt (t * Delta) := by
    have h_nonneg : 0 ≤ C_R := by positivity
    have h_assoc : C_R * t * Delta = C_R * (t * Delta) := by ring
    rw [h_assoc, Real.sqrt_mul h_nonneg] <;> rfl
  have h_abs_hx_le : |h_ext xval| ≤ |h_ext pval| + |deriv h_ext pval| * |xval - pval| + d / 2 * (xval - pval)^2 := by
    have h : h_ext xval = h_ext pval + deriv h_ext pval * (xval - pval) + (h_ext xval - h_ext pval - deriv h_ext pval * (xval - pval)) := by ring
    rw [h]
    have h5 : |h_ext pval + deriv h_ext pval * (xval - pval) + (h_ext xval - h_ext pval - deriv h_ext pval * (xval - pval))| ≤
        |h_ext pval + deriv h_ext pval * (xval - pval)| + |h_ext xval - h_ext pval - deriv h_ext pval * (xval - pval)| :=
      abs_add_le _ _
    have h6 : |h_ext pval + deriv h_ext pval * (xval - pval)| ≤ |h_ext pval| + |deriv h_ext pval| * |xval - pval| := by
      calc
        |h_ext pval + deriv h_ext pval * (xval - pval)|
          ≤ |h_ext pval| + |deriv h_ext pval * (xval - pval)| := abs_add_le _ _
        _ = |h_ext pval| + |deriv h_ext pval| * |xval - pval| := by rw [abs_mul]
    linarith
  have h_pos1 : 0 ≤ (5 + (43 / 2 : ℝ) * C) * Real.sqrt (t * Delta) := by positivity
  have h2 : |deriv h_ext pval| * |xval - pval| ≤
      (5 + (43 / 2 : ℝ) * C) * delta / (2 * Real.sqrt C_R) := by
    have h21 : |deriv h_ext pval| * |xval - pval| ≤
        (5 + (43 / 2 : ℝ) * C) * Real.sqrt (t * Delta) * (L / 2) :=
      calc
        |deriv h_ext pval| * |xval - pval|
          ≤ ((5 + (43 / 2 : ℝ) * C) * Real.sqrt (t * Delta)) * |xval - pval| :=
            mul_le_mul_of_nonneg_right h_abs_h'_bound (abs_nonneg _)
        _ ≤ ((5 + (43 / 2 : ℝ) * C) * Real.sqrt (t * Delta)) * (L / 2) :=
            mul_le_mul_of_nonneg_left h_x_abs_diff h_pos1
    have h22 : (5 + (43 / 2 : ℝ) * C) * Real.sqrt (t * Delta) * (L / 2) =
        (5 + (43 / 2 : ℝ) * C) * delta / (2 * Real.sqrt C_R) := by
      rw [hL_eq, h_sqrt_mul]
      <;> field_simp [hC_R_pos.ne', hsqrt_tDelta_pos.ne'] <;> ring
    rw [h22] at h21
    exact h21
  have h4 : d / 2 * (xval - pval)^2 ≤ 3 * delta / (4 * C_R) := by
    have hL_pos : 0 < L := by
      rw [hL_eq]; positivity
    have h413 : 0 ≤ L / 2 := by linarith [hL_pos]
    have h412 : (xval - pval)^2 ≤ (L / 2)^2 := by
      have h : |xval - pval| ≤ |L / 2| := by
        rw [abs_of_nonneg h413]
        exact h_x_abs_diff
      exact sq_le_sq.mpr h
    have h411 : 0 ≤ d / 2 := by linarith
    have h41 : d / 2 * (xval - pval)^2 ≤ (d / 2) * (L / 2)^2 :=
      mul_le_mul_of_nonneg_left h412 h411
    have h_L2 : (L / 2)^2 = (delta / (2 * (Real.sqrt C_R * Real.sqrt (t * Delta))))^2 := by
      have h5 : L / 2 = delta / (2 * Real.sqrt (C_R * t * Delta)) := by
        rw [hL_eq] <;> field_simp <;> ring
      rw [h5, h_sqrt_mul] <;> rfl
    have h42 : (d / 2) * (L / 2)^2 ≤ 3 * delta / (4 * C_R) := by
      rw [h_L2]
      have h_pos2 : 0 ≤ (delta / (2 * (Real.sqrt C_R * Real.sqrt (t * Delta))))^2 := by positivity
      have h_step1 : (d / 2) * (delta / (2 * (Real.sqrt C_R * Real.sqrt (t * Delta))))^2 ≤
          (3 * t) * (delta / (2 * (Real.sqrt C_R * Real.sqrt (t * Delta))))^2 :=
        mul_le_mul_of_nonneg_right h_d2_le_3t h_pos2
      have h_sq : (Real.sqrt C_R * Real.sqrt (t * Delta))^2 = C_R * t * Delta := by
        have h1 : (Real.sqrt C_R)^2 = C_R := Real.sq_sqrt (by positivity)
        have h2 : (Real.sqrt (t * Delta))^2 = t * Delta := Real.sq_sqrt (by positivity)
        calc (Real.sqrt C_R * Real.sqrt (t * Delta))^2
          = (Real.sqrt C_R)^2 * (Real.sqrt (t * Delta))^2 := by ring
        _ = C_R * (t * Delta) := by rw [h1, h2] <;> ring
        _ = C_R * t * Delta := by ring
      have h_denom_sq : (2 * (Real.sqrt C_R * Real.sqrt (t * Delta)))^2 = 4 * C_R * t * Delta := by
        calc (2 * (Real.sqrt C_R * Real.sqrt (t * Delta)))^2
          = 4 * (Real.sqrt C_R * Real.sqrt (t * Delta))^2 := by ring
        _ = 4 * (C_R * t * Delta) := by rw [h_sq] <;> ring
        _ = 4 * C_R * t * Delta := by ring
      have h_step2 : (3 * t) * (delta / (2 * (Real.sqrt C_R * Real.sqrt (t * Delta))))^2 =
          3 * delta^2 / (4 * C_R * Delta) := by
        have h_pos1 : 0 < (2 * (Real.sqrt C_R * Real.sqrt (t * Delta))) := by positivity
        have h_div_sq : (delta / (2 * (Real.sqrt C_R * Real.sqrt (t * Delta))))^2 =
            delta^2 / (2 * (Real.sqrt C_R * Real.sqrt (t * Delta)))^2 := by
          simp [div_pow, h_pos1.ne'] <;> ring
        have h : (delta / (2 * (Real.sqrt C_R * Real.sqrt (t * Delta))))^2 =
            delta^2 / (4 * C_R * t * Delta) := by
          rw [h_div_sq, h_denom_sq]
        calc (3 * t) * (delta / (2 * (Real.sqrt C_R * Real.sqrt (t * Delta))))^2
          = (3 * t) * (delta^2 / (4 * C_R * t * Delta)) := by rw [h]
        _ = 3 * delta^2 / (4 * C_R * Delta) := by
          field_simp [ht_pos.ne', hC_R_pos.ne', hDelta_pos.ne'] <;> ring
      have h_step3 : 3 * delta^2 / (4 * C_R * Delta) ≤ 3 * delta / (4 * C_R) := by
        have h49 : delta^2 / Delta ≤ delta := by
          have h50 : 0 < Delta := hDelta_pos
          field_simp [h50.ne'] <;> nlinarith [hdelta_Delta]
        have h51 : 0 < C_R := hC_R_pos
        calc 3 * delta^2 / (4 * C_R * Delta)
          = (3 / (4 * C_R)) * (delta^2 / Delta) := by field_simp [h51.ne'] <;> ring
        _ ≤ (3 / (4 * C_R)) * delta := by gcongr
        _ = 3 * delta / (4 * C_R) := by ring
      have h_step1' : (d / 2) * (delta / (2 * (Real.sqrt C_R * Real.sqrt (t * Delta))))^2 ≤ 3 * delta^2 / (4 * C_R * Delta) :=
        le_trans h_step1 (le_of_eq h_step2)
      exact le_trans h_step1' h_step3
    exact le_trans h41 h42
  have h_sqrt_ge_96 : Real.sqrt C_R ≥ 96 := by
    have h1 : 96 * K ≥ 96 := by
      have h2 : K ≥ 1 := hK
      linarith
    exact le_trans h1 hsqrt_C_R_ge_96K
  have h_C_R_ge_9216 : C_R ≥ 9216 := by
    have h12 : (Real.sqrt C_R)^2 ≥ (96 * K)^2 := by gcongr
    have h13 : (Real.sqrt C_R)^2 = C_R := Real.sq_sqrt (by positivity)
    rw [h13] at h12
    have h14 : (96 * K)^2 ≥ 9216 := by
      have h15 : K ≥ 1 := hK
      nlinarith
    linarith
  have h_43_48 : (5 + (43 / 2 : ℝ) * C) / (2 * Real.sqrt C_R) ≤ 43 / 48 + 5 / 192 := by
    have h9 : Real.sqrt C_R ≥ 12 * C := hsqrt_C_R_ge_12C
    have h10 : Real.sqrt C_R ≥ 96 := h_sqrt_ge_96
    have h12 : (5 + (43 / 2 : ℝ) * C) / (2 * Real.sqrt C_R) =
        5 / (2 * Real.sqrt C_R) + (43 / 2 : ℝ) * C / (2 * Real.sqrt C_R) := by
      rw [add_div]
    rw [h12]
    have h_denom : 2 * Real.sqrt C_R ≥ 192 := by linarith [h10]
    have h13 : 5 / (2 * Real.sqrt C_R) ≤ 5 / 192 := by
      have h1 : 0 < (192 : ℝ) := by norm_num
      have h3 : 1 / (2 * Real.sqrt C_R) ≤ 1 / 192 := by
        apply one_div_le_one_div_of_le h1 h_denom
      have h4 : 5 * (1 / (2 * Real.sqrt C_R)) ≤ 5 * (1 / 192) := by gcongr
      have h5 : 5 / (2 * Real.sqrt C_R) = 5 * (1 / (2 * Real.sqrt C_R)) := by ring
      have h6 : (5 : ℝ) / 192 = 5 * (1 / 192) := by ring
      rw [h5, h6]
      exact h4
    have h14 : (43 / 2 : ℝ) * C / (2 * Real.sqrt C_R) ≤ 43 / 48 := by
      have h15 : (43 / 2 : ℝ) * C / (2 * Real.sqrt C_R) = (43 / 4 : ℝ) * C / Real.sqrt C_R := by ring
      rw [h15]
      have h16 : C / Real.sqrt C_R ≤ 1 / 12 := by
        have h17 : Real.sqrt C_R ≥ 12 * C := h9
        have h18 : 0 < Real.sqrt C_R := by positivity
        calc C / Real.sqrt C_R ≤ C / (12 * C) := by gcongr
        _ = 1 / 12 := by field_simp [hC_pos.ne'] <;> ring
      have h_pos43 : 0 ≤ (43 / 4 : ℝ) := by norm_num
      have h191 : (43 / 4 : ℝ) * C / Real.sqrt C_R = (43 / 4 : ℝ) * (C / Real.sqrt C_R) := by ring
      rw [h191]
      have h19 : (43 / 4 : ℝ) * (C / Real.sqrt C_R) ≤ (43 / 4 : ℝ) * (1 / 12) :=
        mul_le_mul_of_nonneg_left h16 h_pos43
      rw [show (43 / 4 : ℝ) * (1 / 12) = 43 / 48 by norm_num] at h19
      exact h19
    linarith
  have h6 : |h_ext xval| ≤ 2 * delta + ((5 + (43 / 2 : ℝ) * C) * delta / (2 * Real.sqrt C_R)) + 3 * delta / (4 * C_R) := by
    linarith [h_abs_hx_le, h_abs_h_p, h2, h4]
  have h7 : (5 + (43 / 2 : ℝ) * C) * delta / (2 * Real.sqrt C_R) ≤ (43 / 48 + 5 / 192 : ℝ) * delta := by
    have h8 : (5 + (43 / 2 : ℝ) * C) / (2 * Real.sqrt C_R) ≤ 43 / 48 + 5 / 192 := h_43_48
    have h9 : 0 ≤ delta := by linarith
    have h10 : ((5 + (43 / 2 : ℝ) * C) / (2 * Real.sqrt C_R)) * delta ≤ (43 / 48 + 5 / 192 : ℝ) * delta :=
      mul_le_mul_of_nonneg_right h8 h9
    have h11 : (5 + (43 / 2 : ℝ) * C) * delta / (2 * Real.sqrt C_R) = ((5 + (43 / 2 : ℝ) * C) / (2 * Real.sqrt C_R)) * delta := by ring
    rw [h11]
    exact h10
  have h10 : 3 * delta / (4 * C_R) ≤ delta / 12288 := by
    have h11 : 3 / (4 * C_R) ≤ 1 / 12288 := by
      have h12 : C_R ≥ 9216 := h_C_R_ge_9216
      have h13 : 0 < C_R := hC_R_pos
      calc
        3 / (4 * C_R) ≤ 3 / (4 * (9216 : ℝ)) := by gcongr
        _ = 1 / 12288 := by norm_num
    have h14 : 0 ≤ delta := by linarith
    calc
      3 * delta / (4 * C_R) = delta * (3 / (4 * C_R)) := by ring
      _ ≤ delta * (1 / 12288) := by gcongr
      _ = delta / 12288 := by ring
  have h12 : 2 * delta + (43 / 48 + 5 / 192 : ℝ) * delta + delta / 12288 ≤ 4 * delta := by
    have h13 : 2 + (43 / 48 + 5 / 192 : ℝ) + (1 / 12288 : ℝ) ≤ 4 := by norm_num
    nlinarith [hdelta]
  linarith

lemma fine_rectangle_scale_bounds
    {K C_R delta t Delta t' L : ℝ}
    (hK : 1 ≤ K)
    (hC_R_pos : 0 < C_R)
    (hsqrt_C_R_ge_96K : 96 * K ≤ Real.sqrt C_R)
    (hdelta : 0 < delta)
    (hdelta_Delta : delta ≤ Delta)
    (hDelta_t : Delta ≤ t)
    (ht'_def : t' = C_R * t * Delta / delta)
    (hL_def : L = Real.sqrt (delta / t'))
    {I : ParameterInterval}
    (hI : I.IsControlled K) :
    L = delta / Real.sqrt (C_R * t * Delta) ∧
      L / 2 ≤ delta / (5 * Real.sqrt (t * Delta)) ∧
      L / 2 ≤ I.length / 16 := by
  have hK_pos : 0 < K := by linarith
  have hDelta_pos : 0 < Delta := by linarith
  have ht_pos : 0 < t := by linarith
  have hsqrt_tDelta_pos : 0 < Real.sqrt (t * Delta) := by positivity
  have hL_eq : L = delta / Real.sqrt (C_R * t * Delta) := by
    have hratio : delta / t' = delta ^ 2 / (C_R * t * Delta) := by
      rw [ht'_def]
      field_simp [hdelta.ne']
      <;> ring
    rw [hL_def, hratio, Real.sqrt_div (by positivity)]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hdelta]
  have hsqrt_product :
      Real.sqrt (C_R * t * Delta) =
        Real.sqrt C_R * Real.sqrt (t * Delta) := by
    rw [show C_R * t * Delta = C_R * (t * Delta) by ring]
    exact Real.sqrt_mul hC_R_pos.le _
  have hL_half_le_s :
      L / 2 ≤ delta / (5 * Real.sqrt (t * Delta)) := by
    have hL_half :
        L / 2 =
          delta / (2 * Real.sqrt C_R * Real.sqrt (t * Delta)) := by
      rw [hL_eq, hsqrt_product]
      field_simp [hC_R_pos.ne', hsqrt_tDelta_pos.ne']
      <;> ring
    rw [hL_half]
    have hdenom :
        5 * Real.sqrt (t * Delta) ≤
          2 * Real.sqrt C_R * Real.sqrt (t * Delta) := by
      have hfive : 5 ≤ 2 * Real.sqrt C_R := by
        nlinarith
      exact mul_le_mul_of_nonneg_right hfive (Real.sqrt_nonneg _)
    exact div_le_div_of_nonneg_left hdelta.le (by positivity) hdenom
  have hdelta_ratio_le_one :
      delta / Real.sqrt (t * Delta) ≤ 1 := by
    have hsquare : delta ^ 2 ≤ t * Delta := by nlinarith
    have hdelta_sqrt : delta ≤ Real.sqrt (t * Delta) := by
      have hsqrt_square :
          delta ^ 2 ≤ (Real.sqrt (t * Delta)) ^ 2 := by
        rw [Real.sq_sqrt (by positivity)]
        exact hsquare
      nlinarith [Real.sqrt_nonneg (t * Delta)]
    calc
      delta / Real.sqrt (t * Delta) ≤
          Real.sqrt (t * Delta) / Real.sqrt (t * Delta) := by
        gcongr
      _ = 1 := by field_simp [hsqrt_tDelta_pos.ne']
  have hI_len_lower : 1 / (12 * K) ≤ I.length := by
    have hlower : (12 * K)⁻¹ ≤ I.length := hI.1
    have hinv : (12 * K)⁻¹ = 1 / (12 * K) := by
      field_simp [hK_pos.ne']
    rw [hinv] at hlower
    exact hlower
  have hL_half_le_I_len_16 : L / 2 ≤ I.length / 16 := by
    have hL_half :
        L / 2 =
          (delta / Real.sqrt (t * Delta)) /
            (2 * Real.sqrt C_R) := by
      rw [hL_eq, hsqrt_product]
      field_simp [hC_R_pos.ne', hsqrt_tDelta_pos.ne']
      <;> ring
    rw [hL_half]
    have hratio :
        (delta / Real.sqrt (t * Delta)) /
            (2 * Real.sqrt C_R) ≤
          1 / (2 * Real.sqrt C_R) := by
      exact div_le_div_of_nonneg_right hdelta_ratio_le_one (by positivity)
    have hsqrt_bound :
        1 / (2 * Real.sqrt C_R) ≤ 1 / (192 * K) := by
      apply one_div_le_one_div_of_le
      · positivity
      · nlinarith
    calc
      (delta / Real.sqrt (t * Delta)) / (2 * Real.sqrt C_R)
          ≤ 1 / (2 * Real.sqrt C_R) := hratio
      _ ≤ 1 / (192 * K) := hsqrt_bound
      _ = (1 / (12 * K)) / 16 := by
        field_simp [hK_pos.ne']
        <;> ring
      _ ≤ I.length / 16 := by gcongr
  exact ⟨hL_eq, hL_half_le_s, hL_half_le_I_len_16⟩

lemma fine_rectangle_sqrt_absorption
    {C t Delta : ℝ}
    (hC : 0 < C)
    (htDelta : 0 < t * Delta) :
    3 * C * Real.sqrt (30 * t * Delta) +
        2 * C * Real.sqrt (6 * t * Delta) ≤
      (5 + (43 / 2 : ℝ) * C) * Real.sqrt (t * Delta) := by
  have hsqrt30 :
      Real.sqrt (30 * t * Delta) =
        Real.sqrt 30 * Real.sqrt (t * Delta) := by
    rw [show 30 * t * Delta = (30 : ℝ) * (t * Delta) by ring]
    exact Real.sqrt_mul (by norm_num) _
  have hsqrt6 :
      Real.sqrt (6 * t * Delta) =
        Real.sqrt 6 * Real.sqrt (t * Delta) := by
    rw [show 6 * t * Delta = (6 : ℝ) * (t * Delta) by ring]
    exact Real.sqrt_mul (by norm_num) _
  have hsqrt30_bound : Real.sqrt 30 ≤ 11 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hsqrt6_bound : Real.sqrt 6 ≤ 5 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hconstant :
      3 * Real.sqrt 30 + 2 * Real.sqrt 6 ≤ 43 / 2 := by
    linarith
  rw [hsqrt30, hsqrt6]
  have hcoef :
      C * (3 * Real.sqrt 30 + 2 * Real.sqrt 6) ≤
        5 + (43 / 2 : ℝ) * C := by
    have hscaled :
        C * (3 * Real.sqrt 30 + 2 * Real.sqrt 6) ≤
          C * (43 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hconstant hC.le
    linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt (t * Delta) :=
    Real.sqrt_nonneg _
  calc
    3 * C * (Real.sqrt 30 * Real.sqrt (t * Delta)) +
        2 * C * (Real.sqrt 6 * Real.sqrt (t * Delta)) =
        (C * (3 * Real.sqrt 30 + 2 * Real.sqrt 6)) *
          Real.sqrt (t * Delta) := by ring
    _ ≤ (5 + (43 / 2 : ℝ) * C) * Real.sqrt (t * Delta) :=
      mul_le_mul_of_nonneg_right hcoef hsqrt_nonneg

lemma exists_centered_fine_interval
    {I : ParameterInterval}
    {p : UnitPoint}
    {L : ℝ}
    (hL_pos : 0 < L)
    (hp : p ∈ I.centeredCarrier (1 / 8))
    (hL_half_le : L / 2 ≤ I.length / 16) :
    ∃ J : ParameterInterval,
      J.length = L ∧
        J.midpoint = (p : ℝ) ∧
        p ∈ J.carrier ∧
        J.carrier ⊆ I.centeredCarrier (1 / 4) := by
  let pval : ℝ := p
  have hp_centered :
      |pval - I.midpoint| ≤ I.length / 16 := by
    change |pval - I.midpoint| ≤ (1 / 8 : ℝ) * I.length / 2 at hp
    calc
      |pval - I.midpoint| ≤
          (1 / 8 : ℝ) * I.length / 2 := hp
      _ = I.length / 16 := by ring
  let J : ParameterInterval :=
    { left := pval - L / 2
      right := pval + L / 2
      left_mem := by
        have hp_lower :
            I.midpoint - I.length / 16 ≤ pval := by
          have habs := (abs_le.mp hp_centered).1
          linarith
        have hmid_lower :
            I.left ≤ I.midpoint - I.length / 8 := by
          dsimp only [ParameterInterval.midpoint,
            ParameterInterval.length]
          linarith [I.left_le_right]
        have hleft : I.left ≤ pval - L / 2 := by
          linarith
        exact
          ⟨I.left_mem.1.trans hleft,
            (sub_le_self pval (by positivity)).trans p.property.2⟩
      right_mem := by
        have hp_upper :
            pval ≤ I.midpoint + I.length / 16 := by
          have habs := (abs_le.mp hp_centered).2
          linarith
        have hmid_upper :
            I.midpoint + I.length / 8 ≤ I.right := by
          dsimp only [ParameterInterval.midpoint,
            ParameterInterval.length]
          linarith [I.left_le_right]
        have hright : pval + L / 2 ≤ I.right := by
          linarith
        exact
          ⟨p.property.1.trans (le_add_of_nonneg_right (by positivity)),
            hright.trans I.right_mem.2⟩
      left_le_right := by linarith }
  have hJ_length : J.length = L := by
    simp only [J, ParameterInterval.length]
    ring
  have hJ_midpoint : J.midpoint = (p : ℝ) := by
    simp only [J, ParameterInterval.midpoint, pval]
    ring
  have hpJ : p ∈ J.carrier := by
    simp only [J, ParameterInterval.carrier, Set.mem_setOf_eq, pval]
    constructor <;> linarith
  have hJ_subset :
      J.carrier ⊆ I.centeredCarrier (1 / 4) := by
    intro x hx
    have hxp : |(x : ℝ) - pval| ≤ L / 2 := by
      simp only [J, ParameterInterval.carrier, Set.mem_setOf_eq] at hx
      rw [abs_le]
      constructor <;> linarith
    have htriangle :
        |(x : ℝ) - I.midpoint| ≤
          |(x : ℝ) - pval| + |pval - I.midpoint| := by
      have heq :
          (x : ℝ) - I.midpoint =
            ((x : ℝ) - pval) + (pval - I.midpoint) := by ring
      rw [heq]
      exact abs_add_le _ _
    have hbound :
        |(x : ℝ) - I.midpoint| ≤ I.length / 8 := by
      linarith
    change
      |(x : ℝ) - I.midpoint| ≤
        (1 / 4 : ℝ) * I.length / 2
    convert hbound using 1 <;> ring
  exact ⟨J, hJ_length, hJ_midpoint, hpJ, hJ_subset⟩

theorem fine_rectangle_assignment
    (hTangency : TangencyGeometryCompletionStatement) :
    FineRectangleAssignmentStatement := by
  intro K D hK hD
  rcases hTangency K D hK hD with ⟨C, hC_pos, hTangency_main⟩
  let C_R : ℝ := max (144 * C^2) (9216 * K^2)
  use C_R
  have hC_R_large : 9216 * K^2 ≤ C_R :=
    le_max_right _ _
  have hK_pos : 0 < K := by linarith
  have hC_R_pos : 0 < C_R := by positivity
  have hsqrt_C_R_ge_12C : Real.sqrt C_R ≥ 12 * C := by
    have h1 : C_R ≥ 144 * C^2 := le_max_left _ _
    have h2 : 0 ≤ 12 * C := by positivity
    have h3 : (12 * C)^2 ≤ C_R := by nlinarith
    have h4 : (12 * C)^2 ≤ (Real.sqrt C_R)^2 := by
      rw [Real.sq_sqrt (by positivity)]; linarith
    nlinarith [Real.sqrt_nonneg C_R]
  have hsqrt_C_R_ge_96K : Real.sqrt C_R ≥ 96 * K := by
    have h1 : C_R ≥ 9216 * K^2 := le_max_right _ _
    have h2 : 0 ≤ 96 * K := by positivity
    have h3 : (96 * K)^2 ≤ C_R := by nlinarith
    have h4 : (96 * K)^2 ≤ (Real.sqrt C_R)^2 := by
      rw [Real.sq_sqrt (by positivity)]; linarith
    nlinarith [Real.sqrt_nonneg C_R]
  have h_main : ∀ (family : Set C2Function), IsCinematicFamily family K D →
      ∀ (I : ParameterInterval), I.IsControlled K →
      ∀ (delta t Delta : ℝ), 0 < delta → delta ≤ Delta → Delta ≤ t →
      ∀ (t' : ℝ), t' = C_R * t * Delta / delta →
      ∀ (p : UnitPoint × ℝ), p.1 ∈ I.centeredCarrier (1 / 8) →
      ∀ (k : C2Function), k ∈ family → |p.2 - k p.1| ≤ delta →
      ∀ (G : FiniteFunctionFamily), G.carrier ⊆ family →
      (∀ f ∈ G.carrier, c2Distance f k ≤ 6 * t ∧
        tangencyParameterOn I f k ≤ Delta ∧ |p.2 - f p.1| ≤ delta) →
      ∃ (R : CurvilinearRectangle delta t'),
        R.function = k ∧ R.interval.midpoint = (p.1 : ℝ) ∧
        p ∈ R.carrier ∧
        R.IsOverCentralQuarterOf I ∧ ∀ f ∈ G.carrier, R.IsLambdaTangent f 5 := by
    intro family hfamily I hI delta t Delta hdelta hdelta_Delta hDelta_t t' ht'_def
    intro p hp1 k hk hpk G hG_sub hG
    have hDelta_pos : 0 < Delta := by linarith
    have ht_pos : 0 < t := by linarith
    have ht'_pos : 0 < t' := by rw [ht'_def]; positivity
    set L : ℝ := Real.sqrt (delta / t') with hL_def
    have hL_pos : 0 < L := by rw [hL_def]; positivity
    rcases fine_rectangle_scale_bounds hK hC_R_pos
      hsqrt_C_R_ge_96K hdelta hdelta_Delta hDelta_t ht'_def hL_def hI with
      ⟨hL_eq, hL_half_le_s, hL_half_le_I_len_16⟩
    set pval : ℝ := (p.1 : ℝ) with hpval_def
    have hp1_carrier : p.1 ∈ I.carrier :=
      I.centeredCarrier_subset_carrier (by norm_num) (by norm_num) hp1
    rcases exists_centered_fine_interval hL_pos hp1
      hL_half_le_I_len_16 with
      ⟨J, hJ_length, hJ_midpoint, hpJ, hJ_over⟩
    let R : CurvilinearRectangle delta t' :=
      { function := k
        interval := J
        interval_length := by rw [hJ_length, hL_def] }
    have hR_function : R.function = k := by rfl
    have hR_midpoint : R.interval.midpoint = (p.1 : ℝ) := by
      simpa [R] using hJ_midpoint
    have h_p_in_R : p ∈ R.carrier := by
      exact ⟨hpJ, hpk⟩
    have hR_over : R.IsOverCentralQuarterOf I := hJ_over
    have h_main_tangent : ∀ f ∈ G.carrier, R.IsLambdaTangent f 5 := by
      intro f hf
      have hfd : c2Distance f k ≤ 6 * t := (hG f hf).1
      have hft : tangencyParameterOn I f k ≤ Delta := (hG f hf).2.1
      have hfp : |p.2 - f p.1| ≤ delta := (hG f hf).2.2
      have hf_in_family : f ∈ family := hG_sub hf
      by_cases hfk : f = k
      · -- Trivial case: f = k
        subst hfk
        intro q hq
        have h10 : |q.2 - f q.1| ≤ delta := hq.2
        have h11 : |q.2 - f q.1| ≤ 5 * delta := by linarith [hdelta]
        exact h11
      · set d : ℝ := c2Distance f k with hd_def
        have hd_nonneg : 0 ≤ d := dist_nonneg
        let h_ext : ℝ → ℝ := f.extension - k.extension
        have h_h_c2 : ContDiff ℝ 2 h_ext := ContDiff.sub f.extension_contDiff k.extension_contDiff
        have hH1 : Differentiable ℝ h_ext := ContDiff.differentiable h_h_c2 (by norm_num)
        have hH2 : Differentiable ℝ (deriv h_ext) :=
          ContDiff.differentiable (ContDiff.deriv' (n := 1) h_h_c2) (by norm_num)
        have h_deriv_ext : ∀ (z : UnitPoint), deriv h_ext z = f.firstDeriv z - k.firstDeriv z := by
          intro z
          have h1 : deriv h_ext z = deriv f.extension z - deriv k.extension z := by
            rw [show deriv h_ext = fun w => deriv f.extension w - deriv k.extension w from by
              funext w; exact deriv_sub (f.extension_contDiff.differentiable (by norm_num) w)
                (k.extension_contDiff.differentiable (by norm_num) w)]
            <;> rfl
          rw [h1, C2Function.deriv_extension_eq_firstDeriv f z,
            C2Function.deriv_extension_eq_firstDeriv k z] <;> ring
        have hH''_bound : ∀ (z : ℝ), z ∈ Set.Icc (0 : ℝ) 1 → |deriv (deriv h_ext) z| ≤ d := by
          intro z hz
          let z' : UnitPoint := ⟨z, ⟨hz.1, hz.2⟩⟩
          have h3 : deriv (deriv h_ext) z = f.secondDeriv z' - k.secondDeriv z' := by
            have h_eq1 : deriv h_ext = fun w => deriv f.extension w - deriv k.extension w := by
              funext w; exact deriv_sub (f.extension_contDiff.differentiable (by norm_num) w)
                (k.extension_contDiff.differentiable (by norm_num) w)
            rw [h_eq1]
            have h : deriv (fun w : ℝ => deriv f.extension w - deriv k.extension w) z =
                deriv (deriv f.extension) z - deriv (deriv k.extension) z := by
              exact deriv_sub
                (ContDiff.differentiable (ContDiff.deriv' (n := 1) f.extension_contDiff) (by norm_num) z)
                (ContDiff.differentiable (ContDiff.deriv' (n := 1) k.extension_contDiff) (by norm_num) z)
            rw [h, C2Function.secondDeriv_extension_eq_secondDeriv f z',
              C2Function.secondDeriv_extension_eq_secondDeriv k z'] <;> ring
          rw [h3]; exact abs_secondDeriv_sub_le_c2Distance f k z'
        have h_abs_h_p1_le : |f p.1 - k p.1| ≤ 2 * delta := by
          have h1 : |f p.1 - k p.1| ≤ |f p.1 - p.2| + |p.2 - k p.1| := by
            have h_eq : f p.1 - k p.1 = (f p.1 - p.2) + (p.2 - k p.1) := by ring
            rw [h_eq]; exact abs_add_le (f p.1 - p.2) (p.2 - k p.1)
          rw [abs_sub_comm (f p.1) p.2] at h1
          linarith [hfp, hpk]
        have h_abs_h'_bound : |deriv h_ext pval| ≤ (5 + (43 / 2 : ℝ) * C) * Real.sqrt (t * Delta) := by
          have h_dec : d < 24 * K * delta ∨ d ≥ 24 * K * delta :=
            lt_or_ge d (24 * K * delta)
          rcases h_dec with (h_small | h_large)
          · -- Case 1: small d
            have h_attained : ∃ (x0 : UnitPoint), x0 ∈ I.centeredCarrier (1 / 2) ∧
                |f x0 - k x0| + |f.firstDeriv x0 - k.firstDeriv x0| = tangencyParameterOn I f k := by
              simpa using tangency_parameter_attained I f k
            rcases h_attained with ⟨x0, hx0_centered, hx0_eq⟩
            have h_abs_f'x0_le : |f.firstDeriv x0 - k.firstDeriv x0| ≤ Delta := by
              have h : |f x0 - k x0| + |f.firstDeriv x0 - k.firstDeriv x0| = tangencyParameterOn I f k := hx0_eq
              have h2 : |f.firstDeriv x0 - k.firstDeriv x0| ≤ tangencyParameterOn I f k := by
                have h3 : 0 ≤ |f x0 - k x0| := by positivity
                linarith [h]
              linarith [hft, h2]
            have h_y_abs_le_sixth : |pval - (x0 : ℝ)| ≤ 1 / (6 * K) := by
              have h_p1_left : I.left ≤ pval := hp1_carrier.1
              have h_p1_right : pval ≤ I.right := hp1_carrier.2
              have hx0_carrier : x0 ∈ I.carrier :=
                I.centeredCarrier_subset_carrier (by norm_num) (by norm_num)
                  hx0_centered
              have h_x0_left : I.left ≤ (x0 : ℝ) := hx0_carrier.1
              have h_x0_right : (x0 : ℝ) ≤ I.right := hx0_carrier.2
              have h1 : |pval - (x0 : ℝ)| ≤ I.length := by
                have h5 : pval - (x0 : ℝ) ≤ I.right - I.left := by linarith
                have h6 : -(pval - (x0 : ℝ)) ≤ I.right - I.left := by linarith
                have h7 : I.right - I.left = I.length := by simp [ParameterInterval.length] <;> ring
                rw [abs_le]; constructor <;> rw [←h7] <;> linarith
              have h2 : I.length ≤ 1 / (6 * K) := by
                have h21 : I.IsShort K := hI.2
                simpa [ParameterInterval.IsShort] using h21
              linarith
            have h_deriv_p1 : deriv h_ext pval = f.firstDeriv p.1 - k.firstDeriv p.1 := h_deriv_ext p.1
            have h_deriv_x0 : deriv h_ext x0 = f.firstDeriv x0 - k.firstDeriv x0 := h_deriv_ext x0
            have h_lip : |deriv h_ext pval - deriv h_ext x0| ≤ d * |pval - (x0 : ℝ)| := by
              have h_orig := lipschitz_deriv f k x0 p.1
              have h1 : |f.firstDeriv x0 - k.firstDeriv x0 - (f.firstDeriv p.1 - k.firstDeriv p.1)| ≤
                  c2Distance f k * |(x0 : ℝ) - (p.1 : ℝ)| := h_orig
              have h2 : |f.firstDeriv x0 - k.firstDeriv x0 - (f.firstDeriv p.1 - k.firstDeriv p.1)| =
                  |f.firstDeriv p.1 - k.firstDeriv p.1 - (f.firstDeriv x0 - k.firstDeriv x0)| := by
                have h3 : f.firstDeriv x0 - k.firstDeriv x0 - (f.firstDeriv p.1 - k.firstDeriv p.1) =
                    -(f.firstDeriv p.1 - k.firstDeriv p.1 - (f.firstDeriv x0 - k.firstDeriv x0)) := by ring
                rw [h3, abs_neg]
              have h4 : |(x0 : ℝ) - (p.1 : ℝ)| = |pval - (x0 : ℝ)| := by
                rw [abs_sub_comm] <;> rfl
              have h5 : |f.firstDeriv p.1 - k.firstDeriv p.1 - (f.firstDeriv x0 - k.firstDeriv x0)| ≤
                  d * |pval - (x0 : ℝ)| := by
                rw [←h2, ←h4, hd_def]
                exact h1
              have h6 : deriv h_ext pval - deriv h_ext x0 = f.firstDeriv p.1 - k.firstDeriv p.1 - (f.firstDeriv x0 - k.firstDeriv x0) := by
                rw [h_deriv_p1, h_deriv_x0] <;> ring
              rw [h6]
              exact h5
            have h_triangle : |deriv h_ext pval| ≤ |deriv h_ext x0| + |deriv h_ext pval - deriv h_ext x0| := by
              have h_eq : deriv h_ext pval = deriv h_ext x0 + (deriv h_ext pval - deriv h_ext x0) := by ring
              rw [h_eq]
              have h := abs_add_le (a := deriv h_ext x0) (b := deriv h_ext pval - deriv h_ext x0)
              simpa using h
            have h6 : |deriv h_ext x0| ≤ Delta := by
              rw [h_deriv_x0]; exact h_abs_f'x0_le
            have h7 : |deriv h_ext pval| ≤ Delta + d * |pval - (x0 : ℝ)| := by
              linarith [h_triangle, h6, h_lip]
            have h8 : |deriv h_ext pval| ≤ Delta + d * (1 / (6 * K)) := by
              have h81 : |pval - (x0 : ℝ)| ≤ 1 / (6 * K) := h_y_abs_le_sixth
              have h82 : 0 ≤ d := hd_nonneg
              have h83 : d * |pval - (x0 : ℝ)| ≤ d * (1 / (6 * K)) := mul_le_mul_of_nonneg_left h81 h82
              linarith [h7, h83]
            have h9 : d * (1 / (6 * K)) < 4 * delta := by
              have h10 : d < 24 * K * delta := h_small
              have h11 : d * (1 / (6 * K)) < (24 * K * delta) * (1 / (6 * K)) := by gcongr
              have h12 : (24 * K * delta) * (1 / (6 * K)) = 4 * delta := by
                field_simp [hK_pos.ne'] <;> ring
              rw [h12] at h11; exact h11
            have h10 : |deriv h_ext pval| < Delta + 4 * delta := by linarith
            have h11 : |deriv h_ext pval| ≤ 5 * Delta := by linarith [hdelta_Delta]
            have h14 : Delta ≤ Real.sqrt (t * Delta) := by
              have h_nonneg : 0 ≤ t * Delta := by positivity
              have h3 : 0 ≤ Delta := by linarith
              have h4 : Delta^2 ≤ t * Delta := by
                calc Delta^2 = Delta * Delta := by ring
                  _ ≤ Delta * t := by exact mul_le_mul_of_nonneg_left hDelta_t h3
                  _ = t * Delta := by ring
              have h_sq : Delta^2 ≤ (Real.sqrt (t * Delta))^2 := by
                rw [Real.sq_sqrt h_nonneg]
                exact h4
              exact le_of_sq_le_sq h_sq (Real.sqrt_nonneg _)
            have h15 : 0 ≤ (43 / 2 : ℝ) * C := by positivity
            have h16 : |deriv h_ext pval| ≤ (5 + (43 / 2 : ℝ) * C) * Real.sqrt (t * Delta) := by
              have h17 : |deriv h_ext pval| ≤ 5 * Real.sqrt (t * Delta) := by
                calc |deriv h_ext pval|
                  ≤ 5 * Delta := h11
                _ ≤ 5 * Real.sqrt (t * Delta) := by
                  exact mul_le_mul_of_nonneg_left h14 (by norm_num)
              have h18 : 5 * Real.sqrt (t * Delta) ≤ (5 + (43 / 2 : ℝ) * C) * Real.sqrt (t * Delta) := by
                have h19 : 0 ≤ Real.sqrt (t * Delta) := by positivity
                have h20 : (5 + (43 / 2 : ℝ) * C) * Real.sqrt (t * Delta) =
                    5 * Real.sqrt (t * Delta) + (43 / 2 : ℝ) * C * Real.sqrt (t * Delta) := by ring
                rw [h20]
                have h21 : 0 ≤ (43 / 2 : ℝ) * C * Real.sqrt (t * Delta) := by positivity
                linarith
              exact le_trans h17 h18
            exact h16
          · -- Case 2: large d (d ≥ 24 * K * delta)
            have h_d_large : d ≥ 24 * K * delta := by linarith
            have h_condition : 4 * delta ≤ d / (6 * K) := by
              have h : 24 * K * delta ≤ d := h_d_large
              have h2 : d / (6 * K) ≥ 4 * delta := by
                calc d / (6 * K) ≥ (24 * K * delta) / (6 * K) := by gcongr
                  _ = 4 * delta := by field_simp [hK_pos.ne'] <;> ring
              linarith
            have hT := hTangency_main family hfamily I hI f hf_in_family k hk hfk
              (4 * delta) (by positivity) h_condition
            rcases hT with ⟨h_pieces_data, _h_quadratic⟩
            rcases h_pieces_data with ⟨pieces, hcard, hunion, halllen, hmem⟩
            let scale : ℝ := Real.sqrt ((tangencyParameterOn I f k + 4 * delta) * d)
            have h_d_pos : 0 < d := by
              have h : d ≥ 24 * K * delta := h_d_large
              have h2 : 0 < 24 * K * delta := by positivity
              linarith
            have h_tp_nonneg : 0 ≤ tangencyParameterOn I f k := by
              have h_mid_in_interval : I.midpoint ∈ unitInterval := by
                simp only [unitInterval, Set.mem_Icc, ParameterInterval.midpoint]
                constructor <;> linarith [I.left_mem.1, I.left_mem.2, I.right_mem.1, I.right_mem.2, I.left_le_right]
              let x_mid : UnitPoint := ⟨I.midpoint, h_mid_in_interval⟩
              have h_x_mid_in_S : x_mid ∈ I.centeredCarrier (1 / 2) := by
                simp only [ParameterInterval.centeredCarrier, Set.mem_setOf_eq]
                simp [x_mid, ParameterInterval.midpoint]
                linarith [I.length_nonneg]
              let S : Set ℝ := {r | ∃ x ∈ I.centeredCarrier (1 / 2), r = |f x - k x| + |f.firstDeriv x - k.firstDeriv x|}
              have h_nonempty : Set.Nonempty S := by
                refine ⟨|f x_mid - k x_mid| + |f.firstDeriv x_mid - k.firstDeriv x_mid|, ?_⟩
                exact ⟨x_mid, h_x_mid_in_S, rfl⟩
              have h_nonneg : ∀ r ∈ S, 0 ≤ r := by
                intro r hr
                rcases hr with ⟨x, _, rfl⟩
                positivity
              exact le_csInf h_nonempty h_nonneg
            have h1 : 0 < (tangencyParameterOn I f k + 4 * delta) * d := by
              have h2 : 0 < tangencyParameterOn I f k + 4 * delta := by linarith
              exact mul_pos h2 h_d_pos
            have hscale_pos : 0 < scale := Real.sqrt_pos.mpr h1
            have hp1_in_sublevel2 : p.1 ∈ tangencySublevelSetOn I f k (2 * delta) := by
              have h1 : p.1 ∈ I.centeredCarrier (1 / 4) := by
                have h_scaling : I.centeredCarrier (1 / 8) ⊆ I.centeredCarrier (1 / 4) := by
                  intro x hx
                  have h2 : |(x : ℝ) - I.midpoint| ≤ (1 / 8 : ℝ) * I.length / 2 := hx
                  have h3 : (1 / 8 : ℝ) * I.length / 2 ≤ (1 / 4 : ℝ) * I.length / 2 := by
                    have h4 : 0 ≤ I.length := I.length_nonneg
                    have h5 : (1 / 8 : ℝ) ≤ (1 / 4 : ℝ) := by norm_num
                    have h6 : (1 / 8 : ℝ) * I.length ≤ (1 / 4 : ℝ) * I.length := mul_le_mul_of_nonneg_right h5 h4
                    linarith
                  have h7 : |(x : ℝ) - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := by linarith
                  exact h7
                exact h_scaling hp1
              have h2 : |f p.1 - k p.1| ≤ 2 * delta := h_abs_h_p1_le
              exact ⟨h1, h2⟩
            have hmem' : ∀ (x : UnitPoint), x ∈ tangencySublevelSetOn I f k (2 * delta) →
                ∃ (j : Fin pieces.card), x ∈ (pieces.interval j).carrier ∧
                  4 * delta ≤ C * scale * (pieces.interval j).length := by
              intro x hx
              have hdelta_eq : (4 * delta / 2 : ℝ) = 2 * delta := by ring
              have hx' : x ∈ tangencySublevelSetOn I f k (4 * delta / 2) := by
                rw [hdelta_eq]; exact hx
              have h := hmem x hx'
              rcases h with ⟨j, hj_in, hj_len⟩
              have h_goal : 4 * delta ≤ C * scale * (pieces.interval j).length := by
                have h1 : scale = Real.sqrt ((tangencyParameterOn I f k + 4 * delta) * d) := by rfl
                rw [h1]
                have h_d_eq : d = c2Distance f k := by rfl
                rw [h_d_eq]
                exact hj_len
              exact ⟨j, hj_in, h_goal⟩
            rcases hmem' p.1 hp1_in_sublevel2 with ⟨j, hj_in, hj_len⟩
            let J_p : ParameterInterval := pieces.interval j
            let ℓ : ℝ := J_p.length
            have hℓ_nonneg : 0 ≤ ℓ := J_p.length_nonneg
            have hℓ_lower : 4 * delta ≤ C * scale * ℓ := hj_len
            have hℓ_upper : ℓ ≤ C * (4 * delta) / scale := halllen j
            have hℓ_pos : 0 < ℓ := by
              have h1 : 4 * delta ≤ C * scale * ℓ := hℓ_lower
              by_contra h6
              have h7 : ℓ ≤ 0 := by linarith
              have h8 : C * scale * ℓ ≤ 0 := by
                exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h7
              linarith
            have hp1_in_Jp : p.1 ∈ J_p.carrier := hj_in
            have h_p1_bounds : J_p.left ≤ pval ∧ pval ≤ J_p.right := hp1_in_Jp
            have hJp_in_sublevel : J_p.carrier ⊆ tangencySublevelSetOn I f k (4 * delta) := by
              intro x hx
              have h_in_union : x ∈ pieces.union := ⟨j, hx⟩
              rw [←hunion] at h_in_union
              exact h_in_union
            have h_bound_Jp : ∀ x ∈ Set.Icc J_p.left J_p.right, |h_ext x| ≤ 4 * delta := by
              intro x hx
              have hx_unit : x ∈ Set.Icc (0 : ℝ) 1 := by
                have h1 : J_p.left ≤ x := hx.1
                have h2 : x ≤ J_p.right := hx.2
                exact ⟨by linarith [J_p.left_mem.1], by linarith [J_p.right_mem.2]⟩
              let x' : UnitPoint := ⟨x, hx_unit⟩
              have h_x'_in_Jp : x' ∈ J_p.carrier := ⟨hx.1, hx.2⟩
              have h_x'_in_union : x' ∈ pieces.union := ⟨j, h_x'_in_Jp⟩
              have h_x'_in_sublevel : x' ∈ tangencySublevelSetOn I f k (4 * delta) := by
                rw [←hunion] at h_x'_in_union
                exact h_x'_in_union
              have h1 : h_ext x = f x' - k x' := by
                have h11 : h_ext x = f.extension x - k.extension x := by simp [h_ext] <;> rfl
                have h12 : f.extension x = f x' := C2Function.extension_eq_value f x'
                have h13 : k.extension x = k x' := C2Function.extension_eq_value k x'
                rw [h11, h12, h13] <;> rfl
              rw [h1]
              exact h_x'_in_sublevel.2
            have hA : |h_ext pval| ≤ 2 * delta := by
              have h1 : h_ext pval = f.extension pval - k.extension pval := by simp [h_ext] <;> rfl
              have h2 : f.extension pval = f p.1 := C2Function.extension_eq_value f p.1
              have h3 : k.extension pval = k p.1 := C2Function.extension_eq_value k p.1
              have h4 : h_ext pval = f p.1 - k p.1 := by rw [h1, h2, h3] <;> rfl
              rw [h4]
              exact h_abs_h_p1_le
            have h_side :
                J_p.right - pval ≥ ℓ / 2 ∨
                  pval - J_p.left ≥ ℓ / 2 :=
              parameter_interval_one_side_ge_half J_p pval ℓ
                h_p1_bounds rfl
            have h_deriv_lipschitz_Jp : ∀ (x : ℝ), x ∈ Set.Icc J_p.left J_p.right →
                ∀ (y : ℝ), y ∈ Set.Icc J_p.left J_p.right →
                |deriv h_ext x - deriv h_ext y| ≤ d * |x - y| := by
              intro x hx y hy
              have hx_unit : x ∈ Set.Icc (0 : ℝ) 1 :=
                ⟨le_trans J_p.left_mem.1 hx.1, le_trans hx.2 J_p.right_mem.2⟩
              have hy_unit : y ∈ Set.Icc (0 : ℝ) 1 :=
                ⟨le_trans J_p.left_mem.1 hy.1, le_trans hy.2 J_p.right_mem.2⟩
              let x' : UnitPoint := ⟨x, hx_unit⟩
              let y' : UnitPoint := ⟨y, hy_unit⟩
              exact deriv_lipschitz_helper h_deriv_ext hd_def x' y'
            have h_deriv_bound : |deriv h_ext pval| ≤ (4 * delta + 2 * delta) / (ℓ / 2) + d * J_p.length :=
              apply_mvt_bound hH1 h_bound_Jp hA h_side hℓ_pos hd_nonneg h_deriv_lipschitz_Jp h_p1_bounds
            have h_Jp_len : J_p.length = ℓ := by rfl
            have h_bound1 : |deriv h_ext pval| ≤ 12 * delta / ℓ + d * ℓ := by
              rw [h_Jp_len] at h_deriv_bound
              have h9 : (4 * delta + 2 * delta) / (ℓ / 2) = 12 * delta / ℓ := by
                field_simp [hℓ_pos.ne'] <;> ring
              rw [h9] at h_deriv_bound
              exact h_deriv_bound
            have h_scale_lower : scale ≥ 2 * Real.sqrt (delta * d) := by
              have h_tp_nonneg : 0 ≤ tangencyParameterOn I f k := by positivity
              have h1 : tangencyParameterOn I f k + 4 * delta ≥ 4 * delta := by linarith
              have h2 : (tangencyParameterOn I f k + 4 * delta) * d ≥ 4 * delta * d := by gcongr
              have h3 : Real.sqrt ((tangencyParameterOn I f k + 4 * delta) * d) ≥ Real.sqrt (4 * delta * d) := Real.sqrt_le_sqrt h2
              have h4 : Real.sqrt (4 * delta * d) = 2 * Real.sqrt (delta * d) := by
                have h5 : 0 ≤ delta := by linarith
                have h6 : 0 ≤ d := hd_nonneg
                rw [show (4 * delta * d) = 4 * (delta * d) by ring]
                rw [Real.sqrt_mul (by positivity)]
                have h7 : Real.sqrt 4 = 2 := by
                  rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq] <;> norm_num
                rw [h7] <;> ring
              rw [h4] at h3; exact h3
            have h_scale_upper : scale ≤ Real.sqrt (5 * Delta * d) := by
              have h_tp_le : tangencyParameterOn I f k ≤ Delta := hft
              have h1 : tangencyParameterOn I f k + 4 * delta ≤ 5 * Delta := by linarith [hdelta_Delta]
              have h2 : (tangencyParameterOn I f k + 4 * delta) * d ≤ (5 * Delta) * d := by gcongr
              exact Real.sqrt_le_sqrt h2
            have h_term1 : 12 * delta / ℓ ≤ 3 * C * scale := by
              have h : 12 * delta / ℓ ≤ 12 * delta / (4 * delta / (C * scale)) := by
                gcongr
                have h' : 0 < 4 * delta / (C * scale) := by positivity
                have h9 : C * scale * ℓ ≥ 4 * delta := hℓ_lower
                have h10 : 0 < C * scale := by positivity
                have h'' : ℓ ≥ 4 * delta / (C * scale) := by
                  have h11 : ℓ = (C * scale * ℓ) / (C * scale) := by field_simp [h10.ne'] <;> ring
                  rw [h11]
                  exact div_le_div_of_nonneg_right h9 h10.le
                exact h''
              have h_eq : 12 * delta / (4 * delta / (C * scale)) = 3 * C * scale := by
                field_simp [hdelta.ne', hC_pos.ne', hscale_pos.ne'] <;> ring
              exact h.trans_eq h_eq
            have h_term2 : d * ℓ ≤ 4 * C * d * delta / scale := by
              calc d * ℓ ≤ d * (C * (4 * delta) / scale) := by gcongr
                _ = 4 * C * d * delta / scale := by ring
            have h_term2' : 4 * C * d * delta / scale ≤ 2 * C * Real.sqrt (delta * d) := by
              have h1 : scale ≥ 2 * Real.sqrt (delta * d) := h_scale_lower
              have h2 : 0 < scale := hscale_pos
              have h3 : 0 ≤ 4 * C * d * delta := by positivity
              calc 4 * C * d * delta / scale
                ≤ 4 * C * d * delta / (2 * Real.sqrt (delta * d)) := by gcongr
                _ = 2 * C * Real.sqrt (delta * d) := by
                  by_cases h4 : d = 0
                  · rw [h4]; simp
                  · have h5 : 0 < Real.sqrt (delta * d) := by positivity
                    have h6 : (Real.sqrt (delta * d)) ^ 2 = delta * d := Real.sq_sqrt (by positivity)
                    have h7 : 4 * C * d * delta = 2 * C * Real.sqrt (delta * d) * (2 * Real.sqrt (delta * d)) := by
                      calc 4 * C * d * delta
                        = 4 * C * (delta * d) := by ring
                      _ = 4 * C * (Real.sqrt (delta * d)) ^ 2 := by rw [h6] <;> ring
                      _ = 2 * C * Real.sqrt (delta * d) * (2 * Real.sqrt (delta * d)) := by ring
                    exact (div_eq_iff (by positivity)).mpr h7
            have h_bound2 : 12 * delta / ℓ + d * ℓ ≤ 3 * C * scale + 2 * C * Real.sqrt (delta * d) := by
              calc 12 * delta / ℓ + d * ℓ
                ≤ 3 * C * scale + d * ℓ := by gcongr
              _ ≤ 3 * C * scale + (4 * C * d * delta / scale) := by gcongr
              _ ≤ 3 * C * scale + 2 * C * Real.sqrt (delta * d) := by gcongr
            have h_main_bound : |deriv h_ext pval| ≤ 3 * C * scale + 2 * C * Real.sqrt (delta * d) :=
              le_trans h_bound1 h_bound2
            have h_d_le_6t : d ≤ 6 * t := hfd
            have h1 : 3 * C * scale ≤ 3 * C * Real.sqrt (5 * Delta * d) := by gcongr
            have h2 : 3 * C * Real.sqrt (5 * Delta * d) ≤ 3 * C * Real.sqrt (30 * t * Delta) := by
              have h3 : 5 * Delta * d ≤ 30 * t * Delta := by
                have h31 : 5 * Delta * d ≤ 5 * Delta * (6 * t) := by gcongr
                have h32 : 5 * Delta * (6 * t) = 30 * t * Delta := by ring
                rw [h32] at h31
                exact h31
              gcongr
            have h3 : 2 * C * Real.sqrt (delta * d) ≤ 2 * C * Real.sqrt (6 * t * Delta) := by
              have h4 : delta * d ≤ 6 * t * Delta := by
                have h41 : delta * d ≤ Delta * d := by gcongr
                have h42 : Delta * d ≤ Delta * (6 * t) := by gcongr
                have h43 : Delta * (6 * t) = 6 * t * Delta := by ring
                rw [h43] at h42
                exact le_trans h41 h42
              gcongr
            calc
              |deriv h_ext pval| ≤ 3 * C * scale + 2 * C * Real.sqrt (delta * d) := h_main_bound
              _ ≤ 3 * C * Real.sqrt (30 * t * Delta) + 2 * C * Real.sqrt (6 * t * Delta) := by linarith
              _ ≤ (5 + (43 / 2 : ℝ) * C) *
                  Real.sqrt (t * Delta) :=
                fine_rectangle_sqrt_absorption hC_pos (by positivity)
        intro q hq
        have hq1 : q.1 ∈ J.carrier := hq.1
        have hq2 : |q.2 - k q.1| ≤ delta := hq.2
        set xval : ℝ := (q.1 : ℝ) with hxval_def
        have h_x_abs_diff : |xval - pval| ≤ L / 2 := by
          have hmid : (J.left + J.right) / 2 = pval := by
            simpa [ParameterInterval.midpoint, hpval_def] using hJ_midpoint
          have hlength : J.right - J.left = L := by
            simpa [ParameterInterval.length] using hJ_length
          have hleft : J.left = pval - L / 2 := by
            linarith
          have hright : J.right = pval + L / 2 := by
            linarith
          rw [abs_le]
          constructor
          · linarith [hq1.1, hxval_def]
          · linarith [hq1.2, hxval_def]
        have h_x_in_01 : xval ∈ Set.Icc (0 : ℝ) 1 := ⟨q.1.property.1, q.1.property.2⟩
        have hp1_in_01 : pval ∈ Set.Icc (0 : ℝ) 1 := ⟨p.1.property.1, p.1.property.2⟩
        have h_taylor2 : |h_ext xval - h_ext pval - deriv h_ext pval * (xval - pval)| ≤ d / 2 * (xval - pval)^2 :=
          taylor_remainder_bound hH1 hH2 (by norm_num) h_x_in_01 hp1_in_01 hH''_bound
        have h_eval_x : h_ext xval = f q.1 - k q.1 := by
          have h1 : h_ext xval = f.extension xval - k.extension xval := by simp [h_ext] <;> rfl
          have h2 : f.extension xval = f q.1 := C2Function.extension_eq_value f q.1
          have h3 : k.extension xval = k q.1 := C2Function.extension_eq_value k q.1
          rw [h1, h2, h3] <;> rfl
        have h_eval_p : h_ext pval = f p.1 - k p.1 := by
          have h1 : h_ext pval = f.extension pval - k.extension pval := by simp [h_ext] <;> rfl
          have h2 : f.extension pval = f p.1 := C2Function.extension_eq_value f p.1
          have h3 : k.extension pval = k p.1 := C2Function.extension_eq_value k p.1
          rw [h1, h2, h3] <;> rfl
        have h_d2_le_3t : d / 2 ≤ 3 * t := by
          have h : d ≤ 6 * t := hfd; linarith
        have h1 : |h_ext pval| ≤ 2 * delta := by
          rw [h_eval_p]; exact h_abs_h_p1_le
        have h_final_bound : |h_ext xval| ≤ 4 * delta :=
          taylor_final_bound
            (hC_pos := hC_pos)
            (hK := hK)
            (hC_R_pos := hC_R_pos)
            (hdelta := hdelta)
            (hdelta_Delta := hdelta_Delta)
            (ht_pos := ht_pos)
            (hd_nonneg := hd_nonneg)
            (hsqrt_C_R_ge_12C := hsqrt_C_R_ge_12C)
            (hsqrt_C_R_ge_96K := hsqrt_C_R_ge_96K)
            (hL_eq := hL_eq)
            (h_abs_h_p := h1)
            (h_abs_h'_bound := h_abs_h'_bound)
            (h_x_abs_diff := h_x_abs_diff)
            (h_taylor2 := h_taylor2)
            (h_d2_le_3t := h_d2_le_3t)
        have h10 : |f q.1 - k q.1| ≤ 4 * delta := by
          have h11 : h_ext xval = f q.1 - k q.1 := h_eval_x
          rw [h11] at h_final_bound; exact h_final_bound
        have h11 : |q.2 - f q.1| ≤ 5 * delta := by
          have h12 : q.2 - f q.1 = (q.2 - k q.1) - (f q.1 - k q.1) := by ring
          rw [h12]
          have h13 : |(q.2 - k q.1) - (f q.1 - k q.1)| ≤ |q.2 - k q.1| + |f q.1 - k q.1| := by
            exact abs_sub _ _
          calc |(q.2 - k q.1) - (f q.1 - k q.1)|
            ≤ |q.2 - k q.1| + |f q.1 - k q.1| := h13
          _ ≤ delta + 4 * delta := by gcongr
          _ = 5 * delta := by ring
        exact h11
    exact
      ⟨R, hR_function, hR_midpoint, h_p_in_R, hR_over,
        h_main_tangent⟩
  have h_main' : ∀ (family : Set C2Function), IsCinematicFamily family K D →
      ∀ (I : ParameterInterval), I.IsControlled K →
      ∀ (delta t Delta : ℝ), 0 < delta → delta ≤ Delta → Delta ≤ t →
      let t' := C_R * t * Delta / delta;
      ∀ (p : UnitPoint × ℝ), p.1 ∈ I.centeredCarrier (1 / 8) →
      ∀ (k : C2Function), k ∈ family → |p.2 - k p.1| ≤ delta →
      ∀ (G : FiniteFunctionFamily), G.carrier ⊆ family →
      (∀ f ∈ G.carrier, c2Distance f k ≤ 6 * t ∧
        tangencyParameterOn I f k ≤ Delta ∧ |p.2 - f p.1| ≤ delta) →
      ∃ (R : CurvilinearRectangle delta (C_R * t * Delta / delta)),
        R.function = k ∧ R.interval.midpoint = (p.1 : ℝ) ∧
        p ∈ R.carrier ∧
        R.IsOverCentralQuarterOf I ∧ ∀ f ∈ G.carrier, R.IsLambdaTangent f 5 := by
    intro family hfamily I hI delta t Delta hdelta hdelta_Delta hDelta_t
    exact h_main family hfamily I hI delta t Delta hdelta hdelta_Delta hDelta_t
      (C_R * t * Delta / delta) rfl
  exact ⟨hC_R_large, h_main'⟩

end Kakeya.Cinematic
