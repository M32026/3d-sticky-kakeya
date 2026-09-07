import MyLeanRepo.Kakeya.Cinematic.Geometry
import MyLeanRepo.Kakeya.Cinematic.Targets.TangencySublevelDiameter.Helpers
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Sqrt

/-!
# Helper lemmas for CommonTangentRectangle (PYZ Lemma 17)

Tangency bounds and calculus helpers.
-/

namespace Kakeya.Cinematic

/--
If R is λ-tangent to f (λ ≥ 1), then on R.interval,
`|f x - R.function x| ≤ (λ - 1) * δ`.
-/
lemma tangency_implies_value_close {δ t : ℝ} (hδ : 0 < δ)
    (R : CurvilinearRectangle δ t) (f : C2Function) {lambda : ℝ}
    (hlambda : 1 ≤ lambda)
    (h : R.IsLambdaTangent f lambda) :
    ∀ (x : UnitPoint), x ∈ R.interval.carrier →
      |f x - R.function x| ≤ (lambda - 1) * δ := by
  intro x hx
  let p_plus : UnitPoint × ℝ := (x, R.function x + δ)
  let p_minus : UnitPoint × ℝ := (x, R.function x - δ)
  have h_plus_in : p_plus ∈ R.carrier := by
    have h1 : p_plus.1 ∈ R.interval.carrier := hx
    have h2 : |p_plus.2 - R.function p_plus.1| ≤ δ := by
      change |R.function x + δ - R.function x| ≤ δ
      have h3 : R.function x + δ - R.function x = δ := by ring
      rw [h3]
      have h4 : |δ| = δ := abs_of_pos hδ
      rw [h4]
    exact ⟨h1, h2⟩
  have h_minus_in : p_minus ∈ R.carrier := by
    have h1 : p_minus.1 ∈ R.interval.carrier := hx
    have h2 : |p_minus.2 - R.function p_minus.1| ≤ δ := by
      change |R.function x - δ - R.function x| ≤ δ
      have h3 : R.function x - δ - R.function x = -δ := by ring
      rw [h3]
      have h4 : |(-δ : ℝ)| = δ := by
        rw [abs_neg, abs_of_pos hδ]
      rw [h4]
    exact ⟨h1, h2⟩
  have h1 : |(R.function x + δ) - f x| ≤ lambda * δ := h p_plus h_plus_in
  have h2 : |(R.function x - δ) - f x| ≤ lambda * δ := h p_minus h_minus_in
  set d : ℝ := f x - R.function x with hd
  have h3 : |d - δ| ≤ lambda * δ := by
    have h_eq : (R.function x + δ) - f x = -(d - δ) := by
      simp [hd] <;> ring
    rw [h_eq] at h1
    rw [abs_neg] at h1
    exact h1
  have h4 : |d + δ| ≤ lambda * δ := by
    have h_eq : (R.function x - δ) - f x = -(d + δ) := by
      simp [hd] <;> ring
    rw [h_eq] at h2
    rw [abs_neg] at h2
    exact h2
  have h5 : d ≤ (lambda - 1) * δ := by
    have h6 : d + δ ≤ lambda * δ := (abs_le.mp h4).2
    linarith
  have h7 : -(lambda - 1) * δ ≤ d := by
    have h8 : -(lambda * δ) ≤ d - δ := (abs_le.mp h3).1
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- If both f and g are 5-tangent to R, then `|f x - g x| ≤ 8 * δ` on R.interval. -/
lemma both_tangent_implies_close {δ t : ℝ} (hδ : 0 < δ)
    (R : CurvilinearRectangle δ t) (f g : C2Function)
    (hf : R.IsLambdaTangent f 5) (hg : R.IsLambdaTangent g 5) :
    ∀ (x : UnitPoint), x ∈ R.interval.carrier →
      |f x - g x| ≤ 8 * δ := by
  intro x hx
  have h1 : |f x - R.function x| ≤ (5 - 1 : ℝ) * δ :=
    tangency_implies_value_close hδ R f (by norm_num) hf x hx
  have h2 : |g x - R.function x| ≤ (5 - 1 : ℝ) * δ :=
    tangency_implies_value_close hδ R g (by norm_num) hg x hx
  have h1' : |f x - R.function x| ≤ 4 * δ := by
    have h_eq : (5 - 1 : ℝ) * δ = 4 * δ := by ring
    rw [h_eq] at h1; exact h1
  have h2' : |g x - R.function x| ≤ 4 * δ := by
    have h_eq : (5 - 1 : ℝ) * δ = 4 * δ := by ring
    rw [h_eq] at h2; exact h2
  have h_main : |f x - g x| ≤ |f x - R.function x| + |g x - R.function x| := by
    have h_eq : f x - g x = (f x - R.function x) - (g x - R.function x) := by ring
    rw [h_eq]
    exact abs_sub _ _
  calc
    |f x - g x| ≤ |f x - R.function x| + |g x - R.function x| := h_main
    _ ≤ 4 * δ + 4 * δ := by gcongr
    _ = 8 * δ := by ring

/-- The tangency parameter is at most twice the C² distance. -/
lemma tangency_parameter_le_two_d {I : ParameterInterval} {f g : C2Function} :
    tangencyParameterOn I f g ≤ 2 * c2Distance f g := by
  rcases tangency_parameter_attained I f g with ⟨x0, _, h_eq⟩
  have h1 : |f x0 - g x0| ≤ c2Distance f g :=
    abs_value_sub_le_c2Distance f g x0
  have h2 : |f.firstDeriv x0 - g.firstDeriv x0| ≤ c2Distance f g :=
    abs_firstDeriv_sub_le_c2Distance f g x0
  linarith [h_eq]


/-- Variation lower bound: if H'' ≥ c on [a,b], then
H(b) - H(a) ≥ H'(a)*(b-a) + c/2*(b-a)^2. -/
lemma variation_lower_bound {H : ℝ → ℝ} {c a b : ℝ}
    (hH1 : Differentiable ℝ H)
    (hH2 : Differentiable ℝ (deriv H))
    (hab : a ≤ b)
    (ha : a ∈ Set.Icc a b)
    (hb : b ∈ Set.Icc a b)
    (hH'' : ∀ z ∈ Set.Icc a b, c ≤ deriv (deriv H) z) :
    H b - H a ≥ deriv H a * (b - a) + c / 2 * (b - a)^2 := by
  have h := taylor_quadratic_lower_bound hH1 hH2 hab ha hb hH''
  linarith

/-- Zero crossing inside [a,b]: if H'(x0)=0, H'' ≥ c on [a,b], and |H| ≤ M
on [a,b], then c*(b-a)^2 ≤ 16*M. -/
lemma zero_crossing_in_interval {H : ℝ → ℝ} {a b x0 c M : ℝ}
    (hH1 : Differentiable ℝ H)
    (hH2 : Differentiable ℝ (deriv H))
    (hab : a ≤ b)
    (hx0 : x0 ∈ Set.Icc a b)
    (hderiv0 : deriv H x0 = 0)
    (hH'' : ∀ z ∈ Set.Icc a b, c ≤ deriv (deriv H) z)
    (h_bound : ∀ z ∈ Set.Icc a b, |H z| ≤ M)
    (hc_pos : 0 < c)
    (_hM_nonneg : 0 ≤ M) :
    c * (b - a)^2 ≤ 16 * M := by
  have ha_in : a ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  have hb_in : b ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  have h_taylor1 := taylor_quadratic_lower_bound hH1 hH2 hab hx0 ha_in hH''
  have h_taylor2 := taylor_quadratic_lower_bound hH1 hH2 hab hx0 hb_in hH''
  rw [hderiv0] at h_taylor1 h_taylor2
  have h1 : H a ≥ H x0 + c / 2 * (a - x0)^2 := by linarith
  have h2 : H b ≥ H x0 + c / 2 * (b - x0)^2 := by linarith
  have h3 : (a - x0)^2 + (b - x0)^2 ≥ (b - a)^2 / 2 := by
    nlinarith [sq_nonneg (a + b - 2 * x0)]
  have h4 : H a + H b ≥ 2 * H x0 + c / 2 * ((a - x0)^2 + (b - x0)^2) := by linarith
  have h5 : H a + H b ≤ 2 * M := by
    have h6 : |H a| ≤ M := h_bound a ha_in
    have h7 : |H b| ≤ M := h_bound b hb_in
    have h61 : H a ≤ M := (abs_le.mp h6).2
    have h71 : H b ≤ M := (abs_le.mp h7).2
    linarith
  have h8 : H x0 ≥ -M := by
    have h9 : |H x0| ≤ M := h_bound x0 hx0
    exact (abs_le.mp h9).1
  nlinarith

/-- Monotonicity of H' from H'' ≥ 0 on an interval. -/
lemma deriv_monotone_of_deriv2_nonneg {H : ℝ → ℝ} {a_J b_J : ℝ}
    (hH1 : Differentiable ℝ H)
    (hH2 : Differentiable ℝ (deriv H))
    (hH''_nonneg : ∀ x ∈ Set.Icc a_J b_J, 0 ≤ deriv (deriv H) x)
    {x y : ℝ} (hx : x ∈ Set.Icc a_J b_J) (hy : y ∈ Set.Icc a_J b_J)
    (hxy : x ≤ y) : deriv H x ≤ deriv H y := by
  by_cases h : x = y
  · rw [h]
  · have hlt : x < y := lt_of_le_of_ne hxy h
    have hsub : Set.Icc x y ⊆ Set.Icc a_J b_J := by
      intro z hz
      exact ⟨by linarith [hz.1, hx.1], by linarith [hz.2, hy.2]⟩
    have hcont : ContinuousOn (deriv H) (Set.Icc x y) :=
      hH2.continuous.continuousOn.mono hsub
    have hfd : ∀ z ∈ Set.Ioo x y, HasDerivAt (deriv H) (deriv (deriv H) z) z :=
      fun z _ => hH2.differentiableAt.hasDerivAt
    have h_mvt : ∃ (c : ℝ), c ∈ Set.Ioo x y ∧
        deriv (deriv H) c = (deriv H y - deriv H x) / (y - x) :=
      exists_hasDerivAt_eq_slope (f := deriv H) (f' := deriv (deriv H)) hlt hcont hfd
    rcases h_mvt with ⟨c, hc, hderiv⟩
    have hc_in : c ∈ Set.Icc a_J b_J := hsub ⟨by linarith [hc.1], by linarith [hc.2]⟩
    have hH''_nonneg' : 0 ≤ deriv (deriv H) c := hH''_nonneg c hc_in
    have h_pos : 0 < y - x := by linarith
    have h_eq : deriv H y - deriv H x = deriv (deriv H) c * (y - x) := by
      rw [hderiv] <;> field_simp [h_pos.ne'] <;> ring
    have h_main : 0 ≤ deriv (deriv H) c * (y - x) := by positivity
    linarith [h_eq, h_main]

/-- MVT derivative lower bound: if H'' ≥ c on [p,q], then H'(q) - H'(p) ≥ c*(q-p). -/
lemma deriv_increase_lower_bound {H : ℝ → ℝ} {p q c : ℝ}
    (hH2 : Differentiable ℝ (deriv H))
    (hpq : p < q)
    (hH'' : ∀ z ∈ Set.Icc p q, c ≤ deriv (deriv H) z) :
    deriv H q - deriv H p ≥ c * (q - p) := by
  have hcont : ContinuousOn (deriv H) (Set.Icc p q) := hH2.continuous.continuousOn
  have hfd : ∀ z ∈ Set.Ioo p q, HasDerivAt (deriv H) (deriv (deriv H) z) z :=
    fun z _ => hH2.differentiableAt.hasDerivAt
  have h_mvt : ∃ (z : ℝ), z ∈ Set.Ioo p q ∧
      deriv (deriv H) z = (deriv H q - deriv H p) / (q - p) :=
    exists_hasDerivAt_eq_slope (f := deriv H) (f' := deriv (deriv H)) hpq hcont hfd
  rcases h_mvt with ⟨z, hz_in, hderiv_eq⟩
  have hz_in' : z ∈ Set.Icc p q := ⟨by linarith [hz_in.1], by linarith [hz_in.2]⟩
  have hH''z : c ≤ deriv (deriv H) z := hH'' z hz_in'
  have h_pos : 0 < q - p := by linarith
  have h_eq : deriv H q - deriv H p = deriv (deriv H) z * (q - p) := by
    rw [hderiv_eq] <;> field_simp [h_pos.ne'] <;> ring
  have h_ineq : c * (q - p) ≤ deriv (deriv H) z * (q - p) :=
    mul_le_mul_of_nonneg_right hH''z (by linarith)
  linarith [h_eq, h_ineq]

/-- MVT value bound: if H'(z) ≤ M for all z in [p,q], then H(q) - H(p) ≤ M*(q-p). -/
lemma value_increase_upper_bound {H : ℝ → ℝ} {p q M : ℝ}
    (hH1 : Differentiable ℝ H)
    (hpq : p < q)
    (hH'_le : ∀ z ∈ Set.Icc p q, deriv H z ≤ M) :
    H q - H p ≤ M * (q - p) := by
  have hcont : ContinuousOn H (Set.Icc p q) := hH1.continuous.continuousOn
  have hfd : ∀ z ∈ Set.Ioo p q, HasDerivAt H (deriv H z) z :=
    fun z _ => hH1.differentiableAt.hasDerivAt
  have h_mvt : ∃ (z : ℝ), z ∈ Set.Ioo p q ∧ deriv H z = (H q - H p) / (q - p) :=
    exists_hasDerivAt_eq_slope (f := H) (f' := deriv H) hpq hcont hfd
  rcases h_mvt with ⟨z, hz_in, hderiv_eq⟩
  have hz_in' : z ∈ Set.Icc p q := ⟨by linarith [hz_in.1], by linarith [hz_in.2]⟩
  have hH'z : deriv H z ≤ M := hH'_le z hz_in'
  have h_pos : 0 < q - p := by linarith
  have h_eq : H q - H p = deriv H z * (q - p) := by
    rw [hderiv_eq] <;> field_simp [h_pos.ne'] <;> ring
  have h_ineq : deriv H z * (q - p) ≤ M * (q - p) :=
    mul_le_mul_of_nonneg_right hH'z (by linarith)
  linarith [h_eq, h_ineq]

/-- Zero crossing to the left of [a,b]: if H'(x0)=0, x0 < a, H'' ≥ c on [x0,b],
|H''| ≤ D on [x0,a], and |H| ≤ M on [a,b], then:
  (1) H'(a) ≥ c*(a-x0)
  (2) c*(a-x0)*(b-a) + c/2*(b-a)^2 ≤ 2*M
  (3) |H(x0)| ≤ M + D*(a-x0)^2/2 -/
lemma zero_crossing_left {H : ℝ → ℝ} {x0 a b c M D : ℝ}
    (hH1 : Differentiable ℝ H)
    (hH2 : Differentiable ℝ (deriv H))
    (hx0_lt_a : x0 < a)
    (hab : a ≤ b)
    (hderiv0 : deriv H x0 = 0)
    (hH''_ge : ∀ z ∈ Set.Icc x0 b, c ≤ deriv (deriv H) z)
    (hH''_le : ∀ z ∈ Set.Icc x0 a, deriv (deriv H) z ≤ D)
    (h_bound : ∀ z ∈ Set.Icc a b, |H z| ≤ M)
    (hc_pos : 0 < c)
    (hD_nonneg : 0 ≤ D)
    (_hM_nonneg : 0 ≤ M) :
    deriv H a ≥ c * (a - x0) ∧
    c * (a - x0) * (b - a) + c / 2 * (b - a)^2 ≤ 2 * M ∧
    |H x0| ≤ M + D * (a - x0)^2 / 2 := by
  have hxa : x0 ≤ a := by linarith
  have h_x0_in_a : x0 ∈ Set.Icc x0 a := ⟨by linarith, by linarith⟩
  have h_a_in_a : a ∈ Set.Icc x0 a := ⟨by linarith, by linarith⟩
  have ha_in_ab : a ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  have hb_in_ab : b ∈ Set.Icc a b := ⟨by linarith, by linarith⟩

  -- Restrict H''_ge to [x0, a]
  have hH''_ge_a : ∀ z ∈ Set.Icc x0 a, c ≤ deriv (deriv H) z :=
    fun z hz => hH''_ge z ⟨by linarith [hz.1], by linarith [hz.2]⟩

  -- (1) H'(a) ≥ c*(a-x0)
  have h1 : deriv H a ≥ c * (a - x0) := by
    have h_inc : deriv H a - deriv H x0 ≥ c * (a - x0) :=
      deriv_increase_lower_bound hH2 hx0_lt_a hH''_ge_a
    rw [hderiv0] at h_inc
    linarith

  -- (2) variation bound
  have hH''_ge_ab : ∀ z ∈ Set.Icc a b, c ≤ deriv (deriv H) z :=
    fun z hz => hH''_ge z ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have h2 : H b - H a ≥ deriv H a * (b - a) + c / 2 * (b - a)^2 :=
    variation_lower_bound hH1 hH2 hab ha_in_ab hb_in_ab hH''_ge_ab
  have h3 : H b - H a ≤ 2 * M := by
    have h4 : |H a| ≤ M := h_bound a ha_in_ab
    have h5 : |H b| ≤ M := h_bound b hb_in_ab
    linarith [abs_le.mp h4, abs_le.mp h5]
  have h6 : c * (a - x0) * (b - a) + c / 2 * (b - a)^2 ≤ 2 * M := by
    calc
      c * (a - x0) * (b - a) + c / 2 * (b - a)^2
        ≤ deriv H a * (b - a) + c / 2 * (b - a)^2 := by gcongr <;> linarith
      _ ≤ H b - H a := h2
      _ ≤ 2 * M := h3

  -- (3) |H(x0)| ≤ M + D*(a-x0)^2/2
  -- Upper bound on H(x0): H(x0) ≤ H(a) ≤ M (from convexity H'' ≥ c > 0)
  have h_taylor_lower : H a ≥ H x0 + deriv H x0 * (a - x0) + c / 2 * (a - x0)^2 :=
    taylor_quadratic_lower_bound hH1 hH2 hxa h_x0_in_a h_a_in_a hH''_ge_a
  rw [hderiv0] at h_taylor_lower
  have hHx0_upper : H x0 ≤ M := by
    have h7 : H a ≥ H x0 + c / 2 * (a - x0)^2 := by linarith
    have h8 : 0 ≤ c / 2 * (a - x0)^2 := by positivity
    have h9 : H x0 ≤ H a := by linarith
    have h9 : H a ≤ M := (abs_le.mp (h_bound a ha_in_ab)).2
    linarith

  -- Lower bound on H(x0): H(x0) ≥ H(a) - D/2*(a-x0)^2
  -- Use K(z) := D/2*z^2 - H(z), K'' = D - H'' ≥ 0 on [x0,a]
  let K : ℝ → ℝ := fun z => D / 2 * z^2 - H z
  have hK_diff1 : Differentiable ℝ K := by
    have h_pow : Differentiable ℝ (fun z : ℝ => z^2) := by
      have h : Differentiable ℝ (fun z : ℝ => z * z) := differentiable_id.mul differentiable_id
      have h_eq : (fun z : ℝ => z * z) = (fun z : ℝ => z^2) := by funext z; simp [pow_two]
      rw [h_eq] at h; exact h
    exact (h_pow.const_mul (D / 2)).sub hH1
  have hK_deriv : ∀ z, deriv K z = D * z - deriv H z := by
    intro z
    have hd : HasDerivAt K (D * z - deriv H z) z := by
      have h1 : HasDerivAt H (deriv H z) z := hH1.differentiableAt.hasDerivAt
      have h2 : HasDerivAt (fun z : ℝ => D / 2 * z^2) (D * z) z := by
        have h_id : HasDerivAt (fun z : ℝ => z) 1 z := hasDerivAt_id' z
        have h3 : HasDerivAt (fun z : ℝ => z^2) (2 * z) z := by
          have h_mul : HasDerivAt (fun z : ℝ => z * z) (1 * z + z * 1) z := h_id.mul h_id
          have h_eq1 : (fun z : ℝ => z^2) = (fun z : ℝ => z * z) := by funext t; simp [pow_two]
          have h_deriv : 1 * z + z * 1 = 2 * z := by ring
          rw [h_eq1]; rw [h_deriv] at h_mul; exact h_mul
        have h4 : HasDerivAt (fun z : ℝ => D / 2 * z^2) (D / 2 * (2 * z)) z := h3.const_mul (D / 2)
        have h5 : D / 2 * (2 * z) = D * z := by ring
        rw [h5] at h4; exact h4
      exact h2.sub h1
    exact hd.deriv
  have hK_diff2 : Differentiable ℝ (deriv K) := by
    have h_eq : deriv K = fun z : ℝ => D * z - deriv H z := by funext z; exact hK_deriv z
    rw [h_eq]
    exact (differentiable_id.const_mul D).sub hH2
  have hK''_nonneg : ∀ z ∈ Set.Icc x0 a, 0 ≤ deriv (deriv K) z := by
    intro z hz
    have h2 : deriv (deriv K) z = D - deriv (deriv H) z := by
      have h_eq1 : deriv K = fun s : ℝ => D * s - deriv H s := by funext s; exact hK_deriv s
      have hd1 : HasDerivAt (deriv H) (deriv (deriv H) z) z := hH2.differentiableAt.hasDerivAt
      have hd2 : HasDerivAt (fun s : ℝ => D * s) D z := by simpa using (hasDerivAt_id' z).const_mul D
      have hd3 : HasDerivAt (fun s : ℝ => D * s - deriv H s) (D - deriv (deriv H) z) z := hd2.sub hd1
      have h4 : deriv (fun s : ℝ => D * s - deriv H s) z = D - deriv (deriv H) z := hd3.deriv
      rw [h_eq1]
      exact h4
    rw [h2]
    have h4 : deriv (deriv H) z ≤ D := hH''_le z hz
    linarith
  have h_taylor_K := taylor_quadratic_lower_bound hK_diff1 hK_diff2 hxa h_x0_in_a h_a_in_a hK''_nonneg
  have hK_x0 : K x0 = D / 2 * x0^2 - H x0 := by simp [K] <;> ring
  have hK_a : K a = D / 2 * a^2 - H a := by simp [K] <;> ring
  have hderiv_K_x0 : deriv K x0 = D * x0 - deriv H x0 := hK_deriv x0
  rw [hK_a, hK_x0, hderiv_K_x0] at h_taylor_K
  rw [hderiv0] at h_taylor_K
  have hHx0_lower : H x0 ≥ H a - D * (a - x0)^2 / 2 := by linarith
  have hHa_lower : H a ≥ -M := (abs_le.mp (h_bound a ha_in_ab)).1
  have hHx0_lower2 : H x0 ≥ -M - D * (a - x0)^2 / 2 := by linarith
  have hHx0_upper2 : H x0 ≤ M + D * (a - x0)^2 / 2 := by
    have h9 : H x0 ≤ M := hHx0_upper
    have h10 : 0 ≤ D * (a - x0)^2 / 2 := by positivity
    linarith
  set B : ℝ := M + D * (a - x0)^2 / 2 with hB_def
  have h_lower : -B ≤ H x0 := by
    dsimp only [B]
    linarith
  have h_upper : H x0 ≤ B := hHx0_upper2
  have h_abs : |H x0| ≤ B := abs_le.mpr ⟨h_lower, h_upper⟩
  exact ⟨h1, ⟨h6, h_abs⟩⟩

/-- Lower bound on H'(a) from geometric constraint:
H'(a) ≥ d/(192K²) when a - a_J ≥ 1/(96K), H'' ≥ d/(2K), and H'(a_J) > 0. -/
lemma geometric_H'a_lower {H : ℝ → ℝ} {K d a_J b_J a : ℝ}
    (hH2 : Differentiable ℝ (deriv H))
    (hK_pos : 0 < K)
    (hd_pos : 0 < d)
    (haJ_le_a : a_J ≤ a)
    (hb_le_bJ : a ≤ b_J)
    (h_geometric_low : a - a_J ≥ 1 / (96 * K))
    (hH'_pos_aJ : 0 < deriv H a_J)
    (hH''_ge : ∀ x ∈ Set.Icc a_J b_J, d / (2 * K) ≤ deriv (deriv H) x) :
    deriv H a ≥ d / (192 * K^2) := by
  have h_aj_lt_a : a_J < a := by
    have h : 0 < a - a_J := by
      have h2 : 0 < 1 / (96 * K) := by positivity
      linarith
    linarith
  have hsub : Set.Icc a_J a ⊆ Set.Icc a_J b_J := by
    intro z hz; exact ⟨by linarith [hz.1], by linarith [hz.2, hb_le_bJ]⟩
  have hH''_restrict : ∀ z ∈ Set.Icc a_J a, d / (2 * K) ≤ deriv (deriv H) z :=
    fun z hz => hH''_ge z (hsub hz)
  have h_inc : deriv H a - deriv H a_J ≥ (d / (2 * K)) * (a - a_J) :=
    deriv_increase_lower_bound hH2 h_aj_lt_a hH''_restrict
  calc
    deriv H a = deriv H a_J + (deriv H a - deriv H a_J) := by ring
    _ ≥ deriv H a_J + (d / (2 * K)) * (a - a_J) := by linarith
    _ ≥ (d / (2 * K)) * (a - a_J) := by linarith [hH'_pos_aJ]
    _ ≥ (d / (2 * K)) * (1 / (96 * K)) := by gcongr
    _ = d / (192 * K^2) := by field_simp [hK_pos.ne'] <;> ring

/-- Upper bound on H'(a) from variation:
H'(a) ≤ 20δ/L - dL/(4K). -/
lemma variation_H'a_upper {H : ℝ → ℝ} {K d delta L a b : ℝ}
    (hH1 : Differentiable ℝ H)
    (hH2 : Differentiable ℝ (deriv H))
    (hK_pos : 0 < K)
    (hd_pos : 0 < d)
    (hδ_pos : 0 < delta)
    (hL_pos : 0 < L)
    (hab : a ≤ b)
    (hba : b - a = L)
    (hH''_ge : ∀ x ∈ Set.Icc a b, d / (2 * K) ≤ deriv (deriv H) x)
    (hHa_bound : |H a| ≤ 10 * delta)
    (hHb_bound : |H b| ≤ 10 * delta) :
    deriv H a ≤ 20 * delta / L - d * L / (4 * K) := by
  have ha_in : a ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  have hb_in : b ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  have h_var : H b - H a ≥ deriv H a * (b - a) + (d / (2 * K)) / 2 * (b - a)^2 :=
    variation_lower_bound hH1 hH2 hab ha_in hb_in hH''_ge
  have h_var2 : H b - H a ≥ deriv H a * L + d * L^2 / (4 * K) := by
    have h9 : (b - a) = L := hba
    rw [h9] at h_var
    have h10 : (d / (2 * K)) / 2 * L^2 = d * L^2 / (4 * K) := by ring
    rw [h10] at h_var
    exact h_var
  have h3 : H b - H a ≤ 20 * delta := by
    linarith [abs_le.mp hHa_bound, abs_le.mp hHb_bound]
  have h4 : deriv H a * L + d * L^2 / (4 * K) ≤ 20 * delta := by linarith
  have h5 : deriv H a * L ≤ 20 * delta - d * L^2 / (4 * K) := by linarith
  have h6 : deriv H a ≤ (20 * delta - d * L^2 / (4 * K)) / L := by
    have h7 : deriv H a = (deriv H a * L) / L := by field_simp [hL_pos.ne'] <;> ring
    rw [h7]
    gcongr
  have h8 : (20 * delta - d * L^2 / (4 * K)) / L = 20 * delta / L - d * L / (4 * K) := by
    field_simp [hL_pos.ne'] <;> ring
  rw [h8] at h6
  exact h6

/-- Bound on Δ at a_J: Δ ≤ 10δ + (25/24)*H'(a). -/
lemma Delta_bound {H : ℝ → ℝ} {K delta a_J b_J a Δ : ℝ}
    (hH1 : Differentiable ℝ H)
    (hH2 : Differentiable ℝ (deriv H))
    (hK : 1 ≤ K)
    (haJ_le_a : a_J ≤ a)
    (hb_le_bJ : a ≤ b_J)
    (h_geometric_high : a - a_J ≤ 1)
    (hH'_pos : ∀ x ∈ Set.Icc a_J b_J, 0 < deriv H x)
    (hH''_nonneg : ∀ x ∈ Set.Icc a_J b_J, 0 ≤ deriv (deriv H) x)
    (hHa_bound : |H a| ≤ 10 * delta)
    (hΔ : Δ ≤ |H a_J| + deriv H a_J) :
    Δ ≤ 10 * delta + (2 : ℝ) * deriv H a := by
  have hK_pos : 0 < K := by linarith
  set c_geo : ℝ := 2 with hc_geo_def
  have h_a_in_J : a ∈ Set.Icc a_J b_J := ⟨by linarith, by linarith⟩
  have h_aJ_in_J : a_J ∈ Set.Icc a_J b_J := ⟨by linarith, by linarith⟩
  have h_H'_mono : ∀ (x y : ℝ), x ∈ Set.Icc a_J b_J → y ∈ Set.Icc a_J b_J → x ≤ y → deriv H x ≤ deriv H y :=
    fun x y hx hy hxy => deriv_monotone_of_deriv2_nonneg hH1 hH2 hH''_nonneg hx hy hxy

  -- H(a_J) ≤ 10δ
  have h4a : H a_J ≤ 10 * delta := by
    by_cases h : a_J = a
    · rw [h]
      exact (abs_le.mp hHa_bound).2
    · have h_aj_lt_a : a_J < a := lt_of_le_of_ne haJ_le_a h
      have hsub : Set.Icc a_J a ⊆ Set.Icc a_J b_J := by
        intro z hz; exact ⟨by linarith [hz.1], by linarith [hz.2, hb_le_bJ]⟩
      have hcont_H : ContinuousOn H (Set.Icc a_J a) := hH1.continuous.continuousOn.mono hsub
      have hfd_H : ∀ z ∈ Set.Ioo a_J a, HasDerivAt H (deriv H z) z :=
        fun z _ => hH1.differentiableAt.hasDerivAt
      have h_mvt : ∃ (z : ℝ), z ∈ Set.Ioo a_J a ∧ deriv H z = (H a - H a_J) / (a - a_J) :=
        exists_hasDerivAt_eq_slope (f := H) (f' := deriv H) h_aj_lt_a hcont_H hfd_H
      rcases h_mvt with ⟨z, hz_in, hderiv⟩
      have hz_in_J : z ∈ Set.Icc a_J b_J := hsub ⟨by linarith [hz_in.1], by linarith [hz_in.2]⟩
      have h_pos : 0 < deriv H z := hH'_pos z hz_in_J
      have h_pos2 : 0 < a - a_J := by linarith
      have h_eq : H a - H a_J = deriv H z * (a - a_J) := by
        rw [hderiv] <;> field_simp [h_pos2.ne'] <;> ring
      have h9 : H a_J ≤ H a := by
        have h10 : 0 ≤ deriv H z * (a - a_J) := by positivity
        linarith [h_eq]
      have h11 : H a ≤ 10 * delta := (abs_le.mp hHa_bound).2
      linarith

  -- H(a_J) ≥ -10δ - H'(a)*(a-a_J)
  have h4b : H a_J ≥ -(10 * delta) - deriv H a * (a - a_J) := by
    by_cases h : a_J = a
    · subst h
      simpa using (abs_le.mp hHa_bound).1
    · have h_aj_lt_a : a_J < a := lt_of_le_of_ne haJ_le_a h
      have hsub : Set.Icc a_J a ⊆ Set.Icc a_J b_J := by
        intro z hz; exact ⟨by linarith [hz.1], by linarith [hz.2, hb_le_bJ]⟩
      have hcont_H : ContinuousOn H (Set.Icc a_J a) := hH1.continuous.continuousOn.mono hsub
      have hfd_H : ∀ z ∈ Set.Ioo a_J a, HasDerivAt H (deriv H z) z :=
        fun z _ => hH1.differentiableAt.hasDerivAt
      have h_mvt : ∃ (z : ℝ), z ∈ Set.Ioo a_J a ∧ deriv H z = (H a - H a_J) / (a - a_J) :=
        exists_hasDerivAt_eq_slope (f := H) (f' := deriv H) h_aj_lt_a hcont_H hfd_H
      rcases h_mvt with ⟨z, hz_in, hderiv⟩
      have hz_in_J : z ∈ Set.Icc a_J b_J := hsub ⟨by linarith [hz_in.1], by linarith [hz_in.2]⟩
      have hz_le_a : z ≤ a := hz_in.2.le
      have h_deriv_le : deriv H z ≤ deriv H a := h_H'_mono z a hz_in_J h_a_in_J hz_le_a
      have h_pos2 : 0 < a - a_J := by linarith
      have h_eq : H a - H a_J = deriv H z * (a - a_J) := by
        rw [hderiv] <;> field_simp [h_pos2.ne'] <;> ring
      have h13 : H a - H a_J ≤ deriv H a * (a - a_J) := by
        rw [h_eq] <;> gcongr
      have h14 : H a ≥ -(10 * delta) := (abs_le.mp hHa_bound).1
      linarith

  have h4c : |H a_J| ≤ 10 * delta + deriv H a * (a - a_J) := by
    have h_pos : 0 ≤ deriv H a * (a - a_J) := by
      have h1 : 0 < deriv H a := hH'_pos a h_a_in_J
      have h2 : 0 ≤ a - a_J := by linarith
      positivity
    have h_up : H a_J ≤ 10 * delta + deriv H a * (a - a_J) := by linarith [h4a]
    have h_low : -(10 * delta + deriv H a * (a - a_J)) ≤ H a_J := by linarith [h4b]
    exact abs_le.mpr ⟨h_low, h_up⟩

  have h4d : deriv H a_J ≤ deriv H a := h_H'_mono a_J a h_aJ_in_J h_a_in_J (by linarith)

  have h3 : a - a_J + 1 ≤ c_geo := by
    have h4 : a - a_J ≤ 1 := h_geometric_high
    have h5 : a - a_J + 1 ≤ 2 := by linarith
    simpa [hc_geo_def] using h5

  have hHa_pos : 0 ≤ deriv H a := by
    have h : 0 < deriv H a := hH'_pos a h_a_in_J
    linarith
  calc
    Δ ≤ |H a_J| + deriv H a_J := hΔ
    _ ≤ 10 * delta + deriv H a * (a - a_J) + deriv H a := by linarith [h4c, h4d]
    _ = 10 * delta + deriv H a * (a - a_J + 1) := by ring
    _ ≤ 10 * delta + deriv H a * c_geo := by
      have h : deriv H a * (a - a_J + 1) ≤ deriv H a * c_geo := mul_le_mul_of_nonneg_left h3 hHa_pos
      linarith
    _ = 10 * delta + (2 : ℝ) * deriv H a := by simp [hc_geo_def] <;> ring

/-- Geometric bound for Case 2b(ii): H' has constant positive sign on J.
Given the geometric constraint a - a_J ≥ 1/(96K), proves
(Δ + δ) * d ≤ 270000 * K^2 * δ * t.

Simpler proof: from H'(a) ≥ d/(192K²) and H'(a) ≤ 20δ/L, we get
d ≤ 3840K²δ/L. Then y*d ≤ (20δ/L)*(3840K²δ/L) = 76800K²δt. -/
lemma constant_sign_geometric_bound
    {H : ℝ → ℝ} {K d delta t L a_J b_J a b Δ : ℝ}
    (hH1 : Differentiable ℝ H)
    (hH2 : Differentiable ℝ (deriv H))
    (hK : 1 ≤ K)
    (hd_pos : 0 < d)
    (hδ_pos : 0 < delta)
    (ht_pos : 0 < t)
    (hδt : delta ≤ t)
    (ht1 : t ≤ 1)
    (hL_eq : L = Real.sqrt (delta / t))
    (hL_le : L ≤ 1 / (24 * K))
    (hL_pos : 0 < L)
    (haJ_le_a : a_J ≤ a)
    (hb_le_bJ : b ≤ b_J)
    (hba : b - a = L)
    (h_geometric_low : a - a_J ≥ 1 / (96 * K))
    (h_geometric_high : a - a_J ≤ 1)
    (hH'_pos : ∀ x ∈ Set.Icc a_J b_J, 0 < deriv H x)
    (hH''_ge : ∀ x ∈ Set.Icc a_J b_J, d / (2 * K) ≤ deriv (deriv H) x)
    (hHa_bound : |H a| ≤ 10 * delta)
    (hHb_bound : |H b| ≤ 10 * delta)
    (hΔ : Δ ≤ |H a_J| + deriv H a_J) :
    (Δ + delta) * d ≤ 270000 * K^2 * delta * t := by
  have hK_pos : 0 < K := by linarith
  set c_geo : ℝ := 2 with hc_geo_def
  have h_a_in_J : a ∈ Set.Icc a_J b_J := ⟨by linarith, by linarith⟩
  have h_aJ_in_J : a_J ∈ Set.Icc a_J b_J := ⟨by linarith, by linarith⟩

  have hH''_nonneg : ∀ x ∈ Set.Icc a_J b_J, 0 ≤ deriv (deriv H) x := by
    intro x hx
    have h : d / (2 * K) ≤ deriv (deriv H) x := hH''_ge x hx
    have h' : 0 ≤ d / (2 * K) := by positivity
    linarith

  have hH''_ge_ab : ∀ x ∈ Set.Icc a b, d / (2 * K) ≤ deriv (deriv H) x :=
    fun x hx => hH''_ge x ⟨by linarith [hx.1], by linarith [hx.2]⟩

  -- Bounds on H'(a)
  have h1_lower : deriv H a ≥ d / (192 * K^2) :=
    geometric_H'a_lower hH2 hK_pos hd_pos haJ_le_a (by linarith) h_geometric_low
      (hH'_pos a_J h_aJ_in_J) hH''_ge

  have h2_upper : deriv H a ≤ 20 * delta / L - d * L / (4 * K) :=
    variation_H'a_upper hH1 hH2 hK_pos hd_pos hδ_pos hL_pos (by linarith) hba
      hH''_ge_ab hHa_bound hHb_bound

  set y : ℝ := 20 * delta / L - d * L / (4 * K) with hy_def
  have hy_pos : 0 < y := by
    have h : 0 < deriv H a := hH'_pos a h_a_in_J
    linarith [h2_upper]

  have h3_geo : d / (192 * K^2) ≤ y := by linarith [h1_lower, h2_upper]

  -- Bound Δ
  have h4Δ : Δ ≤ 10 * delta + c_geo * deriv H a :=
    Delta_bound hH1 hH2 hK haJ_le_a (by linarith) h_geometric_high hH'_pos hH''_nonneg hHa_bound hΔ

  have h5Δ : Δ ≤ 10 * delta + c_geo * y := by
    have h6 : deriv H a ≤ y := by linarith [h2_upper]
    have h7 : 0 ≤ c_geo := by norm_num [hc_geo_def]
    have h8 : c_geo * deriv H a ≤ c_geo * y := mul_le_mul_of_nonneg_left h6 h7
    linarith [h4Δ, h8]

  -- Key bound: d ≤ 3840 * K² * δ / L
  have h_d_bound1 : d ≤ 3840 * K^2 * delta / L := by
    have h_pos_dL : 0 < d * L / (4 * K) := by positivity
    have h_y_le : y ≤ 20 * delta / L := by
      simp only [hy_def]
      linarith
    have h2 : d / (192 * K^2) ≤ 20 * delta / L := by
      calc
        d / (192 * K^2) ≤ y := h3_geo
        _ ≤ 20 * delta / L := h_y_le
    have h5 : 0 < 192 * K^2 := by positivity
    have h4 : d ≤ (20 * delta / L) * (192 * K^2) := by
      calc
        d = (d / (192 * K^2)) * (192 * K^2) := by field_simp [h5.ne'] <;> ring
        _ ≤ (20 * delta / L) * (192 * K^2) := by gcongr
    have h6 : (20 * delta / L) * (192 * K^2) = 3840 * K^2 * delta / L := by ring
    linarith

  -- Also d ≤ 80 * K * t (from y > 0)
  have h_d_bound2 : d ≤ 80 * K * t := by
    have h : d * L / (4 * K) < 20 * delta / L := by
      simpa [hy_def] using hy_pos
    have h2 : d * L^2 < 80 * K * delta := by
      have h3 : 0 < 4 * K * L := by positivity
      have h4 : d * L / (4 * K) < 20 * delta / L := h
      have h5 : 4 * K * L * (d * L / (4 * K)) < 4 * K * L * (20 * delta / L) :=
        mul_lt_mul_of_pos_left h4 h3
      have h6 : 4 * K * L * (20 * delta / L) = 80 * K * delta := by
        field_simp [hL_pos.ne'] <;> ring
      have h7 : d * L^2 = 4 * K * L * (d * L / (4 * K)) := by
        field_simp [hK_pos.ne', hL_pos.ne'] <;> ring
      calc
        d * L^2 = 4 * K * L * (d * L / (4 * K)) := h7
        _ < 4 * K * L * (20 * delta / L) := h5
        _ = 80 * K * delta := h6
    have hL2 : L^2 = delta / t := by
      rw [hL_eq] <;> rw [Real.sq_sqrt (by positivity)]
    rw [hL2] at h2
    have h4 : d * (delta / t) < 80 * K * delta := h2
    have h5 : d < 80 * K * t := by
      have h6 : 0 < delta / t := by positivity
      calc
        d = d * (delta / t) / (delta / t) := by field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
        _ < (80 * K * delta) / (delta / t) := by gcongr
        _ = 80 * K * t := by field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
    linarith

  have hL2 : L^2 = delta / t := by
    rw [hL_eq] <;> rw [Real.sq_sqrt (by positivity)]

  -- y * d ≤ 76800 * K² * δ * t
  have h_yd_bound : y * d ≤ 76800 * K^2 * delta * t := by
    have h_pos_dL : 0 < d * L / (4 * K) := by positivity
    have h_y_le : y ≤ 20 * delta / L := by
      simp only [hy_def]
      linarith
    have h1 : y * d ≤ (20 * delta / L) * d := by
      exact mul_le_mul_of_nonneg_right h_y_le (by linarith)
    have h2 : (20 * delta / L) * d ≤ (20 * delta / L) * (3840 * K^2 * delta / L) := by
      gcongr <;> linarith
    have h3 : (20 * delta / L) * (3840 * K^2 * delta / L) = 76800 * K^2 * (delta^2 / L^2) := by ring
    have h4 : delta^2 / L^2 = delta * t := by
      rw [hL2]
      field_simp [hδ_pos.ne', ht_pos.ne'] <;> ring
    have h5 : (20 * delta / L) * (3840 * K^2 * delta / L) = 76800 * K^2 * delta * t := by
      rw [h3, h4] <;> ring
    have h6 : y * d ≤ 76800 * K^2 * delta * t := by
      calc
        y * d ≤ (20 * delta / L) * d := h1
        _ ≤ (20 * delta / L) * (3840 * K^2 * delta / L) := h2
        _ = 76800 * K^2 * delta * t := h5
    exact h6

  -- 11 * δ * d ≤ 880 * K² * δ * t
  have h_11δd_bound : 11 * delta * d ≤ 880 * K^2 * delta * t := by
    have h1 : 11 * delta * d ≤ 11 * delta * (80 * K * t) := by gcongr
    have h2 : 11 * delta * (80 * K * t) = 880 * K * delta * t := by ring
    rw [h2] at h1
    have h3 : 880 * K * delta * t ≤ 880 * K^2 * delta * t := by
      have h4 : 1 ≤ K^2 := by nlinarith
      have h5 : 0 ≤ 880 * delta * t := by positivity
      have h6 : K ≤ K^2 := by nlinarith
      nlinarith
    linarith

  -- Final: (Δ + δ) * d ≤ 11δd + c_geo * y * d ≤ 880 + 80000 = 80880 ≤ 270000
  have h_final : (Δ + delta) * d ≤ 11 * delta * d + c_geo * y * d := by
    have h1 : (Δ + delta) * d ≤ (10 * delta + c_geo * y + delta) * d := by
      gcongr <;> linarith [h5Δ]
    have h2 : (10 * delta + c_geo * y + delta) * d = 11 * delta * d + c_geo * y * d := by ring
    rw [h2] at h1
    exact h1
  have h_cgeo_yd : c_geo * y * d ≤ 153600 * K^2 * delta * t := by
    have h1 : c_geo * (y * d) ≤ c_geo * (76800 * K^2 * delta * t) := by
      have h2 : 0 ≤ c_geo := by norm_num [hc_geo_def]
      exact mul_le_mul_of_nonneg_left h_yd_bound h2
    have h1' : c_geo * y * d ≤ c_geo * (76800 * K^2 * delta * t) := by
      have h_assoc : c_geo * y * d = c_geo * (y * d) := by ring
      rw [h_assoc]
      exact h1
    have h2 : c_geo * (76800 * K^2 * delta * t) = 153600 * K^2 * delta * t := by
      simp [hc_geo_def] <;> ring
    rw [h2] at h1'
    exact h1'
  calc
    (Δ + delta) * d ≤ 11 * delta * d + c_geo * y * d := h_final
    _ ≤ 880 * K^2 * delta * t + 153600 * K^2 * delta * t := by
      exact add_le_add h_11δd_bound h_cgeo_yd
    _ = 154480 * K^2 * delta * t := by ring
    _ ≤ 270000 * K^2 * delta * t := by
      have h : 0 ≤ K^2 * delta * t := by positivity
      nlinarith

end Kakeya.Cinematic
