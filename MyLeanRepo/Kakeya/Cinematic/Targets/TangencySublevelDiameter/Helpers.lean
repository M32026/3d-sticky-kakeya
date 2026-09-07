import MyLeanRepo.Kakeya.Cinematic.Geometry
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Real.Sqrt

/-!
# Helper lemmas for tangency_sublevel_diameter (PYZ Lemma 16(2a))

1. `quadratic_inequality_bound`
2. `real_lipschitz_of_deriv_bound`
3. `lipschitz_value`, `lipschitz_deriv`
4. `tangency_parameter_attained`
5. `taylor_quadratic_lower_bound`
6. `constant_sign_of_never_zero`
-/

namespace Kakeya.Cinematic

/--
If `a > 0`, `b, c ≥ 0`, `b² ≤ a*c/2`, and `a*u² - b*u - c ≤ 0`,
then `u ≤ √2 * √(c/a)`.
-/
lemma quadratic_inequality_bound {a b c u : ℝ}
    (ha : 0 < a) (_hb : 0 ≤ b) (hc : 0 ≤ c)
    (h_b2 : b^2 ≤ a * c / 2)
    (h : a * u^2 - b * u - c ≤ 0) :
    u ≤ Real.sqrt 2 * Real.sqrt (c / a) := by
  by_cases hu : u ≤ 0
  · have h_rhs : 0 ≤ Real.sqrt 2 * Real.sqrt (c / a) := by positivity
    linarith
  · have hu' : 0 < u := by linarith
    set D : ℝ := b^2 + 4 * a * c with hD_def
    have hD_nonneg : 0 ≤ D := by positivity
    have hD_div : D / (4 * a) = b^2 / (4 * a) + c := by
      rw [hD_def]
      field_simp [ha.ne'] <;> ring
    have h_square : a * (u - b / (2 * a)) ^ 2 ≤ D / (4 * a) := by
      have h_expand : a * (u - b / (2 * a)) ^ 2 = a * u^2 - b * u + b^2 / (4 * a) := by
        field_simp [ha.ne'] <;> ring
      rw [h_expand, hD_div]
      linarith
    have h1 : (u - b / (2 * a)) ^ 2 ≤ D / (4 * a^2) := by
      calc (u - b / (2 * a)) ^ 2
        = (a * (u - b / (2 * a)) ^ 2) / a := by field_simp [ha.ne'] <;> ring
      _ ≤ (D / (4 * a)) / a := by gcongr
      _ = D / (4 * a^2) := by field_simp [ha.ne'] <;> ring
    have h_sqrt_nonneg : 0 ≤ D / (4 * a^2) := by positivity
    have h2 : u - b / (2 * a) ≤ Real.sqrt (D / (4 * a^2)) := by
      have h3 : (u - b / (2 * a)) ^ 2 ≤ (Real.sqrt (D / (4 * a^2))) ^ 2 := by
        rw [Real.sq_sqrt h_sqrt_nonneg] <;> exact h1
      have h4 : 0 ≤ Real.sqrt (D / (4 * a^2)) := by positivity
      nlinarith
    have h5 : Real.sqrt (D / (4 * a^2)) = Real.sqrt D / (2 * a) := by
      rw [Real.sqrt_div (by positivity)]
      have h7 : Real.sqrt (4 * a^2) = 2 * a := by
        have h8 : 0 ≤ 2 * a := by positivity
        calc
          Real.sqrt (4 * a^2) = Real.sqrt ((2 * a)^2) := by
            congr 1
            ring
          _ = 2 * a := Real.sqrt_sq h8
      rw [h7]
    rw [h5] at h2
    have h_upper : u ≤ (b + Real.sqrt D) / (2 * a) := by
      have h9 : u ≤ b / (2 * a) + Real.sqrt D / (2 * a) := by linarith
      have h10 : b / (2 * a) + Real.sqrt D / (2 * a) = (b + Real.sqrt D) / (2 * a) := by
        field_simp [ha.ne'] <;> ring
      rw [h10] at h9
      exact h9
    have h_ac2_nonneg : 0 ≤ a * c / 2 := by positivity
    have hb' : b ≤ Real.sqrt (a * c / 2) := by
      have h7 : b^2 ≤ (Real.sqrt (a * c / 2))^2 := by
        rw [Real.sq_sqrt h_ac2_nonneg] <;> exact h_b2
      have h9 : 0 ≤ Real.sqrt (a * c / 2) := by positivity
      nlinarith
    have hsqrt : Real.sqrt D ≤ 3 * Real.sqrt (a * c / 2) := by
      have h10 : D ≤ 9 * (a * c / 2) := by
        simp only [hD_def] <;> nlinarith
      have h12 : Real.sqrt D ≤ Real.sqrt (9 * (a * c / 2)) := Real.sqrt_le_sqrt h10
      have h13 : Real.sqrt (9 * (a * c / 2)) = 3 * Real.sqrt (a * c / 2) := by
        rw [Real.sqrt_mul (by positivity)]
        have h15 : Real.sqrt 9 = 3 := by
          rw [Real.sqrt_eq_cases] <;> norm_num
        rw [h15] <;> ring
      rw [h13] at h12
      exact h12
    have h_final_algebra : 2 * Real.sqrt (a * c / 2) / a = Real.sqrt 2 * Real.sqrt (c / a) := by
      have h6 : 0 ≤ 2 * Real.sqrt (a * c / 2) / a := by positivity
      have h7 : 0 ≤ Real.sqrt 2 * Real.sqrt (c / a) := by positivity
      have h8 : (2 * Real.sqrt (a * c / 2) / a) ^ 2 = (Real.sqrt 2 * Real.sqrt (c / a)) ^ 2 := by
        have h9 : (2 * Real.sqrt (a * c / 2) / a) ^ 2 = 4 * (a * c / 2) / a^2 := by
          calc
            (2 * Real.sqrt (a * c / 2) / a) ^ 2
              = 4 * (Real.sqrt (a * c / 2)) ^ 2 / a^2 := by ring
            _ = 4 * (a * c / 2) / a^2 := by
              rw [Real.sq_sqrt (by positivity)]
        have h10 : (Real.sqrt 2 * Real.sqrt (c / a)) ^ 2 = 2 * (c / a) := by
          calc
            (Real.sqrt 2 * Real.sqrt (c / a)) ^ 2
              = (Real.sqrt 2)^2 * (Real.sqrt (c / a))^2 := by ring
            _ = 2 * (c / a) := by
              rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
        rw [h9, h10]
        field_simp [ha.ne'] <;> ring
      nlinarith
    calc
      u ≤ (b + Real.sqrt D) / (2 * a) := h_upper
      _ ≤ (Real.sqrt (a * c / 2) + 3 * Real.sqrt (a * c / 2)) / (2 * a) := by
          gcongr <;> linarith
      _ = 2 * Real.sqrt (a * c / 2) / a := by ring
      _ = Real.sqrt 2 * Real.sqrt (c / a) := h_final_algebra

/-- General Lipschitz bound from a uniform derivative bound via MVT. -/
lemma real_lipschitz_of_deriv_bound {h : ℝ → ℝ} {x y B : ℝ}
    (h_diff : Differentiable ℝ h)
    (h_bound : ∀ z : ℝ, z ∈ Set.Icc (min x y) (max x y) → |deriv h z| ≤ B) :
    |h y - h x| ≤ B * |y - x| := by
  by_cases h_eq : x = y
  · rw [h_eq] <;> simp
  · by_cases h_lt : x < y
    · have h_cont : ContinuousOn h (Set.Icc x y) := h_diff.continuous.continuousOn
      have hfd : ∀ z ∈ Set.Ioo x y, HasDerivAt h (deriv h z) z :=
        fun z _ => h_diff.differentiableAt.hasDerivAt
      have h_mvt : ∃ c ∈ Set.Ioo x y,
          deriv h c = (h y - h x) / (y - x) :=
        exists_hasDerivAt_eq_slope (f := h) (f' := deriv h) h_lt h_cont hfd
      rcases h_mvt with ⟨c, hc, hderiv⟩
      have hc' : c ∈ Set.Icc (min x y) (max x y) := by
        have hmin : min x y = x := by rw [min_eq_left]; linarith
        have hmax : max x y = y := by rw [max_eq_right]; linarith
        rw [hmin, hmax]
        exact ⟨by linarith [hc.1], by linarith [hc.2]⟩
      have h_bound' : |deriv h c| ≤ B := h_bound c hc'
      have h_main : h y - h x = deriv h c * (y - x) := by
        rw [hderiv] <;> field_simp [show y - x ≠ 0 by linarith] <;> ring
      calc |h y - h x|
        = |deriv h c| * |y - x| := by rw [h_main, abs_mul]
      _ ≤ B * |y - x| := by gcongr
    · have h_gt : y < x := by
        rcases lt_trichotomy x y with (h | h | h) <;> tauto
      have h_cont : ContinuousOn h (Set.Icc y x) := h_diff.continuous.continuousOn
      have hfd : ∀ z ∈ Set.Ioo y x, HasDerivAt h (deriv h z) z :=
        fun z _ => h_diff.differentiableAt.hasDerivAt
      have h_mvt : ∃ c ∈ Set.Ioo y x,
          deriv h c = (h x - h y) / (x - y) :=
        exists_hasDerivAt_eq_slope (f := h) (f' := deriv h) h_gt h_cont hfd
      rcases h_mvt with ⟨c, hc, hderiv⟩
      have hc' : c ∈ Set.Icc (min x y) (max x y) := by
        have hmin : min x y = y := by rw [min_eq_right]; linarith
        have hmax : max x y = x := by rw [max_eq_left]; linarith
        rw [hmin, hmax]
        exact ⟨by linarith [hc.1], by linarith [hc.2]⟩
      have h_bound' : |deriv h c| ≤ B := h_bound c hc'
      have h_main : h x - h y = deriv h c * (x - y) := by
        rw [hderiv] <;> field_simp [show x - y ≠ 0 by linarith] <;> ring
      calc |h y - h x|
        = |h x - h y| := by rw [abs_sub_comm]
      _ = |deriv h c| * |x - y| := by rw [h_main, abs_mul]
      _ = |deriv h c| * |y - x| := by rw [abs_sub_comm]
      _ ≤ B * |y - x| := by gcongr

/-- Lipschitz estimate for the value difference of two `C2Function`s. -/
lemma lipschitz_value (f g : C2Function) (x y : UnitPoint) :
    |(f x - g x) - (f y - g y)| ≤
      c2Distance f g * |(x : ℝ) - (y : ℝ)| := by
  let h : ℝ → ℝ := f.extension - g.extension
  have h_f_c2 : ContDiff ℝ 2 f.extension := f.extension_contDiff
  have h_g_c2 : ContDiff ℝ 2 g.extension := g.extension_contDiff
  have h_c2 : ContDiff ℝ 2 h := by
    have h_sub : ContDiff ℝ 2 (fun x => f.extension x - g.extension x) :=
      ContDiff.sub h_f_c2 h_g_c2
    convert h_sub using 1 <;> funext z <;> rfl
  have h_diff : Differentiable ℝ h := ContDiff.differentiable h_c2 (by norm_num)
  have h_f_diff : Differentiable ℝ f.extension :=
    ContDiff.differentiable h_f_c2 (by norm_num)
  have h_g_diff : Differentiable ℝ g.extension :=
    ContDiff.differentiable h_g_c2 (by norm_num)
  set xr := (x : ℝ) with hxr
  set yr := (y : ℝ) with hyr
  have h_bound : ∀ (z : ℝ), z ∈ Set.Icc (min xr yr) (max xr yr) →
      |deriv h z| ≤ c2Distance f g := by
    intro z hz
    have hz1 : 0 ≤ z := by
      have hmin1 : 0 ≤ xr := x.property.1
      have hmin2 : 0 ≤ yr := y.property.1
      have hmin : 0 ≤ min xr yr := le_min hmin1 hmin2
      linarith [hz.1]
    have hz2 : z ≤ 1 := by
      have hmax1 : xr ≤ 1 := x.property.2
      have hmax2 : yr ≤ 1 := y.property.2
      have hmax : max xr yr ≤ 1 := max_le hmax1 hmax2
      linarith [hz.2]
    let z' : UnitPoint := ⟨z, ⟨hz1, hz2⟩⟩
    have hderiv : deriv h z = f.firstDeriv z' - g.firstDeriv z' := by
      have h1 : deriv h z = deriv f.extension z - deriv g.extension z :=
        deriv_sub (h_f_diff z) (h_g_diff z)
      rw [h1]
      have h2 : deriv f.extension z = f.firstDeriv z' :=
        C2Function.deriv_extension_eq_firstDeriv f z'
      have h3 : deriv g.extension z = g.firstDeriv z' :=
        C2Function.deriv_extension_eq_firstDeriv g z'
      rw [h2, h3] <;> abel
    rw [hderiv]
    exact abs_firstDeriv_sub_le_c2Distance f g z'
  have h_main := real_lipschitz_of_deriv_bound h_diff h_bound
  have h_eval1 : h xr = f x - g x := by
    have h1 : h xr = f.extension xr - g.extension xr := by
      simp [h] <;> rfl
    rw [h1]
    have h2 : f.extension xr = f x := C2Function.extension_eq_value f x
    have h3 : g.extension xr = g x := C2Function.extension_eq_value g x
    rw [h2, h3] <;> abel
  have h_eval2 : h yr = f y - g y := by
    have h1 : h yr = f.extension yr - g.extension yr := by
      simp [h] <;> rfl
    rw [h1]
    have h2 : f.extension yr = f y := C2Function.extension_eq_value f y
    have h3 : g.extension yr = g y := C2Function.extension_eq_value g y
    rw [h2, h3] <;> abel
  have h_final : |h xr - h yr| ≤ c2Distance f g * |xr - yr| := by
    simpa [abs_sub_comm] using h_main
  rw [h_eval1, h_eval2] at h_final
  exact h_final

/-- Lipschitz estimate for the first-derivative difference of two `C2Function`s. -/
lemma lipschitz_deriv (f g : C2Function) (x y : UnitPoint) :
    |(f.firstDeriv x - g.firstDeriv x) -
       (f.firstDeriv y - g.firstDeriv y)| ≤
      c2Distance f g * |(x : ℝ) - (y : ℝ)| := by
  let h0 : ℝ → ℝ := f.extension - g.extension
  let h : ℝ → ℝ := deriv h0
  have h_f_c2 : ContDiff ℝ 2 f.extension := f.extension_contDiff
  have h_g_c2 : ContDiff ℝ 2 g.extension := g.extension_contDiff
  have h0_c2 : ContDiff ℝ 2 h0 := by
    have h_sub : ContDiff ℝ 2 (fun x => f.extension x - g.extension x) :=
      ContDiff.sub h_f_c2 h_g_c2
    convert h_sub using 1 <;> funext z <;> rfl
  have h1_c2 : ContDiff ℝ 1 h := ContDiff.deriv' (n := 1) h0_c2
  have h_diff : Differentiable ℝ h := ContDiff.differentiable h1_c2 (by norm_num)
  have h_f_diff : Differentiable ℝ f.extension :=
    ContDiff.differentiable h_f_c2 (by norm_num)
  have h_g_diff : Differentiable ℝ g.extension :=
    ContDiff.differentiable h_g_c2 (by norm_num)
  have h_f_diff2 : Differentiable ℝ (deriv f.extension) :=
    ContDiff.differentiable (ContDiff.deriv' (n := 1) h_f_c2) (by norm_num)
  have h_g_diff2 : Differentiable ℝ (deriv g.extension) :=
    ContDiff.differentiable (ContDiff.deriv' (n := 1) h_g_c2) (by norm_num)
  set xr := (x : ℝ) with hxr
  set yr := (y : ℝ) with hyr
  have h_bound : ∀ (z : ℝ), z ∈ Set.Icc (min xr yr) (max xr yr) →
      |deriv h z| ≤ c2Distance f g := by
    intro z hz
    have hz1 : 0 ≤ z := by
      have hmin1 : 0 ≤ xr := x.property.1
      have hmin2 : 0 ≤ yr := y.property.1
      have hmin : 0 ≤ min xr yr := le_min hmin1 hmin2
      linarith [hz.1]
    have hz2 : z ≤ 1 := by
      have hmax1 : xr ≤ 1 := x.property.2
      have hmax2 : yr ≤ 1 := y.property.2
      have hmax : max xr yr ≤ 1 := max_le hmax1 hmax2
      linarith [hz.2]
    let z' : UnitPoint := ⟨z, ⟨hz1, hz2⟩⟩
    have hderiv : deriv h z = f.secondDeriv z' - g.secondDeriv z' := by
      have h1 : deriv h z = deriv (deriv h0) z := by rfl
      rw [h1]
      have h2 : deriv (deriv h0) z = deriv (deriv f.extension) z - deriv (deriv g.extension) z := by
        have h_eq : deriv h0 = fun w => deriv f.extension w - deriv g.extension w := by
          funext w
          exact deriv_sub (h_f_diff w) (h_g_diff w)
        rw [h_eq]
        exact deriv_sub (h_f_diff2 z) (h_g_diff2 z)
      rw [h2]
      have h3 : deriv (deriv f.extension) z = f.secondDeriv z' :=
        C2Function.secondDeriv_extension_eq_secondDeriv f z'
      have h4 : deriv (deriv g.extension) z = g.secondDeriv z' :=
        C2Function.secondDeriv_extension_eq_secondDeriv g z'
      rw [h3, h4] <;> abel
    rw [hderiv]
    exact abs_secondDeriv_sub_le_c2Distance f g z'
  have h_main := real_lipschitz_of_deriv_bound h_diff h_bound
  have h_eval1 : h xr = f.firstDeriv x - g.firstDeriv x := by
    have h1 : h xr = deriv h0 xr := by rfl
    rw [h1]
    have h2 : deriv h0 xr = deriv f.extension xr - deriv g.extension xr :=
      deriv_sub (h_f_diff xr) (h_g_diff xr)
    rw [h2]
    have h3 : deriv f.extension xr = f.firstDeriv x :=
      C2Function.deriv_extension_eq_firstDeriv f x
    have h4 : deriv g.extension xr = g.firstDeriv x :=
      C2Function.deriv_extension_eq_firstDeriv g x
    rw [h3, h4] <;> abel
  have h_eval2 : h yr = f.firstDeriv y - g.firstDeriv y := by
    have h1 : h yr = deriv h0 yr := by rfl
    rw [h1]
    have h2 : deriv h0 yr = deriv f.extension yr - deriv g.extension yr :=
      deriv_sub (h_f_diff yr) (h_g_diff yr)
    rw [h2]
    have h3 : deriv f.extension yr = f.firstDeriv y :=
      C2Function.deriv_extension_eq_firstDeriv f y
    have h4 : deriv g.extension yr = g.firstDeriv y :=
      C2Function.deriv_extension_eq_firstDeriv g y
    rw [h3, h4] <;> abel
  have h_final : |h xr - h yr| ≤ c2Distance f g * |xr - yr| := by
    simpa [abs_sub_comm] using h_main
  rw [h_eval1, h_eval2] at h_final
  exact h_final

/-- The infimum defining `tangencyParameterOn` is attained. -/
lemma tangency_parameter_attained (I : ParameterInterval) (f g : C2Function) :
    ∃ (x : UnitPoint), x ∈ I.centeredCarrier (1 / 2) ∧
      |f x - g x| + |f.firstDeriv x - g.firstDeriv x| =
        tangencyParameterOn I f g := by
  let S := I.centeredCarrier (1 / 2)
  let F : UnitPoint → ℝ := fun x =>
    |f x - g x| + |f.firstDeriv x - g.firstDeriv x|
  have h21 : Continuous (fun (x : UnitPoint) => |(x : ℝ) - I.midpoint|) := by
    continuity
  have h2 : IsClosed {x : UnitPoint | |(x : ℝ) - I.midpoint| ≤ (1 / 2 : ℝ) * I.length / 2} :=
    IsClosed.preimage h21 isClosed_Iic
  have h3 : S =
      {x : UnitPoint | |(x : ℝ) - I.midpoint| ≤ (1 / 2 : ℝ) * I.length / 2} := by
    ext z
    rfl
  have hS_closed : IsClosed S := by
    rw [h3] <;> exact h2
  have hS_compact : IsCompact S := hS_closed.isCompact
  have h_left_nonneg : 0 ≤ I.left := I.left_mem.1
  have h_right_le_one : I.right ≤ 1 := I.right_mem.2
  have h_le : I.left ≤ I.right := I.left_le_right
  have h_mid_nonneg : 0 ≤ I.midpoint := by
    dsimp only [ParameterInterval.midpoint]
    have h : I.left ≤ (I.left + I.right) / 2 := by linarith
    linarith
  have h_mid_le_one : I.midpoint ≤ 1 := by
    dsimp only [ParameterInterval.midpoint]
    have h : (I.left + I.right) / 2 ≤ I.right := by linarith
    linarith
  have h_mid3 : I.midpoint ∈ unitInterval := ⟨h_mid_nonneg, h_mid_le_one⟩
  let midpoint' : UnitPoint := ⟨I.midpoint, h_mid3⟩
  have h_mid_in_S : midpoint' ∈ S := by
    have h5 : |(I.midpoint : ℝ) - I.midpoint| ≤ (1 / 2 : ℝ) * I.length / 2 := by
      have h6 : |(I.midpoint : ℝ) - I.midpoint| = 0 := by
        have h7 : (I.midpoint : ℝ) - I.midpoint = 0 := by ring
        rw [h7]; simp
      rw [h6]
      have h8 : 0 ≤ (1 / 2 : ℝ) * I.length / 2 := by
        have h9 : 0 ≤ I.length := I.length_nonneg
        positivity
      linarith
    exact h5
  have hS_nonempty : S.Nonempty := ⟨midpoint', h_mid_in_S⟩
  have hF_cont : Continuous F := by continuity
  have h_exists : ∃ (x₀ : UnitPoint), x₀ ∈ S ∧ IsMinOn F S x₀ :=
    hS_compact.exists_isMinOn hS_nonempty hF_cont.continuousOn
  rcases h_exists with ⟨x₀, hx₀S, hmin⟩
  have h_image : F '' S =
      {r : ℝ | ∃ x ∈ S, r = F x} := by
    ext r
    simp [Set.mem_image] <;> aesop
  have h_least : IsLeast (F '' S) (F x₀) := by
    constructor
    · exact ⟨x₀, hx₀S, rfl⟩
    · intro r hr
      rcases hr with ⟨y, hyS, rfl⟩
      exact hmin (a := y) hyS
  have h_bdd : BddBelow (F '' S) := by
    use 0
    intro r hr
    rcases hr with ⟨y, _, rfl⟩
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hS'_nonempty : (F '' S).Nonempty :=
    ⟨F x₀, x₀, hx₀S, rfl⟩
  letI : BddBelow (F '' S) := h_bdd
  have h1 : F x₀ ≤ sInf (F '' S) := le_csInf hS'_nonempty h_least.2
  have h2 : sInf (F '' S) ≤ F x₀ := csInf_le h_bdd h_least.1
  have h_eq : sInf (F '' S) = F x₀ := by linarith
  rw [h_image] at h_eq
  exact ⟨x₀, hx₀S, h_eq.symm⟩

/--
Taylor quadratic lower bound: if `H` is twice differentiable and `H'' ≥ c`
on `[a,b]`, then for `x, y ∈ [a,b]`,
`H(x) ≥ H(y) + H'(y)(x-y) + c/2 · (x-y)²`.

Proof: set `K(z) := H(z) - c/2 · z²`. Then `K'' = H'' - c ≥ 0`, so `K` is
convex. The tangent-line inequality at `y` gives the result after algebra.
-/
lemma taylor_quadratic_lower_bound {H : ℝ → ℝ} {c a b x y : ℝ}
    (hH_diff1 : Differentiable ℝ H)
    (hH_diff2 : Differentiable ℝ (deriv H))
    (_hab : a ≤ b)
    (hy : y ∈ Set.Icc a b)
    (hx : x ∈ Set.Icc a b)
    (hH'' : ∀ z ∈ Set.Icc a b, c ≤ deriv (deriv H) z) :
    H x ≥ H y + deriv H y * (x - y) + c / 2 * (x - y)^2 := by
  let K : ℝ → ℝ := fun z => H z - c / 2 * z^2
  have hK_diff1 : Differentiable ℝ K := by
    have h_pow : Differentiable ℝ (fun z : ℝ => z^2) := by
      have h : Differentiable ℝ (fun z : ℝ => z * z) := differentiable_id.mul differentiable_id
      have h_eq : (fun z : ℝ => z * z) = (fun z : ℝ => z^2) := by funext z; simp [pow_two]
      rw [h_eq] at h; exact h
    have h_scaled : Differentiable ℝ (fun z : ℝ => c / 2 * z^2) := h_pow.const_mul (c / 2)
    exact hH_diff1.sub h_scaled
  have hderiv_K : ∀ z, deriv K z = deriv H z - c * z := by
    intro z
    have hd : HasDerivAt K (deriv H z - c * z) z := by
      have h1 : HasDerivAt H (deriv H z) z := hH_diff1.differentiableAt.hasDerivAt
      have h2 : HasDerivAt (fun z : ℝ => c / 2 * z^2) (c * z) z := by
        have h_id : HasDerivAt (fun z : ℝ => z) 1 z := hasDerivAt_id' z
        have h3 : HasDerivAt (fun z : ℝ => z^2) (2 * z) z := by
          have h_mul : HasDerivAt (fun z : ℝ => z * z) (1 * z + z * 1) z := h_id.mul h_id
          have h_eq1 : (fun z : ℝ => z^2) = (fun z : ℝ => z * z) := by funext t; simp [pow_two]
          have h_deriv : 1 * z + z * 1 = 2 * z := by ring
          rw [h_eq1]; rw [h_deriv] at h_mul; exact h_mul
        have h4 : HasDerivAt (fun z : ℝ => c / 2 * z^2) (c / 2 * (2 * z)) z := h3.const_mul (c / 2)
        have h5 : c / 2 * (2 * z) = c * z := by ring
        rw [h5] at h4; exact h4
      exact h1.sub h2
    exact hd.deriv
  have hK_diff2 : Differentiable ℝ (deriv K) := by
    have h_eq : deriv K = fun z => deriv H z - c * z := by
      funext z; exact hderiv_K z
    rw [h_eq]
    have h3 : Differentiable ℝ (fun z : ℝ => c * z) := differentiable_id.const_mul c
    exact hH_diff2.sub h3
  have hK'' : ∀ z ∈ Set.Icc a b, 0 ≤ deriv (deriv K) z := by
    intro z hz
    have h2 : deriv (deriv K) z = deriv (deriv H) z - c := by
      have h3 : deriv (deriv K) z = deriv (fun s => deriv H s - c * s) z := by
        congr with s; exact hderiv_K s
      rw [h3]
      have hd1 : HasDerivAt (deriv H) (deriv (deriv H) z) z :=
        hH_diff2.differentiableAt.hasDerivAt
      have hd2 : HasDerivAt (fun s : ℝ => c * s) c z := by
        simpa [mul_one] using (hasDerivAt_id' z).const_mul c
      have hd3 : HasDerivAt (fun s => deriv H s - c * s)
          (deriv (deriv H) z - c) z := hd1.sub hd2
      exact hd3.deriv
    rw [h2]
    have h4 : c ≤ deriv (deriv H) z := hH'' z hz
    linarith
  have h_convex : ConvexOn ℝ (Set.Icc a b) K :=
    convexOn_of_deriv2_nonneg' (convex_Icc a b)
      hK_diff1.differentiableOn hK_diff2.differentiableOn hK''
  have h_tan : K x ≥ K y + deriv K y * (x - y) := by
    by_cases h_eq : x = y
    · subst h_eq; simp
    · by_cases h_lt : x < y
      · have h : slope K x y ≤ deriv K y :=
          h_convex.slope_le_deriv hx hy h_lt (hK_diff1 y)
        have h_pos : 0 < y - x := by linarith
        have h_s : slope K x y = (K y - K x) / (y - x) := by
          simp [slope] <;> ring
        rw [h_s] at h
        have h6 : (K y - K x) / (y - x) ≤ deriv K y := h
        have h7 : 0 ≤ y - x := by linarith
        have h8 : (K y - K x) / (y - x) * (y - x) ≤ deriv K y * (y - x) :=
          mul_le_mul_of_nonneg_right h6 h7
        have h9 : (K y - K x) / (y - x) * (y - x) = K y - K x := by
          field_simp [h_pos.ne'] <;> ring
        rw [h9] at h8
        linarith
      · have h_gt : y < x := by
          rcases lt_trichotomy x y with (h | h | h) <;> tauto
        have h : deriv K y ≤ slope K y x :=
          h_convex.deriv_le_slope hy hx h_gt (hK_diff1 y)
        have h_pos : 0 < x - y := by linarith
        have h_s : slope K y x = (K x - K y) / (x - y) := by
          simp [slope] <;> ring
        rw [h_s] at h
        have h6 : deriv K y ≤ (K x - K y) / (x - y) := h
        have h7 : 0 ≤ x - y := by linarith
        have h8 : deriv K y * (x - y) ≤ ((K x - K y) / (x - y)) * (x - y) :=
          mul_le_mul_of_nonneg_right h6 h7
        have h9 : ((K x - K y) / (x - y)) * (x - y) = K x - K y := by
          field_simp [h_pos.ne'] <;> ring
        rw [h9] at h8
        linarith
  have hK_y : K y = H y - c / 2 * y^2 := by simp [K] <;> ring
  have hderiv_K_y : deriv K y = deriv H y - c * y := hderiv_K y
  have hK_x : K x = H x - c / 2 * x^2 := by simp [K] <;> ring
  rw [hK_x, hK_y, hderiv_K_y] at h_tan
  linarith

/--
A continuous function that is never zero on a closed interval has constant sign.
-/
lemma constant_sign_of_never_zero {f : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r)
    (hcont : ContinuousOn f (Set.Icc l r))
    (hne : ∀ x ∈ Set.Icc l r, f x ≠ 0) :
    (∀ x ∈ Set.Icc l r, 0 < f x) ∨ (∀ x ∈ Set.Icc l r, f x < 0) := by
  have h_ll : l ∈ Set.Icc l r := ⟨by linarith, by linarith⟩
  have h_l_ne : f l ≠ 0 := hne l h_ll
  have h_cases : f l < 0 ∨ 0 < f l := lt_or_gt_of_ne h_l_ne
  rcases h_cases with (hneg_l | hpos_l)
  · right
    intro x hx
    have h_x_ne : f x ≠ 0 := hne x hx
    have h_x_cases : f x < 0 ∨ 0 < f x := lt_or_gt_of_ne h_x_ne
    rcases h_x_cases with (hneg_x | hpos_x)
    · exact hneg_x
    · have h_conn : IsPreconnected (Set.Icc l r) := isPreconnected_Icc
      have h_sub : Set.Icc (f l) (f x) ⊆ f '' (Set.Icc l r) :=
        h_conn.intermediate_value h_ll hx hcont
      have h0 : (0 : ℝ) ∈ Set.Icc (f l) (f x) := ⟨by linarith, by linarith⟩
      have h_ivt : (0 : ℝ) ∈ f '' (Set.Icc l r) := h_sub h0
      rcases h_ivt with ⟨z, hz, hz0⟩
      exact False.elim (hne z hz hz0)
  · left
    intro x hx
    have h_x_ne : f x ≠ 0 := hne x hx
    have h_x_cases : f x < 0 ∨ 0 < f x := lt_or_gt_of_ne h_x_ne
    rcases h_x_cases with (hneg_x | hpos_x)
    · have h_conn : IsPreconnected (Set.Icc l r) := isPreconnected_Icc
      have h_sub : Set.Icc (f x) (f l) ⊆ f '' (Set.Icc l r) :=
        h_conn.intermediate_value hx h_ll hcont
      have h0 : (0 : ℝ) ∈ Set.Icc (f x) (f l) := ⟨by linarith, by linarith⟩
      have h_ivt : (0 : ℝ) ∈ f '' (Set.Icc l r) := h_sub h0
      rcases h_ivt with ⟨z, hz, hz0⟩
      exact False.elim (hne z hz hz0)
    · exact hpos_x

end Kakeya.Cinematic
