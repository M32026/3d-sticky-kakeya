import MyLeanRepo.Kakeya.Cinematic.Targets.TangencySublevelDiameter.Helpers

/-!
# Calculus helpers for tangency interval extension

These closed lemmas isolate the two one-dimensional estimates used in PYZ
Lemma 18.
-/

namespace Kakeya.Cinematic

/--
If a twice differentiable function is bounded by `B` on `[a, b]` and its
second derivative is at least `c`, then `c * (b - a)² ≤ 16B`.
-/
lemma interval_sq_le_of_second_deriv_lower
    {H : ℝ → ℝ} {a b c B : ℝ}
    (hH1 : Differentiable ℝ H)
    (hH2 : Differentiable ℝ (deriv H))
    (hab : a ≤ b)
    (hbound : ∀ z ∈ Set.Icc a b, |H z| ≤ B)
    (hsecond : ∀ z ∈ Set.Icc a b, c ≤ deriv (deriv H) z) :
    c * (b - a) ^ 2 ≤ 16 * B := by
  let m : ℝ := (a + b) / 2
  have hm : m ∈ Set.Icc a b := by
    dsimp only [m]
    constructor <;> linarith
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hleft :=
    taylor_quadratic_lower_bound hH1 hH2 hab hm ha hsecond
  have hright :=
    taylor_quadratic_lower_bound hH1 hH2 hab hm hb hsecond
  have hHa := hbound a ha
  have hHb := hbound b hb
  have hHm := hbound m hm
  have hHa_upper : H a ≤ B := (abs_le.mp hHa).2
  have hHb_upper : H b ≤ B := (abs_le.mp hHb).2
  have hHm_lower : -B ≤ H m := (abs_le.mp hHm).1
  have hsum :
      H a + H b ≥
        2 * H m + c / 2 * ((a - m) ^ 2 + (b - m) ^ 2) := by
    calc
      H a + H b ≥
          (H m + deriv H m * (a - m) + c / 2 * (a - m) ^ 2) +
            (H m + deriv H m * (b - m) + c / 2 * (b - m) ^ 2) :=
        add_le_add hleft hright
      _ = 2 * H m + c / 2 * ((a - m) ^ 2 + (b - m) ^ 2) := by
        dsimp only [m]
        ring
  have hsquares :
      (a - m) ^ 2 + (b - m) ^ 2 = (b - a) ^ 2 / 2 := by
    dsimp only [m]
    ring
  rw [hsquares] at hsum
  nlinarith

/--
Taylor's theorem with a quadratic remainder, derived from the existing
one-sided quadratic estimate.
-/
lemma taylor_remainder_bound_on_interval
    {H : ℝ → ℝ} {d a b x y : ℝ}
    (hH1 : Differentiable ℝ H)
    (hH2 : Differentiable ℝ (deriv H))
    (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b)
    (hy : y ∈ Set.Icc a b)
    (hsecond : ∀ z ∈ Set.Icc a b, |deriv (deriv H) z| ≤ d) :
    |H x - H y - deriv H y * (x - y)| ≤ d / 2 * (x - y) ^ 2 := by
  have hlower : ∀ z ∈ Set.Icc a b, -d ≤ deriv (deriv H) z := by
    intro z hz
    exact (abs_le.mp (hsecond z hz)).1
  have hupper : ∀ z ∈ Set.Icc a b, deriv (deriv H) z ≤ d := by
    intro z hz
    exact (abs_le.mp (hsecond z hz)).2
  have hlower_taylor :=
    taylor_quadratic_lower_bound hH1 hH2 hab hy hx hlower
  have hneg1 : Differentiable ℝ (-H) := hH1.neg
  have hneg2 : Differentiable ℝ (deriv (-H)) := by
    have heq : deriv (-H) = -deriv H := by
      funext z
      simp
    rw [heq]
    exact hH2.neg
  have hneg_second :
      ∀ z ∈ Set.Icc a b, -d ≤ deriv (deriv (-H)) z := by
    intro z hz
    have heq : deriv (deriv (-H)) z = -deriv (deriv H) z := by
      have hderiv : deriv (-H) = -deriv H := by
        funext w
        simp
      rw [hderiv]
      simp
    rw [heq]
    linarith [hupper z hz]
  have hupper_taylor :=
    taylor_quadratic_lower_bound hneg1 hneg2 hab hy hx hneg_second
  have hneg_x : (-H) x = -H x := by rfl
  have hneg_y : (-H) y = -H y := by rfl
  have hneg_deriv : deriv (-H) y = -deriv H y := by simp
  rw [hneg_x, hneg_y, hneg_deriv] at hupper_taylor
  rw [abs_le]
  constructor <;> nlinarith

/--
If `|f-g| ≤ δ` on `J` and
`dist(f,g) * |J|² ≤ Aδ`, then the value difference on the genuine centered
`λ`-dilation of `J` is at most `(3 + A) λ² δ`.
-/
lemma value_bound_on_centered_dilation
    (f g : C2Function) (J : ParameterInterval)
    {delta A lambda : ℝ} {x : UnitPoint}
    (hdelta : 0 ≤ delta)
    (hA : 0 ≤ A)
    (hJpos : 0 < J.length)
    (hclose : ∀ y ∈ J.carrier, |f y - g y| ≤ delta)
    (hsquare : c2Distance f g * J.length ^ 2 ≤ A * delta)
    (hlambda : 1 ≤ lambda)
    (hx : x ∈ J.centeredCarrier lambda) :
    |f x - g x| ≤ (3 + A) * lambda ^ 2 * delta := by
  let H : ℝ → ℝ := f.extension - g.extension
  have hf2 : ContDiff ℝ 2 f.extension := f.extension_contDiff
  have hg2 : ContDiff ℝ 2 g.extension := g.extension_contDiff
  have hH2 : ContDiff ℝ 2 H := hf2.sub hg2
  have hH1diff : Differentiable ℝ H :=
    hH2.differentiable (by norm_num)
  have hH2diff : Differentiable ℝ (deriv H) :=
    hH2.differentiable_deriv_two
  have hf_diff : Differentiable ℝ f.extension :=
    hf2.differentiable (by norm_num)
  have hg_diff : Differentiable ℝ g.extension :=
    hg2.differentiable (by norm_num)
  have hf_deriv_diff : Differentiable ℝ (deriv f.extension) :=
    hf2.differentiable_deriv_two
  have hg_deriv_diff : Differentiable ℝ (deriv g.extension) :=
    hg2.differentiable_deriv_two
  have hH_value (y : UnitPoint) :
      H y = f y - g y := by
    simp [H]
  have hH_deriv (y : UnitPoint) :
      deriv H y = f.firstDeriv y - g.firstDeriv y := by
    rw [show H = f.extension - g.extension by rfl]
    rw [deriv_sub hf_diff.differentiableAt hg_diff.differentiableAt]
    simp
  have hH_second (y : UnitPoint) :
      deriv (deriv H) y = f.secondDeriv y - g.secondDeriv y := by
    have hderiv :
        deriv H = deriv f.extension - deriv g.extension := by
      funext z
      rw [show H = f.extension - g.extension by rfl]
      exact deriv_sub hf_diff.differentiableAt hg_diff.differentiableAt
    rw [hderiv]
    rw [deriv_sub hf_deriv_diff.differentiableAt
      hg_deriv_diff.differentiableAt]
    simp
  have hleft_mem : J.left ∈ Set.Icc (0 : ℝ) 1 := J.left_mem
  have hright_mem : J.right ∈ Set.Icc (0 : ℝ) 1 := J.right_mem
  have hleft_lt_right : J.left < J.right := by
    simpa [ParameterInterval.length] using hJpos
  have hmvt :
      ∃ c ∈ Set.Ioo J.left J.right,
        deriv H c = (H J.right - H J.left) / (J.right - J.left) :=
    exists_deriv_eq_slope H hleft_lt_right
      hH1diff.continuous.continuousOn hH1diff.differentiableOn
  rcases hmvt with ⟨c, hc, hc_slope⟩
  have hc01 : c ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hleft_mem.1, hright_mem.2, hc.1, hc.2]
  let cp : UnitPoint := ⟨c, hc01⟩
  let leftPoint : UnitPoint := ⟨J.left, J.left_mem⟩
  let rightPoint : UnitPoint := ⟨J.right, J.right_mem⟩
  have hleft_carrier : leftPoint ∈ J.carrier := by
    exact ⟨le_rfl, J.left_le_right⟩
  have hright_carrier : rightPoint ∈ J.carrier := by
    exact ⟨J.left_le_right, le_rfl⟩
  have hcp_carrier : cp ∈ J.carrier := by
    exact ⟨hc.1.le, hc.2.le⟩
  have hleft_bound : |H J.left| ≤ delta := by
    rw [hH_value leftPoint]
    exact hclose leftPoint hleft_carrier
  have hright_bound : |H J.right| ≤ delta := by
    rw [hH_value rightPoint]
    exact hclose rightPoint hright_carrier
  have hcp_bound : |H c| ≤ delta := by
    rw [hH_value cp]
    exact hclose cp hcp_carrier
  have hslope_bound :
      |deriv H c| ≤ 2 * delta / J.length := by
    rw [hc_slope]
    rw [show J.right - J.left = J.length by rfl]
    rw [abs_div, abs_of_pos hJpos]
    calc
      |H J.right - H J.left| / J.length
          ≤ (|H J.right| + |H J.left|) / J.length := by
            gcongr
            exact abs_sub _ _
      _ ≤ (delta + delta) / J.length := by gcongr
      _ = 2 * delta / J.length := by ring
  have hc_mid :
      |c - J.midpoint| ≤ J.length / 2 := by
    rw [abs_le]
    simp only [ParameterInterval.midpoint, ParameterInterval.length]
    constructor <;> linarith [hc.1, hc.2]
  have hxc :
      |(x : ℝ) - c| ≤ lambda * J.length := by
    have htriangle :
        |(x : ℝ) - c| ≤
          |(x : ℝ) - J.midpoint| + |c - J.midpoint| := by
      have heq :
          (x : ℝ) - c =
            ((x : ℝ) - J.midpoint) - (c - J.midpoint) := by ring
      rw [heq]
      exact abs_sub _ _
    have hlen_nonneg : 0 ≤ J.length := J.length_nonneg
    calc
      |(x : ℝ) - c|
          ≤ |(x : ℝ) - J.midpoint| + |c - J.midpoint| := htriangle
      _ ≤ lambda * J.length / 2 + J.length / 2 := by
        gcongr
        exact hx
      _ ≤ lambda * J.length := by
        nlinarith
  have hsecond :
      ∀ z ∈ Set.Icc (0 : ℝ) 1,
        |deriv (deriv H) z| ≤ c2Distance f g := by
    intro z hz
    let zp : UnitPoint := ⟨z, hz⟩
    rw [hH_second zp]
    exact abs_secondDeriv_sub_le_c2Distance f g zp
  have hremainder :
      |H x - H c - deriv H c * ((x : ℝ) - c)| ≤
        c2Distance f g / 2 * ((x : ℝ) - c) ^ 2 :=
    taylor_remainder_bound_on_interval hH1diff hH2diff
      (show (0 : ℝ) ≤ 1 by norm_num) x.property hc01 hsecond
  have hslope_term :
      |deriv H c| * |(x : ℝ) - c| ≤ 2 * lambda * delta := by
    calc
      |deriv H c| * |(x : ℝ) - c|
          ≤ (2 * delta / J.length) * (lambda * J.length) := by
            gcongr
      _ = 2 * lambda * delta := by
        field_simp [hJpos.ne']
        <;> ring
  have hdistance_sq :
      ((x : ℝ) - c) ^ 2 ≤ (lambda * J.length) ^ 2 := by
    have habs_nonneg : 0 ≤ |(x : ℝ) - c| := abs_nonneg _
    have hright_nonneg : 0 ≤ lambda * J.length := by positivity
    have hsquare_abs :
        |(x : ℝ) - c| ^ 2 ≤ (lambda * J.length) ^ 2 := by
      nlinarith
    simpa [sq_abs] using hsquare_abs
  have hremainder_term :
      c2Distance f g / 2 * ((x : ℝ) - c) ^ 2 ≤
        A / 2 * lambda ^ 2 * delta := by
    have hdist_nonneg : 0 ≤ c2Distance f g := dist_nonneg
    calc
      c2Distance f g / 2 * ((x : ℝ) - c) ^ 2
          ≤ c2Distance f g / 2 * (lambda * J.length) ^ 2 := by
            gcongr
      _ = lambda ^ 2 / 2 *
          (c2Distance f g * J.length ^ 2) := by ring
      _ ≤ lambda ^ 2 / 2 * (A * delta) := by
        gcongr
      _ = A / 2 * lambda ^ 2 * delta := by ring
  have hvalue_triangle :
      |H x| ≤
        |H c| +
          |deriv H c| * |(x : ℝ) - c| +
            |H x - H c - deriv H c * ((x : ℝ) - c)| := by
    have heq :
        H x =
          H c + deriv H c * ((x : ℝ) - c) +
            (H x - H c - deriv H c * ((x : ℝ) - c)) := by ring
    calc
      |H x| =
          |H c + deriv H c * ((x : ℝ) - c) +
            (H x - H c - deriv H c * ((x : ℝ) - c))| :=
        congrArg abs heq
      _
          ≤ |H c + deriv H c * ((x : ℝ) - c)| +
              |H x - H c - deriv H c * ((x : ℝ) - c)| :=
            abs_add_le _ _
      _ ≤ (|H c| + |deriv H c * ((x : ℝ) - c)|) +
              |H x - H c - deriv H c * ((x : ℝ) - c)| := by
            gcongr
            exact abs_add_le _ _
      _ = |H c| + |deriv H c| * |(x : ℝ) - c| +
              |H x - H c - deriv H c * ((x : ℝ) - c)| := by
            rw [abs_mul]
  have hraw :
      |H x| ≤
        delta + 2 * lambda * delta +
          A / 2 * lambda ^ 2 * delta := by
    calc
      |H x|
          ≤ |H c| +
              |deriv H c| * |(x : ℝ) - c| +
                |H x - H c - deriv H c * ((x : ℝ) - c)| :=
            hvalue_triangle
      _ ≤ delta + 2 * lambda * delta +
              A / 2 * lambda ^ 2 * delta := by
            exact add_le_add (add_le_add hcp_bound hslope_term)
              (hremainder.trans hremainder_term)
  have hlambda_nonneg : 0 ≤ lambda := by linarith
  have hone_le_sq : 1 ≤ lambda ^ 2 := by nlinarith
  have hlambda_le_sq : lambda ≤ lambda ^ 2 := by nlinarith
  have hdelta_one :
      delta ≤ lambda ^ 2 * delta :=
    by simpa using mul_le_mul_of_nonneg_right hone_le_sq hdelta
  have hdelta_two :
      2 * lambda * delta ≤ 2 * lambda ^ 2 * delta := by
    have htwo :
        2 * lambda ≤ 2 * lambda ^ 2 := by linarith
    exact mul_le_mul_of_nonneg_right htwo hdelta
  have hAterm_nonneg :
      0 ≤ A / 2 * lambda ^ 2 * delta := by positivity
  have hAterm :
      A / 2 * lambda ^ 2 * delta ≤
        A * lambda ^ 2 * delta := by
    have hhalf : A / 2 ≤ A := by linarith
    gcongr
  calc
    |f x - g x|
        = |H x| := by rw [hH_value x]
    _
        ≤ delta + 2 * lambda * delta +
            A / 2 * lambda ^ 2 * delta := hraw
    _ ≤ lambda ^ 2 * delta + 2 * lambda ^ 2 * delta +
          A * lambda ^ 2 * delta := by linarith
    _ = (3 + A) * lambda ^ 2 * delta := by ring

end Kakeya.Cinematic
