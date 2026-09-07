import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs
import MyLeanRepo.Kakeya.Cinematic.Targets.CommonTangentRectangleHelpers
import MyLeanRepo.Kakeya.Cinematic.PreliminaryDichotomy
import MyLeanRepo.Kakeya.Cinematic.TangencyIntervalExtension.Calculus

/-!
# Lift fine tangency to the containing coarse rectangle
-/

namespace Kakeya.Cinematic


lemma sqrt_linear_absorption
    {K x : ℝ}
    (hK : 1 ≤ K)
    (hx : 0 < x) :
    Real.sqrt x + 27 * K * Real.sqrt x ≤
      28 * K * Real.sqrt x := by
  nlinarith [Real.sqrt_pos.mpr hx]

lemma parameter_distance_bound_of_second_deriv
    {K delta Delta d : ℝ}
    (hKpos : 0 < K)
    (hdelta : 0 < delta)
    (hdelta_Delta : delta ≤ Delta)
    (hDeltapos : 0 < Delta)
    (hdpos : 0 < d)
    {I : ParameterInterval}
    {H : ℝ → ℝ}
    (hHc2 : ContDiff ℝ 2 H)
    {x₀ y : UnitPoint}
    (hx₀I : x₀ ∈ I.carrier)
    (hyI : y ∈ I.carrier)
    (hH_x₀ : |H x₀| ≤ Delta)
    (hH'_x₀ : |deriv H x₀| ≤ Delta)
    (hH_y : |H y| ≤ 4 * delta)
    (hsecond_lower :
      ∀ z ∈ I.carrier, d / (6 * K) ≤ |deriv (deriv H) z|)
    (hlarge : 24 * K * Delta ≤ d) :
    |(y : ℝ) - (x₀ : ℝ)| ≤
      Real.sqrt (120 * K * Delta / d) := by
  have hHdiff : Differentiable ℝ H :=
    hHc2.differentiable (by norm_num)
  have hH'diff : Differentiable ℝ (deriv H) :=
    hHc2.differentiable_deriv_two
  have hsecond_ne :
      ∀ r ∈ Set.Icc I.left I.right,
        deriv (deriv H) r ≠ 0 := by
    intro r hr hzero
    have hr01 : r ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨I.left_mem.1.trans hr.1, hr.2.trans I.right_mem.2⟩
    let z : UnitPoint := ⟨r, hr01⟩
    have hzI : z ∈ I.carrier := hr
    have hlower := hsecond_lower z hzI
    rw [hzero, abs_zero] at hlower
    have hpositive : 0 < d / (6 * K) := by positivity
    linarith
  have hsecond_cont :
      ContinuousOn (deriv (deriv H)) (Set.Icc I.left I.right) :=
    hHc2.deriv'.continuous_deriv_one.continuousOn
  have hsign :
      (∀ r ∈ Set.Icc I.left I.right, 0 < deriv (deriv H) r) ∨
        (∀ r ∈ Set.Icc I.left I.right, deriv (deriv H) r < 0) :=
    constant_sign_of_never_zero I.left_le_right hsecond_cont hsecond_ne
  have hx₀real : (x₀ : ℝ) ∈ Set.Icc I.left I.right := hx₀I
  have hyreal : (y : ℝ) ∈ Set.Icc I.left I.right := hyI
  set u : ℝ := |(y : ℝ) - (x₀ : ℝ)| with hu
  have hu_nonneg : 0 ≤ u := abs_nonneg _
  have hu_sq :
      ((y : ℝ) - (x₀ : ℝ)) ^ 2 = u ^ 2 := by
    rw [hu, sq_abs]
  have hquadratic :
      (d / (12 * K)) * u ^ 2 -
          Delta * u - (Delta + 4 * delta) ≤ 0 := by
    rcases hsign with hpositive | hnegative
    · have hsecond_pos :
          ∀ r ∈ Set.Icc I.left I.right,
            d / (6 * K) ≤ deriv (deriv H) r := by
        intro r hr
        have hr01 : r ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨I.left_mem.1.trans hr.1, hr.2.trans I.right_mem.2⟩
        let z : UnitPoint := ⟨r, hr01⟩
        have hzI : z ∈ I.carrier := hr
        have hlower := hsecond_lower z hzI
        have hpos := hpositive r hr
        rw [abs_of_pos hpos] at hlower
        exact hlower
      have htaylor :=
        taylor_quadratic_lower_bound hHdiff hH'diff I.left_le_right
          hx₀real hyreal hsecond_pos
      have hbase : -Delta ≤ H x₀ := (abs_le.mp hH_x₀).1
      have hlinear :
          -Delta * u ≤
            deriv H x₀ * ((y : ℝ) - (x₀ : ℝ)) := by
        calc
          -Delta * u
              ≤ -|deriv H x₀| * u := by
                gcongr
          _ ≤ deriv H x₀ * ((y : ℝ) - (x₀ : ℝ)) := by
            calc
              -|deriv H x₀| * u =
                  -|deriv H x₀ * ((y : ℝ) - (x₀ : ℝ))| := by
                    rw [hu, abs_mul]
                    ring
              _ ≤ deriv H x₀ * ((y : ℝ) - (x₀ : ℝ)) :=
                neg_abs_le _
      have hupper : H y ≤ 4 * delta :=
        (le_abs_self (H y)).trans hH_y
      have hhalf :
          d / (6 * K) / 2 = d / (12 * K) := by ring
      rw [hhalf] at htaylor
      rw [hu_sq] at htaylor
      nlinarith
    · let Hneg : ℝ → ℝ := -H
      have hHneg_diff : Differentiable ℝ Hneg := hHdiff.neg
      have hHneg'_diff : Differentiable ℝ (deriv Hneg) := by
        have heq : deriv Hneg = -deriv H := by
          funext r
          simp [Hneg]
        rw [heq]
        exact hH'diff.neg
      have hsecond_pos :
          ∀ r ∈ Set.Icc I.left I.right,
            d / (6 * K) ≤ deriv (deriv Hneg) r := by
        intro r hr
        have hr01 : r ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨I.left_mem.1.trans hr.1, hr.2.trans I.right_mem.2⟩
        let z : UnitPoint := ⟨r, hr01⟩
        have hzI : z ∈ I.carrier := hr
        have hlower := hsecond_lower z hzI
        have hneg := hnegative r hr
        have heq :
            deriv (deriv Hneg) r = -deriv (deriv H) r := by
          have hfirst : deriv Hneg = -deriv H := by
            funext w
            simp [Hneg]
          rw [hfirst]
          simp
        rw [heq]
        rw [abs_of_neg hneg] at hlower
        exact hlower
      have htaylor :=
        taylor_quadratic_lower_bound hHneg_diff hHneg'_diff
          I.left_le_right hx₀real hyreal hsecond_pos
      have hbase : -Delta ≤ Hneg x₀ := by
        change -Delta ≤ -H x₀
        exact neg_le_neg (abs_le.mp hH_x₀).2
      have hHneg_deriv :
          deriv Hneg x₀ = -deriv H x₀ := by simp [Hneg]
      have hlinear :
          -Delta * u ≤
            deriv Hneg x₀ * ((y : ℝ) - (x₀ : ℝ)) := by
        calc
          -Delta * u
              ≤ -|deriv Hneg x₀| * u := by
                rw [hHneg_deriv, abs_neg]
                gcongr
          _ ≤ deriv Hneg x₀ * ((y : ℝ) - (x₀ : ℝ)) := by
            calc
              -|deriv Hneg x₀| * u =
                  -|deriv Hneg x₀ * ((y : ℝ) - (x₀ : ℝ))| := by
                    rw [hu, abs_mul]
                    ring
              _ ≤ deriv Hneg x₀ * ((y : ℝ) - (x₀ : ℝ)) :=
                neg_abs_le _
      have hupper : Hneg y ≤ 4 * delta := by
        change -H y ≤ 4 * delta
        exact (neg_le_abs (H y)).trans hH_y
      have hhalf :
          d / (6 * K) / 2 = d / (12 * K) := by ring
      rw [hhalf] at htaylor
      rw [hu_sq] at htaylor
      nlinarith
  have hcoefpos : 0 < d / (12 * K) := by positivity
  have hconstant_nonneg : 0 ≤ Delta + 4 * delta := by positivity
  have hsquare_condition :
      Delta ^ 2 ≤
        (d / (12 * K)) * (Delta + 4 * delta) / 2 := by
    have htwo : 2 * Delta ≤ d / (12 * K) := by
      apply (le_div_iff₀ (by positivity : 0 < 12 * K)).2
      nlinarith
    nlinarith
  have hu_bound :
      u ≤ Real.sqrt 2 *
        Real.sqrt ((Delta + 4 * delta) / (d / (12 * K))) :=
    quadratic_inequality_bound hcoefpos hDeltapos.le hconstant_nonneg
      hsquare_condition hquadratic
  have hinside :
      (Delta + 4 * delta) / (d / (12 * K)) ≤
        60 * K * Delta / d := by
    have hsum : Delta + 4 * delta ≤ 5 * Delta := by linarith
    calc
      (Delta + 4 * delta) / (d / (12 * K))
          ≤ (5 * Delta) / (d / (12 * K)) := by gcongr
      _ = 60 * K * Delta / d := by
        field_simp [hdpos.ne', hKpos.ne']
        <;> ring
  have hsqrt_inside := Real.sqrt_le_sqrt hinside
  calc
    |(y : ℝ) - (x₀ : ℝ)| = u := hu.symm
    _ ≤ Real.sqrt 2 *
        Real.sqrt ((Delta + 4 * delta) / (d / (12 * K))) := hu_bound
    _ ≤ Real.sqrt 2 * Real.sqrt (60 * K * Delta / d) := by
      gcongr
    _ = Real.sqrt (120 * K * Delta / d) := by
      rw [← Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
      congr 1
      field_simp [hdpos.ne']
      <;> ring

lemma graph_difference_bound_from_nearby_tangent_point
    {K delta t Delta C_R : ℝ}
    (hK : 1 ≤ K)
    (hdelta : 0 < delta)
    (hdelta_Delta : delta ≤ Delta)
    (ht : 0 < t)
    (hCR : 0 < C_R)
    (hCRlarge : 9216 * K ^ 2 ≤ C_R)
    {f k : C2Function}
    {x y : UnitPoint}
    (hygraph : |f y - k y| ≤ 4 * delta)
    (hyderiv :
      |f.firstDeriv y - k.firstDeriv y| ≤
        28 * K * Real.sqrt (t * Delta))
    (hdistance :
      |(x : ℝ) - (y : ℝ)| ≤
        (Delta - delta) /
          (2 * Real.sqrt (C_R * t * Delta)))
    (hfk_dist : c2Distance f k ≤ 6 * t) :
    |f x - k x| ≤ 4 * Delta := by
  have hDeltapos : 0 < Delta := by linarith
  have hproductpos : 0 < C_R * t * Delta := by positivity
  have hsqrtCRpos : 0 < Real.sqrt C_R := Real.sqrt_pos.mpr hCR
  have hsqrt_tDeltapos : 0 < Real.sqrt (t * Delta) := by positivity
  have hsqrt_product :
      Real.sqrt (C_R * t * Delta) =
        Real.sqrt C_R * Real.sqrt (t * Delta) := by
    rw [show C_R * t * Delta = C_R * (t * Delta) by ring]
    exact Real.sqrt_mul hCR.le _
  have hsqrtCRlarge : 96 * K ≤ Real.sqrt C_R := by
    have hsquare : (96 * K) ^ 2 ≤ C_R := by
      nlinarith
    exact Real.le_sqrt_of_sq_le hsquare
  let H : ℝ → ℝ := f.extension - k.extension
  have hHc2 : ContDiff ℝ 2 H :=
    f.extension_contDiff.sub k.extension_contDiff
  have hHdiff : Differentiable ℝ H :=
    hHc2.differentiable (by norm_num)
  have hH'diff : Differentiable ℝ (deriv H) :=
    hHc2.differentiable_deriv_two
  have hsecond :
      ∀ z ∈ Set.Icc (0 : ℝ) 1,
        |deriv (deriv H) z| ≤ c2Distance f k := by
    intro z hz
    let zp : UnitPoint := ⟨z, hz⟩
    have hf_diff : Differentiable ℝ f.extension :=
      f.extension_contDiff.differentiable (by norm_num)
    have hk_diff : Differentiable ℝ k.extension :=
      k.extension_contDiff.differentiable (by norm_num)
    have hf'_diff : Differentiable ℝ (deriv f.extension) :=
      f.extension_contDiff.differentiable_deriv_two
    have hk'_diff : Differentiable ℝ (deriv k.extension) :=
      k.extension_contDiff.differentiable_deriv_two
    have hderiv :
        deriv H = deriv f.extension - deriv k.extension := by
      funext w
      rw [show H = f.extension - k.extension by rfl]
      exact deriv_sub hf_diff.differentiableAt hk_diff.differentiableAt
    rw [hderiv]
    rw [deriv_sub hf'_diff.differentiableAt hk'_diff.differentiableAt]
    have heq :
        deriv (deriv f.extension) z -
            deriv (deriv k.extension) z =
          f.secondDeriv zp - k.secondDeriv zp := by
      change deriv (deriv f.extension) (zp : ℝ) -
          deriv (deriv k.extension) (zp : ℝ) =
        f.secondDeriv zp - k.secondDeriv zp
      rw [C2Function.secondDeriv_extension_eq_secondDeriv,
        C2Function.secondDeriv_extension_eq_secondDeriv]
    rw [heq]
    exact abs_secondDeriv_sub_le_c2Distance f k zp
  have hremainder :=
    taylor_remainder_bound_on_interval hHdiff hH'diff
      (show (0 : ℝ) ≤ 1 by norm_num) x.property y.property hsecond
  have hHvalue (z : UnitPoint) : H z = f z - k z := by
    simp [H]
  have hHderiv :
      deriv H y = f.firstDeriv y - k.firstDeriv y := by
    have hf_diff : Differentiable ℝ f.extension :=
      f.extension_contDiff.differentiable (by norm_num)
    have hk_diff : Differentiable ℝ k.extension :=
      k.extension_contDiff.differentiable (by norm_num)
    rw [show H = f.extension - k.extension by rfl]
    rw [deriv_sub hf_diff.differentiableAt hk_diff.differentiableAt]
    simp
  have htriangle :
      |H x| ≤ |H y| +
          |deriv H y| * |(x : ℝ) - (y : ℝ)| +
          |H x - H y -
            deriv H y * ((x : ℝ) - (y : ℝ))| := by
    have heq :
        H x =
          H y + deriv H y * ((x : ℝ) - (y : ℝ)) +
            (H x - H y -
              deriv H y * ((x : ℝ) - (y : ℝ))) := by ring
    calc
      |H x| =
          |H y + deriv H y * ((x : ℝ) - (y : ℝ)) +
            (H x - H y -
              deriv H y * ((x : ℝ) - (y : ℝ)))| := congrArg abs heq
      _ ≤ |H y + deriv H y * ((x : ℝ) - (y : ℝ))| +
          |H x - H y -
            deriv H y * ((x : ℝ) - (y : ℝ))| :=
        abs_add_le _ _
      _ ≤ (|H y| + |deriv H y * ((x : ℝ) - (y : ℝ))|) +
          |H x - H y -
            deriv H y * ((x : ℝ) - (y : ℝ))| := by
        gcongr
        exact abs_add_le _ _
      _ = _ := by rw [abs_mul]
  have hlinear :
      |deriv H y| * |(x : ℝ) - (y : ℝ)| ≤
        (7 / 24 : ℝ) * (Delta - delta) := by
    rw [hHderiv]
    calc
      |f.firstDeriv y - k.firstDeriv y| *
          |(x : ℝ) - (y : ℝ)|
          ≤ (28 * K * Real.sqrt (t * Delta)) *
            ((Delta - delta) /
              (2 * Real.sqrt (C_R * t * Delta))) := by
                gcongr
      _ = (14 * K / Real.sqrt C_R) * (Delta - delta) := by
        rw [hsqrt_product]
        field_simp [hsqrt_tDeltapos.ne']
        <;> ring
      _ ≤ (7 / 48 : ℝ) * (Delta - delta) := by
        have hratio : 14 * K / Real.sqrt C_R ≤ 7 / 48 := by
          apply (div_le_iff₀ hsqrtCRpos).2
          nlinarith
        gcongr
      _ ≤ (7 / 24 : ℝ) * (Delta - delta) := by
        gcongr
        norm_num
  have hremainder_bound :
      c2Distance f k / 2 * ((x : ℝ) - (y : ℝ)) ^ 2 ≤
        (1 / 4 : ℝ) * (Delta - delta) := by
    have hsquare :
        ((x : ℝ) - (y : ℝ)) ^ 2 ≤
          ((Delta - delta) /
            (2 * Real.sqrt (C_R * t * Delta))) ^ 2 := by
      have habs_square :
          |(x : ℝ) - (y : ℝ)| ^ 2 ≤
            ((Delta - delta) /
              (2 * Real.sqrt (C_R * t * Delta))) ^ 2 := by
        nlinarith [abs_nonneg ((x : ℝ) - (y : ℝ))]
      simpa [sq_abs] using habs_square
    calc
      c2Distance f k / 2 * ((x : ℝ) - (y : ℝ)) ^ 2
          ≤ (6 * t) / 2 *
            ((Delta - delta) /
              (2 * Real.sqrt (C_R * t * Delta))) ^ 2 := by
                gcongr
      _ = 3 * (Delta - delta) ^ 2 / (4 * C_R * Delta) := by
        rw [div_pow, mul_pow, Real.sq_sqrt hproductpos.le]
        field_simp [hCR.ne', ht.ne', hDeltapos.ne']
        <;> ring
      _ ≤ 3 * (Delta - delta) / (4 * C_R) := by
        have hdiff : 0 ≤ Delta - delta := by linarith
        have hsq_le :
            (Delta - delta) ^ 2 / Delta ≤ Delta - delta := by
          apply (div_le_iff₀ hDeltapos).2
          nlinarith
        calc
          3 * (Delta - delta) ^ 2 / (4 * C_R * Delta) =
              (3 / (4 * C_R)) *
                ((Delta - delta) ^ 2 / Delta) := by ring
          _ ≤ (3 / (4 * C_R)) * (Delta - delta) := by
            gcongr
          _ = 3 * (Delta - delta) / (4 * C_R) := by ring
      _ ≤ (1 / 4 : ℝ) * (Delta - delta) := by
        have hCRone : 3 ≤ C_R := by
          nlinarith [hCRlarge, hK]
        have hcoef : 3 / (4 * C_R) ≤ 1 / 4 := by
          apply (div_le_iff₀ (by positivity : 0 < 4 * C_R)).2
          nlinarith
        have hdiff : 0 ≤ Delta - delta := by linarith
        calc
          3 * (Delta - delta) / (4 * C_R) =
              (3 / (4 * C_R)) * (Delta - delta) := by ring
          _ ≤ (1 / 4) * (Delta - delta) :=
            mul_le_mul_of_nonneg_right hcoef hdiff
  have hHy : |H y| ≤ 4 * delta := by
    rw [hHvalue y]
    exact hygraph
  calc
    |f x - k x| = |H x| := by rw [hHvalue x]
    _ ≤ |H y| + |deriv H y| * |(x : ℝ) - (y : ℝ)| +
        |H x - H y -
          deriv H y * ((x : ℝ) - (y : ℝ))| := htriangle
    _ ≤ 4 * delta + (7 / 24 : ℝ) * (Delta - delta) +
        (1 / 4 : ℝ) * (Delta - delta) := by
      exact add_le_add
        (add_le_add hHy hlinear)
        (hremainder.trans hremainder_bound)
    _ ≤ 4 * Delta := by
      nlinarith

lemma fine_tangency_derivative_bound
    {K D delta t Delta C_R : ℝ}
    (hK : 1 ≤ K)
    (hD : 1 ≤ D)
    (hdelta : 0 < delta)
    (hdelta_Delta : delta ≤ Delta)
    (hDelta_t : Delta ≤ t)
    (ht : 0 < t)
    {family : Set C2Function}
    (hfamily : IsCinematicFamily family K D)
    {I : ParameterInterval}
    (hI : I.IsControlled K)
    {R : CurvilinearRectangle delta (C_R * t * Delta / delta)}
    (hRquarter : R.IsOverCentralQuarterOf I)
    {f k : C2Function}
    (hRk : R.function = k)
    (hk : k ∈ family)
    (hf : f ∈ family)
    (hfk_dist : c2Distance f k ≤ 6 * t)
    (hfk_parameter : tangencyParameterOn I f k ≤ Delta)
    (hRtangent : R.IsLambdaTangent f 5)
    {y : UnitPoint}
    (hy : y ∈ R.interval.carrier) :
    |f.firstDeriv y - k.firstDeriv y| ≤
      28 * K * Real.sqrt (t * Delta) := by
  have hKpos : 0 < K := by linarith
  have hDeltapos : 0 < Delta := by linarith
  have htDeltapos : 0 < t * Delta := mul_pos ht hDeltapos
  have hsqrtpos : 0 < Real.sqrt (t * Delta) :=
    Real.sqrt_pos.mpr htDeltapos
  have hDelta_sqrt : Delta ≤ Real.sqrt (t * Delta) := by
    have hsquare : Delta ^ 2 ≤ t * Delta := by
      nlinarith
    nlinarith [Real.sq_sqrt htDeltapos.le, Real.sqrt_nonneg (t * Delta)]
  have hyIquarter : y ∈ I.centeredCarrier (1 / 4) :=
    hRquarter hy
  have hyI : y ∈ I.carrier :=
    I.centeredCarrier_subset_carrier (by norm_num) (by norm_num) hyIquarter
  have hyclose : |f y - k y| ≤ 4 * delta := by
    have hclose :=
      tangency_implies_value_close hdelta R f (by norm_num) hRtangent y hy
    norm_num at hclose
    simpa [hRk] using hclose
  by_cases hfk : f = k
  · subst f
    simp
    positivity
  have hdpos : 0 < c2Distance f k := by
    simpa [c2Distance_eq_dist] using dist_pos.mpr hfk
  rcases tangency_parameter_attained I f k with
    ⟨x₀, hx₀half, hx₀eq⟩
  have hx₀I : x₀ ∈ I.carrier :=
    I.centeredCarrier_subset_carrier (by norm_num) (by norm_num) hx₀half
  have hx₀value : |f x₀ - k x₀| ≤ Delta := by
    have hnonneg : 0 ≤ |f.firstDeriv x₀ - k.firstDeriv x₀| :=
      abs_nonneg _
    linarith
  have hx₀deriv :
      |f.firstDeriv x₀ - k.firstDeriv x₀| ≤ Delta := by
    have hnonneg : 0 ≤ |f x₀ - k x₀| := abs_nonneg _
    linarith
  have hpoint_distance :
      |(y : ℝ) - (x₀ : ℝ)| ≤ I.length := by
    rw [ParameterInterval.length, abs_le]
    constructor <;> linarith [hyI.1, hyI.2, hx₀I.1, hx₀I.2]
  have hIshort : I.length ≤ 1 / (6 * K) := by
    simpa [ParameterInterval.IsShort] using hI.2
  by_cases hsmall : c2Distance f k < 24 * K * Delta
  · have hlip := lipschitz_deriv f k y x₀
    have hvariation :
        |(f.firstDeriv y - k.firstDeriv y) -
            (f.firstDeriv x₀ - k.firstDeriv x₀)| ≤
          c2Distance f k / (6 * K) := by
      calc
        |(f.firstDeriv y - k.firstDeriv y) -
            (f.firstDeriv x₀ - k.firstDeriv x₀)|
            ≤ c2Distance f k * |(y : ℝ) - (x₀ : ℝ)| := hlip
        _ ≤ c2Distance f k * I.length := by gcongr
        _ ≤ c2Distance f k * (1 / (6 * K)) := by gcongr
        _ = c2Distance f k / (6 * K) := by ring
    have hderiv :
        |f.firstDeriv y - k.firstDeriv y| <
          5 * Delta := by
      have htriangle :
          |f.firstDeriv y - k.firstDeriv y| ≤
            |f.firstDeriv x₀ - k.firstDeriv x₀| +
              |(f.firstDeriv y - k.firstDeriv y) -
                (f.firstDeriv x₀ - k.firstDeriv x₀)| := by
        calc
          |f.firstDeriv y - k.firstDeriv y| =
              |(f.firstDeriv x₀ - k.firstDeriv x₀) +
                ((f.firstDeriv y - k.firstDeriv y) -
                  (f.firstDeriv x₀ - k.firstDeriv x₀))| := by
                    congr 1
                    ring
          _ ≤ _ := abs_add_le _ _
      have hquot :
          c2Distance f k / (6 * K) < 4 * Delta := by
        apply (div_lt_iff₀ (by positivity : 0 < 6 * K)).2
        nlinarith
      linarith
    calc
      |f.firstDeriv y - k.firstDeriv y|
          ≤ 5 * Delta := hderiv.le
      _ ≤ 5 * Real.sqrt (t * Delta) := by gcongr
      _ ≤ 28 * K * Real.sqrt (t * Delta) := by
        gcongr
        nlinarith
  · have hlarge : 24 * K * Delta ≤ c2Distance f k := by
      linarith
    have hdich :=
      preliminary_dichotomy K D hK hD family hfamily I hI.2
        f hf k hk
    rcases hdich with ⟨hvalue_dich, hderiv_dich, hsecond_dich⟩
    have hvalue_small :
        ∀ z ∈ I.carrier,
          |f z - k z| < (3 * K)⁻¹ * c2Distance f k := by
      rcases hvalue_dich with hsmall_value | hlarge_value
      · exact hsmall_value
      · exfalso
        have hlower := hlarge_value x₀ hx₀I
        have hstrict :
            Delta < (6 * K)⁻¹ * c2Distance f k := by
          have hscaled :
              6 * K * Delta < c2Distance f k := by
            nlinarith [hlarge, hKpos, hDeltapos]
          rw [inv_mul_eq_div]
          apply (lt_div_iff₀ (by positivity : 0 < 6 * K)).2
          simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled
        linarith
    have hderiv_small :
        ∀ z ∈ I.carrier,
          |f.firstDeriv z - k.firstDeriv z| <
            (3 * K)⁻¹ * c2Distance f k := by
      rcases hderiv_dich with hsmall_deriv | hlarge_deriv
      · exact hsmall_deriv
      · exfalso
        have hlower := hlarge_deriv x₀ hx₀I
        have hstrict :
            Delta < (6 * K)⁻¹ * c2Distance f k := by
          have hscaled :
              6 * K * Delta < c2Distance f k := by
            nlinarith [hlarge, hKpos, hDeltapos]
          rw [inv_mul_eq_div]
          apply (lt_div_iff₀ (by positivity : 0 < 6 * K)).2
          simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled
        linarith
    have hsecond_lower :
        ∀ z ∈ I.carrier,
          c2Distance f k / (6 * K) ≤
            |f.secondDeriv z - k.secondDeriv z| := by
      intro z hz
      simpa [div_eq_mul_inv, mul_comm] using
        hsecond_dich ⟨hvalue_small, hderiv_small⟩ z hz
    let H : ℝ → ℝ := f.extension - k.extension
    have hHc2 : ContDiff ℝ 2 H :=
      f.extension_contDiff.sub k.extension_contDiff
    have hf_diff : Differentiable ℝ f.extension :=
      f.extension_contDiff.differentiable (by norm_num)
    have hk_diff : Differentiable ℝ k.extension :=
      k.extension_contDiff.differentiable (by norm_num)
    have hf'_diff : Differentiable ℝ (deriv f.extension) :=
      f.extension_contDiff.differentiable_deriv_two
    have hk'_diff : Differentiable ℝ (deriv k.extension) :=
      k.extension_contDiff.differentiable_deriv_two
    have hHvalue (z : UnitPoint) :
        H z = f z - k z := by
      simp [H]
    have hHderiv (z : UnitPoint) :
        deriv H z = f.firstDeriv z - k.firstDeriv z := by
      rw [show H = f.extension - k.extension by rfl]
      rw [deriv_sub hf_diff.differentiableAt hk_diff.differentiableAt]
      simp
    have hHsecond (z : UnitPoint) :
        deriv (deriv H) z = f.secondDeriv z - k.secondDeriv z := by
      have hderiv :
          deriv H = deriv f.extension - deriv k.extension := by
        funext w
        rw [show H = f.extension - k.extension by rfl]
        exact deriv_sub hf_diff.differentiableAt hk_diff.differentiableAt
      rw [hderiv]
      rw [deriv_sub hf'_diff.differentiableAt hk'_diff.differentiableAt]
      simp
    have hH_x₀ : |H x₀| ≤ Delta := by
      rw [hHvalue x₀]
      exact hx₀value
    have hH'_x₀ : |deriv H x₀| ≤ Delta := by
      rw [hHderiv x₀]
      exact hx₀deriv
    have hH_y : |H y| ≤ 4 * delta := by
      rw [hHvalue y]
      exact hyclose
    set u : ℝ := |(y : ℝ) - (x₀ : ℝ)| with hu
    have hu_clean :
        u ≤ Real.sqrt (120 * K * Delta / c2Distance f k) := by
      simpa [u] using
        parameter_distance_bound_of_second_deriv hKpos hdelta
          hdelta_Delta hDeltapos hdpos hHc2 hx₀I hyI hH_x₀ hH'_x₀
          hH_y (fun z hz => by
            rw [hHsecond z]
            exact hsecond_lower z hz) hlarge
    have hlip := lipschitz_deriv f k y x₀
    have hvariation :
        |(f.firstDeriv y - k.firstDeriv y) -
            (f.firstDeriv x₀ - k.firstDeriv x₀)| ≤
          Real.sqrt (120 * K * c2Distance f k * Delta) := by
      calc
        |(f.firstDeriv y - k.firstDeriv y) -
            (f.firstDeriv x₀ - k.firstDeriv x₀)|
            ≤ c2Distance f k * u := by simpa [u] using hlip
        _ ≤ c2Distance f k *
            Real.sqrt (120 * K * Delta / c2Distance f k) := by
              gcongr
        _ = Real.sqrt (120 * K * c2Distance f k * Delta) := by
          have hdnonneg : 0 ≤ c2Distance f k := dist_nonneg
          have hinside_nonneg :
              0 ≤ 120 * K * Delta / c2Distance f k := by positivity
          have hsq :
              (c2Distance f k *
                Real.sqrt (120 * K * Delta / c2Distance f k)) ^ 2 =
                (Real.sqrt
                  (120 * K * c2Distance f k * Delta)) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hinside_nonneg]
            rw [Real.sq_sqrt (by positivity :
              0 ≤ 120 * K * c2Distance f k * Delta)]
            field_simp [hdpos.ne']
            <;> ring
          have hleft_nonneg :
              0 ≤ c2Distance f k *
                Real.sqrt (120 * K * Delta / c2Distance f k) := by
            positivity
          nlinarith [hleft_nonneg, Real.sqrt_nonneg
            (120 * K * c2Distance f k * Delta)]
    have htriangle :
        |f.firstDeriv y - k.firstDeriv y| ≤
          |f.firstDeriv x₀ - k.firstDeriv x₀| +
            |(f.firstDeriv y - k.firstDeriv y) -
              (f.firstDeriv x₀ - k.firstDeriv x₀)| := by
      calc
        |f.firstDeriv y - k.firstDeriv y| =
            |(f.firstDeriv x₀ - k.firstDeriv x₀) +
              ((f.firstDeriv y - k.firstDeriv y) -
                (f.firstDeriv x₀ - k.firstDeriv x₀))| := by
                  congr 1
                  ring
        _ ≤ _ := abs_add_le _ _
    have hsqrt_variation :
        Real.sqrt (120 * K * c2Distance f k * Delta) ≤
          Real.sqrt (720 * K * t * Delta) := by
      apply Real.sqrt_le_sqrt
      calc
        120 * K * c2Distance f k * Delta
            ≤ 120 * K * (6 * t) * Delta := by
              gcongr
        _ = 720 * K * t * Delta := by ring
    have hsqrt_constant :
        Real.sqrt (720 * K * t * Delta) ≤
          27 * K * Real.sqrt (t * Delta) := by
      have hleft_nonneg :
          0 ≤ Real.sqrt (720 * K * t * Delta) := Real.sqrt_nonneg _
      have hright_nonneg :
          0 ≤ 27 * K * Real.sqrt (t * Delta) := by positivity
      have hsquares :
          (Real.sqrt (720 * K * t * Delta)) ^ 2 ≤
            (27 * K * Real.sqrt (t * Delta)) ^ 2 := by
        calc
          (Real.sqrt (720 * K * t * Delta)) ^ 2 =
              720 * K * (t * Delta) := by
                rw [Real.sq_sqrt (by positivity :
                  0 ≤ 720 * K * t * Delta)]
                ring
          _ ≤ 720 * K ^ 2 * (t * Delta) := by
            gcongr
            nlinarith
          _ ≤ 729 * K ^ 2 * (t * Delta) := by
            gcongr
            norm_num
          _ = (27 * K * Real.sqrt (t * Delta)) ^ 2 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt htDeltapos.le]
            ring
      nlinarith
    calc
      |f.firstDeriv y - k.firstDeriv y|
          ≤ |f.firstDeriv x₀ - k.firstDeriv x₀| +
              |(f.firstDeriv y - k.firstDeriv y) -
                (f.firstDeriv x₀ - k.firstDeriv x₀)| := htriangle
      _ ≤ Delta + Real.sqrt (120 * K * c2Distance f k * Delta) := by
        gcongr
      _ ≤ Real.sqrt (t * Delta) +
          Real.sqrt (720 * K * t * Delta) := by
        gcongr
      _ ≤ Real.sqrt (t * Delta) +
          27 * K * Real.sqrt (t * Delta) := by
        gcongr
      _ ≤ 28 * K * Real.sqrt (t * Delta) :=
        sqrt_linear_absorption hK htDeltapos

theorem fine_tangency_lifts_to_coarse :
    FineTangencyLiftToCoarseStatement := by
  unfold FineTangencyLiftToCoarseStatement
  intro K D delta t Delta C_R hK hD hdelta hdelta_Delta hDelta_t ht
    hCR hCRlarge family hfamily I hI R S hRquarter hSfunction
    hSmidpoint hcontain f k hRfunction hk hf hfk_dist hfk_parameter
    hRtangent
  have hKpos : 0 < K := by linarith
  have hDeltapos : 0 < Delta := by linarith
  have hCRtpos : 0 < C_R * t := mul_pos hCR ht
  have hproductpos : 0 < C_R * t * Delta := by positivity
  have hsqrtCRpos : 0 < Real.sqrt C_R := Real.sqrt_pos.mpr hCR
  have hsqrt_tDeltapos : 0 < Real.sqrt (t * Delta) := by positivity
  have hsqrt_product :
      Real.sqrt (C_R * t * Delta) =
        Real.sqrt C_R * Real.sqrt (t * Delta) := by
    rw [show C_R * t * Delta = C_R * (t * Delta) by ring]
    exact Real.sqrt_mul hCR.le _
  have hsqrtCRlarge : 96 * K ≤ Real.sqrt C_R := by
    have hsquare : (96 * K) ^ 2 ≤ C_R := by
      nlinarith
    exact Real.le_sqrt_of_sq_le hsquare
  have hRlength :
      R.interval.length =
        delta / Real.sqrt (C_R * t * Delta) := by
    rw [R.interval_length]
    have hratio :
        delta / (C_R * t * Delta / delta) =
          delta ^ 2 / (C_R * t * Delta) := by
      field_simp [hdelta.ne']
      <;> ring
    rw [hratio, Real.sqrt_div (by positivity)]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hdelta]
  have hSlength :
      S.interval.length =
        Delta / Real.sqrt (C_R * t * Delta) := by
    rw [S.interval_length]
    have hratio :
        Delta / (C_R * t) =
          Delta ^ 2 / (C_R * t * Delta) := by
      field_simp [hCR.ne', ht.ne', hDeltapos.ne']
      <;> ring
    rw [hratio, Real.sqrt_div (by positivity)]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hDeltapos]
  intro p hpS
  have hpvalue : |p.2 - S.function p.1| ≤ Delta := hpS.2
  have hSk : S.function = k := hSfunction.trans hRfunction
  by_cases hpRinterval : p.1 ∈ R.interval.carrier
  · have hgraph :=
      tangency_implies_value_close hdelta R f (by norm_num) hRtangent
        p.1 hpRinterval
    norm_num at hgraph
    have hgraph' : |k p.1 - f p.1| ≤ 4 * delta := by
      simpa [hRfunction, abs_sub_comm] using hgraph
    calc
      |p.2 - f p.1|
          ≤ |p.2 - k p.1| + |k p.1 - f p.1| := abs_sub_le _ _ _
      _ ≤ Delta + 4 * delta := by
        gcongr
        simpa [hSk] using hpvalue
      _ ≤ 5 * Delta := by linarith
  · have hpoutside :
        (p.1 : ℝ) < R.interval.left ∨
          R.interval.right < (p.1 : ℝ) := by
      have hpnot :
          ¬(R.interval.left ≤ (p.1 : ℝ) ∧
            (p.1 : ℝ) ≤ R.interval.right) := by
        simpa [ParameterInterval.carrier] using hpRinterval
      by_cases hleft : (p.1 : ℝ) < R.interval.left
      · exact Or.inl hleft
      · right
        have hleftle : R.interval.left ≤ (p.1 : ℝ) :=
          le_of_not_gt hleft
        have hnotright : ¬(p.1 : ℝ) ≤ R.interval.right :=
          fun hright => hpnot ⟨hleftle, hright⟩
        exact lt_of_not_ge hnotright
    rcases hpoutside with hleft | hright
    · let y : UnitPoint :=
        ⟨R.interval.left, R.interval.left_mem⟩
      have hyR : y ∈ R.interval.carrier :=
        ⟨le_rfl, R.interval.left_le_right⟩
      have hygraph : |f y - k y| ≤ 4 * delta := by
        have hgraph :=
          tangency_implies_value_close hdelta R f (by norm_num)
            hRtangent y hyR
        norm_num at hgraph
        simpa [hRfunction] using hgraph
      have hyderiv :
          |f.firstDeriv y - k.firstDeriv y| ≤
            28 * K * Real.sqrt (t * Delta) :=
        fine_tangency_derivative_bound hK hD hdelta hdelta_Delta
          hDelta_t ht hfamily hI hRquarter hRfunction hk hf hfk_dist
          hfk_parameter hRtangent hyR
      have hdistance :
          |(p.1 : ℝ) - (y : ℝ)| ≤
            (Delta - delta) /
              (2 * Real.sqrt (C_R * t * Delta)) := by
        have hpSleft : S.interval.left ≤ (p.1 : ℝ) := hpS.1.1
        have hleft_relation :
            R.interval.left - S.interval.left =
              (Delta - delta) /
                (2 * Real.sqrt (C_R * t * Delta)) := by
          have hmid : S.interval.midpoint = R.interval.midpoint :=
            hSmidpoint
          simp only [ParameterInterval.midpoint,
            ParameterInterval.length] at hmid hRlength hSlength
          field_simp [hproductpos.ne']
            at hRlength hSlength ⊢
          nlinarith
        have hnonpos : (p.1 : ℝ) - (y : ℝ) ≤ 0 := by
          dsimp only [y]
          linarith
        rw [abs_of_nonpos hnonpos]
        dsimp only [y]
        linarith
      have hgraph_extension :
          |f p.1 - k p.1| ≤ 4 * Delta :=
        graph_difference_bound_from_nearby_tangent_point hK hdelta
          hdelta_Delta ht hCR hCRlarge hygraph hyderiv hdistance hfk_dist
      calc
        |p.2 - f p.1|
            ≤ |p.2 - k p.1| + |k p.1 - f p.1| :=
          abs_sub_le _ _ _
        _ ≤ Delta + 4 * Delta := by
          gcongr
          · simpa [hSk] using hpvalue
          · simpa [abs_sub_comm] using hgraph_extension
        _ = 5 * Delta := by ring
    · let y : UnitPoint :=
        ⟨R.interval.right, R.interval.right_mem⟩
      have hyR : y ∈ R.interval.carrier :=
        ⟨R.interval.left_le_right, le_rfl⟩
      have hygraph : |f y - k y| ≤ 4 * delta := by
        have hgraph :=
          tangency_implies_value_close hdelta R f (by norm_num)
            hRtangent y hyR
        norm_num at hgraph
        simpa [hRfunction] using hgraph
      have hyderiv :
          |f.firstDeriv y - k.firstDeriv y| ≤
            28 * K * Real.sqrt (t * Delta) :=
        fine_tangency_derivative_bound hK hD hdelta hdelta_Delta
          hDelta_t ht hfamily hI hRquarter hRfunction hk hf hfk_dist
          hfk_parameter hRtangent hyR
      have hdistance :
          |(p.1 : ℝ) - (y : ℝ)| ≤
            (Delta - delta) /
              (2 * Real.sqrt (C_R * t * Delta)) := by
        have hpSright : (p.1 : ℝ) ≤ S.interval.right := hpS.1.2
        have hright_relation :
            S.interval.right - R.interval.right =
              (Delta - delta) /
                (2 * Real.sqrt (C_R * t * Delta)) := by
          have hmid : S.interval.midpoint = R.interval.midpoint :=
            hSmidpoint
          simp only [ParameterInterval.midpoint,
            ParameterInterval.length] at hmid hRlength hSlength
          field_simp [hproductpos.ne']
            at hRlength hSlength ⊢
          nlinarith
        have hnonneg : 0 ≤ (p.1 : ℝ) - (y : ℝ) := by
          dsimp only [y]
          linarith
        rw [abs_of_nonneg hnonneg]
        dsimp only [y]
        linarith
      have hgraph_extension :
          |f p.1 - k p.1| ≤ 4 * Delta :=
        graph_difference_bound_from_nearby_tangent_point hK hdelta
          hdelta_Delta ht hCR hCRlarge hygraph hyderiv hdistance hfk_dist
      calc
        |p.2 - f p.1|
            ≤ |p.2 - k p.1| + |k p.1 - f p.1| :=
          abs_sub_le _ _ _
        _ ≤ Delta + 4 * Delta := by
          gcongr
          · simpa [hSk] using hpvalue
          · simpa [abs_sub_comm] using hgraph_extension
        _ = 5 * Delta := by ring

end Kakeya.Cinematic
