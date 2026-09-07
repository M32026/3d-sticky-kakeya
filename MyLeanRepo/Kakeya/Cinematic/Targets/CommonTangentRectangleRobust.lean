import MyLeanRepo.Kakeya.Cinematic.Targets.TangencySublevelDiameter.Helpers
import MyLeanRepo.Kakeya.Cinematic.Targets.CommonTangentRectangleHelpers
import MyLeanRepo.Kakeya.Cinematic.Targets.CommonTangentRectangleRobustHelpers
import MyLeanRepo.Kakeya.Cinematic.Targets.CommonTangentRectangleRobustMain
import MyLeanRepo.Kakeya.Cinematic.Statements

/-!
# PYZ Lemma 17: robust common-tangent rectangle (polynomial in tangency)

Direct generalization of `common_tangent_rectangle_controls_parameter` to an
arbitrary tangency constant.  The value-gap bound is `M := 2 * tangency`.
-/

namespace Kakeya.Cinematic

private lemma common_tangent_small_distance_bound
    {K tangency delta t d Δ : ℝ}
    (hK : 1 ≤ K)
    (h_tangency : 1 ≤ tangency)
    (hdelta : 0 < delta)
    (ht : 0 < t)
    (hd : 0 < d)
    (hΔ_le_2d : Δ ≤ 2 * d)
    (hsq : 2 * d^2 ≤ 259200 * K^2 * tangency^2 * delta * t)
    (hlinear : delta * d ≤ 15 * tangency * delta * t) :
    (Δ + delta) * d ≤ 270000 * K^2 * tangency^2 * delta * t := by
  have hKsq : 1 ≤ K^2 := by nlinarith
  have htan_nonneg : 0 ≤ tangency := le_trans zero_le_one h_tangency
  have htan_sq : tangency ≤ tangency^2 := by nlinarith
  have htan_scale : tangency ≤ K^2 * tangency^2 := by
    calc
      tangency ≤ tangency^2 := htan_sq
      _ = 1 * tangency^2 := by ring
      _ ≤ K^2 * tangency^2 :=
        mul_le_mul_of_nonneg_right hKsq (sq_nonneg tangency)
  have hdelta_t : 0 ≤ delta * t := mul_nonneg hdelta.le ht.le
  have hlinear' : delta * d ≤ 15 * K^2 * tangency^2 * delta * t := by
    calc
      delta * d ≤ 15 * tangency * delta * t := hlinear
      _ = (15 * tangency) * (delta * t) := by ring
      _ ≤ (15 * (K^2 * tangency^2)) * (delta * t) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htan_scale (by norm_num)) hdelta_t
      _ = 15 * K^2 * tangency^2 * delta * t := by ring
  have hleft : (Δ + delta) * d ≤ (2 * d + delta) * d :=
    mul_le_mul_of_nonneg_right
      (by simpa [add_comm] using add_le_add_right hΔ_le_2d delta) hd.le
  let scale : ℝ := K^2 * tangency^2 * delta * t
  have hscale : 0 ≤ scale := by
    dsimp only [scale]
    positivity
  calc
    (Δ + delta) * d ≤ (2 * d + delta) * d := hleft
    _ = 2 * d^2 + delta * d := by ring
    _ ≤ 259200 * K^2 * tangency^2 * delta * t
        + 15 * K^2 * tangency^2 * delta * t := add_le_add hsq hlinear'
    _ = 259215 * scale := by simp only [scale]; ring
    _ ≤ 270000 * scale :=
      mul_le_mul_of_nonneg_right (by norm_num) hscale
    _ = 270000 * K^2 * tangency^2 * delta * t := by simp only [scale]; ring

private lemma common_tangent_rpow_bound
    {K tangency delta t C : ℝ}
    (h_tangency : 1 ≤ tangency)
    (hdelta : 0 < delta)
    (ht : 0 < t)
    (hC_ge2 : 2 ≤ C)
    (hC_coeff : 270000 * K^2 ≤ C) :
    270000 * K^2 * tangency^2 * delta * t
      ≤ C * Real.rpow tangency C * delta * t := by
  have hrpow : tangency^2 ≤ Real.rpow tangency C := by
    have hpow :
        Real.rpow tangency (2 : ℝ) ≤ Real.rpow tangency C :=
      Real.rpow_le_rpow_of_exponent_le h_tangency hC_ge2
    calc
      tangency^2 = Real.rpow tangency (2 : ℝ) :=
        (Real.rpow_two tangency).symm
      _ ≤ Real.rpow tangency C := hpow
  have hC_nonneg : 0 ≤ C := le_trans (by norm_num) hC_ge2
  have hcoeff :
      270000 * K^2 * tangency^2 ≤ C * Real.rpow tangency C := by
    calc
      270000 * K^2 * tangency^2 ≤ C * tangency^2 :=
        mul_le_mul_of_nonneg_right hC_coeff (sq_nonneg tangency)
      _ ≤ C * Real.rpow tangency C :=
        mul_le_mul_of_nonneg_left hrpow hC_nonneg
  have hdelta_t : 0 ≤ delta * t := mul_nonneg hdelta.le ht.le
  calc
    270000 * K^2 * tangency^2 * delta * t
        = (270000 * K^2 * tangency^2) * (delta * t) := by ring
    _ ≤ (C * Real.rpow tangency C) * (delta * t) :=
      mul_le_mul_of_nonneg_right hcoeff hdelta_t
    _ = C * Real.rpow tangency C * delta * t := by ring

private lemma common_tangent_general_rpow_bound
    {K tangency delta t C M : ℝ}
    (h_tangency : 1 ≤ tangency)
    (hdelta : 0 < delta)
    (ht : 0 < t)
    (hC_ge2 : 2 ≤ C)
    (hC_coeff : 270000 * K^2 ≤ C)
    (hM_eq : M = 2 * tangency) :
    2700 * K^2 * M^2 * delta * t
      ≤ C * Real.rpow tangency C * delta * t := by
  have hscale : 0 ≤ K^2 * tangency^2 * delta * t := by positivity
  have hcoefficient :
      10800 * (K^2 * tangency^2 * delta * t)
        ≤ 270000 * (K^2 * tangency^2 * delta * t) :=
    mul_le_mul_of_nonneg_right (by norm_num) hscale
  calc
    2700 * K^2 * M^2 * delta * t
        = 10800 * (K^2 * tangency^2 * delta * t) := by
          rw [hM_eq]
          ring
    _ ≤ 270000 * (K^2 * tangency^2 * delta * t) := hcoefficient
    _ = 270000 * K^2 * tangency^2 * delta * t := by ring
    _ ≤ C * Real.rpow tangency C * delta * t :=
      common_tangent_rpow_bound h_tangency hdelta ht hC_ge2 hC_coeff

private lemma large_distance_forces_parameter_bound
    {K tangency delta t d Δ M L a b : ℝ}
    {H : ℝ → ℝ}
    (hK : 1 ≤ K)
    (h_tangency : 1 ≤ tangency)
    (hdelta : 0 < delta)
    (hdelta_t : delta ≤ t)
    (ht : t ≤ 1)
    (hM_eq : M = 2 * tangency)
    (hL_eq : L = Real.sqrt (delta / t))
    (hL_pos : 0 < L)
    (h_ab_L : b - a = L)
    (h_ab_lt : a < b)
    (hlarge : 360 * K * tangency * Real.sqrt (delta * t) < d)
    (hH_diff : Differentiable ℝ H)
    (hderiv_gap :
      ∀ x ∈ Set.Icc a b, Δ - M * delta ≤ |deriv H x|)
    (hvariation : |H b - H a| ≤ 2 * M * delta) :
    Δ ≤ d / (12 * K) := by
  have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have ht_pos : 0 < t := lt_of_lt_of_le hdelta hdelta_t
  have h_tangency_pos : 0 < tangency :=
    lt_of_lt_of_le zero_lt_one h_tangency
  have h_sqrt_ge_delta : delta ≤ Real.sqrt (delta * t) := by
    have hsquare : delta^2 ≤ delta * t := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left hdelta_t hdelta.le
    have hsqrt :
        Real.sqrt (delta^2) ≤ Real.sqrt (delta * t) :=
      Real.sqrt_le_sqrt hsquare
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hdelta] at hsqrt
    exact hsqrt
  have hMdelta_lt : M * delta < d / (12 * K) := by
    have h360 :
        360 * K * tangency * delta
          ≤ 360 * K * tangency * Real.sqrt (delta * t) := by
      gcongr
    have h30 : 30 * tangency * delta < d / (12 * K) := by
      calc
        30 * tangency * delta
            = (360 * K * tangency * delta) / (12 * K) := by
              field_simp [hK_pos.ne']
              <;> ring
        _ ≤ (360 * K * tangency * Real.sqrt (delta * t)) / (12 * K) := by
          gcongr
        _ < d / (12 * K) := by gcongr
    rw [hM_eq]
    have h2_lt_30 : 2 * tangency * delta < 30 * tangency * delta := by
      exact mul_lt_mul_of_pos_right (by nlinarith) hdelta
    exact lt_trans h2_lt_30 h30
  by_contra hnot
  have hDelta : d / (12 * K) < Δ := lt_of_not_ge hnot
  have hgap_pos : 0 < Δ - M * delta := by
    linarith
  rcases exists_hasDerivAt_eq_slope (f := H) (f' := deriv H)
      h_ab_lt hH_diff.continuous.continuousOn
      (fun z _ => hH_diff.differentiableAt.hasDerivAt) with
    ⟨c, hc, hc_slope⟩
  have hc_mem : c ∈ Set.Icc a b := ⟨hc.1.le, hc.2.le⟩
  have hc_gap : Δ - M * delta ≤ |deriv H c| :=
    hderiv_gap c hc_mem
  have hba_ne : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt h_ab_lt)
  have hchange : H b - H a = deriv H c * (b - a) := by
    calc
      H b - H a = ((H b - H a) / (b - a)) * (b - a) := by
        field_simp [hba_ne]
      _ = deriv H c * (b - a) := by rw [hc_slope]
  have habs_change :
      |H b - H a| = |deriv H c| * L := by
    rw [hchange, abs_mul, h_ab_L, abs_of_pos hL_pos]
  have hgap_variation :
      (Δ - M * delta) * L ≤ |H b - H a| := by
    rw [habs_change]
    exact mul_le_mul_of_nonneg_right hc_gap hL_pos.le
  have hproduct :
      (Δ - M * delta) * L ≤ 2 * M * delta :=
    le_trans hgap_variation hvariation
  have hgap_div :
      Δ - M * delta ≤ 2 * M * delta / L := by
    calc
      Δ - M * delta = ((Δ - M * delta) * L) / L := by
        field_simp [hL_pos.ne']
      _ ≤ (2 * M * delta) / L := by gcongr
  have hsqrt_product :
      Real.sqrt (delta / t) * Real.sqrt (delta * t) = delta := by
    have hproduct_eq : (delta / t) * (delta * t) = delta^2 := by
      field_simp [ht_pos.ne']
      <;> ring
    calc
      Real.sqrt (delta / t) * Real.sqrt (delta * t)
          = Real.sqrt ((delta / t) * (delta * t)) := by
            rw [← Real.sqrt_mul (by positivity)]
      _ = Real.sqrt (delta^2) := by rw [hproduct_eq]
      _ = delta := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hdelta]
  have hquotient :
      2 * M * delta / L = 2 * M * Real.sqrt (delta * t) := by
    rw [hL_eq]
    have hsqrt_pos : 0 < Real.sqrt (delta / t) :=
      Real.sqrt_pos.mpr (by positivity)
    calc
      2 * M * delta / Real.sqrt (delta / t)
          = 2 * M *
              (Real.sqrt (delta / t) * Real.sqrt (delta * t)) /
                Real.sqrt (delta / t) := by rw [hsqrt_product]
      _ = 2 * M * Real.sqrt (delta * t) := by
        field_simp [hsqrt_pos.ne']
        <;> ring
  have hM_pos : 0 < M := by rw [hM_eq]; positivity
  have hMdelta_sqrt :
      M * delta ≤ M * Real.sqrt (delta * t) :=
    mul_le_mul_of_nonneg_left h_sqrt_ge_delta hM_pos.le
  have hDelta_sqrt :
      Δ ≤ 3 * M * Real.sqrt (delta * t) := by
    rw [hquotient] at hgap_div
    linarith
  have hd_lt_72 :
      d < 72 * K * tangency * Real.sqrt (delta * t) := by
    have hdiv :
        d / (12 * K) < 6 * tangency * Real.sqrt (delta * t) := by
      rw [hM_eq] at hDelta_sqrt
      linarith
    calc
      d = (d / (12 * K)) * (12 * K) := by
        field_simp [hK_pos.ne']
        <;> ring
      _ < (6 * tangency * Real.sqrt (delta * t)) * (12 * K) := by
        gcongr
      _ = 72 * K * tangency * Real.sqrt (delta * t) := by ring
  have hscale_nonneg :
      0 ≤ K * tangency * Real.sqrt (delta * t) := by positivity
  have h72_le_360 :
      72 * K * tangency * Real.sqrt (delta * t)
        ≤ 360 * K * tangency * Real.sqrt (delta * t) := by
    calc
      72 * K * tangency * Real.sqrt (delta * t)
          = 72 * (K * tangency * Real.sqrt (delta * t)) := by ring
      _ ≤ 360 * (K * tangency * Real.sqrt (delta * t)) :=
        mul_le_mul_of_nonneg_right (by norm_num) hscale_nonneg
      _ = 360 * K * tangency * Real.sqrt (delta * t) := by ring
  exact (not_lt_of_ge (le_trans h72_le_360 hlarge.le)) hd_lt_72

private lemma central_quarter_endpoint_bounds
    {delta t : ℝ}
    (R : CurvilinearRectangle delta t)
    (I : ParameterInterval)
    (hcentral : R.IsOverCentralQuarterOf I) :
    |R.interval.left - I.midpoint| ≤ I.length / 8 ∧
      |R.interval.right - I.midpoint| ≤ I.length / 8 := by
  let leftPoint : UnitPoint :=
    ⟨R.interval.left, R.interval.left_mem⟩
  let rightPoint : UnitPoint :=
    ⟨R.interval.right, R.interval.right_mem⟩
  have hleft_mem : leftPoint ∈ R.interval.carrier := by
    exact ⟨by simp [leftPoint], R.interval.left_le_right⟩
  have hright_mem : rightPoint ∈ R.interval.carrier := by
    exact ⟨R.interval.left_le_right, by simp [rightPoint]⟩
  have hleft := hcentral hleft_mem
  have hright := hcentral hright_mem
  constructor
  · change |(leftPoint : ℝ) - I.midpoint| ≤
      (1 / 4 : ℝ) * I.length / 2 at hleft
    have hvalue : (leftPoint : ℝ) = R.interval.left := rfl
    have hscale : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
    rw [hvalue, hscale] at hleft
    exact hleft
  · change |(rightPoint : ℝ) - I.midpoint| ≤
      (1 / 4 : ℝ) * I.length / 2 at hright
    have hvalue : (rightPoint : ℝ) = R.interval.right := rfl
    have hscale : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
    rw [hvalue, hscale] at hright
    exact hright

private lemma central_subinterval_geometry
    {K a b : ℝ}
    (I : ParameterInterval)
    (hK : 1 ≤ K)
    (hI_long : 1 / (12 * K) ≤ I.length)
    (hI_short : I.length ≤ 1 / (6 * K))
    (ha_center : |a - I.midpoint| ≤ I.length / 8)
    (hb_center : |b - I.midpoint| ≤ I.length / 8)
    (ha_le_one : a ≤ 1) :
    let aJ := I.midpoint - I.length / 4
    let bJ := I.midpoint + I.length / 4
    aJ ∈ Set.Icc I.left I.right ∧
      bJ ∈ Set.Icc I.left I.right ∧
      Set.Icc aJ bJ ⊆ Set.Icc I.left I.right ∧
      Set.Icc a b ⊆ Set.Icc aJ bJ ∧
      1 / (96 * K) ≤ a - aJ ∧
      a - aJ ≤ 1 ∧
      1 / (96 * K) ≤ bJ - b ∧
      bJ - b ≤ 1 / (16 * K) := by
  dsimp only
  have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have haJ_mem :
      I.midpoint - I.length / 4 ∈ Set.Icc I.left I.right := by
    dsimp only [ParameterInterval.midpoint, ParameterInterval.length]
    constructor <;> linarith [I.left_le_right]
  have hbJ_mem :
      I.midpoint + I.length / 4 ∈ Set.Icc I.left I.right := by
    dsimp only [ParameterInterval.midpoint, ParameterInterval.length]
    constructor <;> linarith [I.left_le_right]
  have hleft_gap_base :
      I.length / 8 ≤ a - (I.midpoint - I.length / 4) := by
    have hcenter_lower :
        -(I.length / 8) ≤ a - I.midpoint := (abs_le.mp ha_center).1
    linarith
  have hright_gap_base :
      I.length / 8 ≤ I.midpoint + I.length / 4 - b := by
    have hcenter_upper :
        b - I.midpoint ≤ I.length / 8 := (abs_le.mp hb_center).2
    linarith
  have hleft_gap :
      1 / (96 * K) ≤ a - (I.midpoint - I.length / 4) := by
    calc
      1 / (96 * K) = (1 / (12 * K)) / 8 := by
        field_simp [hK_pos.ne']
        <;> ring
      _ ≤ I.length / 8 := by gcongr
      _ ≤ a - (I.midpoint - I.length / 4) := hleft_gap_base
  have hright_gap :
      1 / (96 * K) ≤ I.midpoint + I.length / 4 - b := by
    calc
      1 / (96 * K) = (1 / (12 * K)) / 8 := by
        field_simp [hK_pos.ne']
        <;> ring
      _ ≤ I.length / 8 := by gcongr
      _ ≤ I.midpoint + I.length / 4 - b := hright_gap_base
  have hleft_gap_upper :
      a - (I.midpoint - I.length / 4) ≤ 1 := by
    have haJ_nonneg : 0 ≤ I.midpoint - I.length / 4 :=
      le_trans I.left_mem.1 haJ_mem.1
    linarith
  have hright_gap_upper :
      I.midpoint + I.length / 4 - b ≤ 1 / (16 * K) := by
    have hcenter_lower :
        -(I.length / 8) ≤ b - I.midpoint := (abs_le.mp hb_center).1
    have hbase :
        I.midpoint + I.length / 4 - b ≤ 3 * I.length / 8 := by
      linarith
    calc
      I.midpoint + I.length / 4 - b ≤ 3 * I.length / 8 := hbase
      _ ≤ 3 * (1 / (6 * K)) / 8 := by gcongr
      _ = 1 / (16 * K) := by
        field_simp [hK_pos.ne']
        <;> ring
  have hJ_sub :
      Set.Icc (I.midpoint - I.length / 4)
          (I.midpoint + I.length / 4) ⊆
        Set.Icc I.left I.right := by
    intro x hx
    exact ⟨haJ_mem.1.trans hx.1, hx.2.trans hbJ_mem.2⟩
  have hR_sub :
      Set.Icc a b ⊆
        Set.Icc (I.midpoint - I.length / 4)
          (I.midpoint + I.length / 4) := by
    intro x hx
    have haJ_le_a :
        I.midpoint - I.length / 4 ≤ a := by
      have hpositive : 0 < 1 / (96 * K) := by positivity
      linarith
    have hb_le_bJ :
        b ≤ I.midpoint + I.length / 4 := by
      have hpositive : 0 < 1 / (96 * K) := by positivity
      linarith
    exact ⟨haJ_le_a.trans hx.1, hx.2.trans hb_le_bJ⟩
  exact ⟨haJ_mem, hbJ_mem, hJ_sub, hR_sub, hleft_gap,
    hleft_gap_upper, hright_gap, hright_gap_upper⟩

private lemma extension_sub_eq_value
    (f g : C2Function) (x : UnitPoint) :
    (f.extension - g.extension) (x : ℝ) = f x - g x := by
  change f.extension (x : ℝ) - g.extension (x : ℝ) = f x - g x
  rw [C2Function.extension_eq_value f x,
    C2Function.extension_eq_value g x]

private lemma deriv_extension_sub_eq_firstDeriv
    (f g : C2Function) (x : UnitPoint) :
    deriv (f.extension - g.extension) (x : ℝ) =
      f.firstDeriv x - g.firstDeriv x := by
  have hf_diff : Differentiable ℝ f.extension :=
    f.extension_contDiff.differentiable (by norm_num)
  have hg_diff : Differentiable ℝ g.extension :=
    g.extension_contDiff.differentiable (by norm_num)
  rw [deriv_sub (hf_diff (x : ℝ)) (hg_diff (x : ℝ))]
  rw [C2Function.deriv_extension_eq_firstDeriv f x,
    C2Function.deriv_extension_eq_firstDeriv g x]

private lemma extension_sub_bound_on_rectangle_interval
    {delta t M : ℝ}
    (R : CurvilinearRectangle delta t)
    (f g : C2Function)
    (hbound :
      ∀ x : UnitPoint, x ∈ R.interval.carrier →
        |f x - g x| ≤ M * delta) :
    ∀ x ∈ Set.Icc R.interval.left R.interval.right,
      |(f.extension - g.extension) x| ≤ M * delta := by
  intro x hx
  have hx_nonneg : 0 ≤ x := R.interval.left_mem.1.trans hx.1
  have hx_le_one : x ≤ 1 := hx.2.trans R.interval.right_mem.2
  let point : UnitPoint := ⟨x, ⟨hx_nonneg, hx_le_one⟩⟩
  have hpoint_mem : point ∈ R.interval.carrier := hx
  rw [show (f.extension - g.extension) x = f point - g point by
    exact extension_sub_eq_value f g point]
  exact hbound point hpoint_mem

private lemma extension_sub_tangency_lower_on_central_half
    (I : ParameterInterval)
    (f g : C2Function)
    (Δ : ℝ)
    (hpointwise :
      ∀ x : UnitPoint, x ∈ I.centeredCarrier (1 / 2) →
        Δ ≤ |f x - g x| + |f.firstDeriv x - g.firstDeriv x|) :
    ∀ x ∈
        Set.Icc (I.midpoint - I.length / 4)
          (I.midpoint + I.length / 4),
      Δ ≤ |(f.extension - g.extension) x| +
        |deriv (f.extension - g.extension) x| := by
  intro x hx
  rcases hx with ⟨hx_lower, hx_upper⟩
  have hx_left : I.left ≤ x := by
    dsimp only [ParameterInterval.midpoint, ParameterInterval.length] at hx_lower
    linarith [I.left_le_right]
  have hx_right : x ≤ I.right := by
    dsimp only [ParameterInterval.midpoint, ParameterInterval.length] at hx_upper
    linarith [I.left_le_right]
  have hx_nonneg : 0 ≤ x := I.left_mem.1.trans hx_left
  have hx_le_one : x ≤ 1 := hx_right.trans I.right_mem.2
  let point : UnitPoint := ⟨x, ⟨hx_nonneg, hx_le_one⟩⟩
  have hpoint_centered : point ∈ I.centeredCarrier (1 / 2) := by
    change |x - I.midpoint| ≤ (1 / 2 : ℝ) * I.length / 2
    have hcenter : |x - I.midpoint| ≤ I.length / 4 := by
      exact abs_le.mpr ⟨by linarith [hx_lower], by linarith [hx_upper]⟩
    convert hcenter using 1 <;> ring
  have hlower := hpointwise point hpoint_centered
  rw [extension_sub_eq_value f g point,
    deriv_extension_sub_eq_firstDeriv f g point]
  exact hlower

private lemma curvature_abs_lower_on_real_interval
    (I : ParameterInterval)
    (H : ℝ → ℝ)
    (f g : C2Function)
    {K d : ℝ}
    (hK : 0 < K)
    (hd : 0 < d)
    (hbridge :
      ∀ x : UnitPoint,
        deriv (deriv H) (x : ℝ) =
          f.secondDeriv x - g.secondDeriv x)
    (hlower :
      ∀ x : UnitPoint, x ∈ I.carrier →
        d / (2 * K) ≤
          |f.secondDeriv x - g.secondDeriv x|) :
    ∀ x ∈ Set.Icc I.left I.right,
      d / (2 * K) ≤ |deriv (deriv H) x| := by
  intro x hx
  have hx_nonneg : 0 ≤ x := I.left_mem.1.trans hx.1
  have hx_le_one : x ≤ 1 := hx.2.trans I.right_mem.2
  let point : UnitPoint := ⟨x, ⟨hx_nonneg, hx_le_one⟩⟩
  have hpoint_mem : point ∈ I.carrier := hx
  rw [hbridge point]
  exact hlower point hpoint_mem

theorem common_tangent_rectangle_robust :
    CommonTangentRectangleRobustStatement := by
  intro K D hK hD
  let C : ℝ := 270000 * K^2 + 2
  use C
  have hC_ge2 : 2 ≤ C := by
    have h1 : 0 ≤ K^2 := by positivity
    linarith
  have hC_coeff : 270000 * K^2 ≤ C := by
    dsimp only [C]
    linarith
  have hC_ge1 : 1 ≤ C := by linarith
  constructor
  · exact hC_ge1
  intro tangency h_tangency family hfam I hI delta t hδ hδt ht R hRfam hRcentral f hf g hg hfg hftan hgtan

  set d : ℝ := c2Distance f g with hd_def
  set Δ : ℝ := tangencyParameterOn I f g with hΔ_def
  set L : ℝ := R.interval.length with hL_def
  set M : ℝ := 2 * tangency with hM_def

  have hK_pos : 0 < K := by linarith
  have hδ_pos : 0 < delta := hδ
  have ht_pos : 0 < t := by linarith
  have h_tan_pos : 0 < tangency := by linarith
  have hM_ge1 : 1 ≤ M := by
    dsimp only [M]
    linarith

  have hd_pos : 0 < d := by
    have h : 0 < dist f g := dist_pos.mpr hfg
    simpa [hd_def, c2Distance_eq_dist] using h

  have hd_le_K : d ≤ K := hfam.1 hf hg
  have hL_eq : L = Real.sqrt (delta / t) := R.interval_length
  have hL_pos : 0 < L := by
    rw [hL_eq]; apply Real.sqrt_pos.mpr; positivity

  have hendpoint_center :=
    central_quarter_endpoint_bounds R I hRcentral
  have hleft_center :
      |R.interval.left - I.midpoint| ≤ I.length / 8 :=
    hendpoint_center.1
  have hright_center :
      |R.interval.right - I.midpoint| ≤ I.length / 8 :=
    hendpoint_center.2

  -- R.interval.length ≤ I.length / 4
  have hL_le_I4 : L ≤ I.length / 4 := by
    have h9 : L = R.interval.right - R.interval.left := by
      simp [hL_def, ParameterInterval.length]
    rw [h9]
    have h_left_ge : R.interval.left ≥ I.midpoint - I.length / 8 := by
      have h4 : -(I.length / 8) ≤ R.interval.left - I.midpoint :=
        (abs_le.mp hleft_center).1
      linarith
    have h_right_le : R.interval.right ≤ I.midpoint + I.length / 8 := by
      have h5 : R.interval.right - I.midpoint ≤ I.length / 8 :=
        (abs_le.mp hright_center).2
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

  -- |f x - g x| ≤ M*δ on R.interval
  have hfg_bound : ∀ (x : UnitPoint), x ∈ R.interval.carrier → |f x - g x| ≤ M * delta := by
    intro x hx
    let p : UnitPoint × ℝ := (x, R.function x)
    have hp_in_R : p ∈ R.carrier := by
      simp only [CurvilinearRectangle.carrier, Set.mem_setOf_eq]
      have h_abs : |R.function x - R.function x| ≤ delta := by
        have h : R.function x - R.function x = 0 := by simp
        rw [h]
        simpa using hδ_pos.le
      exact ⟨hx, h_abs⟩
    have h1 : |R.function x - f x| ≤ tangency * delta := hftan p hp_in_R
    have h2 : |R.function x - g x| ≤ tangency * delta := hgtan p hp_in_R
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
    have h5 : |f x - g x| ≤ tangency * delta + tangency * delta := by linarith
    have h6 : tangency * delta + tangency * delta = M * delta := by
      simp [hM_def] <;> ring
    rw [h6] at h5
    exact h5

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

  have hHa_bound : |H a| ≤ M * delta := by
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

  have hHb_bound : |H b| ≤ M * delta := by
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

  by_cases hCase1 : d ≤ 360 * K * tangency * Real.sqrt (delta * t)

  · -- Case 1: d small
    have h1 : 2 * d^2 ≤ 259200 * K^2 * tangency^2 * delta * t := by
      have h2 : d ≤ 360 * K * tangency * Real.sqrt (delta * t) := hCase1
      have h3 : 0 ≤ delta * t := by positivity
      have h4 : 0 ≤ d := by positivity
      have h5 : d^2 ≤ (360 * K * tangency * Real.sqrt (delta * t))^2 := by
        gcongr <;> linarith
      have h6 : (360 * K * tangency * Real.sqrt (delta * t))^2 = 129600 * K^2 * tangency^2 * (delta * t) := by
        calc (360 * K * tangency * Real.sqrt (delta * t))^2
          = 360^2 * K^2 * tangency^2 * (Real.sqrt (delta * t))^2 := by ring
        _ = 129600 * K^2 * tangency^2 * (delta * t) := by
          rw [Real.sq_sqrt h3] <;> ring
      rw [h6] at h5
      have h7 : 2 * d^2 ≤ 2 * (129600 * K^2 * tangency^2 * (delta * t)) := by gcongr
      have h8 : 2 * (129600 * K^2 * tangency^2 * (delta * t)) = 259200 * K^2 * tangency^2 * delta * t := by ring
      rw [h8] at h7
      exact h7
    have h_sqrt_le : Real.sqrt (delta / t) ≤ 1 / (24 * K) := by
      rw [hL_eq.symm] <;> exact hL_le
    have h5 : delta * d ≤ 15 * tangency * delta * t := by
      have h6 : d ≤ 360 * K * tangency * Real.sqrt (delta * t) := hCase1
      have h7 : Real.sqrt (delta * t) = Real.sqrt (delta / t) * t := by
        have h8 : 0 < t := ht_pos
        have h9 : delta * t = delta / t * t^2 := by field_simp [h8.ne'] <;> ring
        rw [h9]
        rw [Real.sqrt_mul (by positivity)]
        have h10 : Real.sqrt (t^2) = t := by
          rw [Real.sqrt_sq_eq_abs] <;> rw [abs_of_pos h8]
        rw [h10] <;> ring
      have h8 : delta * d ≤ 360 * K * tangency * Real.sqrt (delta / t) * (delta * t) := by
        calc
          delta * d ≤ delta * (360 * K * tangency * Real.sqrt (delta * t)) := by gcongr
          _ = 360 * K * tangency * delta * (Real.sqrt (delta / t) * t) := by rw [h7] <;> ring
          _ = 360 * K * tangency * Real.sqrt (delta / t) * (delta * t) := by ring
      have h10 : Real.sqrt (delta / t) ≤ 1 / (24 * K) := h_sqrt_le
      calc
        delta * d
        ≤ 360 * K * tangency * Real.sqrt (delta / t) * (delta * t) := h8
        _ ≤ 360 * K * tangency * (1 / (24 * K)) * (delta * t) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h10 (by positivity)) (by positivity)
        _ = 15 * tangency * (delta * t) := by field_simp [hK_pos.ne'] <;> ring
        _ = 15 * tangency * delta * t := by ring
    have h21 : (Δ + delta) * d ≤ 270000 * K^2 * tangency^2 * delta * t :=
      common_tangent_small_distance_bound hK h_tangency hδ_pos ht_pos hd_pos
        hΔ_le_2d h1 h5
    have h_final :
        270000 * K^2 * tangency^2 * delta * t
          ≤ C * Real.rpow tangency C * delta * t :=
      common_tangent_rpow_bound h_tangency hδ_pos ht_pos hC_ge2 hC_coeff
    exact le_trans h21 h_final

  · -- Case 2: d > 360*K*tangency*sqrt(delta*t)
    have hCase2 : d > 360 * K * tangency * Real.sqrt (delta * t) := by linarith

    by_cases h2a : Δ > d / (12 * K)

    · -- Sub-case 2a: contradiction
      have h_ab_L : b - a = L := by
        simp [a, b, hL_def, ParameterInterval.length]
      have hderiv_gap :
          ∀ x ∈ Set.Icc a b, Δ - M * delta ≤ |deriv H x| := by
        intro x hx
        have hx1 : 0 ≤ x := by linarith [R.interval.left_mem.1, hx.1]
        have hx2 : x ≤ 1 := by linarith [R.interval.right_mem.2, hx.2]
        let xp : UnitPoint := ⟨x, ⟨hx1, hx2⟩⟩
        have hxp_in : xp ∈ R.interval.carrier := ⟨hx.1, hx.2⟩
        have hderiv_eq :
            deriv H x = f.firstDeriv xp - g.firstDeriv xp := by
          rw [h_deriv_eq x]
          rw [C2Function.deriv_extension_eq_firstDeriv f xp,
            C2Function.deriv_extension_eq_firstDeriv g xp]
        have hsum :
            Δ ≤ |f xp - g xp| + |f.firstDeriv xp - g.firstDeriv xp| :=
          hΔ_pointwise xp (hR_sub_half hxp_in)
        have hvalue : |f xp - g xp| ≤ M * delta := hfg_bound xp hxp_in
        rw [hderiv_eq]
        linarith
      have hvariation : |H b - H a| ≤ 2 * M * delta := by
        calc
          |H b - H a| = |H b + (-H a)| := by ring_nf
          _ ≤ |H b| + |-H a| := abs_add_le (H b) (-H a)
          _ = |H b| + |H a| := by rw [abs_neg]
          _ ≤ M * delta + M * delta := add_le_add hHb_bound hHa_bound
          _ = 2 * M * delta := by ring
      have h2b : Δ ≤ d / (12 * K) :=
        large_distance_forces_parameter_bound hK h_tangency hδ_pos hδt ht
          (by simp [hM_def]) hL_eq hL_pos h_ab_L h_ab_lt hCase2
          hH_diff1 hderiv_gap hvariation
      exact False.elim ((not_lt_of_ge h2b) h2a)

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

      have hH''_abs_lower :
          ∀ x ∈ Set.Icc I.left I.right,
            d / (2 * K) ≤ |deriv (deriv H) x| :=
        curvature_abs_lower_on_real_interval I H f g hK_pos hd_pos
          hH''_eq h_H''_bound

      have hH''_ne_zero : ∀ (x : ℝ), x ∈ Set.Icc I.left I.right → deriv (deriv H) x ≠ 0 := by
        intro x hx
        have habs_pos : 0 < |deriv (deriv H) x| := by
          have hlower := hH''_abs_lower x hx
          have hpositive : 0 < d / (2 * K) := by positivity
          exact lt_of_lt_of_le hpositive hlower
        exact abs_pos.mp habs_pos

      have hderiv_cont : Continuous (deriv (deriv H)) := hH2_c2.continuous_deriv_one
      have hH_cont : ContinuousOn (deriv (deriv H)) (Set.Icc I.left I.right) := hderiv_cont.continuousOn

      have h_sign : (∀ x ∈ Set.Icc I.left I.right, 0 < deriv (deriv H) x) ∨
          (∀ x ∈ Set.Icc I.left I.right, deriv (deriv H) x < 0) :=
        constant_sign_of_never_zero I.left_le_right hH_cont hH''_ne_zero

      let a_J : ℝ := I.midpoint - I.length / 4
      let b_J : ℝ := I.midpoint + I.length / 4

      let J_set : Set ℝ := Set.Icc a_J b_J

      have hinterval_geometry :=
        central_subinterval_geometry I hK hI_long hI_short
          (by simpa only [a] using hleft_center)
          (by simpa only [b] using hright_center)
          (by simpa only [a] using R.interval.left_mem.2)
      have haJ_in_I : a_J ∈ Set.Icc I.left I.right := by
        simpa only [a_J] using hinterval_geometry.1
      have hbJ_in_I : b_J ∈ Set.Icc I.left I.right := by
        simpa only [b_J] using hinterval_geometry.2.1
      have hJ_sub_I : J_set ⊆ Set.Icc I.left I.right := by
        simpa only [J_set, a_J, b_J] using hinterval_geometry.2.2.1
      have hR_sub_J : Set.Icc a b ⊆ J_set := by
        simpa only [J_set, a_J, b_J] using hinterval_geometry.2.2.2.1
      have h_geom5 : 1 / (96 * K) ≤ a - a_J := by
        simpa only [a_J] using hinterval_geometry.2.2.2.2.1
      have h_geom6 : a - a_J ≤ 1 := by
        simpa only [a_J] using hinterval_geometry.2.2.2.2.2.1
      have h_geom7 : 1 / (96 * K) ≤ b_J - b := by
        simpa only [b_J] using hinterval_geometry.2.2.2.2.2.2.1
      have h_geom8 : b_J - b ≤ 1 / (16 * K) := by
        simpa only [b_J] using hinterval_geometry.2.2.2.2.2.2.2
      have h_ab_L : b - a = L := by simp [a, b, hL_def, ParameterInterval.length] <;> ring

      have h_int_bound_H : ∀ (x0 : ℝ), x0 ∈ Set.Icc a b → |H x0| ≤ M * delta := by
        simpa only [H, a, b] using
          extension_sub_bound_on_rectangle_interval R f g hfg_bound

      have hΔ_J_H : ∀ (x0 : ℝ), x0 ∈ J_set → Δ ≤ |H x0| + |deriv H x0| := by
        simpa only [H, J_set, a_J, b_J] using
          extension_sub_tangency_lower_on_central_half I f g Δ hΔ_pointwise

      have h_final_bound : 2700 * K^2 * M^2 * delta * t ≤
          C * Real.rpow tangency C * delta * t :=
        common_tangent_general_rpow_bound h_tangency hδ_pos ht_pos
          hC_ge2 hC_coeff (by simp [hM_def])
      rcases h_sign with (h_pos | h_neg)
      · have h_main : (Δ + delta) * d ≤ 2700 * K^2 * M^2 * delta * t :=
          common_tangent_main_proof_general K d delta t L a b a_J b_J Δ M I hK hK_pos hd_pos hδ_pos ht_pos hδt ht hL_eq hL_le hL_pos h_ab_L hab ha_in_I hb_in_I hJ_sub_I hR_sub_J h_geom5 h_geom6 h_geom7 h_geom8 H hH_diff1 hH_diff2
            (fun x hx => by
              rw [← abs_of_pos (h_pos x hx)]
              exact hH''_abs_lower x hx)
            hH''_abs_le_d hM_ge1 hHa_bound hHb_bound h_int_bound_H hΔ_J_H
        exact le_trans h_main h_final_bound
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
          rw [← abs_of_neg h4]
          exact hH''_abs_lower x hx
        have hH2''_abs : ∀ x ∈ Set.Icc I.left I.right, |deriv (deriv H2) x| ≤ d := by
          intro x hx
          have h1 : deriv (deriv H2) x = -deriv (deriv H) x := by
            have h2 : deriv H2 = -deriv H := by funext w; simp [H2, deriv_neg]
            rw [h2]
            have h3 : deriv (-deriv H) x = -deriv (deriv H) x := by
              simpa [deriv_neg] using rfl
            exact h3
          rw [h1, abs_neg]; exact hH''_abs_le_d x hx
        have hH2a : |H2 a| ≤ M * delta := by
          have h1 : H2 a = -H a := by simp [H2]
          rw [h1, abs_neg]; exact hHa_bound
        have hH2b : |H2 b| ≤ M * delta := by
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
        have h_int_bound_H2 : ∀ (x0 : ℝ), x0 ∈ Set.Icc a b → |H2 x0| ≤ M * delta := by
          intro x0 hx0
          have h1 : |H2 x0| = |H x0| := by
            have h2 : H2 x0 = -H x0 := by simp [H2]
            rw [h2, abs_neg]
          rw [h1]
          exact h_int_bound_H x0 hx0
        have h_main_robust : (Δ + delta) * d ≤ 2700 * K^2 * M^2 * delta * t :=
          common_tangent_main_proof_general K d delta t L a b a_J b_J Δ M I hK hK_pos hd_pos hδ_pos ht_pos hδt ht hL_eq hL_le hL_pos h_ab_L hab ha_in_I hb_in_I hJ_sub_I hR_sub_J h_geom5 h_geom6 h_geom7 h_geom8 H2 hH2_diff1 hH2_diff2
            hH2''_pos hH2''_abs hM_ge1 hH2a hH2b h_int_bound_H2 hΔ_J2
        exact le_trans h_main_robust h_final_bound

end Kakeya.Cinematic
