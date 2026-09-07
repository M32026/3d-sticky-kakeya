import MyLeanRepo.Kakeya.Assouad.WZ1.Statements
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# WZ1 smooth segment extension

Closed proof of the compactly supported `C²` extension from WZ1 Lemma 28.
-/


namespace Kakeya.Assouad

open Real Filter Set

lemma deriv_st_zero_of_neg {x : ℝ} (hx : x < 0) :
    deriv smoothTransition x = 0 := by
  have h_loc : ∀ᶠ y in nhds x, smoothTransition y = 0 := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact smoothTransition.zero_of_nonpos hy.le
  exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq h_loc |>.deriv

lemma deriv2_st_zero_of_neg {x : ℝ} (hx : x < 0) :
    deriv (deriv smoothTransition) x = 0 := by
  have h_loc : ∀ᶠ y in nhds x, deriv smoothTransition y = 0 := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact deriv_st_zero_of_neg hy
  exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq h_loc |>.deriv

lemma deriv_st_zero_of_gt_one {x : ℝ} (hx : 1 < x) :
    deriv smoothTransition x = 0 := by
  have h_loc : ∀ᶠ y in nhds x, smoothTransition y = 1 := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact smoothTransition.one_of_one_le hy.le
  exact (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq h_loc |>.deriv

lemma deriv2_st_zero_of_gt_one {x : ℝ} (hx : 1 < x) :
    deriv (deriv smoothTransition) x = 0 := by
  have h_loc : ∀ᶠ y in nhds x, deriv smoothTransition y = 0 := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact deriv_st_zero_of_gt_one hy
  exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq h_loc |>.deriv

lemma deriv_st_zero_at_zero : deriv smoothTransition 0 = 0 := by
  have hcd1 : ContDiff ℝ 1 smoothTransition := Real.smoothTransition.contDiff (n := 1)
  have hcont : Continuous (deriv smoothTransition) := hcd1.continuous_deriv_one
  let seq : ℕ → ℝ := fun n => -(1 / (n + 1 : ℝ))
  have hseq_neg : ∀ n, seq n < 0 := by
    intro n; simp [seq]; positivity
  have hseq : ∀ n, deriv smoothTransition (seq n) = 0 := by
    intro n; exact deriv_st_zero_of_neg (hseq_neg n)
  have h4 : Filter.Tendsto seq Filter.atTop (nhds 0) := by
    have hpos : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [seq, neg_zero] using hpos.neg
  have hlim : Filter.Tendsto (deriv smoothTransition ∘ seq) Filter.atTop (nhds (deriv smoothTransition 0)) :=
    hcont.continuousAt.tendsto.comp h4
  have hlim0 : Filter.Tendsto (deriv smoothTransition ∘ seq) Filter.atTop (nhds 0) := by
    have h_eq : deriv smoothTransition ∘ seq = fun (_ : ℕ) => (0 : ℝ) := by
      funext n; exact hseq n
    rw [h_eq]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hlim0

lemma deriv2_st_zero_at_zero : deriv (deriv smoothTransition) 0 = 0 := by
  have hcd2 : ContDiff ℝ 2 smoothTransition := Real.smoothTransition.contDiff (n := 2)
  have hcd1_deriv : ContDiff ℝ 1 (deriv smoothTransition) := hcd2.deriv'
  have hcont : Continuous (deriv (deriv smoothTransition)) := hcd1_deriv.continuous_deriv_one
  let seq : ℕ → ℝ := fun n => -(1 / (n + 1 : ℝ))
  have hseq_neg : ∀ n, seq n < 0 := by
    intro n; simp [seq]; positivity
  have hseq : ∀ n, deriv (deriv smoothTransition) (seq n) = 0 := by
    intro n; exact deriv2_st_zero_of_neg (hseq_neg n)
  have h4 : Filter.Tendsto seq Filter.atTop (nhds 0) := by
    have hpos : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [seq, neg_zero] using hpos.neg
  have hlim : Filter.Tendsto (deriv (deriv smoothTransition) ∘ seq) Filter.atTop (nhds (deriv (deriv smoothTransition) 0)) :=
    hcont.continuousAt.tendsto.comp h4
  have hlim0 : Filter.Tendsto (deriv (deriv smoothTransition) ∘ seq) Filter.atTop (nhds 0) := by
    have h_eq : deriv (deriv smoothTransition) ∘ seq = fun (_ : ℕ) => (0 : ℝ) := by
      funext n; exact hseq n
    rw [h_eq]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hlim0

lemma st_deriv_bounds :
    ∃ (M1 M2 : ℝ), 0 ≤ M1 ∧ 0 ≤ M2 ∧
      (∀ x : ℝ, |deriv smoothTransition x| ≤ M1) ∧
      (∀ x : ℝ, |deriv (deriv smoothTransition) x| ≤ M2) := by
  have hcd1 : ContDiff ℝ 1 smoothTransition :=
    Real.smoothTransition.contDiff (n := 1)
  have hcd2 : ContDiff ℝ 2 smoothTransition :=
    Real.smoothTransition.contDiff (n := 2)
  have hcont1 : Continuous (deriv smoothTransition) := hcd1.continuous_deriv_one
  have hcd1_deriv : ContDiff ℝ 1 (deriv smoothTransition) := hcd2.deriv'
  have hcont2 : Continuous (deriv (deriv smoothTransition)) := hcd1_deriv.continuous_deriv_one
  let K : Set ℝ := Set.Icc (-1 : ℝ) 2
  have hK_compact : IsCompact K := isCompact_Icc
  have h_bdd1 := hK_compact.bddAbove_image (hcont1.abs.continuousOn)
  have h_bdd2 := hK_compact.bddAbove_image (hcont2.abs.continuousOn)
  rcases h_bdd1 with ⟨M1, hM1⟩
  rcases h_bdd2 with ⟨M2, hM2⟩
  have hK_mem : (-1 / 2 : ℝ) ∈ K := by
    simp only [K, Set.mem_Icc] <;> norm_num
  have hM1_nonneg : 0 ≤ M1 := by
    have h : |deriv smoothTransition (-1 / 2 : ℝ)| ≤ M1 :=
      hM1 (Set.mem_image_of_mem _ hK_mem)
    have h' : deriv smoothTransition (-1 / 2 : ℝ) = 0 :=
      deriv_st_zero_of_neg (by norm_num)
    rw [h'] at h; simp at h; linarith
  have hM2_nonneg : 0 ≤ M2 := by
    have h : |deriv (deriv smoothTransition) (-1 / 2 : ℝ)| ≤ M2 :=
      hM2 (Set.mem_image_of_mem _ hK_mem)
    have h' : deriv (deriv smoothTransition) (-1 / 2 : ℝ) = 0 :=
      deriv2_st_zero_of_neg (by norm_num)
    rw [h'] at h; simp at h; linarith
  have h_out1 : ∀ x, x < -1 ∨ x > 2 → deriv smoothTransition x = 0 := by
    intro x hx; rcases hx with (h | h)
    · exact deriv_st_zero_of_neg (by linarith)
    · exact deriv_st_zero_of_gt_one (by linarith)
  have h_out2 : ∀ x, x < -1 ∨ x > 2 → deriv (deriv smoothTransition) x = 0 := by
    intro x hx; rcases hx with (h | h)
    · exact deriv2_st_zero_of_neg (by linarith)
    · exact deriv2_st_zero_of_gt_one (by linarith)
  have h_split : ∀ (x : ℝ), x ∉ K → x < -1 ∨ x > 2 := by
    intro x hx
    have h_nin : ¬(-1 ≤ x ∧ x ≤ 2) := by simpa [K, Set.mem_Icc] using hx
    by_cases h1 : x < -1
    · exact Or.inl h1
    · have h2 : -1 ≤ x := by linarith
      have h3 : ¬(x ≤ 2) := by tauto
      exact Or.inr (by linarith)
  have hM1_all : ∀ x, |deriv smoothTransition x| ≤ M1 := by
    intro x
    by_cases h : x ∈ K
    · exact hM1 (Set.mem_image_of_mem _ h)
    · have h' := h_split x h
      rw [h_out1 x h']; simp; exact hM1_nonneg
  have hM2_all : ∀ x, |deriv (deriv smoothTransition) x| ≤ M2 := by
    intro x
    by_cases h : x ∈ K
    · exact hM2 (Set.mem_image_of_mem _ h)
    · have h' := h_split x h
      rw [h_out2 x h']; simp; exact hM2_nonneg
  exact ⟨M1, M2, hM1_nonneg, hM2_nonneg, hM1_all, hM2_all⟩

lemma deriv_affine (f : ℝ → ℝ) (c a : ℝ) (ha : 0 < a) (x : ℝ)
    (hdiff : DifferentiableAt ℝ f ((x - c) / a)) :
    deriv (fun y => f ((y - c) / a)) x = deriv f ((x - c) / a) / a := by
  have h1 : HasDerivAt (fun y : ℝ => (y - c) / a) (1 / a) x := by
    have h2 : HasDerivAt (fun y => y - c) (1 : ℝ) x :=
      (hasDerivAt_id x).sub_const c
    have h3 : HasDerivAt (fun y => (y - c) / a) ((1 : ℝ) / a) x :=
      h2.div_const a
    simpa using h3
  have h_comp : HasDerivAt (f ∘ fun y => (y - c) / a)
      (deriv f ((x - c) / a) * (1 / a)) x :=
    hdiff.hasDerivAt.comp x h1
  have h_deriv : deriv (f ∘ fun y => (y - c) / a) x =
      deriv f ((x - c) / a) * (1 / a) := h_comp.deriv
  have h_eq1 : (f ∘ fun y => (y - c) / a) = (fun y => f ((y - c) / a)) := by
    funext y; rfl
  rw [h_eq1] at h_deriv
  rw [h_deriv]
  ring

lemma deriv2_affine (f : ℝ → ℝ) (c a : ℝ) (ha : 0 < a) (x : ℝ)
    (hdiff_all : Differentiable ℝ f)
    (hdiff2 : DifferentiableAt ℝ (deriv f) ((x - c) / a)) :
    deriv (deriv (fun y => f ((y - c) / a))) x =
      deriv (deriv f) ((x - c) / a) / a^2 := by
  have h_eq1 : ∀ y, deriv (fun z => f ((z - c) / a)) y =
      deriv f ((y - c) / a) / a := by
    intro y
    exact deriv_affine f c a ha y (hdiff_all.differentiableAt)
  have h : deriv (fun z => f ((z - c) / a)) = fun y => deriv f ((y - c) / a) / a := by
    funext y; exact h_eq1 y
  rw [h]
  have h1 : HasDerivAt (fun y : ℝ => (y - c) / a) (1 / a) x := by
    have h2 : HasDerivAt (fun y => y - c) (1 : ℝ) x :=
      (hasDerivAt_id x).sub_const c
    have h3 : HasDerivAt (fun y => (y - c) / a) ((1 : ℝ) / a) x :=
      h2.div_const a
    simpa using h3
  have h4 : HasDerivAt (deriv f) (deriv (deriv f) ((x - c) / a)) ((x - c) / a) :=
    hdiff2.hasDerivAt
  have h5 : HasDerivAt (deriv f ∘ fun y => (y - c) / a)
      (deriv (deriv f) ((x - c) / a) * (1 / a)) x :=
    h4.comp x h1
  have h5' : HasDerivAt (fun y => deriv f ((y - c) / a))
      (deriv (deriv f) ((x - c) / a) / a) x := by
    have h_eq : deriv (deriv f) ((x - c) / a) * (1 / a) =
        deriv (deriv f) ((x - c) / a) / a := by ring
    rw [h_eq] at h5
    exact h5
  have h6 : HasDerivAt (fun y => deriv f ((y - c) / a) / a)
      (deriv (deriv f) ((x - c) / a) / a / a) x :=
    h5'.div_const a
  have h7 : deriv (deriv f) ((x - c) / a) / a / a =
      deriv (deriv f) ((x - c) / a) / a^2 := by
    field_simp [ha.ne'] <;> ring
  rw [h7] at h6
  exact h6.deriv

lemma alg_identity1 (M2 M1 a y1 m : ℝ) (ha : 0 < a) :
    (M2 / a^2) * (|y1| + a * |m|) + 2 * (M1 / a) * |m| =
    M2 * |y1| / a^2 + (M2 + 2 * M1) * |m| / a := by
  have hne : a ≠ 0 := ha.ne'
  have h1 : (M2 / a^2) * (|y1| + a * |m|) = M2 * |y1| / a^2 + M2 * |m| / a := by
    have h2 : (M2 / a^2) * (a * |m|) = M2 * |m| / a := by
      calc
        (M2 / a^2) * (a * |m|) = M2 * (a * |m|) / a^2 := by ring
        _ = M2 * |m| / a := by
          field_simp [hne] <;> ring
    rw [mul_add, h2] <;> ring
  have h3 : 2 * (M1 / a) * |m| = 2 * M1 * |m| / a := by
    field_simp [hne] <;> ring
  rw [h1, h3] <;> ring

lemma alg_identity2 (A y1 y2 a m : ℝ) (ha : 0 < a) :
    A * ((|y1| + |y2|) / a^2 + |m| / a) =
    A * (|y1| + |y2|) / a^2 + A * |m| / a := by
  have hne : a ≠ 0 := ha.ne'
  field_simp [hne] <;> ring

lemma final_bound2 (A M1 M2 y1 y2 a m : ℝ) (ha : 0 < a)
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hA1 : 1 ≤ A) (hA22 : M2 + 2 * M1 ≤ A) :
    M2 * |y1| / a^2 + (M2 + 2 * M1) * |m| / a ≤
    A * ((|y1| + |y2|) / a^2 + |m| / a) := by
  have h2 : M2 ≤ A := by linarith
  have h3 : 0 ≤ |y1| := abs_nonneg y1
  have h4 : 0 ≤ |y2| := abs_nonneg y2
  have h5 : 0 ≤ A := by linarith
  have h6 : M2 * |y1| ≤ A * (|y1| + |y2|) := by
    have h7 : M2 * |y1| ≤ A * |y1| := mul_le_mul_of_nonneg_right h2 h3
    have h8 : A * |y1| ≤ A * (|y1| + |y2|) := by
      have h9 : 0 ≤ A * |y2| := by positivity
      linarith
    linarith
  have h10 : M2 * |y1| / a^2 ≤ A * (|y1| + |y2|) / a^2 := by
    exact div_le_div_of_nonneg_right h6 (by positivity)
  have h11 : (M2 + 2 * M1) * |m| ≤ A * |m| := by
    exact mul_le_mul_of_nonneg_right hA22 (abs_nonneg m)
  have h12 : (M2 + 2 * M1) * |m| / a ≤ A * |m| / a := by
    exact div_le_div_of_nonneg_right h11 ha.le
  have h14 := alg_identity2 A y1 y2 a m ha
  rw [h14]
  linarith

lemma final_bound2_right (A M1 M2 y1 y2 a m : ℝ) (ha : 0 < a)
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hA1 : 1 ≤ A) (hA22 : M2 + 2 * M1 ≤ A) :
    M2 * |y2| / a^2 + (M2 + 2 * M1) * |m| / a ≤
    A * ((|y1| + |y2|) / a^2 + |m| / a) := by
  have h2 : M2 ≤ A := by linarith
  have h3 : 0 ≤ |y1| := abs_nonneg y1
  have h4 : 0 ≤ |y2| := abs_nonneg y2
  have h5 : 0 ≤ A := by linarith
  have h6 : M2 * |y2| ≤ A * (|y1| + |y2|) := by
    have h7 : M2 * |y2| ≤ A * |y2| := mul_le_mul_of_nonneg_right h2 h4
    have h8 : A * |y2| ≤ A * (|y1| + |y2|) := by
      have h9 : 0 ≤ A * |y1| := by positivity
      linarith
    linarith
  have h10 : M2 * |y2| / a^2 ≤ A * (|y1| + |y2|) / a^2 := by
    exact div_le_div_of_nonneg_right h6 (by positivity)
  have h11 : (M2 + 2 * M1) * |m| ≤ A * |m| := by
    exact mul_le_mul_of_nonneg_right hA22 (abs_nonneg m)
  have h12 : (M2 + 2 * M1) * |m| / a ≤ A * |m| / a := by
    exact div_le_div_of_nonneg_right h11 ha.le
  have h14 := alg_identity2 A y1 y2 a m ha
  rw [h14]
  linarith

lemma interior_second_deriv_bound (A a : ℝ) (ha : 0 < a) (hA1 : 1 ≤ A)
    (y1 y2 m : ℝ) (L : ℝ → ℝ) (x : ℝ) :
    |(0 : ℝ) * L x + 2 * (0 : ℝ) * m| ≤ A * ((|y1| + |y2|) / a^2 + |m| / a) := by
  have h : (0 : ℝ) * L x + 2 * (0 : ℝ) * m = (0 : ℝ) := by simp
  rw [h]
  have h2 : 0 ≤ A * ((|y1| + |y2|) / a^2 + |m| / a) := by positivity
  simpa using h2

lemma dr_zero_at_or_before (s_right : ℝ → ℝ) (x2 a x : ℝ) (ha : 0 < a)
    (h_deriv_right : ∀ y, deriv s_right y = deriv smoothTransition ((y - x2) / a) / a)
    (h_dr_zero : ∀ y, y < x2 → deriv s_right y = 0)
    (h : x ≤ x2) : deriv s_right x = 0 := by
  by_cases h' : x < x2
  · exact h_dr_zero x h'
  · have h_eq : x = x2 := by
      exact le_antisymm h (by linarith)
    rw [h_deriv_right x, h_eq]
    have h_arg : (x2 - x2) / a = 0 := by simp
    rw [h_arg, deriv_st_zero_at_zero] <;> ring

lemma d2r_zero_at_or_before (s_right : ℝ → ℝ) (x2 a x : ℝ) (ha : 0 < a)
    (h_deriv2_right : ∀ y, deriv (deriv s_right) y = deriv (deriv smoothTransition) ((y - x2) / a) / a^2)
    (h_d2r_zero : ∀ y, y < x2 → deriv (deriv s_right) y = 0)
    (h : x ≤ x2) : deriv (deriv s_right) x = 0 := by
  by_cases h' : x < x2
  · exact h_d2r_zero x h'
  · have h_eq : x = x2 := by
      exact le_antisymm h (by linarith)
    rw [h_deriv2_right x, h_eq]
    have h_arg : (x2 - x2) / a = 0 := by simp
    rw [h_arg, deriv2_st_zero_at_zero] <;> ring

theorem wz1_smooth_segment_extension : WZ1SmoothSegmentExtensionStatement := by
  rcases st_deriv_bounds with ⟨M1, M2, hM1_nonneg, hM2_nonneg, hM1, hM2⟩
  let A : ℝ := 3 * M1 + M2 + 2
  have hA1 : 1 ≤ A := by linarith
  have hA_M11 : M1 + 1 ≤ A := by linarith
  have hA_M22 : M2 + 2 * M1 ≤ A := by linarith
  refine' ⟨A, hA1, _⟩
  intro x1 x2 y1 y2 a hx12 ha
  set m : ℝ := (y2 - y1) / (x2 - x1) with hm
  set L : ℝ → ℝ := fun x => y1 + (x - x1) * m with hL
  set s_left : ℝ → ℝ := fun x => smoothTransition ((x - (x1 - a)) / a) with hs_left
  set s_right : ℝ → ℝ := fun x => smoothTransition ((x - x2) / a) with hs_right
  set φ : ℝ → ℝ := fun x => s_left x * (1 - s_right x) with hφ
  set G : ℝ → ℝ := fun x => φ x * L x with hG

  have hcd_st : ContDiff ℝ 2 smoothTransition :=
    Real.smoothTransition.contDiff (n := 2)
  have hcd_left : ContDiff ℝ 2 s_left := by
    simp only [hs_left]
    fun_prop
  have hcd_right : ContDiff ℝ 2 s_right := by
    simp only [hs_right]
    fun_prop
  have hcd_φ : ContDiff ℝ 2 φ := by
    simp only [hφ]
    fun_prop
  have hcd_L : ContDiff ℝ 2 L := by
    simp only [hL]
    fun_prop
  have hcd_G : ContDiff ℝ 2 G := by
    simp only [hG]
    fun_prop
  let G_sf : SlopeFunction := ⟨G, hcd_G⟩

  have hcd_φ1 : ContDiff ℝ 1 (deriv φ) := hcd_φ.deriv'
  have hcd_left1 : ContDiff ℝ 1 (deriv s_left) := hcd_left.deriv'
  have hcd_right1 : ContDiff ℝ 1 (deriv s_right) := hcd_right.deriv'
  have h_diff_φ : Differentiable ℝ φ := by fun_prop
  have h_diff_φ1 : Differentiable ℝ (deriv φ) := by fun_prop
  have h_diff_left : Differentiable ℝ s_left := by fun_prop
  have h_diff_left1 : Differentiable ℝ (deriv s_left) := by fun_prop
  have h_diff_right : Differentiable ℝ s_right := by fun_prop
  have h_diff_right1 : Differentiable ℝ (deriv s_right) := by fun_prop
  have h_diff_L : Differentiable ℝ L := by fun_prop

  have h_deriv_L : ∀ x, deriv L x = m := by
    intro x; simp [hL, hm]
  have h_deriv2_L : ∀ x, deriv (deriv L) x = 0 := by
    intro x
    have h : deriv L = fun (_ : ℝ) => m := by funext z; exact h_deriv_L z
    rw [h]; simp

  have h_diff_all : Differentiable ℝ smoothTransition := by fun_prop
  have h_diff2_all : Differentiable ℝ (deriv smoothTransition) := by fun_prop
  have h_diff_st : ∀ (x : ℝ), DifferentiableAt ℝ smoothTransition x := by
    intro x; exact h_diff_all.differentiableAt
  have h_diff_st2 : ∀ (x : ℝ), DifferentiableAt ℝ (deriv smoothTransition) x := by
    intro x; exact h_diff2_all.differentiableAt

  have h_deriv_left : ∀ x, deriv s_left x =
      deriv smoothTransition ((x - (x1 - a)) / a) / a := by
    intro x
    exact deriv_affine smoothTransition (x1 - a) a ha x (h_diff_st ((x - (x1 - a)) / a))
  have h_deriv2_left : ∀ x, deriv (deriv s_left) x =
      deriv (deriv smoothTransition) ((x - (x1 - a)) / a) / a^2 := by
    intro x
    exact deriv2_affine smoothTransition (x1 - a) a ha x h_diff_all (h_diff_st2 ((x - (x1 - a)) / a))
  have h_deriv_right : ∀ x, deriv s_right x =
      deriv smoothTransition ((x - x2) / a) / a := by
    intro x
    exact deriv_affine smoothTransition x2 a ha x (h_diff_st ((x - x2) / a))
  have h_deriv2_right : ∀ x, deriv (deriv s_right) x =
      deriv (deriv smoothTransition) ((x - x2) / a) / a^2 := by
    intro x
    exact deriv2_affine smoothTransition x2 a ha x h_diff_all (h_diff_st2 ((x - x2) / a))

  have h_left_bound1 : ∀ x, |deriv s_left x| ≤ M1 / a := by
    intro x
    rw [h_deriv_left x]
    rw [abs_div, abs_of_pos ha]
    exact div_le_div_of_nonneg_right (hM1 _) ha.le
  have h_left_bound2 : ∀ x, |deriv (deriv s_left) x| ≤ M2 / a^2 := by
    intro x
    rw [h_deriv2_left x]
    rw [abs_div, abs_of_pos (sq_pos_of_pos ha)]
    exact div_le_div_of_nonneg_right (hM2 _) (sq_nonneg a)
  have h_right_bound1 : ∀ x, |deriv s_right x| ≤ M1 / a := by
    intro x
    rw [h_deriv_right x]
    rw [abs_div, abs_of_pos ha]
    exact div_le_div_of_nonneg_right (hM1 _) ha.le
  have h_right_bound2 : ∀ x, |deriv (deriv s_right) x| ≤ M2 / a^2 := by
    intro x
    rw [h_deriv2_right x]
    rw [abs_div, abs_of_pos (sq_pos_of_pos ha)]
    exact div_le_div_of_nonneg_right (hM2 _) (sq_nonneg a)

  have hsl_eq : ∀ x, s_left x = smoothTransition ((x - (x1 - a)) / a) := by
    intro x; simpa [hs_left] using rfl
  have hsr_eq : ∀ x, s_right x = smoothTransition ((x - x2) / a) := by
    intro x; simpa [hs_right] using rfl
  have hφ_eq : ∀ x, φ x = s_left x * (1 - s_right x) := by
    intro x; simpa [hφ] using rfl
  have hG_eq : ∀ x, G x = φ x * L x := by
    intro x; simpa [hG] using rfl

  have h_sl_zero : ∀ x, x ≤ x1 - a → s_left x = 0 := by
    intro x hx
    have h : (x - (x1 - a)) / a ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg <;> linarith
    have h' : s_left x = smoothTransition ((x - (x1 - a)) / a) := hsl_eq x
    rw [h']; exact smoothTransition.zero_of_nonpos h
  have h_sl_one : ∀ x, x1 ≤ x → s_left x = 1 := by
    intro x hx
    have h : 1 ≤ (x - (x1 - a)) / a := by
      rw [one_le_div ha] <;> linarith
    have h' : s_left x = smoothTransition ((x - (x1 - a)) / a) := hsl_eq x
    rw [h']; exact smoothTransition.one_of_one_le h
  have h_sr_zero : ∀ x, x ≤ x2 → s_right x = 0 := by
    intro x hx
    have h : (x - x2) / a ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg <;> linarith
    have h' : s_right x = smoothTransition ((x - x2) / a) := hsr_eq x
    rw [h']; exact smoothTransition.zero_of_nonpos h
  have h_sr_one : ∀ x, x2 + a ≤ x → s_right x = 1 := by
    intro x hx
    have h : 1 ≤ (x - x2) / a := by
      rw [one_le_div ha] <;> linarith
    have h' : s_right x = smoothTransition ((x - x2) / a) := hsr_eq x
    rw [h']; exact smoothTransition.one_of_one_le h

  have h_dl_zero : ∀ x, x < x1 - a → deriv s_left x = 0 := by
    intro x hx
    have h : (x - (x1 - a)) / a < 0 := by
      apply div_neg_of_neg_of_pos <;> linarith
    rw [h_deriv_left x, deriv_st_zero_of_neg h] <;> ring
  have h_dl_zero' : ∀ x, x1 < x → deriv s_left x = 0 := by
    intro x hx
    have h : 1 < (x - (x1 - a)) / a := by
      rw [one_lt_div ha] <;> linarith
    rw [h_deriv_left x, deriv_st_zero_of_gt_one h] <;> ring
  have h_d2l_zero : ∀ x, x < x1 - a → deriv (deriv s_left) x = 0 := by
    intro x hx
    have h : (x - (x1 - a)) / a < 0 := by
      apply div_neg_of_neg_of_pos <;> linarith
    rw [h_deriv2_left x, deriv2_st_zero_of_neg h] <;> ring
  have h_d2l_zero' : ∀ x, x1 < x → deriv (deriv s_left) x = 0 := by
    intro x hx
    have h : 1 < (x - (x1 - a)) / a := by
      rw [one_lt_div ha] <;> linarith
    rw [h_deriv2_left x, deriv2_st_zero_of_gt_one h] <;> ring

  have h_dr_zero : ∀ x, x < x2 → deriv s_right x = 0 := by
    intro x hx
    have h : (x - x2) / a < 0 := by
      apply div_neg_of_neg_of_pos <;> linarith
    rw [h_deriv_right x, deriv_st_zero_of_neg h] <;> ring
  have h_dr_zero' : ∀ x, x2 + a < x → deriv s_right x = 0 := by
    intro x hx
    have h : 1 < (x - x2) / a := by
      rw [one_lt_div ha] <;> linarith
    rw [h_deriv_right x, deriv_st_zero_of_gt_one h] <;> ring
  have h_d2r_zero : ∀ x, x < x2 → deriv (deriv s_right) x = 0 := by
    intro x hx
    have h : (x - x2) / a < 0 := by
      apply div_neg_of_neg_of_pos <;> linarith
    rw [h_deriv2_right x, deriv2_st_zero_of_neg h] <;> ring
  have h_d2r_zero' : ∀ x, x2 + a < x → deriv (deriv s_right) x = 0 := by
    intro x hx
    have h : 1 < (x - x2) / a := by
      rw [one_lt_div ha] <;> linarith
    rw [h_deriv2_right x, deriv2_st_zero_of_gt_one h] <;> ring

  have h_deriv_G : ∀ x, deriv G x = deriv φ x * L x + φ x * m := by
    intro x
    have h : deriv G x = deriv φ x * L x + φ x * deriv L x :=
      deriv_mul h_diff_φ.differentiableAt h_diff_L.differentiableAt
    rw [h, h_deriv_L x] <;> ring

  have h_deriv2_G : ∀ x, deriv (deriv G) x =
      deriv (deriv φ) x * L x + 2 * deriv φ x * m := by
    intro x
    let f1 : ℝ → ℝ := fun x => deriv φ x * L x
    let f2 : ℝ → ℝ := fun x => φ x * m
    have h1 : deriv G = f1 + f2 := by
      funext z; exact h_deriv_G z
    rw [h1]
    have h_diff_f1 : DifferentiableAt ℝ f1 x := by fun_prop
    have h_diff_f2 : DifferentiableAt ℝ f2 x := by fun_prop
    have h4 : deriv (f1 + f2) x = deriv f1 x + deriv f2 x :=
      deriv_add h_diff_f1 h_diff_f2
    have h2 : deriv f1 x = deriv (deriv φ) x * L x + deriv φ x * deriv L x :=
      deriv_mul h_diff_φ1.differentiableAt h_diff_L.differentiableAt
    have h3 : deriv f2 x = deriv φ x * m := by
      have h_dφ_at_x : DifferentiableAt ℝ φ x := h_diff_φ.differentiableAt
      have h_const : HasDerivAt (fun (_ : ℝ) => m) 0 x := hasDerivAt_const x m
      have h : HasDerivAt f2 (deriv φ x * m + φ x * 0) x :=
        h_dφ_at_x.hasDerivAt.mul h_const
      have h' : deriv f2 x = deriv φ x * m + φ x * 0 := h.deriv
      rw [h']; ring
    rw [h4, h2, h3, h_deriv_L x] <;> ring

  have h_deriv_φ : ∀ x, deriv φ x =
      deriv s_left x * (1 - s_right x) - s_left x * deriv s_right x := by
    intro x
    let oms : ℝ → ℝ := fun x => 1 - s_right x
    have h_diff_oms : DifferentiableAt ℝ oms x :=
      h_diff_right.differentiableAt.const_sub 1
    have h : deriv φ x = deriv s_left x * oms x + s_left x * deriv oms x :=
      deriv_mul h_diff_left.differentiableAt h_diff_oms
    have h2 : deriv oms x = -deriv s_right x := by
      have h_c : HasDerivAt (fun (_ : ℝ) => (1 : ℝ)) 0 x := hasDerivAt_const x (1 : ℝ)
      have h_g : HasDerivAt s_right (deriv s_right x) x := h_diff_right.differentiableAt.hasDerivAt
      have h_sub : HasDerivAt oms (0 - deriv s_right x) x := h_c.sub h_g
      simpa [oms] using h_sub.deriv
    rw [h, h2] <;> ring

  have h_deriv2_φ : ∀ x, deriv (deriv φ) x =
      deriv (deriv s_left) x * (1 - s_right x)
      - 2 * deriv s_left x * deriv s_right x
      - s_left x * deriv (deriv s_right) x := by
    intro x
    let f1 : ℝ → ℝ := fun x => deriv s_left x * (1 - s_right x)
    let f2 : ℝ → ℝ := fun x => s_left x * deriv s_right x
    let oms : ℝ → ℝ := fun x => 1 - s_right x
    have h_diff_oms : DifferentiableAt ℝ oms x :=
      h_diff_right.differentiableAt.const_sub 1
    have h_eq : deriv φ = f1 - f2 := by
      funext z; exact h_deriv_φ z
    rw [h_eq]
    have h_diff_f1 : DifferentiableAt ℝ f1 x := by fun_prop
    have h_diff_f2 : DifferentiableAt ℝ f2 x := by fun_prop
    have h4 : deriv (f1 - f2) x = deriv f1 x - deriv f2 x :=
      deriv_sub h_diff_f1 h_diff_f2
    have h5 : deriv f1 x = deriv (deriv s_left) x * oms x + deriv s_left x * deriv oms x :=
      deriv_mul h_diff_left1.differentiableAt h_diff_oms
    have h6 : deriv oms x = -deriv s_right x := by
      have h_c : HasDerivAt (fun (_ : ℝ) => (1 : ℝ)) 0 x := hasDerivAt_const x (1 : ℝ)
      have h_g : HasDerivAt s_right (deriv s_right x) x := h_diff_right.differentiableAt.hasDerivAt
      have h_sub : HasDerivAt oms (0 - deriv s_right x) x := h_c.sub h_g
      simpa [oms] using h_sub.deriv
    have h7 : deriv f2 x = deriv s_left x * deriv s_right x + s_left x * deriv (deriv s_right) x :=
      deriv_mul h_diff_left.differentiableAt h_diff_right1.differentiableAt
    rw [h4, h5, h7, h6] <;> ring

  refine' ⟨G_sf, _⟩
  constructor
  · intro x hx
    change G x = y1 + (x - x1) * m
    have hsl : s_left x = 1 := h_sl_one x hx.1
    have hsr : s_right x = 0 := h_sr_zero x hx.2
    have hφ1 : φ x = 1 := by
      rw [hφ_eq x, hsl, hsr] <;> ring
    rw [hG_eq x, hφ1]
    simp [hL, hm] <;> ring
  constructor
  · intro x hx
    change G x = 0
    have h : x < x1 - a ∨ x2 + a < x := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hx; tauto
    rcases h with (h | h)
    · have hsl : s_left x = 0 := h_sl_zero x (by linarith)
      rw [hG_eq x, hφ_eq x, hsl] <;> ring
    · have hsr : s_right x = 1 := h_sr_one x (by linarith)
      rw [hG_eq x, hφ_eq x, hsr] <;> ring
  constructor
  · intro x
    change |deriv G x| ≤ A * ((|y1| + |y2|) / a + |m|)
    rw [h_deriv_G x]
    by_cases h1 : x ≤ x1
    · have hsr0 : s_right x = 0 := h_sr_zero x (by linarith)
      have hdr0 : deriv s_right x = 0 := h_dr_zero x (by linarith)
      have h_dφ : deriv φ x = deriv s_left x := by
        rw [h_deriv_φ x, hsr0, hdr0] <;> ring
      by_cases h2 : x ≤ x1 - a
      · have hsl0 : s_left x = 0 := h_sl_zero x h2
        have hφ0 : φ x = 0 := by
          rw [hφ_eq x, hsl0, hsr0] <;> ring
        have hdl0 : deriv s_left x = 0 := by
          rw [h_deriv_left x]
          have h_arg : (x - (x1 - a)) / a ≤ 0 := by
            apply div_nonpos_of_nonpos_of_nonneg <;> linarith
          by_cases h : (x - (x1 - a)) / a < 0
          · rw [deriv_st_zero_of_neg h] <;> ring
          · have h' : (x - (x1 - a)) / a = 0 := by linarith
            rw [h', deriv_st_zero_at_zero] <;> ring
        rw [h_dφ, hφ0, hdl0]
        have h_simp : |(0 : ℝ) * L x + (0 : ℝ) * m| = (0 : ℝ) := by simp
        rw [h_simp]
        have h_goal : (0 : ℝ) ≤ A * ((|y1| + |y2|) / a + |m|) := by positivity
        exact h_goal
      · have h3 : x1 - a < x := by linarith
        have hL_bound : |L x| ≤ |y1| + a * |m| := by
          have h4 : |x - x1| ≤ a := by
            rw [abs_le] <;> constructor <;> linarith
          calc
            |L x| = |y1 + (x - x1) * m| := by rw [hL] <;> ring
            _ ≤ |y1| + |(x - x1) * m| := abs_add_le _ _
            _ = |y1| + |x - x1| * |m| := by rw [abs_mul] <;> ring
            _ ≤ |y1| + a * |m| := by gcongr <;> linarith
        have hφ1 : 0 ≤ φ x := by
          have h : φ x = s_left x * (1 - s_right x) := hφ_eq x
          rw [h, hsr0]
          have hsl_nonneg : 0 ≤ s_left x := by
            rw [hsl_eq x]; exact smoothTransition.nonneg _
          simpa using hsl_nonneg
        have hφ2 : φ x ≤ 1 := by
          have h : φ x = s_left x * (1 - s_right x) := hφ_eq x
          rw [h, hsr0]
          have hsl_le_one : s_left x ≤ 1 := by
            rw [hsl_eq x]; exact smoothTransition.le_one _
          simpa using hsl_le_one
        rw [h_dφ]
        have h_main : |deriv s_left x * L x + φ x * m| ≤
            M1 * |y1| / a + (M1 + 1) * |m| := by
          have h6 : |deriv s_left x * L x + φ x * m| ≤
              |deriv s_left x * L x| + |φ x * m| := abs_add_le _ _
          have h5 : |φ x * m| = φ x * |m| := by
            rw [abs_mul, abs_of_nonneg hφ1]
          have h7 : |deriv s_left x * L x| = |deriv s_left x| * |L x| := by
            rw [abs_mul]
          calc
            |deriv s_left x * L x + φ x * m|
              ≤ |deriv s_left x * L x| + |φ x * m| := h6
            _ = |deriv s_left x| * |L x| + φ x * |m| := by rw [h7, h5]
            _ ≤ (M1 / a) * (|y1| + a * |m|) + 1 * |m| := by
                gcongr <;> linarith [h_left_bound1 x]
            _ = M1 * |y1| / a + (M1 + 1) * |m| := by
                field_simp [ha.ne'] <;> ring
        have h_final : M1 * |y1| / a + (M1 + 1) * |m| ≤
            A * ((|y1| + |y2|) / a + |m|) := by
          have h6 : M1 * |y1| / a ≤ A * (|y1| + |y2|) / a := by
            gcongr <;> linarith [abs_nonneg y2]
          have h7 : (M1 + 1) * |m| ≤ A * |m| := by
            gcongr <;> linarith [abs_nonneg m]
          have h8 : A * ((|y1| + |y2|) / a + |m|) =
              A * (|y1| + |y2|) / a + A * |m| := by
            field_simp [ha.ne'] <;> ring
          rw [h8]; linarith
        linarith
    · have h1' : x1 < x := by linarith
      have hdl0 : deriv s_left x = 0 := h_dl_zero' x h1'
      have hsl1 : s_left x = 1 := h_sl_one x (by linarith)
      by_cases h2 : x ≤ x2
      · have hsr0 : s_right x = 0 := h_sr_zero x h2
        have hdr0 : deriv s_right x = 0 := by
          rw [h_deriv_right x]
          have h_arg : (x - x2) / a ≤ 0 := by
            apply div_nonpos_of_nonpos_of_nonneg <;> linarith
          by_cases h : (x - x2) / a < 0
          · rw [deriv_st_zero_of_neg h] <;> ring
          · have h' : (x - x2) / a = 0 := by linarith
            rw [h', deriv_st_zero_at_zero] <;> ring
        have h_dφ : deriv φ x = 0 := by
          rw [h_deriv_φ x, hdl0, hsr0, hdr0] <;> ring
        have hφ1 : φ x = 1 := by
          rw [hφ_eq x, hsl1, hsr0] <;> ring
        have h_simp : |(0 : ℝ) * L x + (1 : ℝ) * m| = |m| := by simp
        rw [h_dφ, hφ1, h_simp]
        have h10 : A * ((|y1| + |y2|) / a + |m|) =
            A * ((|y1| + |y2|) / a) + A * |m| := by
          rw [mul_add]
        rw [h10]
        have h11 : |m| ≤ A * |m| := by
          have h12 : 0 ≤ |m| := abs_nonneg m
          nlinarith [hA1]
        have h13 : 0 ≤ A * ((|y1| + |y2|) / a) := by positivity
        linarith
      · have h2' : x2 < x := by linarith
        by_cases h3 : x ≤ x2 + a
        · have hL_bound : |L x| ≤ |y2| + a * |m| := by
            have h4 : |x - x2| ≤ a := by
              rw [abs_le] <;> constructor <;> linarith
            have h5 : L x = y2 + (x - x2) * m := by
              have hLx : L x = y1 + (x - x1) * m := by
                rw [hL] <;> simp only
              rw [hLx]
              have h6 : (x2 - x1) * m = y2 - y1 := by
                rw [hm]
                have hne : x2 - x1 ≠ 0 := by linarith
                field_simp [hne] <;> ring
              have h7 : y1 + (x - x1) * m = y2 + (x - x2) * m := by
                have h8 : (x - x1) = (x - x2) + (x2 - x1) := by ring
                rw [h8]
                rw [add_mul, h6] <;> ring
              exact h7
            rw [h5]
            calc
              |y2 + (x - x2) * m|
                ≤ |y2| + |(x - x2) * m| := abs_add_le _ _
              _ = |y2| + |x - x2| * |m| := by rw [abs_mul] <;> ring
              _ ≤ |y2| + a * |m| := by gcongr <;> linarith
          have h_dφ : deriv φ x = -deriv s_right x := by
            rw [h_deriv_φ x, hsl1, hdl0] <;> ring
          have hφ1 : 0 ≤ φ x := by
            have h : φ x = s_left x * (1 - s_right x) := hφ_eq x
            rw [h, hsl1]
            have hsr_nonneg : 0 ≤ s_right x := by
              rw [hsr_eq x]; exact smoothTransition.nonneg _
            have hsr_le_one : s_right x ≤ 1 := by
              rw [hsr_eq x]; exact smoothTransition.le_one _
            linarith
          have hφ2 : φ x ≤ 1 := by
            have h : φ x = s_left x * (1 - s_right x) := hφ_eq x
            rw [h, hsl1]
            have hsr_nonneg : 0 ≤ s_right x := by
              rw [hsr_eq x]; exact smoothTransition.nonneg _
            linarith
          rw [h_dφ]
          have h_main : |(-deriv s_right x) * L x + φ x * m| ≤
              M1 * |y2| / a + (M1 + 1) * |m| := by
            have h_tri : |(-deriv s_right x) * L x + φ x * m| ≤
                |(-deriv s_right x) * L x| + |φ x * m| := abs_add_le _ _
            have h5 : |φ x * m| = φ x * |m| := by
              rw [abs_mul, abs_of_nonneg hφ1]
            have h6 : |(-deriv s_right x) * L x| =
                |deriv s_right x| * |L x| := by
              rw [abs_mul, abs_neg]
            calc
              |(-deriv s_right x) * L x + φ x * m|
                ≤ |(-deriv s_right x) * L x| + |φ x * m| := h_tri
              _ = |deriv s_right x| * |L x| + φ x * |m| := by rw [h6, h5]
              _ ≤ (M1 / a) * (|y2| + a * |m|) + 1 * |m| := by
                  gcongr <;> linarith [h_right_bound1 x]
              _ = M1 * |y2| / a + (M1 + 1) * |m| := by
                  field_simp [ha.ne'] <;> ring
          have h_final : M1 * |y2| / a + (M1 + 1) * |m| ≤
              A * ((|y1| + |y2|) / a + |m|) := by
            have h6 : M1 * |y2| / a ≤ A * (|y1| + |y2|) / a := by
              gcongr <;> linarith [abs_nonneg y1]
            have h7 : (M1 + 1) * |m| ≤ A * |m| := by
              gcongr <;> linarith [abs_nonneg m]
            have h8 : A * ((|y1| + |y2|) / a + |m|) =
                A * (|y1| + |y2|) / a + A * |m| := by
              field_simp [ha.ne'] <;> ring
            rw [h8]; linarith
          linarith
        · have hsr1 : s_right x = 1 := h_sr_one x (by linarith)
          have hdr0 : deriv s_right x = 0 := h_dr_zero' x (by linarith)
          have hφ0 : φ x = 0 := by
            rw [hφ_eq x, hsl1, hsr1] <;> ring
          have h_dφ : deriv φ x = 0 := by
            rw [h_deriv_φ x, hsl1, hdl0, hdr0] <;> ring
          rw [h_dφ, hφ0]
          have h_simp : |(0 : ℝ) * L x + (0 : ℝ) * m| = (0 : ℝ) := by simp
          rw [h_simp]
          have h_goal : (0 : ℝ) ≤ A * ((|y1| + |y2|) / a + |m|) := by positivity
          exact h_goal
  · intro x
    change |deriv (deriv G) x| ≤ A * ((|y1| + |y2|) / a^2 + |m| / a)
    rw [h_deriv2_G x]
    by_cases h1 : x ≤ x1
    · have hsr0 : s_right x = 0 := h_sr_zero x (by linarith)
      have hdr0 : deriv s_right x = 0 := h_dr_zero x (by linarith)
      have h_d2r0 : deriv (deriv s_right) x = 0 := h_d2r_zero x (by linarith)
      have h_dφ : deriv φ x = deriv s_left x := by
        rw [h_deriv_φ x, hsr0, hdr0] <;> ring
      have h_d2φ : deriv (deriv φ) x = deriv (deriv s_left) x := by
        have h_eq := h_deriv2_φ x
        rw [h_eq, hsr0, hdr0, h_d2r0] <;> ring
      by_cases h2 : x ≤ x1 - a
      · have hsl0 : s_left x = 0 := h_sl_zero x h2
        have hφ0 : φ x = 0 := by
          rw [hφ_eq x, hsl0, hsr0] <;> ring
        have hdl0 : deriv s_left x = 0 := by
          rw [h_deriv_left x]
          have h_arg : (x - (x1 - a)) / a ≤ 0 := by
            apply div_nonpos_of_nonpos_of_nonneg <;> linarith
          by_cases h : (x - (x1 - a)) / a < 0
          · rw [deriv_st_zero_of_neg h] <;> ring
          · have h' : (x - (x1 - a)) / a = 0 := by linarith
            rw [h', deriv_st_zero_at_zero] <;> ring
        have h_d2l0 : deriv (deriv s_left) x = 0 := by
          rw [h_deriv2_left x]
          have h_arg : (x - (x1 - a)) / a ≤ 0 := by
            apply div_nonpos_of_nonpos_of_nonneg <;> linarith
          by_cases h : (x - (x1 - a)) / a < 0
          · rw [deriv2_st_zero_of_neg h] <;> ring
          · have h' : (x - (x1 - a)) / a = 0 := by linarith
            rw [h', deriv2_st_zero_at_zero] <;> ring
        rw [h_d2φ, h_dφ, h_d2l0, hdl0]
        have h_simp : |(0 : ℝ) * L x + 2 * (0 : ℝ) * m| = (0 : ℝ) := by simp
        rw [h_simp]
        have h_goal : (0 : ℝ) ≤ A * ((|y1| + |y2|) / a^2 + |m| / a) := by positivity
        exact h_goal
      · have hL_bound : |L x| ≤ |y1| + a * |m| := by
          have h4 : |x - x1| ≤ a := by
            rw [abs_le] <;> constructor <;> linarith
          have hLx : L x = y1 + (x - x1) * m := by rw [hL] <;> simp only
          rw [hLx]
          have h5 : |y1 + (x - x1) * m| ≤ |y1| + |(x - x1) * m| := abs_add_le _ _
          have h6 : |(x - x1) * m| = |x - x1| * |m| := by rw [abs_mul]
          rw [h6] at h5
          have h7 : |y1| + |x - x1| * |m| ≤ |y1| + a * |m| := by gcongr <;> linarith
          exact le_trans h5 h7
        rw [h_d2φ, h_dφ]
        have h_bound1 : |deriv (deriv s_left) x| ≤ M2 / a^2 := h_left_bound2 x
        have h_bound2 : |deriv s_left x| ≤ M1 / a := h_left_bound1 x
        have h9 : |deriv (deriv s_left) x| * |L x| ≤
            (M2 / a^2) * (|y1| + a * |m|) :=
          mul_le_mul h_bound1 hL_bound (abs_nonneg _) (by positivity)
        have h10 : |deriv s_left x| * |m| ≤ (M1 / a) * |m| :=
          mul_le_mul_of_nonneg_right h_bound2 (abs_nonneg m)
        have h11 : |deriv (deriv s_left) x * L x + 2 * deriv s_left x * m| ≤
            |deriv (deriv s_left) x| * |L x| + 2 * |deriv s_left x| * |m| := by
          have h12 : |deriv (deriv s_left) x * L x + 2 * deriv s_left x * m| ≤
              |deriv (deriv s_left) x * L x| + |2 * deriv s_left x * m| := abs_add_le _ _
          have h13 : |2 * deriv s_left x * m| = 2 * |deriv s_left x| * |m| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)] <;> ring
          have h14 : |deriv (deriv s_left) x * L x| =
              |deriv (deriv s_left) x| * |L x| := by rw [abs_mul]
          rw [h14, h13] at h12
          exact h12
        have h15 : |deriv (deriv s_left) x| * |L x| + 2 * |deriv s_left x| * |m| ≤
            (M2 / a^2) * (|y1| + a * |m|) + 2 * (M1 / a) * |m| := by
          have h16 : 2 * |deriv s_left x| * |m| ≤ 2 * (M1 / a) * |m| := by
            have h17 : 0 ≤ |m| := abs_nonneg m
            have h18 : |deriv s_left x| * |m| ≤ (M1 / a) * |m| := h10
            linarith
          exact add_le_add h9 h16
        have h_main : |deriv (deriv s_left) x * L x + 2 * deriv s_left x * m| ≤
            M2 * |y1| / a^2 + (M2 + 2 * M1) * |m| / a := by
          have h19 := alg_identity1 M2 M1 a y1 m ha
          rw [h19] at h15
          exact le_trans h11 h15
        have h_final : M2 * |y1| / a^2 + (M2 + 2 * M1) * |m| / a ≤
            A * ((|y1| + |y2|) / a^2 + |m| / a) :=
          final_bound2 A M1 M2 y1 y2 a m ha hM1_nonneg hM2_nonneg hA1 hA_M22
        exact le_trans h_main h_final
    · have h1' : x1 < x := by linarith
      have hdl0 : deriv s_left x = 0 := h_dl_zero' x h1'
      have h_d2l0 : deriv (deriv s_left) x = 0 := h_d2l_zero' x h1'
      have hsl1 : s_left x = 1 := h_sl_one x (by linarith)
      by_cases h2 : x ≤ x2
      · have hsr0 : s_right x = 0 := h_sr_zero x h2
        have hdr0 : deriv s_right x = 0 :=
          dr_zero_at_or_before s_right x2 a x ha h_deriv_right h_dr_zero h2
        have h_d2r0 : deriv (deriv s_right) x = 0 :=
          d2r_zero_at_or_before s_right x2 a x ha h_deriv2_right h_d2r_zero h2
        have h_dφ : deriv φ x = 0 := by
          rw [h_deriv_φ x, hdl0, hsr0, hdr0] <;> ring
        have h_d2φ : deriv (deriv φ) x = 0 := by
          have h_eq := h_deriv2_φ x
          rw [h_eq, h_d2l0, hdl0, hsr0, hdr0, h_d2r0] <;> ring
        rw [h_d2φ, h_dφ]
        exact interior_second_deriv_bound A a ha hA1 y1 y2 m L x
      · have h2' : x2 < x := by linarith
        by_cases h3 : x ≤ x2 + a
        · have hL_bound : |L x| ≤ |y2| + a * |m| := by
            have h4 : |x - x2| ≤ a := by
              rw [abs_le] <;> constructor <;> linarith
            have h5 : L x = y2 + (x - x2) * m := by
              have hLx : L x = y1 + (x - x1) * m := by
                rw [hL] <;> simp only
              rw [hLx]
              have h6 : (x2 - x1) * m = y2 - y1 := by
                rw [hm]
                have hne : x2 - x1 ≠ 0 := by linarith
                field_simp [hne] <;> ring
              have h7 : y1 + (x - x1) * m = y2 + (x - x2) * m := by
                have h8 : (x - x1) = (x - x2) + (x2 - x1) := by ring
                rw [h8]
                rw [add_mul, h6] <;> ring
              exact h7
            rw [h5]
            have h9 : |y2 + (x - x2) * m| ≤ |y2| + |(x - x2) * m| := abs_add_le _ _
            have h10 : |(x - x2) * m| = |x - x2| * |m| := by rw [abs_mul]
            rw [h10] at h9
            have h11 : |y2| + |x - x2| * |m| ≤ |y2| + a * |m| := by
              gcongr <;> linarith
            exact le_trans h9 h11
          have h_dφ : deriv φ x = -deriv s_right x := by
            rw [h_deriv_φ x, hsl1, hdl0] <;> ring
          have h_d2φ : deriv (deriv φ) x = -deriv (deriv s_right) x := by
            have h_eq := h_deriv2_φ x
            rw [h_eq, h_d2l0, hdl0, hsl1] <;> ring
          rw [h_d2φ, h_dφ]
          set b1 := deriv (deriv s_right) x with hb1
          set b2 := deriv s_right x with hb2
          have h_bound1 : |b1| ≤ M2 / a^2 := h_right_bound2 x
          have h_bound2 : |b2| ≤ M1 / a := h_right_bound1 x
          have h9 : |b1| * |L x| ≤ (M2 / a^2) * (|y2| + a * |m|) :=
            mul_le_mul h_bound1 hL_bound (abs_nonneg _) (by positivity)
          have h10 : |b2| * |m| ≤ (M1 / a) * |m| :=
            mul_le_mul_of_nonneg_right h_bound2 (abs_nonneg m)
          have h11 : |(-b1) * L x + 2 * (-b2) * m| ≤
              |b1| * |L x| + 2 * |b2| * |m| := by
            have h12 : |(-b1) * L x + 2 * (-b2) * m| ≤
                |(-b1) * L x| + |2 * (-b2) * m| := abs_add_le _ _
            have h13 : |2 * (-b2) * m| = 2 * |b2| * |m| := by
              rw [show (2 * (-b2) * m) = -(2 * b2 * m) by ring]
              rw [abs_neg, abs_mul, abs_mul,
                abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)] <;> ring
            have h14 : |(-b1) * L x| = |b1| * |L x| := by rw [abs_mul, abs_neg]
            rw [h14, h13] at h12
            exact h12
          have h15 : |b1| * |L x| + 2 * |b2| * |m| ≤
              (M2 / a^2) * (|y2| + a * |m|) + 2 * (M1 / a) * |m| := by
            have h16 : 2 * |b2| * |m| ≤ 2 * (M1 / a) * |m| := by
              have h17 : 0 ≤ |m| := abs_nonneg m
              have h18 : |b2| * |m| ≤ (M1 / a) * |m| := h10
              linarith
            exact add_le_add h9 h16
          have h19 := alg_identity1 M2 M1 a y2 m ha
          have h_main : |(-b1) * L x + 2 * (-b2) * m| ≤
              M2 * |y2| / a^2 + (M2 + 2 * M1) * |m| / a := by
            rw [h19] at h15
            exact le_trans h11 h15
          have h_final :=
            final_bound2_right A M1 M2 y1 y2 a m ha hM1_nonneg hM2_nonneg hA1 hA_M22
          exact le_trans h_main h_final
        · have hsr1 : s_right x = 1 := h_sr_one x (by linarith)
          have hdr0 : deriv s_right x = 0 := h_dr_zero' x (by linarith)
          have h_d2r0 : deriv (deriv s_right) x = 0 := h_d2r_zero' x (by linarith)
          have hφ0 : φ x = 0 := by
            rw [hφ_eq x, hsl1, hsr1] <;> ring
          have h_dφ : deriv φ x = 0 := by
            rw [h_deriv_φ x, hsl1, hdl0, hdr0] <;> ring
          have h_d2φ : deriv (deriv φ) x = 0 := by
            have h_eq := h_deriv2_φ x
            rw [h_eq, h_d2l0, hdl0, hsr1, hdr0, h_d2r0] <;> ring
          rw [h_d2φ, h_dφ]
          have h_simp : |(0 : ℝ) * L x + 2 * (0 : ℝ) * m| = (0 : ℝ) := by simp
          rw [h_simp]
          have h_goal : (0 : ℝ) ≤ A * ((|y1| + |y2|) / a^2 + |m| / a) := by positivity
          exact h_goal

end Kakeya.Assouad
