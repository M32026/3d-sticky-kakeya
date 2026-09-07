/-
# Directional Variation Lemmas

Auxiliary results for directional variation: lower semicontinuity under
L¹_loc convergence and scaling behavior.

## Main results

- `directionalVariation_lowerSemicontinuity`: L¹_loc convergence implies
  lower semicontinuity of directional variation
- `directionalVariation_scaling`: `directionalVariation (t•S) w = t^(n-1) · directionalVariation S w`

## References

- Maggi, Sets of Finite Perimeter, Theorem 15.5
- Ambrosio-Fusco-Pallara, Functions of BV, Theorem 3.59
-/

import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.LowerSemicontinuity
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.Perimeter

variable {n : ℕ}

/-- **Lower semicontinuity of directional variation under L¹_loc convergence.**

If `E_k → F` in L¹_loc (symmetric difference volume → 0 on every compact set),
then `directionalVariation F w ≤ liminf directionalVariation E_k w` for every
direction `w`. -/
lemma directionalVariation_lowerSemicontinuity
    {F : Set (E n)} (hF : MeasurableSet F)
    {E_seq : ℕ → Set (E n)} (hE : ∀ k, MeasurableSet (E_seq k))
    (h_conv : ∀ (K : Set (E n)), IsCompact K →
      Tendsto (fun k => volume (symmDiff (E_seq k) F ∩ K)) atTop (nhds 0))
    (w : E n) :
    directionalVariation F w ≤
      Filter.liminf (fun k => directionalVariation (E_seq k) w) Filter.atTop := by
  apply iSup_le
  intro φ
  let f : E n → ℝ := fun x => fderiv ℝ φ.toFun x w

  -- f is continuous
  have hdiff : ContDiff ℝ 1 φ.toFun := φ.smooth.of_le (by simp)
  have h_cfderiv : Continuous (fderiv ℝ φ.toFun) :=
    hdiff.continuous_fderiv (by norm_num)
  let eval_w : ((E n) →L[ℝ] ℝ) → ℝ := fun g => g w
  have h_eval : Continuous eval_w := continuous_eval_const w
  have hf_cont : Continuous f := h_eval.comp h_cfderiv

  -- f has compact support
  have hf_support : HasCompactSupport f := by
    have h1 : ∀ (x : E n), x ∉ tsupport φ.toFun → f x = 0 := by
      intro x hx
      have h21 : φ.toFun =ᶠ[nhds x] 0 := by
        have h_open : IsOpen (tsupport φ.toFun)ᶜ := isClosed_tsupport _ |>.isOpen_compl
        have h_nhds : (tsupport φ.toFun)ᶜ ∈ nhds x := h_open.mem_nhds hx
        filter_upwards [h_nhds] with y hy
        have h3 : y ∉ Function.support φ.toFun := fun h => hy (subset_closure h)
        simpa [Function.mem_support] using h3
      have h2 : fderiv ℝ φ.toFun x = 0 := by
        have h_fd : HasFDerivAt φ.toFun (0 : (E n →L[ℝ] ℝ)) x :=
          hasFDerivAt_zero_of_eventually_const (0 : ℝ) h21
        exact h_fd.fderiv
      simpa [f] using congr_arg (fun L : (E n →L[ℝ] ℝ) => L w) h2
    have h3 : Function.support f ⊆ tsupport φ.toFun := by
      intro x hx
      by_contra h4
      exact hx (h1 x h4)
    have h4_φ : IsClosed (tsupport φ.toFun) := isClosed_tsupport _
    have h5 : tsupport f ⊆ tsupport φ.toFun := closure_minimal h3 h4_φ
    have h4_f : IsClosed (tsupport f) := isClosed_tsupport _
    exact φ.compact.of_isClosed_subset h4_f h5

  let K := tsupport f
  have hK : IsCompact K := hf_support
  have h_convK : Tendsto (fun k => volume (symmDiff F (E_seq k) ∩ K)) atTop (nhds 0) := by
    have h_eq : ∀ k, symmDiff (E_seq k) F = symmDiff F (E_seq k) := by
      intro k; ext x; simp [symmDiff] <;> tauto
    have h := h_conv K hK
    simpa [h_eq] using h
  have h_integral_conv : Tendsto (fun k => ∫ x in E_seq k, f x) atTop (nhds (∫ x in F, f x)) :=
    integral_set_convergence hf_cont hf_support hF hE h_convK

  let a : ℕ → ENNReal := fun k => ENNReal.ofReal |∫ x in E_seq k, f x|
  let b : ℕ → ENNReal := fun k => directionalVariation (E_seq k) w
  let a_limit : ENNReal := ENNReal.ofReal |∫ x in F, f x|

  have h3 : ∀ k, a k ≤ b k := by
    intro k
    exact le_iSup (fun (ψ : TestScalar) =>
      ENNReal.ofReal |∫ x in E_seq k, fderiv ℝ ψ.toFun x w|) φ

  have h_ofReal_abs : Continuous (fun x : ℝ => ENNReal.ofReal |x|) := by
    have h1 : (fun x : ℝ => ENNReal.ofReal |x|) = fun x : ℝ => ((|x|.toNNReal : NNReal) : ENNReal) := by
      funext x
      have h2 : 0 ≤ |x| := abs_nonneg x
      simp [ENNReal.ofReal_eq_coe_nnreal, h2] <;> rfl
    rw [h1]
    have h3 : Continuous (fun x : ℝ => (|x|.toNNReal : NNReal)) := by fun_prop
    have h4 : Continuous (fun r : NNReal => (r : ENNReal)) := ENNReal.continuous_coe
    exact h4.comp h3

  have h4 : Tendsto a atTop (nhds a_limit) :=
    h_ofReal_abs.continuousAt.tendsto.comp h_integral_conv

  have h3' : ∀ᶠ k in Filter.atTop, a k ≤ b k := by
    filter_upwards with k
    exact h3 k

  have h_main : a_limit ≤ Filter.liminf b Filter.atTop := by
    apply ENNReal.le_of_forall_nnreal_lt
    intro r hr
    have h_r_lt : (r : ENNReal) < a_limit := by exact_mod_cast hr
    have h1 : ∀ᶠ k in Filter.atTop, (r : ENNReal) ≤ a k := by
      have h_nhds : Set.Ioi (r : ENNReal) ∈ nhds a_limit := Ioi_mem_nhds h_r_lt
      have h2 : ∀ᶠ k in Filter.atTop, a k ∈ Set.Ioi (r : ENNReal) := h4.eventually h_nhds
      filter_upwards [h2] with k hk
      exact le_of_lt hk
    have h2 : ∀ᶠ k in Filter.atTop, (r : ENNReal) ≤ b k := by
      filter_upwards [h1, h3'] with k h1k h3k
      exact le_trans h1k h3k
    have h3 : (r : ENNReal) ∈ {c : ENNReal | ∀ᶠ k in Filter.atTop, c ≤ b k} := h2
    exact le_sSup h3
  exact h_main

/-- **Scaling of directional variation.**

For `t > 0`, `directionalVariation (t • S) w = t^(n-1) · directionalVariation S w`. -/
lemma directionalVariation_scaling (S : Set (E n)) (hS : MeasurableSet S)
    {t : ℝ} (ht : 0 < t) (hn : 1 ≤ n) (w : E n) :
    directionalVariation (scaleSet t S) w =
      ENNReal.ofReal (t ^ (n - 1)) * directionalVariation S w := by
  have hfinrank : Module.finrank ℝ (E n) = n := by simp
  have ht_ne : t ≠ 0 := ht.ne'
  have h_pow : t ^ n = t * t ^ (n - 1) := by
    cases n with
    | zero => contradiction
    | succ n' => simp [pow_succ] <;> ring
  let hmap_fwd : E n → E n := fun x => t • x
  let hmap_inv : E n → E n := fun x => t⁻¹ • x

  -- Compact support of φ(t • ·)
  have h_compact_scaled : ∀ (φ : TestScalar), HasCompactSupport (fun x : E n => φ.toFun (t • x)) := by
    intro φ
    have h_sub : Function.support (fun x : E n => φ.toFun (t • x)) ⊆ hmap_inv '' tsupport φ.toFun := by
      intro x hx
      have h1 : φ.toFun (t • x) ≠ 0 := hx
      have h2 : t • x ∈ Function.support φ.toFun := h1
      have h3 : t • x ∈ tsupport φ.toFun := subset_tsupport (f := φ.toFun) h2
      refine ⟨t • x, h3, ?_⟩
      have h4 : hmap_inv (t • x) = x := by
        simp [hmap_inv, smul_smul] <;> field_simp [ht_ne] <;> simp [one_smul]
      exact h4
    have h_img_compact : IsCompact (hmap_inv '' tsupport φ.toFun) :=
      φ.compact.image (by fun_prop)
    have h_closed : IsClosed (hmap_inv '' tsupport φ.toFun) := h_img_compact.isClosed
    have h_ts : tsupport (fun x : E n => φ.toFun (t • x)) ⊆ hmap_inv '' tsupport φ.toFun :=
      closure_minimal h_sub h_closed
    exact h_img_compact.of_isClosed_subset (isClosed_tsupport _) h_ts

  -- Compact support of ψ(t⁻¹ • ·)
  have h_compact_unscaled : ∀ (ψ : TestScalar), HasCompactSupport (fun x : E n => ψ.toFun (t⁻¹ • x)) := by
    intro ψ
    have h_sub : Function.support (fun x : E n => ψ.toFun (t⁻¹ • x)) ⊆ hmap_fwd '' tsupport ψ.toFun := by
      intro x hx
      have h1 : ψ.toFun (t⁻¹ • x) ≠ 0 := hx
      have h2 : t⁻¹ • x ∈ Function.support ψ.toFun := h1
      have h3 : t⁻¹ • x ∈ tsupport ψ.toFun := subset_tsupport (f := ψ.toFun) h2
      refine ⟨t⁻¹ • x, h3, ?_⟩
      have h4 : hmap_fwd (t⁻¹ • x) = x := by
        simp [hmap_fwd, smul_smul] <;> field_simp [ht_ne] <;> simp [one_smul]
      exact h4
    have h_img_compact : IsCompact (hmap_fwd '' tsupport ψ.toFun) :=
      ψ.compact.image (by fun_prop)
    have h_closed : IsClosed (hmap_fwd '' tsupport ψ.toFun) := h_img_compact.isClosed
    have h_ts : tsupport (fun x : E n => ψ.toFun (t⁻¹ • x)) ⊆ hmap_fwd '' tsupport ψ.toFun :=
      closure_minimal h_sub h_closed
    exact h_img_compact.of_isClosed_subset (isClosed_tsupport _) h_ts

  -- Helper: fderiv of scaled function
  have h_fderiv_scaled : ∀ (φ : TestScalar) (x : E n),
      fderiv ℝ (fun x : E n => φ.toFun (t • x)) x w = t * fderiv ℝ φ.toFun (t • x) w := by
    intro φ x
    have h_diff : DifferentiableAt ℝ φ.toFun (t • x) :=
      φ.smooth.differentiable (by norm_num) (t • x)
    have h_chain : HasFDerivAt (fun x : E n => φ.toFun (t • x))
        ((fderiv ℝ φ.toFun (t • x)).comp (t • ContinuousLinearMap.id ℝ (E n))) x :=
      h_diff.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul t)
    have h_eq : fderiv ℝ (fun x : E n => φ.toFun (t • x)) x =
        (fderiv ℝ φ.toFun (t • x)).comp (t • ContinuousLinearMap.id ℝ (E n)) :=
      h_chain.fderiv
    rw [h_eq]
    have h_eval : (fderiv ℝ φ.toFun (t • x)).comp (t • ContinuousLinearMap.id ℝ (E n)) w =
        fderiv ℝ φ.toFun (t • x) (t • w) := by rfl
    rw [h_eval]
    have h_lin : fderiv ℝ φ.toFun (t • x) (t • w) = t * fderiv ℝ φ.toFun (t • x) w := by
      exact map_smul (fderiv ℝ φ.toFun (t • x)) t w
    rw [h_lin]

  have h_fderiv_unscaled : ∀ (ψ : TestScalar) (x : E n),
      fderiv ℝ (fun x : E n => ψ.toFun (t⁻¹ • x)) x w = t⁻¹ * fderiv ℝ ψ.toFun (t⁻¹ • x) w := by
    intro ψ x
    have h_diff : DifferentiableAt ℝ ψ.toFun (t⁻¹ • x) :=
      ψ.smooth.differentiable (by norm_num) (t⁻¹ • x)
    have h_chain : HasFDerivAt (fun x : E n => ψ.toFun (t⁻¹ • x))
        ((fderiv ℝ ψ.toFun (t⁻¹ • x)).comp (t⁻¹ • ContinuousLinearMap.id ℝ (E n))) x :=
      h_diff.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul t⁻¹)
    have h_eq : fderiv ℝ (fun x : E n => ψ.toFun (t⁻¹ • x)) x =
        (fderiv ℝ ψ.toFun (t⁻¹ • x)).comp (t⁻¹ • ContinuousLinearMap.id ℝ (E n)) :=
      h_chain.fderiv
    rw [h_eq]
    have h_eval : (fderiv ℝ ψ.toFun (t⁻¹ • x)).comp (t⁻¹ • ContinuousLinearMap.id ℝ (E n)) w =
        fderiv ℝ ψ.toFun (t⁻¹ • x) (t⁻¹ • w) := by rfl
    rw [h_eval]
    have h_lin : fderiv ℝ ψ.toFun (t⁻¹ • x) (t⁻¹ • w) = t⁻¹ * fderiv ℝ ψ.toFun (t⁻¹ • x) w := by
      exact map_smul (fderiv ℝ ψ.toFun (t⁻¹ • x)) t⁻¹ w
    rw [h_lin]

  -- Direction 1: ≤
  have h1 : directionalVariation (scaleSet t S) w ≤
      ENNReal.ofReal (t ^ (n - 1)) * directionalVariation S w := by
    apply iSup_le
    intro φ
    let ψ : TestScalar :=
      { toFun := fun x => φ.toFun (t • x)
        smooth := φ.smooth.comp (contDiff_id.const_smul t)
        compact := h_compact_scaled φ
        bound := fun x => φ.bound (t • x) }
    have h_fderiv : ∀ x : E n, fderiv ℝ ψ.toFun x w = t * fderiv ℝ φ.toFun (t • x) w :=
      h_fderiv_scaled φ
    have h_change : ∫ x in scaleSet t S, fderiv ℝ φ.toFun x w =
        (t ^ n) * ∫ x in S, fderiv ℝ φ.toFun (t • x) w := by
      have h : ∫ x in S, fderiv ℝ φ.toFun (t • x) w =
          (t ^ n)⁻¹ * ∫ x in scaleSet t S, fderiv ℝ φ.toFun x w := by
        rw [MeasureTheory.Measure.setIntegral_comp_smul volume (fun y => fderiv ℝ φ.toFun y w) S ht_ne]
        rw [hfinrank]
        have h_abs : |(t ^ n)⁻¹| = (t ^ n)⁻¹ := by
          rw [abs_of_nonneg] <;> positivity
        rw [h_abs] <;> rfl
      field_simp [ht_ne] at h ⊢ <;> linarith
    have h2 : ∫ x in S, fderiv ℝ ψ.toFun x w = ∫ x in S, t * fderiv ℝ φ.toFun (t • x) w := by
      congr with x; exact h_fderiv x
    have h_eq : ∫ x in scaleSet t S, fderiv ℝ φ.toFun x w =
        (t ^ (n - 1)) * (∫ x in S, fderiv ℝ ψ.toFun x w) := by
      rw [h_change, h2, integral_const_mul, h_pow] <;> ring
    rw [h_eq]
    have h_abs : |t ^ (n - 1) * ∫ x in S, fderiv ℝ ψ.toFun x w| =
        t ^ (n - 1) * |∫ x in S, fderiv ℝ ψ.toFun x w| := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
    have h3 : ENNReal.ofReal |t ^ (n - 1) * ∫ x in S, fderiv ℝ ψ.toFun x w| =
        ENNReal.ofReal (t ^ (n - 1)) * ENNReal.ofReal |∫ x in S, fderiv ℝ ψ.toFun x w| := by
      rw [h_abs, ← ENNReal.ofReal_mul (by positivity)] <;> rfl
    rw [h3]
    exact mul_le_mul_of_nonneg_left
      (le_iSup (fun (θ : TestScalar) =>
        ENNReal.ofReal |∫ x in S, fderiv ℝ θ.toFun x w|) ψ)
      (by positivity)

  -- Direction 2: ≥
  have h2 : ENNReal.ofReal (t ^ (n - 1)) * directionalVariation S w ≤
      directionalVariation (scaleSet t S) w := by
    have h_iSup : ENNReal.ofReal (t ^ (n - 1)) * directionalVariation S w =
        iSup fun (ψ : TestScalar) =>
          ENNReal.ofReal (t ^ (n - 1)) * ENNReal.ofReal |∫ x in S, fderiv ℝ ψ.toFun x w| := by
      rw [directionalVariation, ENNReal.mul_iSup] <;> rfl
    rw [h_iSup]
    apply iSup_le
    intro ψ
    let φ : TestScalar :=
      { toFun := fun x => ψ.toFun (t⁻¹ • x)
        smooth := ψ.smooth.comp (contDiff_id.const_smul t⁻¹)
        compact := h_compact_unscaled ψ
        bound := fun x => ψ.bound (t⁻¹ • x) }
    have h_fderiv : ∀ x : E n, fderiv ℝ φ.toFun x w = t⁻¹ * fderiv ℝ ψ.toFun (t⁻¹ • x) w :=
      h_fderiv_unscaled ψ
    let g : E n → ℝ := fun y => fderiv ℝ ψ.toFun (t⁻¹ • y) w
    have h_g : ∀ x : E n, g (t • x) = fderiv ℝ ψ.toFun x w := by
      intro x
      have h_smul : t⁻¹ • (t • x) = x := by
        have h : t⁻¹ • (t • x) = (t⁻¹ * t) • x := by rw [smul_smul]
        have h_mul : t⁻¹ * t = 1 := by field_simp [ht_ne]
        rw [h, h_mul, one_smul]
      simp [g, h_smul]
    have h_comp_smul : ∫ x in S, g (t • x) = (t ^ n)⁻¹ * ∫ x in scaleSet t S, g x := by
      rw [MeasureTheory.Measure.setIntegral_comp_smul volume g S ht_ne]
      rw [hfinrank]
      have h_abs : |(t ^ n)⁻¹| = (t ^ n)⁻¹ := by
        rw [abs_of_nonneg] <;> positivity
      rw [h_abs] <;> rfl
    have h_S_eq : ∫ x in S, fderiv ℝ ψ.toFun x w = (t ^ n)⁻¹ * ∫ x in scaleSet t S, g x := by
      have h_eq : ∫ x in S, g (t • x) = ∫ x in S, fderiv ℝ ψ.toFun x w := by
        congr with x; exact h_g x
      rw [h_eq] at h_comp_smul
      exact h_comp_smul
    have h_change : ∫ x in scaleSet t S, g x = t ^ n * ∫ x in S, fderiv ℝ ψ.toFun x w := by
      field_simp [ht_ne] at h_S_eq ⊢ <;> exact h_S_eq.symm
    have h_int_φ : ∫ x in scaleSet t S, fderiv ℝ φ.toFun x w =
        t ^ (n - 1) * ∫ x in S, fderiv ℝ ψ.toFun x w := by
      have h3 : ∫ x in scaleSet t S, fderiv ℝ φ.toFun x w =
          ∫ x in scaleSet t S, t⁻¹ * g x := by
        congr with x; exact h_fderiv x
      rw [h3, integral_const_mul, h_change]
      have h4 : t⁻¹ * (t ^ n * ∫ x in S, fderiv ℝ ψ.toFun x w) =
          t ^ (n - 1) * ∫ x in S, fderiv ℝ ψ.toFun x w := by
        rw [h_pow]
        field_simp [ht_ne] <;> ring
      exact h4
    have h_pos : 0 < t ^ (n - 1) := by positivity
    have h_abs2 : |∫ x in scaleSet t S, fderiv ℝ φ.toFun x w| =
        t ^ (n - 1) * |∫ x in S, fderiv ℝ ψ.toFun x w| := by
      rw [h_int_φ, abs_mul, abs_of_pos h_pos]
    have h_main : ENNReal.ofReal (t ^ (n - 1)) * ENNReal.ofReal |∫ x in S, fderiv ℝ ψ.toFun x w| =
        ENNReal.ofReal |∫ x in scaleSet t S, fderiv ℝ φ.toFun x w| := by
      rw [h_abs2]
      have h5 : 0 ≤ t ^ (n - 1) := by positivity
      rw [← ENNReal.ofReal_mul h5] <;> rfl
    rw [h_main]
    exact le_iSup (fun (θ : TestScalar) =>
      ENNReal.ofReal |∫ x in scaleSet t S, fderiv ℝ θ.toFun x w|) φ

  exact le_antisymm h1 h2

-- ============================================================================
-- Local directional variation
-- ============================================================================

/-- **Local directional variation** of `S` in direction `w` within `Ω`.

`V(S, w; Ω) = sup { |∫_S D_w φ| : φ ∈ C_c^∞(Ω), |φ| ≤ 1 }`.

This is the localized version of `directionalVariation`, essential for the
blow-up analysis at reduced boundary points where global variation diverges. -/
noncomputable def directionalVariationIn (S : Set (E n)) (w : E n) (Ω : Set (E n)) : ENNReal :=
  iSup fun (φ : {φ : TestScalar // Function.support φ.toFun ⊆ Ω}) =>
    ENNReal.ofReal |∫ x in S, fderiv ℝ φ.val.toFun x w|

/-- Local variation is monotone in the domain `Ω`. -/
lemma directionalVariationIn_mono (S : Set (E n)) (w : E n) {Ω₁ Ω₂ : Set (E n)}
    (h : Ω₁ ⊆ Ω₂) :
    directionalVariationIn S w Ω₁ ≤ directionalVariationIn S w Ω₂ := by
  apply iSup_le
  intro φ
  have h2 : Function.support φ.val.toFun ⊆ Ω₂ := subset_trans φ.property h
  exact le_iSup (fun (ψ : {φ : TestScalar // Function.support φ.toFun ⊆ Ω₂}) =>
    ENNReal.ofReal |∫ x in S, fderiv ℝ ψ.val.toFun x w|) ⟨φ.val, h2⟩

/-- Global variation equals local variation on `univ`. -/
lemma directionalVariationIn_univ (S : Set (E n)) (w : E n) :
    directionalVariationIn S w Set.univ = directionalVariation S w := by
  apply le_antisymm
  · apply iSup_le
    intro φ
    exact le_iSup (fun (ψ : TestScalar) => ENNReal.ofReal |∫ x in S, fderiv ℝ ψ.toFun x w|) φ.val
  · apply iSup_le
    intro φ
    have h_support : Function.support φ.toFun ⊆ (Set.univ : Set (E n)) := Set.subset_univ _
    exact le_iSup (fun (ψ : {φ : TestScalar // Function.support φ.toFun ⊆ Set.univ}) =>
      ENNReal.ofReal |∫ x in S, fderiv ℝ ψ.val.toFun x w|) ⟨φ, h_support⟩

/-- **Lower semicontinuity of local directional variation under L¹_loc convergence.**

If `E_k → F` in L¹_loc (symmetric difference volume → 0 on every compact set),
then `directionalVariationIn F w Ω ≤ liminf directionalVariationIn E_k w Ω`
for every direction `w` and open set `Ω`. -/
lemma directionalVariationIn_lowerSemicontinuity
    {F : Set (E n)} (hF : MeasurableSet F)
    {E_seq : ℕ → Set (E n)} (hE : ∀ k, MeasurableSet (E_seq k))
    (h_conv : ∀ (K : Set (E n)), IsCompact K →
      Tendsto (fun k => volume (symmDiff (E_seq k) F ∩ K)) atTop (nhds 0))
    (w : E n) (Ω : Set (E n)) :
    directionalVariationIn F w Ω ≤
      Filter.liminf (fun k => directionalVariationIn (E_seq k) w Ω) Filter.atTop := by
  apply iSup_le
  intro φ
  let f : E n → ℝ := fun x => fderiv ℝ φ.val.toFun x w

  -- f is continuous
  have hdiff : ContDiff ℝ 1 φ.val.toFun := φ.val.smooth.of_le (by simp)
  have h_cfderiv : Continuous (fderiv ℝ φ.val.toFun) :=
    hdiff.continuous_fderiv (by norm_num)
  let eval_w : ((E n) →L[ℝ] ℝ) → ℝ := fun g => g w
  have h_eval : Continuous eval_w := continuous_eval_const w
  have hf_cont : Continuous f := h_eval.comp h_cfderiv

  -- f has compact support contained in Ω
  have hf_support : HasCompactSupport f := by
    have h1 : ∀ (x : E n), x ∉ tsupport φ.val.toFun → f x = 0 := by
      intro x hx
      have h2 : fderiv ℝ φ.val.toFun x = 0 := fderiv_of_notMem_tsupport ℝ hx
      simpa [f] using congr_arg (fun L : (E n →L[ℝ] ℝ) => L w) h2
    have h3 : Function.support f ⊆ tsupport φ.val.toFun := by
      intro x hx
      by_contra h4
      exact hx (h1 x h4)
    have h4_φ : IsClosed (tsupport φ.val.toFun) := isClosed_tsupport _
    have h5 : tsupport f ⊆ tsupport φ.val.toFun := closure_minimal h3 h4_φ
    have h4_f : IsClosed (tsupport f) := isClosed_tsupport _
    exact φ.val.compact.of_isClosed_subset h4_f h5

  let K := tsupport f
  have hK : IsCompact K := hf_support
  have h_convK : Tendsto (fun k => volume (symmDiff F (E_seq k) ∩ K)) atTop (nhds 0) := by
    have h_eq : ∀ k, symmDiff (E_seq k) F = symmDiff F (E_seq k) := by
      intro k; ext x; simp [symmDiff] <;> tauto
    have h := h_conv K hK
    simpa [h_eq] using h
  have h_integral_conv : Tendsto (fun k => ∫ x in E_seq k, f x) atTop (nhds (∫ x in F, f x)) :=
    integral_set_convergence hf_cont hf_support hF hE h_convK

  let a : ℕ → ENNReal := fun k => ENNReal.ofReal |∫ x in E_seq k, f x|
  let b : ℕ → ENNReal := fun k => directionalVariationIn (E_seq k) w Ω
  let a_limit : ENNReal := ENNReal.ofReal |∫ x in F, f x|

  have h3 : ∀ k, a k ≤ b k := by
    intro k
    exact le_iSup (fun (ψ : {φ : TestScalar // Function.support φ.toFun ⊆ Ω}) =>
      ENNReal.ofReal |∫ x in E_seq k, fderiv ℝ ψ.val.toFun x w|) φ

  have h_ofReal_abs : Continuous (fun x : ℝ => ENNReal.ofReal |x|) := by
    have h1 : (fun x : ℝ => ENNReal.ofReal |x|) = fun x : ℝ => ((|x|.toNNReal : NNReal) : ENNReal) := by
      funext x
      have h2 : 0 ≤ |x| := abs_nonneg x
      simp [ENNReal.ofReal_eq_coe_nnreal, h2] <;> rfl
    rw [h1]
    have h3 : Continuous (fun x : ℝ => (|x|.toNNReal : NNReal)) := by fun_prop
    have h4 : Continuous (fun r : NNReal => (r : ENNReal)) := ENNReal.continuous_coe
    exact h4.comp h3

  have h4 : Tendsto a atTop (nhds a_limit) :=
    h_ofReal_abs.continuousAt.tendsto.comp h_integral_conv

  have h3' : ∀ᶠ k in Filter.atTop, a k ≤ b k := by
    filter_upwards with k
    exact h3 k

  have h_main : a_limit ≤ Filter.liminf b Filter.atTop := by
    apply ENNReal.le_of_forall_nnreal_lt
    intro r hr
    have h_r_lt : (r : ENNReal) < a_limit := by exact_mod_cast hr
    have h1 : ∀ᶠ k in Filter.atTop, (r : ENNReal) ≤ a k := by
      have h_nhds : Set.Ioi (r : ENNReal) ∈ nhds a_limit := Ioi_mem_nhds h_r_lt
      have h2 : ∀ᶠ k in Filter.atTop, a k ∈ Set.Ioi (r : ENNReal) := h4.eventually h_nhds
      filter_upwards [h2] with k hk
      exact le_of_lt hk
    have h2 : ∀ᶠ k in Filter.atTop, (r : ENNReal) ≤ b k := by
      filter_upwards [h1, h3'] with k h1k h3k
      exact le_trans h1k h3k
    have h3 : (r : ENNReal) ∈ {c : ENNReal | ∀ᶠ k in Filter.atTop, c ≤ b k} := h2
    exact le_sSup h3
  exact h_main

/-- If local directional variation vanishes on every compact set, then global
directional variation vanishes. -/
lemma directionalVariationIn_all_compact_zero {F : Set (E n)} (hF : MeasurableSet F) (w : E n)
    (h : ∀ (K : Set (E n)), IsCompact K → directionalVariationIn F w K = 0) :
    directionalVariation F w = 0 := by
  have h_main : directionalVariation F w ≤ 0 := by
    rw [← directionalVariationIn_univ F w]
    apply iSup_le
    intro φ
    let K := tsupport φ.val.toFun
    have hK : IsCompact K := φ.val.compact
    have h0 : directionalVariationIn F w K = 0 := h K hK
    have h1 : Function.support φ.val.toFun ⊆ K := subset_closure
    have h2 : ENNReal.ofReal |∫ x in F, fderiv ℝ φ.val.toFun x w| ≤ directionalVariationIn F w K := by
      exact le_iSup (fun (ψ : {φ : TestScalar // Function.support φ.toFun ⊆ K}) =>
        ENNReal.ofReal |∫ x in F, fderiv ℝ ψ.val.toFun x w|) ⟨φ.val, h1⟩
    rw [h0] at h2
    exact h2
  have h_nonneg : 0 ≤ directionalVariation F w := by positivity
  exact le_antisymm h_main h_nonneg

/-- **Scaling of local directional variation.**

`directionalVariationIn (scaleSet t S) w (scaleSet t Ω) = t^(n-1) * directionalVariationIn S w Ω`.
-/
lemma directionalVariationIn_scaling (S : Set (E n)) (hS : MeasurableSet S)
    {t : ℝ} (ht : 0 < t) (hn : 1 ≤ n) (w : E n) (Ω : Set (E n)) :
    directionalVariationIn (scaleSet t S) w (scaleSet t Ω) =
      ENNReal.ofReal (t ^ (n - 1)) * directionalVariationIn S w Ω := by
  have ht_ne : t ≠ 0 := ht.ne'
  have hfinrank : Module.finrank ℝ (E n) = n := by simp
  have h_pow : t ^ n = t * t ^ (n - 1) := by
    cases n with
    | zero => contradiction
    | succ n' => simp [pow_succ] <;> ring
  let hmap_fwd : E n → E n := fun x => t • x
  let hmap_inv : E n → E n := fun x => t⁻¹ • x

  have h_compact_scaled : ∀ (φ : TestScalar),
      HasCompactSupport (fun x : E n => φ.toFun (t • x)) := by
    intro φ
    have h_sub : Function.support (fun x : E n => φ.toFun (t • x)) ⊆ hmap_inv '' tsupport φ.toFun := by
      intro x hx
      have h1 : φ.toFun (t • x) ≠ 0 := hx
      have h2 : t • x ∈ Function.support φ.toFun := h1
      have h3 : t • x ∈ tsupport φ.toFun := subset_closure h2
      refine ⟨t • x, h3, ?_⟩
      have h4 : hmap_inv (t • x) = x := by
        simp [hmap_inv, smul_smul] <;> field_simp [ht_ne] <;> simp [one_smul]
      exact h4
    have h_img_compact : IsCompact (hmap_inv '' tsupport φ.toFun) :=
      φ.compact.image (by fun_prop)
    have h_closed : IsClosed (hmap_inv '' tsupport φ.toFun) := h_img_compact.isClosed
    have h_ts : tsupport (fun x : E n => φ.toFun (t • x)) ⊆ hmap_inv '' tsupport φ.toFun :=
      closure_minimal h_sub h_closed
    exact h_img_compact.of_isClosed_subset (isClosed_tsupport _) h_ts

  have h_compact_unscaled : ∀ (ψ : TestScalar),
      HasCompactSupport (fun x : E n => ψ.toFun (t⁻¹ • x)) := by
    intro ψ
    have h_sub : Function.support (fun x : E n => ψ.toFun (t⁻¹ • x)) ⊆ hmap_fwd '' tsupport ψ.toFun := by
      intro x hx
      have h1 : ψ.toFun (t⁻¹ • x) ≠ 0 := hx
      have h2 : t⁻¹ • x ∈ Function.support ψ.toFun := h1
      have h3 : t⁻¹ • x ∈ tsupport ψ.toFun := subset_closure h2
      refine ⟨t⁻¹ • x, h3, ?_⟩
      have h4 : hmap_fwd (t⁻¹ • x) = x := by
        simp [hmap_fwd, smul_smul] <;> field_simp [ht_ne] <;> simp [one_smul]
      exact h4
    have h_img_compact : IsCompact (hmap_fwd '' tsupport ψ.toFun) :=
      ψ.compact.image (by fun_prop)
    have h_closed : IsClosed (hmap_fwd '' tsupport ψ.toFun) := h_img_compact.isClosed
    have h_ts : tsupport (fun x : E n => ψ.toFun (t⁻¹ • x)) ⊆ hmap_fwd '' tsupport ψ.toFun :=
      closure_minimal h_sub h_closed
    exact h_img_compact.of_isClosed_subset (isClosed_tsupport _) h_ts

  have h_fderiv_scaled : ∀ (φ : TestScalar) (x : E n),
      fderiv ℝ (fun x : E n => φ.toFun (t • x)) x w = t * fderiv ℝ φ.toFun (t • x) w := by
    intro φ x
    have h_diff : DifferentiableAt ℝ φ.toFun (t • x) :=
      φ.smooth.differentiable (by norm_num) (t • x)
    have h_chain : HasFDerivAt (fun x : E n => φ.toFun (t • x))
        ((fderiv ℝ φ.toFun (t • x)).comp (t • ContinuousLinearMap.id ℝ (E n))) x :=
      h_diff.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul t)
    have h_eq : fderiv ℝ (fun x : E n => φ.toFun (t • x)) x =
        (fderiv ℝ φ.toFun (t • x)).comp (t • ContinuousLinearMap.id ℝ (E n)) :=
      h_chain.fderiv
    rw [h_eq]
    have h_eval : (fderiv ℝ φ.toFun (t • x)).comp (t • ContinuousLinearMap.id ℝ (E n)) w =
        fderiv ℝ φ.toFun (t • x) (t • w) := by rfl
    rw [h_eval]
    have h_lin : fderiv ℝ φ.toFun (t • x) (t • w) = t * fderiv ℝ φ.toFun (t • x) w := by
      exact map_smul (fderiv ℝ φ.toFun (t • x)) t w
    rw [h_lin]

  have h_fderiv_unscaled : ∀ (ψ : TestScalar) (x : E n),
      fderiv ℝ (fun x : E n => ψ.toFun (t⁻¹ • x)) x w = t⁻¹ * fderiv ℝ ψ.toFun (t⁻¹ • x) w := by
    intro ψ x
    have h_diff : DifferentiableAt ℝ ψ.toFun (t⁻¹ • x) :=
      ψ.smooth.differentiable (by norm_num) (t⁻¹ • x)
    have h_chain : HasFDerivAt (fun x : E n => ψ.toFun (t⁻¹ • x))
        ((fderiv ℝ ψ.toFun (t⁻¹ • x)).comp (t⁻¹ • ContinuousLinearMap.id ℝ (E n))) x :=
      h_diff.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul t⁻¹)
    have h_eq : fderiv ℝ (fun x : E n => ψ.toFun (t⁻¹ • x)) x =
        (fderiv ℝ ψ.toFun (t⁻¹ • x)).comp (t⁻¹ • ContinuousLinearMap.id ℝ (E n)) :=
      h_chain.fderiv
    rw [h_eq]
    have h_eval : (fderiv ℝ ψ.toFun (t⁻¹ • x)).comp (t⁻¹ • ContinuousLinearMap.id ℝ (E n)) w =
        fderiv ℝ ψ.toFun (t⁻¹ • x) (t⁻¹ • w) := by rfl
    rw [h_eval]
    have h_lin : fderiv ℝ ψ.toFun (t⁻¹ • x) (t⁻¹ • w) = t⁻¹ * fderiv ℝ ψ.toFun (t⁻¹ • x) w := by
      exact map_smul (fderiv ℝ ψ.toFun (t⁻¹ • x)) t⁻¹ w
    rw [h_lin]

  -- Direction 1: ≤
  have h1 : directionalVariationIn (scaleSet t S) w (scaleSet t Ω) ≤
      ENNReal.ofReal (t ^ (n - 1)) * directionalVariationIn S w Ω := by
    apply iSup_le
    intro φ
    let ψ : {φ : TestScalar // Function.support φ.toFun ⊆ Ω} :=
      ⟨{ toFun := fun x => φ.val.toFun (t • x)
         smooth := φ.val.smooth.comp (contDiff_id.const_smul t)
         compact := h_compact_scaled φ.val
         bound := fun x => φ.val.bound (t • x) },
       fun x hx => by
         have h1 : φ.val.toFun (t • x) ≠ 0 := hx
         have h2 : t • x ∈ Function.support φ.val.toFun := h1
         have h3 : t • x ∈ scaleSet t Ω := φ.property h2
         rcases h3 with ⟨z, hz, h_eq⟩
         have h_zx : z = x := by
           have h : t • z = t • x := h_eq
           have h' : t⁻¹ • (t • z) = t⁻¹ • (t • x) := by rw [h]
           simpa [smul_smul, ht_ne] using h'
         rw [h_zx] at hz
         exact hz⟩
    have h_fderiv : ∀ x : E n, fderiv ℝ ψ.val.toFun x w = t * fderiv ℝ φ.val.toFun (t • x) w :=
      h_fderiv_scaled φ.val
    have h_change : ∫ x in scaleSet t S, fderiv ℝ φ.val.toFun x w =
        (t ^ n) * ∫ x in S, fderiv ℝ φ.val.toFun (t • x) w := by
      have h : ∫ x in S, fderiv ℝ φ.val.toFun (t • x) w =
          (t ^ n)⁻¹ * ∫ x in scaleSet t S, fderiv ℝ φ.val.toFun x w := by
        rw [MeasureTheory.Measure.setIntegral_comp_smul volume (fun y => fderiv ℝ φ.val.toFun y w) S ht_ne]
        rw [hfinrank]
        have h_abs : |(t ^ n)⁻¹| = (t ^ n)⁻¹ := by
          rw [abs_of_nonneg] <;> positivity
        rw [h_abs] <;> rfl
      field_simp [ht_ne] at h ⊢ <;> linarith
    have h2 : ∫ x in S, fderiv ℝ ψ.val.toFun x w = ∫ x in S, t * fderiv ℝ φ.val.toFun (t • x) w := by
      congr with x; exact h_fderiv x
    have h_eq : ∫ x in scaleSet t S, fderiv ℝ φ.val.toFun x w =
        (t ^ (n - 1)) * (∫ x in S, fderiv ℝ ψ.val.toFun x w) := by
      rw [h_change, h2, integral_const_mul, h_pow] <;> ring
    rw [h_eq]
    have h_abs : |t ^ (n - 1) * ∫ x in S, fderiv ℝ ψ.val.toFun x w| =
        t ^ (n - 1) * |∫ x in S, fderiv ℝ ψ.val.toFun x w| := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
    have h3 : ENNReal.ofReal |t ^ (n - 1) * ∫ x in S, fderiv ℝ ψ.val.toFun x w| =
        ENNReal.ofReal (t ^ (n - 1)) * ENNReal.ofReal |∫ x in S, fderiv ℝ ψ.val.toFun x w| := by
      rw [h_abs, ← ENNReal.ofReal_mul (by positivity)] <;> rfl
    rw [h3]
    exact mul_le_mul_of_nonneg_left
      (le_iSup (fun (θ : {φ : TestScalar // Function.support φ.toFun ⊆ Ω}) =>
        ENNReal.ofReal |∫ x in S, fderiv ℝ θ.val.toFun x w|) ψ)
      (by positivity)

  -- Direction 2: ≥
  have h2 : ENNReal.ofReal (t ^ (n - 1)) * directionalVariationIn S w Ω ≤
      directionalVariationIn (scaleSet t S) w (scaleSet t Ω) := by
    have h_iSup : ENNReal.ofReal (t ^ (n - 1)) * directionalVariationIn S w Ω =
        iSup fun (ψ : {φ : TestScalar // Function.support φ.toFun ⊆ Ω}) =>
          ENNReal.ofReal (t ^ (n - 1)) * ENNReal.ofReal |∫ x in S, fderiv ℝ ψ.val.toFun x w| := by
      rw [directionalVariationIn, ENNReal.mul_iSup] <;> rfl
    rw [h_iSup]
    apply iSup_le
    intro ψ
    let φ_fun : E n → ℝ := fun x => ψ.val.toFun (t⁻¹ • x)
    have h_compact_φ : HasCompactSupport φ_fun := by
      have h1 : Function.support φ_fun ⊆ hmap_fwd '' tsupport ψ.val.toFun := by
        intro x hx
        have h2 : ψ.val.toFun (t⁻¹ • x) ≠ 0 := hx
        have h3 : t⁻¹ • x ∈ Function.support ψ.val.toFun := h2
        have h4 : t⁻¹ • x ∈ tsupport ψ.val.toFun := subset_closure h3
        refine ⟨t⁻¹ • x, h4, ?_⟩
        have h5 : hmap_fwd (t⁻¹ • x) = x := by
          simp [hmap_fwd, smul_smul] <;> field_simp [ht_ne] <;> simp [one_smul]
        exact h5
      have h_img_compact : IsCompact (hmap_fwd '' tsupport ψ.val.toFun) :=
        ψ.val.compact.image (by fun_prop)
      have h_closed : IsClosed (hmap_fwd '' tsupport ψ.val.toFun) := h_img_compact.isClosed
      have h_ts : tsupport φ_fun ⊆ hmap_fwd '' tsupport ψ.val.toFun :=
        closure_minimal h1 h_closed
      exact h_img_compact.of_isClosed_subset (isClosed_tsupport _) h_ts
    let φ : {φ : TestScalar // Function.support φ.toFun ⊆ scaleSet t Ω} :=
      ⟨{ toFun := φ_fun
         smooth := ψ.val.smooth.comp (contDiff_id.const_smul t⁻¹)
         compact := h_compact_φ
         bound := fun x => ψ.val.bound (t⁻¹ • x) },
       fun x hx => by
         have h1 : ψ.val.toFun (t⁻¹ • x) ≠ 0 := hx
         have h2 : t⁻¹ • x ∈ Function.support ψ.val.toFun := h1
         have h3 : t⁻¹ • x ∈ Ω := ψ.property h2
         have h4 : t • (t⁻¹ • x) = x := by
           simp [hmap_fwd, smul_smul] <;> field_simp [ht_ne] <;> simp [one_smul]
         exact ⟨t⁻¹ • x, h3, h4⟩⟩
    have h_fderiv : ∀ x : E n, fderiv ℝ φ.val.toFun x w = t⁻¹ * fderiv ℝ ψ.val.toFun (t⁻¹ • x) w :=
      h_fderiv_unscaled ψ.val
    let g : E n → ℝ := fun y => fderiv ℝ ψ.val.toFun (t⁻¹ • y) w
    have h_g : ∀ x : E n, g (t • x) = fderiv ℝ ψ.val.toFun x w := by
      intro x
      have h_smul : t⁻¹ • (t • x) = x := by
        have h : t⁻¹ • (t • x) = (t⁻¹ * t) • x := by rw [smul_smul]
        have h_mul : t⁻¹ * t = 1 := by field_simp [ht_ne]
        rw [h, h_mul, one_smul]
      simp [g, h_smul]
    have h_comp_smul : ∫ x in S, g (t • x) = (t ^ n)⁻¹ * ∫ x in scaleSet t S, g x := by
      rw [MeasureTheory.Measure.setIntegral_comp_smul volume g S ht_ne]
      rw [hfinrank]
      have h_abs : |(t ^ n)⁻¹| = (t ^ n)⁻¹ := by
        rw [abs_of_nonneg] <;> positivity
      rw [h_abs] <;> rfl
    have h_S_eq : ∫ x in S, fderiv ℝ ψ.val.toFun x w = (t ^ n)⁻¹ * ∫ x in scaleSet t S, g x := by
      have h_eq : ∫ x in S, g (t • x) = ∫ x in S, fderiv ℝ ψ.val.toFun x w := by
        congr with x; exact h_g x
      rw [h_eq] at h_comp_smul
      exact h_comp_smul
    have h_change : ∫ x in scaleSet t S, g x = t ^ n * ∫ x in S, fderiv ℝ ψ.val.toFun x w := by
      field_simp [ht_ne] at h_S_eq ⊢ <;> exact h_S_eq.symm
    have h_int_φ : ∫ x in scaleSet t S, fderiv ℝ φ.val.toFun x w =
        t ^ (n - 1) * ∫ x in S, fderiv ℝ ψ.val.toFun x w := by
      have h3 : ∫ x in scaleSet t S, fderiv ℝ φ.val.toFun x w =
          ∫ x in scaleSet t S, t⁻¹ * g x := by
        congr with x; exact h_fderiv x
      rw [h3, integral_const_mul, h_change]
      have h4 : t⁻¹ * (t ^ n * ∫ x in S, fderiv ℝ ψ.val.toFun x w) =
          t ^ (n - 1) * ∫ x in S, fderiv ℝ ψ.val.toFun x w := by
        rw [h_pow]
        field_simp [ht_ne] <;> ring
      exact h4
    have h_pos : 0 < t ^ (n - 1) := by positivity
    have h_abs2 : |∫ x in scaleSet t S, fderiv ℝ φ.val.toFun x w| =
        t ^ (n - 1) * |∫ x in S, fderiv ℝ ψ.val.toFun x w| := by
      rw [h_int_φ, abs_mul, abs_of_pos h_pos]
    have h_main : ENNReal.ofReal (t ^ (n - 1)) * ENNReal.ofReal |∫ x in S, fderiv ℝ ψ.val.toFun x w| =
        ENNReal.ofReal |∫ x in scaleSet t S, fderiv ℝ φ.val.toFun x w| := by
      rw [h_abs2]
      have h5 : 0 ≤ t ^ (n - 1) := by positivity
      rw [← ENNReal.ofReal_mul h5] <;> rfl
    rw [h_main]
    exact le_iSup (fun (θ : {φ : TestScalar // Function.support φ.toFun ⊆ scaleSet t Ω}) =>
      ENNReal.ofReal |∫ x in scaleSet t S, fderiv ℝ θ.val.toFun x w|) φ

  exact le_antisymm h1 h2

-- ============================================================================
-- Isometry invariance of local directional variation
-- ============================================================================

/-- **Isometry invariance of local directional variation.**

A linear isometry equivalence `e` maps test functions by composition and
preserves volume, so `directionalVariationIn` is invariant:

`directionalVariationIn (e '' S) (e w) K = directionalVariationIn S w (e.symm '' K)`. -/
lemma directionalVariationIn_map (e : E n ≃ₗᵢ[ℝ] E n)
    (S : Set (E n)) (w : E n) (K : Set (E n)) :
    directionalVariationIn (e '' S) (e w) K =
    directionalVariationIn S w (e.symm '' K) := by
  have hmp : MeasurePreserving e volume volume := e.measurePreserving
  have hme : MeasurableEmbedding e :=
    e.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding

  have h_support_comp : ∀ (ψ : TestScalar),
      Function.support (ψ.toFun ∘ e) = e.symm '' Function.support ψ.toFun := by
    intro ψ
    ext y
    simp only [Function.mem_support, Set.mem_image]
    constructor
    · intro h
      refine ⟨e y, h, ?_⟩
      simp
    · rintro ⟨x, hx, rfl⟩
      simpa using hx

  have h_support_comp_symm : ∀ (θ : TestScalar),
      Function.support (θ.toFun ∘ e.symm) = e '' Function.support θ.toFun := by
    intro θ
    ext y
    simp only [Function.mem_support, Set.mem_image]
    constructor
    · intro h
      refine ⟨e.symm y, h, ?_⟩
      simp
    · rintro ⟨x, hx, rfl⟩
      simpa using hx

  let comp_e : TestScalar → TestScalar := fun ψ =>
    { toFun := ψ.toFun ∘ e
      smooth := ψ.smooth.comp e.contDiff
      compact := by
        have h_tsupp : tsupport (ψ.toFun ∘ e) = e.symm '' tsupport ψ.toFun := by
          have h1 : Function.support (ψ.toFun ∘ e) = e.symm '' Function.support ψ.toFun := h_support_comp ψ
          have h2 : closure (e.symm '' Function.support ψ.toFun) = e.symm '' closure (Function.support ψ.toFun) := by
            have h_cont : Continuous e.symm := e.symm.continuous
            have h_closed : IsClosed (e.symm '' closure (Function.support ψ.toFun)) :=
              (e.symm.toHomeomorph.isClosed_image).mpr isClosed_closure
            have h3 : closure (e.symm '' Function.support ψ.toFun) ⊆ e.symm '' closure (Function.support ψ.toFun) :=
              closure_minimal (Set.image_mono subset_closure) h_closed
            have h4 : e.symm '' closure (Function.support ψ.toFun) ⊆ closure (e.symm '' Function.support ψ.toFun) :=
              image_closure_subset_closure_image h_cont
            exact le_antisymm h3 h4
          calc tsupport (ψ.toFun ∘ e)
            = closure (Function.support (ψ.toFun ∘ e)) := by rfl
          _ = closure (e.symm '' Function.support ψ.toFun) := by rw [h1]
          _ = e.symm '' closure (Function.support ψ.toFun) := h2
          _ = e.symm '' tsupport ψ.toFun := by rfl
        have h_main : IsCompact (tsupport (ψ.toFun ∘ e)) := by
          rw [h_tsupp]
          exact ψ.compact.image e.symm.continuous
        exact h_main
      bound := fun x => ψ.bound (e x) }

  let comp_e_symm : TestScalar → TestScalar := fun θ =>
    { toFun := θ.toFun ∘ e.symm
      smooth := θ.smooth.comp e.symm.contDiff
      compact := by
        have h_tsupp : tsupport (θ.toFun ∘ e.symm) = e '' tsupport θ.toFun := by
          have h1 : Function.support (θ.toFun ∘ e.symm) = e '' Function.support θ.toFun := h_support_comp_symm θ
          have h2 : closure (e '' Function.support θ.toFun) = e '' closure (Function.support θ.toFun) := by
            have h_cont : Continuous e := e.continuous
            have h_closed : IsClosed (e '' closure (Function.support θ.toFun)) :=
              (e.toHomeomorph.isClosed_image).mpr isClosed_closure
            have h3 : closure (e '' Function.support θ.toFun) ⊆ e '' closure (Function.support θ.toFun) :=
              closure_minimal (Set.image_mono subset_closure) h_closed
            have h4 : e '' closure (Function.support θ.toFun) ⊆ closure (e '' Function.support θ.toFun) :=
              image_closure_subset_closure_image h_cont
            exact le_antisymm h3 h4
          calc tsupport (θ.toFun ∘ e.symm)
            = closure (Function.support (θ.toFun ∘ e.symm)) := by rfl
          _ = closure (e '' Function.support θ.toFun) := by rw [h1]
          _ = e '' closure (Function.support θ.toFun) := h2
          _ = e '' tsupport θ.toFun := by rfl
        have h_main : IsCompact (tsupport (θ.toFun ∘ e.symm)) := by
          rw [h_tsupp]
          exact θ.compact.image e.continuous
        exact h_main
      bound := fun x => θ.bound (e.symm x) }

  have h_chain : ∀ (ψ : TestScalar) (y : E n),
      fderiv ℝ (ψ.toFun ∘ e) y w = fderiv ℝ ψ.toFun (e y) (e w) := by
    intro ψ y
    have h_diff : DifferentiableAt ℝ ψ.toFun (e y) :=
      (ψ.smooth.differentiable (by norm_num)).differentiableAt
    have h_fd : HasFDerivAt ψ.toFun (fderiv ℝ ψ.toFun (e y)) (e y) := h_diff.hasFDerivAt
    have h_fd2 : HasFDerivAt (ψ.toFun ∘ e) ((fderiv ℝ ψ.toFun (e y)).comp (e : E n →L[ℝ] E n)) y :=
      h_fd.comp y e.hasFDerivAt
    have h_eq : fderiv ℝ (ψ.toFun ∘ e) y = (fderiv ℝ ψ.toFun (e y)).comp (e : E n →L[ℝ] E n) := h_fd2.fderiv
    rw [h_eq] <;> rfl

  have h_int : ∀ (ψ : TestScalar),
      ∫ x in e '' S, fderiv ℝ ψ.toFun x (e w) =
      ∫ y in S, fderiv ℝ (ψ.toFun ∘ e) y w := by
    intro ψ
    have h : ∫ x in e '' S, fderiv ℝ ψ.toFun x (e w) =
        ∫ y in S, fderiv ℝ ψ.toFun (e y) (e w) :=
      hmp.setIntegral_image_emb hme (fun x => fderiv ℝ ψ.toFun x (e w)) S
    rw [h]
    <;> congr with y <;> exact (h_chain ψ y).symm

  have h1 : directionalVariationIn (e '' S) (e w) K ≤
      directionalVariationIn S w (e.symm '' K) := by
    apply iSup_le
    intro ψ
    let θ : TestScalar := comp_e ψ.val
    have h_support_θ : Function.support θ.toFun ⊆ e.symm '' K := by
      rw [h_support_comp ψ.val]
      have h_img : e.symm '' Function.support ψ.val.toFun ⊆ e.symm '' K := by
        intro z hz
        rcases hz with ⟨x, hx, rfl⟩
        exact ⟨x, ψ.property hx, rfl⟩
      exact h_img
    let θ' : {θ : TestScalar // Function.support θ.toFun ⊆ e.symm '' K} := ⟨θ, h_support_θ⟩
    have h_int_eq : ∫ x in e '' S, fderiv ℝ ψ.val.toFun x (e w) =
        ∫ y in S, fderiv ℝ θ.toFun y w := h_int ψ.val
    rw [h_int_eq]
    exact le_iSup (fun (χ : {θ : TestScalar // Function.support θ.toFun ⊆ e.symm '' K}) =>
      ENNReal.ofReal |∫ y in S, fderiv ℝ χ.val.toFun y w|) θ'

  have h2 : directionalVariationIn S w (e.symm '' K) ≤
      directionalVariationIn (e '' S) (e w) K := by
    apply iSup_le
    intro θ
    let ψ : TestScalar := comp_e_symm θ.val
    have h_support_ψ : Function.support ψ.toFun ⊆ K := by
      rw [h_support_comp_symm θ.val]
      have h1 : e '' Function.support θ.val.toFun ⊆ e '' (e.symm '' K) := by
        intro z hz
        rcases hz with ⟨x, hx, rfl⟩
        exact ⟨x, θ.property hx, rfl⟩
      have h2 : e '' (e.symm '' K) = K := by
        ext z
        simp only [Set.mem_image]
        constructor
        · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
          simpa using hx
        · intro hz
          refine ⟨e.symm z, ⟨z, hz, by simp⟩, by simp⟩
      rw [h2] at h1
      exact h1
    let ψ' : {ψ : TestScalar // Function.support ψ.toFun ⊆ K} := ⟨ψ, h_support_ψ⟩
    have h21 : ψ.toFun ∘ e = θ.val.toFun := by
      funext y
      simp [ψ, comp_e_symm]
      <;> rfl
    have h_int_eq : ∫ y in S, fderiv ℝ θ.val.toFun y w =
        ∫ x in e '' S, fderiv ℝ ψ.toFun x (e w) := by
      have h : ∫ x in e '' S, fderiv ℝ ψ.toFun x (e w) =
          ∫ y in S, fderiv ℝ (ψ.toFun ∘ e) y w := h_int ψ
      rw [h, h21]
    rw [h_int_eq]
    exact le_iSup (fun (χ : {ψ : TestScalar // Function.support ψ.toFun ⊆ K}) =>
      ENNReal.ofReal |∫ x in e '' S, fderiv ℝ χ.val.toFun x (e w)|) ψ'

  exact le_antisymm h1 h2

end Geometry.Perimeter
