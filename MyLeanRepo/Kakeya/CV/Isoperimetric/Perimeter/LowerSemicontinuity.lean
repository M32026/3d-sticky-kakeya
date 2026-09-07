import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import Mathlib.Tactic

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.Perimeter

variable {n : ℕ}
attribute [local instance] Classical.propDecidable

/-- If `f` is continuous with compact support and `volume((A_k ∆ A) ∩ tsupport f) → 0`,
then `∫_{A_k} f → ∫_A f`. -/
lemma integral_set_convergence {f : E n → ℝ} (hf_cont : Continuous f)
    (hf_compact : HasCompactSupport f)
    {A : Set (E n)} (hA : MeasurableSet A)
    {Ak : ℕ → Set (E n)} (hAk : ∀ k, MeasurableSet (Ak k))
    (h_conv : Filter.Tendsto
      (fun k => volume ((symmDiff A (Ak k)) ∩ tsupport f)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => ∫ x in Ak k, f x) Filter.atTop (nhds (∫ x in A, f x)) := by
  let K := tsupport f
  have hK : IsCompact K := hf_compact
  have hK_meas : MeasurableSet K := isClosed_tsupport f |>.measurableSet
  have h_finite : volume K ≠ ⊤ := hK.measure_ne_top

  -- f is integrable everywhere
  have h_f_integrable : Integrable f volume := by
    exact hf_cont.integrable_of_hasCompactSupport hf_compact

  -- Boundedness of f
  have h_abs_cont : ContinuousOn (fun x => |f x|) K := hf_cont.abs.continuousOn
  have h_abs_bdd : BddAbove ((fun x => |f x|) '' K) := hK.bddAbove_image h_abs_cont
  rcases h_abs_bdd with ⟨C0, hC0⟩
  let C := max C0 0
  have hC_nonneg : 0 ≤ C := by simp [C]
  have hC_all : ∀ x, |f x| ≤ C := by
    intro x
    by_cases hx : x ∈ K
    · have h4 : |f x| ∈ (fun x => |f x|) '' K := ⟨x, hx, rfl⟩
      have h5 : |f x| ≤ C0 := hC0 h4
      exact le_max_of_le_left h5
    · have h5 : f x = 0 := by
        have h6 : x ∉ Function.support f := by
          intro h7
          have h8 : x ∈ K := subset_tsupport (f := f) h7
          exact hx h8
        simpa [Function.mem_support] using h6
      rw [h5]; simp [hC_nonneg]

  have h_main : ∀ k, |(∫ x in Ak k, f x) - (∫ x in A, f x)| ≤
      C * (volume ((symmDiff A (Ak k)) ∩ K)).toReal := by
    intro k
    let D := symmDiff A (Ak k)
    have hD_meas : MeasurableSet D := hA.symmDiff (hAk k)
    have h_indicator : ∀ x, |Set.indicator (Ak k) f x - Set.indicator A f x| =
        Set.indicator D (fun x => |f x|) x := by
      intro x
      by_cases h1 : x ∈ Ak k <;> by_cases h2 : x ∈ A
      · have h3 : x ∉ D := by
          dsimp only [D, symmDiff]; intro h4; rcases h4 with (h4 | h5); exact h4.2 h1; exact h5.2 h2
        simp [Set.indicator_apply, h1, h2, h3]
      · have h3 : x ∈ D := by
          dsimp only [D, symmDiff]; exact Or.inr ⟨h1, h2⟩
        simp [Set.indicator_apply, h1, h2, h3]
      · have h3 : x ∈ D := by
          dsimp only [D, symmDiff]; exact Or.inl ⟨h2, h1⟩
        simp [Set.indicator_apply, h1, h2, h3] <;> rfl
      · have h3 : x ∉ D := by
          dsimp only [D, symmDiff]; intro h4; rcases h4 with (h4 | h4); exact h2 h4.1; exact h1 h4.1
        simp [Set.indicator_apply, h1, h2, h3]
    have h_int1 : Integrable (Set.indicator (Ak k) f) volume :=
      h_f_integrable.indicator (hAk k)
    have h_int2 : Integrable (Set.indicator A f) volume :=
      h_f_integrable.indicator hA
    have h1 : (∫ x in Ak k, f x) - (∫ x in A, f x) =
        ∫ x, (Set.indicator (Ak k) f x - Set.indicator A f x) := by
      have h2 : ∫ x in Ak k, f x = ∫ x, Set.indicator (Ak k) f x := by
        rw [integral_indicator (hAk k)]
      have h3 : ∫ x in A, f x = ∫ x, Set.indicator A f x := by
        rw [integral_indicator hA]
      rw [h2, h3]
      rw [integral_sub h_int1 h_int2]
    rw [h1]
    have h4 : |∫ x, (Set.indicator (Ak k) f x - Set.indicator A f x)| ≤
        ∫ x, |Set.indicator (Ak k) f x - Set.indicator A f x| :=
      abs_integral_le_integral_abs
    have h5 : ∫ x, |Set.indicator (Ak k) f x - Set.indicator A f x| =
        ∫ x, Set.indicator D (fun x => |f x|) x := by
      apply integral_congr_ae
      exact ae_of_all _ h_indicator
    have h6 : ∫ x, Set.indicator D (fun x => |f x|) x = ∫ x in D, |f x| := by
      rw [integral_indicator hD_meas]
    have h7 : ∫ x in D, |f x| = ∫ x in D ∩ K, |f x| := by
      have h8 : ∀ x ∈ D \ (D ∩ K), (fun x => |f x|) x = 0 := by
        intro x hx
        have h91 : x ∈ D := hx.1
        have h92 : x ∉ D ∩ K := hx.2
        have h93 : x ∉ K := by
          intro h94
          exact h92 ⟨h91, h94⟩
        have h10 : f x = 0 := by
          have h11 : x ∉ Function.support f := by
            intro h12
            have h13 : x ∈ K := subset_tsupport (f := f) h12
            exact h93 h13
          simpa [Function.mem_support] using h11
        have h14 : |f x| = 0 := by rw [h10]; simp
        simpa using h14
      have h_sub : D ∩ K ⊆ D := inter_subset_left
      have h_eq : ∫ x in D, (fun x => |f x|) x = ∫ x in D ∩ K, (fun x => |f x|) x :=
        MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hD_meas h_sub h8
      exact h_eq
    have h9 : ∀ x ∈ D ∩ K, |f x| ≤ C := fun x _ => hC_all x
    have h_abs_integrable : Integrable (fun x => |f x|) volume := h_f_integrable.abs
    have h_int_abs : IntegrableOn (fun x => |f x|) (D ∩ K) := h_abs_integrable.integrableOn
    have h_fin2 : volume (D ∩ K) ≠ ⊤ := ne_top_of_le_ne_top h_finite (measure_mono inter_subset_right)
    have hC_enorm : ‖(C : ℝ)‖ₑ ≠ ⊤ := by
      simp [Real.norm_eq_abs]
      <;> positivity
    have h_int_C : IntegrableOn (fun _ : E n => (C : ℝ)) (D ∩ K) :=
      MeasureTheory.integrableOn_const (hs := h_fin2) (hC := hC_enorm)
    have h10 : ∫ x in D ∩ K, |f x| ≤ ∫ x in D ∩ K, (C : ℝ) :=
      MeasureTheory.setIntegral_mono_on h_int_abs h_int_C (hD_meas.inter hK_meas) h9
    have h11 : ∫ x in D ∩ K, (C : ℝ) = C * (volume (D ∩ K)).toReal := by
      have h12 : ∫ x in D ∩ K, (C : ℝ) = (volume (D ∩ K)).toReal * C := by
        rw [MeasureTheory.setIntegral_const]
        <;> rfl
      rw [h12] <;> ring
    have h12 : ∫ x in D ∩ K, |f x| ≤ C * (volume (D ∩ K)).toReal := by
      calc
        ∫ x in D ∩ K, |f x| ≤ ∫ x in D ∩ K, (C : ℝ) := h10
        _ = C * (volume (D ∩ K)).toReal := h11
    calc
      |∫ x, (Set.indicator (Ak k) f x - Set.indicator A f x)|
        ≤ ∫ x, |Set.indicator (Ak k) f x - Set.indicator A f x| := h4
      _ = ∫ x in D, |f x| := by rw [h5, h6]
      _ = ∫ x in D ∩ K, |f x| := h7
      _ ≤ C * (volume (D ∩ K)).toReal := h12

  have h_toReal_at0 : ContinuousAt ENNReal.toReal (0 : ENNReal) := by
    have h : ContinuousOn ENNReal.toReal {a : ENNReal | a ≠ ⊤} := ENNReal.continuousOn_toReal
    have h_open : IsOpen {a : ENNReal | a ≠ ⊤} := by
      exact isOpen_ne_top
    have h_nhds : {a : ENNReal | a ≠ ⊤} ∈ nhds (0 : ENNReal) := h_open.mem_nhds (by simp)
    exact h.continuousAt h_nhds
  have h_to_real_conv : Filter.Tendsto (fun k => (volume ((symmDiff A (Ak k)) ∩ K)).toReal)
      Filter.atTop (nhds 0) :=
    h_toReal_at0.tendsto.comp h_conv
  have h_mul_conv : Filter.Tendsto (fun k => C * (volume ((symmDiff A (Ak k)) ∩ K)).toReal)
      Filter.atTop (nhds 0) := by
    simpa [mul_zero] using h_to_real_conv.const_mul C
  have h_squeeze : Filter.Tendsto (fun k => (∫ x in Ak k, f x) - (∫ x in A, f x))
      Filter.atTop (nhds 0) :=
    squeeze_zero_norm h_main h_mul_conv
  have h_add : Filter.Tendsto (fun k => (∫ x in Ak k, f x) - (∫ x in A, f x) + (∫ x in A, f x))
      Filter.atTop (nhds ((0 : ℝ) + (∫ x in A, f x))) :=
    h_squeeze.add tendsto_const_nhds
  have h_final : Filter.Tendsto (fun k => ∫ x in Ak k, f x) Filter.atTop (nhds (∫ x in A, f x)) := by
    simpa using h_add
  exact h_final

/-- **Lower semicontinuity of perimeter**.

If `S_k → S` in L¹_loc (i.e., `volume((S_k ∆ S) ∩ K) → 0` for every compact K),
then `perimeter S ≤ liminf_{k→∞} perimeter S_k`. -/
theorem perimeter_lowerSemicontinuity {S : Set (E n)} (hS : MeasurableSet S)
    (Sk : ℕ → Set (E n)) (hSk : ∀ k, MeasurableSet (Sk k))
    (h_conv : ∀ (K : Set (E n)), IsCompact K →
      Filter.Tendsto (fun k => volume ((symmDiff S (Sk k)) ∩ K)) Filter.atTop (nhds 0)) :
    perimeter S ≤ Filter.liminf (fun k => perimeter (Sk k)) Filter.atTop := by
  apply iSup_le
  intro φ
  let f : E n → ℝ := divergence φ.toFun

  -- Each coordinate function is C^∞
  have h_coord : ∀ i : Fin n, ContDiff ℝ ∞ (fun y : E n => φ.toFun y i) := by
    intro i
    have h_eval : ContDiff ℝ ∞ (fun w : E n => w i) := by fun_prop
    exact h_eval.comp φ.smooth


  -- f is continuous
  have hf_cont : Continuous f := by
    have h : ∀ i : Fin n, Continuous (fun x : E n => fderiv ℝ (fun y : E n => φ.toFun y i) x (EuclideanSpace.single i 1)) := by
      intro i
      have hdiff : ContDiff ℝ 1 (fun y : E n => φ.toFun y i) :=
        (h_coord i).of_le (by simp)
      have h_cfderiv : Continuous (fderiv ℝ (fun y : E n => φ.toFun y i)) :=
        hdiff.continuous_fderiv (by norm_num)
      let eval_i : ((E n) →L[ℝ] ℝ) → ℝ := fun g => g (EuclideanSpace.single i (1 : ℝ))
      have h_eval : Continuous eval_i := by
        have h_clm : Continuous eval_i :=
          continuous_eval_const (EuclideanSpace.single i (1 : ℝ))
        exact h_clm
      exact h_eval.comp h_cfderiv
    have h' : ∀ i ∈ Finset.univ, Continuous (fun x : E n => fderiv ℝ (fun y : E n => φ.toFun y i) x (EuclideanSpace.single i 1)) := by
      intro i _; exact h i
    exact continuous_finset_sum Finset.univ h'

  -- f has compact support
  have hf_support : HasCompactSupport f := by
    have h1 : ∀ i : Fin n, Function.support (fun x : E n => fderiv ℝ (fun y : E n => φ.toFun y i) x (EuclideanSpace.single i 1)) ⊆ tsupport φ.toFun := by
      intro i
      have h_supp_coord : Function.support (fun y : E n => φ.toFun y i) ⊆ tsupport φ.toFun := by
        intro y hy
        have h4 : y ∈ Function.support φ.toFun := by
          intro h
          have h5 : (φ.toFun y) i = 0 := by rw [h]; simp
          exact hy h5
        exact (subset_tsupport (f := φ.toFun)) h4
      have h_tsupp_coord : tsupport (fun y : E n => φ.toFun y i) ⊆ tsupport φ.toFun := by
        have h_closed : IsClosed (tsupport φ.toFun) := isClosed_tsupport _
        exact closure_minimal h_supp_coord h_closed
      have h2 : Function.support (fderiv ℝ (fun y : E n => φ.toFun y i)) ⊆ tsupport (fun y : E n => φ.toFun y i) :=
        support_fderiv_subset ℝ
      have h2' : Function.support (fderiv ℝ (fun y : E n => φ.toFun y i)) ⊆ tsupport φ.toFun :=
        h2.trans h_tsupp_coord
      have h3 : Function.support (fun x : E n => fderiv ℝ (fun y : E n => φ.toFun y i) x (EuclideanSpace.single i 1)) ⊆
          Function.support (fderiv ℝ (fun y : E n => φ.toFun y i)) := by
        intro x hx
        have h5 : fderiv ℝ (fun y : E n => φ.toFun y i) x ≠ 0 := by
          intro h6
          have h7 : (fderiv ℝ (fun y : E n => φ.toFun y i) x) (EuclideanSpace.single i (1 : ℝ)) = 0 := by
            rw [h6] <;> simp
          exact hx h7
        exact h5
      exact h3.trans h2'
    have hsum_support : Function.support f ⊆ tsupport φ.toFun := by
      intro x hx
      have h2 : f x ≠ 0 := hx
      have h3 : ∃ i : Fin n, (fderiv ℝ (fun y : E n => φ.toFun y i) x) (EuclideanSpace.single i 1) ≠ 0 := by
        by_contra h4
        push Not at h4
        have h5 : ∑ i : Fin n, (fderiv ℝ (fun y : E n => φ.toFun y i) x) (EuclideanSpace.single i 1) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          exact h4 i
        have h6 : f x = 0 := by
          simpa [f, divergence] using h5
        exact h2 h6
      rcases h3 with ⟨i, hi⟩
      exact h1 i hi
    have h9 : tsupport f ⊆ tsupport φ.toFun := by
      have h10 : IsClosed (tsupport φ.toFun) := isClosed_tsupport _
      exact closure_minimal hsum_support h10
    exact φ.compact.of_isClosed_subset (isClosed_tsupport _) h9

  let K := tsupport f
  have hK : IsCompact K := hf_support
  have h_convK : Filter.Tendsto (fun k => volume ((symmDiff S (Sk k)) ∩ K)) Filter.atTop (nhds 0) :=
    h_conv K hK
  have h_integral_conv : Filter.Tendsto (fun k => ∫ x in Sk k, f x) Filter.atTop (nhds (∫ x in S, f x)) :=
    integral_set_convergence hf_cont hf_support hS hSk h_convK

  let a : ℕ → ENNReal := fun k => ENNReal.ofReal |∫ x in Sk k, f x|
  let b : ℕ → ENNReal := fun k => perimeter (Sk k)
  let a_limit : ENNReal := ENNReal.ofReal |∫ x in S, f x|

  have h3 : ∀ k, a k ≤ b k := by
    intro k
    exact le_iSup (fun (θ : TestVectorField) => ENNReal.ofReal |∫ x in Sk k, divergence θ.toFun x|) φ

  -- Continuity of x ↦ ENNReal.ofReal |x|
  have h_ofReal_abs : Continuous (fun x : ℝ => ENNReal.ofReal |x|) := by
    have h1 : (fun x : ℝ => ENNReal.ofReal |x|) = fun x : ℝ => ((|x|.toNNReal : NNReal) : ENNReal) := by
      funext x
      have h2 : 0 ≤ |x| := abs_nonneg x
      simp [ENNReal.ofReal_eq_coe_nnreal, h2] <;> rfl
    rw [h1]
    have h3 : Continuous (fun x : ℝ => (|x|.toNNReal : NNReal)) := by fun_prop
    have h4 : Continuous (fun r : NNReal => (r : ENNReal)) := ENNReal.continuous_coe
    exact h4.comp h3

  have h4 : Filter.Tendsto a Filter.atTop (nhds a_limit) :=
    h_ofReal_abs.continuousAt.tendsto.comp h_integral_conv

  -- a_limit ≤ liminf b: for every r < a_limit, eventually r ≤ a k ≤ b k
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

end Geometry.Perimeter
