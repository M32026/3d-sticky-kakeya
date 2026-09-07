import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.BVCompactnessTranslation.Helpers
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic


/-!
# L¹ Cauchy and Binary Limit Lemmas

Extracted from BVCompactnessTranslation.lean to speed up compilation.

## Main results

- `l1_cauchy_from_approximation`: If `h_k` are uniformly approximated by
  `f_{k,m}` which converge to `g` in L¹, then `h_k` is L¹-Cauchy.
- `binary_l1_limit`: The L¹ limit of {0,1}-valued functions is {0,1}-valued a.e.
- `l1_full_from_cauchy_subseq`: If `h_k` is L¹-Cauchy and a subsequence
  converges to `g`, then the full sequence converges to `g`.
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ}

/-- **L¹ Cauchy from approximation**.

Given `h_k`, `f_{k,m}`, `g` with:
- `∫ |h_k - f_{k,m}| ≤ C * ε_m`
- `∫ |f_{k,m} - g| → 0` as `k → ∞`
- `ε_m → 0`
then `h_k` is L¹-Cauchy on `K`. -/
lemma l1_cauchy_from_approximation
    {K : Set (E n)} (hK : MeasurableSet K) (hKfin : volume K ≠ ⊤)
    (h : ℕ → E n → ℝ) (f : ℕ → ℕ → E n → ℝ) (g : E n → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (ε : ℕ → ℝ) (hε_pos : ∀ m, 0 < ε m)
    (hε_tendsto : Tendsto ε atTop (nhds 0))
    (h_meas_h : ∀ k, Measurable (h k))
    (h_bound_h : ∀ k x, |h k x| ≤ 1)
    (h_cont_f : ∀ k m, Continuous (f k m))
    (h_bound_f : ∀ k m x, |f k m x| ≤ 1)
    (h_g_cont : ContinuousOn g K)
    (h_g_bound : ∀ x ∈ K, 0 ≤ g x ∧ g x ≤ 1)
    (h_error : ∀ k m, ∫ x in K, |h k x - f k m x| ≤ C * ε m)
    (h_conv : ∀ m, Tendsto (fun k => ∫ x in K, |f k m x - g x|) atTop (nhds 0)) :
    ∀ (eps : ℝ), 0 < eps → ∃ N, ∀ k l, N ≤ k → N ≤ l →
      ∫ x in K, |h k x - h l x| ≤ eps := by
  have h_bounded_int : ∀ (g : E n → ℝ), Measurable g → (∀ x, |g x| ≤ 1) → IntegrableOn g K := by
    intro g hg hbound
    have h_bound_ae : ∀ᵐ x ∂volume.restrict K, ‖g x‖ ≤ 1 := by
      filter_upwards with x
      have h_abs : ‖g x‖ = |g x| := by simp [Real.norm_eq_abs]
      rw [h_abs]; exact hbound x
    exact Measure.integrableOn_of_bounded hKfin hg.aestronglyMeasurable h_bound_ae
  have hC' : 0 ≤ C := hC
  intro eps h_eps
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 * C * ε m < eps / 2 := by
    have h_tendsto : Tendsto (fun m : ℕ => 2 * C * ε m) atTop (nhds 0) := by
      have h' : Tendsto (fun m : ℕ => (2 * C) * ε m) atTop (nhds ((2 * C) * (0 : ℝ))) :=
        (tendsto_const_nhds (x := 2 * C)).mul hε_tendsto
      have h0 : (2 * C) * (0 : ℝ) = 0 := by ring
      rw [h0] at h'; exact h'
    have h := h_tendsto (Iio_mem_nhds (show (0 : ℝ) < eps / 2 by linarith))
    rcases Filter.eventually_atTop.mp h with ⟨m, hm⟩
    exact ⟨m, hm m (le_refl m)⟩
  have h_f_conv : ∃ N, ∀ k ≥ N, ∫ x in K, |f k m x - g x| ≤ eps / 4 := by
    have h : Tendsto (fun k => ∫ x in K, |f k m x - g x|) atTop (nhds 0) := h_conv m
    have h' := Metric.tendsto_atTop.mp h (eps / 4) (by linarith)
    rcases h' with ⟨N, hN⟩
    refine ⟨N, fun k hk => ?_⟩
    have h_dist : dist (∫ x in K, |f k m x - g x|) 0 < eps / 4 := hN k hk
    have h_nonneg : 0 ≤ ∫ x in K, |f k m x - g x| := by positivity
    simpa [Real.dist_eq, abs_of_nonneg h_nonneg] using h_dist.le
  rcases h_f_conv with ⟨N, hN⟩
  refine ⟨N, fun k l hk hl => ?_⟩
  have h1 : ∀ x, |h k x - h l x| ≤ |h k x - f k m x| + |f k m x - g x|
        + |g x - f l m x| + |f l m x - h l x| := by
    intro x
    set a := h k x - f k m x with ha
    set b := f k m x - g x with hb
    set c := g x - f l m x with hc
    set d := f l m x - h l x with hd
    have h_eq : h k x - h l x = a + b + c + d := by
      dsimp only [a, b, c, d] <;> abel
    rw [h_eq]
    have h2 : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
      have h21 : |a + b + c + d| ≤ |a + b| + |c + d| := by
        calc |a + b + c + d|
          = |(a + b) + (c + d)| := by abel_nf
        _ ≤ |a + b| + |c + d| := abs_add_le (a + b) (c + d)
      have h22 : |a + b| ≤ |a| + |b| := abs_add_le a b
      have h23 : |c + d| ≤ |c| + |d| := abs_add_le c d
      linarith
    exact h2
  have h_int_hk : IntegrableOn (h k) K := h_bounded_int (h k) (h_meas_h k) (h_bound_h k)
  have h_int_hl : IntegrableOn (h l) K := h_bounded_int (h l) (h_meas_h l) (h_bound_h l)
  have h_int_fk : IntegrableOn (f k m) K :=
    h_bounded_int (f k m) (h_cont_f k m).measurable (h_bound_f k m)
  have h_int_fl : IntegrableOn (f l m) K :=
    h_bounded_int (f l m) (h_cont_f l m).measurable (h_bound_f l m)
  have h_int_g : IntegrableOn g K := by
    have h_ae : AEStronglyMeasurable g (volume.restrict K) :=
      h_g_cont.aestronglyMeasurable hK
    have h_bound_ae : ∀ᵐ x ∂volume.restrict K, ‖g x‖ ≤ 1 := by
      filter_upwards [ae_restrict_mem hK] with x hx
      have h2 : 0 ≤ g x ∧ g x ≤ 1 := h_g_bound x hx
      have h_abs : ‖g x‖ = |g x| := by simp [Real.norm_eq_abs]
      rw [h_abs, abs_of_nonneg h2.1]; exact h2.2
    have hK_lt : volume K < ⊤ := lt_top_iff_ne_top.mpr hKfin
    exact IntegrableOn.of_bound hK_lt h_ae 1 h_bound_ae
  let f1 := fun x : E n => |h k x - f k m x|
  let f2 := fun x : E n => |f k m x - g x|
  let f3 := fun x : E n => |g x - f l m x|
  let f4 := fun x : E n => |f l m x - h l x|
  have h_i1 : IntegrableOn f1 K := (h_int_hk.sub h_int_fk).abs
  have h_i2 : IntegrableOn f2 K := (h_int_fk.sub h_int_g).abs
  have h_i3 : IntegrableOn f3 K := (h_int_g.sub h_int_fl).abs
  have h_i4 : IntegrableOn f4 K := (h_int_fl.sub h_int_hl).abs
  have h_int_sum : IntegrableOn (fun x => f1 x + f2 x + f3 x + f4 x) K :=
    h_i1.add h_i2 |>.add h_i3 |>.add h_i4
  have h_int_hl : IntegrableOn (fun x => |h k x - h l x|) K :=
    (h_int_hk.sub h_int_hl).abs
  have h_mono : ∫ x in K, |h k x - h l x| ≤
      ∫ x in K, (f1 x + f2 x + f3 x + f4 x) := by
    have h_point : ∀ x ∈ K, |h k x - h l x| ≤ f1 x + f2 x + f3 x + f4 x := fun x _ => h1 x
    have h_ae : (fun x : E n => |h k x - h l x|) ≤ᵐ[volume.restrict K] (fun x : E n => f1 x + f2 x + f3 x + f4 x) := by
      filter_upwards [ae_restrict_mem hK] with x hx using h_point x hx
    have h_eq1 : ∫ x in K, |h k x - h l x| = ∫ x, |h k x - h l x| ∂volume.restrict K := by rfl
    have h_eq2 : ∫ x in K, (f1 x + f2 x + f3 x + f4 x) = ∫ x, (f1 x + f2 x + f3 x + f4 x) ∂volume.restrict K := by rfl
    rw [h_eq1, h_eq2]
    exact MeasureTheory.integral_mono_ae h_int_hl h_int_sum h_ae
  have h_sum : ∫ x in K, (f1 x + f2 x + f3 x + f4 x) =
      (∫ x in K, f1 x) + (∫ x in K, f2 x) + (∫ x in K, f3 x) + (∫ x in K, f4 x) := by
    have h_eq1 : ∫ x in K, (f1 x + f2 x) = (∫ x in K, f1 x) + (∫ x in K, f2 x) := by
      exact MeasureTheory.integral_add' h_i1 h_i2
    have h_i12 : IntegrableOn (fun x => f1 x + f2 x) K := h_i1.add h_i2
    have h_eq2 : ∫ x in K, (f1 x + f2 x + f3 x) = (∫ x in K, (f1 x + f2 x)) + (∫ x in K, f3 x) := by
      exact MeasureTheory.integral_add' h_i12 h_i3
    have h_i123 : IntegrableOn (fun x => f1 x + f2 x + f3 x) K := h_i12.add h_i3
    have h_eq3 : ∫ x in K, (f1 x + f2 x + f3 x + f4 x) =
        (∫ x in K, (f1 x + f2 x + f3 x)) + (∫ x in K, f4 x) := by
      exact MeasureTheory.integral_add' h_i123 h_i4
    calc
      ∫ x in K, (f1 x + f2 x + f3 x + f4 x)
        = (∫ x in K, (f1 x + f2 x + f3 x)) + (∫ x in K, f4 x) := h_eq3
      _ = ((∫ x in K, (f1 x + f2 x)) + (∫ x in K, f3 x)) + (∫ x in K, f4 x) := by rw [h_eq2]
      _ = (∫ x in K, f1 x) + (∫ x in K, f2 x) + (∫ x in K, f3 x) + (∫ x in K, f4 x) := by
        rw [h_eq1] <;> ring
  rw [h_sum] at h_mono
  have h_e1 : ∫ x in K, f1 x ≤ C * ε m := by
    have h_eq : ∀ x, f1 x = |f k m x - h k x| := by
      intro x; exact abs_sub_comm (h k x) (f k m x)
    have h_int_eq : ∫ x in K, f1 x = ∫ x in K, |f k m x - h k x| :=
      MeasureTheory.setIntegral_congr_fun hK (fun x _ => h_eq x)
    rw [h_int_eq]
    have h_rev : ∫ x in K, |f k m x - h k x| = ∫ x in K, |h k x - f k m x| :=
      MeasureTheory.setIntegral_congr_fun hK (fun x _ => abs_sub_comm (f k m x) (h k x))
    rw [h_rev]
    exact h_error k m
  have h_e2 : ∫ x in K, f2 x ≤ eps / 4 := hN k hk
  have h_e3 : ∫ x in K, f3 x ≤ eps / 4 := by
    have h_eq : ∀ x, f3 x = |f l m x - g x| := by
      intro x; exact abs_sub_comm (g x) (f l m x)
    have h_int_eq : ∫ x in K, f3 x = ∫ x in K, |f l m x - g x| :=
      MeasureTheory.setIntegral_congr_fun hK (fun x _ => h_eq x)
    rw [h_int_eq]; exact hN l hl
  have h_e4 : ∫ x in K, f4 x ≤ C * ε m := by
    have h_eq : ∀ x, f4 x = |h l x - f l m x| := by
      intro x; exact abs_sub_comm (f l m x) (h l x)
    have h_int_eq : ∫ x in K, f4 x = ∫ x in K, |h l x - f l m x| :=
      MeasureTheory.setIntegral_congr_fun hK (fun x _ => h_eq x)
    rw [h_int_eq]
    exact h_error l m
  linarith

/-- **Binary L¹ limit**.

If `h_k` are {0,1}-valued and converge in L¹ to `g` on `K`,
then `g` is {0,1}-valued a.e. on `K`. -/
lemma binary_l1_limit
    {K : Set (E n)} (hK : MeasurableSet K) (hKfin : volume K ≠ ⊤)
    (h : ℕ → E n → ℝ) (g : E n → ℝ)
    (h_meas_h : ∀ k, Measurable (h k))
    (h_bound_h : ∀ k x, |h k x| ≤ 1)
    (h_binary_h : ∀ k x, h k x = 0 ∨ h k x = 1)
    (hg_integrable : IntegrableOn g K)
    (hg_conv : Tendsto (fun k => ∫ x in K, |h k x - g x|) atTop (nhds 0)) :
    ∀ᵐ x ∂volume.restrict K, g x = 0 ∨ g x = 1 := by
  let μ := volume.restrict K
  letI : IsFiniteMeasure μ := by
    have h2 : μ Set.univ = volume K := by
      rw [Measure.restrict_apply MeasurableSet.univ] <;> simp
    have h3 : μ Set.univ < ⊤ := by rw [h2]; exact lt_top_iff_ne_top.mpr hKfin
    exact ⟨h3⟩
  let d : E n → ℝ := fun x => min |g x| |g x - 1|
  have hd_nonneg : ∀ x, 0 ≤ d x := by
    intro x; exact le_min (abs_nonneg _) (abs_nonneg _)
  have hd_le : ∀ x, d x ≤ |g x| := by intro x; exact min_le_left _ _
  have hd_meas : AEStronglyMeasurable d μ := by
    have h1 : AEStronglyMeasurable (fun x => |g x|) μ := hg_integrable.aestronglyMeasurable.norm
    have h2 : AEStronglyMeasurable (fun x => |g x - 1|) μ :=
      (hg_integrable.aestronglyMeasurable.sub aestronglyMeasurable_const).norm
    exact continuous_min.comp_aestronglyMeasurable₂ h1 h2
  have hd_int : Integrable d μ := by
    have h_bound : ∀ᵐ x ∂μ, ‖d x‖ ≤ ‖g x‖ := by
      filter_upwards with x
      have h1 : ‖d x‖ = d x := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hd_nonneg x)]
      have h2 : ‖g x‖ = |g x| := by simp [Real.norm_eq_abs]
      rw [h1, h2]; exact hd_le x
    exact Integrable.mono hg_integrable hd_meas h_bound
  have h_bounded_int : ∀ (f : E n → ℝ), Measurable f → (∀ x, |f x| ≤ 1) → IntegrableOn f K := by
    intro f hf hbound
    have h_bound_ae : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1 := by
      filter_upwards with x
      have h_abs : ‖f x‖ = |f x| := by simp [Real.norm_eq_abs]
      rw [h_abs]; exact hbound x
    exact Measure.integrableOn_of_bounded hKfin hf.aestronglyMeasurable h_bound_ae
  have h_dist : ∀ n x, d x ≤ |h n x - g x| := by
    intro n x
    have h1 : h n x = 0 ∨ h n x = 1 := h_binary_h n x
    rcases h1 with (h1 | h1)
    · rw [h1]
      have h_abs : |(0 : ℝ) - g x| = |g x| := by rw [zero_sub, abs_neg]
      rw [h_abs]; exact hd_le x
    · rw [h1]
      have h_abs : |(1 : ℝ) - g x| = |g x - 1| := by
        rw [show (1 : ℝ) - g x = -(g x - 1) by ring, abs_neg]
      rw [h_abs]; exact min_le_right _ _
  have h_int_dist : ∀ n, ∫ x, d x ∂μ ≤ ∫ x, |h n x - g x| ∂μ := by
    intro n
    have h_int2 : Integrable (fun x => |h n x - g x|) μ :=
      (IntegrableOn.sub (h_bounded_int (h n) (h_meas_h n) (h_bound_h n)) hg_integrable).norm
    have h_ae : ∀ᵐ x ∂μ, d x ≤ |h n x - g x| := by
      filter_upwards with x; exact h_dist n x
    exact integral_mono_ae hd_int h_int2 h_ae
  have h_zero_dist : ∫ x, d x ∂μ = 0 := by
    have h_nonneg : 0 ≤ ∫ x, d x ∂μ := integral_nonneg hd_nonneg
    have h_le : ∫ x, d x ∂μ ≤ 0 := by
      by_contra h_contra
      have h_pos : 0 < ∫ x, d x ∂μ := by linarith
      have h_tend' : ∃ N, ∀ n ≥ N, dist (∫ x, |h n x - g x| ∂μ) 0 < ∫ x, d x ∂μ :=
        Metric.tendsto_atTop.mp hg_conv (∫ x, d x ∂μ) h_pos
      rcases h_tend' with ⟨N, hN⟩
      have h_event : ∀ᶠ n in atTop, ∫ x, |h n x - g x| ∂μ < ∫ x, d x ∂μ := by
        filter_upwards [Filter.eventually_ge_atTop N] with n hn
        have h_dist := hN n hn
        have h_nonneg' : 0 ≤ ∫ x, |h n x - g x| ∂μ := by positivity
        have h_eq : dist (∫ x, |h n x - g x| ∂μ) 0 = ∫ x, |h n x - g x| ∂μ := by
          rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg h_nonneg']
        rw [h_eq] at h_dist; exact h_dist
      rcases Filter.eventually_atTop.mp h_event with ⟨N, hN⟩
      have h9 := hN N (le_refl N)
      have h10 : ∫ x, d x ∂μ ≤ ∫ x, |h N x - g x| ∂μ := h_int_dist N
      linarith
    exact le_antisymm h_le h_nonneg
  have h_ae_dist : ∀ᵐ x ∂μ, d x = 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall hd_nonneg) hd_int).mp h_zero_dist
  filter_upwards [h_ae_dist] with x hx
  have h5 : min |g x| |g x - 1| = 0 := hx
  have h6 : |g x| = 0 ∨ |g x - 1| = 0 := by
    have h7 : |g x| ≤ |g x - 1| ∨ |g x - 1| ≤ |g x| := le_total _ _
    rcases h7 with (h7 | h7)
    · have h8 : min |g x| |g x - 1| = |g x| := min_eq_left h7
      rw [h8] at h5; exact Or.inl h5
    · have h8 : min |g x| |g x - 1| = |g x - 1| := min_eq_right h7
      rw [h8] at h5; exact Or.inr h5
  rcases h6 with (h6 | h6)
  · have h7 : g x = 0 := by simpa [abs_eq_zero] using h6
    exact Or.inl h7
  · have h7 : g x = 1 := by simpa [sub_eq_zero, abs_eq_zero] using h6
    exact Or.inr h7

/-- **Full L¹ convergence from Cauchy + subsequence**.

If `h_k` is L¹-Cauchy on `K` and a subsequence `h_{k_seq n}` converges
in L¹ to `g`, then the full sequence `h_k` converges in L¹ to `g`. -/
lemma l1_full_from_cauchy_subseq
    {K : Set (E n)} (hK : MeasurableSet K) (hKfin : volume K ≠ ⊤)
    (h : ℕ → E n → ℝ) (g : E n → ℝ)
    (h_meas_h : ∀ k, Measurable (h k))
    (h_bound_h : ∀ k x, |h k x| ≤ 1)
    (hg_integrable : IntegrableOn g K)
    (h_cauchy : ∀ (eps : ℝ), 0 < eps → ∃ N, ∀ k l, N ≤ k → N ≤ l →
      ∫ x in K, |h k x - h l x| ≤ eps)
    (k_seq : ℕ → ℕ) (hk_strict : StrictMono k_seq)
    (hg_conv_subseq : Tendsto (fun n => ∫ x in K, |h (k_seq n) x - g x|) atTop (nhds 0)) :
    Tendsto (fun k => ∫ x in K, |h k x - g x|) atTop (nhds 0) := by
  let μ := volume.restrict K
  have h_bounded_int : ∀ (f : E n → ℝ), Measurable f → (∀ x, |f x| ≤ 1) → IntegrableOn f K := by
    intro f hf hbound
    have h_bound_ae : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1 := by
      filter_upwards with x
      have h_abs : ‖f x‖ = |f x| := by simp [Real.norm_eq_abs]
      rw [h_abs]; exact hbound x
    exact Measure.integrableOn_of_bounded hKfin hf.aestronglyMeasurable h_bound_ae
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h_cauchy' : ∃ N, ∀ k l, N ≤ k → N ≤ l → ∫ x in K, |h k x - h l x| ≤ ε / 3 :=
    h_cauchy (ε / 3) (by linarith)
  rcases h_cauchy' with ⟨N, hN_cauchy⟩
  have h_subseq_conv : ∃ n₀, k_seq n₀ ≥ N ∧ ∫ x in K, |h (k_seq n₀) x - g x| ≤ ε / 3 := by
    have h_tend := Metric.tendsto_atTop.mp hg_conv_subseq (ε / 3) (by linarith)
    rcases h_tend with ⟨n₀', hn₀'⟩
    have h_kseq_tendsto : Tendsto k_seq atTop atTop := hk_strict.tendsto_atTop
    have h_exists_n₀ : ∃ n₀, n₀ ≥ n₀' ∧ k_seq n₀ ≥ N := by
      have h := Filter.tendsto_atTop_atTop.mp h_kseq_tendsto N
      rcases h with ⟨m, hm⟩
      refine ⟨max m n₀', ?_⟩
      constructor
      · exact le_max_right _ _
      · exact hm (max m n₀') (le_max_left _ _)
    rcases h_exists_n₀ with ⟨n₀, hn₀_ge_n₀', hkn₀_ge_N⟩
    have h_err : ∫ x in K, |h (k_seq n₀) x - g x| ≤ ε / 3 := by
      have h_dist : dist (∫ x in K, |h (k_seq n₀) x - g x|) 0 < ε / 3 := hn₀' n₀ hn₀_ge_n₀'
      have h_nonneg2 : 0 ≤ ∫ x in K, |h (k_seq n₀) x - g x| := by positivity
      have h_eq : dist (∫ x in K, |h (k_seq n₀) x - g x|) 0 = ∫ x in K, |h (k_seq n₀) x - g x| := by
        rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg h_nonneg2]
      rw [h_eq] at h_dist; linarith
    exact ⟨n₀, hkn₀_ge_N, h_err⟩
  rcases h_subseq_conv with ⟨n₀, hkn₀_ge_N, hn₀_err⟩
  refine ⟨N, fun k hk => ?_⟩
  have h_i1 : IntegrableOn (fun x => |h k x - g x|) K :=
    (IntegrableOn.sub (h_bounded_int (h k) (h_meas_h k) (h_bound_h k)) hg_integrable).norm
  have h_i2 : IntegrableOn (fun x => |h k x - h (k_seq n₀) x|) K :=
    (IntegrableOn.sub (h_bounded_int (h k) (h_meas_h k) (h_bound_h k))
      (h_bounded_int (h (k_seq n₀)) (h_meas_h (k_seq n₀)) (h_bound_h (k_seq n₀)))).norm
  have h_i3 : IntegrableOn (fun x => |h (k_seq n₀) x - g x|) K :=
    (IntegrableOn.sub (h_bounded_int (h (k_seq n₀)) (h_meas_h (k_seq n₀)) (h_bound_h (k_seq n₀))) hg_integrable).norm
  have h_pointwise : ∀ x, |h k x - g x| ≤ |h k x - h (k_seq n₀) x| + |h (k_seq n₀) x - g x| := by
    intro x
    have h_eq : h k x - g x = (h k x - h (k_seq n₀) x) + (h (k_seq n₀) x - g x) := by abel
    rw [h_eq]; exact abs_add_le _ _
  let g_sum : E n → ℝ := fun x => |h k x - h (k_seq n₀) x| + |h (k_seq n₀) x - g x|
  have h_i4 : IntegrableOn g_sum K := IntegrableOn.add h_i2 h_i3
  have h_ae : ∀ᵐ x ∂μ, |h k x - g x| ≤ g_sum x :=
    Eventually.of_forall (fun x => h_pointwise x)
  have h_mono : ∫ x in K, |h k x - g x| ≤ ∫ x in K, g_sum x :=
    integral_mono_ae h_i1 h_i4 h_ae
  have h_sum : ∫ x in K, g_sum x =
      (∫ x in K, |h k x - h (k_seq n₀) x|) + (∫ x in K, |h (k_seq n₀) x - g x|) := by
    have h_eq : ∫ x in K, g_sum x =
        ∫ x in K, (|h k x - h (k_seq n₀) x| + |h (k_seq n₀) x - g x|) := by rfl
    rw [h_eq]
    exact MeasureTheory.integral_add' h_i2 h_i3
  rw [h_sum] at h_mono
  have h_ineq2 : (∫ x in K, |h k x - h (k_seq n₀) x|) ≤ ε / 3 :=
    hN_cauchy k (k_seq n₀) hk hkn₀_ge_N
  have h_ineq3 : (∫ x in K, |h (k_seq n₀) x - g x|) ≤ ε / 3 := hn₀_err
  have h_sum2 : (∫ x in K, |h k x - h (k_seq n₀) x|) + (∫ x in K, |h (k_seq n₀) x - g x|) ≤ 2 * (ε / 3) := by
    have h : (∫ x in K, |h k x - h (k_seq n₀) x|) + (∫ x in K, |h (k_seq n₀) x - g x|) ≤ ε / 3 + ε / 3 :=
      add_le_add h_ineq2 h_ineq3
    have h2 : ε / 3 + ε / 3 = 2 * (ε / 3) := by ring
    rw [h2] at h
    exact h
  have h_total : ∫ x in K, |h k x - g x| ≤ 2 * (ε / 3) := le_trans h_mono h_sum2
  have h_nonneg : 0 ≤ ∫ x in K, |h k x - g x| := by positivity
  have h_strict : 2 * (ε / 3) < ε := by linarith
  have h_lt : ∫ x in K, |h k x - g x| < ε := lt_of_le_of_lt h_total h_strict
  have h_goal : dist (∫ x in K, |h k x - g x|) 0 < ε := by
    have h_dist_eq : dist (∫ x in K, |h k x - g x|) 0 = ∫ x in K, |h k x - g x| := by
      rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg h_nonneg]
    rw [h_dist_eq]; exact h_lt
  exact h_goal

end Geometry
