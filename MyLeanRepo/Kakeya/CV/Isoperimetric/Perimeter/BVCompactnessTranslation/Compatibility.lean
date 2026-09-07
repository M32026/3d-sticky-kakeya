import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.BVCompactnessTranslation.L1Cauchy
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.BVCompactnessTranslation.Helpers
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


/-!
# BV Compactness — Compatibility and Limit Construction Lemmas

Additional extracted lemmas for BVCompactnessTranslation.
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ}

/-- Given an L¹-Cauchy sequence of {0,1}-valued functions on compact K,
construct an L¹ limit that is {0,1}-valued a.e. using cauchy_complete_eLpNorm. -/
lemma cauchy_complete_binary_limit
    (K : Set (E n))
    (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_fin : volume K ≠ ⊤)
    (h : ℕ → (E n → ℝ))
    (h_meas_h : ∀ k, Measurable (h k))
    (h_bound_h : ∀ k x, |h k x| ≤ 1)
    (h_bin : ∀ k x, h k x = 0 ∨ h k x = 1)
    (h_cauchy : ∀ (eps : ℝ), 0 < eps → ∃ N, ∀ k l, N ≤ k → N ≤ l →
        ∫ x in K, |h k x - h l x| ≤ eps) :
    ∃ (g : E n → ℝ),
        Measurable g ∧
        IntegrableOn g K ∧
        Tendsto (fun k => ∫ x in K, |h k x - g x|) atTop (nhds 0) ∧
        (∀ᵐ x ∂volume.restrict K, g x = 0 ∨ g x = 1) := by
  let μ := volume.restrict K
  have hK_lt : volume K < ⊤ := lt_top_iff_ne_top.mpr hK_fin
  letI : IsFiniteMeasure μ := by
    have h2 : μ Set.univ = volume K := by
      rw [Measure.restrict_apply MeasurableSet.univ] <;> simp
    have h3 : μ Set.univ < ⊤ := by rw [h2]; exact hK_lt
    exact ⟨h3⟩
  have h_bounded_int : ∀ (f : E n → ℝ), Measurable f → (∀ x, |f x| ≤ 1) → IntegrableOn f K := by
    intro f hf hbound
    have h_bound_ae : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1 := by
      filter_upwards with x
      have h_abs : ‖f x‖ = |f x| := by simp [Real.norm_eq_abs]
      rw [h_abs]; exact hbound x
    exact Measure.integrableOn_of_bounded hK_fin hf.aestronglyMeasurable h_bound_ae
  -- Fast subsequence
  have h_exists_N : ∀ (i : ℕ), ∃ N : ℕ, ∀ k l, N ≤ k → N ≤ l →
      ∫ x in K, |h k x - h l x| ≤ (1 / 2 : ℝ) ^ (i + 1) := by
    intro i; exact h_cauchy ((1 / 2 : ℝ) ^ (i + 1)) (by positivity)
  choose N hN using h_exists_N
  let k_seq : ℕ → ℕ := Nat.rec (N 0) fun i prev => max (prev + 1) (N (i + 1))
  have hk_strict : StrictMono k_seq := by
    intro n m hnm
    induction' hnm with m hnm ih
    · simp [k_seq, Nat.rec_add_one] <;> omega
    · exact lt_trans ih (by simp [k_seq, Nat.rec_add_one] <;> omega)
  have hk_ge_N : ∀ i, k_seq i ≥ N i := by
    intro i; induction i with
    | zero => simp [k_seq]
    | succ i ih => simp [k_seq, Nat.rec_add_one] <;> omega
  have hk_fast : ∀ i n m, i ≤ n → i ≤ m →
      ∫ x in K, |h (k_seq n) x - h (k_seq m) x| ≤ (1 / 2 : ℝ) ^ (i + 1) := by
    intro i n m hin him
    have h1 : k_seq n ≥ N i := by
      calc k_seq n ≥ k_seq i := hk_strict.monotone hin
           _ ≥ N i := hk_ge_N i
    have h2 : k_seq m ≥ N i := by
      calc k_seq m ≥ k_seq i := hk_strict.monotone him
           _ ≥ N i := hk_ge_N i
    exact hN i (k_seq n) (k_seq m) h1 h2
  have h_memLp : ∀ n, MeasureTheory.MemLp (h (k_seq n)) 1 μ := by
    intro n
    have h_int : IntegrableOn (h (k_seq n)) K :=
      h_bounded_int (h (k_seq n)) (h_meas_h (k_seq n)) (h_bound_h (k_seq n))
    have h_int' : Integrable (h (k_seq n)) μ := h_int
    exact MeasureTheory.memLp_one_iff_integrable.mpr h_int'
  let B : ℕ → ENNReal := fun N => ENNReal.ofReal ((1 / 2 : ℝ) ^ N)
  have hB : ∑' i, B i ≠ ⊤ := by
    have h1 : ∀ i, B i ≠ ⊤ := by intro i; simp [B]
    have h2 : (∑' i, B i).toReal = ∑' i, (B i).toReal := ENNReal.tsum_toReal_eq h1
    have h3 : ∀ i, (B i).toReal = (1 / 2 : ℝ) ^ i := by
      intro i; simp [B, ENNReal.toReal_ofReal] <;> positivity
    have h4 : (∑' i, B i).toReal = ∑' i, (1 / 2 : ℝ) ^ i := by
      rw [h2]; congr with i; exact h3 i
    have h5 : ∑' i : ℕ, (1 / 2 : ℝ) ^ i = 2 := by
      rw [tsum_geometric_of_norm_lt_one] <;> norm_num
    have h6 : (∑' i, B i).toReal = 2 := by rw [h4, h5]
    have h7 : ∑' i, B i ≠ ⊤ := by
      intro h8; rw [h8] at h6; simp at h6
    exact h7
  have h_eLp_eq : ∀ n m, eLpNorm (h (k_seq n) - h (k_seq m)) 1 μ =
      ENNReal.ofReal (∫ x in K, |h (k_seq n) x - h (k_seq m) x|) := by
    intro n m
    have h_int : IntegrableOn (h (k_seq n) - h (k_seq m)) K := by
      apply IntegrableOn.sub
      · exact h_bounded_int (h (k_seq n)) (h_meas_h (k_seq n)) (h_bound_h (k_seq n))
      · exact h_bounded_int (h (k_seq m)) (h_meas_h (k_seq m)) (h_bound_h (k_seq m))
    have h_int' : Integrable (h (k_seq n) - h (k_seq m)) μ := h_int
    exact eLpNorm_one_eq_ofReal_abs_integral h_int'
  have h_cau_ennreal : ∀ N n m, N ≤ n → N ≤ m →
      eLpNorm (h (k_seq n) - h (k_seq m)) 1 μ < B N := by
    intro N n m hNn hNm
    rw [h_eLp_eq n m]
    have h_int : ∫ x in K, |h (k_seq n) x - h (k_seq m) x| ≤ (1 / 2 : ℝ) ^ (N + 1) :=
      hk_fast N n m hNn hNm
    have h_strict : (1 / 2 : ℝ) ^ (N + 1) < (1 / 2 : ℝ) ^ N := by
      have h : (1 / 2 : ℝ) ^ (N + 1) = (1 / 2 : ℝ) ^ N * (1 / 2 : ℝ) := by
        rw [pow_succ] <;> ring
      rw [h]
      have h_pos : 0 < (1 / 2 : ℝ) ^ N := by positivity
      exact mul_lt_of_lt_one_right h_pos (by norm_num)
    have h6 : ENNReal.ofReal (∫ x in K, |h (k_seq n) x - h (k_seq m) x|) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (N + 1)) :=
      ENNReal.ofReal_le_ofReal h_int
    have h7 : ENNReal.ofReal ((1 / 2 : ℝ) ^ (N + 1)) < ENNReal.ofReal ((1 / 2 : ℝ) ^ N) := by
      have h_posN : 0 < (1 / 2 : ℝ) ^ N := by positivity
      exact (ENNReal.ofReal_lt_ofReal_iff h_posN).mpr h_strict
    exact lt_of_le_of_lt h6 h7
  rcases MeasureTheory.Lp.cauchy_complete_eLpNorm (by norm_num) h_memLp hB h_cau_ennreal
    with ⟨g, hg_memLp, hg_tendsto⟩
  have hg_integrable : IntegrableOn g K := hg_memLp.integrable (by norm_num)
  have hg_conv_subseq_g : Tendsto (fun n => ∫ x in K, |h (k_seq n) x - g x|) atTop (nhds 0) := by
    have h_eq : ∀ n, eLpNorm (h (k_seq n) - g) 1 μ =
        ENNReal.ofReal (∫ x in K, |h (k_seq n) x - g x|) := by
      intro n
      have h_int : IntegrableOn (h (k_seq n) - g) K := by
        apply IntegrableOn.sub
        · exact h_bounded_int (h (k_seq n)) (h_meas_h (k_seq n)) (h_bound_h (k_seq n))
        · exact hg_integrable
      exact eLpNorm_one_eq_ofReal_abs_integral h_int
    have h_tendsto' : Tendsto (fun n => ENNReal.ofReal (∫ x in K, |h (k_seq n) x - g x|)) atTop (nhds 0) := by
      rw [funext h_eq] at hg_tendsto; exact hg_tendsto
    have h_nonneg : ∀ n, 0 ≤ ∫ x in K, |h (k_seq n) x - g x| := by intro n; positivity
    have h_main_tendsto : Tendsto (fun n => ∫ x in K, |h (k_seq n) x - g x|) atTop (nhds 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have h_pos_ennreal : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
      have h_event : ∀ᶠ n in atTop, ENNReal.ofReal (∫ x in K, |h (k_seq n) x - g x|) < ENNReal.ofReal ε :=
        h_tendsto' (Iio_mem_nhds h_pos_ennreal)
      rcases Filter.eventually_atTop.mp h_event with ⟨N, hN⟩
      refine ⟨N, fun n hn => ?_⟩
      have h9 : ENNReal.ofReal (∫ x in K, |h (k_seq n) x - g x|) < ENNReal.ofReal ε := hN n hn
      have h10 : 0 ≤ ∫ x in K, |h (k_seq n) x - g x| := h_nonneg n
      have h11 : ∫ x in K, |h (k_seq n) x - g x| < ε :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h10).mp h9
      simpa [Real.dist_eq, abs_of_nonneg h10] using h11
    exact h_main_tendsto
  have h_full_conv_g := l1_full_from_cauchy_subseq hK_meas hK_fin h g h_meas_h h_bound_h
    hg_integrable h_cauchy k_seq hk_strict hg_conv_subseq_g
  have h_binary_g := binary_l1_limit hK_meas hK_fin h g h_meas_h h_bound_h h_bin hg_integrable h_full_conv_g
  -- Replace g with a measurable representative
  have hg_ae : AEStronglyMeasurable g μ := hg_memLp.aestronglyMeasurable
  let g' : E n → ℝ := AEStronglyMeasurable.mk g hg_ae
  have hg'_meas : Measurable g' := hg_ae.measurable_mk
  have hg_eq : g =ᵐ[μ] g' := hg_ae.ae_eq_mk
  have hg'_eq : g' =ᵐ[μ] g := hg_eq.symm
  have hg'_integrable : IntegrableOn g' K := hg_integrable.congr hg_eq
  have hg'_conv_subseq : Tendsto (fun n => ∫ x in K, |h (k_seq n) x - g' x|) atTop (nhds 0) := by
    have h_eq : ∀ n, ∫ x in K, |h (k_seq n) x - g' x| = ∫ x in K, |h (k_seq n) x - g x| := by
      intro n
      apply integral_congr_ae
      filter_upwards [hg'_eq] with x hx
      rw [hx]
    rw [funext h_eq]
    exact hg_conv_subseq_g
  have h_full_conv := l1_full_from_cauchy_subseq hK_meas hK_fin h g' h_meas_h h_bound_h
    hg'_integrable h_cauchy k_seq hk_strict hg'_conv_subseq
  have h_binary : ∀ᵐ x ∂μ, g' x = 0 ∨ g' x = 1 := by
    filter_upwards [hg'_eq, h_binary_g] with x hx_eq hx_bin
    rw [hx_eq]
    exact hx_bin
  exact ⟨g', hg'_meas, hg'_integrable, h_full_conv, h_binary⟩

/-- If g_j1 and g_j2 are L¹ limits of the same indicator sequence on nested compact sets
K_j1 ⊆ K_j2, then g_j1 = g_j2 a.e. on K_j1. -/
lemma limits_compatible_across_scales
    (K1 K2 : Set (E n))
    (hK1_meas : MeasurableSet K1) (hK2_meas : MeasurableSet K2)
    (hK1_fin : volume K1 ≠ ⊤) (hK2_fin : volume K2 ≠ ⊤)
    (h_sub : K1 ⊆ K2)
    (h : ℕ → (E n → ℝ))
    (h_meas_h : ∀ k, Measurable (h k))
    (h_bound_h : ∀ k x, |h k x| ≤ 1)
    (g1 g2 : E n → ℝ)
    (hg1_integrable : IntegrableOn g1 K1)
    (hg2_integrable : IntegrableOn g2 K2)
    (hg1_conv : Tendsto (fun k => ∫ x in K1, |h k x - g1 x|) atTop (nhds 0))
    (hg2_conv : Tendsto (fun k => ∫ x in K2, |h k x - g2 x|) atTop (nhds 0)) :
    ∀ᵐ x ∂volume.restrict K1, g1 x = g2 x := by
  have h_bounded_int : ∀ (K : Set (E n)) (g : E n → ℝ), Measurable g → (∀ x, |g x| ≤ 1) → volume K ≠ ⊤ → IntegrableOn g K := by
    intro K g hg hbound hKfin
    have h_bound_ae : ∀ᵐ x ∂volume.restrict K, ‖g x‖ ≤ 1 := by
      filter_upwards with x
      have h_abs : ‖g x‖ = |g x| := by simp [Real.norm_eq_abs]
      rw [h_abs]; exact hbound x
    exact Measure.integrableOn_of_bounded hKfin hg.aestronglyMeasurable h_bound_ae
  have h_g2_on_K1 : IntegrableOn g2 K1 := hg2_integrable.mono_set h_sub
  let S : ℕ → ℝ := fun k =>
    (∫ x in K1, |g1 x - h k x|) + (∫ x in K1, |h k x - g2 x|)
  have h_eq1 : ∫ x in K1, |g1 x - g2 x| = 0 := by
    have h2 : ∀ k, ∫ x in K1, |g1 x - g2 x| ≤ S k := by
      intro k
      have h_pointwise : ∀ x, |g1 x - g2 x| ≤ |g1 x - h k x| + |h k x - g2 x| := by
        intro x
        have h_eq : g1 x - g2 x = (g1 x - h k x) + (h k x - g2 x) := by abel
        rw [h_eq]; exact abs_add_le _ _
      have h_ig1 : IntegrableOn (fun x => |g1 x - h k x|) K1 :=
        (IntegrableOn.sub hg1_integrable (h_bounded_int K1 (h k) (h_meas_h k) (h_bound_h k) hK1_fin)).norm
      have h_ig2 : IntegrableOn (fun x => |h k x - g2 x|) K1 := by
        have h_on_K2 : IntegrableOn (fun x => |h k x - g2 x|) K2 :=
          (IntegrableOn.sub (h_bounded_int K2 (h k) (h_meas_h k) (h_bound_h k) hK2_fin) hg2_integrable).norm
        exact h_on_K2.mono_set h_sub
      have h_ig12 : IntegrableOn (fun x => |g1 x - g2 x|) K1 :=
        (IntegrableOn.sub hg1_integrable h_g2_on_K1).norm
      have h_isum : IntegrableOn (fun x => |g1 x - h k x| + |h k x - g2 x|) K1 := h_ig1.add h_ig2
      have h_ae2 : ∀ᵐ x ∂volume.restrict K1, |g1 x - g2 x| ≤ (|g1 x - h k x| + |h k x - g2 x|) :=
        Eventually.of_forall (fun x => h_pointwise x)
      have h_int : ∫ x in K1, |g1 x - g2 x| ≤
          ∫ x in K1, (|g1 x - h k x| + |h k x - g2 x|) :=
        integral_mono_ae h_ig12 h_isum h_ae2
      have h_sum : ∫ x in K1, (|g1 x - h k x| + |h k x - g2 x|) = S k := by
        let f1 := fun x : E n => |g1 x - h k x|
        let f2 := fun x : E n => |h k x - g2 x|
        have h_main : MeasureTheory.integral (volume.restrict K1) (f1 + f2) =
            MeasureTheory.integral (volume.restrict K1) f1 + MeasureTheory.integral (volume.restrict K1) f2 :=
          integral_add' h_ig1 h_ig2
        have h_goal1 : ∫ x in K1, (|g1 x - h k x| + |h k x - g2 x|) =
            MeasureTheory.integral (volume.restrict K1) (f1 + f2) := by rfl
        have h_goal2 : S k = MeasureTheory.integral (volume.restrict K1) f1 + MeasureTheory.integral (volume.restrict K1) f2 := by
          simp [S, f1, f2] <;> rfl
        rw [h_goal1, h_main, h_goal2]
      rw [h_sum] at h_int
      exact h_int
    have h_conv1 : Tendsto (fun k => ∫ x in K1, |g1 x - h k x|) atTop (nhds 0) := by
      have h_eq : ∀ k, ∫ x in K1, |g1 x - h k x| = ∫ x in K1, |h k x - g1 x| := by
        intro k; apply integral_congr_ae; filter_upwards with x; rw [abs_sub_comm]
      exact (hg1_conv).congr (fun k => (h_eq k).symm)
    have h_conv2 : Tendsto (fun k => ∫ x in K1, |h k x - g2 x|) atTop (nhds 0) := by
      have h_le : ∀ k, ∫ x in K1, |h k x - g2 x| ≤ ∫ x in K2, |h k x - g2 x| := by
        intro k
        have h_on_K2 : IntegrableOn (fun x => |h k x - g2 x|) K2 :=
          (IntegrableOn.sub (h_bounded_int K2 (h k) (h_meas_h k) (h_bound_h k) hK2_fin) hg2_integrable).norm
        have h_on_K1 : IntegrableOn (fun x => |h k x - g2 x|) K1 := h_on_K2.mono_set h_sub
        have h_nonneg_ae : ∀ᵐ x ∂volume.restrict K2, 0 ≤ |h k x - g2 x| := by
          filter_upwards with x; exact abs_nonneg _
        have hst : K1 ≤ᵐ[volume] K2 := by filter_upwards with x; intro hx; exact h_sub hx
        exact MeasureTheory.setIntegral_mono_set h_on_K2 h_nonneg_ae hst
      exact squeeze_zero (fun k => integral_nonneg (fun x => abs_nonneg _)) h_le hg2_conv
    have h3 : Tendsto S atTop (nhds 0) := by
      have h3' := h_conv1.add h_conv2
      have h4 : (0 + 0 : ℝ) = 0 := by norm_num
      rw [h4] at h3'
      have h5 : (fun x : ℕ => (∫ (x_1 : E n) in K1, |g1 x_1 - h x x_1|) + (∫ (x_1 : E n) in K1, |h x x_1 - g2 x_1|)) = S := by
        funext k; simp [S]
      rw [h5] at h3'
      exact h3'
    have h4 : 0 ≤ ∫ x in K1, |g1 x - g2 x| := by positivity
    have h_le' : ∀ k, -S k ≤ -∫ x in K1, |g1 x - g2 x| := by
      intro k; linarith [h2 k]
    have h_neg : Tendsto (fun k => -S k) atTop (nhds 0) := by
      simpa using h3.neg
    have h_ge : (0 : ℝ) ≤ -∫ x in K1, |g1 x - g2 x| := le_of_tendsto' h_neg h_le'
    have h_le_zero : ∫ x in K1, |g1 x - g2 x| ≤ 0 := by linarith
    exact le_antisymm h_le_zero h4
  have h_ig12 : IntegrableOn (fun x => |g1 x - g2 x|) K1 :=
    (IntegrableOn.sub hg1_integrable h_g2_on_K1).norm
  have h5 : ∀ᵐ x ∂volume.restrict K1, |g1 x - g2 x| = 0 := by
    have h_nonneg : 0 ≤ (fun x : E n => |g1 x - g2 x|) := fun x => abs_nonneg _
    have h_iff := MeasureTheory.integral_eq_zero_iff_of_nonneg h_nonneg h_ig12
    exact h_iff.mp h_eq1
  filter_upwards [h5] with x hx
  have h6 : |g1 x - g2 x| = 0 := hx
  have h7 : g1 x - g2 x = 0 := abs_eq_zero.mp h6
  exact sub_eq_zero.mp h7

end Geometry
