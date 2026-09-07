import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.BVCompactnessTranslation.Helpers
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ}

/-- **L¹-Cauchy from mollified approximation (per-m limits)**.

Like `l1_cauchy_from_approximation`, but the L¹ limit of `f_{k,m}` as `k → ∞`
may depend on `m`. Only the convergence for the single `m` chosen in the
ε-argument is ever used. -/
lemma l1_cauchy_of_mollified_per_m
    {K : Set (E n)} (hK : MeasurableSet K) (hKfin : volume K ≠ ⊤)
    (h : ℕ → E n → ℝ) (f : ℕ → ℕ → E n → ℝ)
    (gjm : ℕ → E n → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (ε : ℕ → ℝ)
    (hε_pos : ∀ m, 0 < ε m)
    (hε_tendsto : Tendsto ε atTop (nhds 0))
    (h_meas_h : ∀ k, Measurable (h k))
    (h_bound_h : ∀ k x, |h k x| ≤ 1)
    (h_cont_f : ∀ k m, Continuous (f k m))
    (h_bound_f : ∀ k m x, 0 ≤ f k m x ∧ f k m x ≤ 1)
    (hgjm_cont : ∀ m, ContinuousOn (gjm m) K)
    (hgjm_bound : ∀ m x, x ∈ K → 0 ≤ gjm m x ∧ gjm m x ≤ 1)
    (h_error : ∀ k m, ∫ x in K, |h k x - f k m x| ≤ C * ε m)
    (h_conv : ∀ m, Tendsto (fun k => ∫ x in K, |f k m x - gjm m x|) atTop (nhds 0)) :
    ∀ (eps : ℝ), 0 < eps → ∃ N, ∀ k l, N ≤ k → N ≤ l →
      ∫ x in K, |h k x - h l x| ≤ eps := by
  have h_bounded_int : ∀ (g : E n → ℝ), Measurable g → (∀ x, |g x| ≤ 1) → IntegrableOn g K := by
    intro g hg hbound
    have h_bound_ae : ∀ᵐ x ∂volume.restrict K, ‖g x‖ ≤ 1 := by
      filter_upwards with x
      have h_abs : ‖g x‖ = |g x| := by simp [Real.norm_eq_abs]
      rw [h_abs]; exact hbound x
    exact Measure.integrableOn_of_bounded hKfin hg.aestronglyMeasurable h_bound_ae
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
  have h_f_conv : ∃ N, ∀ k ≥ N, ∫ x in K, |f k m x - gjm m x| ≤ eps / 4 := by
    have h : Tendsto (fun k => ∫ x in K, |f k m x - gjm m x|) atTop (nhds 0) := h_conv m
    have h' := Metric.tendsto_atTop.mp h (eps / 4) (by linarith)
    rcases h' with ⟨N, hN⟩
    refine ⟨N, fun k hk => ?_⟩
    have h_dist : dist (∫ x in K, |f k m x - gjm m x|) 0 < eps / 4 := hN k hk
    have h_nonneg : 0 ≤ ∫ x in K, |f k m x - gjm m x| := by positivity
    simpa [Real.dist_eq, abs_of_nonneg h_nonneg] using h_dist.le
  rcases h_f_conv with ⟨N, hN⟩
  refine ⟨N, fun k l hk hl => ?_⟩
  have h1 : ∀ x, |h k x - h l x| ≤ |h k x - f k m x| + |f k m x - gjm m x|
        + |gjm m x - f l m x| + |f l m x - h l x| := by
    intro x
    set a := h k x - f k m x with ha
    set b := f k m x - gjm m x with hb
    set c := gjm m x - f l m x with hc
    set d := f l m x - h l x with hd
    have h_eq : h k x - h l x = a + b + c + d := by
      dsimp only [a, b, c, d] <;> abel
    rw [h_eq]
    have h2 : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
      have h21 : |a + b + c + d| ≤ |a + b| + |c + d| := by
        calc |a + b + c + d|
          = |(a + b) + (c + d)| := by abel_nf
        _ ≤ |a + b| + |c + d| := norm_add_le (a + b) (c + d)
      have h22 : |a + b| ≤ |a| + |b| := norm_add_le a b
      have h23 : |c + d| ≤ |c| + |d| := norm_add_le c d
      linarith
    exact h2
  have h_f_bound : ∀ k m x, |f k m x| ≤ 1 := by
    intro k m x
    have h1 : 0 ≤ f k m x ∧ f k m x ≤ 1 := h_bound_f k m x
    rw [abs_of_nonneg h1.1]; exact h1.2
  have h_int_hk : IntegrableOn (h k) K := h_bounded_int (h k) (h_meas_h k) (h_bound_h k)
  have h_int_hl : IntegrableOn (h l) K := h_bounded_int (h l) (h_meas_h l) (h_bound_h l)
  have h_int_fk : IntegrableOn (f k m) K :=
    h_bounded_int (f k m) (h_cont_f k m).measurable (h_f_bound k m)
  have h_int_fl : IntegrableOn (f l m) K :=
    h_bounded_int (f l m) (h_cont_f l m).measurable (h_f_bound l m)
  have h_int_gjm : IntegrableOn (gjm m) K := by
    have h_ae : AEStronglyMeasurable (gjm m) (volume.restrict K) :=
      (hgjm_cont m).aestronglyMeasurable hK
    have h_bound_ae : ∀ᵐ x ∂volume.restrict K, ‖gjm m x‖ ≤ 1 := by
      filter_upwards [ae_restrict_mem hK] with x hx
      have h2 : 0 ≤ gjm m x ∧ gjm m x ≤ 1 := hgjm_bound m x hx
      have h_abs : ‖gjm m x‖ = |gjm m x| := by simp [Real.norm_eq_abs]
      rw [h_abs, abs_of_nonneg h2.1]; exact h2.2
    have hK_lt : volume K < ⊤ := lt_top_iff_ne_top.mpr hKfin
    exact IntegrableOn.of_bound hK_lt h_ae 1 h_bound_ae
  let f1 := fun x : E n => |h k x - f k m x|
  let f2 := fun x : E n => |f k m x - gjm m x|
  let f3 := fun x : E n => |gjm m x - f l m x|
  let f4 := fun x : E n => |f l m x - h l x|
  have h_i1 : IntegrableOn f1 K := (h_int_hk.sub h_int_fk).abs
  have h_i2 : IntegrableOn f2 K := (h_int_fk.sub h_int_gjm).abs
  have h_i3 : IntegrableOn f3 K := (h_int_gjm.sub h_int_fl).abs
  have h_i4 : IntegrableOn f4 K := (h_int_fl.sub h_int_hl).abs
  have h_int_sum : IntegrableOn (fun x => f1 x + f2 x + f3 x + f4 x) K :=
    h_i1.add h_i2 |>.add h_i3 |>.add h_i4
  have h_int_hl2 : IntegrableOn (fun x => |h k x - h l x|) K :=
    (h_int_hk.sub h_int_hl).abs
  have h_mono : ∫ x in K, |h k x - h l x| ≤
      ∫ x in K, (f1 x + f2 x + f3 x + f4 x) := by
    have h_point : ∀ x ∈ K, |h k x - h l x| ≤ f1 x + f2 x + f3 x + f4 x := fun x _ => h1 x
    exact MeasureTheory.setIntegral_mono_on h_int_hl2 h_int_sum hK h_point
  have h_result : ∫ x in K, (f1 x + f2 x + f3 x + f4 x) =
      (∫ x in K, f1 x) + (∫ x in K, f2 x) + (∫ x in K, f3 x) + (∫ x in K, f4 x) := by
    have h_eq1 : ∫ x in K, (f1 x + f2 x) = (∫ x in K, f1 x) + (∫ x in K, f2 x) := by
      simpa [Pi.add_apply] using MeasureTheory.integral_add' h_i1 h_i2
    have h_i12 : IntegrableOn (fun x => f1 x + f2 x) K := h_i1.add h_i2
    have h_i123 : IntegrableOn (fun x => f1 x + f2 x + f3 x) K := h_i12.add h_i3
    have h_eq2 : ∫ x in K, (f1 x + f2 x + f3 x) = (∫ x in K, (f1 x + f2 x)) + (∫ x in K, f3 x) := by
      simpa [Pi.add_apply] using MeasureTheory.integral_add' h_i12 h_i3
    have h_eq3 : ∫ x in K, (f1 x + f2 x + f3 x + f4 x) =
        (∫ x in K, (f1 x + f2 x + f3 x)) + (∫ x in K, f4 x) := by
      simpa [Pi.add_apply] using MeasureTheory.integral_add' h_i123 h_i4
    calc
      ∫ x in K, (f1 x + f2 x + f3 x + f4 x)
        = (∫ x in K, (f1 x + f2 x + f3 x)) + (∫ x in K, f4 x) := h_eq3
      _ = ((∫ x in K, (f1 x + f2 x)) + (∫ x in K, f3 x)) + (∫ x in K, f4 x) := by rw [h_eq2]
      _ = (∫ x in K, f1 x) + (∫ x in K, f2 x) + (∫ x in K, f3 x) + (∫ x in K, f4 x) := by
        rw [h_eq1] <;> ring
  rw [h_result] at h_mono
  have h_e1 : ∫ x in K, f1 x ≤ C * ε m := by
    have h_eq : ∀ x, f1 x = |f k m x - h k x| := by
      intro x; exact abs_sub_comm (h k x) (f k m x)
    have h_int_eq : ∫ x in K, f1 x = ∫ x in K, |f k m x - h k x| :=
      MeasureTheory.setIntegral_congr_fun hK (fun x _ => h_eq x)
    rw [h_int_eq]
    have h_eq2 : ∫ x in K, |f k m x - h k x| = ∫ x in K, |h k x - f k m x| := by
      apply MeasureTheory.setIntegral_congr_fun hK; intro x _
      exact abs_sub_comm (f k m x) (h k x)
    rw [h_eq2]; exact h_error k m
  have h_e2 : ∫ x in K, f2 x ≤ eps / 4 := hN k hk
  have h_e3 : ∫ x in K, f3 x ≤ eps / 4 := by
    have h_eq : ∀ x, f3 x = |f l m x - gjm m x| := by
      intro x; exact abs_sub_comm (gjm m x) (f l m x)
    have h_int_eq : ∫ x in K, f3 x = ∫ x in K, |f l m x - gjm m x| :=
      MeasureTheory.setIntegral_congr_fun hK (fun x _ => h_eq x)
    rw [h_int_eq]
    exact hN l hl
  have h_e4 : ∫ x in K, f4 x ≤ C * ε m := by
    have h_eq : ∀ x, f4 x = |h l x - f l m x| := by
      intro x; exact abs_sub_comm (f l m x) (h l x)
    have h_int_eq : ∫ x in K, f4 x = ∫ x in K, |h l x - f l m x| :=
      MeasureTheory.setIntegral_congr_fun hK (fun x _ => h_eq x)
    rw [h_int_eq]; exact h_error l m
  linarith

end Geometry
