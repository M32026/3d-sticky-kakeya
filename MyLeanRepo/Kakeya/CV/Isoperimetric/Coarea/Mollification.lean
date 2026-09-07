import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic

/-!
# Mollification Assembly for Relative Isoperimetric Inequality

Provides convergence lemmas for mollifications of characteristic functions.
Uses Mathlib's `ContDiffBump` convolution infrastructure.

## Main results

- `mollify_contDiff`: mollification of a characteristic function is smooth
- `mollify_bound`: 0 ≤ u_ε ≤ 1
- `mollify_tendsto_ae`: mollification converges pointwise a.e.
- `mollify_tendsto_L1`: mollification converges in L¹ on compact sets
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory Convolution Topology

namespace Geometry

variable {n : ℕ} [Nonempty (Fin n)]

abbrev Euc n := EuclideanSpace ℝ (Fin n)

namespace Mollification

/-- A standard family of mollifiers: `rIn = ε/2`, `rOut = ε`. -/
noncomputable def mollifier (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : Euc n) :=
  ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩

/-- The normalized mollifier (integral = 1). -/
noncomputable def rho (ε : ℝ) (hε : 0 < ε) : Euc n → ℝ :=
  (mollifier ε hε).normed volume

/-- Mollification `u_ε = f * ρ_ε`. -/
noncomputable def mollify (ε : ℝ) (hε : 0 < ε) (f : Euc n → ℝ) : Euc n → ℝ :=
  convolution (rho ε hε) f (ContinuousLinearMap.lsmul ℝ ℝ) volume

-- Helper: characteristic function is locally integrable
private lemma char_localIntegrable {E : Set (Euc n)} (hE : MeasurableSet E) :
    LocallyIntegrable (Set.indicator E (fun _ => (1 : ℝ))) volume := by
  let f : Euc n → ℝ := Set.indicator E (fun _ => (1 : ℝ))
  have h1 : Measurable f := measurable_const.indicator hE
  have h2 : ∀ x, ‖f x‖ ≤ 1 := by
    intro x
    by_cases h : x ∈ E <;> simp [f, h, norm_norm] <;> norm_num
  intro x
  have h_ball_open : IsOpen (ball x 1) := isOpen_ball
  have h_ball_mem : ball x 1 ∈ nhds x := ball_mem_nhds x (by norm_num)
  have h_fin : volume (ball x 1) ≠ ⊤ := by
    have h_bdd : Bornology.IsBounded (ball x 1) := Metric.isBounded_ball
    exact h_bdd.measure_lt_top.ne
  have h_int : IntegrableOn f (ball x 1) volume :=
    MeasureTheory.Measure.integrableOn_of_bounded h_fin h1.aestronglyMeasurable (M := 1)
      (by filter_upwards with y; exact h2 y)
  exact ⟨ball x 1, h_ball_mem, h_int⟩

/-- Public wrapper: characteristic function of a measurable set is locally integrable. -/
lemma characteristic_localIntegrable {E : Set (Euc n)} (hE : MeasurableSet E) :
    LocallyIntegrable (Set.indicator E (fun _ => (1 : ℝ))) volume :=
  char_localIntegrable hE

/-- The mollification of a characteristic function is smooth. -/
lemma mollify_contDiff {E : Set (Euc n)} (hE : MeasurableSet E) (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (mollify ε hε (Set.indicator E (fun _ => (1 : ℝ)))) := by
  let φ : ContDiffBump (0 : Euc n) := mollifier ε hε
  let f : Euc n → ℝ := Set.indicator E (fun _ => (1 : ℝ))
  have h1 : HasCompactSupport (rho ε hε) := φ.hasCompactSupport_normed
  have h3 : LocallyIntegrable f volume := char_localIntegrable hE
  have h2 : ContDiff ℝ (↑(⊤ : ℕ∞)) (rho ε hε) :=
    (φ.contDiff_normed : ContDiff ℝ (↑(⊤ : ℕ∞)) (rho ε hε))
  exact h1.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) h2 h3

/-- For a characteristic function, 0 ≤ u_ε ≤ 1. -/
lemma mollify_bound {E : Set (Euc n)} (hE : MeasurableSet E) (ε : ℝ) (hε : 0 < ε) :
    ∀ x, 0 ≤ mollify ε hε (Set.indicator E (fun _ => (1 : ℝ))) x ∧
           mollify ε hε (Set.indicator E (fun _ => (1 : ℝ))) x ≤ 1 := by
  let φ : ContDiffBump (0 : Euc n) := mollifier ε hε
  let ρ : Euc n → ℝ := rho ε hε
  let f : Euc n → ℝ := Set.indicator E (fun _ => (1 : ℝ))
  let u : Euc n → ℝ := mollify ε hε f
  have hρ_cont : Continuous ρ := φ.continuous_normed
  have hρ_nonneg : ∀ x, 0 ≤ ρ x := φ.nonneg_normed
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x; by_cases h : x ∈ E <;> simp [f, h] <;> norm_num
  have hf_le_one : ∀ x, f x ≤ 1 := by
    intro x; by_cases h : x ∈ E <;> simp [f, h] <;> norm_num
  have h_support : HasCompactSupport ρ := φ.hasCompactSupport_normed
  have h3 : LocallyIntegrable f volume := char_localIntegrable hE
  have h_exists : ConvolutionExists ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    h_support.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ_cont h3
  have h_exists_const : ConvolutionExists ρ (fun _ => (1 : ℝ)) (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    h_support.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ_cont
      (locallyIntegrable_const (1 : ℝ))
  intro x
  have h_conv1 : ConvolutionExistsAt ρ f x (ContinuousLinearMap.lsmul ℝ ℝ) volume := h_exists x
  have h_conv_const : ConvolutionExistsAt ρ (fun _ => (1 : ℝ)) x (ContinuousLinearMap.lsmul ℝ ℝ) volume := h_exists_const x
  have h_nonneg : 0 ≤ u x := by
    dsimp only [u, mollify, convolution]
    apply integral_nonneg
    intro t
    have h5 : 0 ≤ ρ t := hρ_nonneg t
    have h6 : 0 ≤ f (x - t) := hf_nonneg (x - t)
    simpa [ContinuousLinearMap.lsmul_apply] using mul_nonneg h5 h6
  have h_eq_const : convolution ρ (fun _ => (1 : ℝ)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x = 1 := by
    have h_exists2 : ConvolutionExistsAt ρ (fun _ => (1 : ℝ)) x (ContinuousLinearMap.lsmul ℝ ℝ) volume := h_exists_const x
    have h_int : ∫ (t : Euc n), ρ t = 1 := φ.integral_normed
    simpa [convolution_def, ContinuousLinearMap.lsmul_apply] using h_int
  have h_le_one : u x ≤ 1 := by
    have h_mono : u x ≤ convolution ρ (fun _ => (1 : ℝ)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x :=
      MeasureTheory.convolution_mono_right h_conv1 h_conv_const hρ_nonneg hf_le_one
    rw [h_eq_const] at h_mono
    exact h_mono
  exact ⟨h_nonneg, h_le_one⟩

/-- Mollification converges a.e. to a locally integrable function. -/
lemma mollify_tendsto_ae {f : Euc n → ℝ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂volume,
      Filter.Tendsto (fun k : ℕ => mollify (1 / (k + 2 : ℝ)) (by positivity) f x)
        atTop (nhds (f x)) := by
  let φ : ℕ → ContDiffBump (0 : Euc n) := fun k =>
    mollifier (1 / (k + 2 : ℝ)) (by positivity)
  have h_rOut_eq : ∀ k : ℕ, (φ k).rOut = 1 / (k + 2 : ℝ) := by
    intro k; rfl
  have hφ : Filter.Tendsto (fun k : ℕ => (φ k).rOut) atTop (nhds (0 : ℝ)) := by
    rw [funext h_rOut_eq]
    have h_shift : Filter.Tendsto (fun k : ℕ => k + 2) atTop atTop :=
      tendsto_atTop_mono (fun k : ℕ => Nat.le_add_right k 2) tendsto_id
    have h_div : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((k + 2 : ℕ) : ℝ)) atTop (nhds 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp h_shift
    simpa using h_div
  have h'φ : ∀ k : ℕ, (φ k).rOut ≤ 2 * (φ k).rIn := by
    intro k
    simp [φ, mollifier]
    <;> ring_nf <;> norm_num
  have h_main : ∀ᵐ (x : Euc n) ∂volume,
      Filter.Tendsto (fun k : ℕ =>
        ((φ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x)
        atTop (nhds (f x)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      hφ (Filter.Eventually.of_forall h'φ) hf
  have h_eq : (fun k : ℕ => mollify (1 / (k + 2 : ℝ)) (by positivity) f) =
      fun k : ℕ => ((φ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) := by
    funext k
    rfl
  have h_final : ∀ᵐ (x : Euc n) ∂volume,
      Filter.Tendsto (fun k : ℕ => mollify (1 / (k + 2 : ℝ)) (by positivity) f x)
        atTop (nhds (f x)) := by
    filter_upwards [h_main] with x hx
    have h_eq2 : (fun k : ℕ => mollify (1 / (k + 2 : ℝ)) (by positivity) f x) =
        (fun k : ℕ => ((φ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x) := by
      funext k; rfl
    rw [h_eq2]
    exact hx
  exact h_final

/-- Mollification of a characteristic function converges in L¹ on compact sets. -/
lemma mollify_tendsto_L1 {E : Set (Euc n)} (hE : MeasurableSet E)
    {K : Set (Euc n)} (hK : IsCompact K) :
    Filter.Tendsto (fun k : ℕ =>
      ∫ x in K, |mollify (1 / (k + 2 : ℝ)) (by positivity)
        (Set.indicator E (fun _ => (1 : ℝ))) x -
        Set.indicator E (fun _ => (1 : ℝ)) x|)
      atTop (nhds 0) := by
  let χ : Euc n → ℝ := Set.indicator E (fun _ => (1 : ℝ))
  let u : ℕ → Euc n → ℝ := fun k =>
    mollify (1 / (k + 2 : ℝ)) (by positivity) χ
  let F : ℕ → Euc n → ℝ := fun k x => |u k x - χ x|
  have h_local : LocallyIntegrable χ volume := char_localIntegrable hE
  have h_bdd : ∀ k x, |u k x - χ x| ≤ 1 := by
    intro k x
    have h1 : 0 ≤ u k x := (mollify_bound hE _ _) x |>.1
    have h2 : u k x ≤ 1 := (mollify_bound hE _ _) x |>.2
    have h3 : 0 ≤ χ x := by
      by_cases h : x ∈ E <;> simp [χ, h] <;> norm_num
    have h4 : χ x ≤ 1 := by
      by_cases h : x ∈ E <;> simp [χ, h] <;> norm_num
    rw [abs_le]
    constructor <;> linarith
  have h_ae : ∀ᵐ x ∂volume, Filter.Tendsto (fun k => u k x) atTop (nhds (χ x)) :=
    mollify_tendsto_ae h_local
  have h_ae_restrict : ∀ᵐ x ∂volume.restrict K,
      Filter.Tendsto (fun k => u k x) atTop (nhds (χ x)) :=
    ae_restrict_of_ae h_ae
  have h_ae_diff : ∀ᵐ x ∂volume.restrict K,
      Filter.Tendsto (fun k => F k x) atTop (nhds 0) := by
    filter_upwards [h_ae_restrict] with x hx
    have h_sub : Filter.Tendsto (fun k => u k x - χ x) atTop (nhds (χ x - χ x)) :=
      hx.sub tendsto_const_nhds
    simpa [F] using h_sub.abs
  have hK_meas : MeasurableSet K := hK.measurableSet
  have hK_fin : volume K ≠ ⊤ := hK.measure_lt_top.ne
  have h_ae_sm : ∀ k, AEStronglyMeasurable (F k) (volume.restrict K) := by
    intro k
    have h_cont : Continuous (u k) := (mollify_contDiff hE _ _).continuous
    have h_χ_meas : Measurable χ := measurable_const.indicator hE
    have h_sub : AEStronglyMeasurable (u k - χ) (volume.restrict K) :=
      h_cont.aestronglyMeasurable.sub h_χ_meas.aestronglyMeasurable
    exact h_sub.norm
  have hK_fin' : (volume.restrict K) univ ≠ ⊤ := by
    simpa [Measure.restrict_apply] using hK_fin
  have hK_fin'' : (volume.restrict K) univ < ⊤ := lt_top_iff_ne_top.mpr hK_fin'
  letI : IsFiniteMeasure (volume.restrict K) := ⟨hK_fin''⟩
  have h_bound_int : Integrable (fun _ : Euc n => (1 : ℝ)) (volume.restrict K) :=
    integrable_const (1 : ℝ)
  have h_bound : ∀ k, ∀ᵐ x ∂volume.restrict K, ‖F k x‖ ≤ (1 : ℝ) := by
    intro k
    filter_upwards [self_mem_ae_restrict hK_meas] with x _
    simpa [F, norm_norm] using h_bdd k x
  have h_main := MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun _ : Euc n => (1 : ℝ))
    (F_measurable := h_ae_sm)
    (bound_integrable := h_bound_int)
    (h_bound := h_bound)
    (h_lim := h_ae_diff)
  have h_zero_int : (∫ x in K, (0 : ℝ)) = 0 := by simp
  have h_main2 : Filter.Tendsto (fun k : ℕ =>
      ∫ x in K, F k x) atTop (nhds 0) := by
    rw [h_zero_int] at h_main
    exact h_main
  have h_final2 : Filter.Tendsto (fun k : ℕ =>
      ∫ x in K, |mollify (1 / (k + 2 : ℝ)) (by positivity)
        (Set.indicator E (fun _ => (1 : ℝ))) x -
        Set.indicator E (fun _ => (1 : ℝ)) x|)
      atTop (nhds 0) := by
    have h_eq3 : (fun k : ℕ => ∫ x in K, F k x) =
        (fun k : ℕ => ∫ x in K, |mollify (1 / (k + 2 : ℝ)) (by positivity)
          (Set.indicator E (fun _ => (1 : ℝ))) x -
          Set.indicator E (fun _ => (1 : ℝ)) x|) := by
      funext k
      congr with x
      <;> simp [F]
      <;> rfl
    rw [h_eq3]
    exact h_main2
  exact h_final2

/-- Canonical mollification sequence for a characteristic function:
`u_k = χ_E * ρ_{1/(k+2)}`. -/
noncomputable def mollificationSeq {E : Set (Euc n)} (hE : MeasurableSet E) (k : ℕ) : Euc n → ℝ :=
  mollify (1 / (k + 2 : ℝ)) (by positivity) (Set.indicator E (fun _ => (1 : ℝ)))

end Mollification

end Geometry
