import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-!
# 1D L¹-L∞ Duality for Continuous Functions

For a continuous compactly supported scalar function `f`,
`∫ |f| = sup { |∫ f · φ| : φ smooth, compactly supported, |φ| ≤ 1 }`.

We prove the non-trivial direction: for any `ε > 0`, there exists smooth
compactly supported `φ` with `|φ| ≤ 1` and `∫ f · φ ≥ ∫ |f| - ε`.
-/


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry

variable {n : ℕ}

/-- **Approximate sign function.**

For continuous compactly supported `f` and `ε > 0`,
`φ_ε(x) = f(x) / max(|f(x)|, ε)` is continuous, compactly supported,
`|φ_ε| ≤ 1`, and `∫ f · φ_ε ≥ ∫ |f| - ε · μ(tsupport f)`. -/
lemma approximate_sign {n : ℕ} [Nonempty (Fin n)]
    {f : E n → ℝ} (hf_cont : Continuous f) (hf_support : HasCompactSupport f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (φ_ε : E n → ℝ), Continuous φ_ε ∧ HasCompactSupport φ_ε ∧
      (∀ x, |φ_ε x| ≤ 1) ∧
      (∫ x, f x * φ_ε x) ≥ (∫ x, |f x|) - ε * ENNReal.toReal (volume (tsupport f)) := by
  let φ_ε : E n → ℝ := fun x => f x / max (|f x|) ε
  let g : E n → ℝ := fun x => |f x| - f x * φ_ε x
  have h_max_pos : ∀ x, 0 < max (|f x|) ε := by
    intro x; have h : ε ≤ max (|f x|) ε := le_max_right _ _; linarith
  have h_cont : Continuous φ_ε := by
    have h1 : Continuous (fun x => |f x|) := by fun_prop
    have h2 : Continuous (fun x => max (|f x|) ε) := by fun_prop
    exact hf_cont.div h2 (fun x => (h_max_pos x).ne')
  have h_support : Function.support φ_ε ⊆ Function.support f := by
    intro x hx
    by_contra h
    have hf0 : f x = 0 := by simpa [Function.mem_support] using h
    have hφ0 : φ_ε x = 0 := by simp [φ_ε, hf0]
    exact hx hφ0
  have h_compact : HasCompactSupport φ_ε := hf_support.mono h_support
  have h_bound : ∀ x, |φ_ε x| ≤ 1 := by
    intro x
    have h1 : |φ_ε x| = |f x| / max (|f x|) ε := by
      calc
        |φ_ε x| = |f x / max (|f x|) ε| := by rfl
        _ = |f x| / |max (|f x|) ε| := by rw [abs_div]
        _ = |f x| / max (|f x|) ε := by
          have hpos : 0 ≤ max (|f x|) ε := by positivity
          rw [abs_of_nonneg hpos]
    rw [h1]
    have h2 : |f x| ≤ max (|f x|) ε := le_max_left _ _
    have h3 : 0 < max (|f x|) ε := h_max_pos x
    exact (div_le_one h3).mpr h2
  have h_main : ∀ x, f x * φ_ε x ≥ |f x| - ε := by
    intro x
    dsimp only [φ_ε]
    by_cases h : |f x| ≤ ε
    · have h4 : 0 ≤ f x * (f x / max (|f x|) ε) := by
        have h5 : 0 ≤ (f x)^2 := sq_nonneg _
        have h6 : 0 < max (|f x|) ε := h_max_pos x
        have h7 : 0 ≤ (f x)^2 / max (|f x|) ε := by positivity
        have h8 : f x * (f x / max (|f x|) ε) = (f x)^2 / max (|f x|) ε := by ring
        rw [h8]; exact h7
      have h9 : |f x| - ε ≤ 0 := by linarith
      linarith
    · have h2 : ε < |f x| := by linarith
      have h3 : max (|f x|) ε = |f x| := by rw [max_eq_left] <;> linarith
      have hfx_ne_zero : f x ≠ 0 := by
        intro h7; rw [h7] at h2; simp at h2 <;> linarith
      have h4 : f x * (f x / max (|f x|) ε) = |f x| := by
        rw [h3]
        have h5 : f x * (f x / |f x|) = (f x)^2 / |f x| := by ring
        rw [h5]
        have h6 : (f x)^2 = |f x|^2 := by rw [sq_abs]
        rw [h6]
        have h7 : |f x| ^ 2 / |f x| = |f x| := by
          field_simp [hfx_ne_zero, abs_pos.mpr hfx_ne_zero] <;> ring
        exact h7
      rw [h4] <;> linarith
  have h_nonneg : ∀ x, 0 ≤ g x := by
    intro x
    dsimp only [g]
    by_cases h : |f x| ≤ ε
    · have h5 : max (|f x|) ε = ε := by rw [max_eq_right] <;> linarith
      have h6 : (f x)^2 ≤ ε * |f x| := by
        have h7 : (f x)^2 = |f x|^2 := by rw [sq_abs]
        rw [h7]
        have h8 : |f x| ≤ ε := h
        nlinarith [abs_nonneg (f x)]
      have h9 : f x * φ_ε x = (f x)^2 / ε := by
        dsimp only [φ_ε]; rw [h5] <;> ring
      rw [h9]
      have h10 : (f x)^2 / ε ≤ |f x| := by
        have h11 : (f x)^2 ≤ ε * |f x| := h6
        have h12 : (f x)^2 / ε ≤ (ε * |f x|) / ε := by gcongr
        have h13 : (ε * |f x|) / ε = |f x| := by
          field_simp [hε.ne'] <;> ring
        rw [h13] at h12
        exact h12
      linarith
    · have h2 : ε < |f x| := by linarith
      have h3 : max (|f x|) ε = |f x| := by rw [max_eq_left] <;> linarith
      have hfx_ne_zero : f x ≠ 0 := by
        intro h7; rw [h7] at h2; simp at h2 <;> linarith
      have h4 : f x * φ_ε x = |f x| := by
        dsimp only [φ_ε]; rw [h3]
        have h5 : f x * (f x / |f x|) = (f x)^2 / |f x| := by ring
        rw [h5]
        have h6 : (f x)^2 = |f x|^2 := by rw [sq_abs]
        rw [h6]
        have h7 : |f x| ^ 2 / |f x| = |f x| := by
          field_simp [hfx_ne_zero, abs_pos.mpr hfx_ne_zero] <;> ring
        exact h7
      rw [h4] <;> linarith
  have h6 : ∀ x, g x ≤ ε := by
    intro x; dsimp only [g]; linarith [h_main x]
  have h_support_g : ∀ x ∉ tsupport f, g x = 0 := by
    intro x hx
    have hf0 : f x = 0 := by
      have h : x ∉ Function.support f := fun h => hx (subset_closure h)
      simpa [Function.mem_support] using h
    have hφ0 : φ_ε x = 0 := by simp [φ_ε, hf0]
    simp [g, hf0, hφ0]
  have h_integrable_f : Integrable f volume :=
    hf_cont.integrable_of_hasCompactSupport hf_support
  have h_integrable_φ : Integrable φ_ε volume :=
    h_cont.integrable_of_hasCompactSupport h_compact
  have h_cont_fφ : Continuous (fun x => f x * φ_ε x) := hf_cont.mul h_cont
  have h_support_fφ : HasCompactSupport (fun x => f x * φ_ε x) := by
    have h : Function.support (fun x => f x * φ_ε x) ⊆ Function.support f := by
      intro x hx
      by_contra h
      have hf0 : f x = 0 := by simpa [Function.mem_support] using h
      have hprod : f x * φ_ε x = 0 := by rw [hf0]; ring
      exact hx hprod
    exact hf_support.mono h
  have h_integrable_fφ : Integrable (fun x => f x * φ_ε x) volume :=
    h_cont_fφ.integrable_of_hasCompactSupport h_support_fφ
  have h_integrable_abs : Integrable (fun x => |f x|) volume := h_integrable_f.norm
  have h_integrable_g : Integrable g volume := h_integrable_abs.sub h_integrable_fφ
  have h_vol_fin : volume (tsupport f) < ⊤ := hf_support.measure_lt_top
  -- Apply integral_le_measure to g/ε
  have h11 : ∀ x ∈ tsupport f, (g x / ε) ≤ 1 := by
    intro x _
    have h : g x ≤ ε := h6 x
    exact (div_le_one hε).mpr h
  have h12 : ∀ x ∉ tsupport f, (g x / ε) ≤ 0 := by
    intro x hx
    have hg0 : g x = 0 := h_support_g x hx
    rw [hg0] <;> simp
  have h13 : ENNReal.ofReal (∫ x, (g x / ε)) ≤ volume (tsupport f) :=
    MeasureTheory.integral_le_measure h11 h12
  have h14 : (∫ x, (g x / ε)) = (1 / ε) * ∫ x, g x := by
    have h : (fun x => g x / ε) = fun x => (1 / ε) * g x := by funext x; ring
    rw [h]
    rw [integral_const_mul]
  rw [h14] at h13
  have h15 : (1 / ε) * ∫ x, g x ≤ ENNReal.toReal (volume (tsupport f)) := by
    have h_nonneg_int : 0 ≤ ∫ x, g x := by
      apply integral_nonneg
      exact h_nonneg
    have h_pos : 0 ≤ (1 / ε) * ∫ x, g x := by positivity
    have h : ENNReal.ofReal ((1 / ε) * ∫ x, g x) ≤ volume (tsupport f) := h13
    have h_ne_top1 : ENNReal.ofReal ((1 / ε) * ∫ x, g x) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h_ne_top2 : volume (tsupport f) ≠ ⊤ := h_vol_fin.ne
    have h_iff : (ENNReal.ofReal ((1 / ε) * ∫ x, g x)).toReal ≤ (volume (tsupport f)).toReal ↔
        ENNReal.ofReal ((1 / ε) * ∫ x, g x) ≤ volume (tsupport f) :=
      ENNReal.toReal_le_toReal h_ne_top1 h_ne_top2
    have h2 : (ENNReal.ofReal ((1 / ε) * ∫ x, g x)).toReal ≤ (volume (tsupport f)).toReal :=
      h_iff.mpr h
    have h3 : (ENNReal.ofReal ((1 / ε) * ∫ x, g x)).toReal = (1 / ε) * ∫ x, g x := by
      rw [ENNReal.toReal_ofReal h_pos]
    rw [h3] at h2
    exact h2
  have h16 : ∫ x, g x ≤ ε * ENNReal.toReal (volume (tsupport f)) := by
    have h17 : (1 / ε) * ∫ x, g x ≤ ENNReal.toReal (volume (tsupport f)) := h15
    have h18 : ∫ x, g x ≤ ε * ENNReal.toReal (volume (tsupport f)) := by
      calc
        ∫ x, g x = ε * ((1 / ε) * ∫ x, g x) := by field_simp [hε.ne'] <;> ring
        _ ≤ ε * ENNReal.toReal (volume (tsupport f)) := by gcongr
    exact h18
  have h19 : ∫ x, g x = (∫ x, |f x|) - ∫ x, f x * φ_ε x := by
    rw [integral_sub h_integrable_abs h_integrable_fφ] <;> rfl
  rw [h19] at h16
  exact ⟨φ_ε, h_cont, h_compact, h_bound, by linarith⟩

namespace Perimeter

/-- **Smooth approximate sign function.**

For continuous compactly supported `f` and `η > 0`, there exists smooth
compactly supported `ψ` with `|ψ| ≤ 1` and `∫ f · ψ ≥ ∫ |f| - η`. -/
lemma smooth_approximate_sign {n : ℕ} [Nonempty (Fin n)]
    {f : E n → ℝ} (hf_cont : Continuous f) (hf_support : HasCompactSupport f)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ψ : E n → ℝ), ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (∀ x, |ψ x| ≤ 1) ∧
      (∫ x, f x * ψ x) ≥ (∫ x, |f x|) - η := by
  by_cases h_vol : volume (tsupport f) = 0
  · -- If tsupport has measure 0, then f = 0 a.e.
    have h1 : Function.support f ⊆ tsupport f := subset_closure
    have h2 : volume (Function.support f) = 0 := measure_mono_null h1 h_vol
    have h3 : ∀ᵐ x ∂volume, f x = 0 := by
      have h4 : volume {x | f x ≠ 0} = 0 := by
        have h5 : {x | f x ≠ 0} = Function.support f := by
          ext x; simp [Function.mem_support]
        rw [h5]; exact h2
      simpa [ae_iff] using h4
    have h4 : ∀ᵐ x ∂volume, |f x| = 0 := by
      filter_upwards [h3] with x hx; rw [hx]; simp
    have h_int : (∫ x, |f x|) = 0 := by
      rw [integral_congr_ae h4]; simp
    let ψ : E n → ℝ := fun _ => 0
    have hψ_smooth : ContDiff ℝ ∞ ψ := contDiff_const
    have hψ_support : HasCompactSupport ψ := by
      have h : Function.support ψ = (∅ : Set (E n)) := by
        ext x; simp [ψ, Function.mem_support]
      have h' : tsupport ψ = (∅ : Set (E n)) := by
        rw [tsupport, h] <;> simp
      have h'' : IsCompact (tsupport ψ) := by
        rw [h']; exact isCompact_empty
      exact h''
    have hψ_bound : ∀ x, |ψ x| ≤ 1 := by intro x; simp [ψ]
    have h_goal : (∫ x, f x * ψ x) ≥ (∫ x, |f x|) - η := by
      have h5 : ∀ᵐ x ∂volume, f x * ψ x = 0 := by
        filter_upwards [h3] with x hx
        simp [ψ, hx]
      have h6 : (∫ x, f x * ψ x) = 0 := by
        rw [integral_congr_ae h5]; simp
      rw [h6, h_int]; linarith
    exact ⟨ψ, hψ_smooth, hψ_support, hψ_bound, h_goal⟩
  · -- volume (tsupport f) ≠ 0
    have h_vol_ne_zero : volume (tsupport f) ≠ 0 := h_vol
    have h_vol_fin : volume (tsupport f) < ⊤ := hf_support.measure_lt_top
    let M : ℝ := ENNReal.toReal (volume (tsupport f))
    have hM_pos : 0 < M := ENNReal.toReal_pos h_vol_ne_zero h_vol_fin.ne
    let ε1 : ℝ := η / (2 * M)
    have hε1_pos : 0 < ε1 := by positivity
    rcases approximate_sign hf_cont hf_support hε1_pos with ⟨φ, hφ_cont, hφ_support, hφ_bound, hφ_int⟩
    -- Mollifier family
    let mollifier (k : ℕ) : ContDiffBump (0 : E n) :=
      let r : ℝ := 1 / (k + 2 : ℝ)
      ⟨r / 2, r, by positivity, by apply half_lt_self; positivity⟩
    let ρ (k : ℕ) : E n → ℝ := (mollifier k).normed volume
    let ψ (k : ℕ) : E n → ℝ := convolution (ρ k) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume
    -- ψ k is smooth
    have h_smooth : ∀ k, ContDiff ℝ ∞ (ψ k) := by
      intro k
      have hρ_support : HasCompactSupport (ρ k) := (mollifier k).hasCompactSupport_normed
      have hφ_local : LocallyIntegrable φ volume := hφ_cont.locallyIntegrable
      exact hρ_support.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
        ((mollifier k).contDiff_normed (μ := volume)) hφ_local
    -- ψ k has compact support
    have h_compact : ∀ k, HasCompactSupport (ψ k) := by
      intro k
      exact (mollifier k).hasCompactSupport_normed.convolution
        (ContinuousLinearMap.lsmul ℝ ℝ) hφ_support
    -- |ψ k| ≤ 1
    have h_bound : ∀ k x, |ψ k x| ≤ 1 := by
      intro k x
      have hρ_nonneg : ∀ z, 0 ≤ ρ k z := (mollifier k).nonneg_normed
      have hρ_int : ∫ z, ρ k z = 1 := (mollifier k).integral_normed
      have hρ_cont : Continuous (ρ k) := (mollifier k).continuous_normed
      have hρ_support : HasCompactSupport (ρ k) := (mollifier k).hasCompactSupport_normed
      have h_exists : ConvolutionExists (ρ k) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
        hρ_support.convolutionExists_left_of_continuous_right
          (ContinuousLinearMap.lsmul ℝ ℝ) hρ_cont.locallyIntegrable hφ_cont
      have h_eq : ψ k x = ∫ t, ρ k t * φ (x - t) := by
        simp [ψ, convolution_def, ContinuousLinearMap.lsmul_apply]
      rw [h_eq]
      have h_integrable : Integrable (fun t : E n => ρ k t * φ (x - t)) volume :=
        (h_exists x).integrable
      have h2 : |∫ t, ρ k t * φ (x - t)| ≤ ∫ t, |ρ k t * φ (x - t)| := by
        exact abs_integral_le_integral_abs
      have h3 : ∀ t, |ρ k t * φ (x - t)| = ρ k t * |φ (x - t)| := by
        intro t
        have h4 : |ρ k t * φ (x - t)| = |ρ k t| * |φ (x - t)| := by rw [abs_mul]
        rw [h4]
        have h5 : 0 ≤ ρ k t := hρ_nonneg t
        rw [abs_of_nonneg h5] <;> ring
      have h4 : ∫ t, |ρ k t * φ (x - t)| = ∫ t, ρ k t * |φ (x - t)| := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        exact h3 t
      have h5 : ∫ t, ρ k t * |φ (x - t)| ≤ ∫ t, ρ k t := by
        have h_integrable2 : Integrable (ρ k) volume :=
          hρ_cont.integrable_of_hasCompactSupport hρ_support
        have hφ'_cont : Continuous (fun t : E n => |φ (x - t)|) := by fun_prop
        have h_integrable3 : Integrable (fun t : E n => ρ k t * |φ (x - t)|) volume := by
          have h_support : Function.support (fun t : E n => ρ k t * |φ (x - t)|) ⊆ Function.support (ρ k) := by
            intro t ht
            by_contra h2
            have h3 : ρ k t = 0 := by simpa [Function.mem_support] using h2
            have h4 : ρ k t * |φ (x - t)| = 0 := by rw [h3]; ring
            exact ht h4
          have h_compact : HasCompactSupport (fun t : E n => ρ k t * |φ (x - t)|) :=
            hρ_support.mono h_support
          exact (hρ_cont.mul hφ'_cont).integrable_of_hasCompactSupport h_compact
        apply MeasureTheory.integral_mono h_integrable3 h_integrable2
        intro t
        have h6 : |φ (x - t)| ≤ 1 := hφ_bound (x - t)
        have h7 : 0 ≤ ρ k t := hρ_nonneg t
        nlinarith
      calc |∫ t, ρ k t * φ (x - t)|
          ≤ ∫ t, |ρ k t * φ (x - t)| := h2
        _ = ∫ t, ρ k t * |φ (x - t)| := h4
        _ ≤ ∫ t, ρ k t := h5
        _ = 1 := hρ_int
    -- ψ k x → φ x pointwise
    have h_rOut : Filter.Tendsto (fun k : ℕ => (mollifier k).rOut) Filter.atTop (nhds 0) := by
      have h : ∀ k : ℕ, (mollifier k).rOut = 1 / (k + 2 : ℝ) := by intro k; rfl
      rw [funext h]
      have h_shift : Filter.Tendsto (fun k : ℕ => k + 2) Filter.atTop Filter.atTop :=
        tendsto_atTop_mono (fun k : ℕ => Nat.le_add_right k 2) tendsto_id
      have h_div : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((k + 2 : ℕ) : ℝ)) Filter.atTop (nhds 0) :=
        (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp h_shift
      simpa using h_div
    have h_pointwise : ∀ x, Filter.Tendsto (fun k => ψ k x) Filter.atTop (nhds (φ x)) := by
      intro x
      exact ContDiffBump.convolution_tendsto_right_of_continuous h_rOut hφ_cont x
    -- ∫ f · ψ k → ∫ f · φ by dominated convergence
    have h_integrable_f : Integrable f volume := hf_cont.integrable_of_hasCompactSupport hf_support
    have h_integrable_abs : Integrable (fun x => |f x|) volume := h_integrable_f.norm
    have h_bound' : ∀ k, ∀ᵐ x ∂volume, |f x * ψ k x| ≤ |f x| := by
      intro k
      filter_upwards with x
      have h4 : |ψ k x| ≤ 1 := h_bound k x
      calc |f x * ψ k x| = |f x| * |ψ k x| := by rw [abs_mul]
        _ ≤ |f x| * 1 := by gcongr
        _ = |f x| := by ring
    have h_meas : ∀ k, AEStronglyMeasurable (fun x => f x * ψ k x) volume := by
      intro k
      have h_cont : Continuous (ψ k) := (h_smooth k).continuous
      exact (hf_cont.mul h_cont).aestronglyMeasurable
    have h_lim : ∀ᵐ x ∂volume, Filter.Tendsto (fun k => f x * ψ k x) Filter.atTop (nhds (f x * φ x)) := by
      filter_upwards with x
      have h5 : Filter.Tendsto (fun k => ψ k x) Filter.atTop (nhds (φ x)) := h_pointwise x
      exact h5.const_mul (f x)
    have h_conv : Filter.Tendsto (fun k => ∫ x, f x * ψ k x) Filter.atTop (nhds (∫ x, f x * φ x)) :=
      tendsto_integral_of_dominated_convergence (bound := fun x => |f x|)
        h_meas h_integrable_abs h_bound' h_lim
    -- Choose k large enough
    let I : ℝ := ∫ x, f x * φ x
    have h_main : ∃ k : ℕ, |(∫ x, f x * ψ k x) - I| < η / 2 := by
      have h7 : Filter.Tendsto (fun k => (∫ x, f x * ψ k x) - I) Filter.atTop (nhds 0) := by
        simpa [I] using h_conv.sub (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => I) Filter.atTop (nhds I))
      have h8 : Filter.Tendsto (fun k => |(∫ x, f x * ψ k x) - I|) Filter.atTop (nhds 0) := by
        simpa [abs_zero] using h7.abs
      exact (h8.eventually (gt_mem_nhds (by linarith))).exists
    rcases h_main with ⟨k, hk⟩
    refine ⟨ψ k, h_smooth k, h_compact k, h_bound k, ?_⟩
    have h7 : (∫ x, f x * ψ k x) ≥ I - η / 2 := by
      have h8 : |(∫ x, f x * ψ k x) - I| < η / 2 := hk
      have h9 : (∫ x, f x * ψ k x) - I ≥ -(η / 2) := by
        linarith [abs_lt.mp h8]
      linarith
    have h10 : I ≥ (∫ x, |f x|) - ε1 * M := by
      simpa [M, I] using hφ_int
    have h11 : ε1 * M = η / 2 := by
      dsimp only [ε1]
      field_simp [hM_pos.ne'] <;> ring
    rw [h11] at h10
    linarith

end Perimeter

end Geometry
