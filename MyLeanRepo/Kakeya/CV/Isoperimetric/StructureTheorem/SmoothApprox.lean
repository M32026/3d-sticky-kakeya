/-
# Smooth approximation helper lemmas

Helper results for `smooth_approx_simpleFunc`:
- Unit ball projection and its nonexpansiveness/continuity
- Mollification preserving the unit ball bound

## Main lemmas

- `projectUnitBall_nonexpansive_at`: projection is nonexpansive toward points in the unit ball
- `mollification_uniform_approx`: smooth uniform approximation preserving `‖·‖ ≤ 1`
-/

import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.Tactic

open MeasureTheory Metric Set ENNReal Filter ContinuousLinearMap
open scoped MeasureTheory ContDiff Convolution

namespace Geometry.Perimeter

variable {n : ℕ}

-- ============================================================================
-- Unit ball projection
-- ============================================================================

/-- Projection onto the closed unit ball. -/
noncomputable def projectUnitBall (x : E n) : E n :=
  if ‖x‖ ≤ 1 then x else (1 / ‖x‖) • x

lemma projectUnitBall_norm (x : E n) : ‖projectUnitBall x‖ ≤ 1 := by
  dsimp only [projectUnitBall]
  by_cases h : ‖x‖ ≤ 1
  · rw [if_pos h]; exact h
  · have hpos : 0 < ‖x‖ := by linarith
    rw [if_neg h]
    have hcalc : ‖(1 / ‖x‖) • x‖ = 1 := by
      rw [norm_smul]
      have h1 : ‖(1 / ‖x‖ : ℝ)‖ = 1 / ‖x‖ := by
        simp [abs_of_pos (show 0 < (1 / ‖x‖ : ℝ) from by positivity)]
      rw [h1]
      have h2 : (1 / ‖x‖ : ℝ) * ‖x‖ = 1 := by field_simp [hpos.ne'] <;> ring
      exact h2
    rw [hcalc] <;> norm_num

lemma projectUnitBall_id {x : E n} (h : ‖x‖ ≤ 1) : projectUnitBall x = x := by
  dsimp only [projectUnitBall]; rw [if_pos h]

/-- Projection is nonexpansive when the second point is in the unit ball. -/
lemma projectUnitBall_nonexpansive_at (x y : E n) (hy : ‖y‖ ≤ 1) :
    ‖projectUnitBall x - y‖ ≤ ‖x - y‖ := by
  dsimp only [projectUnitBall]
  by_cases hx : ‖x‖ ≤ 1
  · rw [if_pos hx]
  · rw [if_neg hx]
    set r : ℝ := ‖x‖ with hr
    have hr1 : 1 < r := by linarith
    have hpos : 0 < r := by linarith
    set xhat : E n := (1 / r) • x with hxhat
    have hxnorm : ‖xhat‖ = 1 := by
      rw [hxhat, norm_smul]
      have h1 : ‖(1 / r : ℝ)‖ = 1 / r := by
        have hpos' : 0 < (1 / r : ℝ) := by positivity
        rw [Real.norm_eq_abs, abs_of_pos hpos']
      rw [h1]
      have h2 : (1 / r : ℝ) * r = 1 := by field_simp [hpos.ne'] <;> ring
      exact h2
    have h_x_eq : x = r • xhat := by
      rw [hxhat]
      have h : (r : ℝ) • ((1 / r) • x) = x := by
        rw [smul_smul]
        have h2 : (r * (1 / r) : ℝ) = 1 := by field_simp [hpos.ne'] <;> ring
        rw [h2, one_smul]
      exact h.symm
    have h_inner : 0 ≤ inner ℝ (xhat - y) xhat := by
      have h1 : inner ℝ (xhat - y) xhat = inner ℝ xhat xhat - inner ℝ y xhat := by
        rw [inner_sub_left]
      rw [h1]
      have h2 : inner ℝ xhat xhat = ‖xhat‖ ^ 2 := by
        have h21 : inner ℝ xhat xhat = ↑‖xhat‖ ^ 2 := inner_self_eq_norm_sq_to_K xhat
        exact_mod_cast h21
      rw [h2, hxnorm]
      have h3 : inner ℝ y xhat ≤ |inner ℝ y xhat| := le_abs_self (inner ℝ y xhat)
      have h4 : |inner ℝ y xhat| ≤ ‖y‖ * ‖xhat‖ := abs_real_inner_le_norm y xhat
      have h5 : inner ℝ y xhat ≤ ‖y‖ * ‖xhat‖ := h3.trans h4
      have h6 : ‖y‖ * ‖xhat‖ ≤ 1 := by rw [hxnorm] <;> linarith
      linarith
    have h_main : ‖x - y‖ ^ 2 ≥ ‖xhat - y‖ ^ 2 := by
      have h5 : x - y = (xhat - y) + (r - 1) • xhat := by
        rw [h_x_eq] <;> simp [sub_smul, add_smul] <;> abel
      rw [h5]
      have h6 := norm_add_sq_real (xhat - y) ((r - 1) • xhat)
      rw [h6]
      have h7 : inner ℝ (xhat - y) ((r - 1) • xhat) = (r - 1) * inner ℝ (xhat - y) xhat := by
        rw [inner_smul_right]
      rw [h7]
      have h8 : 0 ≤ (r - 1) * inner ℝ (xhat - y) xhat := by
        exact mul_nonneg (by linarith) h_inner
      nlinarith [norm_nonneg (xhat - y), norm_nonneg ((r - 1) • xhat)]
    have h9 : 0 ≤ ‖xhat - y‖ := by positivity
    have h10 : 0 ≤ ‖x - y‖ := by positivity
    nlinarith

/-- Continuity of the unit ball projection. -/
lemma projectUnitBall_continuous : Continuous (projectUnitBall : E n → E n) := by
  have h_main : ∀ (x₀ : E n), ContinuousAt projectUnitBall x₀ := by
    intro x₀
    by_cases h : ‖x₀‖ < 1
    · have h_nhds : ∀ᶠ (x : E n) in nhds x₀, ‖x‖ < 1 :=
        (isOpen_lt continuous_norm continuous_const).eventually_mem h
      have h_eq : ∀ᶠ (x : E n) in nhds x₀, projectUnitBall x = x := by
        filter_upwards [h_nhds] with x hx
        exact projectUnitBall_id (by linarith)
      exact continuousAt_id.congr_of_eventuallyEq h_eq
    · by_cases h2 : 1 < ‖x₀‖
      · have h_nhds : ∀ᶠ (x : E n) in nhds x₀, 1 < ‖x‖ :=
          (isOpen_lt continuous_const continuous_norm).eventually_mem h2
        have h_eq : ∀ᶠ (x : E n) in nhds x₀, projectUnitBall x = (1 / ‖x‖) • x := by
          filter_upwards [h_nhds] with x hx
          dsimp only [projectUnitBall]
          rw [if_neg (by linarith)]
        have h_cont : ContinuousAt (fun x : E n => (1 / ‖x‖) • x) x₀ := by
          have hpos0 : 0 < ‖x₀‖ := by linarith
          have hne : ‖x₀‖ ≠ 0 := hpos0.ne'
          have h1 : ContinuousAt (fun x : E n => ‖x‖) x₀ := continuous_norm.continuousAt
          have h2 : ContinuousAt (fun x : E n => (1 / ‖x‖ : ℝ)) x₀ :=
            ContinuousAt.div continuousAt_const h1 hne
          exact h2.smul continuousAt_id
        exact h_cont.congr_of_eventuallyEq h_eq
      · have h3 : ‖x₀‖ = 1 := by linarith
        have h4 : ‖x₀‖ ≤ 1 := by linarith
        have h5 : projectUnitBall x₀ = x₀ := projectUnitBall_id h4
        have h6 : ∀ (x : E n), ‖projectUnitBall x - projectUnitBall x₀‖ ≤ ‖x - x₀‖ := by
          intro x
          rw [h5]
          exact projectUnitBall_nonexpansive_at x x₀ h4
        exact Metric.continuousAt_iff.mpr (fun ε hε => ⟨ε, hε, fun y hy => by
          have h7 : ‖projectUnitBall y - projectUnitBall x₀‖ ≤ ‖y - x₀‖ := h6 y
          exact h7.trans_lt hy⟩)
  exact continuous_iff_continuousAt.mpr h_main

-- ============================================================================
-- Mollification: uniform approximation preserving unit ball bound
-- ============================================================================

/-- Uniform approximation of continuous compactly supported vector field by
smooth compactly supported vector fields, preserving the unit norm bound. -/
lemma mollification_uniform_approx
    {h : E n → E n} (hh_cont : Continuous h) (hh_supp : HasCompactSupport h)
    (h_bound : ∀ x, ‖h x‖ ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ (φ : E n → E n), ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (∀ x, ‖φ x‖ ≤ 1) ∧ (∀ x, ‖φ x - h x‖ < η) := by
  have h_uniform : UniformContinuous h :=
    hh_supp.uniformContinuous_of_continuous hh_cont
  set η2 : ℝ := η / 2 with hη2_def
  have hη2_pos : 0 < η2 := by positivity
  rcases Metric.uniformContinuous_iff.mp h_uniform η2 hη2_pos with ⟨δ, hδ_pos, hδ⟩
  let bump : ContDiffBump (0 : E n) := ⟨δ / 2, δ, half_pos hδ_pos, half_lt_self hδ_pos⟩
  let ρ : E n → ℝ := bump.normed volume
  have hρ_nonneg : ∀ y, 0 ≤ ρ y := bump.nonneg_normed
  have hρ_int : ∫ y, ρ y ∂volume = 1 := bump.integral_normed
  let φ : E n → E n := (ρ ⋆[lsmul ℝ ℝ, volume] h)
  have hρ_smooth : ContDiff ℝ ∞ ρ := bump.contDiff_normed
  have hρ_supp' : HasCompactSupport ρ := bump.hasCompactSupport_normed
  have h_locInt : MeasureTheory.LocallyIntegrable h volume := hh_cont.locallyIntegrable
  have hφ_smooth : ContDiff ℝ ∞ φ :=
    hρ_supp'.contDiff_convolution_left (lsmul ℝ ℝ) hρ_smooth h_locInt
  have hφ_supp : HasCompactSupport φ :=
    show HasCompactSupport (ρ ⋆[lsmul ℝ ℝ, volume] h) from
      hρ_supp'.convolution (L := lsmul ℝ ℝ) (μ := volume) hh_supp
  have hφ_approx : ∀ x, dist (φ x) (h x) ≤ η2 := by
    intro x
    have hball : ∀ y ∈ Metric.ball x δ, dist (h y) (h x) ≤ η2 := by
      intro y hy
      exact (hδ hy).le
    exact bump.dist_normed_convolution_le hh_cont.aestronglyMeasurable hball
  have hφ_close_norm : ∀ x, ‖φ x - h x‖ ≤ η2 := by
    intro x
    simpa [dist_eq_norm] using hφ_approx x
  have hφ_bound : ∀ x, ‖φ x‖ ≤ 1 := by
    intro x
    have h1 : φ x = ∫ y, ρ y • h (x - y) := by
      rfl
    rw [h1]
    have h2 : ‖∫ y, ρ y • h (x - y)‖ ≤ ∫ y, ‖ρ y • h (x - y)‖ :=
      norm_integral_le_integral_norm _
    have h3 : ∀ y, ‖ρ y • h (x - y)‖ = ρ y * ‖h (x - y)‖ := by
      intro y
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ_nonneg y)]
    have h4 : ∫ y, ‖ρ y • h (x - y)‖ = ∫ y, ρ y * ‖h (x - y)‖ := by
      congr with y; exact h3 y
    rw [h4] at h2
    have h_integrand_cont : Continuous (fun y : E n => ρ y • h (x - y)) := by fun_prop
    have h_integrand_supp : HasCompactSupport (fun y : E n => ρ y • h (x - y)) :=
      hρ_supp'.mono (by
        intro z hz
        simp only [Function.mem_support] at hz ⊢
        intro h9
        rw [h9] at hz
        simpa using hz)
    have h_int1 : MeasureTheory.Integrable (fun y : E n => ρ y * ‖h (x - y)‖) volume := by
      have h_eq : (fun y : E n => ρ y * ‖h (x - y)‖) = fun y => ‖ρ y • h (x - y)‖ := by
        funext y
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ_nonneg y)]
      rw [h_eq]
      exact h_integrand_cont.integrable_of_hasCompactSupport h_integrand_supp |>.norm
    have h_int2 : MeasureTheory.Integrable ρ volume :=
      hρ_smooth.continuous.integrable_of_hasCompactSupport hρ_supp'
    have h6 : ∀ y, ρ y * ‖h (x - y)‖ ≤ ρ y := by
      intro y
      have h7 : ‖h (x - y)‖ ≤ 1 := h_bound (x - y)
      have h8 : 0 ≤ ρ y := hρ_nonneg y
      nlinarith
    have h_nonneg : ∀ y, 0 ≤ ρ y * ‖h (x - y)‖ := by
      intro y
      have h7 : 0 ≤ ρ y := hρ_nonneg y
      have h8 : 0 ≤ ‖h (x - y)‖ := by positivity
      exact mul_nonneg h7 h8
    have h5 : ∫ (y : E n), ρ y * ‖h (x - y)‖ ∂volume ≤ ∫ (y : E n), ρ y ∂volume := by
      have h_diff_int : Integrable (fun y : E n => ρ y * ‖h (x - y)‖ - ρ y) volume :=
        h_int1.sub h_int2
      have h_diff_nonpos : ∫ (y : E n), (ρ y * ‖h (x - y)‖ - ρ y) ∂volume ≤ 0 :=
        integral_nonpos_of_ae (ae_of_all volume (fun y =>
          show ρ y * ‖h (x - y)‖ - ρ y ≤ 0 from by linarith [h6 y]))
      have h_eq : ∫ (y : E n), (ρ y * ‖h (x - y)‖ - ρ y) ∂volume =
          (∫ (y : E n), ρ y * ‖h (x - y)‖ ∂volume) - (∫ (y : E n), ρ y ∂volume) :=
        integral_sub h_int1 h_int2
      rw [h_eq] at h_diff_nonpos
      linarith
    rw [hρ_int] at h5
    exact h2.trans h5
  have hφ_strict : ∀ x, ‖φ x - h x‖ < η := by
    intro x
    have h9 : ‖φ x - h x‖ ≤ η2 := hφ_close_norm x
    have h10 : η2 < η := by
      rw [hη2_def] <;> linarith
    exact h9.trans_lt h10
  exact ⟨φ, hφ_smooth, hφ_supp, hφ_bound, hφ_strict⟩

-- ============================================================================
-- L^1 approximation of bounded integrable functions by smooth test fields
-- ============================================================================

/-- Approximate a `‖·‖ ≤ 1`-bounded integrable function `g` by a smooth
compactly supported vector field `φ` with `‖φ‖ ≤ 1`, in `L¹(μ.variation)`.

Uses:
1. L¹ density of continuous compactly supported functions
2. Unit-ball projection (nonexpansive toward unit-ball points)
3. Mollification for uniform smooth approximation -/
lemma smooth_approx_simpleFunc
    (μ : VectorMeasure (E n) (E n)) [IsFiniteMeasure μ.variation] [μ.variation.Regular]
    (g : E n → E n) (hg_int : μ.Integrable g) (hg_bound : ∀ x, ‖g x‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (φ : E n → E n), ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (∀ x, ‖φ x‖ ≤ 1) ∧
      ∫ x, ‖φ x - g x‖ ∂μ.variation < ε := by
  let ν := μ.variation
  set ε3 : ℝ := ε / 3 with hε3_def
  have hε3_pos : 0 < ε3 := by positivity
  rcases hg_int.exists_hasCompactSupport_integral_sub_le hε3_pos with ⟨h, hh_supp, hh_L1, hh_cont, _⟩
  let h' : E n → E n := fun x => projectUnitBall (h x)
  have hh'_cont : Continuous h' := projectUnitBall_continuous.comp hh_cont
  have hh'_supp : HasCompactSupport h' := by
    have h1 : Function.support h' ⊆ Function.support h := by
      intro x hx
      by_contra h2
      have h3 : h x = 0 := by simpa [Function.support] using h2
      have h4 : h' x = 0 := by
        simp [h', h3, projectUnitBall] <;> norm_num
      exact hx (by simpa [Function.support] using h4)
    exact HasCompactSupport.mono hh_supp h1
  have hh'_bound : ∀ x, ‖h' x‖ ≤ 1 := fun x => projectUnitBall_norm (h x)
  -- Integrability facts
  have hh_int : Integrable h ν := hh_cont.integrable_of_hasCompactSupport hh_supp
  have hg_sub_int : Integrable (fun x => h x - g x) ν := hh_int.sub hg_int
  have h_norm_int : Integrable (fun x => ‖h x - g x‖) ν := hg_sub_int.norm
  have h1_le : ∀ x, ‖h' x - g x‖ ≤ ‖h x - g x‖ := by
    intro x; exact projectUnitBall_nonexpansive_at (h x) (g x) (hg_bound x)
  have hh'_sm : AEStronglyMeasurable h' ν := hh'_cont.aestronglyMeasurable
  have hg_sm : AEStronglyMeasurable g ν := hg_int.1
  have h1_le' : ∀ x, ‖(‖h' x - g x‖)‖ ≤ ‖(‖h x - g x‖)‖ := by
    intro x
    have h_pos1 : 0 ≤ ‖h' x - g x‖ := by positivity
    have h_pos2 : 0 ≤ ‖h x - g x‖ := by positivity
    simp [Real.norm_eq_abs, abs_of_nonneg h_pos1, abs_of_nonneg h_pos2, h1_le x]
  have h_int2 : Integrable (fun x => ‖h' x - g x‖) ν :=
    h_norm_int.mono (hh'_sm.sub hg_sm).norm (ae_of_all ν h1_le')
  have hh'_L1 : ∫ x, ‖h' x - g x‖ ∂ν ≤ ε3 := by
    have h2 : ∫ x, ‖h' x - g x‖ ∂ν ≤ ∫ x, ‖h x - g x‖ ∂ν :=
      integral_mono h_int2 h_norm_int h1_le
    have h3 : ∫ x, ‖h x - g x‖ ∂ν = ∫ x, ‖g x - h x‖ ∂ν := by
      congr with x; rw [norm_sub_rev]
    rw [h3] at h2
    exact h2.trans hh_L1
  set η : ℝ := ε3 / ((ν Set.univ).toReal + 1) with hη_def
  have hη_pos : 0 < η := by positivity
  rcases mollification_uniform_approx hh'_cont hh'_supp hh'_bound hη_pos with ⟨φ, hφ_smooth, hφ_supp, hφ_bound, hφ_uniform⟩
  -- More integrability facts
  have hφ_int : Integrable φ ν := hφ_smooth.continuous.integrable_of_hasCompactSupport hφ_supp
  have h_cont_diff : Continuous (fun x => φ x - h' x) := hφ_smooth.continuous.sub hh'_cont
  have h_supp_diff : HasCompactSupport (fun x => φ x - h' x) := hφ_supp.sub hh'_supp
  have h_supp_norm : HasCompactSupport (fun x => ‖φ x - h' x‖) := by
    have h1 : Function.support (fun x => ‖φ x - h' x‖) ⊆ Function.support (fun x => φ x - h' x) := by
      intro x hx
      by_contra h2
      have h3 : φ x - h' x = 0 := by simpa [Function.support] using h2
      have h4 : ‖φ x - h' x‖ = 0 := by rw [h3] <;> simp
      exact hx (by simpa [Function.support] using h4)
    exact h_supp_diff.mono h1
  have h_int1 : Integrable (fun x => ‖φ x - h' x‖) ν :=
    h_cont_diff.norm.integrable_of_hasCompactSupport h_supp_norm
  have hη_int : Integrable (fun x : E n => η) ν := integrable_const η
  have hφ_L1 : ∫ x, ‖φ x - h' x‖ ∂ν ≤ ε3 := by
    have h1 : ∀ x, ‖φ x - h' x‖ ≤ η := fun x => (hφ_uniform x).le
    have h2 : ∫ x, ‖φ x - h' x‖ ∂ν ≤ ∫ x, η ∂ν :=
      integral_mono h_int1 hη_int h1
    have h3 : ∫ x, η ∂ν = (ν Set.univ).toReal * η := by
      rw [integral_const]
      have h4 : ν.real Set.univ = (ν Set.univ).toReal := by rfl
      rw [h4] <;> ring
    rw [h3] at h2
    have h4 : (ν Set.univ).toReal * η ≤ ε3 := by
      rw [hη_def]
      have h5 : (ν Set.univ).toReal ≥ 0 := by positivity
      have h6 : (ν Set.univ).toReal / ((ν Set.univ).toReal + 1) ≤ 1 := by
        have h7 : (ν Set.univ).toReal ≤ (ν Set.univ).toReal + 1 := by linarith
        exact (div_le_one (by positivity)).mpr h7
      have h7 : (ν Set.univ).toReal * (ε3 / ((ν Set.univ).toReal + 1)) =
          ε3 * ((ν Set.univ).toReal / ((ν Set.univ).toReal + 1)) := by ring
      rw [h7]
      have h8 : ε3 * ((ν Set.univ).toReal / ((ν Set.univ).toReal + 1)) ≤ ε3 * 1 := by
        gcongr
      linarith
    exact h2.trans h4
  have h_final : ∫ x, ‖φ x - g x‖ ∂ν < ε := by
    have h1 : ∀ x, ‖φ x - g x‖ ≤ ‖φ x - h' x‖ + ‖h' x - g x‖ := by
      intro x
      have h_eq : φ x - g x = (φ x - h' x) + (h' x - g x) := by abel
      rw [h_eq]
      exact norm_add_le _ _
    have h_int3 : Integrable (fun x => ‖φ x - g x‖) ν :=
      (hφ_int.sub hg_int).norm
    have h2 : ∫ x, ‖φ x - g x‖ ∂ν ≤ ∫ x, (‖φ x - h' x‖ + ‖h' x - g x‖) ∂ν :=
      integral_mono h_int3 (h_int1.add h_int2) h1
    have h3 : ∫ x, (‖φ x - h' x‖ + ‖h' x - g x‖) ∂ν =
        ∫ x, ‖φ x - h' x‖ ∂ν + ∫ x, ‖h' x - g x‖ ∂ν := integral_add h_int1 h_int2
    rw [h3] at h2
    have h4 : ∫ x, ‖φ x - h' x‖ ∂ν + ∫ x, ‖h' x - g x‖ ∂ν ≤ ε3 + ε3 := by
      exact add_le_add hφ_L1 hh'_L1
    have h5 : ε3 + ε3 < ε := by
      have h6 : ε3 + ε3 = 2 * (ε / 3) := by
        simp [hε3_def] <;> ring
      rw [h6]
      have h7 : 0 < ε := hε
      linarith
    exact h2.trans_lt (h4.trans_lt h5)
  exact ⟨φ, hφ_smooth, hφ_supp, hφ_bound, h_final⟩

end Geometry.Perimeter
