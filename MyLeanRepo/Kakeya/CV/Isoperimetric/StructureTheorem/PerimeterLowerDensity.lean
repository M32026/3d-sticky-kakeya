import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.PerimeterDefinition
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.CutoffFunctions
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.BlowUpLemma
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.ReducedBoundaryData
import Mathlib.Tactic

/-!
# Perimeter Lower Density at Reduced Boundary Points

At a reduced boundary point `x` with normal `ν`, the local perimeter has positive
lower density: `P(U; B(x,r)) ≥ c · r^(n-1)` for small `r`.

This is an **unconditional** result derived directly from `ReducedBoundaryData`
via the Gauss-Green cutoff and blow-up convergence. It does not require
perimeter measure density bounds or Besicovitch differentiation.

## Main theorem

`perimeter_lower_density_from_data`:
Given `ReducedBoundaryData U x ν`, there exist `c > 0` and `r0 > 0` such that
for all `0 < r < r0`,
`perimeterIn U (ball x r) ≥ c · r^(n-1)`.

## Proof (Gauss-Green cutoff)

1. Choose radial cutoff `φ = radialCutoff 0 (1/2) (1/2)`, supported in `B(0,1)`.
2. The directional derivative `f(z) := fderiv φ z ν` is non-negative on the
   half-space `Hν = {inner z ν < 0}` and strictly positive on an open subset,
   so `I_H := ∫_{Hν} f > 0`.
3. By the blow-up lemma, `∫_{blowUp U x r} f → I_H` as `r → 0`.
4. Define test vector field `Φ_r(y) := φ((y-x)/r) • ν`, supported in `B(x,r)`.
5. `divergence Φ_r = (1/r) · f((y-x)/r)`, and change of variables gives
   `∫_U divergence Φ_r = r^(n-1) · ∫_{blowUp U x r} f`.
6. For small `r`, this is `≥ r^(n-1) · I_H / 2`.
7. By definition of `perimeterIn`, `P(U; B(x,r)) ≥ |∫_U divergence Φ_r|`.

## Whiteprint

Node `perimeter_lower_density_from_data`.
-/


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.StructureTheorem

open Perimeter

variable {n : ℕ}

-- ============================================================================
-- Helper: directional derivative of radial cutoff
-- ============================================================================

/-- Exact formula for the directional derivative of `radialCutoff 0 a L`. -/
lemma radialCutoff_fderiv_direction_eq {a L : ℝ} (ha : 0 < a) (hL : 0 < L)
    {ν : E n} {z : E n} (hz : z ≠ 0) :
    fderiv ℝ (radialCutoff (0 : E n) a L) z ν =
      deriv smoothStep ((‖z‖ - a) / L) * (1 / L) * (inner ℝ z ν / ‖z‖) := by
  set d : E n → ℝ := fun y => dist y (0 : E n) with hd
  set h : E n → ℝ := fun y => (d y - a) / L with hh
  set g : ℝ → ℝ := smoothStep with hg
  have h_diff_d : HasFDerivAt d (fderiv ℝ d z) z := by
    have h_diff : DifferentiableAt ℝ d z :=
      DifferentiableAt.dist (𝕜 := ℝ) differentiableAt_id (differentiableAt_const (0 : E n)) hz
    exact h_diff.hasFDerivAt
  have h_diff_h : HasFDerivAt h ((1 / L) • fderiv ℝ d z) z := by
    have h1 : HasFDerivAt (fun y => d y - a) (fderiv ℝ d z) z := h_diff_d.sub_const a
    have h2 : HasFDerivAt (fun y => (1 / L) * (d y - a)) ((1 / L) • fderiv ℝ d z) z :=
      h1.const_smul (1 / L)
    have h3 : (fun y : E n => (1 / L) * (d y - a)) = h := by
      funext y; simp [hh]; ring
    rw [h3] at h2; exact h2
  have h_diff_g : HasDerivAt g (deriv g (h z)) (h z) := by
    have h_diff : Differentiable ℝ g := smoothStep_contDiff.differentiable (by simp)
    exact h_diff.differentiableAt.hasDerivAt
  have h_main : HasFDerivAt (g ∘ h) (deriv g (h z) • ((1 / L) • fderiv ℝ d z)) z :=
    h_diff_g.comp_hasFDerivAt z h_diff_h
  have h_η : (g ∘ h) = radialCutoff (0 : E n) a L := by
    funext y; simp [radialCutoff, hh, hg, hd, dist_zero_right] <;> ring
  have h_eq : fderiv ℝ (radialCutoff (0 : E n) a L) z =
      deriv g (h z) • ((1 / L) • fderiv ℝ d z) := by
    rw [← h_η]; exact h_main.fderiv
  have h_pos : 0 < ‖z‖ := by exact norm_pos_iff.mpr hz
  have h_norm_sq_fd : HasFDerivAt (fun x : E n => ‖x‖ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h_sqrt_fd : HasFDerivAt (fun x : E n => Real.sqrt (‖x‖ ^ 2))
      ((1 / (2 * Real.sqrt (‖z‖ ^ 2))) • (2 • innerSL ℝ z)) z :=
    h_norm_sq_fd.sqrt (show (‖z‖ ^ 2 : ℝ) ≠ 0 by positivity)
  have h_eq_fun : (fun x : E n => Real.sqrt (‖x‖ ^ 2)) = (fun x : E n => ‖x‖) := by
    funext x; rw [Real.sqrt_sq_eq_abs, abs_norm]
  have h_simp : (1 / (2 * Real.sqrt (‖z‖ ^ 2))) = (1 / (2 * ‖z‖)) := by
    have h : Real.sqrt (‖z‖ ^ 2) = ‖z‖ := by
      rw [Real.sqrt_sq_eq_abs, abs_norm]
    rw [h]
  have h_norm_fd : HasFDerivAt (fun x : E n => ‖x‖)
      ((1 / (2 * ‖z‖)) • (2 • innerSL ℝ z)) z := by
    rw [h_eq_fun] at h_sqrt_fd
    rw [h_simp] at h_sqrt_fd
    exact h_sqrt_fd
  have h_fderiv_norm : fderiv ℝ (fun x : E n => ‖x‖) z = (1 / ‖z‖) • innerSL ℝ z := by
    rw [h_norm_fd.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    simp [smul_smul, h_pos.ne']
    <;> norm_cast <;> field_simp [h_pos.ne'] <;> ring
  have h_fderiv_dist : (fderiv ℝ d z) ν = inner ℝ z ν / ‖z‖ := by
    have h_eq1 : fderiv ℝ d z = fderiv ℝ (fun x : E n => ‖x‖) z := by
      have h2 : d = fun x : E n => ‖x‖ := by funext x; simp [hd, dist_zero_right]
      rw [h2]
    rw [h_eq1, h_fderiv_norm]
    have h3 : ((1 / ‖z‖) • innerSL ℝ z) ν = (1 / ‖z‖) * (innerSL ℝ z ν) := by
      simp [smul_eq_mul]
    rw [h3]
    have h4 : (innerSL ℝ z ν) = inner ℝ z ν := by rfl
    rw [h4] <;> ring
  have h_smul_apply : ∀ (c : ℝ) (f' : E n →L[ℝ] ℝ), (c • f') ν = c * f' ν := by
    intro c f'; simp [smul_apply]
  have h_main_goal : (fderiv ℝ (radialCutoff (0 : E n) a L) z) ν =
      deriv smoothStep ((‖z‖ - a) / L) * (1 / L) * (inner ℝ z ν / ‖z‖) := by
    rw [h_eq]
    have h2 : (deriv g (h z) • ((1 / L) • fderiv ℝ d z)) ν =
        deriv g (h z) * (((1 / L) • fderiv ℝ d z) ν) := h_smul_apply _ _
    rw [h2]
    have h3 : ((1 / L) • fderiv ℝ d z) ν = (1 / L) * (fderiv ℝ d z) ν := h_smul_apply _ _
    rw [h3, h_fderiv_dist]
    have h4 : deriv g (h z) = deriv smoothStep ((‖z‖ - a) / L) := by
      simp [hg, hh, hd, dist_zero_right] <;> ring
    rw [h4] <;> ring
  exact h_main_goal

-- ============================================================================
-- Helper: smoothStep' is strictly negative somewhere in (0,1)
-- ============================================================================

/-- `deriv smoothStep 1 = 0` by continuity from the right. -/
lemma deriv_smoothStep_one_eq_zero : deriv smoothStep 1 = 0 := by
  have h_cont : Continuous (deriv smoothStep) :=
    smoothStep_contDiff.continuous_deriv (by norm_num)
  have h2 : ∀ t ∈ Set.Ioi (1 : ℝ), deriv smoothStep t = 0 := by
    intro t ht
    have h3 : t ∉ Set.Icc (0 : ℝ) 1 := by
      intro h4
      have h5 : t ≤ 1 := h4.2
      exact not_le.mpr ht h5
    exact smoothStep_deriv_zero_outside h3
  have h_eqOn : (Set.Ioi (1 : ℝ)).EqOn (deriv smoothStep) (fun _ => 0) := h2
  have h1_in_closure : (1 : ℝ) ∈ closure (Set.Ioi (1 : ℝ)) := by
    simp [closure_Ioi]
  have h_contOn : ∀ x ∈ closure (Set.Ioi (1 : ℝ)), ContinuousWithinAt (deriv smoothStep) (Set.Ioi (1 : ℝ)) x :=
    fun x _ => h_cont.continuousWithinAt
  have h_closure_eq : (closure (Set.Ioi (1 : ℝ))).EqOn (deriv smoothStep) (fun _ => 0) :=
    ContinuousWithinAt.eqOn_const_closure h_contOn h_eqOn
  exact h_closure_eq h1_in_closure

/-- There exists an interval `(t1, t2) ⊆ (0,1)` where `deriv smoothStep < 0`. -/
lemma exists_smoothStep_deriv_neg_interval :
    ∃ (t1 t2 : ℝ), 0 < t1 ∧ t1 < t2 ∧ t2 < 1 ∧
      ∀ t ∈ Set.Ioo t1 t2, deriv smoothStep t < 0 := by
  have h0 : smoothStep 0 = 1 := smoothStep_one_of_nonpos (by norm_num)
  have h1 : smoothStep 1 = 0 := smoothStep_zero_of_one_le (by norm_num)
  have h_diff : Differentiable ℝ smoothStep := smoothStep_contDiff.differentiable (by simp)
  have h_cont_deriv : Continuous (deriv smoothStep) :=
    smoothStep_contDiff.continuous_deriv (by norm_num)
  have h_antitone : ∀ t, deriv smoothStep t ≤ 0 := by
    intro t
    exact smoothStep_antitone.deriv_nonpos (x := t)
  by_cases h : ∃ t ∈ Set.Ioo (0 : ℝ) 1, deriv smoothStep t ≠ 0
  · rcases h with ⟨t0, ht0, hne⟩
    have hneg : deriv smoothStep t0 < 0 := by
      have hle : deriv smoothStep t0 ≤ 0 := h_antitone t0
      exact lt_of_le_of_ne hle hne
    have h_t0_pos : 0 < t0 := ht0.1
    have h_t0_lt_one : t0 < 1 := ht0.2
    have h_nhds : ∀ᶠ t in nhds t0, deriv smoothStep t < 0 :=
      h_cont_deriv.continuousAt.eventually (Iio_mem_nhds hneg)
    have h_Ioo_nhds : ∀ᶠ t in nhds t0, t ∈ Set.Ioo (0 : ℝ) 1 :=
      isOpen_Ioo.mem_nhds ht0
    have h_both : ∀ᶠ t in nhds t0, t ∈ Set.Ioo (0 : ℝ) 1 ∧ deriv smoothStep t < 0 :=
      h_Ioo_nhds.and h_nhds
    rcases Metric.nhds_basis_ball.eventually_iff.mp h_both with ⟨ε, hε_pos, hball⟩
    set δ : ℝ := min ε (min t0 (1 - t0)) / 2 with hδ_def
    have hδ_pos : 0 < δ := by
      dsimp only [δ]
      have h1 : 0 < min ε (min t0 (1 - t0)) := by positivity
      linarith
    have hδ_le_ε : δ ≤ ε := by
      dsimp only [δ]
      have h2 : min ε (min t0 (1 - t0)) ≤ ε := min_le_left _ _
      linarith
    set t1 : ℝ := t0 - δ with ht1_def
    set t2 : ℝ := t0 + δ with ht2_def
    have ht1_pos : 0 < t1 := by
      dsimp only [t1, δ]
      have h3 : min ε (min t0 (1 - t0)) / 2 < t0 := by
        have h4 : min ε (min t0 (1 - t0)) ≤ t0 := by
          exact le_trans (min_le_right _ _) (min_le_left _ _)
        have h5 : 0 < t0 := h_t0_pos
        linarith
      linarith
    have ht2_lt_one : t2 < 1 := by
      dsimp only [t2, δ]
      have h3 : min ε (min t0 (1 - t0)) / 2 < 1 - t0 := by
        have h4 : min ε (min t0 (1 - t0)) ≤ 1 - t0 := by
          exact le_trans (min_le_right _ _) (min_le_right _ _)
        have h5 : 0 < 1 - t0 := by linarith
        linarith
      linarith
    have ht1_lt_t2 : t1 < t2 := by
      dsimp only [t1, t2]
      have h3 : 0 < δ := hδ_pos
      linarith
    have h_in_ball : ∀ t ∈ Set.Ioo t1 t2, t ∈ ball t0 ε := by
      intro t ht
      have h4 : t1 < t := ht.1
      have h5 : t < t2 := ht.2
      have h6 : |t - t0| < δ := by
        rw [abs_lt]
        constructor
        · dsimp only [t1] at h4; linarith
        · dsimp only [t2] at h5; linarith
      have h7 : |t - t0| < ε := by
        calc |t - t0| < δ := h6
             _ ≤ ε := hδ_le_ε
      simpa [ball, dist_eq_norm] using h7
    refine ⟨t1, t2, ht1_pos, ht1_lt_t2, ht2_lt_one, ?_⟩
    intro t ht
    exact (hball (h_in_ball t ht)).2
  · push Not at h
    have h_const : ∀ t ∈ Set.Ioo (0 : ℝ) 1, deriv smoothStep t = 0 := h
    have h_cont_on : ContinuousOn smoothStep (Set.Icc (0 : ℝ) 1) :=
      h_diff.continuous.continuousOn
    have h_mvt : ∃ c ∈ Set.Ioo (0 : ℝ) 1, deriv smoothStep c = (smoothStep 1 - smoothStep 0) / (1 - 0) :=
      exists_deriv_eq_slope smoothStep (show (0 : ℝ) < 1 by norm_num) h_cont_on
        (h_diff.differentiableOn)
    rcases h_mvt with ⟨c, hc, h_eq⟩
    have h9 : deriv smoothStep c = 0 := h_const c hc
    rw [h9] at h_eq
    have h10 : smoothStep 1 - smoothStep 0 = 0 := by
      norm_num at h_eq ⊢ <;> linarith
    have h11 : smoothStep 1 = smoothStep 0 := by linarith
    rw [h0, h1] at h11 <;> norm_num at h11

-- ============================================================================
-- Positivity of half-space derivative integral
-- ============================================================================

/-- For a radial cutoff φ and unit normal ν, the integral of `fderiv φ ν`
over the half-space `Hν` is strictly positive. -/
lemma halfspace_derivative_integral_pos {ν : E n} (hν_unit : ‖ν‖ = 1)
    (hn : 2 ≤ n) :
    0 < ∫ z in halfSpace ν, fderiv ℝ (radialCutoff (0 : E n) (1 / 2) (1 / 2)) z ν := by
  set a : ℝ := 1 / 2 with ha_def
  set L : ℝ := 1 / 2 with hL_def
  set φ : E n → ℝ := radialCutoff (0 : E n) a L with hφ_def
  set f : E n → ℝ := fun z => fderiv ℝ φ z ν with hf_def
  have ha_pos : 0 < a := by norm_num
  have hL_pos : 0 < L := by norm_num
  have hν_ne : ν ≠ 0 := by
    intro h; rw [h] at hν_unit; simp at hν_unit
  have hH_meas : MeasurableSet (halfSpace ν) := by
    have h1 : Continuous (fun z : E n => inner ℝ z ν) := by fun_prop
    exact (isOpen_Iio.preimage h1).measurableSet

  -- Step 1: f z ≥ 0 for z ∈ halfSpace ν
  have h_nonneg : ∀ z ∈ halfSpace ν, 0 ≤ f z := by
    intro z hz
    by_cases hz0 : z = 0
    · have h_fd : fderiv ℝ φ 0 = 0 := radialCutoff_fderiv_at_center ha_pos hL_pos
      have h : f z = 0 := by
        simp only [hf_def, hz0, h_fd, zero_apply]
      rw [h] <;> norm_num
    · have h_inner : inner ℝ z ν < 0 := hz
      have h_norm_pos : 0 < ‖z‖ := by exact norm_pos_iff.mpr hz0
      have h_eq : f z = deriv smoothStep ((‖z‖ - a) / L) * (1 / L) * (inner ℝ z ν / ‖z‖) := by
        simp only [hf_def]
        exact radialCutoff_fderiv_direction_eq ha_pos hL_pos hz0
      rw [h_eq]
      have h1 : deriv smoothStep ((‖z‖ - a) / L) ≤ 0 := by
        exact smoothStep_antitone.deriv_nonpos (x := (‖z‖ - a) / L)
      have h2 : 0 < 1 / L := by positivity
      have h3 : inner ℝ z ν / ‖z‖ < 0 := by
        apply div_neg_of_neg_of_pos h_inner h_norm_pos
      nlinarith

  -- Step 2: find open interval where deriv smoothStep < 0
  rcases exists_smoothStep_deriv_neg_interval with ⟨t1, t2, ht1_pos, ht1_lt_t2, ht2_lt_one, h_neg⟩
  set ρ1 : ℝ := a + L * t1 with hρ1_def
  set ρ2 : ℝ := a + L * t2 with hρ2_def
  have hρ1_pos : 0 < ρ1 := by positivity
  have hρ1_lt_ρ2 : ρ1 < ρ2 := by
    dsimp only [ρ1, ρ2]
    have h : t1 < t2 := ht1_lt_t2
    have hL_pos' : 0 < L := hL_pos
    nlinarith
  have hρ2_lt_one : ρ2 < 1 := by
    dsimp only [ρ2, a, L]
    have h : t2 < 1 := ht2_lt_one
    linarith

  -- Step 3: define open set V where f > 0
  let V : Set (E n) := {z | ρ1 < ‖z‖ ∧ ‖z‖ < ρ2 ∧ inner ℝ z ν < 0}
  have hV_open : IsOpen V := by
    have h_cnorm : Continuous (fun z : E n => ‖z‖) := by fun_prop
    have h_cinner : Continuous (fun z : E n => inner ℝ z ν) := by fun_prop
    have h1 : IsOpen {z : E n | ρ1 < ‖z‖} := isOpen_Ioi.preimage h_cnorm
    have h2 : IsOpen {z : E n | ‖z‖ < ρ2} := isOpen_Iio.preimage h_cnorm
    have h3 : IsOpen {z : E n | inner ℝ z ν < 0} := isOpen_Iio.preimage h_cinner
    have h4 : IsOpen ({z : E n | ρ1 < ‖z‖} ∩ {z : E n | ‖z‖ < ρ2} ∩ {z : E n | inner ℝ z ν < 0}) :=
      (h1.inter h2).inter h3
    have h5 : {z : E n | ρ1 < ‖z‖} ∩ {z : E n | ‖z‖ < ρ2} ∩ {z : E n | inner ℝ z ν < 0} = V := by
      ext z; simp [V] <;> tauto
    rw [← h5]; exact h4
  have hV_nonempty : V.Nonempty := by
    let z0 : E n := -((ρ1 + ρ2) / 2) • ν
    have h_norm_z0 : ‖z0‖ = (ρ1 + ρ2) / 2 := by
      have h : ‖z0‖ = ‖-((ρ1 + ρ2) / 2)‖ * ‖ν‖ := norm_smul _ _
      rw [h, hν_unit]
      have hρ2_pos : 0 < ρ2 := by linarith [hρ1_pos, hρ1_lt_ρ2]
      have hpos : 0 < (ρ1 + ρ2) / 2 := by linarith [hρ1_pos, hρ2_pos]
      have habs : ‖-((ρ1 + ρ2) / 2)‖ = (ρ1 + ρ2) / 2 := by
        have h1 : ‖-((ρ1 + ρ2) / 2)‖ = ‖(ρ1 + ρ2) / 2‖ := by rw [norm_neg]
        rw [h1]
        have h2 : ‖(ρ1 + ρ2) / 2‖ = |(ρ1 + ρ2) / 2| := Real.norm_eq_abs _
        rw [h2, abs_of_pos hpos]
      rw [habs] <;> ring
    have h1 : ρ1 < ‖z0‖ := by rw [h_norm_z0] <;> linarith
    have h2 : ‖z0‖ < ρ2 := by rw [h_norm_z0] <;> linarith
    have h3 : inner ℝ z0 ν < 0 := by
      have h4 : inner ℝ z0 ν = -((ρ1 + ρ2) / 2) * inner ℝ ν ν := by
        simp [z0, inner_smul_left] <;> ring
      rw [h4]
      have h5 : inner ℝ ν ν = (‖ν‖ : ℝ) ^ 2 := by
        rw [inner_self_eq_norm_sq_to_K] <;> norm_cast
      rw [h5, hν_unit]
      have hpos2 : 0 < (ρ1 + ρ2) / 2 := by linarith [hρ1_pos, hρ1_lt_ρ2]
      simpa using neg_neg_of_pos hpos2
    exact ⟨z0, h1, h2, h3⟩
  have hV_pos_vol : 0 < volume V :=
    hV_open.measure_pos volume hV_nonempty

  -- Step 4: f > 0 on V
  have h_pos_on_V : ∀ z ∈ V, 0 < f z := by
    intro z hz
    have hz_ne : z ≠ 0 := by
      intro h
      have h4 : ρ1 < ‖z‖ := hz.1
      rw [h] at h4
      have h5 : ‖(0 : E n)‖ = 0 := by simp
      rw [h5] at h4
      linarith [hρ1_pos]
    have h4 : ρ1 < ‖z‖ := hz.1
    have h5 : ‖z‖ < ρ2 := hz.2.1
    have h6 : inner ℝ z ν < 0 := hz.2.2
    have h71 : t1 < (‖z‖ - a) / L := by
      have h_eq : ρ1 = a + L * t1 := by simp [ρ1]
      rw [h_eq] at h4
      have hL_pos' : 0 < L := hL_pos
      have h2 : L * t1 < ‖z‖ - a := by linarith
      calc t1
        = (L * t1) / L := by field_simp [hL_pos'.ne'] <;> ring
      _ < (‖z‖ - a) / L := by gcongr
    have h72 : (‖z‖ - a) / L < t2 := by
      have h_eq : ρ2 = a + L * t2 := by simp [ρ2]
      rw [h_eq] at h5
      have hL_pos' : 0 < L := hL_pos
      have h : ‖z‖ - a < L * t2 := by linarith
      calc (‖z‖ - a) / L
        < (L * t2) / L := by gcongr
      _ = t2 := by field_simp [hL_pos'.ne'] <;> ring
    have h7 : (‖z‖ - a) / L ∈ Set.Ioo t1 t2 := ⟨h71, h72⟩
    have h8 : deriv smoothStep ((‖z‖ - a) / L) < 0 := h_neg _ h7
    have h9 : 0 < ‖z‖ := by linarith
    have h_eq : f z = deriv smoothStep ((‖z‖ - a) / L) * (1 / L) * (inner ℝ z ν / ‖z‖) := by
      simp only [hf_def]
      exact radialCutoff_fderiv_direction_eq ha_pos hL_pos hz_ne
    rw [h_eq]
    have h10 : 0 < 1 / L := by positivity
    have h11 : inner ℝ z ν / ‖z‖ < 0 := by
      apply div_neg_of_neg_of_pos h6 h9
    nlinarith

  -- Step 5: integral is positive
  have h_cont : Continuous f := by
    have h2 : Continuous (fun z : E n => (fderiv ℝ φ z) ν) := by
      have h3 : Continuous (fun p : (E n) × (E n) => (fderiv ℝ φ p.1) p.2) :=
        (radialCutoff_contDiff ha_pos hL_pos).continuous_fderiv_apply (by simp)
      have h4 : Continuous (fun z : E n => (z, ν)) := by fun_prop
      exact h3.comp h4
    simpa [hf_def] using h2
  have h_full : Integrable f volume := h_cont.integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset (isCompact_closedBall _ _) isClosed_closure
      (show tsupport f ⊆ closedBall (0 : E n) 1 from by
        calc tsupport f = closure (Function.support f) := by rfl
          _ ⊆ closure (closedBall (0 : E n) 1) := closure_mono (by
            intro z hz
            have h1 : f z ≠ 0 := by simpa [hf_def, Function.mem_support] using hz
            by_contra h2
            have h3 : 1 < ‖z‖ := by simpa [closedBall, dist_zero_right] using h2
            have h4 : ∀ᶠ w in nhds z, 1 < ‖w‖ := by
              have h5 : Continuous (fun w : E n => ‖w‖) := by fun_prop
              exact h5.continuousAt.eventually (lt_mem_nhds h3)
            have h6 : ∀ᶠ w in nhds z, φ w = 0 := by
              filter_upwards [h4] with w hw
              have h7 : w ∉ ball (0 : E n) (a + L) := by
                have h8 : a + L = 1 := by simp [ha_def, hL_def] <;> norm_num
                rw [h8]
                simpa [ball, dist_zero_right] using le_of_lt hw
              exact radialCutoff_zero_of_not_mem_ball ha_pos hL_pos h7
            have h9 : HasFDerivAt φ (0 : E n →L[ℝ] ℝ) z := by
              have h_const : HasFDerivAt (fun _ : E n => (0 : ℝ)) (0 : E n →L[ℝ] ℝ) z :=
                hasFDerivAt_const (x := z) (c := (0 : ℝ))
              have h10 : φ =ᶠ[nhds z] (fun _ : E n => (0 : ℝ)) := by
                filter_upwards [h6] with w hw; exact hw
              exact h_const.congr_of_eventuallyEq h10
            have h10 : fderiv ℝ φ z = 0 := h9.fderiv
            have h11 : f z = 0 := by simp only [hf_def, h10, zero_apply]
            contradiction)
          _ = closedBall (0 : E n) 1 := by simp))
  have h_int : ∀ (S : Set (E n)), IntegrableOn f S := fun S => h_full.integrableOn
  rcases hV_nonempty with ⟨z0, hz0V⟩
  have h_f_z0_pos : 0 < f z0 := h_pos_on_V z0 hz0V
  have h_half_pos : f z0 / 2 < f z0 := by linarith
  have h1 : ∀ᶠ z in nhds z0, f z0 / 2 < f z :=
    h_cont.continuousAt.eventually (lt_mem_nhds h_half_pos)
  have h2 : ∀ᶠ z in nhds z0, z ∈ V := hV_open.mem_nhds hz0V
  have h3 : ∀ᶠ z in nhds z0, z ∈ V ∧ f z0 / 2 < f z := h2.and h1
  rcases Metric.nhds_basis_ball.eventually_iff.mp h3 with ⟨ε, hε_pos, hball⟩
  have hball' : ∀ (z : E n), z ∈ ball z0 ε → (z ∈ V ∧ f z0 / 2 < f z) := hball
  have hball_sub : ball z0 ε ⊆ V := fun z hz => (hball' z hz).1
  have hball_gt : ∀ z ∈ ball z0 ε, f z0 / 2 < f z := fun z hz => (hball' z hz).2
  have hV_sub_half : V ⊆ halfSpace ν := fun z hz => hz.2.2
  have h_ball_sub_half : ball z0 ε ⊆ halfSpace ν := hball_sub.trans hV_sub_half
  have h_ball_meas : MeasurableSet (ball z0 ε) := isOpen_ball.measurableSet
  have h4 : ∫ z in halfSpace ν, f z ≥ ∫ z in ball z0 ε, f z := by
    have h_diff_meas : MeasurableSet (halfSpace ν \ ball z0 ε) :=
      hH_meas.diff h_ball_meas
    have h_disj : Disjoint (ball z0 ε) (halfSpace ν \ ball z0 ε) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      exact hx2.2 hx1
    have h_union : (ball z0 ε) ∪ (halfSpace ν \ ball z0 ε) = halfSpace ν :=
      Set.union_sdiff_cancel h_ball_sub_half
    have h9 := MeasureTheory.setIntegral_union h_disj h_diff_meas (h_int (ball z0 ε)) (h_int (halfSpace ν \ ball z0 ε))
    have h10 : ball z0 ε ∪ (halfSpace ν \ ball z0 ε) = halfSpace ν := h_union
    rw [h10] at h9
    have h9' : ∫ z in halfSpace ν, f z ∂volume =
        ∫ z in ball z0 ε, f z ∂volume + ∫ z in (halfSpace ν \ ball z0 ε), f z ∂volume := h9
    have h7 : ∀ z ∈ halfSpace ν \ ball z0 ε, 0 ≤ f z := fun z hz => h_nonneg z hz.1
    have h6 : 0 ≤ ∫ z in (halfSpace ν \ ball z0 ε), f z ∂volume :=
      MeasureTheory.setIntegral_nonneg h_diff_meas h7
    have h10 : ∫ z in halfSpace ν, f z ∂volume ≥ ∫ z in ball z0 ε, f z ∂volume := by
      rw [h9]
      linarith [h6]
    simpa using h10
  have h5 : ∫ z in ball z0 ε, f z ≥ (f z0 / 2) * (volume (ball z0 ε)).toReal := by
    have h6 : ∀ z ∈ ball z0 ε, f z0 / 2 ≤ f z := fun z hz => (hball_gt z hz).le
    have h_int_ball : IntegrableOn f (ball z0 ε) := h_int (ball z0 ε)
    have h_int_const : IntegrableOn (fun _ : E n => f z0 / 2) (ball z0 ε) := by
      exact integrableOn_const
    have h7 : ∫ z in ball z0 ε, f z ≥ ∫ z in ball z0 ε, (f z0 / 2) :=
      MeasureTheory.setIntegral_mono_on h_int_const h_int_ball h_ball_meas h6
    have h8 : ∫ z in ball z0 ε, (f z0 / 2) = (f z0 / 2) * (volume (ball z0 ε)).toReal := by
      have h9 : ∫ z in ball z0 ε, (f z0 / 2) = (volume (ball z0 ε)).toReal • (f z0 / 2) := by
        rw [integral_const]
        <;> simp [Measure.real]
        <;> rfl
      rw [h9]
      have h10 : (volume (ball z0 ε)).toReal • (f z0 / 2) = (f z0 / 2) * (volume (ball z0 ε)).toReal := by
        simp [smul_eq_mul, mul_comm]
        <;> ring
      exact h10
    calc
      ∫ z in ball z0 ε, f z ≥ ∫ z in ball z0 ε, (f z0 / 2) := h7
      _ = (f z0 / 2) * (volume (ball z0 ε)).toReal := h8
  have h7 : 0 < (volume (ball z0 ε)).toReal := by
    have h9 : 0 < volume (ball z0 ε) :=
      isOpen_ball.measure_pos volume ⟨z0, mem_ball_self hε_pos⟩
    have h10 : 0 < (volume (ball z0 ε)).toReal := by
      have h11 : volume (ball z0 ε) < ⊤ := Metric.isBounded_ball.measure_lt_top
      exact ENNReal.toReal_pos_iff.mpr ⟨h9, h11⟩
    exact h10
  have h8 : 0 < (f z0 / 2) * (volume (ball z0 ε)).toReal := by
    exact _root_.mul_pos (by linarith) h7
  linarith

-- ============================================================================
-- Integral convergence from symmetric difference convergence
-- ============================================================================

/-- If `f` is continuous with compact support in `K`, and symmetric difference
with `B` tends to zero on `K`, then integrals over `A r` converge to the
integral over `B`. -/
lemma integral_convergence_of_symmDiff
    {f : E n → ℝ} (hf_cont : Continuous f) (hf_support : HasCompactSupport f)
    {A : ℝ → Set (E n)} {B : Set (E n)}
    (hA_meas : ∀ r, MeasurableSet (A r)) (hB_meas : MeasurableSet B)
    {K : Set (E n)} (hK : IsCompact K) (h_support : Function.support f ⊆ K)
    (h_conv : Tendsto (fun r : ℝ => volume (symmDiff (A r) B ∩ K))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Tendsto (fun r : ℝ => ∫ x in A r, f x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ x in B, f x)) := by
  have h_int : ∀ (S : Set (E n)), IntegrableOn f S := by
    have h_full : Integrable f volume := hf_cont.integrable_of_hasCompactSupport hf_support
    intro S; exact h_full.integrableOn
  have h_bdd : ∃ C, 0 < C ∧ ∀ x, |f x| ≤ C := by
    have h1 : BddAbove (Set.image (fun x => |f x|) (tsupport f)) :=
      hf_support.isCompact.bddAbove_image hf_cont.norm.continuousOn
    rcases h1 with ⟨C, hC⟩
    have h2 : ∀ x ∈ tsupport f, |f x| ≤ C := by
      intro x hx; exact hC (Set.mem_image_of_mem _ hx)
    let C' := max C 1
    have hC'_pos : 0 < C' := by positivity
    have h2' : ∀ x ∈ tsupport f, |f x| ≤ C' := fun x hx =>
      le_trans (h2 x hx) (le_max_left _ _)
    have h3 : ∀ x, |f x| ≤ C' := by
      intro x
      by_cases h4 : x ∈ tsupport f
      · exact h2' x h4
      · have h5 : f x = 0 := by
          have h6 : x ∉ Function.support f := fun h7 => h4 (subset_closure h7)
          simpa [Function.mem_support] using h6
        rw [h5, abs_zero]
        exact hC'_pos.le
    exact ⟨C', hC'_pos, h3⟩
  rcases h_bdd with ⟨C, hC_pos, hC_bound⟩
  have h_main : ∀ r, |(∫ x in A r, f x) - (∫ x in B, f x)| ≤
      C * (volume (symmDiff (A r) B ∩ K)).toReal := by
    intro r
    have h_full : Integrable f volume := hf_cont.integrable_of_hasCompactSupport hf_support
    let gA := fun x : E n => Set.indicator (A r) f x
    let gB := fun x : E n => Set.indicator B f x
    have h_gA_int : Integrable gA volume := h_full.indicator (hA_meas r)
    have h_gB_int : Integrable gB volume := h_full.indicator hB_meas
    have h1 : ∫ x in A r, f x = ∫ x, gA x := by
      rw [integral_indicator (hA_meas r)] <;> rfl
    have h2 : ∫ x in B, f x = ∫ x, gB x := by
      rw [integral_indicator hB_meas] <;> rfl
    have h_eq : (∫ x in A r, f x) - (∫ x in B, f x) = ∫ x, (gA x - gB x) := by
      rw [h1, h2, ← integral_sub h_gA_int h_gB_int]
      <;> rfl
    have h_eq2 : (fun x : E n => gA x - gB x) = (fun x : E n => (Set.indicator (A r) (fun _ => (1 : ℝ)) x - Set.indicator B (fun _ => (1 : ℝ)) x) * f x) := by
      funext x
      have hga : gA x = Set.indicator (A r) (fun _ => (1 : ℝ)) x * f x := by
        by_cases h : x ∈ A r <;> simp [gA, Set.indicator_apply, h] <;> ring
      have hgb : gB x = Set.indicator B (fun _ => (1 : ℝ)) x * f x := by
        by_cases h : x ∈ B <;> simp [gB, Set.indicator_apply, h] <;> ring
      rw [hga, hgb] <;> ring
    rw [h_eq, h_eq2]
    let indA := Set.indicator (A r) (fun _ : E n => (1 : ℝ))
    let indB := Set.indicator B (fun _ : E n => (1 : ℝ))
    let indS := Set.indicator (symmDiff (A r) B ∩ K) (fun _ : E n => (1 : ℝ))
    have h4 : |∫ x, (indA x - indB x) * f x| ≤
        ∫ x, |(indA x - indB x) * f x| := abs_integral_le_integral_abs
    have h5 : ∀ x, |(indA x - indB x) * f x| ≤ C * indS x := by
      intro x
      by_cases h6 : x ∈ symmDiff (A r) B ∩ K
      · have h_indS1 : indS x = 1 := by
          simp [indS, Set.indicator, h6]
        have h_diff : |indA x - indB x| ≤ 1 := by
          have h1 : indA x = 0 ∨ indA x = 1 := by simp [indA, Set.indicator] <;> tauto
          have h2 : indB x = 0 ∨ indB x = 1 := by simp [indB, Set.indicator] <;> tauto
          rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2) <;> simp [h1, h2] <;> linarith
        rw [h_indS1]
        have h_abs : |(indA x - indB x) * f x| = |indA x - indB x| * |f x| := by rw [abs_mul]
        rw [h_abs]
        have h7 : |indA x - indB x| * |f x| ≤ 1 * |f x| := by gcongr
        have h8 : 1 * |f x| ≤ C := by
          simpa using hC_bound x
        linarith
      · have h_indS0 : indS x = 0 := by
          simp [indS, Set.indicator, h6]
        have h7 : x ∉ symmDiff (A r) B ∨ x ∉ K := by tauto
        have h_prod : (indA x - indB x) * f x = 0 := by
          rcases h7 with (h7 | h7)
          · have h8 : indA x = indB x := by
              have h9 : x ∉ symmDiff (A r) B := h7
              simp only [indA, indB, symmDiff, Set.mem_union, Set.mem_diff, Set.indicator] at h9 ⊢
              by_cases h10 : x ∈ A r <;> by_cases h11 : x ∈ B <;> simp [h10, h11] at h9 ⊢ <;> tauto
            rw [h8] <;> ring
          · have h8 : x ∉ Function.support f := fun h9 => h7 (h_support h9)
            have h9 : f x = 0 := by simpa [Function.mem_support] using h8
            rw [h9] <;> ring
        rw [h_indS0, h_prod] <;> simp [hC_pos]
    have hS_meas : MeasurableSet (symmDiff (A r) B ∩ K) :=
      (hA_meas r).symmDiff hB_meas |>.inter hK.measurableSet
    calc
      |∫ x, (indA x - indB x) * f x|
        ≤ ∫ x, |(indA x - indB x) * f x| := h4
      _ ≤ ∫ x, C * indS x := by
        have h_int_abs : Integrable (fun x => |(indA x - indB x) * f x|) volume := by
          have h_bound : ∀ x, |(indA x - indB x) * f x| ≤ |f x| := by
            intro x
            have h2 : |indA x - indB x| ≤ 1 := by
              have h3 : indA x = 0 ∨ indA x = 1 := by simp [indA, Set.indicator] <;> tauto
              have h4 : indB x = 0 ∨ indB x = 1 := by simp [indB, Set.indicator] <;> tauto
              rcases h3 with (h3 | h3) <;> rcases h4 with (h4 | h4) <;> simp [h3, h4] <;> linarith
            calc
              |(indA x - indB x) * f x| = |indA x - indB x| * |f x| := by rw [abs_mul]
              _ ≤ 1 * |f x| := by gcongr
              _ = |f x| := by ring
          have h_ae_indA : AEStronglyMeasurable indA volume :=
            aestronglyMeasurable_const.indicator (hA_meas r)
          have h_ae_indB : AEStronglyMeasurable indB volume :=
            aestronglyMeasurable_const.indicator hB_meas
          have h_ae_prod : AEStronglyMeasurable (fun x => (indA x - indB x) * f x) volume :=
            (h_ae_indA.sub h_ae_indB).mul h_full.aestronglyMeasurable
          have h_ae : AEStronglyMeasurable (fun x => |(indA x - indB x) * f x|) volume :=
            h_ae_prod.norm
          have h_bound_ae : ∀ᵐ (a : E n), ‖|(indA a - indB a) * f a|‖ ≤ ‖|f a|‖ := by
            filter_upwards with a
            have h10 : ‖|(indA a - indB a) * f a|‖ = |(indA a - indB a) * f a| := by simp
            have h11 : ‖|f a|‖ = |f a| := by simp
            rw [h10, h11]
            exact h_bound a
          exact h_full.abs.mono h_ae h_bound_ae
        have h_int_C : Integrable (fun x => C * indS x) volume := by
          have h_fin : volume (symmDiff (A r) B ∩ K) < ⊤ := by
            have h_sub : symmDiff (A r) B ∩ K ⊆ K := inter_subset_right
            exact lt_of_le_of_lt (measure_mono h_sub) hK.measure_lt_top
          letI : IsFiniteMeasure (volume.restrict (symmDiff (A r) B ∩ K)) :=
            ⟨by simpa [Measure.restrict_apply'] using h_fin⟩
          have h_indS_on : IntegrableOn (fun _ => (1 : ℝ)) (symmDiff (A r) B ∩ K) volume :=
            integrableOn_const
          have h_indS_int : Integrable indS volume :=
            (MeasureTheory.integrable_indicator_iff hS_meas).mpr h_indS_on
          exact h_indS_int.const_mul C
        exact integral_mono h_int_abs h_int_C h5
      _ = C * (volume (symmDiff (A r) B ∩ K)).toReal := by
        have h_int_ind : ∫ x, C * indS x = C * (volume (symmDiff (A r) B ∩ K)).toReal := by
          rw [MeasureTheory.integral_const_mul]
          have h9 : ∫ x, indS x = (volume (symmDiff (A r) B ∩ K)).toReal := by
            rw [integral_indicator hS_meas]
            simp [indS, integral_const]
            <;> rfl
          rw [h9] <;> ring
        exact h_int_ind
  have h1 : ContinuousAt ENNReal.toReal 0 := ENNReal.continuousAt_toReal (by simp)
  have h2 : Tendsto (fun r : ℝ => (volume (symmDiff (A r) B ∩ K)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    h1.tendsto.comp h_conv
  have h_tendsto : Tendsto (fun r : ℝ => C * (volume (symmDiff (A r) B ∩ K)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [mul_zero] using h2.const_mul C
  have h_zero : Tendsto (fun _ : ℝ => (0 : ℝ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := tendsto_const_nhds
  have h_ev1 : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), (0 : ℝ) ≤ |(∫ x in A r, f x) - (∫ x in B, f x)| := by
    filter_upwards with _ <;> exact abs_nonneg _
  have h_ev2 : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), |(∫ x in A r, f x) - (∫ x in B, f x)| ≤ C * (volume (symmDiff (A r) B ∩ K)).toReal := by
    filter_upwards with r <;> exact h_main r
  have h_abs_tendsto : Tendsto (fun r : ℝ => |(∫ x in A r, f x) - (∫ x in B, f x)|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' (f := fun r : ℝ => |(∫ x in A r, f x) - (∫ x in B, f x)|)
      h_zero h_tendsto h_ev1 h_ev2
  have h_main_tendsto : Tendsto (fun r : ℝ => (∫ x in A r, f x) - (∫ x in B, f x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero (fun r : ℝ => (∫ x in A r, f x) - (∫ x in B, f x))).mpr h_abs_tendsto
  have h_b_const : Tendsto (fun _ : ℝ => ∫ x in B, f x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ x in B, f x)) := tendsto_const_nhds
  have h_sum : Tendsto (fun r : ℝ => ((∫ x in A r, f x) - (∫ x in B, f x)) + (∫ x in B, f x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 + (∫ x in B, f x))) :=
    h_main_tendsto.add h_b_const
  have h_final : Tendsto (fun r : ℝ => ∫ x in A r, f x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ x in B, f x)) := by
    convert h_sum using 1
    · funext r; ring
    · simp
  exact h_final

-- ============================================================================
-- Scaling identity
-- ============================================================================

/-- Chain rule for scaled cutoff:
`fderiv (fun y => φ((1/r)•(y-x))) y ν = (1/r) * fderiv φ ((1/r)•(y-x)) ν`. -/
lemma scaled_cutoff_fderiv {x : E n} {r : ℝ} (hr : 0 < r)
    {φ : E n → ℝ} (hφ : ContDiff ℝ ∞ φ) {ν : E n} (y : E n) :
    fderiv ℝ (fun y : E n => φ ((1 / r) • (y - x))) y ν =
      (1 / r) * fderiv ℝ φ ((1 / r) • (y - x)) ν := by
  have hr_ne : r ≠ 0 := hr.ne'
  set c : ℝ := 1 / r with hc_def
  set L : E n → E n := fun y => c • (y - x) with hL_def
  let idCLM : E n →L[ℝ] E n := ContinuousLinearMap.id ℝ (E n)
  let fderivL : E n →L[ℝ] E n := c • idCLM
  have h_id_id : HasFDerivAt (fun y : E n => y) idCLM y := hasFDerivAt_id y
  have h_id : HasFDerivAt (fun y : E n => y - x) idCLM y := h_id_id.sub_const x
  have hL_fd : HasFDerivAt L fderivL y := h_id.const_smul c
  have hφ_diff : DifferentiableAt ℝ φ (L y) :=
    (hφ.differentiable (by simp)).differentiableAt
  have hφ_fd : HasFDerivAt φ (fderiv ℝ φ (L y)) (L y) := hφ_diff.hasFDerivAt
  have h_chain : HasFDerivAt (φ ∘ L) ((fderiv ℝ φ (L y)).comp fderivL) y :=
    hφ_fd.comp y hL_fd
  have h2 : fderiv ℝ (φ ∘ L) y = (fderiv ℝ φ (L y)).comp fderivL := h_chain.fderiv
  have h3 : ((fderiv ℝ φ (L y)).comp fderivL) ν = c * fderiv ℝ φ (L y) ν := by
    have h4 : ((fderiv ℝ φ (L y)).comp fderivL) ν = fderiv ℝ φ (L y) (fderivL ν) := by rfl
    rw [h4]
    have h5 : fderivL ν = c • ν := by
      simp [fderivL, idCLM, ContinuousLinearMap.smul_apply]
      <;> rfl
    rw [h5]
    have h6 : fderiv ℝ φ (L y) (c • ν) = c * fderiv ℝ φ (L y) ν :=
      (fderiv ℝ φ (L y)).map_smul c ν
    exact h6
  have h_main : fderiv ℝ (φ ∘ L) y ν = c * fderiv ℝ φ (L y) ν := by
    rw [h2, h3]
  have h_eq : (φ ∘ L) = (fun y : E n => φ ((1 / r) • (y - x))) := by
    funext z; simp [L, hc_def]
  rw [h_eq] at h_main
  exact h_main

/-- Change of variables: `∫_U fderiv φ_r ν = r^(n-1) · ∫_{blowUp U x r} fderiv φ ν`. -/
lemma scaling_derivative_integral
    {U : Set (E n)} (hU_meas : MeasurableSet U) (hn : 2 ≤ n)
    {x : E n} {r : ℝ} (hr : 0 < r)
    {φ : E n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {ν : E n} :
    ∫ y in U, fderiv ℝ (fun y : E n => φ ((1 / r) • (y - x))) y ν =
      r ^ (n - 1) * ∫ z in blowUp U x r, fderiv ℝ φ z ν := by
  have hr_ne : r ≠ 0 := hr.ne'
  let scale : E n ≃L[ℝ] E n := scalingEquiv r hr_ne
  let e : E n → E n := fun z => scale z + x
  let ψ : E n → ℝ := fun y => φ ((1 / r) • (y - x))
  have h_e_diff : Differentiable ℝ e := by fun_prop
  have h_e_fderiv : ∀ z, fderiv ℝ e z = (scale : E n →L[ℝ] E n) := by
    intro z
    have h1 : HasFDerivAt scale (scale : E n →L[ℝ] E n) z :=
      (scale : E n →L[ℝ] E n).hasFDerivAt
    have h_const : HasFDerivAt (fun _ : E n => x) (0 : E n →L[ℝ] E n) z :=
      hasFDerivAt_const (c := x) (x := z)
    have h2 : HasFDerivAt e ((scale : E n →L[ℝ] E n) + (0 : E n →L[ℝ] E n)) z :=
      h1.add h_const
    have h3 : (scale : E n →L[ℝ] E n) + (0 : E n →L[ℝ] E n) = (scale : E n →L[ℝ] E n) := by
      ext w; simp
    rw [h3] at h2
    exact h2.fderiv
  have h_e_inj : Set.InjOn e (blowUp U x r) := by
    intro z1 _ z2 _ h
    simpa [e] using h
  have h_det : ∀ z, |(fderiv ℝ e z).det| = r ^ n := by
    intro z
    have h_fd : fderiv ℝ e z = (scale : E n →L[ℝ] E n) := h_e_fderiv z
    rw [h_fd]
    have h : (scale : E n →ₗ[ℝ] E n).det = r ^ n := scalingEquiv_det r hr_ne
    have h_eq_det : (scale : E n →L[ℝ] E n).det = (scale : E n →ₗ[ℝ] E n).det := by rfl
    rw [h_eq_det, h, abs_pow, abs_of_pos hr]
  let S := blowUp U x r
  have h_image : e '' S = U := by
    ext y
    simp only [Set.mem_image, blowUp, blowUpMap, e, scalingEquiv_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases hz with ⟨w, hw, h_eq⟩
      have h4 : scale z = w - x := by
        have h_eq3 : z = (1 / r) • (w - x) := by
          have h : blowUpMap x r w = (1 / r) • (w - x) := by
            simp [blowUpMap] <;> ring
          rw [← h_eq, h]
        have h_eq2 : r • z = w - x := by
          rw [h_eq3, smul_smul]
          have h3 : r * (1 / r) = 1 := by field_simp [hr_ne]
          rw [h3, one_smul]
        exact h_eq2
      have h5 : scale z + x = w := by rw [h4] <;> abel
      rw [h5]; exact hw
    · intro hy
      let z : E n := (1 / r) • (y - x)
      have h_z_in : z ∈ blowUp U x r := by
        refine ⟨y, hy, ?_⟩
        simp [blowUpMap, z]
      have h5 : scale z = y - x := by
        have h51 : r • z = y - x := by
          calc
            r • z = r • ((1 / r) • (y - x)) := by rw [show z = (1 / r) • (y - x) from rfl]
            _ = (r * (1 / r)) • (y - x) := by rw [smul_smul]
            _ = (1 : ℝ) • (y - x) := by
              have h3 : r * (1 / r) = 1 := by
                field_simp [hr_ne]
              rw [h3]
            _ = y - x := by simp
        exact h51
      refine ⟨z, h_z_in, ?_⟩
      have h6 : e z = y := by
        simp [e, h5] <;> abel
      exact h6
  let h : E n → ℝ := fun y => fderiv ℝ ψ y ν
  have hψ_smooth : ContDiff ℝ ∞ ψ := hφ.comp (by fun_prop)
  have h_h_comp : Continuous h := by
    have h1 : Continuous (fun p : (E n) × (E n) => (fderiv ℝ ψ p.1) p.2) :=
      hψ_smooth.continuous_fderiv_apply (by simp)
    have h2 : Continuous (fun y : E n => (y, ν)) := by fun_prop
    exact h1.comp h2
  have h_blow_meas : MeasurableSet S := by
    have h_blowMap_meas : MeasurableEmbedding (blowUpMap x r) :=
      blowUpMap_measurableEmbedding x hr_ne
    exact h_blowMap_meas.measurableSet_image.mpr hU_meas
  have h_eq1 : ∫ y in U, h y = ∫ z in S, |(fderiv ℝ e z).det| * h (e z) := by
    have h_rewrite : U = e '' S := h_image.symm
    rw [h_rewrite]
    exact MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      volume h_blow_meas
      (fun z _ => (h_e_diff.differentiableAt.hasFDerivAt).hasFDerivWithinAt) h_e_inj h
  rw [h_eq1]
  have h_eq2 : ∀ z, |(fderiv ℝ e z).det| * h (e z) =
      r ^ (n - 1) * fderiv ℝ φ z ν := by
    intro z
    have h3 : h (e z) = (1 / r) * fderiv ℝ φ z ν := by
      have h4 : h (e z) = fderiv ℝ ψ (e z) ν := by rfl
      rw [h4]
      have h5 := scaled_cutoff_fderiv (x := x) (ν := ν) hr hφ (e z)
      have h6 : (1 / r) • ((e z) - x) = z := by
        have h7 : (e z) - x = r • z := by
          simp [e, scalingEquiv_apply] <;> abel
        rw [h7]
        rw [smul_smul]
        have h8 : (1 / r) * r = 1 := by field_simp [hr_ne]
        rw [h8, one_smul]
      rw [h5, h6]
    rw [h3, h_det z]
    have h4 : r ^ n * ((1 / r) * fderiv ℝ φ z ν) = r ^ (n - 1) * fderiv ℝ φ z ν := by
      have hn1 : 1 ≤ n := by omega
      have h : r ^ n * (1 / r) = r ^ (n - 1) := by
        cases n with
        | zero => omega
        | succ n' =>
          simp [pow_succ] <;> field_simp [hr_ne] <;> ring
      have h5 : r ^ n * ((1 / r) * fderiv ℝ φ z ν) = (r ^ n * (1 / r)) * fderiv ℝ φ z ν := by ring
      rw [h5, h]
    exact h4
  have h_eq3 : (fun z : E n => |(fderiv ℝ e z).det| * h (e z)) =
      (fun z : E n => r ^ (n - 1) * fderiv ℝ φ z ν) := funext h_eq2
  rw [h_eq3]
  have h_int_mul : ∫ z in S, r ^ (n - 1) * fderiv ℝ φ z ν =
      r ^ (n - 1) * ∫ z in S, fderiv ℝ φ z ν := by
    rw [MeasureTheory.integral_const_mul]
  exact h_int_mul

-- ============================================================================
-- Main theorem
-- ============================================================================

/-- **Perimeter lower density from reduced boundary data**.

At a reduced boundary point `x` with normal `ν`, there exist `c > 0` and `r0 > 0`
such that for all `0 < r < r0`,
`perimeterIn U (ball x r) ≥ c · r^(n-1)`.

This is proved directly from `ReducedBoundaryData` via the Gauss-Green cutoff
and blow-up convergence, without assuming perimeter measure density bounds. -/
theorem perimeter_lower_density_from_data
    {U : Set (E n)} (hU : IsOpen U) (hU_reg : U = interior (closure U))
    (hBdd : Bornology.IsBounded U) (hn : 2 ≤ n)
    {x : E n} {ν : E n} (hν_unit : ‖ν‖ = 1)
    (h_reduced : ReducedBoundaryData U x ν) :
    ∃ (c : ℝ) (r0 : ℝ), 0 < c ∧ 0 < r0 ∧
      ∀ r, 0 < r → r < r0 →
        ENNReal.ofReal (c * r ^ (n - 1)) ≤ perimeterIn U (ball x r) := by
  set a : ℝ := 1 / 2 with ha_def
  set L : ℝ := 1 / 2 with hL_def
  set φ : E n → ℝ := radialCutoff (0 : E n) a L with hφ_def
  set f : E n → ℝ := fun z => fderiv ℝ φ z ν with hf_def
  have ha_pos : 0 < a := by norm_num
  have hL_pos : 0 < L := by norm_num
  have hU_meas : MeasurableSet U := hU.measurableSet

  -- Half-space integral is positive
  have h_I_H_pos : 0 < ∫ z in halfSpace ν, f z :=
    halfspace_derivative_integral_pos hν_unit hn
  set I_H : ℝ := ∫ z in halfSpace ν, f z with hI_H_def
  have hI_H_pos : 0 < I_H := h_I_H_pos

  -- f is continuous with compact support in closedBall 0 1
  have h_f_cont : Continuous f := by
    have h2 : Continuous (fun z : E n => (fderiv ℝ φ z) ν) := by
      have h3 : Continuous (fun p : (E n) × (E n) => (fderiv ℝ φ p.1) p.2) :=
        (radialCutoff_contDiff ha_pos hL_pos).continuous_fderiv_apply (by simp)
      have h4 : Continuous (fun z : E n => (z, ν)) := by fun_prop
      exact h3.comp h4
    simpa [hf_def] using h2
  have h_f_support : Function.support f ⊆ closedBall (0 : E n) 1 := by
    intro z hz
    have h1 : f z ≠ 0 := by simpa [hf_def, Function.mem_support] using hz
    by_contra h2
    have h3 : z ∉ closedBall (0 : E n) 1 := h2
    have h4 : ‖z‖ > 1 := by simpa [closedBall, dist_zero_right] using h3
    have h5 : ∀ᶠ w in nhds z, ‖w‖ > 1 := by
      have h6 : Continuous (fun w : E n => ‖w‖) := by fun_prop
      exact h6.continuousAt.eventually (lt_mem_nhds h4)
    have h7 : ∀ᶠ w in nhds z, φ w = 0 := by
      filter_upwards [h5] with w hw
      have h81 : 1 ≤ ‖w‖ := le_of_lt hw
      have h82 : w ∉ ball (0 : E n) (a + L) := by
        have h9 : a + L = 1 := by simp [ha_def, hL_def] <;> norm_num
        rw [h9]
        simpa [ball, dist_zero_right] using h81
      exact radialCutoff_zero_of_not_mem_ball ha_pos hL_pos h82
    have h8 : HasFDerivAt φ (0 : E n →L[ℝ] ℝ) z := by
      have h_const : HasFDerivAt (fun _ : E n => (0 : ℝ)) (0 : E n →L[ℝ] ℝ) z :=
        hasFDerivAt_const (x := z) (c := (0 : ℝ))
      have h7' : φ =ᶠ[nhds z] (fun _ : E n => (0 : ℝ)) := by
        filter_upwards [h7] with w hw; exact hw
      exact h_const.congr_of_eventuallyEq h7'
    have h9 : fderiv ℝ φ z = 0 := h8.fderiv
    have h10 : f z = 0 := by
      simp only [hf_def, h9, zero_apply]
    contradiction
  have h_f_compact : HasCompactSupport f := by
    have h1 : tsupport f ⊆ closedBall (0 : E n) 1 := by
      calc tsupport f = closure (Function.support f) := by rfl
        _ ⊆ closure (closedBall (0 : E n) 1) := closure_mono h_f_support
        _ = closedBall (0 : E n) 1 := by simp
    exact IsCompact.of_isClosed_subset (isCompact_closedBall _ _) isClosed_closure h1
  have h_φ_support : Function.support φ ⊆ ball (0 : E n) 1 := by
    intro z hz
    have h1 : φ z ≠ 0 := by simpa [hφ_def, Function.mem_support] using hz
    by_contra h2
    have h3 : z ∉ ball (0 : E n) (a + L) := by
      have h4 : a + L = 1 := by simp [ha_def, hL_def] <;> norm_num
      rw [h4]
      exact h2
    have h4 : φ z = 0 := radialCutoff_zero_of_not_mem_ball ha_pos hL_pos h3
    contradiction

  -- Blow-up lemma gives symmetric difference convergence
  have h_blowup : ∀ (R : ℝ), 0 < R →
      Tendsto (fun r : ℝ => volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ ball (0 : E n) R))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    blow_up_lemma hU_meas x ν hν_unit h_reduced hn

  -- Integral convergence
  have hA_meas : ∀ r, MeasurableSet (blowUp U x r) := by
    intro r
    by_cases hr : r = 0
    · have h_simp : blowUp U x r = (fun (_ : E n) => (0 : E n)) '' U := by
        simp [blowUp, blowUpMap, hr]
        <;> rfl
      rw [h_simp]
      have h_img : (fun (_ : E n) => (0 : E n)) '' U = ∅ ∨ (fun (_ : E n) => (0 : E n)) '' U = {(0 : E n)} := by
        by_cases hU_empty : U = ∅
        · left
          rw [hU_empty] <;> simp
        · right
          have hU_nonempty : U.Nonempty := Set.nonempty_iff_ne_empty.mpr hU_empty
          ext z
          simp [hU_nonempty]
      rcases h_img with (h_img | h_img)
      · rw [h_img] <;> simp
      · rw [h_img] <;> exact measurableSet_singleton _
    · have h_blowMap_meas : MeasurableEmbedding (blowUpMap x r) :=
        blowUpMap_measurableEmbedding x hr
      exact h_blowMap_meas.measurableSet_image.mpr hU_meas
  have hH_meas : MeasurableSet (halfSpace ν) := by
    have h1 : Continuous (fun z : E n => inner ℝ z ν) := by fun_prop
    have h2 : Continuous (fun _ : E n => (0 : ℝ)) := by fun_prop
    exact (isOpen_Iio.preimage h1).measurableSet
  have h_blowup2 := h_blowup 2 (by norm_num)
  have h_conv_closed : Tendsto (fun r : ℝ => volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ closedBall (0 : E n) 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h_sub : ∀ r, volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ closedBall (0 : E n) 1) ≤
        volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ ball (0 : E n) 2) := by
      intro r
      apply measure_mono
      apply inter_subset_inter_right _
      exact closedBall_subset_ball (by norm_num)
    have h_zero : Tendsto (fun _ : ℝ => (0 : ENNReal)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := tendsto_const_nhds
    have h_ev1 : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), (0 : ENNReal) ≤ volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ closedBall (0 : E n) 1) := by
      filter_upwards with _ <;> positivity
    have h_ev2 : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ closedBall (0 : E n) 1) ≤ volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ ball (0 : E n) 2) := by
      filter_upwards with r <;> exact h_sub r
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (f := fun r : ℝ => volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ closedBall (0 : E n) 1)) h_zero h_blowup2 h_ev1 h_ev2
  have h_conv_integral : Tendsto (fun r : ℝ => ∫ z in blowUp U x r, f z)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds I_H) :=
    integral_convergence_of_symmDiff h_f_cont h_f_compact hA_meas hH_meas
      (isCompact_closedBall (0 : E n) 1) h_f_support h_conv_closed

  -- For small r, integral ≥ I_H / 2
  have h_eventually : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0),
      I_H / 2 ≤ ∫ z in blowUp U x r, f z := by
    have h_nhds : Ioo (I_H / 2) (3 * I_H / 2) ∈ nhds I_H := by
      apply Ioo_mem_nhds <;> linarith
    have h : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), (∫ z in blowUp U x r, f z) ∈ Ioo (I_H / 2) (3 * I_H / 2) :=
      h_conv_integral h_nhds
    filter_upwards [h] with r hr
    have h9 : I_H / 2 < ∫ z in blowUp U x r, f z := hr.1
    linarith

  -- Get explicit r0
  have h_basis : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).HasBasis (fun ε => 0 < ε) (fun ε => ball (0 : ℝ) ε ∩ Set.Ioi 0) :=
    Metric.nhdsWithin_basis_ball
  rcases h_basis.eventually_iff.mp h_eventually with ⟨ε, hε_pos, hball⟩
  have hball' : ∀ (r : ℝ), r ∈ ball (0 : ℝ) ε ∩ Set.Ioi 0 → I_H / 2 ≤ ∫ z in blowUp U x r, f z := hball
  have h_r0 : ∃ r0, 0 < r0 ∧ ∀ r, 0 < r → r < r0 →
      I_H / 2 ≤ ∫ z in blowUp U x r, f z := by
    refine ⟨ε, hε_pos, fun r hr_pos hr_lt => ?_⟩
    have h1 : r ∈ ball (0 : ℝ) ε ∩ Set.Ioi 0 := by
      simp only [Set.mem_inter_iff, mem_ball, dist_zero_right, Set.mem_setOf_eq]
      exact ⟨by rw [Real.norm_eq_abs, abs_of_pos hr_pos] <;> exact hr_lt, hr_pos⟩
    exact hball' r h1
  rcases h_r0 with ⟨r0, hr0_pos, h_ineq⟩

  -- For each r < r0, construct test vector field and apply perimeter definition
  refine ⟨I_H / 2, r0, by linarith, hr0_pos, ?_⟩
  intro r hr_pos hr_lt
  set φ_r : E n → ℝ := fun y => φ ((1 / r) • (y - x)) with hφ_r_def
  set Φ : E n → E n := fun y => φ_r y • ν with hΦ_def

  have h_inner_smooth : ContDiff ℝ ∞ (fun y : E n => (1 / r) • (y - x)) := by fun_prop
  have hφ_r_smooth : ContDiff ℝ ∞ φ_r :=
    (radialCutoff_contDiff ha_pos hL_pos).comp h_inner_smooth
  have h_constν : ContDiff ℝ ∞ (fun _ : E n => ν) := contDiff_const
  have hΦ_smooth : ContDiff ℝ ∞ Φ := hφ_r_smooth.smul h_constν
  have hΦ_support : Function.support Φ ⊆ ball x r := by
    intro y hy
    have h1 : Φ y ≠ 0 := by simpa [Function.mem_support] using hy
    have h2 : φ_r y ≠ 0 := by
      by_contra h3
      have h4 : Φ y = 0 := by
        simp [hΦ_def, h3]
      contradiction
    have h3 : (1 / r) • (y - x) ∈ Function.support φ := by
      simpa [hφ_r_def, Function.mem_support] using h2
    have h4 : (1 / r) • (y - x) ∈ ball (0 : E n) 1 := h_φ_support h3
    have h5 : ‖(1 / r) • (y - x)‖ < 1 := by simpa [ball, dist_zero_right] using h4
    have h6 : ‖y - x‖ < r := by
      have h7 : ‖(1 / r) • (y - x)‖ = (1 / r) * ‖y - x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
        <;> ring
      rw [h7] at h5
      have h8 : 0 < r := hr_pos
      calc
        ‖y - x‖ = r * ((1 / r) * ‖y - x‖) := by field_simp [h8.ne'] <;> ring
        _ < r * 1 := by gcongr
        _ = r := by ring
    simpa [ball, dist_eq_norm] using h6
  have hΦ_bound : ∀ y, ‖Φ y‖ ≤ 1 := by
    intro y
    have h1 : 0 ≤ φ_r y := by
      set t : ℝ := (‖(1 / r) • (y - x)‖ - a) / L with ht_def
      have h_eq : φ_r y = smoothStep t := by
        rw [hφ_r_def, hφ_def]
        simp [radialCutoff, ht_def, dist_zero_right] <;> rfl
      rw [h_eq]
      have h_s1 : smoothStep 1 = 0 := smoothStep_zero_of_one_le (by norm_num)
      by_cases h3 : t ≤ 1
      · have h4 : smoothStep t ≥ smoothStep 1 := smoothStep_antitone h3
        rw [h_s1] at h4
        exact h4
      · have h5 : 1 < t := by linarith
        have h6 : smoothStep t = 0 := smoothStep_zero_of_one_le (by linarith)
        rw [h6] <;> norm_num
    have h2 : φ_r y ≤ 1 := by
      set t : ℝ := (‖(1 / r) • (y - x)‖ - a) / L with ht_def
      have h_eq : φ_r y = smoothStep t := by
        rw [hφ_r_def, hφ_def]
        simp [radialCutoff, ht_def, dist_zero_right] <;> rfl
      rw [h_eq]
      have h_s0 : smoothStep 0 = 1 := smoothStep_one_of_nonpos (by norm_num)
      by_cases h4 : 0 ≤ t
      · have h5 : smoothStep t ≤ smoothStep 0 := smoothStep_antitone h4
        rw [h_s0] at h5
        exact h5
      · have h6 : t < 0 := by linarith
        have h7 : smoothStep t = 1 := smoothStep_one_of_nonpos (by linarith)
        rw [h7] <;> norm_num
    have h_norm_smul : ‖Φ y‖ = |φ_r y| * ‖ν‖ := by
      rw [hΦ_def]
      have h : ‖φ_r y • ν‖ = ‖φ_r y‖ * ‖ν‖ := norm_smul _ _
      rw [h]
      have h2 : ‖φ_r y‖ = |φ_r y| := Real.norm_eq_abs (φ_r y)
      rw [h2]
    calc
      ‖Φ y‖ = |φ_r y| * ‖ν‖ := h_norm_smul
      _ = φ_r y * ‖ν‖ := by rw [abs_of_nonneg h1]
      _ = φ_r y := by rw [hν_unit] <;> ring
      _ ≤ 1 := h2

  let Φ_test : TestVectorField :=
    { toFun := Φ
      smooth := hΦ_smooth
      compact := by
        have h : Function.support Φ ⊆ ball x r := hΦ_support
        have h' : tsupport Φ ⊆ closure (ball x r) := by
          exact closure_mono h
        have h'' : closure (ball x r) = closedBall x r := closure_ball x hr_pos.ne'
        rw [h''] at h'
        exact IsCompact.of_isClosed_subset (isCompact_closedBall x r) isClosed_closure h'
      bound := hΦ_bound }
  let Φ' : {Φ : TestVectorField // Function.support Φ.toFun ⊆ ball x r} :=
    ⟨Φ_test, hΦ_support⟩

  have h_div : divergence Φ_test.toFun = fun y => fderiv ℝ φ_r y ν :=
    divergence_smul_const hφ_r_smooth

  have h_scaling : ∫ y in U, divergence Φ_test.toFun y =
      r ^ (n - 1) * ∫ z in blowUp U x r, f z := by
    rw [h_div]
    exact scaling_derivative_integral hU_meas hn hr_pos (radialCutoff_contDiff ha_pos hL_pos)

  have h_integral_pos : 0 ≤ ∫ y in U, divergence Φ_test.toFun y := by
    rw [h_scaling]
    have h1 : I_H / 2 ≤ ∫ z in blowUp U x r, f z := h_ineq r hr_pos hr_lt
    have h1' : 0 ≤ ∫ z in blowUp U x r, f z := by linarith [hI_H_pos]
    have h2 : 0 ≤ r ^ (n - 1) := by positivity
    exact mul_nonneg h2 h1'

  have h_main : (I_H / 2) * r ^ (n - 1) ≤ ∫ y in U, divergence Φ_test.toFun y := by
    rw [h_scaling]
    have h1 : I_H / 2 ≤ ∫ z in blowUp U x r, f z := h_ineq r hr_pos hr_lt
    have h2 : 0 ≤ r ^ (n - 1) := by positivity
    nlinarith

  have h_perim : ENNReal.ofReal ((I_H / 2) * r ^ (n - 1)) ≤
      ENNReal.ofReal |∫ y in U, divergence Φ_test.toFun y| := by
    rw [abs_of_nonneg h_integral_pos]
    exact ENNReal.ofReal_le_ofReal h_main

  exact le_trans h_perim (le_iSup (fun (Ψ : {Φ : TestVectorField // Function.support Φ.toFun ⊆ ball x r}) =>
    ENNReal.ofReal |∫ y in U, divergence Ψ.val.toFun y|) Φ')

end Geometry.StructureTheorem
