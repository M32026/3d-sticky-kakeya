import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-!
# Cutoff Functions

Smooth step function and radial cutoff for perimeter estimates.

Provides `smoothStep` (1 for t≤0, 0 for t≥1) and `radialCutoff`
(a smooth radial approximation to the indicator of a ball), with
gradient bounds and the key integral identity `∫ |smoothStep'| = 1`.

Extracted from `IntersectionBall.lean` to avoid its compilation errors.
-/


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.Perimeter

variable {n : ℕ}

-- ============================================================================
-- Smooth step function
-- ============================================================================

/-- Smooth decreasing step: f(t)=1 for t≤0, f(t)=0 for t≥1. -/
noncomputable def smoothStep (t : ℝ) : ℝ :=
  1 - Real.smoothTransition t

lemma smoothStep_one_of_nonpos {t : ℝ} (h : t ≤ 0) : smoothStep t = 1 := by
  simp [smoothStep, Real.smoothTransition.zero_of_nonpos h]

lemma smoothStep_zero_of_one_le {t : ℝ} (h : 1 ≤ t) : smoothStep t = 0 := by
  simp [smoothStep, Real.smoothTransition.one_of_one_le h]

lemma smoothStep_contDiff : ContDiff ℝ ∞ smoothStep := by
  have h : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))
  have h2 : ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℝ)) := contDiff_const
  exact h2.sub h

lemma smoothStep_antitone : Antitone smoothStep := by
  intro x y hxy
  have h : Real.smoothTransition x ≤ Real.smoothTransition y :=
    Real.smoothTransition.monotone hxy
  dsimp only [smoothStep]
  linarith

/-- Range of `smoothStep`: `0 ≤ smoothStep t ≤ 1`. -/
lemma smoothStep_range {t : ℝ} : 0 ≤ smoothStep t ∧ smoothStep t ≤ 1 := by
  have h1 : 0 ≤ Real.smoothTransition t := Real.smoothTransition.nonneg t
  have h2 : Real.smoothTransition t ≤ 1 := Real.smoothTransition.le_one t
  constructor <;> simp [smoothStep] <;> linarith

/-- Bound on |deriv smoothStep|. -/
noncomputable def smoothStepDerivBound : ℝ :=
  sSup (Set.image (fun t : ℝ => |deriv smoothStep t|) (Set.Icc (0 : ℝ) 1))

lemma smoothStepDerivBound_nonneg : 0 ≤ smoothStepDerivBound := by
  apply Real.sSup_nonneg
  intro x hx
  rcases hx with ⟨t, _, rfl⟩
  exact abs_nonneg _

lemma smoothStep_deriv_bound {t : ℝ} : |deriv smoothStep t| ≤ smoothStepDerivBound := by
  by_cases h : t ∈ Set.Icc (0 : ℝ) 1
  · have h1 : |deriv smoothStep t| ∈ Set.image (fun t => |deriv smoothStep t|) (Set.Icc (0 : ℝ) 1) :=
      ⟨t, h, rfl⟩
    have h2 : BddAbove (Set.image (fun t : ℝ => |deriv smoothStep t|) (Set.Icc (0 : ℝ) 1)) := by
      apply IsCompact.bddAbove_image isCompact_Icc
      have h_cont : Continuous (deriv smoothStep) :=
        ContDiff.continuous_deriv smoothStep_contDiff (by norm_num)
      exact h_cont.norm.continuousOn
    exact le_csSup h2 h1
  · have h3 : deriv smoothStep t = 0 := by
      by_cases h4 : t < 0
      · have h5 : ∀ᶠ (x : ℝ) in nhds t, smoothStep x = 1 := by
          filter_upwards [Iio_mem_nhds h4] with x hx
          exact smoothStep_one_of_nonpos hx.le
        have h_const : HasDerivAt (fun (_ : ℝ) => (1 : ℝ)) 0 t := hasDerivAt_const t (1 : ℝ)
        have h6 : HasDerivAt smoothStep 0 t := h_const.congr_of_eventuallyEq h5
        exact h6.deriv
      · have h5 : 1 < t := by
          have h51 : 0 ≤ t := by linarith
          have h52 : ¬(t ≤ 1) := by
            intro h53
            exact h ⟨h51, h53⟩
          linarith
        have h6 : ∀ᶠ (x : ℝ) in nhds t, smoothStep x = 0 := by
          filter_upwards [Ioi_mem_nhds h5] with x hx
          exact smoothStep_zero_of_one_le hx.le
        have h_const : HasDerivAt (fun (_ : ℝ) => (0 : ℝ)) 0 t := hasDerivAt_const t (0 : ℝ)
        have h7 : HasDerivAt smoothStep 0 t := h_const.congr_of_eventuallyEq h6
        exact h7.deriv
    rw [h3]
    simp [smoothStepDerivBound_nonneg]

/-- Integral of |smoothStep'| over [0,1] equals 1. -/
lemma smoothStep_deriv_abs_integral : ∫ t in (0 : ℝ)..1, |deriv smoothStep t| = 1 := by
  have h_diff : Differentiable ℝ smoothStep := smoothStep_contDiff.differentiable (by norm_num)
  have h1 : ∀ t, deriv smoothStep t ≤ 0 := fun t => smoothStep_antitone.deriv_nonpos
  have h_cont_deriv : Continuous (deriv smoothStep) :=
    smoothStep_contDiff.continuous_deriv (by norm_num)
  have h2 : IntervalIntegrable (deriv smoothStep) volume 0 1 :=
    h_cont_deriv.intervalIntegrable 0 1
  have h3 : ∫ t in (0 : ℝ)..1, deriv smoothStep t = smoothStep 1 - smoothStep 0 := by
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt smoothStep (deriv smoothStep x) x :=
      fun x _ => h_diff.differentiableAt.hasDerivAt
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv h2
  have h4 : ∀ t, |deriv smoothStep t| = -deriv smoothStep t := by
    intro t; rw [abs_of_nonpos (h1 t)] <;> ring
  have h5 : ∫ t in (0 : ℝ)..1, |deriv smoothStep t| = -∫ t in (0 : ℝ)..1, deriv smoothStep t := by
    rw [intervalIntegral.integral_congr (fun t _ => h4 t)]
    rw [intervalIntegral.integral_neg]
  rw [h5, h3]
  simp [smoothStep_one_of_nonpos, smoothStep_zero_of_one_le] <;> norm_num

/-- `deriv smoothStep t = 0` outside [0,1]. -/
lemma smoothStep_deriv_zero_outside {t : ℝ} (h : t ∉ Set.Icc (0 : ℝ) 1) : deriv smoothStep t = 0 := by
  by_cases h4 : t < 0
  · have h5 : ∀ᶠ (x : ℝ) in nhds t, smoothStep x = 1 := by
      filter_upwards [Iio_mem_nhds h4] with x hx
      exact smoothStep_one_of_nonpos hx.le
    have h_const : HasDerivAt (fun (_ : ℝ) => (1 : ℝ)) 0 t := hasDerivAt_const t (1 : ℝ)
    have h6 : HasDerivAt smoothStep 0 t := h_const.congr_of_eventuallyEq h5
    exact h6.deriv
  · have h5 : 1 < t := by
      have h51 : 0 ≤ t := by linarith
      have h52 : ¬(t ≤ 1) := by
        intro h53
        exact h ⟨h51, h53⟩
      linarith
    have h6 : ∀ᶠ (x : ℝ) in nhds t, smoothStep x = 0 := by
      filter_upwards [Ioi_mem_nhds h5] with x hx
      exact smoothStep_zero_of_one_le hx.le
    have h_const : HasDerivAt (fun (_ : ℝ) => (0 : ℝ)) 0 t := hasDerivAt_const t (0 : ℝ)
    have h7 : HasDerivAt smoothStep 0 t := h_const.congr_of_eventuallyEq h6
    exact h7.deriv

-- ============================================================================
-- Radial cutoff
-- ============================================================================

/-- Radial cutoff η_L(x) = smoothStep((dist x x₀ - r) / L). -/
noncomputable def radialCutoff (x₀ : E n) (r L : ℝ) (x : E n) : ℝ :=
  smoothStep ((dist x x₀ - r) / L)

lemma radialCutoff_one_of_mem_closedBall {x₀ : E n} {r L : ℝ} (hr : 0 < r) (hL : 0 < L)
    {x : E n} (h : x ∈ closedBall x₀ r) : radialCutoff x₀ r L x = 1 := by
  have h1 : dist x x₀ ≤ r := by simpa [closedBall] using h
  have h2 : (dist x x₀ - r) / L ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg <;> linarith
  exact smoothStep_one_of_nonpos h2

lemma radialCutoff_zero_of_not_mem_ball {x₀ : E n} {r L : ℝ} (hr : 0 < r) (hL : 0 < L)
    {x : E n} (h : x ∉ ball x₀ (r + L)) : radialCutoff x₀ r L x = 0 := by
  have h1 : r + L ≤ dist x x₀ := by simpa [ball, not_lt] using h
  have h2 : 1 ≤ (dist x x₀ - r) / L := by
    have h3 : 0 < L := hL
    have h4 : L ≤ dist x x₀ - r := by linarith
    calc
      1 = L / L := by field_simp [h3.ne'] <;> ring
      _ ≤ (dist x x₀ - r) / L := by gcongr
  exact smoothStep_zero_of_one_le h2

lemma radialCutoff_contDiff {x₀ : E n} {r L : ℝ} (hr : 0 < r) (hL : 0 < L) :
    ContDiff ℝ ∞ (radialCutoff x₀ r L) := by
  have h_main : ∀ (x : E n), ContDiffAt ℝ ∞ (radialCutoff x₀ r L) x := by
    intro x
    by_cases hx : x = x₀
    · rw [hx]
      have h1 : ∀ᶠ (y : E n) in nhds x₀, radialCutoff x₀ r L y = 1 := by
        filter_upwards [ball_mem_nhds x₀ hr] with y hy
        have h2 : y ∈ closedBall x₀ r := ball_subset_closedBall hy
        exact radialCutoff_one_of_mem_closedBall hr hL h2
      have h_const : ContDiffAt ℝ ∞ (fun (_ : E n) => (1 : ℝ)) x₀ :=
        contDiffAt_const
      exact h_const.congr_of_eventuallyEq h1
    · have h_ne : x ≠ x₀ := hx
      have h1 : ContDiffAt ℝ ∞ (fun y : E n => dist y x₀) x := by
        have h2 : ContDiffAt ℝ ∞ (fun z : E n => ‖z‖) (x - x₀) :=
          contDiffAt_norm (𝕜 := ℝ) (show (x - x₀) ≠ 0 from sub_ne_zero.mpr h_ne)
        have h3 : ContDiffAt ℝ ∞ (fun y : E n => y - x₀) x :=
          contDiffAt_id.sub contDiffAt_const
        exact h2.comp x h3
      have h2 : ContDiffAt ℝ ∞ (fun y : E n => (dist y x₀ - r) / L) x :=
        h1.sub contDiffAt_const |>.div contDiffAt_const hL.ne'
      let z0 : ℝ := (dist x x₀ - r) / L
      have h_g : ContDiffAt ℝ ∞ smoothStep z0 :=
        smoothStep_contDiff.contDiffAt
      have h_comp : ContDiffAt ℝ ∞ (smoothStep ∘ (fun y : E n => (dist y x₀ - r) / L)) x :=
        h_g.comp x h2
      have h_eq : (smoothStep ∘ (fun y : E n => (dist y x₀ - r) / L)) = radialCutoff x₀ r L := by
        funext y; simp [radialCutoff] <;> rfl
      rw [h_eq] at h_comp
      exact h_comp
  exact contDiff_iff_contDiffAt.mpr h_main

lemma radialCutoff_fderiv_at_center {x₀ : E n} {r L : ℝ} (hr : 0 < r) (hL : 0 < L) :
    fderiv ℝ (radialCutoff x₀ r L) x₀ = 0 := by
  have h1 : ∀ᶠ (x : E n) in nhds x₀, radialCutoff x₀ r L x = 1 := by
    filter_upwards [ball_mem_nhds x₀ hr] with x hx
    have h2 : x ∈ closedBall x₀ r := ball_subset_closedBall hx
    exact radialCutoff_one_of_mem_closedBall hr hL h2
  let c : E n → ℝ := fun _ => (1 : ℝ)
  have h_const : HasFDerivAt c (0 : E n →L[ℝ] ℝ) x₀ := by
    have h : HasFDerivAt c (fderiv ℝ c x₀) x₀ := (differentiableAt_const (1 : ℝ)).hasFDerivAt
    have h_fderiv : fderiv ℝ c x₀ = 0 := by simp [c]
    rw [h_fderiv] at h
    exact h
  have h3 : HasFDerivAt (radialCutoff x₀ r L) (0 : E n →L[ℝ] ℝ) x₀ :=
    h_const.congr_of_eventuallyEq h1
  exact h3.fderiv

/-- Helper: distance function is differentiable away from center and fderiv norm ≤ 1. -/
lemma dist_fderiv_norm_le_one {x₀ x : E n} (hx : x ≠ x₀) :
    ‖fderiv ℝ (fun y : E n => dist y x₀) x‖ ≤ 1 := by
  haveI : Nontrivial (E n) := ⟨x, x₀, hx⟩
  have h_ne : x - x₀ ≠ 0 := by simpa [sub_ne_zero] using hx
  have h_cda : ContDiffAt ℝ 1 (fun z : E n => ‖z‖) (x - x₀) :=
    contDiffAt_norm (𝕜 := ℝ) h_ne
  have h_diff_norm : DifferentiableAt ℝ (fun z : E n => ‖z‖) (x - x₀) :=
    h_cda.differentiableAt (by norm_num)
  have h_eq : fderiv ℝ (fun y : E n => dist y x₀) x =
      fderiv ℝ (fun z : E n => ‖z‖) (x - x₀) := by
    have h_id : HasFDerivAt (fun y : E n => y) (ContinuousLinearMap.id ℝ (E n)) x :=
      hasFDerivAt_id (x := x)
    have h1 : HasFDerivAt (fun y : E n => y - x₀) (ContinuousLinearMap.id ℝ (E n)) x :=
      h_id.sub_const x₀
    have h2 : HasFDerivAt (fun z : E n => ‖z‖) (fderiv ℝ (fun z : E n => ‖z‖) (x - x₀)) (x - x₀) :=
      h_diff_norm.hasFDerivAt
    have h3 : (fun y : E n => dist y x₀) = (fun z : E n => ‖z‖) ∘ (fun y : E n => y - x₀) := by
      funext y; simp [dist_eq_norm]
    rw [h3]
    exact (h2.comp x h1).fderiv
  rw [h_eq]
  have h_norm : ‖fderiv ℝ (fun z : E n => ‖z‖) (x - x₀)‖ = 1 :=
    norm_fderiv_norm h_diff_norm
  rw [h_norm] <;> norm_num

lemma radialCutoff_fderiv_bound {x₀ : E n} {r L : ℝ} (hr : 0 < r) (hL : 0 < L)
    {x : E n} (hx : x ≠ x₀) :
    ‖fderiv ℝ (radialCutoff x₀ r L) x‖ ≤ smoothStepDerivBound / L := by
  set d : E n → ℝ := fun y => dist y x₀ with hd
  set h : E n → ℝ := fun y => (d y - r) / L with hh
  set g : ℝ → ℝ := smoothStep with hg
  have h_diff_d : HasFDerivAt d (fderiv ℝ d x) x := by
    have h_ne : x ≠ x₀ := hx
    have h_diff : DifferentiableAt ℝ d x := by
      exact DifferentiableAt.dist (𝕜 := ℝ) differentiableAt_id (differentiableAt_const x₀) h_ne
    exact h_diff.hasFDerivAt
  have h_diff_h : HasFDerivAt h ((1 / L) • fderiv ℝ d x) x := by
    have h1 : HasFDerivAt (fun y => d y - r) (fderiv ℝ d x) x :=
      h_diff_d.sub_const r
    have h2 : HasFDerivAt (fun y => (1 / L) * (d y - r)) ((1 / L) • fderiv ℝ d x) x :=
      h1.const_smul (1 / L)
    have h3 : (fun y : E n => (1 / L) * (d y - r)) = h := by
      funext y; simp [hh]; ring
    rw [h3] at h2; exact h2
  have h_diff_g : HasDerivAt g (deriv g (h x)) (h x) := by
    have h_diff : Differentiable ℝ g := smoothStep_contDiff.differentiable (by simp)
    exact h_diff.differentiableAt.hasDerivAt
  have h_main : HasFDerivAt (g ∘ h) (deriv g (h x) • ((1 / L) • fderiv ℝ d x)) x :=
    h_diff_g.comp_hasFDerivAt x h_diff_h
  have h_η : (g ∘ h) = radialCutoff x₀ r L := by
    funext y; simp [radialCutoff, hh, hg] <;> ring
  have h_eq : fderiv ℝ (radialCutoff x₀ r L) x =
      deriv g (h x) • ((1 / L) • fderiv ℝ d x) := by
    rw [← h_η]; exact h_main.fderiv
  rw [h_eq]
  have h_norm : ‖deriv g (h x) • ((1 / L) • fderiv ℝ d x)‖ =
      |deriv g (h x)| * (1 / L) * ‖fderiv ℝ d x‖ := by
    have h1 : ‖deriv g (h x) • ((1 / L) • fderiv ℝ d x)‖ =
        |deriv g (h x)| * ‖(1 / L) • fderiv ℝ d x‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    rw [h1]
    have h2 : ‖(1 / L) • fderiv ℝ d x‖ = (1 / L) * ‖fderiv ℝ d x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 1 / L by positivity)]
    rw [h2] <;> ring
  rw [h_norm]
  have h_grad_dist : ‖fderiv ℝ d x‖ ≤ 1 := dist_fderiv_norm_le_one hx
  have h_deriv_bound : |deriv g (h x)| ≤ smoothStepDerivBound := smoothStep_deriv_bound
  have hL_pos : 0 < L := hL
  calc
    |deriv g (h x)| * (1 / L) * ‖fderiv ℝ d x‖
      ≤ |deriv g (h x)| * (1 / L) * 1 := by gcongr
    _ = |deriv g (h x)| / L := by ring
    _ ≤ smoothStepDerivBound / L := by gcongr

/-- Tight bound: ‖∇η_L(x)‖ ≤ |smoothStep'((d(x)-r)/L)| / L. -/
lemma radialCutoff_fderiv_tight_bound {x₀ : E n} {r L : ℝ} (hr : 0 < r) (hL : 0 < L)
    {x : E n} (hx : x ≠ x₀) :
    ‖fderiv ℝ (radialCutoff x₀ r L) x‖ ≤ |deriv smoothStep ((dist x x₀ - r) / L)| / L := by
  set d : E n → ℝ := fun y => dist y x₀ with hd
  set h : E n → ℝ := fun y => (d y - r) / L with hh
  set g : ℝ → ℝ := smoothStep with hg
  have h_diff_d : HasFDerivAt d (fderiv ℝ d x) x := by
    have h_ne : x ≠ x₀ := hx
    have h_diff : DifferentiableAt ℝ d x := by
      exact DifferentiableAt.dist (𝕜 := ℝ) differentiableAt_id (differentiableAt_const x₀) h_ne
    exact h_diff.hasFDerivAt
  have h_diff_h : HasFDerivAt h ((1 / L) • fderiv ℝ d x) x := by
    have h1 : HasFDerivAt (fun y => d y - r) (fderiv ℝ d x) x :=
      h_diff_d.sub_const r
    have h2 : HasFDerivAt (fun y => (1 / L) * (d y - r)) ((1 / L) • fderiv ℝ d x) x :=
      h1.const_smul (1 / L)
    have h3 : (fun y : E n => (1 / L) * (d y - r)) = h := by
      funext y; simp [hh]; ring
    rw [h3] at h2; exact h2
  have h_diff_g : HasDerivAt g (deriv g (h x)) (h x) := by
    have h_diff : Differentiable ℝ g := smoothStep_contDiff.differentiable (by simp)
    exact h_diff.differentiableAt.hasDerivAt
  have h_main : HasFDerivAt (g ∘ h) (deriv g (h x) • ((1 / L) • fderiv ℝ d x)) x :=
    h_diff_g.comp_hasFDerivAt x h_diff_h
  have h_η : (g ∘ h) = radialCutoff x₀ r L := by
    funext y; simp [radialCutoff, hh, hg] <;> ring
  have h_eq : fderiv ℝ (radialCutoff x₀ r L) x =
      deriv g (h x) • ((1 / L) • fderiv ℝ d x) := by
    rw [← h_η]; exact h_main.fderiv
  rw [h_eq]
  have h_norm : ‖deriv g (h x) • ((1 / L) • fderiv ℝ d x)‖ =
      |deriv g (h x)| * (1 / L) * ‖fderiv ℝ d x‖ := by
    have h1 : ‖deriv g (h x) • ((1 / L) • fderiv ℝ d x)‖ =
        |deriv g (h x)| * ‖(1 / L) • fderiv ℝ d x‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    rw [h1]
    have h2 : ‖(1 / L) • fderiv ℝ d x‖ = (1 / L) * ‖fderiv ℝ d x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 1 / L by positivity)]
    rw [h2] <;> ring
  rw [h_norm]
  have h_grad_dist : ‖fderiv ℝ d x‖ ≤ 1 := dist_fderiv_norm_le_one hx
  have hL_pos : 0 < L := hL
  have h : |deriv g (h x)| * (1 / L) * ‖fderiv ℝ d x‖ ≤ |deriv g (h x)| / L := by
    calc
      |deriv g (h x)| * (1 / L) * ‖fderiv ℝ d x‖
        ≤ |deriv g (h x)| * (1 / L) * 1 := by gcongr
      _ = |deriv g (h x)| / L := by ring
  exact h


-- ============================================================================
-- Analysis helper: weighted average convergence for continuous functions
-- ============================================================================

/-- Weighted approximate identity converges at continuity points.

If `h` is continuous and `w ≥ 0` with `∫_0^1 w = 1`, then
`∫_r^{r+L} w((t-r)/L)/L * h(t) dt → h(r)` as `L → 0+`. -/
lemma weighted_average_convergence_continuous {h : ℝ → ℝ} (h_cont : Continuous h)
    {w : ℝ → ℝ} (hw_cont : Continuous w) (hw_nonneg : ∀ t, 0 ≤ w t)
    (hw_int : ∫ t in (0 : ℝ)..1, w t = 1)
    (C_w : ℝ) (hC_w : ∀ t, w t ≤ C_w)
    (r : ℝ) :
    Tendsto (fun L : ℝ => ∫ t in r..(r + L), (w ((t - r) / L) / L) * h t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (h r)) := by
  -- Normalization: ∫_r^{r+L} w((t-r)/L)/L dt = 1
  have h1 : ∀ (L : ℝ), 0 < L → ∫ t in r..(r + L), (w ((t - r) / L) / L) = 1 := by
    intro L hL
    have hL_ne : L ≠ 0 := hL.ne'
    set c : ℝ := 1 / L with hc_def
    have hc_ne : c ≠ 0 := by positivity
    have h_trans : ∫ t in r..(r + L), w ((t - r) / L) = ∫ s in (0 : ℝ)..L, w (s / L) := by
      have h := intervalIntegral.integral_comp_sub_right (a := r) (b := r + L)
        (fun x : ℝ => w (x / L)) r
      simpa using h
    have h_scale : c * ∫ s in (0 : ℝ)..L, w (c * s) = ∫ u in (c * 0)..(c * L), w u :=
      intervalIntegral.mul_integral_comp_mul_left c
    have h_c0 : c * 0 = 0 := by ring
    have h_cL : c * L = 1 := by
      simp [hc_def] <;> field_simp [hL_ne] <;> ring
    have h_eq : ∫ s in (0 : ℝ)..L, w (s / L) = ∫ s in (0 : ℝ)..L, w (c * s) := by
      apply intervalIntegral.integral_congr; intro s _; simp [hc_def] <;> ring_nf
    have h2 : c * ∫ s in (0 : ℝ)..L, w (s / L) = 1 := by
      rw [h_eq, h_scale, h_c0, h_cL, hw_int]
    have h_cinv : c⁻¹ = L := by
      simp [hc_def] <;> field_simp [hL_ne] <;> ring
    have h3 : ∫ s in (0 : ℝ)..L, w (s / L) = L := by
      calc
        ∫ s in (0 : ℝ)..L, w (s / L)
          = c⁻¹ * (c * ∫ s in (0 : ℝ)..L, w (s / L)) := by field_simp [hc_ne] <;> ring
        _ = c⁻¹ * 1 := by rw [h2]
        _ = L := by rw [h_cinv] <;> ring
    have h4 : ∫ t in r..(r + L), w ((t - r) / L) = L := by
      rw [h_trans, h3]
    have h51 : (fun t : ℝ => w ((t - r) / L) / L) = fun t : ℝ => (1 / L) * w ((t - r) / L) := by
      funext t; ring
    rw [h51]
    rw [intervalIntegral.integral_const_mul (1 / L) (fun t : ℝ => w ((t - r) / L)), h4]
    field_simp [hL_ne] <;> ring

  -- Main estimate: |A(L) - h(r)| ≤ (C_w/L) * ∫ |h(t)-h(r)| dt
  have h_main : ∀ (L : ℝ), 0 < L →
      |(∫ t in r..(r + L), (w ((t - r) / L) / L) * h t) - h r| ≤
      (C_w / L) * ∫ t in r..(r + L), |h t - h r| := by
    intro L hL
    let f := fun t : ℝ => w ((t - r) / L) / L
    have hf_cont : Continuous f := by
      dsimp only [f]
      have h1 : Continuous (fun t : ℝ => (t - r) / L) := by fun_prop
      have h2 : Continuous (fun t : ℝ => w ((t - r) / L)) := hw_cont.comp h1
      have h3 : (fun t : ℝ => w ((t - r) / L) / L) = fun t : ℝ => (1 / L) * w ((t - r) / L) := by
        funext t; ring
      rw [h3]
      exact h2.const_mul (1 / L)
    have hf_int : ∫ t in r..(r + L), f t = 1 := h1 L hL
    have hf_nonneg : ∀ t, 0 ≤ f t := by
      intro t; dsimp only [f]; apply div_nonneg <;> [exact hw_nonneg _; linarith]
    have hfi1 : IntervalIntegrable (fun t => f t * h t) volume r (r + L) :=
      (hf_cont.mul h_cont).intervalIntegrable r (r + L)
    have hfi2 : IntervalIntegrable (fun t => f t * h r) volume r (r + L) :=
      (hf_cont.mul continuous_const).intervalIntegrable r (r + L)
    have h4 : ∫ t in r..(r + L), f t * h r = h r := by
      have h51 : (fun t : ℝ => f t * h r) = fun t : ℝ => h r * f t := by funext t; ring
      rw [h51, intervalIntegral.integral_const_mul (h r) f, hf_int] <;> ring
    have h3 : (∫ t in r..(r + L), f t * h t) - h r =
        ∫ t in r..(r + L), f t * (h t - h r) := by
      calc
        (∫ t in r..(r + L), f t * h t) - h r
          = (∫ t in r..(r + L), f t * h t) - ∫ t in r..(r + L), f t * h r := by rw [h4]
        _ = ∫ t in r..(r + L), (f t * h t - f t * h r) := by
          rw [← intervalIntegral.integral_sub hfi1 hfi2]
        _ = ∫ t in r..(r + L), f t * (h t - h r) := by
          apply intervalIntegral.integral_congr; intro t _; ring
    rw [h3]
    have h_abs : |∫ t in r..(r + L), f t * (h t - h r)| ≤
        ∫ t in r..(r + L), |f t * (h t - h r)| :=
      intervalIntegral.abs_integral_le_integral_abs (by linarith)
    have h6 : ∫ t in r..(r + L), |f t * (h t - h r)| =
        ∫ t in r..(r + L), f t * |h t - h r| := by
      apply intervalIntegral.integral_congr; intro t _
      have h7 : 0 ≤ f t := hf_nonneg t
      calc
        |f t * (h t - h r)|
          = |f t| * |h t - h r| := by rw [abs_mul]
        _ = f t * |h t - h r| := by rw [abs_of_nonneg h7]
    have h9 : ∀ t, f t ≤ C_w / L := by
      intro t
      dsimp only [f]
      have h10 : w ((t - r) / L) ≤ C_w := hC_w ((t - r) / L)
      gcongr
    have h_abs_cont : Continuous (fun t : ℝ => |h t - h r|) := by fun_prop
    have h10 : ∫ t in r..(r + L), f t * |h t - h r| ≤
        ∫ t in r..(r + L), (C_w / L) * |h t - h r| := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((hf_cont.mul h_abs_cont).intervalIntegrable r (r + L))
        (((continuous_const.mul h_abs_cont)).intervalIntegrable r (r + L))
      intro t _
      have h11 : 0 ≤ |h t - h r| := abs_nonneg _
      exact mul_le_mul_of_nonneg_right (h9 t) h11
    calc
      |∫ t in r..(r + L), f t * (h t - h r)|
        ≤ ∫ t in r..(r + L), |f t * (h t - h r)| := h_abs
      _ = ∫ t in r..(r + L), f t * |h t - h r| := h6
      _ ≤ ∫ t in r..(r + L), (C_w / L) * |h t - h r| := h10
      _ = (C_w / L) * ∫ t in r..(r + L), |h t - h r| := by
        rw [intervalIntegral.integral_const_mul (C_w / L) (fun t => |h t - h r|)] <;> ring

  -- C_w must be non-negative (since w ≥ 0 and ∫ w = 1)
  have hCw_nonneg : 0 ≤ C_w := by
    by_contra h
    have h' : C_w < 0 := by linarith
    have h_le : C_w ≤ 0 := by linarith
    have h0 : ∀ t, w t ≤ 0 := fun t => (hC_w t).trans h_le
    have h1' : ∀ t, w t = 0 := fun t => le_antisymm (h0 t) (hw_nonneg t)
    have h2 : w = fun _ => 0 := funext h1'
    rw [h2] at hw_int
    simp at hw_int <;> linarith

  set K : ℝ := max C_w 1 with hK_def
  have hK_pos : 0 < K := by positivity
  have hK_ge : C_w ≤ K := by simp [hK_def] <;> linarith

  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set E : ℝ := ε / (2 * K) with hE_def
  have hE_pos : 0 < E := by positivity
  have h_cont_at : ContinuousAt h r := h_cont.continuousAt
  have hδ : ∃ δ > 0, ∀ y, dist y r < δ → dist (h y) (h r) < E :=
    Metric.continuousAt_iff.mp h_cont_at E hE_pos
  rcases hδ with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, fun L hL_in hL_dist => ?_⟩
  have hL_pos : 0 < L := hL_in
  have hL_lt : L < δ := by
    have h : dist L 0 < δ := hL_dist
    simpa [dist_eq_norm, abs_of_pos hL_pos] using h
  have h_abs_cont : Continuous (fun t : ℝ => |h t - h r|) := by fun_prop
  have h11 : ∀ t ∈ Set.Icc r (r + L), |h t - h r| < E := by
    intro t ht
    have h12 : r ≤ t := ht.1
    have h13 : t ≤ r + L := ht.2
    have h14 : |t - r| ≤ L := by
      have h15 : 0 ≤ t - r := by linarith
      have h16 : t - r ≤ L := by linarith
      rw [abs_of_nonneg h15] <;> linarith
    have h17 : |t - r| < δ := by linarith
    have h18 : dist t r < δ := by simpa [dist_eq_norm] using h17
    have h19 := hδ t h18
    simpa [dist_eq_norm] using h19
  have h14 : ∫ t in r..(r + L), |h t - h r| ≤ L * E := by
    have h15 : ∀ t ∈ Set.Icc r (r + L), |h t - h r| ≤ E := by
      intro t ht; exact (h11 t ht).le
    have h16 := intervalIntegral.integral_mono_on (by linarith)
      (h_abs_cont.intervalIntegrable r (r + L))
      (by exact continuous_const.intervalIntegrable (μ := volume) r (r + L)) h15
    simpa [intervalIntegral.integral_const] using h16
  have h_est : (C_w / L) * ∫ t in r..(r + L), |h t - h r| < ε := by
    calc
      (C_w / L) * ∫ t in r..(r + L), |h t - h r|
        ≤ (C_w / L) * (L * E) := by gcongr
      _ = C_w * E := by field_simp [hL_pos.ne'] <;> ring
      _ ≤ K * E := by gcongr
      _ = ε / 2 := by
        simp [hE_def, hK_pos.ne'] <;> field_simp <;> ring
      _ < ε := by linarith
  have h18 := h_main L hL_pos
  have h19 : |(∫ t in r..(r + L), (w ((t - r) / L) / L) * h t) - h r| < ε :=
    h18.trans_lt h_est
  simpa [dist_eq_norm] using h19

end Geometry.Perimeter
