import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic


/-!
# Cutoff function and constants for relative isoperimetric inequality

Provides a smooth cutoff function equal to 1 on `ball x₀ r`, 0 outside
`ball x₀ (2r)`, with bounded gradient. Also provides the dimension-dependent
constant `relIsoConst` and sphere measure zero lemma.
-/

open MeasureTheory Metric Set ENNReal
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ}

/-- Standard bump function with rIn=1, rOut=2. -/
def standardBump (n : ℕ) : ContDiffBump (0 : E n) := ⟨1, 2, by norm_num, by norm_num⟩

/-- Least upper bound on the derivative norm of the standard bump function. -/
noncomputable def standardCutoffBound (n : ℕ) : ℝ :=
  let b : ContDiffBump (0 : E n) := standardBump n
  sSup ((fun z : E n => ‖fderiv ℝ (b : E n → ℝ) z‖) '' tsupport (b : E n → ℝ))

lemma standardCutoffBound_nonneg (n : ℕ) : 0 ≤ standardCutoffBound n := by
  apply Real.sSup_nonneg
  intro x hx
  rcases hx with ⟨z, _, rfl⟩
  exact norm_nonneg _

lemma standardCutoffBound_is_bound (n : ℕ) :
    ∀ z, ‖fderiv ℝ ((standardBump n : E n → ℝ)) z‖ ≤ standardCutoffBound n := by
  let b : ContDiffBump (0 : E n) := standardBump n
  let f := fun z : E n => ‖fderiv ℝ (b : E n → ℝ) z‖
  let s := tsupport (b : E n → ℝ)
  have h_cont : Continuous (fderiv ℝ (b : E n → ℝ)) :=
    b.contDiff.continuous_fderiv (show (1 : WithTop ℕ∞) ≠ 0 from by simp)
  have h_compact : IsCompact s := by
    have hs : s = tsupport (b : E n → ℝ) := by rfl
    rw [hs, ContDiffBump.tsupport_eq b]
    exact isCompact_closedBall 0 b.rOut
  have h_bdd : BddAbove (f '' s) := h_compact.bddAbove_image h_cont.continuousOn.norm
  have h_main : ∀ z ∈ s, f z ≤ standardCutoffBound n := by
    intro z hz
    have h1 : f z ∈ f '' s := ⟨z, hz, rfl⟩
    exact le_csSup h_bdd h1
  intro z
  by_cases hz : z ∈ s
  · exact h_main z hz
  · have h10 : z ∉ Function.support (fderiv ℝ (b : E n → ℝ)) := by
      intro h11
      have h12 : Function.support (fderiv ℝ (b : E n → ℝ)) ⊆ s := by
        intro x hx
        by_contra h
        have h7 : x ∉ s := h
        have h8 : IsOpen (sᶜ) := isOpen_compl_iff.mpr (isClosed_tsupport (b : E n → ℝ))
        have h9 : (b : E n → ℝ) =ᶠ[nhds x] 0 := by
          filter_upwards [h8.mem_nhds h7] with z hz
          have h10 : z ∉ Function.support (b : E n → ℝ) := by
            intro h11; exact hz (subset_closure h11)
          simpa [Function.mem_support] using h10
        have h13 : fderiv ℝ (b : E n → ℝ) x = 0 := by
          have h14 : fderiv ℝ (b : E n → ℝ) =ᶠ[nhds x] fderiv ℝ (0 : E n → ℝ) := h9.fderiv
          simpa using h14.self_of_nhds
        simpa [Function.mem_support] using hx h13
      exact hz (h12 h11)
    have h11 : fderiv ℝ (b : E n → ℝ) z = 0 := by
      simpa [Function.mem_support] using h10
    rw [h11]
    have h12 : ‖(0 : E n →L[ℝ] ℝ)‖ = 0 := by simp
    rw [h12]
    exact standardCutoffBound_nonneg n

/-- Construct a smooth cutoff `φ` equal to 1 on `ball x₀ r`,
0 outside `ball x₀ (2*r)`, with `‖∇φ‖ ≤ C/r`. -/
lemma exists_cutoff (x₀ : E n) {r : ℝ} (hr : 0 < r) :
    ∃ (φ : E n → ℝ) (C_φ : ℝ), 0 ≤ C_φ ∧
      C_φ = standardCutoffBound n ∧
      ContDiff ℝ 1 φ ∧
      (∀ y ∈ ball x₀ r, φ y = 1) ∧
      (∀ y, y ∉ ball x₀ (2 * r) → φ y = 0) ∧
      (∀ y, 0 ≤ φ y ∧ φ y ≤ 1) ∧
      (∀ y, ‖fderiv ℝ φ y‖ ≤ C_φ / r) := by
  let b : ContDiffBump (0 : E n) := ⟨1, 2, by norm_num, by norm_num⟩
  let g : E n → E n := fun y => r⁻¹ • (y - x₀)
  let φ : E n → ℝ := fun y => b (g y)
  have hb_smooth : ContDiff ℝ 1 (b : E n → ℝ) := b.contDiff
  have h_scalar : ContDiff ℝ 1 (fun _ : E n => r⁻¹) := contDiff_const
  have h_vec : ContDiff ℝ 1 (fun y : E n => y - x₀) := contDiff_id.sub contDiff_const
  have hg_smooth : ContDiff ℝ 1 g := h_scalar.smul h_vec
  have hφ_smooth : ContDiff ℝ 1 φ := hb_smooth.comp hg_smooth
  have hb_diff : Differentiable ℝ (b : E n → ℝ) := hb_smooth.differentiable (by norm_num)
  have hg_diff : Differentiable ℝ g := hg_smooth.differentiable (by norm_num)
  have hφ_one : ∀ y ∈ ball x₀ r, φ y = 1 := by
    intro y hy
    have hdist : dist y x₀ < r := by simpa [mem_ball] using hy
    have hnorm : ‖y - x₀‖ < r := by rwa [dist_eq_norm] at hdist
    have h4 : ‖r⁻¹ • (y - x₀)‖ = |r⁻¹| * ‖y - x₀‖ := by
      rw [norm_smul] <;> simp
    have h3 : ‖r⁻¹ • (y - x₀)‖ ≤ 1 := by
      rw [h4]
      have h5 : |r⁻¹| = r⁻¹ := abs_of_pos (by positivity)
      rw [h5]
      have h6 : r⁻¹ * ‖y - x₀‖ < 1 := by
        calc r⁻¹ * ‖y - x₀‖ < r⁻¹ * r := by gcongr
          _ = 1 := by field_simp [hr.ne'] <;> ring
      exact h6.le
    have h5 : r⁻¹ • (y - x₀) ∈ closedBall (0 : E n) 1 := by
      simpa [closedBall] using h3
    exact b.one_of_mem_closedBall h5
  have hφ_zero : ∀ y, y ∉ ball x₀ (2 * r) → φ y = 0 := by
    intro y hy
    have h1 : 2 * r ≤ dist y x₀ := by simpa [mem_ball, not_lt] using hy
    have hnorm : 2 * r ≤ ‖y - x₀‖ := by rwa [dist_eq_norm] at h1
    have h4 : ‖r⁻¹ • (y - x₀)‖ = |r⁻¹| * ‖y - x₀‖ := by
      rw [norm_smul] <;> simp
    have h2 : (2 : ℝ) ≤ ‖r⁻¹ • (y - x₀)‖ := by
      rw [h4]
      have h5 : |r⁻¹| = r⁻¹ := abs_of_pos (by positivity)
      rw [h5]
      have h6 : r⁻¹ * ‖y - x₀‖ ≥ 2 := by
        calc r⁻¹ * ‖y - x₀‖ ≥ r⁻¹ * (2 * r) := by gcongr
          _ = 2 := by field_simp [hr.ne'] <;> ring
      exact h6
    have h7 : (2 : ℝ) ≤ dist (r⁻¹ • (y - x₀)) (0 : E n) := by
      simpa [dist_zero_right] using h2
    exact b.zero_of_le_dist h7
  have hφ_bounds : ∀ y, 0 ≤ φ y ∧ φ y ≤ 1 := fun y => ⟨b.nonneg, b.le_one⟩
  have hC_b_bound : ∀ z, ‖fderiv ℝ (b : E n → ℝ) z‖ ≤ standardCutoffBound n :=
    standardCutoffBound_is_bound n
  set C_b : ℝ := standardCutoffBound n with hC_b_def
  let scalar_map : E n →L[ℝ] E n := r⁻¹ • ContinuousLinearMap.id ℝ (E n)
  have hg_fderiv : ∀ y, fderiv ℝ g y = scalar_map := by
    intro y
    have h1 : g = fun z : E n => scalar_map z - r⁻¹ • x₀ := by
      funext z; have h_eq : r⁻¹ • (z - x₀) = r⁻¹ • z - r⁻¹ • x₀ := by rw [smul_sub]
      have h_scalar' : scalar_map z = r⁻¹ • z := by simp [scalar_map]
      rw [h_scalar']
      exact h_eq
    have h_lin : HasFDerivAt (fun z : E n => scalar_map z) scalar_map y :=
      scalar_map.hasFDerivAt
    have h2 : HasFDerivAt (fun z : E n => scalar_map z - r⁻¹ • x₀) scalar_map y :=
      h_lin.sub_const (r⁻¹ • x₀)
    rw [h1]; exact h2.fderiv
  have h_scalar_norm : ‖scalar_map‖ ≤ |r⁻¹| := by
    exact ContinuousLinearMap.opNorm_le_bound scalar_map (by positivity) (fun z => by
      have h : ‖scalar_map z‖ = |r⁻¹| * ‖z‖ := by
        rw [show scalar_map z = r⁻¹ • z from rfl, norm_smul] <;> simp
      rw [h])
  have h_fderiv_φ : ∀ y, ‖fderiv ℝ φ y‖ ≤ C_b / r := by
    intro y
    set fdb := fderiv ℝ (b : E n → ℝ) (g y) with hfdb
    have h3 : fderiv ℝ φ y = fdb.comp (fderiv ℝ g y) :=
      fderiv_comp y hb_diff.differentiableAt hg_diff.differentiableAt
    rw [h3, hg_fderiv y]
    have h6 : ‖fdb.comp scalar_map‖ ≤ ‖fdb‖ * ‖scalar_map‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    have h8 : |r⁻¹| = r⁻¹ := abs_of_pos (by positivity)
    have h9 : ‖fdb‖ ≤ C_b := hC_b_bound (g y)
    calc
      ‖fdb.comp scalar_map‖ ≤ ‖fdb‖ * ‖scalar_map‖ := h6
      _ ≤ ‖fdb‖ * |r⁻¹| := by gcongr <;> exact h_scalar_norm
      _ ≤ C_b * |r⁻¹| := by gcongr
      _ = C_b * r⁻¹ := by rw [h8]
      _ = C_b / r := by field_simp [hr.ne'] <;> ring
  exact ⟨φ, C_b, standardCutoffBound_nonneg n, rfl, hφ_smooth, hφ_one, hφ_zero, hφ_bounds, h_fderiv_φ⟩

/-- Base constant for the smooth relative isoperimetric inequality (no perimeter factor). -/
noncomputable def baseRelIsoConst (n : ℕ) : ENNReal :=
  if hn : 2 ≤ n then
    let p' : NNReal := (↑n : NNReal) / (↑n - 1)
    ↑(MeasureTheory.eLpNormLESNormFDerivOneConst (E := E n) (μ := volume) (↑p')) *
    ENNReal.ofReal (max (standardCutoffBound n) 1)
  else 1

/-- Dimension-dependent constant for the relative isoperimetric inequality.

Includes factor `n` for the component-wise gradient bound in the perimeter version. -/
noncomputable def relIsoConst (n : ℕ) : ENNReal :=
  (↑n : ENNReal) * baseRelIsoConst n

/-- Sphere has measure zero in Euclidean space. -/
lemma volume_sphere_eq_zero (x₀ : E n) {r : ℝ} (hr : r ≠ 0) : volume (sphere x₀ r) = 0 :=
  MeasureTheory.Measure.addHaar_sphere_of_ne_zero volume x₀ hr

/-- If `g x = 0` for all `x ∉ s`, then `∫⁻ x, g x ∂μ = ∫⁻ x, g x ∂(μ.restrict s)`. -/
lemma lintegral_eq_restrict_of_zero_outside {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {s : Set α} {g : α → ENNReal} (hs : MeasurableSet s)
    (h : ∀ x, x ∉ s → g x = 0) :
    ∫⁻ x, g x ∂μ = ∫⁻ x, g x ∂(μ.restrict s) := by
  have h2 : ∫⁻ x, g x ∂μ = ∫⁻ x, Set.indicator s g x ∂μ := by
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ s
    · exact (Set.indicator_of_mem hx g).symm
    · have h3 : g x = 0 := h x hx
      have h4 : Set.indicator s g x = 0 := by
        simp [Set.indicator_apply, hx]
      rw [h3, h4]
  rw [h2]
  exact MeasureTheory.lintegral_indicator hs g

/-- eLpNorm at p=1 equals lintegral of enorm. -/
lemma eLpNorm_one_eq {F : Type*} [NormedAddCommGroup F] {f : E n → F} {μ : Measure (E n)} :
    eLpNorm f (1 : NNReal) μ = ∫⁻ y, ‖f y‖ₑ ∂μ := by
  have h : eLpNorm f (1 : NNReal) μ ^ (1 : ℝ) = ∫⁻ y, ‖f y‖ₑ ^ (1 : ℝ) ∂μ :=
    eLpNorm_nnreal_pow_eq_lintegral (show (1 : NNReal) ≠ 0 from by norm_num)
  simpa using h

/-- If `Function.support f ⊆ s`, then `eLpNorm f 1 μ = eLpNorm f 1 (μ.restrict s)`. -/
lemma eLpNorm_restrict_eq_of_support_subset {F : Type*} [NormedAddCommGroup F]
    {f : E n → F} {μ : Measure (E n)} {s : Set (E n)} (hs : MeasurableSet s)
    (h : Function.support f ⊆ s) :
    eLpNorm f (1 : NNReal) μ = eLpNorm f (1 : NNReal) (μ.restrict s) := by
  have h_zero : ∀ x, x ∉ s → ‖f x‖ₑ = 0 := by
    intro x hx
    have h2 : f x = 0 := by
      by_contra h3
      exact hx (h h3)
    rw [h2]
    simp
  rw [eLpNorm_one_eq, eLpNorm_one_eq]
  exact lintegral_eq_restrict_of_zero_outside hs h_zero

/-- Helper: `‖x‖ₑ = 0` when `x = 0` in a normed group. -/
lemma enorm_eq_zero_of_eq_zero {G : Type*} [NormedAddCommGroup G] {x : G} (hx : x = 0) :
    ‖x‖ₑ = 0 := by
  rw [hx]
  rw [enorm_eq_nnnorm (0 : G)]
  simp

/-- Helper: `‖x‖ₑ = ENNReal.ofReal ‖x‖` in a normed group. -/
lemma enorm_eq_ofReal_norm {G : Type*} [NormedAddCommGroup G] (x : G) :
    ‖x‖ₑ = ENNReal.ofReal ‖x‖ := by
  rw [enorm_eq_nnnorm x]
  have h : (↑‖x‖₊ : ENNReal) = ENNReal.ofReal ‖x‖ := by
    simp [NNReal.nnnorm_eq] <;> rfl
  exact h

/-- Bound on `eLpNorm` of `φ • fderiv u` where `0 ≤ φ ≤ 1` and `φ` is supported in `ball x₀ (2r)`. -/
lemma eLpNorm_scalar_mult_bound {u φ : E n → ℝ} {x₀ : E n} {r : ℝ}
    (hφ_bounds : ∀ y, 0 ≤ φ y ∧ φ y ≤ 1)
    (hφ_zero : ∀ y, y ∉ ball x₀ (2 * r) → φ y = 0) :
    eLpNorm (fun y => φ y • fderiv ℝ u y) (1 : NNReal) volume ≤
      eLpNorm (fderiv ℝ u) (1 : NNReal) (volume.restrict (ball x₀ (2 * r))) := by
  let f : E n → (E n →L[ℝ] ℝ) := fun y => φ y • fderiv ℝ u y
  have h_zero_outside : ∀ y, y ∉ ball x₀ (2 * r) → ‖f y‖ₑ = 0 := by
    intro y hy
    have hφ : φ y = 0 := hφ_zero y hy
    have h_eq : f y = 0 := by
      simp only [f, hφ, zero_smul]
    exact enorm_eq_zero_of_eq_zero h_eq
  have h_pointwise : ∀ y, ‖f y‖ₑ ≤ ‖fderiv ℝ u y‖ₑ := by
    intro y
    have h5 : ‖f y‖ₑ = ‖φ y‖ₑ * ‖fderiv ℝ u y‖ₑ := by
      rw [show f y = φ y • fderiv ℝ u y from rfl, enorm_smul]
    rw [h5]
    have h6 : ‖φ y‖ₑ = ENNReal.ofReal (|φ y|) := Real.enorm_eq_ofReal_abs (φ y)
    rw [h6]
    have h7 : |φ y| ≤ 1 := by
      have h8 : 0 ≤ φ y ∧ φ y ≤ 1 := hφ_bounds y
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have h9 : ENNReal.ofReal (|φ y|) ≤ 1 := by
      rw [ENNReal.ofReal_le_one] <;> linarith [abs_nonneg (φ y)]
    calc
      ENNReal.ofReal (|φ y|) * ‖fderiv ℝ u y‖ₑ ≤ 1 * ‖fderiv ℝ u y‖ₑ := by gcongr
      _ = ‖fderiv ℝ u y‖ₑ := by simp
  have h3 : ∫⁻ y, ‖f y‖ₑ ∂volume = ∫⁻ y, ‖f y‖ₑ ∂(volume.restrict (ball x₀ (2 * r))) :=
    lintegral_eq_restrict_of_zero_outside isOpen_ball.measurableSet h_zero_outside
  have h4 : ∫⁻ y, ‖f y‖ₑ ∂(volume.restrict (ball x₀ (2 * r))) ≤
      ∫⁻ y, ‖fderiv ℝ u y‖ₑ ∂(volume.restrict (ball x₀ (2 * r))) :=
    lintegral_mono h_pointwise
  have h9 : eLpNorm f (1 : NNReal) volume = ∫⁻ y, ‖f y‖ₑ ∂volume := eLpNorm_one_eq
  have h10 : eLpNorm (fderiv ℝ u) (1 : NNReal) (volume.restrict (ball x₀ (2 * r))) =
      ∫⁻ y, ‖fderiv ℝ u y‖ₑ ∂(volume.restrict (ball x₀ (2 * r))) := eLpNorm_one_eq
  rw [h9, h10]
  rw [h3]
  exact h4

/-- If `φ` is zero outside `ball x₀ (2r)`, then `fderiv ℝ φ y = 0` for `y ∉ closedBall x₀ (2r)`. -/
lemma fderiv_cutoff_zero_outside {φ : E n → ℝ} {x₀ : E n} {r : ℝ}
    (hφ_smooth : ContDiff ℝ 1 φ)
    (hφ_zero : ∀ y, y ∉ ball x₀ (2 * r) → φ y = 0)
    (hr : 0 < r) :
    ∀ y, y ∉ closedBall x₀ (2 * r) → fderiv ℝ φ y = 0 := by
  intro y hy
  have h_open : IsOpen (closedBall x₀ (2 * r))ᶜ := isOpen_compl_iff.mpr isClosed_closedBall
  have h_nhds : (closedBall x₀ (2 * r))ᶜ ∈ nhds y := h_open.mem_nhds hy
  have h_zero : φ =ᶠ[nhds y] 0 := by
    filter_upwards [h_nhds] with z hz
    have h5 : z ∉ ball x₀ (2 * r) := by
      intro h6
      have h71 : z ∈ closure (ball x₀ (2 * r)) := subset_closure h6
      have h72 : closure (ball x₀ (2 * r)) = closedBall x₀ (2 * r) :=
        closure_ball x₀ (show (2 * r) ≠ 0 by linarith)
      rw [h72] at h71
      exact hz h71
    exact hφ_zero z h5
  have h6 : fderiv ℝ φ =ᶠ[nhds y] fderiv ℝ (0 : E n → ℝ) := h_zero.fderiv
  have h7 : fderiv ℝ φ y = fderiv ℝ (0 : E n → ℝ) y := h6.self_of_nhds
  rw [h7]
  simp

/-- Pointwise bound for `w • fderiv φ`. -/
lemma weighted_fderiv_pointwise_bound {w φ : E n → ℝ}
    (C_φ r : ℝ) (hC_φ_nonneg : 0 ≤ C_φ)
    (hφ_fderiv : ∀ y, ‖fderiv ℝ φ y‖ ≤ C_φ / r) (y : E n) :
    ‖w y • fderiv ℝ φ y‖ₑ ≤ ENNReal.ofReal (C_φ / r) * ‖w y‖ₑ := by
  have h6 : ‖w y • fderiv ℝ φ y‖ₑ = ‖w y‖ₑ * ‖fderiv ℝ φ y‖ₑ := by
    rw [enorm_smul]
  rw [h6]
  have h7 : ‖w y‖ₑ = ENNReal.ofReal (|w y|) := Real.enorm_eq_ofReal_abs (w y)
  have h8 : ‖fderiv ℝ φ y‖ₑ ≤ ENNReal.ofReal (C_φ / r) := by
    rw [enorm_eq_ofReal_norm (fderiv ℝ φ y)]
    exact ENNReal.ofReal_le_ofReal (hφ_fderiv y)
  have h11 : ‖w y‖ₑ * ‖fderiv ℝ φ y‖ₑ ≤ ‖w y‖ₑ * ENNReal.ofReal (C_φ / r) := by
    gcongr
  have h12 : ‖w y‖ₑ * ENNReal.ofReal (C_φ / r) = ENNReal.ofReal (C_φ / r) * ‖w y‖ₑ := by
    exact mul_comm _ _
  rw [h12] at h11
  exact h11

/-- Bound on `eLpNorm` of `w • fderiv φ` where `φ` is a cutoff function. -/
lemma eLpNorm_weighted_fderiv_cutoff_bound {w φ : E n → ℝ} {x₀ : E n} {r : ℝ}
    (hw_meas : Measurable w)
    (hn : 2 ≤ n) (hr : 0 < r) (C_φ : ℝ) (hC_φ_nonneg : 0 ≤ C_φ)
    (hφ_smooth : ContDiff ℝ 1 φ)
    (hφ_zero : ∀ y, y ∉ ball x₀ (2 * r) → φ y = 0)
    (hφ_fderiv : ∀ y, ‖fderiv ℝ φ y‖ ≤ C_φ / r) :
    eLpNorm (fun y => w y • fderiv ℝ φ y) (1 : NNReal) volume ≤
      ENNReal.ofReal (C_φ / r) * eLpNorm w (1 : NNReal) (volume.restrict (ball x₀ (2 * r))) := by
  let f : E n → (E n →L[ℝ] ℝ) := fun y => w y • fderiv ℝ φ y
  have h_fderiv_outside : ∀ y, y ∉ closedBall x₀ (2 * r) → fderiv ℝ φ y = 0 :=
    fderiv_cutoff_zero_outside hφ_smooth hφ_zero hr
  have h_zero_outside : ∀ y, y ∉ closedBall x₀ (2 * r) → ‖f y‖ₑ = 0 := by
    intro y hy
    have hfd : fderiv ℝ φ y = 0 := h_fderiv_outside y hy
    have h_eq : f y = 0 := by
      simp only [f, hfd, smul_zero]
    exact enorm_eq_zero_of_eq_zero h_eq
  have h_sphere_zero : volume (sphere x₀ (2 * r)) = 0 :=
    volume_sphere_eq_zero x₀ (show (2 * r) ≠ 0 by linarith)
  have h_ae : closedBall x₀ (2 * r) =ᵐ[volume] ball x₀ (2 * r) := by
    have h5 : (closedBall x₀ (2 * r) \ ball x₀ (2 * r)) = sphere x₀ (2 * r) := by
      ext z
      simp only [mem_diff, mem_closedBall, mem_ball, mem_sphere]
      constructor
      · intro ⟨h1, h2⟩
        exact le_iff_eq_or_lt.mp h1 |>.resolve_right h2
      · intro h
        constructor <;> linarith
    have h71 : ball x₀ (2 * r) ⊆ closedBall x₀ (2 * r) := ball_subset_closedBall
    have h7 : (ball x₀ (2 * r) \ closedBall x₀ (2 * r)) = ∅ := by
      rw [Set.diff_eq_empty] <;> exact h71
    simpa [ae_eq_set, h5] using ⟨h_sphere_zero, by rw [h7] <;> simp⟩
  have h_pointwise : ∀ y, ‖f y‖ₑ ≤ ENNReal.ofReal (C_φ / r) * ‖w y‖ₑ :=
    fun y => weighted_fderiv_pointwise_bound (w := w) (φ := φ) C_φ r hC_φ_nonneg hφ_fderiv y
  have h3 : ∫⁻ y, ‖f y‖ₑ ∂volume = ∫⁻ y, ‖f y‖ₑ ∂(volume.restrict (closedBall x₀ (2 * r))) :=
    lintegral_eq_restrict_of_zero_outside isClosed_closedBall.measurableSet h_zero_outside
  have h4 : volume.restrict (closedBall x₀ (2 * r)) = volume.restrict (ball x₀ (2 * r)) :=
    Measure.restrict_congr_set h_ae
  have h5 : ∫⁻ y, ‖f y‖ₑ ∂(volume.restrict (ball x₀ (2 * r))) ≤
      ∫⁻ y, ENNReal.ofReal (C_φ / r) * ‖w y‖ₑ ∂(volume.restrict (ball x₀ (2 * r))) :=
    lintegral_mono h_pointwise
  have h11 : eLpNorm f (1 : NNReal) volume = ∫⁻ y, ‖f y‖ₑ ∂volume := eLpNorm_one_eq
  have h12 : eLpNorm w (1 : NNReal) (volume.restrict (ball x₀ (2 * r))) =
      ∫⁻ y, ‖w y‖ₑ ∂(volume.restrict (ball x₀ (2 * r))) := eLpNorm_one_eq
  rw [h11, h12]
  have h13 : ∫⁻ y, ‖f y‖ₑ ∂volume = ∫⁻ y, ‖f y‖ₑ ∂(volume.restrict (ball x₀ (2 * r))) := by
    rw [h3, h4]
  rw [h13]
  have h14 : ∫⁻ y, ENNReal.ofReal (C_φ / r) * ‖w y‖ₑ ∂(volume.restrict (ball x₀ (2 * r))) =
      ENNReal.ofReal (C_φ / r) * ∫⁻ y, ‖w y‖ₑ ∂(volume.restrict (ball x₀ (2 * r))) :=
    MeasureTheory.lintegral_const_mul (ENNReal.ofReal (C_φ / r))
      (measurable_enorm.comp hw_meas)
  exact h14 ▸ h5

/-- Match the cutoff constant to the relative isoperimetric constant. -/
lemma relIsoConst_match (n : ℕ) (hn : 2 ≤ n)
    (C_S : ENNReal) (C_φ : ℝ)
    (hC_φ : C_φ = standardCutoffBound n)
    (hCSM : C_S * ENNReal.ofReal (max (standardCutoffBound n) 1) ≤ relIsoConst n)
    (r : ℝ) (hr : 0 < r) (A B : ENNReal) :
    C_S * (A + ENNReal.ofReal (C_φ / r) * B) ≤
      relIsoConst n * (A + ENNReal.ofReal (1 / r) * B) := by
  let M : ENNReal := ENNReal.ofReal (max (standardCutoffBound n) 1)
  have hM1 : (1 : ENNReal) ≤ M := by
    dsimp only [M]
    have h : (1 : ℝ) ≤ max (standardCutoffBound n) 1 := le_max_right _ _
    have h' : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
    rw [h']
    exact ENNReal.ofReal_le_ofReal h
  have hM2 : ENNReal.ofReal C_φ ≤ M := by
    dsimp only [M]
    have h : ENNReal.ofReal C_φ ≤ ENNReal.ofReal (max C_φ 1) := by
      rw [hC_φ] <;> exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    simpa [hC_φ] using h
  have hC_φ_nonneg : 0 ≤ C_φ := by
    rw [hC_φ]
    exact standardCutoffBound_nonneg n
  have h_div : ENNReal.ofReal (C_φ / r) = ENNReal.ofReal C_φ * ENNReal.ofReal (1 / r) := by
    have hpos1 : 0 ≤ C_φ := hC_φ_nonneg
    have hpos2 : 0 < 1 / r := by positivity
    rw [← ENNReal.ofReal_mul hpos1] <;> ring_nf
  have h1 : C_S * A ≤ (C_S * M) * A := by
    have h12 : A ≤ M * A := by
      calc A = (1 : ENNReal) * A := by simp
        _ ≤ M * A := by gcongr
    have h13 : C_S * A ≤ C_S * (M * A) := by gcongr
    have h14 : C_S * (M * A) = (C_S * M) * A := by ring
    rw [h14] at h13
    exact h13
  have h2 : C_S * (ENNReal.ofReal C_φ * ENNReal.ofReal (1 / r) * B) ≤
      (C_S * M) * (ENNReal.ofReal (1 / r) * B) := by
    have h21 : C_S * (ENNReal.ofReal C_φ * ENNReal.ofReal (1 / r) * B) =
        C_S * ENNReal.ofReal C_φ * (ENNReal.ofReal (1 / r) * B) := by ring
    have h22 : (C_S * M) * (ENNReal.ofReal (1 / r) * B) =
        C_S * M * (ENNReal.ofReal (1 / r) * B) := by ring
    rw [h21, h22]
    gcongr
  have h_const1 : C_S * (A + ENNReal.ofReal (C_φ / r) * B) ≤
      (C_S * M) * (A + ENNReal.ofReal (1 / r) * B) := by
    rw [h_div]
    have h3 : C_S * A + C_S * (ENNReal.ofReal C_φ * ENNReal.ofReal (1 / r) * B) ≤
        (C_S * M) * A + (C_S * M) * (ENNReal.ofReal (1 / r) * B) := by
      exact add_le_add h1 h2
    simpa [mul_add, mul_assoc, mul_left_comm] using h3
  have h_const2 : (C_S * M) * (A + ENNReal.ofReal (1 / r) * B) ≤
      relIsoConst n * (A + ENNReal.ofReal (1 / r) * B) := by
    gcongr <;> exact hCSM
  exact le_trans h_const1 h_const2

end Geometry
