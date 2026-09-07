import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.GradientConvergence
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.MollificationGradientBound
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.Mollification
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory Convolution ContDiff Pointwise

namespace Geometry.Perimeter

variable {n : ℕ} [Nonempty (Fin n)]

-- ============================================================================
-- Gradient vector helpers
-- ============================================================================

/-- Riesz representative (gradient vector) of the derivative. -/
noncomputable def gradVec (u : E n → ℝ) (x : E n) : E n :=
  riesz (fderiv ℝ u x)

lemma fderiv_apply_eq_inner (u : E n → ℝ) (x : E n) (v : E n) :
    fderiv ℝ u x v = inner ℝ (gradVec u x) v :=
  riesz_apply (fderiv ℝ u x) v

lemma fderiv_norm_eq_gradVec_norm (u : E n → ℝ) (x : E n) :
    ‖fderiv ℝ u x‖ = ‖gradVec u x‖ :=
  (riesz_norm (fderiv ℝ u x)).symm

lemma inner_grad_sum (u : E n → ℝ) (x : E n) (φ : E n → E n) :
    inner ℝ (gradVec u x) (φ x) =
    ∑ i : Fin n, (fderiv ℝ u x (EuclideanSpace.single i 1)) * (φ x i) := by
  have h_basis : φ x = ∑ i : Fin n, (φ x i) • EuclideanSpace.single i 1 := by
    let b := EuclideanSpace.basisFun (Fin n) ℝ
    have h1 : ∑ i : Fin n, b.repr (φ x) i • b i = φ x := b.sum_repr (φ x)
    have h2 : ∑ i : Fin n, b.repr (φ x) i • b i =
        ∑ i : Fin n, (φ x i) • EuclideanSpace.single i (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      have h3 : b.repr (φ x) i = φ x i := by simp [b]
      have h4 : b i = EuclideanSpace.single i (1 : ℝ) := by simp [b]
      rw [h3, h4]
    rw [h2] at h1
    exact h1.symm
  have h_lin : fderiv ℝ u x (∑ i : Fin n, (φ x i) • EuclideanSpace.single i 1) =
      ∑ i : Fin n, (φ x i) * fderiv ℝ u x (EuclideanSpace.single i 1) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (fderiv ℝ u x).map_smul (φ x i) (EuclideanSpace.single i 1)
  have h_goal : fderiv ℝ u x (φ x) =
      ∑ i : Fin n, (φ x i) * fderiv ℝ u x (EuclideanSpace.single i 1) := by
    rw [congr_arg (fderiv ℝ u x) h_basis]
    exact h_lin
  calc
    inner ℝ (gradVec u x) (φ x)
      = fderiv ℝ u x (φ x) := by rw [←fderiv_apply_eq_inner u x (φ x)]
    _ = ∑ i : Fin n, (φ x i) * fderiv ℝ u x (EuclideanSpace.single i 1) := h_goal
    _ = ∑ i : Fin n, (fderiv ℝ u x (EuclideanSpace.single i 1)) * (φ x i) := by
        apply Finset.sum_congr rfl <;> intro i _ <;> ring

-- ============================================================================
-- Integration by parts: ∫ u · div φ = -∫ inner(∇u, φ)
-- ============================================================================

lemma integration_by_parts_smooth
    {u : E n → ℝ} (hu : ContDiff ℝ 1 u) (hu_support : HasCompactSupport u)
    {φ : E n → E n} (hφ : ContDiff ℝ ∞ φ) (hφ_support : HasCompactSupport φ) :
    ∫ x, u x * divergence φ x = -∫ x, inner ℝ (gradVec u x) (φ x) := by
  let ψ (i : Fin n) : E n → ℝ := fun y => φ y i
  have hproj : ∀ (i : Fin n), ContDiff ℝ ∞ (fun v : E n => v i) := by
    intro i; fun_prop
  have hψ_smooth_top : ∀ (i : Fin n), ContDiff ℝ ∞ (ψ i) := by
    intro i
    have h_eq : (ψ i) = (fun v : E n => v i) ∘ φ := by funext y; rfl
    rw [h_eq]
    exact (hproj i).comp hφ
  have hψ_smooth1 : ∀ (i : Fin n), ContDiff ℝ 1 (ψ i) := by
    intro i
    exact (hψ_smooth_top i).of_le (by norm_num)
  have hψ_support : ∀ (i : Fin n), HasCompactSupport (ψ i) := by
    intro i
    have h1 : Function.support (ψ i) ⊆ Function.support φ := by
      intro x hx
      have h2 : φ x i ≠ 0 := hx
      have h3 : φ x ≠ 0 := by
        intro h4
        have h5 : φ x i = 0 := by
          rw [h4] <;> simp
        exact h2 h5
      simpa [Function.mem_support] using h3
    exact hφ_support.mono h1
  have h3 : ∀ (i : Fin n), Integrable (fun x : E n => u x * (fderiv ℝ (ψ i) x (EuclideanSpace.single i 1))) volume := by
    intro i
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · have h4 : HasCompactSupport (fun x : E n => fderiv ℝ (ψ i) x (EuclideanSpace.single i 1)) :=
        (hψ_support i).fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
      exact h4.mul_left
  have h_sum_int : ∫ x, u x * divergence φ x =
      ∑ i : Fin n, ∫ x, u x * (fderiv ℝ (ψ i) x (EuclideanSpace.single i 1)) := by
    have h2 : ∀ x, u x * divergence φ x =
        ∑ i : Fin n, u x * (fderiv ℝ (ψ i) x (EuclideanSpace.single i 1)) := by
      intro x
      simp [divergence, ψ, Finset.mul_sum] <;> rfl
    rw [integral_congr_ae (ae_of_all _ h2)]
    rw [integral_finset_sum]
    <;> intro i _
    <;> exact h3 i
  rw [h_sum_int]
  have h_ibp : ∀ (i : Fin n),
      ∫ x, u x * (fderiv ℝ (ψ i) x (EuclideanSpace.single i 1)) =
      -∫ x, (fderiv ℝ u x (EuclideanSpace.single i 1)) * (ψ i x) := by
    intro i
    have h_orig := integration_by_parts_compact hu (hψ_smooth1 i) (hψ_support i) i
    linarith
  have h_sum_ibp : ∑ i : Fin n, ∫ x, u x * (fderiv ℝ (ψ i) x (EuclideanSpace.single i 1)) =
      -∑ i : Fin n, ∫ x, (fderiv ℝ u x (EuclideanSpace.single i 1)) * (ψ i x) := by
    rw [Finset.sum_congr rfl (fun i _ => h_ibp i)]
    rw [Finset.sum_neg_distrib]
  rw [h_sum_ibp]
  have h6 : ∀ (i : Fin n), Integrable (fun x : E n => (fderiv ℝ u x (EuclideanSpace.single i 1)) * (ψ i x)) volume := by
    intro i
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact (hψ_support i).mul_left
  have h5 : ∑ i : Fin n, ∫ x, (fderiv ℝ u x (EuclideanSpace.single i 1)) * (ψ i x) =
      ∫ x, ∑ i : Fin n, (fderiv ℝ u x (EuclideanSpace.single i 1)) * (ψ i x) := by
    rw [←integral_finset_sum]
    <;> intro i _
    <;> exact h6 i
  rw [h5]
  have h7 : ∫ x, ∑ i : Fin n, (fderiv ℝ u x (EuclideanSpace.single i 1)) * (ψ i x) =
      ∫ x, inner ℝ (gradVec u x) (φ x) := by
    apply integral_congr_ae
    filter_upwards with x
    exact (inner_grad_sum u x φ).symm
  rw [h7] <;> ring

-- ============================================================================
-- gradVec has compact support when u does
-- ============================================================================

lemma gradVec_hasCompactSupport {u : E n → ℝ}
    (hu : ContDiff ℝ 1 u) (hu_support : HasCompactSupport u) :
    HasCompactSupport (gradVec u) := by
  have h1 : Function.support (gradVec u) ⊆ tsupport u := by
    intro x hx
    by_contra h2
    have h3 : IsOpen (tsupport u)ᶜ := hu_support.isClosed.isOpen_compl
    have h4 : (tsupport u)ᶜ ∈ nhds x := h3.mem_nhds h2
    have h5 : ∀ᶠ y in nhds x, u y = 0 := by
      filter_upwards [h4] with y hy
      have h6 : y ∉ Function.support u := by
        intro h7
        exact hy (subset_closure h7)
      simpa [Function.mem_support] using h6
    have h6 : fderiv ℝ u x = 0 := by
      have h7 : Filter.EventuallyEq (nhds x) u (fun _ => (0 : ℝ)) := h5
      have h8 : fderiv ℝ u x = fderiv ℝ (fun _ => (0 : ℝ)) x := h7.fderiv_eq
      rw [h8]; simp
    have h9 : gradVec u x = 0 := by
      simp [gradVec, h6, riesz] <;> rfl
    exact hx h9
  have h_closed : IsClosed (tsupport u) := hu_support.isClosed
  have h2 : tsupport (gradVec u) ⊆ tsupport u := closure_minimal h1 h_closed
  exact hu_support.of_isClosed_subset isClosed_closure h2

/-- gradVec is continuous when u is C¹. -/
lemma gradVec_continuous {u : E n → ℝ} (hu : ContDiff ℝ 1 u) :
    Continuous (gradVec u) := by
  have h1 : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have h2 : Continuous (riesz : (E n →L[ℝ] ℝ) → E n) :=
    (InnerProductSpace.toDual ℝ (E n)).symm.continuous
  exact h2.comp h1

-- ============================================================================
-- Gradient normalization field: φ_δ(x) = g(x) / sqrt(‖g(x)‖² + δ²)
-- ============================================================================

/-- Normalize a vector field by sqrt(norm² + δ²), giving a smooth field of norm ≤ 1. -/
noncomputable def gradNormalize (δ : ℝ) (g : E n → E n) (x : E n) : E n :=
  (Real.sqrt (‖g x‖ ^ 2 + δ ^ 2))⁻¹ • g x

lemma gradNormalize_smooth {δ : ℝ} (hδ : 0 < δ) {g : E n → E n}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (gradNormalize δ g) := by
  have h1 : ContDiff ℝ ∞ (fun v : E n => ‖v‖ ^ 2) := by
    have h_sum : ContDiff ℝ ∞ (fun v : E n => ∑ i : Fin n, v i ^ 2) := by
      apply ContDiff.sum
      intro i _
      have h_i : ContDiff ℝ ∞ (fun v : E n => v i) := by fun_prop
      exact h_i.pow 2
    have h_eq : (fun v : E n => ∑ i : Fin n, v i ^ 2) = (fun v : E n => ‖v‖ ^ 2) := by
      funext v
      have h_nonneg : 0 ≤ ∑ i : Fin n, v i ^ 2 := by positivity
      have h : ‖v‖ ^ 2 = ∑ i : Fin n, v i ^ 2 := by
        have h1 : ‖v‖ = Real.sqrt (∑ i : Fin n, v i ^ 2) := by
          simp [EuclideanSpace.norm_eq]
        rw [h1, Real.sq_sqrt h_nonneg]
      exact h.symm
    rw [h_eq] at h_sum
    exact h_sum
  have h2 : ContDiff ℝ ∞ (fun v : E n => ‖v‖ ^ 2 + δ ^ 2) := h1.add contDiff_const
  have h_ne_zero : ∀ (v : E n), (‖v‖ ^ 2 + δ ^ 2) ≠ 0 := by
    intro v; have h : 0 < ‖v‖ ^ 2 + δ ^ 2 := by positivity
    exact h.ne'
  have h3 : ContDiff ℝ ∞ (fun v : E n => Real.sqrt (‖v‖ ^ 2 + δ ^ 2)) :=
    h2.sqrt h_ne_zero
  have h_sqrt_ne_zero : ∀ (v : E n), Real.sqrt (‖v‖ ^ 2 + δ ^ 2) ≠ 0 := by
    intro v; have h : 0 < Real.sqrt (‖v‖ ^ 2 + δ ^ 2) := by positivity
    exact h.ne'
  have h4 : ContDiff ℝ ∞ (fun v : E n => (Real.sqrt (‖v‖ ^ 2 + δ ^ 2))⁻¹) :=
    h3.inv h_sqrt_ne_zero
  have h5 : ContDiff ℝ ∞ (fun v : E n => (Real.sqrt (‖v‖ ^ 2 + δ ^ 2))⁻¹ • v) :=
    h4.smul contDiff_id
  have h_eq : gradNormalize δ g = (fun v : E n => (Real.sqrt (‖v‖ ^ 2 + δ ^ 2))⁻¹ • v) ∘ g := by
    funext x
    rfl
  rw [h_eq]
  exact h5.comp hg

lemma gradNormalize_bound {δ : ℝ} (hδ : 0 < δ) {g : E n → E n} (x : E n) :
    ‖gradNormalize δ g x‖ ≤ 1 := by
  set c : ℝ := Real.sqrt (‖g x‖ ^ 2 + δ ^ 2) with hc
  have hc_pos : 0 < c := by positivity
  by_cases h : g x = 0
  · have h9 : gradNormalize δ g x = 0 := by
      simp [gradNormalize, h]
    rw [h9] <;> norm_num
  · have h6 : 0 < ‖g x‖ := norm_pos_iff.mpr h
    have h7 : ‖gradNormalize δ g x‖ = ‖g x‖ / c := by
      have h8 : ‖gradNormalize δ g x‖ = ‖c⁻¹ • g x‖ := by rfl
      rw [h8]
      have h9 : ‖c⁻¹ • g x‖ = |c⁻¹| * ‖g x‖ := norm_smul c⁻¹ (g x)
      rw [h9]
      have h10 : |c⁻¹| = c⁻¹ := by
        apply abs_of_pos
        positivity
      rw [h10] <;> field_simp <;> ring
    rw [h7]
    have h10 : ‖g x‖ ≤ c := by
      have h11 : ‖g x‖ ^ 2 ≤ ‖g x‖ ^ 2 + δ ^ 2 := by
        have h12 : 0 < δ ^ 2 := by positivity
        linarith
      have h13 : Real.sqrt (‖g x‖ ^ 2) ≤ c := Real.sqrt_le_sqrt h11
      have h14 : Real.sqrt (‖g x‖ ^ 2) = ‖g x‖ := by
        rw [Real.sqrt_sq (by positivity)]
      rw [h14] at h13
      exact h13
    exact (div_le_one hc_pos).mpr h10

lemma gradNormalize_hasCompactSupport {δ : ℝ} (hδ : 0 < δ) {g : E n → E n}
    (hg_support : HasCompactSupport g) : HasCompactSupport (gradNormalize δ g) := by
  have h1 : Function.support (gradNormalize δ g) ⊆ Function.support g := by
    intro x hx
    by_contra h2
    have h3 : g x = 0 := by simpa [Function.mem_support] using h2
    have h4 : gradNormalize δ g x = 0 := by
      simp [gradNormalize, h3]
    exact hx h4
  have h2 : tsupport (gradNormalize δ g) ⊆ tsupport g := closure_mono h1
  exact hg_support.of_isClosed_subset isClosed_closure h2

lemma gradNormalize_inner {δ : ℝ} (hδ : 0 < δ) {g : E n → E n} (x : E n) :
    inner ℝ (g x) (gradNormalize δ g x) =
    ‖g x‖ ^ 2 / Real.sqrt (‖g x‖ ^ 2 + δ ^ 2) := by
  set c : ℝ := Real.sqrt (‖g x‖ ^ 2 + δ ^ 2) with hc
  have h1 : inner ℝ (g x) (gradNormalize δ g x) = c⁻¹ * inner ℝ (g x) (g x) := by
    have h2 : inner ℝ (g x) (c⁻¹ • g x) = c⁻¹ * inner ℝ (g x) (g x) := by
      rw [inner_smul_right]
      <;> ring
    simpa [gradNormalize] using h2
  rw [h1]
  have h2 : inner ℝ (g x) (g x) = (‖g x‖ ^ 2 : ℝ) := by
    simpa [inner_self_eq_norm_sq_to_K] using rfl
  rw [h2] <;> field_simp <;> ring

-- ============================================================================
-- Divergence commutes with mollification
-- ============================================================================

lemma divergence_mollification
    {ρ : E n → ℝ} (hρ_smooth : ContDiff ℝ ∞ ρ) (hρ_support : HasCompactSupport ρ)
    {φ : E n → E n} (hφ : ContDiff ℝ ∞ φ) (hφ_support : HasCompactSupport φ) :
    divergence (mollifyVec ρ φ) =
    convolution ρ (divergence φ) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  funext x
  have h1 : ∀ (i : Fin n), (mollifyVec ρ φ · i) =
      convolution ρ (fun y : E n => φ y i) L volume := by
    intro i
    funext y
    exact mollifyVec_component hρ_support hρ_smooth.continuous hφ.continuous y i
  have h2 : ∀ (i : Fin n), fderiv ℝ (mollifyVec ρ φ · i) x (EuclideanSpace.single i 1) =
      convolution ρ (fun y : E n => fderiv ℝ (fun z : E n => φ z i) y (EuclideanSpace.single i 1)) L volume x := by
    intro i
    have hproj : ContDiff ℝ ∞ (fun v : E n => v i) := by fun_prop
    have hψ_smooth : ContDiff ℝ ∞ (fun y : E n => φ y i) := by
      have h_eq : (fun y : E n => φ y i) = (fun v : E n => v i) ∘ φ := by funext z; rfl
      rw [h_eq]; exact hproj.comp hφ
    have hψ_smooth1 : ContDiff ℝ 1 (fun y : E n => φ y i) := hψ_smooth.of_le (by norm_num)
    have hψ_support : HasCompactSupport (fun y : E n => φ y i) := by
      have h : Function.support (fun y : E n => φ y i) ⊆ Function.support φ := by
        intro y hy
        have h2 : φ y i ≠ 0 := hy
        have h3 : φ y ≠ 0 := by
          intro h4
          have h5 : φ y i = 0 := by rw [h4] <;> simp
          exact h2 h5
        simpa [Function.mem_support] using h3
      exact hφ_support.mono h
    rw [h1 i]
    exact convolution_deriv_commute hρ_smooth hρ_support hψ_smooth1 hψ_support i x
  have h_sum_conv : ∑ i : Fin n, convolution ρ (fun y : E n => fderiv ℝ (fun z : E n => φ z i) y (EuclideanSpace.single i 1)) L volume x =
      convolution ρ (divergence φ) L volume x := by
    have h4 : ∀ (t : E n), ∑ i : Fin n, ρ t * (fderiv ℝ (fun z : E n => φ z i) (x - t) (EuclideanSpace.single i 1)) =
        ρ t * (divergence φ (x - t)) := by
      intro t
      simp [divergence, Finset.mul_sum] <;> ring
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply]
    have h_int_i : ∀ i, Integrable (fun t : E n => ρ t * (fderiv ℝ (fun z : E n => φ z i) (x - t) (EuclideanSpace.single i 1))) volume := by
      intro i
      have h_supp : Function.support (fun t : E n => ρ t * (fderiv ℝ (fun z : E n => φ z i) (x - t) (EuclideanSpace.single i 1))) ⊆ Function.support ρ := by
        intro t ht
        have h2 : ρ t * (fderiv ℝ (fun z : E n => φ z i) (x - t) (EuclideanSpace.single i 1)) ≠ 0 := ht
        have h3 : ρ t ≠ 0 := by
          intro h4
          have h5 : ρ t * (fderiv ℝ (fun z : E n => φ z i) (x - t) (EuclideanSpace.single i 1)) = 0 := by
            rw [h4] <;> ring
          exact h2 h5
        exact h3
      apply Continuous.integrable_of_hasCompactSupport
      · fun_prop
      · exact hρ_support.mono h_supp
    have h5 : ∑ i : Fin n, ∫ (t : E n), (L (ρ t)) ((fderiv ℝ (fun z : E n => φ z i) (x - t)) (EuclideanSpace.single i 1)) =
        ∫ (t : E n), ∑ i : Fin n, ρ t * (fderiv ℝ (fun z : E n => φ z i) (x - t) (EuclideanSpace.single i 1)) := by
      have h_L : ∀ (t : E n) (i : Fin n), (L (ρ t)) ((fderiv ℝ (fun z : E n => φ z i) (x - t)) (EuclideanSpace.single i 1)) =
          ρ t * (fderiv ℝ (fun z : E n => φ z i) (x - t)) (EuclideanSpace.single i 1) := by
        intro t i
        simp [L, ContinuousLinearMap.lsmul_apply] <;> ring
      have h6 : ∀ i, ∫ (t : E n), (L (ρ t)) ((fderiv ℝ (fun z : E n => φ z i) (x - t)) (EuclideanSpace.single i 1)) =
          ∫ (t : E n), ρ t * (fderiv ℝ (fun z : E n => φ z i) (x - t)) (EuclideanSpace.single i 1) := by
        intro i
        apply integral_congr_ae
        filter_upwards with t
        exact h_L t i
      have h7 : ∑ i : Fin n, ∫ (t : E n), (L (ρ t)) ((fderiv ℝ (fun z : E n => φ z i) (x - t)) (EuclideanSpace.single i 1)) =
          ∑ i : Fin n, ∫ (t : E n), ρ t * (fderiv ℝ (fun z : E n => φ z i) (x - t)) (EuclideanSpace.single i 1) := by
        apply Finset.sum_congr rfl
        intro i _
        exact h6 i
      rw [h7]
      rw [integral_finset_sum]
      <;> intro i _
      <;> exact h_int_i i
    rw [h5]
    apply integral_congr_ae
    filter_upwards with t
    exact h4 t
  calc
    divergence (mollifyVec ρ φ) x
      = ∑ i : Fin n, fderiv ℝ (mollifyVec ρ φ · i) x (EuclideanSpace.single i 1) := by rfl
    _ = ∑ i : Fin n, convolution ρ (fun y : E n => fderiv ℝ (fun z : E n => φ z i) y (EuclideanSpace.single i 1)) L volume x := by
        apply Finset.sum_congr rfl; intro i _; exact h2 i
    _ = convolution ρ (divergence φ) L volume x := h_sum_conv

-- ============================================================================
-- Mollification has compact support
-- ============================================================================

lemma mollification_hasCompactSupport {S : Set (E n)} (hS : MeasurableSet S)
    (hBdd : Bornology.IsBounded S) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (convolution (Mollification.rho ε hε)
      (Set.indicator S (fun _ => (1 : ℝ))) (ContinuousLinearMap.lsmul ℝ ℝ) volume) := by
  let ρ : E n → ℝ := Mollification.rho ε hε
  let χ : E n → ℝ := Set.indicator S (fun _ => (1 : ℝ))
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  let b : ContDiffBump (0 : E n) := Mollification.mollifier ε hε
  have hρ_support : HasCompactSupport ρ := b.hasCompactSupport_normed
  have h1 : Function.support χ ⊆ S := by
    intro x hx
    simpa [χ, Function.mem_support, Set.indicator_apply] using hx
  have h2 : Bornology.IsBounded (Function.support χ) := by
    exact Bornology.IsBounded.subset hBdd h1
  have h3 : IsCompact (tsupport χ) := h2.isCompact_closure
  have hχ_support : HasCompactSupport χ := by
    simpa [HasCompactSupport] using h3
  exact hρ_support.convolution L hχ_support

-- ============================================================================
-- Main contraction theorem
-- ============================================================================

/-- **Mollification contraction property**: convolution does not increase total variation.

For `u = χ_S * ρ_ε`, the gradient integral satisfies `∫ ‖∇u‖ ≤ P(S)`. -/
theorem mollification_contraction
    {S : Set (E n)} (hS : MeasurableSet S) (hBdd : Bornology.IsBounded S)
    {ε : ℝ} (hε : 0 < ε) :
    let u : E n → ℝ := convolution (Mollification.rho ε hε)
        (Set.indicator S (fun _ => (1 : ℝ))) (ContinuousLinearMap.lsmul ℝ ℝ) volume
    ENNReal.ofReal (∫ x, ‖fderiv ℝ u x‖) ≤ perimeter S := by
  let ρ : E n → ℝ := Mollification.rho ε hε
  let χ : E n → ℝ := Set.indicator S (fun _ => (1 : ℝ))
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  let u : E n → ℝ := convolution ρ χ L volume
  let b : ContDiffBump (0 : E n) := Mollification.mollifier ε hε
  have hρ_smooth : ContDiff ℝ ∞ ρ := b.contDiff_normed
  have hρ_support : HasCompactSupport ρ := b.hasCompactSupport_normed
  have hρ_nonneg : ∀ x, 0 ≤ ρ x := b.nonneg_normed
  have hρ_int : ∫ x, ρ x = 1 := b.integral_normed
  have hρ_even : ∀ x, ρ (-x) = ρ x := mollifier_even ε hε
  have hρ_cont : Continuous ρ := hρ_smooth.continuous
  have hχ_meas : Measurable χ := measurable_const.indicator hS
  have hχ_bdd : ∀ x, |χ x| ≤ 1 := by
    intro x; by_cases h : x ∈ S <;> simp [χ, h] <;> norm_num
  have hχ_support : HasCompactSupport χ := by
    have h1 : Function.support χ ⊆ S := by
      intro x hx; simpa [χ, Function.mem_support, Set.indicator_apply] using hx
    have h2 : Bornology.IsBounded (Function.support χ) := by exact Bornology.IsBounded.subset hBdd h1
    have h3 : IsCompact (tsupport χ) := h2.isCompact_closure
    simpa [HasCompactSupport] using h3
  have hS_finite : volume S < ⊤ := hBdd.measure_lt_top
  have hχ_integrable : Integrable χ volume := by
    have hfin : (volume.restrict S) Set.univ < ⊤ := by simpa using hS_finite
    have h_const_int : Integrable (fun _ : E n => (1 : ℝ)) (volume.restrict S) := by
      refine' ⟨stronglyMeasurable_const.aestronglyMeasurable, _⟩
      simpa [HasFiniteIntegral, lintegral_const] using hfin
    have h_on : IntegrableOn (fun _ : E n => (1 : ℝ)) S volume := h_const_int
    rw [integrable_indicator_iff hS]
    exact h_on
  have hχ_localInt : LocallyIntegrable χ volume := hχ_integrable.locallyIntegrable
  have hu_smooth : ContDiff ℝ ∞ u :=
    hρ_support.contDiff_convolution_left L hρ_smooth hχ_localInt
  have hu_support : HasCompactSupport u := hρ_support.convolution L hχ_support
  let g : E n → E n := gradVec u
  have h1 : ContDiff ℝ ∞ (fderiv ℝ u) :=
    hu_smooth.fderiv_right (by simp)
  have h2 : ContDiff ℝ ∞ (riesz : (E n →L[ℝ] ℝ) → E n) :=
    (InnerProductSpace.toDual ℝ (E n)).symm.contDiff
  have hg_smooth : ContDiff ℝ ∞ g := h2.comp h1
  have hg_support : HasCompactSupport g := gradVec_hasCompactSupport (hu_smooth.of_le (by norm_num)) hu_support
  have hg_cont : Continuous g := hg_smooth.continuous
  have hg_norm_support : HasCompactSupport (fun x : E n => ‖g x‖) := hg_support.norm
  have hg_norm_integrable : Integrable (fun x : E n => ‖g x‖) volume :=
    hg_cont.norm.integrable_of_hasCompactSupport hg_norm_support

  -- Step 1: For any test vector field ψ, |∫ u · div ψ| ≤ perimeter S
  have h_bound_all : ∀ (ψ : TestVectorField),
      ENNReal.ofReal |∫ x, u x * divergence ψ.toFun x| ≤ perimeter S := by
    intro ψ
    let Ψ : E n → E n := mollifyVec ρ ψ.toFun
    have hΨ_smooth : ContDiff ℝ ∞ Ψ :=
      mollifyVec_smooth hρ_smooth hρ_support ψ.smooth.continuous
    have hΨ_support : HasCompactSupport Ψ :=
      mollifyVec_hasCompactSupport hρ_support ψ.compact
    have hΨ_bound : ∀ x, ‖Ψ x‖ ≤ 1 :=
      mollifyVec_norm_bound hρ_nonneg hρ_int hρ_support hρ_cont ψ.smooth.continuous ψ.bound
    have hdiv_comm : divergence Ψ = convolution ρ (divergence ψ.toFun) L volume :=
      divergence_mollification hρ_smooth hρ_support ψ.smooth ψ.compact
    have h1 : ∀ i, HasCompactSupport (fun y : E n => fderiv ℝ (fun z : E n => ψ.toFun z i) y (EuclideanSpace.single i 1)) := by
      intro i
      have hproj : ContDiff ℝ ∞ (fun v : E n => v i) := by fun_prop
      have hψ_smooth : ContDiff ℝ ∞ (fun y : E n => ψ.toFun y i) := by
        have h_eq : (fun y : E n => ψ.toFun y i) = (fun v : E n => v i) ∘ ψ.toFun := by funext z; rfl
        rw [h_eq]; exact hproj.comp ψ.smooth
      have hψ_support : HasCompactSupport (fun y : E n => ψ.toFun y i) := by
        have h : Function.support (fun y : E n => ψ.toFun y i) ⊆ Function.support ψ.toFun := by
          intro y hy
          have h2 : ψ.toFun y i ≠ 0 := hy
          have h3 : ψ.toFun y ≠ 0 := by
            intro h4
            have h5 : ψ.toFun y i = 0 := by rw [h4] <;> simp
            exact h2 h5
          simpa [Function.mem_support] using h3
        exact ψ.compact.mono h
      exact hψ_support.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
    let f (i : Fin n) : E n → ℝ := fun y => fderiv ℝ (fun z : E n => ψ.toFun z i) y (EuclideanSpace.single i 1)
    have h1' : ∀ i, HasCompactSupport (f i) := h1
    have h_union : IsCompact (⋃ i ∈ Finset.univ, tsupport (f i)) := by
      have h : ∀ i ∈ Finset.univ, IsCompact (tsupport (f i)) := by
        intro i _
        exact (h1' i).isCompact
      exact Finset.isCompact_biUnion Finset.univ h
    have h_supp : Function.support (fun x : E n => ∑ i : Fin n, f i x) ⊆ (⋃ i ∈ Finset.univ, tsupport (f i)) := by
      intro x hx
      by_contra h
      have h' : ∀ i, f i x = 0 := by
        intro i
        have h4 : x ∉ tsupport (f i) := by
          by_contra h3
          have h5 : x ∈ (⋃ i ∈ Finset.univ, tsupport (f i)) := by
            exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_univ i, h3⟩
          exact h h5
        have h6 : x ∉ Function.support (f i) := by
          intro h7
          exact h4 (subset_closure h7)
        simpa [Function.mem_support] using h6
      have h_sum : (∑ i : Fin n, f i x) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact h' i
      exact hx h_sum
    have h_closed : IsClosed (⋃ i ∈ Finset.univ, tsupport (f i)) := h_union.isClosed
    have h_tsupp : tsupport (fun x : E n => ∑ i : Fin n, f i x) ⊆ (⋃ i ∈ Finset.univ, tsupport (f i)) :=
      closure_minimal h_supp h_closed
    have hdivψ_support : HasCompactSupport (divergence ψ.toFun) := by
      have h_sum_support : HasCompactSupport (fun x : E n => ∑ i : Fin n, f i x) :=
        h_union.of_isClosed_subset isClosed_closure h_tsupp
      have h_eq : divergence ψ.toFun = fun x : E n => ∑ i : Fin n, f i x := by funext x; rfl
      rw [h_eq]
      exact h_sum_support
    have hdivψ_cont : Continuous (divergence ψ.toFun) := by
      let f (i : Fin n) : E n → ℝ := fun x => fderiv ℝ (fun z : E n => ψ.toFun z i) x (EuclideanSpace.single i 1)
      have h1 : ∀ i, Continuous (f i) := by
        intro i
        have hproj : ContDiff ℝ ∞ (fun v : E n => v i) := by fun_prop
        have hψ_smooth : ContDiff ℝ ∞ (fun y : E n => ψ.toFun y i) := by
          have h_eq : (fun y : E n => ψ.toFun y i) = (fun v : E n => v i) ∘ ψ.toFun := by funext z; rfl
          rw [h_eq]; exact hproj.comp ψ.smooth
        have hψ_smooth1 : ContDiff ℝ 1 (fun y : E n => ψ.toFun y i) := hψ_smooth.of_le (by norm_num)
        have h_fd : Continuous (fderiv ℝ (fun y : E n => ψ.toFun y i)) :=
          hψ_smooth1.continuous_fderiv (by norm_num)
        have h_eval : Continuous (fun L : (E n →L[ℝ] ℝ) => L (EuclideanSpace.single i 1)) := by fun_prop
        exact h_eval.comp h_fd
      have h2 : Continuous (fun x : E n => ∑ i : Fin n, f i x) := by
        exact continuous_finset_sum Finset.univ (fun i _ => h1 i)
      have h3 : (divergence ψ.toFun) = (fun x : E n => ∑ i : Fin n, f i x) := by
        funext x; rfl
      rw [h3]
      exact h2
    have h_adj : ∫ x, u x * divergence ψ.toFun x =
        ∫ y, χ y * (convolution ρ (divergence ψ.toFun) L volume y) :=
      convolution_adjoint_symm hρ_cont hρ_support hρ_even hχ_meas hχ_bdd hdivψ_cont hdivψ_support
    have h_adj2 : ∫ y, χ y * (convolution ρ (divergence ψ.toFun) L volume y) =
        ∫ y, χ y * divergence Ψ y := by
      rw [hdiv_comm]
    have h_adj3 : ∫ y, χ y * divergence Ψ y = ∫ x in S, divergence Ψ x := by
      let h := divergence Ψ
      have h_eq1 : (fun y => χ y * h y) = Set.indicator S h := by
        funext y
        by_cases hy : y ∈ S <;> simp [χ, Set.indicator_apply, hy]
      rw [h_eq1, integral_indicator hS] <;> rfl
    let Ψ' : TestVectorField := ⟨Ψ, hΨ_smooth, hΨ_support, hΨ_bound⟩
    have h_perim : ENNReal.ofReal |∫ x in S, divergence Ψ x| ≤ perimeter S :=
      le_iSup (fun (θ : TestVectorField) => ENNReal.ofReal |∫ x in S, divergence θ.toFun x|) Ψ'
    have h_final : ∫ x, u x * divergence ψ.toFun x = ∫ x in S, divergence Ψ x := by
      rw [h_adj, h_adj2, h_adj3]
    rw [h_final]
    exact h_perim

  -- Step 2: Construct gradient normalization test fields φ_δ
  let F (δ : ℝ) (x : E n) : ℝ := inner ℝ (g x) (gradNormalize δ g x)
  have hF_formula : ∀ (δ : ℝ), 0 < δ → ∀ (x : E n),
      F δ x = ‖g x‖ ^ 2 / Real.sqrt (‖g x‖ ^ 2 + δ ^ 2) := by
    intro δ hδ x
    exact gradNormalize_inner hδ x
  have hF_nonneg : ∀ (δ : ℝ), 0 < δ → ∀ (x : E n), 0 ≤ F δ x := by
    intro δ hδ x
    rw [hF_formula δ hδ x]
    positivity
  have hF_bound : ∀ (δ : ℝ), 0 < δ → ∀ (x : E n), |F δ x| ≤ ‖g x‖ := by
    intro δ hδ x
    have h1 : 0 ≤ F δ x := hF_nonneg δ hδ x
    rw [abs_of_nonneg h1]
    rw [hF_formula δ hδ x]
    by_cases h : g x = 0
    · rw [h]; simp
    · have h6 : 0 < ‖g x‖ := norm_pos_iff.mpr h
      set c : ℝ := Real.sqrt (‖g x‖ ^ 2 + δ ^ 2) with hc
      have hc_pos : 0 < c := by positivity
      have h7 : ‖g x‖ ≤ c := by
        have h8 : ‖g x‖ ^ 2 ≤ ‖g x‖ ^ 2 + δ ^ 2 := by
          have h9 : 0 < δ ^ 2 := by positivity
          linarith
        have h10 : Real.sqrt (‖g x‖ ^ 2) ≤ c := Real.sqrt_le_sqrt h8
        have h11 : Real.sqrt (‖g x‖ ^ 2) = ‖g x‖ := by
          rw [Real.sqrt_sq (by positivity)]
        rw [h11] at h10; exact h10
      have h12 : ‖g x‖ ^ 2 / c ≤ ‖g x‖ := by
        calc
          ‖g x‖ ^ 2 / c ≤ (‖g x‖ * c) / c := by
            gcongr
            <;> nlinarith
          _ = ‖g x‖ := by
            field_simp [hc_pos.ne'] <;> ring
      exact h12

  -- Step 3: For each δ > 0, φ_δ is a test vector field
  have h_test_field : ∀ (δ : ℝ), 0 < δ →
      ∃ (φδ : TestVectorField), φδ.toFun = gradNormalize δ g := by
    intro δ hδ
    let φδ_fun : E n → E n := gradNormalize δ g
    have h_smooth : ContDiff ℝ ∞ φδ_fun := gradNormalize_smooth hδ hg_smooth
    have h_support : HasCompactSupport φδ_fun := gradNormalize_hasCompactSupport hδ hg_support
    have h_bound : ∀ x, ‖φδ_fun x‖ ≤ 1 := gradNormalize_bound hδ
    refine ⟨⟨φδ_fun, h_smooth, h_support, h_bound⟩, rfl⟩

  -- Step 4: For each δ > 0, ∫ F δ ≤ perimeter S (in ENNReal)
  have h_main_ineq : ∀ (δ : ℝ), 0 < δ →
      ENNReal.ofReal (∫ x, F δ x) ≤ perimeter S := by
    intro δ hδ
    rcases h_test_field δ hδ with ⟨φδ, hφδ_eq⟩
    have h_ibp : ∫ x, u x * divergence φδ.toFun x = -∫ x, F δ x := by
      have h := integration_by_parts_smooth (hu_smooth.of_le (by norm_num)) hu_support
        φδ.smooth φδ.compact
      have h_eq : φδ.toFun = gradNormalize δ g := hφδ_eq
      simpa [F, h_eq] using h
    have h_nonneg_int : 0 ≤ ∫ x, F δ x := by
      apply integral_nonneg
      exact hF_nonneg δ hδ
    have h_abs : |∫ x, u x * divergence φδ.toFun x| = ∫ x, F δ x := by
      rw [h_ibp]
      rw [abs_neg, abs_of_nonneg h_nonneg_int]
    have h := h_bound_all φδ
    rw [h_abs] at h
    exact h

  -- Step 5: DCT: ∫ F (1/(m+1)) → ∫ ‖g‖ as m → ∞
  let δ (m : ℕ) : ℝ := 1 / (m + 1 : ℝ)
  have hδ_pos : ∀ m, 0 < δ m := by intro m; positivity
  have hδ_tendsto : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    have h_eq : δ = fun m : ℕ => ((m : ℝ) + 1)⁻¹ := by
      funext m
      simp [δ] <;> field_simp
    rw [h_eq]
    have h1 : Filter.Tendsto (fun m : ℕ => (m : ℝ) + 1) Filter.atTop Filter.atTop := by
      have h2 : ∀ (m : ℕ), (m : ℝ) ≤ (m : ℝ) + 1 := by intro m; linarith
      exact tendsto_atTop_mono h2 tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp h1
  have h_pointwise : ∀ (x : E n), Filter.Tendsto (fun m : ℕ => F (δ m) x) Filter.atTop (nhds (‖g x‖)) := by
    intro x
    by_cases h : g x = 0
    · have h2 : ∀ m, F (δ m) x = 0 := by
        intro m
        rw [hF_formula (δ m) (hδ_pos m) x, h] <;> simp
      simpa [h] using tendsto_const_nhds.congr (fun m => (h2 m).symm)
    · have h6 : 0 < ‖g x‖ := norm_pos_iff.mpr h
      have h7 : Filter.Tendsto (fun m : ℕ => Real.sqrt (‖g x‖ ^ 2 + (δ m) ^ 2)) Filter.atTop
          (nhds (Real.sqrt (‖g x‖ ^ 2))) := by
        have h8 : Filter.Tendsto (fun m : ℕ => (δ m) ^ 2) Filter.atTop (nhds 0) := by
          have h9 := hδ_tendsto.pow 2
          simpa using h9
        have h9 : Filter.Tendsto (fun m : ℕ => ‖g x‖ ^ 2 + (δ m) ^ 2) Filter.atTop (nhds (‖g x‖ ^ 2 + 0)) :=
          tendsto_const_nhds.add h8
        simpa using h9.sqrt
      have h9 : Real.sqrt (‖g x‖ ^ 2) = ‖g x‖ := by
        rw [Real.sqrt_sq (by positivity)]
      have h10 : ∀ m, F (δ m) x = ‖g x‖ ^ 2 / Real.sqrt (‖g x‖ ^ 2 + (δ m) ^ 2) := by
        intro m
        exact hF_formula (δ m) (hδ_pos m) x
      have h11 : Filter.Tendsto (fun m : ℕ => ‖g x‖ ^ 2 / Real.sqrt (‖g x‖ ^ 2 + (δ m) ^ 2)) Filter.atTop
          (nhds (‖g x‖ ^ 2 / Real.sqrt (‖g x‖ ^ 2))) :=
        tendsto_const_nhds.div h7 (by positivity)
      have h12 : ‖g x‖ ^ 2 / Real.sqrt (‖g x‖ ^ 2) = ‖g x‖ := by
        rw [h9]
        field_simp [h6.ne'] <;> ring
      rw [h12] at h11
      exact h11.congr (fun m => (h10 m).symm)
  have h_dom : ∀ (m : ℕ), ∀ (x : E n), |F (δ m) x| ≤ ‖g x‖ := by
    intro m x
    exact hF_bound (δ m) (hδ_pos m) x
  have h_cont_F : ∀ m, Continuous (fun x : E n => F (δ m) x) := by
    intro m
    have h_smooth : ContDiff ℝ ∞ (gradNormalize (δ m) g) := gradNormalize_smooth (hδ_pos m) hg_smooth
    have h : Continuous (fun x : E n => inner ℝ (g x) (gradNormalize (δ m) g x)) := by
      fun_prop
    exact h
  have h_integrable : ∀ m, Integrable (fun x : E n => F (δ m) x) volume := by
    intro m
    have h_supp : Function.support (fun x : E n => F (δ m) x) ⊆ Function.support g := by
      intro x hx
      by_contra h2
      have h3 : g x = 0 := by simpa [Function.mem_support] using h2
      have h4 : F (δ m) x = 0 := by
        rw [hF_formula (δ m) (hδ_pos m) x, h3] <;> simp
      exact hx h4
    have h_compact : HasCompactSupport (fun x : E n => F (δ m) x) :=
      hg_support.mono h_supp
    exact (h_cont_F m).integrable_of_hasCompactSupport h_compact
  have h_ae_meas : ∀ m, AEStronglyMeasurable (fun x : E n => F (δ m) x) volume := by
    intro m
    exact (h_cont_F m).aestronglyMeasurable
  have h_dom' : ∀ m, ∀ᵐ x, ‖F (δ m) x‖ ≤ ‖g x‖ := by
    intro m
    filter_upwards with x
    have h_eq : ‖F (δ m) x‖ = |F (δ m) x| := by simp [Real.norm_eq_abs]
    rw [h_eq]
    exact h_dom m x
  have h_dct : Filter.Tendsto (fun m : ℕ => ∫ x, F (δ m) x) Filter.atTop (nhds (∫ x, ‖g x‖)) :=
    tendsto_integral_of_dominated_convergence (fun x : E n => ‖g x‖) h_ae_meas
      hg_norm_integrable h_dom' (ae_of_all _ h_pointwise)

  -- Step 6: Take limit in the inequality
  have h_final : ENNReal.ofReal (∫ x, ‖g x‖) ≤ perimeter S := by
    have h1 : ∀ m, ENNReal.ofReal (∫ x, F (δ m) x) ≤ perimeter S :=
      fun m => h_main_ineq (δ m) (hδ_pos m)
    have h1' : ∀ᶠ m in Filter.atTop, ENNReal.ofReal (∫ x, F (δ m) x) ≤ perimeter S := by
      filter_upwards with m
      exact h1 m
    have h_dct2 : Filter.Tendsto (fun m : ℕ => ENNReal.ofReal (∫ x, F (δ m) x)) Filter.atTop
        (nhds (ENNReal.ofReal (∫ x, ‖g x‖))) :=
      ENNReal.continuous_ofReal.tendsto _ |>.comp h_dct
    have h_const : Filter.Tendsto (fun _ : ℕ => perimeter S) Filter.atTop (nhds (perimeter S)) :=
      tendsto_const_nhds
    exact le_of_tendsto_of_tendsto h_dct2 h_const h1'
  have h_norm_eq : ∀ x, ‖g x‖ = ‖fderiv ℝ u x‖ := by
    intro x
    exact (fderiv_norm_eq_gradVec_norm u x).symm
  have h_integral_eq : ∫ x, ‖g x‖ = ∫ x, ‖fderiv ℝ u x‖ := by
    apply integral_congr_ae
    filter_upwards with x
    exact h_norm_eq x
  rw [h_integral_eq] at h_final
  exact h_final

/-- Contraction for the canonical mollification sequence. -/
theorem mollification_contraction_seq
    {S : Set (E n)} (hS : MeasurableSet S) (hBdd : Bornology.IsBounded S)
    (k : ℕ) :
    ENNReal.ofReal (∫ x, ‖fderiv ℝ (Mollification.mollificationSeq hS k) x‖) ≤ perimeter S := by
  let ε : ℝ := 1 / (k + 2 : ℝ)
  have hε : 0 < ε := by positivity
  have h_eq : Mollification.mollificationSeq hS k =
      convolution (Mollification.rho ε hε) (Set.indicator S (fun _ => (1 : ℝ)))
        (ContinuousLinearMap.lsmul ℝ ℝ) volume := by rfl
  rw [h_eq]
  exact mollification_contraction hS hBdd hε

/-- Contraction in lintegral form. -/
theorem mollification_contraction_lintegral
    {S : Set (E n)} (hS : MeasurableSet S) (hBdd : Bornology.IsBounded S)
    (k : ℕ) :
    ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ (Mollification.mollificationSeq hS k) x‖ ≤ perimeter S := by
  let ε : ℝ := 1 / (k + 2 : ℝ)
  have hε : 0 < ε := by positivity
  let u : E n → ℝ := Mollification.mollificationSeq hS k
  have h_smooth : ContDiff ℝ ∞ u := Mollification.mollify_contDiff hS ε hε
  have h_support : HasCompactSupport u := by
    have h_eq : u = convolution (Mollification.rho ε hε) (Set.indicator S (fun _ => (1 : ℝ)))
        (ContinuousLinearMap.lsmul ℝ ℝ) volume := by rfl
    rw [h_eq]
    exact mollification_hasCompactSupport hS hBdd hε
  have h_fd_support : HasCompactSupport (fderiv ℝ u) := h_support.fderiv ℝ
  have h_fd_cont : Continuous (fderiv ℝ u) := h_smooth.continuous_fderiv (by norm_num)
  have h_fd_integrable : Integrable (fderiv ℝ u) volume :=
    h_fd_cont.integrable_of_hasCompactSupport h_fd_support
  have h_eq : ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ u x‖ = ENNReal.ofReal (∫ x, ‖fderiv ℝ u x‖) := by
    have h1 : ENNReal.ofReal (∫ x, ‖fderiv ℝ u x‖) = ∫⁻ x, ‖fderiv ℝ u x‖ₑ :=
      ofReal_integral_norm_eq_lintegral_enorm h_fd_integrable
    have h2 : ∀ x, ‖fderiv ℝ u x‖ₑ = ENNReal.ofReal ‖fderiv ℝ u x‖ := by
      intro x; simp [enorm]
    rw [h1]
    congr with x
    exact (h2 x).symm
  rw [h_eq]
  exact mollification_contraction_seq hS hBdd k

-- ============================================================================
-- Integral convergence helper: ∫ u_k · ψ → ∫_S ψ for smooth compact ψ
-- ============================================================================

/-- Mollification integrals against smooth compact test functions converge. -/
lemma mollification_integral_convergence
    {S : Set (E n)} (hS : MeasurableSet S) (hBdd : Bornology.IsBounded S)
    {ψ : E n → ℝ} (hψ_cont : Continuous ψ) (hψ_support : HasCompactSupport ψ) :
    Filter.Tendsto (fun k => ∫ x, (Mollification.mollificationSeq hS k) x * ψ x)
      Filter.atTop (nhds (∫ x in S, ψ x)) := by
  let u : ℕ → E n → ℝ := fun k => Mollification.mollificationSeq hS k
  let χ : E n → ℝ := Set.indicator S (fun _ => (1 : ℝ))
  let K' : Set (E n) := tsupport ψ
  have hK'_compact : IsCompact K' := hψ_support.isCompact
  have hK'_meas : MeasurableSet K' := hK'_compact.measurableSet
  have hK'_closed : IsClosed K' := hK'_compact.isClosed

  -- Bound ψ on K'
  have hψ_bdd : ∃ (C : ℝ), 0 ≤ C ∧ ∀ x ∈ K', |ψ x| ≤ C := by
    have h_cont_abs : Continuous (fun x => |ψ x|) := by fun_prop
    have h : BddAbove (Set.image (fun x => |ψ x|) K') :=
      hK'_compact.bddAbove_image h_cont_abs.continuousOn
    rcases h with ⟨C, hC⟩
    refine ⟨max C 0, by positivity, fun x hx => ?_⟩
    have h5 : |ψ x| ∈ Set.image (fun x => |ψ x|) K' := ⟨x, hx, rfl⟩
    have h6 : |ψ x| ≤ C := hC h5
    exact le_max_of_le_left h6
  rcases hψ_bdd with ⟨C, hC_nonneg, hC⟩

  -- ψ x = 0 when x ∉ K'
  have hψ_outside : ∀ x, x ∉ K' → ψ x = 0 := by
    intro x hx
    have h1 : x ∉ Function.support ψ := by
      intro h2
      exact hx (subset_closure h2)
    simpa [Function.mem_support] using h1

  -- Integrability of u k * ψ
  have h_int1 : ∀ k, Integrable (fun x => u k x * ψ x) volume := by
    intro k
    have h_u_cont : Continuous (u k) := (Mollification.mollify_contDiff hS _ _).continuous
    have h_cont : Continuous (fun x => u k x * ψ x) := h_u_cont.mul hψ_cont
    have h_supp : Function.support (fun x => u k x * ψ x) ⊆ K' := by
      intro x hx
      by_contra h
      have h9 : ψ x = 0 := hψ_outside x h
      have h10 : u k x * ψ x = 0 := by rw [h9] <;> ring
      exact hx h10
    have h_tsupp : tsupport (fun x => u k x * ψ x) ⊆ K' := by
      have h1 : closure (Function.support (fun x => u k x * ψ x)) ⊆ closure K' := closure_mono h_supp
      have h2 : closure K' = K' := hK'_closed.closure_eq
      rw [h2] at h1
      exact h1
    have h_cs : HasCompactSupport (fun x => u k x * ψ x) :=
      hK'_compact.of_isClosed_subset isClosed_closure h_tsupp
    exact h_cont.integrable_of_hasCompactSupport h_cs

  -- Integrability of χ * ψ via indicator
  have h_eq_χψ : (fun x : E n => χ x * ψ x) = Set.indicator S ψ := by
    funext x
    by_cases hx : x ∈ S <;> simp [χ, hx, Set.indicator_apply] <;> ring
  have hψ_int : Integrable ψ volume := hψ_cont.integrable_of_hasCompactSupport hψ_support
  have h_int2 : Integrable (fun x => χ x * ψ x) volume := by
    rw [h_eq_χψ]
    exact hψ_int.indicator hS

  -- ∫ χ * ψ = ∫_S ψ
  have h_eq_χ_int : ∫ x, χ x * ψ x = ∫ x in S, ψ x := by
    rw [h_eq_χψ, integral_indicator hS]

  -- Difference bound: |∫ u_k * ψ - ∫ χ * ψ| ≤ C * ∫_{K'} |u_k - χ|
  have h_ineq : ∀ k, |(∫ x, u k x * ψ x) - (∫ x, χ x * ψ x)| ≤ C * ∫ x in K', |u k x - χ x| := by
    intro k
    let f1 := fun x : E n => u k x * ψ x
    let f2 := fun x : E n => χ x * ψ x
    have h_diff_eq : (f1 - f2) = fun x : E n => (u k x - χ x) * ψ x := by
      funext x; simp [f1, f2, sub_apply] <;> ring
    have h5 : (∫ x, f1 x) - (∫ x, f2 x) = ∫ x, (f1 - f2) x := by exact Eq.symm (integral_sub' (h_int1 k) h_int2)
    have h5' : (∫ x, f1 x) - (∫ x, f2 x) = ∫ x, (u k x - χ x) * ψ x := by
      rw [h5, h_diff_eq]
    have h_diff_int : Integrable (fun x : E n => (u k x - χ x) * ψ x) volume := by
      rw [←h_diff_eq]; exact (h_int1 k).sub h_int2
    have h6 : |(∫ x, f1 x) - (∫ x, f2 x)| ≤ ∫ x, |(u k x - χ x) * ψ x| := by
      rw [h5']; exact abs_integral_le_integral_abs
    have h8 : ∀ x, x ∉ K' → |(u k x - χ x) * ψ x| = 0 := by
      intro x hx
      have h9 : ψ x = 0 := hψ_outside x hx
      have h10 : (u k x - χ x) * ψ x = 0 := by rw [h9] <;> ring
      rw [h10]; simp
    have h9 : (fun x => |(u k x - χ x) * ψ x|) = Set.indicator K' (fun x => |u k x - χ x| * |ψ x|) := by
      funext x
      by_cases hx : x ∈ K'
      · simp [hx, Set.indicator_apply, abs_mul]
      · have h10 : |(u k x - χ x) * ψ x| = 0 := h8 x hx
        simp [hx, h10, Set.indicator_apply]
    have h7 : ∫ x, |(u k x - χ x) * ψ x| = ∫ x in K', |u k x - χ x| * |ψ x| := by
      rw [h9, integral_indicator hK'_meas] <;> rfl
    have hK'_fin : volume K' < ⊤ := hK'_compact.measure_lt_top
    have h_uk_meas : Measurable (u k) := (Mollification.mollify_contDiff hS _ _).continuous.measurable
    have hχ_meas : Measurable χ := (measurable_const.indicator hS)
    have hψ_meas : Measurable ψ := hψ_cont.measurable
    have h_abs1_meas : AEStronglyMeasurable (fun x : E n => |u k x - χ x| * |ψ x|) (volume.restrict K') := by
      simpa [Real.norm_eq_abs] using
        ((h_uk_meas.sub hχ_meas).norm.mul hψ_meas.norm |>.aestronglyMeasurable)
    have h_uk_bound : ∀ x, |u k x| ≤ 1 := by
      intro x
      have h := Mollification.mollify_bound hS (1 / (k + 2 : ℝ)) (by positivity) x
      have h0 : 0 ≤ u k x := h.1
      have h1 : u k x ≤ 1 := h.2
      rw [abs_le] <;> constructor <;> linarith
    have hχ_bound : ∀ x, |χ x| ≤ 1 := by
      intro x
      by_cases h : x ∈ S <;> simp [χ, h, abs_le] <;> norm_num
    have h_abs1_bdd : ∀ᵐ x ∂volume.restrict K', ‖(|u k x - χ x| * |ψ x|)‖ ≤ 2 * C := by
      have h' : ∀ x ∈ K', ‖(|u k x - χ x| * |ψ x|)‖ ≤ 2 * C := by
        intro x hx
        have h1 : |u k x - χ x| ≤ 2 := by
          calc |u k x - χ x| ≤ |u k x| + |χ x| := by exact abs_sub _ _
            _ ≤ 1 + 1 := by gcongr <;> [exact h_uk_bound x; exact hχ_bound x]
            _ = 2 := by norm_num
        have h2 : |ψ x| ≤ C := hC x hx
        have h4 : |u k x - χ x| * |ψ x| ≤ |u k x - χ x| * C :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        have h5 : |u k x - χ x| * C ≤ 2 * C :=
          mul_le_mul_of_nonneg_right h1 hC_nonneg
        simpa [Real.norm_eq_abs] using le_trans h4 h5
      have h_mem : ∀ᵐ x ∂volume.restrict K', x ∈ K' := by exact ae_restrict_mem hK'_meas
      exact h_mem.mono (fun x hx => h' x hx)
    have h_abs1_int : IntegrableOn (fun x : E n => |u k x - χ x| * |ψ x|) K' volume :=
      IntegrableOn.of_bound hK'_fin h_abs1_meas (2 * C) h_abs1_bdd
    have h_abs2_meas : AEStronglyMeasurable (fun x : E n => |u k x - χ x| * C) (volume.restrict K') := by
      simpa [Real.norm_eq_abs] using
        ((h_uk_meas.sub hχ_meas).norm.mul measurable_const |>.aestronglyMeasurable)
    have h_abs2_bdd : ∀ᵐ x ∂volume.restrict K', ‖(|u k x - χ x| * C)‖ ≤ 2 * C := by
      have h' : ∀ x ∈ K', ‖(|u k x - χ x| * C)‖ ≤ 2 * C := by
        intro x hx
        have h1 : |u k x - χ x| ≤ 2 := by
          calc |u k x - χ x| ≤ |u k x| + |χ x| := by exact abs_sub _ _
            _ ≤ 1 + 1 := by gcongr <;> [exact h_uk_bound x; exact hχ_bound x]
            _ = 2 := by norm_num
        have h3 : 0 ≤ C := hC_nonneg
        have h4 : |u k x - χ x| * C ≤ 2 * C :=
          mul_le_mul_of_nonneg_right h1 h3
        have hC_abs : |C| = C := abs_of_nonneg h3
        simpa [Real.norm_eq_abs, hC_abs] using h4
      have h_mem : ∀ᵐ x ∂volume.restrict K', x ∈ K' := by exact ae_restrict_mem hK'_meas
      exact h_mem.mono (fun x hx => h' x hx)
    have h_abs2_int : IntegrableOn (fun x : E n => |u k x - χ x| * C) K' volume :=
      IntegrableOn.of_bound hK'_fin h_abs2_meas (2 * C) h_abs2_bdd
    have h_mono : ∀ᵐ x ∂volume.restrict K', |u k x - χ x| * |ψ x| ≤ |u k x - χ x| * C := by
      have h' : ∀ x ∈ K', |u k x - χ x| * |ψ x| ≤ |u k x - χ x| * C := by
        intro x hx
        have h2 : |ψ x| ≤ C := hC x hx
        exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      have h_mem : ∀ᵐ x ∂volume.restrict K', x ∈ K' := by exact ae_restrict_mem hK'_meas
      exact h_mem.mono (fun x hx => h' x hx)
    have h10 : ∫ x in K', |u k x - χ x| * |ψ x| ≤ ∫ x in K', |u k x - χ x| * C :=
      integral_mono_ae h_abs1_int h_abs2_int h_mono
    have h11 : ∫ x in K', |u k x - χ x| * C = C * ∫ x in K', |u k x - χ x| := by
      have h : ∫ x in K', |u k x - χ x| * C = ∫ x in K', C * |u k x - χ x| := by
        apply integral_congr_ae
        filter_upwards with x <;> ring
      rw [h, ←integral_const_mul]
    calc
      |(∫ x, f1 x) - (∫ x, f2 x)|
        ≤ ∫ x, |(u k x - χ x) * ψ x| := h6
      _ = ∫ x in K', |u k x - χ x| * |ψ x| := h7
      _ ≤ ∫ x in K', |u k x - χ x| * C := h10
      _ = C * ∫ x in K', |u k x - χ x| := h11

  -- L¹ convergence on K'
  have h_L1 : Filter.Tendsto (fun k => ∫ x in K', |u k x - χ x|) Filter.atTop (nhds 0) :=
    Mollification.mollify_tendsto_L1 hS hK'_compact

  -- Squeeze
  have h_squeeze : Filter.Tendsto (fun k => |(∫ x, u k x * ψ x) - (∫ x, χ x * ψ x)|) Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun k => C * ∫ x in K', |u k x - χ x|) Filter.atTop (nhds 0) := by
      simpa [mul_zero] using h_L1.const_mul C
    exact squeeze_zero (fun k => abs_nonneg _) h_ineq h
  have h_main : Filter.Tendsto (fun k => ∫ x, u k x * ψ x) Filter.atTop (nhds (∫ x, χ x * ψ x)) := by
    have h_dist : Filter.Tendsto (fun k => dist (∫ x, u k x * ψ x) (∫ x, χ x * ψ x)) Filter.atTop (nhds 0) := by
      have h_eq : (fun k => dist (∫ x, u k x * ψ x) (∫ x, χ x * ψ x)) =
          (fun k => |(∫ x, u k x * ψ x) - (∫ x, χ x * ψ x)|) := by
        funext k
        simp [Real.dist_eq] <;> rfl
      rw [h_eq]
      exact h_squeeze
    exact tendsto_iff_dist_tendsto_zero.mpr h_dist
  rw [h_eq_χ_int] at h_main
  exact h_main

-- ============================================================================
-- Gradient integral convergence (lower semicontinuity + contraction)
-- ============================================================================

/-- Bound: `|∫ u · div φ| ≤ ∫ ‖∇u‖` for smooth compact u and test field φ. -/
lemma gradient_integral_bound
    {u : E n → ℝ} (hu : ContDiff ℝ 1 u) (hsu : HasCompactSupport u)
    (φ : TestVectorField) :
    |∫ x, u x * divergence φ.toFun x| ≤ ∫ x, ‖fderiv ℝ u x‖ := by
  have h_ibp : ∫ x, u x * divergence φ.toFun x = -∫ x, inner ℝ (gradVec u x) (φ.toFun x) :=
    integration_by_parts_smooth hu hsu φ.smooth φ.compact
  rw [h_ibp, abs_neg]
  have h_g_cont : Continuous (gradVec u) := gradVec_continuous hu
  have h_abs_cont : Continuous (fun x : E n => |inner ℝ (gradVec u x) (φ.toFun x)|) :=
    continuous_abs.comp (h_g_cont.inner φ.smooth.continuous)
  have h_norm_cont : Continuous (fun x : E n => ‖fderiv ℝ u x‖) :=
    hu.continuous_fderiv (by norm_num) |>.norm
  have h_abs_supp : HasCompactSupport (fun x : E n => |inner ℝ (gradVec u x) (φ.toFun x)|) := by
    have h5 : Function.support (fun x : E n => inner ℝ (gradVec u x) (φ.toFun x)) ⊆ Function.support (gradVec u) := by
      intro x hx
      by_contra h6
      have h7 : gradVec u x = 0 := by simpa [Function.mem_support] using h6
      have h8 : inner ℝ (gradVec u x) (φ.toFun x) = 0 := by rw [h7]; simp
      exact hx h8
    have h_eq : Function.support (fun x : E n => |inner ℝ (gradVec u x) (φ.toFun x)|) =
        Function.support (fun x : E n => inner ℝ (gradVec u x) (φ.toFun x)) := by
      ext x; simp [Function.mem_support]
    have h_sub : Function.support (fun x : E n => |inner ℝ (gradVec u x) (φ.toFun x)|) ⊆
        Function.support (gradVec u) := by
      rw [h_eq]; exact h5
    exact (gradVec_hasCompactSupport hu hsu).mono h_sub
  have h_norm_supp : HasCompactSupport (fun x : E n => ‖fderiv ℝ u x‖) :=
    hasCompactSupport_norm_iff.mpr (hsu.fderiv ℝ)
  have h_abs_int : Integrable (fun x : E n => |inner ℝ (gradVec u x) (φ.toFun x)|) volume :=
    h_abs_cont.integrable_of_hasCompactSupport h_abs_supp
  have h_norm_int : Integrable (fun x : E n => ‖fderiv ℝ u x‖) volume :=
    h_norm_cont.integrable_of_hasCompactSupport h_norm_supp
  have h1 : ∀ x, |inner ℝ (gradVec u x) (φ.toFun x)| ≤ ‖fderiv ℝ u x‖ := by
    intro x
    have h2 : |inner ℝ (gradVec u x) (φ.toFun x)| ≤ ‖gradVec u x‖ * ‖φ.toFun x‖ :=
      abs_real_inner_le_norm (gradVec u x) (φ.toFun x)
    have h3 : ‖φ.toFun x‖ ≤ 1 := φ.bound x
    have h4 : ‖gradVec u x‖ = ‖fderiv ℝ u x‖ := (fderiv_norm_eq_gradVec_norm u x).symm
    calc
      |inner ℝ (gradVec u x) (φ.toFun x)| ≤ ‖gradVec u x‖ * ‖φ.toFun x‖ := h2
      _ = ‖fderiv ℝ u x‖ * ‖φ.toFun x‖ := by rw [h4]
      _ ≤ ‖fderiv ℝ u x‖ * 1 := by gcongr
      _ = ‖fderiv ℝ u x‖ := by ring
  have h_abs_ineq : |∫ x, inner ℝ (gradVec u x) (φ.toFun x)| ≤
      ∫ x, |inner ℝ (gradVec u x) (φ.toFun x)| := by
    have h_main : ∀ (f : E n → ℝ), |∫ x, f x| ≤ ∫ x, |f x| := by
      intro f
      exact abs_integral_le_integral_abs
    exact h_main (fun x => inner ℝ (gradVec u x) (φ.toFun x))
  have h6 : ∫ x, |inner ℝ (gradVec u x) (φ.toFun x)| ≤ ∫ x, ‖fderiv ℝ u x‖ :=
    integral_mono h_abs_int h_norm_int h1
  exact le_trans h_abs_ineq h6

/-- **Gradient integral convergence**: `∫⁻ ‖∇u_k‖ → P(S)` as `k → ∞`. -/
theorem mollification_gradient_convergence'
    {S : Set (E n)} (hS : MeasurableSet S) (hBdd : Bornology.IsBounded S)
    (hP_lt_top : perimeter S < ⊤)
    (u : ℕ → E n → ℝ) (h_u_eq : u = fun k => Mollification.mollificationSeq hS k) :
    Filter.Tendsto (fun k => ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ (u k) x‖)
      Filter.atTop (nhds (perimeter S)) := by
  let a : ℕ → ENNReal := fun k => ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ (u k) x‖
  have h_u_eq' : ∀ k, u k = Mollification.mollificationSeq hS k := by
    intro k; exact congrFun h_u_eq k

  -- Upper bound: a k ≤ perimeter S
  have h_upper : ∀ k, a k ≤ perimeter S := by
    intro k
    dsimp only [a]
    let u_k := Mollification.mollificationSeq hS k
    have h_eq : u k = u_k := h_u_eq' k
    have h4 : (∫⁻ x, ENNReal.ofReal ‖fderiv ℝ (u k) x‖) = (∫⁻ x, ENNReal.ofReal ‖fderiv ℝ u_k x‖) := by
      apply congr_arg (fun f => ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ f x‖) h_eq
    rw [h4]
    exact mollification_contraction_lintegral hS hBdd k

  have h_upper' : ∀ᶠ n in Filter.atTop, a n ≤ perimeter S :=
    Filter.univ_mem' h_upper
  have h_limsup : Filter.limsup a Filter.atTop ≤ perimeter S :=
    limsup_le_of_le (h := h_upper')

  -- Lower bound: perimeter S ≤ liminf a via lower semicontinuity
  have h_lower : perimeter S ≤ Filter.liminf a Filter.atTop := by
    have h_forall : ∀ (φ : TestVectorField),
        ENNReal.ofReal |∫ x in S, divergence φ.toFun x| ≤ Filter.liminf a Filter.atTop := by
      intro φ
      let ψ := divergence φ.toFun
      have hψ_smooth : ContDiff ℝ ∞ ψ := divergence_smooth φ
      have hψ_support : HasCompactSupport ψ := divergence_hasCompactSupport φ
      have hψ_cont : Continuous ψ := hψ_smooth.continuous

      -- Integral convergence: ∫ u_k · ψ → ∫_S ψ
      have h_int_conv : Filter.Tendsto (fun k => ∫ x, u k x * ψ x) Filter.atTop (nhds (∫ x in S, ψ x)) := by
        have h_eq : (fun k => ∫ x, u k x * ψ x) = (fun k => ∫ x, (Mollification.mollificationSeq hS k) x * ψ x) := by
          funext k
          apply congr_arg (fun f => ∫ x, f x * ψ x) (h_u_eq' k)
        rw [h_eq]
        exact mollification_integral_convergence hS hBdd hψ_cont hψ_support

      -- Bound: |∫ u_k · ψ| ≤ ∫ ‖∇u_k‖
      have h_bound : ∀ k, |∫ x, u k x * ψ x| ≤ ∫ x, ‖fderiv ℝ (u k) x‖ := by
        intro k
        rw [h_u_eq' k]
        exact gradient_integral_bound
          (Mollification.mollify_contDiff hS _ _ |>.of_le (by norm_num))
          (mollification_hasCompactSupport hS hBdd _) φ

      -- Lintegral equality
      have h_eq_lint : ∀ k, a k = ENNReal.ofReal (∫ x, ‖fderiv ℝ (u k) x‖) := by
        intro k
        dsimp only [a]
        let u_k := Mollification.mollificationSeq hS k
        have h_eq : u k = u_k := h_u_eq' k
        have h_smooth : ContDiff ℝ ∞ u_k := Mollification.mollify_contDiff hS _ _
        have h_support : HasCompactSupport u_k := mollification_hasCompactSupport hS hBdd _
        have h_fd_support : HasCompactSupport (fderiv ℝ u_k) := h_support.fderiv ℝ
        have h_fd_cont : Continuous (fderiv ℝ u_k) := h_smooth.continuous_fderiv (by norm_num)
        have h_fd_int : Integrable (fderiv ℝ u_k) volume :=
          h_fd_cont.integrable_of_hasCompactSupport h_fd_support
        have h1 : ENNReal.ofReal (∫ x, ‖fderiv ℝ u_k x‖) = ∫⁻ x, ‖fderiv ℝ u_k x‖ₑ :=
          ofReal_integral_norm_eq_lintegral_enorm h_fd_int
        have h2 : (fun x => ‖fderiv ℝ u_k x‖ₑ) = (fun x => ENNReal.ofReal ‖fderiv ℝ u_k x‖) := by
          funext x; simp [enorm]
        have h3 : ∫⁻ x, ‖fderiv ℝ u_k x‖ₑ = ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ u_k x‖ := by rw [h2]
        have h4 : (∫⁻ x, ENNReal.ofReal ‖fderiv ℝ (u k) x‖) = (∫⁻ x, ENNReal.ofReal ‖fderiv ℝ u_k x‖) := by
          apply congr_arg (fun f => ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ f x‖) h_eq
        have h5 : ENNReal.ofReal (∫ x, ‖fderiv ℝ (u k) x‖) = ENNReal.ofReal (∫ x, ‖fderiv ℝ u_k x‖) := by
          apply congr_arg (fun f => ENNReal.ofReal (∫ x, ‖fderiv ℝ f x‖)) h_eq
        calc
          (∫⁻ x, ENNReal.ofReal ‖fderiv ℝ (u k) x‖)
            = ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ u_k x‖ := h4
          _ = ∫⁻ x, ‖fderiv ℝ u_k x‖ₑ := h3.symm
          _ = ENNReal.ofReal (∫ x, ‖fderiv ℝ u_k x‖) := h1.symm
          _ = ENNReal.ofReal (∫ x, ‖fderiv ℝ (u k) x‖) := h5.symm

      have h_ennreal_bound : ∀ k, ENNReal.ofReal |∫ x, u k x * ψ x| ≤ a k := by
        intro k
        have h10 : |∫ x, u k x * ψ x| ≤ ∫ x, ‖fderiv ℝ (u k) x‖ := h_bound k
        have h11 : ENNReal.ofReal |∫ x, u k x * ψ x| ≤ ENNReal.ofReal (∫ x, ‖fderiv ℝ (u k) x‖) :=
          ENNReal.ofReal_le_ofReal h10
        have h12 : a k = ENNReal.ofReal (∫ x, ‖fderiv ℝ (u k) x‖) := h_eq_lint k
        rw [h12]
        exact h11

      -- Take limit via liminf
      let f : ℕ → ENNReal := fun k => ENNReal.ofReal |∫ x, u k x * ψ x|
      have h_abs_conv : Filter.Tendsto f Filter.atTop
          (nhds (ENNReal.ofReal |∫ x in S, ψ x|)) :=
        (ENNReal.continuous_ofReal.comp continuous_abs).tendsto _ |>.comp h_int_conv
      have h_liminf_f : Filter.liminf f Filter.atTop = ENNReal.ofReal |∫ x in S, ψ x| :=
        h_abs_conv.liminf_eq
      have h_le : Filter.liminf f Filter.atTop ≤ Filter.liminf a Filter.atTop :=
        liminf_le_liminf (Filter.univ_mem' h_ennreal_bound)
      rw [h_liminf_f] at h_le
      exact h_le

    simpa [perimeter] using iSup_le h_forall

  -- Combine liminf and limsup
  have h_liminf_le : Filter.liminf a Filter.atTop ≤ Filter.limsup a Filter.atTop := liminf_le_limsup
  have h_eq_liminf : Filter.liminf a Filter.atTop = perimeter S :=
    le_antisymm (h_liminf_le.trans h_limsup) h_lower
  have h_eq_limsup : Filter.limsup a Filter.atTop = perimeter S :=
    le_antisymm h_limsup (h_lower.trans h_liminf_le)
  exact tendsto_of_liminf_eq_limsup h_eq_liminf h_eq_limsup

-- ============================================================================
-- Global L¹ convergence of mollifications
-- ============================================================================

/-- **Global L¹ convergence of mollifications of characteristic functions.**

For a bounded measurable set `U`, the mollification `u_k = χ_U * ρ_{ε_k}`
converges to `χ_U` in L¹ globally:

`∫ |u_k - χ_U| → 0` as `k → ∞`. -/
lemma mollify_tendsto_L1_global {U : Set (E n)}
    (hU : MeasurableSet U) (hBdd : Bornology.IsBounded U) :
    Filter.Tendsto (fun k : ℕ =>
      ∫ x : E n, |Mollification.mollify (1 / (k + 2 : ℝ)) (by positivity)
        (Set.indicator U (fun _ => (1 : ℝ))) x -
        Set.indicator U (fun _ => (1 : ℝ)) x|)
      atTop (nhds 0) := by
  let χ : E n → ℝ := Set.indicator U (fun _ => (1 : ℝ))
  let u : ℕ → E n → ℝ := fun k =>
    Mollification.mollify (1 / (k + 2 : ℝ)) (by positivity) χ
  let ε_k : ℕ → ℝ := fun k => 1 / (k + 2 : ℝ)

  have hε_le : ∀ k : ℕ, ε_k k ≤ 1 := by
    intro k
    have h : (2 : ℝ) ≤ (k + 2 : ℝ) := by
      have h' : k + 2 ≥ 2 := by linarith
      exact_mod_cast h'
    have h2 : 1 / (k + 2 : ℝ) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith
    exact h2

  let K : Set (E n) := closure (U + ball (0 : E n) 1)
  have h_bdd2 : Bornology.IsBounded (U + ball (0 : E n) 1) :=
    hBdd.add Metric.isBounded_ball
  have hK_compact : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure h_bdd2.closure
  have hK_meas : MeasurableSet K := hK_compact.measurableSet

  have hU_sub_K : U ⊆ K := by
    have h1 : U ⊆ U + ball (0 : E n) 1 := by
      intro x hx
      exact ⟨x, hx, 0, by simp, by simp⟩
    exact subset_trans h1 subset_closure

  have h_u_zero : ∀ k (x : E n), x ∉ U + ball (0 : E n) (ε_k k) → u k x = 0 := by
    intro k x hx
    let ρ : E n → ℝ := Mollification.rho (ε_k k) (by positivity)
    let φ := Mollification.mollifier (n := n) (ε_k k) (by positivity)
    have h_supp_ρ : Function.support ρ = ball (0 : E n) (ε_k k) :=
      φ.support_normed_eq
    have h_main : ∀ (t : E n), ρ t * χ (x - t) = 0 := by
      intro t
      by_cases ht : t ∈ Function.support ρ
      · have h_t_in : t ∈ ball (0 : E n) (ε_k k) := by
          rw [h_supp_ρ] at ht; exact ht
        have h_xt_notin_U : x - t ∉ U := by
          intro h_xt
          have h_contra : x ∈ U + ball (0 : E n) (ε_k k) := by
            exact ⟨x - t, h_xt, t, h_t_in, by abel_nf⟩
          exact hx h_contra
        have h_chi : χ (x - t) = 0 := by simpa [χ] using h_xt_notin_U
        rw [h_chi] <;> ring
      · have hρ : ρ t = 0 := by simpa [Function.mem_support] using ht
        rw [hρ] <;> ring
    have h_conv : u k x = ∫ t : E n, ρ t * χ (x - t) := by rfl
    rw [h_conv]
    have hρ_cont : Continuous ρ := φ.continuous_normed
    have hρ_supp : HasCompactSupport ρ := φ.hasCompactSupport_normed
    have hρ_integrable : Integrable ρ volume :=
      hρ_cont.integrable_of_hasCompactSupport hρ_supp
    have hχ_meas : AEStronglyMeasurable (fun t : E n => χ (x - t)) volume := by
      have h1 : Measurable χ := measurable_const.indicator hU
      have h2 : Continuous (fun t : E n => x - t) := continuous_const.sub continuous_id
      exact (h1.comp h2.measurable).aestronglyMeasurable
    have hχ_bdd : ∀ᵐ t ∂volume, ‖χ (x - t)‖ ≤ 1 := by
      filter_upwards with t
      by_cases h : x - t ∈ U <;> simp [χ, h, norm_norm] <;> norm_num
    have h_integrable : Integrable (fun t : E n => ρ t * χ (x - t)) volume :=
      hρ_integrable.smul_bdd 1 hχ_meas hχ_bdd
    have h_goal : (∫ t : E n, ρ t * χ (x - t)) = 0 := by
      have h_g_eq_zero : (fun t : E n => ρ t * χ (x - t)) = 0 := by
        funext t; exact h_main t
      rw [h_g_eq_zero]
      simp
    exact h_goal

  have h_supp_K : ∀ k, Function.support (u k) ⊆ K := by
    intro k x hx
    have h1 : u k x ≠ 0 := hx
    have h2 : x ∈ U + ball (0 : E n) (ε_k k) := by
      by_contra h3
      exact h1 (h_u_zero k x h3)
    have h3 : U + ball (0 : E n) (ε_k k) ⊆ U + ball (0 : E n) 1 := by
      intro z hz
      rcases hz with ⟨w, hw, y, hy, rfl⟩
      have h4 : y ∈ ball (0 : E n) 1 := by
        have h5 : ‖y‖ < ε_k k := by simpa [Metric.mem_ball] using hy
        have h6 : ‖y‖ < (1 : ℝ) := h5.trans_le (hε_le k)
        simpa [Metric.mem_ball] using h6
      exact ⟨w, hw, y, h4, by abel⟩
    exact subset_closure (h3 h2)

  have h_zero_outside : ∀ k (x : E n), x ∉ K → |u k x - χ x| = 0 := by
    intro k x hxK
    have h1 : u k x = 0 := by
      by_contra h
      exact hxK (h_supp_K k (Function.mem_support.mpr h))
    have h2 : χ x = 0 := by
      by_contra h
      have h3 : x ∈ U := by
        simpa [χ, Set.indicator_apply] using (show (χ x ≠ 0) from h)
      exact hxK (hU_sub_K h3)
    rw [h1, h2] <;> norm_num

  have h_int_eq : ∀ k, (∫ x : E n, |u k x - χ x|) = ∫ x in K, |u k x - χ x| := by
    intro k
    let f : E n → ℝ := fun x => |u k x - χ x|
    have h_cong : f = Set.indicator K f := by
      funext x
      by_cases h : x ∈ K
      · simp [h, Set.indicator_apply]
      · have h5 : f x = 0 := h_zero_outside k x h
        simp [h, h5, Set.indicator_apply]
    have h1 : (∫ x : E n, f x) = ∫ x : E n, (Set.indicator K f) x := by
      exact congr_arg (fun g : E n → ℝ => ∫ x, g x) h_cong
    rw [h1]
    exact integral_indicator hK_meas

  have h_main : Filter.Tendsto (fun k : ℕ => ∫ x in K, |u k x - χ x|) atTop (nhds 0) :=
    Mollification.mollify_tendsto_L1 hU hK_compact

  convert h_main using 1
  funext k
  exact h_int_eq k

end Geometry.Perimeter
