import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.AffinePullback
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.GraphAreaFderiv
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Singular set transfer under affine pullback

This module proves that the gradient-zero condition and the negligible singular
set property transfer under affine pullback of polynomials.

Main results:
- `gradientCLM_zero_iff`: equivalence of CLM gradient zero and polynomial gradient zero
- `pullback_gradient_zero`: gradient zero iff under affine pullback
- `hasNegligibleSingularSet_pullback`: `HasNegligibleSingularSet` transfers under affine pullback
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal Real BigOperators

namespace Kakeya.CV

/-- `gradientCLM p x = 0` iff `polynomialGradient p x = 0`. -/
lemma gradientCLM_zero_iff (p : MvPolynomial (Fin 3) ℝ) (x : Point 3) :
    gradientCLM p x = 0 ↔ polynomialGradient p x = 0 := by
  constructor
  · intro h
    have h1 : (gradientCLM p x) (polynomialGradient p x) = 0 := by
      rw [h]
      simp
    simpa [gradientCLM, inner_self_eq_zero] using h1
  · intro h
    ext w
    simp [gradientCLM, h]

/-- The pullback polynomial has zero gradient iff the original does, because the
affine map has invertible Jacobian. -/
lemma pullback_gradient_zero (p : MvPolynomial (Fin 3) ℝ) (z : Point 3) (η : ℝ)
    (hη : 0 < η) (A : Point 3 ≃ₗ[ℝ] Point 3) (y : Point 3) :
    polynomialGradient (pullbackPolynomial p z η A) y = 0 ↔
      polynomialGradient p (z + η • A y) = 0 := by
  let q := pullbackPolynomial p z η A
  let f : Point 3 → Point 3 := fun y => z + η • A y
  let h_lin : Point 3 →L[ℝ] Point 3 :=
    ((η : ℝ) • A.toLinearMap).toContinuousLinearMap
  have hf_inj : Function.Injective h_lin := by
    intro x1 x2 h
    have h1 : η • A x1 = η • A x2 := h
    have h2 : A x1 = A x2 := by
      simpa [smul_eq_zero, hη.ne'] using h1
    exact A.injective h2
  have hf_surj : Function.Surjective h_lin :=
    LinearMap.injective_iff_surjective.mp hf_inj
  have h_main : HasFDerivAt (fun x => polynomialValue p x)
      (gradientCLM p (f y)) (f y) := polynomialValue_fderiv p (f y)
  have h_fderiv : HasFDerivAt f h_lin y := by
    have h1 : HasFDerivAt (fun x => h_lin x) h_lin y := h_lin.hasFDerivAt
    have h2 : HasFDerivAt (fun (_ : Point 3) => z) (0 : Point 3 →L[ℝ] Point 3) y :=
      hasFDerivAt_const (𝕜 := ℝ) z y
    have h4 := h1.add h2
    have h5 : (fun x : Point 3 => h_lin x) + (fun (_ : Point 3) => z) = f := by
      funext x
      simp [f, h_lin]
      abel
    have h6 : h_lin + (0 : Point 3 →L[ℝ] Point 3) = h_lin := by simp
    rw [h5, h6] at h4
    exact h4
  have h_chain : HasFDerivAt (fun y => polynomialValue p (f y))
      ((gradientCLM p (f y)).comp h_lin) y :=
    h_main.comp y h_fderiv
  have h_eq1 : (fun y => polynomialValue p (f y)) = (fun y => polynomialValue q y) := by
    funext y
    exact (pullbackPolynomial_eval p z η A y).symm
  rw [h_eq1] at h_chain
  have h_q_fderiv : HasFDerivAt (fun y => polynomialValue q y)
      (gradientCLM q y) y := polynomialValue_fderiv q y
  have h_unique : (gradientCLM p (f y)).comp h_lin = gradientCLM q y :=
    h_chain.unique h_q_fderiv
  have h_iff : gradientCLM q y = 0 ↔ gradientCLM p (f y) = 0 := by
    rw [← h_unique]
    constructor
    · intro h
      have h_comp : (gradientCLM p (f y)).comp h_lin = 0 := h
      ext x
      rcases hf_surj x with ⟨w, rfl⟩
      have h4 : ((gradientCLM p (f y)).comp h_lin) w = 0 := by
        rw [h_comp]
        simp
      exact h4
    · intro h
      rw [h]
      simp
  have h1 : gradientCLM q y = 0 ↔ polynomialGradient q y = 0 :=
    gradientCLM_zero_iff q y
  have h2 : gradientCLM p (f y) = 0 ↔ polynomialGradient p (f y) = 0 :=
    gradientCLM_zero_iff p (f y)
  rw [← h1, h_iff, h2]

/-- `HasNegligibleSingularSet` transfers under affine pullback. -/
lemma hasNegligibleSingularSet_pullback (p : MvPolynomial (Fin 3) ℝ) (z : Point 3)
    (η : ℝ) (hη : 0 < η) (A : Point 3 ≃ₗ[ℝ] Point 3)
    (h : HasNegligibleSingularSet p) :
    HasNegligibleSingularSet (pullbackPolynomial p z η A) := by
  let q := pullbackPolynomial p z η A
  let f : Point 3 → Point 3 := fun y => z + η • A y
  let g_inv : Point 3 → Point 3 := fun x => η⁻¹ • A.symm (x - z)
  have hf_inv : ∀ x, g_inv (f x) = x := by
    intro x
    simp [g_inv, f, map_smul, hη.ne']
  have hfg_inv : ∀ x, f (g_inv x) = x := by
    intro x
    simp [f, g_inv, map_smul, hη.ne']
  have h_sing_eq : polynomialSingularSet q = g_inv '' polynomialSingularSet p := by
    ext y
    simp only [polynomialSingularSet, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hval, hgrad⟩
      have hval2 : polynomialValue p (f y) = 0 := by
        rw [← pullbackPolynomial_eval p z η A y]
        exact hval
      have hgrad2 : polynomialGradient p (f y) = 0 :=
        (pullback_gradient_zero p z η hη A y).mp hgrad
      refine ⟨f y, ⟨hval2, hgrad2⟩, ?_⟩
      exact hf_inv y
    · rintro ⟨x, hx, rfl⟩
      have h3 : f (g_inv x) = x := hfg_inv x
      have hval2 : polynomialValue q (g_inv x) = 0 := by
        have h4 : polynomialValue p (f (g_inv x)) = 0 := by
          rw [h3]
          exact hx.1
        rw [pullbackPolynomial_eval p z η A (g_inv x)]
        exact h4
      have hgrad2 : polynomialGradient q (g_inv x) = 0 := by
        have h5 : polynomialGradient p (f (g_inv x)) = 0 := by
          rw [h3]
          exact hx.2
        exact (pullback_gradient_zero p z η hη A (g_inv x)).mpr h5
      exact ⟨hval2, hgrad2⟩
  let A_clm : Point 3 →L[ℝ] Point 3 := A.symm.toLinearMap.toContinuousLinearMap
  let K1 : NNReal := ‖A_clm‖₊
  let K2 : NNReal := NNReal.mk (|η⁻¹|) (abs_nonneg _)
  let K3 : NNReal := 1
  let K : NNReal := K2 * K1 * K3
  have h_smul_lip : LipschitzWith K2 (fun x : Point 3 => η⁻¹ • x) := by
    have h : ∀ (x y : Point 3), ‖η⁻¹ • x - η⁻¹ • y‖ ≤ (K2 : ℝ) * ‖x - y‖ := by
      intro x y
      have h4 : ‖η⁻¹ • x - η⁻¹ • y‖ = |η⁻¹| * ‖x - y‖ := by
        have h5 : η⁻¹ • x - η⁻¹ • y = η⁻¹ • (x - y) := by
          simp [smul_sub]
        rw [h5]
        have h6 : ‖η⁻¹ • (x - y)‖ = ‖(η⁻¹ : ℝ)‖ * ‖x - y‖ := norm_smul _ _
        rw [h6]
        have h7 : ‖(η⁻¹ : ℝ)‖ = |η⁻¹| := Real.norm_eq_abs η⁻¹
        rw [h7]
      rw [h4]
      rfl
    exact LipschitzWith.of_dist_le_mul fun x y => h x y
  have h1 : LipschitzWith K1 A_clm := A_clm.lipschitz
  have h_trans_lip : LipschitzWith K3 (fun x : Point 3 => x - z) := by
    intro x y
    simp [K3]
  have h_lip : LipschitzWith K (g_inv) := by
    have h4 : LipschitzWith (K2 * K1) (fun x => η⁻¹ • A_clm x) := h_smul_lip.comp h1
    have h5 : LipschitzWith K (fun x => η⁻¹ • A_clm (x - z)) := h4.comp h_trans_lip
    simpa [g_inv, A_clm] using h5
  have h_main : codimensionOneMeasure 3 (g_inv '' polynomialSingularSet p) = 0 := by
    have h_dim : codimensionOneMeasure 3 = μH[(2 : ℝ)] := by
      funext s
      simp only [codimensionOneMeasure]
      norm_num
    rw [h_dim]
    have h_bound : μH[(2 : ℝ)] (g_inv '' polynomialSingularSet p) ≤
        (K : ENNReal) ^ (2 : ℝ) * μH[(2 : ℝ)] (polynomialSingularSet p) :=
      h_lip.hausdorffMeasure_image_le (by norm_num) (polynomialSingularSet p)
    have h_zero : μH[(2 : ℝ)] (polynomialSingularSet p) = 0 := by
      have h9 : codimensionOneMeasure 3 (polynomialSingularSet p) = 0 := h
      have h10 : codimensionOneMeasure 3 = μH[(2 : ℝ)] := by
        funext s
        simp only [codimensionOneMeasure]
        norm_num
      have h11 := congr_fun h10 (polynomialSingularSet p)
      rw [h11] at h9
      exact h9
    rw [h_zero] at h_bound
    simpa using h_bound
  have h_goal : codimensionOneMeasure 3 (polynomialSingularSet q) = 0 := by
    rw [h_sing_eq]
    exact h_main
  exact h_goal

end Kakeya.CV
