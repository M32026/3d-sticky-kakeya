import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.GraphAreaFderiv
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Affine pullback of polynomials

Defines the pullback of a polynomial under an affine map `y ↦ z + η • A y`
and proves the gradient chain rule.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators RealInnerProductSpace

namespace Kakeya.CV

/-- Pullback of a polynomial under an affine map `y ↦ z + η • A y`. -/
def pullbackPolynomial (p : MvPolynomial (Fin 3) ℝ) (z : Point 3)
    (η : ℝ) (A : Point 3 ≃ₗ[ℝ] Point 3) :
    MvPolynomial (Fin 3) ℝ :=
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  MvPolynomial.bind₁
    (fun j : Fin 3 =>
      MvPolynomial.C (z j) + MvPolynomial.C η *
        LinearMap.toMvPolynomial b b (A : Point 3 →ₗ[ℝ] Point 3) j)
    p

/-- Evaluation property of the pullback polynomial. -/
lemma pullbackPolynomial_eval (p : MvPolynomial (Fin 3) ℝ) (z : Point 3)
    (η : ℝ) (A : Point 3 ≃ₗ[ℝ] Point 3) (y : Point 3) :
    polynomialValue (pullbackPolynomial p z η A) y =
      polynomialValue p (z + η • A y) := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let M := LinearMap.toMatrix b b (A : Point 3 →ₗ[ℝ] Point 3)
  let g : Fin 3 → MvPolynomial (Fin 3) ℝ := fun j =>
    MvPolynomial.C (z j) + MvPolynomial.C η * M.toMvPolynomial j
  have h_def : pullbackPolynomial p z η A = MvPolynomial.bind₁ g p := by
    rfl
  have h1 : ∀ j : Fin 3,
      MvPolynomial.eval (fun i => y i) (g j) = (z + η • A y) j := by
    intro j
    simp only [g, MvPolynomial.eval_add, MvPolynomial.eval_C,
      MvPolynomial.eval_mul]
    have h2 :
        MvPolynomial.eval (fun i => y i) (M.toMvPolynomial j) =
          (A y) j := by
      rw [Matrix.toMvPolynomial_eval_eq_apply]
      have hmat :
          Matrix.mulVec M (fun i => y i) = fun j => (A y) j := by
        have h :
            Matrix.mulVec M (b.repr y) = b.repr (A y) :=
          LinearMap.toMatrix_mulVec_repr b b A y
        have hrepr : b.repr y = (fun i => y i) := by
          ext i
          simp [b, EuclideanSpace.basisFun_repr]
        have hrepr2 : b.repr (A y) = (fun j => (A y) j) := by
          ext j
          simp [b, EuclideanSpace.basisFun_repr]
        rw [hrepr, hrepr2] at h
        exact h
      rw [hmat]
    rw [h2]
    have h_eq : z j + η * (A y) j = (z + η • A y) j := by
      simp [Pi.add_apply, Pi.smul_apply]
    exact h_eq
  have h3 :
      MvPolynomial.eval (fun i => y i) (pullbackPolynomial p z η A) =
        MvPolynomial.eval
          (fun j => MvPolynomial.eval (fun i => y i) (g j)) p := by
    rw [h_def]
    exact MvPolynomial.aeval_bind₁ (fun i => y i) g p
  have h4 :
      (fun j : Fin 3 => MvPolynomial.eval (fun i => y i) (g j)) =
        fun j : Fin 3 => (z + η • A y) j := by
    funext j
    exact h1 j
  have h5 :
      polynomialValue (pullbackPolynomial p z η A) y =
        MvPolynomial.eval (fun i => y i) (pullbackPolynomial p z η A) := by
    rfl
  rw [h5, h3, h4]
  rfl

/-- Gradient transformation under affine pullback:
`∇(p ∘ f)(y) = η • A.adjoint (∇p(f(y)))`. -/
lemma pullbackGradient (p : MvPolynomial (Fin 3) ℝ) (z : Point 3) (η : ℝ)
    (A : Point 3 ≃ₗ[ℝ] Point 3) (y : Point 3) :
    polynomialGradient (pullbackPolynomial p z η A) y =
      η • (A : Point 3 →ₗ[ℝ] Point 3).adjoint
        (polynomialGradient p (z + η • A y)) := by
  let q := pullbackPolynomial p z η A
  let f : Point 3 → Point 3 := fun y => z + η • A y
  let h_lin : Point 3 →L[ℝ] Point 3 :=
    ((η : ℝ) • (A : Point 3 →ₗ[ℝ] Point 3)).toContinuousLinearMap
  have h_main :
      HasFDerivAt (fun x => polynomialValue p x)
        (gradientCLM p (f y)) (f y) :=
    polynomialValue_fderiv p (f y)
  have h_fderiv : HasFDerivAt f h_lin y := by
    have h1 :
        HasFDerivAt (fun x => h_lin x) h_lin y :=
      h_lin.hasFDerivAt
    have h2 :
        HasFDerivAt (fun (_ : Point 3) => z)
          (0 : Point 3 →L[ℝ] Point 3) y :=
      hasFDerivAt_const (𝕜 := ℝ) z y
    have h4 := h1.add h2
    have h5 :
        (fun x : Point 3 => h_lin x) + (fun (_ : Point 3) => z) = f := by
      funext x
      simp [f, h_lin]
      abel
    have h6 : h_lin + (0 : Point 3 →L[ℝ] Point 3) = h_lin := by
      simp
    rw [h5, h6] at h4
    exact h4
  have h_chain :
      HasFDerivAt (fun y => polynomialValue p (f y))
        ((gradientCLM p (f y)).comp h_lin) y :=
    h_main.comp y h_fderiv
  have h_eq1 :
      (fun y => polynomialValue p (f y)) =
        fun y => polynomialValue q y := by
    funext y
    exact (pullbackPolynomial_eval p z η A y).symm
  rw [h_eq1] at h_chain
  have h_q_fderiv :
      HasFDerivAt (fun y => polynomialValue q y)
        (gradientCLM q y) y :=
    polynomialValue_fderiv q y
  have h_unique :
      (gradientCLM p (f y)).comp h_lin = gradientCLM q y :=
    h_chain.unique h_q_fderiv
  have h_ext : ∀ w : Point 3,
      inner ℝ (polynomialGradient q y) w =
        inner ℝ
          (η • (A : Point 3 →ₗ[ℝ] Point 3).adjoint
            (polynomialGradient p (f y))) w := by
    intro w
    have h1 :
        (gradientCLM q y) w =
          ((gradientCLM p (f y)).comp h_lin) w :=
      congr_arg (fun F : Point 3 →L[ℝ] ℝ => F w) h_unique.symm
    have h2 :
        (gradientCLM q y) w =
          inner ℝ (polynomialGradient q y) w := by
      rfl
    have h3 :
        ((gradientCLM p (f y)).comp h_lin) w =
          inner ℝ (polynomialGradient p (f y)) (h_lin w) := by
      rfl
    have h4 :
        h_lin w = η • (A : Point 3 →ₗ[ℝ] Point 3) w := by
      simp [h_lin]
    have h5 :
        inner ℝ (polynomialGradient p (f y)) (h_lin w) =
          η * inner ℝ (polynomialGradient p (f y))
            ((A : Point 3 →ₗ[ℝ] Point 3) w) := by
      rw [h4, inner_smul_right]
    have h6 :
        η * inner ℝ (polynomialGradient p (f y))
            ((A : Point 3 →ₗ[ℝ] Point 3) w) =
          η * inner ℝ
            ((A : Point 3 →ₗ[ℝ] Point 3).adjoint
              (polynomialGradient p (f y))) w := by
      rw [LinearMap.adjoint_inner_left]
    have h7 :
        inner ℝ
            (η • (A : Point 3 →ₗ[ℝ] Point 3).adjoint
              (polynomialGradient p (f y))) w =
          η * inner ℝ
            ((A : Point 3 →ₗ[ℝ] Point 3).adjoint
              (polynomialGradient p (f y))) w := by
      rw [inner_smul_left]
      simp
    calc
      inner ℝ (polynomialGradient q y) w
          = (gradientCLM q y) w := h2.symm
      _ = ((gradientCLM p (f y)).comp h_lin) w := h1
      _ = inner ℝ (polynomialGradient p (f y)) (h_lin w) := h3
      _ = η * inner ℝ (polynomialGradient p (f y))
          ((A : Point 3 →ₗ[ℝ] Point 3) w) := h5
      _ = η * inner ℝ
          ((A : Point 3 →ₗ[ℝ] Point 3).adjoint
            (polynomialGradient p (f y))) w := h6
      _ = inner ℝ
          (η • (A : Point 3 →ₗ[ℝ] Point 3).adjoint
            (polynomialGradient p (f y))) w := h7.symm
  let v :=
    polynomialGradient q y -
      η • (A : Point 3 →ₗ[ℝ] Point 3).adjoint
        (polynomialGradient p (f y))
  have hv : ∀ w : Point 3, inner ℝ v w = 0 := by
    intro w
    have h_sub :
        inner ℝ v w =
          inner ℝ (polynomialGradient q y) w -
            inner ℝ
              (η • (A : Point 3 →ₗ[ℝ] Point 3).adjoint
                (polynomialGradient p (f y))) w := by
      rw [inner_sub_left]
    rw [h_sub, h_ext w]
    ring
  have h_self : inner ℝ v v = 0 := hv v
  have h_norm2 : inner ℝ v v = ‖v‖ ^ 2 :=
    inner_self_eq_norm_sq_to_K v
  have h_norm0 : ‖v‖ = 0 := by
    rw [h_norm2] at h_self
    have h_nonneg : 0 ≤ ‖v‖ := norm_nonneg _
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h_norm0)

end Kakeya.CV
