import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.RotationTransfer
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.AffinePullback
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.MeasurabilitySetup
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Set-level vanishing lemma for directional surface area

If the i-th gradient component of q vanishes on a measurable set T, then both
directional surface areas vanish: SA(e_i, q, T) = 0 and SA(b_i, p, f '' T) = 0.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real BigOperators

namespace Kakeya.CV

/-- Pointwise: if `inner(v, ∇p(x)) = 0`, then `inner(v, n_p(x)) = 0`. -/
lemma normal_inner_vanishes
    (p : MvPolynomial (Fin 3) ℝ) (v : Point 3) (x : Point 3)
    (hzero : inner ℝ v (polynomialGradient p x) = 0) :
    inner ℝ v (polynomialUnitNormal p x) = 0 := by
  by_cases h : ‖polynomialGradient p x‖ = 0
  · rw [polynomialUnitNormal, dif_pos h]; simp
  · rw [polynomialUnitNormal, dif_neg h]
    rw [inner_smul_right, hzero]; ring

/-- Pointwise: if `(∇q(x))_i = 0`, then `inner(e_i, n_q(x)) = 0`. -/
lemma directional_normal_inner_q_vanishes
    (q : MvPolynomial (Fin 3) ℝ) (i : Fin 3) (x : Point 3)
    (hzero : (polynomialGradient q x) i = 0) :
    inner ℝ (eBasis i) (polynomialUnitNormal q x) = 0 := by
  have h1 : inner ℝ (eBasis i) (polynomialGradient q x) = (polynomialGradient q x) i := by
    simp [eBasis, PiLp.inner_apply]
  have h2 : inner ℝ (eBasis i) (polynomialGradient q x) = 0 := by
    rw [h1, hzero]
  exact normal_inner_vanishes q (eBasis i) x h2

/-- Set-level vanishing lemma for directional surface area. -/
lemma directionalSurfaceArea_vanish_on_isingular
    (p q : MvPolynomial (Fin 3) ℝ)
    (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (z : Point 3) (hη : 0 < η)
    (b : OrthonormalBasis (Fin 3) ℝ (Point 3))
    (ℓ : Fin 3 → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (hA : ∀ i, A (eBasis i) = ℓ i • b i)
    (hpq : ∀ x, polynomialValue p (z + η • A x) = polynomialValue q x)
    (i : Fin 3) (T : Set (Point 3))
    (hTmeas : MeasurableSet T)
    (hT : ∀ x ∈ T, (polynomialGradient q x) i = 0) :
    directionalSurfaceArea (eBasis i) q T = 0 ∧
    directionalSurfaceArea (b i) p ((fun y => z + η • A y) '' T) = 0 := by
  let f : Point 3 → Point 3 := fun y => z + η • A y
  let μ : Measure (Point 3) := MeasureTheory.Measure.hausdorffMeasure 2
  let g : Point 3 → Point 3 := fun y => A.symm (η⁻¹ • (y - z))
  have hgf : ∀ x, g (f x) = x := by
    intro x
    have h1 : g (f x) = A.symm (η⁻¹ • ((z + η • A x) - z)) := by rfl
    rw [h1]
    have h2 : (z + η • A x) - z = η • A x := by abel
    rw [h2]
    have h3 : η⁻¹ • (η • A x) = A x := by
      rw [smul_smul]
      have h4 : η⁻¹ * η = 1 := by field_simp [hη.ne']
      rw [h4, one_smul]
    rw [h3]
    exact A.left_inv x
  have hfg : ∀ y, f (g y) = y := by
    intro y
    have h1 : f (g y) = z + η • A (A.symm (η⁻¹ • (y - z))) := by rfl
    rw [h1]
    have h2 : A (A.symm (η⁻¹ • (y - z))) = η⁻¹ • (y - z) := A.right_inv _
    rw [h2]
    have h3 : η • (η⁻¹ • (y - z)) = y - z := by
      rw [smul_smul]
      have h4 : η * η⁻¹ = 1 := by field_simp [hη.ne']
      rw [h4, one_smul]
    rw [h3]; abel
  have h_image_eq : f '' T = g ⁻¹' T := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [hgf] using hx
    · intro hy
      exact ⟨g y, hy, hfg y⟩
  have hg_cont : Continuous g := by
    have h1 : Continuous (fun y : Point 3 => y - z) := continuous_id.sub continuous_const
    have h2 : Continuous (fun y : Point 3 => η⁻¹ • (y - z)) := h1.const_smul _
    have h3 : Continuous (A.symm : Point 3 → Point 3) := A.symm.toContinuousLinearEquiv.continuous
    exact h3.comp h2
  have hfTmeas : MeasurableSet (f '' T) := by
    rw [h_image_eq]
    exact hTmeas.preimage hg_cont.measurable
  let gq : Point 3 → ENNReal :=
    fun x => ENNReal.ofReal ‖inner ℝ (eBasis i) (polynomialUnitNormal q x)‖
  have hq_meas : Measurable gq := by
    have h1 : Measurable (polynomialUnitNormal q) := measurable_polynomialUnitNormal q
    have h2 : Measurable (fun x => inner ℝ (eBasis i) (polynomialUnitNormal q x)) :=
      measurable_const.inner h1
    exact h2.norm.ennreal_ofReal
  have hq_zero : ∀ x ∈ T, gq x = 0 := by
    intro x hx
    have h1 : inner ℝ (eBasis i) (polynomialUnitNormal q x) = 0 :=
      directional_normal_inner_q_vanishes q i x (hT x hx)
    simp [gq, h1]
  have h_q : directionalSurfaceArea (eBasis i) q T = 0 := by
    rw [directionalSurfaceArea]
    rw [setLIntegral_eq_zero_iff hTmeas hq_meas]
    filter_upwards with x
    intro hx
    exact hq_zero x hx
  let gp : Point 3 → ENNReal :=
    fun y => ENNReal.ofReal ‖inner ℝ (b i) (polynomialUnitNormal p y)‖
  have hp_meas : Measurable gp := by
    have h1 : Measurable (polynomialUnitNormal p) := measurable_polynomialUnitNormal p
    have h2 : Measurable (fun y => inner ℝ (b i) (polynomialUnitNormal p y)) :=
      measurable_const.inner h1
    exact h2.norm.ennreal_ofReal
  have hq_eq : q = pullbackPolynomial p z η A := by
    apply MvPolynomial.funext
    intro v
    let xv : Point 3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm v
    have h_coe : (EuclideanSpace.equiv (Fin 3) ℝ) xv = v :=
      (EuclideanSpace.equiv (Fin 3) ℝ).right_inv v
    have h_coe' : (fun j : Fin 3 => xv j) = v := by
      have h_eq : (EuclideanSpace.equiv (Fin 3) ℝ) xv = (fun j => xv j) := by rfl
      rw [h_eq] at h_coe
      exact h_coe
    have h1 : polynomialValue q xv = polynomialValue (pullbackPolynomial p z η A) xv := by
      rw [pullbackPolynomial_eval, hpq xv]
    simpa [polynomialValue, h_coe'] using h1
  have hp_zero : ∀ y ∈ f '' T, gp y = 0 := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h_grad_rel : polynomialGradient q x =
        η • (A : Point 3 →ₗ[ℝ] Point 3).adjoint (polynomialGradient p (f x)) := by
      have h : polynomialGradient q x = polynomialGradient (pullbackPolynomial p z η A) x := by
        rw [hq_eq]
      rw [h]
      exact pullbackGradient p z η A x
    have h_inner_b : inner ℝ (b i) (polynomialGradient p (f x)) = 0 := by
      have h1 : (polynomialGradient q x) i =
          η * ℓ i * inner ℝ (b i) (polynomialGradient p (f x)) := by
        calc
          (polynomialGradient q x) i
              = inner ℝ (eBasis i) (polynomialGradient q x) := by
                simp [eBasis, PiLp.inner_apply]
          _ = inner ℝ (eBasis i)
                (η • (A : Point 3 →ₗ[ℝ] Point 3).adjoint
                  (polynomialGradient p (f x))) := by
                rw [h_grad_rel]
          _ = η * inner ℝ (eBasis i)
                ((A : Point 3 →ₗ[ℝ] Point 3).adjoint
                  (polynomialGradient p (f x))) := by
                rw [inner_smul_right]
          _ = η * inner ℝ (A (eBasis i)) (polynomialGradient p (f x)) := by
                rw [LinearMap.adjoint_inner_right]; rfl
          _ = η * inner ℝ (ℓ i • b i) (polynomialGradient p (f x)) := by
                rw [hA i]
          _ = η * (ℓ i * inner ℝ (b i) (polynomialGradient p (f x))) := by
                simp [inner_smul_left]
          _ = η * ℓ i * inner ℝ (b i) (polynomialGradient p (f x)) := by ring
      have h5 : (polynomialGradient q x) i = 0 := hT x hx
      have h6 : η * ℓ i * inner ℝ (b i) (polynomialGradient p (f x)) = 0 := by
        rw [←h1, h5]
      have h71 : η ≠ 0 := hη.ne'
      have h72 : ℓ i ≠ 0 := (hℓ i).ne'
      have h73 : η * ℓ i ≠ 0 := mul_ne_zero h71 h72
      exact (mul_eq_zero.mp h6).resolve_left h73
    have h_main : inner ℝ (b i) (polynomialUnitNormal p (f x)) = 0 :=
      normal_inner_vanishes p (b i) (f x) h_inner_b
    simp [gp, h_main]
  have h_p : directionalSurfaceArea (b i) p (f '' T) = 0 := by
    rw [directionalSurfaceArea]
    rw [setLIntegral_eq_zero_iff hfTmeas hp_meas]
    filter_upwards with y
    intro hy
    exact hp_zero y hy
  exact ⟨h_q, h_p⟩

end Kakeya.CV
