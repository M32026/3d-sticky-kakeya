import MyLeanRepo.Kakeya.CV.Statements
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Measurability setup for the polynomial cylinder estimate

Establishes measurability of the polynomial zero set, gradient, unit normal,
affine line, unit tube, and the directional surface area integrand.

## Whiteprint node: measurability-setup
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

variable {n : ℕ}

lemma polynomialValue_continuous (p : MvPolynomial (Fin n) ℝ) :
    Continuous (polynomialValue p) := by
  have hpi : Continuous (fun (x : Point n) => (fun i : Fin n => x i)) :=
    PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)
  have h : Continuous (fun x : Point n => MvPolynomial.eval (fun i => x i) p) :=
    (MvPolynomial.continuous_eval p).comp hpi
  have h_eq : (fun x : Point n => MvPolynomial.eval (fun i => x i) p) = polynomialValue p := by
    funext x
    simp [polynomialValue]
  rw [← h_eq]
  exact h

lemma isClosed_polynomialZeroSet (p : MvPolynomial (Fin n) ℝ) :
    IsClosed (polynomialZeroSet p) :=
  isClosed_eq (polynomialValue_continuous p) continuous_const

lemma measurableSet_polynomialZeroSet (p : MvPolynomial (Fin n) ℝ) :
    MeasurableSet (polynomialZeroSet p) :=
  (isClosed_polynomialZeroSet p).measurableSet

lemma polynomialGradient_continuous (p : MvPolynomial (Fin n) ℝ) :
    Continuous (polynomialGradient p) := by
  have hcomp : Continuous (fun x : Point n => (fun i : Fin n =>
      polynomialValue (MvPolynomial.pderiv i p) x)) :=
    continuous_pi (fun i => polynomialValue_continuous (MvPolynomial.pderiv i p))
  have hequiv : Continuous ((EuclideanSpace.equiv (Fin n) ℝ).symm) :=
    ContinuousLinearEquiv.continuous (EuclideanSpace.equiv (Fin n) ℝ).symm
  have h : Continuous (fun x : Point n =>
      (EuclideanSpace.equiv (Fin n) ℝ).symm
        (fun i => polynomialValue (MvPolynomial.pderiv i p) x)) :=
    hequiv.comp hcomp
  have h_eq : (fun x : Point n => (EuclideanSpace.equiv (Fin n) ℝ).symm
        (fun i => polynomialValue (MvPolynomial.pderiv i p) x)) =
      polynomialGradient p := by
    funext x
    rfl
  rw [← h_eq]
  exact h

lemma measurable_polynomialUnitNormal (p : MvPolynomial (Fin n) ℝ) :
    Measurable (polynomialUnitNormal p) := by
  have hgrad : Measurable (polynomialGradient p) :=
    (polynomialGradient_continuous p).measurable
  have h1 : Measurable (fun x : Point n => ‖polynomialGradient p x‖) :=
    hgrad.norm
  have h2 : MeasurableSet {x : Point n | ‖polynomialGradient p x‖ = 0} :=
    h1 (MeasurableSet.singleton 0)
  have h3 : Measurable (fun x : Point n => (0 : Point n)) := measurable_const
  have hinv : Measurable (fun x : Point n => ‖polynomialGradient p x‖⁻¹) := h1.inv
  have h4 : Measurable (fun x : Point n => ‖polynomialGradient p x‖⁻¹ • polynomialGradient p x) :=
    hinv.smul hgrad
  exact Measurable.ite h2 h3 h4

lemma isClosed_affineLine (a e : Point n) : IsClosed (affineLine a e) := by
  let s : AffineSubspace ℝ (Point n) := AffineSubspace.mk' a (ℝ ∙ e)
  have h : (affineLine a e) = (s : Set (Point n)) := by
    ext x
    simp only [affineLine, Set.mem_setOf_eq]
    have h1 : x ∈ s ↔ ∃ (t : ℝ), t • e = x -ᵥ a := by
      simp [s, Submodule.mem_span_singleton, AffineSubspace.mem_mk'] <;> rfl
    constructor
    · rintro ⟨t, rfl⟩
      have h2 : (a + t • e) -ᵥ a = t • e := by
        simp [vsub_eq_sub, vadd_eq_add] <;> abel
      simpa [s, Submodule.mem_span_singleton, AffineSubspace.mem_mk'] using ⟨t, h2⟩
    · rintro h
      have h2 : ∃ (t : ℝ), t • e = x -ᵥ a := (h1).mp h
      rcases h2 with ⟨t, ht⟩
      have hvec : x -ᵥ a = t • e := ht.symm
      have h_eq : x = a +ᵥ (t • e) := by
        have h : a +ᵥ (x -ᵥ a) = x := by
          simp [vsub_eq_sub, vadd_eq_add]
        have h2 : a +ᵥ (t • e) = a +ᵥ (x -ᵥ a) := by rw [hvec]
        rw [h] at h2
        exact h2.symm
      exact ⟨t, h_eq⟩
  rw [h]
  exact AffineSubspace.closed_of_finiteDimensional s

lemma isClosed_unitTube (a e : Point n) : IsClosed (unitTube a e) := by
  have h : Continuous (fun x : Point n => infDist x (affineLine a e)) :=
    Metric.continuous_infDist_pt (affineLine a e)
  exact isClosed_le h continuous_const

lemma measurableSet_unitTube (a e : Point n) :
    MeasurableSet (unitTube a e) :=
  (isClosed_unitTube a e).measurableSet

lemma measurable_directionalSurfaceArea_integrand (e : Point 3)
    (p : MvPolynomial (Fin 3) ℝ) :
    Measurable fun x : Point 3 =>
      ENNReal.ofReal ‖inner ℝ e (polynomialUnitNormal p x)‖ := by
  have h1 : Measurable (polynomialUnitNormal p) := measurable_polynomialUnitNormal p
  have h2 : Measurable (fun x : Point 3 => inner ℝ e (polynomialUnitNormal p x)) :=
    measurable_const.inner h1
  have h3 : Measurable (fun x : Point 3 => ‖inner ℝ e (polynomialUnitNormal p x)‖) :=
    h2.norm
  exact h3.ennreal_ofReal

end Kakeya.CV
