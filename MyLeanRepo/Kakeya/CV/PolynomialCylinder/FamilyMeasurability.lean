import MyLeanRepo.Kakeya.CV.PolynomialMollification
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.MeasurabilitySetup

/-!
# Joint measurability for polynomial parameter families

Polynomial evaluation, gradient, and unit normal are jointly measurable in
the polynomial coefficient and ambient point variables.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real Classical

namespace Kakeya.CV

variable {k : ℕ} {P : PolynomialParameterization k}

/-- Joint continuity of coefficient-dependent polynomial evaluation. -/
lemma family_polynomialValue_continuous :
    Continuous (fun p : (CoefficientSpace P.dim) × Point 3 =>
      polynomialValue (parameterPolynomial P p.1) p.2) := by
  let Coeff := CoefficientSpace P.dim
  let b : Module.Basis (Fin P.dim) ℝ Coeff :=
    PiLp.basisFun 2 ℝ (Fin P.dim)
  let polys : Fin P.dim → MvPolynomial (Fin 3) ℝ :=
    fun i => parameterPolynomial P (b i)
  have h_expand : ∀ x : Coeff,
      parameterPolynomial P x =
        ∑ i : Fin P.dim, (b.repr x) i • polys i := by
    intro x
    have h1 :
        (∑ i : Fin P.dim, (b.repr x) i • b i) = x :=
      b.sum_repr x
    have h2 :
        (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k)
            (∑ i : Fin P.dim, (b.repr x) i • b i) =
          ∑ i : Fin P.dim, (b.repr x) i •
            (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k) (b i) := by
      rw [map_sum (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k)]
      apply Finset.sum_congr rfl
      intro i _
      exact map_smul
        (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k)
        ((b.repr x) i) (b i)
    have h3 :
        (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k) x =
          ∑ i : Fin P.dim, (b.repr x) i •
            (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k) (b i) := by
      calc
        (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k) x =
            (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k)
              (∑ i : Fin P.dim, (b.repr x) i • b i) := by
                rw [h1]
        _ = ∑ i : Fin P.dim, (b.repr x) i •
              (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k) (b i) :=
          h2
    simpa [polys, parameterPolynomial] using
      congr_arg
        (fun p : degreeLESubmodule k =>
          (p : MvPolynomial (Fin 3) ℝ)) h3
  have h_main_eq : ∀ (x : Coeff) (z : Point 3),
      polynomialValue (parameterPolynomial P x) z =
        ∑ i : Fin P.dim,
          (b.repr x) i * polynomialValue (polys i) z := by
    intro x z
    rw [h_expand x]
    have h9 : ∀ q : MvPolynomial (Fin 3) ℝ,
        polynomialValue q z = MvPolynomial.eval z q :=
      fun _ => rfl
    rw [h9, MvPolynomial.eval_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h_smul :
        MvPolynomial.eval z ((b.repr x) i • polys i) =
          (b.repr x) i * MvPolynomial.eval z (polys i) := by
      simpa [smul_eq_mul] using
        map_smul (MvPolynomial.eval z) ((b.repr x) i) (polys i)
    rw [h_smul, ← h9 (polys i)]
  have h_final :
      (fun p : Coeff × Point 3 =>
        polynomialValue (parameterPolynomial P p.1) p.2) =
      fun p : Coeff × Point 3 =>
        ∑ i : Fin P.dim,
          (b.repr p.1) i * polynomialValue (polys i) p.2 := by
    funext p
    exact h_main_eq p.1 p.2
  rw [h_final]
  have h_ind : ∀ s : Finset (Fin P.dim),
      Continuous (fun p : Coeff × Point 3 =>
        ∑ i ∈ s,
          (b.repr p.1) i * polynomialValue (polys i) p.2) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using continuous_const
    | @insert i s hi ih =>
      have hi' : Continuous (fun p : Coeff × Point 3 =>
          (b.repr p.1) i * polynomialValue (polys i) p.2) := by
        have h1 :
            Continuous (fun p : Coeff × Point 3 =>
              (b.repr p.1) i) :=
          ((continuous_apply i).comp b.continuous_coe_repr).comp
            continuous_fst
        have h2 :
            Continuous (fun p : Coeff × Point 3 =>
              polynomialValue (polys i) p.2) :=
          (polynomialValue_continuous (polys i)).comp continuous_snd
        exact h1.mul h2
      convert hi'.add ih using 1
      funext p
      rw [Finset.sum_insert hi]
      rfl
  exact h_ind Finset.univ

/-- Joint continuity of the coefficient-dependent polynomial gradient. -/
lemma family_polynomialGradient_continuous :
    Continuous (fun p : (CoefficientSpace P.dim) × Point 3 =>
      polynomialGradient (parameterPolynomial P p.1) p.2) := by
  let Coeff := CoefficientSpace P.dim
  let b : Module.Basis (Fin P.dim) ℝ Coeff :=
    PiLp.basisFun 2 ℝ (Fin P.dim)
  let polys : Fin P.dim → MvPolynomial (Fin 3) ℝ :=
    fun i => parameterPolynomial P (b i)
  have h_expand : ∀ x : Coeff,
      parameterPolynomial P x =
        ∑ i : Fin P.dim, (b.repr x) i • polys i := by
    intro x
    have h1 :
        (∑ i : Fin P.dim, (b.repr x) i • b i) = x :=
      b.sum_repr x
    have h2 :
        (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k)
            (∑ i : Fin P.dim, (b.repr x) i • b i) =
          ∑ i : Fin P.dim, (b.repr x) i •
            (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k) (b i) := by
      rw [map_sum (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k)]
      apply Finset.sum_congr rfl
      intro i _
      exact map_smul
        (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k)
        ((b.repr x) i) (b i)
    have h3 :
        (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k) x =
          ∑ i : Fin P.dim, (b.repr x) i •
            (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k) (b i) := by
      calc
        (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k) x =
            (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k)
              (∑ i : Fin P.dim, (b.repr x) i • b i) := by
                rw [h1]
        _ = ∑ i : Fin P.dim, (b.repr x) i •
              (P.equiv : Coeff →ₗ[ℝ] degreeLESubmodule k) (b i) :=
          h2
    simpa [polys, parameterPolynomial] using
      congr_arg
        (fun p : degreeLESubmodule k =>
          (p : MvPolynomial (Fin 3) ℝ)) h3
  have h_grad_expand : ∀ (x : Coeff) (z : Point 3),
      polynomialGradient (parameterPolynomial P x) z =
        ∑ i : Fin P.dim,
          (b.repr x) i • polynomialGradient (polys i) z := by
    intro x z
    rw [h_expand x]
    ext j
    have h_sum :
        polynomialValue
            (MvPolynomial.pderiv j
              (∑ i : Fin P.dim, (b.repr x) i • polys i)) z =
          ∑ i : Fin P.dim, (b.repr x) i *
            polynomialValue (MvPolynomial.pderiv j (polys i)) z := by
      have h_pderiv_sum :
          MvPolynomial.pderiv j
              (∑ i : Fin P.dim, (b.repr x) i • polys i) =
            ∑ i : Fin P.dim,
              (b.repr x) i • MvPolynomial.pderiv j (polys i) := by
        rw [map_sum (MvPolynomial.pderiv j)]
        apply Finset.sum_congr rfl
        intro i _
        exact (MvPolynomial.pderiv j).map_smul
          ((b.repr x) i) (polys i)
      rw [h_pderiv_sum]
      have h9 : ∀ q : MvPolynomial (Fin 3) ℝ,
          polynomialValue q z = MvPolynomial.eval z q :=
        fun _ => rfl
      rw [h9, MvPolynomial.eval_sum]
      apply Finset.sum_congr rfl
      intro i _
      have h_smul :
          MvPolynomial.eval z
              ((b.repr x) i • MvPolynomial.pderiv j (polys i)) =
            (b.repr x) i *
              MvPolynomial.eval z (MvPolynomial.pderiv j (polys i)) := by
        simpa [smul_eq_mul] using
          map_smul (MvPolynomial.eval z) ((b.repr x) i)
            (MvPolynomial.pderiv j (polys i))
      rw [h_smul, ← h9 (MvPolynomial.pderiv j (polys i))]
    simpa [polynomialGradient] using h_sum
  have h_main :
      (fun p : Coeff × Point 3 =>
        polynomialGradient (parameterPolynomial P p.1) p.2) =
      fun p =>
        ∑ i : Fin P.dim,
          (b.repr p.1) i • polynomialGradient (polys i) p.2 := by
    funext p
    exact h_grad_expand p.1 p.2
  rw [h_main]
  have h_ind : ∀ s : Finset (Fin P.dim),
      Continuous (fun p : Coeff × Point 3 =>
        ∑ i ∈ s,
          (b.repr p.1) i • polynomialGradient (polys i) p.2) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using continuous_const
    | @insert i s hi ih =>
      have hi' : Continuous (fun p : Coeff × Point 3 =>
          (b.repr p.1) i • polynomialGradient (polys i) p.2) := by
        have h1 :
            Continuous (fun p : Coeff × Point 3 =>
              (b.repr p.1) i) :=
          ((continuous_apply i).comp b.continuous_coe_repr).comp
            continuous_fst
        have h2 :
            Continuous (fun p : Coeff × Point 3 =>
              polynomialGradient (polys i) p.2) :=
          (polynomialGradient_continuous (polys i)).comp continuous_snd
        exact h1.smul h2
      convert hi'.add ih using 1
      funext p
      rw [Finset.sum_insert hi]
      rfl
  exact h_ind Finset.univ

/-- Joint measurability of the coefficient-dependent polynomial unit normal. -/
lemma family_polynomialUnitNormal_measurable :
    Measurable (fun p : (CoefficientSpace P.dim) × Point 3 =>
      polynomialUnitNormal (parameterPolynomial P p.1) p.2) := by
  let Coeff := CoefficientSpace P.dim
  have hgrad : Measurable (fun p : Coeff × Point 3 =>
      polynomialGradient (parameterPolynomial P p.1) p.2) :=
    family_polynomialGradient_continuous.measurable
  have hnorm : Measurable (fun p : Coeff × Point 3 =>
      ‖polynomialGradient (parameterPolynomial P p.1) p.2‖) :=
    hgrad.norm
  have hzero : MeasurableSet {p : Coeff × Point 3 |
      ‖polynomialGradient (parameterPolynomial P p.1) p.2‖ = 0} :=
    hnorm (MeasurableSet.singleton 0)
  have hzeroMap :
      Measurable (fun _ : Coeff × Point 3 => (0 : Point 3)) :=
    measurable_const
  have hinv : Measurable (fun p : Coeff × Point 3 =>
      ‖polynomialGradient (parameterPolynomial P p.1) p.2‖⁻¹) :=
    hnorm.inv
  have hnormalized : Measurable (fun p : Coeff × Point 3 =>
      ‖polynomialGradient (parameterPolynomial P p.1) p.2‖⁻¹ •
        polynomialGradient (parameterPolynomial P p.1) p.2) :=
    hinv.smul hgrad
  exact Measurable.ite hzero hzeroMap hnormalized

end Kakeya.CV
