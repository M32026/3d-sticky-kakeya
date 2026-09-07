import MyLeanRepo.Kakeya.CV.Mollification
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Concrete bounded-degree polynomial mollification

This file connects the generic coefficient-space averaging API to actual
three-variable polynomials of bounded total degree.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.CV

/-- Real polynomials in three variables with total degree at most `k`. -/
def degreeLESubmodule (k : ℕ) :
    Submodule ℝ (MvPolynomial (Fin 3) ℝ) where
  carrier := {p | p.totalDegree ≤ k}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    exact (MvPolynomial.totalDegree_add p q).trans (max_le hp hq)
  smul_mem' := by
    intro c p hp
    exact (MvPolynomial.totalDegree_smul_le c p).trans hp

/-- A linear coordinate model for bounded-degree polynomials. -/
structure PolynomialParameterization (k : ℕ) where
  dim : ℕ
  equiv : CoefficientSpace dim ≃ₗ[ℝ] degreeLESubmodule k

/-- Decode coefficient coordinates into a polynomial. -/
def parameterPolynomial {k : ℕ} (P : PolynomialParameterization k)
    (x : CoefficientSpace P.dim) : MvPolynomial (Fin 3) ℝ :=
  (P.equiv x).1

/-- Unit coefficient sphere of normalized bounded-degree polynomials. -/
def normalizedPolynomialParameters {k : ℕ} (P : PolynomialParameterization k) :
    Set (CoefficientSpace P.dim) :=
  Metric.sphere 0 1

/-- Antipodal map on normalized polynomial parameters. -/
def normalizedParameterAntipodal {k : ℕ} (P : PolynomialParameterization k)
    (x : normalizedPolynomialParameters P) :
    normalizedPolynomialParameters P :=
  ⟨-x.1, by simpa [normalizedPolynomialParameters, Metric.mem_sphere] using x.2⟩

/-- The closed unit cube centered at `c`, with side length one. -/
def unitCube (c : Point 3) : Set (Point 3) :=
  {x | ∀ i : Fin 3, |x i - c i| ≤ 1 / 2}

/-- The closed unit cube is measurable. -/
lemma unitCube_measurableSet (c : Point 3) : MeasurableSet (unitCube c) := by
  apply IsClosed.measurableSet
  rw [show unitCube c = ⋂ i : Fin 3, {x : Point 3 | |x i - c i| ≤ 1 / 2} by
    ext x
    simp [unitCube]]
  exact isClosed_iInter (fun i => isClosed_le (by fun_prop) continuous_const)

/-- The closed unit cube lies in the closed unit ball about its center. -/
lemma unitCube_subset_closedBall (c : Point 3) :
    unitCube c ⊆ Metric.closedBall c 1 := by
  intro x hx
  have hcoord : ∀ i : Fin 3, |x i - c i| ≤ 1 / 2 := hx
  have hsq : ‖x - c‖ ^ 2 = ∑ i : Fin 3, (x i - c i) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq (x - c)
  have hsum : ∑ i : Fin 3, (x i - c i) ^ 2 ≤ 3 / 4 := by
    calc
      ∑ i : Fin 3, (x i - c i) ^ 2
          ≤ ∑ _i : Fin 3, (1 / 2 : ℝ) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            have hi := abs_le.mp (hcoord i)
            nlinarith
      _ = 3 / 4 := by norm_num
  have hnorm : ‖x - c‖ ≤ 1 := by
    have hnorm_nonneg : 0 ≤ ‖x - c‖ := norm_nonneg _
    nlinarith [hsq, hsum]
  simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm

/-- Real-valued regular directional area as a coefficient-space function. -/
def coefficientSurfaceFunctional {k : ℕ} (P : PolynomialParameterization k)
    (u : Point 3) (U : Set (Point 3)) (x : CoefficientSpace P.dim) : ℝ :=
  (directionalSurfaceArea u (parameterPolynomial P x)
    (polynomialZeroSet (parameterPolynomial P x) ∩ U)).toReal

/-- Mollified directional area centered at polynomial coordinates `x`. -/
def concreteMollifiedDirectionalArea {k : ℕ} (P : PolynomialParameterization k)
    (ε : ℝ) (x : CoefficientSpace P.dim) (u : Point 3)
    (U : Set (Point 3)) : ℝ :=
  ballAverage ε (coefficientSurfaceFunctional P u U) x

/-- Concrete mollified visibility body. -/
def concreteMollifiedVisibilityBody {k : ℕ} (P : PolynomialParameterization k)
    (ε : ℝ) (x : CoefficientSpace P.dim) (U : Set (Point 3)) :
    Set (Point 3) :=
  unitBall 3 ∩ {u | concreteMollifiedDirectionalArea P ε x u U ≤ 1}

/-- Concrete mollified visibility. -/
def concreteMollifiedVisibility {k : ℕ} (P : PolynomialParameterization k)
    (ε : ℝ) (x : CoefficientSpace P.dim) (U : Set (Point 3)) : ℝ :=
  Real.rpow (volume (concreteMollifiedVisibilityBody P ε x U)).toReal
    (-1 / 3 : ℝ)

/-- Parameters whose concrete mollified visibility is at most `M`. -/
def concretePolynomialBadSet {k : ℕ} (P : PolynomialParameterization k)
    (ε : ℝ) (U : Set (Point 3)) (M : ℝ) : Set (CoefficientSpace P.dim) :=
  {x | concreteMollifiedVisibility P ε x U ≤ M}

/-- The `r`-th dyadic layer inside a concrete polynomial bad set. -/
def concretePolynomialBadLayer {k : ℕ} (P : PolynomialParameterization k)
    (ε : ℝ) (U : Set (Point 3)) (M : ℝ) (r : ℕ) :
    Set (CoefficientSpace P.dim) :=
  {x |
    Real.rpow 2 (-(r : ℝ) - 1) * M <
        concreteMollifiedVisibility P ε x U ∧
      concreteMollifiedVisibility P ε x U ≤
        Real.rpow 2 (-(r : ℝ)) * M}

/-- Parameters on which the positive polynomial sign dominates in a selected region. -/
def positiveSignClass {k : ℕ} (P : PolynomialParameterization k)
    (selectedRegion : CoefficientSpace P.dim → Set (Point 3))
    (D : Set (CoefficientSpace P.dim)) : Set (CoefficientSpace P.dim) :=
  {x | x ∈ D ∧
    volume (selectedRegion x ∩ {y | 0 < polynomialValue (parameterPolynomial P x) y}) >
      volume (selectedRegion x ∩ {y | polynomialValue (parameterPolynomial P x) y < 0})}

end Kakeya.CV
