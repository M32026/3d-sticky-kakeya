import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.RigidMotion
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Directional anti-concentration for random quaternion rotations

This is the missing rotation component of the Appendix-A rigid-motion
collision estimate.  The output is a probability measure on the unit
quaternion sphere together with a measurable family of genuine linear
isometries of `Point3`.  For every pair of fixed unit directions, the
probability of landing in either antipodal Euclidean cap of radius `alpha` is
`O(alpha^2)`.

The antipodal formulation matches unoriented tube axes.  Translation
anti-concentration is a separate closed result.
-/

noncomputable section

open MeasureTheory Metric

namespace Kakeya.Streamlined.GeneralizedFrostman

def QuaternionDirectionalAntiConcentrationStatement : Prop :=
  ∃ μ : Measure (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
    IsProbabilityMeasure μ ∧
    ∃ rotation :
        sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 →
          (Point3 ≃ₗᵢ[ℝ] Point3),
      (∀ u : Point3, Measurable fun q => rotation q u) ∧
      ∃ C : ENNReal, 1 ≤ C ∧ C ≠ ⊤ ∧
        ∀ u v : Point3,
          ‖u‖ = 1 →
          ‖v‖ = 1 →
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 →
            μ {q |
                ‖rotation q u - v‖ ≤ alpha ∨
                ‖rotation q u + v‖ ≤ alpha} ≤
              C * ENNReal.ofReal (alpha ^ 2)

end Kakeya.Streamlined.GeneralizedFrostman
