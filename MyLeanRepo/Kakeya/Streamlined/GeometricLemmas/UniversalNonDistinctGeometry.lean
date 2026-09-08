import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.RigidMotionNormalizationSelection.GeneralizedCollision
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.RigidMotionNormalizationSelection.GeometryHelpers
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslateContainment

/-!
# Translation-normalized geometry of non-essentially-distinct tubes

The existing local theorem gives universal transverse, direction, and
containment bounds after both tube midpoints have norm at most three.  That
normalization is not a genuine support hypothesis: non-essential
distinctness forces the carriers to intersect, so after translating both
tubes by the negative midpoint of the second tube, its midpoint is zero and
the first midpoint has norm at most `1 + 2 * rho`.

This interface freezes the support-free consequence.  The dilation constant
remains the universal constant `1000`; it must not be replaced by a constant
depending on an ambient fixed-ball radius.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/--
Non-essentially-distinct radius-`rho` tubes satisfy the same local geometry
and `1000`-dilated containment without any global midpoint or support
assumption.
-/
def UniversalNonDistinctGeometryStatement : Prop :=
  ∀ {rho : ℝ}, 0 < rho → rho ≤ 1 →
    ∀ T₁ T₂ : Kakeya.DeltaTube rho,
      ¬ T₁.EssentiallyDistinct T₂ →
      ‖(GeometricLemmas.tubeMidpoint T₁ -
            GeometricLemmas.tubeMidpoint T₂) -
          inner ℝ
              (GeometricLemmas.tubeMidpoint T₁ -
                GeometricLemmas.tubeMidpoint T₂)
              T₂.direction • T₂.direction‖ ≤
          1000 * rho ∧
        (‖T₁.direction - T₂.direction‖ ≤ 1000 * rho ∨
          ‖T₁.direction + T₂.direction‖ ≤ 1000 * rho) ∧
        T₁.carrier ⊆ dilatedTubeCarrier 1000 T₂

end Kakeya.Streamlined
