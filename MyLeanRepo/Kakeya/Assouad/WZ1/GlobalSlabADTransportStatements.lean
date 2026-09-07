import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions

/-!
# Global-slab AD transport boundaries

Two paper-faithful leaves used by the WZ1 Proposition 9 global-planiness
producer.

The first removes the small vertical component of a unit projection normal on
one `delta`-height slab.  The second records stability of one-dimensional AD
control under a bounded affine change followed by a `delta`-thickening.
Together they formalize the passage from the rescaled local-grain projection
in WZ1 Section 4 to the horizontal global-grain direction `(1,f(z),0)`.
-/

namespace Kakeya.Assouad

/--
Horizontalize a projection normal on one thin horizontal slab.

If `normal₀` is bounded away from zero and `normal₂` is small, then on a
`delta`-height slab the projection onto
`(1, normal₁ / normal₀, 0)` lies in the `delta`-thickening of an affine image
of the projection onto `normal`.
-/
def WZ1HorizontalizeSlabProjectionStatement : Prop :=
  ∀ (E : Set Point3) (normal : Point3) (z delta : ℝ),
    0 < delta →
    ‖normal‖ = 1 →
    (1 : ℝ) / 3 ≤ |normal (0 : Fin 3)| →
    |normal (2 : Fin 3)| ≤ (1 : ℝ) / 10 →
    (∀ p ∈ E,
      p (2 : Fin 3) ∈ Set.Icc (z - delta) (z + delta)) →
      scalarProjection
          (globalGrainDirection
            (normal (1 : Fin 3) / normal (0 : Fin 3))) E ⊆
        Metric.cthickening delta
          ((fun u : ℝ =>
              u / normal (0 : Fin 3) -
                normal (2 : Fin 3) * z / normal (0 : Fin 3)) ''
            scalarProjection normal E)

/--
One-dimensional AD control is stable under a uniformly nondegenerate affine
map and one base-scale thickening.

The target boundedness premise is explicit because `IsADSet1` includes the
repository-normalized ambient interval `[-4,4]`.
-/
def WZ1ADAffineThickeningTransportStatement : Prop :=
  ∀ (E A : Set ℝ) (delta alpha a b : ℝ) (C : ENNReal),
    0 < delta →
    delta ≤ 1 →
    0 < alpha →
    alpha ≤ 1 →
    (1 : ℝ) / 4 ≤ |a| →
    |a| ≤ 4 →
    IsADSet1 E delta alpha C →
    A ⊆ Set.Icc (-4 : ℝ) 4 →
    A ⊆ Metric.cthickening delta ((fun u : ℝ => a * u + b) '' E) →
      IsADSet1 A delta alpha (100000 * C)

end Kakeya.Assouad
