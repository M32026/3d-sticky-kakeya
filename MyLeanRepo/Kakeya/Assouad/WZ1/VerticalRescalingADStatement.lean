import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Global AD transport under the Proposition 21 vertical rescaling

This module freezes the first geometric leaf of the final WZ1 Proposition 21
normalization.  It contains only the affine coordinate change, the rescaled
slope, and the horizontal-slice projection identity.  Construction of a new
tube family, extremality transport, and cardinality normalization are separate
later leaves.
-/

noncomputable section

namespace Kakeya.Assouad

/--
The centered coordinate change used for the first Proposition 21 transport.

The vertical slab `c + h * [-1,1]` is sent to `[-1,1]`.  The two horizontal
coordinates are scaled so that the global-grain slope is divided by `M` while
the corresponding scalar projection is uniformly dilated by `M⁻²`.
-/
def wz1VerticalRescalingMap (c h M : ℝ) (p : Point3) : Point3 :=
  point3
    (p (0 : Fin 3) / M ^ 2)
    (p (1 : Fin 3) / M)
    ((p (2 : Fin 3) - c) / h)

/-- The global slope after restricting to `c + h * [-1,1]` and rescaling. -/
def wz1VerticalRescaledSlope
    (g : SlopeFunction) (c h M : ℝ) : SlopeFunction where
  toFun t := g (c + h * t) / M
  contDiff := by
    have hAffine : ContDiff ℝ 2 (fun t : ℝ => c + h * t) :=
      contDiff_const.add (contDiff_const.mul contDiff_id)
    exact (g.contDiff.comp hAffine).div_const M

/--
The global-grain AD statement transported by the centered vertical rescaling.

Besides normalization of the new slope, the conclusion records the exact set
identity
`π_{g(c+h t)/M}(Φ(E)_t) = M⁻² π_{g(c+h t)}(E_{c+h t})`
and the resulting one-dimensional AD estimate at scale `δ / M²`.
-/
def WZ1VerticalRescalingADStatement : Prop :=
  ∀ (g : SlopeFunction) (c h M delta sigma : ℝ) (C : ENNReal),
    0 < h →
    h ≤ 1 →
    1 ≤ M →
    0 < delta →
    0 < sigma →
    sigma < 1 →
    (∀ t ∈ Set.Icc (-1 : ℝ) 1,
      c + h * t ∈ Set.Icc (-1 : ℝ) 1) →
    (∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |g z| ≤ M ∧
        |deriv g z| ≤ M ∧
          |deriv (deriv g) z| ≤ M) →
    ∀ E : Set Point3,
      (∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection (globalGrainDirection (g z))
            (horizontalSlice E z))
          delta (1 - sigma) C) →
      (wz1VerticalRescaledSlope g c h M).IsNormalized ∧
        (∀ t : ℝ,
          scalarProjection
              (globalGrainDirection
                (wz1VerticalRescaledSlope g c h M t))
              (horizontalSlice
                (wz1VerticalRescalingMap c h M '' E) t) =
            (fun u : ℝ => u / M ^ 2) ''
              scalarProjection
                (globalGrainDirection (g (c + h * t)))
                (horizontalSlice E (c + h * t))) ∧
        ∀ t ∈ Set.Icc (-1 : ℝ) 1,
          IsADSet1
            (scalarProjection
              (globalGrainDirection
                (wz1VerticalRescaledSlope g c h M t))
              (horizontalSlice
                (wz1VerticalRescalingMap c h M '' E) t))
            (delta / M ^ 2) (1 - sigma) (10 * C)

end Kakeya.Assouad
