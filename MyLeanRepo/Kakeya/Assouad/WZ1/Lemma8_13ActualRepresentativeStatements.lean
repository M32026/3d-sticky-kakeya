import MyLeanRepo.Kakeya.Assouad.WZ1.FrostmanCoarsening
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFinalStatements

/-!
# Actual representatives after Lemma 48 coarsening

The normalized `F`-class used by PDF Lemma 8.13 must consist of actual affine
images.  Grid-cell centers are useful for balancing and Frostman estimates,
but substituting them into the final graph would destroy the exact affine
dot-difference identity.

This interface selects a constant-density family of actual representatives
from the balanced cells and refines the literal graph on those points.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/--
The actual first-coordinate output of the Lemma 48 coarsening step.

The explicit constant `16200 * logarithmicLoss * sourceConstant` records:

* the `100 * logarithmicLoss` constant in `WZ1FrostmanCoarseningData`;
* at most `81` nearby coarse cells per separated representative; and
* the factor `2` from enlarging a radius-`r` ball to radius `2 * r`.

The graph remains a literal subgraph of the supplied affine graph.
-/
structure WZ1Lemma8_13ActualRepresentativeData
    {F G₁ G₂ : DiscreteSet 2}
    {fineScale coarseScale sourceConstant : ℝ}
    (coarsening :
      WZ1FrostmanCoarseningData
        F fineScale coarseScale 1
          (ENNReal.ofReal sourceConstant))
    (density : ENNReal)
    (H : Finset (Point2 × Point2 × Point2)) where
  normalizedF : DiscreteSet 2
  normalizedF_subset : normalizedF ⊆ coarsening.selected
  normalizedF_nonempty : normalizedF.Nonempty
  normalizedF_ball : normalizedF.IsInUnitBall
  normalizedF_separated :
    normalizedF.IsDeltaSeparated coarseScale
  constant : ℝ
  constant_eq :
    constant =
      16200 * coarsening.logarithmicLoss * sourceConstant
  constant_nonneg : 0 ≤ constant
  normalizedF_frostman :
    normalizedF.IsFrostman coarseScale 1
      (ENNReal.ofReal constant)
  normalizedH : Finset (Point2 × Point2 × Point2)
  normalizedH_subset : normalizedH ⊆ H
  normalizedUniform :
    WZ1UniformTripleDensity (density / 16)
      normalizedF G₁ G₂ normalizedH

/--
Select actual affine representatives from balanced coarse cells and refine
the literal graph.

Every retained source point is required to occur as an actual first
coordinate of `H`.  This is the paper's preliminary replacement by the active
coordinate projection, made explicit rather than inferred for unused ambient
vertices.
-/
def WZ1Lemma8_13ActualRepresentativeSelectionStatement : Prop :=
  ∀ {F G₁ G₂ : DiscreteSet 2}
    {fineScale coarseScale sourceConstant : ℝ}
    (hcoarseScale : 0 < coarseScale)
    (hcoarseScaleOne : coarseScale ≤ 1)
    (hsourceConstant : 1 ≤ sourceConstant)
    (hFball : F.IsInUnitBall)
    (coarsening :
      WZ1FrostmanCoarseningData
        F fineScale coarseScale 1
          (ENNReal.ofReal sourceConstant))
    {density : ENNReal}
    (hdensity : 0 < density)
    {H : Finset (Point2 × Point2 × Point2)}
    (hUniform :
      WZ1UniformTripleDensity density F G₁ G₂ H)
    (hselectedActive :
      ∀ point ∈ coarsening.selected,
        ∃ edge ∈ H, edge.1 = point)
    (hRefine : WZ1TripartiteHypergraphRefinementStatement),
      Nonempty
        (WZ1Lemma8_13ActualRepresentativeData
          (G₁ := G₁) (G₂ := G₂)
          coarsening density H)

end Kakeya.Assouad
