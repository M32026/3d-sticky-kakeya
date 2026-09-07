import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Actual affine-triple transport for WZ1 Lemma 49

The paper applies Kaufman's theorem after an anisotropic affine
normalization of the common strip.  The two `G` coordinates use the same
affine map; the `F` coordinate uses the contragredient linear map.  This
preserves every dot-difference value exactly.

The transformed graph is the literal image of the supplied actual triples.
No grid center is substituted for either endpoint.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Inverse-transpose action on the first vertex class. -/
def wz1ContragredientPoint
    (linear : Point2 ≃ₗ[ℝ] Point2) (point : Point2) : Point2 :=
  linear.symm.toLinearMap.adjoint point

/-- Common affine action on the second and third vertex classes. -/
def wz1AffineEndpoint
    (linear : Point2 ≃ₗ[ℝ] Point2)
    (translation point : Point2) : Point2 :=
  linear point + translation

/-- Transport one actual tripartite edge. -/
def wz1AffineTriple
    (linear : Point2 ≃ₗ[ℝ] Point2)
    (translation : Point2)
    (edge : Point2 × Point2 × Point2) :
    Point2 × Point2 × Point2 :=
  (wz1ContragredientPoint linear edge.1,
    wz1AffineEndpoint linear translation edge.2.1,
    wz1AffineEndpoint linear translation edge.2.2)

/--
Transport actual tripartite sets and edges through one strip normalization.

The output support statement retains actual membership.  The source-witness
field prevents a later proof from replacing transformed endpoints by
unrelated grid centers.
-/
def WZ1Lemma49ActualAffineTripleTransportStatement : Prop :=
  ∀ (linear : Point2 ≃ₗ[ℝ] Point2)
    (translation : Point2)
    (F G₁ G₂ : DiscreteSet 2)
    (H : Finset (Point2 × Point2 × Point2)),
      (∀ edge ∈ H,
        edge.1 ∈ F ∧ edge.2.1 ∈ G₁ ∧ edge.2.2 ∈ G₂) →
      let transformedF :=
        F.image (wz1ContragredientPoint linear)
      let transformedG₁ :=
        G₁.image (wz1AffineEndpoint linear translation)
      let transformedG₂ :=
        G₂.image (wz1AffineEndpoint linear translation)
      let transformedH :=
        H.image (wz1AffineTriple linear translation)
      (∀ edge ∈ transformedH,
        edge.1 ∈ transformedF ∧
          edge.2.1 ∈ transformedG₁ ∧
          edge.2.2 ∈ transformedG₂) ∧
      (∀ transformedEdge ∈ transformedH,
        ∃ sourceEdge ∈ H,
          transformedEdge =
            wz1AffineTriple linear translation sourceEdge) ∧
      wz1DotDifferenceSet transformedH =
        wz1DotDifferenceSet H

end Kakeya.Assouad
