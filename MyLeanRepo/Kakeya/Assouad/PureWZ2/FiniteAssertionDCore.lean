import MyLeanRepo.Kakeya.AssertionD
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement

/-!
# Finite Assertion-D core ABI

This file contains only the data interface between the literal WZ2 frontend
and the finite-set model consumed by Assertion D.  Its separation from the
indexed conversion proof avoids importing unrelated Subunit infrastructure
into the centered rescaling modules.
-/

noncomputable section

namespace Kakeya.Assouad

/--
The finite family and shading needed to invoke `Kakeya.AssertionD`.

Every target tube and shaded set is traced back to the original indexed
family.  No assigned-fiber data occurs in this structure.
-/
structure PureWZ2FiniteAssertionDCore
    {delta assertionEta requestedCardLoss : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (shading : Kakeya.Streamlined.TubeShading family) where
  targetFamily : Kakeya.TubeFamily delta
  source :
    ∀ tube : Kakeya.DeltaTube delta,
      tube ∈ targetFamily → Fin family.card
  targetShading : Kakeya.Shading targetFamily
  target_unit_ball : targetFamily.IsInUnitBall
  target_distinct : targetFamily.IsEssentiallyDistinct
  target_tube_from_source :
    ∀ tube, ∀ membership : tube ∈ targetFamily,
      family.tube (source tube membership) = tube
  target_shading_from_source :
    ∀ tube, ∀ membership : tube ∈ targetFamily,
      targetShading.carrier tube ⊆
        shading.carrier (source tube membership)
  target_dense :
    targetShading.IsLambdaDense
      (Kakeya.realRpowENN delta assertionEta)
  target_katz_tao :
    Kakeya.KatzTaoConvexWolffBound targetFamily
      (Real.rpow delta (-assertionEta))
  target_frostman :
    Kakeya.FrostmanSlabWolffBound targetFamily
      (Real.rpow delta (-assertionEta))
  target_cardinality :
    Kakeya.realRpowENN delta (-2 + requestedCardLoss) ≤
      targetFamily.enncard

namespace PureWZ2FiniteAssertionDCore

/-- The finite target shading is contained in the original indexed shading
union recorded by the core. -/
theorem target_union_subset
    {delta assertionEta requestedCardLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    (core :
      PureWZ2FiniteAssertionDCore
        (assertionEta := assertionEta)
        (requestedCardLoss := requestedCardLoss)
        family shading) :
    core.targetShading.union ⊆ shading.union := by
  rintro point ⟨tube, membership, hpoint⟩
  exact
    ⟨core.source tube membership,
      core.target_shading_from_source
        tube membership hpoint⟩

end PureWZ2FiniteAssertionDCore

end Kakeya.Assouad

end
