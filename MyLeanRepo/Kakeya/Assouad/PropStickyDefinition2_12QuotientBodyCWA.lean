import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12BodyUniformCover

/-!
# Actual-John CWA for a quotient parent fiber

Inside one coarse parent, the fine actual-John bodies are grouped by their
middle parent.  If the grouping is surjective, carrier-faithful, and has
uniform fibers, the middle actual-John bodies inherit CWA by the generic
BodyFamily uniform-cover theorem.

This module freezes only the finite indexed boundary.  Construction of the
public ordinary quotient cover remains a separate geometric theorem.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Finite actual-body grouping data inside one coarse parent. -/
structure WZ2PaperPureQuotientBodyCoverData
    (sourceBodies targetBodies : Kakeya.Streamlined.BodyFamily)
    (K : ENNReal) where
  parent : Fin sourceBodies.card → Fin targetBodies.card
  parent_surjective : Function.Surjective parent
  carrier_contained :
    ∀ source,
      (sourceBodies.body source).carrier ⊆
        (targetBodies.body (parent source)).carrier
  fiber_uniform :
    ∀ first second,
      ((Finset.univ.filter fun source =>
        parent source = first).card : ENNReal) ≤
        K *
          ((Finset.univ.filter fun source =>
            parent source = second).card : ENNReal)

namespace WZ2PaperPureQuotientBodyCoverData

/-- Apply actual BodyFamily uniform-cover transfer to one quotient parent. -/
theorem convexWolff
    {sourceBodies targetBodies : Kakeya.Streamlined.BodyFamily}
    {K C : ENNReal}
    (data :
      WZ2PaperPureQuotientBodyCoverData
        sourceBodies targetBodies K)
    (hsource :
      WZ2PaperBodyConvexWolffBound sourceBodies C) :
    WZ2PaperBodyConvexWolffBound targetBodies (K * C) :=
  wz2PaperBodyConvexWolffBound_of_uniform_cover
    data.parent data.parent_surjective data.carrier_contained
    K C data.fiber_uniform hsource

end WZ2PaperPureQuotientBodyCoverData

/--
One public quotient scale whose parentwise actual-John data is obtained from
ambient fine-scale actual-John data by uniform body grouping.
-/
structure WZ2PaperPureQuotientScaleInputs
    {rho sigma : ℝ}
    {middle : Kakeya.Streamlined.TubeFamily rho}
    {coarse : Kakeya.Streamlined.TubeFamily sigma}
    (middleCoarseCover :
      WZ2PaperPurePartitioningCover middle coarse)
    (coverConstant bodyConstant sourceCWAConstant : ENNReal) where
  delta_pos : 0 < rho
  sigma_pos : 0 < sigma
  middle_full_fiber_uniform :
    WZ2PaperPureFullFibersAreCUniform
      middle coarse coverConstant
  normalization :
    ∀ parent : Fin coarse.card,
      WZ2PaperAssouadUnitRescalingData (coarse.tube parent)
  sourceBodies :
    ∀ parent : Fin coarse.card,
      Kakeya.Streamlined.BodyFamily
  source_cwa :
    ∀ parent,
      WZ2PaperBodyConvexWolffBound
        (sourceBodies parent) sourceCWAConstant
  bodyCover :
    ∀ parent,
      WZ2PaperPureQuotientBodyCoverData
        (sourceBodies parent)
        (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := middle) (coarse := coarse)
          parent (normalization parent))
        bodyConstant

/-- Assemble pure scale data once the public quotient cover and parentwise
actual-body grouping inputs have been constructed. -/
noncomputable def WZ2PaperPureQuotientScaleInputs.toPureScaleData
    {rho sigma : ℝ}
    {middle : Kakeya.Streamlined.TubeFamily rho}
    {coarse : Kakeya.Streamlined.TubeFamily sigma}
    {middleCoarseCover :
      WZ2PaperPurePartitioningCover middle coarse}
    {coverConstant bodyConstant sourceCWAConstant : ENNReal}
    (data :
      WZ2PaperPureQuotientScaleInputs
        middleCoarseCover coverConstant bodyConstant
          sourceCWAConstant) :
    WZ2PaperPureScaleCoverData
      middle sigma
      (max coverConstant
        (bodyConstant * sourceCWAConstant)) where
  delta_pos := data.delta_pos
  rho_pos := data.sigma_pos
  coarse := coarse
  cover := middleCoarseCover
  full_fiber_uniform first second :=
    (data.middle_full_fiber_uniform first second).trans <| by
      gcongr
      exact le_max_left _ _
  rescaledFiber parent :=
    ⟨{
      normalization := data.normalization parent
      convex_wolff := fun convexSet hconvex =>
        ((data.bodyCover parent).convexWolff
          (data.source_cwa parent) convexSet hconvex).trans <| by
            gcongr
            exact le_max_right coverConstant
              (bodyConstant * sourceCWAConstant)
    }⟩

end Kakeya.Assouad

end
