import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerParentCoarseBounds
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGlobalMultiplicityHelpers

/-!
# Global multiplicity band for the owner-parent selection

Since the selected coarse shading has point multiplicity at most one, every
fine tube active at a fixed point has the same parent.  Thus the global fine
multiplicity is exactly the multiplicity in the fiber of any active tube.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private lemma point_mem_union_of_pointMultiplicity_pos
    {bodyFamily : Kakeya.Streamlined.BodyFamily}
    (shading : Kakeya.Streamlined.Shading bodyFamily)
    {point : Point3}
    (hpos : 0 < shading.pointMultiplicity point) :
    point ∈ shading.union := by
  rw [Kakeya.Streamlined.Shading.pointMultiplicity] at hpos
  rcases Finset.card_pos.mp hpos with ⟨index, hindex⟩
  exact ⟨index, (Finset.mem_filter.mp hindex).2⟩

namespace WZ2PaperOwnerParentSelectedData

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {support : PureWZ2PositiveCallerSupportData quotient}
    {coordinateCount : ℕ}
    {regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount}
    {merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized}
    {scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    {sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled}
    {scaleSeparation : 18 * delta ≤ callerRequested.1}
    {balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation}
    {owner :
      WZ2PaperDirectOwnerPreparationData
        balancing.balanced.finalData.producer}
    (data : WZ2PaperOwnerParentSelectedData owner outputConstant)

/-- At an active point, all active fine tubes lie in the fiber of any chosen
active tube.  This is the exact global-to-unique-fiber counting identity. -/
theorem finalFineShading_pointMultiplicity_eq_fiberPointMultiplicity
    (source : Fin data.selectedFine.family.card)
    (point : Point3)
    (hsource : point ∈ data.finalFineShading.carrier source) :
    data.finalFineShading.pointMultiplicity point =
      data.internalCover.toWZ1PaperTubeCover.fiberPointMultiplicity
        data.finalFineShading (data.internalCover.parent source) point := by
  let coarseAtPoint : Finset (Fin data.selectedPacked.family.card) :=
    Finset.univ.filter fun parent =>
      point ∈ data.finalCoarseShading.carrier parent
  have hsourceParent : data.internalCover.parent source ∈ coarseAtPoint := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, data.publicBalanced.point_compatibility
        source (data.internalCover.parent source)
        (data.internalCover.parent_covers source) point hsource⟩
  have hcoarseCard : coarseAtPoint.card ≤ 1 := by
    exact_mod_cast data.coarse_pointMultiplicity_le_one point
  unfold Kakeya.Streamlined.Shading.pointMultiplicity
  unfold WZ1PaperTubeCover.fiberPointMultiplicity
  congr 1
  ext other
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hother
    refine ⟨?_, hother⟩
    have hotherParent : data.internalCover.parent other ∈ coarseAtPoint := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, data.publicBalanced.point_compatibility
          other (data.internalCover.parent other)
          (data.internalCover.parent_covers other) point hother⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Finset.card_le_one.mp hcoarseCard _ hotherParent _ hsourceParent⟩
  · exact fun h => h.2

/-- The final fine shading inherits the owner's dyadic multiplicity band
globally, because at each active point exactly one parent fiber contributes. -/
theorem finalFineShading_constantMultiplicity :
    data.finalFineShading.HasConstantMultiplicity
      (2 ^ balancing.balanced.finalData.producer.fiberBand.level)
      (2 * 2 ^ balancing.balanced.finalData.producer.fiberBand.level) := by
  intro point hpoint
  rcases hpoint with ⟨source, hsource⟩
  let parent := data.internalCover.parent source
  let ownerShading :=
    restrictPaperShading
      (owner.exactified.restrictedCover.fullFiberSubfamily
        (data.selectedPacked.embedding parent))
      owner.exactified.refined
  have heq :
      data.finalFineShading.pointMultiplicity point =
        data.internalCover.toWZ1PaperTubeCover.fiberPointMultiplicity
          data.finalFineShading parent point :=
    data.finalFineShading_pointMultiplicity_eq_fiberPointMultiplicity
      source point hsource
  have hglobalOwnerEq :
      data.finalFineShading.pointMultiplicity point =
        ownerShading.pointMultiplicity point := by
    calc
      data.finalFineShading.pointMultiplicity point =
          data.internalCover.toWZ1PaperTubeCover.fiberPointMultiplicity
            data.finalFineShading parent point := heq
      _ = (restrictPaperShading
            (data.internalCover.fullFiberSubfamily parent)
            data.finalFineShading).pointMultiplicity point := by
          symm
          exact data.internalCover.restrict_fullFiber_pointMultiplicity_eq
            data.finalFineShading parent point
      _ = ownerShading.pointMultiplicity point := by
          exact data.balancedPullback.pullback.full_fiber_pointMultiplicity_eq
            parent point
  have hglobalPos : 0 < data.finalFineShading.pointMultiplicity point := by
    unfold Kakeya.Streamlined.Shading.pointMultiplicity
    exact Finset.card_pos.mpr
      ⟨source, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsource⟩⟩
  have hownerPos : 0 < ownerShading.pointMultiplicity point := by
    rwa [← hglobalOwnerEq]
  have hownerMem : point ∈ ownerShading.union := by
    unfold ownerShading at hownerPos ⊢
    exact point_mem_union_of_pointMultiplicity_pos _ hownerPos
  have hlocal := owner.fiber_multiplicity_band
    (data.selectedPacked.embedding parent) point hownerMem
  norm_cast at hlocal
  rw [hglobalOwnerEq]
  constructor
  · simpa only [ownerShading] using hlocal.1
  · simpa only [ownerShading, pow_succ, mul_comm] using hlocal.2.le

end WZ2PaperOwnerParentSelectedData

end Kakeya.Assouad

end
