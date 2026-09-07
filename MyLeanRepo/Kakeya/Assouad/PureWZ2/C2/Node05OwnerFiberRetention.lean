import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05OwnerExactMultiplicity

/-!
# Parentwise retention for the owner exact-multiplicity truncation

The owner coarse shading has point multiplicity at most one.  Consequently,
all old fine sources through a point have the same parent.  Since exact
cellwise truncation preserves the full fine union and only deletes source-cell
incidences, it preserves the union after restriction to every parent fiber.
The old factor-two multiplicity band and the new exact multiplicity then give
the parentwise factor-two indexed-mass retention.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

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
    {scales : Fin coordinateCount → WZ2PaperRequestedScale delta}
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

/-- Two old fine sources meeting at one point have the same owner parent. -/
private theorem parent_eq_of_mem_finalFineShading
    (first second : Fin data.selectedFine.family.card)
    (point : Point3)
    (hfirst : point ∈ data.finalFineShading.carrier first)
    (hsecond : point ∈ data.finalFineShading.carrier second) :
    data.internalCover.parent first = data.internalCover.parent second := by
  let coarseAtPoint : Finset (Fin data.selectedPacked.family.card) :=
    Finset.univ.filter fun parent =>
      point ∈ data.finalCoarseShading.carrier parent
  have hcard : coarseAtPoint.card ≤ 1 := by
    exact_mod_cast data.coarse_pointMultiplicity_le_one point
  have hfirstParent : data.internalCover.parent first ∈ coarseAtPoint := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, data.publicBalanced.point_compatibility
        first (data.internalCover.parent first)
        (data.internalCover.parent_covers first) point hfirst⟩
  have hsecondParent : data.internalCover.parent second ∈ coarseAtPoint := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, data.publicBalanced.point_compatibility
        second (data.internalCover.parent second)
        (data.internalCover.parent_covers second) point hsecond⟩
  exact Finset.card_le_one.mp hcard _ hfirstParent _ hsecondParent

/-- Restricting the old owner shading and its exact truncation to a fixed
parent gives exactly the same shaded union. -/
theorem toExactMultiplicityData_restrict_fullFiber_union_eq
    (parent : Fin data.selectedPacked.family.card) :
    (restrictPaperShading
        (data.internalCover.fullFiberSubfamily parent)
        data.toExactMultiplicityData.truncation.truncated).union =
      (restrictPaperShading
        (data.internalCover.fullFiberSubfamily parent)
        data.finalFineShading).union := by
  apply Set.Subset.antisymm
  · rintro point ⟨source, hpoint⟩
    exact ⟨source,
      data.toExactMultiplicityData.truncation.subshading
        ((data.internalCover.fullFiberSubfamily parent).embedding source)
        hpoint⟩
  · rintro point ⟨oldSource, holdPoint⟩
    have holdAmbient :
        point ∈ data.finalFineShading.carrier
          ((data.internalCover.fullFiberSubfamily parent).embedding oldSource) :=
      holdPoint
    have hpointOldUnion : point ∈ data.finalFineShading.union :=
      ⟨(data.internalCover.fullFiberSubfamily parent).embedding oldSource,
        holdAmbient⟩
    have hpointNewUnion :
        point ∈ data.toExactMultiplicityData.truncation.truncated.union := by
      rw [data.toExactMultiplicityData.truncation.union_eq]
      exact hpointOldUnion
    rcases hpointNewUnion with ⟨newSource, hnewPoint⟩
    have hnewOld : point ∈ data.finalFineShading.carrier newSource :=
      data.toExactMultiplicityData.truncation.subshading newSource hnewPoint
    have hparent : data.internalCover.parent newSource = parent := by
      calc
        data.internalCover.parent newSource =
            data.internalCover.parent
              ((data.internalCover.fullFiberSubfamily parent).embedding oldSource) :=
          data.parent_eq_of_mem_finalFineShading newSource _ point
            hnewOld holdAmbient
        _ = parent :=
          (data.internalCover.mem_fullFiber_iff_parent parent _).mp
            (data.internalCover.fullFiberSubfamily_mem parent oldSource)
    have hnewMem : newSource ∈ wz2PaperFullFiberIndices
        data.selectedFine.family data.selectedPacked.family parent := by
      exact (data.internalCover.mem_fullFiber_iff_parent parent _).mpr hparent
    let fiberSource : Fin
        (data.internalCover.fullFiberSubfamily parent).family.card :=
      ((wz2PaperFullFiberIndices data.selectedFine.family
        data.selectedPacked.family parent).orderIsoOfFin rfl).symm
          ⟨newSource, hnewMem⟩
    have hembed :
        (data.internalCover.fullFiberSubfamily parent).embedding fiberSource =
          newSource := by
      change
        ((wz2PaperFullFiberIndices data.selectedFine.family
          data.selectedPacked.family parent).orderEmbOfFin rfl) fiberSource =
            newSource
      have hval :
          (((wz2PaperFullFiberIndices data.selectedFine.family
            data.selectedPacked.family parent).orderIsoOfFin rfl)
              fiberSource).1 = newSource := by
        simp [fiberSource]
      exact hval
    refine ⟨fiberSource, ?_⟩
    change point ∈
      data.toExactMultiplicityData.truncation.truncated.carrier
        ((data.internalCover.fullFiberSubfamily parent).embedding fiberSource)
    rwa [hembed]

/-- Exact truncation retains at least half of the indexed shaded mass in
every owner parent fiber. -/
theorem toExactMultiplicityData_restrict_fullFiber_mass_retention
    (parent : Fin data.selectedPacked.family.card) :
    (restrictPaperShading
        (data.internalCover.fullFiberSubfamily parent)
        data.finalFineShading).mass ≤
      2 *
        (restrictPaperShading
          (data.internalCover.fullFiberSubfamily parent)
          data.toExactMultiplicityData.truncation.truncated).mass := by
  let oldFiber := restrictPaperShading
    (data.internalCover.fullFiberSubfamily parent) data.finalFineShading
  let newFiber := restrictPaperShading
    (data.internalCover.fullFiberSubfamily parent)
      data.toExactMultiplicityData.truncation.truncated
  have holdBand : oldFiber.HasConstantMultiplicity
      data.toExactMultiplicityData.m (2 * data.toExactMultiplicityData.m) := by
    intro point hpoint
    rcases hpoint with ⟨source, hsource⟩
    have hambient : point ∈ data.finalFineShading.carrier
        ((data.internalCover.fullFiberSubfamily parent).embedding source) :=
      hsource
    have heq : oldFiber.pointMultiplicity point =
        data.finalFineShading.pointMultiplicity point := by
      calc
        oldFiber.pointMultiplicity point =
            data.internalCover.toWZ1PaperTubeCover.fiberPointMultiplicity
              data.finalFineShading parent point := by
          exact data.internalCover.restrict_fullFiber_pointMultiplicity_eq
            data.finalFineShading parent point
        _ = data.finalFineShading.pointMultiplicity point := by
          symm
          simpa only [
            (data.internalCover.mem_fullFiber_iff_parent parent _).mp
              (data.internalCover.fullFiberSubfamily_mem parent source)] using
            data.finalFineShading_pointMultiplicity_eq_fiberPointMultiplicity
            ((data.internalCover.fullFiberSubfamily parent).embedding source)
            point hambient
    rw [heq]
    exact data.finalFineShading_constantMultiplicity point
      ⟨_, hambient⟩
  have hnewBand : newFiber.HasConstantMultiplicity
      data.toExactMultiplicityData.m (2 * data.toExactMultiplicityData.m) := by
    intro point hpoint
    rcases hpoint with ⟨source, hsource⟩
    have hsourceOld : point ∈ data.finalFineShading.carrier
        ((data.internalCover.fullFiberSubfamily parent).embedding source) :=
      data.toExactMultiplicityData.truncation.subshading _ hsource
    have heq : newFiber.pointMultiplicity point =
        data.toExactMultiplicityData.truncation.truncated.pointMultiplicity point := by
      calc
        newFiber.pointMultiplicity point =
            data.internalCover.toWZ1PaperTubeCover.fiberPointMultiplicity
              data.toExactMultiplicityData.truncation.truncated parent point := by
          exact data.internalCover.restrict_fullFiber_pointMultiplicity_eq
            data.toExactMultiplicityData.truncation.truncated parent point
        _ = data.toExactMultiplicityData.truncation.truncated.pointMultiplicity point := by
          symm
          have hglobalToFiber :=
            data.finalFineShading_pointMultiplicity_eq_fiberPointMultiplicity
              ((data.internalCover.fullFiberSubfamily parent).embedding source)
              point hsourceOld
          have hparent : data.internalCover.parent
              ((data.internalCover.fullFiberSubfamily parent).embedding source) =
                parent :=
            (data.internalCover.mem_fullFiber_iff_parent parent _).mp
              (data.internalCover.fullFiberSubfamily_mem parent source)
          -- Exact truncation has the same active sources at `point` as far as
          -- the unique owner parent is concerned.
          unfold Kakeya.Streamlined.Shading.pointMultiplicity
          congr 1
          ext candidate
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hcand
            exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
              have hcandOld :=
                data.toExactMultiplicityData.truncation.subshading candidate hcand
              exact hparent ▸ data.parent_eq_of_mem_finalFineShading
                candidate _ point hcandOld hsourceOld⟩, hcand⟩
          · exact fun hcand => hcand.2
    rw [heq]
    have hexact :=
      data.toExactMultiplicityData.truncation.exact_multiplicity point
        ⟨_, hsource⟩
    exact ⟨hexact.1, hexact.2.trans (by omega)⟩
  have hvolume : volume oldFiber.union ≤ 1 * volume newFiber.union := by
    rw [one_mul, data.toExactMultiplicityData_restrict_fullFiber_union_eq parent]
  have hmass := constant_multiplicity_mass_le_of_union_volume_le
    holdBand hnewBand 1 hvolume
  simpa [oldFiber, newFiber] using hmass

end WZ2PaperOwnerParentSelectedData

end Kakeya.Assouad

end
