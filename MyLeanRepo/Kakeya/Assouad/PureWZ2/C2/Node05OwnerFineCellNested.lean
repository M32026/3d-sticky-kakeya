import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05FinalCoverExactMultiplicityBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerParentStructure

/-!
# Whole-cell nesting for the owner-selected fine shading

The final owner selection is a subshading of the dominant-owner
exactification, which is itself a subshading of the final exact adapter.
The adapter supplies a containing coarse cell.  The owner certificate supplies
the selected owner cell; the two cells coincide because both contain the same
point.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

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

/-- Every literal fine cell meeting the owner-selected final shading is
contained in one active coarse cell of the final public balanced cover. -/
theorem fineCellNested :
    ∀ source point, point ∈ data.finalFineShading.carrier source →
      ∃ cell ∈ data.publicBalanced.activeCells,
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          wz1PaperGridCube callerRequested.1 cell := by
  intro source point hpoint
  let exactifiedIndex : Fin owner.exactified.selected.family.card :=
    data.balancedPullback.pullback.selectedFine.embedding source
  let adapterIndex : Fin sameFamily.pullback.selectedFine.family.card :=
    owner.exactified.selected.embedding exactifiedIndex
  have hExactifiedPoint :
      point ∈ owner.exactified.refined.carrier exactifiedIndex :=
    data.balancedPullback.pullback.selectedFine_subshading source hpoint
  have hFinalPoint :
      point ∈
        (balancing.balanced.finalData.producer.coarseBand
          |>.selectedFineShading).carrier adapterIndex :=
    owner.exactified_subshading exactifiedIndex hExactifiedPoint
  have hAdapterPoint :
      point ∈ owner.exactAdapter.exact.refined.carrier adapterIndex := by
    rw [owner.exactAdapter.exact_refined_eq]
    exact hFinalPoint
  rcases owner.exactAdapter.fineCellNested
      adapterIndex point hAdapterPoint with
    ⟨adapterCell, hAdapterCell, hFineCellSubset⟩
  rcases owner.exactified.refined_owner
      exactifiedIndex point hExactifiedPoint with
    ⟨ownerCell, hOwnerCell, hPointOwnerCell, hOwnerParent⟩
  have hPointFineCell :
      point ∈ wz1PaperGridCube delta (wz1PaperGridIndex delta point) :=
    (mem_wz1PaperGridCube delta _ point).mpr rfl
  have hPointAdapterCell :
      point ∈ wz1PaperGridCube callerRequested.1 adapterCell :=
    hFineCellSubset hPointFineCell
  have hCellEq : adapterCell = ownerCell := by
    by_contra hNe
    exact Set.disjoint_left.mp
      (wz1PaperGridCube_disjoint hNe)
      hPointAdapterCell hPointOwnerCell
  have hRestrictedParent :
      owner.exactified.restrictedCover.parent exactifiedIndex =
        data.selectedPacked.embedding (data.internalCover.parent source) := by
    calc
      owner.exactified.restrictedCover.parent exactifiedIndex =
          data.selectedPacked.embedding
            (data.balancedPullback.pullback.parent source) :=
        (data.balancedPullback.pullback.parent_ambient_eq source).symm
      _ = data.selectedPacked.embedding
          (data.balancedPullback.pullback.restrictedCover.parent source) :=
        congrArg data.selectedPacked.embedding
          (data.balancedPullback.pullback.restricted_parent_eq source).symm
      _ = data.selectedPacked.embedding (data.internalCover.parent source) := rfl
  have hOwnerSelected : ownerCell ∈ data.balancedPullback.selectedCells := by
    rw [data.balancedPullback.selectedCells_eq]
    apply Finset.mem_filter.mpr
    refine ⟨hOwnerCell, ?_⟩
    refine ⟨data.internalCover.parent source, ?_⟩
    exact hOwnerParent.symm.trans
      (congrArg (WZ2PaperOwnerParentSelectedData.packed
        (owner := owner)).embedding hRestrictedParent)
  have hAdapterSelected :
      adapterCell ∈ data.balancedPullback.selectedCells := by
    rwa [hCellEq]
  refine ⟨adapterCell, ?_, hFineCellSubset⟩
  change adapterCell ∈ data.balancedPullback.balanced.activeCells
  rw [data.balancedPullback.balanced_activeCells_eq]
  exact hAdapterSelected

end WZ2PaperOwnerParentSelectedData

end Kakeya.Assouad

end
