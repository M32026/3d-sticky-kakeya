import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyPositiveParentDeletion

/-!
# Public structure after positive whole-parent deletion

Project the lightweight post-deletion handle to the public Section 6 cover
and balanced-cover records.  These definitions expose only data already
carried by the closed deletion; no new family or parent assignment is chosen.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2SameFamilyPositiveParentDeletionData

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
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
    {deletionExponent : ℕ}

noncomputable def selectedCoarse
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent) :
    Kakeya.Streamlined.TubeSubfamily sameFamily.selectedCoarse.family :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset
    sameFamily.selectedCoarse.family
    data.post.postDeletion.deletion.deletion.retainedParents

noncomputable def selectedFine
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent) :
    Kakeya.Streamlined.TubeSubfamily
      sameFamily.pullback.selectedFine.family :=
  data.post.postDeletion.deletion.restriction.selected

noncomputable def finalFineShading
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent) :
    WZ1PaperTubeShading data.selectedFine.family :=
  data.post.postDeletion.deletion.restriction.selectedFineShading

noncomputable def finalCoarseShading
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent) :
    WZ1PaperTubeShading data.selectedCoarse.family :=
  data.post.postDeletion.deletion.restriction.selectedCoarseShading

noncomputable def internalCover
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent) :
    WZ2PaperPartitioningCover
      data.selectedFine.family data.selectedCoarse.family :=
  data.post.postDeletion.deletion.restriction.restrictedCover

noncomputable def section6Cover
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent) :
    PureWZ2Section6Cover
      data.selectedFine.family data.selectedCoarse.family := by
  let cover := data.internalCover
  exact
    {
      fine_line_class :=
        sameFamily.pullback.section6Cover.fine_line_class.subfamily
          data.selectedFine
      coarse_line_class :=
        sameFamily.pullback.section6Cover.coarse_line_class.subfamily
          data.selectedCoarse
      covers := fun source =>
        ⟨cover.parent source, cover.parent_covers source⟩
      parent_hit := by
        intro parent
        rcases cover.parent_surjective parent with ⟨source, hsource⟩
        exact ⟨source, hsource ▸ cover.parent_covers source⟩
      coarse_essentially_distinct :=
        sameFamily.pullback.section6Cover.coarse_essentially_distinct
          |>.subfamily data.selectedCoarse
    }

noncomputable def publicBalanced
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent) :
    PureWZ2BalancedCoverData
      data.section6Cover data.finalFineShading data.finalCoarseShading := by
  let historical :=
    data.post.postDeletion.deletion.restriction.balanced
  let cover := data.internalCover
  exact
    {
      point_compatibility := by
        intro source parent hcovered point hpoint
        have hparent : parent = cover.parent source :=
          cover.parent_unique source parent hcovered
        subst parent
        exact historical.point_compatibility source point hpoint
      coarse_cubical := historical.coarse_cubical
      activeCells := historical.activeCells
      coarse_union_eq := historical.coarse_union_eq
      cellMass := historical.cellMass
      cellMass_pos := historical.cellMass_pos
      cellMass_ne_top := historical.cellMass_ne_top
      fine_cell_mass := historical.fine_cell_mass
    }

end PureWZ2SameFamilyPositiveParentDeletionData

end Kakeya.Assouad

end
