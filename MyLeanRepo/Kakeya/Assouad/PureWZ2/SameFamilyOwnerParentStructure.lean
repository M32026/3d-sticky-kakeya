import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerParentSelection

/-!
# Public same-family structure after owner-parent selection

The final owner-parent selection is realized by complete coarse fibers and
whole owned spatial cells.  This module exposes that one final fine family,
coarse family, shading pair, Section 6 cover, and balanced certificate.
-/

noncomputable section

namespace Kakeya.Assouad

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

noncomputable def packed :
    Kakeya.Streamlined.TubeSubfamily
      sameFamily.selectedCoarse.family :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset
    sameFamily.selectedCoarse.family
    owner.exactified.retainedParents

noncomputable def selectedCoarse
    (data : WZ2PaperOwnerParentSelectedData owner outputConstant) :
    Kakeya.Streamlined.TubeSubfamily
      sameFamily.selectedCoarse.family :=
  (packed (owner := owner)).comp data.selectedPacked

noncomputable def selectedFine
    (data : WZ2PaperOwnerParentSelectedData owner outputConstant) :
    Kakeya.Streamlined.TubeSubfamily
      sameFamily.pullback.selectedFine.family :=
  owner.exactified.selected.comp
    data.balancedPullback.pullback.selectedFine

noncomputable def finalFineShading
    (data : WZ2PaperOwnerParentSelectedData owner outputConstant) :
    WZ1PaperTubeShading data.selectedFine.family :=
  data.balancedPullback.pullback.selectedFineShading

noncomputable def finalCoarseShading
    (data : WZ2PaperOwnerParentSelectedData owner outputConstant) :
    WZ1PaperTubeShading data.selectedPacked.family :=
  data.balancedPullback.pullback.selectedCoarseShading

noncomputable def internalCover
    (data : WZ2PaperOwnerParentSelectedData owner outputConstant) :
    WZ2PaperPartitioningCover
      data.selectedFine.family data.selectedPacked.family :=
  data.balancedPullback.pullback.restrictedCover

noncomputable def section6Cover
    (data : WZ2PaperOwnerParentSelectedData owner outputConstant) :
    PureWZ2Section6Cover
      data.selectedFine.family data.selectedPacked.family := by
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
    (data : WZ2PaperOwnerParentSelectedData owner outputConstant) :
    PureWZ2BalancedCoverData
      data.section6Cover data.finalFineShading
      data.finalCoarseShading := by
  let historical := data.balancedPullback.balanced
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

theorem finalFineShading_mass_eq_selectedFiberMass
    (data : WZ2PaperOwnerParentSelectedData owner outputConstant) :
    data.finalFineShading.mass =
      ∑ parent : Fin data.selectedPacked.family.card,
        (restrictPaperShading
          (owner.exactified.restrictedCover.fullFiberSubfamily
            (data.selectedPacked.embedding parent))
          owner.exactified.refined).mass := by
  exact
    data.balancedPullback.pullback.selectedFineShading_mass_eq

end WZ2PaperOwnerParentSelectedData

end Kakeya.Assouad

end
