import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05OwnerGlobalMultiplicity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05OwnerFineCellNested
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ExactMultiplicityTruncation

/-!
# Exact multiplicity truncation for the owner-parent output

This file applies the literal-cell exact multiplicity truncation directly to
the already selected owner-parent fine shading.  The fine and coarse families,
the Section-6 cover, the active coarse cells, and `cellMass` are inherited
verbatim from `WZ2PaperOwnerParentSelectedData.publicBalanced`.
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

/-- The dependent output of exact multiplicity truncation at the owner's
dyadic lower endpoint.  This is the truncation certificate itself: the
remaining balanced-cover packages are canonical consequences.  Keeping this
as an abbreviation avoids generating large dependent-record eliminators for
a purely derived package. -/
abbrev ExactMultiplicityData
    (data : WZ2PaperOwnerParentSelectedData owner outputConstant) :=
  PureWZ2Node05ExactMultiplicityTruncationData
    data.finalFineShading actualNearby.scaleData.delta_pos
      (2 ^ balancing.balanced.finalData.producer.fiberBand.level)

/-- The selected dyadic multiplicity. -/
def ExactMultiplicityData.m
    {data : WZ2PaperOwnerParentSelectedData owner outputConstant}
    (_ : ExactMultiplicityData data) : ℕ :=
  2 ^ balancing.balanced.finalData.producer.fiberBand.level

lemma ExactMultiplicityData.m_pos
    {data : WZ2PaperOwnerParentSelectedData owner outputConstant}
    (exact : ExactMultiplicityData data) : 0 < exact.m := by
  unfold ExactMultiplicityData.m
  positivity

/-- The underlying exact truncation certificate. -/
abbrev ExactMultiplicityData.truncation
    {data : WZ2PaperOwnerParentSelectedData owner outputConstant}
    (exact : ExactMultiplicityData data) :
    PureWZ2Node05ExactMultiplicityTruncationData
      data.finalFineShading actualNearby.scaleData.delta_pos exact.m :=
  exact

/-- The balanced cover induced by the exact truncation. -/
noncomputable def ExactMultiplicityData.truncatedBalanced
    {data : WZ2PaperOwnerParentSelectedData owner outputConstant}
    (exact : ExactMultiplicityData data) :
    PureWZ2BalancedCoverData data.section6Cover exact.truncation.truncated
      data.finalCoarseShading :=
  exact.truncation.toBalancedBase data.publicBalanced

/-- The Node-5 balanced-cover certificate induced by the exact truncation. -/
noncomputable def ExactMultiplicityData.node5Balanced
    {data : WZ2PaperOwnerParentSelectedData owner outputConstant}
    (exact : ExactMultiplicityData data) :
    PureWZ2Node5BalancedCoverData exact.truncatedBalanced :=
  exact.truncation.toNode5Balanced data.publicBalanced exact.m_pos
    data.fineCellNested

/-- Apply exact literal-cell truncation without reselecting either family or
any coarse cell. -/
noncomputable def toExactMultiplicityData
    (data : WZ2PaperOwnerParentSelectedData owner outputConstant) :
    ExactMultiplicityData data := by
  exact pureWZ2Node05_exactMultiplicityTruncation
    data.finalFineShading actualNearby.scaleData.delta_pos
      data.balancedPullback.pullback.selectedFine_cubical
      (2 ^ balancing.balanced.finalData.producer.fiberBand.level)
      (by positivity)
      data.finalFineShading_constantMultiplicity

/-- The exact cell-incidence identity, with the original public `cellMass`. -/
theorem toExactMultiplicityData_cellIncidenceMass_eq
    (data : WZ2PaperOwnerParentSelectedData owner outputConstant)
    (cell : WZ2PaperCellIndex)
    (hcell : cell ∈ data.publicBalanced.activeCells) :
    wz2PaperCellIncidenceMass (rho := callerRequested.1)
        data.toExactMultiplicityData.truncation.truncated cell =
      (data.toExactMultiplicityData.m : ENNReal) *
        data.publicBalanced.cellMass := by
  exact
    data.toExactMultiplicityData.truncation.cellIncidenceMass_eq
      data.publicBalanced cell hcell

end WZ2PaperOwnerParentSelectedData

end Kakeya.Assouad

end
