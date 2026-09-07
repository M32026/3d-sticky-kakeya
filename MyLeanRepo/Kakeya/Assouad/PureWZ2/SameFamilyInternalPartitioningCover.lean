import MyLeanRepo.Kakeya.Assouad.PureWZ2.LineCoverCarrierContainment
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SelectedCallerCompletePullback
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralPartitioningFromSeparation

/-!
# Internal partitioning cover for the same-family caller pullback

The public Node 3 output uses only the strict WZ line-metric cover.  The
closed whole-cell balancing infrastructure has a historical internal wrapper
that additionally records cropped carrier containment and doubled-fiber
disjointness.  Strong separation of the quotient callers and the scale gap
derive those extra fields without changing the parent map or the public full
fibers.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
Upgrade a strongly separated strict WZ line cover to the historical internal
partitioning-cover wrapper.  The parent map is unchanged.
-/
noncomputable def WZ1PaperTubeCover.toInternalPartitioningOfStrongSeparation
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (fineLine : WZ1PaperIsLineClass fine)
    (coarseLine : WZ1PaperIsLineClass coarse)
    (parentCarrier :
      ∀ source,
        WZ2PaperTubeCarrierCovers
          (fine.tube source) (coarse.tube (cover.parent source)))
    (stronglySeparated :
      ∀ first second, first ≠ second →
        1600 * rho <
          wz1PaperLineDistance
            (coarse.tube first) (coarse.tube second)) :
    WZ2PaperPartitioningCover fine coarse where
  parent := cover.parent
  parent_surjective := cover.parent_surjective
  parent_covers := cover.parent_covers
  parent_unique := cover.parent_unique
  parent_carrier_covers := parentCarrier
  literal_parent_unique source candidate candidateCovers := by
    by_contra hne
    have assignedDistance :=
      wz2_paper_carrier_containment_lineDistance_le
        hdelta hrho (fineLine source) (coarseLine (cover.parent source))
        (parentCarrier source)
    have candidateDistance :=
      wz2_paper_carrier_containment_lineDistance_le
        hdelta hrho (fineLine source) (coarseLine candidate)
        candidateCovers
    have triangle :=
      wz1PaperLineDistance_triangle
        (coarse.tube candidate) (fine.tube source)
        (coarse.tube (cover.parent source))
    have symmetry :
        wz1PaperLineDistance
            (coarse.tube candidate) (fine.tube source) =
          wz1PaperLineDistance
            (fine.tube source) (coarse.tube candidate) :=
      wz1PaperLineDistance_symm _ _
    rw [symmetry] at triangle
    exact
      (not_le_of_gt
        (stronglySeparated candidate (cover.parent source) hne))
        (triangle.trans (by
          linarith [assignedDistance, candidateDistance]))
  literal_doubled_fibers_disjoint first second hne := by
    rw [Finset.disjoint_left]
    intro source hfirst hsecond
    have firstContainment :
        wz1PaperTubeCarrier (fine.tube source) ⊆
          wz2PaperDoubledTubeCarrier (coarse.tube first) := by
      simpa [wz2PaperLiteralDoubledFiberIndices] using hfirst
    have secondContainment :
        wz1PaperTubeCarrier (fine.tube source) ⊆
          wz2PaperDoubledTubeCarrier (coarse.tube second) := by
      simpa [wz2PaperLiteralDoubledFiberIndices] using hsecond
    have firstDistance :=
      wz2_paper_doubled_carrier_containment_lineDistance_le
        hdelta hrho (fineLine source) (coarseLine first)
        firstContainment
    have secondDistance :=
      wz2_paper_doubled_carrier_containment_lineDistance_le
        hdelta hrho (fineLine source) (coarseLine second)
        secondContainment
    have triangle :=
      wz1PaperLineDistance_triangle
        (coarse.tube first) (fine.tube source) (coarse.tube second)
    have symmetry :
        wz1PaperLineDistance
            (coarse.tube first) (fine.tube source) =
          wz1PaperLineDistance
            (fine.tube source) (coarse.tube first) :=
      wz1PaperLineDistance_symm _ _
    rw [symmetry] at triangle
    exact
      (not_le_of_gt (stronglySeparated first second hne))
        (triangle.trans (by
          linarith [firstDistance, secondDistance]))
  doubled_fibers_disjoint first second hne := by
    rw [Finset.disjoint_left]
    intro source hfirst hsecond
    have firstDistance :
        wz1PaperLineDistance
            (fine.tube source) (coarse.tube first) ≤ rho := by
      simpa [wz2PaperDoubledFiberIndices] using hfirst
    have secondDistance :
        wz1PaperLineDistance
            (fine.tube source) (coarse.tube second) ≤ rho := by
      simpa [wz2PaperDoubledFiberIndices] using hsecond
    have triangle :=
      wz1PaperLineDistance_triangle
        (coarse.tube first) (fine.tube source) (coarse.tube second)
    have symmetry :
        wz1PaperLineDistance
            (coarse.tube first) (fine.tube source) =
          wz1PaperLineDistance
            (fine.tube source) (coarse.tube first) :=
      wz1PaperLineDistance_symm _ _
    rw [symmetry] at triangle
    exact
      (not_le_of_gt (stronglySeparated first second hne))
        (triangle.trans (by
          linarith [firstDistance, secondDistance, hrho]))

namespace PureWZ2SelectedCallerCompletePullbackData

/--
The complete selected-caller pullback has an internal partitioning cover with
exactly the same parent map as its public strict WZ cover.
-/
noncomputable def internalPartitioningCover
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
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
        (outputConstant := outputConstant)
        actualNearby quotient support coordinateCount}
    {merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized}
    {selectedCoarse :
      WZ2PaperPureTubeSubfamily
        (quotient.callerCover.hitParentSubfamily
          quotient.positiveCallerFine).family}
    (data :
      PureWZ2SelectedCallerCompletePullbackData
        merged selectedCoarse)
    (scaleSeparation : 18 * delta ≤ callerRequested.1) :
    WZ2PaperPartitioningCover
      data.selectedFine.family selectedCoarse.family := by
  let hitCaller :=
    quotient.callerCover.hitParentSubfamily
      quotient.positiveCallerFine
  have callerPos : 0 < callerRequested.1 :=
    actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1
  have selectedStronglySeparated :
      ∀ first second : Fin selectedCoarse.family.card,
        first ≠ second →
          1600 * callerRequested.1 <
            wz1PaperLineDistance
              (selectedCoarse.family.tube first)
              (selectedCoarse.family.tube second) := by
    intro first second hne
    rw [selectedCoarse.tube_eq, selectedCoarse.tube_eq,
      hitCaller.tube_eq, hitCaller.tube_eq]
    exact
      quotient.caller_strongly_separated
        (hitCaller.embedding (selectedCoarse.embedding first))
        (hitCaller.embedding (selectedCoarse.embedding second))
        (hitCaller.embedding.injective.ne
          (selectedCoarse.embedding.injective.ne hne))
  have parentCarrier :
      ∀ source,
        WZ2PaperTubeCarrierCovers
          (data.selectedFine.family.tube source)
          (selectedCoarse.family.tube
            (data.callerCover.parent source)) := by
    intro source
    exact
      wz1PaperTubeCarrier_subset_of_lineCover_eighteen
        actualNearby.scaleData.delta_pos callerPos scaleSeparation
        (data.selectedFine.family.tube source)
        (selectedCoarse.family.tube
          (data.callerCover.parent source))
        (data.section6Cover.fine_line_class source)
        (data.section6Cover.coarse_line_class
          (data.callerCover.parent source))
        (data.callerCover.parent_covers source)
  exact
    data.callerCover.toInternalPartitioningOfStrongSeparation
      actualNearby.scaleData.delta_pos callerPos
      data.section6Cover.fine_line_class
      data.section6Cover.coarse_line_class
      parentCarrier selectedStronglySeparated

@[simp] theorem internalPartitioningCover_parent
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
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
        (outputConstant := outputConstant)
        actualNearby quotient support coordinateCount}
    {merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized}
    {selectedCoarse :
      WZ2PaperPureTubeSubfamily
        (quotient.callerCover.hitParentSubfamily
          quotient.positiveCallerFine).family}
    (data :
      PureWZ2SelectedCallerCompletePullbackData
        merged selectedCoarse)
    (scaleSeparation : 18 * delta ≤ callerRequested.1)
    (source : Fin data.selectedFine.family.card) :
    (data.internalPartitioningCover scaleSeparation).parent source =
      data.callerCover.parent source := by
  rfl

end PureWZ2SelectedCallerCompletePullbackData

end Kakeya.Assouad

end
