import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureNearbyTopLevelCWA
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryHelpers

/-!
# Ordinary-to-paper CWA bridge inside the canonical crop box

An ordinary unit-segment tube is contained in its coaxial paper tube as soon
as its ordinary carrier lies in the fixed paper crop box.  This removes the
remaining convention-change premise when a common rigid frame has already
placed every ordinary carrier inside that box.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric

/--
The ordinary carrier lies in the corresponding cropped full-line paper
carrier whenever it already lies in the crop box.
-/
lemma ordinary_carrier_subset_paper_of_axisBox
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (tube : Kakeya.DeltaTube delta)
    (axisBox :
      tube.carrier ⊆
        Kakeya.Streamlined.axisBox 2 2 2) :
    tube.carrier ⊆ wz1PaperTubeCarrier tube := by
  intro point pointMem
  refine ⟨?_, axisBox pointMem⟩
  let segment :=
    Kakeya.unitSegment tube.base tube.direction
  have segmentCompact : IsCompact segment :=
    isCompact_Icc.image (by fun_prop)
  have pointThickening :
      point ∈ Metric.cthickening delta segment := by
    simpa [Kakeya.DeltaTube.carrier, segment] using pointMem
  rcases
      exists_dist_le_of_mem_cthickening_closed
        segmentCompact.isClosed deltaPos.le pointThickening
    with
    ⟨axisPoint, ⟨parameter, _parameterMem, axisPointEq⟩,
      pointAxis⟩
  have axisPointLine :
      axisPoint ∈ tubeAxisLine tube := by
    refine ⟨parameter, ?_⟩
    exact axisPointEq.symm
  exact
    Metric.mem_cthickening_of_dist_le
      point axisPoint (6 * delta) (tubeAxisLine tube)
      axisPointLine (by linarith)

/--
Ordinary top-level CWA becomes paper top-level CWA with no further constant
loss once every ordinary carrier lies in the crop box.
-/
theorem ordinary_topLevelCWA_to_paper_of_axisBox
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (deltaPos : 0 < delta)
    (axisBox :
      ∀ index,
        (family.tube index).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
    (ordinary :
      WZ2PaperBodyConvexWolffBound family.toBodyFamily C) :
    WZ2PaperConvexWolffBound family C :=
  wz2PaperOrdinaryCWA_to_paper_of_carrier_subset
    (fun index =>
      ordinary_carrier_subset_paper_of_axisBox
        deltaPos (family.tube index) (axisBox index))
    ordinary

end Kakeya.Assouad

end
