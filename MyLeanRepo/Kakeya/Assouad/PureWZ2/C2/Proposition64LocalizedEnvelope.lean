import MyLeanRepo.Kakeya.Assouad.PropStickyPaperJohnHomotheticEnvelope
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometry
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperAxisCoreVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyOrdinaryToCroppedShading
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance
import MyLeanRepo.Kakeya.Assouad.Hairbrush.HomogeneousTwoEndsHelpers
import Mathlib.Analysis.Convex.Measure

/-!
# A common cropped envelope from localized ordinary carriers

For a line-class tube with localized midpoint, the cropped full-line paper
carrier lies in a fixed centered dilation of the ordinary unit-segment
carrier.  Consequently all ordinary carriers contained in one convex test
set share one common outer-John envelope for their cropped carriers.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

private theorem pureWZ2Proposition64_center_add_paperDirection_mem_unitSegment
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    {parameter : ℝ} (hparameter : |parameter| ≤ 1 / 2) :
    wz2PaperTubeMidpoint tube +
        parameter • wz1PaperDirection tube ∈
      Kakeya.unitSegment tube.base tube.direction := by
  unfold wz2PaperTubeMidpoint wz1PaperDirection
  split_ifs with horientation
  · refine ⟨1 / 2 + parameter, ?_, ?_⟩
    · rw [abs_le] at hparameter
      constructor <;> linarith
    · module
  · refine ⟨1 / 2 - parameter, ?_, ?_⟩
    · rw [abs_le] at hparameter
      constructor <;> linarith
    · module

/-- A localized cropped paper carrier is contained in the factor-`100`
centered dilation of its ordinary carrier. -/
theorem pureWZ2Proposition64_localized_paperCarrier_subset_centeredDilated
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 10)
    (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube)
    (hmidpoint : ‖wz2PaperTubeMidpoint tube‖ ≤ 3) :
    wz1PaperTubeCarrier tube ⊆
      wz2PaperCenteredDilatedCarrier 100 tube := by
  let center := wz2PaperTubeMidpoint tube
  let direction := wz1PaperDirection tube
  have hgeometry :=
    wz2_paper_tube_carrier_geometry hdelta tube hline
  intro point hpoint
  rcases exists_dist_le_of_mem_cthickening_closed
      (wz2PaperAxisCoreSegment_compact tube).isClosed
      (by positivity : 0 ≤ 24 * delta)
      (hgeometry.2 hpoint) with
    ⟨axisPoint, haxisPoint, hpointAxis⟩
  rw [wz2PaperAxisCoreSegment_eq] at haxisPoint
  rcases haxisPoint with
    ⟨axisParameter, haxisParameter, haxisPointEq⟩
  have hcenterAxis : center ∈ tubeAxisLine tube := by
    exact wz2_paper_unitSegment_subset_axisLine tube
      ⟨1 / 2, by constructor <;> norm_num, rfl⟩
  rcases wz1Paper_axis_exists_parameter hline hcenterAxis with
    ⟨centerParameter, hcenterEq⟩
  have hzeroTwo :
      wz1TubeAxisZeroPoint tube (2 : Fin 3) = 0 :=
    wz1TubeAxisZeroPoint_coord_two tube hline.vertical
  have hdirectionTwo : 1 / 2 ≤ direction (2 : Fin 3) := hline.1
  have hdirectionTwoPos : 0 < direction (2 : Fin 3) := by linarith
  have hcenterCoordinate :
      center (2 : Fin 3) =
        centerParameter * direction (2 : Fin 3) := by
    have hcoordinate := congrArg (fun point : Point3 =>
      point (2 : Fin 3)) hcenterEq
    simpa [direction, hzeroTwo, smul_eq_mul] using hcoordinate
  have hcenterCoordinateAbs : |center (2 : Fin 3)| ≤ 3 := by
    exact (PiLp.norm_apply_le center (2 : Fin 3)).trans hmidpoint
  have hcenterParameterAbs : |centerParameter| ≤ 6 := by
    have hmul :
        |centerParameter| * direction (2 : Fin 3) ≤ 3 := by
      rw [← abs_of_pos hdirectionTwoPos, ← abs_mul, ← hcenterCoordinate]
      exact hcenterCoordinateAbs
    nlinarith [abs_nonneg centerParameter]
  let contractedParameter :=
    (axisParameter - centerParameter) / 100
  have hcontractedParameter : |contractedParameter| ≤ 1 / 2 := by
    have haxisAbs : |axisParameter| ≤ 2 := by
      exact (abs_le).2 haxisParameter
    have hdifference :
        |axisParameter - centerParameter| ≤ 8 := by
      exact (abs_sub _ _).trans (by linarith)
    dsimp only [contractedParameter]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 100)]
    norm_num
    linarith
  let contractedAxisPoint :=
    center + contractedParameter • direction
  have hcontractedAxisPoint :
      contractedAxisPoint ∈
        Kakeya.unitSegment tube.base tube.direction :=
    pureWZ2Proposition64_center_add_paperDirection_mem_unitSegment
      tube hcontractedParameter
  let contractedPoint :=
    center + (1 / 100 : ℝ) • (point - center)
  have haxisDifference :
      axisPoint - center =
        (axisParameter - centerParameter) • direction := by
    rw [haxisPointEq, hcenterEq]
    module
  have hcontractedDifference :
      contractedPoint - contractedAxisPoint =
        (1 / 100 : ℝ) • (point - axisPoint) := by
    dsimp only [contractedPoint, contractedAxisPoint, contractedParameter]
    rw [show point - center =
        (point - axisPoint) + (axisPoint - center) by abel,
      haxisDifference, smul_add, smul_smul]
    module
  have hcontractedDistance :
      dist contractedPoint contractedAxisPoint ≤ delta := by
    rw [dist_eq_norm, hcontractedDifference, norm_smul, Real.norm_eq_abs]
    norm_num
    have hdistance : ‖point - axisPoint‖ ≤ 24 * delta := by
      simpa [dist_eq_norm] using hpointAxis
    nlinarith
  have hcontractedCarrier : contractedPoint ∈ tube.carrier :=
    Metric.mem_cthickening_of_dist_le
      contractedPoint contractedAxisPoint delta
      (Kakeya.unitSegment tube.base tube.direction)
      hcontractedAxisPoint hcontractedDistance
  refine ⟨contractedPoint, hcontractedCarrier, ?_⟩
  rw [AffineMap.homothety_apply]
  apply PiLp.ext
  intro coordinate
  dsimp only [contractedPoint]
  simp only [vsub_eq_sub, vadd_eq_add, PiLp.add_apply,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- All localized ordinary carriers contained in one convex test set have a
single convex envelope containing their cropped paper carriers. -/
theorem pureWZ2Proposition64_localized_common_cropped_envelope
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 10)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (hlocal : ∀ index,
      ‖wz2PaperTubeMidpoint (family.tube index)‖ ≤ 3)
    (sourceSet : Set Point3)
    (hsourceConvex : Convex ℝ sourceSet) :
    ∃ paperSet : Set Point3,
      Convex ℝ paperSet ∧
        volume paperSet ≤
          (212776173 : ENNReal) * volume sourceSet ∧
        ∀ index : Fin family.card,
          (family.tube index).carrier ⊆ sourceSet →
            wz1PaperTubeCarrier (family.tube index) ⊆ paperSet := by
  by_cases heligible :
      ∃ index : Fin family.card,
        (family.tube index).carrier ⊆ sourceSet
  · rcases heligible with ⟨eligible, heligible⟩
    let boundedSource :=
      sourceSet ∩ Metric.closedBall (0 : Point3) 5
    let body := closure boundedSource
    have hballConvex :
        Convex ℝ (Metric.closedBall (0 : Point3) 5) :=
      convex_closedBall (0 : Point3) 5
    have hboundedConvex : Convex ℝ boundedSource :=
      hsourceConvex.inter hballConvex
    have hbodyConvex : Convex ℝ body := hboundedConvex.closure
    have hcarrierBall : ∀ index : Fin family.card,
        (family.tube index).carrier ⊆
          Metric.closedBall (0 : Point3) 5 := by
      intro index point hpoint
      have hmidBall := tube_subset_midpoint_closedBall
        hdelta (family.tube index) hpoint
      have hpointMid :
          dist point (wz2PaperTubeMidpoint (family.tube index)) ≤
            1 / 2 + delta := by
        simpa [wz2PaperTubeMidpoint] using hmidBall
      have hmidZero :
          dist (wz2PaperTubeMidpoint (family.tube index)) 0 ≤ 3 := by
        simpa [dist_zero_right] using hlocal index
      have hpointZero : dist point 0 ≤ 5 := by
        calc
          dist point 0 ≤
              dist point (wz2PaperTubeMidpoint (family.tube index)) +
                dist (wz2PaperTubeMidpoint (family.tube index)) 0 :=
            dist_triangle _ _ _
          _ ≤ (1 / 2 + delta) + 3 := by gcongr
          _ ≤ 5 := by linarith
      simpa [Metric.mem_closedBall] using hpointZero
    have heligibleBody :
        (family.tube eligible).carrier ⊆ body := by
      intro point hpoint
      exact subset_closure ⟨heligible hpoint, hcarrierBall eligible hpoint⟩
    have hbodyCompact : IsCompact body := by
      apply Metric.isCompact_of_isClosed_isBounded isClosed_closure
      exact (Metric.isBounded_closedBall.subset fun point hpoint =>
        closure_minimal (fun _ h => h.2) Metric.isClosed_closedBall hpoint)
    have hbodyInterior : (interior body).Nonempty := by
      exact
        (wz2_paper_ordinary_tube_isConvexBody
          (family.tube eligible) hdelta).2.2.mono
          (interior_mono heligibleBody)
    have hbody : JohnEllipsoid.IsConvexBody body :=
      ⟨hbodyConvex, hbodyCompact, hbodyInterior⟩
    rcases wz2_paper_john_homothetic_envelope body hbody with
      ⟨paperSet, hpaperConvex, hpaperVolume, hpaperHomothetic⟩
    have hbodyVolume : volume body ≤ volume sourceSet := by
      have hbodySubset : body ⊆ closure sourceSet :=
        closure_mono fun _ hpoint => hpoint.1
      have hfrontier : volume (frontier sourceSet) = 0 :=
        Convex.addHaar_frontier volume hsourceConvex
      calc
        volume body ≤ volume (closure sourceSet) := measure_mono hbodySubset
        _ = volume sourceSet := measure_closure_of_null_frontier hfrontier
    refine ⟨paperSet, hpaperConvex,
      hpaperVolume.trans (by gcongr), ?_⟩
    intro index hcarrierSource
    have hcarrierBody : (family.tube index).carrier ⊆ body := by
      intro point hpoint
      exact subset_closure
        ⟨hcarrierSource hpoint, hcarrierBall index hpoint⟩
    have hcenterBody :
        wz2PaperTubeMidpoint (family.tube index) ∈ body :=
      hcarrierBody
        (wz2_paper_tubeMidpoint_mem_carrier
          (family.tube index) hdelta.le)
    exact
      (pureWZ2Proposition64_localized_paperCarrier_subset_centeredDilated
        hdelta hdeltaSmall (family.tube index) (hline index)
        (hlocal index)).trans <|
        (Set.image_mono hcarrierBody).trans <|
          hpaperHomothetic _ hcenterBody
  · refine ⟨(∅ : Set Point3), convex_empty, by simp, ?_⟩
    intro index hcarrier
    exact (heligible ⟨index, hcarrier⟩).elim

end Kakeya.Assouad

end
