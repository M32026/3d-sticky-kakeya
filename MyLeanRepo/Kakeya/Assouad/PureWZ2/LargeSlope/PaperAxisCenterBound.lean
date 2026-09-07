import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperPopularBox
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance

/-!
# Paper-axis control from an occupied spatial box

This map-independent estimate is shared by both triangular and final
isotropic retubing.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- A carrier point in a common box controls the paper-oriented axis at the
center height. -/
theorem pureWZ2_paperAxis_center_coordinate_bound
    {delta : ℝ}
    {tube : Kakeya.DeltaTube delta}
    (hdelta : 0 < delta)
    (hline : WZ1PaperTubeInLineClass tube)
    (center halfWidth point : Point3)
    (hpointCarrier : point ∈ wz1PaperTubeCarrier tube)
    (hpointBox : point ∈ wz1AxisBox center halfWidth)
    (hheight : |center 2 - point 2| ≤ halfWidth 2)
    (coordinate : Fin 3) :
    |(wz1PaperAxisPointAtHeight tube (center 2) - center) coordinate| ≤
      2 * halfWidth 2 + 18 * delta + halfWidth coordinate := by
  let sameHeight := wz1PaperAxisPointAtHeight tube (point 2)
  have hsameDist : dist point sameHeight ≤ 18 * delta :=
    wz2_paper_carrier_same_height_dist_18delta
      hdelta tube hline hpointCarrier
  have hcenterAxis : dist
      (wz1PaperAxisPointAtHeight tube (center 2)) sameHeight ≤
        2 * halfWidth 2 :=
    wz1Paper_axisPointAtHeight_dist_le_of_axis_point hline
      (center 2) (halfWidth 2)
      (wz1PaperAxisPointAtHeight_mem_axis tube (point 2)) <| by
        simpa [sameHeight, wz1PaperAxisPointAtHeight_coord_two hline]
          using hheight
  have hcoordinateBox : |point coordinate - center coordinate| ≤
      halfWidth coordinate := by
    simpa [wz1AxisBox] using hpointBox coordinate
  calc
    |(wz1PaperAxisPointAtHeight tube (center 2) - center) coordinate| ≤
        |(wz1PaperAxisPointAtHeight tube (center 2) - sameHeight) coordinate| +
          |(sameHeight - point) coordinate| +
            |(point - center) coordinate| := by
      rw [show wz1PaperAxisPointAtHeight tube (center 2) - center =
          (wz1PaperAxisPointAtHeight tube (center 2) - sameHeight) +
            (sameHeight - point) + (point - center) by abel]
      simp only [PiLp.add_apply]
      calc
        |_ + _| ≤
            |(wz1PaperAxisPointAtHeight tube (center 2) - sameHeight)
                coordinate + (sameHeight - point) coordinate| +
              |(point - center) coordinate| := abs_add_le _ _
        _ ≤ (|(wz1PaperAxisPointAtHeight tube (center 2) - sameHeight)
                coordinate| + |(sameHeight - point) coordinate|) +
              |(point - center) coordinate| := by
            gcongr
            exact abs_add_le _ _
    _ ≤ 2 * halfWidth 2 + 18 * delta + halfWidth coordinate := by
      gcongr
      · exact (PiLp.norm_apply_le
          (wz1PaperAxisPointAtHeight tube (center 2) - sameHeight) coordinate
          |>.trans <| by simpa [dist_eq_norm] using hcenterAxis)
      · calc
          |(sameHeight - point) coordinate| ≤ ‖sameHeight - point‖ := by
            simpa [Real.norm_eq_abs] using
              PiLp.norm_apply_le (sameHeight - point) coordinate
          _ = dist sameHeight point := by rw [dist_eq_norm]
          _ = dist point sameHeight := dist_comm _ _
          _ ≤ 18 * delta := hsameDist
      · simpa using hcoordinateBox

end Kakeya.Assouad

end
