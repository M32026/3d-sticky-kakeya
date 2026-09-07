import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BalancedSourceWitnessCoarsePropertyP
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance

/-!
# Geometry of honest fine samples in one coarse parent

Different source samples need not lie on one fine tube.  It is enough that
their genuine fine tubes belong to the same frozen Section 6 parent fiber.
The paper line-cover metric then compares both samples to the same coarse
axis with an explicit scale error.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Metric Set

/-- A point in one covered fine paper tube is close to the coarse parent axis
at the same height. -/
lemma fine_source_dist_parent_axis_at_height
    {delta rho : ℝ}
    {fine : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube rho}
    (hdelta : 0 < delta)
    (hfine : WZ1PaperTubeInLineClass fine)
    (hparent : WZ1PaperTubeInLineClass parent)
    (hcover : WZ1PaperTubeCovers fine parent)
    (point : Point3) (hpoint : point ∈ wz1PaperTubeCarrier fine) :
    dist point (wz1PaperAxisPointAtHeight parent (point 2)) ≤
      12 * delta + 3 * rho := by
  rcases exists_dist_le_of_mem_cthickening_closed
      (isClosed_tubeAxisLine fine) (by positivity : 0 ≤ 6 * delta)
      hpoint.1 with
    ⟨fineAxisPoint, hfineAxisPoint, hpointFineAxis⟩
  have hpointFineSameHeight :
      dist point (wz1PaperAxisPointAtHeight fine (point 2)) ≤
        12 * delta := by
    rw [dist_comm]
    exact (wz1Paper_axisPointAtHeight_dist_point_le_two_mul
      hfine point fineAxisPoint hfineAxisPoint).trans (by linarith)
  have hheight : |point 2| ≤ 1 := by
    have hbox := hpoint.2
    simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
  have haxis :
      dist (wz1PaperAxisPointAtHeight fine (point 2))
          (wz1PaperAxisPointAtHeight parent (point 2)) ≤
        3 * rho := by
    have hraw := wz1PaperAxisPointAtHeight_dist_le
      hfine hparent hheight
    exact hraw.trans (by
      have hcover' : wz1PaperLineDistance fine parent ≤ rho / 2 := hcover
      nlinarith)
  calc
    dist point (wz1PaperAxisPointAtHeight parent (point 2)) ≤
        dist point (wz1PaperAxisPointAtHeight fine (point 2)) +
          dist (wz1PaperAxisPointAtHeight fine (point 2))
            (wz1PaperAxisPointAtHeight parent (point 2)) :=
      dist_triangle _ _ _
    _ ≤ 12 * delta + 3 * rho := add_le_add
      hpointFineSameHeight haxis

/-- Two honest shaded samples in fine tubes covered by the same coarse parent
are close up to their height separation and the two tube-scale errors. -/
lemma fine_sources_shared_parent_dist_le
    {delta rho : ℝ}
    {firstTube secondTube : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube rho}
    (hdelta : 0 < delta)
    (hfirstLine : WZ1PaperTubeInLineClass firstTube)
    (hsecondLine : WZ1PaperTubeInLineClass secondTube)
    (hparentLine : WZ1PaperTubeInLineClass parent)
    (hfirstCover : WZ1PaperTubeCovers firstTube parent)
    (hsecondCover : WZ1PaperTubeCovers secondTube parent)
    (first second : Point3)
    (hfirst : first ∈ wz1PaperTubeCarrier firstTube)
    (hsecond : second ∈ wz1PaperTubeCarrier secondTube) :
    dist first second ≤
      2 * |first 2 - second 2| + 24 * delta + 6 * rho := by
  let firstAxis := wz1PaperAxisPointAtHeight parent (first 2)
  let secondAxis := wz1PaperAxisPointAtHeight parent (second 2)
  have hfirstAxis : dist first firstAxis ≤ 12 * delta + 3 * rho := by
    simpa [firstAxis] using fine_source_dist_parent_axis_at_height
      hdelta hfirstLine hparentLine hfirstCover first hfirst
  have hsecondAxis : dist secondAxis second ≤ 12 * delta + 3 * rho := by
    rw [dist_comm]
    simpa [secondAxis] using fine_source_dist_parent_axis_at_height
      hdelta hsecondLine hparentLine hsecondCover second hsecond
  have haxis : dist firstAxis secondAxis ≤
      2 * |first 2 - second 2| := by
    apply wz1Paper_axisPointAtHeight_dist_le_of_axis_point
      hparentLine (first 2) |first 2 - second 2|
      (wz1PaperAxisPointAtHeight_mem_axis parent (second 2))
    rw [wz1PaperAxisPointAtHeight_coord_two hparentLine]
  calc
    dist first second ≤
        dist first firstAxis + dist firstAxis secondAxis +
          dist secondAxis second := by
      linarith [dist_triangle first firstAxis second,
        dist_triangle firstAxis secondAxis second]
    _ ≤ (12 * delta + 3 * rho) +
        2 * |first 2 - second 2| +
          (12 * delta + 3 * rho) := by gcongr
    _ = 2 * |first 2 - second 2| +
        24 * delta + 6 * rho := by ring

end Kakeya.Assouad.PureWZ2

end
