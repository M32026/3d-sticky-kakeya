import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoverCarrierContainment

/-!
# Cropped carrier containment from a strict paper line cover

At the caller scale used by the pure Node 3 route, the strict WZ line-cover
relation and the scale gap already force containment of the cropped full-line
paper carriers.  This is an internal bridge for the closed whole-cell
balancing infrastructure; it does not strengthen the public Section 6 cover.
-/

noncomputable section

namespace Kakeya.Assouad

/--
If a radius-`delta` paper tube is strictly line-covered by a radius-`rho`
paper tube and `4 * delta ≤ rho`, then its cropped paper carrier is contained
in the parent carrier.
-/
theorem wz1PaperTubeCarrier_subset_of_lineCover
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hscale : 4 * delta ≤ rho)
    (fine : Kakeya.DeltaTube delta)
    (coarse : Kakeya.DeltaTube rho)
    (fineLine : WZ1PaperTubeInLineClass fine)
    (coarseLine : WZ1PaperTubeInLineClass coarse)
    (covered : WZ1PaperTubeCovers fine coarse) :
    WZ2PaperTubeCarrierCovers fine coarse := by
  intro point hpoint
  rcases
      exists_dist_le_of_mem_cthickening_closed
        (isClosed_tubeAxisLine fine)
        (by positivity : 0 ≤ 6 * delta)
        hpoint.1
    with ⟨fineAxisPoint, fineAxisPointMem, pointFineAxis⟩
  let height := point (2 : Fin 3)
  let fineAtHeight := wz1PaperAxisPointAtHeight fine height
  let coarseAtHeight := wz1PaperAxisPointAtHeight coarse height
  have heightBound : |height| ≤ 1 := by
    have hbox :
        |point 0| ≤ 1 ∧ |point 1| ≤ 1 ∧ |point 2| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hpoint.2
    simpa [height] using hbox.2.2
  have pointFineAtHeight :
      dist point fineAtHeight ≤ 12 * delta := by
    have h :=
      wz1Paper_axisPointAtHeight_dist_point_le_two_mul
        fineLine point fineAxisPoint fineAxisPointMem
    dsimp only [fineAtHeight, height]
    calc
      dist point
          (wz1PaperAxisPointAtHeight fine (point (2 : Fin 3))) =
          dist
            (wz1PaperAxisPointAtHeight fine (point (2 : Fin 3)))
            point := dist_comm _ _
      _ ≤ 2 * dist point fineAxisPoint := h
      _ ≤ 2 * (6 * delta) := by gcongr
      _ = 12 * delta := by ring
  have fineCoarseAtHeight :
      dist fineAtHeight coarseAtHeight ≤ 3 * rho := by
    have h :=
      wz1PaperAxisPointAtHeight_dist_le
        fineLine coarseLine heightBound
    have coverBound :
        wz1PaperLineDistance fine coarse ≤ rho / 2 := covered
    dsimp only [fineAtHeight, coarseAtHeight]
    exact h.trans (by nlinarith)
  have pointCoarseAtHeight :
      dist point coarseAtHeight ≤ 6 * rho := by
    calc
      dist point coarseAtHeight ≤
          dist point fineAtHeight +
            dist fineAtHeight coarseAtHeight :=
        dist_triangle _ _ _
      _ ≤ 12 * delta + 3 * rho := by
        gcongr
      _ ≤ 6 * rho := by nlinarith
  have coarseAxis :
      coarseAtHeight ∈ tubeAxisLine coarse :=
    wz1PaperAxisPointAtHeight_mem_axis coarse height
  exact
    ⟨Metric.mem_cthickening_of_dist_le
        point coarseAtHeight (6 * rho)
        (tubeAxisLine coarse) coarseAxis pointCoarseAtHeight,
      hpoint.2⟩

/--
The `18 * delta ≤ rho` separation used by whole-cell balancing implies the
smaller scale gap needed by the carrier-containment bridge.
-/
theorem wz1PaperTubeCarrier_subset_of_lineCover_eighteen
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hscale : 18 * delta ≤ rho)
    (fine : Kakeya.DeltaTube delta)
    (coarse : Kakeya.DeltaTube rho)
    (fineLine : WZ1PaperTubeInLineClass fine)
    (coarseLine : WZ1PaperTubeInLineClass coarse)
    (covered : WZ1PaperTubeCovers fine coarse) :
    WZ2PaperTubeCarrierCovers fine coarse :=
  wz1PaperTubeCarrier_subset_of_lineCover
    hdelta hrho (by nlinarith) fine coarse fineLine coarseLine covered

end Kakeya.Assouad

end
