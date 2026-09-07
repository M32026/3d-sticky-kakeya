import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainmentStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoverCarrierContainment
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryHelpers

/-!
# Active coarse cells lie in their paper parent

Given a point `p` where a side-`rho` grid cube meets the fine paper tube:

1. the same-height fine-axis point is within `18 * delta` of `p`;
2. the fine-to-coarse line-cover relation costs at most `3 * rho`;
3. the grid-cube diameter is strictly less than `2 * rho`.

The scale margin `18 * delta ≤ rho` then puts the whole cube in the
`6 * rho` neighborhood of the coarse axis.  The explicit crop premise gives
the second conjunct of the coarse paper carrier.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric

/--
For a point in the paper carrier, the axis point at the same height is within
`18 * delta`.
-/
lemma wz2_paper_carrier_same_height_dist_18delta
    {delta : ℝ} (hdelta : 0 < delta)
    (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube)
    {point : Point3} (hpoint : point ∈ wz1PaperTubeCarrier tube) :
    dist point
        (wz1PaperAxisPointAtHeight tube (point (2 : Fin 3))) ≤
      18 * delta := by
  have hthick :
      point ∈ Metric.cthickening (6 * delta) (tubeAxisLine tube) :=
    hpoint.1
  have hline_closed : IsClosed (tubeAxisLine tube) :=
    isClosed_tubeAxisLine tube
  have hpos6 : 0 ≤ 6 * delta := by positivity
  rcases exists_dist_le_of_mem_cthickening_closed
      hline_closed hpos6 hthick with
    ⟨axisPoint, haxisPoint_line, haxisPoint_dist⟩
  let direction := wz1PaperDirection tube
  let zeroPoint := wz1TubeAxisZeroPoint tube
  let height := point (2 : Fin 3)
  let sameHeightParameter := height / (direction (2 : Fin 3))
  let sameHeightPoint := wz1PaperAxisPointAtHeight tube height
  have hsameHeight_expand :
      sameHeightPoint =
        zeroPoint + sameHeightParameter • direction := by
    simp [sameHeightPoint, sameHeightParameter, zeroPoint, direction,
      wz1PaperAxisPointAtHeight] <;> rfl
  have hdirection_two :
      (1 / 2 : ℝ) ≤ direction (2 : Fin 3) :=
    hline.1
  have hdirection_two_pos :
      0 < direction (2 : Fin 3) := by
    linarith
  have hzeroPoint_two :
      zeroPoint (2 : Fin 3) = 0 :=
    wz1TubeAxisZeroPoint_coord_two tube hline.vertical
  have hsameHeight_two :
      sameHeightPoint (2 : Fin 3) = height := by
    rw [hsameHeight_expand]
    simp [sameHeightParameter, zeroPoint, hzeroPoint_two,
      hdirection_two_pos.ne']
  have hline_eq :
      tubeAxisLine tube =
        {axisPoint |
          ∃ parameter : ℝ,
            axisPoint = zeroPoint + parameter • direction} :=
    tubeAxisLine_eq_affineSpan tube hline.vertical
  have haxisPoint_set :
      axisPoint ∈
        {axisPoint |
          ∃ parameter : ℝ,
            axisPoint = zeroPoint + parameter • direction} := by
    rw [← hline_eq]
    exact haxisPoint_line
  rcases haxisPoint_set with
    ⟨axisParameter, haxisPoint_eq⟩
  have hdirection_norm : ‖direction‖ = 1 :=
    wz1PaperDirection_norm tube
  have hsub :
      zeroPoint + axisParameter • direction - sameHeightPoint =
        (axisParameter - sameHeightParameter) • direction := by
    rw [hsameHeight_expand]
    simp [sub_smul] <;> abel
  have haxis_sameHeight_dist :
      dist axisPoint sameHeightPoint =
        |axisParameter - sameHeightParameter| := by
    rw [haxisPoint_eq, dist_eq_norm, hsub, norm_smul,
      hdirection_norm, mul_one]
    simp [Real.norm_eq_abs]
  have hcoord_diff :
      |axisPoint (2 : Fin 3) -
          sameHeightPoint (2 : Fin 3)| =
        |axisParameter - sameHeightParameter| *
          direction (2 : Fin 3) := by
    rw [haxisPoint_eq]
    have hcoord :
        (zeroPoint + axisParameter • direction) (2 : Fin 3) -
            sameHeightPoint (2 : Fin 3) =
          (axisParameter - sameHeightParameter) *
            direction (2 : Fin 3) := by
      rw [hsameHeight_expand]
      simp [sameHeightParameter, zeroPoint, hzeroPoint_two,
        smul_eq_mul] <;> ring
    rw [hcoord, abs_mul, abs_of_pos hdirection_two_pos]
  have haxis_sameHeight_dist_div :
      dist axisPoint sameHeightPoint =
        |axisPoint (2 : Fin 3) -
            sameHeightPoint (2 : Fin 3)| /
          direction (2 : Fin 3) := by
    rw [haxis_sameHeight_dist, hcoord_diff]
    field_simp [hdirection_two_pos.ne']
  have hcoord_eq :
      |axisPoint (2 : Fin 3) -
          sameHeightPoint (2 : Fin 3)| =
        |axisPoint (2 : Fin 3) - point (2 : Fin 3)| := by
    rw [hsameHeight_two]
  rw [hcoord_eq] at haxis_sameHeight_dist_div
  have hcoord_bound :
      |axisPoint (2 : Fin 3) - point (2 : Fin 3)| ≤
        dist point axisPoint := by
    have hbound :
        |axisPoint (2 : Fin 3) - point (2 : Fin 3)| ≤
          dist axisPoint point :=
      abs_coord_sub_le_dist (2 : Fin 3)
    rw [dist_comm axisPoint point] at hbound
    exact hbound
  have haxis_sameHeight_bound :
      dist axisPoint sameHeightPoint ≤ 12 * delta := by
    rw [haxis_sameHeight_dist_div]
    have hdiv_coord :
        |axisPoint (2 : Fin 3) - point (2 : Fin 3)| /
              direction (2 : Fin 3) ≤
          dist point axisPoint / direction (2 : Fin 3) := by
      gcongr <;> linarith
    have hdiv_distance :
        dist point axisPoint / direction (2 : Fin 3) ≤
          (6 * delta) / (1 / 2 : ℝ) := by
      gcongr <;> linarith
    linarith
  have hpoint_sameHeight :
      dist point sameHeightPoint ≤ 18 * delta := by
    have htriangle :
        dist point sameHeightPoint ≤
          dist point axisPoint +
            dist axisPoint sameHeightPoint :=
      dist_triangle point axisPoint sameHeightPoint
    linarith
  exact hpoint_sameHeight

/--
Two points in the same side-`rho` paper grid cube have Euclidean distance
strictly less than `2 * rho`.
-/
lemma wz1_paper_grid_cube_diameter_lt_two_rho
    {rho : ℝ} (hrho : 0 < rho)
    {cell : ℤ × ℤ × ℤ} {first second : Point3}
    (hfirst : first ∈ wz1PaperGridCube rho cell)
    (hsecond : second ∈ wz1PaperGridCube rho cell) :
    dist first second < 2 * rho := by
  have hbox := wz1PaperGridCube_eq_Ico hrho cell
  rw [hbox] at hfirst hsecond
  rcases hfirst with
    ⟨hfirst0_lo, hfirst0_hi,
      hfirst1_lo, hfirst1_hi,
      hfirst2_lo, hfirst2_hi⟩
  rcases hsecond with
    ⟨hsecond0_lo, hsecond0_hi,
      hsecond1_lo, hsecond1_hi,
      hsecond2_lo, hsecond2_hi⟩
  have hzero :
      |first 0 - second 0| < rho := by
    rw [abs_lt]
    constructor <;> linarith
  have hone :
      |first 1 - second 1| < rho := by
    rw [abs_lt]
    constructor <;> linarith
  have htwo :
      |first 2 - second 2| < rho := by
    rw [abs_lt]
    constructor <;> linarith
  have hdist_sq :
      dist first second ^ 2 =
        ∑ coordinate : Fin 3,
          (first coordinate - second coordinate) ^ 2 := by
    rw [dist_eq_norm, PiLp.norm_eq_of_L2]
    have hnonneg :
        0 ≤ ∑ coordinate : Fin 3,
          ‖(first - second) coordinate‖ ^ 2 := by
      positivity
    rw [Real.sq_sqrt hnonneg]
    apply Finset.sum_congr rfl
    intro coordinate _
    simp [PiLp.sub_apply] <;> ring
  have hsum :
      ∑ coordinate : Fin 3,
          (first coordinate - second coordinate) ^ 2 =
        (first 0 - second 0) ^ 2 +
          (first 1 - second 1) ^ 2 +
          (first 2 - second 2) ^ 2 := by
    simp [Fin.sum_univ_succ] <;> ring
  have hsq_zero :
      (first 0 - second 0) ^ 2 < rho ^ 2 := by
    nlinarith [abs_lt.mp hzero]
  have hsq_one :
      (first 1 - second 1) ^ 2 < rho ^ 2 := by
    nlinarith [abs_lt.mp hone]
  have hsq_two :
      (first 2 - second 2) ^ 2 < rho ^ 2 := by
    nlinarith [abs_lt.mp htwo]
  have hdist_bound :
      dist first second ^ 2 < 3 * rho ^ 2 := by
    rw [hdist_sq, hsum]
    linarith
  have hthree_four :
      3 * rho ^ 2 < (2 * rho) ^ 2 := by
    nlinarith
  have hdist_nonneg :
      0 ≤ dist first second :=
    dist_nonneg
  nlinarith

theorem wz2_prop_sticky_coarse_cell_containment :
    WZ2PropStickyCoarseCellContainmentStatement := by
  intro delta rho hdelta hrho h18delta fineTube coarseTube
    hfine hcoarse hcover coarseCell hnonempty hcrop
  rcases hnonempty with ⟨point, hpoint⟩
  have hpoint_cube :
      point ∈ wz1PaperGridCube rho coarseCell :=
    hpoint.1
  have hpoint_fine :
      point ∈ wz1PaperTubeCarrier fineTube :=
    hpoint.2
  let height : ℝ := point (2 : Fin 3)
  let fineAxisPoint :=
    wz1PaperAxisPointAtHeight fineTube height
  let coarseAxisPoint :=
    wz1PaperAxisPointAtHeight coarseTube height
  have hheight_abs :
      |height| ≤ 1 := by
    have hbox :
        point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
      hpoint_fine.2
    simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
  have hfine_distance :
      dist point fineAxisPoint ≤ 18 * delta :=
    wz2_paper_carrier_same_height_dist_18delta
      hdelta fineTube hfine hpoint_fine
  have haxis_distance :
      dist fineAxisPoint coarseAxisPoint ≤
        6 * wz1PaperLineDistance fineTube coarseTube :=
    wz1PaperAxisPointAtHeight_dist_le
      hfine hcoarse hheight_abs
  have hcover' :
      wz1PaperLineDistance fineTube coarseTube ≤ rho / 2 :=
    hcover
  have hcoarse_distance :
      dist fineAxisPoint coarseAxisPoint ≤ 3 * rho := by
    calc
      dist fineAxisPoint coarseAxisPoint
          ≤ 6 * wz1PaperLineDistance fineTube coarseTube :=
        haxis_distance
      _ ≤ 6 * (rho / 2) := by
        gcongr
      _ = 3 * rho := by
        ring
  have hcoarse_axis :
      coarseAxisPoint ∈ tubeAxisLine coarseTube :=
    wz1PaperAxisPointAtHeight_mem_axis coarseTube height
  intro other hother
  have hcube_distance :
      dist other point < 2 * rho :=
    wz1_paper_grid_cube_diameter_lt_two_rho
      hrho hother hpoint_cube
  have hcarrier_distance :
      dist other coarseAxisPoint ≤ 6 * rho := by
    have htriangle :
        dist other coarseAxisPoint ≤
          dist other point +
            dist point fineAxisPoint +
              dist fineAxisPoint coarseAxisPoint := by
      calc
        dist other coarseAxisPoint
            ≤ dist other point +
                dist point coarseAxisPoint :=
          dist_triangle other point coarseAxisPoint
        _ ≤ dist other point +
              (dist point fineAxisPoint +
                dist fineAxisPoint coarseAxisPoint) := by
          gcongr
          exact
            dist_triangle point fineAxisPoint coarseAxisPoint
        _ = dist other point +
              dist point fineAxisPoint +
                dist fineAxisPoint coarseAxisPoint := by
          ring
    have hstrict :
        dist other point +
              dist point fineAxisPoint +
                dist fineAxisPoint coarseAxisPoint <
          2 * rho + 18 * delta + 3 * rho := by
      linarith
    have hmargin :
        2 * rho + 18 * delta + 3 * rho ≤ 6 * rho := by
      linarith
    linarith
  have hthickening :
      other ∈
        Metric.cthickening (6 * rho)
          (tubeAxisLine coarseTube) :=
    Metric.mem_cthickening_of_dist_le
      other coarseAxisPoint (6 * rho)
      (tubeAxisLine coarseTube)
      hcoarse_axis hcarrier_distance
  have hbox :
      other ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
    hcrop hother
  exact ⟨hthickening, hbox⟩

end Kakeya.Assouad

end
