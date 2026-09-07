import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.PropertyPHeightBridge

/-!
# Distance in a cropped full-line paper tube from anchored height
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Metric Set

/-- Signed axial coordinate in the positively oriented paper chart. -/
def paperTubeHeight
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) (point : Point3) : ℝ :=
  inner ℝ (point - wz1TubeAxisZeroPoint tube) (wz1PaperDirection tube)

lemma abs_paperTubeHeight_sub_eq_distinguishedTubeHeight_sub
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (first second : Point3) :
    |paperTubeHeight tube first - paperTubeHeight tube second| =
      |distinguishedTubeHeight tube first -
        distinguishedTubeHeight tube second| := by
  have hpaperDifference :
      paperTubeHeight tube first - paperTubeHeight tube second =
        inner ℝ (first - second) (wz1PaperDirection tube) := by
    unfold paperTubeHeight
    rw [← inner_sub_left]
    congr 1
    abel
  have hrawDifference :
      distinguishedTubeHeight tube first -
          distinguishedTubeHeight tube second =
        inner ℝ (first - second) tube.direction := by
    unfold distinguishedTubeHeight
    rw [← inner_sub_left]
    congr 1
    abel
  have hpaper : wz1PaperDirection tube = tube.direction ∨
      wz1PaperDirection tube = -tube.direction := by
    unfold wz1PaperDirection
    split_ifs <;> simp
  rcases hpaper with hpaper | hpaper
  · rw [hpaperDifference, hrawDifference, hpaper]
  · rw [hpaperDifference, hrawDifference, hpaper, inner_neg_right, abs_neg]

/-- Two points in the same cropped paper tube are controlled by their genuine
anchored heights plus the two thickness errors. -/
lemma same_paper_tube_dist_le_height_add_twenty_four_delta
    {delta : ℝ} (hdelta : 0 < delta)
    (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube)
    {first second : Point3}
    (hfirst : first ∈ wz1PaperTubeCarrier tube)
    (hsecond : second ∈ wz1PaperTubeCarrier tube) :
    dist first second ≤
      |distinguishedTubeHeight tube first -
        distinguishedTubeHeight tube second| + 24 * delta := by
  have hclosed : IsClosed (tubeAxisLine tube) := isClosed_tubeAxisLine tube
  rcases exists_dist_le_of_mem_cthickening_closed hclosed
      (by positivity : 0 ≤ 6 * delta) hfirst.1 with
    ⟨firstAxis, hfirstAxis, hfirstDist⟩
  rcases exists_dist_le_of_mem_cthickening_closed hclosed
      (by positivity : 0 ≤ 6 * delta) hsecond.1 with
    ⟨secondAxis, hsecondAxis, hsecondDist⟩
  rcases hfirstAxis with ⟨firstParameter, rfl⟩
  rcases hsecondAxis with ⟨secondParameter, rfl⟩
  let firstAxis := tube.base + firstParameter • tube.direction
  let secondAxis := tube.base + secondParameter • tube.direction
  have hfirstHeightAxis : distinguishedTubeHeight tube firstAxis =
      firstParameter - 1 / 2 := by
    simp only [distinguishedTubeHeight, firstAxis]
    rw [show tube.base + firstParameter • tube.direction -
        (tube.base + (1 / 2 : ℝ) • tube.direction) =
        (firstParameter - 1 / 2) • tube.direction by module]
    rw [inner_smul_left, real_inner_self_eq_norm_sq, tube.direction_unit]
    norm_num
  have hsecondHeightAxis : distinguishedTubeHeight tube secondAxis =
      secondParameter - 1 / 2 := by
    simp only [distinguishedTubeHeight, secondAxis]
    rw [show tube.base + secondParameter • tube.direction -
        (tube.base + (1 / 2 : ℝ) • tube.direction) =
        (secondParameter - 1 / 2) • tube.direction by module]
    rw [inner_smul_left, real_inner_self_eq_norm_sq, tube.direction_unit]
    norm_num
  have hfirstHeightError :
      |distinguishedTubeHeight tube first -
        distinguishedTubeHeight tube firstAxis| ≤ 6 * delta := by
    exact (distinguishedTubeHeight_sub_le_dist
      tube first firstAxis).trans hfirstDist
  have hsecondHeightError :
      |distinguishedTubeHeight tube second -
        distinguishedTubeHeight tube secondAxis| ≤ 6 * delta := by
    exact (distinguishedTubeHeight_sub_le_dist
      tube second secondAxis).trans hsecondDist
  have hparameter : |firstParameter - secondParameter| ≤
      |distinguishedTubeHeight tube first -
        distinguishedTubeHeight tube second| + 12 * delta := by
    have halgebra : firstParameter - secondParameter =
        (distinguishedTubeHeight tube first -
          distinguishedTubeHeight tube second) -
        (distinguishedTubeHeight tube first -
          distinguishedTubeHeight tube firstAxis) +
        (distinguishedTubeHeight tube second -
          distinguishedTubeHeight tube secondAxis) := by
      rw [hfirstHeightAxis, hsecondHeightAxis]
      ring
    rw [halgebra]
    calc
      |(distinguishedTubeHeight tube first -
          distinguishedTubeHeight tube second) -
          (distinguishedTubeHeight tube first -
            distinguishedTubeHeight tube firstAxis) +
          (distinguishedTubeHeight tube second -
            distinguishedTubeHeight tube secondAxis)|
          ≤ |distinguishedTubeHeight tube first -
              distinguishedTubeHeight tube second| +
            |distinguishedTubeHeight tube first -
              distinguishedTubeHeight tube firstAxis| +
            |distinguishedTubeHeight tube second -
              distinguishedTubeHeight tube secondAxis| := by
              calc
                _ ≤ |(distinguishedTubeHeight tube first -
                    distinguishedTubeHeight tube second) -
                    (distinguishedTubeHeight tube first -
                      distinguishedTubeHeight tube firstAxis)| +
                    |distinguishedTubeHeight tube second -
                      distinguishedTubeHeight tube secondAxis| :=
                  abs_add_le _ _
                _ ≤ (|distinguishedTubeHeight tube first -
                    distinguishedTubeHeight tube second| +
                    |distinguishedTubeHeight tube first -
                      distinguishedTubeHeight tube firstAxis|) +
                    |distinguishedTubeHeight tube second -
                      distinguishedTubeHeight tube secondAxis| := by
                  gcongr
                  exact abs_sub _ _
      _ ≤ |distinguishedTubeHeight tube first -
          distinguishedTubeHeight tube second| + 12 * delta := by
        linarith
  have haxisDistance : dist firstAxis secondAxis =
      |firstParameter - secondParameter| := by
    rw [dist_eq_norm]
    have hdifference : firstAxis - secondAxis =
        (firstParameter - secondParameter) • tube.direction := by
      dsimp only [firstAxis, secondAxis]
      module
    rw [hdifference, norm_smul, tube.direction_unit, mul_one]
    exact Real.norm_eq_abs _
  calc
    dist first second ≤
        dist first firstAxis + dist firstAxis secondAxis +
          dist secondAxis second := by
      calc
        dist first second ≤ dist first firstAxis + dist firstAxis second :=
          dist_triangle _ _ _
        _ ≤ dist first firstAxis +
            (dist firstAxis secondAxis + dist secondAxis second) := by
          gcongr
          exact dist_triangle _ _ _
        _ = dist first firstAxis + dist firstAxis secondAxis +
            dist secondAxis second := by ring
    _ ≤ 6 * delta + |firstParameter - secondParameter| +
        6 * delta := by
      rw [haxisDistance, dist_comm secondAxis second]
      gcongr
    _ ≤ |distinguishedTubeHeight tube first -
          distinguishedTubeHeight tube second| + 24 * delta := by
      linarith

lemma same_paper_tube_dist_le_paper_height_add_twenty_four_delta
    {delta : ℝ} (hdelta : 0 < delta)
    (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube)
    {first second : Point3}
    (hfirst : first ∈ wz1PaperTubeCarrier tube)
    (hsecond : second ∈ wz1PaperTubeCarrier tube) :
    dist first second ≤
      |paperTubeHeight tube first - paperTubeHeight tube second| +
        24 * delta := by
  rw [abs_paperTubeHeight_sub_eq_distinguishedTubeHeight_sub]
  exact same_paper_tube_dist_le_height_add_twenty_four_delta
    hdelta tube hline hfirst hsecond

end Kakeya.Assouad.PureWZ2

end
