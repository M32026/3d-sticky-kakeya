import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalPopularBoxPullback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalNormalizationLineGeometry
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance

/-!
# Zero-point control from an occupied horizontal popular box

Every tube retained by the nonempty pullback has an actual source point whose
exact triangular image lies in the selected horizontal box.  Comparing that
point with the source axis first at the same height and then at the midpoint of
the selected interval gives a quantitative bound for the zero point after the
final horizontal dilation.

This argument uses the literal source carrier and the exact combined affine
map.  In particular, it does not infer a geometric conclusion from an
arbitrary union representation.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

private theorem dPhiLin_horizontal_coordinate_bound
    (g : SlopeFunction) {c d m : ℝ}
    (hcd : c < d) (hm : 0 < m) (hmOne : m ≤ 1)
    (hlengthOne : d - c ≤ 1)
    (hgmid : |g (c + (d - c) / 2)| ≤ 1)
    (vector : Point3) (coordinate : Fin 3)
    (hcoordinate : coordinate = 0 ∨ coordinate = 1) :
    |dPhiLin g c d m vector coordinate| ≤ 2 * ‖vector‖ := by
  rcases hcoordinate with rfl | rfl
  · simp only [dPhiLin, point3_coord0]
    calc
      |vector 0 + g (c + (d - c) / 2) * vector 1| ≤
          |vector 0| +
            |g (c + (d - c) / 2)| * |vector 1| := by
        simpa [abs_mul] using
          abs_add_le (vector 0)
            (g (c + (d - c) / 2) * vector 1)
      _ ≤ ‖vector‖ + 1 * ‖vector‖ := by
        gcongr
        · simpa [Real.norm_eq_abs] using PiLp.norm_apply_le vector 0
        · simpa [Real.norm_eq_abs] using PiLp.norm_apply_le vector 1
      _ = 2 * ‖vector‖ := by ring
  · simp only [dPhiLin, point3_coord1]
    have hfactorNonnegative : 0 ≤ m * (d - c) / 2 := by positivity
    have hfactorOne : m * (d - c) / 2 ≤ 1 := by
      nlinarith [mul_nonneg hm.le (sub_nonneg.mpr hcd.le)]
    rw [abs_mul, abs_of_nonneg hfactorNonnegative]
    calc
      m * (d - c) / 2 * |vector 1| ≤ 1 * ‖vector‖ := by
        gcongr
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le vector 1
      _ ≤ 2 * ‖vector‖ := by nlinarith [norm_nonneg vector]

/-- An occupied horizontal popular box controls both horizontal coordinates of
the exact combined-image zero point.  The displayed bound separates the box
half-width from the source carrier and height-transport errors. -/
theorem pureWZ2HorizontalPopularPullback_zeroPoint_bound
    {sourceDelta targetDelta c d m width : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm)
    (popular : PureWZ2HorizontalPopularBoxData raw.exactShading width)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hsourceDelta : 0 < sourceDelta)
    (hmOne : m ≤ 1) (hlengthOne : d - c ≤ 1)
    (hgmid : |g (c + (d - c) / 2)| ≤ 1)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hsourceHeight : ∀ index point,
      point ∈ sourceShading.carrier index → point 2 ∈ Set.Icc c d)
    (index : Fin
      (pureWZ2HorizontalPopularPullbackSourceSubfamily raw popular).family.card)
    (coordinate : Fin 3)
    (hcoordinate : coordinate = 0 ∨ coordinate = 1) :
    |pureWZ2HorizontalNormalizedZeroPoint g c d m anisotropicCenter
        popular.center lambda
        ((pureWZ2HorizontalPopularPullbackSourceSubfamily raw popular).family.tube
          index) coordinate| ≤
      lambda * (width / 2 + 2 * ((d - c) + 18 * sourceDelta)) := by
  let selected := pureWZ2HorizontalPopularPullbackSourceSubfamily raw popular
  let source := sourceFamily.tube (selected.embedding index)
  have hsourceEq : selected.family.tube index = source := selected.tube_eq index
  rw [hsourceEq]
  rcases pureWZ2HorizontalPopularPullbackNonemptyShading_carrier_nonempty
      raw popular index with ⟨point, hpoint⟩
  have hpointPullback :
      point ∈ (pureWZ2HorizontalPopularPullbackShading raw popular).carrier
        (selected.embedding index) := by
    simpa [selected] using hpoint
  have hpointSource : point ∈ sourceShading.carrier (selected.embedding index) :=
    hpointPullback.1
  have hpointBox :
      anisotropicCenteredRescalingMap g c d m anisotropicCenter point ∈
        popular.box := by
    have hpreimage := hpointPullback.2
    change (anisotropicCenteredRescalingAffineEquiv
      g c d m anisotropicCenter hcd hm) point ∈ popular.box at hpreimage
    simpa using hpreimage
  have hpointHeight := hsourceHeight (selected.embedding index) point hpointSource
  let midpoint : ℝ := c + (d - c) / 2
  let midpointAxis : Point3 := wz1PaperAxisPointAtHeight source midpoint
  let sameHeightAxis : Point3 := wz1PaperAxisPointAtHeight source (point 2)
  have hline : WZ1PaperTubeInLineClass source :=
    hsourceLine (selected.embedding index)
  have hheight : |midpoint - point 2| ≤ (d - c) / 2 := by
    dsimp only [midpoint]
    rw [abs_le]
    constructor
    · nlinarith [hpointHeight.2]
    · nlinarith [hpointHeight.1]
  have haxisMove : dist midpointAxis sameHeightAxis ≤ d - c := by
    have hraw := wz1Paper_axisPointAtHeight_dist_le_of_axis_point
      hline midpoint ((d - c) / 2)
        (wz1PaperAxisPointAtHeight_mem_axis source (point 2))
        (by
          rw [wz1PaperAxisPointAtHeight_coord_two hline]
          exact hheight)
    calc
      dist midpointAxis sameHeightAxis ≤ 2 * ((d - c) / 2) := by
        simpa [midpointAxis, sameHeightAxis] using hraw
      _ = d - c := by ring
  have hcarrier : point ∈ wz1PaperTubeCarrier source :=
    sourceShading.subset_body (selected.embedding index) hpointSource
  have hpointAxis : dist point sameHeightAxis ≤ 18 * sourceDelta := by
    simpa [sameHeightAxis] using
      wz2_paper_carrier_same_height_dist_18delta
        hsourceDelta source hline hcarrier
  have hsourceDistance : dist midpointAxis point ≤
      (d - c) + 18 * sourceDelta := by
    calc
      dist midpointAxis point ≤
          dist midpointAxis sameHeightAxis + dist sameHeightAxis point :=
        dist_triangle _ _ _
      _ ≤ (d - c) + 18 * sourceDelta := by
        gcongr
        simpa [dist_comm] using hpointAxis
  let rawZero := anisotropicCenteredRescalingMap g c d m
    anisotropicCenter midpointAxis
  let rawPoint := anisotropicCenteredRescalingMap g c d m
    anisotropicCenter point
  have hrawDifference : rawZero - rawPoint =
      dPhiLin g c d m (midpointAxis - point) := by
    exact anisotropicCenteredRescalingMap_sub g c d m anisotropicCenter
      midpointAxis point
  have hrawCoordinate : |(rawZero - rawPoint) coordinate| ≤
      2 * ((d - c) + 18 * sourceDelta) := by
    rw [hrawDifference]
    exact (dPhiLin_horizontal_coordinate_bound g hcd hm hmOne hlengthOne
      hgmid (midpointAxis - point) coordinate hcoordinate).trans <| by
        rw [← dist_eq_norm]
        gcongr
  have hboxCoordinate : |rawPoint coordinate - popular.center coordinate| ≤
      width / 2 := by
    rw [popular.box_eq] at hpointBox
    have haxisBox := hpointBox.1 coordinate
    rcases hcoordinate with rfl | rfl <;>
      simpa [rawPoint, popular.box_eq, pureWZ2HorizontalSourceBox,
        wz1MildRescalingSourceBox, wz1AxisBox, point3] using haxisBox
  have hbeforeDilation : |rawZero coordinate - popular.center coordinate| ≤
      width / 2 + 2 * ((d - c) + 18 * sourceDelta) := by
    calc
      |rawZero coordinate - popular.center coordinate| =
          |(rawZero - rawPoint) coordinate +
            (rawPoint coordinate - popular.center coordinate)| := by
        congr 1
        simp only [PiLp.sub_apply]
        ring
      _ ≤ |(rawZero - rawPoint) coordinate| +
          |rawPoint coordinate - popular.center coordinate| := abs_add_le _ _
      _ ≤ 2 * ((d - c) + 18 * sourceDelta) + width / 2 :=
        add_le_add hrawCoordinate hboxCoordinate
      _ = width / 2 + 2 * ((d - c) + 18 * sourceDelta) := by ring
  have hzeroFormula :
      pureWZ2HorizontalNormalizedZeroPoint g c d m anisotropicCenter
          popular.center lambda source coordinate =
        lambda * (rawZero coordinate - popular.center coordinate) := by
    rcases hcoordinate with rfl | rfl <;>
      simp [pureWZ2HorizontalNormalizedZeroPoint, midpoint, midpointAxis,
        rawZero, pureWZ2HorizontalNormalizedMap, point3,
        popular.center_height]
  rw [hzeroFormula, abs_mul, abs_of_pos hlambda]
  exact mul_le_mul_of_nonneg_left hbeforeDilation hlambda.le

end Kakeya.Assouad

end
