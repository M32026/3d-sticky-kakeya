import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DirectionClusterPlane
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DirectionAlignment
import MyLeanRepo.Kakeya.Assouad.WZ1.CrossPerturbation
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperUnitRescalingBasics

/-!
# Stable normal chart for positively oriented paper directions

Every paper line-class direction has third coordinate at least `1/2`.  Its
cross product with the first coordinate axis is therefore uniformly
nonzero.  Normalizing this cross product gives one global, stable normal
chart on the complete paper line class.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open InnerProductGeometry

/-- First coordinate unit vector. -/
def verticalNormalAxis : Point3 :=
  EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

/-- Stable unit normal for a positively oriented paper direction. -/
def stableVerticalNormal (direction : Point3) : Point3 :=
  NormedSpace.normalize (wz1Cross direction verticalNormalAxis)

lemma verticalNormalAxis_unit : ‖verticalNormalAxis‖ = 1 := by
  simp [verticalNormalAxis, EuclideanSpace.single_apply,
    EuclideanSpace.norm_eq, Fin.sum_univ_succ]

/-- The cross norm with the x-axis dominates the vertical coordinate. -/
lemma abs_vertical_coordinate_le_cross_axis
    (direction : Point3) :
    |direction 2| ≤ ‖wz1Cross direction verticalNormalAxis‖ := by
  have hcoordinate := PiLp.norm_apply_le
    (wz1Cross direction verticalNormalAxis) (2 : Fin 3)
  have heq : (wz1Cross direction verticalNormalAxis) 2 =
      -(direction 1) := by
    simp [wz1Cross, cross_apply, verticalNormalAxis,
      EuclideanSpace.single_apply]
  -- The second cross coordinate equals the vertical coordinate.
  have hcoordinateOne := PiLp.norm_apply_le
    (wz1Cross direction verticalNormalAxis) (1 : Fin 3)
  have heqOne : (wz1Cross direction verticalNormalAxis) 1 =
      direction 2 := by
    simp [wz1Cross, cross_apply, verticalNormalAxis,
      EuclideanSpace.single_apply]
  simpa [heqOne, Real.norm_eq_abs] using hcoordinateOne

/-- Paper line-class directions stay uniformly inside the stable chart. -/
lemma paper_direction_cross_axis_lower
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (hline : WZ1PaperTubeInLineClass tube) :
    (1 / 2 : ℝ) ≤
      ‖wz1Cross (wz1PaperDirection tube) verticalNormalAxis‖ := by
  exact hline.1.trans <|
    (le_abs_self (wz1PaperDirection tube 2)).trans <|
      abs_vertical_coordinate_le_cross_axis (wz1PaperDirection tube)

lemma stableVerticalNormal_unit
    {direction : Point3}
    (hcross : 0 < ‖wz1Cross direction verticalNormalAxis‖) :
    ‖stableVerticalNormal direction‖ = 1 := by
  apply NormedSpace.norm_normalize
  exact norm_pos_iff.mp hcross

lemma stableVerticalNormal_orthogonal (direction : Point3) :
    inner ℝ direction (stableVerticalNormal direction) = 0 := by
  unfold stableVerticalNormal NormedSpace.normalize
  rw [inner_smul_right]
  have hzero : inner ℝ direction
      (wz1Cross direction verticalNormalAxis) = 0 :=
    PureWZ2PlaneMap.inner_cross_self_left direction verticalNormalAxis
  rw [hzero, mul_zero]

/-- Incidence with the stable chart is controlled by cross-product distance
to its central direction. -/
lemma stableVerticalNormal_incidence
    (center direction : Point3)
    (hcenter : ‖center‖ = 1) (hdirection : ‖direction‖ = 1)
    (hcrossCenter : 0 < ‖wz1Cross center verticalNormalAxis‖) :
    |inner ℝ direction (stableVerticalNormal center)| ≤
      ‖wz1Cross center direction‖ := by
  exact abs_inner_le_cross_norm_of_orthogonal_unit
    center direction (stableVerticalNormal center)
    hcenter hdirection (stableVerticalNormal_unit hcrossCenter)
    (stableVerticalNormal_orthogonal center)

/-- In the positively oriented paper line class, projective cross-product
closeness is ordinary direction closeness.  The vertical-coordinate lower
bound excludes the antipodal branch. -/
lemma paper_direction_sub_norm_le_of_cross_le
    {delta : ℝ} {first second : Kakeya.DeltaTube delta}
    {kappa : ℝ}
    (hfirstLine : WZ1PaperTubeInLineClass first)
    (hsecondLine : WZ1PaperTubeInLineClass second)
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (hcross : ‖wz1Cross
      (wz1PaperDirection first)
      (wz1PaperDirection second)‖ ≤ kappa) :
    ‖wz1PaperDirection first - wz1PaperDirection second‖ ≤
      2 * kappa := by
  let u := wz1PaperDirection first
  let v := wz1PaperDirection second
  have hu : ‖u‖ = 1 := wz1PaperDirection_norm first
  have hv : ‖v‖ = 1 := wz1PaperDirection_norm second
  have hinnerLower : -(1 / 2 : ℝ) ≤ inner ℝ u v :=
    paper_inner_lower_bound hu hv hfirstLine.1 hsecondLine.1
  have hinnerUpper : inner ℝ u v ≤ 1 := by
    have hcs := abs_real_inner_le_norm u v
    rw [hu, hv, mul_one] at hcs
    exact (le_abs_self _).trans hcs
  have hcrossSq : ‖wz1Cross u v‖ ^ 2 =
      1 - (inner ℝ u v) ^ 2 := cross_norm_sq u v hu hv
  have hinnerNonnegative : 0 ≤ inner ℝ u v := by
    by_contra hnot
    have hinnerNegative : inner ℝ u v < 0 := lt_of_not_ge hnot
    have hinnerSquare : (inner ℝ u v) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      nlinarith
    have hcrossSquareLower : (3 / 4 : ℝ) ≤ ‖wz1Cross u v‖ ^ 2 := by
      nlinarith [hcrossSq]
    have hcrossSquareUpper : ‖wz1Cross u v‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      nlinarith [norm_nonneg (wz1Cross u v)]
    nlinarith
  have hnormSq : ‖u - v‖ ^ 2 =
      2 - 2 * inner ℝ u v := by
    rw [norm_sub_sq_real, hu, hv]
    ring
  have hfactor :
      1 - inner ℝ u v ≤ 1 - (inner ℝ u v) ^ 2 := by
    nlinarith
  have hnormSquareUpper : ‖u - v‖ ^ 2 ≤ 4 * kappa ^ 2 := by
    have hcrossKappaSquare : ‖wz1Cross u v‖ ^ 2 ≤ kappa ^ 2 := by
      nlinarith [norm_nonneg (wz1Cross u v)]
    nlinarith [hnormSq, hcrossSq, hfactor]
  nlinarith [norm_nonneg (u - v)]

/-- Normalization in the stable vertical chart is Lipschitz with an absolute
constant. -/
lemma stableVerticalNormal_sub_norm_le
    {first second : Point3}
    (hfirst : (1 / 2 : ℝ) ≤
      ‖wz1Cross first verticalNormalAxis‖)
    (hsecond : (1 / 2 : ℝ) ≤
      ‖wz1Cross second verticalNormalAxis‖) :
    ‖stableVerticalNormal first - stableVerticalNormal second‖ ≤
      2 * ‖first - second‖ := by
  let firstCross := wz1Cross first verticalNormalAxis
  let secondCross := wz1Cross second verticalNormalAxis
  have hfirstScaled : 1 ≤ ‖(2 : ℝ) • firstCross‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hsecondScaled : 1 ≤ ‖(2 : ℝ) • secondCross‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hnormalizeFirst :
      NormedSpace.normalize ((2 : ℝ) • firstCross) =
        stableVerticalNormal first := by
    rw [NormedSpace.normalize_smul_of_pos (by norm_num : (0 : ℝ) < 2)]
    rfl
  have hnormalizeSecond :
      NormedSpace.normalize ((2 : ℝ) • secondCross) =
        stableVerticalNormal second := by
    rw [NormedSpace.normalize_smul_of_pos (by norm_num : (0 : ℝ) < 2)]
    rfl
  rw [← hnormalizeFirst, ← hnormalizeSecond]
  calc
    ‖NormedSpace.normalize ((2 : ℝ) • firstCross) -
        NormedSpace.normalize ((2 : ℝ) • secondCross)‖ ≤
        ‖(2 : ℝ) • firstCross - (2 : ℝ) • secondCross‖ :=
      norm_normalize_sub_normalize_le_norm_sub
        hfirstScaled hsecondScaled
    _ = 2 * ‖firstCross - secondCross‖ := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg
        (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * ‖first - second‖ := by
      gcongr
      have heq : firstCross - secondCross =
          wz1Cross (first - second) verticalNormalAxis := by
        dsimp only [firstCross, secondCross]
        have hfirstDecomp : first = second + (first - second) := by abel
        rw [hfirstDecomp, wz1Cross_add_left]
        abel
      rw [heq]
      simpa [verticalNormalAxis_unit] using
        wz1Cross_norm_le (first - second) verticalNormalAxis

/-- Fine directions covered by the same coarse parent have stable normals
within `2 rho`. -/
lemma stableVerticalNormal_shared_parent
    {delta rho : ℝ}
    {first second : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube rho}
    (hfirstLine : WZ1PaperTubeInLineClass first)
    (hsecondLine : WZ1PaperTubeInLineClass second)
    (hfirstCover : WZ1PaperTubeCovers first parent)
    (hsecondCover : WZ1PaperTubeCovers second parent) :
    ‖stableVerticalNormal (wz1PaperDirection first) -
        stableVerticalNormal (wz1PaperDirection second)‖ ≤ 2 * rho := by
  apply (stableVerticalNormal_sub_norm_le
    (paper_direction_cross_axis_lower hfirstLine)
    (paper_direction_cross_axis_lower hsecondLine)).trans
  have halignFirst := paper_cover_direction_alignment hfirstCover
  have halignSecond := paper_cover_direction_alignment hsecondCover
  have htriangle :
      ‖wz1PaperDirection first - wz1PaperDirection second‖ ≤
        ‖wz1PaperDirection first - wz1PaperDirection parent‖ +
          ‖wz1PaperDirection parent - wz1PaperDirection second‖ := by
    have heq : wz1PaperDirection first - wz1PaperDirection second =
        (wz1PaperDirection first - wz1PaperDirection parent) +
          (wz1PaperDirection parent - wz1PaperDirection second) := by
      abel
    rw [heq]
    exact norm_add_le _ _
  rw [norm_sub_rev (wz1PaperDirection parent)
    (wz1PaperDirection second)] at htriangle
  nlinarith

end Kakeya.Assouad.PureWZ2

end
