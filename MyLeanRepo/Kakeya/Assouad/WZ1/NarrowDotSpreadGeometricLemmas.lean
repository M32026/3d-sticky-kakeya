import MyLeanRepo.Kakeya.Assouad.WZ1.AngleGeometryBase
import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowStripPigeonhole

/-!
# Geometric helpers for the narrow dot-spread branch

These are the elementary planar estimates used when transverse concentration
of the two endpoint classes fails to synchronize.
-/

namespace Kakeya.Assouad

/--
A point separated from the origin and lying in the strip orthogonal to
`direction` has a large component perpendicular to `direction`.
-/
lemma large_perp_component_three_sevenths
    {point direction : Point2} {width : ℝ}
    (hdirection : ‖direction‖ = 1)
    (hseparated : 1 / 2 ≤ dist point 0)
    (hstrip :
      point ∈
        wz1LineNeighborhood 0
          (wz1Perp2 direction) width)
    (hwidth : width ≤ 1 / 4) :
    3 / 7 ≤
      |inner ℝ point (wz1Perp2 direction)| := by
  have hnorm :
      ‖point‖ ^ 2 =
        (inner ℝ point direction) ^ 2 +
          (inner ℝ point
            (wz1Perp2 direction)) ^ 2 := by
    have hcross :=
      norm_cross_identity point direction hdirection
    have hcrossEq :
        cross2 point direction =
          -inner ℝ point
            (wz1Perp2 direction) := by
      simp [cross2, inner2_eq, wz1Perp2_coords]
      ring
    rw [hcrossEq] at hcross
    ring_nf at hcross ⊢
    exact hcross
  have hnormLower : 1 / 2 ≤ ‖point‖ := by
    simpa [dist_eq_norm] using hseparated
  have hperpPerp :
      wz1Perp2 (wz1Perp2 direction) = -direction := by
    ext index
    fin_cases index <;>
      simp [wz1Perp2_coords] <;> ring
  have hdirectionBound :
      |inner ℝ point direction| ≤ width := by
    have h :=
      hstrip
    change
      |inner ℝ (point - 0)
        (wz1Perp2 (wz1Perp2 direction))| ≤ width at h
    simpa [hperpPerp, inner_neg_right, abs_neg] using h
  have hwidthNonnegative : 0 ≤ width :=
    (abs_nonneg (inner ℝ point direction)).trans
      hdirectionBound
  have hdirectionSquare :
      (inner ℝ point direction) ^ 2 ≤ width ^ 2 := by
    rw [show
      (inner ℝ point direction) ^ 2 =
        |inner ℝ point direction| ^ 2 by rw [sq_abs]]
    gcongr
  have hnormSquare : 1 / 4 ≤ ‖point‖ ^ 2 := by
    nlinarith [norm_nonneg point]
  have hperpSquare :
      3 / 16 ≤
        (inner ℝ point
          (wz1Perp2 direction)) ^ 2 := by
    have hwidthSquare : width ^ 2 ≤ 1 / 16 := by
      nlinarith
    nlinarith [hnorm]
  have hstrict :
      (3 / 7 : ℝ) ^ 2 <
        (inner ℝ point
          (wz1Perp2 direction)) ^ 2 := by
    norm_num at hperpSquare ⊢
    linarith
  rw [show
    (inner ℝ point (wz1Perp2 direction)) ^ 2 =
      |inner ℝ point (wz1Perp2 direction)| ^ 2 by
        rw [sq_abs]] at hstrict
  nlinarith [abs_nonneg
    (inner ℝ point (wz1Perp2 direction))]

/-- A convenient decimal-free weakening of the sharp rational bound. -/
lemma large_perp_component_two_fifths
    {point direction : Point2} {width : ℝ}
    (hdirection : ‖direction‖ = 1)
    (hseparated : 1 / 2 ≤ dist point 0)
    (hstrip :
      point ∈
        wz1LineNeighborhood 0
          (wz1Perp2 direction) width)
    (hwidth : width ≤ 1 / 4) :
    2 / 5 ≤
      |inner ℝ point (wz1Perp2 direction)| := by
  have hstrong :=
    large_perp_component_three_sevenths
      hdirection hseparated hstrip hwidth
  linarith

/-- The weaker historical constant used by existing downstream proofs. -/
lemma large_perp_component
    {point direction : Point2} {width : ℝ}
    (hdirection : ‖direction‖ = 1)
    (hseparated : 1 / 2 ≤ dist point 0)
    (hstrip :
      point ∈
        wz1LineNeighborhood 0
          (wz1Perp2 direction) width)
    (hwidth : width ≤ 1 / 4) :
    1 / 3 ≤
      |inner ℝ point (wz1Perp2 direction)| := by
  have hstrong :=
    large_perp_component_two_fifths
      hdirection hseparated hstrip hwidth
  linarith

/--
Large transverse displacement gives separated dot products once the
longitudinal error is small.
-/
lemma dot_separation_from_transverse
    {point first second direction : Point2}
    {width delta longitudinalBound : ℝ}
    (hdirection : ‖direction‖ = 1)
    (hperpendicular :
      1 / 3 ≤
        |inner ℝ point (wz1Perp2 direction)|)
    (hdirectionComponent :
      |inner ℝ point direction| ≤ width)
    (hlongitudinal :
      |inner ℝ (first - second) direction| ≤
        longitudinalBound)
    (htransverse :
      9 * delta ≤
        |inner ℝ (first - second)
          (wz1Perp2 direction)|)
    (herror : width * longitudinalBound ≤ delta / 4)
    (hdelta : 0 < delta) :
    2 * delta <
      |inner ℝ point (first - second)| := by
  let displacement := first - second
  let parallel :=
    inner ℝ displacement direction
  let perpendicular :=
    inner ℝ displacement (wz1Perp2 direction)
  have hdecomposition :
      displacement =
        parallel • direction +
          perpendicular • wz1Perp2 direction :=
    orthonormal_decomp displacement direction hdirection
  have hinner :
      inner ℝ point displacement =
        inner ℝ point direction * parallel +
          inner ℝ point (wz1Perp2 direction) *
            perpendicular := by
    rw [hdecomposition, inner_add_right,
      inner_smul_right, inner_smul_right]
    ring
  let mainTerm :=
    inner ℝ point (wz1Perp2 direction) *
      perpendicular
  let errorTerm :=
    inner ℝ point direction * parallel
  have hwidthNonnegative : 0 ≤ width :=
    (abs_nonneg (inner ℝ point direction)).trans
      hdirectionComponent
  have hmain :
      3 * delta ≤ |mainTerm| := by
    calc
      3 * delta =
          (1 / 3 : ℝ) * (9 * delta) := by ring
      _ ≤
          |inner ℝ point (wz1Perp2 direction)| *
            |perpendicular| := by
        gcongr
      _ = |mainTerm| := by
        simp [mainTerm, abs_mul]
  have herrorTerm :
      |errorTerm| ≤ delta / 4 := by
    calc
      |errorTerm| =
          |inner ℝ point direction| * |parallel| := by
        simp [errorTerm, abs_mul]
      _ ≤ width * longitudinalBound := by
        gcongr
      _ ≤ delta / 4 := herror
  have habsolute :
      |mainTerm| - |errorTerm| ≤
        |mainTerm + errorTerm| :=
    abs_sub_abs_le_abs_add mainTerm errorTerm
  have hsum :
      inner ℝ point displacement =
        mainTerm + errorTerm := by
    rw [hinner]
    simp only [mainTerm, errorTerm]
    ring
  rw [hsum]
  linarith

/--
Pigeonhole longitudinal coordinates of unit-ball points into one window of
radius `longitudinalRadius`.
-/
lemma longitudinal_pigeonhole
    {index : Type*} [DecidableEq index]
    (points : Finset index)
    (coordinate : index → Point2)
    {direction : Point2}
    {longitudinalRadius : ℝ}
    (hdirection : ‖direction‖ = 1)
    (hradius : 0 < longitudinalRadius)
    (hball :
      ∀ point ∈ points, ‖coordinate point‖ ≤ 1) :
    ∃ center : ℝ,
      (points.card : ℝ) * longitudinalRadius /
          (2 + 2 * longitudinalRadius) ≤
        ((points.filter fun point =>
          |inner ℝ (coordinate point) direction -
            center| ≤ longitudinalRadius).card : ℝ) := by
  have hcoordinate :
      ∀ point ∈ points,
        -1 ≤ inner ℝ (coordinate point) direction ∧
          inner ℝ (coordinate point) direction ≤ 1 := by
    intro point hpoint
    have hinner :
        |inner ℝ (coordinate point) direction| ≤
          ‖coordinate point‖ * ‖direction‖ :=
      abs_real_inner_le_norm _ _
    rw [hdirection, mul_one] at hinner
    have hbound :=
      hinner.trans (hball point hpoint)
    exact (abs_le.mp hbound)
  rcases
      finite_interval_pigeonhole_lower_bound
        hradius (by norm_num : (-1 : ℝ) ≤ 1)
        (fun point =>
          inner ℝ (coordinate point) direction)
        hcoordinate with
    ⟨center, hcenter⟩
  refine ⟨center, ?_⟩
  convert hcenter using 1 <;> ring

/--
If `a` lies in the strip orthogonal to `direction` and `b₁`, `b₂` lie in
one common parallel strip, their dot difference is bounded by four times the
strip width.
-/
lemma dot_value_range_bound
    {a b₁ b₂ base direction : Point2} {width : ℝ}
    (ha : a ∈ wz1LineNeighborhood 0 (wz1Perp2 direction) width)
    (hb₁ : b₁ ∈ wz1LineNeighborhood base direction width)
    (hb₂ : b₂ ∈ wz1LineNeighborhood base direction width)
    (hball_a : ‖a‖ ≤ 1)
    (hball₁ : ‖b₁‖ ≤ 1) (hball₂ : ‖b₂‖ ≤ 1)
    (hdirection : ‖direction‖ = 1) (hwidth : 0 < width) :
    |inner ℝ a (b₁ - b₂)| ≤ 4 * width := by
  let perpendicular := wz1Perp2 direction
  have hperpendicular_unit : ‖perpendicular‖ = 1 := by
    have hnorm :
        ‖perpendicular‖ ^ 2 =
          perpendicular 0 ^ 2 + perpendicular 1 ^ 2 :=
      norm2_sq perpendicular
    have hcoordinates :
        perpendicular 0 ^ 2 + perpendicular 1 ^ 2 =
          direction 1 ^ 2 + direction 0 ^ 2 := by
      simp [perpendicular, wz1Perp2_coords]
    have hdirection_sq :
        ‖direction‖ ^ 2 =
          direction 0 ^ 2 + direction 1 ^ 2 :=
      norm2_sq direction
    rw [hdirection] at hdirection_sq
    have hsq : ‖perpendicular‖ ^ 2 = 1 := by
      linarith
    nlinarith [norm_nonneg perpendicular]
  have hperpendicular_twice :
      wz1Perp2 (wz1Perp2 direction) = -direction := by
    ext index
    fin_cases index <;> simp [wz1Perp2_coords]
  have ha_direction :
      |inner ℝ a direction| ≤ width := by
    have h :
        |inner ℝ (a - 0) (wz1Perp2 perpendicular)| ≤ width :=
      ha
    have hrewrite : wz1Perp2 perpendicular = -direction := by
      simpa [perpendicular] using hperpendicular_twice
    simpa [hrewrite, inner_neg_right, abs_neg] using h
  have ha_perpendicular :
      |inner ℝ a perpendicular| ≤ 1 := by
    calc
      |inner ℝ a perpendicular|
          ≤ ‖a‖ * ‖perpendicular‖ :=
        abs_real_inner_le_norm a perpendicular
      _ = ‖a‖ := by rw [hperpendicular_unit, mul_one]
      _ ≤ 1 := hball_a
  have hb_perpendicular :
      |inner ℝ (b₁ - b₂) perpendicular| ≤ 2 * width := by
    have h₁ :
        |inner ℝ (b₁ - base) perpendicular| ≤ width :=
      hb₁
    have h₂ :
        |inner ℝ (b₂ - base) perpendicular| ≤ width :=
      hb₂
    have heq :
        inner ℝ (b₁ - b₂) perpendicular =
          inner ℝ (b₁ - base) perpendicular -
            inner ℝ (b₂ - base) perpendicular := by
      simp [inner_sub_left]
    rw [heq]
    linarith [abs_sub
      (inner ℝ (b₁ - base) perpendicular)
      (inner ℝ (b₂ - base) perpendicular)]
  have hb_direction :
      |inner ℝ (b₁ - b₂) direction| ≤ 2 := by
    have h₁ :
        |inner ℝ b₁ direction| ≤ 1 := by
      calc
        |inner ℝ b₁ direction|
            ≤ ‖b₁‖ * ‖direction‖ :=
          abs_real_inner_le_norm b₁ direction
        _ = ‖b₁‖ := by rw [hdirection, mul_one]
        _ ≤ 1 := hball₁
    have h₂ :
        |inner ℝ b₂ direction| ≤ 1 := by
      calc
        |inner ℝ b₂ direction|
            ≤ ‖b₂‖ * ‖direction‖ :=
          abs_real_inner_le_norm b₂ direction
        _ = ‖b₂‖ := by rw [hdirection, mul_one]
        _ ≤ 1 := hball₂
    have heq :
        inner ℝ (b₁ - b₂) direction =
          inner ℝ b₁ direction - inner ℝ b₂ direction := by
      simp [inner_sub_left]
    rw [heq]
    linarith [abs_sub
      (inner ℝ b₁ direction) (inner ℝ b₂ direction)]
  let displacement := b₁ - b₂
  let parallel := inner ℝ displacement direction
  let transverse := inner ℝ displacement perpendicular
  have hdecomposition :
      displacement =
        parallel • direction + transverse • perpendicular :=
    orthonormal_decomp displacement direction hdirection
  have hinner :
      inner ℝ a displacement =
        inner ℝ a direction * parallel +
          inner ℝ a perpendicular * transverse := by
    rw [hdecomposition, inner_add_right,
      inner_smul_right, inner_smul_right]
    ring
  rw [hinner]
  have hparallel :
      |inner ℝ a direction * parallel| ≤ width * 2 := by
    rw [abs_mul]
    have h : |parallel| ≤ 2 := by
      simpa [parallel, displacement] using hb_direction
    gcongr
  have htransverse :
      |inner ℝ a perpendicular * transverse| ≤
        1 * (2 * width) := by
    rw [abs_mul]
    have h : |transverse| ≤ 2 * width := by
      simpa [transverse, displacement] using hb_perpendicular
    gcongr
  linarith [abs_add_le
    (inner ℝ a direction * parallel)
    (inner ℝ a perpendicular * transverse)]

end Kakeya.Assouad
