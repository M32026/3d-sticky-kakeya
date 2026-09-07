import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowDependentFamilyCounting

/-!
# Rotate one short narrow fiber without losing the final threshold

A concentrated fiber lies in a width-`delta` strip transverse to the common
direction and in a longitudinal window of radius `delta / (4 * width)`.  If a
unit endpoint direction has transverse component at most `4 * width`, the
fiber's coordinate normal to that endpoint direction lies in an interval of
radius `2 * delta`.  Two radius-`delta` cells cover that interval, so the
doubled producer threshold leaves one full Alternative-A threshold.
-/

namespace Kakeya.Assouad

noncomputable section

open Classical
open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- Which half of a radius-`2 * delta` scalar interval was retained. -/
inductive WZ1NarrowCellSide
  | lower
  | upper
  deriving DecidableEq, Fintype

/-- The canonical radius-`delta` cell center for one retained half. -/
def WZ1NarrowCellSide.level
    (side : WZ1NarrowCellSide)
    (center delta : ℝ) : ℝ :=
  match side with
  | .lower => center - delta
  | .upper => center + delta

/-- Two-cell pigeonholing with the retained lower/upper side recorded. -/
lemma narrow_two_cell_pigeonhole_with_side
    {index : Type*} [DecidableEq index]
    {points : Finset index}
    {value : index → ℝ}
    {center delta : ℝ}
    {threshold : ENNReal}
    (hdelta : 0 < delta)
    (hbound :
      ∀ point ∈ points,
        |value point - center| ≤ 2 * delta)
    (hcard :
      2 * threshold ≤ (points.card : ENNReal)) :
    ∃ selected : Finset index,
      selected ⊆ points ∧
      threshold ≤ (selected.card : ENNReal) ∧
      ∃ side : WZ1NarrowCellSide,
        ∀ point ∈ selected,
          |value point - side.level center delta| ≤ delta := by
  let left := points.filter fun point => value point ≤ center
  let right := points \ left
  have hpartition :
      points.card = left.card + right.card := by
    have hleft : left ⊆ points :=
      Finset.filter_subset _ _
    have hunion : left ∪ right = points := by
      dsimp only [right]
      exact Finset.union_sdiff_of_subset hleft
    have hdisjoint : Disjoint left right := by
      dsimp only [right]
      exact Finset.disjoint_sdiff
    rw [← hunion, Finset.card_union_of_disjoint hdisjoint]
  have hpartitionENN :
      (points.card : ENNReal) =
        (left.card : ENNReal) + (right.card : ENNReal) := by
    exact_mod_cast hpartition
  by_cases hleft :
      threshold ≤ (left.card : ENNReal)
  · refine ⟨left, Finset.filter_subset _ _, hleft, .lower, ?_⟩
    intro point hpoint
    have hmem := (Finset.mem_filter.mp hpoint).1
    have hupper := (Finset.mem_filter.mp hpoint).2
    have hwindow := abs_le.mp (hbound point hmem)
    change |value point - (center - delta)| ≤ delta
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have hleftStrict :
        (left.card : ENNReal) < threshold :=
      lt_of_not_ge hleft
    have hright :
        threshold ≤ (right.card : ENNReal) := by
      by_contra hright
      have hrightStrict :
          (right.card : ENNReal) < threshold :=
        lt_of_not_ge hright
      have hsum :
          (left.card : ENNReal) + (right.card : ENNReal) <
            threshold + threshold :=
        ENNReal.add_lt_add hleftStrict hrightStrict
      have htwo :
          threshold + threshold = 2 * threshold := by
        ring
      have hsum' :
          (points.card : ENNReal) < 2 * threshold := by
        rw [hpartitionENN, ← htwo]
        exact hsum
      exact (not_lt_of_ge hcard) hsum'
    refine ⟨right, Finset.sdiff_subset, hright, .upper, ?_⟩
    intro point hpoint
    have hmem := (Finset.mem_sdiff.mp hpoint).1
    have hnotLeft := (Finset.mem_sdiff.mp hpoint).2
    have hgreater : center < value point := by
      simp only [left, Finset.mem_filter, hmem, true_and] at hnotLeft
      exact lt_of_not_ge hnotLeft
    have hwindow := abs_le.mp (hbound point hmem)
    change |value point - (center + delta)| ≤ delta
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Two radius-`delta` cells cover one scalar interval of radius
`2 * delta`. -/
lemma narrow_two_cell_pigeonhole
    {index : Type*} [DecidableEq index]
    {points : Finset index}
    {value : index → ℝ}
    {center delta : ℝ}
    {threshold : ENNReal}
    (hdelta : 0 < delta)
    (hbound :
      ∀ point ∈ points,
        |value point - center| ≤ 2 * delta)
    (hcard :
      2 * threshold ≤ (points.card : ENNReal)) :
    ∃ selected : Finset index,
      selected ⊆ points ∧
      threshold ≤ (selected.card : ENNReal) ∧
      ∃ level : ℝ,
        ∀ point ∈ selected,
          |value point - level| ≤ delta := by
  rcases
      narrow_two_cell_pigeonhole_with_side
        hdelta hbound hcard with
    ⟨selected, hselected, hselectedCard, side, hside⟩
  exact
    ⟨selected, hselected, hselectedCard,
      side.level center delta, hside⟩

/-- A unit vector has a unit perpendicular vector. -/
lemma wz1Perp2_norm_eq_one
    {direction : Point2}
    (hdirection : ‖direction‖ = 1) :
    ‖wz1Perp2 direction‖ = 1 := by
  have hnorm := norm2_sq (wz1Perp2 direction)
  have hdirectionSq := norm2_sq direction
  have hcoordinates := wz1Perp2_coords direction
  rw [hcoordinates.1, hcoordinates.2] at hnorm
  rw [hdirection] at hdirectionSq
  nlinarith [norm_nonneg (wz1Perp2 direction)]

/-- The mixed coordinates produced by rotating both vectors by ninety
degrees. -/
lemma wz1Perp2_inner_identities
    (first second : Point2) :
    inner ℝ first (wz1Perp2 second) =
        -inner ℝ second (wz1Perp2 first) ∧
      inner ℝ (wz1Perp2 first) (wz1Perp2 second) =
        inner ℝ first second := by
  constructor
  · simp [inner2_eq, wz1Perp2_coords]
    ring
  · simp [inner2_eq, wz1Perp2_coords]
    ring

/-- The endpoint-normal coordinate of every point in one short rectangular
fiber lies within `2 * delta` of the canonical rotated center. -/
lemma narrow_rotated_fiber_coordinate_bound
    {points : Finset Point2}
    {delta width : ℝ}
    {base direction endpointDirection : Point2}
    {longitudinalCenter : ℝ}
    (hdelta : 0 < delta)
    (hwidth : 0 < width)
    (hdirection : ‖direction‖ = 1)
    (hendpoint : ‖endpointDirection‖ = 1)
    (hendpointTransverse :
      |inner ℝ endpointDirection (wz1Perp2 direction)| ≤
        4 * width)
    (hstrip :
      ∀ point ∈ points,
        point ∈ wz1LineNeighborhood base direction delta)
    (hlongitudinal :
      ∀ point ∈ points,
        |inner ℝ point direction - longitudinalCenter| ≤
          delta / (4 * width))
    (point : Point2)
    (hpoint : point ∈ points) :
    |inner ℝ point (wz1Perp2 endpointDirection) -
        (longitudinalCenter *
            inner ℝ direction (wz1Perp2 endpointDirection) +
          inner ℝ base (wz1Perp2 direction) *
            inner ℝ (wz1Perp2 direction)
              (wz1Perp2 endpointDirection))| ≤
      2 * delta := by
  let endpointNormal := wz1Perp2 endpointDirection
  let directionNormal := wz1Perp2 direction
  let center :=
    longitudinalCenter *
        inner ℝ direction endpointNormal +
      inner ℝ base directionNormal *
        inner ℝ directionNormal endpointNormal
  have hendpointNormal :
      ‖endpointNormal‖ = 1 :=
    wz1Perp2_norm_eq_one hendpoint
  have hdirectionNormal :
      ‖directionNormal‖ = 1 :=
    wz1Perp2_norm_eq_one hdirection
  have hrotatedTransverse :
      |inner ℝ direction endpointNormal| ≤
        4 * width := by
    have hid :=
      (wz1Perp2_inner_identities
        direction endpointDirection).1
    rw [hid, abs_neg]
    simpa [directionNormal] using hendpointTransverse
  have hnormalInner :
      |inner ℝ directionNormal endpointNormal| ≤ 1 := by
    calc
      |inner ℝ directionNormal endpointNormal|
          ≤ ‖directionNormal‖ * ‖endpointNormal‖ :=
        abs_real_inner_le_norm _ _
      _ = 1 := by
        rw [hdirectionNormal, hendpointNormal]
        norm_num
  have hdecomposition :=
    orthonormal_decomp point direction hdirection
  let directionCoordinate := inner ℝ point direction
  let normalCoordinate := inner ℝ point directionNormal
  have hinner :
      inner ℝ point endpointNormal =
        directionCoordinate *
            inner ℝ direction endpointNormal +
          normalCoordinate *
            inner ℝ directionNormal endpointNormal := by
    calc
      inner ℝ point endpointNormal =
          inner ℝ
            (directionCoordinate • direction +
              normalCoordinate • directionNormal)
            endpointNormal := by
        rw [show
          point =
            directionCoordinate • direction +
              normalCoordinate • directionNormal by
          simpa [directionCoordinate, normalCoordinate,
            directionNormal] using hdecomposition]
      _ =
          directionCoordinate *
              inner ℝ direction endpointNormal +
            normalCoordinate *
              inner ℝ directionNormal endpointNormal := by
        rw [inner_add_left,
          inner_smul_left, inner_smul_left]
        simp
  have hstripCoordinate :
      |inner ℝ point directionNormal -
          inner ℝ base directionNormal| ≤ delta := by
    have h := hstrip point hpoint
    change
      |inner ℝ (point - base) directionNormal| ≤ delta at h
    simpa [inner_sub_left] using h
  have hlong := hlongitudinal point hpoint
  have hfirst :
      |(directionCoordinate - longitudinalCenter) *
          inner ℝ direction endpointNormal| ≤ delta := by
    rw [abs_mul]
    calc
      |directionCoordinate - longitudinalCenter| *
            |inner ℝ direction endpointNormal|
          ≤ (delta / (4 * width)) * (4 * width) := by
        gcongr
      _ = delta := by
        field_simp [hwidth.ne']
  have hsecond :
      |(normalCoordinate -
            inner ℝ base directionNormal) *
          inner ℝ directionNormal endpointNormal| ≤ delta := by
    rw [abs_mul]
    calc
      |normalCoordinate -
            inner ℝ base directionNormal| *
            |inner ℝ directionNormal endpointNormal|
          ≤ delta * 1 := by
        gcongr
      _ = delta := by ring
  have heq :
      inner ℝ point endpointNormal - center =
        (directionCoordinate - longitudinalCenter) *
            inner ℝ direction endpointNormal +
          (normalCoordinate -
              inner ℝ base directionNormal) *
            inner ℝ directionNormal endpointNormal := by
    rw [hinner]
    dsimp only [center]
    ring
  change |inner ℝ point endpointNormal - center| ≤ 2 * delta
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)

/--
Rotate a short rectangular fiber to a nearby endpoint direction.

The output base is chosen only through its normal coordinate.  The theorem
does not assume or create any graph edges.
-/
lemma narrow_rotated_fiber_pigeonhole
    {points : Finset Point2}
    {delta width : ℝ}
    {base direction endpointDirection : Point2}
    {longitudinalCenter : ℝ}
    {threshold : ENNReal}
    (hdelta : 0 < delta)
    (hwidth : 0 < width)
    (hdirection : ‖direction‖ = 1)
    (hendpoint : ‖endpointDirection‖ = 1)
    (hendpointTransverse :
      |inner ℝ endpointDirection (wz1Perp2 direction)| ≤
        4 * width)
    (hstrip :
      ∀ point ∈ points,
        point ∈ wz1LineNeighborhood base direction delta)
    (hlongitudinal :
      ∀ point ∈ points,
        |inner ℝ point direction - longitudinalCenter| ≤
          delta / (4 * width))
    (hcard :
      2 * threshold ≤ (points.card : ENNReal)) :
    ∃ selected : Finset Point2,
      selected ⊆ points ∧
      threshold ≤ (selected.card : ENNReal) ∧
      ∃ rotatedBase : Point2,
        ∀ point ∈ selected,
          point ∈
            wz1LineNeighborhood
              rotatedBase endpointDirection delta := by
  let endpointNormal := wz1Perp2 endpointDirection
  let directionNormal := wz1Perp2 direction
  let center :=
    longitudinalCenter *
        inner ℝ direction endpointNormal +
      inner ℝ base directionNormal *
        inner ℝ directionNormal endpointNormal
  have hendpointNormal :
      ‖endpointNormal‖ = 1 :=
    wz1Perp2_norm_eq_one hendpoint
  have hdirectionNormal :
      ‖directionNormal‖ = 1 :=
    wz1Perp2_norm_eq_one hdirection
  have hrotatedTransverse :
      |inner ℝ direction endpointNormal| ≤
        4 * width := by
    have hid :=
      (wz1Perp2_inner_identities
        direction endpointDirection).1
    rw [hid, abs_neg]
    simpa [directionNormal] using hendpointTransverse
  have hnormalInner :
      |inner ℝ directionNormal endpointNormal| ≤ 1 := by
    calc
      |inner ℝ directionNormal endpointNormal|
          ≤ ‖directionNormal‖ * ‖endpointNormal‖ :=
        abs_real_inner_le_norm _ _
      _ = 1 := by
        rw [hdirectionNormal, hendpointNormal]
        norm_num
  have hcoordinate :
      ∀ point ∈ points,
        |inner ℝ point endpointNormal - center| ≤
          2 * delta := by
    intro point hpoint
    have hdecomposition :=
      orthonormal_decomp point direction hdirection
    let directionCoordinate := inner ℝ point direction
    let normalCoordinate := inner ℝ point directionNormal
    have hinner :
        inner ℝ point endpointNormal =
          directionCoordinate *
              inner ℝ direction endpointNormal +
            normalCoordinate *
              inner ℝ directionNormal endpointNormal := by
      calc
        inner ℝ point endpointNormal =
            inner ℝ
              (directionCoordinate • direction +
                normalCoordinate • directionNormal)
              endpointNormal := by
          rw [show
            point =
              directionCoordinate • direction +
                normalCoordinate • directionNormal by
            simpa [directionCoordinate, normalCoordinate,
              directionNormal] using hdecomposition]
        _ =
            directionCoordinate *
                inner ℝ direction endpointNormal +
              normalCoordinate *
                inner ℝ directionNormal endpointNormal := by
          rw [inner_add_left,
            inner_smul_left, inner_smul_left]
          simp
    have hstripCoordinate :
        |inner ℝ point directionNormal -
            inner ℝ base directionNormal| ≤ delta := by
      have h := hstrip point hpoint
      change
        |inner ℝ (point - base) directionNormal| ≤ delta at h
      simpa [inner_sub_left] using h
    have hlong := hlongitudinal point hpoint
    have hfirst :
        |(directionCoordinate - longitudinalCenter) *
            inner ℝ direction endpointNormal| ≤ delta := by
      rw [abs_mul]
      calc
        |directionCoordinate - longitudinalCenter| *
              |inner ℝ direction endpointNormal|
            ≤ (delta / (4 * width)) * (4 * width) := by
          gcongr
        _ = delta := by
          field_simp [hwidth.ne']
    have hsecond :
        |(normalCoordinate -
              inner ℝ base directionNormal) *
            inner ℝ directionNormal endpointNormal| ≤ delta := by
      rw [abs_mul]
      calc
        |normalCoordinate -
              inner ℝ base directionNormal| *
              |inner ℝ directionNormal endpointNormal|
            ≤ delta * 1 := by
          gcongr
        _ = delta := by ring
    have heq :
        inner ℝ point endpointNormal - center =
          (directionCoordinate - longitudinalCenter) *
              inner ℝ direction endpointNormal +
            (normalCoordinate -
                inner ℝ base directionNormal) *
              inner ℝ directionNormal endpointNormal := by
      rw [hinner]
      dsimp only [center]
      ring
    rw [heq]
    exact (abs_add_le _ _).trans (by linarith)
  rcases
      narrow_two_cell_pigeonhole
        hdelta hcoordinate hcard with
    ⟨selected, hselected, hselectedCard, level, hlevel⟩
  let rotatedBase := level • endpointNormal
  refine
    ⟨selected, hselected, hselectedCard,
      rotatedBase, ?_⟩
  intro point hpoint
  have hself :
      inner ℝ endpointNormal endpointNormal = 1 := by
    rw [real_inner_self_eq_norm_sq, hendpointNormal]
    norm_num
  change
    |inner ℝ (point - rotatedBase) endpointNormal| ≤ delta
  have hbase :
      inner ℝ rotatedBase endpointNormal = level := by
    dsimp only [rotatedBase]
    rw [inner_smul_left, hself]
    simp
  rw [inner_sub_left, hbase]
  exact hlevel point hpoint

end

end Kakeya.Assouad
