import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowRotatedFiberPigeonhole
import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowTripleConcentratedStatements

/-!
# Origin-line direction pigeonhole for the narrow branch

A large finite family in the origin-centered strip orthogonal to a unit
direction can be pigeonholed by its projective slope.  The retained family
lies in an exact radius-`delta` origin line for one nearby unit direction.
-/

namespace Kakeya.Assouad

noncomputable section

open scoped ENNReal

structure WZ1NarrowOriginDirectionPigeonholeData
    (points : Finset Point2)
    (referenceDirection : Point2)
    (delta width : ℝ) where
  direction : Point2
  direction_unit : ‖direction‖ = 1
  direction_transverse :
    |inner ℝ direction (wz1Perp2 referenceDirection)| ≤
      31 * width / 12
  selected : Finset Point2
  selected_subset : selected ⊆ points
  cardinality :
    (points.card : ℝ) * (delta / 4) /
        (14 * width / 3 + delta / 2) ≤
      (selected.card : ℝ)
  origin_strip :
    ∀ point ∈ selected,
      point ∈
        wz1LineNeighborhood
          0 (wz1Perp2 direction) delta

theorem narrow_origin_direction_pigeonhole
    {points : Finset Point2}
    {referenceDirection : Point2}
    {delta width : ℝ}
    (hdelta : 0 < delta)
    (hdeltaWidth : delta ≤ width)
    (hwidthQuarter : width ≤ 1 / 4)
    (hdirection : ‖referenceDirection‖ = 1)
    (hpoints : points.Nonempty)
    (hball : ∀ point ∈ points, ‖point‖ ≤ 1)
    (hseparated :
      ∀ point ∈ points, 1 / 2 ≤ dist point 0)
    (hstrip :
      ∀ point ∈ points,
        point ∈
          wz1LineNeighborhood
            0 (wz1Perp2 referenceDirection) width) :
    Nonempty
      (WZ1NarrowOriginDirectionPigeonholeData
        points referenceDirection delta width) := by
  classical
  let normal := wz1Perp2 referenceDirection
  let slope : Point2 → ℝ := fun point =>
    -(inner ℝ point referenceDirection) /
      inner ℝ point normal
  have hwidth : 0 < width :=
    hdelta.trans_le hdeltaWidth
  have hnormal : ‖normal‖ = 1 :=
    wz1Perp2_norm_eq_one hdirection
  have hparallel :
      ∀ point ∈ points,
        |inner ℝ point referenceDirection| ≤ width := by
    intro point hpoint
    have hpointStrip := hstrip point hpoint
    have hperpPerp :
        wz1Perp2 (wz1Perp2 referenceDirection) =
          -referenceDirection := by
      ext coordinate
      fin_cases coordinate <;>
        simp [wz1Perp2_coords]
    change
      |inner ℝ (point - 0)
        (wz1Perp2 (wz1Perp2 referenceDirection))| ≤
          width at hpointStrip
    simpa [hperpPerp, inner_neg_right, abs_neg] using
      hpointStrip
  have hnormalLower :
      ∀ point ∈ points,
        3 / 7 ≤ |inner ℝ point normal| := by
    intro point hpoint
    exact
      large_perp_component_three_sevenths
        hdirection (hseparated point hpoint)
        (hstrip point hpoint) hwidthQuarter
  have hnormalNonzero :
      ∀ point ∈ points,
        inner ℝ point normal ≠ 0 := by
    intro point hpoint hzero
    have hlower := hnormalLower point hpoint
    rw [hzero, abs_zero] at hlower
    norm_num at hlower
  have hslope :
      ∀ point ∈ points,
        -(7 * width / 3) ≤ slope point ∧
          slope point ≤ 7 * width / 3 := by
    intro point hpoint
    have hquotient :
        |slope point| ≤ 7 * width / 3 := by
      dsimp only [slope]
      rw [abs_div, abs_neg]
      have hdenominator :
          0 < |inner ℝ point normal| := by
        exact abs_pos.mpr (hnormalNonzero point hpoint)
      calc
        |inner ℝ point referenceDirection| /
              |inner ℝ point normal|
            ≤ width / (3 / 7 : ℝ) := by
          exact
            div_le_div₀
              hwidth.le
              (hparallel point hpoint)
              (by norm_num)
              (hnormalLower point hpoint)
        _ = 7 * width / 3 := by ring
    exact abs_le.mp hquotient
  let radius := delta / 4
  have hradius : 0 < radius := by
    dsimp only [radius]
    positivity
  rcases
      finite_interval_pigeonhole_lower_bound
        hradius
        (by linarith [hwidth] :
          -(7 * width / 3) ≤ 7 * width / 3)
        slope hslope with
    ⟨level, hlevel⟩
  let selected :=
    points.filter fun point =>
      |slope point - level| ≤ radius
  have hselectedSubset : selected ⊆ points :=
    Finset.filter_subset _ _
  have hcardinality :
      (points.card : ℝ) * (delta / 4) /
          (14 * width / 3 + delta / 2) ≤
        (selected.card : ℝ) := by
    convert hlevel using 1
    simp only [radius]
    ring
  have hselectedNonempty : selected.Nonempty := by
    have hleftPositive :
        0 <
          (points.card : ℝ) * (delta / 4) /
            (14 * width / 3 + delta / 2) := by
      have hcardPositive : 0 < (points.card : ℝ) := by
        exact_mod_cast (Finset.card_pos.mpr hpoints)
      positivity
    have hcardPositive : 0 < (selected.card : ℝ) :=
      hleftPositive.trans_le hcardinality
    exact Finset.card_pos.mp (by exact_mod_cast hcardPositive)
  rcases hselectedNonempty with ⟨reference, hreference⟩
  have hreferenceSource :
      reference ∈ points :=
    hselectedSubset hreference
  have hreferenceWindow :
      |slope reference - level| ≤ radius :=
    (Finset.mem_filter.mp hreference).2
  have hlevelAbs :
      |level| ≤ 31 * width / 12 := by
    have hslopeReference := hslope reference hreferenceSource
    have hslopeAbs :
        |slope reference| ≤ 7 * width / 3 :=
      abs_le.mpr hslopeReference
    have htriangle :
        |level| ≤
          |slope reference| +
            |slope reference - level| := by
      have heq :
          level =
            slope reference -
              (slope reference - level) := by ring
      exact
        (congrArg abs heq).le.trans
          (abs_sub (slope reference)
            (slope reference - level))
    calc
      |level| ≤
          |slope reference| +
            |slope reference - level| :=
        htriangle
      _ ≤ 7 * width / 3 + delta / 4 := by
        simpa [radius] using
          add_le_add hslopeAbs hreferenceWindow
      _ ≤ 7 * width / 3 + width / 4 := by
        gcongr
      _ = 31 * width / 12 := by ring
  let rawDirection :=
    referenceDirection + level • normal
  have hrawInner :
      inner ℝ rawDirection referenceDirection = 1 := by
    have horthogonal :
        inner ℝ normal referenceDirection = 0 := by
      have hidentity :=
        (wz1Perp2_inner_identities
          referenceDirection referenceDirection).1
      have hself :
          inner ℝ referenceDirection normal =
            -inner ℝ referenceDirection normal := by
        simpa [normal] using hidentity
      have hzero :
          inner ℝ referenceDirection normal = 0 := by
        linarith
      simpa [real_inner_comm] using hzero
    simp [rawDirection, inner_add_left, inner_smul_left,
      horthogonal, hdirection]
  have hrawNormLower : 1 ≤ ‖rawDirection‖ := by
    have hinnerBound :=
      abs_real_inner_le_norm
        rawDirection referenceDirection
    rw [hrawInner, abs_one, hdirection, mul_one] at hinnerBound
    exact hinnerBound
  have hrawNorm : 0 < ‖rawDirection‖ := by
    linarith
  let direction :=
    (1 / ‖rawDirection‖) • rawDirection
  have hdirectionUnit : ‖direction‖ = 1 := by
    rw [show direction =
      (1 / ‖rawDirection‖) • rawDirection by rfl,
      norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hrawNorm)]
    field_simp [hrawNorm.ne']
  have hrawNormal :
      inner ℝ rawDirection normal = level := by
    have horthogonal :
        inner ℝ referenceDirection normal = 0 := by
      have hidentity :=
        (wz1Perp2_inner_identities
          referenceDirection referenceDirection).1
      have hself :
          inner ℝ referenceDirection normal =
            -inner ℝ referenceDirection normal := by
        simpa [normal] using hidentity
      linarith
    simp [rawDirection, inner_add_left, inner_smul_left,
      horthogonal, hnormal]
  have hdirectionTransverse :
      |inner ℝ direction normal| ≤ 31 * width / 12 := by
    have heq :
        inner ℝ direction normal =
          (1 / ‖rawDirection‖) * level := by
      simp [direction, inner_smul_left, hrawNormal]
    rw [heq, abs_mul,
      abs_of_pos (one_div_pos.mpr hrawNorm)]
    calc
      (1 / ‖rawDirection‖) * |level|
          ≤ 1 * |level| := by
        gcongr
        exact
          (div_le_iff₀ hrawNorm).2
            (by simpa using hrawNormLower)
      _ = |level| := by ring
      _ ≤ 31 * width / 12 := hlevelAbs
  have horigin :
      ∀ point ∈ selected,
        point ∈
          wz1LineNeighborhood
            0 (wz1Perp2 direction) delta := by
    intro point hpoint
    have hpointSource := hselectedSubset hpoint
    have hpointWindow :
        |slope point - level| ≤ radius :=
      (Finset.mem_filter.mp hpoint).2
    have hslopeIdentity :
        inner ℝ point referenceDirection =
          -(slope point) * inner ℝ point normal := by
      dsimp only [slope]
      field_simp [hnormalNonzero point hpointSource]
    have hpointRaw :
        |inner ℝ point rawDirection| ≤ delta / 4 := by
      have heq :
          inner ℝ point rawDirection =
            (level - slope point) *
              inner ℝ point normal := by
        rw [show rawDirection =
          referenceDirection + level • normal by rfl,
          inner_add_right, inner_smul_right,
          hslopeIdentity]
        ring
      rw [heq, abs_mul]
      have hnormalUpper :
          |inner ℝ point normal| ≤ 1 := by
        calc
          |inner ℝ point normal|
              ≤ ‖point‖ * ‖normal‖ :=
            abs_real_inner_le_norm _ _
          _ = ‖point‖ := by rw [hnormal, mul_one]
          _ ≤ 1 := hball point hpointSource
      calc
        |level - slope point| *
              |inner ℝ point normal|
            ≤ (delta / 4) * 1 := by
          have hwindow :
              |level - slope point| ≤ delta / 4 := by
            simpa [radius, abs_sub_comm] using hpointWindow
          gcongr
        _ = delta / 4 := by ring
    have hpointDirection :
        |inner ℝ point direction| ≤ delta / 4 := by
      rw [show direction =
        (1 / ‖rawDirection‖) • rawDirection by rfl,
        inner_smul_right, abs_mul,
        abs_of_pos (one_div_pos.mpr hrawNorm)]
      calc
        (1 / ‖rawDirection‖) *
              |inner ℝ point rawDirection|
            ≤ 1 * (delta / 4) := by
          gcongr
          exact
            (div_le_iff₀ hrawNorm).2
              (by simpa using hrawNormLower)
        _ = delta / 4 := by ring
    have hperpPerp :
        wz1Perp2 (wz1Perp2 direction) =
          -direction := by
      ext coordinate
      fin_cases coordinate <;>
        simp [wz1Perp2_coords]
    show
      |inner ℝ (point - 0)
        (wz1Perp2 (wz1Perp2 direction))| ≤ delta
    simpa [hperpPerp, inner_neg_right, abs_neg] using
      hpointDirection.trans (by linarith)
  exact
    ⟨{
      direction := direction
      direction_unit := hdirectionUnit
      direction_transverse := by
        simpa [normal] using hdirectionTransverse
      selected := selected
      selected_subset := hselectedSubset
      cardinality := hcardinality
      origin_strip := horigin
    }⟩

/-- The paper-scale specialization of the origin-direction pigeonhole for
one triple-concentrated obstruction. -/
structure WZ1NarrowTripleOriginLineData
    {delta epsilon eta : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {concentration :
      NarrowDotSpreadG1Concentrated
        delta epsilon data.width
        data.selectedF data.selectedG₁ data.selectedG₂
        data.refinedH data.direction}
    (obstruction :
      WZ1NarrowTripleConcentratedData
        parameters data concentration) where
  direction : Point2
  direction_unit : ‖direction‖ = 1
  direction_transverse :
    |inner ℝ direction (wz1Perp2 data.direction)| ≤
      31 * data.width / 12
  points : Finset Point2
  points_subset : points ⊆ obstruction.firstPoints
  cardinality :
    Kakeya.realRpowENN delta (epsilon - 1) ≤
      (points.card : ENNReal)
  origin_strip :
    ∀ point ∈ points,
      point ∈
        wz1LineNeighborhood
          0 (wz1Perp2 direction) delta

/-- The large literal `F` fiber in a triple-concentrated obstruction can be
rotated to a nearby exact radius-`delta` origin line while retaining the full
Alternative-A threshold. -/
theorem WZ1NarrowTripleConcentratedData.origin_direction_pigeonhole
    {delta epsilon eta : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {concentration :
      NarrowDotSpreadG1Concentrated
        delta epsilon data.width
        data.selectedF data.selectedG₁ data.selectedG₂
        data.refinedH data.direction}
    (obstruction :
      WZ1NarrowTripleConcentratedData
        parameters data concentration)
    (hdelta : 0 < delta)
    (_hdeltaOne : delta ≤ 1)
    (_hepsilon : 0 < epsilon)
    (hwidthQuarter : data.width ≤ 1 / 4)
    (hnarrow :
      data.width ≤ Real.rpow delta (1 - epsilon / 10)) :
    Nonempty (WZ1NarrowTripleOriginLineData obstruction) := by
  have hfirstNonempty : obstruction.firstPoints.Nonempty := by
    have hpositive :
        0 < 192 *
          Real.rpow delta (9 * epsilon / 10 - 1) := by
      exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hdelta _)
    have hcardPositive :
        0 < (obstruction.firstPoints.card : ℝ) :=
      hpositive.trans_le obstruction.firstPoints_card
    exact Finset.card_pos.mp (by exact_mod_cast hcardPositive)
  have hfirstBall :
      ∀ point ∈ obstruction.firstPoints, ‖point‖ ≤ 1 := by
    intro point hpoint
    have hselected :=
      obstruction.firstPoints_subset hpoint
    simpa [dist_zero_right] using
      data.selectedF_ball point hselected
  have hfirstSeparated :
      ∀ point ∈ obstruction.firstPoints,
        1 / 2 ≤ dist point 0 := by
    intro point hpoint
    exact
      data.standardSeparation.2.2.2.2 point
        (obstruction.firstPoints_subset hpoint)
  have hfirstStrip :
      ∀ point ∈ obstruction.firstPoints,
        point ∈
          wz1LineNeighborhood
            0 (wz1Perp2 data.direction) data.width := by
    intro point hpoint
    exact
      data.orthogonal_strip point
        (obstruction.firstPoints_subset hpoint)
  rcases
      narrow_origin_direction_pigeonhole
        hdelta data.delta_le_width
        hwidthQuarter
        data.direction_unit hfirstNonempty
        hfirstBall hfirstSeparated hfirstStrip with
    ⟨origin⟩
  have hdenominator :
      14 * data.width / 3 + delta / 2 ≤
        31 * data.width / 6 := by
    have hdeltaWidth := data.delta_le_width
    linarith
  have hdenominatorPositive :
      0 < 14 * data.width / 3 + delta / 2 := by
    nlinarith [data.width_pos]
  have hdenominatorUpperPositive :
      0 < 31 * data.width / 6 := by
    nlinarith [data.width_pos]
  have hselectedReal :
      Real.rpow delta (epsilon - 1) ≤
        (origin.selected.card : ℝ) := by
    have hcardLower :
        192 * Real.rpow delta (9 * epsilon / 10 - 1) *
              (delta / 4) /
              (14 * data.width / 3 + delta / 2) ≤
            (origin.selected.card : ℝ) := by
      exact
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            obstruction.firstPoints_card
            (by nlinarith [hdelta]))
          hdenominatorPositive.le).trans
          origin.cardinality
    have hcoarse :
        192 * Real.rpow delta (9 * epsilon / 10 - 1) *
              (delta / 4) /
              (31 * data.width / 6) ≤
            (origin.selected.card : ℝ) := by
      exact
        (div_le_div_of_nonneg_left
          (mul_nonneg
            (mul_nonneg (by norm_num)
              (Real.rpow_nonneg hdelta.le _))
            (by nlinarith [hdelta]))
          hdenominatorPositive
          hdenominator).trans hcardLower
    have hwidthPower :
        31 * data.width / 6 ≤
          31 * Real.rpow delta (1 - epsilon / 10) / 6 := by
      gcongr
    have hpowerDenominatorPositive :
        0 <
          31 * Real.rpow delta (1 - epsilon / 10) / 6 := by
      exact div_pos
        (mul_pos (by norm_num)
          (Real.rpow_pos_of_pos hdelta _))
        (by norm_num)
    have hpowerLower :
        192 * Real.rpow delta (9 * epsilon / 10 - 1) *
              (delta / 4) /
              (31 * Real.rpow delta (1 - epsilon / 10) / 6) ≤
            (origin.selected.card : ℝ) := by
      exact
        (div_le_div_of_nonneg_left
          (mul_nonneg
            (mul_nonneg (by norm_num)
              (Real.rpow_nonneg hdelta.le _))
            (by nlinarith [hdelta]))
          hdenominatorUpperPositive
          hwidthPower).trans hcoarse
    have hrpowIdentity :
        Real.rpow delta (9 * epsilon / 10 - 1) * delta /
              Real.rpow delta (1 - epsilon / 10) =
            Real.rpow delta (epsilon - 1) := by
      have hproduct :
          Real.rpow delta (9 * epsilon / 10 - 1) * delta =
            Real.rpow delta (9 * epsilon / 10) := by
        calc
          Real.rpow delta (9 * epsilon / 10 - 1) * delta =
              Real.rpow delta (9 * epsilon / 10 - 1) *
                Real.rpow delta 1 := by
            exact
              congrArg
                (fun value =>
                  Real.rpow delta (9 * epsilon / 10 - 1) * value)
                (Real.rpow_one delta).symm
          _ =
              Real.rpow delta
                ((9 * epsilon / 10 - 1) + 1) :=
            (Real.rpow_add hdelta _ _).symm
          _ = Real.rpow delta (9 * epsilon / 10) := by
            congr 1
            ring
      rw [hproduct]
      have hquotient :=
        Real.rpow_sub hdelta
          (9 * epsilon / 10)
          (1 - epsilon / 10)
      rw [show
        9 * epsilon / 10 - (1 - epsilon / 10) =
          epsilon - 1 by ring] at hquotient
      exact hquotient.symm
    have hcoefficient :
        (1 : ℝ) ≤ 288 / 31 := by norm_num
    calc
      Real.rpow delta (epsilon - 1)
          ≤ (288 / 31 : ℝ) *
              Real.rpow delta (epsilon - 1) := by
        exact
          (le_mul_iff_one_le_left
            (Real.rpow_pos_of_pos hdelta _)).2 hcoefficient
      _ =
          192 * Real.rpow delta (9 * epsilon / 10 - 1) *
              (delta / 4) /
              (31 * Real.rpow delta (1 - epsilon / 10) / 6) := by
        rw [← hrpowIdentity]
        ring
      _ ≤ (origin.selected.card : ℝ) := hpowerLower
  have hselectedENN :
      Kakeya.realRpowENN delta (epsilon - 1) ≤
        (origin.selected.card : ENNReal) := by
    rw [Kakeya.realRpowENN, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_mono hselectedReal
  exact
    ⟨{
      direction := origin.direction
      direction_unit := origin.direction_unit
      direction_transverse := origin.direction_transverse
      points := origin.selected
      points_subset := origin.selected_subset
      cardinality := hselectedENN
      origin_strip := origin.origin_strip
    }⟩

/-- The selected origin line gives the ambient `F` line count required by
Alternative A. -/
lemma WZ1NarrowTripleOriginLineData.first_line_count
    {delta epsilon eta : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {concentration :
      NarrowDotSpreadG1Concentrated
        delta epsilon data.width
        data.selectedF data.selectedG₁ data.selectedG₂
        data.refinedH data.direction}
    {obstruction :
      WZ1NarrowTripleConcentratedData
        parameters data concentration}
    (origin : WZ1NarrowTripleOriginLineData obstruction) :
    Kakeya.realRpowENN delta (epsilon - 1) ≤
      wz1DiscreteLineCount
        data.selectedF 0 (wz1Perp2 origin.direction) delta := by
  classical
  calc
    Kakeya.realRpowENN delta (epsilon - 1)
        ≤ (origin.points.card : ENNReal) :=
      origin.cardinality
    _ ≤
        wz1DiscreteLineCount
          data.selectedF 0 (wz1Perp2 origin.direction) delta := by
      simp only [wz1DiscreteLineCount]
      exact_mod_cast
        Finset.card_le_card
          (show
            origin.points ⊆
              data.selectedF.filter fun point =>
                point ∈
                  wz1LineNeighborhood
                    0 (wz1Perp2 origin.direction) delta by
            intro point hpoint
            exact Finset.mem_filter.mpr
              ⟨obstruction.firstPoints_subset
                  (origin.points_subset hpoint),
                origin.origin_strip point hpoint⟩)

end

end Kakeya.Assouad
