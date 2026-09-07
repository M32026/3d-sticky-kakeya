import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowOriginDirectionPigeonhole

/-!
# Rotate both endpoint fibers to the selected origin-line direction

The triple obstruction retains doubled endpoint thresholds.  Once the large
`F` fiber selects a nearby origin-line direction, each endpoint fiber can be
rotated to that same direction while retaining one complete paper threshold.
-/

namespace Kakeya.Assouad

open scoped ENNReal


structure WZ1NarrowTripleRotatedEndpointLinesData
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
    (origin : WZ1NarrowTripleOriginLineData obstruction) where
  firstPoints : Finset Point2
  firstPoints_subset : firstPoints ⊆ concentration.points
  firstPoints_card :
    Kakeya.realRpowENN delta (epsilon - 1) ≤
      (firstPoints.card : ENNReal)
  firstBase : Point2
  first_strip :
    ∀ point ∈ firstPoints,
      point ∈
        wz1LineNeighborhood
          firstBase origin.direction delta
  thirdPoints : Finset Point2
  thirdPoints_subset : thirdPoints ⊆ obstruction.thirdPoints
  thirdPoints_card :
    Kakeya.realRpowENN delta (epsilon - 1) ≤
      (thirdPoints.card : ENNReal)
  thirdBase : Point2
  third_strip :
    ∀ point ∈ thirdPoints,
      point ∈
        wz1LineNeighborhood
          thirdBase origin.direction delta

/-- Rotate both doubled endpoint fibers to the nearby origin-line direction. -/
theorem WZ1NarrowTripleOriginLineData.rotate_endpoint_fibers
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
    (origin : WZ1NarrowTripleOriginLineData obstruction)
    (hdelta : 0 < delta) :
    Nonempty
      (WZ1NarrowTripleRotatedEndpointLinesData obstruction origin) := by
  rcases
      narrow_rotated_fiber_pigeonhole
        hdelta data.width_pos data.direction_unit
        origin.direction_unit
        (origin.direction_transverse.trans
          (by nlinarith [data.width_pos] :
            31 * data.width / 12 ≤ 4 * data.width))
        concentration.strip concentration.longitudinal
        concentration.card_lower with
    ⟨firstPoints, hfirstSubset, hfirstCard, firstBase, hfirstStrip⟩
  rcases
      narrow_rotated_fiber_pigeonhole
        hdelta data.width_pos data.direction_unit
        origin.direction_unit
        (origin.direction_transverse.trans
          (by nlinarith [data.width_pos] :
            31 * data.width / 12 ≤ 4 * data.width))
        obstruction.thirdPoints_strip
        obstruction.thirdPoints_longitudinal
        obstruction.thirdPoints_card with
    ⟨thirdPoints, hthirdSubset, hthirdCard, thirdBase, hthirdStrip⟩
  exact
    ⟨{
      firstPoints := firstPoints
      firstPoints_subset := hfirstSubset
      firstPoints_card := hfirstCard
      firstBase := firstBase
      first_strip := hfirstStrip
      thirdPoints := thirdPoints
      thirdPoints_subset := hthirdSubset
      thirdPoints_card := hthirdCard
      thirdBase := thirdBase
      third_strip := hthirdStrip
    }⟩

namespace WZ1NarrowTripleRotatedEndpointLinesData

/-- The rotated first endpoint fiber gives the ambient `G₁` line count. -/
lemma first_line_count
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
    {origin : WZ1NarrowTripleOriginLineData obstruction}
    (lines :
      WZ1NarrowTripleRotatedEndpointLinesData obstruction origin) :
    Kakeya.realRpowENN delta (epsilon - 1) ≤
      wz1DiscreteLineCount
        data.selectedG₁ lines.firstBase origin.direction delta := by
  classical
  calc
    Kakeya.realRpowENN delta (epsilon - 1)
        ≤ (lines.firstPoints.card : ENNReal) :=
      lines.firstPoints_card
    _ ≤
        wz1DiscreteLineCount
          data.selectedG₁ lines.firstBase origin.direction delta := by
      simp only [wz1DiscreteLineCount]
      exact_mod_cast
        Finset.card_le_card
          (show
            lines.firstPoints ⊆
              data.selectedG₁.filter fun point =>
                point ∈
                  wz1LineNeighborhood
                    lines.firstBase origin.direction delta by
            intro point hpoint
            exact Finset.mem_filter.mpr
              ⟨concentration.subset
                  (lines.firstPoints_subset hpoint),
                lines.first_strip point hpoint⟩)

noncomputable def firstLevel
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
    {origin : WZ1NarrowTripleOriginLineData obstruction}
    (lines :
      WZ1NarrowTripleRotatedEndpointLinesData obstruction origin) : ℝ :=
  inner ℝ lines.firstBase (wz1Perp2 origin.direction)

noncomputable def thirdLevel
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
    {origin : WZ1NarrowTripleOriginLineData obstruction}
    (lines :
      WZ1NarrowTripleRotatedEndpointLinesData obstruction origin) : ℝ :=
  inner ℝ lines.thirdBase (wz1Perp2 origin.direction)

end WZ1NarrowTripleRotatedEndpointLinesData

/-- Any selected endpoint pair realizes the difference of the two canonical
normal levels up to the two radius-`delta` strip errors. -/
lemma WZ1NarrowTripleRotatedEndpointLinesData.endpoint_pair_level_gap
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
    {origin : WZ1NarrowTripleOriginLineData obstruction}
    (lines :
      WZ1NarrowTripleRotatedEndpointLinesData obstruction origin)
    {firstPoint thirdPoint : Point2}
    (hfirst : firstPoint ∈ lines.firstPoints)
    (hthird : thirdPoint ∈ lines.thirdPoints) :
    |inner ℝ (firstPoint - thirdPoint)
          (wz1Perp2 origin.direction) -
        (lines.firstLevel - lines.thirdLevel)| ≤
      2 * delta := by
  let normal := wz1Perp2 origin.direction
  have hfirstWindow := lines.first_strip firstPoint hfirst
  have hthirdWindow := lines.third_strip thirdPoint hthird
  change
    |inner ℝ (firstPoint - lines.firstBase) normal| ≤ delta
    at hfirstWindow
  change
    |inner ℝ (thirdPoint - lines.thirdBase) normal| ≤ delta
    at hthirdWindow
  have heq :
      inner ℝ (firstPoint - thirdPoint) normal -
          (lines.firstLevel - lines.thirdLevel) =
        inner ℝ (firstPoint - lines.firstBase) normal -
          inner ℝ (thirdPoint - lines.thirdBase) normal := by
    simp only [inner_sub_left]
    change
      (inner ℝ firstPoint normal - inner ℝ thirdPoint normal) -
          (inner ℝ lines.firstBase normal -
            inner ℝ lines.thirdBase normal) =
        (inner ℝ firstPoint normal -
            inner ℝ lines.firstBase normal) -
          (inner ℝ thirdPoint normal -
            inner ℝ lines.thirdBase normal)
    ring
  change
    |inner ℝ (firstPoint - thirdPoint) normal -
        (lines.firstLevel - lines.thirdLevel)| ≤ 2 * delta
  rw [heq]
  exact (abs_sub _ _).trans (by linarith)

/-- A large canonical endpoint-level gap forces every selected literal
endpoint pair to have a large transverse displacement. -/
lemma WZ1NarrowTripleRotatedEndpointLinesData.endpoint_pair_transverse_lower
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
    {origin : WZ1NarrowTripleOriginLineData obstruction}
    (lines :
      WZ1NarrowTripleRotatedEndpointLinesData obstruction origin)
    (hgap :
      11 * delta ≤ |lines.firstLevel - lines.thirdLevel|)
    {firstPoint thirdPoint : Point2}
    (hfirst : firstPoint ∈ lines.firstPoints)
    (hthird : thirdPoint ∈ lines.thirdPoints) :
    9 * delta ≤
      |inner ℝ (firstPoint - thirdPoint)
        (wz1Perp2 origin.direction)| := by
  have hclose :=
    lines.endpoint_pair_level_gap hfirst hthird
  have htriangle :
      |lines.firstLevel - lines.thirdLevel| ≤
        |inner ℝ (firstPoint - thirdPoint)
            (wz1Perp2 origin.direction)| +
          |inner ℝ (firstPoint - thirdPoint)
              (wz1Perp2 origin.direction) -
            (lines.firstLevel - lines.thirdLevel)| := by
    have heq :
        lines.firstLevel - lines.thirdLevel =
          inner ℝ (firstPoint - thirdPoint)
              (wz1Perp2 origin.direction) -
            (inner ℝ (firstPoint - thirdPoint)
                (wz1Perp2 origin.direction) -
              (lines.firstLevel - lines.thirdLevel)) := by
      ring
    calc
      |lines.firstLevel - lines.thirdLevel| =
          |inner ℝ (firstPoint - thirdPoint)
              (wz1Perp2 origin.direction) -
            (inner ℝ (firstPoint - thirdPoint)
                (wz1Perp2 origin.direction) -
              (lines.firstLevel - lines.thirdLevel))| := by
        rw [← heq]
      _ ≤
          |inner ℝ (firstPoint - thirdPoint)
              (wz1Perp2 origin.direction)| +
            |inner ℝ (firstPoint - thirdPoint)
                (wz1Perp2 origin.direction) -
              (lines.firstLevel - lines.thirdLevel)| :=
        abs_sub _ _
  linarith

/-- A sufficiently large endpoint-level gap gives a pair of literal endpoint
vertices whose dot product against every retained origin-line `F` point is
strictly `2 * delta` away from zero. -/
lemma WZ1NarrowTripleRotatedEndpointLinesData.large_gap_dot_separation
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
    {origin : WZ1NarrowTripleOriginLineData obstruction}
    (lines :
      WZ1NarrowTripleRotatedEndpointLinesData obstruction origin)
    (hdelta : 0 < delta)
    (hwidthQuarter : data.width ≤ 1 / 4)
    (hgap :
      17 * delta ≤ |lines.firstLevel - lines.thirdLevel|)
    {firstPoint thirdPoint point : Point2}
    (hfirst : firstPoint ∈ lines.firstPoints)
    (hthird : thirdPoint ∈ lines.thirdPoints)
    (hpoint : point ∈ origin.points) :
    2 * delta <
      |inner ℝ point (firstPoint - thirdPoint)| := by
  have hpointSelected :
      point ∈ data.selectedF :=
    obstruction.firstPoints_subset
      (origin.points_subset hpoint)
  have hpointNorm : ‖point‖ ≤ 1 := by
    simpa [dist_zero_right] using
      data.selectedF_ball point hpointSelected
  have hpointSeparated :
      1 / 2 ≤ dist point 0 :=
    data.standardSeparation.2.2.2.2 point hpointSelected
  have hpointStrip :=
    origin.origin_strip point hpoint
  have hperpendicular :
      1 / 3 ≤
        |inner ℝ point (wz1Perp2 origin.direction)| :=
    large_perp_component
      origin.direction_unit hpointSeparated hpointStrip
      (data.delta_le_width.trans hwidthQuarter)
  have hperpPerp :
      wz1Perp2 (wz1Perp2 origin.direction) =
        -origin.direction := by
    ext coordinate
    fin_cases coordinate <;>
      simp [wz1Perp2_coords]
  have hpointDirection :
      |inner ℝ point origin.direction| ≤ delta := by
    change
      |inner ℝ (point - 0)
        (wz1Perp2 (wz1Perp2 origin.direction))| ≤ delta
        at hpointStrip
    simpa [hperpPerp, inner_neg_right, abs_neg] using hpointStrip
  have hfirstSelected :
      firstPoint ∈ data.selectedG₁ :=
    concentration.subset
      (lines.firstPoints_subset hfirst)
  have hthirdSelected :
      thirdPoint ∈ data.selectedG₂ :=
    obstruction.thirdPoints_subset
      (lines.thirdPoints_subset hthird)
  have hfirstNorm : ‖firstPoint‖ ≤ 1 := by
    simpa [dist_zero_right] using
      data.selectedG₁_ball firstPoint hfirstSelected
  have hthirdNorm : ‖thirdPoint‖ ≤ 1 := by
    simpa [dist_zero_right] using
      data.selectedG₂_ball thirdPoint hthirdSelected
  have hlongitudinal :
      |inner ℝ (firstPoint - thirdPoint) origin.direction| ≤ 2 := by
    calc
      |inner ℝ (firstPoint - thirdPoint) origin.direction|
          ≤ ‖firstPoint - thirdPoint‖ * ‖origin.direction‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖firstPoint - thirdPoint‖ := by
        rw [origin.direction_unit, mul_one]
      _ ≤ ‖firstPoint‖ + ‖thirdPoint‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
  have htransverse :
      15 * delta ≤
        |inner ℝ (firstPoint - thirdPoint)
          (wz1Perp2 origin.direction)| := by
    have hclose :=
      lines.endpoint_pair_level_gap hfirst hthird
    have htriangle :
        |lines.firstLevel - lines.thirdLevel| ≤
          |inner ℝ (firstPoint - thirdPoint)
              (wz1Perp2 origin.direction)| +
            |inner ℝ (firstPoint - thirdPoint)
                (wz1Perp2 origin.direction) -
              (lines.firstLevel - lines.thirdLevel)| := by
      have heq :
          lines.firstLevel - lines.thirdLevel =
            inner ℝ (firstPoint - thirdPoint)
                (wz1Perp2 origin.direction) -
              (inner ℝ (firstPoint - thirdPoint)
                  (wz1Perp2 origin.direction) -
                (lines.firstLevel - lines.thirdLevel)) := by
        ring
      exact
        (congrArg abs heq).le.trans
          (abs_sub
            (inner ℝ (firstPoint - thirdPoint)
              (wz1Perp2 origin.direction))
            (inner ℝ (firstPoint - thirdPoint)
                (wz1Perp2 origin.direction) -
              (lines.firstLevel - lines.thirdLevel)))
    linarith
  let parallel :=
    inner ℝ (firstPoint - thirdPoint) origin.direction
  let perpendicular :=
    inner ℝ (firstPoint - thirdPoint)
      (wz1Perp2 origin.direction)
  have hdecomposition :
      firstPoint - thirdPoint =
        parallel • origin.direction +
          perpendicular • wz1Perp2 origin.direction :=
    orthonormal_decomp
      (firstPoint - thirdPoint)
      origin.direction origin.direction_unit
  have hinner :
      inner ℝ point (firstPoint - thirdPoint) =
        inner ℝ point origin.direction * parallel +
          inner ℝ point (wz1Perp2 origin.direction) *
            perpendicular := by
    rw [hdecomposition, inner_add_right,
      inner_smul_right, inner_smul_right]
    ring
  have hmain :
      5 * delta ≤
        |inner ℝ point (wz1Perp2 origin.direction) *
          perpendicular| := by
    rw [abs_mul]
    calc
      5 * delta = (1 / 3 : ℝ) * (15 * delta) := by ring
      _ ≤
          |inner ℝ point (wz1Perp2 origin.direction)| *
            |perpendicular| := by
        gcongr
  have herror :
      |inner ℝ point origin.direction * parallel| ≤
        2 * delta := by
    rw [abs_mul]
    calc
      |inner ℝ point origin.direction| * |parallel|
          ≤ delta * 2 := by
        gcongr
      _ = 2 * delta := by ring
  have habsolute :
      |inner ℝ point (wz1Perp2 origin.direction) *
            perpendicular| -
          |inner ℝ point origin.direction * parallel| ≤
        |inner ℝ point origin.direction * parallel +
          inner ℝ point (wz1Perp2 origin.direction) *
            perpendicular| :=
    by
      simpa [add_comm] using
        (abs_sub_abs_le_abs_add
          (inner ℝ point (wz1Perp2 origin.direction) * perpendicular)
          (inner ℝ point origin.direction * parallel))
  rw [hinner]
  linarith

/-- Equal canonical endpoint bases close Alternative A immediately. -/
theorem WZ1NarrowTripleRotatedEndpointLinesData.alternativeA_of_base_eq
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
    {origin : WZ1NarrowTripleOriginLineData obstruction}
    (lines :
      WZ1NarrowTripleRotatedEndpointLinesData obstruction origin)
    (hbase : lines.firstBase = lines.thirdBase) :
    WZ1Proposition8_9AlternativeA
      delta epsilon
      data.selectedF data.selectedG₁ data.selectedG₂ := by
  classical
  refine
    ⟨lines.firstBase, origin.direction,
      origin.direction_unit,
      origin.first_line_count, ?_, ?_⟩
  · calc
      Kakeya.realRpowENN delta (epsilon - 1)
          ≤ (lines.firstPoints.card : ENNReal) :=
        lines.firstPoints_card
      _ ≤
          wz1DiscreteLineCount
            data.selectedG₁ lines.firstBase
              origin.direction delta := by
        simp only [wz1DiscreteLineCount]
        exact_mod_cast
          Finset.card_le_card
            (show
              lines.firstPoints ⊆
                data.selectedG₁.filter fun point =>
                  point ∈
                    wz1LineNeighborhood
                      lines.firstBase origin.direction delta by
              intro point hpoint
              exact Finset.mem_filter.mpr
                ⟨concentration.subset
                    (lines.firstPoints_subset hpoint),
                  lines.first_strip point hpoint⟩)
  · calc
      Kakeya.realRpowENN delta (epsilon - 1)
          ≤ (lines.thirdPoints.card : ENNReal) :=
        lines.thirdPoints_card
      _ ≤
          wz1DiscreteLineCount
            data.selectedG₂ lines.firstBase
              origin.direction delta := by
        simp only [wz1DiscreteLineCount]
        exact_mod_cast
          Finset.card_le_card
            (show
              lines.thirdPoints ⊆
                data.selectedG₂.filter fun point =>
                  point ∈
                    wz1LineNeighborhood
                      lines.firstBase origin.direction delta by
              intro point hpoint
              apply Finset.mem_filter.mpr
              refine
                ⟨obstruction.thirdPoints_subset
                    (lines.thirdPoints_subset hpoint), ?_⟩
              simpa [hbase] using
                lines.third_strip point hpoint)

/-- Equal normal levels, rather than literal equality of the chosen base
vectors, are exactly what is needed for one common affine endpoint line. -/
theorem WZ1NarrowTripleRotatedEndpointLinesData.alternativeA_of_level_eq
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
    {origin : WZ1NarrowTripleOriginLineData obstruction}
    (lines :
      WZ1NarrowTripleRotatedEndpointLinesData obstruction origin)
    (hlevel : lines.firstLevel = lines.thirdLevel) :
    WZ1Proposition8_9AlternativeA
      delta epsilon
      data.selectedF data.selectedG₁ data.selectedG₂ := by
  classical
  let normal := wz1Perp2 origin.direction
  refine
    ⟨lines.firstBase, origin.direction,
      origin.direction_unit,
      origin.first_line_count, ?_, ?_⟩
  · calc
      Kakeya.realRpowENN delta (epsilon - 1)
          ≤ (lines.firstPoints.card : ENNReal) :=
        lines.firstPoints_card
      _ ≤
          wz1DiscreteLineCount
            data.selectedG₁ lines.firstBase
              origin.direction delta := by
        simp only [wz1DiscreteLineCount]
        exact_mod_cast
          Finset.card_le_card
            (show
              lines.firstPoints ⊆
                data.selectedG₁.filter fun point =>
                  point ∈
                    wz1LineNeighborhood
                      lines.firstBase origin.direction delta by
              intro point hpoint
              exact Finset.mem_filter.mpr
                ⟨concentration.subset
                    (lines.firstPoints_subset hpoint),
                  lines.first_strip point hpoint⟩)
  · calc
      Kakeya.realRpowENN delta (epsilon - 1)
          ≤ (lines.thirdPoints.card : ENNReal) :=
        lines.thirdPoints_card
      _ ≤
          wz1DiscreteLineCount
            data.selectedG₂ lines.firstBase
              origin.direction delta := by
        simp only [wz1DiscreteLineCount]
        exact_mod_cast
          Finset.card_le_card
            (show
              lines.thirdPoints ⊆
                data.selectedG₂.filter fun point =>
                  point ∈
                    wz1LineNeighborhood
                      lines.firstBase origin.direction delta by
              intro point hpoint
              apply Finset.mem_filter.mpr
              refine
                ⟨obstruction.thirdPoints_subset
                    (lines.thirdPoints_subset hpoint), ?_⟩
              have hthird := lines.third_strip point hpoint
              change
                |inner ℝ (point - lines.thirdBase) normal| ≤ delta
                at hthird
              change
                |inner ℝ (point - lines.firstBase) normal| ≤ delta
              have heq :
                  inner ℝ (point - lines.firstBase) normal =
                    inner ℝ (point - lines.thirdBase) normal := by
                simp only [inner_sub_left]
                change
                  inner ℝ point normal - lines.firstLevel =
                    inner ℝ point normal - lines.thirdLevel
                rw [hlevel]
              rw [heq]
              exact hthird)

end Kakeya.Assouad
