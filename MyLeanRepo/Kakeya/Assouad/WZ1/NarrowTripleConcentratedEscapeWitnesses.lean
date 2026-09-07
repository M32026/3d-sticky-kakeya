import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowTripleConcentratedSplitStatements

/-!
# Actual escape witnesses for the final narrow obstruction
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- If a finite set has at least `threshold` points but fewer than
`threshold` points in one strip, an actual point lies outside that strip. -/
lemma wz1Narrow_exists_outside_of_not_lineCount
    {A : DiscreteSet 2}
    {threshold : ENNReal}
    {base direction : Point2}
    {radius : ℝ}
    (hcard : threshold ≤ (A.card : ENNReal))
    (hnot :
      ¬ threshold ≤
        wz1DiscreteLineCount A base direction radius) :
    ∃ point ∈ A,
      point ∉ wz1LineNeighborhood base direction radius := by
  classical
  by_contra houtside
  push Not at houtside
  apply hnot
  calc
    threshold ≤ (A.card : ENNReal) := hcard
    _ =
        wz1DiscreteLineCount A base direction radius := by
      simp only [wz1DiscreteLineCount]
      rw [Finset.filter_eq_self.mpr]
      intro point hpoint
      exact houtside point hpoint

/-- The paper-scale first-coordinate fiber has at least the Alternative-A
threshold, even though its construction retained the stronger
`192 * delta^(9 epsilon / 10 - 1)` real-cardinality bound. -/
lemma wz1Narrow_firstPoints_card_threshold
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
    (hdeltaOne : delta ≤ 1)
    (hepsilon : 0 < epsilon) :
    Kakeya.realRpowENN delta (epsilon - 1) ≤
      (obstruction.firstPoints.card : ENNReal) := by
  rw [Kakeya.realRpowENN, ← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_mono
  calc
    Real.rpow delta (epsilon - 1) ≤
        Real.rpow delta (9 * epsilon / 10 - 1) := by
      exact
        Real.rpow_le_rpow_of_exponent_ge
          hdelta hdeltaOne (by linarith)
    _ ≤
        192 *
          Real.rpow delta (9 * epsilon / 10 - 1) := by
      have hnonnegative :
          0 ≤ Real.rpow delta (9 * epsilon / 10 - 1) :=
        Real.rpow_nonneg hdelta.le _
      nlinarith
    _ ≤ (obstruction.firstPoints.card : ℝ) :=
      obstruction.firstPoints_card

/-- The actual first-coordinate points outside the origin-centered strip
required by Alternative A. -/
noncomputable def wz1NarrowFirstEscapedPoints
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
        parameters data concentration) : DiscreteSet 2 := by
  classical
  exact
    obstruction.firstPoints.filter fun first =>
      first ∉
        wz1LineNeighborhood
          0 (wz1Perp2 data.direction) delta

/-- Failure of first-fiber alignment leaves a paper-scale family of escaped
actual first vertices, not merely one point. -/
lemma wz1Narrow_firstEscapedPoints_card
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
    (hdeltaOne : delta ≤ 1)
    (hepsilon : 0 < epsilon)
    (hescape : ¬ WZ1NarrowFirstFiberAligned obstruction) :
    191 * Real.rpow delta (9 * epsilon / 10 - 1) ≤
      ((wz1NarrowFirstEscapedPoints obstruction).card : ℝ) := by
  classical
  let alignedPoints :=
    obstruction.firstPoints.filter fun first =>
      first ∈
        wz1LineNeighborhood
          0 (wz1Perp2 data.direction) delta
  have haligned :
      (alignedPoints.card : ENNReal) <
        Kakeya.realRpowENN delta (epsilon - 1) := by
    simpa [WZ1NarrowFirstFiberAligned, wz1DiscreteLineCount,
      alignedPoints] using (lt_of_not_ge hescape)
  have hthreshold :
      Kakeya.realRpowENN delta (epsilon - 1) ≤
        ENNReal.ofReal
          (Real.rpow delta (9 * epsilon / 10 - 1)) := by
    rw [Kakeya.realRpowENN]
    exact ENNReal.ofReal_mono
      (Real.rpow_le_rpow_of_exponent_ge
        hdelta hdeltaOne (by linarith))
  have halignedReal :
      (alignedPoints.card : ℝ) ≤
        Real.rpow delta (9 * epsilon / 10 - 1) := by
    have halignedENN :
        (alignedPoints.card : ENNReal) ≤
          ENNReal.ofReal
            (Real.rpow delta (9 * epsilon / 10 - 1)) :=
      haligned.le.trans hthreshold
    have htoReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top halignedENN
    simpa [Real.rpow_nonneg hdelta.le] using htoReal
  have hpartition :
      obstruction.firstPoints.card =
        alignedPoints.card +
          (wz1NarrowFirstEscapedPoints obstruction).card := by
    simpa [alignedPoints, wz1NarrowFirstEscapedPoints,
      Finset.filter_not] using
        (Finset.card_filter_add_card_filter_not
          (s := obstruction.firstPoints)
          (p := fun first =>
            first ∈
              wz1LineNeighborhood
                0 (wz1Perp2 data.direction) delta)).symm
  have hpartitionReal :
      (obstruction.firstPoints.card : ℝ) =
        (alignedPoints.card : ℝ) +
          ((wz1NarrowFirstEscapedPoints obstruction).card : ℝ) := by
    exact_mod_cast hpartition
  linarith [obstruction.firstPoints_card, halignedReal]

/-- Every escaped first vertex retains its literal edge with the fixed
supplied endpoint pair. -/
lemma wz1Narrow_firstEscapedPoints_actual
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
    {first : Point2}
    (hfirst : first ∈ wz1NarrowFirstEscapedPoints obstruction) :
    first ∈ obstruction.firstPoints ∧
      (first, obstruction.second, obstruction.third) ∈
        data.refinedH ∧
      first ∉
        wz1LineNeighborhood
          0 (wz1Perp2 data.direction) delta := by
  classical
  rw [wz1NarrowFirstEscapedPoints, Finset.mem_filter] at hfirst
  exact
    ⟨hfirst.1,
      obstruction.firstPoints_actual first hfirst.1,
      hfirst.2⟩

/-- Failure of first-fiber alignment supplies an actual escaped first vertex
and its edge with the fixed supplied endpoint pair. -/
lemma wz1Narrow_firstFiberEscape_actual_edge
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
    (hdeltaOne : delta ≤ 1)
    (hepsilon : 0 < epsilon)
    (hescape : ¬ WZ1NarrowFirstFiberAligned obstruction) :
    ∃ first ∈ obstruction.firstPoints,
      (first, obstruction.second, obstruction.third) ∈
          data.refinedH ∧
        first ∉
          wz1LineNeighborhood
            0 (wz1Perp2 data.direction) delta := by
  classical
  have hcard :=
    wz1Narrow_firstEscapedPoints_card
      obstruction hdelta hdeltaOne hepsilon hescape
  have hpositive :
      0 <
        ((wz1NarrowFirstEscapedPoints obstruction).card : ℝ) := by
    have hrpow :
        0 < Real.rpow delta (9 * epsilon / 10 - 1) :=
      Real.rpow_pos_of_pos hdelta _
    linarith
  rcases
      Finset.card_pos.mp (by exact_mod_cast hpositive) with
    ⟨first, hfirst⟩
  rcases
      wz1Narrow_firstEscapedPoints_actual
        obstruction hfirst with
    ⟨hfirstPoints, hedge, houtside⟩
  exact ⟨first, hfirstPoints, hedge, houtside⟩

/-- The actual third-coordinate points outside the primary concentrated
`G₁` strip. -/
noncomputable def wz1NarrowThirdEscapedPoints
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
        parameters data concentration) : DiscreteSet 2 := by
  classical
  exact
    obstruction.thirdPoints.filter fun third =>
      third ∉
        wz1LineNeighborhood
          concentration.base data.direction delta

/-- Because the producer retains twice the Alternative-A threshold, failure
of third-fiber alignment leaves a full threshold-sized escaped family. -/
lemma wz1Narrow_thirdEscapedPoints_card
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
    (hescape : ¬ WZ1NarrowThirdFiberAligned obstruction) :
    Kakeya.realRpowENN delta (epsilon - 1) ≤
      ((wz1NarrowThirdEscapedPoints obstruction).card : ENNReal) := by
  classical
  let aligned :=
    obstruction.thirdPoints.filter fun third =>
      third ∈
        wz1LineNeighborhood
          concentration.base data.direction delta
  have haligned :
      (aligned.card : ENNReal) <
        Kakeya.realRpowENN delta (epsilon - 1) := by
    simpa [WZ1NarrowThirdFiberAligned, wz1DiscreteLineCount,
      aligned] using (lt_of_not_ge hescape)
  have hpartition :
      obstruction.thirdPoints.card =
        aligned.card +
          (wz1NarrowThirdEscapedPoints obstruction).card := by
    simpa [aligned, wz1NarrowThirdEscapedPoints,
      Finset.filter_not] using
        (Finset.card_filter_add_card_filter_not
          (s := obstruction.thirdPoints)
          (p := fun third =>
            third ∈
              wz1LineNeighborhood
                concentration.base data.direction delta)).symm
  have hpartitionReal :
      (obstruction.thirdPoints.card : ℝ) =
        (aligned.card : ℝ) +
          ((wz1NarrowThirdEscapedPoints obstruction).card : ℝ) := by
    exact_mod_cast hpartition
  have htotalReal :=
    ENNReal.toReal_mono
      (by simp :
        (obstruction.thirdPoints.card : ENNReal) ≠ ⊤)
      obstruction.thirdPoints_card
  have halignedReal :=
    ENNReal.toReal_mono
      (by simp [Kakeya.realRpowENN] :
        Kakeya.realRpowENN delta (epsilon - 1) ≠ ⊤)
      haligned.le
  have hthresholdPositive :
      0 < Kakeya.realRpowENN delta (epsilon - 1) := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    apply hescape
    simp [WZ1NarrowThirdFiberAligned, hzero]
  have hrpowPositive :
      0 < Real.rpow delta (epsilon - 1) := by
    simpa [Kakeya.realRpowENN, ENNReal.ofReal_pos] using
      hthresholdPositive
  rw [Kakeya.realRpowENN, ← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_mono
  have hnonnegative :
      0 ≤ Real.rpow delta (epsilon - 1) :=
    hrpowPositive.le
  simp only [Kakeya.realRpowENN] at htotalReal
  simp only [Kakeya.realRpowENN] at halignedReal
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal hnonnegative] at htotalReal
  rw [ENNReal.toReal_ofReal hnonnegative] at halignedReal
  have htotalReal' :
      2 * Real.rpow delta (epsilon - 1) ≤
        (obstruction.thirdPoints.card : ℝ) := by
    simpa using htotalReal
  have halignedReal' :
      (aligned.card : ℝ) ≤
        Real.rpow delta (epsilon - 1) := by
    simpa using halignedReal
  linarith

/-- Every escaped third vertex retains its literal edge with the fixed
supplied first/second pair. -/
lemma wz1Narrow_thirdEscapedPoints_actual
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
    {third : Point2}
    (hthird : third ∈ wz1NarrowThirdEscapedPoints obstruction) :
    third ∈ obstruction.thirdPoints ∧
      (concentration.first, obstruction.second, third) ∈
        data.refinedH ∧
      third ∉
        wz1LineNeighborhood
          concentration.base data.direction delta := by
  classical
  rw [wz1NarrowThirdEscapedPoints, Finset.mem_filter] at hthird
  exact
    ⟨hthird.1,
      obstruction.thirdPoints_actual third hthird.1,
      hthird.2⟩

/-- Failure of third-fiber alignment supplies an actual escaped third vertex
and its edge with the fixed supplied first/second pair. -/
lemma wz1Narrow_thirdFiberEscape_actual_edge
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
    (hescape : ¬ WZ1NarrowThirdFiberAligned obstruction) :
    ∃ third ∈ obstruction.thirdPoints,
      (concentration.first, obstruction.second, third) ∈
          data.refinedH ∧
        third ∉
          wz1LineNeighborhood
            concentration.base data.direction delta := by
  classical
  have hcard :=
    wz1Narrow_thirdEscapedPoints_card obstruction hescape
  have hpositive :
      0 <
        ((wz1NarrowThirdEscapedPoints obstruction).card :
          ENNReal) :=
    (by
      have hpow :
          0 < Kakeya.realRpowENN delta (epsilon - 1) := by
        apply pos_iff_ne_zero.mpr
        intro hzero
        apply hescape
        simp [WZ1NarrowThirdFiberAligned, hzero]
      exact hpow.trans_le hcard)
  rcases
      Finset.card_pos.mp (by exact_mod_cast hpositive) with
    ⟨third, hthird⟩
  rcases
      wz1Narrow_thirdEscapedPoints_actual
        obstruction hthird with
    ⟨hthirdPoints, hedge, houtside⟩
  exact ⟨third, hthirdPoints, hedge, houtside⟩

end Kakeya.Assouad
