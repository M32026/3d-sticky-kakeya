import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedCellNormalizationStatements

/-!
# Actual-source package for repaired wide snapped transport

Choose one actual source edge for every normalized edge, retaining graph
membership, pointwise dot approximation, and the source-dot radius bound.
-/

namespace Kakeya.Assouad

/-- Actual source dots attached to one normalized fixed-cell core. -/
structure WZ1WideSnappedSourceData
    {delta epsilon eta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data : WZ1Proposition8_9CommonStripData
      delta epsilon eta parameters F G₁ G₂ H}
    {coarse : WZ1Proposition8_9WideCoarseData
      delta epsilon eta parameters F G₁ G₂ H data}
    {fixed : WZ1Proposition8_9WideFixedCellData coarse}
    (core : WZ1Proposition8_9WideNormalizedCoreData fixed) where
  sourceH : Finset (Point2 × Point2 × Point2)
  sourceH_subset : sourceH ⊆ H
  approximation :
    ∀ value ∈
        (fun normalizedValue : ℝ =>
          core.effectiveWidth * normalizedValue) ''
          wz1DotDifferenceSet core.normalizedH,
      ∃ sourceValue ∈ wz1DotDifferenceSet sourceH,
        dist value sourceValue ≤ core.sourceError
  source_dot_bound :
    ∀ sourceValue ∈ wz1DotDifferenceSet sourceH,
      |sourceValue| ≤
        2 * core.effectiveWidth + core.sourceError

/-- Construct the actual-source package from the core provenance fields. -/
lemma wz1_wide_snapped_source_data
    {delta epsilon eta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data : WZ1Proposition8_9CommonStripData
      delta epsilon eta parameters F G₁ G₂ H}
    {coarse : WZ1Proposition8_9WideCoarseData
      delta epsilon eta parameters F G₁ G₂ H data}
    {fixed : WZ1Proposition8_9WideFixedCellData coarse}
    (core : WZ1Proposition8_9WideNormalizedCoreData fixed) :
    Nonempty (WZ1WideSnappedSourceData core) := by
  classical
  let chooseSource :
      Point2 × Point2 × Point2 →
        Point2 × Point2 × Point2 :=
    fun normalizedEdge =>
      if h : normalizedEdge ∈ core.normalizedH then
        Classical.choose
          (core.source_approximation normalizedEdge h)
      else
        (0, 0, 0)
  let sourceH : Finset (Point2 × Point2 × Point2) :=
    core.normalizedH.image chooseSource
  have hsourceMem :
      ∀ normalizedEdge ∈ core.normalizedH,
        chooseSource normalizedEdge ∈ data.refinedH := by
    intro normalizedEdge hedge
    have hchoose :
        chooseSource normalizedEdge =
          Classical.choose
            (core.source_approximation normalizedEdge hedge) := by
      simp [chooseSource, hedge]
    rw [hchoose]
    exact
      (Classical.choose_spec
        (core.source_approximation normalizedEdge hedge)).1
  have hsourceApprox :
      ∀ normalizedEdge ∈ core.normalizedH,
        |inner ℝ (chooseSource normalizedEdge).1
              ((chooseSource normalizedEdge).2.1 -
                (chooseSource normalizedEdge).2.2) -
            core.effectiveWidth *
              inner ℝ normalizedEdge.1
                (normalizedEdge.2.1 - normalizedEdge.2.2)| ≤
          core.sourceError := by
    intro normalizedEdge hedge
    have hchoose :
        chooseSource normalizedEdge =
          Classical.choose
            (core.source_approximation normalizedEdge hedge) := by
      simp [chooseSource, hedge]
    rw [hchoose]
    exact
      (Classical.choose_spec
        (core.source_approximation normalizedEdge hedge)).2
  have hsourceSubset : sourceH ⊆ H := by
    intro sourceEdge hsourceEdge
    rcases Finset.mem_image.mp hsourceEdge with
      ⟨normalizedEdge, hedge, rfl⟩
    exact data.refinedH_subset
      (hsourceMem normalizedEdge hedge)
  have happroximation :
      ∀ value ∈
          (fun normalizedValue : ℝ =>
            core.effectiveWidth * normalizedValue) ''
            wz1DotDifferenceSet core.normalizedH,
        ∃ sourceValue ∈ wz1DotDifferenceSet sourceH,
          dist value sourceValue ≤ core.sourceError := by
    intro value hvalue
    rcases hvalue with
      ⟨normalizedValue, hnormalizedValue, rfl⟩
    rcases Finset.mem_image.mp hnormalizedValue with
      ⟨normalizedEdge, hedge, rfl⟩
    let sourceEdge := chooseSource normalizedEdge
    let sourceValue :=
      inner ℝ sourceEdge.1
        (sourceEdge.2.1 - sourceEdge.2.2)
    have hsourceEdge : sourceEdge ∈ sourceH :=
      Finset.mem_image.mpr
        ⟨normalizedEdge, hedge, rfl⟩
    have hsourceValue :
        sourceValue ∈ wz1DotDifferenceSet sourceH :=
      Finset.mem_image.mpr
        ⟨sourceEdge, hsourceEdge, rfl⟩
    have herror := hsourceApprox normalizedEdge hedge
    refine ⟨sourceValue, hsourceValue, ?_⟩
    change
      |core.effectiveWidth *
            inner ℝ normalizedEdge.1
              (normalizedEdge.2.1 -
                normalizedEdge.2.2) -
          inner ℝ sourceEdge.1
            (sourceEdge.2.1 - sourceEdge.2.2)| ≤
        core.sourceError
    rw [abs_sub_comm]
    exact herror
  have hsourceDotBound :
      ∀ sourceValue ∈ wz1DotDifferenceSet sourceH,
        |sourceValue| ≤
          2 * core.effectiveWidth +
            core.sourceError := by
    intro sourceValue hsourceValue
    rcases Finset.mem_image.mp hsourceValue with
      ⟨sourceEdge, hsourceEdge, rfl⟩
    rcases Finset.mem_image.mp hsourceEdge with
      ⟨normalizedEdge, hedge, rfl⟩
    let normalizedValue :=
      inner ℝ normalizedEdge.1
        (normalizedEdge.2.1 -
          normalizedEdge.2.2)
    have hnormalizedValue :
        normalizedValue ∈
          wz1DotDifferenceSet core.normalizedH :=
      Finset.mem_image.mpr
        ⟨normalizedEdge, hedge, rfl⟩
    have hnormalizedBound : |normalizedValue| ≤ 2 :=
      core.normalized_dot_bound
        normalizedValue hnormalizedValue
    have herror := hsourceApprox normalizedEdge hedge
    have habs :
        |inner ℝ (chooseSource normalizedEdge).1
            ((chooseSource normalizedEdge).2.1 -
              (chooseSource normalizedEdge).2.2)| ≤
          |core.effectiveWidth * normalizedValue| +
            core.sourceError := by
      calc
        |inner ℝ (chooseSource normalizedEdge).1
              ((chooseSource normalizedEdge).2.1 -
                (chooseSource normalizedEdge).2.2)| =
            |core.effectiveWidth * normalizedValue +
              (inner ℝ (chooseSource normalizedEdge).1
                ((chooseSource normalizedEdge).2.1 -
                  (chooseSource normalizedEdge).2.2) -
                core.effectiveWidth *
                  normalizedValue)| := by
          congr 1
          ring
        _ ≤
            |core.effectiveWidth * normalizedValue| +
              |inner ℝ (chooseSource normalizedEdge).1
                ((chooseSource normalizedEdge).2.1 -
                  (chooseSource normalizedEdge).2.2) -
                core.effectiveWidth *
                  normalizedValue| :=
          abs_add_le _ _
        _ ≤
            |core.effectiveWidth * normalizedValue| +
              core.sourceError := by
          gcongr
    calc
      |inner ℝ (chooseSource normalizedEdge).1
          ((chooseSource normalizedEdge).2.1 -
            (chooseSource normalizedEdge).2.2)| ≤
        |core.effectiveWidth * normalizedValue| +
          core.sourceError := habs
      _ =
          core.effectiveWidth * |normalizedValue| +
            core.sourceError := by
        rw [abs_mul,
          abs_of_pos core.effectiveWidth_pos]
      _ ≤
          core.effectiveWidth * 2 +
            core.sourceError := by
        simpa [add_comm] using
          add_le_add_right
            (mul_le_mul_of_nonneg_left
              hnormalizedBound
              core.effectiveWidth_pos.le)
            core.sourceError
      _ =
          2 * core.effectiveWidth +
            core.sourceError := by ring
  exact
    ⟨⟨sourceH, hsourceSubset,
      happroximation, hsourceDotBound⟩⟩

end Kakeya.Assouad
