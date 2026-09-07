import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineReadyGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.LocallyLinearOneScale.AlternativeAToTrapezoids

/-!
# Pull Alternative A back to actual coarse-grain height cells
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2HorizontalAlternativeAHeightData
    {sigma inputLoss delta rho middleLoss outputLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading : PureWZ2HorizontalFixedLineResidueShadingData residue}
    {prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading}
    {graphParents : PureWZ2HorizontalFixedLineGraphParentData prep}
    {sources : PureWZ2HorizontalFixedLineResidueSourceFamily residueShading}
    {fullGrains : PureWZ2HorizontalFixedLineResidueFullGrainFamily
      (eta := eta) sources prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2HorizontalFixedLineSharpGeometry graph}
    (ready : PureWZ2HorizontalFixedLineReadyGraph
      (eta := eta) (theoremEta := theoremEta)
      (graphParents := graphParents) (sources := sources)
      (fullGrains := fullGrains) sharp)
    (epsilon : ℝ) where
  direction : Point2
  direction_unit : ‖direction‖ = 1
  richF : Finset Point2
  richF_eq : richF = ready.common.F.filter fun point =>
    point ∈ wz1LineNeighborhood 0 (wz1Perp2 direction)
      ready.ready.deltaGraph
  richF_nonempty : richF.Nonempty
  richF_card :
    Kakeya.realRpowENN ready.ready.deltaGraph (epsilon - 1) ≤
      (richF.card : ENNReal)
  pathFor : Point2 →
    ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) ×
      (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ))
  path_mem : ∀ point ∈ richF, pathFor point ∈ sharp.sharp.actual.cycles
  point_eq : ∀ point ∈ richF,
    point = wz1Lemma23UnitBallPoint
      ((1 / Real.sqrt prep.graphScale) •
        wz1Lemma23SnappedHeightPoint prep.graphScale
          prep.windowed.global.extendedSlope
          sharp.sharp.baseHeightIndex (pathFor point).2.1)
  cell_mem : ∀ point ∈ richF,
    (pathFor point).2.1 ∈ graph.residue.cells
  heightIndex : Point2 → ℤ
  heightIndex_eq : ∀ point ∈ richF,
    heightIndex point = (pathFor point).2.1.2.2
  heightIndex_injective : Set.InjOn heightIndex richF
  heightIndices : Finset ℤ := richF.image heightIndex
  heightIndices_eq : heightIndices = richF.image heightIndex
  heightIndices_card : heightIndices.card = richF.card
  centered_strip : ∀ point ∈ richF,
    let baseHeight := wz1Lemma23SnappedBaseHeight prep.graphScale
      sharp.sharp.baseHeightIndex
    let cell := (pathFor point).2.1
    let centeredHeight :=
      (wz1Lemma23SnappedPoint prep.graphScale cell) 2 - baseHeight
    |direction 0 * centeredHeight +
      direction 1 *
        wz1Lemma23CenteredSlope baseHeight
          prep.windowed.global.extendedSlope centeredHeight| ≤
      prep.graphScale / Real.sqrt 3

theorem PureWZ2HorizontalFixedLineReadyGraph.alternativeAHeights
    {sigma inputLoss delta rho middleLoss outputLoss eta theoremEta epsilon : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading : PureWZ2HorizontalFixedLineResidueShadingData residue}
    {prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading}
    {graphParents : PureWZ2HorizontalFixedLineGraphParentData prep}
    {sources : PureWZ2HorizontalFixedLineResidueSourceFamily residueShading}
    {fullGrains : PureWZ2HorizontalFixedLineResidueFullGrainFamily
      (eta := eta) sources prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2HorizontalFixedLineSharpGeometry graph}
    (ready : PureWZ2HorizontalFixedLineReadyGraph
      (eta := eta) (theoremEta := theoremEta)
      (graphParents := graphParents) (sources := sources)
      (fullGrains := fullGrains) sharp)
    (hA : WZ1Proposition8_9AlternativeAUnion
      ready.ready.deltaGraph epsilon
      ready.common.F ready.common.G₁ ready.common.G₁) :
    Nonempty (PureWZ2HorizontalAlternativeAHeightData ready epsilon) := by
  rcases hA with ⟨_base, direction, hdirection, hF, _hG⟩
  let richF := ready.common.F.filter fun point =>
    point ∈ wz1LineNeighborhood 0 (wz1Perp2 direction)
      ready.ready.deltaGraph
  have hrichCard :
      Kakeya.realRpowENN ready.ready.deltaGraph (epsilon - 1) ≤
        (richF.card : ENNReal) := by
    simpa [richF, wz1DiscreteLineCount] using hF
  have hthresholdPos :
      0 < Kakeya.realRpowENN ready.ready.deltaGraph (epsilon - 1) :=
    ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos ready.ready.deltaGraph_pos _)
  have hrichNonempty : richF.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast hthresholdPos.trans_le hrichCard
  have hpathExists : ∀ point (hpoint : point ∈ richF),
      ∃ path ∈ sharp.sharp.actual.cycles,
        point = wz1Lemma23UnitBallPoint
          ((1 / Real.sqrt prep.graphScale) •
            wz1Lemma23SnappedHeightPoint prep.graphScale
              prep.windowed.global.extendedSlope
              sharp.sharp.baseHeightIndex path.2.1) := by
    intro point hpoint
    have hcommon : point ∈ ready.common.F :=
      (Finset.mem_filter.mp hpoint).1
    rw [ready.common.F_eq] at hcommon
    rcases Finset.mem_image.mp hcommon with
      ⟨normalizedPoint, hnormalizedPoint, hpointEq⟩
    rw [sharp.sharp.normalized.F_eq,
      sharp.sharp.normalized_sourceF, sharp.sharp.actual.F_eq] at hnormalizedPoint
    rcases Finset.mem_image.mp hnormalizedPoint with
      ⟨sourcePoint, hsourcePoint, hnormalizedEq⟩
    rcases Finset.mem_image.mp hsourcePoint with ⟨path, hpath, hsourceEq⟩
    refine ⟨path, hpath, ?_⟩
    rw [← hpointEq, ← hnormalizedEq, ← hsourceEq]
  let pathFor : Point2 →
      ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)) := fun point =>
    if hpoint : point ∈ richF then
      Classical.choose (hpathExists point hpoint)
    else ((0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0))
  have hpathMem : ∀ point (hpoint : point ∈ richF),
      pathFor point ∈ sharp.sharp.actual.cycles := by
    intro point hpoint
    simp only [pathFor, dif_pos hpoint]
    exact (Classical.choose_spec (hpathExists point hpoint)).1
  have hpointEq : ∀ point (hpoint : point ∈ richF),
      point = wz1Lemma23UnitBallPoint
        ((1 / Real.sqrt prep.graphScale) •
          wz1Lemma23SnappedHeightPoint prep.graphScale
            prep.windowed.global.extendedSlope
            sharp.sharp.baseHeightIndex (pathFor point).2.1) := by
    intro point hpoint
    simp only [pathFor, dif_pos hpoint]
    exact (Classical.choose_spec (hpathExists point hpoint)).2
  have hcellMem : ∀ point (hpoint : point ∈ richF),
      (pathFor point).2.1 ∈ graph.residue.cells := by
    intro point hpoint
    have hpath := hpathMem point hpoint
    rw [sharp.sharp.actual.cycles_eq] at hpath
    have hfour := (Finset.mem_filter.mp hpath).1
    have hrelations :
        ((pathFor point).1 ∈ graph.residue.cells ∧
          (pathFor point).2.1 ∈ graph.residue.cells ∧
          (pathFor point).2.2.1 ∈ graph.residue.cells ∧
          (pathFor point).2.2.2 ∈ graph.residue.cells) := by
      have h := (Finset.mem_filter.mp hfour).1
      simpa [wz1Lemma23FourCycles, Finset.mem_product] using h
    exact hrelations.2.1
  have hcenteredStrip : ∀ point (hpoint : point ∈ richF),
      let baseHeight := wz1Lemma23SnappedBaseHeight prep.graphScale
        sharp.sharp.baseHeightIndex
      let cell := (pathFor point).2.1
      let centeredHeight :=
        (wz1Lemma23SnappedPoint prep.graphScale cell) 2 - baseHeight
      |direction 0 * centeredHeight +
        direction 1 *
          wz1Lemma23CenteredSlope baseHeight
            prep.windowed.global.extendedSlope centeredHeight| ≤
        prep.graphScale / Real.sqrt 3 := by
    intro point hpoint
    have hline := (Finset.mem_filter.mp hpoint).2
    rw [wz1LineNeighborhood] at hline
    have hpointFormula := hpointEq point hpoint
    rw [hpointFormula] at hline
    have hperp : wz1Perp2 (wz1Perp2 direction) = -direction := by
      ext i
      fin_cases i <;> simp [wz1Perp2, EuclideanSpace.single]
    rw [hperp] at hline
    have hsqrt : 0 < Real.sqrt prep.graphScale :=
      Real.sqrt_pos.mpr prep.graphScale_pos
    change
      |inner ℝ
          (wz1Lemma23UnitBallPoint
            ((1 / Real.sqrt prep.graphScale) •
              wz1Lemma23SnappedHeightPoint prep.graphScale
                prep.windowed.global.extendedSlope
                sharp.sharp.baseHeightIndex (pathFor point).2.1) - 0)
          (-direction)| ≤ ready.ready.deltaGraph at hline
    simp only [sub_zero, inner_neg_right, abs_neg] at hline
    have hscaled :
        |inner ℝ
            (wz1Lemma23SnappedHeightPoint prep.graphScale
              prep.windowed.global.extendedSlope
              sharp.sharp.baseHeightIndex (pathFor point).2.1) direction| ≤
          5 * Real.sqrt prep.graphScale * ready.ready.deltaGraph := by
      have hformula :
          inner ℝ
              (wz1Lemma23UnitBallPoint
                ((1 / Real.sqrt prep.graphScale) •
                  wz1Lemma23SnappedHeightPoint prep.graphScale
                    prep.windowed.global.extendedSlope
                    sharp.sharp.baseHeightIndex (pathFor point).2.1)) direction =
            (1 / (5 * Real.sqrt prep.graphScale)) *
              inner ℝ
                (wz1Lemma23SnappedHeightPoint prep.graphScale
                  prep.windowed.global.extendedSlope
                  sharp.sharp.baseHeightIndex (pathFor point).2.1) direction := by
        simp [wz1Lemma23UnitBallPoint, inner_smul_left]
        ring
      rw [hformula] at hline
      rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (5 * Real.sqrt prep.graphScale))] at hline
      have hpos : 0 < 5 * Real.sqrt prep.graphScale := by positivity
      have hdiv :
          |inner ℝ
              (wz1Lemma23SnappedHeightPoint prep.graphScale
                prep.windowed.global.extendedSlope
                sharp.sharp.baseHeightIndex (pathFor point).2.1) direction| /
              (5 * Real.sqrt prep.graphScale) ≤ ready.ready.deltaGraph := by
        simpa [div_eq_mul_inv, mul_comm] using hline
      have hmul := (div_le_iff₀ hpos).mp hdiv
      simpa [mul_comm] using hmul
    rw [ready.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale] at hscaled
    have hscale :
        5 * Real.sqrt prep.graphScale *
            (Real.sqrt prep.graphScale / (5 * Real.sqrt 3)) =
          prep.graphScale / Real.sqrt 3 := by
      field_simp [hsqrt.ne']
      nlinarith [Real.sq_sqrt prep.graphScale_pos.le]
    rw [hscale] at hscaled
    simpa [wz1Lemma23SnappedHeightPoint, wz1Lemma23HeightGraphPoint,
      PiLp.inner_apply, Fin.sum_univ_succ, EuclideanSpace.single, point3]
      using hscaled
  let heightIndex : Point2 → ℤ := fun point => (pathFor point).2.1.2.2
  have hheightInjective : Set.InjOn heightIndex richF := by
    intro first hfirst second hsecond heq
    have hheight :
        (wz1Lemma23SnappedPoint prep.graphScale (pathFor first).2.1) 2 =
          (wz1Lemma23SnappedPoint prep.graphScale (pathFor second).2.1) 2 := by
      have hcast :
          ((pathFor first).2.1.2.2 : ℝ) =
            ((pathFor second).2.1.2.2 : ℝ) := by exact_mod_cast heq
      simp [wz1Lemma23SnappedPoint, wz1Lemma23CellCenter,
        point3, hcast]
    have hsourcePoint :
        wz1Lemma23SnappedHeightPoint prep.graphScale
            prep.windowed.global.extendedSlope sharp.sharp.baseHeightIndex
            (pathFor first).2.1 =
          wz1Lemma23SnappedHeightPoint prep.graphScale
            prep.windowed.global.extendedSlope sharp.sharp.baseHeightIndex
            (pathFor second).2.1 := by
      simp [wz1Lemma23SnappedHeightPoint, wz1Lemma23HeightGraphPoint, hheight]
    rw [hpointEq first hfirst, hpointEq second hsecond, hsourcePoint]
  let heightIndices := richF.image heightIndex
  have hheightCard : heightIndices.card = richF.card :=
    Finset.card_image_of_injOn hheightInjective
  exact ⟨{
    direction := direction
    direction_unit := hdirection
    richF := richF
    richF_eq := rfl
    richF_nonempty := hrichNonempty
    richF_card := hrichCard
    pathFor := pathFor
    path_mem := hpathMem
    point_eq := hpointEq
    cell_mem := hcellMem
    heightIndex := heightIndex
    heightIndex_eq := by intro point hpoint; rfl
    heightIndex_injective := hheightInjective
    heightIndices := heightIndices
    heightIndices_eq := rfl
    heightIndices_card := hheightCard
    centered_strip := hcenteredStrip
  }⟩

end Kakeya.Assouad
