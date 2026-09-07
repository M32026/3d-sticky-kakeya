import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularRefinedReadyGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.LocallyLinearOneScale.AlternativeAToTrapezoids

/-!
# Alternative-A rich heights on the terminal outer-popular graph

Every selected planar point is pulled back through both common homotheties to
an actual four-cycle of the volume-popular graph.  Thus its recorded height is
a height of the same residue built from the current outer-popular shadow.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalPopularAlternativeAHeightData
    {sigma inputLoss delta stickyLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line}
    {selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents}
    {selectedCarrier :
      PureWZ2TerminalPopularSelectedParentCarrierData selection}
    {sources : PureWZ2TerminalPopularCoarseSourceFamily selection}
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    {prep : PureWZ2TerminalPopularGraphPreparation localized}
    {graphParents : PureWZ2TerminalPopularGraphParentData prep}
    {localCells : PureWZ2TerminalPopularLocalCellData
      (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells}
    {sharp : PureWZ2TerminalPopularSharpGeometry preparedGraph}
    {first : PureWZ2TerminalPopularReadyGraph
      (theoremEta := theoremEta) sharp}
    (ready : PureWZ2CommonRefinedReadyGraph
      delta theoremEta first.common first.ready)
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
  path_mem : ∀ point ∈ richF,
    pathFor point ∈ sharp.sharp.actual.cycles
  point_eq : ∀ point ∈ richF,
    point = wz1Lemma23UnitBallPoint
      (wz1Lemma23UnitBallPoint
        ((1 / Real.sqrt delta) •
          wz1Lemma23SnappedHeightPoint delta
            prep.windowed.global.extendedSlope
            sharp.sharp.baseHeightIndex (pathFor point).2.1))
  cell_mem : ∀ point ∈ richF,
    (pathFor point).2.1 ∈ preparedGraph.graph.residue.cells
  heightIndex : Point2 → ℤ
  heightIndex_eq : ∀ point ∈ richF,
    heightIndex point = (pathFor point).2.1.2.2
  heightIndex_injective : Set.InjOn heightIndex richF
  heightIndices : Finset ℤ := richF.image heightIndex
  heightIndices_eq : heightIndices = richF.image heightIndex
  heightIndices_card : heightIndices.card = richF.card
  centered_strip : ∀ point ∈ richF,
    let baseHeight := wz1Lemma23SnappedBaseHeight delta
      sharp.sharp.baseHeightIndex
    let cell := (pathFor point).2.1
    let centeredHeight :=
      (wz1Lemma23SnappedPoint delta cell) 2 - baseHeight
    |direction 0 * centeredHeight +
      direction 1 *
        wz1Lemma23CenteredSlope baseHeight
          prep.windowed.global.extendedSlope centeredHeight| ≤
      delta / (5 * Real.sqrt 3)

theorem PureWZ2CommonRefinedReadyGraph.alternativeAHeights
    {sigma inputLoss delta stickyLoss eta theoremEta epsilon : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line}
    {selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents}
    {selectedCarrier :
      PureWZ2TerminalPopularSelectedParentCarrierData selection}
    {sources : PureWZ2TerminalPopularCoarseSourceFamily selection}
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    {prep : PureWZ2TerminalPopularGraphPreparation localized}
    {graphParents : PureWZ2TerminalPopularGraphParentData prep}
    {localCells : PureWZ2TerminalPopularLocalCellData
      (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells}
    {sharp : PureWZ2TerminalPopularSharpGeometry preparedGraph}
    {first : PureWZ2TerminalPopularReadyGraph
      (theoremEta := theoremEta) sharp}
    (ready : PureWZ2CommonRefinedReadyGraph
      delta theoremEta first.common first.ready)
    (hA : WZ1Proposition8_9AlternativeAUnion
      ready.ready.deltaGraph epsilon
      ready.common.F ready.common.G₁ ready.common.G₁) :
    Nonempty (PureWZ2TerminalPopularAlternativeAHeightData ready epsilon) := by
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
          (wz1Lemma23UnitBallPoint
            ((1 / Real.sqrt delta) •
              wz1Lemma23SnappedHeightPoint delta
                prep.windowed.global.extendedSlope
                sharp.sharp.baseHeightIndex path.2.1)) := by
    intro point hpoint
    have hcommon : point ∈ ready.common.F :=
      (Finset.mem_filter.mp hpoint).1
    rw [ready.common.F_eq] at hcommon
    rcases Finset.mem_image.mp hcommon with
      ⟨firstPoint, hfirstPoint, hpointEq⟩
    rw [first.common.F_eq] at hfirstPoint
    rcases Finset.mem_image.mp hfirstPoint with
      ⟨normalizedPoint, hnormalizedPoint, hfirstEq⟩
    rw [sharp.sharp.normalized.F_eq, sharp.sharp.normalized_sourceF,
      sharp.sharp.actual.F_eq] at hnormalizedPoint
    rcases Finset.mem_image.mp hnormalizedPoint with
      ⟨sourcePoint, hsourcePoint, hnormalizedEq⟩
    rcases Finset.mem_image.mp hsourcePoint with
      ⟨path, hpath, hsourceEq⟩
    refine ⟨path, hpath, ?_⟩
    rw [← hpointEq, ← hfirstEq, ← hnormalizedEq, ← hsourceEq]
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
        (wz1Lemma23UnitBallPoint
          ((1 / Real.sqrt delta) •
            wz1Lemma23SnappedHeightPoint delta
              prep.windowed.global.extendedSlope
              sharp.sharp.baseHeightIndex (pathFor point).2.1)) := by
    intro point hpoint
    simp only [pathFor, dif_pos hpoint]
    exact (Classical.choose_spec (hpathExists point hpoint)).2
  have hcellMem : ∀ point (hpoint : point ∈ richF),
      (pathFor point).2.1 ∈ preparedGraph.graph.residue.cells := by
    intro point hpoint
    have hpath := hpathMem point hpoint
    rw [sharp.sharp.actual.cycles_eq] at hpath
    have hfour := (Finset.mem_filter.mp hpath).1
    have hrelations :
        ((pathFor point).1 ∈ preparedGraph.graph.residue.cells ∧
          (pathFor point).2.1 ∈ preparedGraph.graph.residue.cells ∧
          (pathFor point).2.2.1 ∈ preparedGraph.graph.residue.cells ∧
          (pathFor point).2.2.2 ∈ preparedGraph.graph.residue.cells) := by
      have h := (Finset.mem_filter.mp hfour).1
      simpa [wz1Lemma23FourCycles, Finset.mem_product] using h
    exact hrelations.2.1
  have hcenteredStrip : ∀ point (hpoint : point ∈ richF),
      let baseHeight := wz1Lemma23SnappedBaseHeight delta
        sharp.sharp.baseHeightIndex
      let cell := (pathFor point).2.1
      let centeredHeight :=
        (wz1Lemma23SnappedPoint delta cell) 2 - baseHeight
      |direction 0 * centeredHeight +
        direction 1 *
          wz1Lemma23CenteredSlope baseHeight
            prep.windowed.global.extendedSlope centeredHeight| ≤
        delta / (5 * Real.sqrt 3) := by
    intro point hpoint
    have hline := (Finset.mem_filter.mp hpoint).2
    rw [wz1LineNeighborhood] at hline
    rw [hpointEq point hpoint] at hline
    have hperp : wz1Perp2 (wz1Perp2 direction) = -direction := by
      ext coordinate
      fin_cases coordinate <;> simp [wz1Perp2, EuclideanSpace.single]
    rw [hperp] at hline
    have hsqrt : 0 < Real.sqrt delta :=
      Real.sqrt_pos.mpr source.extremal.delta_pos
    change
      |inner ℝ
          (wz1Lemma23UnitBallPoint
            (wz1Lemma23UnitBallPoint
              ((1 / Real.sqrt delta) •
                wz1Lemma23SnappedHeightPoint delta
                  prep.windowed.global.extendedSlope
                  sharp.sharp.baseHeightIndex (pathFor point).2.1)) - 0)
          (-direction)| ≤ ready.ready.deltaGraph at hline
    simp only [sub_zero, inner_neg_right, abs_neg] at hline
    have hscaled :
        |inner ℝ
            (wz1Lemma23SnappedHeightPoint delta
              prep.windowed.global.extendedSlope
              sharp.sharp.baseHeightIndex (pathFor point).2.1) direction| ≤
          25 * Real.sqrt delta * ready.ready.deltaGraph := by
      have hformula :
          inner ℝ
              (wz1Lemma23UnitBallPoint
                (wz1Lemma23UnitBallPoint
                  ((1 / Real.sqrt delta) •
                    wz1Lemma23SnappedHeightPoint delta
                      prep.windowed.global.extendedSlope
                      sharp.sharp.baseHeightIndex (pathFor point).2.1)))
              direction =
            (1 / (25 * Real.sqrt delta)) *
              inner ℝ
                (wz1Lemma23SnappedHeightPoint delta
                  prep.windowed.global.extendedSlope
                  sharp.sharp.baseHeightIndex (pathFor point).2.1)
                direction := by
        simp [wz1Lemma23UnitBallPoint, inner_smul_left]
        ring
      rw [hformula, abs_mul,
        abs_of_pos (by positivity : 0 < 1 / (25 * Real.sqrt delta))]
        at hline
      have hpos : 0 < 25 * Real.sqrt delta := by positivity
      have hdiv :
          |inner ℝ
              (wz1Lemma23SnappedHeightPoint delta
                prep.windowed.global.extendedSlope
                sharp.sharp.baseHeightIndex (pathFor point).2.1) direction| /
              (25 * Real.sqrt delta) ≤ ready.ready.deltaGraph := by
        simpa [div_eq_mul_inv, mul_comm] using hline
      have hmul := (div_le_iff₀ hpos).mp hdiv
      simpa [mul_comm] using hmul
    rw [ready.deltaGraph_eq, first.ready.deltaGraph_eq,
      wz1Lemma23Theorem22Scale] at hscaled
    have hscale :
        25 * Real.sqrt delta *
            ((Real.sqrt delta / (5 * Real.sqrt 3)) / 25) =
          delta / (5 * Real.sqrt 3) := by
      field_simp [hsqrt.ne', show Real.sqrt (3 : ℝ) ≠ 0 by positivity]
      nlinarith [Real.sq_sqrt source.extremal.delta_pos.le]
    rw [hscale] at hscaled
    simpa [wz1Lemma23SnappedHeightPoint, wz1Lemma23HeightGraphPoint,
      PiLp.inner_apply, Fin.sum_univ_succ, EuclideanSpace.single, point3]
      using hscaled
  let heightIndex : Point2 → ℤ := fun point => (pathFor point).2.1.2.2
  have hheightInjective : Set.InjOn heightIndex richF := by
    intro firstPoint hfirst secondPoint hsecond heq
    have hheight :
        (wz1Lemma23SnappedPoint delta (pathFor firstPoint).2.1) 2 =
          (wz1Lemma23SnappedPoint delta (pathFor secondPoint).2.1) 2 := by
      have hcast :
          ((pathFor firstPoint).2.1.2.2 : ℝ) =
            ((pathFor secondPoint).2.1.2.2 : ℝ) := by exact_mod_cast heq
      simp [wz1Lemma23SnappedPoint, wz1Lemma23CellCenter, point3, hcast]
    have hsourcePoint :
        wz1Lemma23SnappedHeightPoint delta
            prep.windowed.global.extendedSlope sharp.sharp.baseHeightIndex
            (pathFor firstPoint).2.1 =
          wz1Lemma23SnappedHeightPoint delta
            prep.windowed.global.extendedSlope sharp.sharp.baseHeightIndex
            (pathFor secondPoint).2.1 := by
      simp [wz1Lemma23SnappedHeightPoint, wz1Lemma23HeightGraphPoint, hheight]
    rw [hpointEq firstPoint hfirst, hpointEq secondPoint hsecond, hsourcePoint]
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
    centered_strip := hcenteredStrip }⟩

end Kakeya.Assouad
