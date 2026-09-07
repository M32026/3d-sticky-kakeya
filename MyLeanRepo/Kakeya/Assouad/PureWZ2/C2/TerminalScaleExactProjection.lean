import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactReadyGraph
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalProjectionSchedule

/-!
# Dot-difference AD and normalized-B exclusion at the terminal scale
-/

noncomputable section

namespace Kakeya.Assouad

theorem PureWZ2TerminalExactReadyGraph.dot_difference_ad
    {sigma inputLoss delta stickyLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    {residue : PureWZ2TerminalBinParentYResidueData selection}
    {retained : PureWZ2TerminalBinRetainedShadingData residue}
    {sources : PureWZ2TerminalBinSourceFamily retained}
    {band : PureWZ2TerminalBinFixedBandSelection sources}
    {phase : PureWZ2TerminalBinHeightPhaseSelection band}
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    {graphParents : PureWZ2TerminalExactGraphParentData prep}
    {localCells : PureWZ2TerminalExactLocalCellData (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
    (data : PureWZ2TerminalExactReadyGraph (theoremEta := theoremEta) sharp)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    IsADSet1 (wz1DotDifferenceSet data.common.H)
      (Real.sqrt delta / (25 * Real.sqrt 3)) (1 - sigma)
      ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
        (10 * Kakeya.realRpowENN delta (-inputLoss))) := by
  let graph := preparedGraph.graph
  let C : ENNReal := 10 * Kakeya.realRpowENN delta (-inputLoss)
  let z := prep.windowed.global.selectedHeight sharp.sharp.baseHeightIndex
  let E : Set ℝ := scalarProjection
    (globalGrainDirection (prep.windowed.global.sourceSlope z))
    (horizontalSlice prep.shadow.union z)
  let untranslated : Finset ℝ :=
    (graph.residue.cells.filter fun idx =>
      wz1Lemma23SnappedHeight idx = sharp.sharp.baseHeightIndex).image
      fun idx => wz1Lemma23GlobalCoordinate prep.windowed.global.extendedSlope
        (wz1Lemma23SnappedPoint delta idx)
  let shift : ℝ := (sharp.sharp.baseGlobalBin : ℝ) * delta
  let baseValues := wz1Lemma23SnappedBaseSliceValues delta
    prep.windowed.global.extendedSlope graph.residue.cells
    sharp.sharp.baseHeightIndex sharp.sharp.baseGlobalBin
  have hcoord : ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hpaper : point ∈ retained.shading.union := by
      have hambient := prep.subshading.union_subset hpoint
      rwa [prep.ambient_union] at hambient
    have hbox := shading_union_subset_axisBox hpaper
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hheight := data.base_height_mem
  have hz : z ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases Finset.mem_image.mp hheight with ⟨idx, hidx, hidxHeight⟩
    have hidxGlobal := graph.residue.cells_subset hidx
    rw [prep.windowed.global.cells_eq] at hidxGlobal
    rcases Finset.mem_biUnion.mp hidxGlobal with
      ⟨height, hheightMem, hidxLayer⟩
    have hheightEq : height = sharp.sharp.baseHeightIndex := by
      have h := prep.windowed.global.layer_height height hheightMem idx hidxLayer
      simpa [wz1Lemma23SnappedHeight] using h.symm.trans hidxHeight
    have hidxLayerBase :
        idx ∈ prep.windowed.global.layerCells sharp.sharp.baseHeightIndex := by
      rwa [hheightEq] at hidxLayer
    let cell : WZ1Lemma23ExactSliceCell prep.shadow delta
        source.extremal.delta_pos z :=
      ⟨idx, by
        rw [prep.windowed.global.layerCells_eq] at hidxLayerBase
        exact hidxLayerBase⟩
    let point := wz1Lemma23LiftSlicePoint z
      (wz1Lemma23ExactSliceRepresentative prep.shadow
        source.extremal.delta_pos z cell)
    have hpoint : point ∈ prep.shadow.union :=
      wz1Lemma23ExactSliceRepresentative_mem_union
        prep.shadow source.extremal.delta_pos z cell
    have hpointHeight : point (2 : Fin 3) = z := by
      simp [point, wz1Lemma23LiftSlicePoint, point3]
    have habs : |z| ≤ 1 := by
      rw [← hpointHeight]
      exact hcoord point hpoint 2
    exact abs_le.mp habs
  have hAD : IsADSet1 E delta (1 - sigma) C := by
    dsimp only [E, z, C]
    exact prep.exactAD _ hz
  have huntranslated :
      (untranslated : Set ℝ) ⊆ Metric.cthickening (4 * delta) E := by
    simpa [untranslated, E, z] using
      base_slice_values_containment_of_coord prep.windowed.global
        graph.residue.cells graph.residue.cells_subset
        sharp.sharp.baseHeightIndex hcoord source.extremal.delta_pos
        source.extremal.delta_le_one hheight
  have hbaseValuesEq :
      (baseValues : Set ℝ) = (fun value : ℝ => value - shift) '' untranslated := by
    ext value
    simp [baseValues, untranslated, shift, wz1Lemma23SnappedBaseSliceValues]
  have htranslated : (baseValues : Set ℝ) ⊆
      Metric.cthickening (4 * delta)
        ((fun value : ℝ => value - shift) '' E) := by
    rw [hbaseValuesEq]
    intro value hvalue
    rcases hvalue with ⟨sourceValue, hsourceValue, rfl⟩
    have hnear := huntranslated hsourceValue
    rw [Metric.mem_cthickening_iff] at hnear ⊢
    have heq : Metric.infEDist (sourceValue - shift)
          ((fun value : ℝ => value - shift) '' E) =
        Metric.infEDist sourceValue E := by
      simpa [sub_eq_add_neg] using
        (Metric.infEDist_image (isometry_add_right (-shift))
          (x := sourceValue) (t := E))
    rw [heq]
    exact hnear
  have hnormalizedValues : (sharp.sharp.normalized.values : Set ℝ) =
      (fun value : ℝ => value / Real.sqrt delta) ''
        (baseValues : Set ℝ) := by
    rw [sharp.sharp.normalized.values_eq, sharp.sharp.normalized_sourceValues]
    ext value
    simp [baseValues, graph, wz1Lemma23NormalizedBaseValues]
  have hnormalizedDot := sharp.sharp.normalized.dot_containment
  have hunitDot : wz1DotDifferenceSet data.common.H =
      (fun value : ℝ => value / 25) ''
        wz1DotDifferenceSet sharp.sharp.normalized.H := by
    rw [data.common.dot_image]
  have hunitBound : wz1DotDifferenceSet data.common.H ⊆
      Set.Icc (-2 : ℝ) 2 := by
    intro value hvalue
    rw [data.common.dot_image] at hvalue
    rcases hvalue with ⟨sourceValue, hsourceValue, rfl⟩
    change sourceValue ∈ sharp.sharp.normalized.H.image
      (fun edge => inner ℝ edge.1 (edge.2.1 - edge.2.2)) at hsourceValue
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hsourceValue) with
      ⟨edge, hedge, rfl⟩
    have hs := sharp.sharp.normalized.edge_support edge hedge
    have hfirst := sharp.geometry.vertex_bounds.1 edge.1 hs.1
    have hsecond := sharp.geometry.vertex_bounds.2.1 edge.2.1 hs.2.1
    have hthird := sharp.geometry.vertex_bounds.2.2 edge.2.2 hs.2.2
    rw [dist_zero_right] at hfirst hsecond hthird
    have hdot : |inner ℝ edge.1 (edge.2.1 - edge.2.2)| ≤ 20 := by
      calc
        _ ≤ ‖edge.1‖ * ‖edge.2.1 - edge.2.2‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ 2 * (‖edge.2.1‖ + ‖edge.2.2‖) := by
          gcongr
          exact norm_sub_le _ _
        _ ≤ 2 * (5 + 5) := by gcongr
        _ = 20 := by norm_num
    change inner ℝ edge.1 (edge.2.1 - edge.2.2) / 25 ∈ Set.Icc (-2 : ℝ) 2
    have hdotBounds := abs_le.mp hdot
    constructor <;> linarith
  simpa [C] using dot_difference_AD_transfer_shifted
    source.extremal.delta_pos source.extremal.delta_le_one hsigma hsigmaOne
    (by
      dsimp only [C]
      exact ENNReal.mul_ne_top (by norm_num)
        (by simp [Kakeya.realRpowENN]))
    hAD htranslated hnormalizedValues hnormalizedDot hunitDot hunitBound

theorem PureWZ2TerminalExactReadyGraph.projection_alternative_a_strong
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    {residue : PureWZ2TerminalBinParentYResidueData selection}
    {retained : PureWZ2TerminalBinRetainedShadingData residue}
    {sources : PureWZ2TerminalBinSourceFamily retained}
    {band : PureWZ2TerminalBinFixedBandSelection sources}
    {phase : PureWZ2TerminalBinHeightPhaseSelection band}
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    {graphParents : PureWZ2TerminalExactGraphParentData prep}
    {localCells : PureWZ2TerminalExactLocalCellData (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
    (data : PureWZ2TerminalExactReadyGraph (theoremEta := theoremEta) sharp)
    (hepsilon : 0 < outputLoss) (hepsilonOne : outputLoss < 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilonSigma : outputLoss / 2 < sigma)
    {budgetFactor projectionEta reductionDelta₀ sourceCostLoss : ℝ}
    (hreduction :
      ∀ {rho' : ℝ} {sourceF' sourceG₁' sourceG₂' : DiscreteSet 2}
        {sourceH' : Finset (Point2 × Point2 × Point2)}
        {unitBall' : WZ1Lemma23UnitBallGraph
          rho' sourceF' sourceG₁' sourceG₂' sourceH'}
        (ready' : WZ1Lemma23Theorem22ReadyGraph rho' theoremEta unitBall'),
        ready'.deltaGraph ≤ reductionDelta₀ →
        unitBall'.G₂ = unitBall'.G₁ →
          WZ1Proposition8_9AlternativeAUnion ready'.deltaGraph outputLoss
              unitBall'.F unitBall'.G₁ unitBall'.G₁ ∨
            Nonempty (PureWZ2CommonEndpointProjectionLongData
              (epsilon := outputLoss) ready' budgetFactor projectionEta))
    (hdeltaSmall : data.ready.deltaGraph ≤ reductionDelta₀)
    (htheoremEta : 0 ≤ theoremEta)
    (htheoremEtaSmall : theoremEta ≤ 1 / 100)
    (hsourceCost : Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN data.ready.deltaGraph (-sourceCostLoss))
    (hsourceCostLoss : 0 ≤ sourceCostLoss)
    (hgain : 10 * theoremEta + sourceCostLoss <
      projectionEta * (sigma - outputLoss / 2))
    (hconstantSmall :
      (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN data.ready.deltaGraph
          (-(projectionEta * (sigma - outputLoss / 2) -
            (10 * theoremEta + sourceCostLoss)) / 2)) :
    WZ1Proposition8_9AlternativeAUnion data.ready.deltaGraph outputLoss
      data.common.F data.common.G₁ data.common.G₁ := by
  have hcommon : data.common.G₂ = data.common.G₁ := by
    rw [data.common.G₂_eq, data.common.G₁_eq]
  rcases hreduction data.ready hdeltaSmall hcommon with hA | hB
  · exact hA
  · rcases hB with ⟨strongLong⟩
    exfalso
    let C : ENNReal := (16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
      (10 * Kakeya.realRpowENN delta (-inputLoss))
    have hAD : IsADSet1 (wz1DotDifferenceSet data.common.H)
        (Real.sqrt delta / (25 * Real.sqrt 3))
        (1 - sigma) C := by
      simpa [C] using data.dot_difference_ad hsigma hsigmaOne
    have hCtop : C ≠ ⊤ := by
      dsimp only [C]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        (ENNReal.mul_ne_top (by norm_num)
          (by simp [Kakeya.realRpowENN]))
    have hdeltaAD : Real.sqrt delta / (25 * Real.sqrt 3) =
        data.ready.deltaGraph / 5 :=
      pureWZ2_sourceHorizontal_dotADScale_eq data.ready
    have hdeltaGraphOne : data.ready.deltaGraph ≤ 1 := by
      rw [data.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale]
      have hsqrt := Real.sqrt_le_one.mpr source.extremal.delta_le_one
      have hdenom : 1 ≤ 5 * Real.sqrt 3 := by
        have hsqrt3 : 1 ≤ Real.sqrt 3 := (Real.one_le_sqrt).2 (by norm_num)
        nlinarith
      exact (div_le_self (Real.sqrt_nonneg delta) hdenom).trans hsqrt
    have hdeltaGraphStrict : data.ready.deltaGraph < 1 := by
      have hsqrt3 : 1 ≤ Real.sqrt 3 := (Real.one_le_sqrt).2 (by norm_num)
      have hdenom : 1 < 5 * Real.sqrt 3 := by nlinarith
      rw [data.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale]
      have hsqrtPos : 0 < Real.sqrt delta :=
        Real.sqrt_pos.mpr source.extremal.delta_pos
      exact (div_lt_self hsqrtPos hdenom).trans_le
        (Real.sqrt_le_one.mpr source.extremal.delta_le_one)
    have hscaledOne : strongLong.long.affine.dotScale *
        (Real.sqrt delta / (25 * Real.sqrt 3)) ≤ 1 :=
      strongLong.scaled_dotAD_le_one hdeltaAD htheoremEta
        htheoremEtaSmall hdeltaGraphOne
    have hconstant := strongLong.constant_absorb hdeltaAD htheoremEta
      hdeltaGraphOne hsourceCost hsourceCostLoss hgain hdeltaGraphStrict
      hconstantSmall
    have htargetPos : 0 < data.ready.deltaGraph / 2 :=
      div_pos data.ready.deltaGraph_pos (by norm_num)
    have htargetOne : data.ready.deltaGraph / 2 ≤ 1 :=
      (div_le_self data.ready.deltaGraph_pos.le (by norm_num)).trans
        hdeltaGraphOne
    have htargetStrict : data.ready.deltaGraph / 2 < 1 := by
      calc
        data.ready.deltaGraph / 2 < data.ready.deltaGraph := by
          linarith [data.ready.deltaGraph_pos]
        _ < 1 := hdeltaGraphStrict
    exact strongLong.long.false_of_dot_ad hAD hCtop hsigma hsigmaOne
      (by positivity) hepsilonSigma hscaledOne htargetPos htargetOne
      htargetStrict hconstant

end Kakeya.Assouad
