import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularRichHeightVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalProjectionSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalExactProjectionSchedule
import MyLeanRepo.Kakeya.Assouad.WZ1.LocallyLinearOneScale.BaseSliceValuesAD
import MyLeanRepo.Kakeya.Assouad.WZ1.LocallyLinearOneScale.DotDifferenceAD324
import MyLeanRepo.Kakeya.Assouad.WZ1.VerticalRescalingADProof

/-!
# Projection reduction for the terminal outer-popular graph

The first dot-difference certificate is proved directly from the exact-slice
AD bound on the current graph shadow.  The second common homothety is handled
by a carrier-independent transport lemma.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

private theorem pureWZ2_terminalPopular_refined_graph_le_root
    {rho theoremEta : ℝ}
    {sourceF sourceG : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {first : WZ1Lemma23UnitBallGraph rho sourceF sourceG sourceG sourceH}
    {firstReady : WZ1Lemma23Theorem22ReadyGraph rho theoremEta first}
    (data : PureWZ2CommonRefinedReadyGraph
      rho theoremEta first firstReady)
    (hrho : 0 < rho) :
    data.ready.deltaGraph ≤ Real.sqrt rho := by
  rw [data.deltaGraph_eq, firstReady.deltaGraph_eq,
    wz1Lemma23Theorem22Scale]
  have hdenom : 1 ≤ 5 * Real.sqrt 3 := by
    have hsqrtThree : 1 ≤ Real.sqrt 3 :=
      (Real.one_le_sqrt).2 (by norm_num)
    nlinarith
  exact (div_le_self (by positivity : 0 ≤ Real.sqrt rho /
      (5 * Real.sqrt 3)) (by norm_num : 1 ≤ (25 : ℝ))).trans
    (div_le_self (Real.sqrt_nonneg rho) hdenom)

/-- The twice-normalized popular graph pays four copies of the source AD loss,
exactly as in the old terminal graph.  This lemma is carrier-independent. -/
theorem PureWZ2CommonRefinedReadyGraph.source_cost
    {rho theoremEta inputLoss : ℝ}
    {sourceF sourceG : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {first : WZ1Lemma23UnitBallGraph rho sourceF sourceG sourceG sourceH}
    {firstReady : WZ1Lemma23Theorem22ReadyGraph rho theoremEta first}
    (data : PureWZ2CommonRefinedReadyGraph
      rho theoremEta first firstReady)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hinputLoss : 0 ≤ inputLoss) :
    Kakeya.realRpowENN rho (-inputLoss) ≤
      Kakeya.realRpowENN data.ready.deltaGraph (-4 * inputLoss) := by
  apply ENNReal.ofReal_mono
  let root := Real.sqrt rho
  have hroot : 0 < root := Real.sqrt_pos.mpr hrho
  have hrootOne : root ≤ 1 := Real.sqrt_le_one.mpr hrhoOne
  have hgraph : 0 < data.ready.deltaGraph := data.ready.deltaGraph_pos
  have hgraphRoot : data.ready.deltaGraph ≤ root :=
    pureWZ2_terminalPopular_refined_graph_le_root data hrho
  have hrhoPower : Real.rpow rho (-inputLoss) =
      Real.rpow root (-2 * inputLoss) := by
    dsimp only [root]
    rw [Real.sqrt_eq_rpow]
    calc
      Real.rpow rho (-inputLoss) =
          Real.rpow rho ((1 / 2 : ℝ) * (-2 * inputLoss)) := by
        congr 1
        ring
      _ = (Real.rpow rho (1 / 2 : ℝ)).rpow (-2 * inputLoss) :=
        Real.rpow_mul hrho.le _ _
  rw [hrhoPower]
  calc
    Real.rpow root (-2 * inputLoss) ≤
        Real.rpow root (-4 * inputLoss) :=
      Real.rpow_le_rpow_of_exponent_ge hroot hrootOne (by linarith)
    _ ≤ Real.rpow data.ready.deltaGraph (-4 * inputLoss) :=
      Real.rpow_le_rpow_of_nonpos hgraph hgraphRoot (by linarith)

theorem PureWZ2TerminalPopularReadyGraph.dot_difference_ad
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
    (data : PureWZ2TerminalPopularReadyGraph
      (theoremEta := theoremEta) sharp)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    IsADSet1 (wz1DotDifferenceSet data.common.H)
      (Real.sqrt delta / (25 * Real.sqrt 3)) (1 - sigma)
      ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
        pureWZ2TerminalPopularGraphConstant delta inputLoss) := by
  let C := pureWZ2TerminalPopularGraphConstant delta inputLoss
  let graph := preparedGraph.graph
  let z := prep.windowed.global.selectedHeight sharp.sharp.baseHeightIndex
  let E : Set ℝ := scalarProjection
    (globalGrainDirection (prep.windowed.global.sourceSlope z))
    (horizontalSlice prep.shadow.union z)
  let untranslated : Finset ℝ :=
    (graph.residue.cells.filter fun idx =>
      wz1Lemma23SnappedHeight idx = sharp.sharp.baseHeightIndex).image
      fun idx => wz1Lemma23GlobalCoordinate
        prep.windowed.global.extendedSlope
        (wz1Lemma23SnappedPoint delta idx)
  let shift : ℝ := (sharp.sharp.baseGlobalBin : ℝ) * delta
  let baseValues := wz1Lemma23SnappedBaseSliceValues delta
    prep.windowed.global.extendedSlope graph.residue.cells
    sharp.sharp.baseHeightIndex sharp.sharp.baseGlobalBin
  have hcoord : ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hsource := prep.shadow_source hpoint
    have hbox := shading_union_subset_axisBox hsource
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
      have h := prep.windowed.global.layer_height
        height hheightMem idx hidxLayer
      simpa [wz1Lemma23SnappedHeight] using h.symm.trans hidxHeight
    have hidxLayerBase : idx ∈
        prep.windowed.global.layerCells sharp.sharp.baseHeightIndex := by
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
    rw [sharp.sharp.normalized.values_eq,
      sharp.sharp.normalized_sourceValues]
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
    change inner ℝ edge.1 (edge.2.1 - edge.2.2) / 25 ∈
      Set.Icc (-2 : ℝ) 2
    have hdotBounds := abs_le.mp hdot
    constructor <;> linarith
  simpa [C] using dot_difference_AD_transfer_shifted
    source.extremal.delta_pos source.extremal.delta_le_one hsigma hsigmaOne
    (by
      dsimp only [C, pureWZ2TerminalPopularGraphConstant]
      exact ENNReal.mul_ne_top (by norm_num)
        (by simp [Kakeya.realRpowENN]))
    hAD htranslated hnormalizedValues hnormalizedDot hunitDot hunitBound

theorem PureWZ2CommonRefinedReadyGraph.dot_difference_ad_of_first
    {rho theoremEta sigma : ℝ}
    {sourceF sourceG : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {first : WZ1Lemma23UnitBallGraph rho sourceF sourceG sourceG sourceH}
    {firstReady : WZ1Lemma23Theorem22ReadyGraph rho theoremEta first}
    (data : PureWZ2CommonRefinedReadyGraph
      rho theoremEta first firstReady)
    {C : ENNReal}
    (hrho : 0 < rho) (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hfirst : IsADSet1 (wz1DotDifferenceSet first.H)
      (Real.sqrt rho / (25 * Real.sqrt 3)) (1 - sigma) C) :
    IsADSet1 (wz1DotDifferenceSet data.common.H)
      (data.ready.deltaGraph / 5) (1 - sigma) (10 * C) := by
  have hADScalePos : 0 < Real.sqrt rho / (25 * Real.sqrt 3) := by
    exact div_pos (Real.sqrt_pos.mpr hrho) (by positivity)
  have himage := hfirst.image_div_sq
    (delta := Real.sqrt rho / (25 * Real.sqrt 3))
    (M := 5) (by norm_num) hADScalePos hsigma hsigmaOne
  have hscale :
      (Real.sqrt rho / (25 * Real.sqrt 3)) / 5 ^ 2 =
        data.ready.deltaGraph / 5 := by
    rw [data.deltaGraph_eq, firstReady.deltaGraph_eq,
      wz1Lemma23Theorem22Scale]
    ring
  have himageSet :
      (fun value : ℝ => value / (5 : ℝ) ^ 2) ''
          wz1DotDifferenceSet first.H =
        (fun value : ℝ => value / 25) ''
          wz1DotDifferenceSet first.H := by
    congr 1
    funext value
    norm_num
  rw [data.common.dot_image]
  rw [himageSet, hscale] at himage
  simpa using himage

theorem PureWZ2CommonRefinedReadyGraph.projection_alternative_a_of_dot_ad
    {rho theoremEta sigma epsilon budgetFactor projectionEta
      reductionDelta₀ : ℝ}
    {sourceF sourceG : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {first : WZ1Lemma23UnitBallGraph rho sourceF sourceG sourceG sourceH}
    {firstReady : WZ1Lemma23Theorem22ReadyGraph rho theoremEta first}
    (data : PureWZ2CommonRefinedReadyGraph
      rho theoremEta first firstReady)
    {C : ENNReal}
    (hAD : IsADSet1 (wz1DotDifferenceSet data.common.H)
      (data.ready.deltaGraph / 5) (1 - sigma) C)
    (hCtop : C ≠ ⊤)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon : 0 < epsilon)
    (hepsilonSigma : epsilon / 2 < sigma)
    (hreduction :
      ∀ {rho' : ℝ} {sourceF' sourceG₁' sourceG₂' : DiscreteSet 2}
        {sourceH' : Finset (Point2 × Point2 × Point2)}
        {unitBall' : WZ1Lemma23UnitBallGraph
          rho' sourceF' sourceG₁' sourceG₂' sourceH'}
        (ready' : WZ1Lemma23Theorem22ReadyGraph rho' theoremEta unitBall'),
        ready'.deltaGraph ≤ reductionDelta₀ →
        unitBall'.G₂ = unitBall'.G₁ →
          WZ1Proposition8_9AlternativeAUnion ready'.deltaGraph epsilon
              unitBall'.F unitBall'.G₁ unitBall'.G₁ ∨
            Nonempty (PureWZ2CommonEndpointProjectionLongData
              (epsilon := epsilon) ready' budgetFactor projectionEta))
    (hdeltaSmall : data.ready.deltaGraph ≤ reductionDelta₀)
    (htheoremEta : 0 ≤ theoremEta)
    (htheoremEtaSmall : theoremEta ≤ 1 / 100)
    (hconstant : ∀ strongLong : PureWZ2CommonEndpointProjectionLongData
        (epsilon := epsilon) data.ready budgetFactor projectionEta,
      ((5 * C) * ENNReal.ofReal
            (max 1 (10 * (strongLong.long.affine.dotScale *
              (data.ready.deltaGraph / 5)) /
                (data.ready.deltaGraph / 2)))) * 100 *
          Kakeya.realRpowENN (data.ready.deltaGraph / 2)
            (strongLong.long.projectionEta *
              (sigma - epsilon / 2)) < 1) :
    WZ1Proposition8_9AlternativeAUnion data.ready.deltaGraph epsilon
      data.common.F data.common.G₁ data.common.G₁ := by
  have hcommon : data.common.G₂ = data.common.G₁ := by
    rw [data.common.G₂_eq, data.common.G₁_eq]
  rcases hreduction data.ready hdeltaSmall hcommon with hA | hB
  · exact hA
  · rcases hB with ⟨strongLong⟩
    exfalso
    have hdeltaGraphOne : data.ready.deltaGraph ≤ 1 := by
      rw [data.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale]
      have hrefinedOne : rho / 625 ≤ 1 := by
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 625)).2
        nlinarith
      have hsqrt : Real.sqrt (rho / 625) ≤ 1 :=
        Real.sqrt_le_one.mpr hrefinedOne
      have hdenom : 1 ≤ 5 * Real.sqrt 3 := by
        have hsqrt3 : 1 ≤ Real.sqrt 3 :=
          (Real.one_le_sqrt).2 (by norm_num)
        nlinarith
      exact (div_le_self (Real.sqrt_nonneg _) hdenom).trans hsqrt
    have hscaledOne : strongLong.long.affine.dotScale *
        (data.ready.deltaGraph / 5) ≤ 1 :=
      strongLong.scaled_dotAD_le_one rfl htheoremEta
        htheoremEtaSmall hdeltaGraphOne
    have htargetPos : 0 < data.ready.deltaGraph / 2 :=
      div_pos data.ready.deltaGraph_pos (by norm_num)
    have htargetOne : data.ready.deltaGraph / 2 ≤ 1 :=
      (div_le_self data.ready.deltaGraph_pos.le (by norm_num)).trans
        hdeltaGraphOne
    have htargetStrict : data.ready.deltaGraph / 2 < 1 := by
      calc
        data.ready.deltaGraph / 2 < data.ready.deltaGraph := by
          linarith [data.ready.deltaGraph_pos]
        _ ≤ 1 := hdeltaGraphOne
    have hepsilonHalf : 0 < epsilon / 2 := by positivity
    exact strongLong.long.false_of_dot_ad hAD hCtop hsigma
      hsigmaOne hepsilonHalf hepsilonSigma hscaledOne
      htargetPos htargetOne htargetStrict (hconstant strongLong)

/-- Absorb the larger fixed AD constant carried by the terminal
outer-popular graph.  This is the same projection contradiction as the exact
terminal schedule, with `40000` in place of the old graph constant `10`. -/
theorem PureWZ2CommonEndpointProjectionLongData.constant_absorb_popular
    {rho theoremEta epsilon budgetFactor projectionEta
      sigma inputLoss sourceCostLoss delta : ℝ}
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {unitBall : WZ1Lemma23UnitBallGraph rho sourceF sourceG₁ sourceG₂ sourceH}
    {ready : WZ1Lemma23Theorem22ReadyGraph rho theoremEta unitBall}
    (data : PureWZ2CommonEndpointProjectionLongData
      (epsilon := epsilon) ready budgetFactor projectionEta)
    (htheoremEta : 0 ≤ theoremEta)
    (hdeltaGraphOne : ready.deltaGraph ≤ 1)
    (hsourceCost :
      Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN ready.deltaGraph (-sourceCostLoss))
    (hsourceCostLoss : 0 ≤ sourceCostLoss)
    (hgain : 10 * theoremEta + sourceCostLoss <
      projectionEta * (sigma - epsilon / 2))
    (hdeltaGraphStrict : ready.deltaGraph < 1)
    (hconstantSmall :
      (25920000000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN ready.deltaGraph
          (-(projectionEta * (sigma - epsilon / 2) -
            (10 * theoremEta + sourceCostLoss)) / 2)) :
    let C : ENNReal := 10 *
      ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
        pureWZ2TerminalPopularGraphConstant delta inputLoss)
    ((5 * C) * ENNReal.ofReal
          (max 1 (10 * (data.long.affine.dotScale *
            (ready.deltaGraph / 5)) / (ready.deltaGraph / 2)))) * 100 *
        Kakeya.realRpowENN (ready.deltaGraph / 2)
          (data.long.projectionEta * (sigma - epsilon / 2)) < 1 := by
  dsimp only
  have hmax := data.max_factor_bound rfl htheoremEta hdeltaGraphOne
  have hprojectionEq : data.long.projectionEta = projectionEta :=
    data.projectionEta_eq
  have hhalfPower :
      Kakeya.realRpowENN (ready.deltaGraph / 2)
          (data.long.projectionEta * (sigma - epsilon / 2)) ≤
        Kakeya.realRpowENN ready.deltaGraph
          (projectionEta * (sigma - epsilon / 2)) := by
    rw [hprojectionEq]
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow
    · exact (div_nonneg ready.deltaGraph_pos.le (by norm_num))
    · exact div_le_self ready.deltaGraph_pos.le (by norm_num)
    · have hprojection : 0 < projectionEta := by
        rw [← hprojectionEq]
        exact data.long.projectionEta_pos
      have hsigmaGap : 0 < sigma - epsilon / 2 := by
        by_contra hnot
        have hnonpos : projectionEta * (sigma - epsilon / 2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hprojection.le (le_of_not_gt hnot)
        have hleftNonneg : 0 ≤ 10 * theoremEta + sourceCostLoss := by
          positivity
        linarith
      positivity
  have hnegativeCombine :
      Kakeya.realRpowENN ready.deltaGraph (-sourceCostLoss) *
          Kakeya.realRpowENN ready.deltaGraph (-10 * theoremEta) =
        Kakeya.realRpowENN ready.deltaGraph
          (-(10 * theoremEta + sourceCostLoss)) := by
    rw [← realRpowENN_add ready.deltaGraph_pos]
    congr 1
    ring
  have htotalCombine :
      Kakeya.realRpowENN ready.deltaGraph
          (-(10 * theoremEta + sourceCostLoss)) *
        Kakeya.realRpowENN ready.deltaGraph
          (projectionEta * (sigma - epsilon / 2)) =
      Kakeya.realRpowENN ready.deltaGraph
        (projectionEta * (sigma - epsilon / 2) -
          (10 * theoremEta + sourceCostLoss)) := by
    rw [← realRpowENN_add ready.deltaGraph_pos]
    congr 1
    ring
  let gap := projectionEta * (sigma - epsilon / 2) -
    (10 * theoremEta + sourceCostLoss)
  have hgap : 0 < gap := by dsimp only [gap]; linarith
  have hpowerLt : Kakeya.realRpowENN ready.deltaGraph (gap / 2) < 1 := by
    have h := realRpowENN_strict_antitone
      ready.deltaGraph_pos hdeltaGraphStrict (by positivity : 0 < gap / 2)
    simpa [Kakeya.realRpowENN] using h
  have hscaled :
      (5 * (10 * ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
          pureWZ2TerminalPopularGraphConstant delta inputLoss)) *
          ENNReal.ofReal
            (max 1 (10 * (data.long.affine.dotScale *
              (ready.deltaGraph / 5)) / (ready.deltaGraph / 2)))) * 100 *
          Kakeya.realRpowENN (ready.deltaGraph / 2)
            (data.long.projectionEta * (sigma - epsilon / 2)) ≤
        (25920000000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
          Kakeya.realRpowENN ready.deltaGraph
            (-(10 * theoremEta + sourceCostLoss)) *
          Kakeya.realRpowENN ready.deltaGraph
            (projectionEta * (sigma - epsilon / 2)) := by
    calc
      _ ≤ (5 * (10 * ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
            (40000 * Kakeya.realRpowENN
              ready.deltaGraph (-sourceCostLoss))))) *
            (8 * Kakeya.realRpowENN ready.deltaGraph (-10 * theoremEta)) *
            100 * Kakeya.realRpowENN ready.deltaGraph
              (projectionEta * (sigma - epsilon / 2)) := by
        unfold pureWZ2TerminalPopularGraphConstant
        gcongr
      _ = (25920000000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
            Kakeya.realRpowENN ready.deltaGraph
              (-(10 * theoremEta + sourceCostLoss)) *
            Kakeya.realRpowENN ready.deltaGraph
              (projectionEta * (sigma - epsilon / 2)) := by
        calc
          _ = (25920000000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
              (Kakeya.realRpowENN ready.deltaGraph (-sourceCostLoss) *
                Kakeya.realRpowENN ready.deltaGraph (-10 * theoremEta)) *
              Kakeya.realRpowENN ready.deltaGraph
                (projectionEta * (sigma - epsilon / 2)) := by ring
          _ = _ := by rw [hnegativeCombine]
  have hupper :
      (25920000000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
          Kakeya.realRpowENN ready.deltaGraph
            (-(10 * theoremEta + sourceCostLoss)) *
          Kakeya.realRpowENN ready.deltaGraph
            (projectionEta * (sigma - epsilon / 2)) ≤
        Kakeya.realRpowENN ready.deltaGraph (gap / 2) := by
    calc
      _ = (25920000000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
          (Kakeya.realRpowENN ready.deltaGraph
              (-(10 * theoremEta + sourceCostLoss)) *
            Kakeya.realRpowENN ready.deltaGraph
              (projectionEta * (sigma - epsilon / 2))) := by ring
      _ = (25920000000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
          Kakeya.realRpowENN ready.deltaGraph gap := by
        rw [htotalCombine]
      _ ≤ Kakeya.realRpowENN ready.deltaGraph (-(gap / 2)) *
          Kakeya.realRpowENN ready.deltaGraph gap := by
        gcongr
        have hexponent :
            -(projectionEta * (sigma - epsilon / 2) -
                (10 * theoremEta + sourceCostLoss)) / 2 = -(gap / 2) := by
          dsimp only [gap]
          ring
        rwa [hexponent] at hconstantSmall
      _ = Kakeya.realRpowENN ready.deltaGraph (gap / 2) := by
        rw [← realRpowENN_add ready.deltaGraph_pos]
        congr 1
        ring
  exact hscaled.trans_lt (hupper.trans_lt hpowerLt)

/-- The existing terminal projection threshold also closes Alternative A for
the larger outer-popular AD constant once its strengthened constant bound is
used. -/
theorem PureWZ2TerminalExactProjectionThreshold.alternativeA_popular
    {sigma outputLoss inputLoss delta stickyLoss eta theoremEta : ℝ}
    (self : PureWZ2TerminalExactProjectionThreshold sigma outputLoss)
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
    (data : PureWZ2CommonRefinedReadyGraph
      delta theoremEta first.common first.ready)
    (htheoremEtaEq : theoremEta = self.theoremEta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (houtput : 0 < outputLoss) (houtputSigma : outputLoss / 2 < sigma)
    (hinput : 0 ≤ inputLoss) (hinputCeiling : inputLoss ≤ self.sourceLossCeiling)
    (hdeltaSmall : delta ≤ self.delta₀) :
    WZ1Proposition8_9AlternativeAUnion
      data.ready.deltaGraph outputLoss
      data.common.F data.common.G₁ data.common.G₁ := by
  subst theoremEta
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hdeltaOne : delta ≤ 1 := source.extremal.delta_le_one
  have hgraphSmall : data.ready.deltaGraph ≤ self.reductionDelta₀ := by
    rw [data.ready.deltaGraph_eq]
    exact self.graph_small delta hdelta hdeltaSmall
  have hsourceCost := data.source_cost hdelta hdeltaOne hinput
  have hsourceCostLoss : 0 ≤ 4 * inputLoss := by positivity
  have hgain : 10 * self.theoremEta + 4 * inputLoss <
      self.projectionEta * (sigma - outputLoss / 2) := by
    calc
      10 * self.theoremEta + 4 * inputLoss ≤
          10 * self.theoremEta + 4 * self.sourceLossCeiling := by gcongr
      _ < self.projectionEta * (sigma - outputLoss / 2) := self.gain
  have hgraphOne : data.ready.deltaGraph ≤ 1 := by
    rw [data.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale]
    have hrefinedOne : delta / 625 ≤ 1 := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 625)).2
      nlinarith
    have hroot := Real.sqrt_le_one.mpr hrefinedOne
    have hdenom : 1 ≤ 5 * Real.sqrt 3 := by
      have hsqrtThree : 1 ≤ Real.sqrt 3 :=
        (Real.one_le_sqrt).2 (by norm_num)
      nlinarith
    exact (div_le_self (Real.sqrt_nonneg _) hdenom).trans hroot
  have hgraphStrict : data.ready.deltaGraph < 1 := by
    rw [data.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale]
    have hrefinedPos : 0 < delta / 625 := by positivity
    have hrootPos : 0 < Real.sqrt (delta / 625) :=
      Real.sqrt_pos.mpr hrefinedPos
    have hdenom : 1 < 5 * Real.sqrt 3 := by
      have hsqrtThree : 1 ≤ Real.sqrt 3 :=
        (Real.one_le_sqrt).2 (by norm_num)
      nlinarith
    exact (div_lt_self hrootPos hdenom).trans_le
      (Real.sqrt_le_one.mpr (by
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 625)).2
        nlinarith))
  have hconstantSmall :
      (25920000000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN data.ready.deltaGraph
          (-(self.projectionEta * (sigma - outputLoss / 2) -
            (10 * self.theoremEta + 4 * inputLoss)) / 2) := by
    have hceiling := self.popular_constant_small delta hdelta hdeltaSmall
    rw [data.ready.deltaGraph_eq]
    apply hceiling.trans
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow_of_exponent_ge
    · dsimp only [wz1Lemma23Theorem22Scale]
      positivity
    · rw [← data.ready.deltaGraph_eq]
      exact hgraphOne
    · have hactualGap :
          self.projectionEta * (sigma - outputLoss / 2) -
              (10 * self.theoremEta + 4 * inputLoss) ≥
            self.projectionEta * (sigma - outputLoss / 2) -
              (10 * self.theoremEta + 4 * self.sourceLossCeiling) := by
        linarith
      nlinarith
  have hfirstAD := first.dot_difference_ad hsigma hsigmaOne
  have hAD := data.dot_difference_ad_of_first hdelta hsigma hsigmaOne hfirstAD
  have hCtop : 10 * ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
      pureWZ2TerminalPopularGraphConstant delta inputLoss) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) <|
      ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        (ENNReal.mul_ne_top (by norm_num)
          (by simp [Kakeya.realRpowENN]))
  apply data.projection_alternative_a_of_dot_ad hAD hCtop hdelta hdeltaOne
      hsigma hsigmaOne houtput houtputSigma self.reduction hgraphSmall
      self.theoremEta_pos.le self.theoremEta_small
  intro strongLong
  have hsourceCost' :
      Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN data.ready.deltaGraph (-(4 * inputLoss)) := by
    simpa only [show -(4 * inputLoss) = -4 * inputLoss by ring] using hsourceCost
  exact strongLong.constant_absorb_popular self.theoremEta_pos.le hgraphOne
    hsourceCost' hsourceCostLoss hgain hgraphStrict hconstantSmall

end Kakeya.Assouad
