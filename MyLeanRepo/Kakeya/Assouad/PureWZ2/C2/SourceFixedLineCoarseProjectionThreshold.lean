import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseReadyGraph
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalProjectionThreshold
import MyLeanRepo.Kakeya.Assouad.WZ1.LocallyLinearOneScale.BaseSliceValuesAD
import MyLeanRepo.Kakeya.Assouad.WZ1.LocallyLinearOneScale.DotDifferenceAD324
import MyLeanRepo.Kakeya.Assouad.WZ1.CommonEndpointLongExclusion
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Closed projection threshold for the fixed-bin coarse graph

This module supplies the exact dot-difference AD certificate internally, so
the source-fixed-bin projection threshold has no caller-provided projection
callback.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The fixed-bin Theorem-22 graph scale is at most twice the square root of
the sticky scale.  This estimate is independent of every runtime family and
dependent bin witness. -/
theorem pureWZ2_sourceFixedBinCoarse_deltaGraph_le_two_sqrt
    {rho : ℝ} (hrho : 0 < rho) :
    wz1Lemma23Theorem22Scale (256 * rho) ≤ 2 * Real.sqrt rho := by
  rw [wz1Lemma23Theorem22Scale, Real.sqrt_mul (by norm_num)]
  norm_num
  have hsqrtThree : 8 ≤ 5 * Real.sqrt 3 := by
    have hsqrtSq := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hsqrtNonneg := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  have hrootNonneg : 0 ≤ 16 * Real.sqrt rho := by positivity
  calc
    16 * Real.sqrt rho / (5 * Real.sqrt 3) ≤
        16 * Real.sqrt rho / 8 := by
      exact div_le_div_of_nonneg_left hrootNonneg (by norm_num) hsqrtThree
    _ = 2 * Real.sqrt rho := by ring

/-- Choose one sticky-scale threshold which transports every middle loss
below `middleLossCeiling` to the negative power of the actual fixed-bin
Theorem-22 graph scale.  The choice precedes the source family, preparation,
and selected coarse bin. -/
theorem pureWZ2_sourceFixedBinCoarse_projection_sourceCost_schedule
    {middleLossCeiling sourceCostLoss : ℝ}
    (hmiddleLossCeiling : 0 ≤ middleLossCeiling)
    (hsourceCostLoss : 0 < sourceCostLoss)
    (hgap : middleLossCeiling < (1 / 2 : ℝ) * sourceCostLoss) :
    ∃ rho₀ : ℝ, 0 < rho₀ ∧ rho₀ ≤ 1 ∧
      ∀ {middleLoss rho : ℝ},
        0 ≤ middleLoss → middleLoss ≤ middleLossCeiling →
        0 < rho → rho ≤ rho₀ →
          Kakeya.realRpowENN rho (-middleLoss) ≤
            Kakeya.realRpowENN
              (wz1Lemma23Theorem22Scale (256 * rho))
              (-sourceCostLoss) := by
  rcases exists_scale_power_conversion
      (C := 2) (p := (1 / 2 : ℝ))
      (a := middleLossCeiling) (b := sourceCostLoss)
      (by norm_num) (by norm_num) hmiddleLossCeiling hgap with
    ⟨conversionRho₀, hconversionRho₀, hconversionRho₀One, hconvert⟩
  let rho₀ := min conversionRho₀ (1 / 256 : ℝ)
  refine ⟨rho₀, lt_min hconversionRho₀ (by norm_num),
    (min_le_left _ _).trans hconversionRho₀One, ?_⟩
  intro middleLoss rho hmiddleLoss hmiddleLossBound hrho hrhoSmall
  have hrhoConversion : rho ≤ conversionRho₀ :=
    hrhoSmall.trans (min_le_left _ _)
  have hrhoOne : rho ≤ 1 :=
    hrhoConversion.trans hconversionRho₀One
  have hgraphScalePos :
      0 < wz1Lemma23Theorem22Scale (256 * rho) := by
    dsimp only [wz1Lemma23Theorem22Scale]
    positivity
  have hscaledOne : 256 * rho ≤ 1 := by
    have hrhoBound : rho ≤ 1 / 256 :=
      hrhoSmall.trans (min_le_right _ _)
    linarith
  have hgraphScaleOne :
      wz1Lemma23Theorem22Scale (256 * rho) ≤ 1 := by
    dsimp only [wz1Lemma23Theorem22Scale]
    have hrootOne : Real.sqrt (256 * rho) ≤ 1 :=
      Real.sqrt_le_one.mpr hscaledOne
    have hdenom : 1 ≤ 5 * Real.sqrt 3 := by
      have hsqrtThree : 1 ≤ Real.sqrt 3 :=
        (Real.one_le_sqrt).2 (by norm_num)
      nlinarith
    exact (div_le_self (Real.sqrt_nonneg _) hdenom).trans hrootOne
  have hgraphScalePower :
      wz1Lemma23Theorem22Scale (256 * rho) ≤
        2 * rho ^ (1 / 2 : ℝ) := by
    simpa [Real.sqrt_eq_rpow] using
      pureWZ2_sourceFixedBinCoarse_deltaGraph_le_two_sqrt hrho
  have hceiling := hconvert rho
    (wz1Lemma23Theorem22Scale (256 * rho))
    hrho hrhoConversion hgraphScalePos hgraphScaleOne hgraphScalePower
  have hmiddleMono :
      Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN rho (-middleLossCeiling) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hrho hrhoOne (by linarith)
  exact hmiddleMono.trans hceiling

/-- The same fixed-bin scale conversion with the absolute factor `10` used
as the Lemma-23 graph constant. -/
theorem pureWZ2_sourceFixedBinCoarse_constant_schedule
    {middleLossCeiling constantLoss : ℝ}
    (hmiddleLossCeiling : 0 ≤ middleLossCeiling)
    (hconstantLoss : 0 < constantLoss)
    (hgap : middleLossCeiling < constantLoss) :
    ∃ rho₀ : ℝ, 0 < rho₀ ∧ rho₀ ≤ 1 ∧
      ∀ {middleLoss rho : ℝ},
        0 ≤ middleLoss → middleLoss ≤ middleLossCeiling →
        0 < rho → rho ≤ rho₀ →
          (10 * Kakeya.realRpowENN rho (-middleLoss)).toReal ≤
            Real.rpow (256 * rho) (-constantLoss) := by
  let intermediateLoss := (middleLossCeiling + constantLoss) / 2
  have hmiddleIntermediate : middleLossCeiling < intermediateLoss := by
    dsimp only [intermediateLoss]
    linarith
  have hintermediateNonneg : 0 ≤ intermediateLoss := by
    dsimp only [intermediateLoss]
    positivity
  have hintermediateConstant : intermediateLoss < constantLoss := by
    dsimp only [intermediateLoss]
    linarith
  rcases exists_scale_absorb_constant (10 : ENNReal) (by norm_num)
      hmiddleLossCeiling hmiddleIntermediate with
    ⟨constantRho₀, hconstantRho₀, hconstantRho₀One, habsorb⟩
  rcases exists_scale_power_conversion
      (C := 256) (p := 1) (a := intermediateLoss) (b := constantLoss)
      (by norm_num) (by norm_num) hintermediateNonneg
      (by simpa using hintermediateConstant) with
    ⟨transportRho₀, htransportRho₀, htransportRho₀One, htransport⟩
  let rho₀ := min constantRho₀ (min transportRho₀ (1 / 256 : ℝ))
  refine ⟨rho₀, by positivity,
    (min_le_left _ _).trans hconstantRho₀One, ?_⟩
  intro middleLoss rho hmiddle hmiddleCeiling hrho hrhoSmall
  have hrhoConstant : rho ≤ constantRho₀ :=
    hrhoSmall.trans (min_le_left _ _)
  have hrhoTransport : rho ≤ transportRho₀ :=
    hrhoSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrhoGraph : 256 * rho ≤ 1 := by
    have hsmall : rho ≤ 1 / 256 :=
      hrhoSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hmiddleMono : Kakeya.realRpowENN rho (-middleLoss) ≤
      Kakeya.realRpowENN rho (-middleLossCeiling) := by
    exact realRpowENN_antitone hrho
      (hrhoSmall.trans ((min_le_left _ _).trans hconstantRho₀One))
      (by linarith)
  have hsource : 10 * Kakeya.realRpowENN rho (-middleLoss) ≤
      Kakeya.realRpowENN rho (-intermediateLoss) :=
    (mul_le_mul_left' hmiddleMono 10).trans
      (habsorb rho hrho hrhoConstant)
  have hconverted : Kakeya.realRpowENN rho (-intermediateLoss) ≤
      Kakeya.realRpowENN (256 * rho) (-constantLoss) :=
    htransport rho (256 * rho) hrho hrhoTransport (by positivity)
      hrhoGraph (by simp)
  have hENN := hsource.trans hconverted
  have hrightTop :
      Kakeya.realRpowENN (256 * rho) (-constantLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have hreal := ENNReal.toReal_mono hrightTop hENN
  have hleft :
      (10 * Kakeya.realRpowENN rho (-middleLoss)).toReal =
        10 * Real.rpow rho (-middleLoss) := by
    simp [Kakeya.realRpowENN,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hrho.le _)]
  have hright :
      (Kakeya.realRpowENN (256 * rho) (-constantLoss)).toReal =
        Real.rpow (256 * rho) (-constantLoss) := by
    simp [Kakeya.realRpowENN,
      ENNReal.toReal_ofReal
        (Real.rpow_nonneg (by positivity : 0 ≤ 256 * rho) _)]
  rw [hleft, hright] at hreal
  simpa [Kakeya.realRpowENN,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hrho.le _)] using hreal

/-- A ready fixed-bin graph forces the frozen base height to occur in its
residue carrier. -/
theorem PureWZ2SourceFixedBinCoarseReadyGraph.base_height_mem
    {sigma inputLoss delta rho middleLoss stickyLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData graphParents normalFirst}
    {sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph}
    (data : PureWZ2SourceFixedBinCoarseReadyGraph
      (theoremEta := theoremEta) sharp) :
    sharp.sharp.baseHeightIndex ∈
      wz1Lemma23SnappedHeights preparedGraph.graph.residue.cells := by
  classical
  rcases data.ready.H_nonempty with ⟨edge, hedge⟩
  have hedgeCommon : edge ∈ data.common.H := hedge
  rw [data.common.H_eq] at hedgeCommon
  rcases Finset.mem_image.mp hedgeCommon with
    ⟨normalizedEdge, hnormalizedEdge, _⟩
  have hsourceNormalized : normalizedEdge ∈ sharp.sharp.normalized.H := by
    simpa using hnormalizedEdge
  rw [sharp.sharp.normalized.H_eq] at hsourceNormalized
  rcases Finset.mem_image.mp hsourceNormalized with
    ⟨actualEdge, hactualEdge, _⟩
  rw [sharp.sharp.normalized_sourceH, sharp.sharp.actual.H_eq] at hactualEdge
  rcases Finset.mem_image.mp hactualEdge with ⟨path, hpath, _⟩
  have hpathBase := hpath
  rw [sharp.sharp.actual.cycles_eq] at hpathBase
  have hfilter := Finset.mem_filter.mp hpathBase
  have hbase :
      wz1Lemma23SnappedHeight path.1 = sharp.sharp.baseHeightIndex :=
    hfilter.2.1
  have hfour :
      path ∈ wz1Lemma23SnappedFourCycles
        prep.graphScale prep.windowed.global.extendedSlope
          sharp.sharp.selectedLocal.g preparedGraph.graph.residue.cells :=
    hfilter.1
  have hcell : path.1 ∈ preparedGraph.graph.residue.cells := by
    have hrelations :
        (path.1 ∈ preparedGraph.graph.residue.cells ∧
          path.2.1 ∈ preparedGraph.graph.residue.cells ∧
          path.2.2.1 ∈ preparedGraph.graph.residue.cells ∧
          path.2.2.2 ∈ preparedGraph.graph.residue.cells) ∧
        wz1Lemma23SameSnappedLocalGrain prep.graphScale
          sharp.sharp.selectedLocal.g path.1 path.2.1 ∧
        wz1Lemma23SameSnappedLocalGrain prep.graphScale
          sharp.sharp.selectedLocal.g path.2.2.2 path.2.2.1 ∧
        wz1Lemma23SnappedHeight path.1 =
          wz1Lemma23SnappedHeight path.2.2.2 ∧
        wz1Lemma23SnappedHeight path.2.1 =
          wz1Lemma23SnappedHeight path.2.2.1 ∧
        wz1Lemma23SnappedGlobalBin prep.graphScale
            prep.windowed.global.extendedSlope path.2.1 =
          wz1Lemma23SnappedGlobalBin prep.graphScale
            prep.windowed.global.extendedSlope path.2.2.1 := by
      simpa [wz1Lemma23SnappedFourCycles, wz1Lemma23FourCycles,
        Finset.mem_filter, Finset.mem_product] using hfour
    exact hrelations.1.1
  exact Finset.mem_image.mpr ⟨path.1, hcell, hbase⟩

/-- The fixed-bin ready graph has the exact unit-ball dot-difference AD bound. -/
theorem PureWZ2SourceFixedBinCoarseReadyGraph.dot_difference_ad
    {sigma inputLoss delta rho middleLoss stickyLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData graphParents normalFirst}
    {sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph}
    (data : PureWZ2SourceFixedBinCoarseReadyGraph
      (theoremEta := theoremEta) sharp)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    IsADSet1 (wz1DotDifferenceSet data.common.H)
      (Real.sqrt prep.graphScale / (25 * Real.sqrt 3))
      (1 - sigma)
      ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
        (10 * Kakeya.realRpowENN rho (-middleLoss))) := by
  let C : ENNReal := 10 * Kakeya.realRpowENN rho (-middleLoss)
  let z := prep.windowed.global.selectedHeight sharp.sharp.baseHeightIndex
  let E : Set ℝ := scalarProjection
    (globalGrainDirection (prep.windowed.global.sourceSlope z))
    (horizontalSlice prep.shadow.union z)
  let untranslated : Finset ℝ :=
    (preparedGraph.graph.residue.cells.filter fun idx =>
      wz1Lemma23SnappedHeight idx = sharp.sharp.baseHeightIndex).image
      fun idx => wz1Lemma23GlobalCoordinate
        prep.windowed.global.extendedSlope
        (wz1Lemma23SnappedPoint prep.graphScale idx)
  let shift : ℝ := (sharp.sharp.baseGlobalBin : ℝ) * prep.graphScale
  let baseValues := wz1Lemma23SnappedBaseSliceValues
    prep.graphScale prep.windowed.global.extendedSlope preparedGraph.graph.residue.cells
    sharp.sharp.baseHeightIndex sharp.sharp.baseGlobalBin
  have hcoord : ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hcarrier : point ∈ carrier.shading.union := by
      exact prep.shadow_union_subset hpoint
    have hbox := shading_union_subset_axisBox
      (carrier.subshading.union_subset hcarrier)
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hheight := data.base_height_mem
  have hz : z ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases Finset.mem_image.mp hheight with ⟨idx, hidx, hidxHeight⟩
    have hidxGlobal := preparedGraph.graph.residue.cells_subset hidx
    rw [prep.windowed.global.cells_eq] at hidxGlobal
    rcases Finset.mem_biUnion.mp hidxGlobal with ⟨height, hheightMem, hidxLayer⟩
    have hheightEq : height = sharp.sharp.baseHeightIndex := by
      have h := prep.windowed.global.layer_height height hheightMem idx hidxLayer
      simpa [wz1Lemma23SnappedHeight] using h.symm.trans hidxHeight
    have hidxLayerBase :
        idx ∈ prep.windowed.global.layerCells sharp.sharp.baseHeightIndex := by
      rwa [hheightEq] at hidxLayer
    let cell : WZ1Lemma23ExactSliceCell prep.shadow prep.graphScale
        prep.graphScale_pos z :=
      ⟨idx, by
        rw [prep.windowed.global.layerCells_eq] at hidxLayerBase
        exact hidxLayerBase⟩
    let point := wz1Lemma23LiftSlicePoint z
      (wz1Lemma23ExactSliceRepresentative prep.shadow
        prep.graphScale_pos z cell)
    have hpoint : point ∈ prep.shadow.union :=
      wz1Lemma23ExactSliceRepresentative_mem_union
        prep.shadow prep.graphScale_pos z cell
    have hpointHeight : point (2 : Fin 3) = z := by
      simp [point, wz1Lemma23LiftSlicePoint, point3]
    have habs : |z| ≤ 1 := by
      rw [← hpointHeight]
      exact hcoord point hpoint 2
    exact abs_le.mp habs
  have hAD : IsADSet1 E prep.graphScale (1 - sigma) C := by
    dsimp only [E, z, C]
    exact prep.exactAD _ hz
  have huntranslated :
      (untranslated : Set ℝ) ⊆ Metric.cthickening (4 * prep.graphScale) E := by
    simpa [untranslated, E, z] using
      base_slice_values_containment_of_coord
        prep.windowed.global preparedGraph.graph.residue.cells
        preparedGraph.graph.residue.cells_subset sharp.sharp.baseHeightIndex hcoord
        prep.graphScale_pos prep.graphScale_one hheight
  have hbaseValuesEq :
      (baseValues : Set ℝ) = (fun value : ℝ => value - shift) '' untranslated := by
    ext value
    simp [baseValues, untranslated, shift, wz1Lemma23SnappedBaseSliceValues]
  have htranslated :
      (baseValues : Set ℝ) ⊆ Metric.cthickening (4 * prep.graphScale)
          ((fun value : ℝ => value - shift) '' E) := by
    rw [hbaseValuesEq]
    intro value hvalue
    rcases hvalue with ⟨sourceValue, hsourceValue, rfl⟩
    have hnear := huntranslated hsourceValue
    rw [Metric.mem_cthickening_iff] at hnear ⊢
    have heq :
        Metric.infEDist (sourceValue - shift)
            ((fun value : ℝ => value - shift) '' E) =
          Metric.infEDist sourceValue E := by
      simpa [sub_eq_add_neg] using
        (Metric.infEDist_image (isometry_add_right (-shift))
          (x := sourceValue) (t := E))
    rw [heq]
    exact hnear
  have hnormalizedValues :
      (sharp.sharp.normalized.values : Set ℝ) =
        (fun value : ℝ => value / Real.sqrt prep.graphScale) ''
          (baseValues : Set ℝ) := by
    rw [sharp.sharp.normalized.values_eq, sharp.sharp.normalized_sourceValues]
    ext value
    simp [baseValues, wz1Lemma23NormalizedBaseValues]
  have hnormalizedDot := sharp.sharp.normalized.dot_containment
  have hunitDot :
      wz1DotDifferenceSet data.common.H =
        (fun value : ℝ => value / 25) ''
          wz1DotDifferenceSet sharp.sharp.normalized.H := by
    rw [data.common.dot_image]
  have hunitBound :
      wz1DotDifferenceSet data.common.H ⊆ Set.Icc (-2 : ℝ) 2 := by
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
    have hdot :
        |inner ℝ edge.1 (edge.2.1 - edge.2.2)| ≤ 20 := by
      calc
        |inner ℝ edge.1 (edge.2.1 - edge.2.2)|
            ≤ ‖edge.1‖ * ‖edge.2.1 - edge.2.2‖ :=
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
    prep.graphScale_pos prep.graphScale_one hsigma hsigmaOne
    (by
      dsimp only [C]
      exact ENNReal.mul_ne_top (by norm_num)
        (by simp [Kakeya.realRpowENN])) hAD htranslated
    hnormalizedValues hnormalizedDot hunitDot hunitBound

/-- Exclude the projection long branch using the closed fixed-bin dot AD bound. -/
theorem PureWZ2SourceFixedBinCoarseReadyGraph.projection_alternative_a_strong
    {sigma inputLoss delta rho middleLoss stickyLoss outputLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData graphParents normalFirst}
    {sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph}
    (data : PureWZ2SourceFixedBinCoarseReadyGraph (theoremEta := theoremEta) sharp)
    (hepsilon : 0 < outputLoss) (hepsilonOne : outputLoss < 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilonSigma : outputLoss / 2 < sigma)
    {budgetFactor projectionEta reductionDelta₀ sourceCostLoss : ℝ}
    (hreduction :
      ∀ {rho' : ℝ} {sourceF' sourceG₁' sourceG₂' : DiscreteSet 2}
        {sourceH' : Finset (Point2 × Point2 × Point2)}
        {unitBall' : WZ1Lemma23UnitBallGraph rho' sourceF' sourceG₁' sourceG₂' sourceH'}
        (ready' : WZ1Lemma23Theorem22ReadyGraph rho' theoremEta unitBall'),
        ready'.deltaGraph ≤ reductionDelta₀ → unitBall'.G₂ = unitBall'.G₁ →
          WZ1Proposition8_9AlternativeAUnion ready'.deltaGraph outputLoss
              unitBall'.F unitBall'.G₁ unitBall'.G₁ ∨
            Nonempty (PureWZ2CommonEndpointProjectionLongData
              (epsilon := outputLoss) ready' budgetFactor projectionEta))
    (hdeltaSmall : data.ready.deltaGraph ≤ reductionDelta₀)
    (htheoremEta : 0 ≤ theoremEta)
    (htheoremEtaSmall : theoremEta ≤ 1 / 100)
    (hsourceCost : Kakeya.realRpowENN rho (-middleLoss) ≤
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
      (10 * Kakeya.realRpowENN rho (-middleLoss))
    have hAD : IsADSet1 (wz1DotDifferenceSet data.common.H)
        (Real.sqrt prep.graphScale / (25 * Real.sqrt 3)) (1 - sigma) C := by
      simpa [C] using data.dot_difference_ad hsigma hsigmaOne
    have hCtop : C ≠ ⊤ := by
      dsimp only [C]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        (ENNReal.mul_ne_top (by norm_num) (by simp [Kakeya.realRpowENN]))
    have hdeltaAD :
        Real.sqrt prep.graphScale / (25 * Real.sqrt 3) =
          data.ready.deltaGraph / 5 :=
      pureWZ2_sourceHorizontal_dotADScale_eq data.ready
    have hdeltaGraphOne : data.ready.deltaGraph ≤ 1 := by
      rw [data.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale]
      have hsqrt := Real.sqrt_le_one.mpr prep.graphScale_one
      have hdenom : 1 ≤ 5 * Real.sqrt 3 := by
        have hsqrt3 : 1 ≤ Real.sqrt 3 :=
          (Real.one_le_sqrt).2 (by norm_num)
        nlinarith
      exact (div_le_self (Real.sqrt_nonneg prep.graphScale) hdenom).trans hsqrt
    have hdeltaGraphStrict : data.ready.deltaGraph < 1 := by
      have hsqrt3 : 1 ≤ Real.sqrt 3 :=
        (Real.one_le_sqrt).2 (by norm_num)
      have hdenom : 1 < 5 * Real.sqrt 3 := by nlinarith
      rw [data.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale]
      have hsqrtPos : 0 < Real.sqrt prep.graphScale :=
        Real.sqrt_pos.mpr prep.graphScale_pos
      calc
        Real.sqrt prep.graphScale / (5 * Real.sqrt 3) < Real.sqrt prep.graphScale :=
          div_lt_self hsqrtPos hdenom
        _ ≤ 1 := Real.sqrt_le_one.mpr prep.graphScale_one
    have hscaledOne : strongLong.long.affine.dotScale *
        (Real.sqrt prep.graphScale / (25 * Real.sqrt 3)) ≤ 1 :=
      strongLong.scaled_dotAD_le_one hdeltaAD htheoremEta htheoremEtaSmall hdeltaGraphOne
    have hconstant := strongLong.constant_absorb hdeltaAD htheoremEta hdeltaGraphOne
      hsourceCost hsourceCostLoss hgain hdeltaGraphStrict hconstantSmall
    have htargetPos : 0 < data.ready.deltaGraph / 2 :=
      div_pos data.ready.deltaGraph_pos (by norm_num)
    have htargetOne : data.ready.deltaGraph / 2 ≤ 1 :=
      (div_le_self data.ready.deltaGraph_pos.le (by norm_num)).trans hdeltaGraphOne
    have htargetStrict : data.ready.deltaGraph / 2 < 1 := by
      calc
        data.ready.deltaGraph / 2 < data.ready.deltaGraph := by
          linarith [data.ready.deltaGraph_pos]
        _ < 1 := hdeltaGraphStrict
    exact strongLong.long.false_of_dot_ad hAD hCtop hsigma hsigmaOne
      (by positivity) hepsilonSigma hscaledOne
      htargetPos htargetOne htargetStrict hconstant

/-- The source-horizontal threshold closes Alternative A on every fixed-bin
coarse ready graph, without a caller-provided projection certificate. -/
theorem PureWZ2SourceHorizontalProjectionThreshold.alternativeA_sourceFixedBinCoarse
    {sigma outputLoss inputLoss delta rho middleLoss stickyLoss eta : ℝ}
    (self : PureWZ2SourceHorizontalProjectionThreshold sigma outputLoss)
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData graphParents normalFirst}
    {sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph}
    (data : PureWZ2SourceFixedBinCoarseReadyGraph
      (theoremEta := self.theoremEta) sharp)
    (houtput : 0 < outputLoss) (houtputOne : outputLoss < 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (houtputSigma : outputLoss / 2 < sigma)
    {sourceCostLoss : ℝ}
    (hsourceCost : Kakeya.realRpowENN rho (-middleLoss) ≤
      Kakeya.realRpowENN data.ready.deltaGraph (-sourceCostLoss))
    (hsourceCostLoss : 0 ≤ sourceCostLoss)
    (hsourceCostCeiling : sourceCostLoss ≤ self.sourceCostLossCeiling)
    (hrhoSmall : rho ≤ self.rho₀) :
    WZ1Proposition8_9AlternativeAUnion data.ready.deltaGraph outputLoss
      data.common.F data.common.G₁ data.common.G₁ := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hgraphSmall : data.ready.deltaGraph ≤ self.reductionDelta₀ := by
    rw [data.ready.deltaGraph_eq, prep.graphScale_eq]
    exact self.graph_small rho hrho hrhoSmall
  have hgain : 10 * self.theoremEta + sourceCostLoss <
      self.projectionEta * (sigma - outputLoss / 2) := by
    calc
      10 * self.theoremEta + sourceCostLoss ≤
          10 * self.theoremEta + self.sourceCostLossCeiling := by gcongr
      _ < self.projectionEta * (sigma - outputLoss / 2) := self.gain
  have hconstantSmall :
      (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN data.ready.deltaGraph
          (-(self.projectionEta * (sigma - outputLoss / 2) -
            (10 * self.theoremEta + sourceCostLoss)) / 2) := by
    have hceiling := self.constant_small rho hrho hrhoSmall
    rw [data.ready.deltaGraph_eq, prep.graphScale_eq]
    apply hceiling.trans
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow_of_exponent_ge
    · dsimp only [wz1Lemma23Theorem22Scale]
      positivity
    · exact (self.graph_small rho hrho hrhoSmall).trans
        (self.reductionDelta₀_le_half.trans (by norm_num))
    · have hactualGap :
          self.projectionEta * (sigma - outputLoss / 2) -
              (10 * self.theoremEta + sourceCostLoss) ≥
            self.projectionEta * (sigma - outputLoss / 2) -
              (10 * self.theoremEta + self.sourceCostLossCeiling) := by
        linarith
      nlinarith
  exact data.projection_alternative_a_strong
    houtput houtputOne hsigma hsigmaOne houtputSigma
    self.reduction hgraphSmall self.theoremEta_pos.le self.theoremEta_small
    hsourceCost hsourceCostLoss hgain hconstantSmall

end Kakeya.Assouad

end
