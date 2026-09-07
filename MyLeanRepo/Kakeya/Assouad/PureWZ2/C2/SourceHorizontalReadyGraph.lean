import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalVolume
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23CommonEndpointGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.LocallyLinearOneScale.BaseSliceValuesAD
import MyLeanRepo.Kakeya.Assouad.WZ1.LocallyLinearOneScale.DotDifferenceAD324
import MyLeanRepo.Kakeya.Assouad.WZ1.CommonEndpointLongExclusion
import MyLeanRepo.Kakeya.Assouad.WZ1.WellSeparatedProjectionUnion

/-!
# Common-endpoint ready graph for the Pure fixed-line construction

This is the numerical assembly boundary.  All geometry and counting data come
from the final residue carrier; the caller supplies only the small-scale power
absorptions selected by the outer one-scale parameter schedule.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The common-endpoint graph together with its Theorem-22-ready certificate. -/
structure PureWZ2SourceHorizontalFixedBinReadyGraph
    {sigma inputLoss delta rho middleLoss outputLoss theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalFixedBinResiduePreparation retained}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    (sharp : PureWZ2SourceHorizontalFixedBinSharpGeometry graph) where
  common : WZ1Lemma23UnitBallGraph
    prep.graphScale sharp.sharp.normalized.F
    (wz1Lemma23CommonLocalVertices prep.graphScale
      sharp.sharp.selectedLocal.g graph.residue.cells)
    (wz1Lemma23CommonLocalVertices prep.graphScale
      sharp.sharp.selectedLocal.g graph.residue.cells)
    sharp.sharp.normalized.H
  ready : WZ1Lemma23Theorem22ReadyGraph
    prep.graphScale theoremEta common
  heightFiberCost_eq : graph.residue.heightFiberCost = 2

/-- Backwards-compatible ready graph on the maximal global bin. -/
abbrev PureWZ2SourceHorizontalReadyGraph
    {sigma inputLoss delta rho middleLoss outputLoss theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    (sharp : PureWZ2SourceHorizontalSharpGeometry graph) :=
  PureWZ2SourceHorizontalFixedBinReadyGraph (theoremEta := theoremEta) sharp

/--
Assemble the common ready graph from the explicit Pure volume budget and the
two standard Theorem-22 constant absorptions.
-/
theorem PureWZ2SourceHorizontalSharpGeometry.toReadyGraph
    {sigma inputLoss delta rho middleLoss outputLoss theoremEta
      volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    (sharp : PureWZ2SourceHorizontalSharpGeometry graph)
    (hheightFiberCost : graph.residue.heightFiberCost = 2)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCOne :
      (1 : ENNReal) ≤
        10 * Kakeya.realRpowENN
          delta (-inputLoss))
    (hCpower :
      (10 * Kakeya.realRpowENN
          delta (-inputLoss)).toReal ≤
        Real.rpow prep.graphScale (-constantLoss))
    (hshadow : prep.shadow.union = retained.shading.union)
    (hvolumeBudget :
      Kakeya.realRpowENN prep.graphScale
            (1 + sigma / 2 + volumeLoss) *
          (pureWZ2SourceHorizontalVolumeCost
              rho delta sigma inputLoss *
            MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) ≤
        window.volumeSupply *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass))
    (hextraPower :
      (graph.residue.extraCost : ℝ) ≤
        Real.rpow prep.graphScale (-extraLoss))
    (hedgeAbsorb :
      Real.rpow (wz1Lemma23Theorem22Scale prep.graphScale)
          (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow prep.graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss +
              4 * extraLoss))
    (hKatzTao :
      (4 : ENNReal) ≤
        Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale prep.graphScale) (-theoremEta)) :
    Nonempty (PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp) := by
  let C : ENNReal :=
    10 * Kakeya.realRpowENN
      delta (-inputLoss)
  have hCtop : C ≠ ⊤ := by
    dsimp only [C]
    exact ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN])
  have hcoord :
      ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hpaper : point ∈ retained.shading.union := by
      exact prep.shadow_union_subset hpoint
    have hbox := shading_union_subset_axisBox hpaper
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hvolume :
      ENNReal.ofReal
          (Real.rpow prep.graphScale
            (1 + sigma / 2 + volumeLoss)) ≤
        MeasureTheory.volume prep.shadow.union := by
    exact prep.power_volume_lower hshadow hvolumeBudget
  have hedgeReal :
      Real.rpow (wz1Lemma23Theorem22Scale prep.graphScale)
          (theoremEta - 3) ≤
        (sharp.sharp.normalized.H.card : ℝ) := by
    apply hedgeAbsorb.trans
    exact sharp.sharp.power_edge_bound_of_coord
      prep.graphScale_one hsigma hsigmaOne hcoord
      hCOne hCtop volumeLoss constantLoss extraLoss
      hvolume hCpower hextraPower
  have hedgeNormalized :
      Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale prep.graphScale)
          (theoremEta - 3) ≤
        (sharp.sharp.normalized.H.card : ENNReal) := by
    rw [Kakeya.realRpowENN]
    have hcast :
        (sharp.sharp.normalized.H.card : ENNReal) =
          ENNReal.ofReal (sharp.sharp.normalized.H.card : ℝ) := by
      norm_cast
    rw [hcast]
    exact ENNReal.ofReal_le_ofReal hedgeReal
  have hedgeUnit :
      Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale prep.graphScale)
          (theoremEta - 3) ≤
        (sharp.geometry.unitBall.H.card : ENNReal) := by
    rw [sharp.geometry.unitBall.edge_card]
    exact hedgeNormalized
  rcases sharp.geometry.toCommonEndpointReadyGraph
      prep.graphScale_one hcoord hedgeUnit hKatzTao with
    ⟨common, ready⟩
  exact ⟨{ common := common
           ready := Classical.choice ready
           heightFiberCost_eq := hheightFiberCost }⟩

/-- A ready graph forces the frozen base height to be an actual residue height. -/
theorem PureWZ2SourceHorizontalFixedBinReadyGraph.base_height_mem
    {sigma inputLoss delta rho middleLoss outputLoss theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalFixedBinResiduePreparation retained}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalFixedBinSharpGeometry graph}
    (data : PureWZ2SourceHorizontalFixedBinReadyGraph
      (theoremEta := theoremEta) sharp) :
    sharp.sharp.baseHeightIndex ∈
      wz1Lemma23SnappedHeights graph.residue.cells := by
  classical
  rcases data.ready.H_nonempty with ⟨edge, hedge⟩
  have hedgeCommon : edge ∈ data.common.H := hedge
  rw [data.common.H_eq] at hedgeCommon
  rcases Finset.mem_image.mp hedgeCommon with
    ⟨normalizedEdge, hnormalizedEdge, _⟩
  have hsourceNormalized :
      normalizedEdge ∈ sharp.sharp.normalized.H := by
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
          sharp.sharp.selectedLocal.g graph.residue.cells :=
    hfilter.1
  have hcell : path.1 ∈ graph.residue.cells := by
    have hrelations :
        (path.1 ∈ graph.residue.cells ∧
          path.2.1 ∈ graph.residue.cells ∧
          path.2.2.1 ∈ graph.residue.cells ∧
          path.2.2.2 ∈ graph.residue.cells) ∧
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

/--
The final common graph has the paper dot-difference AD bound at its exact
unit-ball dot scale.  No source/normalized carrier identification is used.
-/
theorem PureWZ2SourceHorizontalFixedBinReadyGraph.dot_difference_ad
    {sigma inputLoss delta rho middleLoss outputLoss theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalFixedBinResiduePreparation retained}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalFixedBinSharpGeometry graph}
    (data : PureWZ2SourceHorizontalFixedBinReadyGraph
      (theoremEta := theoremEta) sharp)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    IsADSet1 (wz1DotDifferenceSet data.common.H)
      (Real.sqrt prep.graphScale / (25 * Real.sqrt 3))
      (1 - sigma)
      ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
        (10 * Kakeya.realRpowENN
          delta (-inputLoss))) := by
  let C : ENNReal := 10 * Kakeya.realRpowENN
    delta (-inputLoss)
  let z := prep.windowed.global.selectedHeight sharp.sharp.baseHeightIndex
  let E : Set ℝ := scalarProjection
    (globalGrainDirection (prep.windowed.global.sourceSlope z))
    (horizontalSlice prep.shadow.union z)
  let untranslated : Finset ℝ :=
    (graph.residue.cells.filter fun idx =>
      wz1Lemma23SnappedHeight idx = sharp.sharp.baseHeightIndex).image
      fun idx => wz1Lemma23GlobalCoordinate
        prep.windowed.global.extendedSlope
        (wz1Lemma23SnappedPoint prep.graphScale idx)
  let shift : ℝ := (sharp.sharp.baseGlobalBin : ℝ) * prep.graphScale
  let baseValues := wz1Lemma23SnappedBaseSliceValues
    prep.graphScale prep.windowed.global.extendedSlope graph.residue.cells
    sharp.sharp.baseHeightIndex sharp.sharp.baseGlobalBin
  have hcoord : ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hpaper : point ∈ retained.shading.union := by
      exact prep.shadow_union_subset hpoint
    have hbox := shading_union_subset_axisBox hpaper
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hheight := data.base_height_mem
  have hz : z ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases Finset.mem_image.mp hheight with ⟨idx, hidx, hidxHeight⟩
    have hidxGlobal := graph.residue.cells_subset hidx
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
        prep.windowed.global graph.residue.cells
        graph.residue.cells_subset sharp.sharp.baseHeightIndex hcoord
        prep.graphScale_pos prep.graphScale_one hheight
  have hbaseValuesEq :
      (baseValues : Set ℝ) = (fun value : ℝ => value - shift) '' untranslated := by
    ext value
    simp [baseValues, untranslated, shift,
      wz1Lemma23SnappedBaseSliceValues]
  have htranslated :
      (baseValues : Set ℝ) ⊆
        Metric.cthickening (4 * prep.graphScale)
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
    rw [sharp.sharp.normalized.values_eq,
      sharp.sharp.normalized_sourceValues]
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

/--
Apply the closed common-endpoint projection reduction and exclude its normalized
long branch using the attached dot-difference AD certificate.
-/
theorem PureWZ2SourceHorizontalFixedBinReadyGraph.projection_alternative_a
    (hWell : WZ1WellSeparatedProjectionUnionConclusion)
    {sigma inputLoss delta rho middleLoss outputLoss theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalFixedBinResiduePreparation retained}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalFixedBinSharpGeometry graph}
    (data : PureWZ2SourceHorizontalFixedBinReadyGraph
      (theoremEta := theoremEta) sharp)
    (hepsilon : 0 < outputLoss) (hepsilonOne : outputLoss < 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilonSigma : outputLoss / 2 < sigma)
    {reductionEta reductionDelta₀ : ℝ}
    (hreduction :
      ∀ {rho' : ℝ}
        {sourceF' sourceG₁' sourceG₂' : DiscreteSet 2}
        {sourceH' : Finset (Point2 × Point2 × Point2)}
        {unitBall' : WZ1Lemma23UnitBallGraph
          rho' sourceF' sourceG₁' sourceG₂' sourceH'}
        (ready' : WZ1Lemma23Theorem22ReadyGraph
          rho' reductionEta unitBall'),
        ready'.deltaGraph ≤ reductionDelta₀ →
        unitBall'.G₂ = unitBall'.G₁ →
          WZ1Proposition8_9AlternativeAUnion
              ready'.deltaGraph outputLoss
              unitBall'.F unitBall'.G₁ unitBall'.G₁ ∨
            Nonempty (WZ1CommonEndpointProjectionLongData
              (epsilon := outputLoss) ready'))
    (hetaEq : theoremEta = reductionEta)
    (hdeltaSmall : data.ready.deltaGraph ≤ reductionDelta₀)
    (hscaledOne :
      ∀ long : WZ1CommonEndpointProjectionLongData
          (epsilon := outputLoss) data.ready,
        long.affine.dotScale *
          (Real.sqrt prep.graphScale / (25 * Real.sqrt 3)) ≤ 1)
    (hconstant :
      ∀ long : WZ1CommonEndpointProjectionLongData
          (epsilon := outputLoss) data.ready,
        let C := (16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
          (10 * Kakeya.realRpowENN
            delta (-inputLoss))
        ((5 * C) * ENNReal.ofReal
              (max 1 (10 * (long.affine.dotScale *
                (Real.sqrt prep.graphScale / (25 * Real.sqrt 3))) /
                (data.ready.deltaGraph / 2)))) * 100 *
            Kakeya.realRpowENN (data.ready.deltaGraph / 2)
              (long.projectionEta * (sigma - outputLoss / 2)) < 1) :
    WZ1Proposition8_9AlternativeAUnion
      data.ready.deltaGraph outputLoss
      data.common.F data.common.G₁ data.common.G₁ := by
  subst theoremEta
  have hcommon : data.common.G₂ = data.common.G₁ := by
    rw [data.common.G₂_eq, data.common.G₁_eq]
  rcases hreduction data.ready hdeltaSmall hcommon with hA | hB
  · exact hA
  · rcases hB with ⟨long⟩
    exfalso
    let C : ENNReal := (16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
      (10 * Kakeya.realRpowENN
        delta (-inputLoss))
    have hAD : IsADSet1 (wz1DotDifferenceSet data.common.H)
        (Real.sqrt prep.graphScale / (25 * Real.sqrt 3))
        (1 - sigma) C := by
      simpa [C] using data.dot_difference_ad hsigma hsigmaOne
    have hCtop : C ≠ ⊤ := by
      dsimp only [C]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        (ENNReal.mul_ne_top (by norm_num)
          (by simp [Kakeya.realRpowENN]))
    have htargetPos : 0 < data.ready.deltaGraph / 2 := by
      exact div_pos data.ready.deltaGraph_pos (by norm_num)
    have hdeltaGraphOne : data.ready.deltaGraph ≤ 1 := by
      rw [data.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale]
      have hsqrt := Real.sqrt_le_one.mpr prep.graphScale_one
      have hdenom : 1 ≤ 5 * Real.sqrt 3 := by
        have hsqrt3 : 1 ≤ Real.sqrt 3 :=
          (Real.one_le_sqrt).2 (by norm_num)
        nlinarith
      exact (div_le_self (Real.sqrt_nonneg prep.graphScale) hdenom).trans hsqrt
    have htargetOne : data.ready.deltaGraph / 2 ≤ 1 := by
      exact (div_le_self data.ready.deltaGraph_pos.le (by norm_num)).trans
        hdeltaGraphOne
    have htargetStrict : data.ready.deltaGraph / 2 < 1 := by
      calc
        data.ready.deltaGraph / 2 < data.ready.deltaGraph := by
          linarith [data.ready.deltaGraph_pos]
        _ ≤ 1 := hdeltaGraphOne
    exact long.false_of_dot_ad hAD hCtop hsigma hsigmaOne
      (by positivity) hepsilonSigma (hscaledOne long)
      htargetPos htargetOne htargetStrict (hconstant long)

/--
Closed analytic wrapper for the source common graph.  The union-valued
well-separated theorem and its common-endpoint reduction are selected
internally; callers retain only the genuine small-scale and normalized
dot-AD absorption obligations.
-/
theorem PureWZ2SourceHorizontalFixedBinReadyGraph.projection_alternative_a_closed
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalFixedBinResiduePreparation retained}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalFixedBinSharpGeometry graph}
    (hepsilon : 0 < outputLoss) (hepsilonOne : outputLoss < 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilonSigma : outputLoss / 2 < sigma)
    :
    ∃ theoremEta reductionDelta₀ : ℝ,
      0 < theoremEta ∧ theoremEta ≤ 1 / 100 ∧
      0 < reductionDelta₀ ∧ reductionDelta₀ ≤ 1 / 2 ∧
      ∀ data : PureWZ2SourceHorizontalFixedBinReadyGraph
          (theoremEta := theoremEta) sharp,
        data.ready.deltaGraph ≤ reductionDelta₀ →
        (∀ long : WZ1CommonEndpointProjectionLongData
            (epsilon := outputLoss) data.ready,
          long.affine.dotScale *
            (Real.sqrt prep.graphScale / (25 * Real.sqrt 3)) ≤ 1) →
        (∀ long : WZ1CommonEndpointProjectionLongData
            (epsilon := outputLoss) data.ready,
          let C := (16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
            (10 * Kakeya.realRpowENN delta (-inputLoss))
          ((5 * C) * ENNReal.ofReal
                (max 1 (10 * (long.affine.dotScale *
                  (Real.sqrt prep.graphScale / (25 * Real.sqrt 3))) /
                  (data.ready.deltaGraph / 2)))) * 100 *
              Kakeya.realRpowENN (data.ready.deltaGraph / 2)
                (long.projectionEta * (sigma - outputLoss / 2)) < 1) →
        WZ1Proposition8_9AlternativeAUnion
          data.ready.deltaGraph outputLoss
          data.common.F data.common.G₁ data.common.G₁ := by
  rcases wz1_common_endpoint_projection_reduction
      wz1_well_separated_projection_union outputLoss hepsilon hepsilonOne with
    ⟨theoremEta, reductionDelta₀, heta, hetaSmall,
      hdelta₀, hdelta₀Half, hreduction⟩
  refine ⟨theoremEta, reductionDelta₀, heta, hetaSmall,
    hdelta₀, hdelta₀Half, ?_⟩
  intro data hdeltaSmall hscaledOne hconstant
  exact data.projection_alternative_a
    wz1_well_separated_projection_union
    hepsilon hepsilonOne hsigma hsigmaOne hepsilonSigma
    hreduction rfl hdeltaSmall hscaledOne hconstant

/-- Backwards-compatible names for the former maximal-bin ready-graph API. -/
theorem PureWZ2SourceHorizontalReadyGraph.base_height_mem
    {sigma inputLoss delta rho middleLoss outputLoss theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    (data : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp) :
    sharp.sharp.baseHeightIndex ∈
      wz1Lemma23SnappedHeights graph.residue.cells :=
  PureWZ2SourceHorizontalFixedBinReadyGraph.base_height_mem data

theorem PureWZ2SourceHorizontalReadyGraph.dot_difference_ad
    {sigma inputLoss delta rho middleLoss outputLoss theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    (data : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    IsADSet1 (wz1DotDifferenceSet data.common.H)
      (Real.sqrt prep.graphScale / (25 * Real.sqrt 3))
      (1 - sigma)
      ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
        (10 * Kakeya.realRpowENN delta (-inputLoss))) :=
  PureWZ2SourceHorizontalFixedBinReadyGraph.dot_difference_ad
    data hsigma hsigmaOne

alias PureWZ2SourceHorizontalReadyGraph.projection_alternative_a :=
  PureWZ2SourceHorizontalFixedBinReadyGraph.projection_alternative_a

alias PureWZ2SourceHorizontalReadyGraph.projection_alternative_a_closed :=
  PureWZ2SourceHorizontalFixedBinReadyGraph.projection_alternative_a_closed

end Kakeya.Assouad
