import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinAnchoredFiniteGraph
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalProjectionThreshold
import MyLeanRepo.Kakeya.Assouad.WZ1.LocallyLinearOneScale.BaseSliceValuesAD
import MyLeanRepo.Kakeya.Assouad.WZ1.LocallyLinearOneScale.DotDifferenceAD324
import MyLeanRepo.Kakeya.Assouad.WZ1.LocallyLinearOneScale.AlternativeAToTrapezoids
import MyLeanRepo.Kakeya.Assouad.WZ1.CommonEndpointLongExclusion

/-!
# WZ1 Theorem 5.2 on the anchored common-bin graph

This is the construction-independent P3 exit.  It starts from the anchored
graph-preparation ABI and from the paper-faithful generalized full-local-grain
family.  The latter has, at each selected anchor, a literal
`WZ1Lemma23FullLocalGrainInputGeneralized`; no concrete local-grain producer is
imported here.

The finite graph executes the paper's common `(z₀,w)` pigeonhole, exact skew
map, and the construction of `F`, `G`, `H`, and the normalized base-value set.
Below we transfer the base-slice AD estimate through the exact dot-product
inclusion, invoke the closed WZ1 Theorem 5.2 reduction, rule out its
dot-product alternative, and turn the surviving line alternative into
`Z_lin` and an affine `L_S`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The Step-4 base height belongs to the literal finite residue. -/
theorem PureWZ2AnchoredTheorem22ReadyGraph.base_height_mem
    {delta rho sigma theoremEta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    {sharp : PureWZ2AnchoredSharpGeometry finiteGraph}
    (data : PureWZ2AnchoredTheorem22ReadyGraph
      (theoremEta := theoremEta) sharp) :
    sharp.sharp.baseHeightIndex ∈
      wz1Lemma23SnappedHeights finiteGraph.graph.residue.cells := by
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
      path ∈ wz1Lemma23SnappedFourCycles rho
        prep.windowed.global.extendedSlope sharp.sharp.selectedLocal.g
        finiteGraph.graph.residue.cells :=
    hfilter.1
  have hcell : path.1 ∈ finiteGraph.graph.residue.cells := by
    have hrelations :
        (path.1 ∈ finiteGraph.graph.residue.cells ∧
          path.2.1 ∈ finiteGraph.graph.residue.cells ∧
          path.2.2.1 ∈ finiteGraph.graph.residue.cells ∧
          path.2.2.2 ∈ finiteGraph.graph.residue.cells) ∧
        wz1Lemma23SameSnappedLocalGrain rho
          sharp.sharp.selectedLocal.g path.1 path.2.1 ∧
        wz1Lemma23SameSnappedLocalGrain rho
          sharp.sharp.selectedLocal.g path.2.2.2 path.2.2.1 ∧
        wz1Lemma23SnappedHeight path.1 =
          wz1Lemma23SnappedHeight path.2.2.2 ∧
        wz1Lemma23SnappedHeight path.2.1 =
          wz1Lemma23SnappedHeight path.2.2.1 ∧
        wz1Lemma23SnappedGlobalBin rho prep.windowed.global.extendedSlope
            path.2.1 =
          wz1Lemma23SnappedGlobalBin rho prep.windowed.global.extendedSlope
            path.2.2.1 := by
      simpa [wz1Lemma23SnappedFourCycles, wz1Lemma23FourCycles,
        Finset.mem_filter, Finset.mem_product] using hfour
    exact hrelations.1.1
  exact Finset.mem_image.mpr ⟨path.1, hcell, hbase⟩

/--
The bounded unit-ball copy of the paper's thickened normalized base set
`A_tilde`.  The harmless intersection with `[-50,50]` contains every
normalized dot product (whose absolute value is at most `20`) and makes the
formal bounded AD predicate literal.
-/
def PureWZ2AnchoredTheorem22ReadyGraph.A_tilde
    {delta rho sigma theoremEta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    {sharp : PureWZ2AnchoredSharpGeometry finiteGraph}
    (_data : PureWZ2AnchoredTheorem22ReadyGraph
      (theoremEta := theoremEta) sharp) : Set ℝ :=
  (fun value : ℝ => value / 25) ''
    (Metric.cthickening (4 * Real.sqrt rho)
      (sharp.sharp.normalized.values : Set ℝ) ∩ Set.Icc (-50 : ℝ) 50)

/--
The paper's `A_tilde` AD bound on the exact anchored graph.

The proof retains the literal Step-4 data:

* `z` is the selected base height `z₀`;
* `shift = w = baseGlobalBin * rho`;
* `baseValues` is the translated base-slice set `A`;
* `normalized.values` is its `rho⁻¹/²` image;
* `normalized.dot_containment` is the exact Step-5 dot-product inclusion.

The final `/25` is only the common unit-ball normalization used by the formal
WZ1 Theorem 5.2.
-/
theorem PureWZ2AnchoredTheorem22ReadyGraph.A_tilde_ad
    {delta rho sigma theoremEta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    {sharp : PureWZ2AnchoredSharpGeometry finiteGraph}
    (data : PureWZ2AnchoredTheorem22ReadyGraph
      (theoremEta := theoremEta) sharp)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    IsADSet1 data.A_tilde
      (Real.sqrt rho / (25 * Real.sqrt 3)) (1 - sigma)
      ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) * C) := by
  let z := prep.windowed.global.selectedHeight sharp.sharp.baseHeightIndex
  let E : Set ℝ := scalarProjection
    (globalGrainDirection (prep.windowed.global.sourceSlope z))
    (horizontalSlice shadow.union z)
  let untranslated : Finset ℝ :=
    (finiteGraph.graph.residue.cells.filter fun idx =>
      wz1Lemma23SnappedHeight idx = sharp.sharp.baseHeightIndex).image
      fun idx => wz1Lemma23GlobalCoordinate
        prep.windowed.global.extendedSlope
        (wz1Lemma23SnappedPoint rho idx)
  let shift : ℝ := (sharp.sharp.baseGlobalBin : ℝ) * rho
  let baseValues := wz1Lemma23SnappedBaseSliceValues
    rho prep.windowed.global.extendedSlope finiteGraph.graph.residue.cells
    sharp.sharp.baseHeightIndex sharp.sharp.baseGlobalBin
  have hheight := data.base_height_mem
  have hz : z ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases Finset.mem_image.mp hheight with ⟨idx, hidx, hidxHeight⟩
    have hidxGlobal := finiteGraph.graph.residue.cells_subset hidx
    rw [prep.windowed.global.cells_eq] at hidxGlobal
    rcases Finset.mem_biUnion.mp hidxGlobal with
      ⟨height, hheightMem, hidxLayer⟩
    have hheightEq : height = sharp.sharp.baseHeightIndex := by
      have h := prep.windowed.global.layer_height height hheightMem idx hidxLayer
      simpa [wz1Lemma23SnappedHeight] using h.symm.trans hidxHeight
    have hidxLayerBase :
        idx ∈ prep.windowed.global.layerCells sharp.sharp.baseHeightIndex := by
      rwa [hheightEq] at hidxLayer
    let cell : WZ1Lemma23ExactSliceCell shadow rho input.rho_pos z :=
      ⟨idx, by
        rw [prep.windowed.global.layerCells_eq] at hidxLayerBase
        exact hidxLayerBase⟩
    let point := wz1Lemma23LiftSlicePoint z
      (wz1Lemma23ExactSliceRepresentative shadow input.rho_pos z cell)
    have hpoint : point ∈ shadow.union :=
      wz1Lemma23ExactSliceRepresentative_mem_union
        shadow input.rho_pos z cell
    have hpointHeight : point (2 : Fin 3) = z := by
      simp [point, wz1Lemma23LiftSlicePoint, point3]
    have habs : |z| ≤ 1 := by
      rw [← hpointHeight]
      exact prep.shadow_coordinate point hpoint 2
    exact abs_le.mp habs
  have hAD : IsADSet1 E rho (1 - sigma) C := by
    dsimp only [E, z]
    exact prep.exactAD _ hz
  have huntranslated :
      (untranslated : Set ℝ) ⊆ Metric.cthickening (4 * rho) E := by
    simpa [untranslated, E, z] using
      base_slice_values_containment_of_coord prep.windowed.global
        finiteGraph.graph.residue.cells
        finiteGraph.graph.residue.cells_subset sharp.sharp.baseHeightIndex
        prep.shadow_coordinate input.rho_pos input.rho_le_one hheight
  have hbaseValuesEq :
      (baseValues : Set ℝ) =
        (fun value : ℝ => value - shift) '' untranslated := by
    ext value
    simp [baseValues, untranslated, shift, wz1Lemma23SnappedBaseSliceValues]
  have htranslated :
      (baseValues : Set ℝ) ⊆ Metric.cthickening (4 * rho)
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
        (fun value : ℝ => value / Real.sqrt rho) ''
          (baseValues : Set ℝ) := by
    rw [sharp.sharp.normalized.values_eq,
      sharp.sharp.normalized_sourceValues]
    ext value
    simp [baseValues, wz1Lemma23NormalizedBaseValues]
  have hnormalizedATilde :
      (Metric.cthickening (4 * Real.sqrt rho)
          (sharp.sharp.normalized.values : Set ℝ) ∩
        Set.Icc (-50 : ℝ) 50) ⊆
        Metric.cthickening (4 * Real.sqrt rho)
          (sharp.sharp.normalized.values : Set ℝ) := by
    intro value hvalue
    exact hvalue.1
  have hunitATilde :
      data.A_tilde =
        (fun value : ℝ => value / 25) ''
          (Metric.cthickening (4 * Real.sqrt rho)
            (sharp.sharp.normalized.values : Set ℝ) ∩
              Set.Icc (-50 : ℝ) 50) := rfl
  have hunitBound :
      data.A_tilde ⊆ Set.Icc (-2 : ℝ) 2 := by
    intro value hvalue
    rcases hvalue with ⟨sourceValue, hsourceValue, rfl⟩
    have hbounds := hsourceValue.2
    change -2 ≤ sourceValue / 25 ∧ sourceValue / 25 ≤ 2
    constructor
    · exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 25)).2 (by
        linarith [hbounds.1])
    · exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 25)).2 (by
        linarith [hbounds.2])
  exact dot_difference_AD_transfer_shifted
    input.rho_pos input.rho_le_one hsigma hsigmaOne
    input.constant_ne_top hAD htranslated hnormalizedValues
    hnormalizedATilde hunitATilde hunitBound

/-- Every formal dot product lies in the literal thickened `A_tilde`. -/
theorem
    PureWZ2AnchoredTheorem22ReadyGraph.dot_product_subset_A_tilde
    {delta rho sigma theoremEta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    {sharp : PureWZ2AnchoredSharpGeometry finiteGraph}
    (data : PureWZ2AnchoredTheorem22ReadyGraph
      (theoremEta := theoremEta) sharp) :
    wz1DotDifferenceSet data.common.H ⊆ data.A_tilde := by
  intro value hvalue
  rw [data.common.dot_image] at hvalue
  rcases hvalue with ⟨sourceValue, hsourceValue, rfl⟩
  refine ⟨sourceValue, ⟨sharp.sharp.normalized.dot_containment hsourceValue,
    ?_⟩, rfl⟩
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
      |inner ℝ edge.1 (edge.2.1 - edge.2.2)|
          ≤ ‖edge.1‖ * ‖edge.2.1 - edge.2.2‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ 2 * (‖edge.2.1‖ + ‖edge.2.2‖) := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ 2 * (5 + 5) := by gcongr
      _ = 20 := by norm_num
  exact ⟨by linarith [abs_le.mp hdot], by linarith [abs_le.mp hdot]⟩

/-- The dot set inherits the AD bound from the paper's `A_tilde`. -/
theorem PureWZ2AnchoredTheorem22ReadyGraph.dot_difference_ad
    {delta rho sigma theoremEta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    {sharp : PureWZ2AnchoredSharpGeometry finiteGraph}
    (data : PureWZ2AnchoredTheorem22ReadyGraph
      (theoremEta := theoremEta) sharp)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    IsADSet1 (wz1DotDifferenceSet data.common.H)
      (Real.sqrt rho / (25 * Real.sqrt 3)) (1 - sigma)
      ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) * C) :=
  (data.A_tilde_ad hsigma hsigmaOne).mono data.dot_product_subset_A_tilde

/--
Invoke the formal WZ1 Theorem 5.2 dichotomy and exclude its dot-product
alternative by the preceding `A_tilde` AD estimate.

`projection` is a pre-runtime parameter schedule constructed by
`pureWZ2_sourceHorizontal_projection_threshold`; it is not an
`AlternativeAProjectionInput` callback.
-/
theorem PureWZ2AnchoredTheorem22ReadyGraph.theorem52_line_alternative
    {delta rho sigma outputLoss sourceScale inputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    {sharp : PureWZ2AnchoredSharpGeometry finiteGraph}
    (projection : PureWZ2SourceHorizontalProjectionThreshold sigma outputLoss)
    (data : PureWZ2AnchoredTheorem22ReadyGraph
      (theoremEta := projection.theoremEta) sharp)
    (houtput : 0 < outputLoss) (houtputOne : outputLoss < 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (houtputSigma : outputLoss / 2 < sigma)
    {sourceCostLoss : ℝ}
    (hCbound :
      C ≤ 10 * Kakeya.realRpowENN sourceScale (-inputLoss))
    (hsourceCost :
      Kakeya.realRpowENN sourceScale (-inputLoss) ≤
        Kakeya.realRpowENN data.ready.deltaGraph (-sourceCostLoss))
    (hsourceCostLoss : 0 ≤ sourceCostLoss)
    (hsourceCostCeiling :
      sourceCostLoss ≤ projection.sourceCostLossCeiling)
    (hdeltaSmall : data.ready.deltaGraph ≤ projection.reductionDelta₀)
    (hconstantSmall :
      (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN data.ready.deltaGraph
          (-(projection.projectionEta * (sigma - outputLoss / 2) -
            (10 * projection.theoremEta + sourceCostLoss)) / 2)) :
    PureWZ2AnchoredAlternativeAProjectionInput data outputLoss := by
  have hcommon : data.common.G₂ = data.common.G₁ := by
    rw [data.common.G₂_eq, data.common.G₁_eq]
  rcases projection.reduction data.ready hdeltaSmall hcommon with hA | hlong
  · exact hA
  · rcases hlong with ⟨strongLong⟩
    exfalso
    let Cdot : ENNReal := (16200 : ENNReal) *
      ENNReal.ofReal (Real.sqrt 3) *
        (10 * Kakeya.realRpowENN sourceScale (-inputLoss))
    have hAD : IsADSet1 (wz1DotDifferenceSet data.common.H)
        (Real.sqrt rho / (25 * Real.sqrt 3)) (1 - sigma) Cdot := by
      apply (data.dot_difference_ad hsigma hsigmaOne).mono_constant
      dsimp only [Cdot]
      gcongr
    have hCdotTop : Cdot ≠ ⊤ := by
      dsimp only [Cdot]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        (ENNReal.mul_ne_top (by norm_num)
          (by simp [Kakeya.realRpowENN]))
    have hdeltaAD :
        Real.sqrt rho / (25 * Real.sqrt 3) =
          data.ready.deltaGraph / 5 := by
      rw [data.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale]
      ring
    have hdeltaGraphOne : data.ready.deltaGraph ≤ 1 := by
      rw [data.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale]
      have hsqrt := Real.sqrt_le_one.mpr input.rho_le_one
      have hdenom : 1 ≤ 5 * Real.sqrt 3 := by
        have hsqrt3 : 1 ≤ Real.sqrt 3 :=
          (Real.one_le_sqrt).2 (by norm_num)
        nlinarith
      exact (div_le_self (Real.sqrt_nonneg rho) hdenom).trans hsqrt
    have hdeltaGraphStrict : data.ready.deltaGraph < 1 := by
      have hsqrt3 : 1 ≤ Real.sqrt 3 :=
        (Real.one_le_sqrt).2 (by norm_num)
      have hdenom : 1 < 5 * Real.sqrt 3 := by nlinarith
      rw [data.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale]
      have hsqrtPos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr input.rho_pos
      calc
        Real.sqrt rho / (5 * Real.sqrt 3) < Real.sqrt rho :=
          div_lt_self hsqrtPos hdenom
        _ ≤ 1 := Real.sqrt_le_one.mpr input.rho_le_one
    have hscaledOne : strongLong.long.affine.dotScale *
        (Real.sqrt rho / (25 * Real.sqrt 3)) ≤ 1 :=
      strongLong.scaled_dotAD_le_one hdeltaAD
        projection.theoremEta_pos.le
        projection.theoremEta_small hdeltaGraphOne
    have hgain : 10 * projection.theoremEta + sourceCostLoss <
        projection.projectionEta * (sigma - outputLoss / 2) := by
      calc
        10 * projection.theoremEta + sourceCostLoss ≤
            10 * projection.theoremEta +
              projection.sourceCostLossCeiling := by gcongr
        _ < projection.projectionEta * (sigma - outputLoss / 2) :=
          projection.gain
    have hconstant := strongLong.constant_absorb hdeltaAD
      projection.theoremEta_pos.le hdeltaGraphOne hsourceCost hsourceCostLoss
      hgain hdeltaGraphStrict hconstantSmall
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
    exact strongLong.long.false_of_dot_ad hAD hCdotTop hsigma hsigmaOne
      (by positivity) houtputSigma hscaledOne htargetPos htargetOne
      htargetStrict hconstant

/-- The exact Step-4/5 objects and the surviving affine line alternative. -/
structure PureWZ2AnchoredTheorem52LineData
    {delta rho sigma theoremEta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    {sharp : PureWZ2AnchoredSharpGeometry finiteGraph}
    (ready : PureWZ2AnchoredTheorem22ReadyGraph
      (theoremEta := theoremEta) sharp)
    (epsilon : ℝ) where
  z₀ : ℝ := wz1Lemma23SnappedBaseHeight rho sharp.sharp.baseHeightIndex
  z₀_eq :
    z₀ = wz1Lemma23SnappedBaseHeight rho sharp.sharp.baseHeightIndex
  w : ℝ := (sharp.sharp.baseGlobalBin : ℝ) * rho
  w_eq : w = (sharp.sharp.baseGlobalBin : ℝ) * rho
  skewMap : Point3 → Point3 :=
    wz1Lemma23SkewPoint z₀ prep.windowed.global.extendedSlope
      sharp.sharp.selectedLocal.g
  skewMap_eq :
    skewMap =
      wz1Lemma23SkewPoint z₀ prep.windowed.global.extendedSlope
        sharp.sharp.selectedLocal.g
  F : DiscreteSet 2 := sharp.sharp.actual.F
  G₁ : DiscreteSet 2 := sharp.sharp.actual.G₁
  G₂ : DiscreteSet 2 := sharp.sharp.actual.G₂
  H : Finset (Point2 × Point2 × Point2) := sharp.sharp.actual.H
  A : Finset ℝ := wz1Lemma23SnappedBaseSliceValues rho
    prep.windowed.global.extendedSlope finiteGraph.graph.residue.cells
    sharp.sharp.baseHeightIndex sharp.sharp.baseGlobalBin
  dot_product_in_A :
    wz1DotDifferenceSet H ⊆ Metric.cthickening (4 * rho) (A : Set ℝ)
  A_normalized : Finset ℝ := sharp.sharp.normalized.values
  normalized_dot_product_near_A :
    wz1DotDifferenceSet sharp.sharp.normalized.H ⊆
      Metric.cthickening (4 * Real.sqrt rho) (A_normalized : Set ℝ)
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
  graphCell : Point2 → (ℤ × ℤ × ℤ) := fun point =>
    (pathFor point).2.1
  graphCell_eq : ∀ point,
    graphCell point = (pathFor point).2.1
  graphCell_mem_residue : ∀ point ∈ richF,
    graphCell point ∈ finiteGraph.graph.residue.cells
  point_eq : ∀ point ∈ richF,
    point = wz1Lemma23UnitBallPoint
      ((1 / Real.sqrt rho) •
        wz1Lemma23SnappedHeightPoint rho
          prep.windowed.global.extendedSlope
          sharp.sharp.baseHeightIndex (pathFor point).2.1)
  sourceHeight : Point2 → ℝ := fun point =>
    (wz1Lemma23SnappedPoint rho (pathFor point).2.1) 2
  sourceHeight_eq : ∀ point,
    sourceHeight point =
      (wz1Lemma23SnappedPoint rho (graphCell point)) 2
  sourceHeight_injective : Set.InjOn sourceHeight richF
  sourceHeight_fiber_card : ∀ height,
    (richF.filter fun point => sourceHeight point = height).card ≤ 1
  Z_lin : Finset ℝ := richF.image sourceHeight
  Z_lin_eq : Z_lin = richF.image sourceHeight
  Z_lin_nonempty : Z_lin.Nonempty
  Z_lin_card : Z_lin.card = richF.card
  Z_lin_intervals : Set ℝ :=
    ⋃ z ∈ (Z_lin : Set ℝ), Set.Icc (z - rho / 2) (z + rho / 2)
  Z_lin_intervals_eq :
    Z_lin_intervals =
      ⋃ z ∈ (Z_lin : Set ℝ), Set.Icc (z - rho / 2) (z + rho / 2)
  L_S_slope : ℝ
  L_S_intercept : ℝ
  L_S : ℝ → ℝ := fun z => L_S_slope * z + L_S_intercept
  L_S_eq : L_S = fun z => L_S_slope * z + L_S_intercept
  L_S_slope_bound : |L_S_slope| ≤ 2
  L_S_approximation_sharp :
    ∀ point ∈ richF,
      |prep.windowed.global.extendedSlope (sourceHeight point) -
          L_S (sourceHeight point)| ≤ 3 * rho
  L_S_approximation :
    ∀ point ∈ richF,
      |prep.windowed.global.extendedSlope (sourceHeight point) -
          L_S (sourceHeight point)| ≤ 5 * rho

/--
Turn the line alternative returned by formal WZ1 Theorem 5.2 into the actual
selected source heights `Z_lin` and an affine function `L_S`.  The set
`Z_lin_intervals` is the union of the complete side-`rho` height intervals
centered at those graph heights.
-/
theorem PureWZ2AnchoredTheorem22ReadyGraph.lineData
    {delta rho sigma theoremEta epsilon : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    {sharp : PureWZ2AnchoredSharpGeometry finiteGraph}
    (ready : PureWZ2AnchoredTheorem22ReadyGraph
      (theoremEta := theoremEta) sharp)
    (hA : PureWZ2AnchoredAlternativeAProjectionInput ready epsilon) :
    Nonempty (PureWZ2AnchoredTheorem52LineData ready epsilon) := by
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
          ((1 / Real.sqrt rho) •
            wz1Lemma23SnappedHeightPoint rho
              prep.windowed.global.extendedSlope
              sharp.sharp.baseHeightIndex path.2.1) := by
    intro point hpoint
    have hcommon : point ∈ ready.common.F :=
      (Finset.mem_filter.mp hpoint).1
    rw [ready.common.F_eq] at hcommon
    rcases Finset.mem_image.mp hcommon with
      ⟨normalizedPoint, hnormalizedPoint, hpointEq⟩
    rw [sharp.sharp.normalized.F_eq,
      sharp.sharp.normalized_sourceF, sharp.sharp.actual.F_eq]
      at hnormalizedPoint
    rcases Finset.mem_image.mp hnormalizedPoint with
      ⟨sourcePoint, hsourcePoint, hnormalizedEq⟩
    rcases Finset.mem_image.mp hsourcePoint with
      ⟨path, hpath, hsourceEq⟩
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
  have hgraphCellMem : ∀ point (hpoint : point ∈ richF),
      (pathFor point).2.1 ∈ finiteGraph.graph.residue.cells := by
    intro point hpoint
    have hpath := hpathMem point hpoint
    rw [sharp.sharp.actual.cycles_eq] at hpath
    have hfour := (Finset.mem_filter.mp hpath).1
    have hrelations :
        (pathFor point).1 ∈ finiteGraph.graph.residue.cells ∧
          (pathFor point).2.1 ∈ finiteGraph.graph.residue.cells ∧
          (pathFor point).2.2.1 ∈ finiteGraph.graph.residue.cells ∧
          (pathFor point).2.2.2 ∈ finiteGraph.graph.residue.cells := by
      simpa [wz1Lemma23FourCycles, Finset.mem_product] using
        (Finset.mem_filter.mp hfour).1
    exact hrelations.2.1
  have hpointEq : ∀ point (hpoint : point ∈ richF),
      point = wz1Lemma23UnitBallPoint
        ((1 / Real.sqrt rho) •
          wz1Lemma23SnappedHeightPoint rho
            prep.windowed.global.extendedSlope
            sharp.sharp.baseHeightIndex (pathFor point).2.1) := by
    intro point hpoint
    simp only [pathFor, dif_pos hpoint]
    exact (Classical.choose_spec (hpathExists point hpoint)).2
  have hcenteredStrip : ∀ point (hpoint : point ∈ richF),
      let baseHeight :=
        wz1Lemma23SnappedBaseHeight rho sharp.sharp.baseHeightIndex
      let cell := (pathFor point).2.1
      let centeredHeight := (wz1Lemma23SnappedPoint rho cell) 2 - baseHeight
      |direction 0 * centeredHeight +
        direction 1 *
          wz1Lemma23CenteredSlope baseHeight
            prep.windowed.global.extendedSlope centeredHeight| ≤
        rho / Real.sqrt 3 := by
    intro point hpoint
    have hline := (Finset.mem_filter.mp hpoint).2
    rw [wz1LineNeighborhood] at hline
    rw [hpointEq point hpoint] at hline
    have hperp : wz1Perp2 (wz1Perp2 direction) = -direction := by
      ext coordinate
      fin_cases coordinate <;>
        simp [wz1Perp2, EuclideanSpace.single]
    rw [hperp] at hline
    have hsqrt : 0 < Real.sqrt rho := Real.sqrt_pos.mpr input.rho_pos
    change
      |inner ℝ
          (wz1Lemma23UnitBallPoint
            ((1 / Real.sqrt rho) •
              wz1Lemma23SnappedHeightPoint rho
                prep.windowed.global.extendedSlope
                sharp.sharp.baseHeightIndex (pathFor point).2.1) - 0)
          (-direction)| ≤ ready.ready.deltaGraph at hline
    simp only [sub_zero, inner_neg_right, abs_neg] at hline
    have hscaled :
        |inner ℝ
            (wz1Lemma23SnappedHeightPoint rho
              prep.windowed.global.extendedSlope
              sharp.sharp.baseHeightIndex (pathFor point).2.1) direction| ≤
          5 * Real.sqrt rho * ready.ready.deltaGraph := by
      have hformula :
          inner ℝ
              (wz1Lemma23UnitBallPoint
                ((1 / Real.sqrt rho) •
                  wz1Lemma23SnappedHeightPoint rho
                    prep.windowed.global.extendedSlope
                    sharp.sharp.baseHeightIndex (pathFor point).2.1))
              direction =
            (1 / (5 * Real.sqrt rho)) *
              inner ℝ
                (wz1Lemma23SnappedHeightPoint rho
                  prep.windowed.global.extendedSlope
                  sharp.sharp.baseHeightIndex (pathFor point).2.1)
                direction := by
        simp [wz1Lemma23UnitBallPoint, inner_smul_left]
        ring
      rw [hformula, abs_mul,
        abs_of_pos (by positivity : 0 < 1 / (5 * Real.sqrt rho))] at hline
      have hpos : 0 < 5 * Real.sqrt rho := by positivity
      have hdiv :
          |inner ℝ
              (wz1Lemma23SnappedHeightPoint rho
                prep.windowed.global.extendedSlope
                sharp.sharp.baseHeightIndex (pathFor point).2.1)
              direction| / (5 * Real.sqrt rho) ≤
            ready.ready.deltaGraph := by
        simpa [div_eq_mul_inv, mul_comm] using hline
      have hmul := (div_le_iff₀ hpos).mp hdiv
      simpa [mul_comm] using hmul
    rw [ready.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale] at hscaled
    have hscale :
        5 * Real.sqrt rho * (Real.sqrt rho / (5 * Real.sqrt 3)) =
          rho / Real.sqrt 3 := by
      field_simp [hsqrt.ne']
      nlinarith [Real.sq_sqrt input.rho_pos.le]
    rw [hscale] at hscaled
    simpa [wz1Lemma23SnappedHeightPoint, wz1Lemma23HeightGraphPoint,
      PiLp.inner_apply, Fin.sum_univ_succ, EuclideanSpace.single, point3]
      using hscaled
  let sourceHeight : Point2 → ℝ := fun point =>
    (wz1Lemma23SnappedPoint rho (pathFor point).2.1) 2
  have hsourceHeightInjective : Set.InjOn sourceHeight richF := by
    intro first hfirst second hsecond heq
    have hheightIndex :
        (pathFor first).2.1.2.2 = (pathFor second).2.1.2.2 := by
      dsimp only [sourceHeight] at heq
      simp [wz1Lemma23SnappedPoint, wz1Lemma23CellCenter, point3] at heq
      rcases heq with hindex | hside
      · exact hindex
      · exfalso
        have hsidePos : 0 < gridSide (rho / 2) := by
          unfold gridSide
          exact div_pos
            (mul_pos (by norm_num) (half_pos input.rho_pos))
            (Real.sqrt_pos.mpr (by norm_num))
        exact hsidePos.ne' hside
    have hheight :
        (wz1Lemma23SnappedPoint rho (pathFor first).2.1) 2 =
          (wz1Lemma23SnappedPoint rho (pathFor second).2.1) 2 := by
      simp [wz1Lemma23SnappedPoint, wz1Lemma23CellCenter, point3,
        hheightIndex]
    have hsourcePoint :
        wz1Lemma23SnappedHeightPoint rho prep.windowed.global.extendedSlope
            sharp.sharp.baseHeightIndex (pathFor first).2.1 =
          wz1Lemma23SnappedHeightPoint rho prep.windowed.global.extendedSlope
            sharp.sharp.baseHeightIndex (pathFor second).2.1 := by
      simp [wz1Lemma23SnappedHeightPoint, wz1Lemma23HeightGraphPoint,
        hheight]
    rw [hpointEq first hfirst, hpointEq second hsecond, hsourcePoint]
  have hsourceHeightFiber : ∀ height,
      (richF.filter fun point => sourceHeight point = height).card ≤ 1 := by
    intro height
    apply Finset.card_le_one.mpr
    intro first hfirst second hsecond
    exact hsourceHeightInjective
      (Finset.mem_filter.mp hfirst).1
      (Finset.mem_filter.mp hsecond).1
      ((Finset.mem_filter.mp hfirst).2.trans
        (Finset.mem_filter.mp hsecond).2.symm)
  let Z_lin := richF.image sourceHeight
  have hZNonempty : Z_lin.Nonempty :=
    Finset.Nonempty.image hrichNonempty sourceHeight
  have hZCard : Z_lin.card = richF.card :=
    Finset.card_image_of_injOn hsourceHeightInjective
  let baseHeight :=
    wz1Lemma23SnappedBaseHeight rho sharp.sharp.baseHeightIndex
  have hcenteredLipschitz :
      ∀ first second,
        |wz1Lemma23CenteredSlope baseHeight
              prep.windowed.global.extendedSlope first -
            wz1Lemma23CenteredSlope baseHeight
              prep.windowed.global.extendedSlope second| ≤
          |first - second| := by
    intro first second
    dsimp only [wz1Lemma23CenteredSlope]
    have h := prep.windowed.global.extendedSlope_lipschitz.dist_le_mul
      (first + baseHeight) (by simp) (second + baseHeight) (by simp)
    simpa [Real.dist_eq] using h
  by_cases hnonvertical : 1 / Real.sqrt 5 ≤ |direction 1|
  · let lineSlope := -(direction 0 / direction 1)
    let lineIntercept :=
      prep.windowed.global.extendedSlope baseHeight - lineSlope * baseHeight
    let L_S : ℝ → ℝ := fun z => lineSlope * z + lineIntercept
    have hslope : |lineSlope| ≤ 2 := by
      simpa only [lineSlope, neg_div, abs_neg] using
        slope_bound_from_direction direction hdirection hnonvertical
    have happSharp : ∀ point ∈ richF,
        |prep.windowed.global.extendedSlope (sourceHeight point) -
            L_S (sourceHeight point)| ≤ 3 * rho := by
      intro point hpoint
      let centered := sourceHeight point - baseHeight
      have hstrip := hcenteredStrip point hpoint
      dsimp only at hstrip
      have hinside :
          prep.windowed.global.extendedSlope (sourceHeight point) -
                L_S (sourceHeight point) =
            (prep.windowed.global.extendedSlope (centered + baseHeight) -
                prep.windowed.global.extendedSlope baseHeight) -
              lineSlope * centered := by
        dsimp only [L_S, lineIntercept]
        have hcentered :
            centered + baseHeight = sourceHeight point := by
          dsimp only [centered]
          ring
        rw [hcentered]
        ring
      rw [hinside]
      have hdirectionOnePos : 0 < |direction 1| :=
        lt_of_lt_of_le (by positivity : 0 < 1 / Real.sqrt 5) hnonvertical
      have hquotient :
          |(prep.windowed.global.extendedSlope (centered + baseHeight) -
                prep.windowed.global.extendedSlope baseHeight) -
              lineSlope * centered| =
            |direction 0 * centered + direction 1 *
                wz1Lemma23CenteredSlope baseHeight
                  prep.windowed.global.extendedSlope centered| /
              |direction 1| := by
        dsimp only [lineSlope, wz1Lemma23CenteredSlope]
        have hdirectionOne : direction 1 ≠ 0 :=
          abs_pos.mp hdirectionOnePos
        rw [show centered + baseHeight = sourceHeight point by
          dsimp only [centered]
          ring]
        have halgebra :
            prep.windowed.global.extendedSlope (sourceHeight point) -
                  prep.windowed.global.extendedSlope baseHeight -
                -(direction 0 / direction 1) * centered =
              (direction 0 * centered + direction 1 *
                  (prep.windowed.global.extendedSlope (sourceHeight point) -
                    prep.windowed.global.extendedSlope baseHeight)) /
                direction 1 := by
          field_simp [hdirectionOne]
          ring
        rw [halgebra, abs_div]
      rw [hquotient]
      have hratio :
          (rho / Real.sqrt 3) / |direction 1| ≤
            (rho / Real.sqrt 3) / (1 / Real.sqrt 5) :=
        div_le_div_of_nonneg_left
          (div_nonneg input.rho_pos.le (Real.sqrt_nonneg 3))
          (by positivity) hnonvertical
      have hsqrt : Real.sqrt 5 ≤ 3 * Real.sqrt 3 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
          Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (3 : ℝ)]
      calc
        _ ≤ (rho / Real.sqrt 3) / |direction 1| :=
          div_le_div_of_nonneg_right hstrip hdirectionOnePos.le
        _ ≤ (rho / Real.sqrt 3) / (1 / Real.sqrt 5) := hratio
        _ = rho * (Real.sqrt 5 / Real.sqrt 3) := by field_simp
        _ ≤ rho * 3 := by
          exact mul_le_mul_of_nonneg_left
            ((div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))).2 hsqrt)
            input.rho_pos.le
        _ = 3 * rho := by ring
    have happ : ∀ point ∈ richF,
        |prep.windowed.global.extendedSlope (sourceHeight point) -
            L_S (sourceHeight point)| ≤ 5 * rho := by
      intro point hpoint
      exact (happSharp point hpoint).trans (by
        nlinarith [input.rho_pos])
    exact ⟨{
      z₀ := baseHeight
      z₀_eq := rfl
      w := (sharp.sharp.baseGlobalBin : ℝ) * rho
      w_eq := rfl
      skewMap := wz1Lemma23SkewPoint baseHeight
        prep.windowed.global.extendedSlope sharp.sharp.selectedLocal.g
      skewMap_eq := rfl
      F := sharp.sharp.actual.F
      G₁ := sharp.sharp.actual.G₁
      G₂ := sharp.sharp.actual.G₂
      H := sharp.sharp.actual.H
      A := wz1Lemma23SnappedBaseSliceValues rho
        prep.windowed.global.extendedSlope finiteGraph.graph.residue.cells
        sharp.sharp.baseHeightIndex sharp.sharp.baseGlobalBin
      dot_product_in_A := sharp.sharp.actual.dot_containment
      A_normalized := sharp.sharp.normalized.values
      normalized_dot_product_near_A :=
        sharp.sharp.normalized.dot_containment
      direction := direction
      direction_unit := hdirection
      richF := richF
      richF_eq := rfl
      richF_nonempty := hrichNonempty
      richF_card := hrichCard
      pathFor := pathFor
      path_mem := hpathMem
      graphCell := fun point => (pathFor point).2.1
      graphCell_eq := fun _ => rfl
      graphCell_mem_residue := hgraphCellMem
      point_eq := hpointEq
      sourceHeight := sourceHeight
      sourceHeight_eq := fun _ => rfl
      sourceHeight_injective := hsourceHeightInjective
      sourceHeight_fiber_card := hsourceHeightFiber
      Z_lin := Z_lin
      Z_lin_eq := rfl
      Z_lin_nonempty := hZNonempty
      Z_lin_card := hZCard
      Z_lin_intervals :=
        ⋃ z ∈ (Z_lin : Set ℝ), Set.Icc (z - rho / 2) (z + rho / 2)
      Z_lin_intervals_eq := rfl
      L_S_slope := lineSlope
      L_S_intercept := lineIntercept
      L_S := L_S
      L_S_eq := rfl
      L_S_slope_bound := hslope
      L_S_approximation_sharp := happSharp
      L_S_approximation := happ
    }⟩
  · have hvertical : |direction 1| < 1 / Real.sqrt 5 :=
      lt_of_not_ge hnonvertical
    let basePoint := Classical.choose hrichNonempty
    have hbasePoint : basePoint ∈ richF :=
      Classical.choose_spec hrichNonempty
    let baseSourceHeight := sourceHeight basePoint
    let baseCentered := baseSourceHeight - baseHeight
    let lineSlope : ℝ := 0
    let lineIntercept := prep.windowed.global.extendedSlope baseSourceHeight
    let L_S : ℝ → ℝ := fun z => lineSlope * z + lineIntercept
    have hslope : |lineSlope| ≤ 2 := by simp [lineSlope]
    have hgap :
        1 / Real.sqrt 5 ≤ |direction 0| - |direction 1| :=
      near_vertical_gap direction hdirection hvertical
    have happSharp : ∀ point ∈ richF,
        |prep.windowed.global.extendedSlope (sourceHeight point) -
            L_S (sourceHeight point)| ≤ 3 * rho := by
      intro point hpoint
      let centered := sourceHeight point - baseHeight
      have hstrip := hcenteredStrip point hpoint
      have hbaseStrip := hcenteredStrip basePoint hbasePoint
      dsimp only at hstrip hbaseStrip
      have hconstThree :
          2 * (1 / (3 * Real.sqrt 3)) / (1 / Real.sqrt 5) ≤ 1 := by
        have hsqrt : 2 * Real.sqrt 5 ≤ 3 * Real.sqrt 3 := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
            Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
            Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (3 : ℝ)]
        have hdenom : 0 < 3 * Real.sqrt 3 := by positivity
        rw [show 2 * (1 / (3 * Real.sqrt 3)) / (1 / Real.sqrt 5) =
          2 * Real.sqrt 5 / (3 * Real.sqrt 3) by field_simp]
        exact (div_le_one hdenom).2 hsqrt
      have hstripThree :
          |direction 0 * centered + direction 1 *
              wz1Lemma23CenteredSlope baseHeight
                prep.windowed.global.extendedSlope centered| ≤
            (1 / (3 * Real.sqrt 3)) * (3 * rho) := by
        convert hstrip using 1 <;> ring
      have hbaseStripThree :
          |direction 0 * baseCentered + direction 1 *
              wz1Lemma23CenteredSlope baseHeight
                prep.windowed.global.extendedSlope baseCentered| ≤
            (1 / (3 * Real.sqrt 3)) * (3 * rho) := by
        convert hbaseStrip using 1 <;> ring
      have happrox := constant_approximation_near_vertical direction
        (3 * rho) (1 / (3 * Real.sqrt 3)) (1 / Real.sqrt 5)
        (mul_pos (by norm_num) input.rho_pos) (by positivity)
        (wz1Lemma23CenteredSlope baseHeight
          prep.windowed.global.extendedSlope)
        hcenteredLipschitz hgap hconstThree baseCentered centered
        hbaseStripThree hstripThree
      dsimp only [wz1Lemma23CenteredSlope] at happrox
      have hcenteredEq :
          centered + baseHeight = sourceHeight point := by
        dsimp only [centered]
        ring
      have hbaseCenteredEq :
          baseCentered + baseHeight = baseSourceHeight := by
        dsimp only [baseCentered]
        ring
      rw [hcenteredEq, hbaseCenteredEq] at happrox
      simpa [L_S, lineSlope, lineIntercept] using happrox
    have happ : ∀ point ∈ richF,
        |prep.windowed.global.extendedSlope (sourceHeight point) -
            L_S (sourceHeight point)| ≤ 5 * rho := by
      intro point hpoint
      exact (happSharp point hpoint).trans (by
        nlinarith [input.rho_pos])
    exact ⟨{
      z₀ := baseHeight
      z₀_eq := rfl
      w := (sharp.sharp.baseGlobalBin : ℝ) * rho
      w_eq := rfl
      skewMap := wz1Lemma23SkewPoint baseHeight
        prep.windowed.global.extendedSlope sharp.sharp.selectedLocal.g
      skewMap_eq := rfl
      F := sharp.sharp.actual.F
      G₁ := sharp.sharp.actual.G₁
      G₂ := sharp.sharp.actual.G₂
      H := sharp.sharp.actual.H
      A := wz1Lemma23SnappedBaseSliceValues rho
        prep.windowed.global.extendedSlope finiteGraph.graph.residue.cells
        sharp.sharp.baseHeightIndex sharp.sharp.baseGlobalBin
      dot_product_in_A := sharp.sharp.actual.dot_containment
      A_normalized := sharp.sharp.normalized.values
      normalized_dot_product_near_A :=
        sharp.sharp.normalized.dot_containment
      direction := direction
      direction_unit := hdirection
      richF := richF
      richF_eq := rfl
      richF_nonempty := hrichNonempty
      richF_card := hrichCard
      pathFor := pathFor
      path_mem := hpathMem
      graphCell := fun point => (pathFor point).2.1
      graphCell_eq := fun _ => rfl
      graphCell_mem_residue := hgraphCellMem
      point_eq := hpointEq
      sourceHeight := sourceHeight
      sourceHeight_eq := fun _ => rfl
      sourceHeight_injective := hsourceHeightInjective
      sourceHeight_fiber_card := hsourceHeightFiber
      Z_lin := Z_lin
      Z_lin_eq := rfl
      Z_lin_nonempty := hZNonempty
      Z_lin_card := hZCard
      Z_lin_intervals :=
        ⋃ z ∈ (Z_lin : Set ℝ), Set.Icc (z - rho / 2) (z + rho / 2)
      Z_lin_intervals_eq := rfl
      L_S_slope := lineSlope
      L_S_intercept := lineIntercept
      L_S := L_S
      L_S_eq := rfl
      L_S_slope_bound := hslope
      L_S_approximation_sharp := happSharp
      L_S_approximation := happ
    }⟩

/-- Complete same-witness output of the anchored Step-4/5 argument. -/
structure PureWZ2AnchoredTheorem52Output
    {delta rho sigma outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C prep.windowed.global.cells}
    (finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins)
    (projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma outputLoss) where
  sharp : PureWZ2AnchoredSharpGeometry finiteGraph
  ready : PureWZ2AnchoredTheorem22ReadyGraph
    (theoremEta := projection.theoremEta) sharp
  A_tilde : Set ℝ := ready.A_tilde
  A_tilde_ad :
    IsADSet1 A_tilde
      (Real.sqrt rho / (25 * Real.sqrt 3)) (1 - sigma)
      ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) * C)
  dot_product_in_A_tilde :
    wz1DotDifferenceSet ready.common.H ⊆ A_tilde
  lineAlternative : PureWZ2AnchoredAlternativeAProjectionInput
    ready outputLoss
  lineData : PureWZ2AnchoredTheorem52LineData ready outputLoss

/--
Construction-specific P3 receipt restoring the side-`rho` source provenance
which the construction-independent graph-preparation ABI intentionally
forgets.

No graph or Theorem-5.2 choice is rerun here.  `blockIndex` is definitionally
the original anchored block index, every graph witness is the representative
of the residue cell already selected by `output.lineData`, and every source
cell is recovered through the exact `rhoShadow.shadow_union` /
`separated.pullback.region_eq` chain.  `completeSourceCells` retains whole
height fibres of the original pre-bin, so its pullback exposes literal
balanced-cover volume and indexed-mass identities.
-/
structure PureWZ2AnchoredTheorem52BlockProvenance
    {sigma inputLoss delta coarseLoss fineLoss outputLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex :
      {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices}}
    {data : PureWZ2AnchoredPreBinRhoHeightRegularizedData selected heightIndex}
    {B₀ threshold : ENNReal} {K : ℕ}
    {block : PureWZ2AnchoredIntegratedCommonBinReceipt data B₀ threshold K}
    {weighted : PureWZ2AnchoredWeightedParentData
      (coarseLoss := coarseLoss) (fineLoss := fineLoss) block}
    {separated : PureWZ2AnchoredSeparatedShadingData weighted}
    (rhoShadow : PureWZ2AnchoredRhoShadowData separated)
    {C : ENNReal}
    (hsourceAbsorb : Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN rhoRequested.1 (-coarseLoss))
    (hCAbsorb : Kakeya.realRpowENN rhoRequested.1 (-coarseLoss) ≤ C)
    (hCTop : C ≠ ⊤)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : 256 * rhoRequested.1 ≤ 1)
    {prep : PureWZ2AnchoredGraphPreparationData
      (rhoShadow.toGlobalInput C hsourceAbsorb hCAbsorb hCTop
        hbridge hgraphOne)}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := 256 * rhoRequested.1) (sigma := sigma) (10 * C)
      prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma outputLoss}
    (output : PureWZ2AnchoredTheorem52Output finiteGraph projection) where
  blockIndex :
    {index // index ∈ selected.standardSqrtSlabIndices} := heightIndex
  blockIndex_eq : blockIndex = heightIndex
  graphWitness :
    {point // point ∈ output.lineData.richF} → Point3
  graphWitness_mem_shadow : ∀ point,
    graphWitness point ∈ rhoShadow.shadow.union
  graphWitness_index : ∀ point,
    wz1Lemma23CellIndex (256 * rhoRequested.1) (graphWitness point) =
      output.lineData.graphCell point.1
  sourceCell :
    {point // point ∈ output.lineData.richF} → (ℤ × ℤ × ℤ)
  sourceCell_mem_weighted : ∀ point,
    sourceCell point ∈ weighted.selectedCells
  sourceCell_mem_block : ∀ point, sourceCell point ∈ block.cells
  sourceCell_mem_preBin : ∀ point, sourceCell point ∈ data.cells
  sourceCell_mem_balanced : ∀ point,
    sourceCell point ∈ selected.selectedCells
  graphWitness_mem_sourceCell : ∀ point,
    graphWitness point ∈
      wz1PaperGridCube rhoRequested.1 (sourceCell point)
  sourceHeight_eq_graphCell : ∀ point :
      {point // point ∈ output.lineData.richF},
    output.lineData.sourceHeight point.1 =
      (wz1Lemma23SnappedPoint (256 * rhoRequested.1)
        (output.lineData.graphCell point.1)) 2
  sourceHeight_injective :
    Set.InjOn output.lineData.sourceHeight output.lineData.richF
  sourceHeight_fiber_card : ∀ height,
    (output.lineData.richF.filter fun point =>
      output.lineData.sourceHeight point = height).card ≤ 1
  sourceHeightIndices : Finset ℤ :=
    output.lineData.richF.attach.image fun point =>
      (sourceCell point).2.2
  sourceHeightIndices_eq :
    sourceHeightIndices =
      output.lineData.richF.attach.image fun point =>
        (sourceCell point).2.2
  sourceHeightIndices_subset :
    sourceHeightIndices ⊆ data.uniform.heightIndices
  completeSourceCells : Finset (ℤ × ℤ × ℤ) :=
    data.cells.filter fun cell => cell.2.2 ∈ sourceHeightIndices
  completeSourceCells_eq :
    completeSourceCells =
      data.cells.filter fun cell => cell.2.2 ∈ sourceHeightIndices
  completeSourceCells_subset_preBin :
    completeSourceCells ⊆ data.cells
  completeSourceCells_subset_balanced :
    completeSourceCells ⊆ selected.selectedCells
  completeSourceCells_card_retention :
    sourceHeightIndices.card * data.cells.card ≤
      2 * data.uniform.heightIndices.card * completeSourceCells.card
  sourcePullback :
    PureWZ2AnchoredSelectedCellSourcePullback selected completeSourceCells
  sourcePullback_region_eq :
    sourcePullback.region =
      ⋃ cell ∈ completeSourceCells,
        wz1PaperGridCube rhoRequested.1 cell
  sourcePullback_volume_eq :
    volume sourcePullback.shading.union =
      (completeSourceCells.card : ENNReal) * coarse.balanced.cellMass
  sourcePullback_mass_eq :
    sourcePullback.shading.mass =
      (completeSourceCells.card : ENNReal) *
        coarse.balanced.incidenceMass

/--
Recover the original anchored block provenance from an already constructed
Theorem-5.2 output.  This is only a dependent projection/selection from
existing witnesses; in particular it does not invoke `theorem52`.
-/
theorem PureWZ2AnchoredTheorem52Output.blockProvenance
    {sigma inputLoss delta coarseLoss fineLoss outputLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex :
      {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices}}
    {data : PureWZ2AnchoredPreBinRhoHeightRegularizedData selected heightIndex}
    {B₀ threshold : ENNReal} {K : ℕ}
    {block : PureWZ2AnchoredIntegratedCommonBinReceipt data B₀ threshold K}
    {weighted : PureWZ2AnchoredWeightedParentData
      (coarseLoss := coarseLoss) (fineLoss := fineLoss) block}
    {separated : PureWZ2AnchoredSeparatedShadingData weighted}
    (rhoShadow : PureWZ2AnchoredRhoShadowData separated)
    {C : ENNReal}
    (hsourceAbsorb : Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN rhoRequested.1 (-coarseLoss))
    (hCAbsorb : Kakeya.realRpowENN rhoRequested.1 (-coarseLoss) ≤ C)
    (hCTop : C ≠ ⊤)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : 256 * rhoRequested.1 ≤ 1)
    {prep : PureWZ2AnchoredGraphPreparationData
      (rhoShadow.toGlobalInput C hsourceAbsorb hCAbsorb hCTop
        hbridge hgraphOne)}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := 256 * rhoRequested.1) (sigma := sigma) (10 * C)
      prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma outputLoss}
    (output : PureWZ2AnchoredTheorem52Output finiteGraph projection) :
    Nonempty (PureWZ2AnchoredTheorem52BlockProvenance
      rhoShadow hsourceAbsorb hCAbsorb hCTop hbridge hgraphOne output) := by
  let graphWitness :
      {point // point ∈ output.lineData.richF} → Point3 := fun point =>
    wz1Lemma23CellRepresentative rhoShadow.shadow
      prep.windowed.global.rho_pos
      ⟨output.lineData.graphCell point.1,
        finiteGraph.graph.residue.cells_active
          (output.lineData.graphCell_mem_residue point.1 point.2)⟩
  have hgraphWitnessMem : ∀ point,
      graphWitness point ∈ rhoShadow.shadow.union := by
    intro point
    exact wz1Lemma23CellRepresentative_mem_union rhoShadow.shadow
      prep.windowed.global.rho_pos _
  have hgraphWitnessIndex : ∀ point,
      wz1Lemma23CellIndex (256 * rhoRequested.1) (graphWitness point) =
        output.lineData.graphCell point.1 := by
    intro point
    exact wz1Lemma23CellRepresentative_index rhoShadow.shadow
      prep.windowed.global.rho_pos _
  have hsourceExists : ∀ point,
      ∃ cell ∈ weighted.selectedCells,
        graphWitness point ∈ wz1PaperGridCube rhoRequested.1 cell := by
    intro point
    have hshadow := hgraphWitnessMem point
    rw [rhoShadow.shadow_union] at hshadow
    have hregion : graphWitness point ∈ separated.pullback.region := by
      rw [separated.pullback.union_eq] at hshadow
      exact hshadow.2
    rw [separated.region_eq, PureWZ2AnchoredWeightedParentData.selectedEnvelope,
      wz2RetainedCellsUnion] at hregion
    rcases Set.mem_iUnion₂.mp hregion with ⟨cell, hcell, hpointCell⟩
    exact ⟨cell, hcell, hpointCell⟩
  let sourceCell :
      {point // point ∈ output.lineData.richF} → (ℤ × ℤ × ℤ) :=
    fun point => Classical.choose (hsourceExists point)
  have hsourceCellMem : ∀ point,
      sourceCell point ∈ weighted.selectedCells := by
    intro point
    exact (Classical.choose_spec (hsourceExists point)).1
  have hsourceCellContains : ∀ point,
      graphWitness point ∈
        wz1PaperGridCube rhoRequested.1 (sourceCell point) := by
    intro point
    exact (Classical.choose_spec (hsourceExists point)).2
  have hsourceCellBlock : ∀ point, sourceCell point ∈ block.cells := by
    intro point
    exact weighted.selectedCells_subset (hsourceCellMem point)
  have hsourceCellPreBin : ∀ point, sourceCell point ∈ data.cells := by
    intro point
    exact block.envelope.cells_subset (hsourceCellBlock point)
  have hsourceCellBalanced : ∀ point,
      sourceCell point ∈ selected.selectedCells := by
    intro point
    exact data.cells_subset_selected (hsourceCellPreBin point)
  let sourceHeightIndices : Finset ℤ :=
    output.lineData.richF.attach.image fun point =>
      (sourceCell point).2.2
  have hheightSubset :
      sourceHeightIndices ⊆ data.uniform.heightIndices := by
    intro height hheight
    rcases Finset.mem_image.mp hheight with ⟨point, _hpoint, rfl⟩
    rw [data.uniform.heightIndices_eq]
    have hcell : sourceCell point ∈ data.uniform.cells := by
      rw [← data.cells_eq]
      exact hsourceCellPreBin point
    exact Finset.mem_image.mpr
      ⟨sourceCell point, hcell, rfl⟩
  let completeSourceCells : Finset (ℤ × ℤ × ℤ) :=
    data.cells.filter fun cell => cell.2.2 ∈ sourceHeightIndices
  have hcompletePreBin : completeSourceCells ⊆ data.cells :=
    Finset.filter_subset _ _
  have hcompleteBalanced :
      completeSourceCells ⊆ selected.selectedCells :=
    hcompletePreBin.trans data.cells_subset_selected
  have hretention :
      sourceHeightIndices.card * data.cells.card ≤
        2 * data.uniform.heightIndices.card * completeSourceCells.card := by
    dsimp only [completeSourceCells]
    rw [data.cells_eq]
    exact data.uniform.selected_height_card_lower
      sourceHeightIndices hheightSubset
  rcases selected.restrictCells completeSourceCells hcompleteBalanced with
    ⟨sourcePullback⟩
  exact ⟨{
    blockIndex := heightIndex
    blockIndex_eq := rfl
    graphWitness := graphWitness
    graphWitness_mem_shadow := hgraphWitnessMem
    graphWitness_index := hgraphWitnessIndex
    sourceCell := sourceCell
    sourceCell_mem_weighted := hsourceCellMem
    sourceCell_mem_block := hsourceCellBlock
    sourceCell_mem_preBin := hsourceCellPreBin
    sourceCell_mem_balanced := hsourceCellBalanced
    graphWitness_mem_sourceCell := hsourceCellContains
    sourceHeight_eq_graphCell := fun point =>
      output.lineData.sourceHeight_eq point.1
    sourceHeight_injective := output.lineData.sourceHeight_injective
    sourceHeight_fiber_card := output.lineData.sourceHeight_fiber_card
    sourceHeightIndices := sourceHeightIndices
    sourceHeightIndices_eq := rfl
    sourceHeightIndices_subset := hheightSubset
    completeSourceCells := completeSourceCells
    completeSourceCells_eq := rfl
    completeSourceCells_subset_preBin := hcompletePreBin
    completeSourceCells_subset_balanced := hcompleteBalanced
    completeSourceCells_card_retention := hretention
    sourcePullback := sourcePullback
    sourcePullback_region_eq := sourcePullback.region_eq
    sourcePullback_volume_eq := sourcePullback.volume_eq
    sourcePullback_mass_eq := sourcePullback.mass_eq
  }⟩

/-- The closed formal WZ1 Theorem 5.2 schedule used by the anchored lane. -/
theorem pureWZ2_anchored_theorem52_projection_schedule
    {sigma outputLoss : ℝ}
    (hsigma : 0 < sigma)
    (houtput : 0 < outputLoss)
    (houtputOne : outputLoss < 1)
    (houtputSigma : outputLoss / 2 < sigma) :
    Nonempty
      (PureWZ2SourceHorizontalProjectionThreshold sigma outputLoss) :=
  pureWZ2_sourceHorizontal_projection_threshold
    hsigma houtput houtputOne houtputSigma

/-- Execute Steps 4--5 from one already prepared anchored finite graph. -/
theorem PureWZ2AnchoredFiniteGraphData.theorem52
    {delta rho sigma outputLoss sourceScale inputLoss
      volumeLoss constantLoss extraLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C prep.windowed.global.cells}
    (finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins)
    (projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma outputLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (houtput : 0 < outputLoss) (houtputOne : outputLoss < 1)
    (houtputSigma : outputLoss / 2 < sigma)
    (hCOne : (1 : ENNReal) ≤ C)
    (hCpower : C.toReal ≤ Real.rpow rho (-constantLoss))
    (hvolume : ENNReal.ofReal
        (Real.rpow rho (1 + sigma / 2 + volumeLoss)) ≤ volume shadow.union)
    (hextraPower : (finiteGraph.graph.residue.extraCost : ℝ) ≤
      Real.rpow rho (-extraLoss))
    (hedgeAbsorb :
      Real.rpow (wz1Lemma23Theorem22Scale rho)
          (projection.theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow rho
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss))
    (hKatzTao : (4 : ENNReal) ≤
      Kakeya.realRpowENN (wz1Lemma23Theorem22Scale rho)
        (-projection.theoremEta))
    {sourceCostLoss : ℝ}
    (hCbound :
      C ≤ 10 * Kakeya.realRpowENN sourceScale (-inputLoss))
    (hsourceCost :
      Kakeya.realRpowENN sourceScale (-inputLoss) ≤
        Kakeya.realRpowENN (wz1Lemma23Theorem22Scale rho)
          (-sourceCostLoss))
    (hsourceCostLoss : 0 ≤ sourceCostLoss)
    (hsourceCostCeiling :
      sourceCostLoss ≤ projection.sourceCostLossCeiling)
    (hdeltaSmall :
      wz1Lemma23Theorem22Scale rho ≤ projection.reductionDelta₀)
    (hconstantSmall :
      (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN (wz1Lemma23Theorem22Scale rho)
          (-(projection.projectionEta * (sigma - outputLoss / 2) -
            (10 * projection.theoremEta + sourceCostLoss)) / 2)) :
    Nonempty (PureWZ2AnchoredTheorem52Output finiteGraph projection) := by
  rcases finiteGraph.toSharpGeometry with ⟨sharp⟩
  rcases sharp.toReadyGraph hsigma hsigmaOne hCOne hCpower hvolume
      hextraPower hedgeAbsorb hKatzTao with ⟨ready⟩
  have hdeltaSmall' :
      ready.ready.deltaGraph ≤ projection.reductionDelta₀ := by
    rw [ready.ready.deltaGraph_eq]
    exact hdeltaSmall
  have hsourceCost' :
      Kakeya.realRpowENN sourceScale (-inputLoss) ≤
        Kakeya.realRpowENN ready.ready.deltaGraph (-sourceCostLoss) := by
    rw [ready.ready.deltaGraph_eq]
    exact hsourceCost
  have hconstantSmall' :
      (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN ready.ready.deltaGraph
          (-(projection.projectionEta * (sigma - outputLoss / 2) -
            (10 * projection.theoremEta + sourceCostLoss)) / 2) := by
    rw [ready.ready.deltaGraph_eq]
    exact hconstantSmall
  have hlineAlternative :=
    ready.theorem52_line_alternative projection houtput houtputOne
      hsigma hsigmaOne houtputSigma hCbound hsourceCost'
      hsourceCostLoss hsourceCostCeiling hdeltaSmall' hconstantSmall'
  rcases ready.lineData hlineAlternative with ⟨lineData⟩
  exact ⟨{
    sharp := sharp
    ready := ready
    A_tilde := ready.A_tilde
    A_tilde_ad := ready.A_tilde_ad hsigma hsigmaOne
    dot_product_in_A_tilde := ready.dot_product_subset_A_tilde
    lineAlternative := hlineAlternative
    lineData := lineData
  }⟩

/--
P3 entrance with no concrete local-grain producer.

The input `fullGrains` is the correct paper output type: its `grainInput`
field supplies a `WZ1Lemma23FullLocalGrainInputGeneralized` at every selected
anchor.  This theorem constructs `g`, the local bins, the finite graph, the
common `(z₀,w)`, the exact skew/dot data, the WZ1 Theorem 5.2 dichotomy,
`Z_lin`, and `L_S` in one dependent result.
-/
structure PureWZ2AnchoredTheorem52FromFullGrainsData
    {delta rho sigma outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    (prep : PureWZ2AnchoredGraphPreparationData input)
    (projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma outputLoss) where
  localBins : WZ1Lemma23LocalBinPackage
    (rho := rho) (sigma := sigma) C prep.windowed.global.cells
  finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins
  output : PureWZ2AnchoredTheorem52Output finiteGraph projection

theorem PureWZ2AnchoredGraphPreparationData.theorem52FromFullLocalGrains
    {delta rho sigma eta outputLoss sourceScale inputLoss
      volumeLoss constantLoss extraLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    (prep : PureWZ2AnchoredGraphPreparationData input)
    (projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma outputLoss)
    (localGrains : WZ1LocalGrainData shadow sigma C)
    (fullGrains : WZ1Lemma23LocalCellFamilyGeneralized
      (rho := rho) (sigma := sigma) (eta := eta) shadow C
      prep.windowed.global.extendedSlope prep.windowed.global.cells localGrains)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (houtput : 0 < outputLoss) (houtputOne : outputLoss < 1)
    (houtputSigma : outputLoss / 2 < sigma)
    (hCpowerLocal : C ≤ Kakeya.realRpowENN rho (-eta))
    (hPlanarSmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall : 20 * Real.sqrt rho ≤ 1)
    (hlocalAbsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤ Real.sqrt rho / 14)
    (hvolumePos : 0 < volume shadow.union)
    (hCOne : (1 : ENNReal) ≤ C)
    (hCpower : C.toReal ≤ Real.rpow rho (-constantLoss))
    (hvolume : ENNReal.ofReal
        (Real.rpow rho (1 + sigma / 2 + volumeLoss)) ≤ volume shadow.union)
    (hextraPower : ∀ localBins :
        WZ1Lemma23LocalBinPackage
          (rho := rho) (sigma := sigma) C prep.windowed.global.cells,
      ∀ finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins,
        (finiteGraph.graph.residue.extraCost : ℝ) ≤
          Real.rpow rho (-extraLoss))
    (hedgeAbsorb :
      Real.rpow (wz1Lemma23Theorem22Scale rho)
          (projection.theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow rho
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss))
    (hKatzTao : (4 : ENNReal) ≤
      Kakeya.realRpowENN (wz1Lemma23Theorem22Scale rho)
        (-projection.theoremEta))
    {sourceCostLoss : ℝ}
    (hCbound :
      C ≤ 10 * Kakeya.realRpowENN sourceScale (-inputLoss))
    (hsourceCost :
      Kakeya.realRpowENN sourceScale (-inputLoss) ≤
        Kakeya.realRpowENN (wz1Lemma23Theorem22Scale rho)
          (-sourceCostLoss))
    (hsourceCostLoss : 0 ≤ sourceCostLoss)
    (hsourceCostCeiling :
      sourceCostLoss ≤ projection.sourceCostLossCeiling)
    (hdeltaSmall :
      wz1Lemma23Theorem22Scale rho ≤ projection.reductionDelta₀)
    (hconstantSmall :
      (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN (wz1Lemma23Theorem22Scale rho)
          (-(projection.projectionEta * (sigma - outputLoss / 2) -
            (10 * projection.theoremEta + sourceCostLoss)) / 2)) :
    Nonempty
      (PureWZ2AnchoredTheorem52FromFullGrainsData prep projection) := by
  rcases wz1_lemma23_local_bin_package_generalized shadow C
      prep.windowed.global.extendedSlope prep.windowed.global.cells
      localGrains input.delta_le_rho input.rho_le_one
      hsigma hsigmaOne heta hetaSigma input.constant_ne_top hCpowerLocal
      hPlanarSmall hrootSmall hlocalAbsorb fullGrains with
    ⟨localBins, _⟩
  rcases prep.prepareFiniteGraph localBins hvolumePos with ⟨finiteGraph⟩
  rcases finiteGraph.theorem52 projection hsigma hsigmaOne houtput
      houtputOne houtputSigma hCOne hCpower hvolume
      (hextraPower localBins finiteGraph) hedgeAbsorb hKatzTao
      hCbound hsourceCost hsourceCostLoss hsourceCostCeiling hdeltaSmall
      hconstantSmall with ⟨output⟩
  exact ⟨{
    localBins := localBins
    finiteGraph := finiteGraph
    output := output
  }⟩

end Kakeya.Assouad

end
