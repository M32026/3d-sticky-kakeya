import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichNeighborhoodGraphParents
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinAnchoredFiniteGraph

/-!
# Local bins for the source-supported direct-rich graph

The graph y-layers are reindexed by their unique selected side-`sqrt rho`
parent.  Their normal is the original P1 plane map at that parent's fixed-line
witness, while horizontal saturation supplies the normal-first theorem.
Local AD and every graph incidence remain on the genuine source shading.
-/

noncomputable section

namespace Kakeya.Assouad

open Set Metric

attribute [local instance] Classical.propDecidable

structure PureWZ2Node05V4RichNeighborhoodGraphData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : neighborhood.graphScale ≤ 1}
    {prep : PureWZ2AnchoredGraphPreparationData
      (neighborhood.graphInput hbridge hgraphOne)}
    (parents : PureWZ2Node05V4RichNeighborhoodGraphParentData prep) where
  g : ℝ → ℝ
  g_lipschitz : LipschitzOnWith 64 g Set.univ
  g_bounded : ∀ y, |g y| ≤ 2
  graph_eq :
    ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
      g (wz1Lemma23SnappedYValue neighborhood.graphScale cell.2.1) =
        current.grain.localGrains.planeMap
            ⟨neighborhood.witness (parents.parentY cell),
              pullback.subshading.union_subset
                (neighborhood.witness_mem_pullback
                  (parents.parentY cell) (parents.parentY_mem cell hcell)).1⟩
            (2 : Fin 3) /
          current.grain.localGrains.planeMap
            ⟨neighborhood.witness (parents.parentY cell),
              pullback.subshading.union_subset
                (neighborhood.witness_mem_pullback
                  (parents.parentY cell) (parents.parentY_mem cell hcell)).1⟩
            (0 : Fin 3)
  normal_first :
    ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
      1 / 4 ≤
        |current.grain.localGrains.planeMap
          ⟨neighborhood.witness (parents.parentY cell),
            pullback.subshading.union_subset
              (neighborhood.witness_mem_pullback
                (parents.parentY cell) (parents.parentY_mem cell hcell)).1⟩
          (0 : Fin 3)|

namespace PureWZ2Node05V4RichNeighborhoodGraphParentData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : neighborhood.graphScale ≤ 1}
    {prep : PureWZ2AnchoredGraphPreparationData
      (neighborhood.graphInput hbridge hgraphOne)}
    (parents : PureWZ2Node05V4RichNeighborhoodGraphParentData prep)

/-- Reindex the saturated parent normals by the actual graph y-layers and
extend their quotient to the bounded global function `g`. -/
theorem localGraph
    (saturated :
      PureWZ2Node05V4RichSaturatedNeighborhoodFullGrainData
        (eta := eta) neighborhood)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hCpower : 160 * Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN (4 * rhoRequested.1) (-eta))
    (hcertificateOne : 4 * rhoRequested.1 ≤ 1)
    (hPlanarSmall : 32 * Real.rpow (4 * rhoRequested.1) eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rhoRequested.1) ≤ 1)
    (habsorb :
      Real.rpow (4 * rhoRequested.1) (1 - 4 * eta / sigma) ≤
        Real.sqrt (4 * rhoRequested.1) / 14) :
    Nonempty (PureWZ2Node05V4RichNeighborhoodGraphData
      (eta := eta) parents) := by
  let cells := prep.windowed.global.cells
  let sample : Finset ℝ :=
    cells.image fun cell =>
      wz1Lemma23SnappedYValue neighborhood.graphScale cell.2.1
  have hcellExists : ∀ y (hy : y ∈ sample),
      ∃ cell ∈ cells,
        wz1Lemma23SnappedYValue neighborhood.graphScale cell.2.1 = y := by
    intro y hy
    simpa [sample] using Finset.mem_image.mp hy
  let cellFor : ∀ y, y ∈ sample → WZ2PaperCellIndex :=
    fun y hy => Classical.choose (hcellExists y hy)
  have hcellForMem : ∀ y (hy : y ∈ sample), cellFor y hy ∈ cells := by
    intro y hy
    exact (Classical.choose_spec (hcellExists y hy)).1
  have hcellForValue : ∀ y (hy : y ∈ sample),
      wz1Lemma23SnappedYValue neighborhood.graphScale
        (cellFor y hy).2.1 = y := by
    intro y hy
    exact (Classical.choose_spec (hcellExists y hy)).2
  let anchor : ℝ → Point3 := fun y =>
    if hy : y ∈ sample then
      neighborhood.witness (parents.parentY (cellFor y hy))
    else 0
  let normal : Point3 → Point3 := fun point =>
    if hpoint : point ∈ current.grain.shading.union then
      current.grain.localGrains.planeMap ⟨point, hpoint⟩ else 0
  have hparentMem : ∀ y (hy : y ∈ sample),
      parents.parentY (cellFor y hy) ∈ neighborhood.sample := by
    intro y hy
    exact parents.parentY_mem _ (hcellForMem y hy)
  have hanchorEq : ∀ y (hy : y ∈ sample),
      anchor y = neighborhood.witness (parents.parentY (cellFor y hy)) := by
    intro y hy
    simp only [anchor, dif_pos hy]
  have hanchorSource : ∀ y (hy : y ∈ sample),
      anchor y ∈ current.grain.shading.union := by
    intro y hy
    rw [hanchorEq y hy]
    exact pullback.subshading.union_subset
      (neighborhood.witness_mem_pullback
        (parents.parentY (cellFor y hy)) (hparentMem y hy)).1
  have hnormalEq : ∀ y (hy : y ∈ sample),
      normal (anchor y) =
        (saturated.fullGrainFor
          (parents.parentY (cellFor y hy)) (hparentMem y hy)).normal := by
    intro y hy
    let grain := saturated.fullGrainFor
      (parents.parentY (cellFor y hy)) (hparentMem y hy)
    simp only [normal, dif_pos (hanchorSource y hy)]
    rw [grain.normal_eq]
    congr 1
    apply Subtype.ext
    exact hanchorEq y hy |>.trans
      (saturated.fullGrain_anchor_eq
        (parents.parentY (cellFor y hy)) (hparentMem y hy)).symm
  have hnormalVertical : ∀ y ∈ sample,
      |normal (anchor y) (2 : Fin 3)| ≤ 1 / 2 := by
    intro y hy
    simp only [normal, dif_pos (hanchorSource y hy)]
    exact current.grain.planeMap_vertical_bound _
  have hnormalFirst : ∀ y ∈ sample,
      1 / 4 ≤ |normal (anchor y) (0 : Fin 3)| := by
    intro y hy
    let grain := saturated.fullGrainFor
      (parents.parentY (cellFor y hy)) (hparentMem y hy)
    have hfirst := grain.normal_first hbridge hsigma hsigmaOne heta hetaSigma
      (by simpa only [grain.certificateScale_eq] using hCpower)
      hcertificateOne
      (by simpa only [grain.certificateScale_eq] using hPlanarSmall)
      (by simpa only [grain.certificateScale_eq] using hrootSmall20)
      (by simpa only [grain.certificateScale_eq] using habsorb)
    rwa [hnormalEq y hy]
  have hnormalDist : ∀ first ∈ sample, ∀ second ∈ sample,
      dist (normal (anchor first)) (normal (anchor second)) ≤
        dist (anchor first) (anchor second) := by
    intro first hfirst second hsecond
    simp only [normal, dif_pos (hanchorSource first hfirst),
      dif_pos (hanchorSource second hsecond)]
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using
      current.grain.localGrains.planeMap_lipschitz.dist_le_mul
        (⟨anchor first, hanchorSource first hfirst⟩ :
          {point : Point3 // point ∈ current.grain.shading.union})
        (⟨anchor second, hanchorSource second hsecond⟩ :
          {point : Point3 // point ∈ current.grain.shading.union})
  have hanchorDist : ∀ first ∈ sample, ∀ second ∈ sample,
      dist (anchor first) (anchor second) ≤ 4 * |first - second| := by
    intro first hfirst second hsecond
    rw [hanchorEq first hfirst, hanchorEq second hsecond]
    have hdist := parents.witness_dist
      (cellFor first hfirst) (hcellForMem first hfirst)
      (cellFor second hsecond) (hcellForMem second hsecond)
    simpa [hcellForValue first hfirst, hcellForValue second hsecond]
      using hdist
  rcases wz1_lemma23_local_graph_extension_of_distortion
      sample anchor normal hnormalVertical hnormalFirst hnormalDist hanchorDist
    with ⟨g, hgLip, hgBound, hgEq⟩
  have hsampleMem : ∀ cell ∈ cells,
      wz1Lemma23SnappedYValue neighborhood.graphScale cell.2.1 ∈ sample := by
    intro cell hcell
    exact Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
  refine ⟨{
    g := g
    g_lipschitz := hgLip
    g_bounded := hgBound
    graph_eq := ?_
    normal_first := ?_
  }⟩
  · intro cell hcell
    let y := wz1Lemma23SnappedYValue neighborhood.graphScale cell.2.1
    have hy : y ∈ sample := hsampleMem cell hcell
    have hparentEq : parents.parentY (cellFor y hy) = parents.parentY cell := by
      apply parents.same_y_parentY
        (cellFor y hy) (hcellForMem y hy) cell hcell
      apply wz1Lemma23SnappedYValue_injective neighborhood.graphScale_pos
      exact hcellForValue y hy
    have hgraph := hgEq y hy
    rw [hnormalEq y hy] at hgraph
    let grain := saturated.fullGrainFor
      (parents.parentY (cellFor y hy)) (hparentMem y hy)
    have hgrainNormal : grain.normal =
        current.grain.localGrains.planeMap
          ⟨neighborhood.witness (parents.parentY (cellFor y hy)),
            pullback.subshading.union_subset
              (neighborhood.witness_mem_pullback
                (parents.parentY (cellFor y hy)) (hparentMem y hy)).1⟩ := by
      rw [grain.normal_eq]
      congr 1
      apply Subtype.ext
      exact saturated.fullGrain_anchor_eq
        (parents.parentY (cellFor y hy)) (hparentMem y hy)
    rw [hgrainNormal] at hgraph
    simpa [y, hparentEq] using hgraph
  · intro cell hcell
    let y := wz1Lemma23SnappedYValue neighborhood.graphScale cell.2.1
    have hy : y ∈ sample := hsampleMem cell hcell
    have hparentEq : parents.parentY (cellFor y hy) = parents.parentY cell := by
      apply parents.same_y_parentY
        (cellFor y hy) (hcellForMem y hy) cell hcell
      apply wz1Lemma23SnappedYValue_injective neighborhood.graphScale_pos
      exact hcellForValue y hy
    have hfirst := hnormalFirst y hy
    simp only [normal, dif_pos (hanchorSource y hy)] at hfirst
    simpa [y, hparentEq, hanchorEq y hy] using hfirst

end PureWZ2Node05V4RichNeighborhoodGraphParentData

namespace PureWZ2Node05V4RichNeighborhoodGraphData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : neighborhood.graphScale ≤ 1}
    {prep : PureWZ2AnchoredGraphPreparationData
      (neighborhood.graphInput hbridge hgraphOne)}
    {parents : PureWZ2Node05V4RichNeighborhoodGraphParentData prep}
    (data : PureWZ2Node05V4RichNeighborhoodGraphData
      (eta := eta) parents)

/-- The heterogeneous local-bin input on the genuine source.  Saturation
enters only through `data.normal_first`; the carrier and witnesses below are
literal points of the original P1 source. -/
noncomputable def toHeterogeneousLocalBinInput :
    WZ1Lemma23HeterogeneousLocalBinInput
      neighborhood.graphScale sigma
      (10 * Kakeya.realRpowENN delta (-inputLoss))
      prep.windowed.global.cells data.g := by
  let cells := prep.windowed.global.cells
  have hlayerCell : ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      ∃ cell ∈ cells, cell.2.1 = y := by
    intro y hy
    simpa [wz1Lemma23SnappedYLayers] using Finset.mem_image.mp hy
  let layerCell : ∀ y, y ∈ wz1Lemma23SnappedYLayers cells →
      WZ2PaperCellIndex :=
    fun y hy => Classical.choose (hlayerCell y hy)
  have hlayerCellMem : ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      layerCell y hy ∈ cells := by
    intro y hy
    exact (Classical.choose_spec (hlayerCell y hy)).1
  have hlayerCellY : ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      (layerCell y hy).2.1 = y := by
    intro y hy
    exact (Classical.choose_spec (hlayerCell y hy)).2
  let anchor : ℤ → Point3 := fun y =>
    if hy : y ∈ wz1Lemma23SnappedYLayers cells then
      neighborhood.witness (parents.parentY (layerCell y hy))
    else 0
  have hanchorEq : ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      anchor y = neighborhood.witness (parents.parentY (layerCell y hy)) := by
    intro y hy
    simp only [anchor, dif_pos hy]
  have hanchorSource : ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      anchor y ∈ current.grain.shading.union := by
    intro y hy
    rw [hanchorEq y hy]
    exact pullback.subshading.union_subset
      (neighborhood.witness_mem_pullback
        (parents.parentY (layerCell y hy))
        (parents.parentY_mem _ (hlayerCellMem y hy))).1
  refine {
    fineCarrier := current.grain.shading.union
    coarseRepresentative := parents.representative
    fineWitness := parents.sourceWitness
    anchor := anchor
    normal := fun y =>
      if hy : y ∈ wz1Lemma23SnappedYLayers cells then
        current.grain.localGrains.planeMap
          ⟨anchor y, hanchorSource y hy⟩
      else 0
    fine_witness_mem := ?_
    coarse_representative_index := parents.representative_index
    coarse_fine_close := ?_
    fine_witness_in_anchor_ball := ?_
    normal_unit := ?_
    normal_vertical := ?_
    normal_first := ?_
    graph_eq := ?_
    fine_local_ad := ?_
  }
  · intro cell hcell
    exact neighborhood.aggregate_sub_source.union_subset (by
      rw [neighborhood.aggregate_union_eq]
      exact Set.mem_iUnion₂.mpr
        ⟨parents.parentY cell, parents.parentY_mem cell hcell,
          parents.sourceWitness_mem_pullback cell hcell⟩)
  · intro cell hcell
    exact (parents.representative_source_dist cell hcell).trans (by
      have hrho : 0 < rho := by
        rw [← pullback.rhoRequested_eq]
        exact twoScale.first.publicSticky.coarse_extremal.delta_pos
      dsimp only [PureWZ2PreCommonBinGlobalGrainNeighborhoodData.graphScale,
        PureWZ2PreCommonBinGlobalGrainNeighborhoodData.saturatedGraphScale]
      nlinarith)
  · intro y hy cell hcell hcellY
    rw [hanchorEq y hy]
    have hparentEq : parents.parentY cell = parents.parentY (layerCell y hy) :=
      parents.same_y_parentY cell hcell
        (layerCell y hy) (hlayerCellMem y hy)
        (hcellY.trans (hlayerCellY y hy).symm)
    have hrepresentativeParent :=
      pullback.preCommonBinFinePullback_subset_parent
        (parents.sourceWitness_mem_pullback cell hcell)
    have hanchorParent := pullback.preCommonBinFinePullback_subset_parent
      (neighborhood.witness_mem_pullback
        (parents.parentY (layerCell y hy))
        (parents.parentY_mem _ (hlayerCellMem y hy)))
    rw [hparentEq] at hrepresentativeParent
    have hdist := wz1_paper_grid_cube_diameter_lt_two_rho
      twoScale.secondSticky.coarse_extremal.delta_pos
      hrepresentativeParent hanchorParent
    have hsqrtGraph :
        Real.sqrt neighborhood.graphScale = 16 * sqrtRequested.1 := by
      dsimp only [PureWZ2PreCommonBinGlobalGrainNeighborhoodData.graphScale,
        PureWZ2PreCommonBinGlobalGrainNeighborhoodData.saturatedGraphScale]
      rw [Real.sqrt_mul (by norm_num),
        show Real.sqrt (256 : ℝ) = 16 by norm_num,
        ← pullback.sqrtRequested_eq]
    rw [hsqrtGraph]
    exact hdist.le.trans (by
      have hroot : 0 < sqrtRequested.1 :=
        twoScale.secondSticky.coarse_extremal.delta_pos
      nlinarith)
  · intro y hy
    change ‖(if h : y ∈ wz1Lemma23SnappedYLayers cells then
      current.grain.localGrains.planeMap ⟨anchor y, hanchorSource y h⟩
      else 0)‖ = 1
    rw [dif_pos hy]
    exact current.grain.localGrains.planeMap_unit _
  · intro y hy
    change |(if h : y ∈ wz1Lemma23SnappedYLayers cells then
      current.grain.localGrains.planeMap ⟨anchor y, hanchorSource y h⟩
      else 0) (2 : Fin 3)| ≤ 1 / 2
    rw [dif_pos hy]
    exact current.grain.planeMap_vertical_bound _
  · intro y hy
    change 1 / 4 ≤ |(if h : y ∈ wz1Lemma23SnappedYLayers cells then
      current.grain.localGrains.planeMap ⟨anchor y, hanchorSource y h⟩
      else 0) (0 : Fin 3)|
    rw [dif_pos hy]
    have hcell := hlayerCellMem y hy
    have hfirst := data.normal_first (layerCell y hy) hcell
    simpa [hlayerCellY y hy, hanchorEq y hy] using hfirst
  · intro y hy
    change data.g (wz1Lemma23SnappedYValue neighborhood.graphScale y) =
      (if h : y ∈ wz1Lemma23SnappedYLayers cells then
          current.grain.localGrains.planeMap ⟨anchor y, hanchorSource y h⟩
        else 0) (2 : Fin 3) /
      (if h : y ∈ wz1Lemma23SnappedYLayers cells then
          current.grain.localGrains.planeMap ⟨anchor y, hanchorSource y h⟩
        else 0) (0 : Fin 3)
    rw [dif_pos hy]
    have hcell := hlayerCellMem y hy
    have hgraph := data.graph_eq (layerCell y hy) hcell
    simpa [hlayerCellY y hy, hanchorEq y hy] using hgraph
  · intro y hy
    change IsADSet1
      (scalarProjection
        (if h : y ∈ wz1Lemma23SnappedYLayers cells then
          current.grain.localGrains.planeMap ⟨anchor y, hanchorSource y h⟩
          else 0)
        (current.grain.shading.union ∩
          Metric.closedBall (anchor y) (Real.sqrt neighborhood.graphScale)))
      neighborhood.graphScale (1 - sigma)
      (10 * Kakeya.realRpowENN delta (-inputLoss))
    rw [dif_pos hy]
    have hliteral := current.grain.localGrains.local_ad
      neighborhood.graphScale
      (by
        have hdeltaRho : delta ≤ rho := by
          rw [← pullback.rhoRequested_eq]
          exact rhoRequested.property.1
        calc
          delta ≤ rho := hdeltaRho
          _ ≤ neighborhood.graphScale := by
            dsimp only [
              PureWZ2PreCommonBinGlobalGrainNeighborhoodData.graphScale,
              PureWZ2PreCommonBinGlobalGrainNeighborhoodData.saturatedGraphScale]
            have hrho : 0 < rho := by
              rw [← pullback.rhoRequested_eq]
              exact twoScale.first.publicSticky.coarse_extremal.delta_pos
            nlinarith)
      hgraphOne ⟨anchor y, hanchorSource y hy⟩
    exact hbridge.1 _ neighborhood.graphScale (1 - sigma)
      (Kakeya.realRpowENN delta (-inputLoss))
      (scalarProjection_paperShading_subset_Icc
        (current.grain.localGrains.planeMap_unit _) Set.inter_subset_left)
      hliteral

/-- Build the local-bin package consumed by the anchored four-cycle graph. -/
theorem localBins
    (data : PureWZ2Node05V4RichNeighborhoodGraphData
      (eta := eta) parents) :
    Nonempty (WZ1Lemma23LocalBinPackage
      (rho := neighborhood.graphScale) (sigma := sigma)
      (160 * Kakeya.realRpowENN delta (-inputLoss))
      prep.windowed.global.cells) := by
  apply pureWZ2_anchoredLocalBinPackage
    (g := data.g) data.toHeterogeneousLocalBinInput
    neighborhood.graphScale_pos hgraphOne data.g_lipschitz data.g_bounded
  · calc
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) =
          350 * Kakeya.realRpowENN delta (-inputLoss) := by ring
      _ ≤ 3040 * Kakeya.realRpowENN delta (-inputLoss) := by gcongr <;> norm_num
      _ = 19 * (160 * Kakeya.realRpowENN delta (-inputLoss)) := by ring
  · exact ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN])

end PureWZ2Node05V4RichNeighborhoodGraphData

end Kakeya.Assouad

end
