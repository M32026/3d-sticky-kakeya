import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightAnchorGeometry

/-!
# Local graph on the final joint-height support

The auxiliary function `g` is built from the unique selected parent in every
graph y-layer.  Its normal is the literal current plane map at that parent's
same-witness fixed-bin anchor.
-/

noncomputable section

namespace Kakeya.Assouad

open Set Metric

attribute [local instance] Classical.propDecidable

structure PureWZ2Node05V4RichJointLocalGraphData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
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
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    {volumePopular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex}
    {B₀ threshold : ENNReal}
    {block : volumePopular.JointHeightCommonBinData B₀ threshold}
    {oneParent : block.JointOneParentPerYData}
    {separated : PureWZ2Node05V4RichJointSeparatedParentData oneParent}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : separated.graphScale ≤ 1}
    {prep : PureWZ2AnchoredGraphPreparationData
      (separated.graphInput hbridge hgraphOne)}
    (parents : PureWZ2Node05V4RichJointGraphParentData prep)
    (grains : PureWZ2Node05V4RichJointFullGrainData
      (eta := eta) separated) where
  g : ℝ → ℝ
  g_lipschitz : LipschitzOnWith 64 g Set.univ
  g_bounded : ∀ y, |g y| ≤ 2
  graph_eq :
    ∀ cell (_hcell : cell ∈ prep.windowed.global.cells),
      g (wz1Lemma23SnappedYValue separated.graphScale cell.2.1) =
        grains.normalFor (parents.parentCell cell) (2 : Fin 3) /
          grains.normalFor (parents.parentCell cell) (0 : Fin 3)
  normal_first :
    ∀ cell (_hcell : cell ∈ prep.windowed.global.cells),
      1 / 4 ≤ |grains.normalFor
        (parents.parentCell cell) (0 : Fin 3)|

namespace PureWZ2Node05V4RichJointFullGrainData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
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
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    {volumePopular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex}
    {B₀ threshold : ENNReal}
    {block : volumePopular.JointHeightCommonBinData B₀ threshold}
    {oneParent : block.JointOneParentPerYData}
    {separated : PureWZ2Node05V4RichJointSeparatedParentData oneParent}
    (grains : PureWZ2Node05V4RichJointFullGrainData
      (eta := eta) separated)
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : separated.graphScale ≤ 1}
    {prep : PureWZ2AnchoredGraphPreparationData
      (separated.graphInput hbridge hgraphOne)}
    (parents : PureWZ2Node05V4RichJointGraphParentData prep)

theorem localGraph
    (hheightAbsorb :
      separated.graphScale + 2 * Real.sqrt rho ≤ 16 * Real.sqrt rho)
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
    Nonempty (PureWZ2Node05V4RichJointLocalGraphData parents grains) := by
  let cells := prep.windowed.global.cells
  let sample : Finset ℝ :=
    cells.image fun cell =>
      wz1Lemma23SnappedYValue separated.graphScale cell.2.1
  have hcellExists : ∀ y (hy : y ∈ sample),
      ∃ cell ∈ cells,
        wz1Lemma23SnappedYValue separated.graphScale cell.2.1 = y := by
    intro y hy
    simpa [sample] using Finset.mem_image.mp hy
  let cellFor : ∀ y, y ∈ sample → WZ2PaperCellIndex :=
    fun y hy => Classical.choose (hcellExists y hy)
  have hcellForMem : ∀ y (hy : y ∈ sample), cellFor y hy ∈ cells := by
    intro y hy
    exact (Classical.choose_spec (hcellExists y hy)).1
  have hcellForValue : ∀ y (hy : y ∈ sample),
      wz1Lemma23SnappedYValue separated.graphScale (cellFor y hy).2.1 = y := by
    intro y hy
    exact (Classical.choose_spec (hcellExists y hy)).2
  let parentFor : ∀ y, y ∈ sample → WZ2PaperCellIndex :=
    fun y hy => parents.parentCell (cellFor y hy)
  have hparentForMem : ∀ y (hy : y ∈ sample),
      parentFor y hy ∈ separated.selectedParents := by
    intro y hy
    exact parents.parentCell_selected _ (hcellForMem y hy)
  let anchor : ℝ → Point3 := fun y =>
    if hy : y ∈ sample then grains.anchorFor (parentFor y hy) else 0
  have hanchorEq : ∀ y (hy : y ∈ sample),
      anchor y = grains.anchorFor (parentFor y hy) := by
    intro y hy
    simp only [anchor, dif_pos hy]
  have hanchorSource : ∀ y (hy : y ∈ sample),
      anchor y ∈ current.grain.shading.union := by
    intro y hy
    rw [hanchorEq y hy]
    exact grains.anchorFor_mem_current _ (hparentForMem y hy)
  let normal : Point3 → Point3 := fun point =>
    if hpoint : point ∈ current.grain.shading.union then
      current.grain.localGrains.planeMap ⟨point, hpoint⟩ else 0
  have hnormalEq : ∀ y (hy : y ∈ sample),
      (grains.fullGrainFor
        (parentFor y hy) (hparentForMem y hy)).normal =
          normal (anchor y) := by
    intro y hy
    let grain := grains.fullGrainFor
      (parentFor y hy) (hparentForMem y hy)
    calc
      grain.normal = current.grain.localGrains.planeMap
          ⟨grain.anchor, grain.anchor_mem_source⟩ := grain.normal_eq
      _ = current.grain.localGrains.planeMap
          ⟨anchor y, hanchorSource y hy⟩ := by
        congr 1
        apply Subtype.ext
        exact grains.fullGrain_anchor_eq (parentFor y hy)
          (hparentForMem y hy) |>.trans (hanchorEq y hy).symm
      _ = normal (anchor y) := by
        simp [normal, hanchorSource y hy]
  have hnormalForEq : ∀ y (hy : y ∈ sample),
      grains.normalFor (parentFor y hy) = normal (anchor y) := by
    intro y hy
    exact (grains.normalFor_eq (parentFor y hy)
      (hparentForMem y hy)).trans (hnormalEq y hy)
  have hnormalVertical : ∀ y ∈ sample,
      |normal (anchor y) (2 : Fin 3)| ≤ 1 / 2 := by
    intro y hy
    simp only [normal, dif_pos (hanchorSource y hy)]
    exact current.grain.planeMap_vertical_bound _
  have hnormalFirst : ∀ y ∈ sample,
      1 / 4 ≤ |normal (anchor y) (0 : Fin 3)| := by
    intro y hy
    let grain := grains.fullGrainFor
      (parentFor y hy) (hparentForMem y hy)
    have hfirst := grain.normal_first hbridge hsigma hsigmaOne heta hetaSigma
      (by simpa only [grain.certificateScale_eq] using hCpower)
      hcertificateOne
      (by simpa only [grain.certificateScale_eq] using hPlanarSmall)
      (by simpa only [grain.certificateScale_eq] using hrootSmall20)
      (by simpa only [grain.certificateScale_eq] using habsorb)
    rwa [hnormalEq y hy] at hfirst
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
    have hdist := grains.anchor_dist_graph parents hheightAbsorb
      (cellFor first hfirst) (hcellForMem first hfirst)
      (cellFor second hsecond) (hcellForMem second hsecond)
    simpa [hcellForValue first hfirst, hcellForValue second hsecond]
      using hdist
  rcases wz1_lemma23_local_graph_extension_of_distortion
      sample anchor normal hnormalVertical hnormalFirst hnormalDist hanchorDist
    with ⟨g, hgLip, hgBound, hgEq⟩
  have hsampleMem : ∀ cell ∈ cells,
      wz1Lemma23SnappedYValue separated.graphScale cell.2.1 ∈ sample := by
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
    let y := wz1Lemma23SnappedYValue separated.graphScale cell.2.1
    have hy : y ∈ sample := hsampleMem cell hcell
    have hparentEq : parentFor y hy = parents.parentCell cell := by
      apply parents.same_y_parentCell
        (cellFor y hy) (hcellForMem y hy) cell hcell
      apply wz1Lemma23SnappedYValue_injective separated.graphScale_pos
      exact hcellForValue y hy
    have hgraph := hgEq y hy
    rw [← hnormalForEq y hy] at hgraph
    rw [hparentEq] at hgraph
    simpa only [y] using hgraph
  · intro cell hcell
    let y := wz1Lemma23SnappedYValue separated.graphScale cell.2.1
    have hy : y ∈ sample := hsampleMem cell hcell
    have hparentEq : parentFor y hy = parents.parentCell cell := by
      apply parents.same_y_parentCell
        (cellFor y hy) (hcellForMem y hy) cell hcell
      apply wz1Lemma23SnappedYValue_injective separated.graphScale_pos
      exact hcellForValue y hy
    have hfirst := hnormalFirst y hy
    rw [← hnormalForEq y hy] at hfirst
    rw [hparentEq] at hfirst
    simpa only [y] using hfirst

end PureWZ2Node05V4RichJointFullGrainData

namespace PureWZ2Node05V4RichJointLocalGraphData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
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
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    {volumePopular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex}
    {B₀ threshold : ENNReal}
    {block : volumePopular.JointHeightCommonBinData B₀ threshold}
    {oneParent : block.JointOneParentPerYData}
    {separated : PureWZ2Node05V4RichJointSeparatedParentData oneParent}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : separated.graphScale ≤ 1}
    {prep : PureWZ2AnchoredGraphPreparationData
      (separated.graphInput hbridge hgraphOne)}
    {parents : PureWZ2Node05V4RichJointGraphParentData prep}
    {grains : PureWZ2Node05V4RichJointFullGrainData
      (eta := eta) separated}
    (data : PureWZ2Node05V4RichJointLocalGraphData parents grains)

private theorem sourceWitness_mem_current
    (_data : PureWZ2Node05V4RichJointLocalGraphData parents grains)
    (cell : WZ2PaperCellIndex)
    (hcell : cell ∈ prep.windowed.global.cells) :
    parents.sourceWitness cell ∈ current.grain.shading.union := by
  have hsource := parents.sourceWitness_mem cell hcell
  exact volumePopular.jointSourceSet_subset_current hsource.1.1.1

noncomputable def toHeterogeneousLocalBinInput :
    WZ1Lemma23HeterogeneousLocalBinInput
      separated.graphScale sigma
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
      grains.anchorFor (parents.parentCell (layerCell y hy))
    else 0
  have hanchorEq : ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      anchor y = grains.anchorFor (parents.parentCell (layerCell y hy)) := by
    intro y hy
    simp only [anchor, dif_pos hy]
  have hanchorSource : ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      anchor y ∈ current.grain.shading.union := by
    intro y hy
    rw [hanchorEq y hy]
    exact grains.anchorFor_mem_current _
      (parents.parentCell_selected _ (hlayerCellMem y hy))
  refine {
    fineCarrier := current.grain.shading.union
    coarseRepresentative := parents.representative
    fineWitness := parents.sourceWitness
    anchor := anchor
    normal := fun y =>
      if hy : y ∈ wz1Lemma23SnappedYLayers cells then
        grains.normalFor (parents.parentCell (layerCell y hy))
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
    exact data.sourceWitness_mem_current cell hcell
  · intro cell hcell
    have hrepresentativeCell :
        parents.representative cell ∈
          wz1PaperGridCube rho (parents.sourceCell cell) :=
      wz1PaperGridCubeSameHeightSaturation_subset_cube
        rho (parents.sourceCell cell)
        (block.jointCellSource (parents.sourceCell cell))
        (parents.representative_mem_saturation cell hcell)
    have hdist := wz1_paper_grid_cube_diameter_lt_two_rho
      (by
        rw [← pullback.rhoRequested_eq]
        exact twoScale.first.publicSticky.coarse_extremal.delta_pos)
      hrepresentativeCell (parents.sourceWitness_mem_sourceCell cell hcell)
    exact hdist.le.trans (by
      have hrho : 0 < rho := by
        rw [← pullback.rhoRequested_eq]
        exact twoScale.first.publicSticky.coarse_extremal.delta_pos
      change 2 * rho ≤ 2 * (256 * rho)
      nlinarith)
  · intro y hy cell hcell hcellY
    rw [hanchorEq y hy]
    have hparentEq :
        parents.parentCell cell = parents.parentCell (layerCell y hy) :=
      parents.same_y_parentCell cell hcell
        (layerCell y hy) (hlayerCellMem y hy)
        (hcellY.trans (hlayerCellY y hy).symm)
    have hsourceParent : parents.sourceWitness cell ∈
        wz1PaperGridCube sqrtRequested.1 (parents.parentCell cell) := by
      have hraw := pullback.standardSecondParent_cell_subset
        (block.jointFixedBinRhoCells_subset_selected
          (oneParent.selectedCells_subset
            (separated.selectedCells_subset
              (parents.sourceCell_mem cell hcell))))
        (parents.sourceWitness_mem_sourceCell cell hcell)
      rwa [← parents.parentCell_eq cell hcell] at hraw
    rw [hparentEq] at hsourceParent
    have hanchorParent := grains.anchorFor_mem_parent
      (parents.parentCell (layerCell y hy))
      (parents.parentCell_selected _ (hlayerCellMem y hy))
    have hdist := wz1_paper_grid_cube_diameter_lt_two_rho
      twoScale.secondSticky.coarse_extremal.delta_pos
      hsourceParent hanchorParent
    have hsqrtGraph :
        Real.sqrt separated.graphScale = 16 * sqrtRequested.1 := by
      unfold PureWZ2Node05V4RichJointSeparatedParentData.graphScale
      rw [Real.sqrt_mul (by norm_num),
        show Real.sqrt (256 : ℝ) = 16 by norm_num,
        twoScale.sqrtRequested_eq, pullback.rhoRequested_eq]
    rw [hsqrtGraph]
    exact hdist.le.trans (by
      have hroot : 0 < sqrtRequested.1 :=
        twoScale.secondSticky.coarse_extremal.delta_pos
      nlinarith)
  · intro y hy
    rw [dif_pos hy, grains.normalFor_eq _
      (parents.parentCell_selected _ (hlayerCellMem y hy))]
    let grain := grains.fullGrainFor
      (parents.parentCell (layerCell y hy))
      (parents.parentCell_selected _ (hlayerCellMem y hy))
    rw [grain.normal_eq]
    exact current.grain.localGrains.planeMap_unit _
  · intro y hy
    rw [dif_pos hy, grains.normalFor_eq _
      (parents.parentCell_selected _ (hlayerCellMem y hy))]
    let grain := grains.fullGrainFor
      (parents.parentCell (layerCell y hy))
      (parents.parentCell_selected _ (hlayerCellMem y hy))
    rw [grain.normal_eq]
    exact current.grain.planeMap_vertical_bound _
  · intro y hy
    rw [dif_pos hy]
    have hfirst := data.normal_first (layerCell y hy)
      (hlayerCellMem y hy)
    simpa [hlayerCellY y hy] using hfirst
  · intro y hy
    rw [dif_pos hy]
    have hcell := hlayerCellMem y hy
    have hgraph := data.graph_eq (layerCell y hy) hcell
    simpa [hlayerCellY y hy] using hgraph
  · intro y hy
    rw [dif_pos hy]
    have hanchor := hanchorSource y hy
    have hliteral := current.grain.localGrains.local_ad
      separated.graphScale
      (by
        have hdeltaRho : delta ≤ rho := by
          rw [← pullback.rhoRequested_eq]
          exact rhoRequested.property.1
        calc
          delta ≤ rho := hdeltaRho
          _ ≤ separated.graphScale := by
            unfold PureWZ2Node05V4RichJointSeparatedParentData.graphScale
            have hrho : 0 < rho := by
              rw [← pullback.rhoRequested_eq]
              exact twoScale.first.publicSticky.coarse_extremal.delta_pos
            nlinarith)
      hgraphOne ⟨anchor y, hanchor⟩
    have hparentMem :=
      parents.parentCell_selected (layerCell y hy) (hlayerCellMem y hy)
    rw [grains.normalFor_eq _ hparentMem]
    let grain := grains.fullGrainFor
      (parents.parentCell (layerCell y hy)) hparentMem
    have hnormal :
        grain.normal =
          current.grain.localGrains.planeMap ⟨anchor y, hanchor⟩ := by
      rw [grain.normal_eq]
      congr 1
      apply Subtype.ext
      exact grains.fullGrain_anchor_eq _ hparentMem |>.trans
        (hanchorEq y hy).symm
    rw [hnormal]
    exact hbridge.1 _ separated.graphScale (1 - sigma)
      (Kakeya.realRpowENN delta (-inputLoss))
      (scalarProjection_paperShading_subset_Icc
        (current.grain.localGrains.planeMap_unit _) Set.inter_subset_left)
      hliteral

include data in
theorem localBins :
    Nonempty (WZ1Lemma23LocalBinPackage
      (rho := separated.graphScale) (sigma := sigma)
      (160 * Kakeya.realRpowENN delta (-inputLoss))
      prep.windowed.global.cells) := by
  apply pureWZ2_anchoredLocalBinPackage
    (g := data.g) data.toHeterogeneousLocalBinInput
    separated.graphScale_pos hgraphOne data.g_lipschitz data.g_bounded
  · calc
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) =
          350 * Kakeya.realRpowENN delta (-inputLoss) := by ring
      _ ≤ 3040 * Kakeya.realRpowENN delta (-inputLoss) := by
        gcongr
        norm_num
      _ = 19 * (160 * Kakeya.realRpowENN delta (-inputLoss)) := by ring
  · exact ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN])

end PureWZ2Node05V4RichJointLocalGraphData

end Kakeya.Assouad

end
