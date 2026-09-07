import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineAnchorGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalBinPackage
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LayerCounts

/-!
# Generalized Lemma-23 local-cell family on the fixed-line residue

This is the dependent assembly point.  The cells, local and global grains,
actual coarse sources, source anchors, and full grains all live on the same
active-cell shadow.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

theorem PureWZ2HorizontalFixedLineGraphParentData.localCellFamily
    {sigma inputLoss delta rho middleLoss outputLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading :
      PureWZ2HorizontalFixedLineResidueShadingData residue}
    {prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading}
    (graphParents : PureWZ2HorizontalFixedLineGraphParentData prep)
    (sources : PureWZ2HorizontalFixedLineResidueSourceFamily residueShading)
    (fullGrains :
      PureWZ2HorizontalFixedLineResidueFullGrainFamily
        (eta := eta) sources prep) :
    Nonempty
      (WZ1Lemma23LocalCellFamilyGeneralized
        (rho := prep.graphScale) (sigma := sigma) (eta := eta)
        prep.shadow
        (10 * Kakeya.realRpowENN
          twoScale.rhoRequested.1 (-middleLoss))
        prep.windowed.global.sourceSlope
        prep.windowed.global.cells prep.localGrains) := by
  let cells := prep.windowed.global.cells
  let sample : Finset ℝ := cells.image fun cell =>
    wz1Lemma23SnappedYValue prep.graphScale cell.2.1
  have hcellExists :
      ∀ y (hy : y ∈ sample),
        ∃ cell ∈ cells,
          wz1Lemma23SnappedYValue prep.graphScale cell.2.1 = y := by
    intro y hy
    simpa [sample] using Finset.mem_image.mp hy
  let cellFor : ∀ y, y ∈ sample → ℤ × ℤ × ℤ := fun y hy =>
    Classical.choose (hcellExists y hy)
  have hcellForMem :
      ∀ y (hy : y ∈ sample), cellFor y hy ∈ cells := by
    intro y hy
    exact (Classical.choose_spec (hcellExists y hy)).1
  have hcellForValue :
      ∀ y (hy : y ∈ sample),
        wz1Lemma23SnappedYValue prep.graphScale (cellFor y hy).2.1 = y := by
    intro y hy
    exact (Classical.choose_spec (hcellExists y hy)).2
  have hySample :
      ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers prep.windowed.global.cells),
        wz1Lemma23SnappedYValue prep.graphScale y ∈ sample := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨cell, hcell, hcellY⟩
    exact Finset.mem_image.mpr
      ⟨cell, hcell, congrArg
        (wz1Lemma23SnappedYValue prep.graphScale) hcellY⟩
  have hparentForMem :
      ∀ y (hy : y ∈ sample),
        graphParents.parentOf (cellFor y hy) ∈ residue.selected := by
    intro y hy
    exact graphParents.parent_mem _ (hcellForMem y hy)
  let anchor : ℝ → Point3 := fun y =>
    if hy : y ∈ sample then
      graphParents.anchorFor sources (cellFor y hy) (hcellForMem y hy)
    else 0
  have hanchorEq :
      ∀ y (hy : y ∈ sample),
        anchor y =
          graphParents.anchorFor sources (cellFor y hy)
            (hcellForMem y hy) := by
    intro y hy
    simp only [anchor, dif_pos hy]
  let grainInput :
      ∀ y, y ∈ sample →
        WZ1Lemma23FullLocalGrainInputGeneralized
          prep.graphScale sigma eta
          (10 * Kakeya.realRpowENN
            twoScale.rhoRequested.1 (-middleLoss))
          prep.windowed.global.sourceSlope := fun y hy =>
    fullGrains.fullInput
      (graphParents.parentOf (cellFor y hy)) (hparentForMem y hy)
  let coarseSource : ∀ y, y ∈ sample → Set Point3 := fun y hy =>
    (sources.sourceFor
      (graphParents.parentOf (cellFor y hy)) (hparentForMem y hy)).coarseSource
  have hanchorMem : ∀ y (hy : y ∈ sample), anchor y ∈ prep.shadow.union := by
    intro y hy
    rw [hanchorEq y hy]
    exact graphParents.anchorFor_mem_shadow sources _ (hcellForMem y hy)
  have hnormalDist :
      ∀ y₁ (hy₁ : y₁ ∈ sample), ∀ y₂ (hy₂ : y₂ ∈ sample),
        dist (prep.localGrains.planeMap (anchor y₁))
            (prep.localGrains.planeMap (anchor y₂)) ≤
          dist (anchor y₁) (anchor y₂) := by
    intro y₁ hy₁ y₂ hy₂
    have hpaper₁ : anchor y₁ ∈ residueShading.shading.union := by
      rw [← prep.shadow_union]
      exact hanchorMem y₁ hy₁
    have hpaper₂ : anchor y₂ ∈ residueShading.shading.union := by
      rw [← prep.shadow_union]
      exact hanchorMem y₂ hy₂
    rw [prep.planeMap_eq_on_paper ⟨anchor y₁, hpaper₁⟩]
    rw [prep.planeMap_eq_on_paper ⟨anchor y₂, hpaper₂⟩]
    have hlip := prep.localPaper.planeMap_lipschitz.dist_le_mul
      ⟨anchor y₁, hpaper₁⟩ ⟨anchor y₂, hpaper₂⟩
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using hlip
  have hanchorDist :
      ∀ y₁ (hy₁ : y₁ ∈ sample), ∀ y₂ (hy₂ : y₂ ∈ sample),
        dist (anchor y₁) (anchor y₂) ≤ 4 * |y₁ - y₂| := by
    intro y₁ hy₁ y₂ hy₂
    rw [hanchorEq y₁ hy₁, hanchorEq y₂ hy₂]
    have hdist := graphParents.anchorFor_dist sources
      (cellFor y₁ hy₁) (hcellForMem y₁ hy₁)
      (cellFor y₂ hy₂) (hcellForMem y₂ hy₂)
    simpa [hcellForValue y₁ hy₁, hcellForValue y₂ hy₂] using hdist
  refine ⟨{
    sample := sample
    anchor := anchor
    normal := prep.localGrains.planeMap
    normal_vertical := ?_
    normal_dist := hnormalDist
    anchor_dist := hanchorDist
    grainInput := grainInput
    grain_normal := ?_
    rho_pos := prep.graphScale_pos
    cells_active := prep.windowed.global.cells_active
    y_mem := ?_
    anchor_mem := ?_
    local_normal := ?_
    grain_center := ?_
    coarseSource := coarseSource
    coarse_source_measurable := ?_
    coarse_source_nonempty := ?_
    coarse_source_subset := ?_
    coarse_source_volume := ?_
    grain_in_coarse_source := ?_
    grain_in_source := ?_
    grain_in_anchor_ball := ?_
    projected_eq := ?_
    layer_ball := ?_ }⟩
  · intro y hy
    exact prep.planeMap_vertical_bound (anchor y) (hanchorMem y hy)
  · intro y hy
    dsimp only [grainInput]
    rw [fullGrains.fullInput_normal]
    rw [hanchorEq y hy]
    simp only [PureWZ2HorizontalFixedLineGraphParentData.anchorFor]
  · intro y hy
    exact hySample y hy
  · intro y hy
    exact hanchorMem (wz1Lemma23SnappedYValue prep.graphScale y)
      (hySample y hy)
  · intro y hy
    rfl
  · intro y hy
    dsimp only [grainInput]
    rw [fullGrains.fullInput_center]
    rw [hanchorEq (wz1Lemma23SnappedYValue prep.graphScale y)
      (hySample y hy)]
    simp only [PureWZ2HorizontalFixedLineGraphParentData.anchorFor]
  · intro y hy
    exact (sources.sourceFor _ _).coarseSource_measurable
  · intro y hy
    exact (sources.sourceFor _ _).coarseSource_nonempty
  · intro y hy point hpoint
    have hsource := sources.coarse_source_subset
      (graphParents.parentOf (cellFor y hy)) (hparentForMem y hy) hpoint
    rw [hanchorEq y hy]
    constructor
    · rw [prep.shadow_union]
      exact hsource.1
    · rw [Metric.mem_closedBall]
      have hball := hsource.2
      rw [Metric.mem_closedBall] at hball
      simpa only [PureWZ2HorizontalFixedLineGraphParentData.anchorFor] using
        hball.trans (by
        rw [prep.graphScale_sqrt]
        nlinarith [twoScale.fine.coarse_extremal.delta_pos])
  · intro y hy
    exact fullGrains.coarse_source_volume _ _
  · intro y hy
    exact fullGrains.grain_in_source _ _
  · intro y hy point hpoint
    have hs := hySample y hy
    have hcoarse := sources.coarse_source_subset
      (graphParents.parentOf (cellFor
        (wz1Lemma23SnappedYValue prep.graphScale y) hs))
      (hparentForMem (wz1Lemma23SnappedYValue prep.graphScale y) hs)
      (fullGrains.grain_in_source _ _ hpoint)
    rw [prep.shadow_union]
    exact hcoarse.1
  · intro y hy point hpoint
    have hs := hySample y hy
    have hcoarse := sources.coarse_source_subset
      (graphParents.parentOf (cellFor
        (wz1Lemma23SnappedYValue prep.graphScale y) hs))
      (hparentForMem (wz1Lemma23SnappedYValue prep.graphScale y) hs)
      (fullGrains.grain_in_source _ _ hpoint)
    rw [hanchorEq (wz1Lemma23SnappedYValue prep.graphScale y) hs]
    rw [Metric.mem_closedBall]
    have hball := hcoarse.2
    rw [Metric.mem_closedBall] at hball
    simpa only [PureWZ2HorizontalFixedLineGraphParentData.anchorFor] using
      hball.trans (by
      rw [prep.graphScale_sqrt]
      nlinarith [twoScale.fine.coarse_extremal.delta_pos])
  · intro y hy z hz
    dsimp only [grainInput]
    exact fullGrains.fullInput_projected _ _ z
  · intro y hy idx hidx hidxY
    have hs := hySample y hy
    let value := wz1Lemma23SnappedYValue prep.graphScale y
    let chosen := cellFor value hs
    have hchosenMem : chosen ∈ cells := hcellForMem value hs
    have hchosenYValue :
        wz1Lemma23SnappedYValue prep.graphScale chosen.2.1 =
          wz1Lemma23SnappedYValue prep.graphScale y := by
      simpa [value] using hcellForValue value hs
    have hchosenY : chosen.2.1 = y :=
      wz1Lemma23SnappedYValue_injective prep.graphScale_pos hchosenYValue
    have hparent : graphParents.parentOf chosen = graphParents.parentOf idx :=
      graphParents.same_y_parent chosen hchosenMem idx hidx
        (hchosenY.trans hidxY.symm)
    have hanchorSame :
        graphParents.anchorFor sources chosen hchosenMem =
          graphParents.anchorFor sources idx hidx := by
      simp only [PureWZ2HorizontalFixedLineGraphParentData.anchorFor, hparent]
    rw [hanchorEq value hs, hanchorSame]
    exact graphParents.canonical_rep_dist_anchor sources idx hidx

end Kakeya.Assouad
