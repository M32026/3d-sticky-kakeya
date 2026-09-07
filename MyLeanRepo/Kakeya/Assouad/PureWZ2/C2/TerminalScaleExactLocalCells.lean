import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactAnchorGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalProjectionHeavyFiberInSource
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23HeavyFiberThreshold
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalBinPackage

/-!
# Exact-scale terminal local-cell family
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalExactLocalCellData
    {sigma inputLoss delta stickyLoss eta : ℝ} {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    {residue : PureWZ2TerminalBinParentYResidueData selection}
    {retained : PureWZ2TerminalBinRetainedShadingData residue}
    {sources : PureWZ2TerminalBinSourceFamily retained}
    {band : PureWZ2TerminalBinFixedBandSelection sources}
    {phase : PureWZ2TerminalBinHeightPhaseSelection band}
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    (graphParents : PureWZ2TerminalExactGraphParentData prep) where
  family : WZ1Lemma23LocalCellFamilyGeneralized
    (rho := delta) (sigma := sigma) (eta := eta) prep.shadow
    (10 * Kakeya.realRpowENN delta (-inputLoss))
    prep.windowed.global.sourceSlope prep.windowed.global.cells prep.localGrains
  localBins : WZ1Lemma23LocalBinPackage
    (rho := delta) (sigma := sigma)
    (10 * Kakeya.realRpowENN delta (-inputLoss)) prep.windowed.global.cells

theorem PureWZ2TerminalExactGraphParentData.localCells
    {sigma inputLoss delta stickyLoss eta : ℝ} {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    {residue : PureWZ2TerminalBinParentYResidueData selection}
    {retained : PureWZ2TerminalBinRetainedShadingData residue}
    {sources : PureWZ2TerminalBinSourceFamily retained}
    {band : PureWZ2TerminalBinFixedBandSelection sources}
    {phase : PureWZ2TerminalBinHeightPhaseSelection band}
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    (graphParents : PureWZ2TerminalExactGraphParentData prep)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hCpower : 10 * Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-eta))
    (hPlanarSmall : 32 * Real.rpow delta eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt delta ≤ 1)
    (habsorb : Real.rpow delta (1 - 4 * eta / sigma) ≤
      Real.sqrt delta / 14)
    (hsourceVolume :
      (512 * (2 * 512 * 57) : ENNReal) *
          Kakeya.realRpowENN delta (3 / 2 + sigma / 2 + eta) ≤
        terminal.sticky.balanced.cellMass) :
    Nonempty (PureWZ2TerminalExactLocalCellData (eta := eta) graphParents) := by
  let cells := prep.windowed.global.cells
  let C : ENNReal := 10 * Kakeya.realRpowENN delta (-inputLoss)
  let sample : Finset ℝ := cells.image fun cell =>
    wz1Lemma23SnappedYValue delta cell.2.1
  have hcellExists : ∀ y (hy : y ∈ sample),
      ∃ cell ∈ cells, wz1Lemma23SnappedYValue delta cell.2.1 = y := by
    intro y hy
    simpa [sample] using Finset.mem_image.mp hy
  let cellFor : ∀ y, y ∈ sample → ℤ × ℤ × ℤ := fun y hy =>
    Classical.choose (hcellExists y hy)
  have hcellForMem : ∀ y (hy : y ∈ sample), cellFor y hy ∈ cells := by
    intro y hy
    exact (Classical.choose_spec (hcellExists y hy)).1
  have hcellForValue : ∀ y (hy : y ∈ sample),
      wz1Lemma23SnappedYValue delta (cellFor y hy).2.1 = y := by
    intro y hy
    exact (Classical.choose_spec (hcellExists y hy)).2
  let anchor : ℝ → Point3 := fun y => if hy : y ∈ sample then
    graphParents.anchorFor (cellFor y hy) (hcellForMem y hy) else 0
  have hanchorEq : ∀ y (hy : y ∈ sample), anchor y =
      graphParents.anchorFor (cellFor y hy) (hcellForMem y hy) := by
    intro y hy
    simp [anchor, hy]
  have hanchorMem : ∀ y (hy : y ∈ sample), anchor y ∈ prep.shadow.union := by
    intro y hy
    rw [hanchorEq y hy]
    exact graphParents.anchorFor_mem_shadow _ _
  let parentFor (y : ℝ) (hy : y ∈ sample) :=
    graphParents.parentOf (cellFor y hy)
  let parentMem (y : ℝ) (hy : y ∈ sample) :
      parentFor y hy ∈ phase.selectedParents :=
    graphParents.parent_mem _ (hcellForMem y hy)
  let coarse (y : ℝ) (hy : y ∈ sample) :=
    anchored.piece (parentFor y hy) (parentMem y hy)
  have hcoarseSubset : ∀ y (hy : y ∈ sample), coarse y hy ⊆
      prep.shadow.union ∩ Metric.closedBall (anchor y) (Real.sqrt delta) := by
    intro y hy point hpoint
    refine ⟨?_, ?_⟩
    · rw [prep.shadow_union, prep.region_eq]
      exact Set.mem_iUnion.mpr ⟨⟨parentFor y hy, parentMem y hy⟩, hpoint⟩
    · have hball := anchored.piece_ball (parentFor y hy) (parentMem y hy) hpoint
      rw [Metric.mem_closedBall] at hball ⊢
      rw [hanchorEq y hy]
      simpa [PureWZ2TerminalExactGraphParentData.anchorFor,
        terminal.sqrtRequested_eq] using hball
  have hcoarseFloor : ∀ y (hy : y ∈ sample),
      Kakeya.realRpowENN delta (3 / 2 + sigma / 2 + eta) ≤
        volume (coarse y hy) := by
    intro y hy
    have hscaled := (anchored.piece_volume (parentFor y hy) (parentMem y hy))
    have hconstZero : (512 * (2 * 512 * 57) : ENNReal) ≠ 0 := by norm_num
    have hconstTop : (512 * (2 * 512 * 57) : ENNReal) ≠ ⊤ := by norm_num
    apply (ENNReal.mul_le_mul_iff_left hconstZero hconstTop).mp
    simpa [mul_comm] using hsourceVolume.trans hscaled
  have hCtop : C ≠ ⊤ := by
    dsimp only [C]
    exact ENNReal.mul_ne_top (by norm_num) (by simp [Kakeya.realRpowENN])
  let fiber (y : ℝ) (hy : y ∈ sample) := Classical.choice
    (wz1_lemma23_local_projection_heavy_fiber_in_source
      prep.shadow C prep.localGrains (anchor y) (coarse y hy)
      (hanchorMem y hy) (anchored.piece_measurable _ _)
      (anchored.piece_nonempty _ _) (hcoarseSubset y hy)
      source.extremal.delta_pos le_rfl source.extremal.delta_le_one hCtop)
  let heightLeft :=
    (retained.commonParentHeight : ℝ) * terminal.sqrtRequested.1
  have hsourceHeight : ∀ y (hy : y ∈ sample), ∀ point ∈ coarse y hy,
      point (2 : Fin 3) ∈ Set.Ico heightLeft
        (heightLeft + Real.sqrt delta) := by
    intro y hy point hpoint
    have hphase := anchored.piece_subset (parentFor y hy) (parentMem y hy) hpoint
    have hband := phase.piece_subset _ _ hphase
    have hraw := band.piece_subset _ _ hband
    have hparentResidue := band.selected_subset
      (phase.selected_subset (parentMem y hy))
    have hparentHeight := retained.parent_height_eq _ hparentResidue
    let data := sources.sourceFor (parentFor y hy) hparentResidue
    have hrawData : point ∈ data.coarseSource := by
      exact hraw
    have hh := data.source_height point hrawData
    have hdataHeight : data.heightLeft =
        (retained.commonParentHeight : ℝ) * terminal.sqrtRequested.1 := by
      rw [data.heightLeft_eq, show data.cell = parentFor y hy by
        exact sources.sourceFor_cell _ hparentResidue, hparentHeight]
    rw [hdataHeight] at hh
    simpa [heightLeft, terminal.sqrtRequested_eq] using hh
  have hheightWindow : Set.Ico heightLeft (heightLeft + Real.sqrt delta) ⊆
      Set.Icc (-1 : ℝ) 1 := by
    rcases phase.selected_nonempty with ⟨parent, hparent⟩
    have hparentResidue := band.selected_subset (phase.selected_subset hparent)
    let data := sources.sourceFor parent hparentResidue
    have hparentHeight := retained.parent_height_eq parent hparentResidue
    have hdataHeight : data.heightLeft =
        (retained.commonParentHeight : ℝ) * terminal.sqrtRequested.1 := by
      rw [data.heightLeft_eq, show data.cell = parent by
        exact sources.sourceFor_cell parent hparentResidue, hparentHeight]
    have hwindow := data.height_window
    rw [hdataHeight] at hwindow
    simpa [heightLeft, terminal.sqrtRequested_eq] using hwindow
  let grainInput (y : ℝ) (hy : y ∈ sample) :
      WZ1Lemma23FullLocalGrainInputGeneralized delta sigma eta C
        prep.windowed.global.sourceSlope :=
    { grain := (fiber y hy).grain
      grain_measurable := (fiber y hy).grain_measurable
      grain_finite := (fiber y hy).grain_finite
      heightLeft := heightLeft
      grain_height := fun point hpoint =>
        hsourceHeight y hy point ((fiber y hy).grain_in_source hpoint)
      grain_volume := (fiber y hy).grain_volume_of_source_lower
        source.extremal.delta_pos (by
          have h := prep.localGrains.local_ad delta le_rfl
            source.extremal.delta_le_one (anchor y) (hanchorMem y hy)
          exact h.2.2.2.1) hCpower (hcoarseFloor y hy)
      center := anchor y
      normal := prep.localGrains.planeMap (anchor y)
      localProjectionCenter := (fiber y hy).center
      normal_unit := prep.localGrains.unit (anchor y) (hanchorMem y hy)
      normal_vertical := prep.planeMap_vertical_bound (anchor y) (hanchorMem y hy)
      grain_square := (fiber y hy).grain_square
      grain_local_strip := (fiber y hy).grain_local_strip
      slope_small := by
        intro z hz
        rw [prep.sourceSlope_eq]
        exact source.globalGrains.slope_bound z (hheightWindow hz)
      projected := fun z => scalarProjection
        (globalGrainDirection (prep.windowed.global.sourceSlope z))
        (horizontalSlice prep.shadow.union z)
      globalAD := by
        intro z hz
        exact prep.exactAD z (hheightWindow hz)
      global_projection_sub := by
        intro z _hz
        rintro value ⟨point, hpoint, rfl⟩
        have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
        have hshading := (fiber y hy).grain_in_shading hlift
        refine ⟨point3 (point 0) (point 1) z, ⟨hshading, by simp [point3]⟩, ?_⟩
        change inner ℝ (point3 (point 0) (point 1) z)
          (globalGrainDirection (prep.windowed.global.sourceSlope z)) =
            point 0 + prep.windowed.global.sourceSlope z * point 1
        rw [PiLp.inner_apply]
        simp [Fin.sum_univ_succ, globalGrainDirection, point3] }
  have hySample : ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      wz1Lemma23SnappedYValue delta y ∈ sample := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨cell, hcell, hcellY⟩
    exact Finset.mem_image.mpr ⟨cell, hcell,
      congrArg (wz1Lemma23SnappedYValue delta) hcellY⟩
  let family : WZ1Lemma23LocalCellFamilyGeneralized
      (rho := delta) (sigma := sigma) (eta := eta) prep.shadow C
      prep.windowed.global.sourceSlope cells prep.localGrains :=
    { sample := sample
      anchor := anchor
      normal := prep.localGrains.planeMap
      normal_vertical := fun y hy =>
        prep.planeMap_vertical_bound (anchor y) (hanchorMem y hy)
      normal_dist := by
        intro y₁ hy₁ y₂ hy₂
        have hpaper₁ : anchor y₁ ∈ retained.shading.union := by
          have := prep.subshading.union_subset (hanchorMem y₁ hy₁)
          rwa [prep.ambient_union] at this
        have hpaper₂ : anchor y₂ ∈ retained.shading.union := by
          have := prep.subshading.union_subset (hanchorMem y₂ hy₂)
          rwa [prep.ambient_union] at this
        rw [prep.planeMap_eq_on_paper ⟨anchor y₁, hanchorMem y₁ hy₁⟩]
        rw [prep.planeMap_eq_on_paper ⟨anchor y₂, hanchorMem y₂ hy₂⟩]
        have hlip := prep.localPaper.planeMap_lipschitz.dist_le_mul
          ⟨anchor y₁, hpaper₁⟩ ⟨anchor y₂, hpaper₂⟩
        simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using hlip
      anchor_dist := by
        intro y₁ hy₁ y₂ hy₂
        rw [hanchorEq y₁ hy₁, hanchorEq y₂ hy₂]
        simpa [hcellForValue y₁ hy₁, hcellForValue y₂ hy₂] using
          graphParents.anchorFor_dist (cellFor y₁ hy₁) (hcellForMem y₁ hy₁)
            (cellFor y₂ hy₂) (hcellForMem y₂ hy₂)
      grainInput := grainInput
      grain_normal := by intro y hy; rfl
      rho_pos := source.extremal.delta_pos
      cells_active := prep.windowed.global.cells_active
      y_mem := hySample
      anchor_mem := fun y hy => hanchorMem _ (hySample y hy)
      local_normal := by intro y hy; rfl
      grain_center := by intro y hy; rfl
      coarseSource := coarse
      coarse_source_measurable := by
        intro y hy
        exact anchored.piece_measurable (parentFor y hy) (parentMem y hy)
      coarse_source_nonempty := by
        intro y hy
        exact anchored.piece_nonempty (parentFor y hy) (parentMem y hy)
      coarse_source_subset := hcoarseSubset
      coarse_source_volume := hcoarseFloor
      grain_in_coarse_source := by
        intro y hy
        let sampleY := wz1Lemma23SnappedYValue delta y
        let hs := hySample y hy
        change (fiber sampleY hs).grain ⊆ coarse sampleY hs
        exact (fiber sampleY hs).grain_in_source
      grain_in_source := by
        intro y hy
        let sampleY := wz1Lemma23SnappedYValue delta y
        let hs := hySample y hy
        change (fiber sampleY hs).grain ⊆ prep.shadow.union
        exact (fiber sampleY hs).grain_in_shading
      grain_in_anchor_ball := by
        intro y hy
        let sampleY := wz1Lemma23SnappedYValue delta y
        let hs := hySample y hy
        change (fiber sampleY hs).grain ⊆
          Metric.closedBall (anchor sampleY) (Real.sqrt delta)
        exact (fiber sampleY hs).grain_in_anchor_ball
      projected_eq := by intro y hy z hz; rfl
      layer_ball := by
        intro y hy idx hidx hidxY
        have hs := hySample y hy
        let value := wz1Lemma23SnappedYValue delta y
        let chosen := cellFor value hs
        have hchosenMem : chosen ∈ cells := hcellForMem value hs
        have hchosenYValue : wz1Lemma23SnappedYValue delta chosen.2.1 =
            wz1Lemma23SnappedYValue delta y := by
          simpa [value] using hcellForValue value hs
        have hchosenY : chosen.2.1 = y :=
          wz1Lemma23SnappedYValue_injective source.extremal.delta_pos hchosenYValue
        have hparent : graphParents.parentOf chosen = graphParents.parentOf idx :=
          graphParents.same_y_parent chosen hchosenMem idx hidx
            (hchosenY.trans hidxY.symm)
        have hanchorSame : graphParents.anchorFor chosen hchosenMem =
            graphParents.anchorFor idx hidx := by
          simp only [PureWZ2TerminalExactGraphParentData.anchorFor, hparent]
        rw [hanchorEq value hs, hanchorSame]
        exact graphParents.canonical_rep_dist_anchor idx hidx }
  rcases wz1_lemma23_local_bin_package_generalized prep.shadow C
      prep.windowed.global.sourceSlope cells prep.localGrains le_rfl
      source.extremal.delta_le_one hsigma hsigmaOne heta hetaSigma hCtop hCpower
      hPlanarSmall hrootSmall20 habsorb family with ⟨localBins, _⟩
  exact ⟨{ family := family, localBins := localBins }⟩

end Kakeya.Assouad
