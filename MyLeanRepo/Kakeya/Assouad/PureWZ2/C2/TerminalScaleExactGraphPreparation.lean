import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleAnchoredPieces
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains
import MyLeanRepo.Kakeya.Assouad.WZ1.AnchoredHierarchyHelpers

/-!
# Exact-`delta` terminal graph preparation

The auxiliary ordinary shading is the union of the genuine localized source
pieces selected in the preceding two finite pigeonholes.  It is a subshading
of the active-cell shadow of the original-family retained paper shading.  Its
graph scale is exactly `delta`; the common projection center and complete-cell
height window are fixed globally.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalBinExactGraphPreparation
    {sigma inputLoss delta stickyLoss : ℝ}
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
    (anchored : PureWZ2TerminalBinAnchoredPieceData phase) where
  graphScale : ℝ := delta
  graphScale_eq : graphScale = delta
  graphScale_pos : 0 < graphScale
  graphScale_one : graphScale ≤ 1
  sourceScale_le_graphScale : delta ≤ graphScale
  ambient : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily retained.shading source.extremal.delta_pos) :=
    pureWZ2ActiveCellShading retained.shading source.extremal.delta_pos
  ambient_union : ambient.union = retained.shading.union
  region : Set Point3 :=
    ⋃ parent : {parent // parent ∈ phase.selectedParents},
      anchored.piece parent.1 parent.2
  region_eq : region =
    ⋃ parent : {parent // parent ∈ phase.selectedParents},
      anchored.piece parent.1 parent.2
  region_measurable : MeasurableSet region
  shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily retained.shading source.extremal.delta_pos)
  carrier_eq : ∀ index, shadow.carrier index = ambient.carrier index ∩ region
  subshading : IsSubshading shadow ambient
  shadow_union : shadow.union = region
  localPaper : PureWZ2LocalGrainData retained.shading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  localPaper_planeMap_eq :
    ∀ point : {point : Point3 // point ∈ retained.shading.union},
      localPaper.planeMap point = source.localGrains.planeMap
        ⟨point, retained.subshading.union_subset point.property⟩
  localGrains : WZ1LocalGrainData shadow sigma
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  planeMap_eq_on_paper :
    ∀ point : {point : Point3 // point ∈ shadow.union},
      localGrains.planeMap point = localPaper.planeMap
        ⟨point, by rw [← ambient_union]; exact subshading.union_subset point.property⟩
  planeMap_vertical_bound : ∀ point ∈ shadow.union,
    |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  windowed : WZ1Lemma23WindowedGlobalSlicePackage
    (delta := delta) (rho := delta) (sigma := sigma) shadow
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  sourceSlope_eq : windowed.global.sourceSlope = source.globalGrains.slope
  exactAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    IsADSet1
      (scalarProjection
        (globalGrainDirection (windowed.global.sourceSlope z))
        (horizontalSlice shadow.union z))
      delta (1 - sigma)
      (10 * Kakeya.realRpowENN delta (-inputLoss))
  localization : WZ1Lemma23GlobalLocalizationInput windowed.global
  volume_eq : volume shadow.union =
    ∑ parent : {parent // parent ∈ phase.selectedParents},
      volume (anchored.piece parent.1 parent.2)
  volume_fraction :
    (phase.selectedParents.card : ENNReal) *
        terminal.sticky.balanced.cellMass ≤
      (512 * (2 * 512 * 57) : ENNReal) * volume shadow.union

/-- Backwards-compatible exact graph preparation on the largest global bin. -/
abbrev PureWZ2TerminalExactGraphPreparation
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    {selection : PureWZ2TerminalParentYSelection parents}
    {residue : PureWZ2TerminalParentYResidueData selection}
    {retained : PureWZ2TerminalRetainedShadingData residue}
    {sources : PureWZ2TerminalSourceFamily retained}
    {band : PureWZ2TerminalFixedBandSelection sources}
    {phase : PureWZ2TerminalHeightPhaseSelection band}
    (anchored : PureWZ2TerminalAnchoredPieceData phase) :=
  PureWZ2TerminalBinExactGraphPreparation anchored

theorem PureWZ2TerminalBinAnchoredPieceData.prepareExactGraphBin
    {sigma inputLoss delta stickyLoss : ℝ}
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
    (anchored : PureWZ2TerminalBinAnchoredPieceData phase)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2TerminalBinExactGraphPreparation anchored) := by
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hdeltaOne : delta ≤ 1 := source.extremal.delta_le_one
  let ambient := pureWZ2ActiveCellShading retained.shading hdelta
  have hambientUnion : ambient.union = retained.shading.union :=
    pureWZ2ActiveCellShading_union retained.shading hdelta retained.whole_cells
  let selectedParents : Finset {parent // parent ∈ phase.selectedParents} :=
    Finset.univ
  let pieceSet (parent : {parent // parent ∈ phase.selectedParents}) : Set Point3 :=
    anchored.piece parent.1 parent.2
  let region : Set Point3 :=
    ⋃ parent : {parent // parent ∈ phase.selectedParents}, pieceSet parent
  have hregionMeas : MeasurableSet region :=
    MeasurableSet.iUnion
      (fun parent : {parent // parent ∈ phase.selectedParents} =>
        anchored.piece_measurable parent.1 parent.2)
  let shadow : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily retained.shading hdelta) :=
    { carrier := fun index => ambient.carrier index ∩ region
      measurable_carrier := fun index =>
        (ambient.measurable_carrier index).inter hregionMeas
      subset_body := fun index => Set.inter_subset_left.trans
        (ambient.subset_body index) }
  have hsub : IsSubshading shadow ambient := fun _ => Set.inter_subset_left
  have hregionAmbient : region ⊆ ambient.union := by
    intro point hpoint
    rcases Set.mem_iUnion.mp hpoint with ⟨parent, hpointPiece⟩
    have hphasePiece := anchored.piece_subset parent.1 parent.2 hpointPiece
    have hbandPiece := phase.piece_subset parent.1 parent.2 hphasePiece
    have hcoarse := band.piece_subset parent.1
      (phase.selected_subset parent.2) hbandPiece
    have hretained := sources.coarse_source_subset parent.1
      (band.selected_subset (phase.selected_subset parent.2)) hcoarse
    rw [hambientUnion]
    exact hretained.1
  have hshadowUnion : shadow.union = region := by
    ext point
    constructor
    · rintro ⟨index, _hambient, hregion⟩
      exact hregion
    · intro hregion
      rcases hregionAmbient hregion with ⟨index, hindex⟩
      exact ⟨index, hindex, hregion⟩
  let C := Kakeya.realRpowENN delta (-inputLoss)
  have hCtop : C ≠ ⊤ := by simp [C, Kakeya.realRpowENN]
  let localPaper := source.localGrains.restrictWithConstant
    retained.subshading le_rfl hCtop
  let ambientLocal := localPaper.toActiveCellShadow
    hdelta retained.whole_cells hbridge
  let localGrains := restrictAndWeakenLocalGrains
    hsub (by rfl) ambientLocal
  have hplane : ∀ point : {point : Point3 // point ∈ shadow.union},
      localGrains.planeMap point = localPaper.planeMap
        ⟨point, by rw [← hambientUnion]; exact hsub.union_subset point.property⟩ := by
    intro point
    have heq := (Classical.choose_spec localPaper.exists_ambient_extension).2
      (⟨point, by rw [← hambientUnion]; exact hsub.union_subset point.property⟩ :
        {point : Point3 // point ∈ retained.shading.union})
    exact heq
  have hvertical : ∀ point ∈ shadow.union,
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point hpoint
    rw [hplane ⟨point, hpoint⟩]
    exact source.planeMap_vertical_bound
      ⟨point, retained.subshading.union_subset (by
        rw [← hambientUnion]
        exact hsub.union_subset hpoint)⟩
  have hball : shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hretained : point ∈ retained.shading.union := by
      rw [← hambientUnion]
      exact hsub.union_subset hpoint
    have hnorm := norm_le_two_of_mem_paperShading hretained
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord : ∀ point ∈ shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hretained : point ∈ retained.shading.union := by
      rw [← hambientUnion]
      exact hsub.union_subset hpoint
    have hbox := shading_union_subset_axisBox hretained
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  let restrictedGlobal :=
    source.globalGrains.toPureWZ2LipschitzGlobalGrainData.restrict
      retained.subshading le_rfl hCtop
  let globalPaper :=
    PureWZ2BoundedLipschitzGlobalGrainData.ofSlopeBound restrictedGlobal <| by
      intro z hz
      exact source.globalGrains.slope_bound z hz
  have hexactSource : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice ambient.union z))
        delta (1 - sigma) (10 * C) := by
    intro z hz
    have h := globalPaper.activeCellShadow_exactAD
      hdelta retained.whole_cells hbridge globalPaper.slope_bound z hz
    rw [show globalPaper.slope = source.globalGrains.slope by rfl] at h
    simpa [ambient, C] using h
  have hexactShadow : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice shadow.union z))
        delta (1 - sigma) (10 * C) := by
    intro z hz
    apply (hexactSource z hz).mono
    rintro value ⟨point, hpoint, rfl⟩
    exact ⟨point, ⟨hsub.union_subset hpoint.1, hpoint.2⟩, rfl⟩
  rcases wz1_lemma23_global_slice_package_of_exact_paper_window
      shadow hdelta le_rfl hdeltaOne hball hcoord
      source.globalGrains.slope source.globalGrains.slope_lipschitz
      source.globalGrains.slope_bound (10 * C)
      (ENNReal.mul_ne_top (by norm_num) hCtop) hexactShadow with
    ⟨global, hsourceSlope⟩
  have hactiveWindow : WZ1Lemma23ActiveCellHeightWindow shadow hdelta := by
    refine ⟨phase.left, ?_⟩
    intro cell hcell
    rcases (wz1Lemma23_mem_active_iff shadow hdelta cell).mp hcell with
      ⟨_hbounded, point, hpointShadow, hpointIndex⟩
    rw [hshadowUnion] at hpointShadow
    rcases Set.mem_iUnion.mp hpointShadow with ⟨parent, hpointPiece⟩
    change point ∈ anchored.piece parent.1 parent.2 at hpointPiece
    have hphasePiece := anchored.piece_subset parent.1 parent.2 hpointPiece
    rw [phase.piece_eq parent.1 parent.2] at hphasePiece
    have hwindow := hphasePiece.2
    rcases Set.mem_iUnion₂.mp hwindow with
      ⟨windowCell, hwindowCell, hpointWindowCell⟩
    have hwindowIndex : wz1Lemma23CellIndex delta point = windowCell :=
      hpointWindowCell
    have hcellEq : windowCell = cell := hwindowIndex.symm.trans hpointIndex
    rw [← hcellEq]
    exact (Finset.mem_filter.mp hwindowCell).2
  let windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := delta) (sigma := sigma) shadow (10 * C) :=
    { global := global
      active_height_window := hactiveWindow }
  have hlocalization : WZ1Lemma23GlobalLocalizationInput global := by
    refine ⟨fun _ => band.center, ?_⟩
    intro heightIndex hheightIndex
    rintro value ⟨point, hpoint, rfl⟩
    rw [hshadowUnion] at hpoint
    rcases Set.mem_iUnion.mp hpoint.1 with ⟨parent, hpointPiece⟩
    change point ∈ anchored.piece parent.1 parent.2 at hpointPiece
    have hbound := anchored.piece_localized parent.1 parent.2 point hpointPiece
    rw [hpoint.2] at hbound
    rw [Metric.mem_closedBall, Real.dist_eq]
    change |inner ℝ point
      (globalGrainDirection (global.sourceSlope (global.selectedHeight heightIndex))) -
        band.center| ≤ Real.sqrt delta
    rw [hsourceSlope]
    exact hbound.trans (by
      rw [← terminal.sqrtRequested_eq]
      nlinarith [terminal.sticky.coarse_extremal.delta_pos])
  have hpieceDisjoint :
      (Set.univ : Set {parent // parent ∈ phase.selectedParents}).PairwiseDisjoint
        pieceSet := by
    intro first _hfirst second _hsecond hne
    have hvalNe : first.1 ≠ second.1 := by
      intro hval
      exact hne (Subtype.ext hval)
    apply (wz1PaperGridCube_disjoint
      (scale := terminal.sqrtRequested.1) hvalNe).mono
    · intro point hpoint
      have hcoarse := band.piece_subset first.1
        (phase.selected_subset first.2)
        (phase.piece_subset first.1 first.2
          (anchored.piece_subset first.1 first.2 hpoint))
      rw [(sources.sourceFor first.1
          (band.selected_subset (phase.selected_subset first.2))).coarseSource_eq,
        (sources.sourceFor first.1
          (band.selected_subset (phase.selected_subset first.2))).fullSource_eq]
        at hcoarse
      simpa only [sources.sourceFor_cell] using hcoarse.1.2
    · intro point hpoint
      have hcoarse := band.piece_subset second.1
        (phase.selected_subset second.2)
        (phase.piece_subset second.1 second.2
          (anchored.piece_subset second.1 second.2 hpoint))
      rw [(sources.sourceFor second.1
          (band.selected_subset (phase.selected_subset second.2))).coarseSource_eq,
        (sources.sourceFor second.1
          (band.selected_subset (phase.selected_subset second.2))).fullSource_eq]
        at hcoarse
      simpa only [sources.sourceFor_cell] using hcoarse.1.2
  have hvolumeEq : volume shadow.union =
      ∑ parent : {parent // parent ∈ phase.selectedParents},
        volume (pieceSet parent) := by
    rw [hshadowUnion]
    rw [show region = ⋃ parent ∈ selectedParents, pieceSet parent by
      ext point
      simp [region, selectedParents]]
    exact MeasureTheory.measure_biUnion_finset
      (fun first hfirst second hsecond hne =>
        hpieceDisjoint (by simp) (by simp) hne)
      (fun parent (_ : parent ∈ selectedParents) =>
        anchored.piece_measurable parent.1 parent.2)
  have hvolumeFraction :
      (phase.selectedParents.card : ENNReal) *
          terminal.sticky.balanced.cellMass ≤
        (512 * (2 * 512 * 57) : ENNReal) * volume shadow.union := by
    rw [hvolumeEq, Finset.mul_sum]
    calc
      (phase.selectedParents.card : ENNReal) *
          terminal.sticky.balanced.cellMass =
        ∑ _parent : {parent // parent ∈ phase.selectedParents},
          terminal.sticky.balanced.cellMass := by
          simp [Finset.sum_const]
      _ ≤ ∑ parent : {parent // parent ∈ phase.selectedParents},
          (512 * (2 * 512 * 57) : ENNReal) * volume (pieceSet parent) := by
          exact Finset.sum_le_sum fun parent _ =>
            anchored.piece_volume parent.1 parent.2
  exact ⟨{
    graphScale := delta
    graphScale_eq := rfl
    graphScale_pos := source.extremal.delta_pos
    graphScale_one := source.extremal.delta_le_one
    sourceScale_le_graphScale := le_rfl
    ambient := ambient
    ambient_union := hambientUnion
    region := region
    region_eq := rfl
    region_measurable := hregionMeas
    shadow := shadow
    carrier_eq := fun _ => rfl
    subshading := hsub
    shadow_union := hshadowUnion
    localPaper := localPaper
    localPaper_planeMap_eq := by intro point; rfl
    localGrains := localGrains
    planeMap_eq_on_paper := hplane
    planeMap_vertical_bound := hvertical
    windowed := windowed
    sourceSlope_eq := hsourceSlope
    exactAD := by
      intro z hz
      rw [hsourceSlope]
      simpa [C] using hexactShadow z hz
    localization := hlocalization
    volume_eq := hvolumeEq
    volume_fraction := hvolumeFraction
  }⟩

/-- Compatibility wrapper for the former largest-bin terminal chain. -/
theorem PureWZ2TerminalAnchoredPieceData.prepareExactGraph
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    {selection : PureWZ2TerminalParentYSelection parents}
    {residue : PureWZ2TerminalParentYResidueData selection}
    {retained : PureWZ2TerminalRetainedShadingData residue}
    {sources : PureWZ2TerminalSourceFamily retained}
    {band : PureWZ2TerminalFixedBandSelection sources}
    {phase : PureWZ2TerminalHeightPhaseSelection band}
    (anchored : PureWZ2TerminalAnchoredPieceData phase)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2TerminalExactGraphPreparation anchored) :=
  anchored.prepareExactGraphBin hbridge

end Kakeya.Assouad
