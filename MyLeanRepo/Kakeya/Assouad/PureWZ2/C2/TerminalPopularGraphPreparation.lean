import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularLocalizedPieces
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureCubicalGlobalSlabAD
import MyLeanRepo.Kakeya.Assouad.WZ1.AnchoredHierarchyHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23WindowedGlobalPackage

/-!
# Graph preparation on localized outer-popular terminal pieces

The graph carrier is the union of the localized pieces, cut out inside the
equal-union partial-cell shadow of the selected outer-popular paper shading.
Complete terminal parents are used by the heterogeneous local-bin proof for
normal and heavy-fibre witnesses, while the graph's measured carrier remains
the high-height outer-popular set.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

def pureWZ2TerminalPopularGraphConstant
    (delta inputLoss : ℝ) : ENNReal :=
  40000 * Kakeya.realRpowENN delta (-inputLoss)

structure PureWZ2TerminalPopularGraphPreparation
    {sigma inputLoss delta stickyLoss : ℝ}
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
    (localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources) where
  ambient : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily selectedCarrier.shading
      source.extremal.delta_pos) :=
    pureWZ2PartialActiveCellShading selectedCarrier.shading
      source.extremal.delta_pos
  ambient_union : ambient.union = selectedCarrier.shading.union
  region : Set Point3 :=
    ⋃ parent : {parent // parent ∈ localized.selectedParents},
      localized.piece parent.1 parent.2
  region_eq : region =
    ⋃ parent : {parent // parent ∈ localized.selectedParents},
      localized.piece parent.1 parent.2
  region_measurable : MeasurableSet region
  shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily selectedCarrier.shading
      source.extremal.delta_pos)
  carrier_eq : ∀ index,
    shadow.carrier index = ambient.carrier index ∩ region
  subshading : IsSubshading shadow ambient
  shadow_union : shadow.union = region
  shadow_selectedRegion : shadow.union ⊆ selection.selectedRegion
  shadow_terminal : shadow.union ⊆ terminalSource.shading.union
  shadow_source : shadow.union ⊆ source.shading.union
  localPaper : PureWZ2LocalGrainData selectedCarrier.shading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  localGrains : WZ1LocalGrainData shadow sigma
    (pureWZ2TerminalPopularGraphConstant delta inputLoss)
  planeMap_eq_on_paper :
    ∀ point : {point : Point3 // point ∈ shadow.union},
      localGrains.planeMap point = localPaper.planeMap
        ⟨point, by
          rw [← ambient_union]
          exact subshading.union_subset point.property⟩
  planeMap_eq_on_source :
    ∀ point : {point : Point3 // point ∈ shadow.union},
      localGrains.planeMap point = source.localGrains.planeMap
        ⟨point, by
          apply selectedCarrier.subshading_source.union_subset
          rw [← ambient_union]
          exact subshading.union_subset point.property⟩
  planeMap_vertical_bound : ∀ point ∈ shadow.union,
    |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  windowed : WZ1Lemma23WindowedGlobalSlicePackage
    (delta := delta) (rho := delta) (sigma := sigma) shadow
    (pureWZ2TerminalPopularGraphConstant delta inputLoss)
  sourceSlope_eq :
    windowed.global.sourceSlope = source.globalGrains.slope
  exactAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    IsADSet1
      (scalarProjection
        (globalGrainDirection (windowed.global.sourceSlope z))
        (horizontalSlice shadow.union z))
      delta (1 - sigma)
      (pureWZ2TerminalPopularGraphConstant delta inputLoss)
  globalSlabAD : HasGlobalSlabAD shadow windowed.global.sourceSlope sigma
    (pureWZ2TerminalPopularGraphConstant delta inputLoss)
  localization : WZ1Lemma23GlobalLocalizationInput windowed.global
  volume_eq : volume shadow.union =
    ∑ parent : {parent // parent ∈ localized.selectedParents},
      volume (localized.piece parent.1 parent.2)
  volume_floor :
    (localized.selectedParents.card : ENNReal) * weightClass.weightFloor ≤
      pureWZ2TerminalPopularLocalizedPieceCost * volume shadow.union

theorem PureWZ2TerminalPopularLocalizedPieceData.prepareGraph
    {sigma inputLoss delta stickyLoss : ℝ}
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
    (localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2TerminalPopularGraphPreparation localized) := by
  let C : ENNReal := Kakeya.realRpowENN delta (-inputLoss)
  let graphC : ENNReal := pureWZ2TerminalPopularGraphConstant delta inputLoss
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hdeltaOne : delta ≤ 1 := source.extremal.delta_le_one
  have hCtop : C ≠ ⊤ := by simp [C, Kakeya.realRpowENN]
  have hgraphCtop : graphC ≠ ⊤ := by
    change (40000 : ENNReal) * C ≠ ⊤
    exact ENNReal.mul_ne_top (by norm_num) hCtop
  have hten : 10 * C ≤ graphC := by
    dsimp only [graphC, pureWZ2TerminalPopularGraphConstant]
    gcongr
    norm_num
  let ambient := pureWZ2PartialActiveCellShading
    selectedCarrier.shading hdelta
  have hambientUnion : ambient.union = selectedCarrier.shading.union :=
    pureWZ2PartialActiveCellShading_union selectedCarrier.shading hdelta
  let pieceSet (parent : {parent // parent ∈ localized.selectedParents}) :
      Set Point3 := localized.piece parent.1 parent.2
  let region : Set Point3 :=
    ⋃ parent : {parent // parent ∈ localized.selectedParents}, pieceSet parent
  have hregionMeas : MeasurableSet region :=
    MeasurableSet.iUnion fun parent :
      {parent // parent ∈ localized.selectedParents} =>
        localized.piece_measurable parent.1 parent.2
  have hregionAmbient : region ⊆ ambient.union := by
    intro point hpoint
    rcases Set.mem_iUnion.mp hpoint with ⟨parent, hpiece⟩
    rw [hambientUnion]
    exact localized.piece_subset_selectedCarrier parent.1 parent.2 hpiece
  let shadow : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily selectedCarrier.shading hdelta) :=
    { carrier := fun index => ambient.carrier index ∩ region
      measurable_carrier := fun index =>
        (ambient.measurable_carrier index).inter hregionMeas
      subset_body := fun index => Set.inter_subset_left.trans
        (ambient.subset_body index) }
  have hsub : IsSubshading shadow ambient := fun _ => Set.inter_subset_left
  have hshadowUnion : shadow.union = region := by
    apply Set.Subset.antisymm
    · rintro point ⟨_index, _hambient, hregion⟩
      exact hregion
    · intro point hregion
      rcases hregionAmbient hregion with ⟨index, hindex⟩
      exact ⟨index, hindex, hregion⟩
  have hshadowSelectedRegion : shadow.union ⊆ selection.selectedRegion := by
    intro point hpoint
    rw [hshadowUnion, show region =
        ⋃ parent : {parent // parent ∈ localized.selectedParents},
          pieceSet parent by rfl] at hpoint
    rcases Set.mem_iUnion.mp hpoint with ⟨parent, hpiece⟩
    rw [selection.selectedRegion_eq]
    exact Set.mem_iUnion₂.mpr ⟨parent.1,
      localized.selected_subset parent.2,
      localized.piece_subset_parent parent.1 parent.2 hpiece⟩
  let localPaper : PureWZ2LocalGrainData selectedCarrier.shading sigma C :=
    source.localGrains.restrictWithConstant
      selectedCarrier.subshading_source le_rfl hCtop
  let ambientLocal : WZ1LocalGrainData ambient sigma (10 * C) :=
    localPaper.toPartialActiveCellShadow hdelta hbridge
  let localGrains : WZ1LocalGrainData shadow sigma graphC :=
    restrictAndWeakenLocalGrains hsub hten ambientLocal
  have hplane : ∀ point : {point : Point3 // point ∈ shadow.union},
      localGrains.planeMap point = localPaper.planeMap
        ⟨point, by
          rw [← hambientUnion]
          exact hsub.union_subset point.property⟩ := by
    intro point
    have heq := (Classical.choose_spec localPaper.exists_ambient_extension).2
      (⟨point, by
        rw [← hambientUnion]
        exact hsub.union_subset point.property⟩ :
        {point : Point3 // point ∈ selectedCarrier.shading.union})
    exact heq
  have hverticalPaper :
      ∀ point : {point : Point3 // point ∈ selectedCarrier.shading.union},
        |localPaper.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    have hsource := selectedCarrier.subshading_source.union_subset point.property
    simpa [localPaper, PureWZ2LocalGrainData.restrictWithConstant] using
      source.planeMap_vertical_bound ⟨point, hsource⟩
  have hverticalAmbient : ∀ point ∈ ambient.union,
      |ambientLocal.planeMap point (2 : Fin 3)| ≤ 1 / 2 :=
    localPaper.toPartialActiveCellShadow_vertical_bound
      hdelta hbridge hverticalPaper
  have hvertical : ∀ point ∈ shadow.union,
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point hpoint
    exact hverticalAmbient point (hsub.union_subset hpoint)
  have hball : shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hselected : point ∈ selectedCarrier.shading.union := by
      rw [← hambientUnion]
      exact hsub.union_subset hpoint
    have hsource := selectedCarrier.subshading_source.union_subset hselected
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord : ∀ point ∈ shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hselected : point ∈ selectedCarrier.shading.union := by
      rw [← hambientUnion]
      exact hsub.union_subset hpoint
    have hsource := selectedCarrier.subshading_source.union_subset hselected
    have hbox := shading_union_subset_axisBox hsource
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hexact : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice shadow.union z))
        delta (1 - sigma) graphC := by
    intro z hz
    apply ((restrictedPrepared.exactAD z hz).mono ?_).mono_constant
      (by simpa [graphC, C] using hten)
    rintro value ⟨point, hpoint, rfl⟩
    refine ⟨point, ⟨?_, hpoint.2⟩, rfl⟩
    rw [pureWZ2PartialActiveCellShading_union]
    exact selectedCarrier.subshading_restricted.union_subset (by
      rw [← hambientUnion]
      exact hsub.union_subset hpoint.1)
  rcases wz1_lemma23_global_slice_package_of_exact_paper_window
      shadow hdelta le_rfl hdeltaOne hball hcoord
      source.globalGrains.slope source.globalGrains.slope_lipschitz
      source.globalGrains.slope_bound graphC hgraphCtop hexact with
    ⟨global, hsourceSlope⟩
  have hactive : WZ1Lemma23ActiveCellHeightWindow shadow hdelta := by
    refine ⟨localized.left, ?_⟩
    intro cell hcell
    rcases (wz1Lemma23_mem_active_iff shadow hdelta cell).mp hcell with
      ⟨_hbounded, point, hpointShadow, hpointIndex⟩
    rw [hshadowUnion] at hpointShadow
    rcases Set.mem_iUnion.mp hpointShadow with ⟨parent, hpointPiece⟩
    have hwindow := localized.piece_height_window parent.1 parent.2
      point hpointPiece
    rcases Set.mem_iUnion₂.mp hwindow with
      ⟨windowCell, hwindowCell, hpointWindowCell⟩
    have hcellEq : windowCell = cell :=
      hpointWindowCell.symm.trans hpointIndex
    rw [← hcellEq]
    exact (Finset.mem_filter.mp hwindowCell).2
  let windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := delta) (sigma := sigma) shadow graphC :=
    { global := global
      active_height_window := hactive }
  have hlocalization : WZ1Lemma23GlobalLocalizationInput global := by
    refine ⟨fun _ => localized.center, ?_⟩
    intro heightIndex hheightIndex
    rintro value ⟨point, hpoint, rfl⟩
    rw [hshadowUnion] at hpoint
    rcases Set.mem_iUnion.mp hpoint.1 with ⟨parent, hpointPiece⟩
    have hbound := localized.piece_localized parent.1 parent.2 point hpointPiece
    rw [hpoint.2] at hbound
    rw [Metric.mem_closedBall, Real.dist_eq]
    change |inner ℝ point
        (globalGrainDirection (global.sourceSlope
          (global.selectedHeight heightIndex))) - localized.center| ≤
      Real.sqrt delta
    rw [hsourceSlope]
    exact hbound.trans (by
      rw [← terminal.sqrtRequested_eq]
      nlinarith [terminal.sticky.coarse_extremal.delta_pos])
  have hshadowSlab : HasGlobalSlabAD shadow source.globalGrains.slope
      sigma graphC := by
    intro z hz
    have hpaper := source.globalGrains.paperGlobalSlabAD hdelta hdeltaOne
      source.cubical hbridge z hz
    have hbounded : globalGrainProjection source.globalGrains.slope
        (globalGrainSlab source.shading.union z delta) ⊆
          Set.Icc (-4 : ℝ) 4 := by
      rintro value ⟨point, hpoint, rfl⟩
      have hsourcePoint : point ∈ source.shading.union := hpoint.1.1
      have hheight : point (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 := hpoint.2
      have hbox := shading_union_subset_axisBox hsourcePoint
      have hx : |point 0| ≤ 1 := by
        simpa [Kakeya.Streamlined.axisBox] using hbox.1
      have hy : |point 1| ≤ 1 := by
        simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
      have hslope : |source.globalGrains.slope (point 2)| ≤ 3 :=
        source.globalGrains.slope_bound _ hheight
      have hformula : inner ℝ point
          (globalGrainDirection (source.globalGrains.slope (point 2))) =
          point 0 + source.globalGrains.slope (point 2) * point 1 := by
        simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      change inner ℝ point
        (globalGrainDirection (source.globalGrains.slope (point 2))) ∈
          Set.Icc (-4 : ℝ) 4
      rw [hformula]
      have hvalue : |point 0 + source.globalGrains.slope (point 2) * point 1| ≤
          4 := by
        calc
          _ ≤ |point 0| +
              |source.globalGrains.slope (point 2)| * |point 1| := by
            simpa [abs_mul] using abs_add_le (point 0)
              (source.globalGrains.slope (point 2) * point 1)
          _ ≤ 1 + 3 * 1 := by gcongr
          _ = 4 := by norm_num
      exact abs_le.mp hvalue
    have hinternal := hbridge.1 _ delta (1 - sigma) (4000 * C)
      hbounded hpaper
    have hinternal' : IsADSet1
        (globalGrainProjection source.globalGrains.slope
          (globalGrainSlab source.shading.union z delta))
        delta (1 - sigma) graphC := by
      convert hinternal using 1 <;>
        simp [graphC, pureWZ2TerminalPopularGraphConstant, C] <;> ring
    apply hinternal'.mono
    rintro value ⟨point, hpoint, rfl⟩
    refine ⟨point, ?_, rfl⟩
    exact ⟨⟨selectedCarrier.subshading_source.union_subset (by
      rw [← hambientUnion]
      exact hsub.union_subset hpoint.1.1), hpoint.1.2⟩, hpoint.2⟩
  have hpieceDisjoint :
      (Set.univ : Set {parent // parent ∈ localized.selectedParents}).PairwiseDisjoint
        pieceSet := by
    intro first _hfirst second _hsecond hne
    have hvalNe : first.1 ≠ second.1 := by
      intro hval
      exact hne (Subtype.ext hval)
    exact (wz1PaperGridCube_disjoint hvalNe).mono
      (localized.piece_subset_parent first.1 first.2)
      (localized.piece_subset_parent second.1 second.2)
  have hvolumeEq : volume shadow.union =
      ∑ parent : {parent // parent ∈ localized.selectedParents},
        volume (pieceSet parent) := by
    rw [hshadowUnion]
    rw [show region = ⋃ parent ∈ (Finset.univ :
        Finset {parent // parent ∈ localized.selectedParents}),
        pieceSet parent by ext point; simp [region]]
    exact MeasureTheory.measure_biUnion_finset
      (fun first hfirst second hsecond hne =>
        hpieceDisjoint (by simpa using hfirst) (by simpa using hsecond) hne)
      (fun parent _ => localized.piece_measurable parent.1 parent.2)
  have hvolumeFloor :
      (localized.selectedParents.card : ENNReal) * weightClass.weightFloor ≤
        pureWZ2TerminalPopularLocalizedPieceCost * volume shadow.union := by
    rw [hvolumeEq, Finset.mul_sum]
    calc
      (localized.selectedParents.card : ENNReal) * weightClass.weightFloor =
          ∑ _parent : {parent // parent ∈ localized.selectedParents},
            weightClass.weightFloor := by simp [Finset.sum_const]
      _ ≤ ∑ parent : {parent // parent ∈ localized.selectedParents},
          pureWZ2TerminalPopularLocalizedPieceCost *
            volume (pieceSet parent) := by
        exact Finset.sum_le_sum fun parent _ =>
          localized.piece_volume parent.1 parent.2
  exact ⟨{
    ambient := ambient
    ambient_union := hambientUnion
    region := region
    region_eq := rfl
    region_measurable := hregionMeas
    shadow := shadow
    carrier_eq := fun _ => rfl
    subshading := hsub
    shadow_union := hshadowUnion
    shadow_selectedRegion := hshadowSelectedRegion
    shadow_terminal := fun point hpoint => by
      have hselected : point ∈ selectedCarrier.shading.union := by
        rw [← hambientUnion]
        exact hsub.union_subset hpoint
      rcases hselected with ⟨sourceIndex, hsourceIndex⟩
      have hcarrier : point ∈ carrier.shading.carrier sourceIndex := by
        rw [selectedCarrier.carrier_eq] at hsourceIndex
        rw [restricted.carrier_eq] at hsourceIndex
        exact hsourceIndex.1.1
      rw [carrier.carrier_eq] at hcarrier
      rcases carrier.zeroExtension.carrier_support sourceIndex point
          hcarrier.1 with
        ⟨index, _heq, hindex⟩
      exact ⟨index, by rw [terminalSource.shading_eq]; exact hindex⟩
    shadow_source := fun _ hpoint =>
      selectedCarrier.subshading_source.union_subset (by
        rw [← hambientUnion]
        exact hsub.union_subset hpoint)
    localPaper := localPaper
    localGrains := localGrains
    planeMap_eq_on_paper := hplane
    planeMap_eq_on_source := by
      intro point
      rw [hplane point]
      rfl
    planeMap_vertical_bound := hvertical
    windowed := windowed
    sourceSlope_eq := by simpa [windowed] using hsourceSlope
    exactAD := by
      intro z hz
      change IsADSet1
        (scalarProjection (globalGrainDirection (global.sourceSlope z))
          (horizontalSlice shadow.union z))
        delta (1 - sigma) graphC
      rw [hsourceSlope]
      exact hexact z hz
    globalSlabAD := by
      simpa [windowed, hsourceSlope] using hshadowSlab
    localization := by simpa [windowed] using hlocalization
    volume_eq := by simpa [pieceSet] using hvolumeEq
    volume_floor := by simpa [pieceSet] using hvolumeFloor
  }⟩

end Kakeya.Assouad

end
