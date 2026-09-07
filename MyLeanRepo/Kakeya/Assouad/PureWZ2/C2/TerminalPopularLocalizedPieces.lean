import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularCoarseSources
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularSelectedParentCarrier
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleGraphPreparation
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma18SpatialSelfCenteredCover

/-!
# Common-band terminal pieces on the outer-popular carrier

This file performs the three remaining finite selections before the terminal
Lemma-23 graph: one common projection band, one common height-window phase,
and one self-centered anchored piece in each surviving official parent.  The
whole construction stays inside the outer-popular carrier and pays only the
fixed factor `512 * 57 * 2 * 512` against the pre-line parent weight floor.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

def pureWZ2TerminalPopularLocalizedPieceCost : ENNReal :=
  512 * 57 * 2 * 512

structure PureWZ2TerminalPopularLocalizedPieceData
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
    (sources : PureWZ2TerminalPopularCoarseSourceFamily selection) where
  commonBand : ℤ
  commonBand_mem : commonBand ∈ Finset.Icc (-28 : ℤ) 28
  center : ℝ := line.lineLevel +
    (commonBand : ℝ) * terminal.sqrtRequested.1 / 2
  center_eq : center = line.lineLevel +
    (commonBand : ℝ) * terminal.sqrtRequested.1 / 2
  commonPhase : Bool
  left : ℝ :=
    (selection.commonParentHeight : ℝ) * terminal.sqrtRequested.1 -
      delta / 2 + if commonPhase then delta else 0
  left_eq : left =
    (selection.commonParentHeight : ℝ) * terminal.sqrtRequested.1 -
      delta / 2 + if commonPhase then delta else 0
  selectedParents : Finset (ℤ × ℤ × ℤ)
  selected_nonempty : selectedParents.Nonempty
  selected_subset : selectedParents ⊆ selection.selected
  parent_card : selection.selected.card ≤ 114 * selectedParents.card
  anchor : ∀ parent, parent ∈ selectedParents → Point3
  piece : ∀ parent, parent ∈ selectedParents → Set Point3
  piece_measurable : ∀ parent (hparent : parent ∈ selectedParents),
    MeasurableSet (piece parent hparent)
  piece_nonempty : ∀ parent (hparent : parent ∈ selectedParents),
    (piece parent hparent).Nonempty
  anchor_mem : ∀ parent (hparent : parent ∈ selectedParents),
    anchor parent hparent ∈ piece parent hparent
  piece_subset_selectedCarrier :
    ∀ parent (hparent : parent ∈ selectedParents),
      piece parent hparent ⊆ selectedCarrier.shading.union
  piece_subset_parent : ∀ parent (hparent : parent ∈ selectedParents),
    piece parent hparent ⊆
      wz1PaperGridCube terminal.sqrtRequested.1 parent
  piece_ball : ∀ parent (hparent : parent ∈ selectedParents),
    piece parent hparent ⊆
      Metric.closedBall (anchor parent hparent) terminal.sqrtRequested.1
  piece_localized : ∀ parent (hparent : parent ∈ selectedParents),
    ∀ point ∈ piece parent hparent,
      |inner ℝ point
            (globalGrainDirection
              (source.globalGrains.slope (point (2 : Fin 3)))) - center| ≤
        terminal.sqrtRequested.1 / 2
  piece_height_window : ∀ parent (hparent : parent ∈ selectedParents),
    ∀ point ∈ piece parent hparent,
      point ∈ wz1Lemma23CellHeightWindowSet delta
        source.extremal.delta_pos left
  piece_volume : ∀ parent (hparent : parent ∈ selectedParents),
    weightClass.weightFloor ≤
      pureWZ2TerminalPopularLocalizedPieceCost *
        volume (piece parent hparent)
  y_separated : ∀ first ∈ selectedParents, ∀ second ∈ selectedParents,
    first ≠ second → (512 : ℤ) ≤ |first.2.1 - second.2.1|

theorem PureWZ2TerminalPopularCoarseSourceFamily.localize
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
    (sources : PureWZ2TerminalPopularCoarseSourceFamily selection) :
    Nonempty (PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources) := by
  let root := terminal.sqrtRequested.1
  have hroot : 0 < root := terminal.sticky.coarse_extremal.delta_pos
  have hdeltaRoot : delta ≤ root := by
    rw [show root = Real.sqrt delta by exact terminal.sqrtRequested_eq]
    nlinarith [Real.sqrt_nonneg delta,
      Real.sq_sqrt source.extremal.delta_pos.le,
      source.extremal.delta_le_one]
  have hsourceSelectedCarrier :
      ∀ parent (hparent : parent ∈ selection.selected),
        (sources.sourceFor parent hparent).coarseSource ⊆
          selectedCarrier.shading.union := by
    intro parent hparent point hpoint
    have hsource := sources.coarse_source_subset parent hparent hpoint
    rw [selectedCarrier.union_eq]
    refine ⟨hsource.1, ?_⟩
    rw [selection.selectedRegion_eq]
    refine Set.mem_iUnion₂.mpr ⟨parent, hparent, ?_⟩
    let data := sources.sourceFor parent hparent
    rw [data.coarseSource_eq, data.fullSource_eq] at hpoint
    simpa only [data, sources.sourceFor_cell parent hparent] using hpoint.1.2
  let bands : Finset ℤ := Finset.Icc (-28 : ℤ) 28
  have hbandsNonempty : bands.Nonempty := ⟨0, by simp [bands]⟩
  have hbandsCard : bands.card = 57 := by simp [bands, Int.card_Icc]
  let projection (point : Point3) : ℝ := inner ℝ point
    (globalGrainDirection
      (restrictedPrepared.windowed.global.extendedSlope (point (2 : Fin 3))))
  let bandCenter (band : ℤ) : ℝ :=
    line.lineLevel + (band : ℝ) * root / 2
  let bandPiece (parent : ℤ × ℤ × ℤ)
      (hparent : parent ∈ selection.selected) (band : ℤ) : Set Point3 :=
    (sources.sourceFor parent hparent).coarseSource ∩
      {point | |projection point - bandCenter band| ≤ root / 2}
  have hprojectionMeasurable : Measurable projection := by
    have hslope : Measurable fun point : Point3 =>
        restrictedPrepared.windowed.global.extendedSlope (point (2 : Fin 3)) :=
      (continuousOn_univ.mp
        restrictedPrepared.windowed.global.extendedSlope_lipschitz.continuousOn).measurable.comp
          (by fun_prop)
    have hdirection : Measurable fun point : Point3 =>
        globalGrainDirection
          (restrictedPrepared.windowed.global.extendedSlope
            (point (2 : Fin 3))) := by
      have hcontinuous : Continuous globalGrainDirection := by
        have heq : globalGrainDirection = fun slope : ℝ =>
            EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
              slope • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) := by
          funext slope
          rfl
        rw [heq]
        exact continuous_const.add (continuous_id.smul continuous_const)
      exact hcontinuous.measurable.comp hslope
    exact continuous_inner.measurable.comp
      (Measurable.prodMk measurable_id hdirection)
  have hpieceMeasurable : ∀ parent (hparent : parent ∈ selection.selected) band,
      MeasurableSet (bandPiece parent hparent band) := by
    intro parent hparent band
    apply (sources.sourceFor parent hparent).coarseSource_measurable.inter
    have hset : {point : Point3 |
        |projection point - bandCenter band| ≤ root / 2} =
        (fun point => projection point - bandCenter band) ⁻¹'
          Set.Icc (-root / 2) (root / 2) := by
      ext point
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc]
      rw [abs_le]
      constructor <;> intro h <;> exact ⟨by linarith [h.1], h.2⟩
    rw [hset]
    exact (hprojectionMeasurable.sub measurable_const) measurableSet_Icc
  have hprojectionSource : ∀ parent (hparent : parent ∈ selection.selected),
      ∀ point ∈ (sources.sourceFor parent hparent).coarseSource,
        projection point = inner ℝ point
          (globalGrainDirection
            (source.globalGrains.slope (point (2 : Fin 3)))) := by
    intro parent hparent point hpoint
    have hsource := hsourceSelectedCarrier parent hparent hpoint
    have hbox := shading_union_subset_axisBox
      (selectedCarrier.subshading_source.union_subset hsource)
    have hheight : point (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2
    dsimp only [projection]
    rw [restrictedPrepared.windowed.global.extendedSlope_eq _ hheight,
      restrictedPrepared.sourceSlope_eq]
  have hbandCover : ∀ parent (hparent : parent ∈ selection.selected),
      (sources.sourceFor parent hparent).coarseSource ⊆
        ⋃ band ∈ bands, bandPiece parent hparent band := by
    intro parent hparent point hpoint
    have hfixed := selectedCarrier.fixed_line_localization point
      (hsourceSelectedCarrier parent hparent hpoint)
    have hprojectionEq := hprojectionSource parent hparent point hpoint
    let quotient := 2 * (projection point - line.lineLevel) / root
    let band : ℤ := Int.floor quotient
    have hquotientBounds : (-28 : ℝ) ≤ quotient ∧ quotient ≤ 28 := by
      dsimp only [quotient]
      rw [div_le_iff₀ hroot, le_div_iff₀ hroot, hprojectionEq]
      have hbounds := abs_le.mp hfixed
      constructor <;> nlinarith
    have hbandMem : band ∈ bands := by
      rw [Finset.mem_Icc]
      constructor
      · apply Int.le_floor.mpr
        simpa only [Int.cast_neg, Int.cast_ofNat] using hquotientBounds.1
      · have hfloor := Int.floor_le quotient
        have hcast : (band : ℝ) ≤ 28 := hfloor.trans hquotientBounds.2
        exact_mod_cast hcast
    have hqLower : (band : ℝ) ≤ quotient := Int.floor_le quotient
    have hqUpper : quotient ≤ (band : ℝ) + 1 :=
      (Int.lt_floor_add_one quotient).le
    have hrelation : quotient * root =
        2 * (projection point - line.lineLevel) := by
      dsimp only [quotient]
      field_simp [hroot.ne']
    have hbandDistance : |projection point - bandCenter band| ≤ root / 2 := by
      rw [abs_le]
      dsimp only [bandCenter]
      constructor <;> nlinarith
    exact Set.mem_iUnion₂.mpr ⟨band, hbandMem, hpoint, hbandDistance⟩
  have hbestBandExists : ∀ parent (hparent : parent ∈ selection.selected),
      ∃ band ∈ bands,
        volume (sources.sourceFor parent hparent).coarseSource ≤
          57 * volume (bandPiece parent hparent band) := by
    intro parent hparent
    rcases Finset.exists_max_image bands
        (fun band => volume (bandPiece parent hparent band))
        hbandsNonempty with ⟨band, hband, hmax⟩
    refine ⟨band, hband, (measure_mono
      (hbandCover parent hparent)).trans
        ((MeasureTheory.measure_biUnion_finset_le bands
          (bandPiece parent hparent)).trans ?_)⟩
    calc
      ∑ other ∈ bands, volume (bandPiece parent hparent other) ≤
          ∑ _other ∈ bands, volume (bandPiece parent hparent band) := by
        exact Finset.sum_le_sum fun other hother => hmax other hother
      _ = 57 * volume (bandPiece parent hparent band) := by
        rw [Finset.sum_const, hbandsCard]
        norm_num
  let bestBand (parent : ℤ × ℤ × ℤ)
      (hparent : parent ∈ selection.selected) : ℤ :=
    Classical.choose (hbestBandExists parent hparent)
  have hbestBandMem : ∀ parent (hparent : parent ∈ selection.selected),
      bestBand parent hparent ∈ bands := fun parent hparent =>
    (Classical.choose_spec (hbestBandExists parent hparent)).1
  have hbestBandVolume : ∀ parent (hparent : parent ∈ selection.selected),
      volume (sources.sourceFor parent hparent).coarseSource ≤
        57 * volume (bandPiece parent hparent (bestBand parent hparent)) :=
    fun parent hparent =>
      (Classical.choose_spec (hbestBandExists parent hparent)).2
  let bandLabel (parent : ℤ × ℤ × ℤ) : ℤ :=
    if hparent : parent ∈ selection.selected then bestBand parent hparent else 0
  rcases finset_exists_max_fiber_with_product_bound
      selection.selected bandLabel selection.selected_nonempty with
    ⟨commonBand, hcommonBandImage, hbandCardRaw, hbandSelectedNonempty⟩
  let bandSelected := selection.selected.filter fun parent =>
    bandLabel parent = commonBand
  have hbandImageCard : (selection.selected.image bandLabel).card ≤ 57 := by
    apply (Finset.card_le_card ?_).trans_eq hbandsCard
    intro band hband
    rcases Finset.mem_image.mp hband with ⟨parent, hparent, rfl⟩
    simpa [bandLabel, hparent] using hbestBandMem parent hparent
  have hbandCard : selection.selected.card ≤ 57 * bandSelected.card :=
    hbandCardRaw.trans (Nat.mul_le_mul_right bandSelected.card hbandImageCard)
  have hbandSubset : bandSelected ⊆ selection.selected :=
    Finset.filter_subset _ _
  have hbandEq : ∀ parent (hparent : parent ∈ bandSelected),
      bestBand parent (hbandSubset hparent) = commonBand := by
    intro parent hparent
    simpa [bandLabel, hbandSubset hparent] using
      (Finset.mem_filter.mp hparent).2
  let baseLeft :=
    (selection.commonParentHeight : ℝ) * root - delta / 2
  let phaseLeft (phase : Bool) := baseLeft + if phase then delta else 0
  let phaseSet (phase : Bool) :=
    wz1Lemma23CellHeightWindowSet delta source.extremal.delta_pos
      (phaseLeft phase)
  let bandSelectedPiece (parent : ℤ × ℤ × ℤ)
      (hparent : parent ∈ bandSelected) : Set Point3 :=
    bandPiece parent (hbandSubset hparent) commonBand
  let phasePiece (parent : ℤ × ℤ × ℤ)
      (hparent : parent ∈ bandSelected) (phase : Bool) : Set Point3 :=
    bandSelectedPiece parent hparent ∩ phaseSet phase
  have hphaseMeas : ∀ parent (hparent : parent ∈ bandSelected) phase,
      MeasurableSet (phasePiece parent hparent phase) := by
    intro parent hparent phase
    exact (hpieceMeasurable parent (hbandSubset hparent) commonBand).inter
      (wz1Lemma23CellHeightWindowSet_measurable delta
        source.extremal.delta_pos (phaseLeft phase))
  have hphaseCover : ∀ parent (hparent : parent ∈ bandSelected),
      bandSelectedPiece parent hparent ⊆
        phasePiece parent hparent false ∪ phasePiece parent hparent true := by
    intro parent hparent point hpoint
    have hsource := hpoint.1
    have hheight := (sources.sourceFor parent (hbandSubset hparent)).source_height
      point hsource
    rw [sources.sourceFor_cell parent (hbandSubset hparent),
      selection.parent_height_eq parent (hbandSubset hparent)] at hheight
    let cell := wz1Lemma23CellIndex delta point
    have hpointSource := hsourceSelectedCarrier parent
      (hbandSubset hparent) hsource
    have hnorm := norm_le_two_of_mem_paperShading
      (selectedCarrier.subshading_source.union_subset hpointSource)
    have hbounded : cell ∈ wz1Lemma23BoundedCells delta
        source.extremal.delta_pos :=
      wz1Lemma23_index_mem_bounded_two source.extremal.delta_pos hnorm
    have hcenterClose :=
      ((wz1_lemma23_snapped_cell_geometry delta source.extremal.delta_pos
        source.extremal.delta_le_one).2.1 cell point rfl).1 (2 : Fin 3)
    let centerZ := (wz1Lemma23SnappedPoint delta cell) (2 : Fin 3)
    have hcenterLower : baseLeft ≤ centerZ := by
      dsimp only [baseLeft, centerZ]
      rw [show (wz1Lemma23SnappedPoint delta cell) (2 : Fin 3) =
        (wz1Lemma23CellCenter delta cell) (2 : Fin 3) by rfl]
      linarith [hheight.1, (abs_le.mp hcenterClose).2]
    have hcenterUpper : centerZ ≤ baseLeft + root + delta := by
      dsimp only [baseLeft, centerZ]
      rw [show (wz1Lemma23SnappedPoint delta cell) (2 : Fin 3) =
        (wz1Lemma23CellCenter delta cell) (2 : Fin 3) by rfl]
      linarith [hheight.2.le, (abs_le.mp hcenterClose).1]
    have hwindowMem : point ∈ phaseSet false ∨ point ∈ phaseSet true := by
      by_cases hfirst : centerZ ≤ baseLeft + root
      · left
        refine Set.mem_iUnion₂.mpr ⟨cell, Finset.mem_filter.mpr
          ⟨hbounded, ?_⟩, rfl⟩
        change centerZ ∈ Set.Icc (phaseLeft false)
          (phaseLeft false + Real.sqrt delta)
        rw [show phaseLeft false = baseLeft by simp [phaseLeft],
          show Real.sqrt delta = root by exact terminal.sqrtRequested_eq.symm]
        exact ⟨hcenterLower, hfirst⟩
      · right
        refine Set.mem_iUnion₂.mpr ⟨cell, Finset.mem_filter.mpr
          ⟨hbounded, ?_⟩, rfl⟩
        have hsecondLower : baseLeft + delta ≤ centerZ := by
          have : baseLeft + delta ≤ baseLeft + root := by linarith
          linarith
        change centerZ ∈ Set.Icc (phaseLeft true)
          (phaseLeft true + Real.sqrt delta)
        rw [show phaseLeft true = baseLeft + delta by simp [phaseLeft],
          show Real.sqrt delta = root by exact terminal.sqrtRequested_eq.symm]
        exact ⟨hsecondLower, by linarith⟩
    rcases hwindowMem with hfirst | hsecond
    · exact Or.inl ⟨hpoint, hfirst⟩
    · exact Or.inr ⟨hpoint, hsecond⟩
  have hbestPhaseExists : ∀ parent (hparent : parent ∈ bandSelected),
      ∃ phase : Bool, volume (bandSelectedPiece parent hparent) ≤
        2 * volume (phasePiece parent hparent phase) := by
    intro parent hparent
    have hcoverVolume : volume (bandSelectedPiece parent hparent) ≤
        volume (phasePiece parent hparent false) +
          volume (phasePiece parent hparent true) :=
      (measure_mono (hphaseCover parent hparent)).trans
      (MeasureTheory.measure_union_le
        (phasePiece parent hparent false) (phasePiece parent hparent true))
    by_cases horder : volume (phasePiece parent hparent false) ≤
        volume (phasePiece parent hparent true)
    · exact ⟨true, hcoverVolume.trans (by
        calc
          volume (phasePiece parent hparent false) +
              volume (phasePiece parent hparent true) ≤
            volume (phasePiece parent hparent true) +
              volume (phasePiece parent hparent true) := by gcongr
          _ = 2 * volume (phasePiece parent hparent true) := by ring)⟩
    · have hle : volume (phasePiece parent hparent true) ≤
          volume (phasePiece parent hparent false) := le_of_not_ge horder
      exact ⟨false, hcoverVolume.trans (by
        calc
          volume (phasePiece parent hparent false) +
              volume (phasePiece parent hparent true) ≤
            volume (phasePiece parent hparent false) +
              volume (phasePiece parent hparent false) := by gcongr
          _ = 2 * volume (phasePiece parent hparent false) := by ring)⟩
  let bestPhase (parent : ℤ × ℤ × ℤ)
      (hparent : parent ∈ bandSelected) : Bool :=
    Classical.choose (hbestPhaseExists parent hparent)
  have hbestPhaseVolume : ∀ parent (hparent : parent ∈ bandSelected),
      volume (bandSelectedPiece parent hparent) ≤
        2 * volume (phasePiece parent hparent (bestPhase parent hparent)) :=
    fun parent hparent =>
      Classical.choose_spec (hbestPhaseExists parent hparent)
  let phaseLabel (parent : ℤ × ℤ × ℤ) : Bool :=
    if hparent : parent ∈ bandSelected then bestPhase parent hparent else false
  rcases finset_exists_max_fiber_with_product_bound bandSelected phaseLabel
      hbandSelectedNonempty with
    ⟨commonPhase, _hphaseImage, hphaseCardRaw, hphaseSelectedNonempty⟩
  let phaseSelected := bandSelected.filter fun parent =>
    phaseLabel parent = commonPhase
  have hphaseImageCard : (bandSelected.image phaseLabel).card ≤ 2 := by
    exact (Finset.card_le_univ _).trans_eq (by decide)
  have hphaseCard : bandSelected.card ≤ 2 * phaseSelected.card :=
    hphaseCardRaw.trans (Nat.mul_le_mul_right phaseSelected.card hphaseImageCard)
  have hphaseSubset : phaseSelected ⊆ bandSelected := Finset.filter_subset _ _
  have hphaseEq : ∀ parent (hparent : parent ∈ phaseSelected),
      bestPhase parent (hphaseSubset hparent) = commonPhase := by
    intro parent hparent
    simpa [phaseLabel, hphaseSubset hparent] using
      (Finset.mem_filter.mp hparent).2
  let preAnchorPiece (parent : ℤ × ℤ × ℤ)
      (hparent : parent ∈ phaseSelected) : Set Point3 :=
    phasePiece parent (hphaseSubset hparent) commonPhase
  have hpreMeas : ∀ parent (hparent : parent ∈ phaseSelected),
      MeasurableSet (preAnchorPiece parent hparent) :=
    fun parent hparent => hphaseMeas parent (hphaseSubset hparent) commonPhase
  have hpreVolume : ∀ parent (hparent : parent ∈ phaseSelected),
      weightClass.weightFloor ≤ (512 * 57 * 2 : ENNReal) *
        volume (preAnchorPiece parent hparent) := by
    intro parent hparent
    let hparentSelected := hbandSubset (hphaseSubset hparent)
    have hbandPieceEq :
        bandPiece parent hparentSelected (bestBand parent hparentSelected) =
          bandSelectedPiece parent (hphaseSubset hparent) := by
      rw [hbandEq parent (hphaseSubset hparent)]
    have hphasePieceEq :
        phasePiece parent (hphaseSubset hparent)
            (bestPhase parent (hphaseSubset hparent)) =
          preAnchorPiece parent hparent := by
      rw [hphaseEq parent hparent]
    calc
      weightClass.weightFloor ≤
          512 * volume (sources.sourceFor parent hparentSelected).coarseSource :=
        (sources.sourceFor parent hparentSelected).weightFloor_le_coarseSource
      _ ≤ 512 * (57 * volume
          (bandPiece parent hparentSelected (bestBand parent hparentSelected))) := by
        gcongr
        exact hbestBandVolume parent hparentSelected
      _ = 512 * (57 * volume
          (bandSelectedPiece parent (hphaseSubset hparent))) := by
        rw [hbandPieceEq]
      _ ≤ 512 * (57 * (2 * volume
          (phasePiece parent (hphaseSubset hparent)
            (bestPhase parent (hphaseSubset hparent))))) := by
        gcongr
        exact hbestPhaseVolume parent (hphaseSubset hparent)
      _ = 512 * (57 * (2 * volume
          (preAnchorPiece parent hparent))) := by
        rw [hphasePieceEq]
      _ = (512 * 57 * 2 : ENNReal) *
          volume (preAnchorPiece parent hparent) := by
        ring
  have hpreNonempty : ∀ parent (hparent : parent ∈ phaseSelected),
      (preAnchorPiece parent hparent).Nonempty := by
    intro parent hparent
    have hpositive : 0 < volume (preAnchorPiece parent hparent) := by
      by_contra hzero
      have hzero' : volume (preAnchorPiece parent hparent) = 0 :=
        le_zero_iff.mp (not_lt.mp hzero)
      have hle := hpreVolume parent hparent
      rw [hzero'] at hle
      simp at hle
      exact weightClass.weightFloor_pos.ne' hle
    exact nonempty_iff_ne_empty.mpr fun hempty => by
      rw [hempty] at hpositive
      simpa using hpositive
  have hpreParent : ∀ parent (hparent : parent ∈ phaseSelected),
      preAnchorPiece parent hparent ⊆
        wz1PaperGridCube root parent := by
    intro parent hparent point hpoint
    have hsource := hpoint.1.1
    let data := sources.sourceFor parent (hbandSubset (hphaseSubset hparent))
    rw [data.coarseSource_eq, data.fullSource_eq] at hsource
    simpa only [data, sources.sourceFor_cell] using hsource.1.2
  have hcoverExists : ∀ parent (hparent : parent ∈ phaseSelected),
      ∃ centers : Finset Point3,
        (centers : Set Point3) ⊆ preAnchorPiece parent hparent ∧
        centers.card ≤ 512 ∧
        preAnchorPiece parent hparent ⊆ ⋃ center ∈ centers,
          Metric.closedBall center root := by
    intro parent hparent
    let first := Classical.choose (hpreNonempty parent hparent)
    have hfirst : first ∈ preAnchorPiece parent hparent :=
      Classical.choose_spec (hpreNonempty parent hparent)
    have hball : preAnchorPiece parent hparent ⊆
        Metric.closedBall first (2 * root) := by
      intro point hpoint
      rw [Metric.mem_closedBall]
      exact le_of_lt (wz1_paper_grid_cube_diameter_lt_two_rho hroot
        (hpreParent parent hparent hpoint)
        (hpreParent parent hparent hfirst))
    exact point3_subset_self_centered_sqrt_cover hroot hball
  let centers (parent : ℤ × ℤ × ℤ)
      (hparent : parent ∈ phaseSelected) : Finset Point3 :=
    Classical.choose (hcoverExists parent hparent)
  have hcentersSubset : ∀ parent (hparent : parent ∈ phaseSelected),
      (centers parent hparent : Set Point3) ⊆
        preAnchorPiece parent hparent := fun parent hparent =>
    (Classical.choose_spec (hcoverExists parent hparent)).1
  have hcentersCard : ∀ parent (hparent : parent ∈ phaseSelected),
      (centers parent hparent).card ≤ 512 := fun parent hparent =>
    (Classical.choose_spec (hcoverExists parent hparent)).2.1
  have hcover : ∀ parent (hparent : parent ∈ phaseSelected),
      preAnchorPiece parent hparent ⊆ ⋃ center ∈ centers parent hparent,
        Metric.closedBall center root := fun parent hparent =>
    (Classical.choose_spec (hcoverExists parent hparent)).2.2
  have hcentersNonempty : ∀ parent (hparent : parent ∈ phaseSelected),
      (centers parent hparent).Nonempty := by
    intro parent hparent
    rcases hpreNonempty parent hparent with ⟨point, hpoint⟩
    rcases Set.mem_iUnion₂.mp (hcover parent hparent hpoint) with
      ⟨center, hcenter, _⟩
    exact ⟨center, hcenter⟩
  let rawPiece (parent : ℤ × ℤ × ℤ)
      (hparent : parent ∈ phaseSelected) (center : Point3) :=
    preAnchorPiece parent hparent ∩ Metric.closedBall center root
  let anchor (parent : ℤ × ℤ × ℤ)
      (hparent : parent ∈ phaseSelected) : Point3 :=
    Classical.choose (Finset.exists_max_image (centers parent hparent)
      (fun center => volume (rawPiece parent hparent center))
      (hcentersNonempty parent hparent))
  have hanchorMem : ∀ parent (hparent : parent ∈ phaseSelected),
      anchor parent hparent ∈ centers parent hparent := fun parent hparent =>
    (Classical.choose_spec (Finset.exists_max_image (centers parent hparent)
      (fun center => volume (rawPiece parent hparent center))
      (hcentersNonempty parent hparent))).1
  have hanchorMax : ∀ parent (hparent : parent ∈ phaseSelected),
      ∀ center ∈ centers parent hparent,
        volume (rawPiece parent hparent center) ≤
          volume (rawPiece parent hparent (anchor parent hparent)) :=
    fun parent hparent =>
      (Classical.choose_spec (Finset.exists_max_image (centers parent hparent)
        (fun center => volume (rawPiece parent hparent center))
        (hcentersNonempty parent hparent))).2
  let piece : ∀ parent, parent ∈ phaseSelected → Set Point3 :=
    fun parent hparent => rawPiece parent hparent (anchor parent hparent)
  have hfinalVolume : ∀ parent (hparent : parent ∈ phaseSelected),
      weightClass.weightFloor ≤ pureWZ2TerminalPopularLocalizedPieceCost *
        volume (piece parent hparent) := by
    intro parent hparent
    have hvolumeCover : volume (preAnchorPiece parent hparent) ≤
        ∑ center ∈ centers parent hparent,
          volume (rawPiece parent hparent center) := by
      have hsubset : preAnchorPiece parent hparent ⊆
          ⋃ center ∈ centers parent hparent, rawPiece parent hparent center := by
        intro point hpoint
        rcases Set.mem_iUnion₂.mp (hcover parent hparent hpoint) with
          ⟨center, hcenter, hpointBall⟩
        exact Set.mem_iUnion₂.mpr ⟨center, hcenter, hpoint, hpointBall⟩
      exact (measure_mono hsubset).trans
        (MeasureTheory.measure_biUnion_finset_le (centers parent hparent)
          (rawPiece parent hparent))
    have haverage : volume (preAnchorPiece parent hparent) ≤
        512 * volume (piece parent hparent) := by
      calc
        volume (preAnchorPiece parent hparent) ≤
            ∑ center ∈ centers parent hparent,
              volume (rawPiece parent hparent center) := hvolumeCover
        _ ≤ ∑ _center ∈ centers parent hparent,
            volume (piece parent hparent) := by
          exact Finset.sum_le_sum fun center hcenter =>
            hanchorMax parent hparent center hcenter
        _ = ((centers parent hparent).card : ENNReal) *
            volume (piece parent hparent) := by simp [Finset.sum_const]
        _ ≤ 512 * volume (piece parent hparent) := by
          gcongr
          exact_mod_cast hcentersCard parent hparent
    exact (hpreVolume parent hparent).trans (by
      calc
        (512 * 57 * 2 : ENNReal) *
            volume (preAnchorPiece parent hparent) ≤
          (512 * 57 * 2 : ENNReal) *
            (512 * volume (piece parent hparent)) := by gcongr
        _ = pureWZ2TerminalPopularLocalizedPieceCost *
            volume (piece parent hparent) := by
          simp [pureWZ2TerminalPopularLocalizedPieceCost]
          ring)
  have hfinalNonempty : ∀ parent (hparent : parent ∈ phaseSelected),
      (piece parent hparent).Nonempty := by
    intro parent hparent
    refine ⟨anchor parent hparent, ?_⟩
    exact ⟨hcentersSubset parent hparent (hanchorMem parent hparent),
      Metric.mem_closedBall_self hroot.le⟩
  exact ⟨{
    commonBand := commonBand
    commonBand_mem := by
      rcases Finset.mem_image.mp hcommonBandImage with
        ⟨parent, hparent, heq⟩
      have hlabelEq : bestBand parent hparent = commonBand := by
        simpa [bandLabel, hparent] using heq
      rw [← hlabelEq]
      exact hbestBandMem parent hparent
    center := bandCenter commonBand
    center_eq := rfl
    commonPhase := commonPhase
    left := phaseLeft commonPhase
    left_eq := rfl
    selectedParents := phaseSelected
    selected_nonempty := hphaseSelectedNonempty
    selected_subset := hphaseSubset.trans hbandSubset
    parent_card := by
      calc
        selection.selected.card ≤ 57 * bandSelected.card := hbandCard
        _ ≤ 57 * (2 * phaseSelected.card) := by gcongr
        _ = 114 * phaseSelected.card := by ring
    anchor := anchor
    piece := piece
    piece_measurable := by
      intro parent hparent
      exact (hpreMeas parent hparent).inter measurableSet_closedBall
    piece_nonempty := hfinalNonempty
    anchor_mem := by
      intro parent hparent
      exact ⟨hcentersSubset parent hparent (hanchorMem parent hparent),
        Metric.mem_closedBall_self hroot.le⟩
    piece_subset_selectedCarrier := by
      intro parent hparent point hpoint
      exact hsourceSelectedCarrier parent
        (hbandSubset (hphaseSubset hparent)) hpoint.1.1.1
    piece_subset_parent := by
      intro parent hparent point hpoint
      exact hpreParent parent hparent hpoint.1
    piece_ball := by
      intro parent hparent
      exact Set.inter_subset_right
    piece_localized := by
      intro parent hparent point hpoint
      have hbandPoint := hpoint.1.1.2
      change |inner ℝ point
          (globalGrainDirection
            (source.globalGrains.slope (point (2 : Fin 3)))) -
          bandCenter commonBand| ≤ root / 2
      rw [← hprojectionSource parent
        (hbandSubset (hphaseSubset hparent)) point hpoint.1.1.1]
      exact hbandPoint
    piece_height_window := by
      intro parent hparent point hpoint
      have hphasePoint := hpoint.1.2
      change point ∈ wz1Lemma23CellHeightWindowSet delta
        source.extremal.delta_pos (phaseLeft commonPhase) at hphasePoint
      exact hphasePoint
    piece_volume := hfinalVolume
    y_separated := by
      intro first hfirst second hsecond hne
      exact selection.y_separated first
        ((hphaseSubset.trans hbandSubset) hfirst) second
        ((hphaseSubset.trans hbandSubset) hsecond) hne
  }⟩

end Kakeya.Assouad

end
