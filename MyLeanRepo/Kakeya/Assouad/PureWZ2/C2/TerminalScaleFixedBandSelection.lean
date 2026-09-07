import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleSourceCells
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleGraphPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLine

/-!
# One fixed projection band for terminal coarse sources

The retained terminal carrier lies in the fixed strip of radius
`14 * sqrt delta` around `line.lineLevel`.  Split that strip into the 57
closed bands of radius `sqrt delta / 2` centered at
`line.lineLevel + k * sqrt delta / 2`, `-28 ≤ k ≤ 28`.  First choose a
largest band in every genuine coarse source, then retain a largest common
band class of parents.  The final center is one fixed offset of the original
global line; it is not chosen separately at each height.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalBinFixedBandSelection
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
    (sources : PureWZ2TerminalBinSourceFamily retained) where
  commonBand : ℤ
  commonBand_mem : commonBand ∈ Finset.Icc (-28 : ℤ) 28
  center : ℝ :=
    line.lineLevel + (commonBand : ℝ) * terminal.sqrtRequested.1 / 2
  center_eq : center =
    line.lineLevel + (commonBand : ℝ) * terminal.sqrtRequested.1 / 2
  selectedParents : Finset (ℤ × ℤ × ℤ)
  selected_nonempty : selectedParents.Nonempty
  selected_subset : selectedParents ⊆ residue.selected
  parent_card : residue.selected.card ≤ 57 * selectedParents.card
  piece : ∀ parent, parent ∈ selectedParents → Set Point3
  piece_eq : ∀ parent (hparent : parent ∈ selectedParents),
    piece parent hparent =
      (sources.sourceFor parent (selected_subset hparent)).coarseSource ∩
        {point |
          |inner ℝ point
                (globalGrainDirection
                  (source.globalGrains.slope (point (2 : Fin 3)))) -
              center| ≤ terminal.sqrtRequested.1 / 2}
  piece_measurable : ∀ parent (hparent : parent ∈ selectedParents),
    MeasurableSet (piece parent hparent)
  piece_subset : ∀ parent (hparent : parent ∈ selectedParents),
    piece parent hparent ⊆
      (sources.sourceFor parent (selected_subset hparent)).coarseSource
  piece_localized : ∀ parent (hparent : parent ∈ selectedParents),
    ∀ point ∈ piece parent hparent,
      |inner ℝ point
            (globalGrainDirection
              (source.globalGrains.slope (point (2 : Fin 3)))) - center| ≤
        terminal.sqrtRequested.1 / 2
  piece_volume : ∀ parent (hparent : parent ∈ selectedParents),
    terminal.sticky.balanced.cellMass ≤
      (512 * 57 : ENNReal) * volume (piece parent hparent)

/-- Backwards-compatible fixed-band package on the largest global bin. -/
abbrev PureWZ2TerminalFixedBandSelection
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
    (sources : PureWZ2TerminalSourceFamily retained) :=
  PureWZ2TerminalBinFixedBandSelection sources

theorem PureWZ2TerminalBinSourceFamily.selectFixedBandBin
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
    (sources : PureWZ2TerminalBinSourceFamily retained) :
    Nonempty (PureWZ2TerminalBinFixedBandSelection sources) := by
  let root := terminal.sqrtRequested.1
  have hroot : 0 < root := terminal.sticky.coarse_extremal.delta_pos
  let bands : Finset ℤ := Finset.Icc (-28 : ℤ) 28
  have hbandsNonempty : bands.Nonempty := by
    exact ⟨0, by simp [bands]
      ⟩
  have hbandsCard : bands.card = 57 := by
    simp [bands, Int.card_Icc]
  let projection (point : Point3) : ℝ :=
    inner ℝ point
      (globalGrainDirection
        (window.windowed.global.extendedSlope (point (2 : Fin 3))))
  let bandCenter (band : ℤ) : ℝ :=
    line.lineLevel + (band : ℝ) * root / 2
  let bandPiece (parent : ℤ × ℤ × ℤ)
      (hparent : parent ∈ residue.selected) (band : ℤ) : Set Point3 :=
    (sources.sourceFor parent hparent).coarseSource ∩
      {point | |projection point - bandCenter band| ≤ root / 2}
  have hprojectionMeasurable : Measurable projection := by
    have hslope : Measurable fun point : Point3 =>
        window.windowed.global.extendedSlope (point (2 : Fin 3)) :=
      (continuousOn_univ.mp
        window.windowed.global.extendedSlope_lipschitz.continuousOn).measurable.comp
          (by fun_prop)
    have hdirection : Measurable fun point : Point3 =>
        globalGrainDirection
          (window.windowed.global.extendedSlope (point (2 : Fin 3))) := by
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
  have hpieceMeasurable : ∀ parent (hparent : parent ∈ residue.selected) band,
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
      constructor <;> intro h
      · exact ⟨by linarith [h.1], h.2⟩
      · exact ⟨by linarith [h.1], h.2⟩
    rw [hset]
    exact (hprojectionMeasurable.sub measurable_const) measurableSet_Icc
  have hprojectionSource : ∀ parent (hparent : parent ∈ residue.selected),
      ∀ point ∈ (sources.sourceFor parent hparent).coarseSource,
        projection point = inner ℝ point
          (globalGrainDirection
            (source.globalGrains.slope (point (2 : Fin 3)))) := by
    intro parent hparent point hpoint
    have hretained := sources.coarse_source_subset parent hparent hpoint
    have hbox := shading_union_subset_axisBox
      (retained.subshading.union_subset hretained.1)
    have hheight : point (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2
    dsimp only [projection]
    rw [window.windowed.global.extendedSlope_eq _ hheight,
      window.sourceSlope_eq]
  have hcover : ∀ parent (hparent : parent ∈ residue.selected),
      (sources.sourceFor parent hparent).coarseSource ⊆
        ⋃ band ∈ bands, bandPiece parent hparent band := by
    intro parent hparent point hpoint
    have hretained := sources.coarse_source_subset parent hparent hpoint
    have hfixed := retained.fixed_line_localization point hretained.1
    have hprojectionEq := hprojectionSource parent hparent point hpoint
    let quotient := 2 * (projection point - line.lineLevel) / root
    let band : ℤ := Int.floor quotient
    have hquotientBounds : (-28 : ℝ) ≤ quotient ∧ quotient ≤ 28 := by
      dsimp only [quotient]
      have hrootNonzero : root ≠ 0 := hroot.ne'
      rw [div_le_iff₀ hroot, le_div_iff₀ hroot]
      rw [hprojectionEq]
      have hbounds := abs_le.mp hfixed
      constructor <;> nlinarith
    have hbandLower : (-28 : ℤ) ≤ band := by
      apply Int.le_floor.mpr
      simpa only [Int.cast_neg, Int.cast_ofNat] using hquotientBounds.1
    have hbandUpper : band ≤ (28 : ℤ) := by
      have hfloor := Int.floor_le quotient
      have hcast : (band : ℝ) ≤ 28 := hfloor.trans hquotientBounds.2
      exact_mod_cast hcast
    have hbandMem : band ∈ bands :=
      Finset.mem_Icc.mpr ⟨hbandLower, hbandUpper⟩
    have hqLower : (band : ℝ) ≤ quotient := Int.floor_le quotient
    have hqUpper : quotient ≤ (band : ℝ) + 1 :=
      (Int.lt_floor_add_one quotient).le
    have hrelation : quotient * root =
        2 * (projection point - line.lineLevel) := by
      dsimp only [quotient]
      field_simp [hroot.ne']
    have hbandDistance :
        |projection point - bandCenter band| ≤ root / 2 := by
      rw [abs_le]
      dsimp only [bandCenter]
      constructor <;> nlinarith
    exact Set.mem_iUnion₂.mpr
      ⟨band, hbandMem, hpoint, hbandDistance⟩
  have hsourceVolume : ∀ parent (hparent : parent ∈ residue.selected),
      volume (sources.sourceFor parent hparent).coarseSource ≤
        ∑ band ∈ bands, volume (bandPiece parent hparent band) := by
    intro parent hparent
    exact (measure_mono (hcover parent hparent)).trans
      (MeasureTheory.measure_biUnion_finset_le bands
        (bandPiece parent hparent))
  have hbestExists : ∀ parent (hparent : parent ∈ residue.selected),
      ∃ band ∈ bands,
        volume (sources.sourceFor parent hparent).coarseSource ≤
          57 * volume (bandPiece parent hparent band) := by
    intro parent hparent
    rcases Finset.exists_max_image bands
        (fun band => volume (bandPiece parent hparent band))
        hbandsNonempty with ⟨band, hband, hmax⟩
    refine ⟨band, hband, (hsourceVolume parent hparent).trans ?_⟩
    calc
      ∑ other ∈ bands, volume (bandPiece parent hparent other) ≤
          ∑ _other ∈ bands, volume (bandPiece parent hparent band) := by
            exact Finset.sum_le_sum fun other hother => hmax other hother
      _ = 57 * volume (bandPiece parent hparent band) := by
            rw [Finset.sum_const, hbandsCard]
            norm_num
  let bestBand (parent : ℤ × ℤ × ℤ)
      (hparent : parent ∈ residue.selected) : ℤ :=
    Classical.choose (hbestExists parent hparent)
  have hbestMem : ∀ parent (hparent : parent ∈ residue.selected),
      bestBand parent hparent ∈ bands := by
    intro parent hparent
    exact (Classical.choose_spec (hbestExists parent hparent)).1
  have hbestVolume : ∀ parent (hparent : parent ∈ residue.selected),
      volume (sources.sourceFor parent hparent).coarseSource ≤
        57 * volume (bandPiece parent hparent (bestBand parent hparent)) := by
    intro parent hparent
    exact (Classical.choose_spec (hbestExists parent hparent)).2
  let label (parent : ℤ × ℤ × ℤ) : ℤ :=
    if hparent : parent ∈ residue.selected then bestBand parent hparent else 0
  rcases finset_exists_max_fiber_with_product_bound
      residue.selected label residue.selected_nonempty with
    ⟨commonBand, hcommonImage, hparentCardRaw, hselectedNonempty⟩
  let selectedParents := residue.selected.filter fun parent =>
    label parent = commonBand
  have hcommonMem : commonBand ∈ bands := by
    rcases Finset.mem_image.mp hcommonImage with ⟨parent, hparent, hlabel⟩
    rw [← hlabel]
    simp only [label, dif_pos hparent]
    exact hbestMem parent hparent
  have himageSubset : residue.selected.image label ⊆ bands := by
    intro band hband
    rcases Finset.mem_image.mp hband with ⟨parent, hparent, rfl⟩
    simp only [label, dif_pos hparent]
    exact hbestMem parent hparent
  have himageCard : (residue.selected.image label).card ≤ 57 := by
    rw [← hbandsCard]
    exact Finset.card_le_card himageSubset
  have hparentCard : residue.selected.card ≤
      57 * selectedParents.card := by
    exact hparentCardRaw.trans (Nat.mul_le_mul_right
      selectedParents.card himageCard)
  have hselectedSubset : selectedParents ⊆ residue.selected :=
    Finset.filter_subset _ _
  have hselectedBand : ∀ parent (hparent : parent ∈ selectedParents),
      bestBand parent (hselectedSubset hparent) = commonBand := by
    intro parent hparent
    have hfilter := (Finset.mem_filter.mp hparent).2
    simpa only [label, dif_pos (hselectedSubset hparent)] using hfilter
  let piece : ∀ parent, parent ∈ selectedParents → Set Point3 :=
    fun parent hparent => bandPiece parent (hselectedSubset hparent) commonBand
  have hpieceVolume : ∀ parent (hparent : parent ∈ selectedParents),
      terminal.sticky.balanced.cellMass ≤
        (512 * 57 : ENNReal) * volume (piece parent hparent) := by
    intro parent hparent
    let hparentAll := hselectedSubset hparent
    let data := sources.sourceFor parent hparentAll
    have hcoarse : terminal.sticky.balanced.cellMass ≤
        512 * volume data.coarseSource := by
      calc
        terminal.sticky.balanced.cellMass = volume data.fullSource :=
          data.fullSource_volume.symm
        _ ≤ (data.centers.card : ENNReal) * volume data.coarseSource :=
          data.volume_average
        _ ≤ 512 * volume data.coarseSource := by
          gcongr
          exact_mod_cast data.centers_card
    calc
      terminal.sticky.balanced.cellMass ≤
          512 * volume data.coarseSource := hcoarse
      _ ≤ 512 * (57 * volume
          (bandPiece parent hparentAll (bestBand parent hparentAll))) := by
            gcongr
            exact hbestVolume parent hparentAll
      _ = (512 * 57 : ENNReal) * volume (piece parent hparent) := by
            rw [hselectedBand parent hparent]
            dsimp only [piece]
            ring
  exact ⟨{
    commonBand := commonBand
    commonBand_mem := hcommonMem
    center := bandCenter commonBand
    center_eq := rfl
    selectedParents := selectedParents
    selected_nonempty := hselectedNonempty
    selected_subset := hselectedSubset
    parent_card := hparentCard
    piece := piece
    piece_eq := by
      intro parent hparent
      ext point
      constructor
      · intro hpoint
        refine ⟨hpoint.1, ?_⟩
        change |inner ℝ point
            (globalGrainDirection
              (source.globalGrains.slope (point (2 : Fin 3)))) -
            bandCenter commonBand| ≤ root / 2
        rw [← hprojectionSource parent (hselectedSubset hparent) point hpoint.1]
        exact hpoint.2
      · intro hpoint
        refine ⟨hpoint.1, ?_⟩
        change |projection point - bandCenter commonBand| ≤ root / 2
        rw [hprojectionSource parent (hselectedSubset hparent) point hpoint.1]
        exact hpoint.2
    piece_measurable := by
      intro parent hparent
      exact hpieceMeasurable parent (hselectedSubset hparent) commonBand
    piece_subset := by
      intro parent hparent
      exact Set.inter_subset_left
    piece_localized := by
      intro parent hparent point hpoint
      change |inner ℝ point
          (globalGrainDirection
            (source.globalGrains.slope (point (2 : Fin 3)))) -
          bandCenter commonBand| ≤ root / 2
      rw [← hprojectionSource parent (hselectedSubset hparent) point hpoint.1]
      exact hpoint.2
    piece_volume := hpieceVolume
  }⟩

/-- Compatibility wrapper for the former largest-bin terminal chain. -/
theorem PureWZ2TerminalSourceFamily.selectFixedBand
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
    (sources : PureWZ2TerminalSourceFamily retained) :
    Nonempty (PureWZ2TerminalFixedBandSelection sources) :=
  sources.selectFixedBandBin

end Kakeya.Assouad
