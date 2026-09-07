import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleFixedBandSelection
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23WindowedGlobalPackage

/-!
# A common exact-scale height-window phase

Inside the common side-`sqrt delta` parent-height slab, actual Lemma-23 cell
centers range over an interval of length at most `sqrt delta + delta`.  Two
windows of length `sqrt delta`, with left endpoints differing by `delta`,
cover that range.  Choose a heavier phase in each localized coarse source and
then one common phase on a largest parent class.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalBinHeightPhaseSelection
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
    (band : PureWZ2TerminalBinFixedBandSelection sources) where
  commonPhase : Bool
  left : ℝ :=
    (retained.commonParentHeight : ℝ) * terminal.sqrtRequested.1 -
      delta / 2 + if commonPhase then delta else 0
  left_eq : left =
    (retained.commonParentHeight : ℝ) * terminal.sqrtRequested.1 -
      delta / 2 + if commonPhase then delta else 0
  selectedParents : Finset (ℤ × ℤ × ℤ)
  selected_nonempty : selectedParents.Nonempty
  selected_subset : selectedParents ⊆ band.selectedParents
  parent_card : band.selectedParents.card ≤ 2 * selectedParents.card
  piece : ∀ parent, parent ∈ selectedParents → Set Point3
  piece_eq : ∀ parent (hparent : parent ∈ selectedParents),
    piece parent hparent =
      band.piece parent (selected_subset hparent) ∩
        wz1Lemma23CellHeightWindowSet delta source.extremal.delta_pos left
  piece_measurable : ∀ parent (hparent : parent ∈ selectedParents),
    MeasurableSet (piece parent hparent)
  piece_subset : ∀ parent (hparent : parent ∈ selectedParents),
    piece parent hparent ⊆ band.piece parent (selected_subset hparent)
  piece_localized : ∀ parent (hparent : parent ∈ selectedParents),
    ∀ point ∈ piece parent hparent,
      |inner ℝ point
            (globalGrainDirection
              (source.globalGrains.slope (point (2 : Fin 3)))) - band.center| ≤
        terminal.sqrtRequested.1 / 2
  piece_volume : ∀ parent (hparent : parent ∈ selectedParents),
    terminal.sticky.balanced.cellMass ≤
      (2 * 512 * 57 : ENNReal) * volume (piece parent hparent)

/-- Backwards-compatible height-phase package on the largest global bin. -/
abbrev PureWZ2TerminalHeightPhaseSelection
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
    (band : PureWZ2TerminalFixedBandSelection sources) :=
  PureWZ2TerminalBinHeightPhaseSelection band

theorem PureWZ2TerminalBinFixedBandSelection.selectHeightPhaseBin
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
    (band : PureWZ2TerminalBinFixedBandSelection sources) :
    Nonempty (PureWZ2TerminalBinHeightPhaseSelection band) := by
  let root := terminal.sqrtRequested.1
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hdeltaOne : delta ≤ 1 := source.extremal.delta_le_one
  have hroot : 0 < root := terminal.sticky.coarse_extremal.delta_pos
  have hdeltaRoot : delta ≤ root := by
    rw [show root = Real.sqrt delta by exact terminal.sqrtRequested_eq]
    nlinarith [Real.sqrt_nonneg delta, Real.sq_sqrt hdelta.le]
  let baseLeft :=
    (retained.commonParentHeight : ℝ) * root - delta / 2
  let phaseLeft (phase : Bool) := baseLeft + if phase then delta else 0
  let phaseSet (phase : Bool) :=
    wz1Lemma23CellHeightWindowSet delta hdelta (phaseLeft phase)
  let phasePiece (parent : ℤ × ℤ × ℤ)
      (hparent : parent ∈ band.selectedParents) (phase : Bool) :=
    band.piece parent hparent ∩ phaseSet phase
  have hphaseMeasurable : ∀ parent (hparent : parent ∈ band.selectedParents) phase,
      MeasurableSet (phasePiece parent hparent phase) := by
    intro parent hparent phase
    exact (band.piece_measurable parent hparent).inter
      (wz1Lemma23CellHeightWindowSet_measurable delta hdelta (phaseLeft phase))
  have hcover : ∀ parent (hparent : parent ∈ band.selectedParents),
      band.piece parent hparent ⊆
        phasePiece parent hparent false ∪ phasePiece parent hparent true := by
    intro parent hparent point hpoint
    have hsourceOriginal := band.piece_subset parent hparent hpoint
    have hsource := hsourceOriginal
    have hparentAll := band.selected_subset hparent
    rw [(sources.sourceFor parent hparentAll).coarseSource_eq,
      (sources.sourceFor parent hparentAll).fullSource_eq] at hsource
    have hpointParent : point ∈ wz1PaperGridCube root parent := by
      simpa only [sources.sourceFor_cell parent hparentAll] using hsource.1.2
    have hparentHeight := retained.parent_height_eq parent hparentAll
    rw [wz1PaperGridCube_eq_Ico hroot parent, hparentHeight] at hpointParent
    have hpointNorm : ‖point‖ ≤ 2 :=
      norm_le_two_of_mem_paperShading
        (retained.subshading.union_subset
          (sources.coarse_source_subset parent hparentAll hsourceOriginal).1)
    let cell := wz1Lemma23CellIndex delta point
    have hbounded : cell ∈ wz1Lemma23BoundedCells delta hdelta :=
      wz1Lemma23_index_mem_bounded_two hdelta hpointNorm
    have hpointCell : point ∈ wz1Lemma23Cell delta cell := rfl
    have hcenterClose :=
      ((wz1_lemma23_snapped_cell_geometry delta hdelta hdeltaOne).2.1
        cell point rfl).1 (2 : Fin 3)
    let center := (wz1Lemma23SnappedPoint delta cell) (2 : Fin 3)
    have hcenterLower : baseLeft ≤ center := by
      dsimp only [baseLeft, center]
      rw [show (wz1Lemma23SnappedPoint delta cell) (2 : Fin 3) =
        (wz1Lemma23CellCenter delta cell) (2 : Fin 3) by rfl]
      have hcoord := (abs_le.mp hcenterClose).2
      linarith [hpointParent.2.2.2.2.1]
    have hcenterUpper : center ≤ baseLeft + root + delta := by
      dsimp only [baseLeft, center]
      rw [show (wz1Lemma23SnappedPoint delta cell) (2 : Fin 3) =
        (wz1Lemma23CellCenter delta cell) (2 : Fin 3) by rfl]
      have hcoord := (abs_le.mp hcenterClose).1
      linarith [hpointParent.2.2.2.2.2]
    have hwindowMem : point ∈ phaseSet false ∨ point ∈ phaseSet true := by
      by_cases hfirst : center ≤ baseLeft + root
      · left
        refine Set.mem_iUnion₂.mpr ⟨cell, Finset.mem_filter.mpr
          ⟨hbounded, ?_⟩, hpointCell⟩
        change center ∈ Set.Icc (phaseLeft false)
          (phaseLeft false + Real.sqrt delta)
        rw [show phaseLeft false = baseLeft by simp [phaseLeft],
          show Real.sqrt delta = root by exact terminal.sqrtRequested_eq.symm]
        exact ⟨hcenterLower, hfirst⟩
      · right
        refine Set.mem_iUnion₂.mpr ⟨cell, Finset.mem_filter.mpr
          ⟨hbounded, ?_⟩, hpointCell⟩
        have hsecondLower : baseLeft + delta ≤ center := by
          have : baseLeft + delta ≤ baseLeft + root := by linarith
          linarith
        change center ∈ Set.Icc (phaseLeft true)
          (phaseLeft true + Real.sqrt delta)
        rw [show phaseLeft true = baseLeft + delta by simp [phaseLeft],
          show Real.sqrt delta = root by exact terminal.sqrtRequested_eq.symm]
        exact ⟨hsecondLower, by linarith [hcenterUpper]⟩
    rcases hwindowMem with hfirst | hsecond
    · exact Or.inl ⟨hpoint, hfirst⟩
    · exact Or.inr ⟨hpoint, hsecond⟩
  have hpieceVolumeCover : ∀ parent (hparent : parent ∈ band.selectedParents),
      volume (band.piece parent hparent) ≤
        volume (phasePiece parent hparent false) +
          volume (phasePiece parent hparent true) := by
    intro parent hparent
    exact (measure_mono (hcover parent hparent)).trans
      (MeasureTheory.measure_union_le _ _)
  have hbestExists : ∀ parent (hparent : parent ∈ band.selectedParents),
      ∃ phase : Bool, volume (band.piece parent hparent) ≤
        2 * volume (phasePiece parent hparent phase) := by
    intro parent hparent
    by_cases horder : volume (phasePiece parent hparent false) ≤
        volume (phasePiece parent hparent true)
    · refine ⟨true, (hpieceVolumeCover parent hparent).trans ?_⟩
      calc
        volume (phasePiece parent hparent false) +
            volume (phasePiece parent hparent true) ≤
          volume (phasePiece parent hparent true) +
            volume (phasePiece parent hparent true) := by gcongr
        _ = 2 * volume (phasePiece parent hparent true) := by ring
    · refine ⟨false, (hpieceVolumeCover parent hparent).trans ?_⟩
      have hle : volume (phasePiece parent hparent true) ≤
          volume (phasePiece parent hparent false) := le_of_not_ge horder
      calc
        volume (phasePiece parent hparent false) +
            volume (phasePiece parent hparent true) ≤
          volume (phasePiece parent hparent false) +
            volume (phasePiece parent hparent false) := by gcongr
        _ = 2 * volume (phasePiece parent hparent false) := by ring
  let bestPhase (parent : ℤ × ℤ × ℤ)
      (hparent : parent ∈ band.selectedParents) : Bool :=
    Classical.choose (hbestExists parent hparent)
  have hbestVolume : ∀ parent (hparent : parent ∈ band.selectedParents),
      volume (band.piece parent hparent) ≤
        2 * volume (phasePiece parent hparent (bestPhase parent hparent)) := by
    intro parent hparent
    exact Classical.choose_spec (hbestExists parent hparent)
  let label (parent : ℤ × ℤ × ℤ) : Bool :=
    if hparent : parent ∈ band.selectedParents then bestPhase parent hparent else false
  rcases finset_exists_max_fiber_with_product_bound
      band.selectedParents label band.selected_nonempty with
    ⟨commonPhase, _hcommonImage, hparentCardRaw, hselectedNonempty⟩
  let selectedParents := band.selectedParents.filter fun parent =>
    label parent = commonPhase
  have himageCard : (band.selectedParents.image label).card ≤ 2 := by
    exact (Finset.card_le_univ _).trans_eq (by decide)
  have hparentCard : band.selectedParents.card ≤
      2 * selectedParents.card :=
    hparentCardRaw.trans (Nat.mul_le_mul_right selectedParents.card himageCard)
  have hselectedSubset : selectedParents ⊆ band.selectedParents :=
    Finset.filter_subset _ _
  have hselectedPhase : ∀ parent (hparent : parent ∈ selectedParents),
      bestPhase parent (hselectedSubset hparent) = commonPhase := by
    intro parent hparent
    have hfilter := (Finset.mem_filter.mp hparent).2
    simpa only [label, dif_pos (hselectedSubset hparent)] using hfilter
  let left := phaseLeft commonPhase
  let piece : ∀ parent, parent ∈ selectedParents → Set Point3 :=
    fun parent hparent => phasePiece parent (hselectedSubset hparent) commonPhase
  have hpieceVolume : ∀ parent (hparent : parent ∈ selectedParents),
      terminal.sticky.balanced.cellMass ≤
        (2 * 512 * 57 : ENNReal) * volume (piece parent hparent) := by
    intro parent hparent
    let hparentBand := hselectedSubset hparent
    calc
      terminal.sticky.balanced.cellMass ≤
          (512 * 57 : ENNReal) * volume (band.piece parent hparentBand) :=
        band.piece_volume parent hparentBand
      _ ≤ (512 * 57 : ENNReal) *
          (2 * volume (phasePiece parent hparentBand
            (bestPhase parent hparentBand))) := by
        gcongr
        exact hbestVolume parent hparentBand
      _ = (2 * 512 * 57 : ENNReal) * volume (piece parent hparent) := by
        rw [hselectedPhase parent hparent]
        dsimp only [piece]
        ring
  exact ⟨{
    commonPhase := commonPhase
    left := left
    left_eq := rfl
    selectedParents := selectedParents
    selected_nonempty := hselectedNonempty
    selected_subset := hselectedSubset
    parent_card := hparentCard
    piece := piece
    piece_eq := by intro parent hparent; rfl
    piece_measurable := by
      intro parent hparent
      exact hphaseMeasurable parent (hselectedSubset hparent) commonPhase
    piece_subset := by
      intro parent hparent
      exact Set.inter_subset_left
    piece_localized := by
      intro parent hparent point hpoint
      exact band.piece_localized parent (hselectedSubset hparent) point hpoint.1
    piece_volume := hpieceVolume
  }⟩

/-- Compatibility wrapper for the former largest-bin terminal chain. -/
theorem PureWZ2TerminalFixedBandSelection.selectHeightPhase
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
    (band : PureWZ2TerminalFixedBandSelection sources) :
    Nonempty (PureWZ2TerminalHeightPhaseSelection band) :=
  band.selectHeightPhaseBin

end Kakeya.Assouad
