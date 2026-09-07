import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleHeightPhaseSelection
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma18SpatialSelfCenteredCover

/-!
# Self-centered terminal pieces at exact scale

The fixed-band/height-phase piece lies in one genuine coarse source and hence
inside a radius-`sqrt delta` ball.  Cover it by at most 512 radius-`sqrt delta`
balls centered in the piece and keep a largest piece.  The chosen anchor now
belongs to the final auxiliary carrier and its entire source lies in the exact
local AD ball.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalBinAnchoredPieceData
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
    (phase : PureWZ2TerminalBinHeightPhaseSelection band) where
  anchor : ∀ parent, parent ∈ phase.selectedParents → Point3
  anchor_mem : ∀ parent (hparent : parent ∈ phase.selectedParents),
    anchor parent hparent ∈ phase.piece parent hparent
  piece : ∀ parent, parent ∈ phase.selectedParents → Set Point3
  piece_eq : ∀ parent (hparent : parent ∈ phase.selectedParents),
    piece parent hparent = phase.piece parent hparent ∩
      Metric.closedBall (anchor parent hparent) terminal.sqrtRequested.1
  piece_measurable : ∀ parent (hparent : parent ∈ phase.selectedParents),
    MeasurableSet (piece parent hparent)
  piece_nonempty : ∀ parent (hparent : parent ∈ phase.selectedParents),
    (piece parent hparent).Nonempty
  piece_subset : ∀ parent (hparent : parent ∈ phase.selectedParents),
    piece parent hparent ⊆ phase.piece parent hparent
  piece_ball : ∀ parent (hparent : parent ∈ phase.selectedParents),
    piece parent hparent ⊆
      Metric.closedBall (anchor parent hparent) terminal.sqrtRequested.1
  piece_localized : ∀ parent (hparent : parent ∈ phase.selectedParents),
    ∀ point ∈ piece parent hparent,
      |inner ℝ point
            (globalGrainDirection
              (source.globalGrains.slope (point (2 : Fin 3)))) - band.center| ≤
        terminal.sqrtRequested.1 / 2
  piece_volume : ∀ parent (hparent : parent ∈ phase.selectedParents),
    terminal.sticky.balanced.cellMass ≤
      (512 * (2 * 512 * 57) : ENNReal) * volume (piece parent hparent)

/-- Backwards-compatible anchored pieces on the largest global bin. -/
abbrev PureWZ2TerminalAnchoredPieceData
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
    (phase : PureWZ2TerminalHeightPhaseSelection band) :=
  PureWZ2TerminalBinAnchoredPieceData phase

theorem PureWZ2TerminalBinHeightPhaseSelection.anchorPiecesBin
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
    (phase : PureWZ2TerminalBinHeightPhaseSelection band) :
    Nonempty (PureWZ2TerminalBinAnchoredPieceData phase) := by
  let root := terminal.sqrtRequested.1
  have hroot : 0 < root := terminal.sticky.coarse_extremal.delta_pos
  have hsourceNonempty : ∀ parent (hparent : parent ∈ phase.selectedParents),
      (phase.piece parent hparent).Nonempty := by
    intro parent hparent
    have hpositive : 0 < volume (phase.piece parent hparent) := by
      have hmass := terminal.sticky.balanced.cellMass_pos
      have hbound := phase.piece_volume parent hparent
      by_contra hzero
      have : volume (phase.piece parent hparent) = 0 := le_zero_iff.mp (not_lt.mp hzero)
      rw [this] at hbound
      simp at hbound
      exact hmass.ne' hbound
    exact nonempty_iff_ne_empty.mpr fun hempty => by
      rw [hempty] at hpositive
      simpa using hpositive
  have hcoverExists : ∀ parent (hparent : parent ∈ phase.selectedParents),
      ∃ centers : Finset Point3,
        (centers : Set Point3) ⊆ phase.piece parent hparent ∧
        centers.card ≤ 512 ∧
        phase.piece parent hparent ⊆ ⋃ center ∈ centers,
          Metric.closedBall center root := by
    intro parent hparent
    let first := Classical.choose (hsourceNonempty parent hparent)
    have hfirst : first ∈ phase.piece parent hparent :=
      Classical.choose_spec (hsourceNonempty parent hparent)
    have hball : phase.piece parent hparent ⊆
        Metric.closedBall first (2 * root) := by
      intro point hpoint
      have hpointParent := phase.piece_subset parent hparent hpoint
      have hfirstParent := phase.piece_subset parent hparent hfirst
      have hpointCoarse := band.piece_subset parent
        (phase.selected_subset hparent) hpointParent
      have hfirstCoarse := band.piece_subset parent
        (phase.selected_subset hparent) hfirstParent
      have hparentAll := band.selected_subset (phase.selected_subset hparent)
      rw [(sources.sourceFor parent hparentAll).coarseSource_eq,
        (sources.sourceFor parent hparentAll).fullSource_eq] at hpointCoarse hfirstCoarse
      have hp : point ∈ wz1PaperGridCube root parent := by
        simpa only [sources.sourceFor_cell parent hparentAll] using
          hpointCoarse.1.2
      have hf : first ∈ wz1PaperGridCube root parent := by
        simpa only [sources.sourceFor_cell parent hparentAll] using
          hfirstCoarse.1.2
      rw [Metric.mem_closedBall]
      exact le_of_lt (wz1_paper_grid_cube_diameter_lt_two_rho hroot hp hf)
    exact point3_subset_self_centered_sqrt_cover hroot hball
  let centers (parent : ℤ × ℤ × ℤ)
      (hparent : parent ∈ phase.selectedParents) : Finset Point3 :=
    Classical.choose (hcoverExists parent hparent)
  have hcentersSubset : ∀ parent (hparent : parent ∈ phase.selectedParents),
      (centers parent hparent : Set Point3) ⊆ phase.piece parent hparent := by
    intro parent hparent
    exact (Classical.choose_spec (hcoverExists parent hparent)).1
  have hcentersCard : ∀ parent (hparent : parent ∈ phase.selectedParents),
      (centers parent hparent).card ≤ 512 := by
    intro parent hparent
    exact (Classical.choose_spec (hcoverExists parent hparent)).2.1
  have hcover : ∀ parent (hparent : parent ∈ phase.selectedParents),
      phase.piece parent hparent ⊆ ⋃ center ∈ centers parent hparent,
        Metric.closedBall center root := by
    intro parent hparent
    exact (Classical.choose_spec (hcoverExists parent hparent)).2.2
  have hcentersNonempty : ∀ parent (hparent : parent ∈ phase.selectedParents),
      (centers parent hparent).Nonempty := by
    intro parent hparent
    rcases hsourceNonempty parent hparent with ⟨point, hpoint⟩
    rcases Set.mem_iUnion₂.mp (hcover parent hparent hpoint) with
      ⟨center, hcenter, _⟩
    exact ⟨center, hcenter⟩
  let rawPiece (parent : ℤ × ℤ × ℤ)
      (hparent : parent ∈ phase.selectedParents) (center : Point3) :=
    phase.piece parent hparent ∩ Metric.closedBall center root
  let anchor (parent : ℤ × ℤ × ℤ)
      (hparent : parent ∈ phase.selectedParents) : Point3 :=
    Classical.choose (Finset.exists_max_image (centers parent hparent)
      (fun center => volume (rawPiece parent hparent center))
      (hcentersNonempty parent hparent))
  have hanchorMem : ∀ parent (hparent : parent ∈ phase.selectedParents),
      anchor parent hparent ∈ centers parent hparent := by
    intro parent hparent
    exact (Classical.choose_spec (Finset.exists_max_image
      (centers parent hparent)
      (fun center => volume (rawPiece parent hparent center))
      (hcentersNonempty parent hparent))).1
  have hanchorMax : ∀ parent (hparent : parent ∈ phase.selectedParents),
      ∀ center ∈ centers parent hparent,
        volume (rawPiece parent hparent center) ≤
          volume (rawPiece parent hparent (anchor parent hparent)) := by
    intro parent hparent
    exact (Classical.choose_spec (Finset.exists_max_image
      (centers parent hparent)
      (fun center => volume (rawPiece parent hparent center))
      (hcentersNonempty parent hparent))).2
  let piece (parent : ℤ × ℤ × ℤ)
      (hparent : parent ∈ phase.selectedParents) :=
    rawPiece parent hparent (anchor parent hparent)
  have hvolumeCover : ∀ parent (hparent : parent ∈ phase.selectedParents),
      volume (phase.piece parent hparent) ≤
        ∑ center ∈ centers parent hparent,
          volume (rawPiece parent hparent center) := by
    intro parent hparent
    have hsubset : phase.piece parent hparent ⊆
        ⋃ center ∈ centers parent hparent, rawPiece parent hparent center := by
      intro point hpoint
      rcases Set.mem_iUnion₂.mp (hcover parent hparent hpoint) with
        ⟨center, hcenter, hball⟩
      exact Set.mem_iUnion₂.mpr ⟨center, hcenter, hpoint, hball⟩
    exact (measure_mono hsubset).trans
      (MeasureTheory.measure_biUnion_finset_le (centers parent hparent)
        (rawPiece parent hparent))
  have haverage : ∀ parent (hparent : parent ∈ phase.selectedParents),
      volume (phase.piece parent hparent) ≤
        512 * volume (piece parent hparent) := by
    intro parent hparent
    calc
      volume (phase.piece parent hparent) ≤
          ∑ center ∈ centers parent hparent,
            volume (rawPiece parent hparent center) := hvolumeCover parent hparent
      _ ≤ ∑ _center ∈ centers parent hparent,
          volume (piece parent hparent) := by
            exact Finset.sum_le_sum fun center hcenter =>
              hanchorMax parent hparent center hcenter
      _ = ((centers parent hparent).card : ENNReal) *
          volume (piece parent hparent) := by simp [Finset.sum_const]
      _ ≤ 512 * volume (piece parent hparent) := by
        gcongr
        exact_mod_cast hcentersCard parent hparent
  exact ⟨{
    anchor := anchor
    anchor_mem := fun parent hparent =>
      hcentersSubset parent hparent (hanchorMem parent hparent)
    piece := piece
    piece_eq := by intro parent hparent; rfl
    piece_measurable := by
      intro parent hparent
      exact (phase.piece_measurable parent hparent).inter measurableSet_closedBall
    piece_nonempty := by
      intro parent hparent
      refine ⟨anchor parent hparent, ?_⟩
      exact ⟨hcentersSubset parent hparent (hanchorMem parent hparent),
        Metric.mem_closedBall_self hroot.le⟩
    piece_subset := by
      intro parent hparent
      exact Set.inter_subset_left
    piece_ball := by
      intro parent hparent
      exact Set.inter_subset_right
    piece_localized := by
      intro parent hparent point hpoint
      exact phase.piece_localized parent hparent point hpoint.1
    piece_volume := by
      intro parent hparent
      calc
        terminal.sticky.balanced.cellMass ≤
            (2 * 512 * 57 : ENNReal) *
              volume (phase.piece parent hparent) :=
          phase.piece_volume parent hparent
        _ ≤ (2 * 512 * 57 : ENNReal) *
            (512 * volume (piece parent hparent)) := by
          gcongr
          exact haverage parent hparent
        _ = (512 * (2 * 512 * 57) : ENNReal) *
            volume (piece parent hparent) := by ring
  }⟩

/-- Compatibility wrapper for the former largest-bin terminal chain. -/
theorem PureWZ2TerminalHeightPhaseSelection.anchorPieces
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
    (phase : PureWZ2TerminalHeightPhaseSelection band) :
    Nonempty (PureWZ2TerminalAnchoredPieceData phase) :=
  phase.anchorPiecesBin

end Kakeya.Assouad
