import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactGraphPreparation

/-!
# Actual parents of exact-scale terminal graph cells

Every active Lemma-23 cell has a genuine canonical representative in one of
the anchored parent pieces.  That parent is unique on each snapped y-layer
because distinct retained parents are separated by 512 side-`sqrt delta`
y-layers, while two representatives in one exact `delta` y-cell differ by at
most `delta`.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalExactGraphParentData
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
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    (prep : PureWZ2TerminalBinExactGraphPreparation anchored) where
  representative : (ℤ × ℤ × ℤ) → Point3
  representative_eq : ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
    representative cell =
      wz1Lemma23CellRepresentative prep.shadow source.extremal.delta_pos
        ⟨cell, prep.windowed.global.cells_active hcell⟩
  representative_mem : ∀ cell ∈ prep.windowed.global.cells,
    representative cell ∈ prep.shadow.union
  representative_index : ∀ cell ∈ prep.windowed.global.cells,
    wz1Lemma23CellIndex delta (representative cell) = cell
  parentOf : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
  parent_mem : ∀ cell ∈ prep.windowed.global.cells,
    parentOf cell ∈ phase.selectedParents
  representative_mem_piece : ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
    ∃ hparent : parentOf cell ∈ phase.selectedParents,
      representative cell ∈ anchored.piece (parentOf cell) hparent
  representative_mem_parent : ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
    representative cell ∈
      wz1PaperGridCube terminal.sqrtRequested.1 (parentOf cell)
  different_parent_y_far :
    ∀ first ∈ prep.windowed.global.cells,
      ∀ second ∈ prep.windowed.global.cells,
        parentOf first ≠ parentOf second →
          511 * terminal.sqrtRequested.1 <
            |representative first (1 : Fin 3) - representative second 1|
  same_y_parent :
    ∀ first ∈ prep.windowed.global.cells,
      ∀ second ∈ prep.windowed.global.cells,
        first.2.1 = second.2.1 → parentOf first = parentOf second

theorem PureWZ2TerminalBinExactGraphPreparation.graphParents
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
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    (prep : PureWZ2TerminalBinExactGraphPreparation anchored) :
    Nonempty (PureWZ2TerminalExactGraphParentData prep) := by
  let root := terminal.sqrtRequested.1
  have hroot : 0 < root := terminal.sticky.coarse_extremal.delta_pos
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hdeltaOne : delta ≤ 1 := source.extremal.delta_le_one
  have hdeltaRoot : delta ≤ root := by
    rw [show root = Real.sqrt delta by exact terminal.sqrtRequested_eq]
    nlinarith [Real.sqrt_nonneg delta, Real.sq_sqrt hdelta.le]
  let representative (cell : ℤ × ℤ × ℤ) : Point3 :=
    if hcell : cell ∈ prep.windowed.global.cells then
      wz1Lemma23CellRepresentative prep.shadow hdelta
        ⟨cell, prep.windowed.global.cells_active hcell⟩ else 0
  have hrepresentativeMem : ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
      representative cell ∈ prep.shadow.union := by
    intro cell hcell
    simp only [representative, dif_pos hcell]
    exact wz1Lemma23CellRepresentative_mem_union prep.shadow hdelta _
  have hrepresentativeIndex : ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
      wz1Lemma23CellIndex delta (representative cell) = cell := by
    intro cell hcell
    simp only [representative, dif_pos hcell]
    exact wz1Lemma23CellRepresentative_index prep.shadow hdelta _
  have hparentExists : ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
      ∃ parent, ∃ hparent : parent ∈ phase.selectedParents,
        representative cell ∈ anchored.piece parent hparent := by
    intro cell hcell
    have hshadow := hrepresentativeMem cell hcell
    rw [prep.shadow_union, prep.region_eq] at hshadow
    rcases Set.mem_iUnion.mp hshadow with ⟨parent, hpiece⟩
    exact ⟨parent.1, parent.2, hpiece⟩
  let defaultParent := Classical.choose phase.selected_nonempty
  let parentOf (cell : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
    if hcell : cell ∈ prep.windowed.global.cells then
      Classical.choose (hparentExists cell hcell) else defaultParent
  have hparentMem : ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
      parentOf cell ∈ phase.selectedParents := by
    intro cell hcell
    simp only [parentOf, dif_pos hcell]
    exact Classical.choose (Classical.choose_spec (hparentExists cell hcell))
  have hrepPiece : ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
      ∃ hparent : parentOf cell ∈ phase.selectedParents,
        representative cell ∈ anchored.piece (parentOf cell) hparent := by
    intro cell hcell
    let chosen := Classical.choose (hparentExists cell hcell)
    have hchosen : chosen ∈ phase.selectedParents :=
      Classical.choose (Classical.choose_spec (hparentExists cell hcell))
    have hpiece : representative cell ∈ anchored.piece chosen hchosen :=
      Classical.choose_spec (Classical.choose_spec (hparentExists cell hcell))
    have hparentEq : parentOf cell = chosen := by
      simp [parentOf, hcell, chosen]
    rw [hparentEq]
    exact ⟨hchosen, hpiece⟩
  have hrepParent : ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
      representative cell ∈ wz1PaperGridCube root (parentOf cell) := by
    intro cell hcell
    rcases hrepPiece cell hcell with ⟨hparent, hpiece⟩
    have hphase := anchored.piece_subset (parentOf cell) hparent hpiece
    have hband := phase.piece_subset (parentOf cell)
      (hparentMem cell hcell) hphase
    have hcoarse := band.piece_subset (parentOf cell)
      (phase.selected_subset (hparentMem cell hcell)) hband
    have hparentAll := band.selected_subset
      (phase.selected_subset (hparentMem cell hcell))
    rw [(sources.sourceFor (parentOf cell) hparentAll).coarseSource_eq,
      (sources.sourceFor (parentOf cell) hparentAll).fullSource_eq] at hcoarse
    simpa only [sources.sourceFor_cell (parentOf cell) hparentAll] using
      hcoarse.1.2
  have hfarParents :
      ∀ first (hfirst : first ∈ prep.windowed.global.cells),
        ∀ second (hsecond : second ∈ prep.windowed.global.cells),
          parentOf first ≠ parentOf second →
            511 * root <
              |representative first 1 - representative second 1| := by
    intro first hfirst second hsecond hne
    have hfirstResidue : parentOf first ∈ residue.selected :=
      band.selected_subset (phase.selected_subset (hparentMem first hfirst))
    have hsecondResidue : parentOf second ∈ residue.selected :=
      band.selected_subset (phase.selected_subset (hparentMem second hsecond))
    have hparentYNe : (parentOf first).2.1 ≠ (parentOf second).2.1 := by
      intro heq
      exact hne (selection.selected_y_injective
        (residue.selected_subset hfirstResidue)
        (residue.selected_subset hsecondResidue) heq)
    have hyParent := (residue.y_separated
      (parentOf first) hfirstResidue
      (parentOf second) hsecondResidue).resolve_left hparentYNe
    have hfirstBox := hrepParent first hfirst
    have hsecondBox := hrepParent second hsecond
    rw [wz1PaperGridCube_eq_Ico hroot (parentOf first)] at hfirstBox
    rw [wz1PaperGridCube_eq_Ico hroot (parentOf second)] at hsecondBox
    by_cases horder : (parentOf first).2.1 < (parentOf second).2.1
    · have hindexGap : (512 : ℤ) ≤
          (parentOf second).2.1 - (parentOf first).2.1 := by
        have habs : |(parentOf first).2.1 - (parentOf second).2.1| =
            (parentOf second).2.1 - (parentOf first).2.1 := by
          rw [abs_of_neg (sub_neg.mpr horder)]
          ring
        rwa [habs] at hyParent
      have hcastGap : (512 : ℝ) ≤
          ((parentOf second).2.1 : ℝ) - ((parentOf first).2.1 : ℝ) := by
        exact_mod_cast hindexGap
      have hmulGap := mul_le_mul_of_nonneg_right hcastGap hroot.le
      have hfar : 511 * root < representative second 1 - representative first 1 := by
        linarith [hfirstBox.2.2.2.1, hsecondBox.2.2.1]
      rw [abs_sub_comm, abs_of_pos (by linarith [hfar])]
      exact hfar
    · have horder' : (parentOf second).2.1 < (parentOf first).2.1 := by omega
      have hindexGap : (512 : ℤ) ≤
          (parentOf first).2.1 - (parentOf second).2.1 := by
        have habs : |(parentOf first).2.1 - (parentOf second).2.1| =
            (parentOf first).2.1 - (parentOf second).2.1 := by
          rw [abs_of_pos (sub_pos.mpr horder')]
        rwa [habs] at hyParent
      have hcastGap : (512 : ℝ) ≤
          ((parentOf first).2.1 : ℝ) - ((parentOf second).2.1 : ℝ) := by
        exact_mod_cast hindexGap
      have hmulGap := mul_le_mul_of_nonneg_right hcastGap hroot.le
      have hfar : 511 * root < representative first 1 - representative second 1 := by
        linarith [hsecondBox.2.2.2.1, hfirstBox.2.2.1]
      rw [abs_of_pos (by linarith [hfar])]
      exact hfar
  have hsameY :
      ∀ first (hfirst : first ∈ prep.windowed.global.cells),
        ∀ second (hsecond : second ∈ prep.windowed.global.cells),
          first.2.1 = second.2.1 → parentOf first = parentOf second := by
    intro first hfirst second hsecond hy
    have hfirstCenter :=
      ((wz1_lemma23_snapped_cell_geometry delta hdelta hdeltaOne).2.1
        first (representative first) (hrepresentativeIndex first hfirst)).1 1
    have hsecondCenter :=
      ((wz1_lemma23_snapped_cell_geometry delta hdelta hdeltaOne).2.1
        second (representative second) (hrepresentativeIndex second hsecond)).1 1
    have hcentersEqual :=
      (wz1_lemma23_snapped_cell_geometry delta hdelta hdeltaOne).2.2.1
        first second hy
    have hpointClose :
        |representative first 1 - representative second 1| ≤ delta := by
      have htriangle : |representative first 1 - representative second 1| ≤
          |representative first 1 - (wz1Lemma23CellCenter delta first) 1| +
          |representative second 1 - (wz1Lemma23CellCenter delta second) 1| := by
        calc
          _ = |(representative first 1 -
                (wz1Lemma23CellCenter delta first) 1) +
              ((wz1Lemma23CellCenter delta second) 1 -
                representative second 1)| := by rw [hcentersEqual]; ring
          _ ≤ _ := by
            simpa [abs_sub_comm] using abs_add_le
              (representative first 1 - (wz1Lemma23CellCenter delta first) 1)
              ((wz1Lemma23CellCenter delta second) 1 - representative second 1)
      linarith [hfirstCenter, hsecondCenter]
    by_contra hne
    have hfar := hfarParents first hfirst second hsecond hne
    linarith
  exact ⟨{
    representative := representative
    representative_eq := by
      intro cell hcell
      simp [representative, hcell]
    representative_mem := hrepresentativeMem
    representative_index := hrepresentativeIndex
    parentOf := parentOf
    parent_mem := hparentMem
    representative_mem_piece := hrepPiece
    representative_mem_parent := hrepParent
    different_parent_y_far := hfarParents
    same_y_parent := hsameY
  }⟩

/-- The genuine anchored-piece center attached to one exact graph cell. -/
def PureWZ2TerminalExactGraphParentData.anchorFor
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
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    (data : PureWZ2TerminalExactGraphParentData prep)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ prep.windowed.global.cells) : Point3 :=
  anchored.anchor (data.parentOf cell) (data.parent_mem cell hcell)

lemma PureWZ2TerminalExactGraphParentData.anchorFor_mem_shadow
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
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    (data : PureWZ2TerminalExactGraphParentData prep)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ prep.windowed.global.cells) :
    data.anchorFor cell hcell ∈ prep.shadow.union := by
  rw [prep.shadow_union, prep.region_eq]
  exact Set.mem_iUnion.mpr
    ⟨⟨data.parentOf cell, data.parent_mem cell hcell⟩,
      by
        rw [anchored.piece_eq]
        exact ⟨anchored.anchor_mem _ _,
          Metric.mem_closedBall_self terminal.sticky.coarse_extremal.delta_pos.le⟩⟩

lemma PureWZ2TerminalExactGraphParentData.canonical_rep_dist_anchor
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
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    (data : PureWZ2TerminalExactGraphParentData prep)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ prep.windowed.global.cells) :
    dist
        (wz1Lemma23CellRepresentative prep.shadow source.extremal.delta_pos
          ⟨cell, prep.windowed.global.cells_active hcell⟩)
        (data.anchorFor cell hcell) ≤ Real.sqrt delta := by
  have hrepEq : wz1Lemma23CellRepresentative prep.shadow
      source.extremal.delta_pos
      ⟨cell, prep.windowed.global.cells_active hcell⟩ = data.representative cell := by
    exact (data.representative_eq cell hcell).symm
  rw [hrepEq]
  rcases data.representative_mem_piece cell hcell with ⟨hparent, hpiece⟩
  have hball := anchored.piece_ball (data.parentOf cell) hparent hpiece
  rw [Metric.mem_closedBall] at hball
  simpa [PureWZ2TerminalExactGraphParentData.anchorFor,
    terminal.sqrtRequested_eq] using hball

end Kakeya.Assouad
