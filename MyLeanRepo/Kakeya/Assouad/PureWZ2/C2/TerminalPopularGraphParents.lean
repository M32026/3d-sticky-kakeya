import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularGraphPreparation

/-!
# Official parents of localized outer-popular graph cells

Every active exact-scale graph cell is assigned to an official selected
`sqrt delta` parent through a canonical representative in the localized
piece union.  The assignment is constant on each snapped y-layer.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalPopularGraphParentData
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
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    (prep : PureWZ2TerminalPopularGraphPreparation localized) where
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
    parentOf cell ∈ localized.selectedParents
  representative_mem_piece :
    ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
      ∃ hparent : parentOf cell ∈ localized.selectedParents,
        representative cell ∈ localized.piece (parentOf cell) hparent
  representative_mem_parent :
    ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
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

theorem PureWZ2TerminalPopularGraphPreparation.graphParents
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
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    (prep : PureWZ2TerminalPopularGraphPreparation localized) :
    Nonempty (PureWZ2TerminalPopularGraphParentData prep) := by
  let root := terminal.sqrtRequested.1
  have hroot : 0 < root := terminal.sticky.coarse_extremal.delta_pos
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hdeltaRoot : delta ≤ root := by
    rw [show root = Real.sqrt delta by exact terminal.sqrtRequested_eq]
    nlinarith [Real.sqrt_nonneg delta, Real.sq_sqrt hdelta.le,
      source.extremal.delta_le_one]
  let representative (cell : ℤ × ℤ × ℤ) : Point3 :=
    if hcell : cell ∈ prep.windowed.global.cells then
      wz1Lemma23CellRepresentative prep.shadow hdelta
        ⟨cell, prep.windowed.global.cells_active hcell⟩ else 0
  have hrepresentativeMem :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        representative cell ∈ prep.shadow.union := by
    intro cell hcell
    simp only [representative, dif_pos hcell]
    exact wz1Lemma23CellRepresentative_mem_union prep.shadow hdelta _
  have hrepresentativeIndex :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        wz1Lemma23CellIndex delta (representative cell) = cell := by
    intro cell hcell
    simp only [representative, dif_pos hcell]
    exact wz1Lemma23CellRepresentative_index prep.shadow hdelta _
  have hparentExists : ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
      ∃ parent, ∃ hparent : parent ∈ localized.selectedParents,
        representative cell ∈ localized.piece parent hparent := by
    intro cell hcell
    have hshadow := hrepresentativeMem cell hcell
    rw [prep.shadow_union, prep.region_eq] at hshadow
    rcases Set.mem_iUnion.mp hshadow with ⟨parent, hpiece⟩
    exact ⟨parent.1, parent.2, hpiece⟩
  let defaultParent := Classical.choose localized.selected_nonempty
  let parentOf (cell : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
    if hcell : cell ∈ prep.windowed.global.cells then
      Classical.choose (hparentExists cell hcell) else defaultParent
  have hparentMem : ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
      parentOf cell ∈ localized.selectedParents := by
    intro cell hcell
    simp only [parentOf, dif_pos hcell]
    exact Classical.choose (Classical.choose_spec (hparentExists cell hcell))
  have hrepPiece : ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
      ∃ hparent : parentOf cell ∈ localized.selectedParents,
        representative cell ∈ localized.piece (parentOf cell) hparent := by
    intro cell hcell
    let chosen := Classical.choose (hparentExists cell hcell)
    have hchosen : chosen ∈ localized.selectedParents :=
      Classical.choose (Classical.choose_spec (hparentExists cell hcell))
    have hpiece : representative cell ∈ localized.piece chosen hchosen :=
      Classical.choose_spec (Classical.choose_spec (hparentExists cell hcell))
    have hparentEq : parentOf cell = chosen := by
      simp [parentOf, hcell, chosen]
    rw [hparentEq]
    exact ⟨hchosen, hpiece⟩
  have hrepParent : ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
      representative cell ∈
        wz1PaperGridCube root (parentOf cell) := by
    intro cell hcell
    rcases hrepPiece cell hcell with ⟨hparent, hpiece⟩
    exact localized.piece_subset_parent (parentOf cell) hparent hpiece
  have hfarParents :
      ∀ first (hfirst : first ∈ prep.windowed.global.cells),
        ∀ second (hsecond : second ∈ prep.windowed.global.cells),
          parentOf first ≠ parentOf second →
            511 * root <
              |representative first 1 - representative second 1| := by
    intro first hfirst second hsecond hne
    have hyParent := localized.y_separated
      (parentOf first) (hparentMem first hfirst)
      (parentOf second) (hparentMem second hsecond) hne
    have hyNe : (parentOf first).2.1 ≠ (parentOf second).2.1 := by
      intro hy
      rw [hy] at hyParent
      norm_num at hyParent
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
      have hfar : 511 * root <
          representative second 1 - representative first 1 := by
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
      have hfar : 511 * root <
          representative first 1 - representative second 1 := by
        linarith [hsecondBox.2.2.2.1, hfirstBox.2.2.1]
      rw [abs_of_pos (by linarith [hfar])]
      exact hfar
  have hsameY :
      ∀ first (hfirst : first ∈ prep.windowed.global.cells),
        ∀ second (hsecond : second ∈ prep.windowed.global.cells),
          first.2.1 = second.2.1 → parentOf first = parentOf second := by
    intro first hfirst second hsecond hy
    have hfirstCenter :=
      ((wz1_lemma23_snapped_cell_geometry delta hdelta
        source.extremal.delta_le_one).2.1 first (representative first)
        (hrepresentativeIndex first hfirst)).1 1
    have hsecondCenter :=
      ((wz1_lemma23_snapped_cell_geometry delta hdelta
        source.extremal.delta_le_one).2.1 second (representative second)
        (hrepresentativeIndex second hsecond)).1 1
    have hcentersEqual :=
      (wz1_lemma23_snapped_cell_geometry delta hdelta
        source.extremal.delta_le_one).2.2.1 first second hy
    have hpointClose :
        |representative first 1 - representative second 1| ≤ delta := by
      have htriangle :
          |representative first 1 - representative second 1| ≤
            |representative first 1 - (wz1Lemma23CellCenter delta first) 1| +
            |representative second 1 - (wz1Lemma23CellCenter delta second) 1| := by
        calc
          _ = |(representative first 1 -
                (wz1Lemma23CellCenter delta first) 1) +
              ((wz1Lemma23CellCenter delta second) 1 -
                representative second 1)| := by
            rw [hcentersEqual]
            ring_nf
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

/-- The localized-piece anchor attached to one exact graph cell. -/
def PureWZ2TerminalPopularGraphParentData.anchorFor
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
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    {prep : PureWZ2TerminalPopularGraphPreparation localized}
    (data : PureWZ2TerminalPopularGraphParentData prep)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ prep.windowed.global.cells) : Point3 :=
  localized.anchor (data.parentOf cell) (data.parent_mem cell hcell)

lemma PureWZ2TerminalPopularGraphParentData.anchorFor_mem_shadow
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
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    {prep : PureWZ2TerminalPopularGraphPreparation localized}
    (data : PureWZ2TerminalPopularGraphParentData prep)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ prep.windowed.global.cells) :
    data.anchorFor cell hcell ∈ prep.shadow.union := by
  rw [prep.shadow_union, prep.region_eq]
  exact Set.mem_iUnion.mpr
    ⟨⟨data.parentOf cell, data.parent_mem cell hcell⟩,
      localized.anchor_mem _ _⟩

lemma PureWZ2TerminalPopularGraphParentData.canonical_rep_dist_anchor
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
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    {prep : PureWZ2TerminalPopularGraphPreparation localized}
    (data : PureWZ2TerminalPopularGraphParentData prep)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ prep.windowed.global.cells) :
    dist
        (wz1Lemma23CellRepresentative prep.shadow
          source.extremal.delta_pos
          ⟨cell, prep.windowed.global.cells_active hcell⟩)
        (data.anchorFor cell hcell) ≤ Real.sqrt delta := by
  have hrepEq : wz1Lemma23CellRepresentative prep.shadow
      source.extremal.delta_pos
      ⟨cell, prep.windowed.global.cells_active hcell⟩ =
        data.representative cell :=
    (data.representative_eq cell hcell).symm
  rw [hrepEq]
  rcases data.representative_mem_piece cell hcell with ⟨hparent, hpiece⟩
  have hball := localized.piece_ball (data.parentOf cell) hparent hpiece
  rw [Metric.mem_closedBall] at hball
  simpa [PureWZ2TerminalPopularGraphParentData.anchorFor,
    terminal.sqrtRequested_eq] using hball

lemma PureWZ2TerminalPopularGraphParentData.anchorFor_mem_parent
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
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    {prep : PureWZ2TerminalPopularGraphPreparation localized}
    (data : PureWZ2TerminalPopularGraphParentData prep)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ prep.windowed.global.cells) :
    data.anchorFor cell hcell ∈
      wz1PaperGridCube terminal.sqrtRequested.1 (data.parentOf cell) := by
  exact localized.piece_subset_parent _ _ (localized.anchor_mem _ _)

lemma PureWZ2TerminalPopularGraphParentData.anchorFor_localized
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
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    {prep : PureWZ2TerminalPopularGraphPreparation localized}
    (data : PureWZ2TerminalPopularGraphParentData prep)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ prep.windowed.global.cells) :
    |inner ℝ (data.anchorFor cell hcell)
          (globalGrainDirection
            (source.globalGrains.slope ((data.anchorFor cell hcell) 2))) -
        localized.center| ≤ terminal.sqrtRequested.1 / 2 := by
  exact localized.piece_localized _ _ _ (localized.anchor_mem _ _)

lemma PureWZ2TerminalPopularGraphParentData.anchorFor_dist
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
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    {prep : PureWZ2TerminalPopularGraphPreparation localized}
    (data : PureWZ2TerminalPopularGraphParentData prep)
    (first : ℤ × ℤ × ℤ) (hfirst : first ∈ prep.windowed.global.cells)
    (second : ℤ × ℤ × ℤ) (hsecond : second ∈ prep.windowed.global.cells) :
    dist (data.anchorFor first hfirst) (data.anchorFor second hsecond) ≤
      4 * |wz1Lemma23SnappedYValue delta first.2.1 -
        wz1Lemma23SnappedYValue delta second.2.1| := by
  by_cases hparent : data.parentOf first = data.parentOf second
  · have hanchor : data.anchorFor first hfirst = data.anchorFor second hsecond := by
      simp only [PureWZ2TerminalPopularGraphParentData.anchorFor, hparent]
    rw [hanchor, dist_self]
    positivity
  · let firstRep := data.representative first
    let secondRep := data.representative second
    let firstAnchor := data.anchorFor first hfirst
    let secondAnchor := data.anchorFor second hsecond
    let root := terminal.sqrtRequested.1
    let y₁ := wz1Lemma23SnappedYValue delta first.2.1
    let y₂ := wz1Lemma23SnappedYValue delta second.2.1
    let d := |y₁ - y₂|
    have hroot : 0 < root := terminal.sticky.coarse_extremal.delta_pos
    have hdelta : 0 < delta := source.extremal.delta_pos
    have hdeltaRoot : delta ≤ root := by
      rw [show root = Real.sqrt delta by exact terminal.sqrtRequested_eq]
      nlinarith [Real.sqrt_nonneg delta, Real.sq_sqrt hdelta.le,
        source.extremal.delta_le_one]
    have hfirstCenter := ((wz1_lemma23_snapped_cell_geometry delta hdelta
      source.extremal.delta_le_one).2.1 first firstRep
      (data.representative_index first hfirst)).1 1
    have hsecondCenter := ((wz1_lemma23_snapped_cell_geometry delta hdelta
      source.extremal.delta_le_one).2.1 second secondRep
      (data.representative_index second hsecond)).1 1
    have hfirstY : |firstRep 1 - y₁| ≤ delta / 2 := by
      simpa [y₁, wz1Lemma23SnappedYValue, wz1Lemma23CellCenter, point3]
        using hfirstCenter
    have hsecondY : |secondRep 1 - y₂| ≤ delta / 2 := by
      simpa [y₂, wz1Lemma23SnappedYValue, wz1Lemma23CellCenter, point3]
        using hsecondCenter
    have hrepYUpper : |firstRep 1 - secondRep 1| ≤ d + delta := by
      calc
        _ = |(firstRep 1 - y₁) + (y₁ - y₂) + (y₂ - secondRep 1)| := by
          ring_nf
        _ ≤ |firstRep 1 - y₁| + |y₁ - y₂| + |y₂ - secondRep 1| := by
          calc
            _ ≤ |(firstRep 1 - y₁) + (y₁ - y₂)| +
                |y₂ - secondRep 1| := abs_add_le _ _
            _ ≤ (|firstRep 1 - y₁| + |y₁ - y₂|) +
                |y₂ - secondRep 1| := by gcongr; exact abs_add_le _ _
        _ ≤ d + delta := by
          rw [abs_sub_comm y₂ (secondRep 1)]
          dsimp only [d]
          linarith
    have hfar := data.different_parent_y_far first hfirst second hsecond hparent
    have hseparation : 510 * root < d := by linarith
    have hfirstAnchorRep : dist firstAnchor firstRep ≤ root := by
      rw [show firstRep = wz1Lemma23CellRepresentative prep.shadow
        source.extremal.delta_pos
        ⟨first, prep.windowed.global.cells_active hfirst⟩ by
          exact data.representative_eq first hfirst]
      rw [show root = Real.sqrt delta by exact terminal.sqrtRequested_eq]
      simpa [firstAnchor, dist_comm] using
        data.canonical_rep_dist_anchor first hfirst
    have hsecondRepAnchor : dist secondRep secondAnchor ≤ root := by
      rw [show secondRep = wz1Lemma23CellRepresentative prep.shadow
        source.extremal.delta_pos
        ⟨second, prep.windowed.global.cells_active hsecond⟩ by
          exact data.representative_eq second hsecond]
      rw [show root = Real.sqrt delta by exact terminal.sqrtRequested_eq]
      simpa [secondAnchor] using data.canonical_rep_dist_anchor second hsecond
    have hy : |firstAnchor 1 - secondAnchor 1| ≤ d + 3 * root := by
      have hfirstCoord := abs_coord_sub_le_dist
        (x := firstAnchor) (y := firstRep) (1 : Fin 3)
      have hsecondCoord := abs_coord_sub_le_dist
        (x := secondRep) (y := secondAnchor) (1 : Fin 3)
      calc
        _ = |(firstAnchor 1 - firstRep 1) +
            (firstRep 1 - secondRep 1) +
            (secondRep 1 - secondAnchor 1)| := by ring_nf
        _ ≤ |firstAnchor 1 - firstRep 1| +
            |firstRep 1 - secondRep 1| +
            |secondRep 1 - secondAnchor 1| := by
          calc
            _ ≤ |(firstAnchor 1 - firstRep 1) +
                  (firstRep 1 - secondRep 1)| +
                |secondRep 1 - secondAnchor 1| := abs_add_le _ _
            _ ≤ (|firstAnchor 1 - firstRep 1| +
                  |firstRep 1 - secondRep 1|) +
                |secondRep 1 - secondAnchor 1| := by
              gcongr
              exact abs_add_le _ _
        _ ≤ d + 3 * root := by
          have hrepBound : |firstRep 1 - secondRep 1| ≤ d + root :=
            hrepYUpper.trans (by linarith)
          have hfirstCoordRoot : |firstAnchor 1 - firstRep 1| ≤ root :=
            hfirstCoord.trans hfirstAnchorRep
          have hsecondCoordRoot : |secondRep 1 - secondAnchor 1| ≤ root :=
            hsecondCoord.trans hsecondRepAnchor
          linarith
    have hfirstBox := data.anchorFor_mem_parent first hfirst
    have hsecondBox := data.anchorFor_mem_parent second hsecond
    rw [wz1PaperGridCube_eq_Ico hroot (data.parentOf first)] at hfirstBox
    rw [wz1PaperGridCube_eq_Ico hroot (data.parentOf second)] at hsecondBox
    have hparentHeightFirst := selection.parent_height_eq _
      (localized.selected_subset (data.parent_mem first hfirst))
    have hparentHeightSecond := selection.parent_height_eq _
      (localized.selected_subset (data.parent_mem second hsecond))
    have hz : |firstAnchor 2 - secondAnchor 2| ≤ root := by
      rw [abs_le]
      rw [hparentHeightFirst] at hfirstBox
      rw [hparentHeightSecond] at hsecondBox
      constructor
      · linarith [hfirstBox.2.2.2.2.1, hsecondBox.2.2.2.2.2.le]
      · linarith [hsecondBox.2.2.2.2.1, hfirstBox.2.2.2.2.2.le]
    have hfirstPaper : firstAnchor ∈ source.shading.union :=
      prep.shadow_source (data.anchorFor_mem_shadow first hfirst)
    have hsecondPaper : secondAnchor ∈ source.shading.union :=
      prep.shadow_source (data.anchorFor_mem_shadow second hsecond)
    have hfirstAxis := shading_union_subset_axisBox hfirstPaper
    have hsecondAxis := shading_union_subset_axisBox hsecondPaper
    have hfirstHeight : firstAnchor 2 ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Kakeya.Streamlined.axisBox, abs_le] using hfirstAxis.2.2
    have hsecondHeight : secondAnchor 2 ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Kakeya.Streamlined.axisBox, abs_le] using hsecondAxis.2.2
    have hsecondYBound : |secondAnchor 1| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hsecondAxis.2.1
    have hslopeFirst : |source.globalGrains.slope (firstAnchor 2)| ≤ 3 :=
      source.globalGrains.slope_bound _ hfirstHeight
    have hslopeDiff : |source.globalGrains.slope (firstAnchor 2) -
        source.globalGrains.slope (secondAnchor 2)| ≤ root := by
      have hlip := source.globalGrains.slope_lipschitz.dist_le_mul
        (firstAnchor 2) hfirstHeight (secondAnchor 2) hsecondHeight
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
      exact hlip.trans hz
    have hprojection :
        |(firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) * firstAnchor 1) -
          (secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) * secondAnchor 1)| ≤
          root := by
      have hfirstLine := data.anchorFor_localized first hfirst
      have hsecondLine := data.anchorFor_localized second hsecond
      have hfirstInner : inner ℝ firstAnchor
            (globalGrainDirection (source.globalGrains.slope (firstAnchor 2))) =
          firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) * firstAnchor 1 := by
        simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      have hsecondInner : inner ℝ secondAnchor
            (globalGrainDirection (source.globalGrains.slope (secondAnchor 2))) =
          secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) * secondAnchor 1 := by
        simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      rw [hfirstInner] at hfirstLine
      rw [hsecondInner] at hsecondLine
      have htriangle := abs_sub
        ((firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) * firstAnchor 1) -
          localized.center)
        ((secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) * secondAnchor 1) -
          localized.center)
      have hrearrange :
          ((firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) * firstAnchor 1) -
            localized.center) -
          ((secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) * secondAnchor 1) -
            localized.center) =
          (firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) * firstAnchor 1) -
          (secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) * secondAnchor 1) := by
        ring
      rw [hrearrange] at htriangle
      linarith
    have hslopeProduct :
        |source.globalGrains.slope (firstAnchor 2) * firstAnchor 1 -
          source.globalGrains.slope (secondAnchor 2) * secondAnchor 1| ≤
          3 * |firstAnchor 1 - secondAnchor 1| + root := by
      have hrearrange :
          source.globalGrains.slope (firstAnchor 2) * firstAnchor 1 -
            source.globalGrains.slope (secondAnchor 2) * secondAnchor 1 =
          source.globalGrains.slope (firstAnchor 2) *
              (firstAnchor 1 - secondAnchor 1) +
            (source.globalGrains.slope (firstAnchor 2) -
              source.globalGrains.slope (secondAnchor 2)) * secondAnchor 1 := by
        ring
      rw [hrearrange]
      calc
        _ ≤ |source.globalGrains.slope (firstAnchor 2)| *
              |firstAnchor 1 - secondAnchor 1| +
            |source.globalGrains.slope (firstAnchor 2) -
              source.globalGrains.slope (secondAnchor 2)| * |secondAnchor 1| := by
          simpa [abs_mul] using abs_add_le
            (source.globalGrains.slope (firstAnchor 2) *
              (firstAnchor 1 - secondAnchor 1))
            ((source.globalGrains.slope (firstAnchor 2) -
              source.globalGrains.slope (secondAnchor 2)) * secondAnchor 1)
        _ ≤ 3 * |firstAnchor 1 - secondAnchor 1| + root := by
          have hyNonneg := abs_nonneg (firstAnchor 1 - secondAnchor 1)
          nlinarith [mul_le_mul_of_nonneg_right hslopeFirst hyNonneg,
            mul_le_mul hslopeDiff hsecondYBound (abs_nonneg _) (by positivity)]
    have hx : |firstAnchor 0 - secondAnchor 0| ≤ 3 * d + 11 * root := by
      have hsolve := abs_sub
        ((firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) * firstAnchor 1) -
          (secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) * secondAnchor 1))
        (source.globalGrains.slope (firstAnchor 2) * firstAnchor 1 -
          source.globalGrains.slope (secondAnchor 2) * secondAnchor 1)
      have hrearrange :
          ((firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) * firstAnchor 1) -
            (secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) * secondAnchor 1)) -
          (source.globalGrains.slope (firstAnchor 2) * firstAnchor 1 -
            source.globalGrains.slope (secondAnchor 2) * secondAnchor 1) =
          firstAnchor 0 - secondAnchor 0 := by ring
      rw [hrearrange] at hsolve
      linarith
    have hx' : |firstAnchor 0 - secondAnchor 0| ≤ 31 * d / 10 := by linarith
    have hy' : |firstAnchor 1 - secondAnchor 1| ≤ 101 * d / 100 := by linarith
    have hz' : |firstAnchor 2 - secondAnchor 2| ≤ d / 100 := by linarith
    have hxSq : (firstAnchor 0 - secondAnchor 0)^2 ≤ (31*d/10)^2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg (by positivity : 0 ≤ 31*d/10)] using hx'
    have hySq : (firstAnchor 1 - secondAnchor 1)^2 ≤ (101*d/100)^2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg (by positivity : 0 ≤ 101*d/100)] using hy'
    have hzSq : (firstAnchor 2 - secondAnchor 2)^2 ≤ (d/100)^2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg (by positivity : 0 ≤ d/100)] using hz'
    have hcoeff : (31*d/10)^2 + (101*d/100)^2 + (d/100)^2 ≤ (4*d)^2 := by
      nlinarith [sq_nonneg d]
    have hdistSq : dist firstAnchor secondAnchor ^ 2 ≤ (4*d)^2 := by
      rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three]
      simpa [Real.dist_eq, sq_abs] using
        (add_le_add (add_le_add hxSq hySq) hzSq).trans hcoeff
    exact (sq_le_sq₀ dist_nonneg (by positivity : 0 ≤ 4*d)).mp hdistSq

end Kakeya.Assouad

end
