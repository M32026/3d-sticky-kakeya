import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalResiduePreparation

/-!
# Map source-slope graph cells to actual residue parents

The Lemma-23 diameter grid is independent of both paper grids.  Each graph
cell is assigned through a genuine point of the final source carrier, first
to its selected side-`rho` cell and then to the actual side-`sqrt rho` residue
parent.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2SourceHorizontalFixedBinGraphParentData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    (prep : PureWZ2SourceHorizontalFixedBinResiduePreparation retained) where
  representative : (ℤ × ℤ × ℤ) → Point3
  representative_mem :
    ∀ cell ∈ prep.windowed.global.cells,
      representative cell ∈ prep.shadow.union
  representative_index :
    ∀ cell ∈ prep.windowed.global.cells,
      wz1Lemma23CellIndex prep.graphScale (representative cell) = cell
  rhoCellOf : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
  rhoCell_mem :
    ∀ cell ∈ prep.windowed.global.cells, rhoCellOf cell ∈ retained.selectedCells
  representative_mem_rhoCell :
    ∀ cell ∈ prep.windowed.global.cells,
      representative cell ∈ wz1PaperGridCube rho (rhoCellOf cell)
  parentOf : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
  parentOf_eq : ∀ cell ∈ prep.windowed.global.cells,
    parentOf cell = retained.cellParent (rhoCellOf cell)
  parent_mem :
    ∀ cell ∈ prep.windowed.global.cells,
      parentOf cell ∈ residue.selected
  representative_mem_parent :
    ∀ cell ∈ prep.windowed.global.cells,
      representative cell ∈
        wz1PaperGridCube twoScale.sqrtRequested.1 (parentOf cell)
  different_parent_y_far :
    ∀ first ∈ prep.windowed.global.cells,
      ∀ second ∈ prep.windowed.global.cells,
        parentOf first ≠ parentOf second →
          511 * twoScale.sqrtRequested.1 <
            |representative first (1 : Fin 3) -
              representative second (1 : Fin 3)|
  same_y_parent :
    ∀ first ∈ prep.windowed.global.cells,
      ∀ second ∈ prep.windowed.global.cells,
        first.2.1 = second.2.1 → parentOf first = parentOf second

theorem PureWZ2SourceHorizontalFixedBinResiduePreparation.graphParentsFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    (prep : PureWZ2SourceHorizontalFixedBinResiduePreparation retained) :
    Nonempty (PureWZ2SourceHorizontalFixedBinGraphParentData prep) := by
  let root := twoScale.sqrtRequested.1
  have hroot : 0 < root := twoScale.fine.coarse_extremal.delta_pos
  have hgraph : 0 < prep.graphScale := prep.graphScale_pos
  let representative : (ℤ × ℤ × ℤ) → Point3 := fun cell =>
    if hcell : cell ∈ prep.windowed.global.cells then
      wz1Lemma23CellRepresentative prep.shadow hgraph
        ⟨cell, prep.windowed.global.cells_active hcell⟩
    else 0
  have hrepresentativeMem :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        representative cell ∈ prep.shadow.union := by
    intro cell hcell
    simp only [representative, dif_pos hcell]
    exact wz1Lemma23CellRepresentative_mem_union prep.shadow hgraph _
  have hrepresentativeIndex :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        wz1Lemma23CellIndex prep.graphScale (representative cell) = cell := by
    intro cell hcell
    simp only [representative, dif_pos hcell]
    exact wz1Lemma23CellRepresentative_index prep.shadow hgraph _
  have hrhoCellExists :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        ∃ rhoCell ∈ retained.selectedCells,
          representative cell ∈ wz1PaperGridCube rho rhoCell := by
    intro cell hcell
    have hshadow := hrepresentativeMem cell hcell
    have hpaper : representative cell ∈ retained.shading.union := by
      exact prep.shadow_union_subset hshadow
    rw [retained.union_eq] at hpaper
    rw [retained.selectedRegion_eq] at hpaper
    rcases Set.mem_iUnion₂.mp hpaper.2 with
      ⟨selectedCell, hselectedCell, hpointCell⟩
    exact ⟨selectedCell, hselectedCell, hpointCell⟩
  let defaultRhoCell := retained.cellFor (Classical.choose residue.selected_nonempty)
  let rhoCellOf : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun cell =>
    if hcell : cell ∈ prep.windowed.global.cells then
      Classical.choose (hrhoCellExists cell hcell) else defaultRhoCell
  have hrhoCellMem :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        rhoCellOf cell ∈ retained.selectedCells := by
    intro cell hcell
    simp only [rhoCellOf, dif_pos hcell]
    exact (Classical.choose_spec (hrhoCellExists cell hcell)).1
  have hrepRhoCell :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        representative cell ∈ wz1PaperGridCube rho (rhoCellOf cell) := by
    intro cell hcell
    simp only [rhoCellOf, dif_pos hcell]
    exact (Classical.choose_spec (hrhoCellExists cell hcell)).2
  let defaultParent := Classical.choose residue.selected_nonempty
  let parentOf : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun cell =>
    retained.cellParent (rhoCellOf cell)
  have hparentEq :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        parentOf cell = retained.cellParent (rhoCellOf cell) := by
    intro cell hcell
    rfl
  have hparentMem :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        parentOf cell ∈ residue.selected := by
    intro cell hcell
    rw [hparentEq cell hcell]
    have hdata := Finset.mem_filter.mp (by
      rw [retained.selectedCells_eq] at hrhoCellMem
      exact hrhoCellMem cell hcell)
    exact hdata.2
  have hrepParent :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        representative cell ∈ wz1PaperGridCube root (parentOf cell) := by
    intro cell hcell
    rw [hparentEq cell hcell]
    have hmem := hrhoCellMem cell hcell
    rw [retained.selectedCells_eq] at hmem
    have hdata := Finset.mem_filter.mp hmem
    exact retained.cell_parent (rhoCellOf cell) hdata.1
      (hrepRhoCell cell hcell)
  have hfarParents :
      ∀ first (hfirst : first ∈ prep.windowed.global.cells),
        ∀ second (hsecond : second ∈ prep.windowed.global.cells),
          parentOf first ≠ parentOf second →
            511 * root <
              |representative first (1 : Fin 3) -
                representative second (1 : Fin 3)| := by
    intro first hfirst second hsecond hne
    have hparentYNe : (parentOf first).2.1 ≠ (parentOf second).2.1 := by
      intro heq
      exact hne
        (selection.selected_y_injective
          (residue.selected_subset (hparentMem first hfirst))
          (residue.selected_subset (hparentMem second hsecond)) heq)
    have hsep := residue.y_separated
      (parentOf first) (hparentMem first hfirst)
      (parentOf second) (hparentMem second hsecond)
    have hyParent :
        (512 : ℤ) ≤ |(parentOf first).2.1 - (parentOf second).2.1| :=
      hsep.resolve_left hparentYNe
    have hfirstBox := hrepParent first hfirst
    have hsecondBox := hrepParent second hsecond
    rw [wz1PaperGridCube_eq_Ico hroot (parentOf first)] at hfirstBox
    rw [wz1PaperGridCube_eq_Ico hroot (parentOf second)] at hsecondBox
    by_cases horder : (parentOf first).2.1 < (parentOf second).2.1
    · have hindexGap :
          (512 : ℤ) ≤ (parentOf second).2.1 - (parentOf first).2.1 := by
        have habs :
            |(parentOf first).2.1 - (parentOf second).2.1| =
              (parentOf second).2.1 - (parentOf first).2.1 := by
          rw [abs_of_neg (sub_neg.mpr horder)]
          ring
        rwa [habs] at hyParent
      have hcastGap :
          (512 : ℝ) ≤
            ((parentOf second).2.1 : ℝ) - ((parentOf first).2.1 : ℝ) := by
        exact_mod_cast hindexGap
      have hmulGap := mul_le_mul_of_nonneg_right hcastGap hroot.le
      have hfar :
          511 * root < representative second 1 - representative first 1 := by
        have hfirstUpper := hfirstBox.2.2.2.1
        have hsecondLower := hsecondBox.2.2.1
        nlinarith
      rw [abs_sub_comm, abs_of_pos (by linarith [hfar])]
      exact hfar
    · have horder' : (parentOf second).2.1 < (parentOf first).2.1 := by omega
      have hindexGap :
          (512 : ℤ) ≤ (parentOf first).2.1 - (parentOf second).2.1 := by
        have habs :
            |(parentOf first).2.1 - (parentOf second).2.1| =
              (parentOf first).2.1 - (parentOf second).2.1 := by
          rw [abs_of_pos (sub_pos.mpr horder')]
        rwa [habs] at hyParent
      have hcastGap :
          (512 : ℝ) ≤
            ((parentOf first).2.1 : ℝ) - ((parentOf second).2.1 : ℝ) := by
        exact_mod_cast hindexGap
      have hmulGap := mul_le_mul_of_nonneg_right hcastGap hroot.le
      have hfar :
          511 * root < representative first 1 - representative second 1 := by
        have hsecondUpper := hsecondBox.2.2.2.1
        have hfirstLower := hfirstBox.2.2.1
        nlinarith
      rw [abs_of_pos (by linarith [hfar])]
      exact hfar
  have hsameY :
      ∀ first (hfirst : first ∈ prep.windowed.global.cells),
        ∀ second (hsecond : second ∈ prep.windowed.global.cells),
          first.2.1 = second.2.1 → parentOf first = parentOf second := by
    intro first hfirst second hsecond hy
    have hfirstCenter :=
      ((wz1_lemma23_snapped_cell_geometry
          prep.graphScale hgraph prep.graphScale_one).2.1
        first (representative first) (hrepresentativeIndex first hfirst)).1
          (1 : Fin 3)
    have hsecondCenter :=
      ((wz1_lemma23_snapped_cell_geometry
          prep.graphScale hgraph prep.graphScale_one).2.1
        second (representative second)
          (hrepresentativeIndex second hsecond)).1 (1 : Fin 3)
    have hcentersEqual :
        (wz1Lemma23CellCenter prep.graphScale first) (1 : Fin 3) =
          (wz1Lemma23CellCenter prep.graphScale second) (1 : Fin 3) :=
      (wz1_lemma23_snapped_cell_geometry
        prep.graphScale hgraph prep.graphScale_one).2.2.1 first second hy
    have hpointClose :
        |representative first 1 - representative second 1| ≤
          prep.graphScale := by
      have htriangle :
          |representative first 1 - representative second 1| ≤
            |representative first 1 -
              (wz1Lemma23CellCenter prep.graphScale first) 1| +
            |representative second 1 -
              (wz1Lemma23CellCenter prep.graphScale second) 1| := by
        calc
          _ = |(representative first 1 -
                  (wz1Lemma23CellCenter prep.graphScale first) 1) +
                ((wz1Lemma23CellCenter prep.graphScale second) 1 -
                  representative second 1)| := by rw [hcentersEqual]; ring
          _ ≤ _ := by
            simpa [abs_sub_comm] using abs_add_le
              (representative first 1 -
                (wz1Lemma23CellCenter prep.graphScale first) 1)
              ((wz1Lemma23CellCenter prep.graphScale second) 1 -
                representative second 1)
      linarith [hfirstCenter, hsecondCenter]
    by_contra hne
    have hfar := hfarParents first hfirst second hsecond hne
    have hgraphSmall : prep.graphScale ≤ 14 * root := by
      linarith [prep.graphScale_two_root_bound]
    linarith
  exact ⟨{
    representative := representative
    representative_mem := hrepresentativeMem
    representative_index := hrepresentativeIndex
    rhoCellOf := rhoCellOf
    rhoCell_mem := hrhoCellMem
    representative_mem_rhoCell := hrepRhoCell
    parentOf := parentOf
    parentOf_eq := hparentEq
    parent_mem := hparentMem
    representative_mem_parent := hrepParent
    different_parent_y_far := hfarParents
    same_y_parent := hsameY
  }⟩

/-- Backwards-compatible graph-parent data on the maximal global bin. -/
abbrev PureWZ2SourceHorizontalGraphParentData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    (prep : PureWZ2SourceHorizontalResiduePreparation retained) :=
  PureWZ2SourceHorizontalFixedBinGraphParentData prep

/-- Compatibility wrapper for the former maximal-bin graph-parent API. -/
theorem PureWZ2SourceHorizontalResiduePreparation.graphParents
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    (prep : PureWZ2SourceHorizontalResiduePreparation retained) :
    Nonempty (PureWZ2SourceHorizontalGraphParentData prep) :=
  prep.graphParentsFixedBin

end Kakeya.Assouad
