import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineResidueFullGrains
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers

/-!
# Map genuine Lemma-23 graph cells to actual residue parents

The graph diameter grid and the paper grid are not identified.  Each graph
cell is assigned through its genuine shaded representative.  Residue
separation then proves that two graph cells with the same snapped y-index
must belong to the same actual paper parent.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2HorizontalFixedLineGraphParentData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading :
      PureWZ2HorizontalFixedLineResidueShadingData residue}
    (prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading) where
  representative : (ℤ × ℤ × ℤ) → Point3
  representative_mem :
    ∀ cell ∈ prep.windowed.global.cells,
      representative cell ∈ prep.shadow.union
  representative_index :
    ∀ cell ∈ prep.windowed.global.cells,
      wz1Lemma23CellIndex prep.graphScale (representative cell) = cell
  rhoCellOf : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
  rhoCellOf_eq :
    ∀ cell ∈ prep.windowed.global.cells,
      rhoCellOf cell = wz1PaperGridIndex rho (representative cell)
  rhoCell_mem :
    ∀ cell ∈ prep.windowed.global.cells,
      rhoCellOf cell ∈
        wz1PaperActiveCells residueShading.shading
          twoScale.coarseGrains.extremal.delta_pos
  representative_mem_rhoCell :
    ∀ cell ∈ prep.windowed.global.cells,
      representative cell ∈ wz1PaperGridCube rho (rhoCellOf cell)
  parentOf : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
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

theorem PureWZ2HorizontalFixedLineResiduePreparation.graphParents
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading :
      PureWZ2HorizontalFixedLineResidueShadingData residue}
    (prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading) :
    Nonempty (PureWZ2HorizontalFixedLineGraphParentData prep) := by
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
  let rhoCellOf : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun cell =>
    wz1PaperGridIndex rho (representative cell)
  have hrhoCellEq :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        rhoCellOf cell = wz1PaperGridIndex rho (representative cell) := by
    intro cell hcell
    rfl
  have hrhoCellMem :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        rhoCellOf cell ∈
          wz1PaperActiveCells residueShading.shading
            twoScale.coarseGrains.extremal.delta_pos := by
    intro cell hcell
    have hshadow := hrepresentativeMem cell hcell
    have hpaper : representative cell ∈ residueShading.shading.union := by
      rwa [prep.shadow_union] at hshadow
    rw [mem_wz1PaperActiveCells]
    refine ⟨?_, ⟨representative cell, hpaper, ?_⟩⟩
    · rcases hpaper with ⟨index, hindex⟩
      have hbody := residueShading.shading.subset_body index hindex
      simpa only [rhoCellOf, twoScale.rhoRequested_eq] using
        (paper_point_gridIndex_in_window
          twoScale.coarseGrains.extremal.delta_pos hbody.2)
    · simpa only [twoScale.rhoRequested_eq] using
        ((mem_wz1PaperGridCube rho
          (rhoCellOf cell) (representative cell)).mpr rfl)
  have hrepRhoCell :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        representative cell ∈ wz1PaperGridCube rho (rhoCellOf cell) := by
    intro cell hcell
    exact (mem_wz1PaperGridCube rho
      (rhoCellOf cell) (representative cell)).mpr rfl
  have hparentExists :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        ∃ parent ∈ residue.selected,
          representative cell ∈ wz1PaperGridCube root parent := by
    intro cell hcell
    have hshadow := hrepresentativeMem cell hcell
    have hpaper : representative cell ∈ residueShading.shading.union := by
      rwa [prep.shadow_union] at hshadow
    rw [residueShading.union_eq] at hpaper
    rw [residueShading.selectedRegion_eq] at hpaper
    simpa [root] using Set.mem_iUnion₂.mp hpaper.2
  let defaultParent := Classical.choose residue.selected_nonempty
  let parentOf : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun cell =>
    if hcell : cell ∈ prep.windowed.global.cells then
      Classical.choose (hparentExists cell hcell)
    else defaultParent
  have hparentMem :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        parentOf cell ∈ residue.selected := by
    intro cell hcell
    simp only [parentOf, dif_pos hcell]
    exact (Classical.choose_spec (hparentExists cell hcell)).1
  have hrepParent :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        representative cell ∈ wz1PaperGridCube root (parentOf cell) := by
    intro cell hcell
    simp only [parentOf, dif_pos hcell]
    exact (Classical.choose_spec (hparentExists cell hcell)).2
  have hfarParents :
      ∀ first (hfirst : first ∈ prep.windowed.global.cells),
        ∀ second (hsecond : second ∈ prep.windowed.global.cells),
          parentOf first ≠ parentOf second →
            511 * root <
              |representative first (1 : Fin 3) -
                representative second (1 : Fin 3)| := by
    intro first hfirst second hsecond hne
    let firstPoint := representative first
    let secondPoint := representative second
    let firstParent := parentOf first
    let secondParent := parentOf second
    have hparentYNe : firstParent.2.1 ≠ secondParent.2.1 := by
      intro heq
      exact hne
        (selection.selected_y_injective
          (residue.selected_subset (hparentMem first hfirst))
          (residue.selected_subset (hparentMem second hsecond)) heq)
    have hsep := residue.y_separated firstParent (hparentMem first hfirst)
      secondParent (hparentMem second hsecond)
    have hyParent : (512 : ℤ) ≤ |firstParent.2.1 - secondParent.2.1| :=
      hsep.resolve_left hparentYNe
    have hfirstParentBox := hrepParent first hfirst
    have hsecondParentBox := hrepParent second hsecond
    rw [wz1PaperGridCube_eq_Ico hroot firstParent] at hfirstParentBox
    rw [wz1PaperGridCube_eq_Ico hroot secondParent] at hsecondParentBox
    by_cases horder : firstParent.2.1 < secondParent.2.1
    · have hindexGap : (512 : ℤ) ≤ secondParent.2.1 - firstParent.2.1 := by
        have habs : |firstParent.2.1 - secondParent.2.1| =
            secondParent.2.1 - firstParent.2.1 := by
          rw [abs_of_neg (sub_neg.mpr horder)]
          ring
        rwa [habs] at hyParent
      have hcastGap : (512 : ℝ) ≤
          (secondParent.2.1 : ℝ) - (firstParent.2.1 : ℝ) := by
        exact_mod_cast hindexGap
      have hmulGap := mul_le_mul_of_nonneg_right hcastGap hroot.le
      have hmulEq :
          ((secondParent.2.1 : ℝ) - (firstParent.2.1 : ℝ)) * root =
            (secondParent.2.1 : ℝ) * root -
              (firstParent.2.1 : ℝ) * root := by ring
      rw [hmulEq] at hmulGap
      have hfar : 511 * root < secondPoint 1 - firstPoint 1 := by
        have hfirstUpper := hfirstParentBox.2.2.2.1
        have hsecondLower := hsecondParentBox.2.2.1
        linarith
      rw [abs_sub_comm, abs_of_pos (by linarith [hfar])]
      exact hfar
    · have horder' : secondParent.2.1 < firstParent.2.1 := by
        omega
      have hindexGap : (512 : ℤ) ≤ firstParent.2.1 - secondParent.2.1 := by
        have habs : |firstParent.2.1 - secondParent.2.1| =
            firstParent.2.1 - secondParent.2.1 := by
          rw [abs_of_pos (sub_pos.mpr horder')]
        rwa [habs] at hyParent
      have hcastGap : (512 : ℝ) ≤
          (firstParent.2.1 : ℝ) - (secondParent.2.1 : ℝ) := by
        exact_mod_cast hindexGap
      have hmulGap := mul_le_mul_of_nonneg_right hcastGap hroot.le
      have hmulEq :
          ((firstParent.2.1 : ℝ) - (secondParent.2.1 : ℝ)) * root =
            (firstParent.2.1 : ℝ) * root -
              (secondParent.2.1 : ℝ) * root := by ring
      rw [hmulEq] at hmulGap
      have hfar : 511 * root < firstPoint 1 - secondPoint 1 := by
        have hsecondUpper := hsecondParentBox.2.2.2.1
        have hfirstLower := hfirstParentBox.2.2.1
        linarith
      rw [abs_of_pos (by linarith [hfar])]
      exact hfar
  have hsameY :
      ∀ first (hfirst : first ∈ prep.windowed.global.cells),
        ∀ second (hsecond : second ∈ prep.windowed.global.cells),
          first.2.1 = second.2.1 → parentOf first = parentOf second := by
    intro first hfirst second hsecond hy
    let firstPoint := representative first
    let secondPoint := representative second
    let firstParent := parentOf first
    let secondParent := parentOf second
    have hfirstIndex := hrepresentativeIndex first hfirst
    have hsecondIndex := hrepresentativeIndex second hsecond
    have hfirstCenter :=
      ((wz1_lemma23_snapped_cell_geometry
          prep.graphScale hgraph prep.graphScale_one).2.1
        first firstPoint hfirstIndex).1 (1 : Fin 3)
    have hsecondCenter :=
      ((wz1_lemma23_snapped_cell_geometry
          prep.graphScale hgraph prep.graphScale_one).2.1
        second secondPoint hsecondIndex).1 (1 : Fin 3)
    have hcentersEqual :
        (wz1Lemma23CellCenter prep.graphScale first) (1 : Fin 3) =
          (wz1Lemma23CellCenter prep.graphScale second) (1 : Fin 3) := by
      exact (wz1_lemma23_snapped_cell_geometry
        prep.graphScale hgraph prep.graphScale_one).2.2.1 first second hy
    have hpointClose : |firstPoint 1 - secondPoint 1| ≤ prep.graphScale := by
      have htriangle :
          |firstPoint 1 - secondPoint 1| ≤
            |firstPoint 1 -
              (wz1Lemma23CellCenter prep.graphScale first) 1| +
            |secondPoint 1 -
              (wz1Lemma23CellCenter prep.graphScale second) 1| := by
        calc
          |firstPoint 1 - secondPoint 1| =
              |(firstPoint 1 -
                  (wz1Lemma23CellCenter prep.graphScale first) 1) +
                ((wz1Lemma23CellCenter prep.graphScale second) 1 -
                  secondPoint 1)| := by rw [hcentersEqual]; ring
          _ ≤ _ := by
            simpa [abs_sub_comm] using abs_add_le
              (firstPoint 1 -
                (wz1Lemma23CellCenter prep.graphScale first) 1)
              ((wz1Lemma23CellCenter prep.graphScale second) 1 -
                secondPoint 1)
      linarith [hfirstCenter, hsecondCenter]
    by_contra hne
    have hfar := hfarParents first hfirst second hsecond hne
    have hgraphSmall : prep.graphScale ≤ 14 * root := by
      linarith [prep.graphScale_two_root_bound]
    linarith [hpointClose]
  exact
    ⟨{ representative := representative
       representative_mem := hrepresentativeMem
       representative_index := hrepresentativeIndex
       rhoCellOf := rhoCellOf
       rhoCellOf_eq := hrhoCellEq
       rhoCell_mem := hrhoCellMem
       representative_mem_rhoCell := hrepRhoCell
       parentOf := parentOf
       parent_mem := hparentMem
       representative_mem_parent := hrepParent
       different_parent_y_far := hfarParents
       same_y_parent := hsameY }⟩

end Kakeya.Assouad
