import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderCarrier
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarsePreparation

/-!
# Graph cells on the genuine coarse carrier with original fine witnesses

The Lemma-23 graph grid has side `256 * rho`, while the first balanced cover
and its original-source witnesses use side `rho`.  This file records the two
cell indices separately and proves that graph cells in one snapped y-layer
belong to the same selected side-`sqrt rho` parent.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

attribute [local instance] Classical.propDecidable

structure PureWZ2SourceFixedBinCoarseGraphParentData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    (prep : PureWZ2SourceFixedBinCoarsePreparationData original) where
  representative : (ℤ × ℤ × ℤ) → Point3
  representative_mem :
    ∀ cell ∈ prep.windowed.global.cells,
      representative cell ∈ prep.shadow.union
  representative_index :
    ∀ cell ∈ prep.windowed.global.cells,
      wz1Lemma23CellIndex prep.graphScale (representative cell) = cell
  ownerCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
  owner_active :
    ∀ cell ∈ prep.windowed.global.cells,
      ownerCell cell ∈ fineWitnesses.coarseWitnesses.activeCells
  representative_mem_owner :
    ∀ cell ∈ prep.windowed.global.cells,
      representative cell ∈ wz1PaperGridCube rho (ownerCell cell)
  parentOf : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
  parent_mem :
    ∀ cell ∈ prep.windowed.global.cells,
      parentOf cell ∈ residue.selected
  representative_mem_parent :
    ∀ cell ∈ prep.windowed.global.cells,
      representative cell ∈
        wz1PaperGridCube twoScale.sqrtRequested.1 (parentOf cell)
  owner_witness_mem_parent :
    ∀ cell ∈ prep.windowed.global.cells,
      fineWitnesses.coarseWitnesses.witness (ownerCell cell) ∈
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

/-- Backwards-compatible maximal-bin view of fixed-bin graph parents. -/
abbrev PureWZ2SourceFixedLineCoarseGraphParentData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {original : PureWZ2SourceFixedLineCoarseOriginalSlopeData
      carriers.coarseCarrier carriers.fineWitnesses.coarseWitnesses}
    (prep : PureWZ2SourceFixedLineCoarsePreparationData original) : Type :=
  PureWZ2SourceFixedBinCoarseGraphParentData prep

theorem PureWZ2SourceFixedBinCoarsePreparationData.graphParentsFixedBin
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    (prep : PureWZ2SourceFixedBinCoarsePreparationData original) :
    Nonempty (PureWZ2SourceFixedBinCoarseGraphParentData prep) := by
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
  have hownerExists :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        ∃ owner ∈ fineWitnesses.coarseWitnesses.activeCells,
          representative cell ∈ wz1PaperGridCube rho owner := by
    intro cell hcell
    have hcarrier : representative cell ∈
        carrier.shading.union := by
      exact prep.shadow_union_subset (hrepresentativeMem cell hcell)
    have hcoarseGrains : representative cell ∈
        twoScale.coarseGrains.shading.union :=
      carrier.subshading.union_subset hcarrier
    have hcoarse : representative cell ∈
        twoScale.coarse.croppedCoarseShading.union :=
      twoScale.coarseGrains.subshading.union_subset hcoarseGrains
    rw [twoScale.coarse.balanced.coarse_union_eq] at hcoarse
    rcases Set.mem_iUnion₂.mp hcoarse with ⟨owner, howner, hpointOwner⟩
    have hownerActive : owner ∈ fineWitnesses.coarseWitnesses.activeCells := by
      rw [fineWitnesses.coarseWitnesses.activeCells_eq]
      exact howner
    refine ⟨owner, hownerActive, ?_⟩
    simpa only [twoScale.rhoRequested_eq] using hpointOwner
  let defaultOwner : ℤ × ℤ × ℤ := (0, 0, 0)
  let ownerCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun cell =>
    if hcell : cell ∈ prep.windowed.global.cells then
      Classical.choose (hownerExists cell hcell)
    else defaultOwner
  have hownerActive :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        ownerCell cell ∈
          fineWitnesses.coarseWitnesses.activeCells := by
    intro cell hcell
    simp only [ownerCell, dif_pos hcell]
    exact (Classical.choose_spec (hownerExists cell hcell)).1
  have hrepOwner :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        representative cell ∈ wz1PaperGridCube rho (ownerCell cell) := by
    intro cell hcell
    simp only [ownerCell, dif_pos hcell]
    exact (Classical.choose_spec (hownerExists cell hcell)).2
  have hparentExists :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        ∃ parent ∈ residue.selected,
          representative cell ∈ wz1PaperGridCube root parent := by
    intro cell hcell
    have hcarrier : representative cell ∈
        carrier.shading.union := by
      exact prep.shadow_union_subset (hrepresentativeMem cell hcell)
    rw [carrier.union_eq] at hcarrier
    rw [carrier.selectedRegion_eq] at hcarrier
    rcases Set.mem_iUnion₂.mp hcarrier.2 with
      ⟨parent, hparent, hpointParent⟩
    exact ⟨parent, hparent, by simpa only [root] using hpointParent⟩
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
  have hwitnessParent :
      ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
        fineWitnesses.coarseWitnesses.witness (ownerCell cell) ∈
          wz1PaperGridCube root (parentOf cell) := by
    intro cell hcell
    have hcarrier : representative cell ∈
        carrier.shading.union := by
      exact prep.shadow_union_subset (hrepresentativeMem cell hcell)
    rw [carrier.union_eq] at hcarrier
    rcases hcarrier.1 with ⟨fineIndex, hfineIndex⟩
    rcases twoScale.fine.balanced.fine_cell_nested
        fineIndex (representative cell) hfineIndex with
      ⟨nestedParent, _hnestedActive, hnested⟩
    have hcanonical : representative cell ∈
        wz1PaperGridCube twoScale.rhoRequested.1
          (wz1PaperGridIndex twoScale.rhoRequested.1
            (representative cell)) :=
      (mem_wz1PaperGridCube _ _ _).mpr rfl
    have hrepNested : representative cell ∈
        wz1PaperGridCube root nestedParent := hnested hcanonical
    have hnestedEq : nestedParent = parentOf cell :=
      ((mem_wz1PaperGridCube root nestedParent
        (representative cell)).mp hrepNested).symm.trans
      ((mem_wz1PaperGridCube root (parentOf cell)
        (representative cell)).mp (hrepParent cell hcell))
    have hownerEq : ownerCell cell = wz1PaperGridIndex rho
        (representative cell) :=
      ((mem_wz1PaperGridCube rho (ownerCell cell)
        (representative cell)).mp (hrepOwner cell hcell)).symm
    have hwitnessAtRequested :
        fineWitnesses.coarseWitnesses.witness (ownerCell cell) ∈
          wz1PaperGridCube twoScale.rhoRequested.1
            (wz1PaperGridIndex twoScale.rhoRequested.1
              (representative cell)) := by
      simpa [twoScale.rhoRequested_eq, hownerEq] using
        fineWitnesses.coarseWitnesses.witness_mem_cell
          (ownerCell cell) (hownerActive cell hcell)
    rw [← hnestedEq]
    exact hnested hwitnessAtRequested
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
      exact hne (selection.selected_y_injective
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
        have habs : |(parentOf first).2.1 - (parentOf second).2.1| =
            (parentOf second).2.1 - (parentOf first).2.1 := by
          rw [abs_of_neg (sub_neg.mpr horder)]
          ring
        rwa [habs] at hyParent
      have hcastGap : (512 : ℝ) ≤
          ((parentOf second).2.1 : ℝ) - ((parentOf first).2.1 : ℝ) := by
        exact_mod_cast hindexGap
      have hmulGap := mul_le_mul_of_nonneg_right hcastGap hroot.le
      have hfar : 511 * root < representative second 1 -
          representative first 1 := by
        have hfirstUpper := hfirstBox.2.2.2.1
        have hsecondLower := hsecondBox.2.2.1
        nlinarith
      rw [abs_sub_comm, abs_of_pos (by linarith [hfar])]
      exact hfar
    · have horder' : (parentOf second).2.1 < (parentOf first).2.1 := by
        omega
      have hindexGap :
          (512 : ℤ) ≤ (parentOf first).2.1 - (parentOf second).2.1 := by
        have habs : |(parentOf first).2.1 - (parentOf second).2.1| =
            (parentOf first).2.1 - (parentOf second).2.1 := by
          rw [abs_of_pos (sub_pos.mpr horder')]
        rwa [habs] at hyParent
      have hcastGap : (512 : ℝ) ≤
          ((parentOf first).2.1 : ℝ) - ((parentOf second).2.1 : ℝ) := by
        exact_mod_cast hindexGap
      have hmulGap := mul_le_mul_of_nonneg_right hcastGap hroot.le
      have hfar : 511 * root < representative first 1 -
          representative second 1 := by
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
      ((wz1_lemma23_snapped_cell_geometry prep.graphScale hgraph
        prep.graphScale_one).2.1 first (representative first)
        (hrepresentativeIndex first hfirst)).1 (1 : Fin 3)
    have hsecondCenter :=
      ((wz1_lemma23_snapped_cell_geometry prep.graphScale hgraph
        prep.graphScale_one).2.1 second (representative second)
        (hrepresentativeIndex second hsecond)).1 (1 : Fin 3)
    have hcentersEqual :
        (wz1Lemma23CellCenter prep.graphScale first) (1 : Fin 3) =
          (wz1Lemma23CellCenter prep.graphScale second) (1 : Fin 3) :=
      (wz1_lemma23_snapped_cell_geometry prep.graphScale hgraph
        prep.graphScale_one).2.2.1 first second hy
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
                  representative second 1)| := by
              rw [hcentersEqual]
              ring
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
    ownerCell := ownerCell
    owner_active := hownerActive
    representative_mem_owner := hrepOwner
    parentOf := parentOf
    parent_mem := hparentMem
    representative_mem_parent := hrepParent
    owner_witness_mem_parent := hwitnessParent
    different_parent_y_far := hfarParents
    same_y_parent := hsameY
  }⟩

/-- Backwards-compatible maximal-bin constructor for graph parents. -/
theorem PureWZ2SourceFixedLineCoarsePreparationData.graphParents
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {original : PureWZ2SourceFixedLineCoarseOriginalSlopeData
      carriers.coarseCarrier carriers.fineWitnesses.coarseWitnesses}
    (prep : PureWZ2SourceFixedLineCoarsePreparationData original) :
    Nonempty (PureWZ2SourceFixedLineCoarseGraphParentData prep) :=
  prep.graphParentsFixedBin

/-- The original fine anchor attached to a genuine coarse graph cell through
its selected side-`sqrt rho` parent. -/
def PureWZ2SourceFixedBinCoarseGraphParentData.anchorFor
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    (graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep)
    (cell : ℤ × ℤ × ℤ)
    (_hcell : cell ∈ prep.windowed.global.cells) : Point3 :=
  fineWitnesses.witness (graphParents.parentOf cell)

/-- Backwards-compatible maximal-bin name for `anchorFor`. -/
def PureWZ2SourceFixedLineCoarseGraphParentData.anchorFor
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {original : PureWZ2SourceFixedLineCoarseOriginalSlopeData
      carriers.coarseCarrier carriers.fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedLineCoarsePreparationData original}
    (graphParents : PureWZ2SourceFixedLineCoarseGraphParentData prep)
    (cell : ℤ × ℤ × ℤ)
    (hcell : cell ∈ prep.windowed.global.cells) : Point3 :=
  PureWZ2SourceFixedBinCoarseGraphParentData.anchorFor graphParents cell hcell

/-- Original fine anchors vary at most four times the snapped graph-y
separation.  This is the same fixed-line geometry as the source-shadow route,
but the graph representatives themselves now belong to the genuine coarse
carrier. -/
lemma PureWZ2SourceFixedBinCoarseGraphParentData.anchorFor_dist
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    (graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep)
    (first : ℤ × ℤ × ℤ)
    (hfirst : first ∈ prep.windowed.global.cells)
    (second : ℤ × ℤ × ℤ)
    (hsecond : second ∈ prep.windowed.global.cells) :
    dist (graphParents.anchorFor first hfirst)
        (graphParents.anchorFor second hsecond) ≤
      4 * |wz1Lemma23SnappedYValue prep.graphScale first.2.1 -
        wz1Lemma23SnappedYValue prep.graphScale second.2.1| := by
  let firstParent := graphParents.parentOf first
  let secondParent := graphParents.parentOf second
  by_cases hparent : firstParent = secondParent
  · have hanchor : graphParents.anchorFor first hfirst =
        graphParents.anchorFor second hsecond := by
      simp only [PureWZ2SourceFixedBinCoarseGraphParentData.anchorFor]
      rw [show graphParents.parentOf first = graphParents.parentOf second by
        simpa [firstParent, secondParent] using hparent]
    rw [hanchor, dist_self]
    positivity
  · let firstRep := graphParents.representative first
    let secondRep := graphParents.representative second
    let firstAnchor := graphParents.anchorFor first hfirst
    let secondAnchor := graphParents.anchorFor second hsecond
    let root := twoScale.sqrtRequested.1
    let y₁ := wz1Lemma23SnappedYValue prep.graphScale first.2.1
    let y₂ := wz1Lemma23SnappedYValue prep.graphScale second.2.1
    let d := |y₁ - y₂|
    have hroot : 0 < root := twoScale.fine.coarse_extremal.delta_pos
    have hfirstCenter :=
      ((wz1_lemma23_snapped_cell_geometry prep.graphScale
        prep.graphScale_pos prep.graphScale_one).2.1 first firstRep
        (graphParents.representative_index first hfirst)).1 (1 : Fin 3)
    have hsecondCenter :=
      ((wz1_lemma23_snapped_cell_geometry prep.graphScale
        prep.graphScale_pos prep.graphScale_one).2.1 second secondRep
        (graphParents.representative_index second hsecond)).1 (1 : Fin 3)
    have hfirstY : |firstRep 1 - y₁| ≤ prep.graphScale / 2 := by
      simpa [y₁, wz1Lemma23SnappedYValue, wz1Lemma23CellCenter, point3]
        using hfirstCenter
    have hsecondY : |secondRep 1 - y₂| ≤ prep.graphScale / 2 := by
      simpa [y₂, wz1Lemma23SnappedYValue, wz1Lemma23CellCenter, point3]
        using hsecondCenter
    have hrepYUpper : |firstRep 1 - secondRep 1| ≤
        d + prep.graphScale := by
      calc
        |firstRep 1 - secondRep 1| =
            |(firstRep 1 - y₁) + (y₁ - y₂) +
              (y₂ - secondRep 1)| := by ring_nf
        _ ≤ |firstRep 1 - y₁| + |y₁ - y₂| +
              |y₂ - secondRep 1| := by
          calc
            _ ≤ |(firstRep 1 - y₁) + (y₁ - y₂)| +
                  |y₂ - secondRep 1| := abs_add_le _ _
            _ ≤ (|firstRep 1 - y₁| + |y₁ - y₂|) +
                  |y₂ - secondRep 1| := by
              gcongr
              exact abs_add_le _ _
        _ ≤ d + prep.graphScale := by
          rw [abs_sub_comm y₂ (secondRep 1)]
          dsimp only [d]
          linarith
    have hfar := graphParents.different_parent_y_far
      first hfirst second hsecond hparent
    have hgraphSmall : prep.graphScale ≤ 14 * root := by
      linarith [prep.graphScale_two_root_bound]
    have hseparation : 497 * root < d := by
      linarith [hfar, hrepYUpper]
    have hfirstPaper := fineWitnesses.witness_mem_parent
      firstParent (graphParents.parent_mem first hfirst)
    have hsecondPaper := fineWitnesses.witness_mem_parent
      secondParent (graphParents.parent_mem second hsecond)
    have hfirstRepPaper := graphParents.representative_mem_parent first hfirst
    have hsecondRepPaper := graphParents.representative_mem_parent second hsecond
    have hfirstAnchorRep : dist firstAnchor firstRep < 2 * root :=
      wz1_paper_grid_cube_diameter_lt_two_rho hroot
        hfirstPaper hfirstRepPaper
    have hsecondRepAnchor : dist secondRep secondAnchor < 2 * root := by
      simpa [secondAnchor, secondRep,
        PureWZ2SourceFixedBinCoarseGraphParentData.anchorFor] using
        (wz1_paper_grid_cube_diameter_lt_two_rho hroot
          hsecondRepPaper hsecondPaper)
    have hy : |firstAnchor 1 - secondAnchor 1| ≤ d + 18 * root := by
      have hfirstCoord := abs_coord_sub_le_dist
        (x := firstAnchor) (y := firstRep) (1 : Fin 3)
      have hsecondCoord := abs_coord_sub_le_dist
        (x := secondRep) (y := secondAnchor) (1 : Fin 3)
      calc
        |firstAnchor 1 - secondAnchor 1| =
            |(firstAnchor 1 - firstRep 1) +
              (firstRep 1 - secondRep 1) +
              (secondRep 1 - secondAnchor 1)| := by ring_nf
        _ ≤ |firstAnchor 1 - firstRep 1| +
              |firstRep 1 - secondRep 1| +
              |secondRep 1 - secondAnchor 1| := by
          calc
            _ ≤ |(firstAnchor 1 - firstRep 1) +
                    (firstRep 1 - secondRep 1)| +
                  |secondRep 1 - secondAnchor 1| := abs_add_le _ _
            _ ≤ _ := by
              gcongr
              exact abs_add_le _ _
        _ ≤ d + 18 * root := by
          linarith [hfirstCoord, hsecondCoord, hfirstAnchorRep,
            hsecondRepAnchor, hrepYUpper, hgraphSmall]
    rw [wz1PaperGridCube_eq_Ico hroot firstParent] at hfirstPaper
    rw [wz1PaperGridCube_eq_Ico hroot secondParent] at hsecondPaper
    have hz : |firstAnchor 2 - secondAnchor 2| ≤ root := by
      change |fineWitnesses.witness firstParent 2 -
        fineWitnesses.witness secondParent 2| ≤ root
      rw [abs_le]
      have hfirstLower := hfirstPaper.2.2.2.2.1
      have hfirstUpper := hfirstPaper.2.2.2.2.2
      have hsecondLower := hsecondPaper.2.2.2.2.1
      have hsecondUpper := hsecondPaper.2.2.2.2.2
      rw [carrier.parent_height_eq firstParent
        (graphParents.parent_mem first hfirst)] at hfirstLower hfirstUpper
      rw [carrier.parent_height_eq secondParent
        (graphParents.parent_mem second hsecond)] at hsecondLower hsecondUpper
      constructor <;> linarith
    have hfirstLine :=
      retained.fixed_line_localizationFixedBin firstAnchor
      (fineWitnesses.witness_mem_retained firstParent
        (graphParents.parent_mem first hfirst))
    have hsecondLine :=
      retained.fixed_line_localizationFixedBin secondAnchor
      (fineWitnesses.witness_mem_retained secondParent
        (graphParents.parent_mem second hsecond))
    have hfirstAxis := shading_union_subset_axisBox
      (fineWitnesses.witness_mem_source firstParent
        (graphParents.parent_mem first hfirst))
    have hsecondAxis := shading_union_subset_axisBox
      (fineWitnesses.witness_mem_source secondParent
        (graphParents.parent_mem second hsecond))
    have hfirstHeight : firstAnchor 2 ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [firstAnchor,
        PureWZ2SourceFixedBinCoarseGraphParentData.anchorFor,
        Kakeya.Streamlined.axisBox, abs_le] using
        hfirstAxis.2.2
    have hsecondHeight : secondAnchor 2 ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [secondAnchor,
        PureWZ2SourceFixedBinCoarseGraphParentData.anchorFor,
        Kakeya.Streamlined.axisBox, abs_le] using
        hsecondAxis.2.2
    have hsecondYBound : |secondAnchor 1| ≤ 1 := by
      simpa [secondAnchor,
        PureWZ2SourceFixedBinCoarseGraphParentData.anchorFor,
        Kakeya.Streamlined.axisBox] using hsecondAxis.2.1
    have hslopeFirst :
        |source.globalGrains.slope (firstAnchor 2)| ≤ 3 :=
      source.globalGrains.slope_bound _ hfirstHeight
    have hslopeDiff :
        |source.globalGrains.slope (firstAnchor 2) -
          source.globalGrains.slope (secondAnchor 2)| ≤ root := by
      have hlip := source.globalGrains.slope_lipschitz.dist_le_mul
        (firstAnchor 2) hfirstHeight (secondAnchor 2) hsecondHeight
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
      exact hlip.trans hz
    have hprojection :
        |(firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) *
            firstAnchor 1) -
          (secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) *
            secondAnchor 1)| ≤ 28 * root := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ] at hfirstLine hsecondLine
      have htriangle := abs_sub
        ((firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) *
          firstAnchor 1) - line.lineLevel)
        ((secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) *
          secondAnchor 1) - line.lineLevel)
      have hrearrange :
          ((firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) *
              firstAnchor 1) - line.lineLevel) -
            ((secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) *
              secondAnchor 1) - line.lineLevel) =
          (firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) *
              firstAnchor 1) -
            (secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) *
              secondAnchor 1) := by ring
      rw [hrearrange] at htriangle
      exact htriangle.trans (by linarith [hfirstLine, hsecondLine])
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
                source.globalGrains.slope (secondAnchor 2)) *
                secondAnchor 1 := by ring
      rw [hrearrange]
      calc
        _ ≤ |source.globalGrains.slope (firstAnchor 2)| *
              |firstAnchor 1 - secondAnchor 1| +
            |source.globalGrains.slope (firstAnchor 2) -
              source.globalGrains.slope (secondAnchor 2)| *
              |secondAnchor 1| := by
          simpa [abs_mul] using abs_add_le
            (source.globalGrains.slope (firstAnchor 2) *
              (firstAnchor 1 - secondAnchor 1))
            ((source.globalGrains.slope (firstAnchor 2) -
                source.globalGrains.slope (secondAnchor 2)) * secondAnchor 1)
        _ ≤ 3 * |firstAnchor 1 - secondAnchor 1| + root := by
          have hyNonneg := abs_nonneg (firstAnchor 1 - secondAnchor 1)
          nlinarith [mul_le_mul_of_nonneg_right hslopeFirst hyNonneg,
            mul_le_mul hslopeDiff hsecondYBound (abs_nonneg _) (by positivity)]
    have hx : |firstAnchor 0 - secondAnchor 0| ≤ 3 * d + 83 * root := by
      have hsolve := abs_sub
        ((firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) *
          firstAnchor 1) -
          (secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) *
            secondAnchor 1))
        (source.globalGrains.slope (firstAnchor 2) * firstAnchor 1 -
          source.globalGrains.slope (secondAnchor 2) * secondAnchor 1)
      have hrearrange :
          ((firstAnchor 0 + source.globalGrains.slope (firstAnchor 2) *
              firstAnchor 1) -
            (secondAnchor 0 + source.globalGrains.slope (secondAnchor 2) *
              secondAnchor 1)) -
            (source.globalGrains.slope (firstAnchor 2) * firstAnchor 1 -
              source.globalGrains.slope (secondAnchor 2) * secondAnchor 1) =
          firstAnchor 0 - secondAnchor 0 := by ring
      rw [hrearrange] at hsolve
      linarith [hprojection, hslopeProduct, hy]
    have hx' : |firstAnchor 0 - secondAnchor 0| ≤ 13 * d / 4 := by
      linarith [hx, hseparation]
    have hy' : |firstAnchor 1 - secondAnchor 1| ≤ 21 * d / 20 := by
      linarith [hy, hseparation]
    have hz' : |firstAnchor 2 - secondAnchor 2| ≤ d / 400 := by
      linarith [hz, hseparation]
    have hxSq : (firstAnchor 0 - secondAnchor 0) ^ 2 ≤
        (13 * d / 4) ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg (by positivity : 0 ≤ 13 * d / 4)] using hx'
    have hySq : (firstAnchor 1 - secondAnchor 1) ^ 2 ≤
        (21 * d / 20) ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg (by positivity : 0 ≤ 21 * d / 20)] using hy'
    have hzSq : (firstAnchor 2 - secondAnchor 2) ^ 2 ≤
        (d / 400) ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg (by positivity : 0 ≤ d / 400)] using hz'
    have hcoeff :
        (13 * d / 4) ^ 2 + (21 * d / 20) ^ 2 + (d / 400) ^ 2 ≤
          (4 * d) ^ 2 := by nlinarith [sq_nonneg d]
    have hdistSq : dist firstAnchor secondAnchor ^ 2 ≤ (4 * d) ^ 2 := by
      rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three]
      simpa [Real.dist_eq, sq_abs] using
        (add_le_add (add_le_add hxSq hySq) hzSq).trans hcoeff
    simpa [firstAnchor, secondAnchor, y₁, y₂, d] using
      (sq_le_sq₀ dist_nonneg (by positivity : 0 ≤ 4 * d)).mp hdistSq

/-- Backwards-compatible maximal-bin name for `anchorFor_dist`. -/
lemma PureWZ2SourceFixedLineCoarseGraphParentData.anchorFor_dist
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {original : PureWZ2SourceFixedLineCoarseOriginalSlopeData
      carriers.coarseCarrier carriers.fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedLineCoarsePreparationData original}
    (graphParents : PureWZ2SourceFixedLineCoarseGraphParentData prep)
    (first : ℤ × ℤ × ℤ)
    (hfirst : first ∈ prep.windowed.global.cells)
    (second : ℤ × ℤ × ℤ)
    (hsecond : second ∈ prep.windowed.global.cells) :
    dist (graphParents.anchorFor first hfirst)
        (graphParents.anchorFor second hsecond) ≤
      4 * |wz1Lemma23SnappedYValue prep.graphScale first.2.1 -
        wz1Lemma23SnappedYValue prep.graphScale second.2.1| := by
  exact PureWZ2SourceFixedBinCoarseGraphParentData.anchorFor_dist
    graphParents first hfirst second hsecond

end Kakeya.Assouad

end
