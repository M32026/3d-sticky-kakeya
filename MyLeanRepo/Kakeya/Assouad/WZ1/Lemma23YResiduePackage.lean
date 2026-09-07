import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GlobalSlicePackage
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23YLayerSelection

/-!
# Separated y-residue package for the actual WZ1 Lemma 23 cells

The global-slice package contains the genuine exact-slice cells, but it still
uses every fine y-layer.  This module applies the closed weighted residue
selection to those actual cells with unit weight.  It records the resulting
cell-count loss, `sqrt rho` y-separation, inherited active-cell support, and
the inherited per-height global-bin bound.

No auxiliary incidence graph is introduced.  The selected cells are a literal
filtered subset of `WZ1Lemma23GlobalSlicePackage.cells`.
-/

namespace Kakeya.Assouad

noncomputable section

open MeasureTheory

/-- Occupied snapped y-layers are monotone under restriction of the cells. -/
lemma wz1Lemma23_snappedYLayers_mono
    {selected cells : Finset (ℤ × ℤ × ℤ)}
    (hselected : selected ⊆ cells) :
    wz1Lemma23SnappedYLayers selected ⊆
      wz1Lemma23SnappedYLayers cells := by
  exact Finset.image_mono (fun idx => idx.2.1) hselected

/-- Occupied snapped heights are monotone under restriction of the cells. -/
lemma wz1Lemma23_snappedHeights_mono
    {selected cells : Finset (ℤ × ℤ × ℤ)}
    (hselected : selected ⊆ cells) :
    wz1Lemma23SnappedHeights selected ⊆
      wz1Lemma23SnappedHeights cells := by
  exact Finset.image_mono (fun idx => idx.2.2) hselected

/-- Local scalar-bin sets are monotone under restriction of the cells. -/
lemma wz1Lemma23_snappedLocalBinsAt_mono
    (rho : ℝ) (g : ℝ → ℝ) (y : ℤ)
    {selected cells : Finset (ℤ × ℤ × ℤ)}
    (hselected : selected ⊆ cells) :
    wz1Lemma23SnappedLocalBinsAt rho g selected y ⊆
      wz1Lemma23SnappedLocalBinsAt rho g cells y := by
  exact
    Finset.image_mono
      (fun idx =>
        Int.floor
          (wz1Lemma23LocalCoordinate g
            (wz1Lemma23SnappedPoint rho idx) / rho))
      (Finset.filter_subset_filter _ hselected)

/-- Global scalar-bin sets are monotone under restriction of the cells. -/
lemma wz1Lemma23_snappedGlobalBinsAt_mono
    (rho : ℝ) (f : ℝ → ℝ) (z : ℤ)
    {selected cells : Finset (ℤ × ℤ × ℤ)}
    (hselected : selected ⊆ cells) :
    wz1Lemma23SnappedGlobalBinsAt rho f selected z ⊆
      wz1Lemma23SnappedGlobalBinsAt rho f cells z := by
  exact
    Finset.image_mono
      (fun idx => wz1Lemma23SnappedGlobalBin rho f idx)
      (Finset.filter_subset_filter _ hselected)

/--
The actual global-slice cells after retaining one fine-y residue class.
-/
structure WZ1Lemma23YResiduePackage
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (globalPackage :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C) where
  stride_pos : 0 < wz1Lemma23YStride rho
  stride_bound :
    (wz1Lemma23YStride rho : ℝ) ≤
      2 * Real.sqrt 3 / Real.sqrt rho
  residue : Fin (wz1Lemma23YStride rho)
  cells : Finset (ℤ × ℤ × ℤ)
  cells_eq :
    cells ⊆
      wz1Lemma23YResidueCells
        rho globalPackage.cells residue
  cells_subset : cells ⊆ globalPackage.cells
  cells_active :
    cells ⊆
      wz1Lemma23ActiveCells
        Y rho globalPackage.rho_pos
  cardCost : ℕ
  cardCost_pos : 0 < cardCost
  extraCost : ℕ
  extraCost_pos : 0 < extraCost
  card_loss :
    globalPackage.cells.card ≤
      cardCost * cells.card
  volumeCost : ℕ
  volumeCost_pos : 0 < volumeCost
  volumeCost_bound :
    volumeCost ≤ wz1Lemma23YStride rho * extraCost
  volume_cell_bound :
    volume Y.union ≤
      (((volumeCost * cells.card : ℕ) : ENNReal) *
        ENNReal.ofReal (gridSide (rho / 2))) *
        (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi)
  residue_condition :
    ∀ idx ∈ cells,
      idx.2.1 % (wz1Lemma23YStride rho : ℤ) =
        ((residue : ℕ) : ℤ)
  y_separated :
    ∀ first ∈ cells, ∀ second ∈ cells,
      first.2.1 = second.2.1 ∨
        Real.sqrt rho ≤
          |(wz1Lemma23CellCenter rho first) 1 -
            (wz1Lemma23CellCenter rho second) 1|
  global_bins :
    ∀ heightIndex ∈ wz1Lemma23SnappedHeights cells,
      (wz1Lemma23SnappedGlobalBinsAt
        rho globalPackage.extendedSlope cells heightIndex).card ≤
          globalPackage.globalBinBound
  heightFiberCost : ℕ
  heightFiberCost_pos : 0 < heightFiberCost
  height_uniform :
    ∀ first ∈ wz1Lemma23SnappedHeights cells,
      ∀ second ∈ wz1Lemma23SnappedHeights cells,
        (cells.filter fun cell => cell.2.2 = first).card ≤
          heightFiberCost *
            (cells.filter fun cell => cell.2.2 = second).card

/--
Apply the actual y-residue selection to a global-slice package.
-/
theorem wz1_lemma23_y_residue_package
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (globalPackage :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (hrho_one : rho ≤ 1) :
    ∃ package : WZ1Lemma23YResiduePackage globalPackage,
      package.cells =
        wz1Lemma23YResidueCells
          rho globalPackage.cells package.residue ∧
        package.extraCost = 1 := by
  rcases
      wz1_lemma23_y_layer_selection
        rho globalPackage.rho_pos hrho_one with
    ⟨hstridePos, hstrideBound, hselection⟩
  rcases
      hselection globalPackage.cells (fun _ => 1) with
    ⟨residue, hweight, hsubset, hresidue, hseparated⟩
  let cells :=
    wz1Lemma23YResidueCells
      rho globalPackage.cells residue
  have hcard :
      globalPackage.cells.card ≤
        wz1Lemma23YStride rho * cells.card := by
    simpa [cells] using hweight
  have hactive :
      cells ⊆
        wz1Lemma23ActiveCells
          Y rho globalPackage.rho_pos :=
    hsubset.trans globalPackage.cells_active
  have hvolume :
      volume Y.union ≤
        (((wz1Lemma23YStride rho * cells.card : ℕ) : ENNReal) *
          ENNReal.ofReal (gridSide (rho / 2))) *
          (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi) := by
    apply globalPackage.volume_cell_bound.trans
    gcongr
  have hglobalBins :
      ∀ heightIndex ∈ wz1Lemma23SnappedHeights cells,
        (wz1Lemma23SnappedGlobalBinsAt
          rho globalPackage.extendedSlope cells heightIndex).card ≤
            globalPackage.globalBinBound := by
    intro heightIndex hheight
    have hheightGlobal :
        heightIndex ∈
          wz1Lemma23SnappedHeights globalPackage.cells :=
      wz1Lemma23_snappedHeights_mono hsubset hheight
    exact
      (Finset.card_le_card
          (wz1Lemma23_snappedGlobalBinsAt_mono
            rho globalPackage.extendedSlope heightIndex hsubset)).trans
        (globalPackage.global_bins
          heightIndex hheightGlobal)
  let package : WZ1Lemma23YResiduePackage globalPackage :=
    { stride_pos := hstridePos
      stride_bound := hstrideBound
      residue := residue
      cells := cells
      cells_eq := by intro cell hcell; exact hcell
      cells_subset := hsubset
      cells_active := hactive
      cardCost := wz1Lemma23YStride rho
      cardCost_pos := hstridePos
      extraCost := 1
      extraCost_pos := by omega
      card_loss := hcard
      volumeCost := wz1Lemma23YStride rho
      volumeCost_pos := hstridePos
      volumeCost_bound := by simp
      volume_cell_bound := hvolume
      residue_condition := hresidue
      y_separated := hseparated
      global_bins := hglobalBins
      heightFiberCost := cells.card + 1
      heightFiberCost_pos := by omega
      height_uniform := by
        intro first hfirst second hsecond
        have hfirstCard :
            (cells.filter fun cell => cell.2.2 = first).card ≤ cells.card :=
          Finset.card_filter_le _ _
        have hsecondNonempty :
            (cells.filter fun cell => cell.2.2 = second).Nonempty := by
          rcases Finset.mem_image.mp hsecond with ⟨cell, hcell, hheight⟩
          exact ⟨cell, Finset.mem_filter.mpr ⟨hcell, hheight⟩⟩
        have hsecondPos :
            1 ≤ (cells.filter fun cell => cell.2.2 = second).card :=
          hsecondNonempty.card_pos
        calc
          (cells.filter fun cell => cell.2.2 = first).card ≤ cells.card :=
            hfirstCard
          _ ≤ (cells.card + 1) *
              (cells.filter fun cell => cell.2.2 = second).card := by
            nlinarith }
  exact ⟨package, rfl, rfl⟩

end

end Kakeya.Assouad
