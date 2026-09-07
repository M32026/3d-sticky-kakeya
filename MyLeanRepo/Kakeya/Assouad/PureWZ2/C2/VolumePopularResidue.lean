import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HeightVolumePopularity
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23YResiduePackage
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ExactSliceCells

/-!
# A y-residue inside genuinely source-volume-popular heights

The graph cells are first restricted to heights selected by actual union
volume.  Only then is one separated y-residue chosen.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

structure PureWZ2VolumePopularResidueData
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambient : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    (global : WZ1Lemma23GlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) ambient C)
    (popular : PureWZ2HeightVolumePopularData ambient rho) where
  popularCells : Finset (ℤ × ℤ × ℤ) :=
    global.cells.filter fun cell => cell.2.2 ∈ popular.heightIndices
  popularCells_eq : popularCells =
    global.cells.filter fun cell => cell.2.2 ∈ popular.heightIndices
  popularCells_nonempty : popularCells.Nonempty
  residue : WZ1Lemma23YResiduePackage global
  cells_eq : residue.cells =
    wz1Lemma23YResidueCells rho popularCells residue.residue
  cells_nonempty : residue.cells.Nonempty
  cells_popular_height :
    ∀ cell ∈ residue.cells, cell.2.2 ∈ popular.heightIndices
  extraCost_eq : residue.extraCost = 2 * popular.bins
  volumeCost_eq : residue.volumeCost =
    wz1Lemma23YStride rho * residue.extraCost

theorem PureWZ2HeightVolumePopularData.toVolumePopularResidue
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambient : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    (global : WZ1Lemma23GlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) ambient C)
    (popular : PureWZ2HeightVolumePopularData ambient rho)
    (hrhoOne : rho ≤ 1)
    (hball : ambient.union ⊆ Metric.closedBall (0 : Point3) 2) :
    Nonempty (PureWZ2VolumePopularResidueData global popular) := by
  let popularCells := global.cells.filter fun cell =>
    cell.2.2 ∈ popular.heightIndices
  have hpopularSubset : popularCells ⊆ global.cells :=
    Finset.filter_subset _ _
  have hheightGlobal : popular.heightIndices ⊆ global.heightIndices := by
    rw [global.heightIndices_eq]
    exact popular.heightIndices_subset
  have hpopularCellsEq : popularCells =
      popular.heightIndices.biUnion global.layerCells := by
    ext cell
    constructor
    · intro hcell
      have hdata := Finset.mem_filter.mp hcell
      rw [global.cells_eq] at hdata
      rcases Finset.mem_biUnion.mp hdata.1 with
        ⟨heightIndex, hheightIndex, hcellLayer⟩
      have hheight := global.layer_height
        heightIndex hheightIndex cell hcellLayer
      exact Finset.mem_biUnion.mpr
        ⟨cell.2.2, hdata.2, by simpa [hheight] using hcellLayer⟩
    · intro hcell
      rcases Finset.mem_biUnion.mp hcell with
        ⟨heightIndex, hheightPopular, hcellLayer⟩
      have hheightIndex := hheightGlobal hheightPopular
      apply Finset.mem_filter.mpr
      constructor
      · rw [global.cells_eq]
        exact Finset.mem_biUnion.mpr
          ⟨heightIndex, hheightIndex, hcellLayer⟩
      · simpa [global.layer_height heightIndex hheightIndex cell hcellLayer]
          using hheightPopular
  have hlayersDisjoint :
      ∀ first ∈ popular.heightIndices,
        ∀ second ∈ popular.heightIndices, first ≠ second →
          Disjoint (global.layerCells first) (global.layerCells second) := by
    intro first hfirst second hsecond hne
    rw [Finset.disjoint_left]
    intro cell hcellFirst hcellSecond
    have hfirstHeight := global.layer_height first
      (hheightGlobal hfirst) cell hcellFirst
    have hsecondHeight := global.layer_height second
      (hheightGlobal hsecond) cell hcellSecond
    exact hne (hfirstHeight.symm.trans hsecondHeight)
  have hsumLayerCards :
      (∑ heightIndex ∈ popular.heightIndices,
          (global.layerCells heightIndex).card) = popularCells.card := by
    rw [← Finset.card_biUnion hlayersDisjoint, ← hpopularCellsEq]
  have hsidePos : 0 < ENNReal.ofReal (gridSide (rho / 2)) := by
    apply ENNReal.ofReal_pos.mpr
    dsimp [gridSide]
    exact div_pos (by nlinarith [global.rho_pos])
      (Real.sqrt_pos.mpr (by norm_num))
  have hsideTop : ENNReal.ofReal (gridSide (rho / 2)) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  let disk : ENNReal := ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi
  have hlayerVolume : ∀ heightIndex ∈ popular.heightIndices,
      volume (ambient.union ∩ wz1Lemma23HeightSlab rho heightIndex) ≤
        ((global.layerCells heightIndex).card : ENNReal) *
          ENNReal.ofReal (gridSide (rho / 2)) * disk := by
    intro heightIndex hheightPopular
    have hheightGlobal := hheightGlobal hheightPopular
    have hslice := wz1_lemma23_exactSlice_area_le_two
      ambient global.rho_pos hball (global.selectedHeight heightIndex)
    have hslice' :
        volume (wz1Lemma23PlanarSlice ambient.union
            (global.selectedHeight heightIndex)) ≤
          ((global.layerCells heightIndex).card : ENNReal) * disk := by
      simpa [global.layerCells_eq, disk] using hslice
    have hdiv := (global.layer_volume_bound
      heightIndex hheightGlobal).trans hslice'
    have hmul := (ENNReal.div_le_iff hsidePos.ne' hsideTop).mp hdiv
    calc
      volume (ambient.union ∩ wz1Lemma23HeightSlab rho heightIndex) ≤
          (((global.layerCells heightIndex).card : ENNReal) * disk) *
            ENNReal.ofReal (gridSide (rho / 2)) := hmul
      _ = ((global.layerCells heightIndex).card : ENNReal) *
          ENNReal.ofReal (gridSide (rho / 2)) * disk := by ring
  have hpopularVolume : volume popular.shading.union ≤
      (popularCells.card : ENNReal) *
        ENNReal.ofReal (gridSide (rho / 2)) * disk := by
    rw [popular.volume_eq_sum]
    calc
      (∑ heightIndex ∈ popular.heightIndices,
          volume (ambient.union ∩ wz1Lemma23HeightSlab rho heightIndex)) ≤
          ∑ heightIndex ∈ popular.heightIndices,
            (((global.layerCells heightIndex).card : ENNReal) *
              ENNReal.ofReal (gridSide (rho / 2)) * disk) := by
        exact Finset.sum_le_sum fun heightIndex hheight =>
          hlayerVolume heightIndex hheight
      _ = (popularCells.card : ENNReal) *
          ENNReal.ofReal (gridSide (rho / 2)) * disk := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, hsumLayerCards]
  have hpopularCellsNonempty : popularCells.Nonempty := by
    rcases popular.heightIndices_nonempty with ⟨heightIndex, hheightIndex⟩
    have hlayerPos : 0 < volume
        (ambient.union ∩ wz1Lemma23HeightSlab rho heightIndex) :=
      popular.layerMass_pos.trans_le
        (popular.layer_volume_band heightIndex hheightIndex).1
    have hlayerUpper := hlayerVolume heightIndex hheightIndex
    have hcardPos : 0 < (global.layerCells heightIndex).card := by
      by_contra hzero
      have hcardZero : (global.layerCells heightIndex).card = 0 :=
        Nat.eq_zero_of_not_pos hzero
      rw [hcardZero] at hlayerUpper
      have hlayerZero : volume
          (ambient.union ∩ wz1Lemma23HeightSlab rho heightIndex) = 0 := by
        simpa using hlayerUpper
      exact (ne_of_gt hlayerPos) hlayerZero
    rcases Finset.card_pos.mp hcardPos with ⟨cell, hcell⟩
    rw [hpopularCellsEq]
    exact ⟨cell, Finset.mem_biUnion.mpr
      ⟨heightIndex, hheightIndex, hcell⟩⟩
  rcases wz1_lemma23_y_layer_selection rho global.rho_pos hrhoOne with
    ⟨hstridePos, hstrideBound, hselection⟩
  rcases hselection popularCells (fun _ => 1) with
    ⟨selectedResidue, hcardRetained, hselectedSubset,
      hresidueCondition, hySeparated⟩
  let cells := wz1Lemma23YResidueCells rho popularCells selectedResidue
  have hselectedNonempty : cells.Nonempty := by
    apply Finset.card_pos.mp
    by_contra hzero
    have hcellsZero : cells.card = 0 := Nat.eq_zero_of_not_pos hzero
    have hpopularCard := hpopularCellsNonempty.card_pos
    have hpopularCardLe : popularCells.card ≤
        wz1Lemma23YStride rho * cells.card := by
      simpa [cells] using hcardRetained
    rw [hcellsZero, Nat.mul_zero] at hpopularCardLe
    omega
  have hcellsGlobal : cells ⊆ global.cells :=
    hselectedSubset.trans hpopularSubset
  have hcellsActive : cells ⊆
      wz1Lemma23ActiveCells ambient rho global.rho_pos :=
    hcellsGlobal.trans global.cells_active
  have hcellsPopular : ∀ cell ∈ cells,
      cell.2.2 ∈ popular.heightIndices := by
    intro cell hcell
    exact (Finset.mem_filter.mp (hselectedSubset hcell)).2
  have hglobalBins : ∀ heightIndex ∈ wz1Lemma23SnappedHeights cells,
      (wz1Lemma23SnappedGlobalBinsAt rho global.extendedSlope
        cells heightIndex).card ≤ global.globalBinBound := by
    intro heightIndex hheight
    have hheightGlobal := wz1Lemma23_snappedHeights_mono
      hcellsGlobal hheight
    exact (Finset.card_le_card
      (wz1Lemma23_snappedGlobalBinsAt_mono rho global.extendedSlope
        heightIndex hcellsGlobal)).trans
      (global.global_bins heightIndex hheightGlobal)
  let extraCost := 2 * popular.bins
  have hbinsPos : 0 < popular.bins := by rw [popular.bins_eq]; omega
  have hextraPos : 0 < extraCost := Nat.mul_pos (by omega) hbinsPos
  let volumeCost := wz1Lemma23YStride rho * extraCost
  have hvolumeCostPos : 0 < volumeCost :=
    Nat.mul_pos hstridePos hextraPos
  have hambientVolume : volume ambient.union ≤
      ((volumeCost * cells.card : ℕ) : ENNReal) *
        ENNReal.ofReal (gridSide (rho / 2)) * disk := by
    have hretained :=
      (ENNReal.div_le_iff (by norm_num) (by norm_num)).mp
        popular.retained_volume
    have hcardCast : (popularCells.card : ENNReal) ≤
        (wz1Lemma23YStride rho : ENNReal) * (cells.card : ENNReal) := by
      have hcardNat : popularCells.card ≤
          wz1Lemma23YStride rho * cells.card := by
        simpa [cells] using hcardRetained
      exact_mod_cast hcardNat
    calc
      volume ambient.union ≤
          (popular.bins : ENNReal) * volume popular.shading.union * 2 := by
        simpa using hretained
      _ ≤ (popular.bins : ENNReal) *
          ((popularCells.card : ENNReal) *
            ENNReal.ofReal (gridSide (rho / 2)) * disk) * 2 := by gcongr
      _ ≤ (popular.bins : ENNReal) *
          (((wz1Lemma23YStride rho : ENNReal) * (cells.card : ENNReal)) *
            ENNReal.ofReal (gridSide (rho / 2)) * disk) * 2 := by gcongr
      _ = ((volumeCost * cells.card : ℕ) : ENNReal) *
          ENNReal.ofReal (gridSide (rho / 2)) * disk := by
        simp only [volumeCost, extraCost, Nat.cast_mul]
        ring
  let cardCost := global.cells.card
  have hcardCostPos : 0 < cardCost :=
    hpopularCellsNonempty.mono hpopularSubset |>.card_pos
  have hcardLoss : global.cells.card ≤ cardCost * cells.card := by
    dsimp only [cardCost]
    have hcellsCard : 1 ≤ cells.card := hselectedNonempty.card_pos
    nlinarith
  let package : WZ1Lemma23YResiduePackage global :=
    { stride_pos := hstridePos
      stride_bound := hstrideBound
      residue := selectedResidue
      cells := cells
      cells_eq := by
        intro cell hcell
        exact Finset.mem_filter.mpr
          ⟨hpopularSubset (hselectedSubset hcell), hresidueCondition cell hcell⟩
      cells_subset := hcellsGlobal
      cells_active := hcellsActive
      cardCost := cardCost
      cardCost_pos := hcardCostPos
      extraCost := extraCost
      extraCost_pos := hextraPos
      card_loss := hcardLoss
      volumeCost := volumeCost
      volumeCost_pos := hvolumeCostPos
      volumeCost_bound := le_rfl
      volume_cell_bound := by simpa [disk] using hambientVolume
      residue_condition := hresidueCondition
      y_separated := hySeparated
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
  exact ⟨{
    popularCells := popularCells
    popularCells_eq := rfl
    popularCells_nonempty := hpopularCellsNonempty
    residue := package
    cells_eq := rfl
    cells_nonempty := hselectedNonempty
    cells_popular_height := hcellsPopular
    extraCost_eq := rfl
    volumeCost_eq := rfl
  }⟩

end Kakeya.Assouad
