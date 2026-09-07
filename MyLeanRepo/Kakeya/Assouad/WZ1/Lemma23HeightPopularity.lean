import MyLeanRepo.Kakeya.Assouad.MultiscaleUniformRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23YResiduePackage

/-!
# Dyadic popularity of actual Lemma-23 height layers
-/

namespace Kakeya.Assouad

noncomputable section

open Finset MeasureTheory

attribute [local instance] Classical.propDecidable

def wz1Lemma23HeightFiber
    (cells : Finset (ℤ × ℤ × ℤ)) (height : ℤ) :
    Finset (ℤ × ℤ × ℤ) :=
  cells.filter fun cell => cell.2.2 = height

lemma finset_selected_fibers_card_lower
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (source : Finset α) (label : α → β)
    (selectedLabels : Finset β)
    (hselected : selectedLabels ⊆ source.image label)
    (C : ℕ)
    (huniform :
      ∀ first ∈ source.image label, ∀ second ∈ source.image label,
        (source.filter fun item => label item = first).card ≤
          C * (source.filter fun item => label item = second).card) :
    selectedLabels.card * source.card ≤
      C * (source.image label).card *
        (source.filter fun item => label item ∈ selectedLabels).card := by
  classical
  by_cases hselectedEmpty : selectedLabels = ∅
  · simp [hselectedEmpty]
  have hselectedNonempty : selectedLabels.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hselectedEmpty
  obtain ⟨base, hbase, hbaseMin⟩ :=
    Finset.exists_min_image selectedLabels
      (fun value => (source.filter fun item => label item = value).card)
      hselectedNonempty
  have hbaseSource : base ∈ source.image label := hselected hbase
  let fiber := fun value : β => source.filter fun item => label item = value
  have hsourceSum :
      source.card = ∑ value ∈ source.image label, (fiber value).card := by
    have hmaps : Set.MapsTo label source (source.image label) :=
      fun item hitem => Finset.mem_image.mpr ⟨item, hitem, rfl⟩
    simpa [fiber] using Finset.card_eq_sum_card_fiberwise (H := hmaps)
  have hselectedSum :
      (source.filter fun item => label item ∈ selectedLabels).card =
        ∑ value ∈ selectedLabels, (fiber value).card := by
    simpa [fiber] using
      (Finset.sum_card_fiberwise_eq_card_filter source selectedLabels label).symm
  have hsourceBase :
      source.card ≤ (source.image label).card * (C * (fiber base).card) := by
    rw [hsourceSum]
    calc
      (∑ value ∈ source.image label, (fiber value).card) ≤
          ∑ _value ∈ source.image label, C * (fiber base).card := by
        exact Finset.sum_le_sum fun value hvalue =>
          huniform value hvalue base hbaseSource
      _ = (source.image label).card * (C * (fiber base).card) := by
        simp [Finset.sum_const]
  have hselectedBase :
      selectedLabels.card * (fiber base).card ≤
        (source.filter fun item => label item ∈ selectedLabels).card := by
    rw [hselectedSum]
    calc
      selectedLabels.card * (fiber base).card =
          ∑ _value ∈ selectedLabels, (fiber base).card := by
        simp [Finset.sum_const]
      _ ≤ ∑ value ∈ selectedLabels, (fiber value).card := by
        exact Finset.sum_le_sum fun value hvalue => hbaseMin value hvalue
  calc
    selectedLabels.card * source.card ≤
        selectedLabels.card *
          ((source.image label).card * (C * (fiber base).card)) :=
      Nat.mul_le_mul_left _ hsourceBase
    _ = C * (source.image label).card *
        (selectedLabels.card * (fiber base).card) := by ring
    _ ≤ C * (source.image label).card *
        (source.filter fun item => label item ∈ selectedLabels).card := by
      gcongr

structure WZ1Lemma23HeightPopularResidueData
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {globalPackage :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C}
    (source : WZ1Lemma23YResiduePackage globalPackage) where
  logarithmicCost : ℕ := Nat.log 2 source.cells.card + 1
  logarithmicCost_eq :
    logarithmicCost = Nat.log 2 source.cells.card + 1
  residue : WZ1Lemma23YResiduePackage globalPackage
  cells_subset : residue.cells ⊆ source.cells
  cells_nonempty : residue.cells.Nonempty
  card_retention :
    source.cells.card ≤ logarithmicCost * residue.cells.card
  cardCost_eq : residue.cardCost = source.cardCost * logarithmicCost
  extraCost_eq : residue.extraCost = source.extraCost * logarithmicCost
  volumeCost_eq :
    residue.volumeCost = source.volumeCost * logarithmicCost
  heightFiberCost_eq : residue.heightFiberCost = 2
  height_uniform :
    ∀ first ∈ wz1Lemma23SnappedHeights residue.cells,
      ∀ second ∈ wz1Lemma23SnappedHeights residue.cells,
        (wz1Lemma23HeightFiber residue.cells first).card ≤
          2 * (wz1Lemma23HeightFiber residue.cells second).card

theorem WZ1Lemma23YResiduePackage.regularizeHeights
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {globalPackage :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C}
    (source : WZ1Lemma23YResiduePackage globalPackage)
    (hsource : source.cells.Nonempty) :
    Nonempty (WZ1Lemma23HeightPopularResidueData source) := by
  let heights := wz1Lemma23SnappedHeights source.cells
  let fiber : ℤ → Finset (ℤ × ℤ × ℤ) :=
    wz1Lemma23HeightFiber source.cells
  let partition : Finset (Finset (ℤ × ℤ × ℤ)) := heights.image fiber
  have hfiberSub : ∀ height, fiber height ⊆ source.cells := by
    intro height
    exact Finset.filter_subset _ _
  have hpartitionDisjoint :
      ∀ first ∈ partition, ∀ second ∈ partition, first ≠ second →
        Disjoint first second := by
    intro first hfirst second hsecond hne
    rcases Finset.mem_image.mp hfirst with
      ⟨firstHeight, _hfirstHeight, rfl⟩
    rcases Finset.mem_image.mp hsecond with
      ⟨secondHeight, _hsecondHeight, rfl⟩
    have hheightNe : firstHeight ≠ secondHeight := by
      intro heq
      exact hne (congrArg fiber heq)
    rw [Finset.disjoint_left]
    intro cell hcellFirst hcellSecond
    have hfirstEq := (Finset.mem_filter.mp hcellFirst).2
    have hsecondEq := (Finset.mem_filter.mp hcellSecond).2
    exact hheightNe (hfirstEq.symm.trans hsecondEq)
  have hcover : source.cells ⊆ Finset.biUnion partition id := by
    intro cell hcell
    let height := cell.2.2
    have hheight : height ∈ heights :=
      Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
    have hfiberMem : fiber height ∈ partition :=
      Finset.mem_image.mpr ⟨height, hheight, rfl⟩
    exact Finset.mem_biUnion.mpr
      ⟨fiber height, hfiberMem, Finset.mem_filter.mpr ⟨hcell, rfl⟩⟩
  rcases dyadic_uniformity_single_level source.cells hsource partition
      hpartitionDisjoint hcover with
    ⟨selected, kept, hkept, hselectedEq, hselectedNonempty,
      huniform, hretentionReal⟩
  have hselectedSub : selected ⊆ source.cells := by
    rw [hselectedEq]
    intro cell hcell
    rcases Finset.mem_biUnion.mp hcell with ⟨piece, hpiece, hcellPiece⟩
    exact (Finset.mem_inter.mp hcellPiece).1
  let logarithmicCost := Nat.log 2 source.cells.card + 1
  have hlogPos : 0 < logarithmicCost := by
    dsimp only [logarithmicCost]
    omega
  have hretention :
      source.cells.card ≤ logarithmicCost * selected.card := by
    have hlogReal : 0 < (logarithmicCost : ℝ) := by exact_mod_cast hlogPos
    have hmul :
        (source.cells.card : ℝ) ≤
          (logarithmicCost : ℝ) * (selected.card : ℝ) := by
      have hdiv :
          (source.cells.card : ℝ) / logarithmicCost ≤ selected.card := by
        simpa [logarithmicCost] using hretentionReal
      have hraw := (div_le_iff₀ hlogReal).mp hdiv
      nlinarith
    exact_mod_cast hmul
  let newCost := source.cardCost * logarithmicCost
  let newVolumeCost := source.volumeCost * logarithmicCost
  let newExtraCost := source.extraCost * logarithmicCost
  have hnewCostPos : 0 < newCost :=
    Nat.mul_pos source.cardCost_pos hlogPos
  have hnewExtraCostPos : 0 < newExtraCost :=
    Nat.mul_pos source.extraCost_pos hlogPos
  have hnewVolumeCostPos : 0 < newVolumeCost :=
    Nat.mul_pos source.volumeCost_pos hlogPos
  have hnewVolumeCostBound :
      newVolumeCost ≤ wz1Lemma23YStride rho * newExtraCost := by
    dsimp only [newVolumeCost, newExtraCost]
    calc
      source.volumeCost * logarithmicCost ≤
          (wz1Lemma23YStride rho * source.extraCost) * logarithmicCost :=
        Nat.mul_le_mul_right logarithmicCost source.volumeCost_bound
      _ = wz1Lemma23YStride rho *
          (source.extraCost * logarithmicCost) := by ring
  have hglobalCard :
      globalPackage.cells.card ≤ newCost * selected.card := by
    calc
      globalPackage.cells.card ≤ source.cardCost * source.cells.card :=
        source.card_loss
      _ ≤ source.cardCost * (logarithmicCost * selected.card) :=
        Nat.mul_le_mul_left _ hretention
      _ = newCost * selected.card := by
        dsimp only [newCost]
        ring
  have hvolume :
      volume Y.union ≤
        (((newVolumeCost * selected.card : ℕ) : ENNReal) *
          ENNReal.ofReal (gridSide (rho / 2))) *
          (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi) := by
    calc
      volume Y.union ≤
          (((source.volumeCost * source.cells.card : ℕ) : ENNReal) *
            ENNReal.ofReal (gridSide (rho / 2))) *
            (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi) :=
        source.volume_cell_bound
      _ ≤ (((newVolumeCost * selected.card : ℕ) : ENNReal) *
            ENNReal.ofReal (gridSide (rho / 2))) *
            (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi) := by
        have hcountCost :
            source.volumeCost * source.cells.card ≤
              newVolumeCost * selected.card := by
          dsimp only [newVolumeCost]
          calc
            source.volumeCost * source.cells.card ≤
                source.volumeCost * (logarithmicCost * selected.card) :=
              Nat.mul_le_mul_left _ hretention
            _ = (source.volumeCost * logarithmicCost) * selected.card := by ring
        have hcast :
            ((source.volumeCost * source.cells.card : ℕ) : ENNReal) ≤
              ((newVolumeCost * selected.card : ℕ) : ENNReal) := by
          exact_mod_cast hcountCost
        exact mul_le_mul_right'
          (mul_le_mul_right' hcast _) _
  have hresidueCondition : ∀ cell ∈ selected,
      cell.2.1 % (wz1Lemma23YStride rho : ℤ) =
        ((source.residue : ℕ) : ℤ) := by
    intro cell hcell
    exact source.residue_condition cell (hselectedSub hcell)
  have hySeparated : ∀ first ∈ selected, ∀ second ∈ selected,
      first.2.1 = second.2.1 ∨
        Real.sqrt rho ≤
          |(wz1Lemma23CellCenter rho first) 1 -
            (wz1Lemma23CellCenter rho second) 1| := by
    intro first hfirst second hsecond
    exact source.y_separated first (hselectedSub hfirst)
      second (hselectedSub hsecond)
  have hglobalBins : ∀ heightIndex ∈ wz1Lemma23SnappedHeights selected,
      (wz1Lemma23SnappedGlobalBinsAt
        rho globalPackage.extendedSlope selected heightIndex).card ≤
          globalPackage.globalBinBound := by
    intro heightIndex hheight
    have hsourceHeight :=
      wz1Lemma23_snappedHeights_mono hselectedSub hheight
    exact
      (Finset.card_le_card
        (wz1Lemma23_snappedGlobalBinsAt_mono
          rho globalPackage.extendedSlope heightIndex hselectedSub)).trans
        (source.global_bins heightIndex hsourceHeight)
  have hheightUniform :
      ∀ first ∈ wz1Lemma23SnappedHeights selected,
        ∀ second ∈ wz1Lemma23SnappedHeights selected,
          (wz1Lemma23HeightFiber selected first).card ≤
            2 * (wz1Lemma23HeightFiber selected second).card := by
    intro first hfirst second hsecond
    rcases Finset.mem_image.mp hfirst with ⟨firstCell, hfirstCell, hfirstEq⟩
    rcases Finset.mem_image.mp hsecond with ⟨secondCell, hsecondCell, hsecondEq⟩
    have hfirstSource : first ∈ heights := by
      rw [← hfirstEq]
      exact Finset.mem_image.mpr ⟨firstCell, hselectedSub hfirstCell, rfl⟩
    have hsecondSource : second ∈ heights := by
      rw [← hsecondEq]
      exact Finset.mem_image.mpr ⟨secondCell, hselectedSub hsecondCell, rfl⟩
    have hfirstPartition : fiber first ∈ partition :=
      Finset.mem_image.mpr ⟨first, hfirstSource, rfl⟩
    have hsecondPartition : fiber second ∈ partition :=
      Finset.mem_image.mpr ⟨second, hsecondSource, rfl⟩
    have hfirstNonempty : (selected ∩ fiber first).Nonempty := by
      refine ⟨firstCell, Finset.mem_inter.mpr ⟨hfirstCell, ?_⟩⟩
      exact Finset.mem_filter.mpr ⟨hselectedSub hfirstCell, hfirstEq⟩
    have hsecondNonempty : (selected ∩ fiber second).Nonempty := by
      refine ⟨secondCell, Finset.mem_inter.mpr ⟨hsecondCell, ?_⟩⟩
      exact Finset.mem_filter.mpr ⟨hselectedSub hsecondCell, hsecondEq⟩
    have hraw := huniform (fiber first) hfirstPartition
      (fiber second) hsecondPartition hfirstNonempty hsecondNonempty
    have hfirstFiberEq :
        wz1Lemma23HeightFiber selected first = selected ∩ fiber first := by
      ext cell
      constructor
      · intro hcell
        have hdata := Finset.mem_filter.mp hcell
        exact Finset.mem_inter.mpr
          ⟨hdata.1, Finset.mem_filter.mpr ⟨hselectedSub hdata.1, hdata.2⟩⟩
      · intro hcell
        have hdata := Finset.mem_inter.mp hcell
        have hfiberData := Finset.mem_filter.mp hdata.2
        exact Finset.mem_filter.mpr ⟨hdata.1, hfiberData.2⟩
    have hsecondFiberEq :
        wz1Lemma23HeightFiber selected second = selected ∩ fiber second := by
      ext cell
      constructor
      · intro hcell
        have hdata := Finset.mem_filter.mp hcell
        exact Finset.mem_inter.mpr
          ⟨hdata.1, Finset.mem_filter.mpr ⟨hselectedSub hdata.1, hdata.2⟩⟩
      · intro hcell
        have hdata := Finset.mem_inter.mp hcell
        have hfiberData := Finset.mem_filter.mp hdata.2
        exact Finset.mem_filter.mpr ⟨hdata.1, hfiberData.2⟩
    rw [hfirstFiberEq, hsecondFiberEq]
    exact hraw
  let residue : WZ1Lemma23YResiduePackage globalPackage :=
    { stride_pos := source.stride_pos
      stride_bound := source.stride_bound
      residue := source.residue
      cells := selected
      cells_eq := hselectedSub.trans source.cells_eq
      cells_subset := hselectedSub.trans source.cells_subset
      cells_active := hselectedSub.trans source.cells_active
      cardCost := newCost
      cardCost_pos := hnewCostPos
      extraCost := newExtraCost
      extraCost_pos := hnewExtraCostPos
      card_loss := hglobalCard
      volumeCost := newVolumeCost
      volumeCost_pos := hnewVolumeCostPos
      volumeCost_bound := hnewVolumeCostBound
      volume_cell_bound := hvolume
      residue_condition := hresidueCondition
      y_separated := hySeparated
      global_bins := hglobalBins
      heightFiberCost := 2
      heightFiberCost_pos := by omega
      height_uniform := hheightUniform }
  exact ⟨{
    logarithmicCost := logarithmicCost
    logarithmicCost_eq := rfl
    residue := residue
    cells_subset := hselectedSub
    cells_nonempty := hselectedNonempty
    card_retention := hretention
    cardCost_eq := rfl
    extraCost_eq := rfl
    volumeCost_eq := rfl
    heightFiberCost_eq := rfl
    height_uniform := hheightUniform
  }⟩

end

end Kakeya.Assouad
