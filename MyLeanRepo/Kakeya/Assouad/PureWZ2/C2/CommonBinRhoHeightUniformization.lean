import MyLeanRepo.Kakeya.Assouad.MultiscaleUniformRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23HeightPopularity

/-!
# Dyadic uniformization of genuine side-rho cube heights

This is the finite combinatorial core of paper Step 3.  A nonempty family of
genuine side-`rho` cubes is refined by its literal center-height label.  Whole
height fibres are retained, their cardinalities become comparable within a
factor two, and only a logarithmic cardinality loss is paid.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure CommonBinRhoHeightUniformData
    (source : Finset (ℤ × ℤ × ℤ)) where
  logarithmicCost : ℕ := Nat.log 2 source.card + 1
  logarithmicCost_eq :
    logarithmicCost = Nat.log 2 source.card + 1
  heightIndices : Finset ℤ
  cells : Finset (ℤ × ℤ × ℤ)
  cells_subset : cells ⊆ source
  cells_nonempty : cells.Nonempty
  heightIndices_eq :
    heightIndices = cells.image fun cell => cell.2.2
  heightIndices_nonempty : heightIndices.Nonempty
  cells_eq_filter :
    cells = source.filter fun cell => cell.2.2 ∈ heightIndices
  card_retention :
    source.card ≤ logarithmicCost * cells.card
  heightFiberCount : ℕ
  heightFiberCount_pos : 0 < heightFiberCount
  height_fiber_lower :
    ∀ height ∈ heightIndices,
      heightFiberCount ≤
        (cells.filter fun cell => cell.2.2 = height).card
  height_fiber_upper :
    ∀ height ∈ heightIndices,
      (cells.filter fun cell => cell.2.2 = height).card ≤
        2 * heightFiberCount

theorem commonBin_rhoHeightUniformization
    (source : Finset (ℤ × ℤ × ℤ))
    (hsource : source.Nonempty) :
    Nonempty (CommonBinRhoHeightUniformData source) := by
  let label : (ℤ × ℤ × ℤ) → ℤ := fun cell => cell.2.2
  let heights := source.image label
  let fiber : ℤ → Finset (ℤ × ℤ × ℤ) := fun height =>
    source.filter fun cell => label cell = height
  let partition : Finset (Finset (ℤ × ℤ × ℤ)) :=
    heights.image fiber
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
  have hcover : source ⊆ Finset.biUnion partition id := by
    intro cell hcell
    have hheight : label cell ∈ heights :=
      Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
    have hfiber : fiber (label cell) ∈ partition :=
      Finset.mem_image.mpr ⟨label cell, hheight, rfl⟩
    exact Finset.mem_biUnion.mpr
      ⟨fiber (label cell), hfiber,
        Finset.mem_filter.mpr ⟨hcell, rfl⟩⟩
  rcases dyadic_uniformity_single_level source hsource partition
      hpartitionDisjoint hcover with
    ⟨selected, kept, hkept, hselectedEq, hselectedNonempty,
      huniform, hretentionReal⟩
  have hselectedSub : selected ⊆ source := by
    intro cell hcell
    rw [hselectedEq] at hcell
    rcases Finset.mem_biUnion.mp hcell with
      ⟨piece, _hpiece, hcellPiece⟩
    exact (Finset.mem_inter.mp hcellPiece).1
  let logarithmicCost := Nat.log 2 source.card + 1
  have hlogPos : 0 < logarithmicCost := by
    dsimp only [logarithmicCost]
    omega
  have hretention :
      source.card ≤ logarithmicCost * selected.card := by
    have hlogReal : 0 < (logarithmicCost : ℝ) := by
      exact_mod_cast hlogPos
    have hmul :
        (source.card : ℝ) ≤
          (logarithmicCost : ℝ) * (selected.card : ℝ) := by
      have hdiv :
          (source.card : ℝ) / logarithmicCost ≤ selected.card := by
        simpa [logarithmicCost] using hretentionReal
      simpa [mul_comm] using (div_le_iff₀ hlogReal).mp hdiv
    exact_mod_cast hmul
  let selectedHeights := selected.image label
  have hselectedHeightsNonempty : selectedHeights.Nonempty :=
    hselectedNonempty.image label
  have hselectedExact :
      selected =
        source.filter fun cell => label cell ∈ selectedHeights := by
    apply Finset.Subset.antisymm
    · intro cell hcell
      exact Finset.mem_filter.mpr
        ⟨hselectedSub hcell,
          Finset.mem_image.mpr ⟨cell, hcell, rfl⟩⟩
    · intro cell hcell
      have hdata := Finset.mem_filter.mp hcell
      rcases Finset.mem_image.mp hdata.2 with
        ⟨selectedCell, hselectedCell, hlabelEq⟩
      rw [hselectedEq] at hselectedCell ⊢
      rcases Finset.mem_biUnion.mp hselectedCell with
        ⟨piece, hpieceKept, hselectedPiece⟩
      have hpiecePartition := hkept hpieceKept
      rcases Finset.mem_image.mp hpiecePartition with
        ⟨pieceHeight, _hpieceHeight, hpieceEq⟩
      have hselectedHeight :
          label selectedCell = pieceHeight := by
        rw [← hpieceEq] at hselectedPiece
        exact (Finset.mem_filter.mp
          (Finset.mem_inter.mp hselectedPiece).2).2
      have hcellHeight : label cell = pieceHeight :=
        hlabelEq.symm.trans hselectedHeight
      exact Finset.mem_biUnion.mpr
        ⟨piece, hpieceKept, by
          refine Finset.mem_inter.mpr ⟨hdata.1, ?_⟩
          rw [← hpieceEq]
          exact Finset.mem_filter.mpr ⟨hdata.1, hcellHeight⟩⟩
  have hheightUniform :
      ∀ first ∈ selectedHeights, ∀ second ∈ selectedHeights,
        (selected.filter fun cell => label cell = first).card ≤
          2 * (selected.filter fun cell => label cell = second).card := by
    intro first hfirst second hsecond
    rcases Finset.mem_image.mp hfirst with
      ⟨firstCell, hfirstCell, hfirstEq⟩
    rcases Finset.mem_image.mp hsecond with
      ⟨secondCell, hsecondCell, hsecondEq⟩
    have hfirstSource : first ∈ heights := by
      rw [← hfirstEq]
      exact Finset.mem_image.mpr
        ⟨firstCell, hselectedSub hfirstCell, rfl⟩
    have hsecondSource : second ∈ heights := by
      rw [← hsecondEq]
      exact Finset.mem_image.mpr
        ⟨secondCell, hselectedSub hsecondCell, rfl⟩
    have hfirstPartition : fiber first ∈ partition :=
      Finset.mem_image.mpr ⟨first, hfirstSource, rfl⟩
    have hsecondPartition : fiber second ∈ partition :=
      Finset.mem_image.mpr ⟨second, hsecondSource, rfl⟩
    have hfirstKept : fiber first ∈ kept := by
      rw [hselectedEq] at hfirstCell
      rcases Finset.mem_biUnion.mp hfirstCell with
        ⟨piece, hpiece, hfirstPiece⟩
      have hpiecePartition := hkept hpiece
      rcases Finset.mem_image.mp hpiecePartition with
        ⟨pieceHeight, _hpieceHeight, hpieceEq⟩
      have hheight :
          first = pieceHeight := by
        have hpieceMem := (Finset.mem_inter.mp hfirstPiece).2
        rw [← hpieceEq] at hpieceMem
        exact hfirstEq.symm.trans (Finset.mem_filter.mp hpieceMem).2
      have hpiece' : fiber pieceHeight ∈ kept := by
        rwa [hpieceEq]
      rwa [hheight]
    have hsecondKept : fiber second ∈ kept := by
      rw [hselectedEq] at hsecondCell
      rcases Finset.mem_biUnion.mp hsecondCell with
        ⟨piece, hpiece, hsecondPiece⟩
      have hpiecePartition := hkept hpiece
      rcases Finset.mem_image.mp hpiecePartition with
        ⟨pieceHeight, _hpieceHeight, hpieceEq⟩
      have hheight :
          second = pieceHeight := by
        have hpieceMem := (Finset.mem_inter.mp hsecondPiece).2
        rw [← hpieceEq] at hpieceMem
        exact hsecondEq.symm.trans (Finset.mem_filter.mp hpieceMem).2
      have hpiece' : fiber pieceHeight ∈ kept := by
        rwa [hpieceEq]
      rwa [hheight]
    have hfirstNonempty :
        (selected ∩ fiber first).Nonempty :=
      ⟨firstCell, Finset.mem_inter.mpr
        ⟨hfirstCell, Finset.mem_filter.mpr
          ⟨hselectedSub hfirstCell, hfirstEq⟩⟩⟩
    have hsecondNonempty :
        (selected ∩ fiber second).Nonempty :=
      ⟨secondCell, Finset.mem_inter.mpr
        ⟨hsecondCell, Finset.mem_filter.mpr
          ⟨hselectedSub hsecondCell, hsecondEq⟩⟩⟩
    have hraw := huniform (fiber first) hfirstPartition
      (fiber second) hsecondPartition hfirstNonempty hsecondNonempty
    have hfirstFiber :
        selected.filter (fun cell => label cell = first) =
          selected ∩ fiber first := by
      ext cell
      constructor
      · intro hcell
        have hdata := Finset.mem_filter.mp hcell
        exact Finset.mem_inter.mpr
          ⟨hdata.1, Finset.mem_filter.mpr
            ⟨hselectedSub hdata.1, hdata.2⟩⟩
      · intro hcell
        have hdata := Finset.mem_inter.mp hcell
        exact Finset.mem_filter.mpr
          ⟨hdata.1, (Finset.mem_filter.mp hdata.2).2⟩
    have hsecondFiber :
        selected.filter (fun cell => label cell = second) =
          selected ∩ fiber second := by
      ext cell
      constructor
      · intro hcell
        have hdata := Finset.mem_filter.mp hcell
        exact Finset.mem_inter.mpr
          ⟨hdata.1, Finset.mem_filter.mpr
            ⟨hselectedSub hdata.1, hdata.2⟩⟩
      · intro hcell
        have hdata := Finset.mem_inter.mp hcell
        exact Finset.mem_filter.mpr
          ⟨hdata.1, (Finset.mem_filter.mp hdata.2).2⟩
    rw [hfirstFiber, hsecondFiber]
    exact hraw
  obtain ⟨baseHeight, hbaseHeight, hbaseMin⟩ :=
    Finset.exists_min_image selectedHeights
      (fun height =>
        (selected.filter fun cell => label cell = height).card)
      hselectedHeightsNonempty
  let heightFiberCount :=
    (selected.filter fun cell => label cell = baseHeight).card
  have hheightFiberCountPos : 0 < heightFiberCount := by
    rcases Finset.mem_image.mp hbaseHeight with
      ⟨cell, hcell, hcellHeight⟩
    apply Finset.card_pos.mpr
    exact ⟨cell, Finset.mem_filter.mpr ⟨hcell, hcellHeight⟩⟩
  exact ⟨{
    logarithmicCost := logarithmicCost
    logarithmicCost_eq := rfl
    heightIndices := selectedHeights
    cells := selected
    cells_subset := hselectedSub
    cells_nonempty := hselectedNonempty
    heightIndices_eq := rfl
    heightIndices_nonempty := hselectedHeightsNonempty
    cells_eq_filter := by
      simpa [selectedHeights] using hselectedExact
    card_retention := hretention
    heightFiberCount := heightFiberCount
    heightFiberCount_pos := hheightFiberCountPos
    height_fiber_lower := by
      intro height hheight
      exact hbaseMin height hheight
    height_fiber_upper := by
      intro height hheight
      exact hheightUniform height hheight baseHeight hbaseHeight
  }⟩

namespace CommonBinRhoHeightUniformData

/-- Any selected subset of the paper-popular height labels retains the
corresponding relative number of genuine side-`rho` cubes. -/
theorem selected_height_card_lower
    {source : Finset (ℤ × ℤ × ℤ)}
    (data : CommonBinRhoHeightUniformData source)
    (selectedHeights : Finset ℤ)
    (hselected : selectedHeights ⊆ data.heightIndices) :
    selectedHeights.card * data.cells.card ≤
      2 * data.heightIndices.card *
        (data.cells.filter fun cell =>
          cell.2.2 ∈ selectedHeights).card := by
  have himage :
      data.cells.image (fun cell => cell.2.2) = data.heightIndices :=
    data.heightIndices_eq.symm
  have hraw := finset_selected_fibers_card_lower
      data.cells (fun cell => cell.2.2) selectedHeights
      (by rwa [himage]) 2 (by
        intro first hfirst second hsecond
        have hfirst' : first ∈ data.heightIndices := by
          rwa [← himage]
        have hsecond' : second ∈ data.heightIndices := by
          rwa [← himage]
        calc
          (data.cells.filter fun cell => cell.2.2 = first).card ≤
              2 * data.heightFiberCount :=
            data.height_fiber_upper first hfirst'
          _ ≤ 2 * (data.cells.filter fun cell =>
                cell.2.2 = second).card := by
            exact Nat.mul_le_mul_left 2
              (data.height_fiber_lower second hsecond'))
  rwa [himage] at hraw

end CommonBinRhoHeightUniformData

end Kakeya.Assouad

end
