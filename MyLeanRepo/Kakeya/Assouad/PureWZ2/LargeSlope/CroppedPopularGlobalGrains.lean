import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CroppedMultiplicityBand
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6ScaleData
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ADBinCount
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperInfrastructure
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.MultiscaleUniformRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicADTransfer
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LipschitzGraphFrostman
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGridCubeVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadow

/-!
# Popular global grains from whole paper cells

This is WZ2 Section 6, Refinement 1.  It is a construction on the selected
constant-multiplicity shading, not an extra conclusion of Proposition 21.
Whole `delta`-cells are labelled by their z-layer and their global scalar
`delta`-bin.  Light labels are removed; each surviving label is therefore an
almost-full literal global grain.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

@[simp] theorem pureWZ2PaperCellCenter_zero
    (delta : ℝ) (cell : ℤ × ℤ × ℤ) :
    pureWZ2PaperCellCenter delta cell (0 : Fin 3) =
      ((cell.1 : ℝ) + 1 / 2) * delta := by
  simp [pureWZ2PaperCellCenter, cellCorner,
    wz1PaperGridCubeTranslation, point3]
  ring

@[simp] theorem pureWZ2PaperCellCenter_one
    (delta : ℝ) (cell : ℤ × ℤ × ℤ) :
    pureWZ2PaperCellCenter delta cell (1 : Fin 3) =
      ((cell.2.1 : ℝ) + 1 / 2) * delta := by
  simp [pureWZ2PaperCellCenter, cellCorner,
    wz1PaperGridCubeTranslation, point3]
  ring

@[simp] theorem pureWZ2PaperCellCenter_two
    (delta : ℝ) (cell : ℤ × ℤ × ℤ) :
    pureWZ2PaperCellCenter delta cell (2 : Fin 3) =
      ((cell.2.2 : ℝ) + 1 / 2) * delta := by
  simp [pureWZ2PaperCellCenter, cellCorner,
    wz1PaperGridCubeTranslation, point3]
  ring

/-- The Section-6 global-grain label of one literal `delta`-cell. -/
def pureWZ2GlobalGrainLabel
    (slope : ℝ → ℝ) (delta : ℝ)
    (cell : ℤ × ℤ × ℤ) : ℤ × ℤ :=
  let center := pureWZ2PaperCellCenter delta cell
  (cell.2.2,
    Int.floor
      (inner ℝ center
        (globalGrainDirection (slope (center (2 : Fin 3)))) / delta))

/-- Active cells carrying one global-grain label. -/
def pureWZ2GlobalGrainFiber
    (slope : ℝ → ℝ) (delta : ℝ)
    (cells : Finset (ℤ × ℤ × ℤ)) (label : ℤ × ℤ) :
    Finset (ℤ × ℤ × ℤ) :=
  cells.filter fun cell =>
    pureWZ2GlobalGrainLabel slope delta cell = label

/-- Labels actually occupied by the finite active cell family. -/
def pureWZ2GlobalGrainLabels
    (slope : ℝ → ℝ) (delta : ℝ)
    (cells : Finset (ℤ × ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  cells.image (pureWZ2GlobalGrainLabel slope delta)

@[simp] theorem mem_pureWZ2GlobalGrainFiber
    (slope : ℝ → ℝ) (delta : ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (label : ℤ × ℤ) (cell : ℤ × ℤ × ℤ) :
    cell ∈ pureWZ2GlobalGrainFiber slope delta cells label ↔
      cell ∈ cells ∧ pureWZ2GlobalGrainLabel slope delta cell = label := by
  simp [pureWZ2GlobalGrainFiber]

@[simp] theorem mem_pureWZ2GlobalGrainLabels
    (slope : ℝ → ℝ) (delta : ℝ)
    (cells : Finset (ℤ × ℤ × ℤ)) (label : ℤ × ℤ) :
    label ∈ pureWZ2GlobalGrainLabels slope delta cells ↔
      ∃ cell ∈ cells, pureWZ2GlobalGrainLabel slope delta cell = label := by
  simp [pureWZ2GlobalGrainLabels]

/-- The occupied label fibers partition all active cells. -/
theorem pureWZ2GlobalGrainFiber_biUnion
    (slope : ℝ → ℝ) (delta : ℝ)
    (cells : Finset (ℤ × ℤ × ℤ)) :
    (pureWZ2GlobalGrainLabels slope delta cells).biUnion
        (pureWZ2GlobalGrainFiber slope delta cells) = cells := by
  ext cell
  constructor
  · simp [pureWZ2GlobalGrainLabels, pureWZ2GlobalGrainFiber]
  · intro hcell
    exact Finset.mem_biUnion.mpr
      ⟨pureWZ2GlobalGrainLabel slope delta cell,
        Finset.mem_image.mpr ⟨cell, hcell, rfl⟩,
        (mem_pureWZ2GlobalGrainFiber slope delta cells _ cell).mpr
          ⟨hcell, rfl⟩⟩

/-- Distinct labels have disjoint cell fibers. -/
theorem pureWZ2GlobalGrainFiber_disjoint
    (slope : ℝ → ℝ) (delta : ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    {first second : ℤ × ℤ} (hne : first ≠ second) :
    Disjoint
      (pureWZ2GlobalGrainFiber slope delta cells first)
      (pureWZ2GlobalGrainFiber slope delta cells second) := by
  rw [Finset.disjoint_left]
  intro cell hfirst hsecond
  have hfirstLabel :=
    (mem_pureWZ2GlobalGrainFiber slope delta cells first cell).mp hfirst |>.2
  have hsecondLabel :=
    (mem_pureWZ2GlobalGrainFiber slope delta cells second cell).mp hsecond |>.2
  exact hne (hfirstLabel.symm.trans hsecondLabel)

private lemma pureWZ2_floor_int_add_half (index : ℤ) :
    Int.floor ((index : ℝ) + 1 / 2) = index := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num

/-- Canonical centers belong to their literal paper cells. -/
theorem pureWZ2PaperCellCenter_mem
    {delta : ℝ} (hdelta : 0 < delta)
    (cell : ℤ × ℤ × ℤ) :
    pureWZ2PaperCellCenter delta cell ∈
      wz1PaperGridCube delta cell := by
  apply (mem_wz1PaperGridCube delta cell _).mpr
  apply Prod.ext
  · simp only [wz1PaperGridIndex, gridIndex, pureWZ2PaperCellCenter_zero]
    have hdiv : (((cell.1 : ℝ) + 1 / 2) * delta) / delta =
        (cell.1 : ℝ) + 1 / 2 := by field_simp [hdelta.ne']
    rw [hdiv]
    exact pureWZ2_floor_int_add_half cell.1
  · apply Prod.ext
    · simp only [wz1PaperGridIndex, gridIndex, pureWZ2PaperCellCenter_one]
      have hdiv : (((cell.2.1 : ℝ) + 1 / 2) * delta) / delta =
          (cell.2.1 : ℝ) + 1 / 2 := by field_simp [hdelta.ne']
      rw [hdiv]
      exact pureWZ2_floor_int_add_half cell.2.1
    · simp only [wz1PaperGridIndex, gridIndex, pureWZ2PaperCellCenter_two]
      have hdiv : (((cell.2.2 : ℝ) + 1 / 2) * delta) / delta =
          (cell.2.2 : ℝ) + 1 / 2 := by field_simp [hdelta.ne']
      rw [hdiv]
      exact pureWZ2_floor_int_add_half cell.2.2

private lemma pureWZ2_floor_coord_bound
    {scale value : ℝ} {index : ℤ} (hscale : 0 < scale)
    (hfloor : Int.floor (value / scale) = index) :
    |value - ((index : ℝ) + 1 / 2) * scale| ≤ scale / 2 := by
  have hlower : (index : ℝ) ≤ value / scale := by
    rw [← hfloor]
    exact Int.floor_le _
  have hupper : value / scale < (index : ℝ) + 1 := by
    rw [← hfloor]
    exact Int.lt_floor_add_one _
  have hlower' : (index : ℝ) * scale ≤ value := by
    have h := mul_le_mul_of_nonneg_right hlower hscale.le
    have hcancel : value / scale * scale = value := by
      field_simp [hscale.ne']
    rwa [hcancel] at h
  have hupper' : value < ((index : ℝ) + 1) * scale := by
    have h := mul_lt_mul_of_pos_right hupper hscale
    have hcancel : value / scale * scale = value := by
      field_simp [hscale.ne']
    rwa [hcancel] at h
  rw [abs_le]
  constructor <;> linarith

/-- Points in one literal paper cell are coordinatewise within `delta`. -/
theorem pureWZ2_point_close_to_cellCenter
    {delta : ℝ} (hdelta : 0 < delta)
    {cell : ℤ × ℤ × ℤ} {point : Point3}
    (hpoint : point ∈ wz1PaperGridCube delta cell) :
    ∀ coordinate : Fin 3,
      |point coordinate - pureWZ2PaperCellCenter delta cell coordinate| ≤
        delta / 2 := by
  have hindex := (mem_wz1PaperGridCube delta cell point).mp hpoint
  intro coordinate
  fin_cases coordinate
  · have hfloor : Int.floor (point 0 / delta) = cell.1 := by
      exact congr_arg Prod.fst hindex
    simpa using pureWZ2_floor_coord_bound hdelta hfloor
  · have hfloor : Int.floor (point 1 / delta) = cell.2.1 := by
      exact congr_arg (fun index : ℤ × ℤ × ℤ => index.2.1) hindex
    simpa using pureWZ2_floor_coord_bound hdelta hfloor
  · have hfloor : Int.floor (point 2 / delta) = cell.2.2 := by
      exact congr_arg (fun index : ℤ × ℤ × ℤ => index.2.2) hindex
    simpa using pureWZ2_floor_coord_bound hdelta hfloor

/-- Literal global grain with an explicit constant multiple of `delta`. -/
def pureWZ2GlobalGrainWithConstant
    (constant : ℝ) (slope : ℝ → ℝ)
    (delta : ℝ) (anchor : Point3) : Set Point3 :=
  {point |
    |point (2 : Fin 3) - anchor (2 : Fin 3)| ≤ constant * delta ∧
      |inner ℝ point
          (globalGrainDirection (slope (anchor (2 : Fin 3)))) -
        inner ℝ anchor
          (globalGrainDirection (slope (anchor (2 : Fin 3))))| ≤
          constant * delta}

private theorem pureWZ2_inner_globalDirection
    (point : Point3) (value : ℝ) :
    inner ℝ point (globalGrainDirection value) =
      point 0 + value * point 1 := by
  simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]

private theorem pureWZ2_abs_sub_lt_of_floor_div_eq
    {first second scale : ℝ} (hscale : 0 < scale)
    (hfloor : Int.floor (first / scale) = Int.floor (second / scale)) :
    |first - second| < scale := by
  have hfirstLower :
      (Int.floor (first / scale) : ℝ) ≤ first / scale :=
    Int.floor_le _
  have hfirstUpper :
      first / scale < (Int.floor (first / scale) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hsecondLower :
      (Int.floor (second / scale) : ℝ) ≤ second / scale :=
    Int.floor_le _
  have hsecondUpper :
      second / scale < (Int.floor (second / scale) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hratio : |first / scale - second / scale| < 1 := by
    rw [abs_lt]
    constructor
    · rw [hfloor] at hfirstLower hfirstUpper
      linarith
    · rw [← hfloor] at hsecondLower hsecondUpper
      linarith
  have hdiv : |(first - second) / scale| < 1 := by
    rw [sub_div]
    exact hratio
  rw [abs_div, abs_of_pos hscale] at hdiv
  have hmul := mul_lt_mul_of_pos_right hdiv hscale
  simpa [hscale.ne'] using hmul

/-- Equal global labels put cell centers in one `delta`-grain. -/
theorem pureWZ2_cellCenters_same_label
    {delta : ℝ} (hdelta : 0 < delta)
    (slope : ℝ → ℝ)
    {first second : ℤ × ℤ × ℤ}
    (hlabel :
      pureWZ2GlobalGrainLabel slope delta first =
        pureWZ2GlobalGrainLabel slope delta second) :
    |(pureWZ2PaperCellCenter delta first) 2 -
        (pureWZ2PaperCellCenter delta second) 2| = 0 ∧
      |inner ℝ (pureWZ2PaperCellCenter delta first)
            (globalGrainDirection
              (slope ((pureWZ2PaperCellCenter delta first) 2))) -
        inner ℝ (pureWZ2PaperCellCenter delta second)
            (globalGrainDirection
              (slope ((pureWZ2PaperCellCenter delta first) 2)))| < delta := by
  have hzIndex : first.2.2 = second.2.2 :=
    congr_arg Prod.fst hlabel
  have hzCenter :
      (pureWZ2PaperCellCenter delta first) 2 =
        (pureWZ2PaperCellCenter delta second) 2 := by
    simp [hzIndex]
  have hbin :
      Int.floor
          (inner ℝ (pureWZ2PaperCellCenter delta first)
              (globalGrainDirection
                (slope ((pureWZ2PaperCellCenter delta first) 2))) / delta) =
        Int.floor
          (inner ℝ (pureWZ2PaperCellCenter delta second)
              (globalGrainDirection
                (slope ((pureWZ2PaperCellCenter delta second) 2))) / delta) :=
    congr_arg Prod.snd hlabel
  rw [← hzCenter] at hbin
  constructor
  · rw [hzCenter, sub_self, abs_zero]
  · exact pureWZ2_abs_sub_lt_of_floor_div_eq hdelta hbin

/--
Every point of a cell with the same label as the anchor cell lies in a
constant-`4` literal global grain through the anchor center.
-/
theorem pureWZ2_same_label_cell_subset_globalGrain
    {delta : ℝ} (hdelta : 0 < delta)
    (slope : ℝ → ℝ)
    (hnormalized : PureWZ2AmbientSlopeIsNormalized slope)
    {anchorCell cell : ℤ × ℤ × ℤ}
    (hanchorHeight :
      (pureWZ2PaperCellCenter delta anchorCell) 2 ∈
        Set.Icc (-1 : ℝ) 1)
    (hlabel :
      pureWZ2GlobalGrainLabel slope delta cell =
        pureWZ2GlobalGrainLabel slope delta anchorCell) :
    wz1PaperGridCube delta cell ⊆
      pureWZ2GlobalGrainWithConstant 4 slope delta
        (pureWZ2PaperCellCenter delta anchorCell) := by
  intro point hpoint
  let center := pureWZ2PaperCellCenter delta cell
  let anchor := pureWZ2PaperCellCenter delta anchorCell
  have hcenters :=
    pureWZ2_cellCenters_same_label hdelta slope hlabel
  have hpoint0 := pureWZ2_point_close_to_cellCenter hdelta hpoint 0
  have hpoint1 := pureWZ2_point_close_to_cellCenter hdelta hpoint 1
  have hpoint2 := pureWZ2_point_close_to_cellCenter hdelta hpoint 2
  have hslopeBound : |slope (anchor 2)| ≤ 1 :=
    (hnormalized (anchor 2) hanchorHeight).1
  have hz : |point 2 - anchor 2| ≤ 4 * delta := by
    have hcenterZ : center 2 = anchor 2 := by
      have := hcenters.1
      exact sub_eq_zero.mp (abs_eq_zero.mp this)
    rw [← hcenterZ]
    linarith [hpoint2]
  have hpointCenterProjection :
      |inner ℝ point (globalGrainDirection (slope (anchor 2))) -
        inner ℝ center (globalGrainDirection (slope (anchor 2)))| ≤
          2 * delta := by
    rw [pureWZ2_inner_globalDirection, pureWZ2_inner_globalDirection]
    have hsum :
        |(point 0 - center 0) +
            slope (anchor 2) * (point 1 - center 1)| ≤
          |point 0 - center 0| +
            |slope (anchor 2)| * |point 1 - center 1| := by
      calc
        |(point 0 - center 0) +
            slope (anchor 2) * (point 1 - center 1)|
            ≤ |point 0 - center 0| +
                |slope (anchor 2) * (point 1 - center 1)| :=
              abs_add_le _ _
        _ = _ := by rw [abs_mul]
    have hbound :
        |point 0 - center 0| +
            |slope (anchor 2)| * |point 1 - center 1| ≤
          2 * delta := by
      nlinarith [abs_nonneg (slope (anchor 2)), hpoint0, hpoint1]
    have heq :
        (point 0 + slope (anchor 2) * point 1) -
            (center 0 + slope (anchor 2) * center 1) =
          (point 0 - center 0) +
            slope (anchor 2) * (point 1 - center 1) := by ring
    rw [heq]
    exact hsum.trans hbound
  have hcenterProjection :
      |inner ℝ center (globalGrainDirection (slope (anchor 2))) -
        inner ℝ anchor (globalGrainDirection (slope (anchor 2)))| <
          delta := by
    have hp := hcenters.2
    have hcenterZ : center 2 = anchor 2 := by
      exact sub_eq_zero.mp (abs_eq_zero.mp hcenters.1)
    change
      |inner ℝ center (globalGrainDirection (slope (anchor 2))) -
        inner ℝ anchor (globalGrainDirection (slope (anchor 2)))| < delta
    simpa [center, anchor, hcenterZ] using hp
  have hprojection :
      |inner ℝ point (globalGrainDirection (slope (anchor 2))) -
        inner ℝ anchor (globalGrainDirection (slope (anchor 2)))| ≤
          4 * delta := by
    calc
      |inner ℝ point (globalGrainDirection (slope (anchor 2))) -
          inner ℝ anchor (globalGrainDirection (slope (anchor 2)))|
          ≤ |inner ℝ point (globalGrainDirection (slope (anchor 2))) -
                inner ℝ center (globalGrainDirection (slope (anchor 2)))| +
              |inner ℝ center (globalGrainDirection (slope (anchor 2))) -
                inner ℝ anchor (globalGrainDirection (slope (anchor 2)))| := by
            exact abs_sub_le _ _ _
      _ ≤ 2 * delta + delta := by
        exact add_le_add hpointCenterProjection hcenterProjection.le
      _ ≤ 4 * delta := by linarith
  exact ⟨hz, hprojection⟩

/-- Dyadically popular global-grain cell fibers. -/
structure PureWZ2PopularGlobalGrainCellData
    (slope : ℝ → ℝ) (delta : ℝ)
    (cells : Finset (ℤ × ℤ × ℤ)) where
  retainedCells : Finset (ℤ × ℤ × ℤ)
  keptLabels : Finset (ℤ × ℤ)
  keptLabels_subset :
    keptLabels ⊆ pureWZ2GlobalGrainLabels slope delta cells
  retained_eq :
    retainedCells = keptLabels.biUnion
      (pureWZ2GlobalGrainFiber slope delta cells)
  retained_nonempty : retainedCells.Nonempty
  retained_card_lower :
    (cells.card : ℝ) / (Nat.log 2 cells.card + 1 : ℝ) ≤
      (retainedCells.card : ℝ)
  fiber_nonempty :
    ∀ label ∈ keptLabels,
      (pureWZ2GlobalGrainFiber slope delta cells label).Nonempty
  fiber_uniform :
    ∀ first ∈ keptLabels, ∀ second ∈ keptLabels,
      (pureWZ2GlobalGrainFiber slope delta cells first).card ≤
        2 * (pureWZ2GlobalGrainFiber slope delta cells second).card

/-- Occupied labels have distinct nonempty fibers. -/
theorem pureWZ2GlobalGrainFiber_injective_on_labels
    (slope : ℝ → ℝ) (delta : ℝ)
    (cells : Finset (ℤ × ℤ × ℤ)) :
    Set.InjOn (pureWZ2GlobalGrainFiber slope delta cells)
      (pureWZ2GlobalGrainLabels slope delta cells) := by
  intro first hfirst second hsecond heq
  rcases (mem_pureWZ2GlobalGrainLabels slope delta cells first).mp hfirst with
    ⟨cell, hcell, hlabel⟩
  have hmemFirst : cell ∈ pureWZ2GlobalGrainFiber slope delta cells first :=
    (mem_pureWZ2GlobalGrainFiber slope delta cells first cell).mpr
      ⟨hcell, hlabel⟩
  have hmemSecond : cell ∈ pureWZ2GlobalGrainFiber slope delta cells second := by
    rw [← heq]
    exact hmemFirst
  have hsecondLabel :=
    (mem_pureWZ2GlobalGrainFiber slope delta cells second cell).mp
      hmemSecond |>.2
  exact hlabel.symm.trans hsecondLabel

/-- Select one dyadic popularity band of complete global-grain fibers. -/
theorem pureWZ2_select_popular_globalGrainCells
    (slope : ℝ → ℝ) (delta : ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (hcells : cells.Nonempty) :
    Nonempty (PureWZ2PopularGlobalGrainCellData slope delta cells) := by
  let labels := pureWZ2GlobalGrainLabels slope delta cells
  let fiber := pureWZ2GlobalGrainFiber slope delta cells
  let fibers : Finset (Finset (ℤ × ℤ × ℤ)) := labels.image fiber
  have hfiberInj : Set.InjOn fiber labels :=
    pureWZ2GlobalGrainFiber_injective_on_labels slope delta cells
  have hfibersDisjoint :
      ∀ first ∈ fibers, ∀ second ∈ fibers, first ≠ second →
        Disjoint first second := by
    intro first hfirst second hsecond hne
    rcases Finset.mem_image.mp hfirst with ⟨firstLabel, hfirstLabel, rfl⟩
    rcases Finset.mem_image.mp hsecond with ⟨secondLabel, hsecondLabel, rfl⟩
    have hlabelNe : firstLabel ≠ secondLabel := by
      intro hlabel
      apply hne
      rw [hlabel]
    exact pureWZ2GlobalGrainFiber_disjoint slope delta cells hlabelNe
  have hcover : cells ⊆ fibers.biUnion id := by
    intro cell hcell
    let label := pureWZ2GlobalGrainLabel slope delta cell
    have hlabel : label ∈ labels :=
      Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
    have hfiberMem : fiber label ∈ fibers :=
      Finset.mem_image.mpr ⟨label, hlabel, rfl⟩
    exact Finset.mem_biUnion.mpr
      ⟨fiber label, hfiberMem,
        (mem_pureWZ2GlobalGrainFiber slope delta cells label cell).mpr
          ⟨hcell, rfl⟩⟩
  rcases dyadic_uniformity_single_level
      cells hcells fibers hfibersDisjoint hcover with
    ⟨retainedCells, keptFibers, hkeptFibers, hretainedEq,
      hretainedNonempty, huniform, hretainedCard⟩
  let keptLabels : Finset (ℤ × ℤ) :=
    labels.filter fun label => fiber label ∈ keptFibers
  have hkeptLabelsSubset : keptLabels ⊆ labels :=
    Finset.filter_subset _ _
  have hkeptImage : keptLabels.image fiber = keptFibers := by
    ext selectedFiber
    constructor
    · intro hselected
      rcases Finset.mem_image.mp hselected with
        ⟨label, hlabel, rfl⟩
      exact (Finset.mem_filter.mp hlabel).2
    · intro hselected
      have hselectedFiber : selectedFiber ∈ fibers :=
        hkeptFibers hselected
      rcases Finset.mem_image.mp hselectedFiber with
        ⟨label, hlabel, hfiberEq⟩
      exact Finset.mem_image.mpr
        ⟨label, Finset.mem_filter.mpr ⟨hlabel, by rwa [hfiberEq]⟩,
          hfiberEq⟩
  have hretainedLabels :
      retainedCells = keptLabels.biUnion fiber := by
    rw [hretainedEq, ← hkeptImage]
    ext cell
    constructor
    · intro hcell
      rcases Finset.mem_biUnion.mp hcell with
        ⟨labelFiber, hlabelFiber, hcellInter⟩
      rcases Finset.mem_image.mp hlabelFiber with
        ⟨label, hlabel, rfl⟩
      exact Finset.mem_biUnion.mpr
        ⟨label, hlabel, (Finset.mem_inter.mp hcellInter).2⟩
    · intro hcell
      rcases Finset.mem_biUnion.mp hcell with
        ⟨label, hlabel, hcellFiber⟩
      have hcellSource : cell ∈ cells :=
        (mem_pureWZ2GlobalGrainFiber slope delta cells label cell).mp
          hcellFiber |>.1
      exact Finset.mem_biUnion.mpr
        ⟨fiber label, Finset.mem_image.mpr ⟨label, hlabel, rfl⟩,
          Finset.mem_inter.mpr ⟨hcellSource, hcellFiber⟩⟩
  have hlabelFiberNonempty :
      ∀ label ∈ keptLabels, (fiber label).Nonempty := by
    intro label hlabel
    have hoccupied : label ∈ labels :=
      (Finset.mem_filter.mp hlabel).1
    rcases (mem_pureWZ2GlobalGrainLabels slope delta cells label).mp
        hoccupied with
      ⟨cell, hcell, hcellLabel⟩
    exact ⟨cell,
      (mem_pureWZ2GlobalGrainFiber slope delta cells label cell).mpr
        ⟨hcell, hcellLabel⟩⟩
  have hfiberRetained :
      ∀ label ∈ keptLabels, retainedCells ∩ fiber label = fiber label := by
    intro label hlabel
    apply Finset.inter_eq_right.mpr
    intro cell hcell
    rw [hretainedLabels]
    exact Finset.mem_biUnion.mpr ⟨label, hlabel, hcell⟩
  have hfiberUniform :
      ∀ first ∈ keptLabels, ∀ second ∈ keptLabels,
        (fiber first).card ≤ 2 * (fiber second).card := by
    intro first hfirst second hsecond
    have hfirstFiber : fiber first ∈ fibers :=
      Finset.mem_image.mpr
        ⟨first, hkeptLabelsSubset hfirst, rfl⟩
    have hsecondFiber : fiber second ∈ fibers :=
      Finset.mem_image.mpr
        ⟨second, hkeptLabelsSubset hsecond, rfl⟩
    have hfirstNe := hlabelFiberNonempty first hfirst
    have hsecondNe := hlabelFiberNonempty second hsecond
    have hmain := huniform (fiber first) hfirstFiber
      (fiber second) hsecondFiber
    rw [hfiberRetained first hfirst, hfiberRetained second hsecond] at hmain
    exact hmain hfirstNe hsecondNe
  exact ⟨{
    retainedCells := retainedCells
    keptLabels := keptLabels
    keptLabels_subset := hkeptLabelsSubset
    retained_eq := hretainedLabels
    retained_nonempty := hretainedNonempty
    retained_card_lower := hretainedCard
    fiber_nonempty := hlabelFiberNonempty
    fiber_uniform := hfiberUniform
  }⟩

/-- Convert retained popular cells back to a whole-cell paper shading. -/
def PureWZ2PopularGlobalGrainCellData.refinedShading
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {slope : ℝ → ℝ}
    {cells : Finset (ℤ × ℤ × ℤ)}
    (data : PureWZ2PopularGlobalGrainCellData slope delta cells) :
    WZ1PaperTubeShading family :=
  wz2RefinedShading shading data.retainedCells

theorem PureWZ2PopularGlobalGrainCellData.retainedCells_subset
    {slope : ℝ → ℝ} {delta : ℝ}
    {cells : Finset (ℤ × ℤ × ℤ)}
    (data : PureWZ2PopularGlobalGrainCellData slope delta cells) :
    data.retainedCells ⊆ cells := by
  intro cell hcell
  rw [data.retained_eq] at hcell
  rcases Finset.mem_biUnion.mp hcell with ⟨label, _, hcellFiber⟩
  exact (mem_pureWZ2GlobalGrainFiber slope delta cells label cell).mp
    hcellFiber |>.1

theorem PureWZ2PopularGlobalGrainCellData.refined_union_eq
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {slope : ℝ → ℝ}
    {cells : Finset (ℤ × ℤ × ℤ)}
    (data : PureWZ2PopularGlobalGrainCellData slope delta cells)
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hcells : ∀ cell ∈ cells,
      cell ∈ wz1PaperActiveCells shading hdelta) :
    data.refinedShading (shading := shading).union =
      wz2RetainedCellsUnion delta data.retainedCells := by
  exact wz2RefinedShading_union_eq
    (shading := shading) (retainedFineCells := data.retainedCells)
    hcubical hdelta
    (fun (fineCell : ℤ × ℤ × ℤ) hfineCell =>
      hcells fineCell
        (data.retainedCells_subset hfineCell))

theorem PureWZ2PopularGlobalGrainCellData.refined_union_volume
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {slope : ℝ → ℝ}
    {cells : Finset (ℤ × ℤ × ℤ)}
    (data : PureWZ2PopularGlobalGrainCellData slope delta cells)
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hcells : ∀ cell ∈ cells,
      cell ∈ wz1PaperActiveCells shading hdelta) :
    volume (data.refinedShading (shading := shading).union) =
      (data.retainedCells.card : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  rw [data.refined_union_eq hdelta hcubical hcells]
  exact wz1PaperGridCube_volume_biUnion hdelta data.retainedCells

/-- Total incidence mass of a whole-cell restriction is the cellwise sum. -/
theorem wz2RefinedShading_mass_eq_sum_cells
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (cells : Finset (ℤ × ℤ × ℤ)) :
    (wz2RefinedShading shading cells).mass =
      ∑ cell ∈ cells,
        ∑ index : Fin family.card,
          volume (shading.carrier index ∩
            wz1PaperGridCube delta cell) := by
  have hcarrier :
      ∀ index : Fin family.card,
        (wz2RefinedShading shading cells).carrier index =
          ⋃ cell ∈ cells,
            shading.carrier index ∩ wz1PaperGridCube delta cell := by
    intro index
    ext point
    simp only [wz2RefinedShading_carrier, Set.mem_inter_iff,
      wz2RetainedCellsUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨hcarrier, cell, hcell⟩
      rcases hcell with ⟨hcellMem, hpointCell⟩
      exact ⟨cell, ⟨hcellMem, hcarrier, hpointCell⟩⟩
    · rintro ⟨cell, hcellMem, hcarrier, hpointCell⟩
      exact ⟨hcarrier, ⟨cell, hcellMem, hpointCell⟩⟩
  have hcarrierVolume :
      ∀ index : Fin family.card,
        volume ((wz2RefinedShading shading cells).carrier index) =
          ∑ cell ∈ cells,
            volume (shading.carrier index ∩
              wz1PaperGridCube delta cell) := by
    intro index
    rw [hcarrier index]
    apply MeasureTheory.measure_biUnion_finset
    · intro first _ second _ hne
      exact (wz1PaperGridCube_disjoint hne).mono
        Set.inter_subset_right Set.inter_subset_right
    · intro cell _
      exact (shading.measurable_carrier index).inter
        (wz1PaperGridCube_measurable cell)
  calc
    (wz2RefinedShading shading cells).mass =
        ∑ index : Fin family.card,
          ∑ cell ∈ cells,
            volume (shading.carrier index ∩
              wz1PaperGridCube delta cell) := by
      apply Finset.sum_congr rfl
      intro index _
      exact hcarrierVolume index
    _ = _ := by rw [Finset.sum_comm]

/-- Incidence mass in one active whole cell under constant multiplicity. -/
theorem wholeCell_incidence_mass_bounds
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    {lower upper : ℕ}
    (hconstant : shading.HasConstantMultiplicity lower upper)
    (hdelta : 0 < delta)
    {cell : ℤ × ℤ × ℤ}
    (hcell : cell ∈ wz1PaperActiveCells shading hdelta) :
    (lower : ENNReal) * volume (wz1PaperGridCube delta cell) ≤
        ∑ index : Fin family.card,
          volume (shading.carrier index ∩
            wz1PaperGridCube delta cell) ∧
      (∑ index : Fin family.card,
          volume (shading.carrier index ∩
            wz1PaperGridCube delta cell)) ≤
        (upper : ENNReal) * volume (wz1PaperGridCube delta cell) := by
  let center := pureWZ2PaperCellCenter delta cell
  have hcenterCell : center ∈ wz1PaperGridCube delta cell :=
    pureWZ2PaperCellCenter_mem hdelta cell
  have hcenterUnion : center ∈ shading.union := by
    have heq := hcubical.inter_activeCell_eq hdelta hcell
    have hmem : center ∈ shading.union ∩ wz1PaperGridCube delta cell := by
      rw [heq]
      exact hcenterCell
    exact hmem.1
  have hmultiplicity := hconstant center hcenterUnion
  have hcarrierEq :
      ∀ index : Fin family.card,
        shading.carrier index ∩ wz1PaperGridCube delta cell =
          if center ∈ shading.carrier index then
            wz1PaperGridCube delta cell else ∅ := by
    intro index
    by_cases hmem : center ∈ shading.carrier index
    · rw [if_pos hmem]
      apply Set.inter_eq_right.mpr
      intro point hpointCell
      have hsame :
          wz1PaperGridIndex delta center =
            wz1PaperGridIndex delta point := by
        rw [(mem_wz1PaperGridCube delta cell center).mp hcenterCell,
          (mem_wz1PaperGridCube delta cell point).mp hpointCell]
      exact (hcubical.carrier_mem_iff_of_same_cell index hsame).mp hmem
    · rw [if_neg hmem]
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hnonempty
      rcases hnonempty with ⟨point, hpointCarrier, hpointCell⟩
      have hsame :
          wz1PaperGridIndex delta point =
            wz1PaperGridIndex delta center := by
        rw [(mem_wz1PaperGridCube delta cell point).mp hpointCell,
          (mem_wz1PaperGridCube delta cell center).mp hcenterCell]
      exact hmem
        ((hcubical.carrier_mem_iff_of_same_cell index hsame).mp
          hpointCarrier)
  have hsumEq :
      (∑ index : Fin family.card,
          volume (shading.carrier index ∩
            wz1PaperGridCube delta cell)) =
        (shading.pointMultiplicity center : ENNReal) *
          volume (wz1PaperGridCube delta cell) := by
    classical
    rw [show shading.pointMultiplicity center =
        (Finset.univ.filter fun index : Fin family.card =>
          center ∈ shading.carrier index).card by rfl]
    calc
      (∑ index : Fin family.card,
          volume (shading.carrier index ∩
            wz1PaperGridCube delta cell)) =
          ∑ index : Fin family.card,
            if center ∈ shading.carrier index then
              volume (wz1PaperGridCube delta cell) else 0 := by
        apply Finset.sum_congr rfl
        intro index _
        rw [hcarrierEq index]
        split_ifs <;> simp
      _ = ((Finset.univ.filter fun index : Fin family.card =>
            center ∈ shading.carrier index).card : ENNReal) *
          volume (wz1PaperGridCube delta cell) := by
        rw [Finset.sum_ite]
        simp [Finset.sum_const]
  rw [hsumEq]
  constructor <;> gcongr
  · exact_mod_cast hmultiplicity.1
  · exact_mod_cast hmultiplicity.2

/-- Every kept label has at least the retained average up to factor two. -/
theorem PureWZ2PopularGlobalGrainCellData.fiber_card_lower
    {slope : ℝ → ℝ} {delta : ℝ}
    {cells : Finset (ℤ × ℤ × ℤ)}
    (data : PureWZ2PopularGlobalGrainCellData slope delta cells)
    (label : ℤ × ℤ) (hlabel : label ∈ data.keptLabels) :
    data.retainedCells.card ≤
      2 * data.keptLabels.card *
        (pureWZ2GlobalGrainFiber slope delta cells label).card := by
  have hsum :
      data.retainedCells.card =
        ∑ other ∈ data.keptLabels,
          (pureWZ2GlobalGrainFiber slope delta cells other).card := by
    rw [data.retained_eq]
    apply Finset.card_biUnion
    intro first _ second _ hne
    exact pureWZ2GlobalGrainFiber_disjoint slope delta cells hne
  rw [hsum]
  calc
    ∑ other ∈ data.keptLabels,
          (pureWZ2GlobalGrainFiber slope delta cells other).card
        ≤ ∑ _other ∈ data.keptLabels,
            2 * (pureWZ2GlobalGrainFiber slope delta cells label).card := by
          exact Finset.sum_le_sum fun other hother =>
            data.fiber_uniform other hother label hlabel
    _ = 2 * data.keptLabels.card *
          (pureWZ2GlobalGrainFiber slope delta cells label).card := by
      simp [Finset.sum_const]
      ring

theorem PureWZ2PopularGlobalGrainCellData.keptLabels_card_le
    {slope : ℝ → ℝ} {delta : ℝ}
    {cells : Finset (ℤ × ℤ × ℤ)}
    (data : PureWZ2PopularGlobalGrainCellData slope delta cells) :
    data.keptLabels.card ≤
      (pureWZ2GlobalGrainLabels slope delta cells).card :=
  Finset.card_le_card data.keptLabels_subset

/-- Absolute cell count in each popular global grain from any label bound. -/
theorem PureWZ2PopularGlobalGrainCellData.fiber_card_lower_of_labelBound
    {slope : ℝ → ℝ} {delta : ℝ}
    {cells : Finset (ℤ × ℤ × ℤ)}
    (data : PureWZ2PopularGlobalGrainCellData slope delta cells)
    {labelBound : ℕ}
    (hlabels :
      (pureWZ2GlobalGrainLabels slope delta cells).card ≤ labelBound)
    (label : ℤ × ℤ) (hlabel : label ∈ data.keptLabels) :
    data.retainedCells.card ≤
      2 * labelBound *
        (pureWZ2GlobalGrainFiber slope delta cells label).card := by
  exact (data.fiber_card_lower label hlabel).trans
    (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left 2
        (data.keptLabels_card_le.trans hlabels)))

/-- Scalar values attached to active cells on one fixed z-layer. -/
def pureWZ2GlobalValuesAtHeight
    (slope : ℝ → ℝ) (delta : ℝ)
    (cells : Finset (ℤ × ℤ × ℤ)) (heightIndex : ℤ) : Finset ℝ :=
  (cells.filter fun cell => cell.2.2 = heightIndex).image fun cell =>
    inner ℝ (pureWZ2PaperCellCenter delta cell)
      (globalGrainDirection
        (slope ((pureWZ2PaperCellCenter delta cell) 2)))

/-- The scalar-bin image at one height is the second-coordinate label image. -/
theorem pureWZ2_globalBinsAtHeight_eq
    (slope : ℝ → ℝ) {delta : ℝ} (hdelta : 0 < delta)
    (cells : Finset (ℤ × ℤ × ℤ)) (heightIndex : ℤ) :
    wz1Lemma23ScalarBins delta
        (pureWZ2GlobalValuesAtHeight slope delta cells heightIndex) =
      (cells.filter fun cell => cell.2.2 = heightIndex).image
        fun cell => (pureWZ2GlobalGrainLabel slope delta cell).2 := by
  ext scalarBin
  simp only [wz1Lemma23ScalarBins, pureWZ2GlobalValuesAtHeight,
    Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨value, ⟨cell, ⟨hcell, hheight⟩, rfl⟩, rfl⟩
    refine ⟨cell, ⟨hcell, hheight⟩, ?_⟩
    simp [pureWZ2GlobalGrainLabel, hheight]
  · rintro ⟨cell, ⟨hcell, hheight⟩, rfl⟩
    refine ⟨inner ℝ (pureWZ2PaperCellCenter delta cell)
        (globalGrainDirection
          (slope ((pureWZ2PaperCellCenter delta cell) 2))), ?_, ?_⟩
    · exact ⟨cell, ⟨hcell, hheight⟩, rfl⟩
    · simp [pureWZ2GlobalGrainLabel, hheight]

/-- Occupied height indices of one active-cell family. -/
def pureWZ2GlobalGrainHeights
    (cells : Finset (ℤ × ℤ × ℤ)) : Finset ℤ :=
  cells.image fun cell => cell.2.2

/-- Total global labels are bounded by height count times the worst bin count. -/
theorem pureWZ2_globalLabels_card_le_height_mul_bins
    (slope : ℝ → ℝ) (delta : ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (binBound : ℕ)
    (hbin : ∀ heightIndex ∈ pureWZ2GlobalGrainHeights cells,
      ((cells.filter fun cell => cell.2.2 = heightIndex).image
        fun cell => (pureWZ2GlobalGrainLabel slope delta cell).2).card ≤
          binBound) :
    (pureWZ2GlobalGrainLabels slope delta cells).card ≤
      (pureWZ2GlobalGrainHeights cells).card * binBound := by
  let labelsAtHeight : ℤ → Finset (ℤ × ℤ) := fun heightIndex =>
    (cells.filter fun cell => cell.2.2 = heightIndex).image
      (pureWZ2GlobalGrainLabel slope delta)
  have hcover :
      pureWZ2GlobalGrainLabels slope delta cells ⊆
        (pureWZ2GlobalGrainHeights cells).biUnion labelsAtHeight := by
    intro label hlabel
    rcases (mem_pureWZ2GlobalGrainLabels slope delta cells label).mp hlabel with
      ⟨cell, hcell, rfl⟩
    let heightIndex := cell.2.2
    have hheight : heightIndex ∈ pureWZ2GlobalGrainHeights cells :=
      Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
    exact Finset.mem_biUnion.mpr
      ⟨heightIndex, hheight, Finset.mem_image.mpr
        ⟨cell, Finset.mem_filter.mpr ⟨hcell, rfl⟩, rfl⟩⟩
  calc
    (pureWZ2GlobalGrainLabels slope delta cells).card
        ≤ ((pureWZ2GlobalGrainHeights cells).biUnion
            labelsAtHeight).card := Finset.card_le_card hcover
    _ ≤ ∑ heightIndex ∈ pureWZ2GlobalGrainHeights cells,
          (labelsAtHeight heightIndex).card := Finset.card_biUnion_le
    _ ≤ ∑ _heightIndex ∈ pureWZ2GlobalGrainHeights cells, binBound := by
      apply Finset.sum_le_sum
      intro heightIndex hheight
      have hfst :
          ∀ label ∈ labelsAtHeight heightIndex, label.1 = heightIndex := by
        intro label hlabel
        rcases Finset.mem_image.mp hlabel with
          ⟨cell, hcell, rfl⟩
        simpa [pureWZ2GlobalGrainLabel] using
          (Finset.mem_filter.mp hcell).2
      have hinj : Set.InjOn Prod.snd
          (labelsAtHeight heightIndex : Set (ℤ × ℤ)) := by
        intro first hfirst second hsecond hsnd
        apply Prod.ext
        · rw [hfst first hfirst, hfst second hsecond]
        · exact hsnd
      have hcardImage :
          (labelsAtHeight heightIndex).card =
            ((labelsAtHeight heightIndex).image Prod.snd).card :=
        (Finset.card_image_of_injOn hinj).symm
      rw [hcardImage]
      have himage :
          (labelsAtHeight heightIndex).image Prod.snd =
            (cells.filter fun cell => cell.2.2 = heightIndex).image
              fun cell => (pureWZ2GlobalGrainLabel slope delta cell).2 := by
        simp [labelsAtHeight, Finset.image_image, Function.comp_def]
      rw [himage]
      exact hbin heightIndex hheight
    _ = (pureWZ2GlobalGrainHeights cells).card * binBound := by
      simp [Finset.sum_const]

/-- ENNReal-valued version, avoiding a ceiling detour in parameter budgets. -/
theorem pureWZ2_globalLabels_enncard_le_height_mul_bins
    (slope : ℝ → ℝ) (delta : ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (binBound : ENNReal)
    (hbin : ∀ heightIndex ∈ pureWZ2GlobalGrainHeights cells,
      (((cells.filter fun cell => cell.2.2 = heightIndex).image
        fun cell => (pureWZ2GlobalGrainLabel slope delta cell).2).card :
          ENNReal) ≤ binBound) :
    ((pureWZ2GlobalGrainLabels slope delta cells).card : ENNReal) ≤
      ((pureWZ2GlobalGrainHeights cells).card : ENNReal) * binBound := by
  let labelsAtHeight : ℤ → Finset (ℤ × ℤ) := fun heightIndex =>
    (cells.filter fun cell => cell.2.2 = heightIndex).image
      (pureWZ2GlobalGrainLabel slope delta)
  have hcover :
      pureWZ2GlobalGrainLabels slope delta cells ⊆
        (pureWZ2GlobalGrainHeights cells).biUnion labelsAtHeight := by
    intro label hlabel
    rcases (mem_pureWZ2GlobalGrainLabels slope delta cells label).mp hlabel with
      ⟨cell, hcell, rfl⟩
    exact Finset.mem_biUnion.mpr
      ⟨cell.2.2, Finset.mem_image.mpr ⟨cell, hcell, rfl⟩,
        Finset.mem_image.mpr
          ⟨cell, Finset.mem_filter.mpr ⟨hcell, rfl⟩, rfl⟩⟩
  have hcardNat :
      (pureWZ2GlobalGrainLabels slope delta cells).card ≤
        ((pureWZ2GlobalGrainHeights cells).biUnion labelsAtHeight).card :=
    Finset.card_le_card hcover
  have hcard :
      ((pureWZ2GlobalGrainLabels slope delta cells).card : ENNReal) ≤
        (((pureWZ2GlobalGrainHeights cells).biUnion labelsAtHeight).card :
          ENNReal) := by exact_mod_cast hcardNat
  calc
    ((pureWZ2GlobalGrainLabels slope delta cells).card : ENNReal)
        ≤ (((pureWZ2GlobalGrainHeights cells).biUnion labelsAtHeight).card :
            ENNReal) := hcard
    _ ≤ ∑ heightIndex ∈ pureWZ2GlobalGrainHeights cells,
          ((labelsAtHeight heightIndex).card : ENNReal) := by
      exact_mod_cast Finset.card_biUnion_le
        (s := pureWZ2GlobalGrainHeights cells) (t := labelsAtHeight)
    _ ≤ ∑ _heightIndex ∈ pureWZ2GlobalGrainHeights cells, binBound := by
      apply Finset.sum_le_sum
      intro heightIndex hheight
      have hfst :
          ∀ label ∈ labelsAtHeight heightIndex, label.1 = heightIndex := by
        intro label hlabel
        rcases Finset.mem_image.mp hlabel with ⟨cell, hcell, rfl⟩
        simpa [pureWZ2GlobalGrainLabel] using
          (Finset.mem_filter.mp hcell).2
      have hinj : Set.InjOn Prod.snd
          (labelsAtHeight heightIndex : Set (ℤ × ℤ)) := by
        intro first hfirst second hsecond hsnd
        apply Prod.ext
        · rw [hfst first hfirst, hfst second hsecond]
        · exact hsnd
      have hcardImage :
          (labelsAtHeight heightIndex).card =
            ((labelsAtHeight heightIndex).image Prod.snd).card :=
        (Finset.card_image_of_injOn hinj).symm
      rw [hcardImage]
      have himage :
          (labelsAtHeight heightIndex).image Prod.snd =
            (cells.filter fun cell => cell.2.2 = heightIndex).image
              fun cell => (pureWZ2GlobalGrainLabel slope delta cell).2 := by
        simp [labelsAtHeight, Finset.image_image, Function.comp_def]
      rw [himage]
      exact hbin heightIndex hheight
    _ = ((pureWZ2GlobalGrainHeights cells).card : ENNReal) * binBound := by
      simp [Finset.sum_const]

/-- Active literal cells have centers in the cubical shading union. -/
theorem pureWZ2_activeCellCenter_mem_union
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading shading)
    {cell : ℤ × ℤ × ℤ}
    (hcell : cell ∈ wz1PaperActiveCells shading hdelta) :
    pureWZ2PaperCellCenter delta cell ∈ shading.union := by
  have hcellSubset : wz1PaperGridCube delta cell ⊆ shading.union :=
    Set.inter_eq_right.mp
      (hcubical.inter_activeCell_eq hdelta hcell)
  exact hcellSubset (pureWZ2PaperCellCenter_mem hdelta cell)

/-- Scalar cell-center values at one height belong to the exact-slice AD set. -/
theorem pureWZ2_globalValuesAtHeight_subset_projection
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading shading)
    (slope : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (hcells : ∀ cell ∈ cells,
      cell ∈ wz1PaperActiveCells shading hdelta)
    (heightIndex : ℤ) :
    (pureWZ2GlobalValuesAtHeight slope delta cells heightIndex : Set ℝ) ⊆
      scalarProjection
        (globalGrainDirection
          (slope (((heightIndex : ℝ) + 1 / 2) * delta)))
        (horizontalSlice shading.union
          (((heightIndex : ℝ) + 1 / 2) * delta)) := by
  intro value hvalue
  rcases Finset.mem_image.mp hvalue with
    ⟨cell, hcell, rfl⟩
  have hsource := (Finset.mem_filter.mp hcell).1
  have hheight := (Finset.mem_filter.mp hcell).2
  let center := pureWZ2PaperCellCenter delta cell
  have hcenterUnion : center ∈ shading.union :=
    pureWZ2_activeCellCenter_mem_union hdelta hcubical (hcells cell hsource)
  have hcenterHeight :
      center 2 = ((heightIndex : ℝ) + 1 / 2) * delta := by
    simp [center, hheight]
  refine ⟨center, ⟨hcenterUnion, hcenterHeight⟩, ?_⟩
  rw [hcenterHeight]

/-- Per-height global scalar-bin count from the exact-slice AD certificate. -/
theorem pureWZ2_globalBinsAtHeight_card_bound
    {sigma loss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
    {shading : WZ1PaperTubeShading cfg.family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hsub : ∀ index, shading.carrier index ⊆ cfg.shading.carrier index)
    (cells : Finset (ℤ × ℤ × ℤ))
    (hcells : ∀ cell ∈ cells,
      cell ∈ wz1PaperActiveCells shading cfg.extremal.delta_pos)
    (heightIndex : ℤ)
    (hheight : ((heightIndex : ℝ) + 1 / 2) * delta ∈
      Set.Icc (-1 : ℝ) 1) :
    (((cells.filter fun cell => cell.2.2 = heightIndex).image
      fun cell =>
        (pureWZ2GlobalGrainLabel cfg.globalGrains.slope delta cell).2).card :
          ENNReal) ≤
      24 * Kakeya.realRpowENN delta (-loss) *
        Kakeya.realRpowENN (1 / delta) (1 - sigma) := by
  let z : ℝ := ((heightIndex : ℝ) + 1 / 2) * delta
  let projectionSet : Set ℝ :=
    scalarProjection
      (globalGrainDirection (cfg.globalGrains.slope z))
      (horizontalSlice cfg.shading.union z)
  have hpaper := cfg.globalGrains.global_ad_slope z hheight
  have hbounded : projectionSet ⊆ Set.Icc (-4 : ℝ) 4 := by
    intro value hvalue
    rcases hvalue with ⟨point, hpoint, rfl⟩
    rcases hpoint.1 with ⟨index, hcarrier⟩
    have hbox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
      (cfg.shading.subset_body index hcarrier).2
    have hcoords : |point 0| ≤ 1 ∧ |point 1| ≤ 1 := by
      simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
      norm_num at hbox
      exact ⟨hbox.1, hbox.2.1⟩
    have hslope : |cfg.globalGrains.slope z| ≤ 1 :=
      (cfg.globalGrains.slope_normalized z hheight).1
    change inner ℝ point
      (globalGrainDirection (cfg.globalGrains.slope z)) ∈ Set.Icc (-4) 4
    rw [pureWZ2_inner_globalDirection]
    have habs :
        |point 0 + cfg.globalGrains.slope z * point 1| ≤ 2 := by
      calc
        |point 0 + cfg.globalGrains.slope z * point 1|
            ≤ |point 0| +
                |cfg.globalGrains.slope z| * |point 1| := by
              calc
                |point 0 + cfg.globalGrains.slope z * point 1|
                    ≤ |point 0| +
                        |cfg.globalGrains.slope z * point 1| :=
                      abs_add_le _ _
                _ = _ := by rw [abs_mul]
        _ ≤ 2 := by nlinarith [abs_nonneg (cfg.globalGrains.slope z)]
    exact ⟨by linarith [abs_le.mp habs], by linarith [abs_le.mp habs]⟩
  have hisad : IsADSet1 projectionSet delta (1 - sigma)
      (2 * Kakeya.realRpowENN delta (-loss)) :=
    hpaper.toIsADSet1 hbounded
  let values := pureWZ2GlobalValuesAtHeight
    cfg.globalGrains.slope delta cells heightIndex
  have hvaluesSource : (values : Set ℝ) ⊆
      scalarProjection
        (globalGrainDirection (cfg.globalGrains.slope z))
        (horizontalSlice shading.union z) := by
    simpa [values, z] using
      pureWZ2_globalValuesAtHeight_subset_projection
        cfg.extremal.delta_pos hcubical cfg.globalGrains.slope
        cells hcells heightIndex
  have hunionSub : shading.union ⊆ cfg.shading.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index, hsub index hpoint⟩
  have hvalues : (values : Set ℝ) ⊆ projectionSet :=
    hvaluesSource.trans (Set.image_mono
      (Set.inter_subset_inter hunionSub (Set.Subset.rfl)))
  have hbins := wz1_lemma23_ad_bin_count delta (1 - sigma)
    (2 * Kakeya.realRpowENN delta (-loss)) projectionSet values
    hisad cfg.extremal.delta_le_one hvalues
  rw [pureWZ2_globalBinsAtHeight_eq
    cfg.globalGrains.slope cfg.extremal.delta_pos cells heightIndex] at hbins
  convert hbins using 1 <;> ring

/-- Real center heights occupied by a cell family. -/
def pureWZ2GlobalGrainHeightValues
    (delta : ℝ) (cells : Finset (ℤ × ℤ × ℤ)) : Finset ℝ :=
  (pureWZ2GlobalGrainHeights cells).image fun (heightIndex : ℤ) =>
    ((heightIndex : ℝ) + 1 / 2) * delta

private theorem pureWZ2_heightValue_injective
    {delta : ℝ} (hdelta : 0 < delta) :
    Function.Injective
      (fun heightIndex : ℤ => ((heightIndex : ℝ) + 1 / 2) * delta) := by
  intro first second heq
  have hcast : (first : ℝ) = (second : ℝ) := by
    nlinarith
  exact_mod_cast hcast

theorem pureWZ2_globalGrainHeightValues_card
    {delta : ℝ} (hdelta : 0 < delta)
    (cells : Finset (ℤ × ℤ × ℤ)) :
    (pureWZ2GlobalGrainHeightValues delta cells).card =
      (pureWZ2GlobalGrainHeights cells).card := by
  exact Finset.card_image_of_injective _
    (pureWZ2_heightValue_injective hdelta)

/-- Active cells inside one selected slab occupy at most `|J|/delta + 2` layers. -/
theorem pureWZ2_globalGrainHeights_card_bound
    {delta : ℝ} (hdelta : 0 < delta)
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (cells : Finset (ℤ × ℤ × ℤ))
    (hcells : ∀ cell ∈ cells,
      cell ∈ wz1PaperActiveCells shading hdelta)
    {left right : ℝ}
    (hordered : left < right)
    (hinSlab : ∀ index, shading.carrier index ⊆
      horizontalSlab left right) :
    ((pureWZ2GlobalGrainHeights cells).card : ℝ) ≤
      (right - left) / delta + 2 := by
  let values := pureWZ2GlobalGrainHeightValues delta cells
  by_cases hvalues : values = ∅
  · have hheights : pureWZ2GlobalGrainHeights cells = ∅ := by
      by_contra hne
      rcases Finset.nonempty_iff_ne_empty.mpr hne with ⟨heightIndex, hheight⟩
      have : ((heightIndex : ℝ) + 1 / 2) * delta ∈ values :=
        Finset.mem_image.mpr ⟨heightIndex, hheight, rfl⟩
      rw [hvalues] at this
      simp at this
    simp [hheights]
    have hnonneg : 0 ≤ (right - left) / delta := by positivity
    linarith
  · have hnonempty : values.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hvalues
    have hrange :
        ∀ value ∈ values, left - delta / 2 ≤ value ∧
          value ≤ right + delta / 2 := by
      intro value hvalue
      rcases Finset.mem_image.mp hvalue with
        ⟨heightIndex, hheight, rfl⟩
      rcases Finset.mem_image.mp hheight with
        ⟨cell, hcell, hcellHeight⟩
      rcases ((mem_wz1PaperActiveCells shading hdelta cell).mp
        (hcells cell hcell)).2 with ⟨point, hpointUnion, hpointCell⟩
      rcases hpointUnion with ⟨index, hpointCarrier⟩
      have hslab := hinSlab index hpointCarrier
      have hclose := pureWZ2_point_close_to_cellCenter hdelta hpointCell 2
      have hcenter :
          (pureWZ2PaperCellCenter delta cell) 2 =
            ((heightIndex : ℝ) + 1 / 2) * delta := by
        simp [hcellHeight]
      rw [hcenter] at hclose
      have habs := abs_le.mp hclose
      constructor <;> linarith [hslab.1, hslab.2]
    have hseparated :
        ∀ first ∈ values, ∀ second ∈ values, first ≠ second →
          delta ≤ |first - second| := by
      intro first hfirst second hsecond hne
      rcases Finset.mem_image.mp hfirst with
        ⟨firstIndex, _, rfl⟩
      rcases Finset.mem_image.mp hsecond with
        ⟨secondIndex, _, rfl⟩
      have hindexNe : firstIndex ≠ secondIndex := by
        intro heq
        exact hne (by rw [heq])
      have hint : (1 : ℝ) ≤ |((firstIndex - secondIndex : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hindexNe)
      have hcast :
          ((firstIndex - secondIndex : ℤ) : ℝ) =
            (firstIndex : ℝ) - (secondIndex : ℝ) := by norm_cast
      have hformula :
          ((firstIndex : ℝ) + 1 / 2) * delta -
              ((secondIndex : ℝ) + 1 / 2) * delta =
            ((firstIndex - secondIndex : ℤ) : ℝ) * delta := by
        rw [hcast]
        ring
      rw [hformula, abs_mul, abs_of_pos hdelta]
      nlinarith
    have hcount := lemma23_separated_real_finset_card_le
      hdelta hnonempty hrange hseparated
    rw [pureWZ2_globalGrainHeightValues_card hdelta cells] at hcount
    calc
      ((pureWZ2GlobalGrainHeights cells).card : ℝ)
          ≤ ((right + delta / 2) - (left - delta / 2)) / delta + 1 :=
        hcount
      _ = (right - left) / delta + 2 := by
        field_simp [hdelta.ne']
        ring

/-- Complete paper output of Section 6 Refinement 1 at one selected scale. -/
structure PureWZ2PopularGlobalGrainData
    {sigma loss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData
      cfg.shading sigma loss scale) where
  multiplicityBand : LargeSlopeCroppedMultiplicityBandData
    scaleData.slabShading scaleData.slabLeft scaleData.slabRight
  activeCells : Finset (ℤ × ℤ × ℤ)
  activeCells_eq :
    activeCells = wz1PaperActiveCells
      multiplicityBand.band cfg.extremal.delta_pos
  popular : PureWZ2PopularGlobalGrainCellData
    cfg.globalGrains.slope delta activeCells
  F1 : WZ1PaperTubeShading cfg.family
  F1_eq : F1 = popular.refinedShading
    (shading := multiplicityBand.band)
  F1_cubical : WZ1PaperIsCubicalShading F1
  F1_in_slab :
    ∀ index, F1.carrier index ⊆
      horizontalSlab scaleData.slabLeft scaleData.slabRight
  F1_mass :
    F1.mass =
      ∑ cell ∈ popular.retainedCells,
        ∑ index : Fin cfg.family.card,
          volume (multiplicityBand.band.carrier index ∩
            wz1PaperGridCube delta cell)
  total_label_bound :
    ((pureWZ2GlobalGrainLabels cfg.globalGrains.slope delta activeCells).card :
        ENNReal) ≤
      ENNReal.ofReal (scale.1 / delta + 2) *
        (24 * Kakeya.realRpowENN delta (-loss) *
          Kakeya.realRpowENN (1 / delta) (1 - sigma))
  /-- Every popular label occupies one constant-4 literal global grain. -/
  label_anchor : ∀ label, label ∈ popular.keptLabels → ℤ × ℤ × ℤ
  label_anchor_mem :
    ∀ label (hlabel : label ∈ popular.keptLabels),
      label_anchor label hlabel ∈ pureWZ2GlobalGrainFiber
        cfg.globalGrains.slope delta activeCells label
  label_grain_containment :
    ∀ label (hlabel : label ∈ popular.keptLabels),
      ⋃ cell ∈ pureWZ2GlobalGrainFiber
          cfg.globalGrains.slope delta activeCells label,
        wz1PaperGridCube delta cell ⊆
      pureWZ2GlobalGrainWithConstant 4 cfg.globalGrains.slope delta
        (pureWZ2PaperCellCenter delta
          (label_anchor label hlabel))
  label_volume :
    ∀ label ∈ popular.keptLabels,
      volume
          (⋃ cell ∈ pureWZ2GlobalGrainFiber
              cfg.globalGrains.slope delta activeCells label,
            wz1PaperGridCube delta cell) =
        ((pureWZ2GlobalGrainFiber
          cfg.globalGrains.slope delta activeCells label).card : ENNReal) *
          ENNReal.ofReal (delta ^ 3)

/-- Assemble Refinement 1 from the selected whole-cell slab. -/
theorem pureWZ2_popularGlobalGrains
    {sigma loss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData
      cfg.shading sigma loss scale)
    (hbandNonempty : Nonempty
      (LargeSlopeCroppedMultiplicityBandData
        scaleData.slabShading scaleData.slabLeft scaleData.slabRight)) :
    Nonempty (PureWZ2PopularGlobalGrainData cfg scale scaleData) := by
  rcases hbandNonempty with ⟨multiplicityBand⟩
  let activeCells := wz1PaperActiveCells
    multiplicityBand.band cfg.extremal.delta_pos
  have hactiveNonempty : activeCells.Nonempty := by
    have hsourceMass : scaleData.slabShading.mass ≠ 0 := by
      have hfamily : 0 < cfg.family.enncard := by
        rw [show cfg.family.enncard = (cfg.family.card : ENNReal) by rfl]
        exact_mod_cast cfg.extremal.nonempty
      have hleft :
          0 < ENNReal.ofReal (Real.pi / 4) *
              Kakeya.realRpowENN delta (loss + 2) *
              cfg.family.enncard * ENNReal.ofReal scale.1 := by
        have hpi : 0 < ENNReal.ofReal (Real.pi / 4) :=
          ENNReal.ofReal_pos.mpr (by positivity)
        have hrpow : 0 < Kakeya.realRpowENN delta (loss + 2) := by
          simp [Kakeya.realRpowENN,
            Real.rpow_pos_of_pos cfg.extremal.delta_pos]
        have hscale : 0 < ENNReal.ofReal scale.1 :=
          ENNReal.ofReal_pos.mpr
            (cfg.extremal.delta_pos.trans_le scale.2.1)
        have hfirst := ENNReal.mul_pos hpi.ne' hrpow.ne'
        have hsecond := ENNReal.mul_pos hfirst.ne' hfamily.ne'
        exact ENNReal.mul_pos hsecond.ne' hscale.ne'
      exact (hleft.trans_le scaleData.slab_mass).ne'
    have hbandMass : multiplicityBand.band.mass ≠ 0 := by
      have hslabMass :
          paperShadedMassInSlab scaleData.slabShading
            scaleData.slabLeft scaleData.slabRight =
            scaleData.slabShading.mass := by
        apply Finset.sum_congr rfl
        intro index _
        rw [Set.inter_eq_left.mpr (scaleData.slab_in_slab index)]
      have hretained := multiplicityBand.slab_mass_retention
      rw [hslabMass] at hretained
      intro hzero
      have hbandSlabZero :
          paperShadedMassInSlab multiplicityBand.band
            scaleData.slabLeft scaleData.slabRight = 0 := by
        apply le_zero_iff.mp
        calc
          paperShadedMassInSlab multiplicityBand.band
              scaleData.slabLeft scaleData.slabRight
              ≤ multiplicityBand.band.mass := by
            apply Finset.sum_le_sum
            intro index _
            exact measure_mono Set.inter_subset_left
          _ = 0 := hzero
      have hquotZero :
          scaleData.slabShading.mass /
              ((Nat.log 2 cfg.family.card + 1 : ℕ) : ENNReal) = 0 :=
        le_zero_iff.mp (hretained.trans_eq hbandSlabZero)
      have hdenTop :
          ((Nat.log 2 cfg.family.card + 1 : ℕ) : ENNReal) ≠ ⊤ := by simp
      exact hsourceMass
        (((ENNReal.div_eq_zero_iff).mp hquotZero).resolve_right hdenTop)
    by_contra hempty
    have hactiveEmpty : activeCells = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hunionEmpty : multiplicityBand.band.union = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hnonempty
      rcases hnonempty with ⟨point, hpoint⟩
      rcases hpoint with ⟨index, hcarrier⟩
      have haxis := (multiplicityBand.band.subset_body index hcarrier).2
      have hcell : wz1PaperGridIndex delta point ∈ activeCells := by
        rw [mem_wz1PaperActiveCells]
        constructor
        · exact paper_point_gridIndex_in_window
            cfg.extremal.delta_pos haxis
        · exact ⟨point, ⟨index, hcarrier⟩,
            (mem_wz1PaperGridCube delta _ point).mpr rfl⟩
      rw [hactiveEmpty] at hcell
      simp at hcell
    have hmassZero : multiplicityBand.band.mass = 0 := by
      have hcarrierEmpty : ∀ index, multiplicityBand.band.carrier index = ∅ := by
        intro index
        apply Set.not_nonempty_iff_eq_empty.mp
        intro hnonempty
        rcases hnonempty with ⟨point, hpoint⟩
        have : point ∈ multiplicityBand.band.union := ⟨index, hpoint⟩
        rw [hunionEmpty] at this
        exact this
      simp [Kakeya.Streamlined.Shading.mass, hcarrierEmpty]
    exact hbandMass hmassZero
  rcases pureWZ2_select_popular_globalGrainCells
      cfg.globalGrains.slope delta activeCells hactiveNonempty with
    ⟨popular⟩
  let F1 := popular.refinedShading (shading := multiplicityBand.band)
  have hactive : ∀ cell ∈ activeCells,
      cell ∈ wz1PaperActiveCells multiplicityBand.band cfg.extremal.delta_pos :=
    fun _ hcell => hcell
  have hF1Cubical : WZ1PaperIsCubicalShading F1 :=
    wz2RefinedShading_cubical multiplicityBand.band_cubical
  have hF1InSlab : ∀ index, F1.carrier index ⊆
      horizontalSlab scaleData.slabLeft scaleData.slabRight := by
    intro index
    exact (wz2RefinedShading_subshading index).trans
      ((multiplicityBand.band_subshading index).trans
        (scaleData.slab_in_slab index))
  have hF1Mass := wz2RefinedShading_mass_eq_sum_cells
    multiplicityBand.band popular.retainedCells
  have hheightBound := pureWZ2_globalGrainHeights_card_bound
    cfg.extremal.delta_pos activeCells hactive
    scaleData.slab_ordered
    (fun index => (multiplicityBand.band_subshading index).trans
      (scaleData.slab_in_slab index))
  have hbinBound :
      ∀ heightIndex ∈ pureWZ2GlobalGrainHeights activeCells,
        (((activeCells.filter fun cell => cell.2.2 = heightIndex).image
          fun cell => (pureWZ2GlobalGrainLabel
            cfg.globalGrains.slope delta cell).2).card : ENNReal) ≤
          24 * Kakeya.realRpowENN delta (-loss) *
            Kakeya.realRpowENN (1 / delta) (1 - sigma) := by
    intro heightIndex hheightIndex
    rcases Finset.mem_image.mp hheightIndex with ⟨cell, hcell, hcellHeight⟩
    have hcenterUnion := pureWZ2_activeCellCenter_mem_union
      cfg.extremal.delta_pos multiplicityBand.band_cubical hcell
    have hcenterSlab :
        (pureWZ2PaperCellCenter delta cell) 2 ∈
          Set.Icc scaleData.slabLeft scaleData.slabRight := by
      rcases hcenterUnion with ⟨index, hcarrier⟩
      exact (scaleData.slab_in_slab index
        (multiplicityBand.band_subshading index hcarrier))
    have hheight :
        ((heightIndex : ℝ) + 1 / 2) * delta ∈ Set.Icc (-1 : ℝ) 1 := by
      have hcenterEq :
          (pureWZ2PaperCellCenter delta cell) 2 =
            ((heightIndex : ℝ) + 1 / 2) * delta := by
        simp [hcellHeight]
      rw [← hcenterEq]
      exact ⟨scaleData.slabLeft_mem.trans hcenterSlab.1,
        hcenterSlab.2.trans scaleData.slabRight_mem⟩
    exact pureWZ2_globalBinsAtHeight_card_bound cfg
      multiplicityBand.band_cubical
      (fun index => (multiplicityBand.band_subshading index).trans
        (scaleData.slab_subshading index))
      activeCells hactive heightIndex hheight
  have hlabelBoundBase := pureWZ2_globalLabels_enncard_le_height_mul_bins
    cfg.globalGrains.slope delta activeCells
    (24 * Kakeya.realRpowENN delta (-loss) *
      Kakeya.realRpowENN (1 / delta) (1 - sigma))
    hbinBound
  have hlabelBound :
      ((pureWZ2GlobalGrainLabels
        cfg.globalGrains.slope delta activeCells).card : ENNReal) ≤
        ENNReal.ofReal (scale.1 / delta + 2) *
          (24 * Kakeya.realRpowENN delta (-loss) *
            Kakeya.realRpowENN (1 / delta) (1 - sigma)) := by
    have hheightENN :
        ((pureWZ2GlobalGrainHeights activeCells).card : ENNReal) ≤
          ENNReal.ofReal (scale.1 / delta + 2) := by
      rw [← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_mono
      rw [scaleData.slab_width] at hheightBound
      exact hheightBound
    exact hlabelBoundBase.trans (mul_le_mul_right' hheightENN _)
  choose label_anchor hlabel_anchor using popular.fiber_nonempty
  have hanchorHeight : ∀ label (hlabel : label ∈ popular.keptLabels),
      (pureWZ2PaperCellCenter delta (label_anchor label hlabel)) 2 ∈
        Set.Icc (-1 : ℝ) 1 := by
    intro label hlabel
    have hanchorActive :=
      (mem_pureWZ2GlobalGrainFiber cfg.globalGrains.slope delta
        activeCells label (label_anchor label hlabel)).mp
        (hlabel_anchor label hlabel) |>.1
    have hcenterUnion := pureWZ2_activeCellCenter_mem_union
      cfg.extremal.delta_pos multiplicityBand.band_cubical hanchorActive
    rcases hcenterUnion with ⟨index, hcarrier⟩
    have hslab := scaleData.slab_in_slab index
      (multiplicityBand.band_subshading index hcarrier)
    exact ⟨scaleData.slabLeft_mem.trans hslab.1,
      hslab.2.trans scaleData.slabRight_mem⟩
  have hcontainment : ∀ label (hlabel : label ∈ popular.keptLabels),
      ⋃ cell ∈ pureWZ2GlobalGrainFiber
          cfg.globalGrains.slope delta activeCells label,
        wz1PaperGridCube delta cell ⊆
      pureWZ2GlobalGrainWithConstant 4 cfg.globalGrains.slope delta
        (pureWZ2PaperCellCenter delta (label_anchor label hlabel)) := by
    intro label hlabel point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
    have hcellLabel :
        pureWZ2GlobalGrainLabel cfg.globalGrains.slope delta cell = label :=
      (mem_pureWZ2GlobalGrainFiber cfg.globalGrains.slope delta
        activeCells label cell).mp hcell |>.2
    have hanchorLabel :
        pureWZ2GlobalGrainLabel cfg.globalGrains.slope delta
            (label_anchor label hlabel) = label :=
      (mem_pureWZ2GlobalGrainFiber cfg.globalGrains.slope delta
        activeCells label (label_anchor label hlabel)).mp
          (hlabel_anchor label hlabel) |>.2
    exact pureWZ2_same_label_cell_subset_globalGrain
      cfg.extremal.delta_pos cfg.globalGrains.slope
      cfg.globalGrains.slope_normalized (hanchorHeight label hlabel)
      (hcellLabel.trans hanchorLabel.symm)
      hpointCell
  have hlabelVolume : ∀ label ∈ popular.keptLabels,
      volume (⋃ cell ∈ pureWZ2GlobalGrainFiber
          cfg.globalGrains.slope delta activeCells label,
        wz1PaperGridCube delta cell) =
      ((pureWZ2GlobalGrainFiber cfg.globalGrains.slope delta
        activeCells label).card : ENNReal) * ENNReal.ofReal (delta ^ 3) := by
    intro label _
    rw [wz1PaperGridCube_volume_biUnion cfg.extremal.delta_pos,
      wz1PaperGridCube_volume_exact cfg.extremal.delta_pos]
  exact ⟨{
    multiplicityBand := multiplicityBand
    activeCells := activeCells
    activeCells_eq := rfl
    popular := popular
    F1 := F1
    F1_eq := rfl
    F1_cubical := hF1Cubical
    F1_in_slab := hF1InSlab
    F1_mass := hF1Mass
    total_label_bound := hlabelBound
    label_anchor := label_anchor
    label_anchor_mem := hlabel_anchor
    label_grain_containment := hcontainment
    label_volume := hlabelVolume
  }⟩

end Kakeya.Assouad

end
