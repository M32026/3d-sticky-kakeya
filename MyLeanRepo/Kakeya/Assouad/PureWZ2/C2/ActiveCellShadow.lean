import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Refinement
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGridCubeVolume
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GlobalSlicePackage

/-!
# Ordinary active-cell shadow of a cropped paper shading

The finite Lemma-23 graph only needs one ordinary tube direction attached to
each occupied whole cell.  A cubical paper shading supplies such a direction:
choose a genuinely shaded source tube meeting the cell.  Cubicality puts the
whole cell in that source carrier, and the cell fits inside a same-scale
ordinary tube centered on the cell with the chosen source direction.

The construction is proof-local.  It does not claim CWA, distinctness, or
extremality for the shadow family.  Its shaded union is exactly the original
cropped-paper shaded union.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- Center of a literal paper grid cell. -/
def pureWZ2PaperCellCenter
    (delta : ℝ) (cell : ℤ × ℤ × ℤ) : Point3 :=
  cellCorner delta cell + point3 (delta / 2) (delta / 2) (delta / 2)

/-- Every point of a positive-scale paper cell lies within `delta` of its center. -/
theorem dist_pureWZ2PaperCellCenter_le
    {delta : ℝ} (hdelta : 0 < delta)
    {cell : ℤ × ℤ × ℤ} {point : Point3}
    (hpoint : point ∈ wz1PaperGridCube delta cell) :
    dist point (pureWZ2PaperCellCenter delta cell) ≤ delta := by
  rw [wz1PaperGridCube_eq_Ico hdelta] at hpoint
  rcases hpoint with ⟨h0l, h0u, h1l, h1u, h2l, h2u⟩
  have hcoord : ∀ coordinate : Fin 3,
      |point coordinate - pureWZ2PaperCellCenter delta cell coordinate| ≤
        delta / 2 := by
    intro coordinate
    fin_cases coordinate
    · simp [pureWZ2PaperCellCenter, cellCorner,
        wz1PaperGridCubeTranslation, point3]
      rw [abs_le]
      constructor <;> linarith
    · simp [pureWZ2PaperCellCenter, cellCorner,
        wz1PaperGridCubeTranslation, point3]
      rw [abs_le]
      constructor <;> linarith
    · simp [pureWZ2PaperCellCenter, cellCorner,
        wz1PaperGridCubeTranslation, point3]
      rw [abs_le]
      constructor <;> linarith
  have hsq :
      dist point (pureWZ2PaperCellCenter delta cell) ^ 2 ≤
        3 * (delta / 2) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    have hsum :
        (∑ coordinate : Fin 3,
          (point coordinate -
            pureWZ2PaperCellCenter delta cell coordinate) ^ 2) ≤
          ∑ _coordinate : Fin 3, (delta / 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro coordinate _
      rw [← sq_abs]
      nlinarith [hcoord coordinate, abs_nonneg
        (point coordinate - pureWZ2PaperCellCenter delta cell coordinate)]
    simpa [Fin.sum_univ_succ, Real.dist_eq] using hsum
  have hsqrt3_lt_two : Real.sqrt 3 < 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sqrt_nonneg 3]
  have hdist :
      dist point (pureWZ2PaperCellCenter delta cell) ≤
        Real.sqrt 3 * (delta / 2) := by
    have hnonneg : 0 ≤ dist point (pureWZ2PaperCellCenter delta cell) :=
      dist_nonneg
    have hrhs : 0 ≤ Real.sqrt 3 * (delta / 2) := by positivity
    have hrhs_sq :
        (Real.sqrt 3 * (delta / 2)) ^ 2 =
          3 * (delta / 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
    nlinarith
  calc
    dist point (pureWZ2PaperCellCenter delta cell)
        ≤ Real.sqrt 3 * (delta / 2) := hdist
    _ ≤ delta := by
      have : Real.sqrt 3 ≤ 2 := hsqrt3_lt_two.le
      nlinarith

section Shadow

variable {delta : ℝ}
variable {source : Kakeya.Streamlined.TubeFamily delta}
variable (shading : WZ1PaperTubeShading source)
variable (hdelta : 0 < delta)

abbrev PureWZ2ActivePaperCell :=
  {cell : ℤ × ℤ × ℤ // cell ∈ wz1PaperActiveCells shading hdelta}

/-- One genuine shaded point in an active paper cell. -/
def pureWZ2ActiveCellPoint (cell : PureWZ2ActivePaperCell shading hdelta) :
    Point3 :=
  Classical.choose
    ((mem_wz1PaperActiveCells shading hdelta cell.1).mp cell.2).2

theorem pureWZ2ActiveCellPoint_mem_union
    (cell : PureWZ2ActivePaperCell shading hdelta) :
    pureWZ2ActiveCellPoint shading hdelta cell ∈ shading.union :=
  (Classical.choose_spec
    ((mem_wz1PaperActiveCells shading hdelta cell.1).mp cell.2).2).1

theorem pureWZ2ActiveCellPoint_mem_cell
    (cell : PureWZ2ActivePaperCell shading hdelta) :
    pureWZ2ActiveCellPoint shading hdelta cell ∈
      wz1PaperGridCube delta cell.1 :=
  (Classical.choose_spec
    ((mem_wz1PaperActiveCells shading hdelta cell.1).mp cell.2).2).2

/-- A source tube whose shaded carrier genuinely meets the active cell. -/
def pureWZ2ActiveCellSource (cell : PureWZ2ActivePaperCell shading hdelta) :
    Fin source.card :=
  Classical.choose (pureWZ2ActiveCellPoint_mem_union shading hdelta cell)

theorem pureWZ2ActiveCellPoint_mem_source
    (cell : PureWZ2ActivePaperCell shading hdelta) :
    pureWZ2ActiveCellPoint shading hdelta cell ∈
      shading.carrier (pureWZ2ActiveCellSource shading hdelta cell) :=
  Classical.choose_spec (pureWZ2ActiveCellPoint_mem_union shading hdelta cell)

theorem pureWZ2ActiveCell_subset_source
    (hcubical : WZ1PaperIsCubicalShading shading)
    (cell : PureWZ2ActivePaperCell shading hdelta) :
    wz1PaperGridCube delta cell.1 ⊆
      shading.carrier (pureWZ2ActiveCellSource shading hdelta cell) := by
  have hindex :
      wz1PaperGridIndex delta
          (pureWZ2ActiveCellPoint shading hdelta cell) = cell.1 :=
    (mem_wz1PaperGridCube delta cell.1 _).mp
      (pureWZ2ActiveCellPoint_mem_cell shading hdelta cell)
  simpa [hindex] using
    (hcubical _ _
      (pureWZ2ActiveCellPoint_mem_source shading hdelta cell))

/-- Same-scale ordinary tube centered on one active cell. -/
def pureWZ2ActiveCellTube (cell : PureWZ2ActivePaperCell shading hdelta) :
    Kakeya.DeltaTube delta where
  base := pureWZ2PaperCellCenter delta cell.1 -
    (1 / 2 : ℝ) • (source.tube
      (pureWZ2ActiveCellSource shading hdelta cell)).direction
  direction := (source.tube
    (pureWZ2ActiveCellSource shading hdelta cell)).direction
  direction_unit := (source.tube
    (pureWZ2ActiveCellSource shading hdelta cell)).direction_unit

theorem pureWZ2PaperCell_subset_activeCellTube
    (cell : PureWZ2ActivePaperCell shading hdelta) :
    wz1PaperGridCube delta cell.1 ⊆
      (pureWZ2ActiveCellTube shading hdelta cell).carrier := by
  intro point hpoint
  let tube := pureWZ2ActiveCellTube shading hdelta cell
  have hcenter : pureWZ2PaperCellCenter delta cell.1 ∈
      Kakeya.unitSegment tube.base tube.direction := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    dsimp [tube, pureWZ2ActiveCellTube]
    module
  exact Metric.mem_cthickening_of_dist_le
    point (pureWZ2PaperCellCenter delta cell.1) delta
    (Kakeya.unitSegment tube.base tube.direction) hcenter
    (dist_pureWZ2PaperCellCenter_le hdelta hpoint)

/-- Finite ordinary tube family indexed by active paper cells. -/
def pureWZ2ActiveCellFamily : Kakeya.Streamlined.TubeFamily delta where
  card := (wz1PaperActiveCells shading hdelta).card
  tube index :=
    pureWZ2ActiveCellTube shading hdelta
      ((wz1PaperActiveCells shading hdelta).equivFin.symm index)

/-- Ordinary shading whose pieces are exactly the active whole paper cells. -/
def pureWZ2ActiveCellShading :
    Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily shading hdelta) where
  carrier index :=
    wz1PaperGridCube delta
      (((wz1PaperActiveCells shading hdelta).equivFin.symm index).1)
  measurable_carrier index := wz1PaperGridCube_measurable _
  subset_body index :=
    pureWZ2PaperCell_subset_activeCellTube shading hdelta _

/-- Ordinary shading whose piece at an active cell is the part of the paper
shaded union lying in that cell.

Unlike `pureWZ2ActiveCellShading`, this construction does not require the
paper shading to contain whole cells.  It is the shadow needed after the
height-popularity restriction in Corollary 5.6. -/
def pureWZ2PartialActiveCellShading :
    Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily shading hdelta) where
  carrier index :=
    shading.union ∩
      wz1PaperGridCube delta
        (((wz1PaperActiveCells shading hdelta).equivFin.symm index).1)
  measurable_carrier index :=
    shading.union_measurable.inter (wz1PaperGridCube_measurable _)
  subset_body index := by
    intro point hpoint
    exact pureWZ2PaperCell_subset_activeCellTube shading hdelta _ hpoint.2

/-- The partial-cell shadow has exactly the same union as the paper shading. -/
theorem pureWZ2PartialActiveCellShading_union :
    (pureWZ2PartialActiveCellShading shading hdelta).union =
      shading.union := by
  apply Set.Subset.antisymm
  · rintro point ⟨index, hpoint⟩
    exact hpoint.1
  · intro point hpoint
    let cell := wz1PaperGridIndex delta point
    have hcellWindow :
        cell ∈ wz1PaperGridIndicesInWindow delta hdelta := by
      apply paper_point_gridIndex_in_window hdelta
      rcases hpoint with ⟨sourceIndex, hsourcePoint⟩
      have hcarrier :
          point ∈ wz1PaperTubeCarrier (source.tube sourceIndex) :=
        shading.subset_body sourceIndex hsourcePoint
      exact hcarrier.2
    have hpointCell : point ∈ wz1PaperGridCube delta cell := by
      exact (mem_wz1PaperGridCube delta cell point).mpr rfl
    have hcellActive : cell ∈ wz1PaperActiveCells shading hdelta := by
      exact (mem_wz1PaperActiveCells shading hdelta cell).mpr
        ⟨hcellWindow, ⟨point, hpoint, hpointCell⟩⟩
    let index : Fin (wz1PaperActiveCells shading hdelta).card :=
      (wz1PaperActiveCells shading hdelta).equivFin ⟨cell, hcellActive⟩
    refine ⟨index, hpoint, ?_⟩
    change point ∈ wz1PaperGridCube delta
      (((wz1PaperActiveCells shading hdelta).equivFin.symm index).1)
    simpa [index] using hpointCell

theorem pureWZ2ActiveCellShading_union
    (hcubical : WZ1PaperIsCubicalShading shading) :
    (pureWZ2ActiveCellShading shading hdelta).union = shading.union := by
  rw [hcubical.union_eq_activeCells hdelta]
  ext point
  constructor
  · rintro ⟨index, hpoint⟩
    exact Set.mem_iUnion₂.mpr
      ⟨((wz1PaperActiveCells shading hdelta).equivFin.symm index).1,
        ((wz1PaperActiveCells shading hdelta).equivFin.symm index).2,
        hpoint⟩
  · intro hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
    let index : Fin (wz1PaperActiveCells shading hdelta).card :=
      (wz1PaperActiveCells shading hdelta).equivFin ⟨cell, hcell⟩
    refine ⟨index, ?_⟩
    change point ∈ wz1PaperGridCube delta
      (((wz1PaperActiveCells shading hdelta).equivFin.symm index).1)
    simpa [index] using hpointCell

theorem pureWZ2ActiveCellFamily_direction
    (index : Fin (pureWZ2ActiveCellFamily shading hdelta).card) :
    ((pureWZ2ActiveCellFamily shading hdelta).tube index).direction =
      (source.tube
        (pureWZ2ActiveCellSource shading hdelta
          ((wz1PaperActiveCells shading hdelta).equivFin.symm index))).direction :=
  rfl

end Shadow

end Kakeya.Assouad
