import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CubicalSliceADBridge

/-!
# Finite height cells of a cubical paper shading

Paper shadings live in the fixed height window `[-1,1]`.  Cubicality rules out
an occupied grid cell whose lower face lies outside that window, since the
lower face itself belongs to the same carrier.  This gives the finite set of
source heights used by the final affine global-AD bridge.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- All grid-height indices whose lower face lies in the paper height window. -/
def pureWZ2PaperHeightCells (delta : ℝ) : Finset ℤ :=
  Finset.Icc (Int.ceil (-(1 / delta))) (Int.floor (1 / delta))

/-- A fixed seventeen-cell window centered at the grid cell containing a
reference height. -/
def pureWZ2CenteredHeightCells (delta center : ℝ) : Finset ℤ :=
  Finset.Icc (Int.floor (center / delta) - 8)
    (Int.floor (center / delta) + 8)

/-- The legal paper-height cells inside the fixed window. -/
def pureWZ2LocalPaperHeightCells (delta center : ℝ) : Finset ℤ :=
  pureWZ2CenteredHeightCells delta center ∩ pureWZ2PaperHeightCells delta

@[simp] theorem pureWZ2CenteredHeightCells_card
    (delta center : ℝ) :
    (pureWZ2CenteredHeightCells delta center).card = 17 := by
  unfold pureWZ2CenteredHeightCells
  rw [Int.card_Icc]
  omega

/-- Heights within eight grid scales of a reference height occupy its fixed
seventeen-cell window. -/
theorem pureWZ2_heightCell_mem_centered
    {delta center height : ℝ} (hdelta : 0 < delta)
    (hclose : |height - center| ≤ 8 * delta) :
    Int.floor (height / delta) ∈
      pureWZ2CenteredHeightCells delta center := by
  have hquotient : |height / delta - center / delta| ≤ (8 : ℝ) := by
    rw [show height / delta - center / delta =
      (height - center) / delta by ring, abs_div, abs_of_pos hdelta]
    exact (div_le_iff₀ hdelta).2 hclose
  unfold pureWZ2CenteredHeightCells
  rw [Finset.mem_Icc]
  have hlowerReal : center / delta - 8 ≤ height / delta := by
    linarith [(abs_le.mp hquotient).1]
  have hupperReal : height / delta ≤ center / delta + 8 := by
    linarith [(abs_le.mp hquotient).2]
  have hlower := Int.floor_le_floor hlowerReal
  have hupper := Int.floor_le_floor hupperReal
  constructor
  · simpa using hlower
  · simpa using hupper

theorem pureWZ2LocalPaperHeightCells_card_le
    (delta center : ℝ) :
    (pureWZ2LocalPaperHeightCells delta center).card ≤ 17 := by
  have hsubset : pureWZ2LocalPaperHeightCells delta center ⊆
      pureWZ2CenteredHeightCells delta center := by
    intro cell hcell
    exact (Finset.mem_inter.mp hcell).1
  exact (Finset.card_le_card hsubset).trans_eq
    (pureWZ2CenteredHeightCells_card delta center)

/-- For every positive paper scale, the zero height cell belongs to the
explicit finite list. -/
theorem pureWZ2PaperHeightCells_nonempty
    {delta : ℝ} (hdelta : 0 < delta) :
    (pureWZ2PaperHeightCells delta).Nonempty := by
  refine ⟨0, ?_⟩
  rw [pureWZ2PaperHeightCells, Finset.mem_Icc]
  constructor
  · apply Int.ceil_le.mpr
    have hinv : 0 < 1 / delta := by positivity
    exact_mod_cast (neg_nonpos.mpr hinv.le)
  · apply Int.le_floor.mpr
    have hinv : 0 < 1 / delta := by positivity
    exact_mod_cast hinv.le

/-- Every listed lower-face height belongs to `[-1,1]`. -/
theorem pureWZ2PaperHeightCells_height_mem
    {delta : ℝ} (hdelta : 0 < delta)
    {cell : ℤ} (hcell : cell ∈ pureWZ2PaperHeightCells delta) :
    (cell : ℝ) * delta ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [pureWZ2PaperHeightCells, Finset.mem_Icc] at hcell
  constructor
  · have hceil : -(1 / delta) ≤ (cell : ℝ) := by
      exact (Int.le_ceil (-(1 / delta))).trans <| by exact_mod_cast hcell.1
    have hmul := mul_le_mul_of_nonneg_right hceil hdelta.le
    have hinv : (1 / delta) * delta = 1 := by
      field_simp [hdelta.ne']
    nlinarith
  · have hfloor : (cell : ℝ) ≤ 1 / delta := by
      exact (by exact_mod_cast hcell.2 :
          (cell : ℝ) ≤ (Int.floor (1 / delta) : ℝ)) |>.trans
        (Int.floor_le (1 / delta))
    have hmul := mul_le_mul_of_nonneg_right hfloor hdelta.le
    have hinv : (1 / delta) * delta = 1 := by
      field_simp [hdelta.ne']
    linarith

/-- The occupied height cell of every point of a cubical paper shading is in
the explicit finite height-cell set. -/
theorem WZ1PaperIsCubicalShading.heightCell_mem
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdelta : 0 < delta)
    {point : Point3} (hpoint : point ∈ shading.union) :
    Int.floor (point 2 / delta) ∈ pureWZ2PaperHeightCells delta := by
  rcases hpoint with ⟨index, hpointCarrier⟩
  let lower := pureWZ2ReplaceHeight point
    (pureWZ2PaperCellLowerHeight delta point)
  have hlowerCarrier : lower ∈ shading.carrier index :=
    hcubical.replaceHeight_lower_mem hdelta hpointCarrier
  have hlowerBox : lower ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
    (shading.subset_body index hlowerCarrier).2
  have hlowerHeight : -1 ≤ lower 2 := by
    have habs : |lower 2| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hlowerBox.2.2
    exact (abs_le.mp habs).1
  have hpointBox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
    (shading.subset_body index hpointCarrier).2
  have hpointHeight : point 2 ≤ 1 := by
    have habs : |point 2| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hpointBox.2.2
    exact (abs_le.mp habs).2
  rw [pureWZ2PaperHeightCells, Finset.mem_Icc]
  constructor
  · apply Int.ceil_le.mpr
    have hlowerFormula : lower 2 =
        (Int.floor (point 2 / delta) : ℝ) * delta := by
      simp [lower, pureWZ2ReplaceHeight, pureWZ2PaperCellLowerHeight, point3]
    rw [hlowerFormula] at hlowerHeight
    have hneg : -(1 / delta) = (-1) / delta := by ring
    rw [hneg]
    exact (div_le_iff₀ hdelta).2 hlowerHeight
  · apply Int.le_floor.mpr
    have hcellPoint :
        (Int.floor (point 2 / delta) : ℝ) ≤ point 2 / delta :=
      Int.floor_le _
    have hpointOne : point 2 / delta ≤ 1 / delta :=
      (div_le_div_iff_of_pos_right hdelta).2 hpointHeight
    exact hcellPoint.trans hpointOne

theorem pureWZ2LocalPaperHeightCells_height_mem
    {delta center : ℝ} (hdelta : 0 < delta)
    {cell : ℤ} (hcell : cell ∈
      pureWZ2LocalPaperHeightCells delta center) :
    (cell : ℝ) * delta ∈ Set.Icc (-1 : ℝ) 1 := by
  exact pureWZ2PaperHeightCells_height_mem hdelta
    (Finset.mem_inter.mp hcell).2

theorem WZ1PaperIsCubicalShading.heightCell_mem_local
    {delta center : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdelta : 0 < delta)
    {point : Point3} (hpoint : point ∈ shading.union)
    (hclose : |point 2 - center| ≤ 8 * delta) :
    Int.floor (point 2 / delta) ∈
      pureWZ2LocalPaperHeightCells delta center := by
  exact Finset.mem_inter.mpr
    ⟨pureWZ2_heightCell_mem_centered hdelta hclose,
      hcubical.heightCell_mem hdelta hpoint⟩

/-- A nonempty cubical shading has a nonempty finite height-cell index set. -/
theorem pureWZ2PaperHeightCells_nonempty_of_shading
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdelta : 0 < delta) (hunion : shading.union.Nonempty) :
    (pureWZ2PaperHeightCells delta).Nonempty := by
  rcases hunion with ⟨point, hpoint⟩
  exact ⟨Int.floor (point 2 / delta), hcubical.heightCell_mem hdelta hpoint⟩

end Kakeya.Assouad

end
