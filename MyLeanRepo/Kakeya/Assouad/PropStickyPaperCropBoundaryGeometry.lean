import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers

/-!
# Volume of the boundary layer of the cropped paper window

The side-`rho` cells that meet `[-1,1]^3` but are not contained in it are
supported near one of the six faces.  The corresponding boundary region has
volume at most `48 * rho`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

def wz2PaperCropBoundaryRegion (rho : ℝ) : Set Point3 :=
  {point |
    point ∈ Kakeya.Streamlined.axisBox 2 2 2 ∧
      ∃ coordinate : Fin 3, 1 - rho < |point coordinate|}

theorem wz2_paper_crop_boundary_region_volume
    {rho : ℝ} (hrho : 0 < rho) :
    volume (wz2PaperCropBoundaryRegion rho) ≤
      ENNReal.ofReal (48 * rho) := by
  let positiveFace : Fin 3 → Set Point3 :=
    fun coordinate =>
      {point |
        point ∈ Kakeya.Streamlined.axisBox 2 2 2 ∧
          |point coordinate - 1| < rho}
  let negativeFace : Fin 3 → Set Point3 :=
    fun coordinate =>
      {point |
        point ∈ Kakeya.Streamlined.axisBox 2 2 2 ∧
          |point coordinate - (-1)| < rho}
  have hSubset :
      wz2PaperCropBoundaryRegion rho ⊆
        (⋃ coordinate : Fin 3, positiveFace coordinate) ∪
          ⋃ coordinate : Fin 3, negativeFace coordinate := by
    intro point hpoint
    rcases hpoint with ⟨hbox, coordinate, hboundary⟩
    have hcoordinate :
        |point coordinate| ≤ 1 := by
      have h := hbox
      simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at h
      norm_num at h
      fin_cases coordinate <;> tauto
    by_cases hnonnegative : 0 ≤ point coordinate
    · apply Or.inl
      apply Set.mem_iUnion.mpr
      refine ⟨coordinate, ?_⟩
      refine ⟨hbox, ?_⟩
      rw [abs_of_nonneg hnonnegative] at hboundary hcoordinate
      rw [abs_lt]
      constructor <;> linarith
    · apply Or.inr
      apply Set.mem_iUnion.mpr
      refine ⟨coordinate, ?_⟩
      refine ⟨hbox, ?_⟩
      have hnegative : point coordinate < 0 :=
        lt_of_not_ge hnonnegative
      rw [abs_of_neg hnegative] at hboundary hcoordinate
      rw [abs_lt]
      constructor <;> linarith
  have hPositive :
      volume (⋃ coordinate : Fin 3, positiveFace coordinate) ≤
        ∑ coordinate : Fin 3,
          volume (positiveFace coordinate) :=
    MeasureTheory.measure_iUnion_fintype_le
      volume positiveFace
  have hNegative :
      volume (⋃ coordinate : Fin 3, negativeFace coordinate) ≤
        ∑ coordinate : Fin 3,
          volume (negativeFace coordinate) :=
    MeasureTheory.measure_iUnion_fintype_le
      volume negativeFace
  have hPositiveEach :
      ∀ coordinate,
        volume (positiveFace coordinate) ≤
          ENNReal.ofReal (8 * rho) := by
    intro coordinate
    exact boundary_slab_volume_le coordinate 1 rho hrho
  have hNegativeEach :
      ∀ coordinate,
        volume (negativeFace coordinate) ≤
          ENNReal.ofReal (8 * rho) := by
    intro coordinate
    exact boundary_slab_volume_le coordinate (-1) rho hrho
  have hUnion :
      volume
          ((⋃ coordinate : Fin 3, positiveFace coordinate) ∪
            ⋃ coordinate : Fin 3, negativeFace coordinate) ≤
        2 * (3 * ENNReal.ofReal (8 * rho)) := by
    calc
      volume
          ((⋃ coordinate : Fin 3, positiveFace coordinate) ∪
            ⋃ coordinate : Fin 3, negativeFace coordinate) ≤
          volume (⋃ coordinate : Fin 3, positiveFace coordinate) +
            volume (⋃ coordinate : Fin 3, negativeFace coordinate) :=
        measure_union_le _ _
      _ ≤
          (∑ coordinate : Fin 3, volume (positiveFace coordinate)) +
            ∑ coordinate : Fin 3, volume (negativeFace coordinate) := by
        gcongr
      _ ≤
          (∑ _coordinate : Fin 3, ENNReal.ofReal (8 * rho)) +
            ∑ _coordinate : Fin 3, ENNReal.ofReal (8 * rho) := by
        gcongr
        · exact hPositiveEach _
        · exact hNegativeEach _
      _ = 2 * (3 * ENNReal.ofReal (8 * rho)) := by
        norm_num
        ring
  have hArithmetic :
      2 * (3 * ENNReal.ofReal (8 * rho)) =
        ENNReal.ofReal (48 * rho) := by
    have hnonnegative : 0 ≤ rho := hrho.le
    rw [show ENNReal.ofReal (8 * rho) =
        (8 : ENNReal) * ENNReal.ofReal rho by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num]
    rw [show ENNReal.ofReal (48 * rho) =
        (48 : ENNReal) * ENNReal.ofReal rho by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num]
    ring
  calc
    volume (wz2PaperCropBoundaryRegion rho) ≤
        volume
          ((⋃ coordinate : Fin 3, positiveFace coordinate) ∪
            ⋃ coordinate : Fin 3, negativeFace coordinate) :=
      measure_mono hSubset
    _ ≤ 2 * (3 * ENNReal.ofReal (8 * rho)) := hUnion
    _ = ENNReal.ofReal (48 * rho) := hArithmetic

end Kakeya.Assouad

end
