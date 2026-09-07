import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinOccupiedBound

/-!
# Bounded common-bin incidence of one spatial cell

A side-`s` spatial cube meets only an absolute number of the fixed
height-independent common bins.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Bins from a supplied finite family that meet one side-`side` paper-grid
cube. -/
def pureWZ2CommonBinsMeetingSpatialCell
    (bins : Finset ℤ)
    (slope : ℝ → ℝ)
    (referenceHeight side : ℝ)
    (cell : ℤ × ℤ × ℤ) : Finset ℤ :=
  bins.filter fun bin =>
    ∃ point ∈ wz1PaperGridCube side cell,
      pureWZ2FixedCommonBinLabel slope referenceHeight side point = bin

private theorem abs_floor_sub_le_two
    {first second : ℝ}
    (hclose : |first - second| ≤ 2) :
    |Int.floor first - Int.floor second| ≤ (2 : ℤ) := by
  have hforward :
      (Int.floor first : ℝ) - (Int.floor second : ℝ) < 3 := by
    have hfirst := Int.floor_le first
    have hsecond := Int.lt_floor_add_one second
    have hdiff := (abs_le.mp hclose).2
    linarith
  have hbackward :
      (Int.floor second : ℝ) - (Int.floor first : ℝ) < 3 := by
    have hsecond := Int.floor_le second
    have hfirst := Int.lt_floor_add_one first
    have hdiff := (abs_le.mp hclose).1
    linarith
  rw [abs_le]
  constructor
  · by_contra h
    have hinteger :
        Int.floor first - Int.floor second ≤ (-3 : ℤ) := by omega
    have hreal :
        (Int.floor second : ℝ) - (Int.floor first : ℝ) ≥ 3 := by
      exact_mod_cast (show
        (3 : ℤ) ≤ Int.floor second - Int.floor first by omega)
    linarith
  · by_contra h
    have hinteger :
        (3 : ℤ) ≤ Int.floor first - Int.floor second := by omega
    have hreal :
        (3 : ℝ) ≤
          (Int.floor first : ℝ) - (Int.floor second : ℝ) := by
      exact_mod_cast hinteger
    linarith

/-- Every fixed common bin meeting one side-`side` spatial cube lies within
two labels of the bin containing the cube center. -/
theorem commonBinLabel_mem_center_window
    {side : ℝ}
    (hside : 0 < side)
    (bins : Finset ℤ)
    (slope : ℝ → ℝ)
    (referenceHeight : ℝ)
    (slope_bound : |slope referenceHeight| ≤ 3)
    (cell : ℤ × ℤ × ℤ)
    {bin : ℤ}
    (hbin :
      bin ∈ pureWZ2CommonBinsMeetingSpatialCell
        bins slope referenceHeight side cell) :
    bin ∈ Finset.Icc
      (pureWZ2FixedCommonBinLabel slope referenceHeight side
          (pureWZ2PaperCellCenter side cell) - 2)
      (pureWZ2FixedCommonBinLabel slope referenceHeight side
          (pureWZ2PaperCellCenter side cell) + 2) := by
  rw [pureWZ2CommonBinsMeetingSpatialCell, Finset.mem_filter] at hbin
  rcases hbin.2 with ⟨point, hpoint, rfl⟩
  let center := pureWZ2PaperCellCenter side cell
  have hcube := hpoint
  rw [wz1PaperGridCube_eq_Ico hside cell] at hcube
  have hcoordinate :
      ∀ coordinate : Fin 3,
        |point coordinate - center coordinate| ≤ side / 2 := by
    intro coordinate
    fin_cases coordinate
    · simp [center, pureWZ2PaperCellCenter, cellCorner,
        wz1PaperGridCubeTranslation, point3]
      rw [abs_le]
      constructor <;> linarith [hcube.1, hcube.2.1]
    · simp [center, pureWZ2PaperCellCenter, cellCorner,
        wz1PaperGridCubeTranslation, point3]
      rw [abs_le]
      constructor <;> linarith [hcube.2.2.1, hcube.2.2.2.1]
    · simp [center, pureWZ2PaperCellCenter, cellCorner,
        wz1PaperGridCubeTranslation, point3]
      rw [abs_le]
      constructor <;> linarith [hcube.2.2.2.2.1, hcube.2.2.2.2.2]
  let pointCoordinate :=
    inner ℝ point (globalGrainDirection (slope referenceHeight))
  let centerCoordinate :=
    inner ℝ center (globalGrainDirection (slope referenceHeight))
  have hcommonCoordinate :
      |pointCoordinate - centerCoordinate| ≤ 2 * side := by
    have hformula :
        pointCoordinate - centerCoordinate =
          (point 0 - center 0) +
            slope referenceHeight * (point 1 - center 1) := by
      simp [pointCoordinate, centerCoordinate, center,
        globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      ring
    rw [hformula]
    calc
      |(point 0 - center 0) +
          slope referenceHeight * (point 1 - center 1)| ≤
          |point 0 - center 0| +
            |slope referenceHeight| * |point 1 - center 1| := by
        simpa [abs_mul] using
          abs_add_le (point 0 - center 0)
            (slope referenceHeight * (point 1 - center 1))
      _ ≤ side / 2 + 3 * (side / 2) := by
        gcongr
        · exact hcoordinate 0
        · exact hcoordinate 1
      _ = 2 * side := by ring
  have hnormalized :
      |pointCoordinate / side - centerCoordinate / side| ≤ 2 := by
    rw [← sub_div, abs_div, abs_of_pos hside]
    exact (div_le_iff₀ hside).2
      (by simpa [mul_comm] using hcommonCoordinate)
  have hfloor :=
    abs_floor_sub_le_two hnormalized
  change
    Int.floor (pointCoordinate / side) ∈
      Finset.Icc
        (Int.floor (centerCoordinate / side) - 2)
        (Int.floor (centerCoordinate / side) + 2)
  rw [Finset.mem_Icc]
  rw [abs_le] at hfloor
  omega

/-- One side-`side` spatial cube meets at most five fixed common bins. -/
theorem commonBinsMeetingSpatialCell_card_le_five
    {side : ℝ}
    (hside : 0 < side)
    (bins : Finset ℤ)
    (slope : ℝ → ℝ)
    (referenceHeight : ℝ)
    (slope_bound : |slope referenceHeight| ≤ 3)
    (cell : ℤ × ℤ × ℤ) :
    (pureWZ2CommonBinsMeetingSpatialCell
      bins slope referenceHeight side cell).card ≤ 5 := by
  let centerBin :=
    pureWZ2FixedCommonBinLabel slope referenceHeight side
      (pureWZ2PaperCellCenter side cell)
  have hsubset :
      pureWZ2CommonBinsMeetingSpatialCell
          bins slope referenceHeight side cell ⊆
        Finset.Icc (centerBin - 2) (centerBin + 2) := by
    intro bin hbin
    simpa [centerBin] using
      commonBinLabel_mem_center_window
        hside bins slope referenceHeight slope_bound cell hbin
  calc
    (pureWZ2CommonBinsMeetingSpatialCell
        bins slope referenceHeight side cell).card ≤
        (Finset.Icc (centerBin - 2) (centerBin + 2)).card :=
      Finset.card_le_card hsubset
    _ = 5 := by
      rw [Int.card_Icc]
      omega

end Kakeya.Assouad

end
