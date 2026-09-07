import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruningGeometry
import Mathlib.Tactic

/-!
# A grid-aligned target scale for the Proposition 6.5 rescaling

The exact triangular map sends the selected height interval to [-1,1].
For the induced fixed-origin paper cubes, it is useful to choose a target
scale whose reciprocal is an integer.  Rounding the geometric retubing
radius upward in this way costs less than a factor two.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The geometric radius needed before aligning the target grid. -/
def anisotropicPaperRawScale (delta c d : ℝ) : ℝ :=
  16 * delta / (d - c)

/-- Number of target cells in a unit coordinate interval. -/
def anisotropicPaperAlignedCount (delta c d : ℝ) : ℕ :=
  Nat.floor (1 / anisotropicPaperRawScale delta c d)

/-- The target scale after reciprocal-grid alignment. -/
def anisotropicPaperAlignedScale (delta c d : ℝ) : ℝ :=
  1 / (anisotropicPaperAlignedCount delta c d : ℝ)

theorem anisotropicPaperAlignedCount_pos
    {delta c d : ℝ}
    (hraw : 0 < anisotropicPaperRawScale delta c d)
    (hrawHalf : anisotropicPaperRawScale delta c d ≤ 1 / 2) :
    0 < anisotropicPaperAlignedCount delta c d := by
  apply Nat.floor_pos.mpr
  have : (2 : ℝ) ≤ 1 / anisotropicPaperRawScale delta c d := by
    rw [le_div_iff₀ hraw]
    linarith
  linarith

theorem anisotropicPaperRawScale_le_aligned
    {delta c d : ℝ}
    (hraw : 0 < anisotropicPaperRawScale delta c d)
    (hrawHalf : anisotropicPaperRawScale delta c d ≤ 1 / 2) :
    anisotropicPaperRawScale delta c d ≤
      anisotropicPaperAlignedScale delta c d := by
  let raw := anisotropicPaperRawScale delta c d
  let count := anisotropicPaperAlignedCount delta c d
  have hcountPos : 0 < count :=
    anisotropicPaperAlignedCount_pos hraw hrawHalf
  have honeRaw : 0 ≤ 1 / raw := by positivity
  have hcountLe : (count : ℝ) ≤ 1 / raw := by
    exact Nat.floor_le honeRaw
  change raw ≤ 1 / (count : ℝ)
  rw [le_div_iff₀ (by exact_mod_cast hcountPos)]
  calc
    raw * (count : ℝ) ≤ raw * (1 / raw) :=
      mul_le_mul_of_nonneg_left hcountLe hraw.le
    _ = 1 := by
      rw [mul_div_cancel₀]
      exact hraw.ne'

theorem anisotropicPaperAlignedScale_lt_two_mul_raw
    {delta c d : ℝ}
    (hraw : 0 < anisotropicPaperRawScale delta c d)
    (hrawHalf : anisotropicPaperRawScale delta c d ≤ 1 / 2) :
    anisotropicPaperAlignedScale delta c d <
      2 * anisotropicPaperRawScale delta c d := by
  let raw := anisotropicPaperRawScale delta c d
  let count := anisotropicPaperAlignedCount delta c d
  have hcountPos : 0 < count :=
    anisotropicPaperAlignedCount_pos hraw hrawHalf
  have hfloorPlus : 1 / raw < (count : ℝ) + 1 := by
    exact Nat.lt_floor_add_one (1 / raw)
  have htwo : (2 : ℝ) ≤ 1 / raw := by
    rw [le_div_iff₀ hraw]
    linarith
  have hcountLower : 1 / (2 * raw) < (count : ℝ) := by
    have hsub : 1 / raw - 1 < (count : ℝ) := by linarith
    have hhalf : 1 / (2 * raw) ≤ 1 / raw - 1 := by
      have hrewrite : 1 / (2 * raw) = (1 / raw) / 2 := by
        field_simp [ne_of_gt hraw]
      rw [hrewrite]
      linarith
    exact hhalf.trans_lt hsub
  change 1 / (count : ℝ) < 2 * raw
  rw [div_lt_iff₀ (by exact_mod_cast hcountPos)]
  calc
    1 = (2 * raw) * (1 / (2 * raw)) := by
      symm
      rw [mul_div_cancel₀]
      positivity
    _ < (2 * raw) * (count : ℝ) :=
      mul_lt_mul_of_pos_left hcountLower (mul_pos (by norm_num) hraw)

theorem anisotropicPaperAlignedScale_pos
    {delta c d : ℝ}
    (hraw : 0 < anisotropicPaperRawScale delta c d)
    (hrawHalf : anisotropicPaperRawScale delta c d ≤ 1 / 2) :
    0 < anisotropicPaperAlignedScale delta c d := by
  unfold anisotropicPaperAlignedScale
  positivity [anisotropicPaperAlignedCount_pos hraw hrawHalf]

theorem anisotropicPaperAlignedScale_mul_count
    {delta c d : ℝ}
    (hraw : 0 < anisotropicPaperRawScale delta c d)
    (hrawHalf : anisotropicPaperRawScale delta c d ≤ 1 / 2) :
    anisotropicPaperAlignedScale delta c d *
        (anisotropicPaperAlignedCount delta c d : ℝ) = 1 := by
  unfold anisotropicPaperAlignedScale
  field_simp [show (anisotropicPaperAlignedCount delta c d : ℝ) ≠ 0 by
    exact_mod_cast (anisotropicPaperAlignedCount_pos hraw hrawHalf).ne']

/-- A fixed-origin grid cube meeting the half-open unit interval in one
coordinate remains in the closed unit interval when the reciprocal scale is
an integer. -/
theorem aligned_gridCube_coordinate_mem_unit
    {scale : ℝ} {count : ℕ}
    (hscale : 0 < scale) (hcount : 0 < count)
    (halign : scale * (count : ℝ) = 1)
    {cell : ℤ × ℤ × ℤ} {source target : Point3}
    (coordinate : Fin 3)
    (hsourceCell : source ∈ wz1PaperGridCube scale cell)
    (htargetCell : target ∈ wz1PaperGridCube scale cell)
    (hsourceWindow : -1 ≤ source coordinate ∧ source coordinate < 1) :
    |target coordinate| ≤ 1 := by
  have hsourceBounds := (mem_gridCube_iff hscale).mp hsourceCell coordinate
  have htargetBounds := (mem_gridCube_iff hscale).mp htargetCell coordinate
  let index : ℤ := tripleCoord cell coordinate
  have halignNeg : (-(count : ℤ) : ℝ) * scale = -1 := by
    push_cast
    linarith
  have hindexLower : (-(count : ℤ) : ℝ) < (index : ℝ) + 1 := by
    have : (-(count : ℤ) : ℝ) * scale <
        ((index : ℝ) + 1) * scale := by
      rw [halignNeg]
      exact hsourceWindow.1.trans_lt hsourceBounds.2
    nlinarith
  have hindexLowerInt : -(count : ℤ) ≤ index := by
    by_contra hnot
    have hinterger : index + 1 ≤ -(count : ℤ) := by omega
    have hreal : (index : ℝ) + 1 ≤ (-(count : ℤ) : ℝ) := by
      exact_mod_cast hinterger
    linarith
  have hlower : -1 ≤ target coordinate := by
    calc
      -1 = (-(count : ℤ) : ℝ) * scale := halignNeg.symm
      _ ≤ (index : ℝ) * scale := by
        gcongr
        exact_mod_cast hindexLowerInt
      _ ≤ target coordinate := htargetBounds.1
  have halignPos : (count : ℝ) * scale = 1 := by
    linarith [halign]
  have hindexUpper : (index : ℝ) < (count : ℝ) := by
    have : (index : ℝ) * scale < (count : ℝ) * scale := by
      calc
        (index : ℝ) * scale ≤ source coordinate := hsourceBounds.1
        _ < 1 := hsourceWindow.2
        _ = (count : ℝ) * scale := halignPos.symm
    nlinarith
  have hindexUpperInt : index + 1 ≤ (count : ℤ) := by
    exact_mod_cast hindexUpper
  have hupper : target coordinate ≤ 1 := by
    calc
      target coordinate ≤ ((index : ℝ) + 1) * scale :=
        htargetBounds.2.le
      _ ≤ (count : ℝ) * scale := by
        gcongr
        exact_mod_cast hindexUpperInt
      _ = 1 := halignPos
  exact abs_le.mpr ⟨hlower, hupper⟩

end Kakeya.Assouad

end
