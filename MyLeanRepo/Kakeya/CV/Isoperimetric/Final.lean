import MyLeanRepo.Kakeya.CV.Isoperimetric.EdgeCases
import MyLeanRepo.Kakeya.CV.Isoperimetric.Regularization
import MyLeanRepo.Kakeya.CV.Isoperimetric.FinalMollificationAssembly

open scoped Pointwise

/-!
# Isoperimetric Inequality — Clean Final Assembly
-/

namespace Geometry

open MeasureTheory ENNReal Metric Filter Set

/-!
## Main theorem
-/

/-- **Isoperimetric inequality** (Knill §71). For any measurable bounded
`B ⊆ ℝⁿ` with `n ≥ 2`,
`n^n · volume B^{n−1} · volume (unitBall n) ≤ μHE[n−1] (frontier B)^n`. -/
theorem isoperimetric_main (n : ℕ) (hn : 2 ≤ n) (B : Set (E n))
    (hB : MeasurableSet B) (hBdd : Bornology.IsBounded B) :
    (n : ℝ≥0∞) ^ n * (volume B) ^ (n - 1) * volume (unitBall n)
      ≤ (μHE[n - 1] (frontier B)) ^ n := by
  -- Case 1: volume B = 0
  by_cases hvol : volume B = 0
  · exact isoperimetric_volume_zero n hn B hB hBdd hvol

  -- Case 2: boundary Hausdorff measure = ∞
  by_cases hfr : μHE[n - 1] (frontier B) = ⊤
  · exact isoperimetric_boundary_top n hn B hB hBdd hfr

  -- Case 3: volume B > 0 and finite boundary measure
  have hvol_pos : 0 < volume B := Ne.bot_lt hvol
  have hfin : μHE[n - 1] (frontier B) ≠ ⊤ := hfr
  have hfin_lt : μHE[n - 1] (frontier B) < ⊤ := lt_top_iff_ne_top.mpr hfin

  -- Regularize: U = interior(closure B) is regular open
  have h_reg := regularize_open n hn B hB hBdd hfin_lt
  let U := interior (closure B)
  have hU_open : IsOpen U := h_reg.1
  have hU_bdd : Bornology.IsBounded U := h_reg.2.1
  have hU_reg : U = interior (closure U) := h_reg.2.2.1
  have hvol_eq : volume U = volume B := h_reg.2.2.2.1
  have hmon : μHE[n - 1] (frontier U) ≤ μHE[n - 1] (frontier B) := h_reg.2.2.2.2
  have hvolU_pos : 0 < volume U := by
    rw [hvol_eq]; exact hvol_pos
  have hfinU : μHE[n - 1] (frontier U) ≠ ⊤ := ne_top_of_le_ne_top hfin hmon

  have h_iso_U := isoperimetric_open_mollification n hn hU_open hU_reg hU_bdd hvolU_pos hfinU.lt_top

  rw [hvol_eq] at h_iso_U
  exact le_trans h_iso_U (pow_le_pow_left₀ (by positivity) hmon n)

end Geometry
