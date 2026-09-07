import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.PerimeterDensityOne
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.NonSharpIsoperimetric
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.IsoperimetricFromMollification
import Mathlib.Tactic

/-!
# Final Isoperimetric Assembly via Mollification Route

## Proof

1. For regular open bounded `U` with positive volume and finite boundary Hausdorff:
   - `P(U) < ⊤` from `perimeter_finite_of_euclideanHausdorff_finite`
   - `0 < P(U)`: if `P(U) = 0`, non-sharp isoperimetric gives `volume U = 0`
   - `isoperimetric_from_mollification`: `n · V^α · ω^β ≤ P(U)`
   - `perimeter_le_hausdorff_frontier`: `P(U) ≤ H(∂U)`
   - Combine: `n · V^α · ω^β ≤ H(∂U)`
   - Raise to nth power: `n^n · V^(n-1) · ω ≤ H(∂U)^n`

2. For general measurable bounded `B`:
   - Edge cases (volume zero, boundary top)
   - Regularize to `U = interior(closure B)`
   - Transfer volume equality and Hausdorff monotonicity
-/

namespace Geometry

open MeasureTheory ENNReal Metric Set

/-- **Isoperimetric inequality for regular open sets via mollification route.**

Alternative to `isoperimetric_open` that avoids `outerMinkowskiContent_upperBound`. -/
theorem isoperimetric_open_mollification (n : ℕ) (hn : 2 ≤ n)
    {U : Set (E n)} (hU : IsOpen U) (hU_reg : U = interior (closure U))
    (hBdd : Bornology.IsBounded U)
    (hvol_pos : 0 < volume U) (hfin : μHE[n - 1] (frontier U) < ⊤) :
    (n : ℝ≥0∞) ^ n * (volume U) ^ (n - 1) * volume (unitBall n)
      ≤ (μHE[n - 1] (frontier U)) ^ n := by
  letI : Nonempty (Fin n) := ⟨⟨0, by linarith⟩⟩
  set V : ENNReal := volume U with hV_def
  set H : ENNReal := μHE[n - 1] (frontier U) with hH_def
  set ω : ENNReal := volume (unitBall n) with hω_def
  set α : ℝ := (n - 1 : ℝ) / n with hα_def
  set β : ℝ := 1 / (n : ℝ) with hβ_def

  have hV_lt_top : V < ⊤ := hBdd.measure_lt_top
  have hH_ne_top : H ≠ ⊤ := hfin.ne
  have hω_lt_top : ω < ⊤ := Metric.isBounded_closedBall.measure_lt_top

  -- Step 1: Finite perimeter
  have hP_lt_top : Perimeter.perimeter U < ⊤ :=
    perimeter_finite_of_euclideanHausdorff_finite (by linarith) hU.measurableSet hfin

  -- Step 2: Positive perimeter (from non-sharp isoperimetric)
  have hP_pos : 0 < Perimeter.perimeter U := by
    by_contra h
    have hP0 : Perimeter.perimeter U = 0 := by simpa using h
    have h_nonsharp := Perimeter.non_sharp_isoperimetric_perimeter hn hU.measurableSet hBdd
    rw [hP0] at h_nonsharp
    have hα_pos : 0 < α := by
      rw [hα_def]
      have h1 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n from by omega)
      have h2 : (n : ℝ) ≥ 2 := by exact_mod_cast hn
      have h3 : 0 < (n : ℝ) - 1 := by linarith
      exact div_pos h3 h1
    have h : V ^ α = 0 := by simpa [mul_zero] using h_nonsharp
    have hV_pos' : 0 < V := hvol_pos
    have h_ne_zero : 0 < V ^ α := ENNReal.rpow_pos_of_nonneg hV_pos' hα_pos.le
    exact Ne.symm h_ne_zero.ne h

  -- Step 3: Mollification route gives perimeter form
  have h_perim_iso : (n : ENNReal) * V ^ α * ω ^ β ≤ Perimeter.perimeter U :=
    isoperimetric_from_mollification n hn U hU.measurableSet hBdd hP_pos hP_lt_top

  -- Step 4: Perimeter ≤ Hausdorff
  have hP_le_H : Perimeter.perimeter U ≤ H :=
    StructureTheorem.perimeter_le_hausdorff_frontier hU hU_reg hBdd hfin hn

  -- Step 5: Combine
  have h_main : (n : ENNReal) * V ^ α * ω ^ β ≤ H :=
    le_trans h_perim_iso hP_le_H

  -- Step 6: Raise to nth power
  have h_n_pow_ne_top : (n : ENNReal) ^ n ≠ ⊤ := by simp
  have hV_pow_ne_top : V ^ (n - 1) ≠ ⊤ := by simp [hV_lt_top.ne]
  have hLHS_ne_top : ((n : ENNReal) ^ n * V ^ (n - 1) * ω) ≠ ⊤ := by
    apply mul_ne_top
    · apply mul_ne_top
      · exact h_n_pow_ne_top
      · exact hV_pow_ne_top
    · exact hω_lt_top.ne
  have hRHS_ne_top : H ^ n ≠ ⊤ := by simp [hH_ne_top]

  have h_ennreal : ((n : ENNReal) ^ n * V ^ (n - 1) * ω) ≤ H ^ n := by
    -- Algebra: (n * V^α * ω^β)^n = n^n * V^(n-1) * ω
    have h1 : ((n : ENNReal) * V ^ α * ω ^ β) ^ n ≤ H ^ n :=
      ENNReal.pow_le_pow_left h_main
    have h2 : ((n : ENNReal) * V ^ α * ω ^ β) ^ n =
        (n : ENNReal) ^ n * (V ^ α) ^ n * (ω ^ β) ^ n := by
      simp [mul_pow]
      <;> ring
    rw [h2] at h1
    have h3 : (V ^ α) ^ n = V ^ (n - 1) := by
      have h31 : (V ^ α) ^ n = (V ^ α) ^ (n : ℝ) := by
        norm_cast
      rw [h31]
      have h32 : (V ^ α) ^ (n : ℝ) = V ^ (α * (n : ℝ)) := by
        rw [← ENNReal.rpow_mul] <;> positivity
      rw [h32]
      have h33 : α * (n : ℝ) = ((n - 1 : ℕ) : ℝ) := by
        have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n from by omega)
        rw [hα_def]
        have h : ((n - 1 : ℝ) / (n : ℝ)) * (n : ℝ) = (n - 1 : ℝ) := by
          field_simp [hn_pos.ne'] <;> ring
        rw [h]
        have h_cast : (n - 1 : ℝ) = ((n - 1 : ℕ) : ℝ) := by
          cases n with
          | zero => omega
          | succ n' => simp [Nat.cast_add] <;> ring
        exact h_cast
      rw [h33]
      have h34 : V ^ ((n - 1 : ℕ) : ℝ) = V ^ (n - 1) := by
        norm_cast
      exact h34
    have h4 : (ω ^ β) ^ n = ω := by
      have h41 : (ω ^ β) ^ n = (ω ^ β) ^ (n : ℝ) := by norm_cast
      rw [h41]
      have h42 : (ω ^ β) ^ (n : ℝ) = ω ^ (β * (n : ℝ)) := by
        rw [← ENNReal.rpow_mul] <;> positivity
      rw [h42]
      have h43 : β * (n : ℝ) = 1 := by
        rw [hβ_def] <;> field_simp <;> ring
      rw [h43]
      <;> simp
    rw [h3, h4] at h1
    exact h1
  exact h_ennreal

end Geometry
