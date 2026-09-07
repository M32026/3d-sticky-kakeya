import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Edge Case Reductions

Trivial cases and reductions for the isoperimetric inequality.

## Main results

- `isoperimetric_volume_zero`: the inequality holds when `volume B = 0`.
- `isoperimetric_boundary_top`: the inequality holds when `μHE[n-1](frontier B) = ⊤`.
- `volume_zero_of_hausdorff_fin`: if `μHE[n-1] S ≠ ⊤`, then `volume S = 0`.
- `volume_interior_eq_volume`, `volume_closure_eq_volume`: if the frontier has volume zero,
  then `B`, `interior B`, and `closure B` all have equal volume.
- `frontier_interior_subset`: `frontier(interior B) ⊆ frontier B`.
- `reduce_to_open`: it suffices to prove the theorem for bounded open sets.

## Proof sketch

The dimension dichotomy follows from `euclideanHausdorffMeasure_zero_or_top`:
since `n-1 < n`, either `μHE[n] S = 0` or `μHE[n-1] S = ⊤`.
Since `μHE[n] = volume`, finiteness of `μHE[n-1] S` implies `volume S = 0`.

The reduction to open sets uses `U := interior B`. Since `frontier U ⊆ frontier B`,
monotonicity of Hausdorff measure transfers the inequality from `U` to `B`.

## Whiteprint

This module corresponds to the `edge_cases` whiteprint node.
-/

namespace Geometry

open MeasureTheory ENNReal Metric Set TopologicalSpace
open scoped MeasureTheory

variable {n : ℕ}

/-- If `volume B = 0` and `n ≥ 2`, the isoperimetric inequality holds trivially
because the LHS is zero. -/
theorem isoperimetric_volume_zero (n : ℕ) (hn : 2 ≤ n) (B : Set (E n))
    (hB : MeasurableSet B) (hBdd : Bornology.IsBounded B)
    (hvol : volume B = 0) :
    (n : ℝ≥0∞) ^ n * (volume B) ^ (n - 1) * volume (unitBall n)
      ≤ (μHE[n - 1] (frontier B)) ^ n := by
  have h1 : n - 1 ≥ 1 := by omega
  have h2 : (volume B) ^ (n - 1) = 0 := by
    rw [hvol]
    have hpos : n - 1 ≠ 0 := by omega
    exact zero_pow hpos
  have h3 : (n : ℝ≥0∞) ^ n * (volume B) ^ (n - 1) * volume (unitBall n) = 0 := by
    rw [h2]
    <;> simp [mul_zero]
  rw [h3]
  <;> positivity

/-- If `μHE[n - 1] (frontier B) = ⊤`, the isoperimetric inequality holds trivially
because the RHS is `⊤`. -/
theorem isoperimetric_boundary_top (n : ℕ) (hn : 2 ≤ n) (B : Set (E n))
    (hB : MeasurableSet B) (hBdd : Bornology.IsBounded B)
    (hfr : μHE[n - 1] (frontier B) = ⊤) :
    (n : ℝ≥0∞) ^ n * (volume B) ^ (n - 1) * volume (unitBall n)
      ≤ (μHE[n - 1] (frontier B)) ^ n := by
  rw [hfr]
  have h_npos : n ≠ 0 := by omega
  have h_top : (⊤ : ℝ≥0∞) ^ n = ⊤ := by
    simp [h_npos]
  rw [h_top]
  simp

/-- **Dimension dichotomy**: If `μHE[n - 1] S < ⊤`, then `volume S = 0`.
Since `n - 1 < n`, the `(n-1)`-dimensional Hausdorff measure being finite
forces the `n`-dimensional Lebesgue measure to be zero. -/
theorem volume_zero_of_hausdorff_fin (n : ℕ) (hn : 2 ≤ n) {S : Set (E n)}
    (hS : MeasurableSet S) (hfin : μHE[n - 1] S ≠ ⊤) :
    volume S = 0 := by
  have hlt : n - 1 < n := by omega
  have h := MeasureTheory.Measure.euclideanHausdorffMeasure_zero_or_top hlt S
  rcases h with (h | h)
  · -- μHE[n] S = 0
    have heq : (μHE[n] : Measure (E n)) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
    rw [heq] at h
    exact h
  · -- μHE[n - 1] S = ⊤, contradiction
    exfalso
    exact hfin h

/-- If `volume (frontier B) = 0`, then `volume (interior B) = volume B`. -/
theorem volume_interior_eq_volume (B : Set (E n))
    (hB : MeasurableSet B) (hfrvol : volume (frontier B) = 0) :
    volume (interior B) = volume B := by
  have h1 : interior B ⊆ B := interior_subset
  have h2 : B ⊆ closure B := subset_closure
  have h3 : closure B = interior B ∪ frontier B :=
    closure_eq_interior_union_frontier B
  have h4 : volume (closure B) ≤ volume (interior B) + volume (frontier B) := by
    rw [h3]
    exact measure_union_le _ _
  have h5 : volume (closure B) ≤ volume (interior B) := by
    rw [hfrvol] at h4
    simpa using h4
  have h6 : volume (interior B) ≤ volume B := measure_mono h1
  have h7 : volume B ≤ volume (closure B) := measure_mono h2
  have h8 : volume B ≤ volume (interior B) := le_trans h7 h5
  exact le_antisymm h6 h8

/-- If `volume (frontier B) = 0`, then `volume (closure B) = volume B`. -/
theorem volume_closure_eq_volume (B : Set (E n))
    (hB : MeasurableSet B) (hfrvol : volume (frontier B) = 0) :
    volume (closure B) = volume B := by
  have h1 : B ⊆ closure B := subset_closure
  have h2 : closure B = interior B ∪ frontier B :=
    closure_eq_interior_union_frontier B
  have h3 : volume (closure B) ≤ volume (interior B) + volume (frontier B) := by
    rw [h2]
    exact measure_union_le _ _
  have h4 : volume (closure B) ≤ volume (interior B) := by
    rw [hfrvol] at h3
    simpa using h3
  have h5 : volume (interior B) ≤ volume B := measure_mono (interior_subset)
  have h6 : volume B ≤ volume (closure B) := measure_mono h1
  have h7 : volume (closure B) ≤ volume B := le_trans h4 h5
  exact le_antisymm h7 h6

/-- The frontier of the interior is a subset of the frontier. -/
theorem frontier_interior_subset (B : Set (E n)) :
    frontier (interior B) ⊆ frontier B := by
  have h1 : closure (interior B) ⊆ closure B :=
    closure_mono (interior_subset)
  have h2 : frontier (interior B) = closure (interior B) \ interior B := by
    simp [frontier, interior_interior]
    <;> rfl
  rw [h2]
  intro x hx
  exact ⟨h1 hx.1, hx.2⟩

/-- **Reduction to open sets**: It suffices to prove the isoperimetric inequality
for bounded open sets. Given a bounded measurable `B` with finite boundary
Hausdorff measure, let `U := interior B`. Then `U` is open and bounded,
`volume U = volume B`, and `frontier U ⊆ frontier B`. Hence the inequality
for `U` implies the inequality for `B`. -/
theorem reduce_to_open (n : ℕ) (hn : 2 ≤ n) (B : Set (E n))
    (hB : MeasurableSet B) (hBdd : Bornology.IsBounded B)
    (hfin : μHE[n - 1] (frontier B) ≠ ⊤)
    (h_main : ∀ (U : Set (E n)), IsOpen U → Bornology.IsBounded U →
      (n : ℝ≥0∞) ^ n * (volume U) ^ (n - 1) * volume (unitBall n)
        ≤ (μHE[n - 1] (frontier U)) ^ n) :
    (n : ℝ≥0∞) ^ n * (volume B) ^ (n - 1) * volume (unitBall n)
      ≤ (μHE[n - 1] (frontier B)) ^ n := by
  let U := interior B
  have hU_open : IsOpen U := isOpen_interior
  have hU_bdd : Bornology.IsBounded U := Bornology.IsBounded.subset hBdd (interior_subset)
  have hfrvol : volume (frontier B) = 0 :=
    volume_zero_of_hausdorff_fin n hn (isClosed_frontier.measurableSet) hfin
  have hvol_eq : volume U = volume B :=
    volume_interior_eq_volume B hB hfrvol
  have hfr_sub : frontier U ⊆ frontier B := frontier_interior_subset B
  have hmon : μHE[n - 1] (frontier U) ≤ μHE[n - 1] (frontier B) :=
    measure_mono hfr_sub
  have h_iso_U := h_main U hU_open hU_bdd
  rw [hvol_eq] at *
  exact le_trans h_iso_U (pow_le_pow_left₀ (by positivity) hmon n)

end Geometry
