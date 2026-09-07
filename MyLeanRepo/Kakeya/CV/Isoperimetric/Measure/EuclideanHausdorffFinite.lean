import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.Tactic

/-!
# Euclidean Hausdorff Measure Utilities

Basic facts about `μHE[d]` (Euclidean Hausdorff measure) and its relation
to `μH[d]` (standard Hausdorff measure).

## Main results
- `euclideanHausdorffMeasure_finite_iff`: `μHE[d] S < ⊤ ↔ μH[d] S < ⊤`
-/

open MeasureTheory ENNReal Metric
open scoped MeasureTheory

namespace Geometry

/-- Equivalence between finiteness of Euclidean Hausdorff measure and Hausdorff measure.

Since `μHE[d] = c • μH[d]` with `0 < c < ∞`, we have `μHE[d] S < ⊤ ↔ μH[d] S < ⊤`. -/
lemma euclideanHausdorffMeasure_finite_iff {n d : ℕ} {S : Set (E n)} :
    μHE[d] S < ⊤ ↔ μH[d] S < ⊤ := by
  set c : NNReal := (volume : Measure (E d)).addHaarScalarFactor (μH[d] : Measure (E d)) with hc
  have hc_ne_zero : c ≠ 0 := by
    rw [hc]
    exact MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero d
  have h_def : (μHE[d] : Measure (E n)) =
      ((volume : Measure (E d)).addHaarScalarFactor (μH[d] : Measure (E d))) • μH[d] :=
    MeasureTheory.Measure.euclideanHausdorffMeasure_def (X := E n) d
  have h_def' : (μHE[d] : Measure (E n)) = c • μH[d] := by
    rw [hc]
    exact h_def
  have h_eval : μHE[d] S = (c : ENNReal) * μH[d] S := by
    rw [h_def']
    exact Measure.coe_nnreal_smul_apply c μH[d] S
  rw [h_eval]
  have h1 : (c : ENNReal) ≠ 0 := by exact_mod_cast hc_ne_zero
  have h2 : (c : ENNReal) < ⊤ := coe_lt_top
  constructor
  · intro h
    by_contra h3
    have h4 : μH[d] S = ⊤ := by simpa [not_lt] using h3
    rw [h4] at h
    simp [h1, mul_top] at h
  · intro h
    exact ENNReal.mul_lt_top h2 h

end Geometry
