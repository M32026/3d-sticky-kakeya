module

/-
# Frostman Measure → IsRealDeltaSet

Full chain: Frostman probability measure on a finite δ-separated set
→ discard tiny weights
→ dyadic weight thinning
→ ball-counting bound
→ `ball_counting_to_real_delta_set`
→ IsRealDeltaSet.
-/

public import MyLeanRepo.Energy.EnergyToNonConcentration
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Finset Set Bornology Classical

namespace robust_projection

/-- Sum of singleton measures over a finset equals measure of the finset. -/
lemma finset_measure_sum (μ : Measure ℝ) {s : Finset ℝ} :
    μ (↑s : Set ℝ) = ∑ a ∈ s, μ {a} := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have h_ms : MeasurableSet (↑s : Set ℝ) := Finset.measurableSet s
    have h_disj : Disjoint ({a} : Set ℝ) (↑s : Set ℝ) := by
      simp [ha]
    have h_union : μ (({a} : Set ℝ) ∪ ↑s) = μ {a} + μ (↑s : Set ℝ) :=
      measure_union h_disj h_ms
    have h_insert : (↑(insert a s) : Set ℝ) = ({a} : Set ℝ) ∪ ↑s := by
      ext x; simp [ha] <;> tauto
    calc μ (↑(insert a s) : Set ℝ)
      = μ (({a} : Set ℝ) ∪ ↑s) := by rw [h_insert]
    _ = μ {a} + μ (↑s : Set ℝ) := h_union
    _ = μ {a} + ∑ x ∈ s, μ {x} := by rw [ih]
    _ = ∑ x ∈ insert a s, μ {x} := by
      rw [Finset.sum_insert ha] <;> ring

end robust_projection
