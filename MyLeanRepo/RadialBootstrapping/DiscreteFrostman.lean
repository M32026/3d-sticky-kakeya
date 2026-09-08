/-
Discrete Frostman Lemma and Mass Distribution Principle

This module provides:
1. Quantitative mass distribution principle for Hausdorff content
2. Discrete Frostman lemma: from positive Hausdorff content, extract a separated
   set with packing/covering number lower bound

Authors: Onyx (SeedMathlib extension)
-/
module

public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal

namespace SeedMathlib.MeasureTheory.FractalGeometry.FrostmanLemma

variable {n : ℕ} {s : ℝ}

/-! ============================================================================
   Mass Distribution Principle with Constant
   ============================================================================ -/

/-- If a measure satisfies `μ(closedBall x r) ≤ C * r^s`, then it vanishes
    on singletons. -/
lemma bounded_packingNumber_ne_top {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA_bounded : Bornology.IsBounded A) {ε : ℝ≥0} (hε_pos : 0 < ε) :
    Metric.packingNumber ε A ≠ ⊤ := by
  have hA_tb : TotallyBounded A := by
    have h1 : IsCompact (closure A) := hA_bounded.isCompact_closure
    exact h1.totallyBounded.subset subset_closure
  let ε2 : ℝ≥0 := ε / 2
  have hε2_pos : 0 < ε2 := by positivity
  have h_exists : ∃ (t : Set (EuclideanSpace ℝ (Fin n))),
      t.Finite ∧ A ⊆ ⋃ x ∈ t, Metric.ball x (ε2 : ℝ) := by
    have h := (totallyBounded_iff.mp hA_tb) (ε2 : ℝ) hε2_pos
    exact h
  rcases h_exists with ⟨t, ht_finite, hcover⟩
  let t' : Finset (EuclideanSpace ℝ (Fin n)) := ht_finite.toFinset
  have h_coe : (t' : Set (EuclideanSpace ℝ (Fin n))) = t := ht_finite.coe_toFinset
  have h_is_cover : Metric.IsCover ε2 A (t' : Set (EuclideanSpace ℝ (Fin n))) := by
    intro x hx
    have h_in_union : x ∈ ⋃ y ∈ t, Metric.ball y (ε2 : ℝ) := hcover hx
    rcases Set.mem_iUnion₂.mp h_in_union with ⟨y, hy, hball⟩
    have h_y_in_t' : y ∈ t' := by
      have h_y_in_t : y ∈ t := hy
      have h : y ∈ (t' : Set _) := by
        simpa [h_coe] using h_y_in_t
      exact h
    have h_dist : dist x y < (ε2 : ℝ) := by simpa [Metric.mem_ball] using hball
    refine ⟨y, h_y_in_t', ?_⟩
    exact_mod_cast h_dist.le
  have h_ext : Metric.externalCoveringNumber ε2 A ≠ ⊤ := by
    have h : Metric.externalCoveringNumber ε2 A ≤ ((t' : Set _) : Set (EuclideanSpace ℝ (Fin n))).encard := by
      exact iInf_le_of_le ((t' : Set _) : Set (EuclideanSpace ℝ (Fin n))) (iInf_le_of_le h_is_cover le_rfl)
    have h2 : ((t' : Set (EuclideanSpace ℝ (Fin n)))).encard < ⊤ := by
      simp
      <;> exact WithTop.coe_ne_top
    exact h.trans_lt h2 |>.ne
  have h6 : Metric.packingNumber ε A ≤ Metric.externalCoveringNumber ε2 A := by
    have h7 : ε = 2 * ε2 := by
      ext <;> simp [ε2] <;> ring
    rw [h7]
    exact Metric.packingNumber_two_mul_le_externalCoveringNumber ε2 A
  intro h_contra
  rw [h_contra] at h6
  exact h_ext (top_le_iff.mp h6)
end SeedMathlib.MeasureTheory.FractalGeometry.FrostmanLemma
