module

/-
  Generic S-set refinement utilities for Section 9.

  Provides `IsDeltaSSet.subset_with_cover_ratio`: if `P' ⊆ P`,
  `Ncover(P) ≤ K * Ncover(P')`, and `P` is a `(δ, t, C_P)`-set,
  then `P'` is a `(δ, t, C_P * K)`-set.

  This is a direct consequence of the base `IsDeltaSSet` definition and
  does not depend on any Appendix A modules.

  Whiteprint node: section9 / sset_refinement
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace DirecretisedFurstenbergEstimate.Section9

/-- If `P' ⊆ P`, `Ncover(P) ≤ K * Ncover(P')`, and `P` is a `(δ, s, C)`-set,
    then `P'` is a `(δ, s, C * K)`-set. -/
lemma IsDeltaSSet.subset_with_cover_ratio {X : Type*} [PseudoMetricSpace X]
    {δ s C : ℝ} {S S' : Set X} {K : ℝ} (hK_pos : 0 < K)
    (hS : IsDeltaSSet δ s C S)
    (hS'_sub : S' ⊆ S)
    (h_ratio : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤
               ENNReal.ofReal K * (Metric.externalCoveringNumber δ.toNNReal S')) :
    IsDeltaSSet δ s (C * K) S' := by
  rcases hS with ⟨hS_nonempty, hδ_pos, hC_pos, hs_nonneg, h_main⟩
  have hKC_pos : 0 < C * K := mul_pos hC_pos hK_pos
  have hS'_nonempty : S'.Nonempty := by
    by_contra h
    have h_empty : S' = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using h
    rw [h_empty] at h_ratio
    have h_zero : Metric.externalCoveringNumber δ.toNNReal S = 0 := by
      have h_le : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤ 0 := by
        simpa [Metric.externalCoveringNumber_empty] using h_ratio
      exact le_zero_iff.mp (by exact_mod_cast h_le)
    have hS_empty : S = ∅ := Metric.externalCoveringNumber_eq_zero.mp h_zero
    rw [hS_empty] at hS_nonempty
    simp at hS_nonempty
  refine' ⟨hS'_nonempty, hδ_pos, hKC_pos, hs_nonneg, _⟩
  intro x r hr
  have h_sub : S' ∩ Metric.closedBall x r ⊆ S ∩ Metric.closedBall x r := by
    intro y hy
    exact ⟨hS'_sub hy.1, hy.2⟩
  have h1 : (Metric.externalCoveringNumber δ.toNNReal (S' ∩ Metric.closedBall x r) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall x r) : ENNReal) := by
    have h11 := Metric.externalCoveringNumber_mono_set (ε := δ.toNNReal) h_sub
    exact_mod_cast h11
  have h2 := h_main x r hr
  have hC_nonneg : 0 ≤ C := by linarith
  calc (Metric.externalCoveringNumber δ.toNNReal (S' ∩ Metric.closedBall x r) : ENNReal)
    ≤ (Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall x r) : ENNReal) := h1
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := h2
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal K * Metric.externalCoveringNumber δ.toNNReal S') := by
      gcongr
    _ = ENNReal.ofReal (C * K) * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ.toNNReal S' := by
      have h_mul : ENNReal.ofReal C * ENNReal.ofReal K = ENNReal.ofReal (C * K) := by
        rw [← ENNReal.ofReal_mul hC_nonneg]
        <;> ring
      have h_assoc : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal K * Metric.externalCoveringNumber δ.toNNReal S') =
          (ENNReal.ofReal C * ENNReal.ofReal K) * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ.toNNReal S' := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      rw [h_assoc, h_mul] <;> simp [mul_assoc]

end DirecretisedFurstenbergEstimate.Section9
