module

/-
  Common Section 6 lemmas shared between B1ToSection6 and PerSquareRetention.

  Extracted from Section6_Assembly to break the circular/legacy dependency.

  Contains:
  - thin_preserves_sset_by_density — density-aware S-set restriction
  - Re-exports clean square/grid lemmas from CombiningTheoremRework.CleanSquareLemmas:
    - ball_intersects_at_most_9_squares
    - fine_square_subset_coarse
    - pointSet_ncover_bound

  Whiteprint node: section6_common_lemmas
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CleanSquareLemmas
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section6

open DiscretisedFurstenbergEstimate

/-! ========================================================================
   Density-aware S-set preservation (general helper)
   ======================================================================== -/

/-- Density-aware S-set preservation under subsets. -/
lemma thin_preserves_sset_by_density
    {X : Type*} [PseudoMetricSpace X]
    {δ s C K : ℝ} {E E' : Set X}
    (hE : IsDeltaSSet δ s C E)
    (h_sub : E' ⊆ E)
    (hE'_nonempty : E'.Nonempty)
    (hK_pos : 0 < K)
    (h_density : (Metric.externalCoveringNumber δ.toNNReal E : ENNReal) ≤
                 ENNReal.ofReal K * (Metric.externalCoveringNumber δ.toNNReal E' : ENNReal)) :
    IsDeltaSSet δ s (C * K) E' := by
  rcases hE with ⟨_, hδ_pos, hC_pos, hs_nonneg, hcover⟩
  have hCK_pos : 0 < C * K := mul_pos hC_pos hK_pos
  have hCK : ENNReal.ofReal C * ENNReal.ofReal K = ENNReal.ofReal (C * K) := by
    rw [←ENNReal.ofReal_mul hC_pos.le] <;> rfl
  refine' ⟨hE'_nonempty, hδ_pos, hCK_pos, hs_nonneg, _⟩
  intro x r hr
  let N_E' := (Metric.externalCoveringNumber δ.toNNReal E' : ENNReal)
  let N_E := (Metric.externalCoveringNumber δ.toNNReal E : ENNReal)
  have h1 : (Metric.externalCoveringNumber δ.toNNReal (E' ∩ Metric.closedBall x r) : ENNReal) ≤
            (Metric.externalCoveringNumber δ.toNNReal (E ∩ Metric.closedBall x r) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set (by gcongr)
  have h2 := hcover x r hr
  have h3 : N_E ≤ ENNReal.ofReal K * N_E' := h_density
  have h4 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * N_E ≤
            ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal K * N_E') := by gcongr
  have h5 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal K * N_E') =
            (ENNReal.ofReal C * ENNReal.ofReal K) * (ENNReal.ofReal r) ^ s * N_E' := by
    simp [mul_assoc, mul_comm, mul_left_comm]
  have h6 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal K * N_E') ≤
            ENNReal.ofReal (C * K) * (ENNReal.ofReal r) ^ s * N_E' := by
    rw [h5, hCK]
  exact le_trans (le_trans h1 h2) (le_trans h4 h6)

end DirecretisedFurstenbergEstimate.Section6

end
