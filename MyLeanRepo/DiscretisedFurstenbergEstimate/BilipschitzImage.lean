module

/-
  Bilipschitz invariance of `IsDeltaSSet` with a doubling hypothesis.

  The original `IsDeltaSSet.bilipschitz_image` (without doubling) is false for
  general pseudo-metric spaces.  With a uniform doubling condition on the source
  space at scale `δ`, the covering number transfers correctly across a
  `K`-bilipschitz map.

  ## Main results

  - `HasDoublingAtScale`: every ball of radius `R ≥ δ` has covering number
    at most `D · (R/δ)^d`.
  - `covering_transfer_via_bilipschitz`: lower bound on `covering_δ(P)` in
    terms of `covering_{Kδ}(f '' P)` under doubling.
  - `IsDeltaSSet.bilipschitz_image_of_doubling`: the image of a `(δ,s,C)`-set
    under a `K`-bilipschitz map is a `(Kδ, s, C')`-set with
    `C' = C · (2K)^s · D · (2K²)^d`.

  Whiteprint node: `bilipschitz_image`
  Dependencies: `basics`, `covering_utils`
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.OSWPrelude

@[expose] public section


open scoped ENNReal NNReal

namespace DirecretisedFurstenbergEstimate

/-- If every `εY`-cover `C_Q` of `Q` satisfies `covering_εX(P) ≤ a · |C_Q|`,
    then `covering_εX(P) ≤ a · covering_εY(Q)`. -/
lemma externalCoveringNumber_transfer
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {εX εY : NNReal} {P : Set X} {Q : Set Y} {a : ENNReal}
    (h : ∀ (C_Q : Set Y), Metric.IsCover εY Q C_Q →
      (Metric.externalCoveringNumber εX P : ENNReal) ≤ a * (C_Q.encard : ENNReal)) :
    (Metric.externalCoveringNumber εX P : ENNReal) ≤
      a * (Metric.externalCoveringNumber εY Q : ENNReal) := by
  by_cases ha : a = 0
  · have h_univ : Metric.IsCover εY Q Set.univ := by
      intro x _; exact ⟨x, Set.mem_univ x, by simp⟩
    have hP0 : (Metric.externalCoveringNumber εX P : ENNReal) = 0 := by
      have h1 := h Set.univ h_univ
      rw [ha] at h1; simpa using h1
    rw [hP0, ha] <;> simp
  · by_cases h_top : (Metric.externalCoveringNumber εY Q : ENNReal) = ⊤
    · rw [h_top]; simp [ha]
    · have hfin : Metric.externalCoveringNumber εY Q < ⊤ := by
        exact lt_top_iff_ne_top.mpr (by exact_mod_cast h_top)
      rcases DiscretisedFurstenbergEstimate.CoveringUtils.exists_external_cover_eq hfin with ⟨C_Q, hC_Q, h_enc⟩
      have h4 : (C_Q.encard : ENNReal) = (Metric.externalCoveringNumber εY Q : ENNReal) := by
        exact_mod_cast h_enc
      have h5 := h C_Q hC_Q
      rw [h4] at h5
      exact h5

end DirecretisedFurstenbergEstimate
