module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ActualMarginCpackW102

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uI

/- The finite pruning step in the multiscale blueprint.  The imported
   project theorem performs the max-weight deletion induction; this wrapper
   exposes the metric form used by occupied small ancestors. -/
theorem exists_weighted_separated_subset_w102
    {ι : Type uI} [DecidableEq ι]
    (H : Finset ι) (d : ι → ι → Real) (r : Real) {D : Nat}
    (hr : 0 < r)
    (hsymm : ∀ a b, d a b = d b a)
    (hdiag : ∀ a, d a a = 0)
    (hdeg : ∀ a ∈ H, {b ∈ (H : Set ι) | d b a < r}.ncard ≤ D)
    (w : ι → ENNReal) :
    ∃ J ⊆ H,
      (∀ a ∈ J, ∀ b ∈ J, a ≠ b → r ≤ d a b) ∧
        (∑ a ∈ H, w a) ≤ (D + 1 : Nat) * (∑ a ∈ J, w a) := by
  have hrel_symm : ∀ a b, (a ≠ b ∧ d a b < r) →
      (b ≠ a ∧ d b a < r) := by
    intro a b hab
    refine ⟨Ne.symm hab.1, ?_⟩
    rw [hsymm]
    exact hab.2
  have hrel_irrefl : ∀ a, ¬ (a ≠ a ∧ d a a < r) := by
    intro a haa
    exact haa.1 rfl
  have hdeg_rel : ∀ a ∈ H,
      {b ∈ (H : Set ι) | b ≠ a ∧ d b a < r}.ncard ≤ D := by
    intro a ha
    let S : Finset ι := H.filter (fun b => b ≠ a ∧ d b a < r)
    let T : Finset ι := H.filter (fun b => d b a < r)
    have hSset : (S : Set ι) = {b ∈ (H : Set ι) | b ≠ a ∧ d b a < r} := by
      ext b
      simp [S]
    have hTset : (T : Set ι) = {b ∈ (H : Set ι) | d b a < r} := by
      ext b
      simp [T]
    have hScard : S.card = {b ∈ (H : Set ι) | b ≠ a ∧ d b a < r}.ncard := by
      rw [← hSset]
      rw [Set.ncard_coe_finset]
    have hTcard : T.card = {b ∈ (H : Set ι) | d b a < r}.ncard := by
      rw [← hTset]
      rw [Set.ncard_coe_finset]
    rw [← hScard]
    exact (Finset.card_le_card (by
      intro b hb
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hb).1,
        (Finset.mem_filter.mp hb).2.2⟩)).trans (by
          rw [hTcard]
          exact hdeg a ha)
  obtain ⟨J, hJH, hJpair, hJmass⟩ :=
    Kakeya.exists_pairwise_not_of_degree_le H
      (fun a b => a ≠ b ∧ d a b < r) hrel_symm hrel_irrefl hdeg_rel w
  refine ⟨J, hJH, ?_, hJmass⟩
  intro a ha b hb hab
  have hnrel : ¬ (a ≠ b ∧ d a b < r) := hJpair ha hb hab
  exact le_of_not_gt (fun hlt => hnrel ⟨hab, hlt⟩)

end
end Kakeya.ml1Boot.TrialRestartW94
