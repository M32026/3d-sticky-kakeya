import MyLeanRepo.Kakeya.Cinematic.Geometry
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.DerivativeBound
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Curvature sign lemma

Using the cinematic curvature gap and uniform derivative/value bounds,
show that h'' has constant sign and is bounded away from zero.
-/

namespace Kakeya.Cinematic

open Set

/--
If |h| ≤ M, |h'| ≤ M' on [a,b], and the curvature gap gives
|h| + |h'| + |h''| ≥ d/K, with M + M' < d/K, then |h''| ≥ d/K - M - M' > 0
and h'' has constant sign on [a,b].
-/
lemma curvature_constant_sign
    {h h' h'' : ℝ → ℝ} {a b d K M M' : ℝ}
    (hab : a < b)
    (hK : 1 ≤ K)
    (hd_pos : 0 < d)
    (h''_cont : ContinuousOn h'' (Icc a b))
    (h_curv : ∀ x ∈ Icc a b, d / K ≤ |h x| + |h' x| + |h'' x|)
    (h_val : ∀ x ∈ Icc a b, |h x| ≤ M)
    (h_deriv : ∀ x ∈ Icc a b, |h' x| ≤ M')
    (h_small : M + M' < d / K) :
    (∀ x ∈ Icc a b, d / K - M - M' ≤ |h'' x|) ∧
    ((∀ x ∈ Icc a b, 0 < h'' x) ∨ (∀ x ∈ Icc a b, h'' x < 0)) := by
  set c := d / K - M - M' with hc_def
  have hc_pos : 0 < c := by
    dsimp only [c]
    have hK_pos : 0 < K := by linarith
    have h1 : 0 < d / K := by positivity
    linarith

  have h_lower : ∀ x ∈ Icc a b, c ≤ |h'' x| := by
    intro x hx
    have h1 : d / K ≤ |h x| + |h' x| + |h'' x| := h_curv x hx
    have h2 : |h x| ≤ M := h_val x hx
    have h3 : |h' x| ≤ M' := h_deriv x hx
    have h4 : |h x| + |h' x| + |h'' x| ≤ M + M' + |h'' x| := by linarith
    linarith

  have h_no_zero : ∀ x ∈ Icc a b, h'' x ≠ 0 := by
    intro x hx
    have h5 : c ≤ |h'' x| := h_lower x hx
    intro h6
    rw [h6] at h5
    simp at h5 <;> linarith

  have h_sign : (∀ x ∈ Icc a b, 0 < h'' x) ∨ (∀ x ∈ Icc a b, h'' x < 0) := by
    by_cases h_pos_at_a : 0 < h'' a
    · left
      intro x hx
      by_contra h_nonpos
      have h_le : h'' x < 0 := by
        have h : h'' x ≤ 0 := by linarith
        have h' : h'' x ≠ 0 := h_no_zero x hx
        by_contra h''; exact h' (by linarith)
      have h_cont' : ContinuousOn h'' (Icc a x) :=
        h''_cont.mono (Icc_subset_Icc (by linarith [hx.1]) (by linarith [hx.2]))
      have hg_cont : ContinuousOn (fun y => -h'' y) (Icc a x) := h_cont'.neg
      have h1 : (-h'' a) < 0 := by linarith
      have h2 : 0 < (-h'' x) := by linarith
      have h0_in : (0 : ℝ) ∈ Set.Ioo (-h'' a) (-h'' x) := ⟨h1, h2⟩
      have h_ivt : (0 : ℝ) ∈ (fun y => -h'' y) '' Set.Ioo a x :=
        intermediate_value_Ioo (by linarith [hx.1]) hg_cont h0_in
      rcases h_ivt with ⟨ξ, hξ, hξ_zero⟩
      have h''ξ_zero : h'' ξ = 0 := by simpa using hξ_zero
      have hξ_in : ξ ∈ Icc a b := ⟨le_of_lt hξ.1, le_trans (le_of_lt hξ.2) hx.2⟩
      exact h_no_zero ξ hξ_in h''ξ_zero
    · have h_neg_at_a : h'' a < 0 := by
        have h : h'' a ≠ 0 := h_no_zero a (left_mem_Icc.mpr (by linarith))
        by_contra h'; exact h (by linarith)
      right
      intro x hx
      by_contra h_nonneg
      have h_ge : h'' x > 0 := by
        have h : 0 ≤ h'' x := by linarith
        have h' : h'' x ≠ 0 := h_no_zero x hx
        by_contra h''; exact h' (by linarith)
      have h_cont' : ContinuousOn h'' (Icc a x) :=
        h''_cont.mono (Icc_subset_Icc (by linarith [hx.1]) (by linarith [hx.2]))
      have h0_in : (0 : ℝ) ∈ Set.Ioo (h'' a) (h'' x) := ⟨h_neg_at_a, h_ge⟩
      have h_ivt : (0 : ℝ) ∈ h'' '' Set.Ioo a x :=
        intermediate_value_Ioo (by linarith [hx.1]) h_cont' h0_in
      rcases h_ivt with ⟨ξ, hξ, hξ_zero⟩
      have hξ_in : ξ ∈ Icc a b := ⟨le_of_lt hξ.1, le_trans (le_of_lt hξ.2) hx.2⟩
      exact h_no_zero ξ hξ_in hξ_zero

  exact ⟨h_lower, h_sign⟩

end Kakeya.Cinematic
