import MyLeanRepo.Kakeya.Hairbrush.Basic
import MyLeanRepo.Kakeya.Hairbrush.Pigeonhole
import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements

/-!
# Stem averaging via double counting

Given a map from each hair `T ∈ H` to a finset of stems `stems_T T ⊆ F`,
if every hair has at least `L` stems, then some stem is incident to at least
`L * |H| / |F|` hairs.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open Finset

namespace Kakeya.Assouad

/-- General double-counting pigeonhole for hair-stem incidences. -/
lemma stem_averaging_general
    {δ : ℝ} {F H : Kakeya.TubeFamily δ}
    (hF_nonempty : F.Nonempty)
    (stems_T : Kakeya.DeltaTube δ → Finset (Kakeya.DeltaTube δ))
    (h_stems_subset : ∀ T ∈ H, stems_T T ⊆ F)
    (L : ENNReal)
    (hL : ∀ T ∈ H, L ≤ (stems_T T).card) :
    ∃ (stem : Kakeya.DeltaTube δ), stem ∈ F ∧
      (↑((H.filter fun T => stem ∈ stems_T T).card) : ENNReal) ≥
        L * H.enncard / F.enncard := by
  let f : Kakeya.DeltaTube δ → ENNReal := fun U =>
    ↑((H.filter fun T => U ∈ stems_T T).card)
  have h_sum : ∑ U ∈ F, f U = ∑ T ∈ H, (↑(stems_T T).card : ENNReal) := by
    have h1 : ∀ U : Kakeya.DeltaTube δ, f U = ∑ T ∈ H, (if U ∈ stems_T T then (1 : ENNReal) else 0) := by
      intro U
      have h_eq : f U = ∑ T ∈ H, (if U ∈ stems_T T then (1 : ENNReal) else 0) := by
        dsimp only [f]
        rw [Finset.sum_ite]
        ; simp
      exact h_eq
    calc
      ∑ U ∈ F, f U
        = ∑ U ∈ F, ∑ T ∈ H, (if U ∈ stems_T T then (1 : ENNReal) else 0) := by
          apply Finset.sum_congr rfl; intro U _; exact h1 U
      _ = ∑ T ∈ H, ∑ U ∈ F, (if U ∈ stems_T T then (1 : ENNReal) else 0) := by
          rw [Finset.sum_comm]
      _ = ∑ T ∈ H, (↑(stems_T T).card : ENNReal) := by
          apply Finset.sum_congr rfl
          intro T hT
          have h_sub : stems_T T ⊆ F := h_stems_subset T hT
          have h_filter_eq : F.filter (fun U => U ∈ stems_T T) = stems_T T := by
            apply Finset.ext
            intro U
            simp only [Finset.mem_filter]
            ; constructor
            · intro h; exact h.2
            · intro h; exact ⟨h_sub h, h⟩
          rw [Finset.sum_ite, h_filter_eq]
          ; simp
  have h_lower : L * H.enncard ≤ ∑ U ∈ F, f U := by
    rw [h_sum]
    have h : ∑ T ∈ H, (↑(stems_T T).card : ENNReal) ≥ ∑ T ∈ H, L := by
      apply Finset.sum_le_sum
      intro T hT
      exact hL T hT
    have h2 : ∑ T ∈ H, L = H.enncard * L := by
      simp [Kakeya.TubeFamily.enncard, Finset.sum_const, mul_comm]
    rw [h2] at h
    simpa [mul_comm] using h
  by_cases hH_empty : H.Nonempty
  · rcases hH_empty with ⟨T0, hT0⟩
    have hL_finite : L ≠ ⊤ := by
      have h3 : L ≤ (↑(stems_T T0).card : ENNReal) := hL T0 hT0
      exact ne_top_of_le_ne_top (by simp) h3
    have hH_finite : H.enncard ≠ ⊤ := by
      simp [Kakeya.TubeFamily.enncard]
    have hc_finite : L * H.enncard ≠ ⊤ :=
      ENNReal.mul_ne_top hL_finite hH_finite
    have h_pigeon := Kakeya.Hairbrush.ennreal_sum_pigeonhole hc_finite h_lower hF_nonempty
    rcases h_pigeon with ⟨U, hU, hge⟩
    exact ⟨U, hU, hge⟩
  · have hH_eq_empty : H = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hH_empty
    rcases hF_nonempty with ⟨U, hU⟩
    refine ⟨U, hU, ?_⟩
    simp [hH_eq_empty, Kakeya.TubeFamily.enncard]

end Kakeya.Assouad
