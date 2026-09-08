/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A stopping-time chain for a monotone weight on a finite set

Given a monotone real-valued weight `M` on the subsets of a finite set `F`, bounded below on
nonempty subsets, one can iterate "pass to a subset that loses a factor `A` in cardinality and
gains a factor `B` in weight" only finitely often. The terminal subset of that iteration is
simultaneously large and weight-stable.
-/

@[expose] public section

noncomputable section

namespace Kakeya

/-- **Stopping-time chain.**
Let `F` be a finite nonempty set, `A, B > 1`, and `M` a real-valued function on subsets of `F`
that is bounded below by `m₀ > 0` on nonempty subsets.
Then there are `k : ℕ` and a nonempty `G ⊆ F` with
(i) `|G| ≥ A^(-k) |F|`, (ii) `M(G) ≤ B^(-k) M(F)`, and
(iii) every `H ⊆ G` with `|H| ≥ A⁻¹ |G|` satisfies `M(H) ≥ B⁻¹ M(G)`. -/
lemma stoppingTimeChain {σ : Type*} (F : Finset σ) (hF : F.Nonempty)
    {A B : ℝ} (hA : 1 < A) (hB : 1 < B)
    (M : Finset σ → ℝ)
    {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hMlb : ∀ ⦃S : Finset σ⦄, S ⊆ F → S.Nonempty → m₀ ≤ M S) :
    ∃ (k : ℕ) (G : Finset σ), G ⊆ F ∧ G.Nonempty ∧
      (A ^ k)⁻¹ * (F.card : ℝ) ≤ (G.card : ℝ) ∧
      M G ≤ (B ^ k)⁻¹ * M F ∧
      (∀ ⦃H : Finset σ⦄, H ⊆ G → A⁻¹ * (G.card : ℝ) ≤ (H.card : ℝ) →
        B⁻¹ * M G ≤ M H) := by
  classical
  have hApos : (0:ℝ) < A := by linarith
  have hBpos : (0:ℝ) < B := by linarith
  -- General claim by strong induction on cardinality, relative to each `G`.
  suffices H : ∀ G : Finset σ, G ⊆ F → G.Nonempty →
      ∃ (k : ℕ) (G' : Finset σ), G' ⊆ G ∧ G'.Nonempty ∧
        (A ^ k)⁻¹ * (G.card : ℝ) ≤ (G'.card : ℝ) ∧
        M G' ≤ (B ^ k)⁻¹ * M G ∧
        (∀ ⦃J : Finset σ⦄, J ⊆ G' → A⁻¹ * (G'.card : ℝ) ≤ (J.card : ℝ) →
          B⁻¹ * M G' ≤ M J) from H F subset_rfl hF
  intro G
  induction G using Finset.strongInductionOn with
  | _ G IH =>
  intro hGF hGne
  by_cases hex : ∃ J : Finset σ, J ⊆ G ∧ A⁻¹ * (G.card : ℝ) ≤ (J.card : ℝ) ∧ M J ≤ B⁻¹ * M G
  · obtain ⟨J, hJG, hJcard, hJM⟩ := hex
    have hGcardpos : 0 < (G.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hGne
    have hJcardpos : 0 < (J.card : ℝ) := lt_of_lt_of_le (by positivity) hJcard
    have hJne : J.Nonempty := Finset.card_pos.mp (by exact_mod_cast hJcardpos)
    have hMGpos : 0 < M G := lt_of_lt_of_le hm₀ (hMlb hGF hGne)
    have hJlt : J ⊂ G := Finset.ssubset_iff_subset_ne.mpr ⟨hJG, by
      rintro rfl
      linarith [mul_lt_of_lt_one_left hMGpos ((inv_lt_one₀ hBpos).mpr hB)]⟩
    obtain ⟨k', G', hG'J, hG'ne, hcard', hM', hterm'⟩ := IH J hJlt (hJG.trans hGF) hJne
    refine ⟨k' + 1, G', hG'J.trans hJG, hG'ne, ?_, ?_, hterm'⟩
    · calc (A ^ (k' + 1))⁻¹ * (G.card : ℝ)
          = (A ^ k')⁻¹ * (A⁻¹ * (G.card : ℝ)) := by rw [pow_succ, mul_inv]; ring
        _ ≤ (A ^ k')⁻¹ * (J.card : ℝ) := mul_le_mul_of_nonneg_left hJcard (by positivity)
        _ ≤ (G'.card : ℝ) := hcard'
    · calc M G'
          ≤ (B ^ k')⁻¹ * M J := hM'
        _ ≤ (B ^ k')⁻¹ * (B⁻¹ * M G) := mul_le_mul_of_nonneg_left hJM (by positivity)
        _ = (B ^ (k' + 1))⁻¹ * M G := by rw [pow_succ, mul_inv]; ring
  · refine ⟨0, G, subset_rfl, hGne, by simp, by simp, fun J hJG hJcard => ?_⟩
    by_contra! hcon
    exact hex ⟨J, hJG, hJcard, hcon.le⟩

end Kakeya

end

end
