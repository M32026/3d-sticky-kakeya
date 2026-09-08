/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Maximal δ-separated subsets

A standard greedy-packing argument: a Frostman-regular set contains a
δ-separated subset of cardinality at least `(ρ / C_F) · δ^{1-n}`.
-/

@[expose] public section

open scoped ENNReal NNReal MeasureTheory

namespace Tube

/-- A δ-separated subset of a Frostman-regular set has cardinality at least
`(ρ / C_F) · δ^{1-n}`.  The constant depends only on `n` and on the Frostman constant `C_F` of
`σ`, not on `ρ` or `δ`. -/
theorem maximal_separated_subset
    {n : ℕ} (hn : 1 ≤ n)
    {σ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))}
    {C_F : ℝ} (hC_F_pos : 0 < C_F)
    (hσ_frost : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 ≤ r →
        σ (Metric.closedBall x r) ≤ ENNReal.ofReal (C_F * r ^ (n - 1)))
    {F : Set (EuclideanSpace ℝ (Fin n))}
    {ρ : ℝ} (hρ : 0 < ρ)
    (hσF : σ F ≥ ENNReal.ofReal ρ) {δ : ℝ} (hδ_pos : 0 < δ) :
    ∃ (Ω : Finset (EuclideanSpace ℝ (Fin n))),
      (↑Ω : Set _) ⊆ F ∧
      (∀ ω₁ ∈ Ω, ∀ ω₂ ∈ Ω, ω₁ ≠ ω₂ → δ ≤ dist ω₁ ω₂) ∧
      (Ω.card : ℝ) ≥ (ρ / C_F) * δ ^ (1 - (n : ℤ)) := by
  classical
  set P : Finset (EuclideanSpace ℝ (Fin n)) → Prop :=
    fun Ω => (↑Ω : Set _) ⊆ F ∧
      (∀ ω₁ ∈ Ω, ∀ ω₂ ∈ Ω, ω₁ ≠ ω₂ → δ ≤ dist ω₁ ω₂) with hP_def
  have hδ_npow_pos : (0 : ℝ) < δ ^ (n - 1) := pow_pos hδ_pos _
  have hδ_zpow_pos : (0 : ℝ) < δ ^ (1 - (n : ℤ)) := zpow_pos hδ_pos _
  have hC_F_ne : C_F ≠ 0 := ne_of_gt hC_F_pos
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
  have hδ_npow_ne : δ ^ (n - 1) ≠ 0 := ne_of_gt hδ_npow_pos
  set target : ℝ := (ρ / C_F) * δ ^ (1 - (n : ℤ)) with htarget_def
  have htarget_pos : 0 < target := mul_pos (div_pos hρ hC_F_pos) hδ_zpow_pos
  by_contra h_contra
  push Not at h_contra
  have h_lt : ∀ Ω : Finset (EuclideanSpace ℝ (Fin n)), P Ω → (Ω.card : ℝ) < target := by
    intro Ω hΩ
    exact h_contra Ω hΩ.1 hΩ.2
  have hP_empty : P (∅ : Finset (EuclideanSpace ℝ (Fin n))) := by
    refine ⟨?_, ?_⟩
    · intro x hx; simp at hx
    · intro ω₁ hω₁; simp at hω₁
  set M : ℕ := ⌈target⌉₊ with hM_def
  have h_card_le_M : ∀ Ω : Finset (EuclideanSpace ℝ (Fin n)), P Ω → Ω.card ≤ M := by
    intro Ω hΩ
    have h1 : (Ω.card : ℝ) ≤ target := (h_lt Ω hΩ).le
    have h2 : (Ω.card : ℝ) ≤ (M : ℝ) := h1.trans (Nat.le_ceil _)
    exact_mod_cast h2
  have h_exists_max :
      ∃ k : ℕ, k ≤ M ∧ (∃ Ω : Finset (EuclideanSpace ℝ (Fin n)), P Ω ∧ Ω.card = k) ∧
        ∀ k' : ℕ, k < k' → k' ≤ M →
          ¬ ∃ Ω : Finset (EuclideanSpace ℝ (Fin n)), P Ω ∧ Ω.card = k' := by
    let Q : ℕ → Prop := fun k => ∃ Ω : Finset (EuclideanSpace ℝ (Fin n)), P Ω ∧ Ω.card = k
    have hQ_dec : DecidablePred Q := Classical.decPred Q
    refine ⟨Nat.findGreatest Q M, Nat.findGreatest_le M, ?_, ?_⟩
    · have hQ0 : Q 0 := ⟨∅, hP_empty, by simp⟩
      have : Nat.findGreatest Q M ≥ 0 := Nat.zero_le _
      exact Nat.findGreatest_spec (Nat.zero_le M) hQ0
    · intro k' hk' hk'_le hQk'
      have : k' ≤ Nat.findGreatest Q M := Nat.le_findGreatest hk'_le hQk'
      exact absurd this (not_le.mpr hk')
  obtain ⟨kmax, hkmax_le, ⟨Ω, hP_Ω, hΩ_card⟩, hΩ_max⟩ := h_exists_max
  have h_cover : ∀ x ∈ F, ∃ ω ∈ Ω, dist x ω ≤ δ := by
    intro x hxF
    by_cases hxΩ : x ∈ Ω
    · exact ⟨x, hxΩ, by simp [hδ_pos.le]⟩
    by_contra h_no_close
    push Not at h_no_close
    let Ω' : Finset (EuclideanSpace ℝ (Fin n)) := insert x Ω
    have hΩ'_subset : (↑Ω' : Set _) ⊆ F := by
      intro y hy
      simp only [Ω', Finset.coe_insert, Set.mem_insert_iff] at hy
      rcases hy with rfl | hyΩ
      · exact hxF
      · exact hP_Ω.1 hyΩ
    have hΩ'_sep : ∀ ω₁ ∈ Ω', ∀ ω₂ ∈ Ω', ω₁ ≠ ω₂ → δ ≤ dist ω₁ ω₂ := by
      intro ω₁ h₁ ω₂ h₂ h_ne
      simp only [Ω', Finset.mem_insert] at h₁ h₂
      rcases h₁ with rfl | h₁Ω
      · rcases h₂ with rfl | h₂Ω
        · exact (h_ne rfl).elim
        · exact (h_no_close ω₂ h₂Ω).le
      · rcases h₂ with rfl | h₂Ω
        · rw [dist_comm]
          exact (h_no_close ω₁ h₁Ω).le
        · exact hP_Ω.2 ω₁ h₁Ω ω₂ h₂Ω h_ne
    have hP_Ω' : P Ω' := ⟨hΩ'_subset, hΩ'_sep⟩
    have hΩ'_card : Ω'.card = kmax + 1 := by
      simp only [Ω', Finset.card_insert_of_notMem hxΩ, hΩ_card]
    have hΩ'_card_le : Ω'.card ≤ M := h_card_le_M Ω' hP_Ω'
    have hkmax_lt : kmax < kmax + 1 := Nat.lt_succ_self kmax
    have hkmax_succ_le : kmax + 1 ≤ M := by rw [← hΩ'_card]; exact hΩ'_card_le
    exact hΩ_max (kmax + 1) hkmax_lt hkmax_succ_le ⟨Ω', hP_Ω', hΩ'_card⟩
  have hF_subset : F ⊆ ⋃ ω ∈ Ω, Metric.closedBall ω δ := by
    intro x hxF
    obtain ⟨ω, hω, h_dist⟩ := h_cover x hxF
    simp only [Set.mem_iUnion]
    exact ⟨ω, by simp [hω, Metric.mem_closedBall, h_dist]⟩
  have hσF_le_union : σ F ≤ σ (⋃ ω ∈ Ω, Metric.closedBall ω δ) :=
    MeasureTheory.measure_mono hF_subset
  have hσ_union_le_sum :
      σ (⋃ ω ∈ Ω, Metric.closedBall ω δ) ≤
        ∑ ω ∈ Ω, σ (Metric.closedBall ω δ) :=
    MeasureTheory.measure_biUnion_finset_le Ω _
  have hσ_each_le : ∀ ω ∈ Ω, σ (Metric.closedBall ω δ) ≤
      ENNReal.ofReal (C_F * δ ^ (n - 1)) := fun ω _ => hσ_frost ω δ hδ_pos.le
  have hsum_le :
      ∑ ω ∈ Ω, σ (Metric.closedBall ω δ) ≤
        ∑ _ω ∈ Ω, ENNReal.ofReal (C_F * δ ^ (n - 1)) :=
    Finset.sum_le_sum hσ_each_le
  have hsum_eq :
      ∑ _ω ∈ Ω, ENNReal.ofReal (C_F * δ ^ (n - 1)) =
        Ω.card • ENNReal.ofReal (C_F * δ ^ (n - 1)) := by
    simp [Finset.sum_const]
  have hcombined : ENNReal.ofReal ρ ≤
      Ω.card • ENNReal.ofReal (C_F * δ ^ (n - 1)) := by
    calc ENNReal.ofReal ρ
        ≤ σ F := hσF
      _ ≤ σ (⋃ ω ∈ Ω, Metric.closedBall ω δ) := hσF_le_union
      _ ≤ ∑ ω ∈ Ω, σ (Metric.closedBall ω δ) := hσ_union_le_sum
      _ ≤ ∑ _ω ∈ Ω, ENNReal.ofReal (C_F * δ ^ (n - 1)) := hsum_le
      _ = Ω.card • ENNReal.ofReal (C_F * δ ^ (n - 1)) := hsum_eq
  have hC_F_δ_nn : (0 : ℝ) ≤ C_F * δ ^ (n - 1) :=
    mul_nonneg hC_F_pos.le hδ_npow_pos.le
  have hcombined_real : ρ ≤ (Ω.card : ℝ) * (C_F * δ ^ (n - 1)) := by
    have hsmul_eq : (Ω.card : ℕ) • ENNReal.ofReal (C_F * δ ^ (n - 1))
        = ENNReal.ofReal ((Ω.card : ℝ) * (C_F * δ ^ (n - 1))) := by
      rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast (Ω.card),
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    rw [hsmul_eq] at hcombined
    have h_nn : (0 : ℝ) ≤ (Ω.card : ℝ) * (C_F * δ ^ (n - 1)) :=
      mul_nonneg (Nat.cast_nonneg _) hC_F_δ_nn
    exact (ENNReal.ofReal_le_ofReal_iff h_nn).mp hcombined
  have h_target_eq : target = ρ / (C_F * δ ^ (n - 1)) := by
    change (ρ / C_F) * δ ^ (1 - (n : ℤ)) = ρ / (C_F * δ ^ (n - 1))
    have h_zpow : δ ^ (1 - (n : ℤ)) = (δ ^ (n - 1))⁻¹ := by
      have h_eq : (1 - (n : ℤ)) = -((n : ℤ) - 1) := by ring
      rw [h_eq, zpow_neg]
      congr 1
      have hn1 : ((n : ℤ) - 1) = ((n - 1 : ℕ) : ℤ) := by omega
      rw [hn1, zpow_natCast]
    rw [h_zpow]
    field_simp
  have hCFδ_pos : 0 < C_F * δ ^ (n - 1) := mul_pos hC_F_pos hδ_npow_pos
  have h_card_ge_target : (Ω.card : ℝ) ≥ target := by
    rw [h_target_eq, ge_iff_le, div_le_iff₀ hCFδ_pos]
    exact hcombined_real
  exact absurd (h_lt Ω hP_Ω) (not_lt.mpr h_card_ge_target)

end Tube
