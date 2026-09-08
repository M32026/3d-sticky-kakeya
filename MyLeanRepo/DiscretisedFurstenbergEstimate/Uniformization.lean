/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Uniformization Lemmas (OS Lemmas 7.1–7.2)

Formalizes the "bottom-to-top" pigeonholing argument that extracts a
multi-scale uniform subset from a finite point set.

## Main results

- `exists_subset_half_weight`: select N elements retaining ≥ half the total weight.
- `pigeonhole_dyadic_range`: find a dyadic count range capturing a logarithmic fraction.
- `uniformize_one_step`: one level of uniformization.
- `uniformization`: multi-level uniformization (OS Lemma 7.1).

## References

- Orponen–Sahlsten, *Improved bounds for Furstenberg sets*, Section 7.
-/

open Finset
open scoped BigOperators

namespace DiscretisedFurstenbergEstimate.Uniformization

-- ============================================================================
-- 1. Weight selection
-- ============================================================================

/-- Given `items` with weight `w`, if `N ≤ |items| ≤ 2N` and `N > 0`, there
    exists an `N`-element subset whose total weight is at least half of the
    total weight of `items`. -/
lemma exists_subset_half_weight {α : Type*} [DecidableEq α]
    (items : Finset α) (w : α → ℕ) (N : ℕ) (hNpos : 0 < N)
    (h1 : N ≤ items.card) (h2 : items.card ≤ 2 * N) :
    ∃ selected : Finset α, selected ⊆ items ∧ selected.card = N ∧
      2 * (∑ x ∈ selected, w x) ≥ ∑ x ∈ items, w x := by
  let candidates := powersetCard N items
  have hnonempty : candidates.Nonempty :=
    powersetCard_nonempty.mpr h1
  rcases Finset.exists_max_image candidates (fun S : Finset α => ∑ x ∈ S, w x) hnonempty
    with ⟨selected, hsel, hmax⟩
  have hsub : selected ⊆ items := (mem_powersetCard.mp hsel).1
  have hcard : selected.card = N := (mem_powersetCard.mp hsel).2
  by_cases h : 2 * (∑ x ∈ selected, w x) ≥ ∑ x ∈ items, w x
  · exact ⟨selected, hsub, hcard, h⟩
  · have hdisj1 : Disjoint selected (items \ selected) := by
      simp [Finset.disjoint_left] <;> tauto
    have h4 : (∑ x ∈ items, w x) =
        (∑ x ∈ selected, w x) + (∑ x ∈ (items \ selected), w x) := by
      rw [← Finset.sum_union hdisj1, Finset.union_sdiff_of_subset hsub]
    have h3 : (∑ x ∈ (items \ selected), w x) > (∑ x ∈ selected, w x) := by linarith
    have hTcard : (items \ selected).card ≤ N := by
      have h5 : (items \ selected).card + selected.card = items.card := by
        have h51 : (selected ∪ (items \ selected)).card = selected.card + (items \ selected).card :=
          Finset.card_union_of_disjoint hdisj1
        have h52 : selected ∪ (items \ selected) = items := Finset.union_sdiff_of_subset hsub
        rw [h52] at h51
        omega
      omega
    have h6 : N - (items \ selected).card ≤ selected.card := by
      rw [hcard] <;> omega
    have h7 : (powersetCard (N - (items \ selected).card) selected).Nonempty :=
      powersetCard_nonempty.mpr h6
    rcases h7 with ⟨A, hA⟩
    have hA1 : A ⊆ selected := (mem_powersetCard.mp hA).1
    have hA2 : A.card = N - (items \ selected).card := (mem_powersetCard.mp hA).2
    let S' := (items \ selected) ∪ A
    have hS'2 : S' ⊆ items := by
      have h1 : (items \ selected) ⊆ items := by simp
      have h2 : A ⊆ items := hA1.trans hsub
      exact Finset.union_subset h1 h2
    have hdisj2 : Disjoint (items \ selected) A := by
      simp [Finset.disjoint_left] <;> tauto
    have hS'3 : S'.card = N := by
      rw [Finset.card_union_of_disjoint hdisj2, hA2] <;> omega
    have hS'in : S' ∈ candidates := by
      exact mem_powersetCard.mpr ⟨hS'2, hS'3⟩
    have h10 : (∑ x ∈ S', w x) > (∑ x ∈ selected, w x) := by
      have h11 : (items \ selected) ⊆ S' := by simp [S']
      have h12 : (∑ x ∈ (items \ selected), w x) ≤ (∑ x ∈ S', w x) :=
        Finset.sum_le_sum_of_subset_of_nonneg h11 (fun _ _ _ => Nat.zero_le _)
      linarith
    have h11 := hmax S' hS'in
    exact False.elim (not_le.mpr h10 h11)

-- ============================================================================
-- 2. Helper: Real.log 2 ≥ 1/2
-- ============================================================================

lemma half_le_log2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h1 : (-1 / 2 : ℝ) + 1 ≤ Real.exp (-1 / 2 : ℝ) :=
    Real.add_one_le_exp (-1 / 2 : ℝ)
  have h2 : (1 / 2 : ℝ) ≤ Real.exp (-1 / 2 : ℝ) := by
    have h21 : (-1 / 2 : ℝ) + 1 = (1 / 2 : ℝ) := by ring
    rw [h21] at h1; exact h1
  have h3 : Real.exp (-1 / 2 : ℝ) = (Real.exp (1 / 2 : ℝ))⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.exp_neg]
  have h4 : (1 / 2 : ℝ) ≤ (Real.exp (1 / 2 : ℝ))⁻¹ := by
    rw [← h3]; exact h2
  have h5 : (0 : ℝ) < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
  have h6 : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have h7 : (1 / 2 : ℝ) ≤ (Real.exp (1 / 2 : ℝ))⁻¹ := h4
    have h8 : (Real.exp (1 / 2 : ℝ))⁻¹ * Real.exp (1 / 2 : ℝ) = 1 := by
      field_simp [h5.ne'] <;> ring
    have h9 : (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) ≤ 1 := by
      calc
        (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ)
          ≤ (Real.exp (1 / 2 : ℝ))⁻¹ * Real.exp (1 / 2 : ℝ) := by gcongr
        _ = 1 := h8
    linarith
  have h10 : (1 / 2 : ℝ) = Real.log (Real.exp (1 / 2 : ℝ)) := by
    rw [Real.log_exp] <;> ring
  rw [h10]
  exact Real.log_le_log (by positivity) h6

-- ============================================================================
-- 3. Dyadic pigeonholing
-- ============================================================================

lemma nat_log2_mono {a b : ℕ} (h : a ≤ b) : Nat.log 2 a ≤ Nat.log 2 b := by
  by_cases ha : a = 0
  · simp [ha]
  · by_cases hb : b = 0
    · exfalso; omega
    · by_contra hgt
      have h3 : Nat.log 2 b < Nat.log 2 a := by omega
      have h4 : Nat.log 2 b + 1 ≤ Nat.log 2 a := by omega
      have h5 : (2 : ℕ) ^ (Nat.log 2 b + 1) ≤ (2 : ℕ) ^ (Nat.log 2 a) := by
        gcongr <;> omega
      have h6 : b < (2 : ℕ) ^ (Nat.log 2 b + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num) b
      have h7 : (2 : ℕ) ^ (Nat.log 2 a) ≤ a := Nat.pow_log_le_self 2 ha
      have h8 : (2 : ℕ) ^ (Nat.log 2 b + 1) ≤ b := by
        calc
          (2 : ℕ) ^ (Nat.log 2 b + 1) ≤ (2 : ℕ) ^ (Nat.log 2 a) := h5
          _ ≤ a := h7
          _ ≤ b := h
      omega

/-- Given `Qs` with count function `c : α → ℕ` and weight `w : α → ℕ`,
    with `1 ≤ c Q ≤ M` for all `Q ∈ Qs`, find `N : ℕ` such that the total
    weight of `Q` with `N ≤ c Q < 2*N` is at least `total / (6 * Real.log M)`. -/
lemma pigeonhole_dyadic_range {α : Type*} [DecidableEq α]
    (Qs : Finset α) (c : α → ℕ) (w : α → ℕ)
    (M : ℕ) (hM : 1 < M)
    (hc1 : ∀ Q ∈ Qs, 1 ≤ c Q)
    (hc2 : ∀ Q ∈ Qs, c Q ≤ M) :
    ∃ N : ℕ, 0 < N ∧
      let range := Qs.filter (fun Q => N ≤ c Q ∧ c Q < 2 * N)
      (∑ Q ∈ range, w Q : ℝ) * (6 * Real.log M) ≥ (∑ Q ∈ Qs, w Q : ℝ) := by
  by_cases hQs : Qs = ∅
  · refine ⟨1, by norm_num, ?_⟩
    simp [hQs] <;> norm_num
  · let K : ℕ := Nat.log 2 M + 1
    have hMne : M ≠ 0 := by omega
    have hM2 : M < 2 ^ K := by
      simpa [K] using Nat.lt_pow_succ_log_self (by norm_num) M
    have hKpos : 0 < K := by simp [K, hM] <;> omega
    let ranges : ℕ → Finset α := fun k =>
      Qs.filter (fun Q => 2 ^ k ≤ c Q ∧ c Q < 2 ^ (k + 1))
    have hcover : ∀ Q ∈ Qs, ∃ k, k ∈ Finset.range K ∧ Q ∈ ranges k := by
      intro Q hQ
      have hcq1 : c Q ≠ 0 := by
        have h : 1 ≤ c Q := hc1 Q hQ
        omega
      let k : ℕ := Nat.log 2 (c Q)
      have hk1 : 2 ^ k ≤ c Q := Nat.pow_log_le_self 2 hcq1
      have hk2 : c Q < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) (c Q)
      have hkK : k < K := by
        have h : c Q ≤ M := hc2 Q hQ
        have h' : Nat.log 2 (c Q) ≤ Nat.log 2 M := nat_log2_mono h
        simp [K, k] <;> omega
      exact ⟨k, Finset.mem_range.mpr hkK, by
        simp only [ranges, mem_filter] <;> exact ⟨hQ, ⟨hk1, hk2⟩⟩⟩
    have hdisj : Set.PairwiseDisjoint (Finset.range K : Set ℕ) ranges := by
      intro k _ l _ hne
      simp only [ranges, Finset.disjoint_left, mem_filter]
      intro Q hQ1 hQ2
      have h1 : 2 ^ k ≤ c Q ∧ c Q < 2 ^ (k + 1) := hQ1.2
      have h2 : 2 ^ l ≤ c Q ∧ c Q < 2 ^ (l + 1) := hQ2.2
      have h3 : k ≤ l := by
        by_contra h4; have h5 : l < k := by omega
        have h6 : 2 ^ (l + 1) ≤ 2 ^ k := by gcongr <;> omega
        omega
      have h4 : l ≤ k := by
        by_contra h5; have h6 : k < l := by omega
        have h7 : 2 ^ (k + 1) ≤ 2 ^ l := by gcongr <;> omega
        omega
      have h5 : k = l := by omega
      exact hne h5
    have hbunion : (Finset.range K).biUnion ranges = Qs := by
      ext Q
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨k, _, hQ⟩
        exact (Finset.mem_filter.mp hQ).1
      · intro hQ
        rcases hcover Q hQ with ⟨k, hk, hQr⟩
        exact ⟨k, hk, hQr⟩
    have hsum : ∑ k ∈ Finset.range K, (∑ Q ∈ ranges k, w Q) = ∑ Q ∈ Qs, w Q := by
      rw [← Finset.sum_biUnion hdisj, hbunion]
    have hpg : ∃ k ∈ Finset.range K,
        (∑ Q ∈ ranges k, w Q : ℝ) * (K : ℝ) ≥ (∑ Q ∈ Qs, w Q : ℝ) := by
      by_contra h
      push Not at h
      have hKpos' : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
      have h' : (∑ k ∈ Finset.range K, (∑ Q ∈ ranges k, w Q : ℝ)) < (∑ Q ∈ Qs, w Q : ℝ) := by
        calc
          (∑ k ∈ Finset.range K, (∑ Q ∈ ranges k, w Q : ℝ))
            < ∑ k ∈ Finset.range K, (∑ Q ∈ Qs, w Q : ℝ) / (K : ℝ) := by
              apply Finset.sum_lt_sum_of_nonempty
              · exact ⟨0, Finset.mem_range.mpr hKpos⟩
              · intro i hi
                have h_i : (∑ Q ∈ ranges i, w Q : ℝ) * (K : ℝ) < (∑ Q ∈ Qs, w Q : ℝ) := h i hi
                have h : (∑ Q ∈ ranges i, w Q : ℝ) < (∑ Q ∈ Qs, w Q : ℝ) / (K : ℝ) := by
                  calc
                    (∑ Q ∈ ranges i, w Q : ℝ)
                      = ((∑ Q ∈ ranges i, w Q : ℝ) * (K : ℝ)) / (K : ℝ) := by
                        field_simp [hKpos'.ne'] <;> ring
                    _ < (∑ Q ∈ Qs, w Q : ℝ) / (K : ℝ) := by gcongr
                exact h
          _ = (∑ Q ∈ Qs, w Q : ℝ) := by
              simp [Finset.sum_const, hKpos.ne'] <;> field_simp <;> ring
      have hsum' : (∑ k ∈ Finset.range K, (∑ Q ∈ ranges k, w Q : ℝ)) = (∑ Q ∈ Qs, w Q : ℝ) := by
        exact_mod_cast hsum
      rw [hsum'] at h'
      exact lt_irrefl _ h'
    rcases hpg with ⟨k, hk, hbound⟩
    let N : ℕ := 2 ^ k
    have hNpos : 0 < N := by positivity
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hM2' : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hKbound : (K : ℝ) ≤ 6 * Real.log M := by
      have h1 : (K : ℝ) = (Nat.log 2 M : ℝ) + 1 := by
        simp [K] <;> norm_cast
      rw [h1]
      have h2 : (2 : ℝ) ^ (Nat.log 2 M) ≤ (M : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 hMne
      have h3 : (Nat.log 2 M : ℝ) * Real.log 2 ≤ Real.log M := by
        calc
          (Nat.log 2 M : ℝ) * Real.log 2
            = Real.log ((2 : ℝ) ^ (Nat.log 2 M)) := by
              rw [← Real.log_pow] <;> norm_num
          _ ≤ Real.log M := Real.log_le_log (by positivity) (by exact_mod_cast h2)
      have h4 : (Nat.log 2 M : ℝ) ≤ Real.log M / Real.log 2 := by
        calc
          (Nat.log 2 M : ℝ)
            = ((Nat.log 2 M : ℝ) * Real.log 2) / Real.log 2 := by
              field_simp [hlog2pos.ne'] <;> ring
          _ ≤ Real.log M / Real.log 2 := by gcongr
      have h5 : (1 : ℝ) ≤ Real.log M / Real.log 2 := by
        have h6 : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hM2'
        have h7 : (0 : ℝ) < Real.log 2 := hlog2pos
        rw [one_le_div h7]
        exact h6
      have h8 : (Nat.log 2 M : ℝ) + 1 ≤ 2 * (Real.log M / Real.log 2) := by
        calc
          (Nat.log 2 M : ℝ) + 1
            ≤ Real.log M / Real.log 2 + 1 := by gcongr
          _ ≤ Real.log M / Real.log 2 + Real.log M / Real.log 2 := by gcongr
          _ = 2 * (Real.log M / Real.log 2) := by ring
      have h9 : 2 * (Real.log M / Real.log 2) ≤ 6 * Real.log M := by
        have h10 : (1 : ℝ) / Real.log 2 ≤ 3 := by
          have h11 : (1 / 2 : ℝ) ≤ Real.log 2 := half_le_log2
          have h12 : (0 : ℝ) < Real.log 2 := hlog2pos
          calc
            (1 : ℝ) / Real.log 2 ≤ 1 / (1 / 2 : ℝ) := by gcongr
            _ = 2 := by norm_num
            _ ≤ 3 := by norm_num
        calc
          2 * (Real.log M / Real.log 2)
            = 2 * (1 / Real.log 2) * Real.log M := by ring
          _ ≤ 2 * 3 * Real.log M := by gcongr
          _ = 6 * Real.log M := by ring
      linarith
    have hfinal : (∑ Q ∈ ranges k, w Q : ℝ) * (6 * Real.log M) ≥ (∑ Q ∈ Qs, w Q : ℝ) := by
      calc
        (∑ Q ∈ ranges k, w Q : ℝ) * (6 * Real.log M)
          ≥ (∑ Q ∈ ranges k, w Q : ℝ) * (K : ℝ) := by gcongr
        _ ≥ (∑ Q ∈ Qs, w Q : ℝ) := hbound
    have hrange_eq : ranges k = Qs.filter (fun Q => N ≤ c Q ∧ c Q < 2 * N) := by
      ext Q
      simp only [ranges, N, mem_filter]
      constructor
      · rintro ⟨hQ, h1, h2⟩
        have h3 : c Q < 2 * N := by
          have h4 : 2 * N = 2 ^ (k + 1) := by
            simp [N] <;> ring
          rw [h4] <;> exact h2
        exact ⟨hQ, h1, h3⟩
      · rintro ⟨hQ, h1, h2⟩
        have h3 : c Q < 2 ^ (k + 1) := by
          have h4 : 2 * N = 2 ^ (k + 1) := by simp [N] <;> ring
          rw [h4] at h2 <;> exact h2
        exact ⟨hQ, h1, h3⟩
    refine ⟨N, hNpos, ?_⟩
    have hgoal : (∑ Q ∈ (Qs.filter (fun Q => N ≤ c Q ∧ c Q < 2 * N)), w Q : ℝ) * (6 * Real.log M) ≥
        (∑ Q ∈ Qs, w Q : ℝ) := by
      rw [← hrange_eq]
      exact hfinal
    exact hgoal

-- ============================================================================
-- 4. AM-GM product bound
-- ============================================================================

/-- AM-GM inequality: for positive reals `a_i`, the product satisfies
    `∏ a_i ≤ (∑ a_i / n)^n`. -/
lemma amgm_product_upper_bound {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    ∏ i : Fin n, a i ≤ ((∑ i : Fin n, a i) / (n : ℝ)) ^ n := by
  by_cases hn : n = 0
  · subst hn; simp
  have hpos : 0 < n := by omega
  haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
  set μ : ℝ := (∑ i : Fin n, a i) / (n : ℝ) with hμ_def
  have hμ_pos : 0 < μ := by
    apply div_pos
    · apply Finset.sum_pos
      · intro i _; exact ha i
      · exact Finset.univ_nonempty
    · positivity
  have h1 : ∀ i : Fin n, Real.log (a i / μ) ≤ a i / μ - 1 := by
    intro i
    have hpos2 : 0 < a i / μ := div_pos (ha i) hμ_pos
    have h3 : Real.log (a i / μ) + 1 ≤ a i / μ := by
      have h4 := Real.add_one_le_exp (Real.log (a i / μ))
      rw [Real.exp_log hpos2] at h4
      exact h4
    linarith
  have hsum_log : ∑ i : Fin n, Real.log (a i / μ) ≤ 0 := by
    calc
      ∑ i : Fin n, Real.log (a i / μ)
        ≤ ∑ i : Fin n, (a i / μ - 1) := Finset.sum_le_sum (fun i _ => h1 i)
      _ = (∑ i : Fin n, (a i / μ)) - (n : ℝ) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const] <;> simp
      _ = (∑ i : Fin n, a i) / μ - (n : ℝ) := by
        have h4 : ∑ i : Fin n, (a i / μ) = (∑ i : Fin n, a i) / μ := by
          rw [Finset.sum_div]
        rw [h4]
      _ = 0 := by
        have hsum_ne : (∑ i : Fin n, a i) ≠ 0 := by
          have h : 0 < ∑ i : Fin n, a i := by
            apply Finset.sum_pos
            · intro i _; exact ha i
            · exact Finset.univ_nonempty
          exact h.ne'
        have h5 : (∑ i : Fin n, a i) / μ = (n : ℝ) := by
          rw [hμ_def]
          field_simp [hpos.ne', hsum_ne] <;> ring
        rw [h5] <;> ring
  have hprod_log : Real.log (∏ i : Fin n, (a i / μ)) = ∑ i : Fin n, Real.log (a i / μ) := by
    have h : ∀ (s : Finset (Fin n)), Real.log (∏ i ∈ s, (a i / μ)) = ∑ i ∈ s, Real.log (a i / μ) := by
      intro s
      induction s using Finset.induction with
      | empty => simp
      | @insert i s hi ih =>
        have hpos1 : 0 < a i / μ := div_pos (ha i) hμ_pos
        have hpos2 : 0 < ∏ x ∈ s, (a x / μ) := by
          apply Finset.prod_pos
          intro x _; exact div_pos (ha x) hμ_pos
        rw [Finset.prod_insert hi, Finset.sum_insert hi, Real.log_mul hpos1.ne' hpos2.ne']
        rw [ih]
    exact h Finset.univ
  have h5 : Real.log (∏ i : Fin n, (a i / μ)) ≤ 0 := by
    rw [hprod_log] <;> exact hsum_log
  have h6 : 0 < ∏ i : Fin n, (a i / μ) := by
    apply Finset.prod_pos
    intro i _; exact div_pos (ha i) hμ_pos
  have h7 : ∏ i : Fin n, (a i / μ) ≤ 1 := by
    have h8 : Real.log (∏ i : Fin n, (a i / μ)) ≤ Real.log 1 := by
      simpa using h5
    exact (Real.log_le_log_iff h6 (by norm_num)).mp h8
  have h9 : ∏ i : Fin n, (a i / μ) = (∏ i : Fin n, a i) / μ ^ n := by
    have h10 : ∏ i : Fin n, (a i / μ) = (∏ i : Fin n, a i) / μ ^ n := by
      rw [Finset.prod_div_distrib]
      have h11 : ∏ i : Fin n, μ = μ ^ n := by
        rw [Finset.prod_const, Finset.card_fin]
      rw [h11] <;> ring
    exact h10
  rw [h9] at h7
  have h11 : (∏ i : Fin n, a i) / μ ^ n ≤ 1 := h7
  have h12 : 0 < μ ^ n := by positivity
  have h13 : ∏ i : Fin n, a i ≤ μ ^ n := by
    calc
      ∏ i : Fin n, a i = ((∏ i : Fin n, a i) / μ ^ n) * μ ^ n := by
        field_simp [h12.ne'] <;> ring
      _ ≤ 1 * μ ^ n := by gcongr
      _ = μ ^ n := by ring
  simpa [hμ_def] using h13

/-- AM-GM inequality: for positive reals `a_i`, the product of reciprocals
    satisfies `∏ (1/a_i) ≥ (n / ∑ a_i)^n`. -/
lemma amgm_product_lower_bound {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    ∏ i : Fin n, (1 / a i) ≥ ((n : ℝ) / ∑ i : Fin n, a i) ^ n := by
  by_cases hn : n = 0
  · subst hn; simp
  have hpos : 0 < n := by omega
  haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
  have hsum_pos : (0 : ℝ) < ∑ i : Fin n, a i := by
    apply Finset.sum_pos
    · intro i _; exact ha i
    · exact Finset.univ_nonempty
  have hprod_pos : (0 : ℝ) < ∏ i : Fin n, a i := by
    apply Finset.prod_pos
    intro i _; exact ha i
  have h_amgm : ∏ i : Fin n, a i ≤ ((∑ i : Fin n, a i) / (n : ℝ)) ^ n :=
    amgm_product_upper_bound a ha
  have h9 : ∏ i : Fin n, (1 / a i) = (∏ i : Fin n, a i)⁻¹ := by
    have h10 : ∏ i : Fin n, (1 / a i) = ∏ i : Fin n, (a i)⁻¹ := by
      apply Finset.prod_congr rfl
      intro i _; field_simp
    rw [h10, Finset.prod_inv_distrib] <;> field_simp
  rw [h9]
  have h10 : ((∑ i : Fin n, a i) / (n : ℝ)) ^ n > 0 := by positivity
  have h11 : (∏ i : Fin n, a i)⁻¹ ≥ (((∑ i : Fin n, a i) / (n : ℝ)) ^ n)⁻¹ := by
    gcongr
    <;> exact h_amgm
  have h12 : (((∑ i : Fin n, a i) / (n : ℝ)) ^ n)⁻¹ = ((n : ℝ) / ∑ i : Fin n, a i) ^ n := by
    have h13 : ((∑ i : Fin n, a i) / (n : ℝ)) ^ n ≠ 0 := h10.ne'
    have h14 : (((∑ i : Fin n, a i) / (n : ℝ)) ^ n)⁻¹ =
               (((n : ℝ) / ∑ i : Fin n, a i) ^ n) := by
      have h15 : ((∑ i : Fin n, a i) / (n : ℝ))⁻¹ = (n : ℝ) / ∑ i : Fin n, a i := by
        field_simp [hsum_pos.ne', hpos.ne'] <;> ring
      rw [← inv_pow]
      <;> rw [h15]
    exact h14
  rw [h12] at h11
  exact h11

-- ============================================================================
-- 5. Multi-step uniformization product bound
-- ============================================================================

/-- If at each of `n` levels we lose a factor of `1/(6 * Real.log (M i))`,
    the total retention factor is at least `(n / (6 * L))^n` where
    `L ≥ ∑ Real.log (M i)`, by AM-GM. -/
lemma uniformization_product_bound {n : ℕ} (M : Fin n → ℕ) (hM : ∀ i, 1 < M i)
    (L : ℝ) (hL : ∑ i : Fin n, Real.log (M i) ≤ L) :
    ∏ i : Fin n, (1 / (6 * Real.log (M i))) ≥ ((n : ℝ) / (6 * L)) ^ n := by
  by_cases hn : n = 0
  · subst hn
    simp
  have hpos : 0 < n := by omega
  haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
  have hLpos : (0 : ℝ) < L := by
    have h1 : ∀ i : Fin n, 0 < Real.log (M i) := by
      intro i
      have h2 : (1 : ℝ) < (M i : ℝ) := by exact_mod_cast hM i
      exact Real.log_pos h2
    have h3 : (0 : ℝ) < ∑ i : Fin n, Real.log (M i) := by
      apply Finset.sum_pos
      · intro i _; exact h1 i
      · exact Finset.univ_nonempty
    exact h3.trans_le hL
  let a : Fin n → ℝ := fun i => 6 * Real.log (M i)
  have ha : ∀ i, 0 < a i := by
    intro i
    have h2 : (1 : ℝ) < (M i : ℝ) := by exact_mod_cast hM i
    have h3 : 0 < Real.log (M i) := Real.log_pos h2
    positivity
  have hsum : ∑ i : Fin n, a i = 6 * ∑ i : Fin n, Real.log (M i) := by
    simp [a, Finset.mul_sum] <;> ring
  have h4 : ∑ i : Fin n, a i ≤ 6 * L := by
    rw [hsum] <;> linarith
  have h5 : ∏ i : Fin n, (1 / a i) ≥ ((n : ℝ) / ∑ i : Fin n, a i) ^ n :=
    amgm_product_lower_bound a ha
  have h6 : ((n : ℝ) / ∑ i : Fin n, a i) ^ n ≥ ((n : ℝ) / (6 * L)) ^ n := by
    have h7 : 0 < ∑ i : Fin n, a i := by
      apply Finset.sum_pos
      · intro i _; exact ha i
      · exact Finset.univ_nonempty
    gcongr
    <;> linarith
  have h8 : ∏ i : Fin n, (1 / a i) = ∏ i : Fin n, (1 / (6 * Real.log (M i))) := by
    apply Finset.prod_congr rfl
    intro i _; simp [a]
  rw [h8]
  exact le_trans h6 h5

-- ============================================================================
-- 6. One-step uniformization (clean statement)
-- ============================================================================

/-- One-step uniformization: given items partitioned into cells with counts
    `c Q` bounded by `M`, find `N` and select cells whose counts lie in
    `[N, 2*N)`. The total weight of selected cells is at least
    `total / (6 * Real.log M)`. -/
lemma uniformize_one_step {α : Type*} [DecidableEq α]
    (cells : Finset α) (c w : α → ℕ)
    (M : ℕ) (hM : 1 < M)
    (hc1 : ∀ Q ∈ cells, 1 ≤ c Q)
    (hc2 : ∀ Q ∈ cells, c Q ≤ M) :
    ∃ (N : ℕ), 0 < N ∧
      let selected := cells.filter (fun Q => N ≤ c Q ∧ c Q < 2 * N)
      (∑ Q ∈ selected, w Q : ℝ) * (6 * Real.log M) ≥ (∑ Q ∈ cells, w Q : ℝ) :=
  pigeonhole_dyadic_range cells c w M hM hc1 hc2

-- ============================================================================
-- 7. Subset preservation for δ-s-set condition (OS Lemma 7.2)
-- ============================================================================

/-- If a set `P` satisfies the `(δ,s,C)`-set growth condition and `P' ⊆ P`
    has `δ`-covering number at least `c * |P|_δ` for some `c > 0`, then `P'`
    satisfies the `(δ,s,C/c)`-set growth condition.
    This is the "uniformization under subsetting" lemma (OS Lemma 7.2).

    Stated directly in terms of covering numbers to avoid circular imports. -/
lemma subset_growth_condition {X : Type*} [PseudoMetricSpace X]
    {δ s C c : ℝ} {P P' : Set X}
    (hδpos : 0 < δ) (hCpos : 0 < C) (hs : 0 ≤ s) (hcpos : 0 < c)
    (hgrowth : ∀ (x : X) (r : ℝ), δ ≤ r →
      Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          Metric.externalCoveringNumber δ.toNNReal P)
    (hsub : P' ⊆ P)
    (hcov : ENNReal.ofReal c * Metric.externalCoveringNumber δ.toNNReal P
              ≤ Metric.externalCoveringNumber δ.toNNReal P') :
    ∀ (x : X) (r : ℝ), δ ≤ r →
      Metric.externalCoveringNumber δ.toNNReal (P' ∩ Metric.closedBall x r) ≤
        ENNReal.ofReal (C / c) * (ENNReal.ofReal r) ^ s *
          Metric.externalCoveringNumber δ.toNNReal P' := by
  let cover : Set X → ENNReal := fun A => (Metric.externalCoveringNumber δ.toNNReal A : ENNReal)
  intro x r hr
  have h1 : P' ∩ Metric.closedBall x r ⊆ P ∩ Metric.closedBall x r := by
    gcongr <;> tauto
  have h2_raw : Metric.externalCoveringNumber δ.toNNReal (P' ∩ Metric.closedBall x r) ≤
                  Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) :=
    Metric.externalCoveringNumber_mono_set h1
  have h2 : cover (P' ∩ Metric.closedBall x r) ≤ cover (P ∩ Metric.closedBall x r) := by
    have h_coe : ∀ (a b : ℕ∞), a ≤ b → ((a : ENNReal) ≤ (b : ENNReal)) := by
      intro a b h
      exact ENat.toENNReal_le.mpr h
    exact h_coe _ _ h2_raw
  have h3 : cover (P ∩ Metric.closedBall x r) ≤
              ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * cover P := hgrowth x r hr
  have h4 : cover (P' ∩ Metric.closedBall x r) ≤
              ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * cover P :=
    h2.trans h3
  have hc_pos' : (0 : ENNReal) < ENNReal.ofReal c := ENNReal.ofReal_pos.mpr hcpos
  have hc_ne_top : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc_ne_zero : ENNReal.ofReal c ≠ 0 := hc_pos'.ne'
  have h_cancel : (ENNReal.ofReal c)⁻¹ * ENNReal.ofReal c = 1 := by
    rw [ENNReal.inv_mul_cancel hc_ne_zero hc_ne_top]
  have h5 : cover P ≤ (ENNReal.ofReal c)⁻¹ * cover P' := by
    have h6 : (ENNReal.ofReal c) * cover P ≤ cover P' := hcov
    calc
      cover P
        = 1 * cover P := by simp
      _ = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c) * cover P := by rw [h_cancel] <;> ring
      _ = (ENNReal.ofReal c)⁻¹ * ((ENNReal.ofReal c) * cover P) := by ring
      _ ≤ (ENNReal.ofReal c)⁻¹ * cover P' := by gcongr
  have h10 : ENNReal.ofReal (C / c) * ENNReal.ofReal c = ENNReal.ofReal C := by
    have hC0 : 0 ≤ C := by linarith
    have hc0 : 0 ≤ c := by linarith
    have h_mul : ENNReal.ofReal ((C / c) * c) = ENNReal.ofReal (C / c) * ENNReal.ofReal c := by
      exact ENNReal.ofReal_mul' hc0
    have h_eq : (C / c) * c = C := by
      field_simp [hcpos.ne'] <;> ring
    rw [← h_mul, h_eq]
  have h_cancel2 : ENNReal.ofReal c * (ENNReal.ofReal c)⁻¹ = 1 := by
    rw [mul_comm, ENNReal.inv_mul_cancel hc_ne_zero hc_ne_top]
  have hdiv : ENNReal.ofReal C * (ENNReal.ofReal c)⁻¹ = ENNReal.ofReal (C / c) := by
    calc
      ENNReal.ofReal C * (ENNReal.ofReal c)⁻¹
        = (ENNReal.ofReal (C / c) * ENNReal.ofReal c) * (ENNReal.ofReal c)⁻¹ := by rw [h10]
      _ = ENNReal.ofReal (C / c) * (ENNReal.ofReal c * (ENNReal.ofReal c)⁻¹) := by ring
      _ = ENNReal.ofReal (C / c) * 1 := by rw [h_cancel2]
      _ = ENNReal.ofReal (C / c) := by ring
  calc
    cover (P' ∩ Metric.closedBall x r)
      ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * cover P := h4
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * ((ENNReal.ofReal c)⁻¹ * cover P') := by gcongr
    _ = (ENNReal.ofReal C * (ENNReal.ofReal c)⁻¹) * (ENNReal.ofReal r) ^ s * cover P' := by ring
    _ = ENNReal.ofReal (C / c) * (ENNReal.ofReal r) ^ s * cover P' := by rw [hdiv] <;> ring

-- ============================================================================
-- 8. Uniform cardinality refinement (Lemma A, combinatorial core)
-- ============================================================================

/-- Uniform cardinality refinement: given a finite index set `P` and a
    family of finite sets `Tp p`, with cardinalities bounded between 1 and
    `M_max`, extract a subfamily `P' ⊆ P` and a scale `M` such that
    `M ≤ |Tp p| < 2*M` for all `p ∈ P'`, and `P'` retains at least a
    `1 / (6 * Real.log M_max)` fraction of `P`.

    This is the combinatorial engine behind OS Appendix A, Step 1
    (lines 1415-1416) and OS Section 5, Proposition 5.1.

    Direct corollary of `pigeonhole_dyadic_range` with unit weights. -/
lemma uniform_cardinality_refinement {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : Finset α) (Tp : α → Finset β)
    (M_max : ℕ) (hMmax : 1 < M_max)
    (h1 : ∀ p ∈ P, 1 ≤ (Tp p).card)
    (h2 : ∀ p ∈ P, (Tp p).card ≤ M_max) :
    ∃ (P' : Finset α) (M : ℕ),
      0 < M ∧
      P' ⊆ P ∧
      (∀ p ∈ P', M ≤ (Tp p).card ∧ (Tp p).card < 2 * M) ∧
      (P'.card : ℝ) * (6 * Real.log M_max) ≥ (P.card : ℝ) := by
  let c : α → ℕ := fun p => (Tp p).card
  let w : α → ℕ := fun _ => 1
  have hpg := pigeonhole_dyadic_range P c w M_max hMmax h1 h2
  rcases hpg with ⟨M, hMpos, hbound⟩
  let P' := P.filter (fun p => M ≤ c p ∧ c p < 2 * M)
  have hP'_sub : P' ⊆ P := filter_subset _ _
  have h_uniform : ∀ p ∈ P', M ≤ c p ∧ c p < 2 * M := by
    intro p hp
    exact (mem_filter.mp hp).2
  have h_card : (∑ p ∈ P', w p : ℝ) = (P'.card : ℝ) := by
    simp [w, sum_const] <;> ring
  have h_total : (∑ p ∈ P, w p : ℝ) = (P.card : ℝ) := by
    simp [w, sum_const] <;> ring
  have hfinal : (P'.card : ℝ) * (6 * Real.log M_max) ≥ (P.card : ℝ) := by
    have h : (∑ p ∈ P', w p : ℝ) * (6 * Real.log M_max) ≥ (∑ p ∈ P, w p : ℝ) := by
      simpa [P'] using hbound
    rw [h_card, h_total] at h
    exact h
  exact ⟨P', M, hMpos, hP'_sub, h_uniform, hfinal⟩

/-- Version with explicit loss factor `K = 6 * Real.log M_max`, satisfying `K ≥ 1`. -/
lemma uniform_cardinality_refinement' {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : Finset α) (Tp : α → Finset β)
    (M_max : ℕ) (hMmax : 1 < M_max)
    (h1 : ∀ p ∈ P, 1 ≤ (Tp p).card)
    (h2 : ∀ p ∈ P, (Tp p).card ≤ M_max) :
    ∃ (P' : Finset α) (M : ℕ) (K : ℝ),
      0 < M ∧
      1 ≤ K ∧
      P' ⊆ P ∧
      (∀ p ∈ P', M ≤ (Tp p).card ∧ (Tp p).card < 2 * M) ∧
      (P'.card : ℝ) * K ≥ (P.card : ℝ) := by
  rcases uniform_cardinality_refinement P Tp M_max hMmax h1 h2 with ⟨P', M, hM, hsub, hunif, hbound⟩
  let K : ℝ := 6 * Real.log M_max
  have hK1 : 1 ≤ K := by
    have h1 : (1 : ℝ) < (M_max : ℝ) := by exact_mod_cast hMmax
    have h2 : 0 < Real.log M_max := Real.log_pos h1
    have h3 : Real.log M_max ≥ Real.log 2 := Real.log_le_log (by norm_num) (by exact_mod_cast hMmax)
    have h4 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h5 : (-1 / 2 : ℝ) + 1 ≤ Real.exp (-1 / 2 : ℝ) := Real.add_one_le_exp (-1 / 2 : ℝ)
      have h51 : (-1 / 2 : ℝ) + 1 = (1 / 2 : ℝ) := by ring
      have h6 : (1 / 2 : ℝ) ≤ Real.exp (-1 / 2 : ℝ) := by rw [← h51]; exact h5
      have h7 : Real.exp (-1 / 2 : ℝ) = (Real.exp (1 / 2 : ℝ))⁻¹ := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.exp_neg]
      have h8 : (1 / 2 : ℝ) ≤ (Real.exp (1 / 2 : ℝ))⁻¹ := by rw [← h7]; exact h6
      have h9 : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
      have h10 : Real.exp (1 / 2 : ℝ) ≤ 2 := by
        have h11 : (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) ≤ 1 := by
          calc (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ)
            ≤ (Real.exp (1 / 2 : ℝ))⁻¹ * Real.exp (1 / 2 : ℝ) := by gcongr
          _ = 1 := by field_simp [h9.ne'] <;> ring
        linarith
      have h12 : (1 / 2 : ℝ) = Real.log (Real.exp (1 / 2 : ℝ)) := by rw [Real.log_exp] <;> ring
      rw [h12]
      exact Real.log_le_log (by positivity) h10
    linarith
  exact ⟨P', M, K, hM, hK1, hsub, hunif, hbound⟩

end DiscretisedFurstenbergEstimate.Uniformization
