import MyLeanRepo.Kakeya.AssertionD
import MyLeanRepo.Kakeya.Hairbrush.Pigeonhole
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card

/-!
# Radius pigeonholing lemma

Given a finite family indexed by `α` and a function `f : α → ℝ` with values in
`[δ, 2]`, pigeonhole a geometric bin `[radius, (3/2) * radius)` containing at
least a `δ^familyLoss` fraction of the indices.

The number of geometric bins is `O(log(1/δ))`, which is absorbed by any positive
power `δ^(-familyLoss)` for sufficiently small `δ`.
-/

noncomputable section

open Finset Real

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- For any `familyLoss > 0`, there exists `delta₀ > 0` with `delta₀ ≤ 1/1000`
such that for all `0 < δ ≤ delta₀`, the number of geometric radius bins
`log(2/δ)/log(3/2) + 2` is bounded by `δ^(-familyLoss)`. -/
lemma radius_log_bound (familyLoss : ℝ) (hfl_pos : 0 < familyLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 / 1000 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
        Real.log (2 / δ) / Real.log (3 / 2) + 2 ≤ Real.rpow δ (-familyLoss) := by
  set ε : ℝ := familyLoss / 2 with hε_def
  have hε_pos : 0 < ε := by linarith
  have hlog32_pos : 0 < Real.log (3 / 2) := by
    apply Real.log_pos
    norm_num
  have hlog2_nonneg : 0 ≤ Real.log 2 := by
    apply Real.log_nonneg
    norm_num
  set C1 : ℝ := (ε * Real.log (3 / 2) / 2) ^ (1 / ε) with hC1_def
  set C2 : ℝ := (1 / (2 * (Real.log 2 / Real.log (3 / 2) + 2))) ^ (1 / (2 * ε)) with hC2_def
  have hC1_pos : 0 < C1 := by
    apply Real.rpow_pos_of_pos
    positivity
  have hC2_pos : 0 < C2 := by
    apply Real.rpow_pos_of_pos
    positivity
  set delta₀ : ℝ := min (1 / 1000) (min C1 C2) with hdelta₀_def
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_le : delta₀ ≤ 1 / 1000 := by
    exact min_le_left _ _
  have hdelta₀_le_C1 : delta₀ ≤ C1 := by
    have h : delta₀ ≤ min C1 C2 := min_le_right _ _
    exact le_trans h (min_le_left _ _)
  have hdelta₀_le_C2 : delta₀ ≤ C2 := by
    have h : delta₀ ≤ min C1 C2 := min_le_right _ _
    exact le_trans h (min_le_right _ _)
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_le, ?_⟩
  intro δ hδ_pos hδ_le
  have hδ_le_C1 : δ ≤ C1 := le_trans hδ_le hdelta₀_le_C1
  have hδ_le_C2 : δ ≤ C2 := le_trans hδ_le hdelta₀_le_C2
  set x : ℝ := 1 / δ with hx_def
  have hx_pos : 0 < x := by positivity
  have h1 : Real.log (2 / δ) = Real.log 2 + Real.log x := by
    have h2 : (2 / δ) = 2 * x := by
      simp only [hx_def]
      <;> field_simp [hδ_pos.ne'] <;> ring
    rw [h2, Real.log_mul (by norm_num) hx_pos.ne'] <;> ring
  have h2 : Real.log x ≤ x ^ ε / ε := Real.log_le_rpow_div (by positivity) hε_pos
  have h3 : Real.log (2 / δ) ≤ Real.log 2 + x ^ ε / ε := by
    rw [h1] <;> linarith
  have h4 : x ^ ε ≥ 2 / (ε * Real.log (3 / 2)) := by
    have h5 : x ≥ 1 / C1 := by
      calc x = 1 / δ := by rfl
           _ ≥ 1 / C1 := by gcongr
    have h6 : (1 / C1) ^ ε = 2 / (ε * Real.log (3 / 2)) := by
      set y : ℝ := ε * Real.log (3 / 2) / 2 with hy_def
      have hy_pos : 0 < y := by positivity
      have hC1_eq : C1 = y ^ (1 / ε) := by
        simpa [hC1_def, hy_def] using rfl
      have hC1ε : C1 ^ ε = y := by
        rw [hC1_eq]
        have h : (y ^ (1 / ε)) ^ ε = y := by
          rw [← Real.rpow_mul hy_pos.le]
          have h2 : (1 / ε) * ε = 1 := by field_simp [hε_pos.ne'] <;> ring
          rw [h2] <;> simp
        exact h
      have h_inv_rpow : (1 / C1) ^ ε = 1 / (C1 ^ ε) := by
        rw [Real.div_rpow (by norm_num) hC1_pos.le]
        <;> simp
      rw [h_inv_rpow, hC1ε]
      field_simp [hy_def] <;> ring
    have h9 : x ^ ε ≥ (1 / C1) ^ ε := by gcongr <;> linarith
    rw [h6] at h9
    exact h9
  have h5 : x ^ (2 * ε) ≥ 2 * (Real.log 2 / Real.log (3 / 2) + 2) := by
    have h6 : x ≥ 1 / C2 := by
      calc x = 1 / δ := by rfl
           _ ≥ 1 / C2 := by gcongr
    have h7 : (1 / C2) ^ (2 * ε) = 2 * (Real.log 2 / Real.log (3 / 2) + 2) := by
      set z : ℝ := 1 / (2 * (Real.log 2 / Real.log (3 / 2) + 2)) with hz_def
      have hz_pos : 0 < z := by positivity
      have hC2_eq : C2 = z ^ (1 / (2 * ε)) := by
        simpa [hC2_def, hz_def] using rfl
      have hC2ε : C2 ^ (2 * ε) = z := by
        rw [hC2_eq]
        have h : (z ^ (1 / (2 * ε))) ^ (2 * ε) = z := by
          rw [← Real.rpow_mul hz_pos.le]
          have h2 : (1 / (2 * ε)) * (2 * ε) = 1 := by field_simp [hε_pos.ne'] <;> ring
          rw [h2] <;> simp
        exact h
      have h_inv_rpow : (1 / C2) ^ (2 * ε) = 1 / (C2 ^ (2 * ε)) := by
        rw [Real.div_rpow (by norm_num) hC2_pos.le] <;> simp
      rw [h_inv_rpow, hC2ε]
      have h_final : 1 / z = 2 * (Real.log 2 / Real.log (3 / 2) + 2) := by
        rw [hz_def]
        field_simp
        <;> ring
      exact h_final
    have h10 : x ^ (2 * ε) ≥ (1 / C2) ^ (2 * ε) := by gcongr <;> linarith
    rw [h7] at h10
    exact h10
  have h_family : Real.rpow δ (-familyLoss) = x ^ familyLoss := by
    have h10 : Real.rpow δ (-familyLoss) = 1 / Real.rpow δ familyLoss := by
      have h : Real.rpow δ (-familyLoss) = (Real.rpow δ familyLoss)⁻¹ := Real.rpow_neg hδ_pos.le familyLoss
      rw [h]
      <;> field_simp
    have h11 : x ^ familyLoss = 1 / Real.rpow δ familyLoss := by
      have h12 : x = 1 / δ := by rfl
      rw [h12]
      have h13 : (1 / δ) ^ familyLoss = 1 / Real.rpow δ familyLoss := by
        rw [Real.div_rpow (by norm_num) hδ_pos.le] <;> simp
      exact h13
    rw [h10, h11]
  rw [h_family]
  calc
    Real.log (2 / δ) / Real.log (3 / 2) + 2
      ≤ (Real.log 2 + x ^ ε / ε) / Real.log (3 / 2) + 2 := by gcongr
    _ = (Real.log 2 / Real.log (3 / 2) + 2) + (x ^ ε / ε) / Real.log (3 / 2) := by ring
    _ ≤ x ^ (2 * ε) / 2 + x ^ (2 * ε) / 2 := by
      have h12 : (Real.log 2 / Real.log (3 / 2) + 2) ≤ x ^ (2 * ε) / 2 := by linarith
      have h13 : (x ^ ε / ε) / Real.log (3 / 2) ≤ x ^ (2 * ε) / 2 := by
        have h14 : (x ^ ε / ε) / Real.log (3 / 2) = x ^ ε / (ε * Real.log (3 / 2)) := by ring
        rw [h14]
        have h15 : 0 < x ^ ε := by positivity
        have h16 : x ^ ε * x ^ ε ≥ x ^ ε * (2 / (ε * Real.log (3 / 2))) := by
          gcongr
          <;> exact h4
        have h17 : x ^ ε * (2 / (ε * Real.log (3 / 2))) = 2 * (x ^ ε / (ε * Real.log (3 / 2))) := by ring
        have h18 : x ^ ε * x ^ ε ≥ 2 * (x ^ ε / (ε * Real.log (3 / 2))) := by
          rw [h17] at h16
          exact h16
        have h19 : x ^ ε * x ^ ε = x ^ (2 * ε) := by
          rw [← Real.rpow_add (by positivity)] <;> ring
        rw [h19] at h18
        linarith
      linarith
    _ = x ^ (2 * ε) := by ring
    _ = x ^ familyLoss := by
      have h14 : familyLoss = 2 * ε := by linarith
      rw [h14]

/-- Geometric radius pigeonhole: given `f : α → ℝ` with `δ ≤ f i ≤ 2`, find a
common `radius ∈ [δ, 2]` and a subfamily `sub` of cardinality at least
`δ^familyLoss * card(univ)` such that every `i ∈ sub` satisfies
`radius ≤ f i < (3/2) * radius`.

The hypothesis `h_log_bound` ensures the number of bins is at most
`δ^(-familyLoss)`. Obtain it from `radius_log_bound`. -/
lemma radius_pigeonhole {δ : ℝ} (hδ : 0 < δ) (hδ_small : δ ≤ 1 / 1000)
    {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ)
    (hf_range : ∀ i, δ ≤ f i ∧ f i ≤ 2)
    (familyLoss : ℝ) (hfl_pos : 0 < familyLoss)
    (h_log_bound : Real.log (2 / δ) / Real.log (3 / 2) + 2 ≤ Real.rpow δ (-familyLoss)) :
    ∃ (radius : ℝ) (sub : Finset α),
      δ ≤ radius ∧ radius ≤ 2 ∧
      (Finset.card sub : ENNReal) ≥
        ENNReal.ofReal (Real.rpow δ familyLoss) * (Finset.card (Finset.univ : Finset α) : ENNReal) ∧
      ∀ i ∈ sub, radius ≤ f i ∧ f i < (3 / 2 : ℝ) * radius := by
  -- Empty universe case: return empty subfamily
  by_cases h_univ : (Finset.univ : Finset α).Nonempty
  · -- Nonempty universe case
    let c : ℝ := 3 / 2
    have hc_gt_one : 1 < c := by norm_num
    have hc_pos : 0 < c := by norm_num
    have hlog32_pos : 0 < Real.log c := by
      simpa [c] using Real.log_pos (by norm_num)
    set K : ℕ := Nat.ceil (Real.log (2 / δ) / Real.log c) with hK_def
    have hK_nonneg : 0 ≤ Real.log (2 / δ) / Real.log c := by
      have h1 : 1 ≤ 2 / δ := by rw [one_le_div hδ] <;> linarith
      have h2 : 0 ≤ Real.log (2 / δ) := Real.log_nonneg h1
      positivity
    have hK_ge : (K : ℝ) ≥ Real.log (2 / δ) / Real.log c := Nat.le_ceil _
    have hK_lt : (K : ℝ) < Real.log (2 / δ) / Real.log c + 1 := Nat.ceil_lt_add_one hK_nonneg
    have h_pow_ge : δ * c ^ K ≥ 2 := by
      have h1 : Real.log (2 / δ) ≤ (K : ℝ) * Real.log c := by
        calc Real.log (2 / δ)
          = (Real.log (2 / δ) / Real.log c) * Real.log c := by field_simp [hlog32_pos.ne'] <;> ring
        _ ≤ (K : ℝ) * Real.log c := by gcongr
      have h2 : 0 < 2 / δ := by positivity
      have h3 : Real.log (2 / δ) ≤ Real.log (c ^ K) := by
        have h4 : Real.log (c ^ K) = (K : ℝ) * Real.log c := by simp [Real.log_pow] <;> ring
        rw [h4]; exact h1
      have h5 : 2 / δ ≤ c ^ K := (Real.log_le_log_iff h2 (by positivity)).mp h3
      have h6 : δ * (2 / δ) ≤ δ * c ^ K := by gcongr
      have h7 : δ * (2 / δ) = 2 := by field_simp [hδ.ne'] <;> ring
      rw [h7] at h6; exact h6
    have h_pow_lt : δ * c ^ K < 2 * c := by
      have h1 : (K : ℝ) * Real.log c < Real.log (2 / δ) + Real.log c := by
        calc (K : ℝ) * Real.log c
          < (Real.log (2 / δ) / Real.log c + 1) * Real.log c := by gcongr
        _ = Real.log (2 / δ) + Real.log c := by field_simp [hlog32_pos.ne'] <;> ring
      have h3 : Real.log (c ^ K) < Real.log ((2 / δ) * c) := by
        have h4 : Real.log (c ^ K) = (K : ℝ) * Real.log c := by simp [Real.log_pow] <;> ring
        have h5 : Real.log ((2 / δ) * c) = Real.log (2 / δ) + Real.log c := by
          rw [Real.log_mul (by positivity) (by positivity)] <;> ring
        rw [h4, h5] <;> exact h1
      have h6 : 0 < c ^ K := by positivity
      have h7 : 0 < (2 / δ) * c := by positivity
      have h8 : c ^ K < (2 / δ) * c := (Real.log_lt_log_iff h6 h7).mp h3
      have h9 : δ * c ^ K < δ * ((2 / δ) * c) := by gcongr
      have h10 : δ * ((2 / δ) * c) = 2 * c := by field_simp [hδ.ne'] <;> ring
      rw [h10] at h9; exact h9
    let bin : ℕ → Finset α := fun k =>
      Finset.univ.filter (fun i => δ * c ^ k ≤ f i ∧ f i < δ * c ^ (k + 1))
    have h_cover : (Finset.univ : Finset α) ⊆ Finset.biUnion (Finset.range (K + 1)) bin := by
      intro i _
      have hfi1 : δ ≤ f i := (hf_range i).1
      have hfi2 : f i ≤ 2 := (hf_range i).2
      let S : Finset ℕ := Finset.filter (fun k => δ * c ^ k ≤ f i) (Finset.range (K + 1))
      have h0_in_S : 0 ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_range] <;> norm_num <;> linarith
      have hS_nonempty : S.Nonempty := ⟨0, h0_in_S⟩
      let k := S.max' hS_nonempty
      have hk_in_S : k ∈ S := Finset.max'_mem S hS_nonempty
      have hk_lt : k < K + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hk_in_S).1
      have h_pow1 : δ * c ^ k ≤ f i := (Finset.mem_filter.mp hk_in_S).2
      have h_pow2 : f i < δ * c ^ (k + 1) := by
        by_cases h_kK : k = K
        · rw [h_kK]; have h2 : δ * c ^ (K + 1) = δ * c ^ K * c := by ring
          rw [h2]; have h3 : δ * c ^ K ≥ 2 := h_pow_ge; nlinarith
        · have h_k_lt_K : k < K := by omega
          by_contra h; have h' : δ * c ^ (k + 1) ≤ f i := by linarith
          have h_k1_in_range : k + 1 ∈ Finset.range (K + 1) := by simp only [Finset.mem_range] <;> omega
          have h_k1_in_S : k + 1 ∈ S := by
            simp only [S, Finset.mem_filter] <;> exact ⟨h_k1_in_range, h'⟩
          have h_le : k + 1 ≤ k := Finset.le_max' S (k + 1) h_k1_in_S; omega
      have hk_in : k ∈ Finset.range (K + 1) := by simp only [Finset.mem_range] <;> omega
      have hi_in_bin : i ∈ bin k := by
        simp only [bin, Finset.mem_filter] <;> exact ⟨Finset.mem_univ i, h_pow1, h_pow2⟩
      exact Finset.mem_biUnion.mpr ⟨k, hk_in, hi_in_bin⟩
    have h3 : (Finset.univ : Finset α).card ≤ ∑ k ∈ Finset.range (K + 1), (bin k).card := by
      calc (Finset.univ : Finset α).card
        ≤ (Finset.biUnion (Finset.range (K + 1)) bin).card := Finset.card_le_card h_cover
      _ ≤ ∑ k ∈ Finset.range (K + 1), (bin k).card := Finset.card_biUnion_le
    have h_sum_enn : ((Finset.univ : Finset α).card : ENNReal) ≤
        ∑ k ∈ Finset.range (K + 1), ((bin k).card : ENNReal) := by exact_mod_cast h3
    have h_range_nonempty : (Finset.range (K + 1)).Nonempty := by simp
    rcases Kakeya.Hairbrush.ennreal_sum_pigeonhole
        (ENNReal.natCast_ne_top _) h_sum_enn h_range_nonempty with
      ⟨k, hk_in, hk_ge⟩
    set sub : Finset α := bin k with hsub_def
    have hk_le : k ≤ K := by simp only [Finset.mem_range] at hk_in <;> omega
    set radius : ℝ := δ * c ^ k with hradius_def
    have h_univ_card_pos : 0 < (Finset.univ : Finset α).card := h_univ.card_pos
    have h_card_pos : 0 < (sub.card : ENNReal) := by
      by_contra h; have h' : (sub.card : ENNReal) = 0 := by simpa using h
      rw [h'] at hk_ge
      have h4 : ((Finset.univ : Finset α).card : ENNReal) ≤ 0 := by simpa using hk_ge
      have h5 : ((Finset.univ : Finset α).card : ENNReal) = 0 := by simpa using h4
      have h6 : (Finset.univ : Finset α).card = 0 := by exact_mod_cast h5
      omega
    have h_radius_nonempty : sub.Nonempty := Finset.card_pos.mp (by exact_mod_cast h_card_pos)
    have h_delta_le_radius : δ ≤ radius := by
      rw [hradius_def]
      have h1 : (1 : ℝ) ≤ c ^ k := by
        have h2 : 1 ≤ c := by norm_num
        have h3 : (1 : ℝ) ^ k ≤ c ^ k := by gcongr
        simpa using h3
      have h4 : δ * 1 ≤ δ * c ^ k := by gcongr
      simpa using h4
    have h_radius_le_two : radius ≤ 2 := by
      rw [hradius_def]
      by_cases h : k < K
      · have h_k_le_K1 : k ≤ K - 1 := by omega
        have h4 : c ^ k ≤ c ^ (K - 1) := by gcongr <;> norm_num
        have h5 : δ * c ^ k ≤ δ * c ^ (K - 1) := by gcongr
        have h6 : δ * c ^ (K - 1) < 2 := by
          have hK_pos : 0 < K := by
            by_contra h7; have h8 : K = 0 := by omega
            rw [h8] at hK_ge
            have h9 : Real.log (2 / δ) / Real.log c ≤ 0 := by linarith
            have h10 : 0 ≤ Real.log (2 / δ) / Real.log c := hK_nonneg
            have h11 : Real.log (2 / δ) / Real.log c = 0 := by linarith
            have h12 : Real.log (2 / δ) = 0 := by field_simp [hlog32_pos.ne'] at h11 <;> linarith
            have h13 : 2 / δ = 1 := by rw [Real.log_eq_zero] at h12 <;> linarith
            have h14 : δ = 2 := by field_simp [hδ.ne'] at h13 <;> linarith
            linarith
          have h7 : ((K - 1 : ℕ) : ℝ) < Real.log (2 / δ) / Real.log c :=
            Kakeya.Hairbrush.ceil_sub_one_lt (Real.log (2 / δ) / Real.log c) K hK_def hK_pos hK_nonneg
          have h8 : c ^ (K - 1) < 2 / δ := by
            have h9 : Real.log (c ^ (K - 1)) = ((K - 1 : ℕ) : ℝ) * Real.log c := by simp [Real.log_pow] <;> ring
            have h10 : Real.log (c ^ (K - 1)) < Real.log (2 / δ) := by
              rw [h9]
              have h11 : ((K - 1 : ℕ) : ℝ) * Real.log c < (Real.log (2 / δ) / Real.log c) * Real.log c := by gcongr
              have h12 : (Real.log (2 / δ) / Real.log c) * Real.log c = Real.log (2 / δ) := by
                field_simp [hlog32_pos.ne'] <;> ring
              rw [h12] at h11; exact h11
            have h13 : 0 < c ^ (K - 1) := by positivity
            have h14 : 0 < 2 / δ := by positivity
            exact (Real.log_lt_log_iff h13 h14).mp h10
          have h15 : δ * c ^ (K - 1) < δ * (2 / δ) := by gcongr
          have h16 : δ * (2 / δ) = 2 := by field_simp [hδ.ne'] <;> ring
          rw [h16] at h15; exact h15
        linarith
      · have h_k_eq_K : k = K := by omega
        rw [h_k_eq_K]
        rcases h_radius_nonempty with ⟨i, hi⟩
        have h81 : δ * c ^ k ≤ f i := (Finset.mem_filter.mp hi).2.1
        have h8 : δ * c ^ K ≤ f i := by rw [h_k_eq_K] at h81; exact h81
        have h9 : f i ≤ 2 := (hf_range i).2
        linarith
    have h_bin_prop : ∀ i ∈ sub, radius ≤ f i ∧ f i < c * radius := by
      intro i hi
      have h1 : δ * c ^ k ≤ f i ∧ f i < δ * c ^ (k + 1) := (Finset.mem_filter.mp hi).2
      have h2 : radius ≤ f i := by rw [hradius_def] <;> exact h1.1
      have h3 : f i < c * radius := by
        rw [hradius_def]
        have h4 : δ * c ^ (k + 1) = c * (δ * c ^ k) := by ring
        rw [h4] at h1; exact h1.2
      exact ⟨h2, h3⟩
    have hK1_le : (K + 1 : ENNReal) ≤ ENNReal.ofReal (Real.rpow δ (-familyLoss)) := by
      have h1 : (K + 1 : ℝ) ≤ Real.log (2 / δ) / Real.log (3 / 2) + 2 := by
        have h2 : (K : ℝ) < Real.log (2 / δ) / Real.log c + 1 := hK_lt
        simp only [c] at h2; linarith
      have h3 : (K + 1 : ℝ) ≤ Real.rpow δ (-familyLoss) := by linarith [h_log_bound]
      have h4 : (K + 1 : ENNReal) = ENNReal.ofReal ((K + 1 : ℝ)) := by
        norm_cast
      rw [h4]
      exact ENNReal.ofReal_le_ofReal h3
    have hK1_pos : (K + 1 : ENNReal) ≠ 0 := by simp
    have hK1_ne_top : (K + 1 : ENNReal) ≠ ⊤ := by simp
    have h_rpow_pos : 0 < Real.rpow δ (-familyLoss) := Real.rpow_pos_of_pos hδ (-familyLoss)
    have h_inv : (ENNReal.ofReal (Real.rpow δ (-familyLoss)))⁻¹ = ENNReal.ofReal (Real.rpow δ familyLoss) := by
      have h5 : Real.rpow δ (-familyLoss) = (Real.rpow δ familyLoss)⁻¹ := Real.rpow_neg hδ.le familyLoss
      have h6 : (Real.rpow δ (-familyLoss))⁻¹ = Real.rpow δ familyLoss := by
        rw [h5] <;> simp
      have h7 : (ENNReal.ofReal (Real.rpow δ (-familyLoss)))⁻¹ = ENNReal.ofReal ((Real.rpow δ (-familyLoss))⁻¹) := by
        rw [ENNReal.ofReal_inv_of_pos h_rpow_pos]
      rw [h7, h6]
    have h_card_ge : (sub.card : ENNReal) ≥
        ((Finset.univ : Finset α).card : ENNReal) / (K + 1 : ENNReal) := by
      have h_card : (Finset.range (K + 1)).card = K + 1 := by simp
      simpa [h_card] using hk_ge
    have h_main : (sub.card : ENNReal) ≥
        ENNReal.ofReal (Real.rpow δ familyLoss) * ((Finset.univ : Finset α).card : ENNReal) := by
      calc (sub.card : ENNReal)
        ≥ ((Finset.univ : Finset α).card : ENNReal) / (K + 1 : ENNReal) := h_card_ge
      _ ≥ ((Finset.univ : Finset α).card : ENNReal) / ENNReal.ofReal (Real.rpow δ (-familyLoss)) := by gcongr
      _ = ENNReal.ofReal (Real.rpow δ familyLoss) * ((Finset.univ : Finset α).card : ENNReal) := by
        rw [div_eq_mul_inv, h_inv] <;> ring
    exact ⟨radius, sub, h_delta_le_radius, h_radius_le_two, h_main, h_bin_prop⟩
  · -- Empty universe case
    refine ⟨δ, (∅ : Finset α), by linarith, by linarith, ?_, ?_⟩
    · have h1 : (Finset.univ : Finset α) = ∅ := by
        simpa [Finset.not_nonempty_iff_eq_empty] using h_univ
      have h2 : (Finset.univ : Finset α).card = 0 := by rw [h1] <;> simp
      simp [h2]
    · intro i hi; simp at hi

end Kakeya.Assouad
