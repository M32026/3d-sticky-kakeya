import MyLeanRepo.Kakeya.Streamlined.Basic

/-!
# ENNReal dyadic weight binning

Given finite weights, select a nonempty subfamily whose weights all lie in one
dyadic interval `[c, 2c]`, are above a minimum threshold, and retain at least
`1/bins` of the total mass after discarding low-weight elements.

The number of dyadic bins is `Nat.log 2 (2 * |α|) + 1`.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Dyadic weight binning: discard elements below `total / (2 * |α|)`, then partition
the remainder into `Nat.log 2 (2 * |α|) + 1` dyadic bins and return the
maximum-mass bin.  The selected bin is nonempty, has all weights in `[c, 2c]`
for some `c > 0`, and retains at least `total / (2 * bins)` mass.
-/
lemma ennreal_dyadic_bin {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ENNReal) (total : ENNReal) (htotal : total = ∑ i, w i)
    (htotal_lt_top : total ≠ ⊤) (htotal_pos : 0 < total) :
    ∃ (bins : ℕ) (S : Finset α),
      bins = Nat.log 2 (2 * Fintype.card α) + 1 ∧
      S.Nonempty ∧
      (∑ i ∈ S, w i) * bins ≥ total / 2 ∧
      (∀ i ∈ S, total / (2 * Fintype.card α) ≤ w i) ∧
      (∃ (c : ENNReal), 0 < c ∧ ∀ i ∈ S, c ≤ w i ∧ w i ≤ 2 * c) := by
  classical
  let N := Fintype.card α
  have hN_pos : 0 < N := by
    by_contra h
    have h' : N = 0 := by omega
    have h_empty : IsEmpty α := by
      rw [Fintype.card_eq_zero_iff] at h' <;> exact h'
    have h_total0 : total = 0 := by
      rw [htotal]
      simp [h_empty]
    exact htotal_pos.ne' h_total0
  let twoN : ENNReal := ↑(2 * N)
  have htwoN_ne_zero : twoN ≠ 0 := by
    simp [twoN] <;> omega
  have htwoN_ne_top : twoN ≠ ⊤ := ENNReal.coe_ne_top
  have htwoN_pos : 0 < twoN := Ne.bot_lt htwoN_ne_zero
  let threshold : ENNReal := total / twoN
  have hthreshold_pos : 0 < threshold :=
    ENNReal.div_pos htotal_pos.ne' htwoN_ne_top
  have hthreshold_ne_top : threshold ≠ ⊤ :=
    ENNReal.div_ne_top htotal_lt_top htwoN_ne_zero
  have h_half_ne_top : total / 2 ≠ ⊤ :=
    ENNReal.div_ne_top htotal_lt_top (by norm_num)
  let bins : ℕ := Nat.log 2 (2 * N) + 1
  have hbins_pos : 0 < bins := by simp [bins] <;> omega
  have h_twoN_lt : twoN < (2 ^ bins : ENNReal) := by
    have h1 : 2 * N < 2 ^ bins := by
      simp [bins, Nat.lt_pow_succ_log_self] <;> omega
    have h2 : (twoN : ENNReal) = ↑(2 * N) := by rfl
    rw [h2]
    exact_mod_cast h1
  let c : ℕ → ENNReal := fun k => threshold * 2 ^ k
  have h_inv_mul : twoN⁻¹ * twoN = 1 :=
    ENNReal.inv_mul_cancel htwoN_ne_zero htwoN_ne_top
  have h_total_eq : threshold * twoN = total := by
    have h1 : (total / twoN) * twoN = total * (twoN⁻¹ * twoN) := by
      simp [threshold, div_eq_mul_inv] <;> ring
    rw [h1, h_inv_mul] <;> ring
  have h_twoN_add_one_le : (twoN + 1 : ENNReal) ≤ (2 ^ bins : ENNReal) := by
    have h1 : 2 * N + 1 ≤ 2 ^ bins := by
      simp [bins, Nat.lt_pow_succ_log_self] <;> omega
    have h2 : ((twoN + 1 : ENNReal)) = ↑(2 * N + 1) := by
      simp [twoN] <;> norm_cast
    rw [h2]
    norm_cast <;> exact h1
  have h_strict_mul : threshold * twoN < threshold * (twoN + 1 : ENNReal) := by
    have h1 : threshold * twoN ≠ ⊤ := ENNReal.mul_ne_top hthreshold_ne_top htwoN_ne_top
    have h2 : threshold * (twoN + 1 : ENNReal) = threshold * twoN + threshold := by
      rw [mul_add] <;> ring
    rw [h2]
    exact ENNReal.lt_add_right h1 hthreshold_pos.ne'
  have h_total_lt_cbins : total < c bins := by
    have h_eq : total = threshold * twoN := h_total_eq.symm
    rw [h_eq]
    have h3 : threshold * (twoN + 1 : ENNReal) ≤ threshold * (2 ^ bins : ENNReal) :=
      mul_le_mul_of_nonneg_left h_twoN_add_one_le (by positivity)
    exact lt_of_lt_of_le h_strict_mul h3
  let S0 : Finset α := Finset.univ.filter (fun i => threshold ≤ w i)
  have h_N_mul_threshold : (N : ENNReal) * threshold = total / 2 := by
    have h1 : twoN * threshold = total := by
      rw [mul_comm]
      exact h_total_eq
    have h2 : twoN * threshold = 2 * ((N : ENNReal) * threshold) := by
      simp [twoN, mul_comm] <;> ring
    rw [h2] at h1
    have h3 : 2 * ((N : ENNReal) * threshold) = total := h1
    have h4 : (2 : ENNReal) ≠ 0 := by norm_num
    have h5 : (2 : ENNReal) ≠ ⊤ := by norm_num
    have h6 : ((2 : ENNReal)⁻¹ * (2 : ENNReal)) = 1 :=
      ENNReal.inv_mul_cancel h4 h5
    have h7 : (2 * ((N : ENNReal) * threshold)) / 2 = (N : ENNReal) * threshold := by
      calc
        (2 * ((N : ENNReal) * threshold)) / 2
          = (2 * ((N : ENNReal) * threshold)) * (2 : ENNReal)⁻¹ := by rfl
        _ = ((N : ENNReal) * threshold) * ((2 : ENNReal) * (2 : ENNReal)⁻¹) := by ring
        _ = ((N : ENNReal) * threshold) * 1 := by rw [←h6] <;> ring
        _ = (N : ENNReal) * threshold := by ring
    have h8 : (2 * ((N : ENNReal) * threshold)) / 2 = total / 2 := by rw [h3]
    rw [h7] at h8
    exact h8
  have h_mass_S0 : total / 2 ≤ ∑ i ∈ S0, w i := by
    let S1 := Finset.univ \ S0
    have h_disj : Disjoint S0 S1 := by
      simp [S1, Finset.disjoint_left] <;> tauto
    have h_univ : S0 ∪ S1 = Finset.univ := by
      simp [S1, Finset.ext] <;> tauto
    have h_sum : (∑ i ∈ S0, w i) + (∑ i ∈ S1, w i) = total := by
      have h : (∑ i ∈ S0 ∪ S1, w i) = (∑ i ∈ S0, w i) + (∑ i ∈ S1, w i) :=
        Finset.sum_union h_disj
      rw [←h, h_univ, ←htotal]
    have h_S1_card_le : S1.card ≤ N := by
      have h : S1 ⊆ Finset.univ := Finset.subset_univ _
      have h2 : S1.card ≤ (Finset.univ : Finset α).card := Finset.card_le_card h
      simpa using h2
    have h_S1_le : ∑ i ∈ S1, w i ≤ total / 2 := by
      have h2 : ∀ i ∈ S1, w i ≤ threshold := by
        intro i hi
        have h3 : i ∉ S0 := (Finset.mem_sdiff).mp hi |>.2
        have h4 : ¬(threshold ≤ w i) := by
          simpa [S0, Finset.mem_filter] using h3
        exact le_of_not_ge h4
      calc
        ∑ i ∈ S1, w i ≤ ∑ i ∈ S1, threshold := Finset.sum_le_sum h2
        _ = (S1.card : ENNReal) * threshold := by
          simp [Finset.sum_const] <;> ring
        _ ≤ (N : ENNReal) * threshold := by
          have h_card : (S1.card : ENNReal) ≤ (N : ENNReal) := by exact_mod_cast h_S1_card_le
          exact mul_le_mul_of_nonneg_right h_card (by positivity)
        _ = total / 2 := h_N_mul_threshold
    have h3 : (∑ i ∈ S0, w i) + (∑ i ∈ S1, w i) = total := h_sum
    have h4 : (∑ i ∈ S0, w i) + total / 2 ≥ total := by
      calc
        (∑ i ∈ S0, w i) + total / 2
          ≥ (∑ i ∈ S0, w i) + (∑ i ∈ S1, w i) := by gcongr
        _ = total := h3
    have h5 : total / 2 + total / 2 = total := ENNReal.add_halves total
    have h6 : total / 2 + total / 2 ≤ (∑ i ∈ S0, w i) + total / 2 := by
      rw [h5] <;> exact h4
    exact (ENNReal.add_le_add_iff_right h_half_ne_top).mp h6
  let B : ℕ → Finset α := fun k =>
    S0.filter (fun i => c k ≤ w i ∧ w i < 2 * c k)
  have h_bins_partition : S0 ⊆ Finset.biUnion (Finset.range bins) B := by
    intro i hi
    have h_i_S0 : threshold ≤ w i := (Finset.mem_filter.mp hi).2
    have h_wi_le_total : w i ≤ total := by
      rw [htotal]
      exact Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ i)
    have h_wi_lt_cbins : w i < c bins :=
      lt_of_le_of_lt h_wi_le_total h_total_lt_cbins
    have h_exists : ∃ k : ℕ, w i < c (k + 1) := by
      refine ⟨bins - 1, ?_⟩
      have h : c ((bins - 1) + 1) = c bins := by
        have h_eq : (bins - 1) + 1 = bins := Nat.sub_add_cancel hbins_pos
        rw [h_eq]
      rw [h]
      exact h_wi_lt_cbins
    let k := Nat.find h_exists
    have hk : w i < c (k + 1) := Nat.find_spec h_exists
    have h_k_le : k ≤ bins - 1 := by
      apply Nat.find_min' h_exists
      have h_eq : (bins - 1) + 1 = bins := Nat.sub_add_cancel hbins_pos
      rw [h_eq]
      exact h_wi_lt_cbins
    have h_k_lt_bins : k < bins := by omega
    have h_ck_le : c k ≤ w i := by
      by_cases h_k0 : k = 0
      · rw [h_k0]
        simpa [c] using h_i_S0
      · have h_k_pos : 0 < k := by omega
        have h5 : ¬(w i < c k) := by
          intro h6
          have h_lt : k - 1 < k := by omega
          have h7 := Nat.find_min h_exists h_lt
          have h8 : c ((k - 1) + 1) = c k := by
            have h_eq : (k - 1) + 1 = k := Nat.sub_add_cancel h_k_pos
            rw [h_eq]
          rw [h8] at h7
          exact h7 h6
        exact le_of_not_gt h5
    have h9 : w i < 2 * c k := by
      have h10 : c (k + 1) = 2 * c k := by
        simp [c, pow_succ] <;> ring
      rw [h10] at hk
      exact hk
    have h11 : i ∈ B k := by
      simp only [B, Finset.mem_filter]
      exact ⟨hi, h_ck_le, h9⟩
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr h_k_lt_bins, h11⟩
  have h_disj_bins : ∀ k1 ∈ Finset.range bins, ∀ k2 ∈ Finset.range bins,
      k1 ≠ k2 → Disjoint (B k1) (B k2) := by
    intro k1 _ k2 _ hne
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have h1 : c k1 ≤ w i ∧ w i < 2 * c k1 := (Finset.mem_filter.mp hi1).2
    have h2 : c k2 ≤ w i ∧ w i < 2 * c k2 := (Finset.mem_filter.mp hi2).2
    by_cases h : k1 < k2
    · have h4 : k1 + 1 ≤ k2 := by omega
      have h5 : (2 ^ (k1 + 1) : ENNReal) ≤ (2 ^ k2 : ENNReal) := by
        have h6 : 2 ^ (k1 + 1) ≤ 2 ^ k2 := by
          gcongr
          <;> omega
        exact_mod_cast h6
      have h3 : 2 * c k1 ≤ c k2 := by
        have h7 : 2 * c k1 = threshold * (2 ^ (k1 + 1) : ENNReal) := by
          simp [c, pow_succ] <;> ring
        rw [h7]
        exact mul_le_mul_of_nonneg_left h5 (by positivity)
      have h4' : w i < 2 * c k1 := h1.2
      have h5' : c k2 ≤ w i := h2.1
      exact False.elim (not_le.mpr h4' (le_trans h3 h5'))
    · have h' : k2 < k1 := by omega
      have h4 : k2 + 1 ≤ k1 := by omega
      have h5 : (2 ^ (k2 + 1) : ENNReal) ≤ (2 ^ k1 : ENNReal) := by
        have h6 : 2 ^ (k2 + 1) ≤ 2 ^ k1 := by
          gcongr
          <;> omega
        exact_mod_cast h6
      have h3 : 2 * c k2 ≤ c k1 := by
        have h7 : 2 * c k2 = threshold * (2 ^ (k2 + 1) : ENNReal) := by
          simp [c, pow_succ] <;> ring
        rw [h7]
        exact mul_le_mul_of_nonneg_left h5 (by positivity)
      have h4' : w i < 2 * c k2 := h2.2
      have h5' : c k1 ≤ w i := h1.1
      exact False.elim (not_le.mpr h4' (le_trans h3 h5'))
  have h_sum_bins : ∑ k ∈ Finset.range bins, ∑ i ∈ B k, w i = ∑ i ∈ S0, w i := by
    have h : Finset.biUnion (Finset.range bins) B = S0 := by
      apply Finset.Subset.antisymm
      · intro i hi
        rcases Finset.mem_biUnion.mp hi with ⟨k, _, hki⟩
        exact (Finset.mem_filter.mp hki).1
      · exact h_bins_partition
    have h2 : ∑ k ∈ Finset.range bins, ∑ i ∈ B k, w i =
        ∑ i ∈ Finset.biUnion (Finset.range bins) B, w i :=
      (Finset.sum_biUnion h_disj_bins).symm
    rw [h2, h]
  have h_exists_max : ∃ k ∈ Finset.range bins,
      ∀ j ∈ Finset.range bins, (∑ i ∈ B j, w i) ≤ (∑ i ∈ B k, w i) :=
    Finset.exists_max_image (Finset.range bins) (fun k => ∑ i ∈ B k, w i)
      (by simp [hbins_pos])
  rcases h_exists_max with ⟨k, hk_in, hmax⟩
  let S := B k
  have h_mass_S : (∑ i ∈ S, w i) * bins ≥ ∑ i ∈ S0, w i := by
    have h1 : ∑ j ∈ Finset.range bins, (∑ i ∈ B j, w i) ≤
        ∑ j ∈ Finset.range bins, (∑ i ∈ S, w i) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hmax j hj
    have h2 : ∑ j ∈ Finset.range bins, (∑ i ∈ S, w i) =
        (bins : ENNReal) * (∑ i ∈ S, w i) := by
      simp [Finset.sum_const, Finset.card_range] <;> ring
    rw [h2] at h1
    have h3 : (bins : ENNReal) * (∑ i ∈ S, w i) =
        (∑ i ∈ S, w i) * (bins : ENNReal) := by ring
    rw [h3] at h1
    rw [h_sum_bins] at h1
    exact h1
  have h_S_nonempty : S.Nonempty := by
    by_contra h
    have h' : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have h_mass0 : (∑ i ∈ S, w i) = 0 := by
      rw [h'] <;> simp
    have h_cont : (∑ i ∈ S0, w i) ≤ 0 := by
      have h9 : (∑ i ∈ S, w i) * (bins : ENNReal) = 0 := by
        rw [h_mass0] <;> simp
      rw [h9] at h_mass_S
      exact h_mass_S
    have h10 : total / 2 ≤ 0 := le_trans h_mass_S0 h_cont
    have h11 : 0 < total / 2 := ENNReal.div_pos htotal_pos.ne' (by norm_num)
    exact not_le.mpr h11 h10
  have h_final_mass : (∑ i ∈ S, w i) * bins ≥ total / 2 :=
    le_trans h_mass_S0 h_mass_S
  have h_threshold1 : ∀ i ∈ S, threshold ≤ w i := by
    intro i hi
    have h1 : c k ≤ w i := (Finset.mem_filter.mp hi).2.1
    have h2 : threshold ≤ c k := by
      have h3 : c k = threshold * (2 ^ k : ENNReal) := by rfl
      rw [h3]
      have h4 : (1 : ENNReal) ≤ (2 ^ k : ENNReal) := by
        exact_mod_cast Nat.one_le_pow k 2 (by norm_num)
      have h5 : threshold * (1 : ENNReal) ≤ threshold * (2 ^ k : ENNReal) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      simpa using h5
    exact le_trans h2 h1
  have h_threshold2 : ∀ i ∈ S, total / (2 * Fintype.card α) ≤ w i := by
    intro i hi
    have h_goal : threshold ≤ w i := h_threshold1 i hi
    have h_eq : threshold = total / (2 * Fintype.card α) := by
      simp [threshold, twoN, N] <;> rfl
    have h_final : total / (2 * Fintype.card α) ≤ w i := by
      calc
        total / (2 * Fintype.card α) = threshold := h_eq.symm
        _ ≤ w i := h_goal
    exact h_final
  refine ⟨bins, S, rfl, h_S_nonempty, h_final_mass, h_threshold2, ?_⟩
  have h_c_pos : 0 < c k := by
    have h1 : threshold ≠ 0 := hthreshold_pos.ne'
    have h2 : (2 ^ k : ENNReal) ≠ 0 := by
      have h3 : 0 < 2 ^ k := by positivity
      exact_mod_cast (show (2 ^ k : ℕ) ≠ 0 from by omega)
    exact ENNReal.mul_pos h1 h2
  exact ⟨c k, h_c_pos, fun i hi =>
    ⟨(Finset.mem_filter.mp hi).2.1,
     le_of_lt (Finset.mem_filter.mp hi).2.2⟩⟩

end Kakeya.Assouad
