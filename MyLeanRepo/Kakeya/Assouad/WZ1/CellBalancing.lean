import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Cell balancing pigeonholing lemma

Given a finite collection of measurable cells with positive volumes bounded between
Vmin and Vmax, select a dyadic band [M, 2M] containing at least a
1/(log_2(Vmax/Vmin) + 1) fraction of the total volume.
-/

noncomputable section

namespace Kakeya.Assouad

open Finset

/--
Dyadic cell balancing pigeonhole.

Given cells with volumes in [Vmin, Vmax], there exists M and a subset t such that
all cells in t have volume in [M, 2M] and the total volume of t is at least
the grand total divided by `log_2(Vmax/Vmin) + 1`.
-/
lemma cell_balance_pigeonhole_with_lower
    {α : Type*} [DecidableEq α] (s : Finset α)
    (v : α → ENNReal)
    (Vmin Vmax : ℝ)
    (_hpos : ∀ i ∈ s, 0 < v i)
    (hmax : ∀ i ∈ s, v i ≤ ENNReal.ofReal Vmax)
    (hmin : ∀ i ∈ s, ENNReal.ofReal Vmin ≤ v i)
    (hVmin_pos : 0 < Vmin)
    (hVmin_le_Vmax : Vmin ≤ Vmax) :
    ∃ (M : ENNReal) (t : Finset α),
      t ⊆ s ∧
      (ENNReal.ofReal Vmin ≤ M) ∧
      (∀ i ∈ t, M ≤ v i ∧ v i ≤ 2 * M) ∧
      (∑ i ∈ t, v i) ≥ (∑ i ∈ s, v i) / ENNReal.ofReal (Real.logb 2 (Vmax / Vmin) + 1) := by
  by_cases hs : s.Nonempty
  · -- Nonempty case
    set r : ℝ := Vmax / Vmin with hr_def
    have hr_pos : 0 < r := by
      apply div_pos
      · exact hVmin_pos.trans_le hVmin_le_Vmax
      · exact hVmin_pos
    have hr_one : 1 ≤ r := by
      have h'' : 1 ≤ Vmax / Vmin := by
        calc
          1 = Vmin / Vmin := by field_simp [hVmin_pos.ne']
          _ ≤ Vmax / Vmin := by gcongr
      exact h''
    have hlogb_nonneg : 0 ≤ Real.logb 2 r := by
      apply Real.logb_nonneg
      <;> norm_num <;> linarith
    -- Use K = floor(logb) + 1, so K > logb and K ≤ logb + 1
    let K : ℕ := Nat.floor (Real.logb 2 r) + 1
    have hK_gt : Real.logb 2 r < (K : ℝ) := by
      have h : Real.logb 2 r < ↑(Nat.floor (Real.logb 2 r)) + 1 :=
        Nat.lt_floor_add_one (Real.logb 2 r)
      simpa [K] using h
    have hK_le : (K : ℝ) ≤ Real.logb 2 r + 1 := by
      have h_floor_le : (Nat.floor (Real.logb 2 r) : ℝ) ≤ Real.logb 2 r :=
        Nat.floor_le hlogb_nonneg
      have h : (Nat.floor (Real.logb 2 r) : ℝ) + 1 ≤ Real.logb 2 r + 1 := by
        linarith
      simpa [K] using h
    have h_rpow_strict : r < (2 : ℝ) ^ K := by
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h_eq : (2 : ℝ) ^ Real.logb 2 r = r := by
        have h1 : (2 : ℝ) ^ Real.logb 2 r = Real.exp (Real.log 2 * Real.logb 2 r) := by
          rw [Real.rpow_def_of_pos (by norm_num)]
        rw [h1]
        have h2 : Real.log 2 * Real.logb 2 r = Real.log r := by
          simp [Real.logb]
          <;> field_simp [hlog2_pos.ne']
        rw [h2, Real.exp_log hr_pos]
      have h4 : Real.log 2 * Real.logb 2 r < Real.log 2 * (K : ℝ) := by
        exact mul_lt_mul_of_pos_left hK_gt hlog2_pos
      have h5 : Real.exp (Real.log 2 * Real.logb 2 r) < Real.exp (Real.log 2 * (K : ℝ)) :=
        Real.exp_strictMono h4
      have h6 : ∀ (x : ℝ), (2 : ℝ) ^ x = Real.exp (Real.log 2 * x) := by
        intro x
        rw [Real.rpow_def_of_pos (by norm_num)]
      have h7 : (2 : ℝ) ^ Real.logb 2 r < (2 : ℝ) ^ (K : ℝ) := by
        rw [h6 _, h6 _] <;> exact h5
      rw [h_eq] at h7
      exact_mod_cast h7
    have hVmax_lt : ENNReal.ofReal Vmax <
        ENNReal.ofReal Vmin * (2 : ENNReal) ^ K := by
      have h3 : Vmax < Vmin * (2 : ℝ) ^ K := by
        have h4 : Vmax / Vmin < (2 : ℝ) ^ K := h_rpow_strict
        calc
          Vmax = (Vmax / Vmin) * Vmin := by
            field_simp [hVmin_pos.ne']
          _ < ((2 : ℝ) ^ K) * Vmin := by gcongr
          _ = Vmin * (2 : ℝ) ^ K := by ring
      have h6 : ENNReal.ofReal Vmax < ENNReal.ofReal (Vmin * (2 : ℝ) ^ K) := by
        exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr h3
      have h7 : ENNReal.ofReal (Vmin * (2 : ℝ) ^ K) =
          ENNReal.ofReal Vmin * (2 : ENNReal) ^ K := by
        rw [ENNReal.ofReal_mul (by positivity)]
        <;> norm_cast
      rw [h7] at h6
      exact h6
    let M : ℕ → ENNReal := fun k =>
      ENNReal.ofReal Vmin * (2 : ENNReal) ^ k
    have hM_double : ∀ k : ℕ, M (k + 1) = 2 * M k := by
      intro k
      simp only [M]
      ring
    have hM_mono : ∀ (k l : ℕ), k ≤ l → M k ≤ M l := by
      intro k l hkl
      have hpow : (2 : ENNReal) ^ k ≤ (2 : ENNReal) ^ l := by
        gcongr
        <;> norm_num
      calc
        M k = ENNReal.ofReal Vmin * (2 : ENNReal) ^ k := by rfl
        _ ≤ ENNReal.ofReal Vmin * (2 : ENNReal) ^ l := by gcongr
        _ = M l := by rfl
    let band : ℕ → Finset α := fun k =>
      s.filter (fun i => M k ≤ v i ∧ v i < M (k + 1))
    have h_disjoint : ∀ k ∈ Finset.range K,
        ∀ l ∈ Finset.range K, k ≠ l → Disjoint (band k) (band l) := by
      intro k _ l _ hkl
      simp only [band, Finset.disjoint_left]
      intro i hi1 hi2
      have h1 : M k ≤ v i := (Finset.mem_filter.mp hi1).2.1
      have h2 : v i < M (k + 1) := (Finset.mem_filter.mp hi1).2.2
      have h3 : M l ≤ v i := (Finset.mem_filter.mp hi2).2.1
      have h4 : v i < M (l + 1) := (Finset.mem_filter.mp hi2).2.2
      by_cases hkl' : k < l
      · have h5 : k + 1 ≤ l := by omega
        have h6 : M (k + 1) ≤ M l := hM_mono (k + 1) l h5
        have h7 : M (k + 1) ≤ v i := h6.trans h3
        exact False.elim (not_le.mpr h2 h7)
      · have h6 : l < k := by omega
        have h7 : l + 1 ≤ k := by omega
        have h8 : M (l + 1) ≤ M k := hM_mono (l + 1) k h7
        have h9 : M (l + 1) ≤ v i := h8.trans h1
        exact False.elim (not_le.mpr h4 h9)
    have hK_pos : 0 < K := by
      simp [K] <;> omega
    have h_cover : ∀ i ∈ s, ∃ k ∈ Finset.range K, i ∈ band k := by
      intro i hi
      have hvi_min : M 0 ≤ v i := by
        simpa [M] using hmin i hi
      have hvi_max : v i < M K := by
        calc
          v i ≤ ENNReal.ofReal Vmax := hmax i hi
          _ < M K := hVmax_lt
      let P : ℕ → Prop := fun n => v i < M (n + 1)
      have h_witness : P (K - 1) := by
        have h_eq : (K - 1) + 1 = K := by omega
        simpa [P, h_eq] using hvi_max
      have hP : ∃ n : ℕ, P n := ⟨K - 1, h_witness⟩
      let k : ℕ := Nat.find hP
      have hk : P k := Nat.find_spec hP
      have hk_le : k ≤ K - 1 := by
        exact Nat.find_min' hP h_witness
      have hk_lt : k < K := by omega
      have h_k_min : M k ≤ v i := by
        by_contra h
        have h' : v i < M k := by exact lt_of_not_ge h
        if h0 : k = 0 then
          rw [h0] at h' <;> exact not_le.mpr h' hvi_min
        else
          have h_prev : k - 1 < k := by omega
          have h_prev2 : v i < M ((k - 1) + 1) := by
            have h_eq : (k - 1) + 1 = k := by omega
            rw [h_eq]
            exact h'
          exact Nat.find_min hP h_prev h_prev2
      have hk_range : k ∈ Finset.range K := by
        simp only [Finset.mem_range] <;> omega
      exact ⟨k, hk_range, Finset.mem_filter.mpr ⟨hi, h_k_min, hk⟩⟩
    have h_union : (Finset.biUnion (Finset.range K) band) = s := by
      ext i
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨k, _, hk⟩
        exact (Finset.mem_filter.mp hk).1
      · intro hi
        exact h_cover i hi
    have h_sum : ∑ k ∈ Finset.range K, ∑ i ∈ band k, v i =
        ∑ i ∈ s, v i := by
      rw [←Finset.sum_biUnion h_disjoint, h_union]
    have h_max : ∃ k ∈ Finset.range K,
        (K : ENNReal) * (∑ i ∈ band k, v i) ≥ ∑ i ∈ s, v i := by
      have h_nonempty : (Finset.range K).Nonempty := by
        simp [K] <;> omega
      have h : ∃ k ∈ Finset.range K,
          ∀ l ∈ Finset.range K,
            (∑ i ∈ band l, v i) ≤ (∑ i ∈ band k, v i) :=
        Finset.exists_max_image (Finset.range K)
          (fun k => ∑ i ∈ band k, v i) h_nonempty
      rcases h with ⟨k, hk, hmax⟩
      have h_le : ∑ l ∈ Finset.range K, (∑ i ∈ band l, v i) ≤
          (Finset.range K).card * (∑ i ∈ band k, v i) := by
        calc
          ∑ l ∈ Finset.range K, (∑ i ∈ band l, v i)
            ≤ ∑ l ∈ Finset.range K, (∑ i ∈ band k, v i) := by
              apply Finset.sum_le_sum
              intro l hl
              exact hmax l hl
          _ = (Finset.range K).card * (∑ i ∈ band k, v i) := by
            simp [Finset.sum_const]
            <;> ring
      have h_card : (Finset.range K).card = K := by simp
      rw [h_card] at h_le
      rw [h_sum] at h_le
      exact ⟨k, hk, h_le⟩
    rcases h_max with ⟨k, hk, hge⟩
    have hM_ge : ENNReal.ofReal Vmin ≤ M k := by
      have h1 : (1 : ENNReal) ≤ (2 : ENNReal) ^ k := by
        have h2 : ∀ n : ℕ, (1 : ENNReal) ≤ (2 : ENNReal) ^ n := by
          intro n
          induction n with
          | zero => simp
          | succ n ih =>
              have h3 :
                  (2 : ENNReal) ^ n ≤ (2 : ENNReal) ^ (n + 1) := by
                rw [pow_succ]
                simpa [mul_comm] using
                  mul_le_mul_left'
                    (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal))
                    ((2 : ENNReal) ^ n)
              exact ih.trans h3
        exact h2 k
      have h2 :
          ENNReal.ofReal Vmin * (1 : ENNReal) ≤
            ENNReal.ofReal Vmin * (2 : ENNReal) ^ k :=
        mul_le_mul_left' h1 (ENNReal.ofReal Vmin)
      simpa [M] using h2
    have h_sub : band k ⊆ s := Finset.filter_subset _ _
    have h_balance : ∀ i ∈ band k, M k ≤ v i ∧ v i ≤ 2 * M k := by
      intro i hi
      have h := (Finset.mem_filter.mp hi).2
      have h_upper : v i ≤ 2 * M k := by
        have h9 : v i < M (k + 1) := h.2
        have h10 : M (k + 1) = 2 * M k := hM_double k
        rw [h10] at h9
        exact le_of_lt h9
      exact ⟨h.1, h_upper⟩
    have h_retention :
        (∑ i ∈ band k, v i) ≥
          (∑ i ∈ s, v i) /
            ENNReal.ofReal (Real.logb 2 r + 1) := by
      have h_K_le_ennreal : (K : ENNReal) ≤ ENNReal.ofReal (Real.logb 2 r + 1) := by
        have h9 : (K : ℝ) ≤ Real.logb 2 r + 1 := hK_le
        have h10 : ENNReal.ofReal (K : ℝ) ≤ ENNReal.ofReal (Real.logb 2 r + 1) :=
          ENNReal.ofReal_le_ofReal h9
        simpa using h10
      have h_div : (∑ i ∈ s, v i) / (K : ENNReal) ≥
          (∑ i ∈ s, v i) / ENNReal.ofReal (Real.logb 2 r + 1) := by
        gcongr
      have hK_ne_zero : (K : ENNReal) ≠ 0 := by
        simp [K] <;> positivity
      have h_main : (∑ i ∈ s, v i) / (K : ENNReal) ≤ (∑ i ∈ band k, v i) := by
        have h : (∑ i ∈ s, v i) ≤ (K : ENNReal) * (∑ i ∈ band k, v i) := hge
        have hK_ne_top : (K : ENNReal) ≠ ⊤ := by simp
        have h3 : (K : ENNReal) * (K : ENNReal)⁻¹ = 1 := by
          apply ENNReal.mul_inv_cancel <;> simp [hK_ne_zero]
        have hcancel : ((K : ENNReal) * (∑ i ∈ band k, v i)) / (K : ENNReal) = (∑ i ∈ band k, v i) := by
          simp only [div_eq_mul_inv]
          rw [mul_assoc, mul_comm (∑ i ∈ band k, v i), ←mul_assoc, h3, one_mul]
        calc
          (∑ i ∈ s, v i) / (K : ENNReal)
            ≤ ((K : ENNReal) * (∑ i ∈ band k, v i)) / (K : ENNReal) := by gcongr
          _ = (∑ i ∈ band k, v i) := hcancel
      exact h_div.trans h_main
    exact ⟨M k, band k, h_sub, hM_ge, h_balance, h_retention⟩
  · -- Empty case
    have h_empty : s = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using hs
    refine ⟨ENNReal.ofReal Vmin, ∅, by simp, by simp, by simp, ?_⟩
    rw [h_empty]
    <;> simp

/--
Compatibility form of `cell_balance_pigeonhole_with_lower` that forgets the
explicit lower bound on the selected dyadic scale.
-/
lemma cell_balance_pigeonhole
    {α : Type*} [DecidableEq α] (s : Finset α)
    (v : α → ENNReal)
    (Vmin Vmax : ℝ)
    (hpos : ∀ i ∈ s, 0 < v i)
    (hmax : ∀ i ∈ s, v i ≤ ENNReal.ofReal Vmax)
    (hmin : ∀ i ∈ s, ENNReal.ofReal Vmin ≤ v i)
    (hVmin_pos : 0 < Vmin)
    (hVmin_le_Vmax : Vmin ≤ Vmax) :
    ∃ (M : ENNReal) (t : Finset α),
      t ⊆ s ∧
      (∀ i ∈ t, M ≤ v i ∧ v i ≤ 2 * M) ∧
      (∑ i ∈ t, v i) ≥
        (∑ i ∈ s, v i) /
          ENNReal.ofReal (Real.logb 2 (Vmax / Vmin) + 1) := by
  rcases cell_balance_pigeonhole_with_lower s v Vmin Vmax
      hpos hmax hmin hVmin_pos hVmin_le_Vmax with
    ⟨M, t, ht, _hM, hband, hmass⟩
  exact ⟨M, t, ht, hband, hmass⟩

end Kakeya.Assouad
