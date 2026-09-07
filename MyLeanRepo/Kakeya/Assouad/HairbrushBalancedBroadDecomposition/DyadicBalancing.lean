import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic

/-!
# Dyadic balancing lemma with logarithmic loss

Given non-negative reals `c_i` with sum ≥ C * total, where C ≥ 1 + log N,
there exists a subset of indices of size M such that:
  each selected c_i ≥ total / M
  sum of selected c_i ≥ total

This is proved by sorting descending and using the harmonic series bound.
-/

noncomputable section

open Finset BigOperators

namespace Kakeya.Assouad

/-- Harmonic number bound: ∑_{k=1}^N 1/k ≤ 1 + log N for N ≥ 1. -/
lemma harmonic_sum_bound (N : ℕ) (hN : 0 < N) :
    ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) ≤ 1 + Real.log (N : ℝ) := by
  induction N with
  | zero => contradiction
  | succ N ih =>
    by_cases hN0 : N = 0
    · subst hN0
      norm_num
    · have hN_pos : 0 < N := Nat.pos_of_ne_zero hN0
      rw [Finset.sum_Icc_succ_top (show 1 ≤ N.succ from by omega)]
      have h_ih : ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) ≤ 1 + Real.log (N : ℝ) := ih hN_pos
      set x : ℝ := (N.succ : ℝ) / (N : ℝ) with hx
      have hx_pos : 0 < x := by positivity
      have h1 : Real.log x ≥ 1 - 1 / x := by
        have h2 : Real.log (1 / x) ≤ 1 / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
        have h3 : Real.log (1 / x) = -Real.log x := by
          rw [Real.log_div (by norm_num) hx_pos.ne']
          simp
        linarith
      have h4 : 1 - 1 / x = 1 / (N.succ : ℝ) := by
        simp [hx] <;> field_simp <;> ring
      have h5 : Real.log x = Real.log (N.succ : ℝ) - Real.log (N : ℝ) := by
        rw [hx, Real.log_div (by positivity) (by positivity)]
      have h6 : 1 / (N.succ : ℝ) ≤ Real.log (N.succ : ℝ) - Real.log (N : ℝ) := by
        linarith [h1, h4, h5]
      linarith

/-- Dyadic balancing for sorted non-increasing non-negative reals.

Given c_0 ≥ c_1 ≥ ... ≥ c_{N-1} ≥ 0 with sum ≥ total, and C ≥ 1 + log N,
there exists k ∈ {1,...,N} such that:
  for all i < k: total ≤ C * k * c_i
  total / C ≤ ∑_{i<k} c_i
-/
lemma dyadic_balancing_sorted {N : ℕ} (hN : 0 < N)
    (c : Fin N → ℝ) (hc_nonneg : ∀ i, 0 ≤ c i)
    (h_sort : ∀ i j : Fin N, i ≤ j → c i ≥ c j)
    (total C : ℝ) (hC_pos : 0 < C) (hC_log : C ≥ 1 + Real.log (N : ℝ))
    (h_total : total ≤ ∑ i : Fin N, c i) :
    ∃ (k : ℕ) (hk_pos : 0 < k) (hk_le : k ≤ N),
      (∀ i : Fin k, total ≤ C * (k : ℝ) * c (Fin.castLE hk_le i)) ∧
      total / C ≤ ∑ i : Fin k, c (Fin.castLE hk_le i) := by
  let i0' : Fin N := ⟨0, hN⟩
  let f : Fin N → ℝ := fun i => ((i.val : ℝ) + 1) * c i
  let s : Finset ℝ := Finset.image f (Finset.univ)
  have hs_nonempty : s.Nonempty := by
    refine' ⟨f i0', _⟩
    exact Finset.mem_image.mpr ⟨i0', Finset.mem_univ i0', rfl⟩
  let M_val : ℝ := Finset.max' s hs_nonempty
  have hM_ge : ∀ i : Fin N, f i ≤ M_val := by
    intro i
    have h_in : f i ∈ s := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    exact Finset.le_max' s (f i) h_in
  have hM_nonneg : 0 ≤ M_val := by
    have h0 : 0 ≤ c i0' := hc_nonneg i0'
    have h_f0 : 0 ≤ f i0' := by
      dsimp only [f]
      exact mul_nonneg (by norm_num) h0
    exact h_f0.trans (hM_ge i0')
  -- Sum equality: ∑ c_i = ∑ f i / (i+1)
  have h_sum_eq : ∑ i : Fin N, c i = ∑ i : Fin N, f i / ((i.val : ℝ) + 1) := by
    apply Finset.sum_congr rfl
    intro i _
    simp [f] <;> field_simp <;> ring
  have h_sum_le : ∑ i : Fin N, c i ≤ M_val * ∑ i : Fin N, 1 / ((i.val : ℝ) + 1) := by
    rw [h_sum_eq]
    have h4 : ∑ i : Fin N, f i / ((i.val : ℝ) + 1) ≤
        ∑ i : Fin N, M_val * (1 / ((i.val : ℝ) + 1)) := by
      apply Finset.sum_le_sum
      intro i _
      have h5 : f i ≤ M_val := hM_ge i
      have h6 : 0 < ((i.val : ℝ) + 1) := by positivity
      calc f i / ((i.val : ℝ) + 1)
          ≤ M_val / ((i.val : ℝ) + 1) := by gcongr
        _ = M_val * (1 / ((i.val : ℝ) + 1)) := by ring
    rw [Finset.mul_sum] at *
    exact h4
  have h_idx_eq : ∑ i : Fin N, 1 / ((i.val : ℝ) + 1) = ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) := by
    let g : Fin N → ℕ := fun i => i.val + 1
    let f : ℕ → ℝ := fun k => 1 / (k : ℝ)
    have h_inj : Set.InjOn g (Finset.univ : Finset (Fin N)) := by
      intro i _ j _ h
      have h' : i.val = j.val := by
        simpa [g] using h
      exact Fin.ext h'
    have h_sum_image : ∑ i : Fin N, f (g i) = ∑ k ∈ Finset.image g (Finset.univ), f k :=
      Eq.symm (Finset.sum_image h_inj)
    have h_image : Finset.image g (Finset.univ) = Finset.Icc 1 N := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Icc, g]
      constructor
      · rintro ⟨i, rfl⟩
        constructor <;> omega
      · rintro ⟨h1, h2⟩
        have h3 : x - 1 < N := by omega
        refine' ⟨⟨x - 1, h3⟩, _⟩
        have h4 : (x - 1) + 1 = x := by omega
        exact h4
    have h_eq1 : ∑ i : Fin N, 1 / ((i.val : ℝ) + 1) = ∑ i : Fin N, f (g i) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [f, g]
      <;> norm_cast <;> ring
    rw [h_eq1, h_sum_image, h_image]
  rw [h_idx_eq] at h_sum_le
  have h_harmonic : ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) ≤ 1 + Real.log (N : ℝ) :=
    harmonic_sum_bound N hN
  have hT_le_MC : total ≤ M_val * C := by
    calc total
      ≤ ∑ i : Fin N, c i := h_total
    _ ≤ M_val * ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) := h_sum_le
    _ ≤ M_val * (1 + Real.log (N : ℝ)) := by
      gcongr
      <;> linarith
    _ ≤ M_val * C := by
      gcongr <;> exact hC_log
  -- Pick i0 achieving M_val
  have hM_in : M_val ∈ s := Finset.max'_mem s hs_nonempty
  rcases Finset.mem_image.mp hM_in with ⟨i0, _, hi0_eq⟩
  let k : ℕ := i0.val + 1
  have hk_pos : 0 < k := by
    simp [k] <;> omega
  have hk_le : k ≤ N := by
    simp [k] <;> exact i0.is_lt
  have h_ci0_eq : c i0 = M_val / (k : ℝ) := by
    have h : f i0 = (k : ℝ) * c i0 := by
      simp [f, k] <;> ring
    rw [h] at hi0_eq
    field_simp [hk_pos.ne'] at hi0_eq ⊢ <;> linarith
  have h_balance : ∀ i : Fin k, total ≤ C * (k : ℝ) * c (Fin.castLE hk_le i) := by
    intro i
    have h_ival : i.val < k := i.is_lt
    have h_ival_le : i.val ≤ i0.val := by
      simp only [k] at h_ival <;> omega
    have h_i_le : (Fin.castLE hk_le i) ≤ i0 := by
      exact Fin.le_iff_val_le_val.mpr h_ival_le
    have h8 : c (Fin.castLE hk_le i) ≥ c i0 := h_sort _ _ h_i_le
    have h9 : C * (k : ℝ) * c (Fin.castLE hk_le i) ≥ C * (k : ℝ) * (M_val / (k : ℝ)) := by
      gcongr <;> linarith
    have h10 : C * (k : ℝ) * (M_val / (k : ℝ)) = M_val * C := by
      field_simp [hC_pos.ne', hk_pos.ne'] <;> ring
    have h11 : total ≤ M_val * C := hT_le_MC
    linarith
  have h_retention : total / C ≤ ∑ i : Fin k, c (Fin.castLE hk_le i) := by
    have h12 : ∀ i : Fin k, c (Fin.castLE hk_le i) ≥ c i0 := by
      intro i
      have h_ival : i.val < k := i.is_lt
      have h_ival_le : i.val ≤ i0.val := by
        simp only [k] at h_ival <;> omega
      have h_i_le : (Fin.castLE hk_le i) ≤ i0 := by
        exact Fin.le_iff_val_le_val.mpr h_ival_le
      exact h_sort _ _ h_i_le
    have h_card : Finset.card (Finset.univ : Finset (Fin k)) = k := by simp
    have h13 : ∑ i : Fin k, c (Fin.castLE hk_le i) ≥ (k : ℝ) * c i0 := by
      calc ∑ i : Fin k, c (Fin.castLE hk_le i)
        ≥ ∑ i : Fin k, c i0 := Finset.sum_le_sum (fun i _ => h12 i)
      _ = (Finset.card (Finset.univ) : ℝ) * c i0 := by
        rw [Finset.sum_const] <;> ring
      _ = (k : ℝ) * c i0 := by rw [h_card] <;> ring
    have h14 : (k : ℝ) * c i0 = M_val := by
      have h : f i0 = (k : ℝ) * c i0 := by simp [f, k] <;> ring
      rw [h] at hi0_eq; exact hi0_eq
    have h15 : M_val ≥ total / C := by
      have h16 : total ≤ M_val * C := hT_le_MC
      calc M_val
        = (M_val * C) / C := by field_simp [hC_pos.ne'] <;> ring
      _ ≥ total / C := by gcongr
    linarith [h13, h14, h15]
  exact ⟨k, hk_pos, hk_le, h_balance, h_retention⟩

/-- Dyadic balancing with logarithmic loss.

Given non-negative `cards i` with `C * total ≤ ∑ cards i` and `C ≥ 1 + log N`,
there exists an injective selection of M indices such that:
  each selected card ≥ total / M
  sum of selected cards ≥ total
-/
lemma dyadic_balancing_with_log {N : ℕ} (hN : 0 < N)
    (cards : Fin N → ℝ) (h_nonneg : ∀ i, 0 ≤ cards i)
    (total C : ℝ) (hC : C ≥ 1 + Real.log (N : ℝ))
    (h_total : C * total ≤ ∑ i : Fin N, cards i) :
    ∃ (M : ℕ) (hm_pos : 0 < M) (select : Fin M → Fin N),
      Function.Injective select ∧
      (∀ k : Fin M, total ≤ (M : ℝ) * cards (select k)) ∧
      total ≤ ∑ k : Fin M, cards (select k) := by
  have hC_pos : 0 < C := by
    have h1 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    linarith
  -- Sort cards in non-increasing order using Tuple.sort on negated values
  let neg_cards : Fin N → ℝ := fun i => -cards i
  let σ : Equiv.Perm (Fin N) := Tuple.sort neg_cards
  have h_eq_sort : σ = Tuple.sort neg_cards := by rfl
  have hσ_sort : Monotone (fun i : Fin N => -cards (σ i)) :=
    (Tuple.eq_sort_iff.mp h_eq_sort).1
  let c : Fin N → ℝ := fun i => cards (σ i)
  have hc_nonneg : ∀ i, 0 ≤ c i := fun i => h_nonneg (σ i)
  have h_sort : ∀ (i j : Fin N), i ≤ j → c i ≥ c j := by
    intro i j hij
    have h : -c i ≤ -c j := hσ_sort hij
    linarith
  have h_sum : ∑ i : Fin N, c i = ∑ i : Fin N, cards i := by
    have h : ∑ i : Fin N, c i = ∑ i : Fin N, cards (σ i) := by rfl
    rw [h]
    apply Finset.sum_bij' (fun (i : Fin N) _ => σ i) (fun (j : Fin N) _ => σ.symm j)
    · intro i _; exact Finset.mem_univ _
    · intro j _; exact Finset.mem_univ _
    · intro i _; simp
    · intro j _; simp
    · intro i _; rfl
  let total' : ℝ := C * total
  have h_total' : total' ≤ ∑ i : Fin N, c i := by
    rw [h_sum] <;> exact h_total
  -- Apply sorted balancing
  rcases dyadic_balancing_sorted hN c hc_nonneg h_sort total' C hC_pos hC h_total' with
    ⟨M, hm_pos, hm_le, h_balance, h_retention⟩
  -- Simplify the conclusions
  have h_balance_simp : ∀ i : Fin M, total ≤ (M : ℝ) * c (Fin.castLE hm_le i) := by
    intro i
    have h : total' ≤ C * (M : ℝ) * c (Fin.castLE hm_le i) := h_balance i
    have h_total'_def : total' = C * total := by rfl
    rw [h_total'_def] at h
    have h' : total ≤ (M : ℝ) * c (Fin.castLE hm_le i) := by
      nlinarith
    exact h'
  have h_retention_simp : total ≤ ∑ i : Fin M, c (Fin.castLE hm_le i) := by
    have h : (C * total) / C ≤ ∑ i : Fin M, c (Fin.castLE hm_le i) := h_retention
    have h' : (C * total) / C = total := by
      field_simp [hC_pos.ne'] <;> ring
    rw [h'] at h
    exact h
  -- Define selection mapping back to original indices
  let select : Fin M → Fin N := fun i => σ (Fin.castLE hm_le i)
  have h_select_inj : Function.Injective select := by
    intro i j h
    have h1 : σ (Fin.castLE hm_le i) = σ (Fin.castLE hm_le j) := h
    have h2 : Fin.castLE hm_le i = Fin.castLE hm_le j := σ.injective h1
    have h3 : i = j := by
      exact Fin.ext (by simpa [Fin.ext_iff] using h2)
    exact h3
  have h1 : ∀ k : Fin M, c (Fin.castLE hm_le k) = cards (select k) := by
    intro k
    rfl
  have h_final_balance : ∀ k : Fin M, total ≤ (M : ℝ) * cards (select k) := by
    intro k
    rw [← h1 k]
    exact h_balance_simp k
  have h_final_sum : total ≤ ∑ k : Fin M, cards (select k) := by
    have h_eq : ∑ k : Fin M, cards (select k) = ∑ k : Fin M, c (Fin.castLE hm_le k) := by
      apply Finset.sum_congr rfl
      intro k _
      exact (h1 k).symm
    rw [h_eq]
    exact h_retention_simp
  exact ⟨M, hm_pos, select, h_select_inj, h_final_balance, h_final_sum⟩

end Kakeya.Assouad
