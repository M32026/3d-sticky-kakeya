import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.IntersectionCounting
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.WeightOptimization
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.FinalAssembly
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

/-!
# Final theorem wiring for Marcus-Tardos Theorem 1

This module wires together the proved pieces (IntersectionCounting,
WeightOptimization, FinalAssembly) and derives the final bound
`d ≤ C * (√n * log(n+1) + n/√m)`, taking the combined inequality
from Lemmas 4+5 as an explicit assumption parameter.
-/

namespace MarcusTardos.TheoremWiring

open MarcusTardos WeightOptimization FinalAssembly

/-- `Real.log 2 > 1/2`. -/
lemma log2_gt_half : (1 / 2 : ℝ) < Real.log 2 := by
  have h : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  linarith

/-- `1 ≤ Real.log (n + 1) / Real.log 2` for `n > 0`. -/
lemma one_le_logn1_div_log2 (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) ≤ Real.log (n + 1) / Real.log 2 := by
  have h1 : (2 : ℝ) ≤ (n : ℝ) + 1 := by
    have h2 : n ≥ 1 := by omega
    have h3 : (n : ℝ) ≥ 1 := by exact_mod_cast h2
    linarith
  have h4 : Real.log 2 ≤ Real.log (n + 1) := Real.log_le_log (by norm_num) h1
  have h5 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (1 : ℝ) = Real.log 2 / Real.log 2 := by field_simp [h5.ne']
    _ ≤ Real.log (n + 1) / Real.log 2 := by
      exact div_le_div_of_nonneg_right h4 (by linarith)

/-- If `1 < b` and `0 < n`, then `(Nat.clog b n : ℝ) ≤ Real.log n / Real.log b + 1`. -/
lemma clog_le_log_plus_one {b n : ℕ} (hb : 1 < b) (hn : 0 < n) :
    (Nat.clog b n : ℝ) ≤ Real.log n / Real.log b + 1 := by
  by_cases h1 : n ≤ 1
  · have h2 : n = 1 := by omega
    rw [h2, Nat.clog_one_right]
    <;> simp [Real.log_one] <;> norm_num
  · have h2 : 1 < n := by omega
    set k : ℕ := Nat.clog b n with hk
    have hk_pos : 0 < k := Nat.clog_pos hb h2
    have h3 : b ^ (k - 1) < n := by
      have h4 : ¬k ≤ k - 1 := by omega
      have h5 : ¬n ≤ b ^ (k - 1) := by
        rwa [Nat.clog_le_iff_le_pow hb] at h4
      exact Nat.lt_of_not_ge h5
    have h6 : (b : ℝ) ^ (k - 1) < (n : ℝ) := by exact_mod_cast h3
    have h7 : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
    have h8 : Real.log ((b : ℝ) ^ (k - 1)) < Real.log (n : ℝ) :=
      Real.log_lt_log (by positivity) h6
    have h9 : Real.log ((b : ℝ) ^ (k - 1)) = (↑(k - 1) : ℝ) * Real.log b := by
      rw [Real.log_pow] <;> ring
    rw [h9] at h8
    have h10 : (↑(k - 1) : ℝ) = (k : ℝ) - 1 := Nat.cast_pred hk_pos
    rw [h10] at h8
    have h12 : ((k : ℝ) - 1) * Real.log b < Real.log (n : ℝ) := h8
    have h13 : ((k : ℝ) - 1) < Real.log (n : ℝ) / Real.log b := by
      have h14 : (((k : ℝ) - 1) * Real.log b) / Real.log b = (k : ℝ) - 1 := by
        field_simp [h7.ne'] <;> ring
      calc
        ((k : ℝ) - 1)
          = (((k : ℝ) - 1) * Real.log b) / Real.log b := h14.symm
        _ < (Real.log (n : ℝ)) / Real.log b := by gcongr
    linarith

/-- `k ≤ 4 * Real.log (n + 1)` when `d ≤ n` and `k = Nat.clog 2 d`. -/
lemma k_log_bound (d n : ℕ) (hdn : d ≤ n) :
    (Nat.clog 2 d : ℝ) ≤ 4 * Real.log (n + 1) := by
  by_cases hd : d = 0
  · rw [hd, Nat.clog_zero_right]
    have h_log : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by linarith)
    have h'' : (0 : ℝ) ≤ 4 * Real.log (n + 1) := by
      exact mul_nonneg (by norm_num) h_log
    exact_mod_cast h''
  · have hd' : 0 < d := by omega
    by_cases hn : n = 0
    · have : d = 0 := by omega
      contradiction
    · have hn' : 0 < n := by omega
      have h1 : (Nat.clog 2 d : ℝ) ≤ Real.log d / Real.log 2 + 1 :=
        clog_le_log_plus_one (by norm_num) hd'
      have h2 : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
      have h3 : Real.log d ≤ Real.log n := Real.log_le_log (by exact_mod_cast hd') h2
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h41 : Real.log d / Real.log 2 ≤ Real.log n / Real.log 2 := by gcongr
      have h4 : (Nat.clog 2 d : ℝ) ≤ Real.log n / Real.log 2 + 1 := by linarith [h1, h41]
      have h7 : (1 : ℝ) ≤ Real.log (n + 1) / Real.log 2 := one_le_logn1_div_log2 n hn'
      have h9 : Real.log n ≤ Real.log (n + 1) := Real.log_le_log (by positivity) (by linarith)
      have h10 : Real.log n / Real.log 2 ≤ Real.log (n + 1) / Real.log 2 := by gcongr
      have h11 : Real.log n / Real.log 2 + 1 ≤ 2 * Real.log (n + 1) / Real.log 2 := by
        calc
          Real.log n / Real.log 2 + 1
            ≤ Real.log (n + 1) / Real.log 2 + 1 := by gcongr
          _ ≤ Real.log (n + 1) / Real.log 2 + Real.log (n + 1) / Real.log 2 := by
            have h7' : (1 : ℝ) ≤ Real.log (n + 1) / Real.log 2 := h7
            linarith
          _ = 2 * Real.log (n + 1) / Real.log 2 := by ring
      have h13 : (2 : ℝ) / Real.log 2 ≤ 4 := by
        have h14 : (1 / 2 : ℝ) < Real.log 2 := log2_gt_half
        calc
          (2 : ℝ) / Real.log 2 ≤ (2 : ℝ) / (1 / 2 : ℝ) := by gcongr <;> linarith
          _ = 4 := by norm_num
      have h15 : (Nat.clog 2 d : ℝ) ≤ 2 * Real.log (n + 1) / Real.log 2 := by
        calc
          (Nat.clog 2 d : ℝ) ≤ Real.log n / Real.log 2 + 1 := h4
          _ ≤ 2 * Real.log (n + 1) / Real.log 2 := h11
      have h_log_nonneg : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by linarith)
      calc
        (Nat.clog 2 d : ℝ) ≤ 2 * Real.log (n + 1) / Real.log 2 := h15
        _ = ((2 : ℝ) / Real.log 2) * Real.log (n + 1) := by ring
        _ ≤ 4 * Real.log (n + 1) := by
          exact mul_le_mul_of_nonneg_right h13 h_log_nonneg

/-- The final bound, assuming the combined inequality from Lemmas 4+5. -/
theorem final_bound_with_combined
    {α : Type*} [DecidableEq α]
    {m d n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {alphabet : Finset α} (hcard : alphabet.card = n)
    {A : Fin m → List α}
    (hnodup : ∀ i, (A i).Nodup)
    (hlen : ∀ i, (A i).length = d)
    (halph : ∀ i, ∀ x ∈ A i, x ∈ alphabet)
    (k : ℕ) (hk : k = Nat.clog 2 d)
    (p : ℕ) (hp : p = totalIntersection A)
    (W V U : ℝ)
    (hW_def : W = ∑ l ∈ Finset.Icc 1 k, w k l)
    (hV_def : V = ∑ l ∈ Finset.Icc 1 k, 1 / w k l)
    (hU_def : U = ∑ l ∈ Finset.Icc 1 k, w k l / (2 : ℝ)^l)
    (h_combined : - (m : ℝ) * (d : ℝ)^2 * U ≤ (p : ℝ) * W - (p : ℝ)^2 / (12 * (m : ℝ)^2 * V)) :
    (d : ℝ) ≤ 64 * (Real.sqrt n * Real.log (n + 1) + (n : ℝ) / Real.sqrt m) := by
  let i0 : Fin m := ⟨0, hm⟩
  have hdn : d ≤ n := by
    have h1 : (A i0).Nodup := hnodup i0
    have h2 : (A i0).length = d := hlen i0
    have h3 : (A i0).toFinset ⊆ alphabet := by
      intro x hx
      exact halph i0 x (List.mem_toFinset.mp hx)
    have h4 : (A i0).toFinset.card = d := by
      rw [List.toFinset_card_of_nodup h1, h2]
    have h5 : (A i0).toFinset.card ≤ alphabet.card := Finset.card_le_card h3
    rw [h4, hcard] at h5
    exact h5

  -- Trivial case d ≤ 1
  by_cases hd1 : d ≤ 1
  · have h2 : (1 : ℝ) ≤ Real.sqrt n := by
      have h3 : (n : ℝ) ≥ 1 := by exact_mod_cast (show 1 ≤ n from by omega)
      have h4 : Real.sqrt 1 ≤ Real.sqrt n := Real.sqrt_le_sqrt h3
      have h5 : Real.sqrt 1 = 1 := by simp
      rw [h5] at h4
      exact h4
    have h_n1 : (2 : ℝ) ≤ (n : ℝ) + 1 := by
      have h : n ≥ 1 := by omega
      have h' : (n : ℝ) ≥ 1 := by exact_mod_cast h
      linarith
    have h3 : Real.log 2 ≤ Real.log (n + 1) := Real.log_le_log (by norm_num) h_n1
    have h4 : (1 : ℝ) ≤ 64 * Real.log 2 := by
      have h5 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      linarith
    have h6 : (1 : ℝ) ≤ 64 * (Real.sqrt n * Real.log (n + 1)) := by
      calc
        (1 : ℝ) ≤ 64 * Real.log 2 := h4
        _ ≤ 64 * (Real.sqrt n * Real.log (n + 1)) := by
          have h7 : Real.log 2 ≤ Real.sqrt n * Real.log (n + 1) := by
            calc
              Real.log 2 ≤ Real.log (n + 1) := h3
              _ ≤ Real.sqrt n * Real.log (n + 1) := by
                have h8 : (1 : ℝ) ≤ Real.sqrt n := h2
                have h9 : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by linarith)
                nlinarith
          gcongr
    have h7 : (d : ℝ) ≤ 1 := by exact_mod_cast hd1
    have h8 : 0 ≤ (n : ℝ) / Real.sqrt m := by positivity
    linarith

  have hd_gt1 : 1 < d := by omega
  have hd_pos : 0 < d := by omega

  -- Edge case d * m ≤ 2 * n
  by_cases h_edge : d * m ≤ 2 * n
  · have h_raw : (d : ℝ) ≤ 2 * (n : ℝ) / Real.sqrt m :=
      FinalAssembly.edge_case_bound (d : ℝ) (m : ℝ) (n : ℝ)
        (by exact_mod_cast (show 1 ≤ m from by omega))
        (by exact_mod_cast hn) (by positivity)
        (by exact_mod_cast h_edge)
    have h : (d : ℝ) ≤ 2 * ((n : ℝ) / Real.sqrt m) := by
      have h_eq : 2 * (n : ℝ) / Real.sqrt m = 2 * ((n : ℝ) / Real.sqrt m) := by ring
      rw [h_eq] at h_raw
      exact h_raw
    have h_pos2 : 0 ≤ (n : ℝ) / Real.sqrt m := by positivity
    have h_pos1 : 0 ≤ Real.sqrt n * Real.log (n + 1) := by
      apply mul_nonneg
      · exact Real.sqrt_nonneg n
      · exact Real.log_nonneg (by linarith)
    calc
      (d : ℝ) ≤ 2 * ((n : ℝ) / Real.sqrt m) := h
      _ ≤ 64 * ((n : ℝ) / Real.sqrt m) := by
        have h3 : (2 : ℝ) ≤ 64 := by norm_num
        exact mul_le_mul_of_nonneg_right h3 h_pos2
      _ ≤ 64 * (Real.sqrt n * Real.log (n + 1) + (n : ℝ) / Real.sqrt m) := by
        have h4 : 64 * ((n : ℝ) / Real.sqrt m) ≤
            64 * (Real.sqrt n * Real.log (n + 1) + (n : ℝ) / Real.sqrt m) := by
          gcongr
          <;> linarith
        exact h4

  -- Main case
  have h_main : d * m > 2 * n := by omega
  have hk_pos : 0 < k := by
    rw [hk]
    exact Nat.clog_pos (by norm_num) hd_gt1
  have hk_ge1 : 1 ≤ k := by omega
  have hk_nonempty : (Finset.Icc 1 k).Nonempty := ⟨1, by simp [hk_ge1]⟩

  have hW_pos : 0 < W := by
    rw [hW_def]
    exact Finset.sum_pos (fun l _ => w_pos k l) hk_nonempty

  have hV_pos : 0 < V := by
    rw [hV_def]
    exact Finset.sum_pos (fun l _ => by
      have h_wpos : 0 < w k l := w_pos k l
      have h : 0 < 1 / w k l := by positivity
      exact h) hk_nonempty

  have hU_nonneg : 0 ≤ U := by
    rw [hU_def]
    apply Finset.sum_nonneg
    intro l _
    have h_wpos : 0 < w k l := w_pos k l
    exact div_nonneg (by linarith) (by positivity)

  have hW_bound : W ≤ (k : ℝ) := by
    rw [hW_def]
    exact sum_w_bound k

  have hV_bound : V ≤ 4 * (k : ℝ) := by
    rw [hV_def]
    exact sum_inv_w_bound k

  have hU_bound : U ≤ 3 / (k : ℝ) := by
    rw [hU_def]
    exact sum_w_over_2l_bound k hk_pos

  have h_p_lower : (p : ℝ) ≥ (d : ℝ)^2 * (m : ℝ)^2 / (2 * (n : ℝ)) := by
    have h := totalIntersection_lower_bound hm hn hcard hnodup hlen halph h_main
    simpa [hp] using h

  have hp_pos : 0 < (p : ℝ) := by
    have h : (p : ℝ) ≥ (d : ℝ)^2 * (m : ℝ)^2 / (2 * (n : ℝ)) := h_p_lower
    have h' : 0 < (d : ℝ)^2 * (m : ℝ)^2 / (2 * (n : ℝ)) := by positivity
    linarith

  have h_dichotomy :=
    FinalAssembly.main_dichotomy (C := 12) (by norm_num) (d : ℝ) (m : ℝ) (p : ℝ) W V U
      (by exact_mod_cast hm) (by exact_mod_cast hd_pos) hp_pos
      hW_pos hV_pos hU_nonneg h_combined

  rcases h_dichotomy with (h_case1 | h_case2)

  · -- Case 1
    have h : (d : ℝ) ≤ 2 * Real.sqrt 12 * Real.sqrt ((n : ℝ) * W * V) :=
      FinalAssembly.case1_bound (C := 12) (by norm_num) (d : ℝ) (m : ℝ) (n : ℝ) (p : ℝ) W V
        (by exact_mod_cast hm) (by exact_mod_cast hn) (by exact_mod_cast hd_pos)
        hW_pos hV_pos h_case1 h_p_lower
    have h_sqrt12 : Real.sqrt 12 ≤ 4 := by
      rw [Real.sqrt_le_iff] <;> norm_num
    have h6 : (d : ℝ) ≤ 8 * Real.sqrt ((n : ℝ) * W * V) := by
      have h7 : 2 * Real.sqrt 12 ≤ 8 := by linarith [h_sqrt12]
      calc
        (d : ℝ) ≤ 2 * Real.sqrt 12 * Real.sqrt ((n : ℝ) * W * V) := h
        _ ≤ 8 * Real.sqrt ((n : ℝ) * W * V) := by gcongr
    have hWV : W * V ≤ 4 * (k : ℝ)^2 := by
      calc
        W * V ≤ W * (4 * (k : ℝ)) := by gcongr
        _ = 4 * W * (k : ℝ) := by ring
        _ ≤ 4 * (k : ℝ) * (k : ℝ) := by gcongr <;> linarith
        _ = 4 * (k : ℝ)^2 := by ring
    have h8 : (n : ℝ) * (W * V) ≤ (n : ℝ) * (4 * (k : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hWV (by positivity)
    have h8' : (n : ℝ) * W * V ≤ (n : ℝ) * (4 * (k : ℝ)^2) := by
      have h_assoc : (n : ℝ) * W * V = (n : ℝ) * (W * V) := by ring
      rw [h_assoc]
      exact h8
    have h9 : Real.sqrt ((n : ℝ) * W * V) ≤ Real.sqrt ((n : ℝ) * (4 * (k : ℝ)^2)) :=
      Real.sqrt_le_sqrt h8'
    have h10 : Real.sqrt ((n : ℝ) * (4 * (k : ℝ)^2)) = 2 * (k : ℝ) * Real.sqrt n := by
      have h11 : 0 ≤ (n : ℝ) := by positivity
      have h12 : 0 ≤ (k : ℝ) := by positivity
      have h13 : Real.sqrt ((n : ℝ) * (4 * (k : ℝ)^2)) =
          Real.sqrt (4 * (k : ℝ)^2) * Real.sqrt n := by
        have h_pos1 : 0 ≤ (n : ℝ) := by positivity
        have h14 : Real.sqrt ((n : ℝ) * (4 * (k : ℝ)^2)) =
            Real.sqrt n * Real.sqrt (4 * (k : ℝ)^2) := by
          rw [Real.sqrt_mul h_pos1]
        rw [h14, mul_comm]
      rw [h13]
      have h14 : Real.sqrt (4 * (k : ℝ)^2) = 2 * (k : ℝ) := by
        have h15 : 0 ≤ 2 * (k : ℝ) := by positivity
        rw [← Real.sqrt_sq h15] <;> ring_nf
      rw [h14] <;> ring
    have h7 : Real.sqrt ((n : ℝ) * W * V) ≤ 2 * (k : ℝ) * Real.sqrt n := by
      calc
        Real.sqrt ((n : ℝ) * W * V) ≤ Real.sqrt ((n : ℝ) * (4 * (k : ℝ)^2)) := h9
        _ = 2 * (k : ℝ) * Real.sqrt n := h10
    have h' : (d : ℝ) ≤ 16 * (k : ℝ) * Real.sqrt n := by
      calc
        (d : ℝ) ≤ 8 * Real.sqrt ((n : ℝ) * W * V) := h6
        _ ≤ 8 * (2 * (k : ℝ) * Real.sqrt n) := by gcongr
        _ = 16 * (k : ℝ) * Real.sqrt n := by ring
    have h_klog : (k : ℝ) ≤ 4 * Real.log (n + 1) := by
      rw [hk]
      exact k_log_bound d n hdn
    have h_pos1 : 0 ≤ Real.sqrt n * Real.log (n + 1) := by
      apply mul_nonneg
      · exact Real.sqrt_nonneg n
      · exact Real.log_nonneg (by linarith)
    have h_pos2 : 0 ≤ (n : ℝ) / Real.sqrt m := by positivity
    calc
      (d : ℝ) ≤ 16 * (k : ℝ) * Real.sqrt n := h'
      _ ≤ 16 * (4 * Real.log (n + 1)) * Real.sqrt n := by gcongr
      _ = 64 * (Real.sqrt n * Real.log (n + 1)) := by ring
      _ ≤ 64 * (Real.sqrt n * Real.log (n + 1) + (n : ℝ) / Real.sqrt m) := by
        gcongr <;> linarith

  · -- Case 2
    have h : (d : ℝ) ≤ Real.sqrt (8 * 12) * (n : ℝ) * Real.sqrt (U * V) / Real.sqrt m :=
      FinalAssembly.case2_bound (C := 12) (by norm_num) (d : ℝ) (m : ℝ) (n : ℝ) (p : ℝ) U V
        (by exact_mod_cast hm) (by exact_mod_cast hn) (by exact_mod_cast hd_pos)
        hU_nonneg hV_pos h_case2 h_p_lower
    have h_sqrt96 : Real.sqrt (8 * 12) = Real.sqrt 96 := by norm_num
    rw [h_sqrt96] at h
    have hUV : U * V ≤ 12 := by
      have h1 : U * V ≤ (3 / (k : ℝ)) * V := by gcongr
      have h2 : (3 / (k : ℝ)) * V ≤ (3 / (k : ℝ)) * (4 * (k : ℝ)) := by gcongr
      have h3 : (3 / (k : ℝ)) * (4 * (k : ℝ)) = 12 := by
        field_simp [hk_pos.ne'] <;> ring
      linarith
    have h_sqrt96_le : Real.sqrt 96 ≤ 10 := by
      rw [Real.sqrt_le_iff] <;> norm_num
    have h_sqrtUV_le : Real.sqrt (U * V) ≤ 4 := by
      have h4 : U * V ≤ 16 := by linarith
      have h5 : Real.sqrt (U * V) ≤ Real.sqrt 16 := Real.sqrt_le_sqrt h4
      have h6 : Real.sqrt 16 = 4 := by
        have h7 : (0 : ℝ) ≤ 4 := by norm_num
        rw [← Real.sqrt_sq h7] <;> norm_num
      rw [h6] at h5
      exact h5
    have h' : (d : ℝ) ≤ 40 * ((n : ℝ) / Real.sqrt m) := by
      calc
        (d : ℝ) ≤ Real.sqrt 96 * (n : ℝ) * Real.sqrt (U * V) / Real.sqrt m := h
        _ ≤ 10 * (n : ℝ) * 4 / Real.sqrt m := by gcongr
        _ = 40 * ((n : ℝ) / Real.sqrt m) := by ring
    have h_pos1 : 0 ≤ Real.sqrt n * Real.log (n + 1) := by
      apply mul_nonneg
      · exact Real.sqrt_nonneg n
      · exact Real.log_nonneg (by linarith)
    have h_pos2 : 0 ≤ (n : ℝ) / Real.sqrt m := by positivity
    calc
      (d : ℝ) ≤ 40 * ((n : ℝ) / Real.sqrt m) := h'
      _ ≤ 64 * ((n : ℝ) / Real.sqrt m) := by
        have h6 : (40 : ℝ) ≤ 64 := by norm_num
        exact mul_le_mul_of_nonneg_right h6 h_pos2
      _ ≤ 64 * (Real.sqrt n * Real.log (n + 1) + (n : ℝ) / Real.sqrt m) := by
        gcongr <;> linarith

end MarcusTardos.TheoremWiring
