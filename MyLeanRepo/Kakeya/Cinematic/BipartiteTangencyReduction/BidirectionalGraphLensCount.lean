import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Lenses

/-!
# Combine the two directional graph-lens counts

The robust unit core partitions its rectangles between an upward and a
downward perturbation. This module converts the two Marcus--Tardos estimates
into one bound at the common bipartite normalized count.
-/

namespace Kakeya.Cinematic

private lemma log_card_succ_le_two_log
    {N : ℝ} (hN : 2 ≤ N) {n : ℕ} (hn : (n : ℝ) ≤ N) :
    Real.log ((n : ℝ) + 1) ≤ 2 * Real.log N := by
  have hN_sq : N + 1 ≤ N ^ 2 := by
    nlinarith
  have hn_sq : (n : ℝ) + 1 ≤ N ^ 2 := by
    linarith
  have hlog :
      Real.log ((n : ℝ) + 1) ≤ Real.log (N ^ 2) :=
    Real.log_le_log (by positivity) hn_sq
  rw [Real.log_pow] at hlog
  norm_num at hlog
  exact hlog

private lemma log_nat_succ_nonneg (n : ℕ) :
    0 ≤ Real.log ((n : ℝ) + 1) := by
  apply Real.log_nonneg
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

lemma bidirectional_graph_lens_count_bound
    {C C_mt N : ℝ} {n_up n_down m_up m_down : ℕ}
    (hC_mt_pos : 0 < C_mt)
    (hC_mt_le : 4 * C_mt ≤ C)
    (hN : 2 ≤ N)
    (hm_up : (m_up : ℝ) ≤ N)
    (hm_down : (m_down : ℝ) ≤ N)
    (h_up :
      (n_up : ℝ) ≤
        C_mt * Real.rpow (m_up : ℝ) (3 / 2 : ℝ) *
          Real.log ((m_up : ℝ) + 1))
    (h_down :
      (n_down : ℝ) ≤
        C_mt * Real.rpow (m_down : ℝ) (3 / 2 : ℝ) *
          Real.log ((m_down : ℝ) + 1)) :
    (n_up : ℝ) + (n_down : ℝ) ≤
      C * Real.rpow N (3 / 2 : ℝ) * Real.log N := by
  have h_rpow_up :
      Real.rpow (m_up : ℝ) (3 / 2 : ℝ) ≤
        Real.rpow N (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg m_up) hm_up (by norm_num)
  have h_rpow_down :
      Real.rpow (m_down : ℝ) (3 / 2 : ℝ) ≤
        Real.rpow N (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg m_down) hm_down (by norm_num)
  have h_log_up :
      Real.log ((m_up : ℝ) + 1) ≤ 2 * Real.log N :=
    log_card_succ_le_two_log hN hm_up
  have h_log_down :
      Real.log ((m_down : ℝ) + 1) ≤ 2 * Real.log N :=
    log_card_succ_le_two_log hN hm_down
  have h_rpow_nonneg :
      0 ≤ Real.rpow N (3 / 2 : ℝ) :=
    Real.rpow_nonneg (by linarith) _
  have h_log_nonneg : 0 ≤ Real.log N :=
    Real.log_nonneg (by linarith)
  have h_log_up_nonneg :
      0 ≤ Real.log ((m_up : ℝ) + 1) :=
    log_nat_succ_nonneg m_up
  have h_log_down_nonneg :
      0 ≤ Real.log ((m_down : ℝ) + 1) :=
    log_nat_succ_nonneg m_down
  have h_coefficient_nonneg :
      0 ≤ C_mt * Real.rpow N (3 / 2 : ℝ) :=
    mul_nonneg hC_mt_pos.le h_rpow_nonneg
  have h_up_common :
      C_mt * Real.rpow (m_up : ℝ) (3 / 2 : ℝ) *
          Real.log ((m_up : ℝ) + 1) ≤
        C_mt * Real.rpow N (3 / 2 : ℝ) *
          (2 * Real.log N) := by
    calc
      C_mt * Real.rpow (m_up : ℝ) (3 / 2 : ℝ) *
          Real.log ((m_up : ℝ) + 1) ≤
          C_mt * Real.rpow N (3 / 2 : ℝ) *
            Real.log ((m_up : ℝ) + 1) := by
        gcongr
      _ ≤ C_mt * Real.rpow N (3 / 2 : ℝ) *
          (2 * Real.log N) :=
        mul_le_mul_of_nonneg_left h_log_up h_coefficient_nonneg
  have h_down_common :
      C_mt * Real.rpow (m_down : ℝ) (3 / 2 : ℝ) *
          Real.log ((m_down : ℝ) + 1) ≤
        C_mt * Real.rpow N (3 / 2 : ℝ) *
          (2 * Real.log N) := by
    calc
      C_mt * Real.rpow (m_down : ℝ) (3 / 2 : ℝ) *
          Real.log ((m_down : ℝ) + 1) ≤
          C_mt * Real.rpow N (3 / 2 : ℝ) *
            Real.log ((m_down : ℝ) + 1) := by
        gcongr
      _ ≤ C_mt * Real.rpow N (3 / 2 : ℝ) *
          (2 * Real.log N) :=
        mul_le_mul_of_nonneg_left h_log_down h_coefficient_nonneg
  have h_sum :
      (n_up : ℝ) + (n_down : ℝ) ≤
        (4 * C_mt) * Real.rpow N (3 / 2 : ℝ) * Real.log N := by
    calc
      (n_up : ℝ) + (n_down : ℝ) ≤
          (C_mt * Real.rpow (m_up : ℝ) (3 / 2 : ℝ) *
              Real.log ((m_up : ℝ) + 1)) +
            (C_mt * Real.rpow (m_down : ℝ) (3 / 2 : ℝ) *
              Real.log ((m_down : ℝ) + 1)) :=
        add_le_add h_up h_down
      _ ≤
          (C_mt * Real.rpow N (3 / 2 : ℝ) *
              (2 * Real.log N)) +
            (C_mt * Real.rpow N (3 / 2 : ℝ) *
              (2 * Real.log N)) :=
        add_le_add h_up_common h_down_common
      _ = (4 * C_mt) * Real.rpow N (3 / 2 : ℝ) *
          Real.log N := by ring
  exact h_sum.trans <| by
    gcongr

end Kakeya.Cinematic
