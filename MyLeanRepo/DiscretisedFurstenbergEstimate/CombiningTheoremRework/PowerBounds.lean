module

/-
  Reusable Power Bounds

  Absorb constants and polynomial-in-n factors into dyadic power bounds δ_n^{-loss}.

  - constant_absorption: C ≤ δ^{-loss} for fixed C > 0
  - polynomial7_absorption: C * (4n+7)^7 ≤ δ_n^{-loss}
  - K_global_absorption: specialization for K_global
  - CQ_absorption: specialization for CQ

  Whiteprint node: combining_theorem_rework / power_bounds
  Status: IMPLEMENTED
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.ExponentLedgerClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Section6

/-! ========================================================================
   Basic constant absorption
   ======================================================================== -/

/-- Absorb a fixed constant C into δ^{-loss}. -/
lemma constant_absorption (C loss : ℝ) (hC_pos : 0 < C) (hloss_pos : 0 < loss) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ, 0 < δ → δ < δ0 → C ≤ δ ^ (-loss) := by
  let δ0 : ℝ := C ^ (-1 / loss)
  have hδ0_pos : 0 < δ0 := by positivity
  have hδ0_pow : δ0 ^ (-loss) = C := by
    have h3 : δ0 ^ (-loss) = (C ^ (-1 / loss)) ^ (-loss) := by rfl
    rw [h3]
    have h4 : (C ^ (-1 / loss)) ^ (-loss) = C ^ ((-1 / loss) * (-loss)) := by
      rw [←Real.rpow_mul] <;> positivity
    rw [h4]
    have h5 : (-1 / loss) * (-loss) = 1 := by
      field_simp [hloss_pos.ne'] <;> ring
    rw [h5]
    have h6 : C ^ (1 : ℝ) = C := by simp
    exact h6
  refine ⟨δ0, hδ0_pos, fun δ hδ_pos hδ_lt => ?_⟩
  have h1 : δ ^ (-loss) > δ0 ^ (-loss) := by
    have h2 : -loss < 0 := by linarith
    have h_strict := Real.strictAntiOn_rpow_Ioi_of_exponent_neg h2
    exact h_strict hδ_pos hδ0_pos hδ_lt
  rw [hδ0_pow] at h1
  exact h1.le

/-- Product of two power bounds. -/
lemma product_power_bound {δ lossA lossB A B : ℝ} (hδ_pos : 0 < δ)
    (hA : A ≤ δ ^ (-lossA)) (hB : B ≤ δ ^ (-lossB))
    (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B) :
    A * B ≤ δ ^ (-(lossA + lossB)) := by
  calc A * B
    ≤ δ ^ (-lossA) * δ ^ (-lossB) := by gcongr
  _ = δ ^ (-lossA + -lossB) := by rw [←Real.rpow_add hδ_pos] <;> ring
  _ = δ ^ (-(lossA + lossB)) := by ring_nf

/-! ========================================================================
   Polynomial (4n+7)^7 absorption into dyadic power bounds
   ======================================================================== -/

private lemma n_to_log_bound (n : ℕ) (hn_pos : 0 < n) :
    (4 * (n : ℝ) + 7) ≤ (11 / Real.log 2) * Real.log (1 / dyadicDelta n) := by
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn_pos
  have h2 : (4 * (n : ℝ) + 7) ≤ 11 * (n : ℝ) := by nlinarith
  have h_log_eq : Real.log (1 / dyadicDelta n) = (n : ℝ) * Real.log 2 := by
    have h4 : dyadicDelta n = (1 / 2 : ℝ) ^ n := by simp [dyadicDelta] <;> ring
    rw [h4]
    have h5 : (1 / ((1 / 2 : ℝ) ^ n)) = (2 : ℝ) ^ n := by
      have h6 : (1 / 2 : ℝ) ^ n * (2 : ℝ) ^ n = 1 := by
        have h7 : (1 / 2 : ℝ) ^ n * (2 : ℝ) ^ n = ((1 / 2 : ℝ) * (2 : ℝ)) ^ n := by rw [←mul_pow]
        rw [h7]
        have h8 : (1 / 2 : ℝ) * (2 : ℝ) = 1 := by norm_num
        rw [h8, one_pow]
      have h9 : (1 / 2 : ℝ) ^ n ≠ 0 := by positivity
      have h10 : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by rw [mul_comm, h6]
      exact ((eq_div_iff h9).mpr h10).symm
    rw [h5, Real.log_pow] <;> norm_num
  calc (4 * (n : ℝ) + 7)
    ≤ 11 * (n : ℝ) := h2
  _ = (11 / Real.log 2) * Real.log (1 / dyadicDelta n) := by
    rw [h_log_eq] <;> field_simp [h_log2_pos.ne'] <;> ring

/-- Absorb C * (4n+7)^7 into δ_n^{-loss}. -/
lemma polynomial7_absorption
    (C loss : ℝ) (hC_pos : 0 < C) (hloss_pos : 0 < loss) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ (n : ℕ), 0 < n → dyadicDelta n < δ0 →
      ∀ (X : ℝ), X ≤ C * (4 * (n : ℝ) + 7)^7 →
        X ≤ (dyadicDelta n)^(-loss) := by
  let C_log : ℝ := 11 / Real.log 2
  let C_K : ℝ := C * C_log ^ (7 : ℝ)
  have hC_K_pos : 0 < C_K := by positivity
  rcases absorb_polylog_upper C_K 7 loss hC_K_pos (by norm_num) hloss_pos with
    ⟨δ0, hδ0_pos, h_abs⟩
  refine ⟨δ0, hδ0_pos, fun n hn_pos hδn_lt X hX_bound => ?_⟩
  have h1 := n_to_log_bound n hn_pos
  have h3 : X ≤ C_K * (Real.log (1 / dyadicDelta n))^(7 : ℝ) := by
    calc X
      ≤ C * (4 * (n : ℝ) + 7)^7 := hX_bound
    _ = C * (4 * (n : ℝ) + 7)^(7 : ℝ) := by norm_cast
    _ ≤ C * (C_log * Real.log (1 / dyadicDelta n))^(7 : ℝ) := by gcongr
    _ = C_K * (Real.log (1 / dyadicDelta n))^(7 : ℝ) := by
      dsimp only [C_K]
      have h_expand : (C_log * Real.log (1 / dyadicDelta n))^(7 : ℝ) =
          C_log^(7 : ℝ) * (Real.log (1 / dyadicDelta n))^(7 : ℝ) := by
        simp [Real.mul_rpow] <;> ring
      rw [h_expand] <;> ring
  have h4 : C_K * (Real.log (1 / dyadicDelta n))^(7 : ℝ) ≤ (dyadicDelta n)^(-loss) :=
    h_abs (dyadicDelta n) (dyadicDelta_pos n) hδn_lt
  exact le_trans h3 h4

/-- Absorb K_global into δ_n^{-loss_global}. -/
lemma K_global_absorption
    (C loss_global : ℝ) (hC_pos : 0 < C) (hloss_pos : 0 < loss_global) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ (n : ℕ), 0 < n → dyadicDelta n < δ0 →
      ∀ (K_global : ℝ), K_global ≤ C * (4 * (n : ℝ) + 7)^7 →
        K_global ≤ (dyadicDelta n)^(-loss_global) :=
  polynomial7_absorption C loss_global hC_pos hloss_pos

/-- Absorb CQ into δ_n^{-b}. -/
lemma CQ_absorption
    (C b : ℝ) (hC_pos : 0 < C) (hb_pos : 0 < b) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ (n : ℕ), 0 < n → dyadicDelta n < δ0 →
      ∀ (CQ : ℝ), CQ ≤ C * (4 * (n : ℝ) + 7)^7 →
        CQ ≤ (dyadicDelta n)^(-b) :=
  polynomial7_absorption C b hC_pos hb_pos

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
