module

/-
  FineAbsorptionHelpers.lean

  Elementary real-arithmetic helpers for the fine polynomial absorption
  block in CombiningInductionWithBound.

  Provides:
  - `real_rpow_nonneg`: non-negativity of real powers
  - `uniformisation_power_nonneg`: non-negativity of uniformisation power
  - `cancel_positive_rpow`: positive rpow denominator cancellation
  - `combine_equal_rpows`: multiplicative distribution of real powers

  Dependencies: none beyond Mathlib
-/

public import MyLeanRepo.OSWPrelude
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem

@[expose] public section

open scoped ENNReal NNReal

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure

/-- Cast `j.val + 1` from `Fin (n-1)` to `Fin n` when `n ≥ 2`.
    Used to avoid `⟨j.val + 1, by omega⟩` in large theorem types. -/
def finSuccN {n : ℕ} (hn : 2 ≤ n) (j : Fin (n - 1)) : Fin n :=
  ⟨j.val + 1, by omega⟩

/-- The Δ-access index corresponding to `finSuccN`, cast to `Fin (n+1)`. -/
def finCast1N {n : ℕ} (hn : 2 ≤ n) (j : Fin (n - 1)) : Fin (n + 1) :=
  Fin.castSucc (finSuccN hn j)

/-- The second Δ-access index: `Fin.succ` of `finSuccN`. -/
def finSucc2N {n : ℕ} (hn : 2 ≤ n) (j : Fin (n - 1)) : Fin (n + 1) :=
  Fin.succ (finSuccN hn j)

/-- Non-negativity of real powers: `0 ≤ L^C` when `0 ≤ L`. -/
lemma real_rpow_nonneg (L C : ℝ)
    (hL : 0 ≤ L) :
    0 ≤ L ^ C := by
  exact Real.rpow_nonneg hL C

/-- Non-negativity of uniformisation power: `0 ≤ (24*L/q)^d` when `0 ≤ L`. -/
lemma uniformisation_power_nonneg
    (L : ℝ) (q d : ℕ)
    (hL : 0 ≤ L) :
    0 ≤ (24 * L / (q : ℝ)) ^ d := by
  positivity

/-- Positive rpow denominator cancellation: `(B / A^r) * A^r * X = B * X` when `0 < A`. -/
lemma cancel_positive_rpow
    (B A X r : ℝ)
    (hA : 0 < A) :
    (B / A ^ r) * A ^ r * X = B * X := by
  have hpow : A ^ r ≠ 0 := (Real.rpow_pos_of_pos hA r).ne'
  field_simp [hpow]

/-- Multiplicative distribution of real powers: `A^r * k^r = (A*k)^r`
    when `0 ≤ A` and `0 ≤ k`. -/
lemma combine_equal_rpows
    (A k r : ℝ)
    (hA : 0 ≤ A)
    (hk : 0 ≤ k) :
    A ^ r * k ^ r = (A * k) ^ r := by
  exact (Real.mul_rpow hA hk).symm

/-- Mixed-degree identity: `x^7 * x^(n-1) * x^C = x^(n+6+C)` for `x > 0`, `n ≥ 2`.
    Combines natural and real exponents using `rpow_add`. -/
lemma mixed_degree_identity
    (x C : ℝ) (n : ℕ)
    (hx : 0 < x)
    (hn : 2 ≤ n) :
    x ^ 7 * x ^ (n - 1) * x ^ C = x ^ (n + 6 + C) := by
  rw [← Real.rpow_natCast x 7, ← Real.rpow_natCast x (n - 1)]
  rw [← Real.rpow_add hx, ← Real.rpow_add hx]
  congr 1
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  ring

/-- Real power with natural subtraction: `x^(r - q) = x^r / x^q` for `x > 0`. -/
lemma rpow_sub_nat
    (x r : ℝ) (q : ℕ)
    (hx : 0 < x) :
    x ^ (r - q) = x ^ r / x ^ q := by
  rw [Real.rpow_sub hx, Real.rpow_natCast]

/-- Absorb a natural-degree factor: if `A ≤ x^q`, then
    `A * B * x^(r - q) ≤ B * x^r` for `x > 0`, `B ≥ 0`. -/
lemma absorb_natural_degree
    (A B x r : ℝ) (q : ℕ)
    (hx : 0 < x)
    (hB : 0 ≤ B)
    (hA : A ≤ x ^ q) :
    A * B * x ^ (r - q) ≤ B * x ^ r := by
  rw [rpow_sub_nat x r q hx]
  have hq : 0 < x ^ q := pow_pos hx q
  have hr : 0 ≤ x ^ r := Real.rpow_nonneg hx.le r
  calc
    A * B * (x ^ r / x ^ q) = (B * x ^ r) * (A / x ^ q) := by
      field_simp [hq.ne'] <;> ring
    _ ≤ (B * x ^ r) * 1 := by
      gcongr
      exact (div_le_one hq).2 hA
    _ = B * x ^ r := by ring

/-- Spare degree equality: `n + 6 + C_P = (C_P + 2*C_n) - (n + 2)`
    when `C_n = n + 4`. -/
lemma spare_degree_equality (C_P : ℝ) (n : ℕ) (C_n : ℝ)
    (hCn : C_n = (n : ℝ) + 4) :
    (n : ℝ) + 6 + C_P = (C_P + 2 * C_n) - ((n : ℝ) + 2) := by
  rw [hCn] <;> ring

/-- Fine spare degree equality: `n + 6 + C_P = (C_P + 2*(n+4)) - (n+2)`.
    Operator-verified standalone version for direct `simpa` use. -/
lemma fine_spare_degree (C_P : ℝ) (n : ℕ) :
    (n : ℝ) + 6 + C_P = (C_P + 2 * ((n : ℝ) + 4)) - ((n : ℝ) + 2) := by
  ring

/-- Isolated h_main2 absorption: polynomial factor absorbed into k^(n+2).
    All parameters are explicit (no let-bindings) to avoid whnf hangs. -/
lemma fine_main2_absorption
    (C_fine_total C_P_fine C_P τ log2 k : ℝ)
    (n : ℕ)
    (h_k_pos : 0 < k)
    (h_C_pos : 0 ≤ (τ * log2)^C_P_fine)
    (h_fine_poly : C_fine_total ≤ k^(n + 2))
    (h_deg : (n : ℝ) + 6 + C_P = C_P_fine - ((n : ℝ) + 2)) :
    C_fine_total * (τ * log2)^C_P_fine * k^((n : ℝ) + 6 + C_P) ≤
    (τ * log2)^C_P_fine * k^C_P_fine := by
  have h_cast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by
    rw [Nat.cast_add] <;> norm_num
  have h_deg' : (n : ℝ) + 6 + C_P = C_P_fine - ↑(n + 2) := by
    convert h_deg using 2
    <;> rw [h_cast]
  rw [h_deg']
  exact absorb_natural_degree C_fine_total ((τ * log2)^C_P_fine) k C_P_fine (n + 2) h_k_pos h_C_pos h_fine_poly

/-- C_fine_total cancellation identity: `C_fine_total * (τ*log2)^C_P_fine = constant`.
    Takes the definition of C_fine_total and C_P_fine equality as explicit hypotheses. -/
lemma fine_C_cancel
    (C_fine_total C_P C_n C_P_fine τ : ℝ)
    (n : ℕ) (hn : 2 ≤ n)
    (hτ : 0 < τ) (hlog2_pos : 0 < Real.log 2)
    (hC_fine_total_def : C_fine_total =
        (18 : ℝ) * (2700 * 3145728 * (11 : ℝ)^7) *
        ((24 : ℝ) / (n - 1 : ℝ))^(n - 1) * (4 : ℝ)^(n - 1) /
        (τ * Real.log 2)^(C_P + 2 * C_n))
    (hCP_fine_eq : C_P_fine = C_P + 2 * C_n) :
    C_fine_total * (τ * Real.log 2)^C_P_fine =
        18 * (2700 * 3145728 * (11 : ℝ)^7) *
        (((24 : ℝ) / ((n - 1 : ℕ) : ℝ))^(n - 1)) * (4 : ℝ)^(n - 1) := by
  have h1 : 1 ≤ n := by omega
  have h_cast : (n - 1 : ℝ) = ((n - 1 : ℕ) : ℝ) := by
    have h2 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub h1] <;> simp
    exact h2.symm
  have h_eq2 : (τ * Real.log 2)^C_P_fine = (τ * Real.log 2)^(C_P + 2 * C_n) := by
    rw [hCP_fine_eq]
  have hτlog_pos : 0 < τ * Real.log 2 := mul_pos hτ hlog2_pos
  have hpos : (τ * Real.log 2)^(C_P + 2 * C_n) ≠ 0 := (Real.rpow_pos_of_pos hτlog_pos _).ne'
  calc
    C_fine_total * (τ * Real.log 2)^C_P_fine
      = C_fine_total * (τ * Real.log 2)^(C_P + 2 * C_n) := by rw [h_eq2]
    _ = ((18 : ℝ) * (2700 * 3145728 * (11 : ℝ)^7) *
          ((24 : ℝ) / (n - 1 : ℝ))^(n - 1) * (4 : ℝ)^(n - 1) /
          (τ * Real.log 2)^(C_P + 2 * C_n)) *
        (τ * Real.log 2)^(C_P + 2 * C_n) := by rw [hC_fine_total_def]
    _ = (18 : ℝ) * (2700 * 3145728 * (11 : ℝ)^7) *
          ((24 : ℝ) / (n - 1 : ℝ))^(n - 1) * (4 : ℝ)^(n - 1) := by
      field_simp [hpos] <;> ring
    _ = 18 * (2700 * 3145728 * (11 : ℝ)^7) *
          (((24 : ℝ) / ((n - 1 : ℕ) : ℝ))^(n - 1)) * (4 : ℝ)^(n - 1) := by
      rw [h_cast] <;> ring

/-- Full scalar fine absorption: polynomial domination + C_between combination.
    All geometry/config/Fin-index work stays in the caller.
    Every variable is an explicit parameter (no let-bindings in type). -/
lemma fine_scalar_absorption
    (n : ℕ) (hn : 2 ≤ n)
    (k : ℕ) (hk_ge_one : (1 : ℝ) ≤ (k : ℝ))
    (τ : ℝ) (hτ : 0 < τ)
    (C_P C_P_fine : ℝ)
    (hCP : 0 < C_P) (hCP_fine : 1 ≤ C_P_fine)
    (hlog2_pos : 0 < Real.log 2)
    (L_fine L_k_fine C_fine_total : ℝ)
    (hL_fine_nonneg : 0 ≤ L_fine)
    (hLk_nonneg : 0 ≤ L_k_fine)
    (hLk_eq : L_k_fine = (k : ℝ) * Real.log 2)
    (hLk_le_k : L_k_fine ≤ (k : ℝ))
    (hL_le_k : L_fine ≤ (k : ℝ))
    (hL_ge : L_fine ≥ τ * L_k_fine)
    (h_fine_poly : C_fine_total ≤ (k : ℝ)^(n + 2))
    (hC_cancel : C_fine_total * (τ * Real.log 2)^C_P_fine =
        18 * (2700 * 3145728 * (11 : ℝ)^7) *
        (((24 : ℝ) / ((n - 1 : ℕ) : ℝ))^(n - 1)) * (4 : ℝ)^(n - 1))
    (h_deg : (n : ℝ) + 6 + C_P = C_P_fine - ((n : ℝ) + 2))
    (C_between_val : ℝ)
    (K : ℝ) (hK_ge1 : 1 ≤ K)
    (hK_bound : K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7)
    (ratio : ℝ) (ratio_pos : 0 < ratio)
    (ε : ℝ) (hε_pos : 0 < ε)
    (hCb : C_between_val ≤ L_k_fine ^ C_P * ratio ^ ε) :
    9 * C_between_val * 2 * K *
      (24 * L_fine / ((n - 1 : ℕ) : ℝ)) ^ (n - 1) * (4 : ℝ) ^ (n - 1) ≤
    L_fine ^ C_P_fine * ratio ^ ε := by
  have hK_poly : K ≤ 2700 * 3145728 * (11 * (k : ℝ))^7 := by
    have h : 4 * (k : ℝ) + 7 ≤ 11 * (k : ℝ) := by linarith [hk_ge_one]
    calc K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 := hK_bound
      _ ≤ 2700 * 3145728 * (11 * (k : ℝ))^7 := by gcongr
  have h_pos1 : 0 < τ * Real.log 2 := mul_pos hτ hlog2_pos
  have h_Lk_rpow_nonneg : 0 ≤ L_k_fine ^ C_P :=
    real_rpow_nonneg L_k_fine C_P hLk_nonneg
  have h_uniform_nonneg : 0 ≤ (24 * L_fine / ((n - 1 : ℕ) : ℝ))^(n - 1) :=
    uniformisation_power_nonneg L_fine (n - 1) (n - 1) hL_fine_nonneg
  have h_main1 : 18 * K * (24 * L_fine / ((n - 1 : ℕ) : ℝ))^(n - 1) * (4 : ℝ)^(n - 1) * L_k_fine ^ C_P ≤
      C_fine_total * (τ * Real.log 2)^C_P_fine * (k : ℝ)^(n + 6 + C_P) := by
    have hK7 : K ≤ 2700 * 3145728 * (11 : ℝ)^7 * (k : ℝ)^7 := by
      calc K ≤ 2700 * 3145728 * (11 * (k : ℝ))^7 := hK_poly
        _ = 2700 * 3145728 * (11 : ℝ)^7 * (k : ℝ)^7 := by ring
    have hL_pow : (24 * L_fine / ((n - 1 : ℕ) : ℝ))^(n - 1) ≤
        ((24 : ℝ) / ((n - 1 : ℕ) : ℝ))^(n - 1) * (k : ℝ)^(n - 1) := by
      let c := (24 : ℝ) / ((n - 1 : ℕ) : ℝ)
      have hc_nonneg : 0 ≤ c := by positivity
      have h_eq : 24 * L_fine / ((n - 1 : ℕ) : ℝ) = c * L_fine := by ring
      rw [h_eq]
      have h4 : c * L_fine ≤ c * (k : ℝ) := mul_le_mul_of_nonneg_left hL_le_k hc_nonneg
      have h5 : (c * L_fine)^(n - 1) ≤ (c * (k : ℝ))^(n - 1) := by gcongr
      have h6 : (c * (k : ℝ))^(n - 1) = c^(n - 1) * (k : ℝ)^(n - 1) := by rw [mul_pow]
      rw [h6] at h5
      exact h5
    have hLk_C_P : L_k_fine ^ C_P ≤ (k : ℝ) ^ C_P := by
      exact Real.rpow_le_rpow hLk_nonneg hLk_le_k (by linarith [hCP])
    have h_k_pow : (k : ℝ)^7 * (k : ℝ)^(n - 1) * (k : ℝ)^C_P = (k : ℝ)^(n + 6 + C_P) :=
      mixed_degree_identity (k : ℝ) C_P n (by linarith [hk_ge_one]) (by omega)
    calc 18 * K * (24 * L_fine / ((n - 1 : ℕ) : ℝ))^(n - 1) * (4 : ℝ)^(n - 1) * L_k_fine ^ C_P
      ≤ 18 * (2700 * 3145728 * (11 : ℝ)^7 * (k : ℝ)^7) *
          (((24 : ℝ) / ((n - 1 : ℕ) : ℝ))^(n - 1) * (k : ℝ)^(n - 1)) *
          (4 : ℝ)^(n - 1) * ((k : ℝ) ^ C_P) := by gcongr
      _ = (18 * (2700 * 3145728 * (11 : ℝ)^7) *
          (((24 : ℝ) / ((n - 1 : ℕ) : ℝ))^(n - 1)) * (4 : ℝ)^(n - 1)) *
          ((k : ℝ)^7 * (k : ℝ)^(n - 1) * (k : ℝ)^C_P) := by ring
      _ = (18 * (2700 * 3145728 * (11 : ℝ)^7) *
          (((24 : ℝ) / ((n - 1 : ℕ) : ℝ))^(n - 1)) * (4 : ℝ)^(n - 1)) * (k : ℝ)^(n + 6 + C_P) := by rw [h_k_pow]
      _ = C_fine_total * (τ * Real.log 2)^C_P_fine * (k : ℝ)^(n + 6 + C_P) := by rw [hC_cancel] <;> rfl
  have h_main2 : C_fine_total * (τ * Real.log 2)^C_P_fine * (k : ℝ)^(n + 6 + C_P) ≤
      (τ * Real.log 2)^C_P_fine * (k : ℝ)^C_P_fine := by
    have h_k_pos : 0 < (k : ℝ) := by linarith [hk_ge_one]
    have h_C_pos : 0 ≤ (τ * Real.log 2)^C_P_fine := by positivity
    exact fine_main2_absorption
      C_fine_total C_P_fine C_P τ (Real.log 2) (k : ℝ) n
      h_k_pos h_C_pos h_fine_poly h_deg
  have h_main3 : (τ * Real.log 2)^C_P_fine * (k : ℝ)^C_P_fine ≤ L_fine ^ C_P_fine := by
    have h11 : τ * Real.log 2 * (k : ℝ) ≤ L_fine := by
      have h12 : L_fine ≥ τ * L_k_fine := hL_ge
      rw [hLk_eq] at h12
      have h14 : τ * ((k : ℝ) * Real.log 2) = τ * Real.log 2 * (k : ℝ) := by ring
      rw [h14] at h12
      exact h12
    have hA : 0 ≤ τ * Real.log 2 := by positivity
    have hk' : 0 ≤ (k : ℝ) := by linarith [hk_ge_one]
    have h_combine : (τ * Real.log 2)^C_P_fine * (k : ℝ)^C_P_fine = (τ * Real.log 2 * (k : ℝ))^C_P_fine :=
      combine_equal_rpows (τ * Real.log 2) (k : ℝ) C_P_fine hA hk'
    rw [h_combine]
    have hpos : 0 ≤ τ * Real.log 2 * (k : ℝ) := by positivity
    exact Real.rpow_le_rpow hpos h11 (by linarith [hCP_fine])
  have h_main : 18 * K * (24 * L_fine / ((n - 1 : ℕ) : ℝ))^(n - 1) * (4 : ℝ)^(n - 1) * L_k_fine ^ C_P ≤ L_fine ^ C_P_fine :=
    le_trans h_main1 (le_trans h_main2 h_main3)
  have h_eps_nonneg : 0 ≤ ratio ^ ε := by positivity
  have h_mult_nonneg : 0 ≤ 18 * K * (24 * L_fine / ((n - 1 : ℕ) : ℝ))^(n - 1) * (4 : ℝ)^(n - 1) := by positivity
  calc 9 * C_between_val * 2 * K *
      (24 * L_fine / ((n - 1 : ℕ) : ℝ)) ^ (n - 1) * (4 : ℝ) ^ (n - 1)
    = 18 * K * (24 * L_fine / ((n - 1 : ℕ) : ℝ))^(n - 1) * (4 : ℝ)^(n - 1) * C_between_val := by ring
    _ ≤ 18 * K * (24 * L_fine / ((n - 1 : ℕ) : ℝ))^(n - 1) * (4 : ℝ)^(n - 1) *
        (L_k_fine ^ C_P * ratio ^ ε) := by
      exact mul_le_mul_of_nonneg_left hCb h_mult_nonneg
    _ = (18 * K * (24 * L_fine / ((n - 1 : ℕ) : ℝ))^(n - 1) * (4 : ℝ)^(n - 1) * L_k_fine ^ C_P) *
        ratio ^ ε := by ring
    _ ≤ L_fine ^ C_P_fine * ratio ^ ε := by
      exact mul_le_mul_of_nonneg_right h_main h_eps_nonneg

/-- Good-case adapter: takes h_fine_absorb_core and h_C_between_good as explicit
    parameters, avoiding any let-binding-heavy local type in CIBW. -/
lemma fine_good_adapter
    (n : ℕ) (hn : 2 ≤ n)
    (k : ℕ)
    (C_P C_P_fine L_fine L_k_fine : ℝ)
    (C_between : Fin n → ℝ)
    (Δ : Fin (n + 1) → ℝ)
    (scaleClass : Fin n → CombiningTheorem.ScaleClass)
    (ε_G : ℝ) (hεG : 0 < ε_G)
    (h_fine_absorb_core : ∀ (ε : ℝ), 0 < ε → ∀ (j : Fin (n - 1)),
        (C_between ⟨j.val + 1, by omega⟩ ≤ L_k_fine ^ C_P *
          (Δ ⟨j.val + 1, by omega⟩ / Δ ⟨j.val + 2, by omega⟩) ^ ε) →
        ∀ (K : ℝ), 1 ≤ K → K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 →
        scaleClass ⟨j.val + 1, by omega⟩ ≠ CombiningTheorem.ScaleClass.bad →
        9 * (C_between ⟨j.val + 1, by omega⟩) * 2 * K *
          (24 * L_fine / ((n - 1 : ℕ) : ℝ)) ^ (n - 1) * (4 : ℝ) ^ (n - 1) ≤
        L_fine ^ C_P_fine * (Δ ⟨j.val + 1, by omega⟩ / Δ ⟨j.val + 2, by omega⟩) ^ ε)
    (h_C_between_good : ∀ (j : Fin n) (t_j : ℝ),
        scaleClass j = CombiningTheorem.ScaleClass.good t_j →
        C_between j ≤ L_k_fine ^ C_P * (Δ (Fin.castSucc j) / Δ (Fin.succ j)) ^ ε_G)
    :
    ∀ (K : ℝ), 1 ≤ K → K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 →
    ∀ (j : Fin (n - 1)) (t_j : ℝ),
      scaleClass ⟨j.val + 1, by omega⟩ = CombiningTheorem.ScaleClass.good t_j →
      9 * (C_between ⟨j.val + 1, by omega⟩) * 2 * K *
        (24 * L_fine / ((n - 1 : ℕ) : ℝ)) ^ (n - 1) * (4 : ℝ) ^ (n - 1) ≤
      L_fine ^ C_P_fine * (Δ ⟨j.val + 1, by omega⟩ / Δ ⟨j.val + 2, by omega⟩) ^ ε_G := by
  intro K hK_ge1 hK_bound j t_j hj
  let idx : Fin n := ⟨j.val + 1, by omega⟩
  let idx2 : Fin (n + 1) := ⟨j.val + 2, by omega⟩
  have h_idx2_succ : idx2 = Fin.succ idx := by
    apply Fin.ext <;> simp [idx, idx2] <;> omega
  have hCb : C_between idx ≤ L_k_fine ^ C_P * (Δ (Fin.castSucc idx) / Δ idx2) ^ ε_G := by
    have h := h_C_between_good idx t_j hj
    simpa [h_idx2_succ] using h
  have h_nonbad : scaleClass idx ≠ CombiningTheorem.ScaleClass.bad := by
    rw [hj]; simp
  exact h_fine_absorb_core ε_G hεG j hCb K hK_ge1 hK_bound h_nonbad


end DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure
