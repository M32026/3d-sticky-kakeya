module

public import MyLeanRepo.OSWPrelude
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CommonTubeEnergyExtraction

@[expose] public section

set_option maxHeartbeats 500000

/-!
# Quantitative thick-tube cover

This is the combinatorial-geometric content of OS Proposition 4.1. Fine
objects are assigned to a fixed separated net at the coarse scale `Δ`.

The important clauses are the two-sided average relation for `H`, the
polylogarithmic bound for `K`, and the bound for `C₂`.  Without those clauses a
singleton coarse family would satisfy the qualitative conclusion but would be
useless in the induction on scales.

The finite delta-set hypotheses below are cardinal Frostman estimates, as in
OS. They are deliberately not phrased only in terms of same-scale covering
numbers. In a general metric space, a `δ`-separated set can contain arbitrarily
many points in one closed `δ`-ball, so same-scale covering regularity alone
does not imply this theorem.
-/

noncomputable section

open scoped ENNReal NNReal

-- ============================================================================
-- Definitions (exact copies from target file)
-- ============================================================================

def IsFiniteDeltaSSet {X : Type*} [PseudoMetricSpace X]
    (δ s C : ℝ) (P : Finset X) : Prop :=
  P.Nonempty ∧ 0 < δ ∧ 1 ≤ C ∧ 0 ≤ s ∧
    SeparatedAt δ (P : Set X) ∧
    ∀ x : X, ∀ r : ℝ, δ ≤ r →
      ((P.filter fun y => dist y x ≤ r).card : ℝ) ≤
        C * r ^ s * (P.card : ℝ)

/-- Ball growth property for finite sets, without a separation requirement.
    QTTC only needs the ball growth part of `IsFiniteDeltaSSet` for its input;
    separation at scale δ is not used. This allows inputs that are only
    δ/2-separated (e.g. dyadic tube families). -/
structure BallGrowth (δ s C : ℝ) {X : Type*} [PseudoMetricSpace X] (P : Finset X) : Prop where
  nonempty : P.Nonempty
  δ_pos : 0 < δ
  C_one : 1 ≤ C
  s_nonneg : 0 ≤ s
  growth : ∀ (x : X) (r : ℝ), δ ≤ r →
    ((P.filter fun y => dist y x ≤ r).card : ℝ) ≤
      C * r ^ s * (P.card : ℝ)

/-- Extract the ball growth from a full `IsFiniteDeltaSSet`. -/
lemma IsFiniteDeltaSSet.toBallGrowth {δ s C : ℝ} {X : Type*} [PseudoMetricSpace X] {P : Finset X}
    (h : IsFiniteDeltaSSet δ s C P) : BallGrowth δ s C P :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩

def assignedCount {α L : Type*} [DecidableEq L]
    (coarse : L → L) (T : α → Finset L) (p : α) (c : L) : ℕ :=
  ((T p).filter fun ℓ => coarse ℓ = c).card

section Proofs
open Finset

-- ============================================================================
-- Constant bounds
-- ============================================================================

def L_bound (B D Δ : ℝ) : ℕ :=
  Nat.log 2 (Nat.ceil (8 * B * Δ ^ (-D))) + 3

lemma ceil_le_double' {x : ℝ} (hx : 1 ≤ x) : (Nat.ceil x : ℝ) ≤ 2 * x := by
  have h1 : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one_of_gt_neg_one (by linarith)
  have h2 : x + 1 ≤ 2 * x := by linarith
  linarith

lemma natLog2_le_realLog' {n : ℕ} (hn : 0 < n) :
    (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
  have h1 : (Nat.log 2 n : ℝ) ≤ Real.logb (2 : ℝ) (n : ℝ) := Real.natLog_le_logb n 2
  have h2 : Real.logb (2 : ℝ) (n : ℝ) = Real.log (n : ℝ) / Real.log 2 := by
    rw [Real.logb] <;> ring
  rw [h2] at h1
  exact h1

lemma log2Δ_ge_one' (Δ : ℝ) (hΔ_pos : 0 < Δ) (hΔ_half : Δ ≤ 1 / 2) :
    1 ≤ Real.log (2 / Δ) := by
  have h1 : 2 / Δ ≥ 4 := by
    have h2 : 0 < Δ := hΔ_pos
    have h3 : Δ ≤ 1 / 2 := hΔ_half
    have h4 : 2 / Δ ≥ 2 / (1 / 2 : ℝ) := by gcongr
    have h5 : 2 / (1 / 2 : ℝ) = 4 := by norm_num
    linarith
  have h2 : Real.log (2 / Δ) ≥ Real.log 4 := Real.log_le_log (by linarith) h1
  have h_log2_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have h_log4 : Real.log 4 = 2 * Real.log 2 := by
    have h : Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
    rw [h, Real.log_pow] <;> ring
  have h3 : Real.log 4 ≥ 1 := by
    rw [h_log4]
    linarith
  linarith

lemma half_pow_le_half (D : ℝ) (hD : 1 ≤ D) : (1 / 2 : ℝ) ^ D ≤ 1 / 2 := by
  have h_pos : (0 : ℝ) < 1 / 2 := by norm_num
  have h_log_nonpos : Real.log (1 / 2 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  have h7 : D * Real.log (1 / 2 : ℝ) ≤ (1 : ℝ) * Real.log (1 / 2 : ℝ) := by nlinarith
  have h8 : Real.log ((1 / 2 : ℝ) ^ D) = D * Real.log (1 / 2 : ℝ) := by
    rw [Real.log_rpow (by norm_num)] <;> ring
  have h9 : Real.log ((1 / 2 : ℝ) ^ (1 : ℝ)) = (1 : ℝ) * Real.log (1 / 2 : ℝ) := by
    rw [Real.log_rpow (by norm_num)] <;> ring
  have h10 : Real.log ((1 / 2 : ℝ) ^ D) ≤ Real.log ((1 / 2 : ℝ) ^ (1 : ℝ)) := by
    rw [h8, h9] <;> exact h7
  have h11 : (0 : ℝ) < (1 / 2 : ℝ) ^ D := Real.rpow_pos_of_pos h_pos D
  have h12 : (0 : ℝ) < (1 / 2 : ℝ) ^ (1 : ℝ) := Real.rpow_pos_of_pos h_pos 1
  have h13 : (1 / 2 : ℝ) ^ D ≤ (1 / 2 : ℝ) ^ (1 : ℝ) := (Real.log_le_log_iff h11 h12).mp h10
  have h14 : (1 / 2 : ℝ) ^ (1 : ℝ) = 1 / 2 := by simp
  rw [h14] at h13
  exact h13

theorem L_bound_log
    (B D Δ : ℝ) (hB : 1 ≤ B) (hD : 1 ≤ D) (hΔ_pos : 0 < Δ) (hΔ_half : Δ ≤ 1 / 2) :
    ∃ C : ℝ, 1 ≤ C ∧ (L_bound B D Δ : ℝ) ≤ C * Real.log (2 / Δ) := by
  set x : ℝ := 8 * B * Δ ^ (-D) with hx_def
  have hΔD_pos : 0 < Δ ^ D := Real.rpow_pos_of_pos hΔ_pos D
  have hΔD_le_half : Δ ^ D ≤ 1 / 2 := by
    have h1 : 0 ≤ Δ := by linarith
    have h2 : Δ ^ D ≤ (1 / 2 : ℝ) ^ D := Real.rpow_le_rpow h1 (by linarith) (by linarith)
    have h3 : (1 / 2 : ℝ) ^ D ≤ 1 / 2 := half_pow_le_half D hD
    linarith
  have h_x_ge16 : 16 ≤ x := by
    have h1 : Δ ^ (-D) = (Δ ^ D)⁻¹ := by
      rw [Real.rpow_neg (show 0 ≤ Δ by linarith)] <;> rfl
    rw [hx_def, h1]
    have h2 : (Δ ^ D)⁻¹ ≥ 2 := by
      have h3 : Δ ^ D ≤ 1 / 2 := hΔD_le_half
      have h4 : 0 < Δ ^ D := hΔD_pos
      have h5 : 1 / (Δ ^ D) ≥ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le h4 h3
      simpa using h5
    have h7 : 8 * B ≥ 8 := by nlinarith
    nlinarith
  set n : ℕ := Nat.ceil x with hn_def
  have hn_pos : 0 < n := Nat.ceil_pos.mpr (by linarith)
  have hn_le : (n : ℝ) ≤ 2 * x := ceil_le_double' (by linarith)
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_log2_le_log2Δ : Real.log 2 ≤ Real.log (2 / Δ) := by
    have h5 : 0 < Δ := hΔ_pos
    have h6 : Δ ≤ 1 / 2 := hΔ_half
    have h7 : 2 / Δ ≥ 2 := by
      have h8 : 2 / Δ ≥ 2 / (1 / 2 : ℝ) := by gcongr
      have h9 : 2 / (1 / 2 : ℝ) = 4 := by norm_num
      linarith
    exact Real.log_le_log (by positivity) h7
  have h3 : Real.log (n : ℝ) ≤ Real.log (2 * x) := Real.log_le_log (by positivity) hn_le
  have h4 : Real.log (2 * x) = Real.log 2 + Real.log x := by
    rw [Real.log_mul (by positivity) (by positivity)] <;> ring
  have h_logx : Real.log x = Real.log (8 * B) - D * Real.log Δ := by
    have h_pos1 : 0 < 8 * B := by positivity
    have h_pos2 : 0 < Δ ^ (-D) := Real.rpow_pos_of_pos hΔ_pos (-D)
    have h : Real.log x = Real.log (8 * B) + Real.log (Δ ^ (-D)) := by
      rw [hx_def, Real.log_mul (ne_of_gt h_pos1) (ne_of_gt h_pos2)] <;> ring
    rw [h]
    have h2 : Real.log (Δ ^ (-D)) = (-D) * Real.log Δ := by
      rw [Real.log_rpow hΔ_pos] <;> ring
    rw [h2] <;> ring
  have h_neg_logΔ_le_log2Δ : -Real.log Δ ≤ Real.log (2 / Δ) := by
    have h_eq : Real.log (2 / Δ) = Real.log 2 - Real.log Δ := by
      rw [Real.log_div (ne_of_gt (by positivity)) (ne_of_gt hΔ_pos)] <;> ring
    rw [h_eq] <;> linarith
  have h_log8B_nonneg : 0 ≤ Real.log (8 * B) := by
    have h : 8 * B ≥ 1 := by nlinarith
    exact Real.log_nonneg h
  have hD_nonneg : 0 ≤ D := by linarith
  have h_logx_bound : Real.log x ≤ Real.log (8 * B) + D * Real.log (2 / Δ) := by
    rw [h_logx]
    have h : D * (-Real.log Δ) ≤ D * Real.log (2 / Δ) := by
      gcongr <;> exact h_neg_logΔ_le_log2Δ
    have h_eq : Real.log (8 * B) - D * Real.log Δ = Real.log (8 * B) + D * (-Real.log Δ) := by ring
    rw [h_eq]
    gcongr
  have h_logn_bound : Real.log (n : ℝ) ≤ Real.log 2 + Real.log (8 * B) + D * Real.log (2 / Δ) := by
    calc
      Real.log (n : ℝ)
        ≤ Real.log (2 * x) := h3
      _ = Real.log 2 + Real.log x := h4
      _ ≤ Real.log 2 + Real.log (8 * B) + D * Real.log (2 / Δ) := by linarith [h_logx_bound]
  set C : ℝ := (Real.log 2 + Real.log (8 * B) + D) / Real.log 2 + 3 / Real.log 2 with hC_def
  have hC_ge1 : 1 ≤ C := by
    have h4 : (Real.log 2 + Real.log (8 * B) + D) / Real.log 2 ≥ 1 := by
      have h5 : Real.log 2 + Real.log (8 * B) + D ≥ Real.log 2 := by linarith
      have h6 : 0 < Real.log 2 := h_log2_pos
      have h7 : ((Real.log 2 + Real.log (8 * B) + D) / Real.log 2) ≥ (Real.log 2 / Real.log 2) := by gcongr
      have h8 : Real.log 2 / Real.log 2 = 1 := by field_simp [h6.ne'] <;> ring
      rw [h8] at h7
      exact h7
    have h9 : 0 < 3 / Real.log 2 := by positivity
    have h10 : 1 ≤ (Real.log 2 + Real.log (8 * B) + D) / Real.log 2 + 3 / Real.log 2 := by linarith
    exact h10
  have h11 : (Nat.log 2 n : ℝ) ≤ ((Real.log 2 + Real.log (8 * B) + D) / Real.log 2) * Real.log (2 / Δ) := by
    have h10 : (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := natLog2_le_realLog' hn_pos
    have h_y_ge1 : 1 ≤ Real.log (2 / Δ) := log2Δ_ge_one' Δ hΔ_pos hΔ_half
    have h_coeff1 : 0 ≤ (Real.log 2 + Real.log (8 * B)) / Real.log 2 := by positivity
    have h_step1 : (Real.log 2 + Real.log (8 * B) + D * Real.log (2 / Δ)) / Real.log 2 =
        (Real.log 2 + Real.log (8 * B)) / Real.log 2 + D * Real.log (2 / Δ) / Real.log 2 := by
      rw [add_div]
    have h_step2 : (Real.log 2 + Real.log (8 * B)) / Real.log 2 ≤ ((Real.log 2 + Real.log (8 * B)) / Real.log 2) * Real.log (2 / Δ) := by
      exact le_mul_of_one_le_right h_coeff1 h_y_ge1
    have h_step3 : D * Real.log (2 / Δ) / Real.log 2 = (D / Real.log 2) * Real.log (2 / Δ) := by ring
    calc
      (Nat.log 2 n : ℝ)
        ≤ Real.log (n : ℝ) / Real.log 2 := h10
      _ ≤ (Real.log 2 + Real.log (8 * B) + D * Real.log (2 / Δ)) / Real.log 2 := by gcongr
      _ = (Real.log 2 + Real.log (8 * B)) / Real.log 2 + D * Real.log (2 / Δ) / Real.log 2 := h_step1
      _ ≤ ((Real.log 2 + Real.log (8 * B)) / Real.log 2) * Real.log (2 / Δ) + (D / Real.log 2) * Real.log (2 / Δ) := by
        rw [h_step3] <;> gcongr
      _ = ((Real.log 2 + Real.log (8 * B) + D) / Real.log 2) * Real.log (2 / Δ) := by ring
  have h12 : (3 : ℝ) ≤ (3 / Real.log 2) * Real.log (2 / Δ) := by
    calc
      (3 : ℝ)
        = (3 / Real.log 2) * Real.log 2 := by field_simp [h_log2_pos.ne'] <;> ring
      _ ≤ (3 / Real.log 2) * Real.log (2 / Δ) := by gcongr
  have h_main : (Nat.log 2 n : ℝ) + 3 ≤ C * Real.log (2 / Δ) := by
    have h13 : C * Real.log (2 / Δ) =
        ((Real.log 2 + Real.log (8 * B) + D) / Real.log 2) * Real.log (2 / Δ) +
        (3 / Real.log 2) * Real.log (2 / Δ) := by
      dsimp only [C] <;> ring
    rw [h13]
    linarith
  have h_final : (L_bound B D Δ : ℝ) = (Nat.log 2 n : ℝ) + 3 := by
    simp [L_bound, hn_def] <;> norm_cast
  rw [h_final]
  exact ⟨C, hC_ge1, h_main⟩

theorem monomial_log_bound'
    (B D Δ : ℝ) (hB : 1 ≤ B) (hD : 1 ≤ D) (hΔ_pos : 0 < Δ) (hΔ_half : Δ ≤ 1 / 2)
    (c : ℝ) (hc_nonneg : 0 ≤ c) (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ c * (L_bound B D Δ : ℝ)^n ≤ A * Real.rpow (Real.log (2 / Δ)) A := by
  rcases L_bound_log B D Δ hB hD hΔ_pos hΔ_half with ⟨C, hC_ge1, hCL⟩
  set y : ℝ := Real.log (2 / Δ) with hy_def
  have h_y_ge1 : 1 ≤ y := log2Δ_ge_one' Δ hΔ_pos hΔ_half
  set Lval : ℝ := (L_bound B D Δ : ℝ) with hLval_def
  have hL_le : Lval ≤ C * y := hCL
  set A : ℝ := max (max (n : ℝ) 1) (c * C^n) with hA_def
  have hA_ge1 : 1 ≤ A := by
    have h1 : 1 ≤ max (n : ℝ) 1 := le_max_right _ _
    exact le_trans h1 (le_max_left _ _)
  have hA_ge_n : (n : ℝ) ≤ A := by
    have h1 : (n : ℝ) ≤ max (n : ℝ) 1 := le_max_left _ _
    exact le_trans h1 (le_max_left _ _)
  have hA_ge_cCn : c * C^n ≤ A := le_max_right _ _
  have h_pos1 : 0 ≤ Lval := by positivity
  have h_pos2 : 0 ≤ C * y := by positivity
  have h1 : Lval^n ≤ (C * y)^n := by gcongr
  have h5 : 0 ≤ C := by linarith
  have h6 : 0 ≤ y := by linarith
  have h7 : ∀ (k : ℕ), (C * y)^k = C^k * y^k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      simp [ih, pow_succ] <;> ring
  have h4 : (C * y)^n = C^n * y^n := h7 n
  have h_pos3 : 0 ≤ c := hc_nonneg
  have h7 : c * Lval^n ≤ c * C^n * y^n := by
    have h71 : c * Lval^n ≤ c * (C * y)^n := by gcongr
    have h72 : c * (C * y)^n = c * C^n * y^n := by rw [h4] <;> ring
    rw [h72] at h71
    exact h71
  have h9 : 1 ≤ y := h_y_ge1
  have h10 : y^n = y^(n : ℝ) := by norm_cast
  have h8 : y^n ≤ y^A := by
    rw [h10]
    exact Real.rpow_le_rpow_of_exponent_le h9 hA_ge_n
  have h_pos4 : 0 ≤ A := by linarith
  have h11 : c * C^n * y^n ≤ A * y^A := by
    have h111 : c * C^n ≤ A := hA_ge_cCn
    have h112 : c * C^n * y^n ≤ A * y^n := by gcongr
    have h113 : A * y^n ≤ A * y^A := by gcongr
    exact h112.trans h113
  exact ⟨A, hA_ge1, h7.trans h11⟩

theorem rpow_K_bound'
    (K C₁ c : ℝ) (hK : 1 ≤ K) (hC1 : 1 ≤ C₁) (hc_nonneg : 0 ≤ c) (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ c * K^n ≤ A * Real.rpow K A * C₁ := by
  set A : ℝ := max (n : ℝ) (max c 1) with hA_def
  have hA_ge1 : 1 ≤ A := by
    have h1 : 1 ≤ max c 1 := le_max_right _ _
    exact le_trans h1 (le_max_right _ _)
  have hA_ge_n : (n : ℝ) ≤ A := le_max_left _ _
  have hA_ge_c : c ≤ A := by
    have h1 : c ≤ max c 1 := le_max_left _ _
    exact le_trans h1 (le_max_right _ _)
  have h_posK : 0 ≤ K := by linarith
  have h1 : K^n = K^(n : ℝ) := by norm_cast
  have h2 : K^n ≤ K^A := by
    rw [h1]
    exact Real.rpow_le_rpow_of_exponent_le hK hA_ge_n
  have h_posA : 0 ≤ A := by linarith
  have h3 : c * K^n ≤ A * K^n := by gcongr
  have h4 : A * K^n ≤ A * K^A := by gcongr
  have h5 : c * K^n ≤ A * K^A := h3.trans h4
  have h6 : 0 ≤ A * K^A := by positivity
  have h7 : A * K^A ≤ A * K^A * C₁ := by
    have h8 : 1 ≤ C₁ := hC1
    nlinarith
  exact ⟨A, hA_ge1, h5.trans h7⟩

theorem K_bound
    (s D B Δ : ℝ) (N L_levels : ℕ) (K : ℝ)
    (hB : 1 ≤ B) (hD : 1 ≤ D) (hΔ_pos : 0 < Δ) (hΔ_half : Δ ≤ 1 / 2)
    (hN : (N : ℝ) ≤ B * Δ ^ (-D))
    (hL : L_levels = Nat.log 2 N + 4)
    (hK : K = 2^21 * (L_levels : ℝ)^6) :
    ∃ A : ℝ, 1 ≤ A ∧ K ≤ A * Real.rpow (Real.log (2 / Δ)) A := by
  set Lval : ℕ := L_bound B D Δ with hLval_def
  have h_x_ge16 : 16 ≤ 8 * B * Δ ^ (-D) := by
    have h1 : Δ ^ (-D) ≥ 2 := by
      have h2 : Δ ^ D ≤ 1 / 2 := by
        have h3 : 0 ≤ Δ := by linarith
        have h4 : Δ ^ D ≤ (1 / 2 : ℝ) ^ D := Real.rpow_le_rpow h3 (by linarith) (by linarith)
        have h5 : (1 / 2 : ℝ) ^ D ≤ 1 / 2 := half_pow_le_half D hD
        linarith
      have h3 : 0 < Δ ^ D := Real.rpow_pos_of_pos hΔ_pos D
      have h4 : (Δ ^ D)⁻¹ ≥ 2 := by
        have h5 : Δ ^ D ≤ 1 / 2 := h2
        have h6 : 1 / (Δ ^ D) ≥ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le h3 h5
        simpa using h6
      have h7 : Δ ^ (-D) = (Δ ^ D)⁻¹ := by
        rw [Real.rpow_neg (show 0 ≤ Δ by linarith)] <;> rfl
      rw [h7]
      exact h4
    have h8 : 8 * B ≥ 8 := by nlinarith
    nlinarith
  have hN_le_ceil : N ≤ Nat.ceil (8 * B * Δ ^ (-D)) := by
    have h1 : (N : ℝ) ≤ B * Δ ^ (-D) := hN
    have h2 : B * Δ ^ (-D) ≤ 8 * B * Δ ^ (-D) := by
      have h3 : 0 ≤ Δ ^ (-D) := by positivity
      nlinarith
    have h4 : (N : ℝ) ≤ 8 * B * Δ ^ (-D) := by linarith
    have h5 : 8 * B * Δ ^ (-D) ≤ (Nat.ceil (8 * B * Δ ^ (-D)) : ℝ) := Nat.le_ceil _
    have h6 : (N : ℝ) ≤ (Nat.ceil (8 * B * Δ ^ (-D)) : ℝ) := by linarith
    exact_mod_cast h6
  have h_log_mono : Nat.log 2 N ≤ Nat.log 2 (Nat.ceil (8 * B * Δ ^ (-D))) :=
    Nat.log_mono_right hN_le_ceil
  have hL_levels_le : L_levels ≤ Lval + 1 := by
    rw [hL, hLval_def, L_bound] <;> omega
  have hLval_ge7 : 7 ≤ Lval := by
    dsimp only [Lval, L_bound]
    have h1 : 16 ≤ Nat.ceil (8 * B * Δ ^ (-D)) := by
      have h2 : (16 : ℝ) ≤ 8 * B * Δ ^ (-D) := h_x_ge16
      have h3 : (8 * B * Δ ^ (-D)) ≤ (Nat.ceil (8 * B * Δ ^ (-D)) : ℝ) := Nat.le_ceil _
      have h4 : (16 : ℝ) ≤ (Nat.ceil (8 * B * Δ ^ (-D)) : ℝ) := by linarith
      exact_mod_cast h4
    have h5 : 2 ^ 4 ≤ Nat.ceil (8 * B * Δ ^ (-D)) := by simpa using h1
    have h6 : 4 ≤ Nat.log 2 (Nat.ceil (8 * B * Δ ^ (-D))) := by
      have h7 : 0 < Nat.ceil (8 * B * Δ ^ (-D)) := by positivity
      have h8 : 2 ^ 4 ≤ Nat.ceil (8 * B * Δ ^ (-D)) := h5
      have h9 : 4 ≤ Nat.log 2 (Nat.ceil (8 * B * Δ ^ (-D))) :=
        Nat.le_log_of_pow_le (by norm_num) h8
      exact h9
    omega
  have hL_levels_le2 : (L_levels : ℝ) ≤ 2 * (Lval : ℝ) := by
    have h1 : (L_levels : ℝ) ≤ (Lval : ℝ) + 1 := by exact_mod_cast hL_levels_le
    have h2 : (Lval : ℝ) ≥ 7 := by exact_mod_cast hLval_ge7
    linarith
  have hK_bound : K ≤ 2^27 * (Lval : ℝ)^6 := by
    rw [hK]
    have h1 : (L_levels : ℝ)^6 ≤ (2 * (Lval : ℝ))^6 := by gcongr
    have h2 : (2 * (Lval : ℝ))^6 = 2^6 * (Lval : ℝ)^6 := by ring
    rw [h2] at h1
    linarith
  have h_main := monomial_log_bound' B D Δ hB hD hΔ_pos hΔ_half (2^27 : ℝ) (by positivity) 6
  rcases h_main with ⟨A, hA_ge1, hA_bound⟩
  exact ⟨A, hA_ge1, hK_bound.trans hA_bound⟩

theorem C2_bound
    (s : ℝ) (C₁ : ℝ) (L_levels : ℕ) (K C2_val : ℝ)
    (hs : 0 ≤ s) (hC1 : 1 ≤ C₁) (hL_ge1 : 1 ≤ L_levels)
    (hK : 1 ≤ K)
    (hC2 : C2_val = 1024 * 2^(s+2) * C₁ * (L_levels : ℝ)^2)
    (hK_def : K = 2^21 * (L_levels : ℝ)^6) :
    ∃ A : ℝ, 1 ≤ A ∧ C2_val ≤ A * Real.rpow K A * C₁ := by
  have hL2_le_K : (L_levels : ℝ)^2 ≤ K := by
    rw [hK_def]
    have h1 : 1 ≤ (L_levels : ℝ) := by exact_mod_cast hL_ge1
    have h2 : (L_levels : ℝ)^2 ≤ (L_levels : ℝ)^6 := by gcongr <;> norm_num
    have h3 : (L_levels : ℝ)^6 ≤ 2^21 * (L_levels : ℝ)^6 := by
      have h4 : 0 ≤ (L_levels : ℝ)^6 := by positivity
      nlinarith
    linarith
  set c : ℝ := 1024 * 2^(s+2) with hc_def
  have hc_nonneg : 0 ≤ c := by dsimp only [c]; positivity
  have hC2_le : C2_val ≤ c * C₁ * K := by
    rw [hC2]
    have h1 : c * C₁ * (L_levels : ℝ)^2 ≤ c * C₁ * K := by
      gcongr <;> exact hL2_le_K
    exact h1
  have h_main := rpow_K_bound' K C₁ (c * C₁) hK hC1 (by positivity) 1
  rcases h_main with ⟨A, hA_ge1, hA_bound⟩
  have hA_bound' : (c * C₁) * K ≤ A * Real.rpow K A * C₁ := by
    simpa [pow_one] using hA_bound
  exact ⟨A, hA_ge1, hC2_le.trans hA_bound'⟩

theorem combined_bound
    (s D B Δ : ℝ) (N L_levels : ℕ) (K C2_val C₁ : ℝ)
    (hB : 1 ≤ B) (hD : 1 ≤ D) (hΔ_pos : 0 < Δ) (hΔ_half : Δ ≤ 1 / 2)
    (hs : 0 ≤ s) (hC1 : 1 ≤ C₁) (hL_ge1 : 1 ≤ L_levels)
    (hN : (N : ℝ) ≤ B * Δ ^ (-D))
    (hL : L_levels = Nat.log 2 N + 4)
    (hK_def : K = 2^21 * (L_levels : ℝ)^6)
    (hC2 : C2_val = 1024 * 2^(s+2) * C₁ * (L_levels : ℝ)^2) :
    ∃ A : ℝ, 1 ≤ A ∧
      K ≤ A * Real.rpow (Real.log (2 / Δ)) A ∧
      C2_val ≤ A * Real.rpow K A * C₁ := by
  have hK_ge1 : 1 ≤ K := by
    rw [hK_def]
    have h1 : 1 ≤ (L_levels : ℝ) := by exact_mod_cast hL_ge1
    have h3 : (L_levels : ℝ)^6 ≥ 1 := by
      have h4 : (L_levels : ℝ) ≥ 1 := h1
      have h5 : (L_levels : ℝ)^6 ≥ 1^6 := by gcongr
      simpa using h5
    have h6 : (2 : ℝ)^21 * (L_levels : ℝ)^6 ≥ 1 := by
      have h7 : (2 : ℝ)^21 ≥ 1 := by norm_num
      nlinarith
    exact h6
  rcases K_bound s D B Δ N L_levels K hB hD hΔ_pos hΔ_half hN hL hK_def with ⟨A1, hA1_ge1, hA1_K⟩
  rcases C2_bound s C₁ L_levels K C2_val hs hC1 hL_ge1 hK_ge1 hC2 hK_def with ⟨A2, hA2_ge1, hA2_C2⟩
  set A : ℝ := max A1 A2 with hA_def
  have hA_ge1 : 1 ≤ A := by
    have h1 : 1 ≤ A1 := hA1_ge1
    have h2 : A1 ≤ A := le_max_left _ _
    linarith
  have hA_ge_A1 : A1 ≤ A := le_max_left _ _
  have hA_ge_A2 : A2 ≤ A := le_max_right _ _
  have h_log_ge1 : 1 ≤ Real.log (2 / Δ) := log2Δ_ge_one' Δ hΔ_pos hΔ_half
  have h_base_log_pos : 0 < Real.log (2 / Δ) := by linarith [h_log_ge1]
  have h_pos_log1 : 0 ≤ Real.rpow (Real.log (2 / Δ)) A1 := Real.rpow_nonneg (by linarith) _
  have hK_bound : K ≤ A * Real.rpow (Real.log (2 / Δ)) A := by
    have h1 : Real.rpow (Real.log (2 / Δ)) A1 ≤ Real.rpow (Real.log (2 / Δ)) A :=
      Real.rpow_le_rpow_of_exponent_le h_log_ge1 hA_ge_A1
    have h2 : A1 * Real.rpow (Real.log (2 / Δ)) A1 ≤ A * Real.rpow (Real.log (2 / Δ)) A := by
      have h3 : 0 ≤ A1 := by linarith
      have h4 : 0 ≤ Real.rpow (Real.log (2 / Δ)) A1 := h_pos_log1
      gcongr
    exact hA1_K.trans h2
  have h_baseK_pos : 0 < K := by linarith [hK_ge1]
  have h_posK_rpow : 0 ≤ Real.rpow K A2 := Real.rpow_nonneg (by linarith) _
  have hC2_bound : C2_val ≤ A * Real.rpow K A * C₁ := by
    have h1 : Real.rpow K A2 ≤ Real.rpow K A := Real.rpow_le_rpow_of_exponent_le hK_ge1 hA_ge_A2
    have h2 : A2 * Real.rpow K A2 * C₁ ≤ A * Real.rpow K A * C₁ := by
      have h3 : 0 ≤ A2 := by linarith
      have h4 : 0 ≤ Real.rpow K A2 := h_posK_rpow
      have h5 : 0 ≤ C₁ := by linarith
      gcongr
    exact hA2_C2.trans h2
  exact ⟨A, hA_ge1, hK_bound, hC2_bound⟩


-- ============================================================================
-- Pigeonholing lemmas
-- ============================================================================

lemma dyadic_pigeonhole_bounded {α : Type*} [DecidableEq α]
    {s : Finset α} {f : α → ℕ} {k_min k_max K : ℕ}
    (h_total_pos : 0 < ∑ a ∈ s, f a)
    (h_range : ∀ a ∈ s, 2 ^ k_min ≤ f a ∧ f a < 2 ^ (k_max + 1))
    (hK : k_max + 1 - k_min ≤ K) :
    ∃ k ∈ Finset.Icc k_min k_max,
      (∑ a ∈ (s.filter (fun a => 2 ^ k ≤ f a ∧ f a < 2 ^ (k + 1))), f a) * K ≥
        ∑ a ∈ s, f a := by
  let layers := Finset.Icc k_min k_max
  let S : ℕ → Finset α := fun k =>
    s.filter (fun a => 2 ^ k ≤ f a ∧ f a < 2 ^ (k + 1))
  have h1 : ∃ a ∈ s, 0 < f a := by
    by_cases h : ∃ a ∈ s, 0 < f a
    · exact h
    · have h2 : ∀ a ∈ s, f a = 0 := by
        intro a ha
        by_contra h3
        have h4 : 0 < f a := by omega
        exact h ⟨a, ha, h4⟩
      have h3 : ∑ a ∈ s, f a = 0 := by
        rw [Finset.sum_eq_zero] <;> exact h2
      rw [h3] at h_total_pos <;> simp at h_total_pos
  rcases h1 with ⟨a, ha, hfa⟩
  have h_kmin_le_kmax : k_min ≤ k_max := by
    have h3 : 2 ^ k_min ≤ f a := (h_range a ha).1
    have h4 : f a < 2 ^ (k_max + 1) := (h_range a ha).2
    have h5 : 2 ^ k_min < 2 ^ (k_max + 1) := lt_of_le_of_lt h3 h4
    have h6 : k_min < k_max + 1 := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h5
    omega
  have h_layers_card_pos : 0 < layers.card := by
    have h : layers.card = k_max - k_min + 1 := by
      simp [layers, Finset.Icc_eq_empty_of_lt] <;> omega
    rw [h] <;> omega
  have h_disj : ∀ k1 ∈ layers, ∀ k2 ∈ layers, k1 ≠ k2 → Disjoint (S k1) (S k2) := by
    intro k1 _ k2 _ hne
    simp only [S, Finset.disjoint_left]
    intro a ha1 ha2
    have h1 : 2 ^ k1 ≤ f a ∧ f a < 2 ^ (k1 + 1) := (Finset.mem_filter.mp ha1).2
    have h2 : 2 ^ k2 ≤ f a ∧ f a < 2 ^ (k2 + 1) := (Finset.mem_filter.mp ha2).2
    by_cases h : k1 < k2
    · have h5 : k1 + 1 ≤ k2 := by omega
      have h6 : 2 ^ (k1 + 1) ≤ 2 ^ k2 := by gcongr <;> norm_num
      linarith
    · have h' : k2 < k1 := by omega
      have h5 : k2 + 1 ≤ k1 := by omega
      have h6 : 2 ^ (k2 + 1) ≤ 2 ^ k1 := by gcongr <;> norm_num
      linarith
  have h_cover : ∀ a ∈ s, ∃ k ∈ layers, a ∈ S k := by
    intro a ha
    let k := Nat.log 2 (f a)
    have h_pos2 : 0 < 2 ^ k_min := by positivity
    have hfa_pos : 0 < f a := by
      have h : 2 ^ k_min ≤ f a := (h_range a ha).1
      linarith
    have hk1 : 2 ^ k ≤ f a := Nat.pow_log_le_self 2 (by omega)
    have hk2 : f a < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) (f a)
    have hk_min : k_min ≤ k := by
      have h : 2 ^ k_min ≤ f a := (h_range a ha).1
      have h_log : Nat.log 2 (2 ^ k_min) ≤ Nat.log 2 (f a) := Nat.log_mono_right h
      have h_eq : Nat.log 2 (2 ^ k_min) = k_min := by
        rw [Nat.log_pow] <;> norm_num
      rw [h_eq] at h_log
      exact h_log
    have hk_max : k ≤ k_max := by
      have h : f a < 2 ^ (k_max + 1) := (h_range a ha).2
      have h'' : 2 ^ k < 2 ^ (k_max + 1) := lt_of_le_of_lt hk1 h
      have : k < k_max + 1 := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h''
      omega
    exact ⟨k, Finset.mem_Icc.mpr ⟨hk_min, hk_max⟩,
      Finset.mem_filter.mpr ⟨ha, ⟨hk1, hk2⟩⟩⟩
  have h_union : (Finset.biUnion layers S) = s := by
    ext a
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨k, _, hk⟩
      exact (Finset.mem_filter.mp hk).1
    · intro ha
      exact h_cover a ha
  have h_sum : ∑ k ∈ layers, ∑ a ∈ S k, f a = ∑ a ∈ s, f a := by
    have h_eq : ∑ k ∈ layers, ∑ a ∈ S k, f a = ∑ a ∈ (Finset.biUnion layers S), f a := by
      exact Eq.symm (sum_biUnion h_disj)
    rw [h_eq, h_union]
  have h_layers_card : layers.card = k_max + 1 - k_min := by
    simp [layers, Finset.Icc_eq_empty_of_lt] <;> omega
  have h_main : ∃ k ∈ layers, (∑ a ∈ S k, f a) * layers.card ≥ ∑ a ∈ s, f a := by
    by_contra h
    have h' : ∀ k ∈ layers, (∑ a ∈ S k, f a) * layers.card < ∑ a ∈ s, f a := by
      simpa [not_exists] using h
    have h4 : ∀ k ∈ layers, ∑ a ∈ S k, f a ≤ (∑ a ∈ s, f a - 1) / layers.card := by
      intro k hk
      have h5 : (∑ a ∈ S k, f a) * layers.card < ∑ a ∈ s, f a := h' k hk
      have h6 : (∑ a ∈ S k, f a) * layers.card ≤ ∑ a ∈ s, f a - 1 := by omega
      have h_pos : 0 < layers.card := h_layers_card_pos
      have h7 : ∑ a ∈ S k, f a ≤ (∑ a ∈ s, f a - 1) / layers.card := by
        rw [Nat.le_div_iff_mul_le h_pos]
        exact h6
      exact h7
    have h3 : ∑ k ∈ layers, (∑ a ∈ S k, f a) ≤
        layers.card * ((∑ a ∈ s, f a - 1) / layers.card) := by
      calc
        ∑ k ∈ layers, (∑ a ∈ S k, f a)
          ≤ ∑ _k ∈ layers, (∑ a ∈ s, f a - 1) / layers.card := Finset.sum_le_sum h4
        _ = layers.card * ((∑ a ∈ s, f a - 1) / layers.card) := by
          simp [Finset.sum_const]
    have h5 : layers.card * ((∑ a ∈ s, f a - 1) / layers.card) ≤ ∑ a ∈ s, f a - 1 :=
      Nat.mul_div_le _ _
    have h6 : ∑ k ∈ layers, (∑ a ∈ S k, f a) ≤ ∑ a ∈ s, f a - 1 := h3.trans h5
    rw [h_sum] at h6
    omega
  rcases h_main with ⟨k, hk_layer, hk_ineq⟩
  have h7 : (∑ a ∈ S k, f a) * layers.card ≤ (∑ a ∈ S k, f a) * K := by
    gcongr
    rw [h_layers_card] <;> exact hK
  exact ⟨k, hk_layer, le_trans hk_ineq h7⟩

/-! ==========================================================================
   2. First pigeonhole (per-p uniformization)
   ========================================================================== -/

/-- Per-p uniformization: for a single `p`, find `C_p ⊆ coarseRange` and `m1`
such that assigned counts lie in `[m1, 2*m1)` and mass is in `[M/(8*K1), M]`. -/
lemma first_pigeonhole_single {α L : Type*} [DecidableEq α] [DecidableEq L]
    {M : ℕ} {p : α}
    (U : Finset L) (T : α → Finset L) (coarse : L → L) (coarseRange : Finset L)
    (hM_pos : 0 < M)
    (hT_card : M / 2 < (T p).card)
    (hT_le : (T p).card ≤ M)
    (hT_sub : T p ⊆ U)
    (h_coarse_in : ∀ ℓ ∈ U, coarse ℓ ∈ coarseRange)
    (hN_pos : 0 < coarseRange.card)
    (K1 : ℕ) (hK1_eq : K1 = Nat.log 2 coarseRange.card + 4) :
    ∃ (C_p : Finset L) (m1 : ℕ) (k : ℕ),
      C_p ⊆ coarseRange ∧
      (∀ c ∈ C_p, m1 ≤ assignedCount coarse T p c ∧ assignedCount coarse T p c < 2 * m1) ∧
      ((M : ℝ) / (8 * (K1 : ℝ)) ≤ (m1 : ℝ) * (C_p.card : ℝ)) ∧
      ((m1 : ℝ) * (C_p.card : ℝ) ≤ (M : ℝ)) ∧
      m1 = 2 ^ k ∧
      Nat.log 2 (M / (4 * coarseRange.card) + 1) ≤ k ∧ k ≤ Nat.log 2 M := by
  let N := coarseRange.card
  let f : L → ℕ := fun c => assignedCount coarse T p c
  have hft : ∀ ℓ ∈ T p, coarse ℓ ∈ coarseRange := fun ℓ hℓ => h_coarse_in ℓ (hT_sub hℓ)
  have h_sum_total : ∑ c ∈ coarseRange, f c = (T p).card := by
    have h1 : ∀ (c : L), f c = ∑ ℓ ∈ T p, (if coarse ℓ = c then (1 : ℕ) else (0 : ℕ)) := by
      intro c
      simp [f, assignedCount, Finset.sum_ite] <;> rfl
    have h1' : ∀ c ∈ coarseRange, f c = ∑ ℓ ∈ T p, (if coarse ℓ = c then (1 : ℕ) else (0 : ℕ)) := by
      intro c _
      exact h1 c
    have h2 : ∑ c ∈ coarseRange, f c = ∑ ℓ ∈ T p, 1 := by
      rw [Finset.sum_congr rfl h1', Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      have h5 : coarse ℓ ∈ coarseRange := hft ℓ hℓ
      simpa [Finset.sum_ite_eq, h5] using rfl
    rw [h2]
    simp
  let t := M / (4 * N)
  let low := coarseRange.filter (fun c => f c ≤ t)
  let high := coarseRange.filter (fun c => t < f c)
  have h_low_sub : low ⊆ coarseRange := Finset.filter_subset _ _
  have h_high_sub : high ⊆ coarseRange := Finset.filter_subset _ _
  have h_union : low ∪ high = coarseRange := by
    ext c
    simp only [low, high, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> tauto
    · intro hc
      by_cases h : f c ≤ t
      · left <;> exact ⟨hc, h⟩
      · right <;> exact ⟨hc, by omega⟩
  have h_disj : Disjoint low high := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    have h1 : f c ≤ t := (Finset.mem_filter.mp hc1).2
    have h2 : t < f c := (Finset.mem_filter.mp hc2).2
    omega
  have h4N_pos : 0 < 4 * N := by positivity
  have h_Nt_le_M4 : N * t ≤ M / 4 := by
    have h1 : (4 * N) * t ≤ M := Nat.mul_div_le M (4 * N)
    have h2 : 4 * (N * t) ≤ M := by
      have h3 : (4 * N) * t = 4 * (N * t) := by ring
      rw [h3] at h1
      exact h1
    have h4 : N * t * 4 ≤ M := by
      have h5 : N * t * 4 = 4 * (N * t) := by ring
      rw [h5] <;> exact h2
    have h6 : N * t ≤ M / 4 := by omega
    exact h6
  have h_sum_low_le : (∑ c ∈ low, f c : ℝ) ≤ (M : ℝ) / 4 := by
    have h1 : ∑ c ∈ low, f c ≤ N * t := by
      calc
        ∑ c ∈ low, f c ≤ ∑ c ∈ low, t := Finset.sum_le_sum (fun c hc =>
          (Finset.mem_filter.mp hc).2)
        _ = low.card * t := by simp [Finset.sum_const]
        _ ≤ N * t := by
          have h4 : low.card ≤ N := by
            have h5 : low.card ≤ coarseRange.card := Finset.card_le_card h_low_sub
            simpa [N] using h5
          exact mul_le_mul_right' h4 t
    have h2 : (∑ c ∈ low, f c : ℝ) ≤ (N * t : ℝ) := by exact_mod_cast h1
    have h3 : (N * t : ℝ) ≤ ((M / 4 : ℕ) : ℝ) := by exact_mod_cast h_Nt_le_M4
    have h4 : ((M / 4 : ℕ) : ℝ) ≤ (M : ℝ) / 4 := by
      have h5 : 4 * ((M / 4 : ℕ) : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast Nat.mul_div_le M 4
      linarith
    linarith
  have hT_card_real : ((T p).card : ℝ) > (M : ℝ) / 2 := by
    have h1 : M / 2 < (T p).card := hT_card
    have h2 : 2 * (T p).card > M := by
      have h3 : (T p).card ≥ M / 2 + 1 := by omega
      have h4 : 2 * (M / 2) ≥ M - 1 := by omega
      omega
    have h5 : (2 : ℝ) * ((T p).card : ℝ) > (M : ℝ) := by exact_mod_cast h2
    linarith
  have h_sum_high_real : (∑ c ∈ high, f c : ℝ) > (M : ℝ) / 4 := by
    have h_eq : (∑ c ∈ low, f c : ℝ) + (∑ c ∈ high, f c : ℝ) = ((T p).card : ℝ) := by
      have h_e : (∑ c ∈ low, f c) + (∑ c ∈ high, f c) = ∑ c ∈ coarseRange, f c := by
        rw [← Finset.sum_union h_disj, h_union]
      exact_mod_cast (by rw [h_e, h_sum_total])
    linarith
  have h_sum_high_pos : 0 < ∑ c ∈ high, f c := by
    have hM4_pos : (0 : ℝ) < (M : ℝ) / 4 := by positivity
    have h6 : (0 : ℝ) < (∑ c ∈ high, f c : ℝ) := by
      have h7 : (∑ c ∈ high, f c : ℝ) > (M : ℝ) / 4 := h_sum_high_real
      linarith
    exact_mod_cast h6
  let k_min := Nat.log 2 (t + 1)
  let k_max := Nat.log 2 M
  have h_bound1 : ∀ c ∈ high, 2 ^ k_min ≤ f c := by
    intro c hc
    have hft : t < f c := (Finset.mem_filter.mp hc).2
    have h : t + 1 ≤ f c := by omega
    have h2 : 2 ^ k_min ≤ t + 1 := Nat.pow_log_le_self 2 (by positivity)
    linarith
  have h_bound2 : ∀ c ∈ high, f c < 2 ^ (k_max + 1) := by
    intro c hc
    have hfc_le : f c ≤ (T p).card := by
      simp [f, assignedCount] <;> exact Finset.card_le_card (Finset.filter_subset _ _)
    have h : f c ≤ M := le_trans hfc_le hT_le
    have h3 : M < 2 ^ (k_max + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
    exact lt_of_le_of_lt h h3
  have h_k_bound : k_max + 1 - k_min ≤ K1 := by
    have h1 : M / (4 * N) < M / (4 * N) + 1 := by omega
    have hM_lt : M < (M / (4 * N) + 1) * (4 * N) :=
      (Nat.div_lt_iff_lt_mul h4N_pos).mp h1
    have hM_lt' : M < 4 * N * (t + 1) := by
      have h3 : (M / (4 * N) + 1) * (4 * N) = 4 * N * (t + 1) := by
        simp [t] <;> ring
      rw [h3] at hM_lt
      exact hM_lt
    let j := Nat.log 2 N
    have hj1 : 2 ^ j ≤ N := Nat.pow_log_le_self 2 hN_pos.ne'
    have hj2 : N < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
    have h4 : 2 ^ k_max ≤ M := Nat.pow_log_le_self 2 hM_pos.ne'
    have h5 : t + 1 < 2 ^ (k_min + 1) := Nat.lt_pow_succ_log_self (by norm_num) (t + 1)
    have h6 : M < 2 ^ (j + k_min + 4) := by
      calc
        M < 4 * N * (t + 1) := hM_lt'
        _ < 4 * (2 ^ (j + 1)) * (t + 1) := by gcongr <;> linarith
        _ = 2 ^ (j + 3) * (t + 1) := by ring_nf
        _ < 2 ^ (j + 3) * (2 ^ (k_min + 1)) := by gcongr
        _ = 2 ^ (j + k_min + 4) := by ring_nf
    have h7 : 2 ^ k_max < 2 ^ (j + k_min + 4) := lt_of_le_of_lt h4 h6
    have h8 : k_max < j + k_min + 4 := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h7
    have h9 : k_max + 1 - k_min ≤ j + 4 := by omega
    have h10 : j + 4 = K1 := by
      have h11 : j = Nat.log 2 N := by rfl
      rw [h11, hK1_eq] <;> ring
    rw [h10] at h9
    exact h9
  rcases dyadic_pigeonhole_bounded
    (s := high) (f := f) (k_min := k_min) (k_max := k_max) (K := K1)
    h_sum_high_pos (fun c hc => ⟨h_bound1 c hc, h_bound2 c hc⟩) h_k_bound
    with ⟨k, hk_layer, hk_ineq⟩
  let S_k := high.filter (fun c => 2 ^ k ≤ f c ∧ f c < 2 ^ (k + 1))
  have hS_sub : S_k ⊆ coarseRange := by
    trans high <;> exact Finset.filter_subset _ _
  have h_dyadic : ∀ c ∈ S_k, 2 ^ k ≤ f c ∧ f c < 2 ^ (k + 1) := by
    intro c hc
    exact (Finset.mem_filter.mp hc).2
  have h_ineq : (∑ c ∈ S_k, f c) * K1 ≥ ∑ c ∈ high, f c := by
    simpa [S_k] using hk_ineq
  have h_Sk_nonempty : S_k.Nonempty := by
    by_contra h
    have h_empty : S_k = ∅ := by simpa using h
    have h_sum_zero : ∑ c ∈ S_k, f c = 0 := by
      rw [h_empty] <;> simp
    rw [h_sum_zero] at h_ineq
    have h_cont : 0 ≥ ∑ c ∈ high, f c := by simpa using h_ineq
    have h_pos : 0 < ∑ c ∈ high, f c := h_sum_high_pos
    linarith
  have h_mass_upper : (2 ^ k : ℝ) * (S_k.card : ℝ) ≤ (M : ℝ) := by
    have h1 : ∑ c ∈ S_k, f c ≤ ∑ c ∈ coarseRange, f c := by
      gcongr <;> exact hS_sub
    have h2 : (2 ^ k : ℕ) * S_k.card ≤ ∑ c ∈ S_k, f c := by
      have h3 : ∀ c ∈ S_k, 2 ^ k ≤ f c := fun c hc => (h_dyadic c hc).1
      calc
        (2 ^ k) * S_k.card
          = S_k.card * (2 ^ k) := by ring
        _ = ∑ c ∈ S_k, (2 ^ k) := by simp [Finset.sum_const]
        _ ≤ ∑ c ∈ S_k, f c := Finset.sum_le_sum h3
    have h4 : ∑ c ∈ coarseRange, f c = (T p).card := h_sum_total
    have h5 : (T p).card ≤ M := hT_le
    exact_mod_cast le_trans h2 (le_trans h1 (by rw [h4] <;> exact h5))
  set S_sum : ℝ := (∑ c ∈ S_k, f c : ℝ) with hS_sum_def
  set H_sum : ℝ := (∑ c ∈ high, f c : ℝ) with hH_sum_def
  set m : ℝ := (2 ^ k : ℝ) with hm_def
  set ccard : ℝ := (S_k.card : ℝ) with hc_def
  set K1r : ℝ := (K1 : ℝ) with hK1r_def
  have hK1_pos' : 0 < K1r := by
    have h : K1 ≥ 4 := by
      rw [hK1_eq] <;> omega
    have h' : (K1 : ℝ) ≥ 4 := by exact_mod_cast h
    have h'' : 0 < (K1 : ℝ) := by linarith
    simpa [K1r] using h''
  have h11 : K1r * S_sum ≥ H_sum := by
    have h11' : (∑ c ∈ S_k, f c) * K1 ≥ ∑ c ∈ high, f c := h_ineq
    have h11'' : K1 * (∑ c ∈ S_k, f c) ≥ ∑ c ∈ high, f c := by
      have h_comm : (∑ c ∈ S_k, f c) * K1 = K1 * (∑ c ∈ S_k, f c) := by ring
      rw [h_comm] at h11'
      exact h11'
    have h11''' : (K1 : ℝ) * (∑ c ∈ S_k, f c : ℝ) ≥ (∑ c ∈ high, f c : ℝ) := by exact_mod_cast h11''
    simpa [K1r, S_sum, H_sum] using h11'''
  have h13 : H_sum > (M : ℝ) / 4 := h_sum_high_real
  have h14 : K1r * S_sum > (M : ℝ) / 4 := by linarith
  have h15 : S_sum > (M : ℝ) / (4 * K1r) := by
    have h : K1r * S_sum > (M : ℝ) / 4 := h14
    have h' : S_sum > ((M : ℝ) / 4) / K1r := by
      calc
        S_sum = (K1r * S_sum) / K1r := by field_simp [hK1_pos'.ne'] <;> ring
        _ > ((M : ℝ) / 4) / K1r := by gcongr
    have h'' : ((M : ℝ) / 4) / K1r = (M : ℝ) / (4 * K1r) := by ring
    rw [h''] at h'
    exact h'
  have h1 : S_sum < 2 * m * ccard := by
    have h5 : ∑ c ∈ S_k, f c < ∑ c ∈ S_k, (2 * (2 ^ k)) := by
      apply Finset.sum_lt_sum_of_nonempty h_Sk_nonempty
      intro c hc
      have h6 : f c < 2 ^ (k + 1) := (h_dyadic c hc).2
      have h7 : 2 ^ (k + 1) = 2 * (2 ^ k) := by simp [pow_succ] <;> ring
      rw [h7] at h6
      exact h6
    have h5' : (∑ c ∈ S_k, f c : ℝ) < (∑ c ∈ S_k, (2 * (2 ^ k)) : ℝ) := by exact_mod_cast h5
    have h6 : (∑ c ∈ S_k, (2 * (2 ^ k)) : ℝ) = ccard * (2 * m) := by
      simp [hc_def, hm_def, Finset.sum_const] <;> ring
    rw [h6] at h5'
    have h7 : ccard * (2 * m) = 2 * m * ccard := by ring
    rw [h7] at h5'
    exact h5'
  have h16 : (M : ℝ) / (4 * K1r) < 2 * m * ccard := by linarith
  have h17 : (M : ℝ) / (8 * K1r) ≤ m * ccard := by
    have h16 : (M : ℝ) / (4 * K1r) < 2 * m * ccard := by linarith
    have h171 : 0 < K1r := hK1_pos'
    have h172 : 0 < m := by positivity
    have h173 : 0 < ccard := by positivity
    have h174 : (M : ℝ) / (8 * K1r) < m * ccard := by
      calc
        (M : ℝ) / (8 * K1r)
          = ((M : ℝ) / (4 * K1r)) / 2 := by ring
        _ < (2 * m * ccard) / 2 := by gcongr
        _ = m * ccard := by ring
    exact le_of_lt h174
  have h_mass_lower : (M : ℝ) / (8 * (K1 : ℝ)) ≤ ↑(2 ^ k) * ↑(S_k.card) := by
    have h_K1r_eq : K1r = (K1 : ℝ) := by simp [K1r] <;> rfl
    have h_eq2 : m * ccard = (↑(2 ^ k) : ℝ) * (↑(S_k.card) : ℝ) := by
      simp [hm_def, hc_def] <;> rfl
    have h17' : (M : ℝ) / (8 * (K1 : ℝ)) ≤ m * ccard := by
      rw [show (8 * (K1 : ℝ)) = (8 * K1r) by rw [h_K1r_eq]]
      exact h17
    rw [h_eq2] at h17'
    exact h17'
  have h_dyadic' : ∀ c ∈ S_k, 2 ^ k ≤ f c ∧ f c < 2 * (2 ^ k) := by
    intro c hc
    have h := h_dyadic c hc
    have h_eq : 2 ^ (k + 1) = 2 * (2 ^ k) := by simp [pow_succ] <;> ring
    have h_upper : f c < 2 * (2 ^ k) := by
      rw [h_eq] at h
      exact h.2
    exact ⟨h.1, h_upper⟩
  let m1 : ℕ := 2 ^ k
  let C_p : Finset L := S_k
  have h_pow_conv : ((2 : ℝ) ^ k) = (m1 : ℝ) := by
    simp [m1] <;> norm_cast
  have h_K1r_eq : K1r = (K1 : ℝ) := by simp [K1r]
  have h_mass_lower_final : (M : ℝ) / (8 * (K1 : ℝ)) ≤ (m1 : ℝ) * (C_p.card : ℝ) := by
    have h : (M : ℝ) / (8 * K1r) ≤ (2 : ℝ) ^ k * (S_k.card : ℝ) := h_mass_lower
    rw [h_K1r_eq, h_pow_conv] at h
    exact h
  have h_mass_upper_final : (m1 : ℝ) * (C_p.card : ℝ) ≤ (M : ℝ) := by
    have h : (2 : ℝ) ^ k * (S_k.card : ℝ) ≤ (M : ℝ) := h_mass_upper
    rw [h_pow_conv] at h
    exact h
  have hk_bounds : k_min ≤ k ∧ k ≤ k_max := Finset.mem_Icc.mp hk_layer
  exact ⟨C_p, m1, k, hS_sub, h_dyadic', h_mass_lower_final, h_mass_upper_final, rfl, hk_bounds.1, hk_bounds.2⟩

/-- First pigeonhole: per-p uniformization over coarse centers.

For each `p ∈ P`, finds `C_p p ⊆ coarseRange` and `m1 p : ℕ` such that:
- All assigned counts for `c ∈ C_p p` lie in `[m1 p, 2 * m1 p)`.
- `M / (8 * K1) ≤ m1 p * |C_p p| ≤ M`.
- `K1 = Nat.log 2 |coarseRange| + 4` depends only on the coarse net size.
-/
lemma first_pigeonhole {α L : Type*} [DecidableEq α] [DecidableEq L]
    {M : ℕ}
    (P : Finset α) (U : Finset L) (T : α → Finset L)
    (coarse : L → L) (coarseRange : Finset L)
    (hM_pos : 0 < M)
    (hT_card : ∀ p ∈ P, M / 2 < (T p).card)
    (hT_le : ∀ p ∈ P, (T p).card ≤ M)
    (hT_sub : ∀ p ∈ P, T p ⊆ U)
    (h_coarse_in : ∀ ℓ ∈ U, coarse ℓ ∈ coarseRange) :
    ∃ (K1 : ℕ) (C_p : α → Finset L) (m1 : α → ℕ) (M1_vals : Finset ℕ),
      (K1 = Nat.log 2 coarseRange.card + 4) ∧
      M1_vals.card ≤ K1 ∧
      (∀ p ∈ P, m1 p ∈ M1_vals) ∧
      (∀ p ∈ P, C_p p ⊆ coarseRange) ∧
      (∀ p ∈ P, ∀ c ∈ C_p p,
        m1 p ≤ assignedCount coarse T p c ∧ assignedCount coarse T p c < 2 * m1 p) ∧
      (∀ p ∈ P, (M : ℝ) / (8 * (K1 : ℝ)) ≤
        (m1 p : ℝ) * ((C_p p).card : ℝ)) ∧
      (∀ p ∈ P, (m1 p : ℝ) * ((C_p p).card : ℝ) ≤ (M : ℝ)) ∧
      (∀ p ∈ P, ∃ k : ℕ, m1 p = 2 ^ k) := by
  let N := coarseRange.card
  let K1 := Nat.log 2 N + 4
  by_cases hP : P = ∅
  · refine ⟨K1, fun _ => ∅, fun _ => 0, (∅ : Finset ℕ), by rfl, ?_⟩
    simp [hP]
  · have hP_nonempty : P.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty] <;> exact hP
    have hN_pos : 0 < N := by
      rcases hP_nonempty with ⟨p, hp⟩
      have hTp_pos : 0 < (T p).card := by
        have h : M / 2 < (T p).card := hT_card p hp
        omega
      have hTp_nonempty : (T p).Nonempty := Finset.card_pos.mp hTp_pos
      rcases hTp_nonempty with ⟨ℓ, hℓ⟩
      have hℓU : ℓ ∈ U := hT_sub p hp hℓ
      have h : coarse ℓ ∈ coarseRange := h_coarse_in ℓ hℓU
      exact Finset.card_pos.mpr ⟨coarse ℓ, h⟩
    have h_main : ∀ (p : α), p ∈ P → ∃ (C : Finset L) (m : ℕ) (k : ℕ),
        C ⊆ coarseRange ∧
        (∀ c ∈ C, m ≤ assignedCount coarse T p c ∧ assignedCount coarse T p c < 2 * m) ∧
        ((M : ℝ) / (8 * (K1 : ℝ)) ≤ (m : ℝ) * (C.card : ℝ)) ∧
        ((m : ℝ) * (C.card : ℝ) ≤ (M : ℝ)) ∧
        m = 2 ^ k ∧
        Nat.log 2 (M / (4 * N) + 1) ≤ k ∧ k ≤ Nat.log 2 M := by
      intro p hp
      exact first_pigeonhole_single U T coarse coarseRange
        hM_pos (hT_card p hp) (hT_le p hp) (hT_sub p hp) h_coarse_in hN_pos K1 rfl
    let chooseC (p : α) (hp : p ∈ P) : Finset L :=
      Classical.choose (h_main p hp)
    let chooseM (p : α) (hp : p ∈ P) : ℕ :=
      Classical.choose (Classical.choose_spec (h_main p hp))
    let chooseK (p : α) (hp : p ∈ P) : ℕ :=
      Classical.choose (Classical.choose_spec (Classical.choose_spec (h_main p hp)))
    let chooseSpec (p : α) (hp : p ∈ P) :=
      Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (h_main p hp)))
    let C_p_raw : α → Finset L := fun p =>
      if h : p ∈ P then chooseC p h else ∅
    let m1_raw : α → ℕ := fun p =>
      if h : p ∈ P then chooseM p h else 0
    have h_spec : ∀ (p : α), ∀ (hp : p ∈ P),
        (C_p_raw p ⊆ coarseRange) ∧
        (∀ c ∈ C_p_raw p, m1_raw p ≤ assignedCount coarse T p c ∧
          assignedCount coarse T p c < 2 * m1_raw p) ∧
        ((M : ℝ) / (8 * (K1 : ℝ)) ≤ (m1_raw p : ℝ) * ((C_p_raw p).card : ℝ)) ∧
        ((m1_raw p : ℝ) * ((C_p_raw p).card : ℝ) ≤ (M : ℝ)) ∧
        (∃ k : ℕ, m1_raw p = 2 ^ k ∧
          Nat.log 2 (M / (4 * N) + 1) ≤ k ∧ k ≤ Nat.log 2 M) := by
      intro p hp
      have h5 : (chooseC p hp ⊆ coarseRange) ∧
          (∀ c ∈ chooseC p hp, chooseM p hp ≤ assignedCount coarse T p c ∧
            assignedCount coarse T p c < 2 * chooseM p hp) ∧
          ((M : ℝ) / (8 * (K1 : ℝ)) ≤ (chooseM p hp : ℝ) * ((chooseC p hp).card : ℝ)) ∧
          ((chooseM p hp : ℝ) * ((chooseC p hp).card : ℝ) ≤ (M : ℝ)) ∧
          (chooseM p hp = 2 ^ chooseK p hp) ∧
          (Nat.log 2 (M / (4 * N) + 1) ≤ chooseK p hp ∧ chooseK p hp ≤ Nat.log 2 M) :=
        chooseSpec p hp
      have hC : C_p_raw p = chooseC p hp := by
        simp [C_p_raw, hp]
      have hM : m1_raw p = chooseM p hp := by
        simp [m1_raw, hp]
      rw [hC, hM]
      exact ⟨h5.1, h5.2.1, h5.2.2.1, h5.2.2.2.1,
        ⟨chooseK p hp, h5.2.2.2.2.1, h5.2.2.2.2.2⟩⟩
    have h1 : ∀ p ∈ P, C_p_raw p ⊆ coarseRange := by
      intro p hp
      exact (h_spec p hp).1
    have h2 : ∀ p ∈ P, ∀ c ∈ C_p_raw p,
        m1_raw p ≤ assignedCount coarse T p c ∧ assignedCount coarse T p c < 2 * m1_raw p := by
      intro p hp
      exact (h_spec p hp).2.1
    have h3 : ∀ p ∈ P, (M : ℝ) / (8 * (K1 : ℝ)) ≤
        (m1_raw p : ℝ) * ((C_p_raw p).card : ℝ) := by
      intro p hp
      exact (h_spec p hp).2.2.1
    have h4 : ∀ p ∈ P, (m1_raw p : ℝ) * ((C_p_raw p).card : ℝ) ≤ (M : ℝ) := by
      intro p hp
      exact (h_spec p hp).2.2.2.1
    have h5 : ∀ p ∈ P, ∃ k : ℕ, m1_raw p = 2 ^ k ∧
        Nat.log 2 (M / (4 * N) + 1) ≤ k ∧ k ≤ Nat.log 2 M := by
      intro p hp
      exact (h_spec p hp).2.2.2.2
    let k_min : ℕ := Nat.log 2 (M / (4 * N) + 1)
    let k_max : ℕ := Nat.log 2 M
    let M1_vals : Finset ℕ := Finset.image (fun k : ℕ => 2 ^ k) (Finset.Icc k_min k_max)
    have h_k_bound : k_max + 1 - k_min ≤ K1 := by
      have h4N_pos : 0 < 4 * N := by omega
      have h1 : M / (4 * N) < M / (4 * N) + 1 := by omega
      have hM_lt : M < (M / (4 * N) + 1) * (4 * N) :=
        (Nat.div_lt_iff_lt_mul h4N_pos).mp h1
      have hM_lt' : M < 4 * N * (M / (4 * N) + 1) := by
        have h3 : (M / (4 * N) + 1) * (4 * N) = 4 * N * (M / (4 * N) + 1) := by ring
        rw [h3] at hM_lt
        exact hM_lt
      let j := Nat.log 2 N
      have hj1 : 2 ^ j ≤ N := Nat.pow_log_le_self 2 hN_pos.ne'
      have hj2 : N < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
      have h4 : 2 ^ k_max ≤ M := Nat.pow_log_le_self 2 hM_pos.ne'
      have h5 : M / (4 * N) + 1 < 2 ^ (k_min + 1) := Nat.lt_pow_succ_log_self (by norm_num) (M / (4 * N) + 1)
      have h6 : M < 2 ^ (j + k_min + 4) := by
        calc
          M < 4 * N * (M / (4 * N) + 1) := hM_lt'
          _ < 4 * (2 ^ (j + 1)) * (M / (4 * N) + 1) := by gcongr <;> linarith
          _ = 2 ^ (j + 3) * (M / (4 * N) + 1) := by ring_nf
          _ < 2 ^ (j + 3) * (2 ^ (k_min + 1)) := by gcongr
          _ = 2 ^ (j + k_min + 4) := by ring_nf
      have h7 : 2 ^ k_max < 2 ^ (j + k_min + 4) := lt_of_le_of_lt h4 h6
      have h8 : k_max < j + k_min + 4 := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h7
      have h9 : k_max + 1 - k_min ≤ j + 4 := by omega
      have h10 : j + 4 = K1 := by
        have h11 : j = Nat.log 2 N := by rfl
        rw [h11] <;> ring
      rw [h10] at h9
      exact h9
    have hM1_card : M1_vals.card ≤ K1 := by
      have h1 : M1_vals.card ≤ (Finset.Icc k_min k_max).card := Finset.card_image_le
      have h2 : (Finset.Icc k_min k_max).card = k_max + 1 - k_min := by
        simp [Finset.Icc_eq_empty_of_lt] <;> omega
      rw [h2] at h1
      exact h1.trans h_k_bound
    have hM1_mem : ∀ p ∈ P, m1_raw p ∈ M1_vals := by
      intro p hp
      rcases h5 p hp with ⟨k, hk_eq, hk_min, hk_max⟩
      have hk_in : k ∈ Finset.Icc k_min k_max := Finset.mem_Icc.mpr ⟨hk_min, hk_max⟩
      have h : 2 ^ k ∈ M1_vals := Finset.mem_image_of_mem _ hk_in
      rw [hk_eq]
      exact h
    refine ⟨K1, C_p_raw, m1_raw, M1_vals, by rfl, ?_⟩
    exact ⟨hM1_card, hM1_mem, h1, h2, h3, h4, fun p hp => (h5 p hp).imp (fun k hk => hk.1)⟩

/-! ==========================================================================
   3. General finite pigeonhole
   ========================================================================== -/

/-- General finite pigeonhole: if `f : α → β` maps a finset `P` into a finset
`Q` of cardinality `K`, then some fiber has size at least `|P| / K`. -/
lemma finset_pigeonhole {α β : Type*} [DecidableEq α] [DecidableEq β]
    {P : Finset α} {Q : Finset β} {f : α → β}
    (hP_nonempty : P.Nonempty)
    (h_maps_to : ∀ x ∈ P, f x ∈ Q) :
    ∃ b ∈ Q, (P.card : ℝ) ≤ (Q.card : ℝ) * ((P.filter (fun x => f x = b)).card : ℝ) := by
  have h_cover : P ⊆ Q.biUnion (fun b => P.filter (fun x => f x = b)) := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨f x, h_maps_to x hx,
      Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
  have h_card : P.card ≤ ∑ b ∈ Q, (P.filter (fun x => f x = b)).card :=
    (Finset.card_le_card h_cover).trans Finset.card_biUnion_le
  by_cases hQ : Q.card = 0
  · have hQ_empty : Q = ∅ := Finset.card_eq_zero.mp hQ
    rw [hQ_empty] at h_maps_to
    have hP_empty : P = ∅ := by
      ext x
      simp
      intro hx
      have h_cont : f x ∈ (∅ : Finset β) := h_maps_to x hx
      simpa using h_cont
    exfalso
    exact hP_nonempty.ne_empty hP_empty
  · have hQ_pos : 0 < (Q.card : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hQ)
    have hQ_nonempty : Q.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hQ)
    by_contra h
    push Not at h
    have h' : ∀ b ∈ Q, (Q.card : ℝ) * ((P.filter (fun x => f x = b)).card : ℝ) < (P.card : ℝ) := h
    have h_sum : (∑ b ∈ Q, ((P.filter (fun x => f x = b)).card : ℝ)) < (P.card : ℝ) := by
      calc
        (∑ b ∈ Q, ((P.filter (fun x => f x = b)).card : ℝ))
          < ∑ _b ∈ Q, (P.card : ℝ) / (Q.card : ℝ) := by
            apply Finset.sum_lt_sum_of_nonempty hQ_nonempty
            intro b hb
            have h4 := h' b hb
            have h5 : ((P.filter (fun x => f x = b)).card : ℝ) < (P.card : ℝ) / (Q.card : ℝ) := by
              calc
                ((P.filter (fun x => f x = b)).card : ℝ)
                  = ((Q.card : ℝ) * ((P.filter (fun x => f x = b)).card : ℝ)) / (Q.card : ℝ) := by field_simp [hQ_pos.ne'] <;> ring
                _ < (P.card : ℝ) / (Q.card : ℝ) := by gcongr
            exact h5
        _ = (P.card : ℝ) := by
          simp [Finset.sum_const, hQ_pos.ne'] <;> field_simp <;> ring
    have h6 : (P.card : ℝ) ≤ (∑ b ∈ Q, ((P.filter (fun x => f x = b)).card : ℝ)) := by
      have h7 : P.card ≤ ∑ b ∈ Q, (P.filter (fun x => f x = b)).card := h_card
      have h8 : (P.card : ℝ) ≤ ↑(∑ b ∈ Q, (P.filter (fun x => f x = b)).card) := by exact_mod_cast h7
      have h9 : (↑(∑ b ∈ Q, (P.filter (fun x => f x = b)).card) : ℝ) = ∑ b ∈ Q, ((P.filter (fun x => f x = b)).card : ℝ) := by
        rw [Nat.cast_sum]
      rw [h9] at h8
      exact h8
    exact not_le.mpr h_sum h6

/-! ==========================================================================
   4. Second pigeonhole (uniformize over P)
   ========================================================================== -/

/-- Second pigeonhole: find `P' ⊆ P` and fixed `m1, m2` such that for all
`p ∈ P'`, `m1 ≤ m1_p p < 2*m1` and `m2 ≤ |C_p p| < 2*m2`. -/
lemma second_pigeonhole {α L : Type*} [DecidableEq α] [DecidableEq L]
    {M K1 N : ℕ}
    (P : Finset α)
    (C_p : α → Finset L)
    (m1_p : α → ℕ)
    (hM_pos : 0 < M)
    (hK1_pos : 0 < K1)
    (hP_nonempty : P.Nonempty)
    (h_m1_range : ∃ (M1_vals : Finset ℕ),
        M1_vals.card ≤ K1 ∧ ∀ p ∈ P, m1_p p ∈ M1_vals)
    (h_Cp_le_N : ∀ p ∈ P, (C_p p).card ≤ N)
    (h_K1_ge_log : Nat.log 2 N + 1 ≤ K1)
    (h_mass_lower : ∀ p ∈ P,
        (M : ℝ) / (8 * (K1 : ℝ)) ≤ (m1_p p : ℝ) * ((C_p p).card : ℝ))
    (h_mass_upper : ∀ p ∈ P,
        (m1_p p : ℝ) * ((C_p p).card : ℝ) ≤ (M : ℝ)) :
    ∃ (P' : Finset α) (m1 m2 : ℕ),
      P' ⊆ P ∧
      (P.card : ℝ) ≤ (K1 : ℝ)^2 * (P'.card : ℝ) ∧
      (∀ p ∈ P', m1 ≤ m1_p p ∧ m1_p p < 2 * m1) ∧
      (∀ p ∈ P', m2 ≤ (C_p p).card ∧ (C_p p).card < 2 * m2) ∧
      (M : ℝ) / (32 * (K1 : ℝ)) ≤ (m1 : ℝ) * (m2 : ℝ) ∧
      (m1 : ℝ) * (m2 : ℝ) ≤ (M : ℝ) := by
  rcases h_m1_range with ⟨M1_vals, hM1_card, hM1_mem⟩
  let j : α → ℕ := fun p => Nat.log 2 (C_p p).card
  let J_vals := Finset.range K1
  have h_j_in : ∀ p ∈ P, j p ∈ J_vals := by
    intro p hp
    have h1 : (C_p p).card ≤ N := h_Cp_le_N p hp
    have h2 : j p ≤ Nat.log 2 N := by
      simpa [j] using Nat.log_mono_right h1
    have h3 : j p < K1 := by omega
    exact Finset.mem_range.mpr h3
  let Q := M1_vals ×ˢ J_vals
  have hQ_card : Q.card ≤ K1^2 := by
    calc
      Q.card = M1_vals.card * J_vals.card := by rw [Finset.card_product]
      _ ≤ K1 * K1 := by gcongr <;> simp [J_vals]
      _ = K1^2 := by ring
  let f : α → ℕ × ℕ := fun p => (m1_p p, j p)
  have h_maps : ∀ p ∈ P, f p ∈ Q := by
    intro p hp
    exact Finset.mem_product.mpr ⟨hM1_mem p hp, h_j_in p hp⟩
  rcases finset_pigeonhole hP_nonempty h_maps with ⟨⟨m1, j0⟩, hpr_in, h_ineq⟩
  let P' := P.filter (fun p => f p = (m1, j0))
  let m2 := 2^j0
  have hP'_sub : P' ⊆ P := Finset.filter_subset _ _
  have h_card_bound : (P.card : ℝ) ≤ (K1 : ℝ)^2 * (P'.card : ℝ) := by
    have h1 : (P.card : ℝ) ≤ (Q.card : ℝ) * (P'.card : ℝ) := by
      simpa [P', f] using h_ineq
    have h2 : (Q.card : ℝ) ≤ (K1 : ℝ)^2 := by exact_mod_cast hQ_card
    calc
      (P.card : ℝ) ≤ (Q.card : ℝ) * (P'.card : ℝ) := h1
      _ ≤ (K1 : ℝ)^2 * (P'.card : ℝ) := by gcongr
  have hP'_nonempty : P'.Nonempty := by
    by_contra h
    have h_empty : P' = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have h_pos : 0 < (P.card : ℝ) := by exact_mod_cast hP_nonempty.card_pos
    rw [h_empty] at h_card_bound
    have h_cont : (P.card : ℝ) ≤ 0 := by
      simpa [Finset.card_empty] using h_card_bound
    linarith
  have h_m1_eq : ∀ p ∈ P', m1_p p = m1 := by
    intro p hp
    have h : f p = (m1, j0) := (Finset.mem_filter.mp hp).2
    exact congr_arg Prod.fst h
  have h_j_eq : ∀ p ∈ P', j p = j0 := by
    intro p hp
    have h : f p = (m1, j0) := (Finset.mem_filter.mp hp).2
    exact congr_arg Prod.snd h
  have hm1_pos : 0 < m1 := by
    rcases hP'_nonempty with ⟨p, hp⟩
    have h_pos1 : (0 : ℝ) < (M : ℝ) / (8 * (K1 : ℝ)) := by positivity
    have h_pos2 : (M : ℝ) / (8 * (K1 : ℝ)) ≤ (m1_p p : ℝ) * ((C_p p).card : ℝ) :=
      h_mass_lower p (hP'_sub hp)
    have h_pos3 : 0 < (m1_p p : ℝ) * ((C_p p).card : ℝ) := by linarith
    have h_pos4 : 0 < m1_p p := by
      by_contra h5
      have h6 : m1_p p = 0 := by omega
      rw [h6] at h_pos3 <;> simp at h_pos3
    have h_eq : m1_p p = m1 := h_m1_eq p hp
    rw [h_eq] at h_pos4
    exact h_pos4
  have h_m1_range : ∀ p ∈ P', m1 ≤ m1_p p ∧ m1_p p < 2 * m1 := by
    intro p hp
    have h_eq : m1_p p = m1 := h_m1_eq p hp
    constructor
    · rw [h_eq] <;> linarith
    · rw [h_eq] <;> linarith [hm1_pos]
  have h_m2_range : ∀ p ∈ P', m2 ≤ (C_p p).card ∧ (C_p p).card < 2 * m2 := by
    intro p hp
    have h_eq : j p = j0 := h_j_eq p hp
    have h_pos : 0 < (C_p p).card := by
      have h_mass : (M : ℝ) / (8 * (K1 : ℝ)) ≤ (m1_p p : ℝ) * ((C_p p).card : ℝ) :=
        h_mass_lower p (hP'_sub hp)
      have h_pos1 : (0 : ℝ) < (M : ℝ) / (8 * (K1 : ℝ)) := by positivity
      have h_pos2 : 0 < (m1_p p : ℝ) * ((C_p p).card : ℝ) := by linarith
      have h : 0 < (C_p p).card := by
        by_contra h'
        have h'' : (C_p p).card = 0 := by omega
        rw [h''] at h_pos2 <;> simp at h_pos2
      exact h
    have h1 : 2 ^ (j p) ≤ (C_p p).card := Nat.pow_log_le_self 2 h_pos.ne'
    have h2 : (C_p p).card < 2 ^ (j p + 1) := Nat.lt_pow_succ_log_self (by norm_num) ((C_p p).card)
    rw [h_eq] at h1 h2
    have h3 : 2 ^ (j0 + 1) = 2 * m2 := by
      simp [m2, pow_succ] <;> ring
    exact ⟨h1, by rw [h3] at h2; exact h2⟩
  have h_mass_lower2 : (M : ℝ) / (32 * (K1 : ℝ)) ≤ (m1 : ℝ) * (m2 : ℝ) := by
    rcases hP'_nonempty with ⟨p, hp⟩
    have h1 : m1_p p = m1 := h_m1_eq p hp
    have h2 : (C_p p).card < 2 * m2 := (h_m2_range p hp).2
    have h3 : (M : ℝ) / (8 * (K1 : ℝ)) ≤ (m1_p p : ℝ) * ((C_p p).card : ℝ) :=
      h_mass_lower p (hP'_sub hp)
    have h4 : (m1 : ℝ) * ((C_p p).card : ℝ) ≥ (M : ℝ) / (8 * (K1 : ℝ)) := by
      have h5 : (m1_p p : ℝ) = (m1 : ℝ) := by exact_mod_cast h1
      rw [h5] at h3
      exact h3
    have h6 : ((C_p p).card : ℝ) < 2 * (m2 : ℝ) := by exact_mod_cast h2
    have h7 : (m1 : ℝ) * ((C_p p).card : ℝ) < (m1 : ℝ) * (2 * (m2 : ℝ)) := by
      exact mul_lt_mul_of_pos_left h6 (by exact_mod_cast hm1_pos)
    have h8 : (M : ℝ) / (8 * (K1 : ℝ)) < 2 * (m1 : ℝ) * (m2 : ℝ) := by
      calc
        (M : ℝ) / (8 * (K1 : ℝ)) ≤ (m1 : ℝ) * ((C_p p).card : ℝ) := h4
        _ < (m1 : ℝ) * (2 * (m2 : ℝ)) := h7
        _ = 2 * (m1 : ℝ) * (m2 : ℝ) := by ring
    have h9 : (M : ℝ) / (16 * (K1 : ℝ)) < (m1 : ℝ) * (m2 : ℝ) := by
      have h10 : (M : ℝ) / (8 * (K1 : ℝ)) = 2 * ((M : ℝ) / (16 * (K1 : ℝ))) := by
        field_simp [hK1_pos.ne'] <;> ring
      rw [h10] at h8
      linarith
    have h11 : (M : ℝ) / (32 * (K1 : ℝ)) ≤ (M : ℝ) / (16 * (K1 : ℝ)) := by
      have hK1_pos' : 0 < (K1 : ℝ) := by exact_mod_cast hK1_pos
      have hM_pos' : 0 ≤ (M : ℝ) := by exact_mod_cast hM_pos.le
      gcongr <;> norm_num
    exact h11.trans h9.le
  have h_mass_upper2 : (m1 : ℝ) * (m2 : ℝ) ≤ (M : ℝ) := by
    rcases hP'_nonempty with ⟨p, hp⟩
    have h1 : m1 ≤ m1_p p := (h_m1_range p hp).1
    have h2 : m2 ≤ (C_p p).card := (h_m2_range p hp).1
    have h3 : (m1_p p : ℝ) * ((C_p p).card : ℝ) ≤ (M : ℝ) :=
      h_mass_upper p (hP'_sub hp)
    have h41 : (m1 : ℝ) ≤ (m1_p p : ℝ) := by exact_mod_cast h1
    have h42 : (m2 : ℝ) ≤ ((C_p p).card : ℝ) := by exact_mod_cast h2
    have h4 : (m1 : ℝ) * (m2 : ℝ) ≤ (m1_p p : ℝ) * ((C_p p).card : ℝ) := by
      gcongr
    exact h4.trans h3
  exact ⟨P', m1, m2, hP'_sub, h_card_bound, h_m1_range, h_m2_range, h_mass_lower2, h_mass_upper2⟩

/-! ==========================================================================
   5. Third pigeonhole (uniformize over coarse centers)
   ========================================================================== -/

/-- Third pigeonhole: find `C' ⊆ coarseRange` and `j` such that all `c ∈ C'`
have incidence count `n(c) ∈ [2^j, 2^(j+1))`, and
`2^j * |C'| ≥ m2 * |P'| / (4 * K1)`. -/
lemma third_pigeonhole {α L : Type*} [DecidableEq α] [DecidableEq L]
    {m2 K1 N : ℕ}
    (P' : Finset α)
    (C_p : α → Finset L)
    (coarseRange : Finset L)
    (hK1_pos : 0 < K1)
    (hN_pos : 0 < N)
    (hm2_pos : 0 < m2)
    (hP'_nonempty : P'.Nonempty)
    (hCp_sub : ∀ p ∈ P', C_p p ⊆ coarseRange)
    (hCp_size_lower : ∀ p ∈ P', m2 ≤ (C_p p).card)
    (h_coarseRange_card : coarseRange.card = N)
    (h_K1_ge : Nat.log 2 N + 4 ≤ K1) :
    ∃ (C' : Finset L) (j : ℕ),
      C' ⊆ coarseRange ∧
      (∀ c ∈ C',
        2^j ≤ (P'.filter (fun p => c ∈ C_p p)).card ∧
        (P'.filter (fun p => c ∈ C_p p)).card < 2^(j+1)) ∧
      (2^j : ℝ) * (C'.card : ℝ) ≥
        (m2 : ℝ) * (P'.card : ℝ) / (4 * (K1 : ℝ)) := by
  let n : L → ℕ := fun c => (P'.filter (fun p => c ∈ C_p p)).card
  have h_total_eq : ∑ c ∈ coarseRange, n c = ∑ p ∈ P', (C_p p).card := by
    have h1 : ∑ c ∈ coarseRange, n c = ∑ c ∈ coarseRange, ∑ p ∈ P', if c ∈ C_p p then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_ite] <;> simp [n] <;> rfl
    rw [h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    have h2 : C_p p ⊆ coarseRange := hCp_sub p hp
    have h3 : ∑ c ∈ coarseRange, (if c ∈ C_p p then 1 else 0) = (C_p p).card := by
      have h31 : ∑ c ∈ coarseRange, (if c ∈ C_p p then 1 else 0) = (coarseRange.filter (fun c => c ∈ C_p p)).card := by
        rw [Finset.sum_ite] <;> simp
      rw [h31]
      have h32 : coarseRange.filter (fun c => c ∈ C_p p) = C_p p := by
        ext x
        simp [h2]
        <;> tauto
      rw [h32]
    exact h3
  have h_total_lower : ∑ c ∈ coarseRange, n c ≥ m2 * P'.card := by
    rw [h_total_eq]
    have h : ∀ p ∈ P', m2 ≤ (C_p p).card := hCp_size_lower
    have h_sum : ∑ p ∈ P', (C_p p).card ≥ ∑ p ∈ P', m2 := Finset.sum_le_sum h
    have h_sum2 : ∑ p ∈ P', m2 = P'.card * m2 := by simp [Finset.sum_const] <;> ring
    have h_comm : P'.card * m2 = m2 * P'.card := by ring
    rw [h_sum2, h_comm] at h_sum
    exact h_sum
  let t : ℕ := m2 * P'.card / (4 * N)
  let low := coarseRange.filter (fun c => n c ≤ t)
  let high := coarseRange.filter (fun c => t < n c)
  have h_partition1 : low ∪ high = coarseRange := by
    ext c
    simp [low, high] <;> by_cases h : n c ≤ t <;> simp [h] <;> omega
  have h_partition2 : Disjoint low high := by
    simp [low, high, Finset.disjoint_left] <;> omega
  have h_sum_low : ∑ c ∈ low, n c ≤ N * t := by
    calc
      ∑ c ∈ low, n c ≤ ∑ c ∈ low, t := Finset.sum_le_sum (fun c hc =>
        (Finset.mem_filter.mp hc).2)
      _ = low.card * t := by simp [Finset.sum_const]
      _ ≤ N * t := by
        have h4 : low.card ≤ coarseRange.card := Finset.card_le_card (Finset.filter_subset _ _)
        rw [h_coarseRange_card] at h4
        exact mul_le_mul_right' h4 t
  have h4N_pos : 0 < 4 * N := by positivity
  have h_Nt_le : N * t ≤ m2 * P'.card / 4 := by
    have h1 : (4 * N) * t ≤ m2 * P'.card := Nat.mul_div_le (m2 * P'.card) (4 * N)
    have h2 : 4 * (N * t) ≤ m2 * P'.card := by
      have h3 : 4 * (N * t) = (4 * N) * t := by ring
      rw [h3]; exact h1
    have h4 : N * t ≤ m2 * P'.card / 4 := by
      omega
    exact h4
  have h_sum_high_pos : 0 < ∑ c ∈ high, n c := by
    have h_eq : (∑ c ∈ low, n c) + (∑ c ∈ high, n c) = ∑ c ∈ coarseRange, n c := by
      rw [← Finset.sum_union h_partition2, h_partition1]
    have h4 : (∑ c ∈ low, n c : ℝ) ≤ (m2 * P'.card : ℝ) / 4 := by
      have h41 : (∑ c ∈ low, n c : ℝ) ≤ (N * t : ℝ) := by exact_mod_cast h_sum_low
      have h42 : (N * t : ℝ) ≤ ((m2 * P'.card / 4 : ℕ) : ℝ) := by exact_mod_cast h_Nt_le
      have h43 : ((m2 * P'.card / 4 : ℕ) : ℝ) ≤ (m2 * P'.card : ℝ) / 4 := by
        have hdiv : 4 * ((m2 * P'.card / 4 : ℕ) : ℝ) ≤ (m2 * P'.card : ℝ) := by
          exact_mod_cast Nat.mul_div_le (m2 * P'.card) 4
        linarith
      calc
        (∑ c ∈ low, n c : ℝ) ≤ (N * t : ℝ) := h41
        _ ≤ ((m2 * P'.card / 4 : ℕ) : ℝ) := h42
        _ ≤ (m2 * P'.card : ℝ) / 4 := h43
    have h5 : (∑ c ∈ coarseRange, n c : ℝ) ≥ (m2 * P'.card : ℝ) := by
      exact_mod_cast h_total_lower
    have h6 : (∑ c ∈ high, n c : ℝ) > 0 := by
      have h_eq2 : (∑ c ∈ low, n c : ℝ) + (∑ c ∈ high, n c : ℝ) = (∑ c ∈ coarseRange, n c : ℝ) := by
        rw [← Finset.sum_union h_partition2, h_partition1]
      have h7 : (∑ c ∈ high, n c : ℝ) = (∑ c ∈ coarseRange, n c : ℝ) - (∑ c ∈ low, n c : ℝ) := by linarith
      rw [h7]
      have h_pos : 0 < (m2 * P'.card : ℝ) := by
        exact_mod_cast mul_pos hm2_pos hP'_nonempty.card_pos
      have h_goal : (∑ c ∈ coarseRange, n c : ℝ) - (∑ c ∈ low, n c : ℝ) > 0 := by
        calc
          (∑ c ∈ coarseRange, n c : ℝ) - (∑ c ∈ low, n c : ℝ)
            ≥ (m2 * P'.card : ℝ) - (m2 * P'.card : ℝ) / 4 := by gcongr
          _ = (3 : ℝ) / 4 * (m2 * P'.card : ℝ) := by ring
          _ > 0 := by positivity
      exact h_goal
    exact_mod_cast h6
  let k_min := Nat.log 2 (t + 1)
  let k_max := Nat.log 2 P'.card
  have h_bound1 : ∀ c ∈ high, 2 ^ k_min ≤ n c := by
    intro c hc
    have hft : t < n c := (Finset.mem_filter.mp hc).2
    have h : t + 1 ≤ n c := by omega
    have h2 : 2 ^ k_min ≤ t + 1 := Nat.pow_log_le_self 2 (by positivity)
    linarith
  have h_bound2 : ∀ c ∈ high, n c < 2 ^ (k_max + 1) := by
    intro c hc
    have hfc_le : n c ≤ P'.card := by
      simp [n] <;> exact Finset.card_le_card (Finset.filter_subset _ _)
    have h3 : P'.card < 2 ^ (k_max + 1) := Nat.lt_pow_succ_log_self (by norm_num) P'.card
    linarith
  have h_k_bound : k_max + 1 - k_min ≤ K1 := by
    have hM_lt : P'.card < 4 * N * (t + 1) := by
      have h1 : 1 ≤ m2 := by omega
      have h2 : P'.card ≤ m2 * P'.card := by nlinarith
      have h4pos : 0 < 4 * N := by positivity
      have h5 : m2 * P'.card = 4 * N * t + (m2 * P'.card % (4 * N)) := by
        have h_div : 4 * N * (m2 * P'.card / (4 * N)) + (m2 * P'.card % (4 * N)) = m2 * P'.card :=
          Nat.div_add_mod (m2 * P'.card) (4 * N)
        have h_t : (m2 * P'.card / (4 * N)) = t := by rfl
        rw [h_t] at h_div
        ring_nf at h_div ⊢
        exact h_div.symm
      have h6 : m2 * P'.card % (4 * N) < 4 * N := Nat.mod_lt _ h4pos
      have h3 : m2 * P'.card < 4 * N * (t + 1) := by
        rw [h5]
        have h7 : 4 * N * t + (m2 * P'.card % (4 * N)) < 4 * N * t + 4 * N := by
          gcongr
        have h8 : 4 * N * t + 4 * N = 4 * N * (t + 1) := by ring
        rw [h8] at h7
        exact h7
      linarith
    have hN_log : ∃ j0 : ℕ, 2 ^ j0 ≤ N ∧ N < 2 ^ (j0 + 1) := by
      refine ⟨Nat.log 2 N, Nat.pow_log_le_self 2 hN_pos.ne', ?_⟩
      exact Nat.lt_pow_succ_log_self (by norm_num) N
    rcases hN_log with ⟨j0, hj1, hj2⟩
    have h4 : 2 ^ k_max ≤ P'.card := Nat.pow_log_le_self 2 hP'_nonempty.card_pos.ne'
    have h5 : t + 1 < 2 ^ (k_min + 1) := Nat.lt_pow_succ_log_self (by norm_num) (t + 1)
    have h6 : P'.card < 2 ^ (j0 + k_min + 4) := by
      calc
        P'.card < 4 * N * (t + 1) := hM_lt
        _ < 4 * (2 ^ (j0 + 1)) * (t + 1) := by gcongr <;> linarith
        _ = 2 ^ (j0 + 3) * (t + 1) := by ring_nf
        _ < 2 ^ (j0 + 3) * (2 ^ (k_min + 1)) := by gcongr
        _ = 2 ^ (j0 + k_min + 4) := by ring_nf
    have h7 : 2 ^ k_max < 2 ^ (j0 + k_min + 4) := lt_of_le_of_lt h4 h6
    have h8 : k_max < j0 + k_min + 4 := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h7
    have h9 : k_max + 1 - k_min ≤ j0 + 4 := by omega
    have h10 : j0 ≤ Nat.log 2 N := by
      have h101 : 2 ^ j0 ≤ N := hj1
      have h102 : Nat.log 2 (2 ^ j0) = j0 := by
        rw [Nat.log_pow] <;> simp <;> norm_num
      have h103 : Nat.log 2 (2 ^ j0) ≤ Nat.log 2 N := Nat.log_mono_right h101
      rw [h102] at h103
      exact h103
    have h11 : j0 + 4 ≤ Nat.log 2 N + 4 := by omega
    have h12 : Nat.log 2 N + 4 ≤ K1 := h_K1_ge
    have h13 : j0 + 4 ≤ K1 := by omega
    omega
  let layers := Finset.Icc k_min k_max
  let S : ℕ → Finset L := fun k =>
    high.filter (fun c => 2 ^ k ≤ n c ∧ n c < 2 ^ (k + 1))
  have h_layers_cover : ∀ c ∈ high, ∃ k ∈ layers, c ∈ S k := by
    intro c hc
    let k := Nat.log 2 (n c)
    have hft : t < n c := (Finset.mem_filter.mp hc).2
    have hnc_pos : 0 < n c := by linarith
    have hk1 : 2 ^ k ≤ n c := Nat.pow_log_le_self 2 hnc_pos.ne'
    have hk2 : n c < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) (n c)
    have hk_min : k_min ≤ k := by
      have h : t + 1 ≤ n c := by omega
      exact Nat.log_mono_right h
    have hk_max : k ≤ k_max := by
      have h : n c < 2 ^ (k_max + 1) := h_bound2 c hc
      have h'' : 2 ^ k ≤ n c := hk1
      have h''' : 2 ^ k < 2 ^ (k_max + 1) := lt_of_le_of_lt h'' h
      have : k < k_max + 1 := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h'''
      omega
    exact ⟨k, Finset.mem_Icc.mpr ⟨hk_min, hk_max⟩,
      Finset.mem_filter.mpr ⟨hc, ⟨hk1, hk2⟩⟩⟩
  have h_disj : ∀ k1 ∈ layers, ∀ k2 ∈ layers, k1 ≠ k2 → Disjoint (S k1) (S k2) := by
    intro k1 _ k2 _ hne
    simp only [S, Finset.disjoint_left]
    intro c ha1 ha2
    have h1 : 2 ^ k1 ≤ n c ∧ n c < 2 ^ (k1 + 1) := (Finset.mem_filter.mp ha1).2
    have h2 : 2 ^ k2 ≤ n c ∧ n c < 2 ^ (k2 + 1) := (Finset.mem_filter.mp ha2).2
    by_cases h : k1 < k2
    · have h5 : k1 + 1 ≤ k2 := by omega
      have h6 : 2 ^ (k1 + 1) ≤ 2 ^ k2 := by gcongr <;> norm_num
      linarith
    · have h' : k2 < k1 := by omega
      have h5 : k2 + 1 ≤ k1 := by omega
      have h6 : 2 ^ (k2 + 1) ≤ 2 ^ k1 := by gcongr <;> norm_num
      linarith
  have h_sum_layers : ∑ k ∈ layers, ∑ c ∈ S k, n c = ∑ c ∈ high, n c := by
    have h_union : (Finset.biUnion layers S) = high := by
      ext c
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨k, _, hk⟩
        exact (Finset.mem_filter.mp hk).1
      · intro hc
        exact h_layers_cover c hc
    have h : ∑ k ∈ layers, ∑ c ∈ S k, n c = ∑ c ∈ (Finset.biUnion layers S), n c :=
      (Finset.sum_biUnion h_disj).symm
    rw [h, h_union]
  let a : ℕ → ℕ := fun k => 2 ^ k * (S k).card
  have h_sum_high_le : (∑ c ∈ high, n c : ℝ) ≤ 2 * ∑ k ∈ layers, (a k : ℝ) := by
    have h1 : ∀ k ∈ layers, (∑ c ∈ S k, n c : ℝ) ≤ 2 * (a k : ℝ) := by
      intro k _
      have h2 : ∀ c ∈ S k, n c < 2 ^ (k + 1) := fun c hc =>
        (Finset.mem_filter.mp hc).2.2
      have h3 : (∑ c ∈ S k, n c : ℝ) ≤ ∑ c ∈ S k, (2 ^ (k + 1) : ℝ) := by
        apply Finset.sum_le_sum
        intro c hc
        have h4 : n c < 2 ^ (k + 1) := h2 c hc
        exact_mod_cast le_of_lt h4
      have h5 : ∑ c ∈ S k, (2 ^ (k + 1) : ℝ) = (2 ^ (k + 1) : ℝ) * (S k).card := by
        simp [Finset.sum_const] <;> ring
      rw [h5] at h3
      have h6 : (2 ^ (k + 1) : ℝ) * (S k).card = 2 * (a k : ℝ) := by
        simp [a, pow_succ] <;> ring
      rw [h6] at h3
      exact h3
    calc
      (∑ c ∈ high, n c : ℝ)
        = ∑ k ∈ layers, (∑ c ∈ S k, n c : ℝ) := by
          simpa [Nat.cast_sum] using congr_arg (fun x : ℕ => (x : ℝ)) h_sum_layers.symm
      _ ≤ ∑ k ∈ layers, 2 * (a k : ℝ) := Finset.sum_le_sum h1
      _ = 2 * ∑ k ∈ layers, (a k : ℝ) := by
        rw [Finset.mul_sum]
  have h_sum_a_lower : (3 : ℝ) / 8 * (m2 : ℝ) * (P'.card : ℝ) ≤ ∑ k ∈ layers, (a k : ℝ) := by
    have h1 : (∑ c ∈ high, n c : ℝ) ≥ (3 : ℝ) / 4 * (m2 : ℝ) * (P'.card : ℝ) := by
      have h2 : (∑ c ∈ low, n c : ℝ) ≤ (m2 : ℝ) * (P'.card : ℝ) / 4 := by
        have h21 : (∑ c ∈ low, n c : ℝ) ≤ (N * t : ℝ) := by exact_mod_cast h_sum_low
        have h22 : (N * t : ℝ) ≤ ↑(m2 * P'.card / 4) := by exact_mod_cast h_Nt_le
        have h23 : ↑(m2 * P'.card / 4) ≤ (m2 : ℝ) * (P'.card : ℝ) / 4 := by
          have hdiv : (4 : ℝ) * ↑(m2 * P'.card / 4) ≤ ↑(m2 * P'.card) := by
            exact_mod_cast Nat.mul_div_le (m2 * P'.card) 4
          have h_eq : ↑(m2 * P'.card) = (m2 : ℝ) * (P'.card : ℝ) := by
            simp [Nat.cast_mul] <;> ring
          have h : (4 : ℝ) * ↑(m2 * P'.card / 4) ≤ (m2 : ℝ) * (P'.card : ℝ) := by
            rw [h_eq] at hdiv
            exact hdiv
          calc
            ↑(m2 * P'.card / 4)
              = ((4 : ℝ) * ↑(m2 * P'.card / 4)) / 4 := by ring
            _ ≤ ((m2 : ℝ) * (P'.card : ℝ)) / 4 := by gcongr
        calc
          (∑ c ∈ low, n c : ℝ) ≤ (N * t : ℝ) := h21
          _ ≤ ↑(m2 * P'.card / 4) := h22
          _ ≤ (m2 : ℝ) * (P'.card : ℝ) / 4 := h23
      have h3 : (∑ c ∈ coarseRange, n c : ℝ) ≥ (m2 : ℝ) * (P'.card : ℝ) := by
        exact_mod_cast h_total_lower
      have h4 : (∑ c ∈ low, n c : ℝ) + (∑ c ∈ high, n c : ℝ) = (∑ c ∈ coarseRange, n c : ℝ) := by
        rw [← Finset.sum_union h_partition2, h_partition1]
      have h_sum_high_eq : (∑ c ∈ high, n c : ℝ) = (∑ c ∈ coarseRange, n c : ℝ) - (∑ c ∈ low, n c : ℝ) := by
        exact eq_sub_of_add_eq' h4
      rw [h_sum_high_eq]
      have h_goal : (∑ c ∈ coarseRange, n c : ℝ) - (∑ c ∈ low, n c : ℝ) ≥ (3 : ℝ) / 4 * (m2 : ℝ) * (P'.card : ℝ) := by
        calc
          (∑ c ∈ coarseRange, n c : ℝ) - (∑ c ∈ low, n c : ℝ)
            ≥ (m2 : ℝ) * (P'.card : ℝ) - (m2 : ℝ) * (P'.card : ℝ) / 4 := by gcongr
          _ = (3 : ℝ) / 4 * (m2 : ℝ) * (P'.card : ℝ) := by ring
      exact h_goal
    have h5 : (∑ c ∈ high, n c : ℝ) ≤ 2 * ∑ k ∈ layers, (a k : ℝ) := h_sum_high_le
    have h6 : 2 * ∑ k ∈ layers, (a k : ℝ) ≥ (3 : ℝ) / 4 * (m2 : ℝ) * (P'.card : ℝ) := by
      calc
        2 * ∑ k ∈ layers, (a k : ℝ) ≥ (∑ c ∈ high, n c : ℝ) := h5
        _ ≥ (3 : ℝ) / 4 * (m2 : ℝ) * (P'.card : ℝ) := h1
    have h7 : (3 : ℝ) / 8 * (m2 : ℝ) * (P'.card : ℝ) ≤ ∑ k ∈ layers, (a k : ℝ) := by
      have h8 : 2 * ∑ k ∈ layers, (a k : ℝ) ≥ (3 : ℝ) / 4 * (m2 : ℝ) * (P'.card : ℝ) := h6
      have h9 : (3 : ℝ) / 8 * (m2 : ℝ) * (P'.card : ℝ) ≤ ∑ k ∈ layers, (a k : ℝ) := by
        calc
          (3 : ℝ) / 8 * (m2 : ℝ) * (P'.card : ℝ)
            = ((3 : ℝ) / 4 * (m2 : ℝ) * (P'.card : ℝ)) / 2 := by ring
          _ ≤ (2 * ∑ k ∈ layers, (a k : ℝ)) / 2 := by gcongr
          _ = ∑ k ∈ layers, (a k : ℝ) := by ring
      exact h9
    exact h7
  have h_layers_card_le : layers.card ≤ K1 := by
    have h_high_nonempty : high.Nonempty := by
      by_contra h3
      have h4 : high = ∅ := Finset.not_nonempty_iff_eq_empty.mp h3
      rw [h4] at h_sum_high_pos
      simp at h_sum_high_pos
    have hkm : k_min ≤ k_max := by
      rcases h_high_nonempty with ⟨c, hc⟩
      have hft : t < n c := (Finset.mem_filter.mp hc).2
      have h1 : t + 1 ≤ n c := by omega
      have h2 : n c ≤ P'.card := by
        simp [n] <;> exact Finset.card_le_card (Finset.filter_subset _ _)
      have h3 : t + 1 ≤ P'.card := by omega
      exact Nat.log_mono_right h3
    have h : layers.card = k_max - k_min + 1 := by
      simp [layers, hkm] <;> omega
    rw [h]
    omega
  have h_layers_pos : 0 < layers.card := by
    have h1 : high.Nonempty := by
      by_contra h3
      have h4 : high = ∅ := Finset.not_nonempty_iff_eq_empty.mp h3
      rw [h4] at h_sum_high_pos
      simp at h_sum_high_pos
    rcases h1 with ⟨c, hc⟩
    rcases h_layers_cover c hc with ⟨k, hk, _⟩
    exact Finset.card_pos.mpr ⟨k, hk⟩
  have h_main : ∃ k ∈ layers,
      (a k : ℝ) ≥ (3 : ℝ) / 8 * (m2 : ℝ) * (P'.card : ℝ) / (K1 : ℝ) := by
    by_contra h
    push Not at h
    have h' : ∀ k ∈ layers, (a k : ℝ) < (3 : ℝ) / 8 * (m2 : ℝ) * (P'.card : ℝ) / (K1 : ℝ) := h
    have h_sum : ∑ k ∈ layers, (a k : ℝ) < (3 : ℝ) / 8 * (m2 : ℝ) * (P'.card : ℝ) := by
      calc
        ∑ k ∈ layers, (a k : ℝ)
          < ∑ _k ∈ layers, (3 : ℝ) / 8 * (m2 : ℝ) * (P'.card : ℝ) / (K1 : ℝ) :=
            Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp h_layers_pos) h'
        _ = (layers.card : ℝ) * ((3 : ℝ) / 8 * (m2 : ℝ) * (P'.card : ℝ) / (K1 : ℝ)) := by
          simp [Finset.sum_const] <;> ring
        _ ≤ (K1 : ℝ) * ((3 : ℝ) / 8 * (m2 : ℝ) * (P'.card : ℝ) / (K1 : ℝ)) := by
          gcongr <;> exact_mod_cast h_layers_card_le
        _ = (3 : ℝ) / 8 * (m2 : ℝ) * (P'.card : ℝ) := by
          field_simp [hK1_pos.ne'] <;> ring
    have h_cont : ¬((3 : ℝ) / 8 * (m2 : ℝ) * (P'.card : ℝ) ≤ ∑ k ∈ layers, (a k : ℝ)) :=
      not_le.mpr h_sum
    exact h_cont h_sum_a_lower
  rcases h_main with ⟨k, hk_layer, hk_ineq⟩
  let C' := S k
  have hC'_sub : C' ⊆ coarseRange := by
    trans high <;> exact Finset.filter_subset _ _
  have h_dyadic : ∀ c ∈ C', 2^k ≤ n c ∧ n c < 2^(k+1) := by
    intro c hc
    exact (Finset.mem_filter.mp hc).2
  have h_final : (2^k : ℝ) * (C'.card : ℝ) ≥
      (m2 : ℝ) * (P'.card : ℝ) / (4 * (K1 : ℝ)) := by
    have h1 : (a k : ℝ) = (2^k : ℝ) * (C'.card : ℝ) := by
      simp [a, C'] <;> ring
    have h2 : (a k : ℝ) ≥ (3 : ℝ) / 8 * (m2 : ℝ) * (P'.card : ℝ) / (K1 : ℝ) := hk_ineq
    have h3 : (3 : ℝ) / 8 * (m2 : ℝ) * (P'.card : ℝ) / (K1 : ℝ) ≥
        (m2 : ℝ) * (P'.card : ℝ) / (4 * (K1 : ℝ)) := by
      have h4 : (0 : ℝ) < (m2 : ℝ) := by exact_mod_cast hm2_pos
      have h6 : (0 : ℝ) < (P'.card : ℝ) := by exact_mod_cast hP'_nonempty.card_pos
      have h7 : (0 : ℝ) < (K1 : ℝ) := by positivity
      have h8 : (3 : ℝ) / 8 ≥ (1 : ℝ) / 4 := by norm_num
      have h9 : (3 : ℝ) / 8 * (m2 : ℝ) * (P'.card : ℝ) / (K1 : ℝ) ≥
          (1 : ℝ) / 4 * (m2 : ℝ) * (P'.card : ℝ) / (K1 : ℝ) := by gcongr
      have h10 : (1 : ℝ) / 4 * (m2 : ℝ) * (P'.card : ℝ) / (K1 : ℝ) =
          (m2 : ℝ) * (P'.card : ℝ) / (4 * (K1 : ℝ)) := by ring
      rw [h10] at h9
      exact h9
    have h4 : (a k : ℝ) ≥ (m2 : ℝ) * (P'.card : ℝ) / (4 * (K1 : ℝ)) := by
      calc (a k : ℝ) ≥ (3 : ℝ) / 8 * (m2 : ℝ) * (P'.card : ℝ) / (K1 : ℝ) := h2
           _ ≥ (m2 : ℝ) * (P'.card : ℝ) / (4 * (K1 : ℝ)) := h3
    rw [h1] at h4
    exact h4
  exact ⟨C', k, hC'_sub, h_dyadic, h_final⟩

/-! ==========================================================================
   6. Combined second + third pigeonhole
   ========================================================================== -/

/-- Combined second + third pigeonhole.

Given the output of `first_pigeonhole` (`C_p`, `m1_p`), produces:
- `P' ⊆ P` with `|P| ≤ K1² * |P'|`
- `T' p ⊆ T p` with `|T' p| ≥ M / (32 * K1)`
- `C' ⊆ coarseRange`
- `H` with `H ≤ ∑_{p ∈ P'} assignedCount coarse T' p c` for all `c ∈ C'`
- Two-sided: `M * |P'| / (128 * K1²) ≤ H * |C'| ≤ 4 * M * |P'|`

Note: This does NOT include the peeling step. The output `C'` may not equal
`P'.biUnion (fun p => (T' p).image coarse)`. That requires the peeling lemma.
-/
lemma second_third_pigeonhole {α L : Type*} [DecidableEq α] [DecidableEq L]
    {M K1 N : ℕ}
    (P : Finset α)
    (T : α → Finset L)
    (C_p : α → Finset L)
    (m1_p : α → ℕ)
    (coarse : L → L)
    (coarseRange : Finset L)
    (hM_pos : 0 < M)
    (hK1_pos : 0 < K1)
    (hN_pos : 0 < N)
    (hP_nonempty : P.Nonempty)
    (h_m1_range : ∃ (M1_vals : Finset ℕ),
        M1_vals.card ≤ K1 ∧ ∀ p ∈ P, m1_p p ∈ M1_vals)
    (h_Cp_le_N : ∀ p ∈ P, (C_p p).card ≤ N)
    (h_K1_ge : Nat.log 2 N + 4 ≤ K1)
    (h_mass_lower : ∀ p ∈ P,
        (M : ℝ) / (8 * (K1 : ℝ)) ≤ (m1_p p : ℝ) * ((C_p p).card : ℝ))
    (h_mass_upper : ∀ p ∈ P,
        (m1_p p : ℝ) * ((C_p p).card : ℝ) ≤ (M : ℝ))
    (hCp_sub : ∀ p ∈ P, C_p p ⊆ coarseRange)
    (h_coarseRange_card : coarseRange.card = N)
    (h_assigned_lower : ∀ p ∈ P, ∀ c ∈ C_p p,
        m1_p p ≤ assignedCount coarse T p c) :
    ∃ (P' : Finset α) (T' : α → Finset L)
      (C' : Finset L) (H : ℕ),
      P' ⊆ P ∧
      (P.card : ℝ) ≤ (K1 : ℝ)^2 * (P'.card : ℝ) ∧
      (∀ p ∈ P', T' p ⊆ T p) ∧
      (∀ p ∈ P', (M : ℝ) / (32 * (K1 : ℝ)) ≤ ((T' p).card : ℝ)) ∧
      C' ⊆ coarseRange ∧
      (∀ c ∈ C', H ≤ ∑ p ∈ P', assignedCount coarse T' p c) ∧
      (M : ℝ) * (P'.card : ℝ) / (128 * (K1 : ℝ)^2) ≤ (H : ℝ) * (C'.card : ℝ) ∧
      (H : ℝ) * (C'.card : ℝ) ≤ 4 * (M : ℝ) * (P'.card : ℝ) := by
  -- Second pigeonhole
  rcases second_pigeonhole P C_p m1_p hM_pos hK1_pos hP_nonempty
      h_m1_range h_Cp_le_N (by omega) h_mass_lower h_mass_upper
    with ⟨P', m1, m2, hP'_sub, hP'_card, h_m1_range, h_m2_range, h_mass_lower2, h_mass_upper2⟩
  have hP'_nonempty : P'.Nonempty := by
    by_contra h
    have h_empty : P' = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [h_empty] at hP'_card
    have h_pos : 0 < (P.card : ℝ) := by exact_mod_cast hP_nonempty.card_pos
    have h_cont : (P.card : ℝ) ≤ 0 := by simpa using hP'_card
    linarith
  -- Define T'
  let T' : α → Finset L := fun p =>
    (T p).filter (fun ℓ => coarse ℓ ∈ C_p p)
  have hT'_sub : ∀ p ∈ P', T' p ⊆ T p := by
    intro p _
    exact Finset.filter_subset _ _
  have hT'_card_eq : ∀ p ∈ P',
      (T' p).card = ∑ c ∈ C_p p, assignedCount coarse T p c := by
    intro p hp
    have h_disj : ∀ c1 ∈ C_p p, ∀ c2 ∈ C_p p, c1 ≠ c2 →
        Disjoint ((T p).filter (fun ℓ => coarse ℓ = c1))
                   ((T p).filter (fun ℓ => coarse ℓ = c2)) := by
      intro c1 _ c2 _ hne
      simp only [Finset.disjoint_left]
      intro ℓ h1 h2
      have h3 : coarse ℓ = c1 := (Finset.mem_filter.mp h1).2
      have h4 : coarse ℓ = c2 := (Finset.mem_filter.mp h2).2
      rw [h3] at h4
      exact hne h4
    have h1 : (T' p) = (C_p p).biUnion (fun c => (T p).filter (fun ℓ => coarse ℓ = c)) := by
      ext ℓ
      simp [T', assignedCount, Finset.mem_biUnion] <;> tauto
    rw [h1, Finset.card_biUnion h_disj] <;> rfl
  have hT'_card_lower : ∀ p ∈ P',
      (M : ℝ) / (32 * (K1 : ℝ)) ≤ (T' p).card := by
    intro p hp
    have h1 : (T' p).card = ∑ c ∈ C_p p, assignedCount coarse T p c := hT'_card_eq p hp
    rw [h1]
    have h2 : ∀ c ∈ C_p p, m1_p p ≤ assignedCount coarse T p c :=
      h_assigned_lower p (hP'_sub hp)
    have h3 : m1 ≤ m1_p p := (h_m1_range p hp).1
    have h4 : m2 ≤ (C_p p).card := (h_m2_range p hp).1
    have h5 : ∑ c ∈ C_p p, assignedCount coarse T p c ≥ (C_p p).card * m1_p p := by
      calc
        ∑ c ∈ C_p p, assignedCount coarse T p c
          ≥ ∑ c ∈ C_p p, m1_p p := Finset.sum_le_sum h2
        _ = (C_p p).card * m1_p p := by simp [Finset.sum_const] <;> ring
    have h6 : (C_p p).card * m1_p p ≥ m1 * m2 := by
      have h6' : (C_p p).card * m1_p p ≥ m2 * m1 := by gcongr <;> omega
      have h_comm : m2 * m1 = m1 * m2 := by ring
      rw [h_comm] at h6'
      exact h6'
    have h7 : (M : ℝ) / (32 * (K1 : ℝ)) ≤ (m1 : ℝ) * (m2 : ℝ) := h_mass_lower2
    have h9 : (m1 : ℝ) * (m2 : ℝ) ≤ ↑(∑ c ∈ C_p p, assignedCount coarse T p c) := by
      have h9' : (m1 : ℝ) * (m2 : ℝ) ≤ (∑ c ∈ C_p p, (assignedCount coarse T p c : ℝ)) := by
        exact_mod_cast h6.trans h5
      have h_sum_cast : (∑ c ∈ C_p p, (assignedCount coarse T p c : ℝ)) = ↑(∑ c ∈ C_p p, assignedCount coarse T p c) := by
        rw [← Nat.cast_sum]
        <;> rfl
      rw [h_sum_cast] at h9'
      exact h9'
    exact h7.trans h9
  -- Derive m2 > 0 from mass lower bound
  have hm2_pos : 0 < m2 := by
    have h_pos : (0 : ℝ) < (M : ℝ) / (32 * (K1 : ℝ)) := by positivity
    have h : (0 : ℝ) < (m1 : ℝ) * (m2 : ℝ) := h_pos.trans_le h_mass_lower2
    have h' : 0 < m1 * m2 := by exact_mod_cast h
    exact Nat.pos_of_ne_zero (fun h0 => by simp [h0] at h')
  -- Third pigeonhole
  rcases third_pigeonhole P' C_p coarseRange hK1_pos hN_pos hm2_pos hP'_nonempty
      (fun p hp => hCp_sub p (hP'_sub hp))
      (fun p hp => (h_m2_range p hp).1)
      h_coarseRange_card h_K1_ge
    with ⟨C', j, hC'_sub, h_dyadic, h_C'_bound⟩
  let H := 2^j * m1
  -- Incidence lower bound
  have h_inc_lower : ∀ c ∈ C', H ≤ ∑ p ∈ P', assignedCount coarse T' p c := by
    intro c hc
    let P_c := P'.filter (fun p => c ∈ C_p p)
    have h_n_lower : 2^j ≤ P_c.card := (h_dyadic c hc).1
    have h1 : ∀ p ∈ P_c, c ∈ C_p p := fun p hp => (Finset.mem_filter.mp hp).2
    have h2 : ∀ p ∈ P_c, m1 ≤ m1_p p := fun p hp =>
      (h_m1_range p (Finset.mem_filter.mp hp).1).1
    have h3 : ∀ p ∈ P_c, m1_p p ≤ assignedCount coarse T p c :=
      fun p hp => h_assigned_lower p (hP'_sub (Finset.mem_filter.mp hp).1) c (h1 p hp)
    have h4 : ∀ p ∈ P_c, assignedCount coarse T' p c = assignedCount coarse T p c := by
      intro p hp
      have h5 : c ∈ C_p p := h1 p hp
      have h6 : (T' p).filter (fun ℓ => coarse ℓ = c) = (T p).filter (fun ℓ => coarse ℓ = c) := by
        ext ℓ
        simp only [T', Finset.mem_filter]
        constructor
        · rintro ⟨⟨hℓ1, _⟩, hℓ2⟩
          exact ⟨hℓ1, hℓ2⟩
        · rintro ⟨hℓ1, hℓ2⟩
          have hℓ3 : coarse ℓ ∈ C_p p := by
            rw [hℓ2] <;> exact h5
          exact ⟨⟨hℓ1, hℓ3⟩, hℓ2⟩
      have h7 : assignedCount coarse T' p c = ((T' p).filter (fun ℓ => coarse ℓ = c)).card := by rfl
      have h8 : assignedCount coarse T p c = ((T p).filter (fun ℓ => coarse ℓ = c)).card := by rfl
      rw [h7, h8, h6]
    have h5 : ∑ p ∈ P', assignedCount coarse T' p c ≥ ∑ p ∈ P_c, assignedCount coarse T' p c :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)
    have h6 : ∑ p ∈ P_c, assignedCount coarse T' p c = ∑ p ∈ P_c, assignedCount coarse T p c := by
      apply Finset.sum_congr rfl
      intro p hp
      exact h4 p hp
    have h7 : ∑ p ∈ P_c, assignedCount coarse T p c ≥ P_c.card * m1 := by
      calc
        ∑ p ∈ P_c, assignedCount coarse T p c
          ≥ ∑ p ∈ P_c, m1_p p := Finset.sum_le_sum (fun p hp => h3 p hp)
        _ ≥ ∑ p ∈ P_c, m1 := Finset.sum_le_sum (fun p hp => h2 p hp)
        _ = P_c.card * m1 := by simp [Finset.sum_const] <;> ring
    have h8 : P_c.card * m1 ≥ 2^j * m1 := by
      gcongr <;> exact h_n_lower
    have h10 : ∑ p ∈ P', assignedCount coarse T' p c ≥ 2^j * m1 := by
      calc
        ∑ p ∈ P', assignedCount coarse T' p c
          ≥ ∑ p ∈ P_c, assignedCount coarse T' p c := h5
        _ = ∑ p ∈ P_c, assignedCount coarse T p c := h6
        _ ≥ P_c.card * m1 := h7
        _ ≥ 2^j * m1 := h8
    exact h10
  -- Lower bound: H * C'.card ≥ M * P'.card / (128 * K1²)
  have h_lower_bound : (M : ℝ) * (P'.card : ℝ) / (128 * (K1 : ℝ)^2) ≤
      (H : ℝ) * (C'.card : ℝ) := by
    have h1 : (H : ℝ) * (C'.card : ℝ) = (m1 : ℝ) * ((2^j : ℝ) * (C'.card : ℝ)) := by
      simp [H] <;> ring
    rw [h1]
    have h2 : (2^j : ℝ) * (C'.card : ℝ) ≥
        (m2 : ℝ) * (P'.card : ℝ) / (4 * (K1 : ℝ)) := h_C'_bound
    have h3 : (m1 : ℝ) * (m2 : ℝ) ≥ (M : ℝ) / (32 * (K1 : ℝ)) := h_mass_lower2
    calc
      (m1 : ℝ) * ((2^j : ℝ) * (C'.card : ℝ))
        ≥ (m1 : ℝ) * ((m2 : ℝ) * (P'.card : ℝ) / (4 * (K1 : ℝ))) := by gcongr
      _ = ((m1 : ℝ) * (m2 : ℝ)) * (P'.card : ℝ) / (4 * (K1 : ℝ)) := by ring
      _ ≥ ((M : ℝ) / (32 * (K1 : ℝ))) * (P'.card : ℝ) / (4 * (K1 : ℝ)) := by gcongr
      _ = (M : ℝ) * (P'.card : ℝ) / (128 * (K1 : ℝ)^2) := by
        field_simp [hK1_pos.ne'] <;> ring
  -- Derive m1 > 0 from mass lower bound
  have hm1_pos : 0 < m1 := by
    have h_pos : (0 : ℝ) < (M : ℝ) / (32 * (K1 : ℝ)) := by positivity
    have h : (0 : ℝ) < (m1 : ℝ) * (m2 : ℝ) := h_pos.trans_le h_mass_lower2
    have h' : 0 < m1 * m2 := by exact_mod_cast h
    exact Nat.pos_of_ne_zero (fun h0 => by simp [h0] at h')
  -- Upper bound: H * C'.card ≤ 4 * M * P'.card
  have h_upper_bound : (H : ℝ) * (C'.card : ℝ) ≤ 4 * (M : ℝ) * (P'.card : ℝ) := by
    have h1_nat : ∑ c ∈ C', (P'.filter (fun p => c ∈ C_p p)).card ≤ ∑ p ∈ P', (C_p p).card := by
      have h_swap : ∑ c ∈ C', (P'.filter (fun p => c ∈ C_p p)).card =
          ∑ p ∈ P', (C' ∩ C_p p).card := by
        have h2 : ∀ c, (P'.filter (fun p => c ∈ C_p p)).card =
            ∑ p ∈ P', (if c ∈ C_p p then 1 else 0) := by
          intro c
          rw [Finset.sum_ite] <;> simp
        rw [Finset.sum_congr rfl (fun c _ => h2 c), Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_ite] <;> simp [Finset.filter] <;> rfl
      rw [h_swap]
      have h3 : ∀ p ∈ P', (C' ∩ C_p p).card ≤ (C_p p).card := by
        intro p _
        exact Finset.card_le_card (show (C' ∩ C_p p) ⊆ (C_p p) from Finset.inter_subset_right)
      exact Finset.sum_le_sum h3
    have h1 : (∑ c ∈ C', (P'.filter (fun p => c ∈ C_p p)).card : ℝ) ≤ (∑ p ∈ P', ((C_p p).card : ℝ)) := by
      exact_mod_cast h1_nat
    have h2 : (∑ p ∈ P', ((C_p p).card : ℝ)) < 2 * (m2 : ℝ) * (P'.card : ℝ) := by
      have h3 : ∀ p ∈ P', (C_p p).card < 2 * m2 := fun p hp => (h_m2_range p hp).2
      have h4 : ∑ p ∈ P', (C_p p).card < P'.card * (2 * m2) := by
        have h5 : ∑ p ∈ P', (C_p p).card < ∑ p ∈ P', (2 * m2) :=
          Finset.sum_lt_sum_of_nonempty hP'_nonempty h3
        simpa [Finset.sum_const] using h5
      have h4' : ∑ p ∈ P', (C_p p).card < 2 * m2 * P'.card := by
        have h_eq : P'.card * (2 * m2) = 2 * m2 * P'.card := by ring
        rw [h_eq] at h4
        exact h4
      exact_mod_cast h4'
    have h5 : (2^j : ℝ) * (C'.card : ℝ) ≤ (∑ c ∈ C', (P'.filter (fun p => c ∈ C_p p)).card : ℝ) := by
      have h6 : ∀ c ∈ C', (2^j : ℝ) ≤ ((P'.filter (fun p => c ∈ C_p p)).card : ℝ) :=
        fun c hc => by exact_mod_cast (h_dyadic c hc).1
      calc
        (2^j : ℝ) * (C'.card : ℝ)
          = ∑ c ∈ C', (2^j : ℝ) := by simp [Finset.sum_const] <;> ring
        _ ≤ ∑ c ∈ C', ((P'.filter (fun p => c ∈ C_p p)).card : ℝ) := Finset.sum_le_sum h6
        _ = (∑ c ∈ C', (P'.filter (fun p => c ∈ C_p p)).card : ℝ) := by rfl
    have h7 : (H : ℝ) * (C'.card : ℝ) = (m1 : ℝ) * ((2^j : ℝ) * (C'.card : ℝ)) := by
      simp [H] <;> ring
    rw [h7]
    have h8 : (m1 : ℝ) * (m2 : ℝ) ≤ (M : ℝ) := h_mass_upper2
    have h10 : (m1 : ℝ) * ((2^j : ℝ) * (C'.card : ℝ)) ≤ 4 * (M : ℝ) * (P'.card : ℝ) := by
      calc
        (m1 : ℝ) * ((2^j : ℝ) * (C'.card : ℝ))
          ≤ (m1 : ℝ) * (∑ c ∈ C', (P'.filter (fun p => c ∈ C_p p)).card : ℝ) := by gcongr
        _ ≤ (m1 : ℝ) * (∑ p ∈ P', (C_p p).card : ℝ) := by gcongr
        _ ≤ (m1 : ℝ) * (2 * (m2 : ℝ) * (P'.card : ℝ)) := by
          exact mul_le_mul_of_nonneg_left h2.le (by positivity)
        _ = 2 * ((m1 : ℝ) * (m2 : ℝ)) * (P'.card : ℝ) := by ring
        _ ≤ 2 * (M : ℝ) * (P'.card : ℝ) := by gcongr
        _ ≤ 4 * (M : ℝ) * (P'.card : ℝ) := by
          have hpos : 0 ≤ (M : ℝ) * (P'.card : ℝ) := by positivity
          have h : 2 * (M : ℝ) * (P'.card : ℝ) ≤ 4 * (M : ℝ) * (P'.card : ℝ) := by
            have h5 : 0 ≤ 2 * (M : ℝ) * (P'.card : ℝ) := by positivity
            nlinarith
          exact h
    exact h10
  exact ⟨P', T', C', H, hP'_sub, hP'_card, hT'_sub, hT'_card_lower,
    hC'_sub, h_inc_lower, h_lower_bound, h_upper_bound⟩


-- ============================================================================
-- Bipartite peeling lemma
-- ============================================================================

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def inducedEdges (E : Finset (α × β)) (A' : Finset α) (B' : Finset β) :
    Finset (α × β) :=
  E.filter (fun p => p.1 ∈ A' ∧ p.2 ∈ B')

/-- Degree of `a` in the induced subgraph on `(A', B')`. -/
def degAInd (E : Finset (α × β)) (A' : Finset α) (B' : Finset β) (a : α) : ℕ :=
  ((inducedEdges E A' B').filter (fun p => p.1 = a)).card

/-- Degree of `b` in the induced subgraph on `(A', B')`. -/
def degBInd (E : Finset (α × β)) (A' : Finset α) (B' : Finset β) (b : β) : ℕ :=
  ((inducedEdges E A' B').filter (fun p => p.2 = b)).card

/-- One step of the peeling process: remove one low-degree vertex if one exists. -/
def peelStep (E : Finset (α × β)) (dA dB : ℝ)
    (A_cur : Finset α) (B_cur : Finset β) : Finset α × Finset β :=
  let lowA := A_cur.filter (fun a => (degAInd E A_cur B_cur a : ℝ) < dA / 4)
  if hA : lowA.Nonempty then
    let a := Classical.choose hA
    (A_cur.erase a, B_cur)
  else
    let lowB := B_cur.filter (fun b => (degBInd E A_cur B_cur b : ℝ) < dB / 4)
    if hB : lowB.Nonempty then
      let b := Classical.choose hB
      (A_cur, B_cur.erase b)
    else
      (A_cur, B_cur)

/-- Iterate `peelStep` `n` times. -/
def peelN (E : Finset (α × β)) (dA dB : ℝ) :
    ℕ → Finset α → Finset β → Finset α × Finset β
  | 0, A_cur, B_cur => (A_cur, B_cur)
  | n + 1, A_cur, B_cur =>
    let (A1, B1) := peelStep E dA dB A_cur B_cur
    peelN E dA dB n A1 B1

/-- Case analysis for `peelStep`. -/
lemma peelStep_cases (E : Finset (α × β)) (dA dB : ℝ)
    (A_cur : Finset α) (B_cur : Finset β) :
    (peelStep E dA dB A_cur B_cur = (A_cur, B_cur)) ∨
    (∃ (a : α), a ∈ A_cur ∧ (degAInd E A_cur B_cur a : ℝ) < dA / 4 ∧
      peelStep E dA dB A_cur B_cur = (A_cur.erase a, B_cur)) ∨
    (∃ (b : β), b ∈ B_cur ∧ (degBInd E A_cur B_cur b : ℝ) < dB / 4 ∧
      peelStep E dA dB A_cur B_cur = (A_cur, B_cur.erase b)) := by
  let lowA := A_cur.filter (fun a => (degAInd E A_cur B_cur a : ℝ) < dA / 4)
  by_cases hA : lowA.Nonempty
  · let a := Classical.choose hA
    have ha : a ∈ lowA := Classical.choose_spec hA
    have haA : a ∈ A_cur := (Finset.mem_filter.mp ha).1
    have halow : (degAInd E A_cur B_cur a : ℝ) < dA / 4 := (Finset.mem_filter.mp ha).2
    have hstep : peelStep E dA dB A_cur B_cur = (A_cur.erase a, B_cur) := by
      unfold peelStep
      rw [dif_pos hA] <;> rfl
    exact Or.inr (Or.inl ⟨a, haA, halow, hstep⟩)
  · let lowB := B_cur.filter (fun b => (degBInd E A_cur B_cur b : ℝ) < dB / 4)
    by_cases hB : lowB.Nonempty
    · let b := Classical.choose hB
      have hb : b ∈ lowB := Classical.choose_spec hB
      have hbB : b ∈ B_cur := (Finset.mem_filter.mp hb).1
      have hblow : (degBInd E A_cur B_cur b : ℝ) < dB / 4 := (Finset.mem_filter.mp hb).2
      have hstep : peelStep E dA dB A_cur B_cur = (A_cur, B_cur.erase b) := by
        unfold peelStep
        rw [dif_neg hA, dif_pos hB] <;> rfl
      exact Or.inr (Or.inr ⟨b, hbB, hblow, hstep⟩)
    · have hstep : peelStep E dA dB A_cur B_cur = (A_cur, B_cur) := by
        unfold peelStep
        rw [dif_neg hA, dif_neg hB] <;> rfl
      exact Or.inl hstep

/-- `peelStep` either returns the input or strictly decreases the cardinality sum. -/
lemma peelStep_strict_or_fixed (E : Finset (α × β)) (dA dB : ℝ)
    (A_cur : Finset α) (B_cur : Finset β) :
    peelStep E dA dB A_cur B_cur = (A_cur, B_cur) ∨
    (peelStep E dA dB A_cur B_cur).1.card + (peelStep E dA dB A_cur B_cur).2.card <
      A_cur.card + B_cur.card := by
  rcases peelStep_cases E dA dB A_cur B_cur with (h | ⟨a, ha, _, hstep⟩ | ⟨b, hb, _, hstep⟩)
  · exact Or.inl h
  · rw [hstep]
    have h : (A_cur.erase a).card + B_cur.card < A_cur.card + B_cur.card := by
      have h' : (A_cur.erase a).card < A_cur.card := Finset.card_erase_lt_of_mem ha
      linarith
    exact Or.inr h
  · rw [hstep]
    have h : A_cur.card + (B_cur.erase b).card < A_cur.card + B_cur.card := by
      have h' : (B_cur.erase b).card < B_cur.card := Finset.card_erase_lt_of_mem hb
      linarith
    exact Or.inr h

/-- `peelStep` output is a subset of the input. -/
lemma peelStep_subset (E : Finset (α × β)) (dA dB : ℝ)
    (A_cur : Finset α) (B_cur : Finset β) :
    (peelStep E dA dB A_cur B_cur).1 ⊆ A_cur ∧
    (peelStep E dA dB A_cur B_cur).2 ⊆ B_cur := by
  rcases peelStep_cases E dA dB A_cur B_cur with (h | ⟨a, _, _, hstep⟩ | ⟨b, _, _, hstep⟩)
  · rw [h] <;> exact ⟨rfl.subset, rfl.subset⟩
  · rw [hstep] <;> exact ⟨Finset.erase_subset _ _, rfl.subset⟩
  · rw [hstep] <;> exact ⟨rfl.subset, Finset.erase_subset _ _⟩

/-- Edge count decreases by the degree of the removed A-vertex. -/
lemma edge_diff_A (E : Finset (α × β)) (A_cur : Finset α) (B_cur : Finset β) (a : α) (ha : a ∈ A_cur) :
    (inducedEdges E A_cur B_cur).card =
      (inducedEdges E (A_cur.erase a) B_cur).card + degAInd E A_cur B_cur a := by
  let E_cur := inducedEdges E A_cur B_cur
  let E_new := inducedEdges E (A_cur.erase a) B_cur
  let E_a := E_cur.filter (fun p => p.1 = a)
  have h1 : E_cur = E_new ∪ E_a := by
    ext ⟨x, y⟩
    simp only [E_cur, E_new, E_a, inducedEdges, Finset.mem_filter, Finset.mem_union,
      Finset.mem_erase, ha]
    <;> by_cases h : x = a <;> simp [h] <;> tauto
  have h2 : Disjoint E_new E_a := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h3 : p.1 ≠ a := by
      simp only [E_new, inducedEdges, Finset.mem_filter] at hp1
      exact (Finset.mem_erase.mp hp1.2.1).1
    have h4 : p.1 = a := (Finset.mem_filter.mp hp2).2
    exact h3 h4
  have h3 : E_cur.card = E_new.card + E_a.card := by
    rw [h1, Finset.card_union_of_disjoint h2]
  simpa [E_a, degAInd] using h3

/-- Edge count decreases by the degree of the removed B-vertex. -/
lemma edge_diff_B (E : Finset (α × β)) (A_cur : Finset α) (B_cur : Finset β) (b : β) (hb : b ∈ B_cur) :
    (inducedEdges E A_cur B_cur).card =
      (inducedEdges E A_cur (B_cur.erase b)).card + degBInd E A_cur B_cur b := by
  let E_cur := inducedEdges E A_cur B_cur
  let E_new := inducedEdges E A_cur (B_cur.erase b)
  let E_b := E_cur.filter (fun p => p.2 = b)
  have h1 : E_cur = E_new ∪ E_b := by
    ext ⟨x, y⟩
    simp only [E_cur, E_new, E_b, inducedEdges, Finset.mem_filter, Finset.mem_union,
      Finset.mem_erase, hb]
    <;> by_cases h : y = b <;> simp [h] <;> tauto
  have h2 : Disjoint E_new E_b := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h3 : p.2 ≠ b := by
      simp only [E_new, inducedEdges, Finset.mem_filter] at hp1
      exact (Finset.mem_erase.mp hp1.2.2).1
    have h4 : p.2 = b := (Finset.mem_filter.mp hp2).2
    exact h3 h4
  have h3 : E_cur.card = E_new.card + E_b.card := by
    rw [h1, Finset.card_union_of_disjoint h2]
  simpa [E_b, degBInd] using h3

/-- Cardinality of set difference increases by 1 when erasing a member. -/
lemma sdiff_card_erase {γ : Type*} [DecidableEq γ] {S_init S_cur : Finset γ} {x : γ}
    (hsub : S_cur ⊆ S_init) (hx : x ∈ S_cur) :
    (S_init \ (S_cur.erase x)).card = (S_init \ S_cur).card + 1 := by
  have hx_init : x ∈ S_init := hsub hx
  have hx_notin : x ∉ S_init \ S_cur := by
    simp only [Finset.mem_sdiff, not_and, not_true] <;> tauto
  have h3 : S_init \ (S_cur.erase x) = insert x (S_init \ S_cur) := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
    constructor
    · intro h
      by_cases hz : z = x
      · exact Or.inl hz
      · have hz' : z ≠ x := hz
        have h4 : z ∉ S_cur := by
          intro h5
          exact h.2 ⟨hz', h5⟩
        exact Or.inr ⟨h.1, h4⟩
    · rintro (rfl | h)
      · exact ⟨hx_init, by simp [hx]⟩
      · exact ⟨h.1, by simp [h.2]⟩
  rw [h3]
  have h4 : (insert x (S_init \ S_cur)).card = (S_init \ S_cur).card + 1 := by
    simp [hx_notin] <;> omega
  exact h4

/-- Degree in induced subgraph ≤ degree in original graph (A side). -/
lemma degAInd_le_original (E : Finset (α × β)) (A' : Finset α) (B' : Finset β) (a : α) :
    degAInd E A' B' a ≤ (E.filter (fun p : α × β => p.1 = a)).card := by
  apply Finset.card_le_card
  intro p hp
  have h1 : p ∈ inducedEdges E A' B' := (Finset.mem_filter.mp hp).1
  have h2 : p.1 = a := (Finset.mem_filter.mp hp).2
  have h3 : p ∈ E := (Finset.mem_filter.mp h1).1
  exact Finset.mem_filter.mpr ⟨h3, h2⟩

/-- Degree in induced subgraph ≤ degree in original graph (B side). -/
lemma degBInd_le_original (E : Finset (α × β)) (A' : Finset α) (B' : Finset β) (b : β) :
    degBInd E A' B' b ≤ (E.filter (fun p : α × β => p.2 = b)).card := by
  apply Finset.card_le_card
  intro p hp
  have h1 : p ∈ inducedEdges E A' B' := (Finset.mem_filter.mp hp).1
  have h2 : p.2 = b := (Finset.mem_filter.mp hp).2
  have h3 : p ∈ E := (Finset.mem_filter.mp h1).1
  exact Finset.mem_filter.mpr ⟨h3, h2⟩

/-- The peeling invariant: |E_init| ≤ |E_cur| + dA/4 * |A_init \\ A_cur| + dB/4 * |B_init \\ B_cur|. -/
lemma peelN_invariant (E : Finset (α × β)) (dA dB : ℝ)
    (A_init : Finset α) (B_init : Finset β) :
    ∀ (n : ℕ) (A_cur : Finset α) (B_cur : Finset β),
      A_cur ⊆ A_init → B_cur ⊆ B_init →
      ((inducedEdges E A_init B_init).card : ℝ) ≤
        ((inducedEdges E A_cur B_cur).card : ℝ) +
        dA / 4 * ((A_init \ A_cur).card : ℝ) +
        dB / 4 * ((B_init \ B_cur).card : ℝ) →
      let (A', B') := peelN E dA dB n A_cur B_cur
      A' ⊆ A_cur ∧ B' ⊆ B_cur ∧
      ((inducedEdges E A_init B_init).card : ℝ) ≤
        ((inducedEdges E A' B').card : ℝ) +
        dA / 4 * ((A_init \ A').card : ℝ) +
        dB / 4 * ((B_init \ B').card : ℝ) := by
  intro n
  induction n with
  | zero =>
    intro A_cur B_cur hA_sub hB_sub h_inv
    exact ⟨rfl.subset, rfl.subset, h_inv⟩
  | succ n ih =>
    intro A_cur B_cur hA_sub hB_sub h_inv
    set p : Finset α × Finset β := peelStep E dA dB A_cur B_cur with hp_def
    let A1 := p.1
    let B1 := p.2
    have h_sub1 : A1 ⊆ A_init := (peelStep_subset E dA dB A_cur B_cur).1.trans hA_sub
    have h_sub2 : B1 ⊆ B_init := (peelStep_subset E dA dB A_cur B_cur).2.trans hB_sub
    have h_inv1 : ((inducedEdges E A_init B_init).card : ℝ) ≤
        ((inducedEdges E A1 B1).card : ℝ) +
        dA / 4 * ((A_init \ A1).card : ℝ) +
        dB / 4 * ((B_init \ B1).card : ℝ) := by
      rcases peelStep_cases E dA dB A_cur B_cur with
        (h_eq | ⟨a, ha, halow, hstep⟩ | ⟨b, hb, hblow, hstep⟩)
      · have hA1 : A1 = A_cur := by
          have h : p = (A_cur, B_cur) := h_eq
          exact congr_arg Prod.fst h
        have hB1 : B1 = B_cur := by
          have h : p = (A_cur, B_cur) := h_eq
          exact congr_arg Prod.snd h
        rw [hA1, hB1]
        exact h_inv
      · have h_ediff : ((inducedEdges E A_cur B_cur).card : ℝ) =
            ((inducedEdges E (A_cur.erase a) B_cur).card : ℝ) + (degAInd E A_cur B_cur a : ℝ) := by
          exact_mod_cast edge_diff_A E A_cur B_cur a ha
        have h_sdiff : ((A_init \ (A_cur.erase a)).card : ℝ) = ((A_init \ A_cur).card : ℝ) + 1 := by
          exact_mod_cast sdiff_card_erase hA_sub ha
        have h_low : (degAInd E A_cur B_cur a : ℝ) < dA / 4 := halow
        have h_p : p = (A_cur.erase a, B_cur) := hp_def.trans hstep
        have hA1 : A1 = A_cur.erase a := by simp [A1, h_p]
        have hB1 : B1 = B_cur := by simp [B1, h_p]
        have h_goal : ((inducedEdges E A_init B_init).card : ℝ) ≤
            ((inducedEdges E (A_cur.erase a) B_cur).card : ℝ) +
            dA / 4 * ((A_init \ (A_cur.erase a)).card : ℝ) +
            dB / 4 * ((B_init \ B_cur).card : ℝ) := by
          calc ((inducedEdges E A_init B_init).card : ℝ)
            ≤ ((inducedEdges E A_cur B_cur).card : ℝ) + dA / 4 * ((A_init \ A_cur).card : ℝ) + dB / 4 * ((B_init \ B_cur).card : ℝ) := h_inv
          _ = ((inducedEdges E (A_cur.erase a) B_cur).card : ℝ) + (degAInd E A_cur B_cur a : ℝ) + dA / 4 * ((A_init \ A_cur).card : ℝ) + dB / 4 * ((B_init \ B_cur).card : ℝ) := by
              rw [h_ediff] <;> ring
          _ ≤ ((inducedEdges E (A_cur.erase a) B_cur).card : ℝ) + dA / 4 + dA / 4 * ((A_init \ A_cur).card : ℝ) + dB / 4 * ((B_init \ B_cur).card : ℝ) := by
              gcongr <;> linarith
          _ = ((inducedEdges E (A_cur.erase a) B_cur).card : ℝ) + dA / 4 * (((A_init \ A_cur).card : ℝ) + 1) + dB / 4 * ((B_init \ B_cur).card : ℝ) := by ring
          _ = ((inducedEdges E (A_cur.erase a) B_cur).card : ℝ) + dA / 4 * ((A_init \ (A_cur.erase a)).card : ℝ) + dB / 4 * ((B_init \ B_cur).card : ℝ) := by
              rw [h_sdiff] <;> ring
        rw [hA1, hB1]
        exact h_goal
      · have h_ediff : ((inducedEdges E A_cur B_cur).card : ℝ) =
            ((inducedEdges E A_cur (B_cur.erase b)).card : ℝ) + (degBInd E A_cur B_cur b : ℝ) := by
          exact_mod_cast edge_diff_B E A_cur B_cur b hb
        have h_sdiff : ((B_init \ (B_cur.erase b)).card : ℝ) = ((B_init \ B_cur).card : ℝ) + 1 := by
          exact_mod_cast sdiff_card_erase hB_sub hb
        have h_low : (degBInd E A_cur B_cur b : ℝ) < dB / 4 := hblow
        have h_p : p = (A_cur, B_cur.erase b) := hp_def.trans hstep
        have hA1 : A1 = A_cur := by simp [A1, h_p]
        have hB1 : B1 = B_cur.erase b := by simp [B1, h_p]
        have h_goal : ((inducedEdges E A_init B_init).card : ℝ) ≤
            ((inducedEdges E A_cur (B_cur.erase b)).card : ℝ) +
            dA / 4 * ((A_init \ A_cur).card : ℝ) +
            dB / 4 * ((B_init \ (B_cur.erase b)).card : ℝ) := by
          calc ((inducedEdges E A_init B_init).card : ℝ)
            ≤ ((inducedEdges E A_cur B_cur).card : ℝ) + dA / 4 * ((A_init \ A_cur).card : ℝ) + dB / 4 * ((B_init \ B_cur).card : ℝ) := h_inv
          _ = ((inducedEdges E A_cur (B_cur.erase b)).card : ℝ) + (degBInd E A_cur B_cur b : ℝ) + dA / 4 * ((A_init \ A_cur).card : ℝ) + dB / 4 * ((B_init \ B_cur).card : ℝ) := by
              rw [h_ediff] <;> ring
          _ ≤ ((inducedEdges E A_cur (B_cur.erase b)).card : ℝ) + dB / 4 + dA / 4 * ((A_init \ A_cur).card : ℝ) + dB / 4 * ((B_init \ B_cur).card : ℝ) := by
              gcongr <;> linarith
          _ = ((inducedEdges E A_cur (B_cur.erase b)).card : ℝ) + dA / 4 * ((A_init \ A_cur).card : ℝ) + dB / 4 * (((B_init \ B_cur).card : ℝ) + 1) := by ring
          _ = ((inducedEdges E A_cur (B_cur.erase b)).card : ℝ) + dA / 4 * ((A_init \ A_cur).card : ℝ) + dB / 4 * ((B_init \ (B_cur.erase b)).card : ℝ) := by
              rw [h_sdiff] <;> ring
        rw [hA1, hB1]
        exact h_goal
    have h_ih := ih A1 B1 h_sub1 h_sub2 h_inv1
    have hA'_sub : (peelN E dA dB n A1 B1).1 ⊆ A_cur :=
      h_ih.1.trans (peelStep_subset E dA dB A_cur B_cur).1
    have hB'_sub : (peelN E dA dB n A1 B1).2 ⊆ B_cur :=
      h_ih.2.1.trans (peelStep_subset E dA dB A_cur B_cur).2
    exact ⟨hA'_sub, hB'_sub, h_ih.2.2⟩

/-- After enough iterations, `peelN` reaches a fixed point. -/
lemma peelN_fixed (E : Finset (α × β)) (dA dB : ℝ) :
    ∀ (n : ℕ) (A_cur : Finset α) (B_cur : Finset β),
      n ≥ A_cur.card + B_cur.card →
      let (A', B') := peelN E dA dB n A_cur B_cur
      peelStep E dA dB A' B' = (A', B') := by
  intro n
  induction n with
  | zero =>
    intro A_cur B_cur h
    have h0 : A_cur.card + B_cur.card ≤ 0 := by exact_mod_cast h
    have h0' : A_cur.card + B_cur.card = 0 := by omega
    have hAcard : A_cur.card = 0 := by omega
    have hBcard : B_cur.card = 0 := by omega
    have hA : A_cur = ∅ := Finset.card_eq_zero.mp hAcard
    have hB : B_cur = ∅ := Finset.card_eq_zero.mp hBcard
    subst hA hB
    simp [peelStep, peelN, inducedEdges, degAInd, degBInd]
  | succ n ih =>
    intro A_cur B_cur h
    set p : Finset α × Finset β := peelStep E dA dB A_cur B_cur with hp_def
    let A1 := p.1
    let B1 := p.2
    by_cases h_eq : p = (A_cur, B_cur)
    · have h_id : ∀ k : ℕ, peelN E dA dB k A_cur B_cur = (A_cur, B_cur) := by
        intro k
        induction k with
        | zero => exact rfl
        | succ k ih2 =>
          have h1 : peelN E dA dB (k + 1) A_cur B_cur =
              peelN E dA dB k (peelStep E dA dB A_cur B_cur).1 (peelStep E dA dB A_cur B_cur).2 := by rfl
          rw [h1]
          have hstep_eq : peelStep E dA dB A_cur B_cur = (A_cur, B_cur) := hp_def.symm.trans h_eq
          have hA1 : (peelStep E dA dB A_cur B_cur).1 = A_cur := by
            rw [hstep_eq] <;> rfl
          have hB1 : (peelStep E dA dB A_cur B_cur).2 = B_cur := by
            rw [hstep_eq] <;> rfl
          rw [hA1, hB1]
          exact ih2
      have h_main : peelN E dA dB (n + 1) A_cur B_cur = (A_cur, B_cur) := h_id (n + 1)
      rw [h_main]
      exact h_eq
    · have h_lt : A1.card + B1.card < A_cur.card + B_cur.card := by
        have h := peelStep_strict_or_fixed E dA dB A_cur B_cur
        rcases h with (h' | h_lt')
        · exact False.elim (h_eq h')
        · exact h_lt'
      have h' : n ≥ A1.card + B1.card := by linarith
      have h_main : peelN E dA dB (n + 1) A_cur B_cur = peelN E dA dB n A1 B1 := by
        simp [peelN, hp_def] <;> rfl
      rw [h_main]
      exact ih A1 B1 h'

/-- A fixed point of `peelStep` has no low-degree vertices. -/
lemma fixed_point_no_low (E : Finset (α × β)) (dA dB : ℝ)
    (A' : Finset α) (B' : Finset β) (h : peelStep E dA dB A' B' = (A', B')) :
    (∀ a ∈ A', ¬ (degAInd E A' B' a : ℝ) < dA / 4) ∧
    (∀ b ∈ B', ¬ (degBInd E A' B' b : ℝ) < dB / 4) := by
  let lowA := A'.filter (fun a => (degAInd E A' B' a : ℝ) < dA / 4)
  let lowB := B'.filter (fun b => (degBInd E A' B' b : ℝ) < dB / 4)
  have hA : ¬ lowA.Nonempty := by
    by_contra hA'
    let a := Classical.choose hA'
    have ha : a ∈ lowA := Classical.choose_spec hA'
    have haA : a ∈ A' := (Finset.mem_filter.mp ha).1
    have hstep : peelStep E dA dB A' B' = (A'.erase a, B') := by
      unfold peelStep
      rw [dif_pos hA'] <;> rfl
    rw [hstep] at h
    have h_cont : A'.erase a ≠ A' := by
      intro h4
      have h5 : (A'.erase a).card < A'.card := Finset.card_erase_lt_of_mem haA
      rw [h4] at h5
      exact lt_irrefl A'.card h5
    have h6 : (A'.erase a, B') = (A', B') := h
    have h7 : A'.erase a = A' := congr_arg Prod.fst h6
    exact h_cont h7
  have hB : ¬ lowB.Nonempty := by
    by_contra hB'
    let b := Classical.choose hB'
    have hb : b ∈ lowB := Classical.choose_spec hB'
    have hbB : b ∈ B' := (Finset.mem_filter.mp hb).1
    have hstep : peelStep E dA dB A' B' = (A', B'.erase b) := by
      unfold peelStep
      rw [dif_neg hA, dif_pos hB'] <;> rfl
    rw [hstep] at h
    have h_cont : B'.erase b ≠ B' := by
      intro h4
      have h5 : (B'.erase b).card < B'.card := Finset.card_erase_lt_of_mem hbB
      rw [h4] at h5
      exact lt_irrefl B'.card h5
    have h6 : (A', B'.erase b) = (A', B') := h
    have h7 : B'.erase b = B' := congr_arg Prod.snd h6
    exact h_cont h7
  have hA_empty : lowA = ∅ := by
    simpa [Finset.not_nonempty_iff_eq_empty] using hA
  have hB_empty : lowB = ∅ := by
    simpa [Finset.not_nonempty_iff_eq_empty] using hB
  have h4 : ∀ a ∈ A', ¬ (degAInd E A' B' a : ℝ) < dA / 4 := by
    intro a ha
    have h5 : a ∉ lowA := by rw [hA_empty] <;> simp
    simpa [lowA, Finset.mem_filter, ha] using h5
  have h5 : ∀ b ∈ B', ¬ (degBInd E A' B' b : ℝ) < dB / 4 := by
    intro b hb
    have h6 : b ∉ lowB := by rw [hB_empty] <;> simp
    simpa [lowB, Finset.mem_filter, hb] using h6
  exact ⟨h4, h5⟩

/-- Total edge count equals sum of degrees on the A side. -/
lemma edge_card_sum_degA (E : Finset (α × β)) (A' : Finset α) (B' : Finset β) :
    (inducedEdges E A' B').card = ∑ a ∈ A', degAInd E A' B' a := by
  have h1 : inducedEdges E A' B' = A'.biUnion (fun a => (inducedEdges E A' B').filter (fun p => p.1 = a)) := by
    ext p
    simp only [inducedEdges, Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · intro h
      exact ⟨p.1, h.2.1, ⟨h, rfl⟩⟩
    · rintro ⟨a, ha, hp⟩
      exact hp.1
  have h_disj : ∀ a₁ ∈ A', ∀ a₂ ∈ A', a₁ ≠ a₂ →
      Disjoint ((inducedEdges E A' B').filter (fun p => p.1 = a₁))
        ((inducedEdges E A' B').filter (fun p => p.1 = a₂)) := by
    intro a₁ _ a₂ _ hne
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 : p.1 = a₁ := (Finset.mem_filter.mp hp1).2
    have h2 : p.1 = a₂ := (Finset.mem_filter.mp hp2).2
    have h3 : a₁ = a₂ := Eq.trans (Eq.symm h1) h2
    exact hne h3
  have h2 : (inducedEdges E A' B').card =
      (A'.biUnion (fun a => (inducedEdges E A' B').filter (fun p => p.1 = a))).card :=
    congr_arg Finset.card h1
  rw [h2, Finset.card_biUnion h_disj]
  <;> rfl

/-- Total edge count equals sum of degrees on the B side. -/
lemma edge_card_sum_degB (E : Finset (α × β)) (A' : Finset α) (B' : Finset β) :
    (inducedEdges E A' B').card = ∑ b ∈ B', degBInd E A' B' b := by
  have h1 : inducedEdges E A' B' = B'.biUnion (fun b => (inducedEdges E A' B').filter (fun p => p.2 = b)) := by
    ext p
    simp only [inducedEdges, Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · intro h
      exact ⟨p.2, h.2.2, ⟨h, rfl⟩⟩
    · rintro ⟨b, hb, hp⟩
      exact hp.1
  have h_disj : ∀ b₁ ∈ B', ∀ b₂ ∈ B', b₁ ≠ b₂ →
      Disjoint ((inducedEdges E A' B').filter (fun p => p.2 = b₁))
        ((inducedEdges E A' B').filter (fun p => p.2 = b₂)) := by
    intro b₁ _ b₂ _ hne
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 : p.2 = b₁ := (Finset.mem_filter.mp hp1).2
    have h2 : p.2 = b₂ := (Finset.mem_filter.mp hp2).2
    have h3 : b₁ = b₂ := Eq.trans (Eq.symm h1) h2
    exact hne h3
  have h2 : (inducedEdges E A' B').card =
      (B'.biUnion (fun b => (inducedEdges E A' B').filter (fun p => p.2 = b))).card :=
    congr_arg Finset.card h1
  rw [h2, Finset.card_biUnion h_disj]
  <;> rfl

/-- **Bipartite Peeling Lemma**: Given a bipartite graph with average degrees
    `dA = |E|/|A|`, `dB = |E|/|B|` and max degree bounds, produce a subgraph
    with minimum degree ≥ average/4 on both sides and retaining enough vertices. -/
theorem bipartite_peeling {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (E : Finset (α × β))
    (hE : E ⊆ A ×ˢ B)
    (dA dB : ℝ)
    (hdA : dA = (E.card : ℝ) / (A.card : ℝ))
    (hdB : dB = (E.card : ℝ) / (B.card : ℝ))
    (maxDegA maxDegB : ℕ)
    (hmaxA : ∀ a ∈ A, (E.filter (fun p : α × β => p.1 = a)).card ≤ maxDegA)
    (hmaxB : ∀ b ∈ B, (E.filter (fun p : α × β => p.2 = b)).card ≤ maxDegB)
    (hA : A.Nonempty) (hB : B.Nonempty) (hEne : E.Nonempty) :
    ∃ (A' : Finset α) (B' : Finset β),
      let E' := inducedEdges E A' B'
      A' ⊆ A ∧ B' ⊆ B ∧
      (∀ a ∈ A', (dA / 4 : ℝ) ≤ (degAInd E A' B' a : ℝ)) ∧
      (∀ b ∈ B', (dB / 4 : ℝ) ≤ (degBInd E A' B' b : ℝ)) ∧
      B' = E'.image Prod.snd ∧
      (A'.card : ℝ) ≥ (A.card : ℝ) * dA / (4 * (maxDegA : ℝ)) ∧
      (B'.card : ℝ) ≥ (B.card : ℝ) * dB / (4 * (maxDegB : ℝ)) := by
  have hA_pos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hB_pos : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hE_pos : 0 < (E.card : ℝ) := by exact_mod_cast hEne.card_pos
  have hmaxA_pos : 0 < (maxDegA : ℝ) := by
    rcases hEne with ⟨p, hp⟩
    have hpin : p ∈ E := hp
    have h1 : p.1 ∈ A := (Finset.mem_product.mp (hE hpin)).1
    have h2 : 1 ≤ (E.filter (fun q : α × β => q.1 = p.1)).card := by
      apply Finset.one_le_card.mpr
      exact ⟨p, Finset.mem_filter.mpr ⟨hpin, rfl⟩⟩
    have h3 := hmaxA p.1 h1
    exact_mod_cast (h2.trans h3)
  have hmaxB_pos : 0 < (maxDegB : ℝ) := by
    rcases hEne with ⟨p, hp⟩
    have hpin : p ∈ E := hp
    have h1 : p.2 ∈ B := (Finset.mem_product.mp (hE hpin)).2
    have h2 : 1 ≤ (E.filter (fun q : α × β => q.2 = p.2)).card := by
      apply Finset.one_le_card.mpr
      exact ⟨p, Finset.mem_filter.mpr ⟨hpin, rfl⟩⟩
    have h3 := hmaxB p.2 h1
    exact_mod_cast (h2.trans h3)
  have hdA_pos : 0 < dA := by rw [hdA] <;> positivity
  have hdB_pos : 0 < dB := by rw [hdB] <;> positivity

  let N := A.card + B.card
  let p := peelN E dA dB N A B
  let A' := p.1
  let B' := p.2
  let E' := inducedEdges E A' B'

  have h_fixed : peelStep E dA dB A' B' = (A', B') :=
    peelN_fixed E dA dB N A B (by simp [N])
  have h_no_low := fixed_point_no_low E dA dB A' B' h_fixed

  have hEAB : inducedEdges E A B = E := by
    ext p
    simp only [inducedEdges, Finset.mem_filter]
    constructor
    · intro h; exact h.1
    · intro hp
      have h1 : p.1 ∈ A := (Finset.mem_product.mp (hE hp)).1
      have h2 : p.2 ∈ B := (Finset.mem_product.mp (hE hp)).2
      exact ⟨hp, h1, h2⟩
  have h_init_inv : ((inducedEdges E A B).card : ℝ) ≤
      ((inducedEdges E A B).card : ℝ) + dA / 4 * ((A \ A).card : ℝ) + dB / 4 * ((B \ B).card : ℝ) := by
    simp
  have h_main_inv := peelN_invariant E dA dB A B N A B rfl.subset rfl.subset h_init_inv
  have hA'_sub : A' ⊆ A := h_main_inv.1
  have hB'_sub : B' ⊆ B := h_main_inv.2.1
  have h_edge_inv : ((inducedEdges E A B).card : ℝ) ≤
      (E'.card : ℝ) + dA / 4 * ((A \ A').card : ℝ) + dB / 4 * ((B \ B').card : ℝ) :=
    h_main_inv.2.2

  -- Edge count bound: |E| ≤ |E'| + |E|/2, so |E'| ≥ |E|/2
  have h1 : dA / 4 * ((A \ A').card : ℝ) + dB / 4 * ((B \ B').card : ℝ) ≤ (E.card : ℝ) / 2 := by
    have h2 : (A \ A').card ≤ A.card := Finset.card_le_card (show A \ A' ⊆ A from by simp)
    have h3 : (B \ B').card ≤ B.card := Finset.card_le_card (show B \ B' ⊆ B from by simp)
    have h4 : dA * (A.card : ℝ) = (E.card : ℝ) := by
      rw [hdA] <;> field_simp [hA_pos.ne'] <;> ring
    have h5 : dB * (B.card : ℝ) = (E.card : ℝ) := by
      rw [hdB] <;> field_simp [hB_pos.ne'] <;> ring
    calc
      dA / 4 * ((A \ A').card : ℝ) + dB / 4 * ((B \ B').card : ℝ)
        ≤ dA / 4 * (A.card : ℝ) + dB / 4 * (B.card : ℝ) := by gcongr <;> exact_mod_cast ‹_›
      _ = (E.card : ℝ) / 2 := by linarith
  have hE'_ge : (E'.card : ℝ) ≥ (E.card : ℝ) / 2 := by
    rw [hEAB] at h_edge_inv
    linarith

  -- Size bound for A': |E'| ≤ |A'| * maxDegA
  have h_sumA : E'.card = ∑ a ∈ A', degAInd E A' B' a := edge_card_sum_degA E A' B'
  have h_deg_boundA : ∀ a ∈ A', degAInd E A' B' a ≤ maxDegA := by
    intro a ha
    have h6 : a ∈ A := hA'_sub ha
    have h7 : degAInd E A' B' a ≤ (E.filter (fun p : α × β => p.1 = a)).card :=
      degAInd_le_original E A' B' a
    exact h7.trans (hmaxA a h6)
  have hE'_le_A : (E'.card : ℝ) ≤ (A'.card : ℝ) * (maxDegA : ℝ) := by
    rw [h_sumA]
    have h8 : (∑ a ∈ A', (degAInd E A' B' a : ℝ)) ≤ ∑ a ∈ A', (maxDegA : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact_mod_cast h_deg_boundA i ‹_›
    have h9 : (∑ a ∈ A', (maxDegA : ℝ)) = (A'.card : ℝ) * (maxDegA : ℝ) := by
      simp [Finset.sum_const] <;> ring
    have h10 : (↑(∑ a ∈ A', degAInd E A' B' a) : ℝ) = ∑ a ∈ A', (degAInd E A' B' a : ℝ) := by
      rw [Nat.cast_sum]
    rw [h10]
    rw [h9] at h8
    exact h8
  have h_divA : ((A'.card : ℝ) * (maxDegA : ℝ)) / (maxDegA : ℝ) = (A'.card : ℝ) := by
    have h15 : (maxDegA : ℝ) ≠ 0 := hmaxA_pos.ne'
    field_simp [h15] <;> ring
  have hA'_size : (A'.card : ℝ) ≥ (A.card : ℝ) * dA / (4 * (maxDegA : ℝ)) := by
    have h10 : (E.card : ℝ) = (A.card : ℝ) * dA := by
      rw [hdA] <;> field_simp [hA_pos.ne'] <;> ring
    have h11 : (A'.card : ℝ) ≥ (E'.card : ℝ) / (maxDegA : ℝ) := by
      calc (A'.card : ℝ)
        = ((A'.card : ℝ) * (maxDegA : ℝ)) / (maxDegA : ℝ) := h_divA.symm
      _ ≥ (E'.card : ℝ) / (maxDegA : ℝ) := by gcongr
    have h12 : (E'.card : ℝ) / (maxDegA : ℝ) ≥ ((E.card : ℝ) / 2) / (maxDegA : ℝ) := by gcongr
    have h13 : ((E.card : ℝ) / 2) / (maxDegA : ℝ) = ((A.card : ℝ) * dA) / (2 * (maxDegA : ℝ)) := by
      rw [h10] <;> ring
    have h15 : 0 ≤ (A.card : ℝ) * dA := by
      have h15a : 0 ≤ (A.card : ℝ) := by exact_mod_cast Nat.zero_le A.card
      have h15b : 0 ≤ dA := by linarith
      exact mul_nonneg h15a h15b
    have h16 : 0 < (maxDegA : ℝ) := hmaxA_pos
    have h17 : ((A.card : ℝ) * dA) / (2 * (maxDegA : ℝ)) =
                 2 * ((A.card : ℝ) * dA / (4 * (maxDegA : ℝ))) := by ring
    have h18 : 0 ≤ (A.card : ℝ) * dA / (4 * (maxDegA : ℝ)) := by
      apply div_nonneg
      · exact h15
      · have h19 : 0 ≤ (4 * (maxDegA : ℝ)) := by positivity
        exact h19
    have h14 : ((A.card : ℝ) * dA) / (2 * (maxDegA : ℝ)) ≥ (A.card : ℝ) * dA / (4 * (maxDegA : ℝ)) := by
      rw [h17] <;> linarith
    have h_final : (A'.card : ℝ) ≥ (A.card : ℝ) * dA / (4 * (maxDegA : ℝ)) := by
      calc (A'.card : ℝ)
        ≥ (E'.card : ℝ) / (maxDegA : ℝ) := h11
      _ ≥ ((E.card : ℝ) / 2) / (maxDegA : ℝ) := h12
      _ = ((A.card : ℝ) * dA) / (2 * (maxDegA : ℝ)) := h13
      _ ≥ (A.card : ℝ) * dA / (4 * (maxDegA : ℝ)) := h14
    exact h_final

  -- Size bound for B': |E'| ≤ |B'| * maxDegB
  have h_sumB : E'.card = ∑ b ∈ B', degBInd E A' B' b := edge_card_sum_degB E A' B'
  have h_deg_boundB : ∀ b ∈ B', degBInd E A' B' b ≤ maxDegB := by
    intro b hb
    have h6 : b ∈ B := hB'_sub hb
    have h7 : degBInd E A' B' b ≤ (E.filter (fun p : α × β => p.2 = b)).card :=
      degBInd_le_original E A' B' b
    exact h7.trans (hmaxB b h6)
  have hE'_le_B : (E'.card : ℝ) ≤ (B'.card : ℝ) * (maxDegB : ℝ) := by
    rw [h_sumB]
    have h8 : (∑ b ∈ B', (degBInd E A' B' b : ℝ)) ≤ ∑ b ∈ B', (maxDegB : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact_mod_cast h_deg_boundB i ‹_›
    have h9 : (∑ b ∈ B', (maxDegB : ℝ)) = (B'.card : ℝ) * (maxDegB : ℝ) := by
      simp [Finset.sum_const] <;> ring
    have h10 : (↑(∑ b ∈ B', degBInd E A' B' b) : ℝ) = ∑ b ∈ B', (degBInd E A' B' b : ℝ) := by
      rw [Nat.cast_sum]
    rw [h10]
    rw [h9] at h8
    exact h8
  have h_divB : ((B'.card : ℝ) * (maxDegB : ℝ)) / (maxDegB : ℝ) = (B'.card : ℝ) := by
    have h15 : (maxDegB : ℝ) ≠ 0 := hmaxB_pos.ne'
    field_simp [h15] <;> ring
  have hB'_size : (B'.card : ℝ) ≥ (B.card : ℝ) * dB / (4 * (maxDegB : ℝ)) := by
    have h10 : (E.card : ℝ) = (B.card : ℝ) * dB := by
      rw [hdB] <;> field_simp [hB_pos.ne'] <;> ring
    have h11 : (B'.card : ℝ) ≥ (E'.card : ℝ) / (maxDegB : ℝ) := by
      calc (B'.card : ℝ)
        = ((B'.card : ℝ) * (maxDegB : ℝ)) / (maxDegB : ℝ) := h_divB.symm
      _ ≥ (E'.card : ℝ) / (maxDegB : ℝ) := by gcongr
    have h12 : (E'.card : ℝ) / (maxDegB : ℝ) ≥ ((E.card : ℝ) / 2) / (maxDegB : ℝ) := by gcongr
    have h13 : ((E.card : ℝ) / 2) / (maxDegB : ℝ) = ((B.card : ℝ) * dB) / (2 * (maxDegB : ℝ)) := by
      rw [h10] <;> ring
    have h15 : 0 ≤ (B.card : ℝ) * dB := by
      have h15a : 0 ≤ (B.card : ℝ) := by exact_mod_cast Nat.zero_le B.card
      have h15b : 0 ≤ dB := by linarith
      exact mul_nonneg h15a h15b
    have h16 : 0 < (maxDegB : ℝ) := hmaxB_pos
    have h17 : ((B.card : ℝ) * dB) / (2 * (maxDegB : ℝ)) =
                 2 * ((B.card : ℝ) * dB / (4 * (maxDegB : ℝ))) := by ring
    have h18 : 0 ≤ (B.card : ℝ) * dB / (4 * (maxDegB : ℝ)) := by
      apply div_nonneg
      · exact h15
      · have h19 : 0 ≤ (4 * (maxDegB : ℝ)) := by positivity
        exact h19
    have h14 : ((B.card : ℝ) * dB) / (2 * (maxDegB : ℝ)) ≥ (B.card : ℝ) * dB / (4 * (maxDegB : ℝ)) := by
      rw [h17] <;> linarith
    have h_final : (B'.card : ℝ) ≥ (B.card : ℝ) * dB / (4 * (maxDegB : ℝ)) := by
      calc (B'.card : ℝ)
        ≥ (E'.card : ℝ) / (maxDegB : ℝ) := h11
      _ ≥ ((E.card : ℝ) / 2) / (maxDegB : ℝ) := h12
      _ = ((B.card : ℝ) * dB) / (2 * (maxDegB : ℝ)) := h13
      _ ≥ (B.card : ℝ) * dB / (4 * (maxDegB : ℝ)) := h14
    exact h_final

  -- Neighborhood condition: B' = E'.image Prod.snd
  have h_nbhd1 : E'.image Prod.snd ⊆ B' := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨p, hp, rfl⟩
    have h : p ∈ inducedEdges E A' B' := hp
    exact (Finset.mem_filter.mp h).2.2
  have h_nbhd2 : B' ⊆ E'.image Prod.snd := by
    intro b hb
    have hdeg : (degBInd E A' B' b : ℝ) ≥ dB / 4 := by
      have h : ¬ (degBInd E A' B' b : ℝ) < dB / 4 := h_no_low.2 b hb
      linarith
    have hpos : 0 < degBInd E A' B' b := by
      have h1 : (degBInd E A' B' b : ℝ) ≥ dB / 4 := hdeg
      have h2 : 0 < dB / 4 := by linarith
      have h3 : (degBInd E A' B' b : ℝ) > 0 := by linarith
      exact_mod_cast h3
    have h3 : (E'.filter (fun p : α × β => p.2 = b)).Nonempty := Finset.card_pos.mp hpos
    rcases h3 with ⟨p, hp⟩
    have h4 : p ∈ E' := (Finset.mem_filter.mp hp).1
    have h5 : p.2 = b := (Finset.mem_filter.mp hp).2
    exact Finset.mem_image.mpr ⟨p, h4, h5⟩
  have h_nbhd : B' = E'.image Prod.snd :=
    Finset.Subset.antisymm h_nbhd2 h_nbhd1

  have h_minA : ∀ a ∈ A', (dA / 4 : ℝ) ≤ (degAInd E A' B' a : ℝ) := by
    intro a ha
    have h : ¬ (degAInd E A' B' a : ℝ) < dA / 4 := h_no_low.1 a ha
    linarith
  have h_minB : ∀ b ∈ B', (dB / 4 : ℝ) ≤ (degBInd E A' B' b : ℝ) := by
    intro b hb
    have h : ¬ (degBInd E A' B' b : ℝ) < dB / 4 := h_no_low.2 b hb
    linarith
  exact ⟨A', B', hA'_sub, hB'_sub, h_minA, h_minB, h_nbhd, hA'_size, hB'_size⟩


-- ============================================================================
-- Frostman property inheritance
-- ============================================================================

section Helpers

variable {L : Type*} [PseudoMetricSpace L] [DecidableEq L]
variable {α : Type*} [DecidableEq α]

/-- If `dist ℓ c ≤ Δ` and `dist c x ≤ r` with `Δ ≤ r`, then `dist ℓ x ≤ 2 * r`. -/
lemma dist_le_two_r (x ℓ c : L) (Δ r : ℝ)
    (h1 : dist ℓ c ≤ Δ) (h2 : dist c x ≤ r) (hΔ : Δ ≤ r) :
    dist ℓ x ≤ 2 * r := by
  calc dist ℓ x ≤ dist ℓ c + dist c x := dist_triangle ℓ c x
    _ ≤ Δ + r := by linarith
    _ ≤ 2 * r := by linarith

/-- `(2 * r)^s = 2^s * r^s` for `r ≥ 0`. -/
lemma rpow_two_mul (r s : ℝ) (hr : 0 ≤ r) :
    (2 * r) ^ s = (2 : ℝ) ^ s * r ^ s := by
  exact Real.mul_rpow (by norm_num) hr

/--
Core Frostman inheritance lemma via incidence counting (due to indigo).

Given fine sets `T p` with Frostman property at scale `δ`, a coarse map,
and a selected family where each coarse point `c ∈ C'` has at least `H`
incidences, and the total size `∑_{p ∈ P'} |T p|` is bounded by `K * H * |C'|`,
then `C'` satisfies the Frostman ball bound at scale `Δ` with constant
`C₁ * 2^s * K`.
-/
lemma frostman_inheritance_core
    (δ Δ s C₁ : ℝ)
    (P : Finset α) (T : α → Finset L)
    (P' : Finset α) (T' : α → Finset L)
    (coarse : L → L) (C' : Finset L)
    (K H : ℝ)
    (hδ_pos : 0 < δ)
    (hδΔ : δ ≤ Δ)
    (hs : 0 ≤ s)
    (hC1 : 1 ≤ C₁)
    (hT_frostman : ∀ p ∈ P, BallGrowth δ s C₁ (T p))
    (hT'_sub : ∀ p ∈ P', T' p ⊆ T p)
    (hP'_sub : P' ⊆ P)
    (h_coarse_dist : ∀ ℓ ∈ P'.biUnion T', dist ℓ (coarse ℓ) ≤ Δ)
    (hH_lower : ∀ c ∈ C', H ≤ ∑ p ∈ P', assignedCount coarse T' p c)
    (h_sum_T_upper : (∑ p ∈ P', (T p).card : ℝ) ≤ K * H * (C'.card : ℝ))
    (hH_pos : 0 < H) :
    ∀ (x : L) (r : ℝ), Δ ≤ r →
      ((C'.filter fun c => dist c x ≤ r).card : ℝ) ≤
        (C₁ * (2 : ℝ) ^ s * K) * r ^ s * (C'.card : ℝ) := by
  intro x r hr
  have hr_pos : 0 ≤ r := by linarith [hδ_pos, hδΔ, hr]
  have h2r_ge_delta : δ ≤ 2 * r := by
    calc δ ≤ Δ := hδΔ
      _ ≤ r := hr
      _ ≤ 2 * r := by linarith
  set F : Finset L := C'.filter (fun c => dist c x ≤ r) with hF_def
  set I : ℕ := ∑ p ∈ P', ((T' p).filter (fun ℓ => dist ℓ x ≤ 2 * r)).card with hI_def
  -- For any ℓ with coarse ℓ ∈ F, we have dist ℓ x ≤ 2 * r
  have h_ball_expansion : ∀ ℓ ∈ P'.biUnion T', coarse ℓ ∈ F → dist ℓ x ≤ 2 * r := by
    intro ℓ hℓ hcoarseF
    have hcr : dist (coarse ℓ) x ≤ r := (Finset.mem_filter.mp hcoarseF).2
    have hdist1 : dist ℓ (coarse ℓ) ≤ Δ := h_coarse_dist ℓ hℓ
    exact dist_le_two_r x ℓ (coarse ℓ) Δ r hdist1 hcr hr
  -- Lower bound: H * |F| ≤ total incidences in expanded ball
  have h_lower : H * (F.card : ℝ) ≤ (I : ℝ) := by
    have h1 : ∀ p ∈ P',
        ((T' p).filter (fun ℓ => coarse ℓ ∈ F)).card ≤
        ((T' p).filter (fun ℓ => dist ℓ x ≤ 2 * r)).card := by
      intro p hp
      apply Finset.card_le_card
      intro ℓ hℓ
      have hℓ_in_T' : ℓ ∈ T' p := (Finset.mem_filter.mp hℓ).1
      have hcoarseF : coarse ℓ ∈ F := (Finset.mem_filter.mp hℓ).2
      have hℓ_in_union : ℓ ∈ P'.biUnion T' := Finset.mem_biUnion.mpr ⟨p, hp, hℓ_in_T'⟩
      exact Finset.mem_filter.mpr ⟨hℓ_in_T', h_ball_expansion ℓ hℓ_in_union hcoarseF⟩
    have h2 : ∑ c ∈ F, (∑ p ∈ P', assignedCount coarse T' p c : ℝ) ≤ (I : ℝ) := by
      calc ∑ c ∈ F, (∑ p ∈ P', assignedCount coarse T' p c : ℝ)
          = ∑ p ∈ P', ∑ c ∈ F, (assignedCount coarse T' p c : ℝ) := by
            rw [Finset.sum_comm]
        _ = ∑ p ∈ P', (((T' p).filter (fun ℓ => coarse ℓ ∈ F)).card : ℝ) := by
            apply Finset.sum_congr rfl
            intro p _
            simp only [assignedCount]
            exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter (T' p) F coarse
        _ ≤ ∑ p ∈ P', (((T' p).filter (fun ℓ => dist ℓ x ≤ 2 * r)).card : ℝ) := by
            apply Finset.sum_le_sum
            intro p hp
            exact_mod_cast h1 p hp
        _ = (I : ℝ) := by
            simp only [hI_def] <;> norm_cast
    have h3 : ∑ c ∈ F, H ≤ ∑ c ∈ F, (∑ p ∈ P', assignedCount coarse T' p c : ℝ) := by
      apply Finset.sum_le_sum
      intro c hc
      have hcC' : c ∈ C' := (Finset.mem_filter.mp hc).1
      exact_mod_cast hH_lower c hcC'
    have h4 : ∑ c ∈ F, H = H * (F.card : ℝ) := by
      simp [Finset.sum_const] <;> ring
    rw [h4] at h3
    exact le_trans h3 h2
  -- Upper bound: I ≤ C₁ * (2r)^s * ∑_{p ∈ P'} |T p|
  have h_upper : (I : ℝ) ≤ C₁ * (2 * r) ^ s * (∑ p ∈ P', (T p).card : ℝ) := by
    have hI_cast : (I : ℝ) = ∑ p ∈ P', (((T' p).filter (fun ℓ => dist ℓ x ≤ 2 * r)).card : ℝ) := by
      simp [hI_def] <;> norm_cast
    rw [hI_cast]
    calc ∑ p ∈ P', (((T' p).filter (fun ℓ => dist ℓ x ≤ 2 * r)).card : ℝ)
        ≤ ∑ p ∈ P', (((T p).filter (fun ℓ => dist ℓ x ≤ 2 * r)).card : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          have hsub : (T' p).filter (fun ℓ => dist ℓ x ≤ 2 * r) ⊆
              (T p).filter (fun ℓ => dist ℓ x ≤ 2 * r) := by
            apply Finset.filter_subset_filter
            exact hT'_sub p hp
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ p ∈ P', (C₁ * (2 * r) ^ s * ((T p).card : ℝ)) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpfrost : BallGrowth δ s C₁ (T p) := hT_frostman p (hP'_sub hp)
          have h_frost : ∀ (x : L) (r : ℝ), δ ≤ r →
              (((T p).filter fun y => dist y x ≤ r).card : ℝ) ≤
                C₁ * r ^ s * ((T p).card : ℝ) := hpfrost.growth
          exact h_frost x (2 * r) h2r_ge_delta
      _ = C₁ * (2 * r) ^ s * (∑ p ∈ P', (T p).card : ℝ) := by
          rw [Finset.mul_sum] <;> simp [mul_assoc]
  -- Combine and cancel H
  have h_main : H * (F.card : ℝ) ≤ C₁ * (2 * r) ^ s * (∑ p ∈ P', (T p).card : ℝ) :=
    le_trans h_lower h_upper
  have h5 : H * (F.card : ℝ) ≤ C₁ * (2 * r) ^ s * (K * H * (C'.card : ℝ)) := by
    calc H * (F.card : ℝ)
        ≤ C₁ * (2 * r) ^ s * (∑ p ∈ P', (T p).card : ℝ) := h_main
      _ ≤ C₁ * (2 * r) ^ s * (K * H * (C'.card : ℝ)) := by gcongr <;> linarith
  have h6 : H * (F.card : ℝ) ≤ H * (C₁ * (2 * r) ^ s * K * (C'.card : ℝ)) := by
    convert h5 using 1 <;> ring
  have h7 : (F.card : ℝ) ≤ C₁ * (2 * r) ^ s * K * (C'.card : ℝ) :=
    le_of_mul_le_mul_left h6 hH_pos
  have h8 : (2 * r) ^ s = (2 : ℝ) ^ s * r ^ s := rpow_two_mul r s hr_pos
  rw [h8] at h7
  have h9 : (F.card : ℝ) ≤ (C₁ * (2 : ℝ) ^ s * K) * r ^ s * (C'.card : ℝ) := by
    convert h7 using 1 <;> ring
  exact h9


/--
A coarse separated set inherits the cardinal Frostman property from fine sets,
given a uniform incidence structure.

Given:
- Each `T p` is a `(δ, s, Cfrost)`-Frostman set with `|T p| ≤ M`
- Each `c ∈ S p` has `m₁/2 < assignedCount coarse T p c ≤ m₁`
- Each `c ∈ Cset` has `H/2 < |{p ∈ P₁ : c ∈ S p}| ≤ H`
- `M ≤ K₁ * m₁ * m₂`
- `m₂ * |P₁| ≤ L₃ * H * |Cset|`

Then `Cset` is a `(Δ, s, C₂)`-Frostman set with
`C₂ = 2^(s+2) * Cfrost * K₁ * L₃`.
-/
theorem frostman_inheritance
    {α L : Type*} [PseudoMetricSpace L] [DecidableEq α] [DecidableEq L]
    (δ Δ s Cfrost : ℝ)
    (M m₁ m₂ H : ℕ)
    (K₁ L₃ : ℝ)
    (P₁ : Finset α)
    (Cset : Finset L)
    (S : α → Finset L)
    (T : α → Finset L)
    (coarse : L → L)
    (coarseRange : Finset L)
    (U : Finset L)
    (hδ : 0 < δ)
    (hδΔ : δ ≤ Δ)
    (hs : 0 ≤ s)
    (hCfrost : 1 ≤ Cfrost)
    (hK₁ : 1 ≤ K₁)
    (hL₃ : 1 ≤ L₃)
    (hM : 0 < M)
    (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂)
    (hH : 0 < H)
    (hP1nonempty : P₁.Nonempty)
    (hS1 : ∀ p ∈ P₁, S p ⊆ Cset)
    (hT : ∀ p ∈ P₁, T p ⊆ U)
    (hFrost : ∀ p ∈ P₁, BallGrowth δ s Cfrost (T p))
    (hTcard : ∀ p ∈ P₁, (T p).card ≤ M)
    (hcoarse : ∀ ℓ ∈ U, coarse ℓ ∈ coarseRange ∧ dist ℓ (coarse ℓ) ≤ Δ)
    (hsep : SeparatedAt Δ (coarseRange : Set L))
    (hCsub : Cset ⊆ coarseRange)
    (hassigned : ∀ p ∈ P₁, ∀ c ∈ S p,
        (m₁ : ℝ) / 2 < (assignedCount coarse T p c : ℝ) ∧
        (assignedCount coarse T p c : ℝ) ≤ (m₁ : ℝ))
    (hScard : ∀ p ∈ P₁,
        (m₂ : ℝ) ≤ (S p).card ∧ (S p).card < 2 * (m₂ : ℝ))
    (hcoverage : ∀ c ∈ Cset,
        (H : ℝ) / 2 < ((P₁.filter (fun p => c ∈ S p)).card : ℝ) ∧
        ((P₁.filter (fun p => c ∈ S p)).card : ℝ) ≤ (H : ℝ))
    (hprod : (M : ℝ) ≤ K₁ * (m₁ : ℝ) * (m₂ : ℝ))
    (hcov : (m₂ : ℝ) * (P₁.card : ℝ) ≤ L₃ * (H : ℝ) * (Cset.card : ℝ)) :
    IsFiniteDeltaSSet Δ s (Real.rpow 2 (s + 2) * Cfrost * K₁ * L₃) Cset := by
  let H' : ℝ := (H : ℝ) * (m₁ : ℝ) / 4
  let K' : ℝ := 4 * K₁ * L₃
  let C₂ : ℝ := Real.rpow 2 (s + 2) * Cfrost * K₁ * L₃
  have hΔpos : 0 < Δ := by linarith
  have hH'pos : 0 < H' := by positivity
  have hK'one : 1 ≤ K' := by
    have h1 : 1 ≤ 4 * K₁ * L₃ := by
      have h2 : 1 ≤ K₁ := hK₁
      have h3 : 1 ≤ L₃ := hL₃
      nlinarith
    simpa [K'] using h1
  have hC2one : 1 ≤ C₂ := by
    have h1 : 1 ≤ Real.rpow 2 (s + 2) := by
      apply Real.one_le_rpow <;> norm_num <;> linarith
    have h2 : 1 ≤ Cfrost * K₁ * L₃ := by
      calc 1 = 1 * 1 * 1 := by ring
        _ ≤ Cfrost * K₁ * L₃ := by gcongr <;> linarith
    have h3 : 1 ≤ Real.rpow 2 (s + 2) * (Cfrost * K₁ * L₃) := by
      calc 1 = 1 * 1 := by ring
        _ ≤ Real.rpow 2 (s + 2) * (Cfrost * K₁ * L₃) := by gcongr <;> linarith
    have h4 : Real.rpow 2 (s + 2) * (Cfrost * K₁ * L₃) = C₂ := by
      simp [C₂] <;> ring
    rw [h4] at h3
    exact h3
  have hCnonempty : Cset.Nonempty := by
    by_contra h
    have h4 : Cset.card = 0 := by simpa [Finset.not_nonempty_iff_eq_empty] using h
    have h5 : (m₂ : ℝ) * (P₁.card : ℝ) > 0 := by
      have h51 : (m₂ : ℝ) > 0 := by exact_mod_cast hm₂
      have h52 : (P₁.card : ℝ) > 0 := by exact_mod_cast hP1nonempty.card_pos
      positivity
    rw [h4] at hcov
    norm_num at hcov <;> linarith
  have hsepC : SeparatedAt Δ (Cset : Set L) := by
    have h : SeparatedAt Δ (Cset : Set L) := hsep.mono hCsub
    intro x hx y hy hne
    have h2 : Δ ≤ dist x y := h hx hy hne
    linarith
  -- hH_lower: H' ≤ ∑_{p ∈ P₁} assignedCount coarse T p c for each c ∈ Cset
  have hH_lower : ∀ c ∈ Cset, H' ≤ ∑ p ∈ P₁, (assignedCount coarse T p c : ℝ) := by
    intro c hc
    let Q := P₁.filter (fun p => c ∈ S p)
    have hQpos : (H : ℝ) / 2 < (Q.card : ℝ) := (hcoverage c hc).1
    have hQnonempty : Q.Nonempty := by
      have h : (Q.card : ℝ) > 0 := by linarith [hQpos]
      exact Finset.card_pos.mp (by exact_mod_cast h)
    have h1 : ∀ p ∈ Q, (m₁ : ℝ) / 2 < (assignedCount coarse T p c : ℝ) := by
      intro p hp
      have hpP1 : p ∈ P₁ := (Finset.mem_filter.mp hp).1
      have hcs : c ∈ S p := (Finset.mem_filter.mp hp).2
      exact (hassigned p hpP1 c hcs).1
    have h2 : ∑ p ∈ Q, (assignedCount coarse T p c : ℝ) > (Q.card : ℝ) * (m₁ : ℝ) / 2 := by
      obtain ⟨p0, hp0⟩ := hQnonempty
      have h3 : ∑ p ∈ Q, (assignedCount coarse T p c : ℝ) > ∑ p ∈ Q, ((m₁ : ℝ) / 2) := by
        exact Finset.sum_lt_sum (fun p hp => le_of_lt (h1 p hp)) ⟨p0, hp0, h1 p0 hp0⟩
      have h4 : ∑ p ∈ Q, ((m₁ : ℝ) / 2) = (Q.card : ℝ) * ((m₁ : ℝ) / 2) := by
        simp [Finset.sum_const] <;> ring
      rw [h4] at h3
      have h5 : (Q.card : ℝ) * ((m₁ : ℝ) / 2) = (Q.card : ℝ) * (m₁ : ℝ) / 2 := by ring
      rw [h5] at h3
      exact h3
    have h4 : ∑ p ∈ Q, (assignedCount coarse T p c : ℝ) ≤ ∑ p ∈ P₁, (assignedCount coarse T p c : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      exact Finset.filter_subset _ _
      intro i _ _
      exact Nat.cast_nonneg _
    have h5 : H' < ∑ p ∈ P₁, (assignedCount coarse T p c : ℝ) := by
      have h6 : (H : ℝ) / 2 < (Q.card : ℝ) := hQpos
      have h7 : (H : ℝ) * (m₁ : ℝ) / 4 < (Q.card : ℝ) * (m₁ : ℝ) / 2 := by
        have hm1pos : (m₁ : ℝ) > 0 := by exact_mod_cast hm₁
        calc (H : ℝ) * (m₁ : ℝ) / 4
            = ((H : ℝ) / 2) * ((m₁ : ℝ) / 2) := by ring
          _ < (Q.card : ℝ) * ((m₁ : ℝ) / 2) := by gcongr
          _ = (Q.card : ℝ) * (m₁ : ℝ) / 2 := by ring
      calc H'
          = (H : ℝ) * (m₁ : ℝ) / 4 := by rfl
        _ < (Q.card : ℝ) * (m₁ : ℝ) / 2 := h7
        _ < ∑ p ∈ Q, (assignedCount coarse T p c : ℝ) := h2
        _ ≤ ∑ p ∈ P₁, (assignedCount coarse T p c : ℝ) := h4
    exact h5.le
  -- h_sum_T_upper: ∑ |T p| ≤ K' * H' * |Cset|
  have h_sum_T_upper : (∑ p ∈ P₁, (T p).card : ℝ) ≤ K' * H' * (Cset.card : ℝ) := by
    have h1 : (∑ p ∈ P₁, (T p).card : ℝ) ≤ (P₁.card : ℝ) * (M : ℝ) := by
      have h2 : ∑ p ∈ P₁, (T p).card ≤ P₁.card * M := by
        calc ∑ p ∈ P₁, (T p).card
            ≤ ∑ p ∈ P₁, M := Finset.sum_le_sum (fun p hp => hTcard p hp)
          _ = P₁.card * M := by simp [Finset.sum_const] <;> ring
      exact_mod_cast h2
    have hm2pos : (m₂ : ℝ) > 0 := by exact_mod_cast hm₂
    have hHpos : (H : ℝ) > 0 := by exact_mod_cast hH
    have h3 : (P₁.card : ℝ) * (M : ℝ) ≤ K' * H' * (Cset.card : ℝ) := by
      have h4 : (P₁.card : ℝ) ≤ L₃ * (H : ℝ) * (Cset.card : ℝ) / (m₂ : ℝ) := by
        calc (P₁.card : ℝ)
            = ((m₂ : ℝ) * (P₁.card : ℝ)) / (m₂ : ℝ) := by field_simp [hm2pos.ne'] <;> ring
          _ ≤ (L₃ * (H : ℝ) * (Cset.card : ℝ)) / (m₂ : ℝ) := by gcongr
      calc (P₁.card : ℝ) * (M : ℝ)
          ≤ (L₃ * (H : ℝ) * (Cset.card : ℝ) / (m₂ : ℝ)) * (M : ℝ) := by gcongr
        _ ≤ (L₃ * (H : ℝ) * (Cset.card : ℝ) / (m₂ : ℝ)) * (K₁ * (m₁ : ℝ) * (m₂ : ℝ)) := by gcongr
        _ = K' * H' * (Cset.card : ℝ) := by
          simp [K', H'] <;> field_simp <;> ring
    exact h1.trans h3
  -- h_coarse_dist
  have h_coarse_dist : ∀ ℓ ∈ P₁.biUnion T, dist ℓ (coarse ℓ) ≤ Δ := by
    intro ℓ hℓ
    rcases Finset.mem_biUnion.mp hℓ with ⟨p, hp, hℓT⟩
    have h2 : ℓ ∈ U := hT p hp hℓT
    exact (hcoarse ℓ h2).2
  -- Constant equality: Cfrost * 2^s * K' = C₂
  have hC_eq : Cfrost * (2 : ℝ) ^ s * K' = C₂ := by
    have h51 : Real.rpow 2 (s + 2) = Real.rpow 2 s * Real.rpow 2 (2 : ℝ) :=
      Real.rpow_add (by norm_num) s (2 : ℝ)
    have h52 : Real.rpow 2 (2 : ℝ) = 4 := by norm_num
    have h5 : Real.rpow 2 (s + 2) = 4 * Real.rpow 2 s := by
      rw [h51, h52] <;> ring
    have h81 : (2 : ℝ) ^ s = Real.rpow 2 s := by rfl
    have h8 : Cfrost * (2 : ℝ) ^ s * K' = Real.rpow 2 s * Cfrost * (4 * K₁ * L₃) := by
      rw [h81]
      have hK'eq : K' = 4 * K₁ * L₃ := by rfl
      rw [hK'eq] <;> ring
    have h9 : C₂ = Real.rpow 2 (s + 2) * Cfrost * K₁ * L₃ := by rfl
    rw [h8, h9, h5] <;> ring
  -- Convert hH_lower to the type expected by the core lemma
  have hH_lower' : ∀ c ∈ Cset, H' ≤ ↑(∑ p ∈ P₁, assignedCount coarse T p c) := by
    intro c hc
    have h7 : (∑ p ∈ P₁, (assignedCount coarse T p c : ℝ)) = ↑(∑ p ∈ P₁, assignedCount coarse T p c) := by
      rw [Nat.cast_sum] <;> rfl
    have h8 : H' ≤ (∑ p ∈ P₁, (assignedCount coarse T p c : ℝ)) := hH_lower c hc
    rw [h7] at *
    exact h8
  -- Apply core lemma
  have h_core : ∀ (x : L) (r : ℝ), Δ ≤ r →
      ((Cset.filter fun c => dist c x ≤ r).card : ℝ) ≤
        (Cfrost * (2 : ℝ) ^ s * K') * r ^ s * (Cset.card : ℝ) :=
    frostman_inheritance_core δ Δ s Cfrost P₁ T P₁ T coarse Cset K' H'
      hδ hδΔ hs hCfrost hFrost (fun p _ => subset_refl (T p)) (subset_refl P₁)
      h_coarse_dist hH_lower' h_sum_T_upper hH'pos
  rw [hC_eq] at h_core
  exact ⟨hCnonempty, hΔpos, hC2one, hs, hsepC, h_core⟩


-- ============================================================================
-- Glue lemmas
-- ============================================================================

lemma image_eq_intersection
    {α L : Type*} [DecidableEq α] [DecidableEq L]
    (T : α → Finset L) (coarse : L → L)
    (C_p : α → Finset L) (C' : Finset L) (p : α)
    (hCp_sub : C_p p ⊆ C')
    (h_exists : ∀ c ∈ C_p p, ∃ ℓ ∈ T p, coarse ℓ = c) :
    ((T p).filter (fun ℓ => coarse ℓ ∈ C_p p)).image coarse = C_p p := by
  let T'p := (T p).filter (fun ℓ => coarse ℓ ∈ C_p p)
  have h1 : T'p.image coarse ⊆ C_p p := by
    intro c hc
    rcases mem_image.mp hc with ⟨ℓ, hℓ, rfl⟩
    exact (mem_filter.mp hℓ).2
  have h2 : C_p p ⊆ T'p.image coarse := by
    intro c hc
    rcases h_exists c hc with ⟨ℓ, hℓ, hcoarse⟩
    have h3 : ℓ ∈ T'p := by
      apply mem_filter.mpr
      exact ⟨hℓ, by rw [hcoarse] <;> exact hc⟩
    exact mem_image.mpr ⟨ℓ, h3, hcoarse⟩
  exact Finset.Subset.antisymm h1 h2

/-- If C' = P'.biUnion (fun p => S p) and for each p, (T' p).image coarse = S p,
    then C' = P'.biUnion (fun p => (T' p).image coarse). -/
lemma biUnion_from_images
    {α L : Type*} [DecidableEq α] [DecidableEq L]
    (P' : Finset α) (C' : Finset L) (S : α → Finset L)
    (T' : α → Finset L) (coarse : L → L)
    (hC' : C' = P'.biUnion S)
    (h_img : ∀ p ∈ P', (T' p).image coarse = S p) :
    C' = P'.biUnion (fun p => (T' p).image coarse) := by
  rw [hC']
  apply Finset.biUnion_congr rfl
  intro p hp
  exact (h_img p hp).symm

/-- Upper average bound: H_final * C'.card ≤ K * M * P.card.

    Uses: H_final ≤ totalAssigned c for all c, (T' p).card ≤ M, P' ⊆ P, K ≥ 1.
-/
lemma avg_upper_bound
    {α L : Type*} [DecidableEq α] [DecidableEq L]
    (P P' : Finset α) (T' : α → Finset L) (coarse : L → L) (C' : Finset L)
    (H_final : ℕ) (M : ℕ) (K : ℝ)
    (hP' : P' ⊆ P)
    (hK : 1 ≤ K)
    (hH : ∀ c ∈ C', (H_final : ℝ) ≤ ∑ p ∈ P', (assignedCount coarse T' p c : ℝ))
    (hM : ∀ p ∈ P', ((T' p).card : ℝ) ≤ (M : ℝ))
    (hcover : ∀ p ∈ P', (T' p).image coarse ⊆ C') :
    (H_final : ℝ) * (C'.card : ℝ) ≤ K * (M : ℝ) * (P.card : ℝ) := by
  set S : L → ℝ := fun c => ∑ p ∈ P', (assignedCount coarse T' p c : ℝ) with hS
  have h_total : ∑ c ∈ C', S c = ∑ p ∈ P', ((T' p).card : ℝ) := by
    have h1 : ∑ c ∈ C', S c = ∑ p ∈ P', ∑ c ∈ C', (assignedCount coarse T' p c : ℝ) := by
      rw [sum_comm] <;> rfl
    rw [h1]
    apply sum_congr rfl
    intro p hp
    have h2 : ∑ c ∈ C', (assignedCount coarse T' p c : ℝ) = ((T' p).card : ℝ) := by
      have h_maps : ((T' p : Set L).MapsTo coarse (C' : Set L)) := by
        intro x hx
        exact hcover p hp (mem_image_of_mem coarse hx)
      exact_mod_cast (card_eq_sum_card_fiberwise (f := coarse) (s := T' p) (t := C') h_maps).symm
    exact h2
  have h1 : (H_final : ℝ) * (C'.card : ℝ) ≤ ∑ c ∈ C', S c := by
    have h1a : C'.card • (H_final : ℝ) ≤ ∑ c ∈ C', S c := card_nsmul_le_sum C' S (H_final : ℝ) hH
    have h1b : C'.card • (H_final : ℝ) = (H_final : ℝ) * (C'.card : ℝ) := by
      simp [nsmul_eq_mul, mul_comm]
    rw [h1b] at h1a
    exact h1a
  have h2 : ∑ p ∈ P', ((T' p).card : ℝ) ≤ (P'.card : ℝ) * (M : ℝ) := by
    have h2a : ∑ p ∈ P', ((T' p).card : ℝ) ≤ P'.card • (M : ℝ) := sum_le_card_nsmul P' (fun p => ((T' p).card : ℝ)) (M : ℝ) hM
    have h2b : P'.card • (M : ℝ) = (P'.card : ℝ) * (M : ℝ) := by simp [nsmul_eq_mul]
    rw [h2b] at h2a
    exact h2a
  have h3 : (P'.card : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast card_le_card hP'
  calc
    (H_final : ℝ) * (C'.card : ℝ)
      ≤ ∑ c ∈ C', S c := h1
    _ = ∑ p ∈ P', ((T' p).card : ℝ) := h_total
    _ ≤ (P'.card : ℝ) * (M : ℝ) := h2
    _ ≤ (P.card : ℝ) * (M : ℝ) := by gcongr
    _ ≤ K * (M : ℝ) * (P.card : ℝ) := by
      have h4 : 0 ≤ (P.card : ℝ) * (M : ℝ) := by positivity
      have h5 : (P.card : ℝ) * (M : ℝ) ≤ K * ((P.card : ℝ) * (M : ℝ)) := by
        calc
          (P.card : ℝ) * (M : ℝ)
            = 1 * ((P.card : ℝ) * (M : ℝ)) := by ring
          _ ≤ K * ((P.card : ℝ) * (M : ℝ)) := by gcongr
      simpa [mul_comm, mul_assoc, mul_left_comm] using h5

/-- Lower average bound with explicit balancing factor.

    If totalAssigned c ≤ bal * H_final for all c ∈ C', then
    M * P.card ≤ K^2 * bal * H_final * C'.card.

    In the main proof, bal = 1 (perfect balancing from construction)
    or bal is absorbed into K.
-/
lemma avg_lower_bound
    {α L : Type*} [DecidableEq α] [DecidableEq L]
    (P P' : Finset α) (T' : α → Finset L) (coarse : L → L) (C' : Finset L)
    (H_final : ℕ) (M : ℕ) (K bal : ℝ)
    (hK : 1 ≤ K)
    (hP : (P.card : ℝ) ≤ K * (P'.card : ℝ))
    (hM : ∀ p ∈ P', (M : ℝ) ≤ K * ((T' p).card : ℝ))
    (hH_upper : ∀ c ∈ C', (∑ p ∈ P', (assignedCount coarse T' p c : ℝ)) ≤ bal * (H_final : ℝ))
    (hcover : ∀ p ∈ P', (T' p).image coarse ⊆ C') :
    (M : ℝ) * (P.card : ℝ) ≤ K^2 * bal * (H_final : ℝ) * (C'.card : ℝ) := by
  set S : L → ℝ := fun c => ∑ p ∈ P', (assignedCount coarse T' p c : ℝ) with hS
  have h_total : ∑ c ∈ C', S c = ∑ p ∈ P', ((T' p).card : ℝ) := by
    have h1 : ∑ c ∈ C', S c = ∑ p ∈ P', ∑ c ∈ C', (assignedCount coarse T' p c : ℝ) := by
      rw [sum_comm] <;> rfl
    rw [h1]
    apply sum_congr rfl
    intro p hp
    have h2 : ∑ c ∈ C', (assignedCount coarse T' p c : ℝ) = ((T' p).card : ℝ) := by
      have h_maps : ((T' p : Set L).MapsTo coarse (C' : Set L)) := by
        intro x hx
        exact hcover p hp (mem_image_of_mem coarse hx)
      exact_mod_cast (card_eq_sum_card_fiberwise (f := coarse) (s := T' p) (t := C') h_maps).symm
    exact h2
  have h1 : ∑ c ∈ C', S c ≤ (C'.card : ℝ) * (bal * (H_final : ℝ)) := by
    have h1a : ∑ c ∈ C', S c ≤ C'.card • (bal * (H_final : ℝ)) := sum_le_card_nsmul C' S (bal * (H_final : ℝ)) hH_upper
    have h1b : C'.card • (bal * (H_final : ℝ)) = (C'.card : ℝ) * (bal * (H_final : ℝ)) := by simp [nsmul_eq_mul]
    rw [h1b] at h1a
    exact h1a
  have h2 : (M : ℝ) * (P'.card : ℝ) ≤ K * ∑ p ∈ P', ((T' p).card : ℝ) := by
    calc
      (M : ℝ) * (P'.card : ℝ)
        = (P'.card : ℝ) * (M : ℝ) := by ring
      _ = ∑ p ∈ P', (M : ℝ) := by simp [sum_const]
      _ ≤ ∑ p ∈ P', K * ((T' p).card : ℝ) := sum_le_sum hM
      _ = K * ∑ p ∈ P', ((T' p).card : ℝ) := by
        rw [← Finset.mul_sum] <;> rfl
  calc
    (M : ℝ) * (P.card : ℝ)
      ≤ K * ((M : ℝ) * (P'.card : ℝ)) := by
        have hpos : 0 ≤ (M : ℝ) := by positivity
        nlinarith
    _ ≤ K * (K * ∑ p ∈ P', ((T' p).card : ℝ)) := by gcongr
    _ = K^2 * ∑ p ∈ P', ((T' p).card : ℝ) := by ring
    _ = K^2 * ∑ c ∈ C', S c := by rw [h_total]
    _ ≤ K^2 * ((C'.card : ℝ) * (bal * (H_final : ℝ))) := by gcongr
    _ = K^2 * bal * (H_final : ℝ) * (C'.card : ℝ) := by ring


lemma incidence_card_eq
    {α L : Type*} [DecidableEq α] [DecidableEq L]
    (P1 : Finset α) (C1 : Finset L) (C_p : α → Finset L) :
    ((P1 ×ˢ C1).filter (fun pc : α × L => pc.2 ∈ C_p pc.1)).card =
    ∑ c ∈ C1, (P1.filter (fun p => c ∈ C_p p)).card := by
  let n : L → Finset α := fun c => P1.filter (fun p => c ∈ C_p p)
  have h_disj : (C1 : Set L).PairwiseDisjoint (fun c => (n c).image (fun p : α => (p, c))) := by
    intro c1 _ c2 _ hne
    simp only [disjoint_left, mem_image]
    intro x hx1 hx2
    rcases hx1 with ⟨p1, _, rfl⟩
    rcases hx2 with ⟨p2, _, h⟩
    injection h with _ h2
    exact hne h2.symm
  have h1 : (P1 ×ˢ C1).filter (fun pc : α × L => pc.2 ∈ C_p pc.1) =
      C1.biUnion (fun c => (n c).image (fun p : α => (p, c))) := by
    ext x
    rcases x with ⟨p, c⟩
    have h_iff : ((p, c) ∈ (P1 ×ˢ C1).filter (fun pc : α × L => pc.2 ∈ C_p pc.1)) ↔
        ((p, c) ∈ C1.biUnion (fun c => (n c).image (fun p : α => (p, c)))) := by
      constructor
      · intro h
        rcases mem_filter.mp h with ⟨hprod, hCp⟩
        rcases mem_product.mp hprod with ⟨hP1, hC1⟩
        refine mem_biUnion.mpr ⟨c, hC1, ?_⟩
        have h5 : p ∈ n c := by
          simpa [n] using ⟨hP1, hCp⟩
        exact mem_image.mpr ⟨p, h5, rfl⟩
      · intro h
        rcases mem_biUnion.mp h with ⟨c', hc', himg⟩
        rcases mem_image.mp himg with ⟨p', hp', heq⟩
        have hpe : p' = p := congrArg Prod.fst heq
        have hce : c' = c := congrArg Prod.snd heq
        subst hpe hce
        rcases mem_filter.mp hp' with ⟨hP12, hCp2⟩
        exact mem_filter.mpr ⟨mem_product.mpr ⟨hP12, hc'⟩, hCp2⟩
    exact h_iff
  rw [h1]
  rw [card_biUnion h_disj]
  apply sum_congr rfl
  intro c _
  have h_inj : Function.Injective (fun p : α => (p, c)) := by
    intro p1 p2 h
    exact congrArg Prod.fst h
  exact card_image_of_injective _ h_inj

/-- Lower bound: E.card ≥ H * |C1| ≥ m2 * |P1| / (4L). -/
lemma hI_lower
    {α L : Type*} [DecidableEq α] [DecidableEq L]
    (P1 : Finset α) (C1 : Finset L) (C_p : α → Finset L)
    (m2 H : ℕ) (L_levels : ℕ)
    (h_n_lower : ∀ c ∈ C1, H ≤ (P1.filter (fun p => c ∈ C_p p)).card)
    (h_mass : (H : ℝ) * (C1.card : ℝ) ≥ (m2 : ℝ) * (P1.card : ℝ) / (4 * L_levels)) :
    (((P1 ×ˢ C1).filter (fun pc : α × L => pc.2 ∈ C_p pc.1)).card : ℝ) ≥
    (m2 : ℝ) * (P1.card : ℝ) / (4 * L_levels) := by
  have hE_eq : ((P1 ×ˢ C1).filter (fun pc : α × L => pc.2 ∈ C_p pc.1)).card =
      ∑ c ∈ C1, (P1.filter (fun p => c ∈ C_p p)).card :=
    incidence_card_eq P1 C1 C_p
  have hE_cast : (((P1 ×ˢ C1).filter (fun pc : α × L => pc.2 ∈ C_p pc.1)).card : ℝ) =
      ∑ c ∈ C1, ((P1.filter (fun p => c ∈ C_p p)).card : ℝ) := by
    rw [hE_eq]
    <;> simp [Nat.cast_sum]
    <;> rfl
  rw [hE_cast]
  have h2 : ∑ c ∈ C1, ((P1.filter (fun p => c ∈ C_p p)).card : ℝ) ≥
      (C1.card : ℝ) * (H : ℝ) := by
    have h2a : ∀ c ∈ C1, (H : ℝ) ≤ ((P1.filter (fun p => c ∈ C_p p)).card : ℝ) := by
      intro c hc
      exact_mod_cast h_n_lower c hc
    have h2b : C1.card • (H : ℝ) ≤ ∑ c ∈ C1, ((P1.filter (fun p => c ∈ C_p p)).card : ℝ) :=
      card_nsmul_le_sum C1 (fun c => ((P1.filter (fun p => c ∈ C_p p)).card : ℝ)) (H : ℝ) h2a
    have h2c : C1.card • (H : ℝ) = (C1.card : ℝ) * (H : ℝ) := by simp [nsmul_eq_mul]
    rw [h2c] at h2b
    exact h2b
  linarith

/-- Upper bound: E.card < 2H * |C1|. -/
lemma hI_upper
    {α L : Type*} [DecidableEq α] [DecidableEq L]
    (P1 : Finset α) (C1 : Finset L) (C_p : α → Finset L)
    (H : ℕ)
    (h_n_upper : ∀ c ∈ C1, (P1.filter (fun p => c ∈ C_p p)).card < 2 * H)
    (hC1_nonempty : C1.Nonempty) :
    (((P1 ×ˢ C1).filter (fun pc : α × L => pc.2 ∈ C_p pc.1)).card : ℝ) <
    2 * (H : ℝ) * (C1.card : ℝ) := by
  have hE_eq : ((P1 ×ˢ C1).filter (fun pc : α × L => pc.2 ∈ C_p pc.1)).card =
      ∑ c ∈ C1, (P1.filter (fun p => c ∈ C_p p)).card :=
    incidence_card_eq P1 C1 C_p
  have hE_cast : (((P1 ×ˢ C1).filter (fun pc : α × L => pc.2 ∈ C_p pc.1)).card : ℝ) =
      ∑ c ∈ C1, ((P1.filter (fun p => c ∈ C_p p)).card : ℝ) := by
    rw [hE_eq] <;> simp [Nat.cast_sum] <;> rfl
  rw [hE_cast]
  have h2a : ∀ c ∈ C1, ((P1.filter (fun p => c ∈ C_p p)).card : ℝ) < 2 * (H : ℝ) := by
    intro c hc
    exact_mod_cast h_n_upper c hc
  have h2b : ∑ c ∈ C1, ((P1.filter (fun p => c ∈ C_p p)).card : ℝ) <
      ∑ c ∈ C1, (2 * (H : ℝ)) := sum_lt_sum_of_nonempty hC1_nonempty h2a
  have h2c : ∑ c ∈ C1, (2 * (H : ℝ)) = (C1.card : ℝ) * (2 * (H : ℝ)) := by
    simp [sum_const] <;> ring
  rw [h2c] at h2b
  have h3 : (C1.card : ℝ) * (2 * (H : ℝ)) = 2 * (H : ℝ) * (C1.card : ℝ) := by ring
  rw [h3] at h2b
  exact h2b

-- ============================================================================
-- 2. Max degree bounds
-- ============================================================================

/-- Max degree on A side: degree(p) ≤ 2*m2. -/
lemma hmaxA
    {α L : Type*} [DecidableEq α] [DecidableEq L]
    (P1 : Finset α) (C1 : Finset L) (C_p : α → Finset L)
    (m2 : ℕ)
    (h_m2_upper : ∀ p ∈ P1, (C_p p).card < 2 * m2)
    (p : α) (hp : p ∈ P1) :
    (((P1 ×ˢ C1).filter (fun pc : α × L => pc.2 ∈ C_p pc.1)).filter
      (fun e : α × L => e.1 = p)).card ≤ 2 * m2 := by
  let E := (P1 ×ˢ C1).filter (fun pc : α × L => pc.2 ∈ C_p pc.1)
  let S := C_p p ∩ C1
  have h1 : (E.filter (fun e : α × L => e.1 = p)) = S.image (fun c : L => (p, c)) := by
    ext x
    rcases x with ⟨p', c⟩
    simp [E, S, mem_image]
    <;> constructor <;> intro h <;> aesop
  have h_inj : Function.Injective (fun c : L => (p, c)) := by
    intro c1 c2 h
    exact congrArg Prod.snd h
  have h2 : (S.image (fun c : L => (p, c))).card = S.card :=
    card_image_of_injective _ h_inj
  have h3 : S.card ≤ (C_p p).card := by
    have h4 : S ⊆ C_p p := by
      simp [S]
      <;> tauto
    exact card_le_card h4
  have h5 : (C_p p).card < 2 * m2 := h_m2_upper p hp
  have h6 : ((E.filter (fun e : α × L => e.1 = p))).card ≤ 2 * m2 := by
    have h7 : ((E.filter (fun e : α × L => e.1 = p))).card < 2 * m2 := by
      calc
        ((E.filter (fun e : α × L => e.1 = p))).card
          = (S.image (fun c : L => (p, c))).card := by rw [h1]
        _ = S.card := h2
        _ ≤ (C_p p).card := h3
        _ < 2 * m2 := h5
    exact le_of_lt h7
  exact h6

/-- Max degree on B side: degree(c) < 2H. -/
lemma hmaxB
    {α L : Type*} [DecidableEq α] [DecidableEq L]
    (P1 : Finset α) (C1 : Finset L) (C_p : α → Finset L)
    (H : ℕ)
    (h_n_upper : ∀ c ∈ C1, (P1.filter (fun p => c ∈ C_p p)).card < 2 * H)
    (c : L) (hc : c ∈ C1) :
    (((P1 ×ˢ C1).filter (fun pc : α × L => pc.2 ∈ C_p pc.1)).filter
      (fun e : α × L => e.2 = c)).card < 2 * H := by
  let E := (P1 ×ˢ C1).filter (fun pc : α × L => pc.2 ∈ C_p pc.1)
  let n : L → Finset α := fun c => P1.filter (fun p => c ∈ C_p p)
  have h1 : (E.filter (fun e : α × L => e.2 = c)) = (n c).image (fun p : α => (p, c)) := by
    ext x
    rcases x with ⟨p, c'⟩
    simp [E, n, mem_image]
    <;> constructor <;> intro h <;> aesop
  have h_inj : Function.Injective (fun p : α => (p, c)) := by
    intro p1 p2 h
    exact congrArg Prod.fst h
  have h2 : ((n c).image (fun p : α => (p, c))).card = (n c).card :=
    card_image_of_injective _ h_inj
  have h3 : ((E.filter (fun e : α × L => e.2 = c))).card < 2 * H := by
    calc
      ((E.filter (fun e : α × L => e.2 = c))).card
        = ((n c).image (fun p : α => (p, c))).card := by rw [h1]
      _ = (n c).card := h2
      _ < 2 * H := h_n_upper c hc
  exact h3

-- ============================================================================
-- 3. Image equality with C'
-- ============================================================================

/-- (T' p).image coarse = C_p p ∩ C'. -/
lemma image_eq_with_C'
    {α L : Type*} [DecidableEq α] [DecidableEq L]
    (T : α → Finset L) (coarse : L → L)
    (C_p : α → Finset L) (C' : Finset L) (p : α)
    (h_exists : ∀ c ∈ C_p p, ∃ ℓ ∈ T p, coarse ℓ = c) :
    ((T p).filter (fun ℓ => coarse ℓ ∈ C_p p ∩ C')).image coarse = C_p p ∩ C' := by
  let T'p := (T p).filter (fun ℓ => coarse ℓ ∈ C_p p ∩ C')
  have h1 : T'p.image coarse ⊆ C_p p ∩ C' := by
    intro c hc
    rcases mem_image.mp hc with ⟨ℓ, hℓ, rfl⟩
    exact (mem_filter.mp hℓ).2
  have h2 : C_p p ∩ C' ⊆ T'p.image coarse := by
    intro c hc
    have hc1 : c ∈ C_p p := (mem_inter.mp hc).1
    rcases h_exists c hc1 with ⟨ℓ, hℓ, hcoarse⟩
    have h3 : ℓ ∈ T'p := by
      apply mem_filter.mpr
      exact ⟨hℓ, by rw [hcoarse] <;> exact hc⟩
    exact mem_image.mpr ⟨ℓ, h3, hcoarse⟩
  exact Finset.Subset.antisymm h1 h2

-- ============================================================================
-- 4. Direct tight average lower bound
-- ============================================================================

/-- Direct lower bound: M * |P| ≤ K * H_final * |C'|. -/
lemma direct_avg_lower
    (M m1 m2 H H_final : ℕ) (P_card P'_card C'_card : ℕ)
    (L_levels : ℕ) (K : ℝ)
    (hL_pos : 1 ≤ L_levels)
    (hM_bound : (M : ℝ) ≤ 32 * (L_levels : ℝ) * (m1 : ℝ) * (m2 : ℝ))
    (hP_bound : (P_card : ℝ) ≤ 32 * (L_levels : ℝ)^3 * (P'_card : ℝ))
    (hm2_bound : (m2 : ℝ) * (P'_card : ℝ) ≤ 128 * (L_levels : ℝ) * (H : ℝ) * (C'_card : ℝ))
    (hH_final : (H_final : ℝ) ≥ (H : ℝ) * (m1 : ℝ) / 16)
    (hK : K = 2^21 * (L_levels : ℝ)^6) :
    (M : ℝ) * (P_card : ℝ) ≤ K * (H_final : ℝ) * (C'_card : ℝ) := by
  set L : ℝ := (L_levels : ℝ) with hL_def
  have hL1 : (1 : ℝ) ≤ L := by
    simpa [hL_def] using show (1 : ℝ) ≤ (L_levels : ℝ) from by exact_mod_cast hL_pos
  have h_pos1 : 0 ≤ (m1 : ℝ) := by positivity
  have h_pos2 : 0 ≤ (H : ℝ) := by positivity
  have h_pos3 : 0 ≤ (C'_card : ℝ) := by positivity
  have h_ineq1 : 131072 * L^5 ≤ (2^21 : ℝ) * L^6 / 16 := by
    have h : L ≥ 1 := hL1
    norm_num
    <;> nlinarith [pow_nonneg (show 0 ≤ L by linarith) 5]
  have h_main1 : (M : ℝ) * (P_card : ℝ) ≤
      131072 * L^5 * (m1 : ℝ) * (H : ℝ) * (C'_card : ℝ) := by
    calc
      (M : ℝ) * (P_card : ℝ)
        ≤ (32 * L * (m1 : ℝ) * (m2 : ℝ)) * (P_card : ℝ) := by gcongr
      _ ≤ (32 * L * (m1 : ℝ) * (m2 : ℝ)) * (32 * L^3 * (P'_card : ℝ)) := by gcongr
      _ = 1024 * L^4 * (m1 : ℝ) * ((m2 : ℝ) * (P'_card : ℝ)) := by ring
      _ ≤ 1024 * L^4 * (m1 : ℝ) * (128 * L * (H : ℝ) * (C'_card : ℝ)) := by gcongr
      _ = 131072 * L^5 * (m1 : ℝ) * (H : ℝ) * (C'_card : ℝ) := by ring
  have h_main2 : 131072 * L^5 * (m1 : ℝ) * (H : ℝ) * (C'_card : ℝ) ≤
      (2^21 : ℝ) * L^6 * (H_final : ℝ) * (C'_card : ℝ) := by
    have h4 : 131072 * L^5 * (m1 : ℝ) * (H : ℝ) * (C'_card : ℝ) ≤
        (2^21 : ℝ) * L^6 * ((H : ℝ) * (m1 : ℝ) / 16) * (C'_card : ℝ) := by
      calc
        131072 * L^5 * (m1 : ℝ) * (H : ℝ) * (C'_card : ℝ)
          = (131072 * L^5) * ((m1 : ℝ) * (H : ℝ)) * (C'_card : ℝ) := by ring
        _ ≤ ((2^21 : ℝ) * L^6 / 16) * ((m1 : ℝ) * (H : ℝ)) * (C'_card : ℝ) := by
          gcongr
        _ = (2^21 : ℝ) * L^6 * ((H : ℝ) * (m1 : ℝ) / 16) * (C'_card : ℝ) := by ring
    have h5 : (H : ℝ) * (m1 : ℝ) / 16 ≤ (H_final : ℝ) := by
      have h6 : (H : ℝ) * (m1 : ℝ) / 16 = (m1 : ℝ) * (H : ℝ) / 16 := by ring
      rw [h6]
      linarith [hH_final]
    calc
      131072 * L^5 * (m1 : ℝ) * (H : ℝ) * (C'_card : ℝ)
        ≤ (2^21 : ℝ) * L^6 * ((H : ℝ) * (m1 : ℝ) / 16) * (C'_card : ℝ) := h4
      _ ≤ (2^21 : ℝ) * L^6 * (H_final : ℝ) * (C'_card : ℝ) := by gcongr
  have h_final : (2^21 : ℝ) * L^6 * (H_final : ℝ) * (C'_card : ℝ) =
      K * (H_final : ℝ) * (C'_card : ℝ) := by
    rw [hK, hL_def] <;> ring
  rw [h_final] at h_main2
  exact le_trans h_main1 h_main2


-- ============================================================================
-- Frostman subset
-- ============================================================================

lemma frostman_subset
    {L : Type*} [PseudoMetricSpace L] [DecidableEq L]
    {Δ s C2 : ℝ} {C1 C' : Finset L} {factor : ℝ}
    (hC1 : IsFiniteDeltaSSet Δ s C2 C1)
    (hC'_sub : C' ⊆ C1)
    (hC'_nonempty : C'.Nonempty)
    (h_factor : 1 ≤ factor)
    (h_size : (C1.card : ℝ) ≤ factor * (C'.card : ℝ)) :
    IsFiniteDeltaSSet Δ s (factor * C2) C' := by
  have h1 : C'.Nonempty := hC'_nonempty
  have h2 : 0 < Δ := hC1.2.1
  have h3 : 1 ≤ factor * C2 := by
    have h3a : 1 ≤ C2 := hC1.2.2.1
    have h3b : 0 ≤ factor := by linarith
    nlinarith
  have h4 : 0 ≤ s := hC1.2.2.2.1
  have h5 : SeparatedAt Δ (C' : Set L) := by
    have h5a : SeparatedAt Δ (C1 : Set L) := hC1.2.2.2.2.1
    exact h5a.mono (show (C' : Set L) ⊆ (C1 : Set L) from hC'_sub)
  have h6 : ∀ x : L, ∀ r : ℝ, Δ ≤ r →
      ((C'.filter fun y => dist y x ≤ r).card : ℝ) ≤
        (factor * C2) * r ^ s * (C'.card : ℝ) := by
    intro x r hr
    have h7 : C'.filter (fun y => dist y x ≤ r) ⊆ C1.filter (fun y => dist y x ≤ r) := by
      intro y hy
      have h8 : y ∈ C' := (mem_filter.mp hy).1
      have h9 : dist y x ≤ r := (mem_filter.mp hy).2
      exact mem_filter.mpr ⟨hC'_sub h8, h9⟩
    have h10 : ((C'.filter fun y => dist y x ≤ r).card : ℝ) ≤
        ((C1.filter fun y => dist y x ≤ r).card : ℝ) := by
      exact_mod_cast card_le_card h7
    have h11 : ((C1.filter fun y => dist y x ≤ r).card : ℝ) ≤
        C2 * r ^ s * (C1.card : ℝ) := hC1.2.2.2.2.2 x r hr
    have h12 : (C1.card : ℝ) ≤ factor * (C'.card : ℝ) := h_size
    have hC2_pos : 0 ≤ C2 := by
      have h : 1 ≤ C2 := hC1.2.2.1
      linarith
    have hr_pos : 0 < r := by linarith
    have h13 : 0 ≤ C2 * r ^ s := by
      have h13a : 0 ≤ C2 := hC2_pos
      have h13b : 0 ≤ r ^ s := Real.rpow_nonneg (by linarith) s
      positivity
    calc
      ((C'.filter fun y => dist y x ≤ r).card : ℝ)
        ≤ ((C1.filter fun y => dist y x ≤ r).card : ℝ) := h10
      _ ≤ C2 * r ^ s * (C1.card : ℝ) := h11
      _ ≤ C2 * r ^ s * (factor * (C'.card : ℝ)) := by
        exact mul_le_mul_of_nonneg_left h12 h13
      _ = (factor * C2) * r ^ s * (C'.card : ℝ) := by ring
  exact ⟨h1, h2, h3, h4, h5, h6⟩

-- ============================================================================
-- Two-sided average bounds
-- ============================================================================

end Helpers

section TwoSidedAverage

variable {α L : Type*} [DecidableEq α] [DecidableEq L]

def totalAssigned (P' : Finset α) (T' : α → Finset L) (coarse : L → L) (c : L) : ℕ :=
  ∑ p ∈ P', ((T' p).filter fun ℓ => coarse ℓ = c).card

variable (P P' : Finset α) (T T' : α → Finset L) (coarse : L → L) (C' : Finset L)
variable (H M : ℕ) (K : ℝ)

/-- For each p, the sum of assigned counts over C' equals (T' p).card. -/
lemma assignedCount_sum_eq_card (p : α) (hp : p ∈ P')
    (h : (T' p).image coarse ⊆ C') :
    ∑ c ∈ C', ((T' p).filter fun ℓ => coarse ℓ = c).card = (T' p).card := by
  have h_maps : ((T' p : Set L).MapsTo coarse (C' : Set L)) := by
    intro x hx
    exact h (mem_image_of_mem coarse hx)
  exact (card_eq_sum_card_fiberwise (f := coarse) (s := T' p) (t := C') h_maps).symm

/-- Total incidences: ∑_c S c = ∑_p (T' p).card. -/
lemma total_incidences_double_count
    (hcover : ∀ p ∈ P', (T' p).image coarse ⊆ C') :
    ∑ c ∈ C', totalAssigned P' T' coarse c = ∑ p ∈ P', (T' p).card := by
  have h1 : ∑ c ∈ C', ∑ p ∈ P', ((T' p).filter fun ℓ => coarse ℓ = c).card =
              ∑ p ∈ P', ∑ c ∈ C', ((T' p).filter fun ℓ => coarse ℓ = c).card := by
    rw [sum_comm]
  have h2 : ∑ p ∈ P', ∑ c ∈ C', ((T' p).filter fun ℓ => coarse ℓ = c).card =
              ∑ p ∈ P', (T' p).card := by
    apply sum_congr rfl
    intro p hp
    exact assignedCount_sum_eq_card P' T' coarse C' p hp (hcover p hp)
  simpa [totalAssigned] using h1.trans h2

/-- **Upper bound**: `H * C'.card ≤ K * M * P.card`. -/
lemma two_sided_average_upper
    (hP' : P' ⊆ P)
    (hK : 1 ≤ K)
    (hH : ∀ c ∈ C', (H : ℝ) ≤ (totalAssigned P' T' coarse c : ℝ))
    (hM : ∀ p ∈ P', ((T' p).card : ℝ) ≤ (M : ℝ))
    (hcover : ∀ p ∈ P', (T' p).image coarse ⊆ C') :
    (H : ℝ) * (C'.card : ℝ) ≤ K * (M : ℝ) * (P.card : ℝ) := by
  set S : L → ℝ := fun c => (totalAssigned P' T' coarse c : ℝ) with hS
  have h_total : ∑ c ∈ C', S c = ∑ p ∈ P', ((T' p).card : ℝ) := by
    have h := total_incidences_double_count P' T' coarse C' hcover
    simpa [hS, totalAssigned, Nat.cast_sum] using congr_arg (fun x : ℕ => (x : ℝ)) h
  have h1 : (H : ℝ) * (C'.card : ℝ) ≤ ∑ c ∈ C', S c := by
    have h1a : C'.card • (H : ℝ) ≤ ∑ c ∈ C', S c := card_nsmul_le_sum C' S (H : ℝ) hH
    have h1b : C'.card • (H : ℝ) = (H : ℝ) * (C'.card : ℝ) := by
      simp [nsmul_eq_mul, mul_comm]
    rw [h1b] at h1a
    exact h1a
  have h2 : ∑ p ∈ P', ((T' p).card : ℝ) ≤ (P'.card : ℝ) * (M : ℝ) := by
    have h2a : ∑ p ∈ P', ((T' p).card : ℝ) ≤ P'.card • (M : ℝ) := sum_le_card_nsmul P' (fun p => ((T' p).card : ℝ)) (M : ℝ) hM
    have h2b : P'.card • (M : ℝ) = (P'.card : ℝ) * (M : ℝ) := by
      simp [nsmul_eq_mul]
    rw [h2b] at h2a
    exact h2a
  have h3 : (P'.card : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast card_le_card hP'
  calc
    (H : ℝ) * (C'.card : ℝ)
      ≤ ∑ c ∈ C', S c := h1
    _ = ∑ p ∈ P', ((T' p).card : ℝ) := h_total
    _ ≤ (P'.card : ℝ) * (M : ℝ) := h2
    _ ≤ (P.card : ℝ) * (M : ℝ) := by gcongr
    _ ≤ K * (M : ℝ) * (P.card : ℝ) := by
      have h4 : 0 ≤ (P.card : ℝ) * (M : ℝ) := by positivity
      have h5 : (P.card : ℝ) * (M : ℝ) ≤ K * ((P.card : ℝ) * (M : ℝ)) := by
        calc
          (P.card : ℝ) * (M : ℝ)
            = 1 * ((P.card : ℝ) * (M : ℝ)) := by ring
          _ ≤ K * ((P.card : ℝ) * (M : ℝ)) := by gcongr
      simpa [mul_comm, mul_assoc, mul_left_comm] using h5

/-- **Lower bound with perfect balancing**: `M * P.card ≤ K^2 * H * C'.card`.

    Requires `S c ≤ H` for all `c ∈ C'`.
-/
lemma two_sided_average_lower_perfect
    (hK : 1 ≤ K)
    (hP : (P.card : ℝ) ≤ K * (P'.card : ℝ))
    (hM : ∀ p ∈ P', (M : ℝ) ≤ K * ((T' p).card : ℝ))
    (hH_upper : ∀ c ∈ C', (totalAssigned P' T' coarse c : ℝ) ≤ (H : ℝ))
    (hcover : ∀ p ∈ P', (T' p).image coarse ⊆ C') :
    (M : ℝ) * (P.card : ℝ) ≤ K^2 * (H : ℝ) * (C'.card : ℝ) := by
  set S : L → ℝ := fun c => (totalAssigned P' T' coarse c : ℝ) with hS
  have h_total : ∑ c ∈ C', S c = ∑ p ∈ P', ((T' p).card : ℝ) := by
    have h := total_incidences_double_count P' T' coarse C' hcover
    simpa [hS, totalAssigned, Nat.cast_sum] using congr_arg (fun x : ℕ => (x : ℝ)) h
  have h1 : ∑ c ∈ C', S c ≤ (C'.card : ℝ) * (H : ℝ) := by
    have h1a : ∑ c ∈ C', S c ≤ C'.card • (H : ℝ) := sum_le_card_nsmul C' S (H : ℝ) hH_upper
    have h1b : C'.card • (H : ℝ) = (C'.card : ℝ) * (H : ℝ) := by simp [nsmul_eq_mul]
    rw [h1b] at h1a
    exact h1a
  have h2 : (M : ℝ) * (P'.card : ℝ) ≤ K * ∑ p ∈ P', ((T' p).card : ℝ) := by
    calc
      (M : ℝ) * (P'.card : ℝ)
        = (P'.card : ℝ) * (M : ℝ) := by ring
      _ = ∑ p ∈ P', (M : ℝ) := by simp [sum_const]
      _ ≤ ∑ p ∈ P', K * ((T' p).card : ℝ) := sum_le_sum hM
      _ = K * ∑ p ∈ P', ((T' p).card : ℝ) := by
        rw [← Finset.mul_sum]
        <;> rfl
  calc
    (M : ℝ) * (P.card : ℝ)
      ≤ K * ((M : ℝ) * (P'.card : ℝ)) := by
        have hpos : 0 ≤ (M : ℝ) := by positivity
        nlinarith
    _ ≤ K * (K * ∑ p ∈ P', ((T' p).card : ℝ)) := by gcongr
    _ = K^2 * ∑ p ∈ P', ((T' p).card : ℝ) := by ring
    _ = K^2 * ∑ c ∈ C', S c := by rw [h_total]
    _ ≤ K^2 * ((C'.card : ℝ) * (H : ℝ)) := by gcongr
    _ = K^2 * (H : ℝ) * (C'.card : ℝ) := by ring

/-- **Lower bound with K-balancing**: `M * P.card ≤ K^3 * H * C'.card`.

    Requires `S c ≤ K * H` for all `c ∈ C'`.
-/
lemma two_sided_average_lower_balanced
    (hK : 1 ≤ K)
    (hP : (P.card : ℝ) ≤ K * (P'.card : ℝ))
    (hM : ∀ p ∈ P', (M : ℝ) ≤ K * ((T' p).card : ℝ))
    (hH_upper : ∀ c ∈ C', (totalAssigned P' T' coarse c : ℝ) ≤ K * (H : ℝ))
    (hcover : ∀ p ∈ P', (T' p).image coarse ⊆ C') :
    (M : ℝ) * (P.card : ℝ) ≤ K^3 * (H : ℝ) * (C'.card : ℝ) := by
  set S : L → ℝ := fun c => (totalAssigned P' T' coarse c : ℝ) with hS
  have h_total : ∑ c ∈ C', S c = ∑ p ∈ P', ((T' p).card : ℝ) := by
    have h := total_incidences_double_count P' T' coarse C' hcover
    simpa [hS, totalAssigned, Nat.cast_sum] using congr_arg (fun x : ℕ => (x : ℝ)) h
  have h1 : ∑ c ∈ C', S c ≤ (C'.card : ℝ) * (K * (H : ℝ)) := by
    have h1a : ∑ c ∈ C', S c ≤ C'.card • (K * (H : ℝ)) := sum_le_card_nsmul C' S (K * (H : ℝ)) hH_upper
    have h1b : C'.card • (K * (H : ℝ)) = (C'.card : ℝ) * (K * (H : ℝ)) := by simp [nsmul_eq_mul]
    rw [h1b] at h1a
    exact h1a
  have h2 : (M : ℝ) * (P'.card : ℝ) ≤ K * ∑ p ∈ P', ((T' p).card : ℝ) := by
    calc
      (M : ℝ) * (P'.card : ℝ)
        = (P'.card : ℝ) * (M : ℝ) := by ring
      _ = ∑ p ∈ P', (M : ℝ) := by simp [sum_const]
      _ ≤ ∑ p ∈ P', K * ((T' p).card : ℝ) := sum_le_sum hM
      _ = K * ∑ p ∈ P', ((T' p).card : ℝ) := by
        rw [← Finset.mul_sum] <;> rfl
  calc
    (M : ℝ) * (P.card : ℝ)
      ≤ K * ((M : ℝ) * (P'.card : ℝ)) := by
        have hpos : 0 ≤ (M : ℝ) := by positivity
        nlinarith
    _ ≤ K * (K * ∑ p ∈ P', ((T' p).card : ℝ)) := by gcongr
    _ = K^2 * ∑ p ∈ P', ((T' p).card : ℝ) := by ring
    _ = K^2 * ∑ c ∈ C', S c := by rw [h_total]
    _ ≤ K^2 * ((C'.card : ℝ) * (K * (H : ℝ))) := by gcongr
    _ = K^3 * (H : ℝ) * (C'.card : ℝ) := by ring

-- ============================================================================
-- Explicit A bounds
-- ============================================================================

/-- Helper: `Real.log (2 / Δ) ≥ 1` when `0 < Δ ≤ 1/2`. -/
lemma explicit_log2Δ_ge_one (Δ : ℝ) (hΔ_pos : 0 < Δ) (hΔ_half : Δ ≤ 1 / 2) :
    1 ≤ Real.log (2 / Δ) := by
  have h1 : 2 / Δ ≥ 4 := by
    have h2 : 0 < Δ := hΔ_pos
    have h3 : Δ ≤ 1 / 2 := hΔ_half
    have h4 : 2 / Δ ≥ 2 / (1 / 2 : ℝ) := by gcongr
    have h5 : 2 / (1 / 2 : ℝ) = 4 := by norm_num
    linarith
  have h2 : Real.log (2 / Δ) ≥ Real.log 4 := Real.log_le_log (by linarith) h1
  have h_log2_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have h_log4 : Real.log 4 = 2 * Real.log 2 := by
    have h : Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
    rw [h, Real.log_pow] <;> ring
  have h3 : Real.log 4 ≥ 1 := by
    rw [h_log4]
    linarith
  linarith

/-- Helper: `Nat.log 2 n ≤ Real.log n / Real.log 2` for `n > 0`. -/
lemma explicit_natLog2_le {n : ℕ} (hn : 0 < n) :
    (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
  have h1 : (Nat.log 2 n : ℝ) ≤ Real.logb (2 : ℝ) (n : ℝ) := Real.natLog_le_logb n 2
  have h2 : Real.logb (2 : ℝ) (n : ℝ) = Real.log (n : ℝ) / Real.log 2 := by
    rw [Real.logb] <;> ring
  rw [h2] at h1
  exact h1

/-- Algebra identity: (H * m1 / 4) * (E / (8 * H)) = m1 * E / 32 when H ≠ 0. -/
lemma frostman_algebra_identity (H m1 E : ℝ) (hH : H ≠ 0) :
    (H * m1 / 4) * (E / (8 * H)) = m1 * E / 32 := by
  have h1 : (H * m1 / 4) * (E / (8 * H)) = (H * m1 * E) / (4 * (8 * H)) := by
    rw [div_mul_div_comm] <;> ring
  rw [h1]
  have h2 : 4 * (8 * H) = 32 * H := by ring
  rw [h2]
  have h3 : (H * m1 * E) / (32 * H) = m1 * E / 32 := by
    have h4 : (32 : ℝ) ≠ 0 := by norm_num
    have h5 : (32 * H) ≠ 0 := mul_ne_zero h4 hH
    exact (div_eq_div_iff h5 h4).mpr (by ring)
  exact h3

/-- Simple bound: if `K1 ≥ 1`, then `32 * K1^3 ≤ 2^21 * K1^6`. -/
lemma simple_K1_bound (K1 : ℕ) (hK1 : 1 ≤ K1) :
    (32 : ℝ) * (K1 : ℝ)^3 ≤ (2^21 : ℝ) * (K1 : ℝ)^6 := by
  have h1 : (1 : ℝ) ≤ (K1 : ℝ) := by exact_mod_cast hK1
  have h2 : (K1 : ℝ)^3 ≥ 1 := by
    have h21 : (K1 : ℝ)^3 ≥ (1 : ℝ)^3 := by
      gcongr <;> linarith
    simpa using h21
  have h3 : (K1 : ℝ)^3 ≤ (K1 : ℝ)^6 := by
    have h31 : (K1 : ℝ)^6 = (K1 : ℝ)^3 * (K1 : ℝ)^3 := by ring
    rw [h31]
    have h32 : 0 ≤ (K1 : ℝ)^3 := by positivity
    exact le_mul_of_one_le_right h32 h2
  have h4 : (32 : ℝ) ≤ (2^21 : ℝ) := by norm_num
  have h5 : 0 ≤ (K1 : ℝ)^3 := by positivity
  have h6 : (32 : ℝ) * (K1 : ℝ)^3 ≤ (2^21 : ℝ) * (K1 : ℝ)^3 :=
    mul_le_mul h4 le_rfl (by positivity) (by norm_num)
  have h7 : (2^21 : ℝ) * (K1 : ℝ)^3 ≤ (2^21 : ℝ) * (K1 : ℝ)^6 :=
    mul_le_mul_of_nonneg_left h3 (by norm_num)
  exact le_trans h6 h7

/-- Lower bound: if `K1 ≥ 1`, then `2^21 * K1^6 ≥ 1`. -/
lemma K_val_ge1_lemma (K1 : ℕ) (hK1 : 1 ≤ K1) :
    (1 : ℝ) ≤ (2^21 : ℝ) * (K1 : ℝ)^6 := by
  have h1 : (1 : ℝ) ≤ (K1 : ℝ) := by exact_mod_cast hK1
  have h2 : (K1 : ℝ)^6 ≥ 1 := by
    have h21 : (K1 : ℝ)^6 ≥ (1 : ℝ)^6 := by gcongr
    simpa using h21
  have h3 : (2^21 : ℝ) ≥ 1 := by norm_num
  have h4 : (2^21 : ℝ) * (K1 : ℝ)^6 ≥ 1 * 1 := by
    exact mul_le_mul h3 h2 (by norm_num) (by linarith)
  simpa using h4

/-- **K bound**: With `C = (log B + D) / log 2 + 4` and `A ≥ max(2^21 * C^6, 7)`,
    prove `K ≤ A * (log(2/Δ))^A`. -/
lemma explicit_K_bound
    (s D B Δ : ℝ) (N K1 : ℕ) (K C A : ℝ)
    (hB : 1 ≤ B) (hD : 1 ≤ D) (hΔ_pos : 0 < Δ) (hΔ_half : Δ ≤ 1 / 2)
    (hN_pos : 0 < N)
    (hN : (N : ℝ) ≤ B * Δ ^ (-D))
    (hK1 : K1 = Nat.log 2 N + 4)
    (hK : K = 2^21 * (K1 : ℝ)^6)
    (hC : C = (Real.log B + D) / Real.log 2 + 4)
    (hA1 : A ≥ 2^21 * C^6)
    (hA7 : A ≥ 7) :
    K ≤ A * Real.rpow (Real.log (2 / Δ)) A := by
  set y : ℝ := Real.log (2 / Δ) with hy_def
  have h_y_ge1 : 1 ≤ y := explicit_log2Δ_ge_one Δ hΔ_pos hΔ_half
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_logB_nonneg : 0 ≤ Real.log B := Real.log_nonneg hB
  have hD_nonneg : 0 ≤ D := by linarith
  have h1 : (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 :=
    explicit_natLog2_le hN_pos
  have h_pos1 : 0 < (N : ℝ) := by exact_mod_cast hN_pos
  have h_pos2 : 0 < B * Δ ^ (-D) := by positivity
  have h_logN_le : Real.log (N : ℝ) ≤ Real.log (B * Δ ^ (-D)) :=
    Real.log_le_log (by linarith) hN
  have h_log_prod : Real.log (B * Δ ^ (-D)) = Real.log B + D * Real.log (1 / Δ) := by
    have h_pos3 : 0 < Δ ^ (-D) := Real.rpow_pos_of_pos hΔ_pos (-D)
    have h1 : Real.log (B * Δ ^ (-D)) = Real.log B + Real.log (Δ ^ (-D)) := by
      rw [Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt h_pos3)] <;> ring
    rw [h1]
    have h2 : Real.log (Δ ^ (-D)) = (-D) * Real.log Δ := by
      rw [Real.log_rpow hΔ_pos] <;> ring
    rw [h2]
    have h3 : Real.log (1 / Δ) = -Real.log Δ := by
      rw [Real.log_div (by norm_num) (ne_of_gt hΔ_pos)]
      have h4 : Real.log 1 = 0 := by simp
      rw [h4] <;> ring
    rw [h3] <;> ring
  have h_log_inv_le : Real.log (1 / Δ) ≤ y := by
    have h4 : (1 / Δ : ℝ) ≤ (2 / Δ : ℝ) := by
      have h5 : 0 < Δ := hΔ_pos
      field_simp [h5.ne'] <;> linarith
    exact Real.log_le_log (by positivity) h4
  have h2 : Real.log (N : ℝ) ≤ Real.log B + D * y := by
    calc
      Real.log (N : ℝ) ≤ Real.log (B * Δ ^ (-D)) := h_logN_le
      _ = Real.log B + D * Real.log (1 / Δ) := h_log_prod
      _ ≤ Real.log B + D * y := by gcongr
  have h3 : (Nat.log 2 N : ℝ) ≤ (Real.log B + D * y) / Real.log 2 := by
    calc
      (Nat.log 2 N : ℝ)
        ≤ Real.log (N : ℝ) / Real.log 2 := h1
      _ ≤ (Real.log B + D * y) / Real.log 2 := by gcongr
  have h4 : (Real.log B + D * y) / Real.log 2 + 4 ≤ C * y := by
    rw [hC]
    have h5 : ((Real.log B + D) / Real.log 2 + 4) * y -
             ((Real.log B + D * y) / Real.log 2 + 4) =
             (y - 1) * (Real.log B / Real.log 2 + 4) := by
      field_simp [h_log2_pos.ne'] <;> ring
    have h6 : 0 ≤ (y - 1) * (Real.log B / Real.log 2 + 4) := by
      have h7 : 0 ≤ y - 1 := by linarith
      have h8 : 0 ≤ Real.log B / Real.log 2 + 4 := by positivity
      exact mul_nonneg h7 h8
    linarith
  have h5 : (K1 : ℝ) ≤ C * y := by
    rw [hK1]
    have h61 : ((Nat.log 2 N + 4 : ℕ) : ℝ) = (Nat.log 2 N : ℝ) + 4 := by
      simp <;> norm_cast
    rw [h61]
    have h6 : (Nat.log 2 N : ℝ) + 4 ≤ (Real.log B + D * y) / Real.log 2 + 4 := by
      gcongr
    exact h6.trans h4
  have hC_nonneg : 0 ≤ C := by
    rw [hC]
    have h7 : 0 ≤ (Real.log B + D) / Real.log 2 := by positivity
    linarith
  have h6 : K ≤ 2^21 * C^6 * y^6 := by
    rw [hK]
    have h7 : (K1 : ℝ)^6 ≤ (C * y)^6 := by gcongr
    have h8 : (C * y)^6 = C^6 * y^6 := by ring
    rw [h8] at h7
    linarith
  have h9 : y^6 ≤ Real.rpow y A := by
    have h10 : y^6 = Real.rpow y 6 := by
      simp [Real.rpow_natCast] <;> norm_cast
    rw [h10]
    have h11 : (6 : ℝ) ≤ A := by linarith
    exact Real.rpow_le_rpow_of_exponent_le h_y_ge1 h11
  have h12 : 2^21 * C^6 ≤ A := hA1
  have h13 : 2^21 * C^6 * y^6 ≤ A * Real.rpow y A := by
    calc
      2^21 * C^6 * y^6
        ≤ A * y^6 := by gcongr
      _ ≤ A * Real.rpow y A := by gcongr
  exact h6.trans h13

/-- **C2 bound**: With `A ≥ 1024 * 2^(s+2)`, prove
    `1024 * 2^(s+2) * C₁ * K1^2 ≤ A * K^A * C₁`. -/
lemma explicit_C2_bound
    (s : ℝ) (C₁ : ℝ) (K1 : ℕ) (K A : ℝ)
    (hs : 0 ≤ s) (hC1 : 1 ≤ C₁) (hK1_ge1 : 1 ≤ K1)
    (hK : K = 2^21 * (K1 : ℝ)^6)
    (hA_ge : A ≥ 1024 * Real.rpow 2 (s + 2)) :
    1024 * Real.rpow 2 (s + 2) * C₁ * (K1 : ℝ)^2 ≤ A * Real.rpow K A * C₁ := by
  have hK_ge1 : 1 ≤ K := by
    rw [hK]
    have h1 : (K1 : ℝ) ≥ 1 := by exact_mod_cast hK1_ge1
    have h2 : (K1 : ℝ)^6 ≥ 1 := by
      have h3 : (K1 : ℝ) ≥ 1 := h1
      have h4 : (K1 : ℝ)^6 ≥ 1^6 := by gcongr
      simpa using h4
    have h5 : (2 : ℝ)^21 * (K1 : ℝ)^6 ≥ 1 := by
      have h6 : (2 : ℝ)^21 ≥ 1 := by norm_num
      nlinarith
    exact h5
  have hK1_2_le_K : (K1 : ℝ)^2 ≤ K := by
    rw [hK]
    have h1 : (K1 : ℝ) ≥ 1 := by exact_mod_cast hK1_ge1
    have h2 : (K1 : ℝ)^2 ≤ (K1 : ℝ)^6 := by
      gcongr <;> norm_num
    have h3 : (K1 : ℝ)^6 ≤ (2 : ℝ)^21 * (K1 : ℝ)^6 := by
      have h4 : 0 ≤ (K1 : ℝ)^6 := by positivity
      nlinarith
    linarith
  have hA_ge1 : 1 ≤ A := by
    have h1 : Real.rpow 2 (s + 2) ≥ 4 := by
      have h2 : (2 : ℝ) ≤ (s + 2) := by linarith
      have h3 : Real.rpow 2 (s + 2) ≥ Real.rpow 2 2 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
      have h4 : Real.rpow 2 2 = 4 := by norm_num
      linarith
    have h5 : 1024 * Real.rpow 2 (s + 2) ≥ 4096 := by nlinarith
    linarith [hA_ge]
  have hK_A_ge_K : K ≤ Real.rpow K A := by
    have h1 : Real.rpow K 1 ≤ Real.rpow K A :=
      Real.rpow_le_rpow_of_exponent_le hK_ge1 (by linarith)
    have h2 : Real.rpow K 1 = K := by simp
    rw [h2] at h1
    exact h1
  have h_rpow_ge_K1_2 : (K1 : ℝ)^2 ≤ Real.rpow K A :=
    hK1_2_le_K.trans hK_A_ge_K
  have h_coeff : A ≥ 1024 * Real.rpow 2 (s + 2) := hA_ge
  have hC1_nonneg : 0 ≤ C₁ := by linarith
  have h1 : A * Real.rpow K A ≥ (1024 * Real.rpow 2 (s + 2)) * (K1 : ℝ)^2 := by
    gcongr <;> linarith
  have h2 : A * Real.rpow K A * C₁ ≥
      (1024 * Real.rpow 2 (s + 2)) * (K1 : ℝ)^2 * C₁ := by
    gcongr <;> linarith
  have h3 : (1024 * Real.rpow 2 (s + 2)) * (K1 : ℝ)^2 * C₁ =
      1024 * Real.rpow 2 (s + 2) * C₁ * (K1 : ℝ)^2 := by ring
  rw [h3] at h2
  exact h2

end TwoSidedAverage

-- ============================================================================
-- Extracted sum bound lemma (reduces main theorem proof size)
-- ============================================================================

/-- Bound on `∑_{p ∈ P'} |T p|` used in the Frostman argument. -/
lemma four_mul_div_ceil_ge (a : ℕ) : 4 * ((a + 3) / 4) ≥ a := by omega

/-- Bound on `∑_{p ∈ P'} |T p|` used in the Frostman argument. -/
lemma sum_T_upper_bound
    {α L : Type*} [DecidableEq α] [DecidableEq L]
    (P P1 P' : Finset α) (T : α → Finset L)
    (M K1 m1 m2 : ℕ)
    (C1 C' : Finset L) (E : Finset (α × L))
    (H_raw H_final : ℕ)
    (hT_card : ∀ p ∈ P, M / 2 < (T p).card ∧ (T p).card ≤ M)
    (hP'_sub_P1 : P' ⊆ P1)
    (hP1_sub : P1 ⊆ P)
    (hC1_nonempty : C1.Nonempty)
    (hE_nonempty : E.Nonempty)
    (hH_raw_pos : 0 < H_raw)
    (hH_final_pos : 0 < H_final)
    (hC'_card_lower : (C'.card : ℝ) ≥ (C1.card : ℝ) * ((E.card : ℝ) / (C1.card : ℝ)) / (4 * (↑(2 * H_raw) : ℝ)))
    (hE_ge_dyadic : (E.card : ℝ) ≥ (H_raw : ℝ) * (C1.card : ℝ))
    (h_C1_lower : (H_raw : ℝ) * (C1.card : ℝ) ≥ (m2 : ℝ) * (P1.card : ℝ) / (4 * (K1 : ℝ)))
    (h_mass_lower2 : (M : ℝ) / (32 * (K1 : ℝ)) ≤ (m1 : ℝ) * (m2 : ℝ))
    (hH_final_ge4 : 4 * H_final ≥ H_raw * m1)
    (hK1_ge1 : 1 ≤ K1) :
    (∑ p ∈ P', (T p).card : ℝ) ≤ (4096 * (K1 : ℝ)^2) * (H_final : ℝ) * (C'.card : ℝ) := by
  have h1 : (∑ p ∈ P', (T p).card : ℝ) ≤ (P'.card : ℝ) * (M : ℝ) := by
    have h2 : ∀ p ∈ P', (T p).card ≤ M := fun p hp => (hT_card p (hP1_sub (hP'_sub_P1 hp))).2
    have h3 : ∑ p ∈ P', (T p).card ≤ P'.card • M := Finset.sum_le_card_nsmul P' (fun p => (T p).card) M h2
    exact_mod_cast h3
  have h4 : (P'.card : ℝ) ≤ (P1.card : ℝ) := by exact_mod_cast Finset.card_le_card hP'_sub_P1
  have h5 : (∑ p ∈ P', (T p).card : ℝ) ≤ (P1.card : ℝ) * (M : ℝ) := by
    calc
      (∑ p ∈ P', (T p).card : ℝ) ≤ (P'.card : ℝ) * (M : ℝ) := h1
      _ ≤ (P1.card : ℝ) * (M : ℝ) := by gcongr
  have hH_pos : (H_raw : ℝ) > 0 := Nat.cast_pos.mpr hH_raw_pos
  have hC1_pos : (C1.card : ℝ) > 0 := Nat.cast_pos.mpr hC1_nonempty.card_pos
  have hE_pos : (E.card : ℝ) > 0 := Nat.cast_pos.mpr hE_nonempty.card_pos
  have h7 : (C'.card : ℝ) ≥ (E.card : ℝ) / (8 * (H_raw : ℝ)) := by
    have h_eq2 : (↑(2 * H_raw) : ℝ) = 2 * (H_raw : ℝ) := by
      rw [Nat.cast_mul] <;> norm_cast <;> ring
    have h8 : (C'.card : ℝ) ≥ (C1.card : ℝ) * ((E.card : ℝ) / (C1.card : ℝ)) / (4 * (↑(2 * H_raw))) := hC'_card_lower
    rw [h_eq2] at h8
    have h9 : (C1.card : ℝ) * ((E.card : ℝ) / (C1.card : ℝ)) = (E.card : ℝ) := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ hC1_pos.ne'
    rw [h9] at h8
    have h10 : (4 * (2 * (H_raw : ℝ))) = (8 * (H_raw : ℝ)) := by ring
    rw [h10] at h8
    exact h8
  have h10 : (H_final : ℝ) ≥ (H_raw : ℝ) * (m1 : ℝ) / 4 := by
    have h11 : (4 * H_final : ℝ) ≥ ((H_raw * m1 : ℕ) : ℝ) := by exact_mod_cast hH_final_ge4
    have h12 : (4 * H_final : ℝ) = 4 * (H_final : ℝ) := by simp
    have h13 : ((H_raw * m1 : ℕ) : ℝ) = (H_raw : ℝ) * (m1 : ℝ) := by
      rw [Nat.cast_mul] <;> ring
    rw [h12, h13] at h11
    linarith
  have hC'_pos : 0 ≤ (C'.card : ℝ) := by exact Nat.cast_nonneg C'.card
  have h14 : (H_final : ℝ) * (C'.card : ℝ) ≥ (m1 : ℝ) * (E.card : ℝ) / 32 := by
    have h15 : 0 ≤ (H_raw : ℝ) * (m1 : ℝ) / 4 := by positivity
    have h16 : ((H_raw : ℝ) * (m1 : ℝ) / 4) * (C'.card : ℝ) ≥
        ((H_raw : ℝ) * (m1 : ℝ) / 4) * ((E.card : ℝ) / (8 * (H_raw : ℝ))) :=
      mul_le_mul_of_nonneg_left h7 h15
    have h17 : ((H_raw : ℝ) * (m1 : ℝ) / 4) * ((E.card : ℝ) / (8 * (H_raw : ℝ))) =
        (m1 : ℝ) * (E.card : ℝ) / 32 :=
      frostman_algebra_identity (H_raw : ℝ) (m1 : ℝ) (E.card : ℝ) hH_pos.ne'
    calc
      (H_final : ℝ) * (C'.card : ℝ)
        ≥ ((H_raw : ℝ) * (m1 : ℝ) / 4) * (C'.card : ℝ) := mul_le_mul_of_nonneg_right h10 hC'_pos
      _ ≥ ((H_raw : ℝ) * (m1 : ℝ) / 4) * ((E.card : ℝ) / (8 * (H_raw : ℝ))) := h16
      _ = (m1 : ℝ) * (E.card : ℝ) / 32 := h17
  have h15 : (E.card : ℝ) ≥ (m2 : ℝ) * (P1.card : ℝ) / (4 * (K1 : ℝ)) := by
    have h16 : (E.card : ℝ) ≥ (H_raw : ℝ) * (C1.card : ℝ) := hE_ge_dyadic
    have h17 : (H_raw : ℝ) * (C1.card : ℝ) ≥ (m2 : ℝ) * (P1.card : ℝ) / (4 * (K1 : ℝ)) := h_C1_lower
    exact h17.trans h16
  have h18 : (H_final : ℝ) * (C'.card : ℝ) ≥ (m1 : ℝ) * (m2 : ℝ) * (P1.card : ℝ) / (128 * (K1 : ℝ)) := by
    have h18a : 0 ≤ (m1 : ℝ) / 32 := by positivity
    have h18b : (m1 : ℝ) / 32 * (E.card : ℝ) ≥
        (m1 : ℝ) / 32 * ((m2 : ℝ) * (P1.card : ℝ) / (4 * (K1 : ℝ))) :=
      mul_le_mul_of_nonneg_left h15 h18a
    have h18c : (m1 : ℝ) * (E.card : ℝ) / 32 = (m1 : ℝ) / 32 * (E.card : ℝ) := by ring
    have h18d : (m1 : ℝ) / 32 * ((m2 : ℝ) * (P1.card : ℝ) / (4 * (K1 : ℝ))) =
        (m1 : ℝ) * ((m2 : ℝ) * (P1.card : ℝ) / (4 * (K1 : ℝ))) / 32 := by ring
    have h18e : (m1 : ℝ) * (E.card : ℝ) / 32 ≥
        (m1 : ℝ) * ((m2 : ℝ) * (P1.card : ℝ) / (4 * (K1 : ℝ))) / 32 := by
      rw [h18c, Eq.symm h18d]
      exact h18b
    have h18f : (m1 : ℝ) * ((m2 : ℝ) * (P1.card : ℝ) / (4 * (K1 : ℝ))) / 32 =
        (m1 : ℝ) * (m2 : ℝ) * (P1.card : ℝ) / (128 * (K1 : ℝ)) := by ring
    rw [h18f] at h18e
    exact le_trans h18e h14
  have h19 : (m1 : ℝ) * (m2 : ℝ) ≥ (M : ℝ) / (32 * (K1 : ℝ)) := h_mass_lower2
  have h19c : 0 ≤ (P1.card : ℝ) / (128 * (K1 : ℝ)) := by positivity
  have h19g : (m1 : ℝ) * (m2 : ℝ) * (P1.card : ℝ) / (128 * (K1 : ℝ)) ≥
      ((M : ℝ) / (32 * (K1 : ℝ))) * ((P1.card : ℝ) / (128 * (K1 : ℝ))) := by
    have h_eq : (m1 : ℝ) * (m2 : ℝ) * (P1.card : ℝ) / (128 * (K1 : ℝ)) =
        (m1 : ℝ) * (m2 : ℝ) * ((P1.card : ℝ) / (128 * (K1 : ℝ))) := by ring
    rw [h_eq]
    exact mul_le_mul_of_nonneg_right h19 h19c
  have h19f : (m1 : ℝ) * (m2 : ℝ) * (P1.card : ℝ) / (128 * (K1 : ℝ)) =
      (m1 : ℝ) * (m2 : ℝ) * ((P1.card : ℝ) / (128 * (K1 : ℝ))) := by ring
  have h19h : ((M : ℝ) / (32 * (K1 : ℝ))) * ((P1.card : ℝ) / (128 * (K1 : ℝ))) =
      (M : ℝ) * (P1.card : ℝ) / (4096 * (K1 : ℝ)^2) := by ring
  have h6 : (H_final : ℝ) * (C'.card : ℝ) ≥ (M : ℝ) * (P1.card : ℝ) / (4096 * (K1 : ℝ)^2) := by
    calc
      (H_final : ℝ) * (C'.card : ℝ)
        ≥ (m1 : ℝ) * (m2 : ℝ) * (P1.card : ℝ) / (128 * (K1 : ℝ)) := h18
      _ ≥ ((M : ℝ) / (32 * (K1 : ℝ))) * ((P1.card : ℝ) / (128 * (K1 : ℝ))) := h19g
      _ = (M : ℝ) * (P1.card : ℝ) / (4096 * (K1 : ℝ)^2) := h19h
  have h22 : 0 < 4096 * (K1 : ℝ)^2 := by positivity
  have h24 : (4096 * (K1 : ℝ)^2) * ((H_final : ℝ) * (C'.card : ℝ)) ≥ (M : ℝ) * (P1.card : ℝ) := by
    have h25 : (4096 * (K1 : ℝ)^2) * ((H_final : ℝ) * (C'.card : ℝ)) ≥
        (4096 * (K1 : ℝ)^2) * ((M : ℝ) * (P1.card : ℝ) / (4096 * (K1 : ℝ)^2)) :=
      mul_le_mul_of_nonneg_left h6 (by positivity)
    have h26 : (4096 * (K1 : ℝ)^2) * ((M : ℝ) * (P1.card : ℝ) / (4096 * (K1 : ℝ)^2)) =
        (M : ℝ) * (P1.card : ℝ) := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ h22.ne'
    rw [h26] at h25
    exact h25
  have h27 : (4096 * (K1 : ℝ)^2) * ((H_final : ℝ) * (C'.card : ℝ)) =
      (4096 * (K1 : ℝ)^2) * (H_final : ℝ) * (C'.card : ℝ) := by ring
  rw [h27] at h24
  have h28 : (P1.card : ℝ) * (M : ℝ) ≤ (4096 * (K1 : ℝ)^2) * (H_final : ℝ) * (C'.card : ℝ) := by
    have h29 : (P1.card : ℝ) * (M : ℝ) = (M : ℝ) * (P1.card : ℝ) := by ring
    rw [h29]
    exact h24
  have h20 : (P1.card : ℝ) * (M : ℝ) ≤ (4096 * (K1 : ℝ)^2) * (H_final : ℝ) * (C'.card : ℝ) := h28
  exact h5.trans h20

-- ============================================================================
-- Algebraic helper lemmas for the main proof
-- ============================================================================

/-- Algebraic core of the T' cardinality lower bound. -/
lemma t_prime_card_algebraic
    (M K1 m1 m2 : ℕ) (K_val : ℝ)
    (card_Cp_inter_C' card_T'p : ℝ)
    (hK1_ge1 : 1 ≤ K1)
    (h_mass_lower2 : (M : ℝ) / (32 * (K1 : ℝ)) ≤ (m1 : ℝ) * (m2 : ℝ))
    (h_Cp_ge : card_Cp_inter_C' ≥ (m2 : ℝ) / (16 * (K1 : ℝ)))
    (h_sum_ge : card_T'p ≥ (m1 : ℝ) * card_Cp_inter_C')
    (hK_val_eq : K_val = (2^21 : ℝ) * (K1 : ℝ)^6) :
    (M : ℝ) ≤ K_val * card_T'p := by
  have h8 : card_T'p ≥ (m1 : ℝ) * (m2 : ℝ) / (16 * (K1 : ℝ)) := by
    calc
      card_T'p ≥ (m1 : ℝ) * card_Cp_inter_C' := h_sum_ge
      _ ≥ (m1 : ℝ) * ((m2 : ℝ) / (16 * (K1 : ℝ))) := by gcongr
      _ = (m1 : ℝ) * (m2 : ℝ) / (16 * (K1 : ℝ)) := by ring
  have h9 : (m1 : ℝ) * (m2 : ℝ) ≥ (M : ℝ) / (32 * (K1 : ℝ)) := h_mass_lower2
  have h10 : card_T'p ≥ (M : ℝ) / (512 * (K1 : ℝ)^2) := by
    calc
      card_T'p ≥ (m1 : ℝ) * (m2 : ℝ) / (16 * (K1 : ℝ)) := h8
      _ ≥ ((M : ℝ) / (32 * (K1 : ℝ))) / (16 * (K1 : ℝ)) := by gcongr
      _ = (M : ℝ) / (512 * (K1 : ℝ)^2) := by ring
  have h11 : (512 : ℝ) * (K1 : ℝ)^2 ≤ K_val := by
    rw [hK_val_eq]
    have h13 : (1 : ℝ) ≤ (K1 : ℝ) := by exact_mod_cast hK1_ge1
    have h14 : (K1 : ℝ)^2 ≤ (K1 : ℝ)^6 := by
      have h15 : (K1 : ℝ)^6 = (K1 : ℝ)^2 * (K1 : ℝ)^4 := by ring
      rw [h15]
      have h16 : (K1 : ℝ)^4 ≥ 1 := by
        have h17 : (K1 : ℝ) ≥ 1 := h13
        have h18 : (K1 : ℝ)^4 ≥ (1 : ℝ)^4 := by gcongr
        simpa using h18
      have h18 : (K1 : ℝ)^2 * 1 ≤ (K1 : ℝ)^2 * (K1 : ℝ)^4 := by
        exact mul_le_mul_of_nonneg_left h16 (by positivity)
      simpa using h18
    have h19 : (512 : ℝ) ≤ (2^21 : ℝ) := by norm_num
    exact mul_le_mul h19 h14 (by positivity) (by positivity)
  have h17 : (M : ℝ) / K_val ≤ (M : ℝ) / (512 * (K1 : ℝ)^2) := by
    apply div_le_div_of_nonneg_left
    · exact Nat.cast_nonneg M
    · positivity
    · exact h11
  have h18 : (M : ℝ) / K_val ≤ card_T'p := h17.trans h10
  have h20 : 0 < K_val := by
    rw [hK_val_eq]
    have h21 : (1 : ℝ) ≤ (K1 : ℝ) := by exact_mod_cast hK1_ge1
    have h22 : (0 : ℝ) < (2^21 : ℝ) := by norm_num
    exact mul_pos h22 (pow_pos (by linarith) 6)
  calc
    (M : ℝ) = K_val * ((M : ℝ) / K_val) := by
      field_simp [h20.ne'] <;> ring
    _ ≤ K_val * card_T'p := by gcongr

/-- Algebraic core of the P cardinality bound. -/
lemma p_card_bound_algebraic
    (P_card P1_card P'_card : ℝ) (K1 : ℕ) (K_val : ℝ)
    (hK1_ge1 : 1 ≤ K1)
    (hP1_card : P_card ≤ (K1 : ℝ)^2 * P1_card)
    (h_P1_lower : P1_card ≤ (32 : ℝ) * (K1 : ℝ) * P'_card)
    (hP'_nonneg : 0 ≤ P'_card)
    (hK_val_eq : K_val = (2^21 : ℝ) * (K1 : ℝ)^6) :
    P_card ≤ K_val * P'_card := by
  have h2 : P_card ≤ (K1 : ℝ)^2 * ((32 : ℝ) * (K1 : ℝ) * P'_card) := by
    have h21 : P1_card ≤ (32 : ℝ) * (K1 : ℝ) * P'_card := h_P1_lower
    have h22 : (K1 : ℝ)^2 * P1_card ≤ (K1 : ℝ)^2 * ((32 : ℝ) * (K1 : ℝ) * P'_card) :=
      mul_le_mul_of_nonneg_left h21 (sq_nonneg (K1 : ℝ))
    exact hP1_card.trans h22
  have h3 : (K1 : ℝ)^2 * ((32 : ℝ) * (K1 : ℝ) * P'_card) =
      (32 : ℝ) * (K1 : ℝ)^3 * P'_card := by ring
  rw [h3] at h2
  have h4 : (32 : ℝ) * (K1 : ℝ)^3 ≤ K_val := by
    rw [hK_val_eq]
    exact simple_K1_bound K1 hK1_ge1
  have h_pos : 0 ≤ P'_card := hP'_nonneg
  calc
    P_card ≤ (32 : ℝ) * (K1 : ℝ)^3 * P'_card := h2
    _ ≤ K_val * P'_card := by
      exact mul_le_mul_of_nonneg_right h4 h_pos

/-- Algebraic core of the incidence lower bound. -/
lemma incidence_algebraic
    (m1 H_raw H_final S : ℕ)
    (hH_final_def : H_final = (H_raw * m1 + 3) / 4)
    (hS_ge : (S : ℝ) ≥ (m1 : ℝ) * (H_raw : ℝ) / 4) :
    H_final ≤ S := by
  have h : (m1 : ℝ) * (H_raw : ℝ) ≤ 4 * (S : ℝ) := by linarith
  have h' : m1 * H_raw ≤ 4 * S := by exact_mod_cast h
  have h2 : H_final ≤ S := by
    rw [hH_final_def]
    have h3 : m1 * H_raw = H_raw * m1 := by ring
    rw [h3] at h'
    omega
  exact h2

/-- Algebraic core of the dA lower bound. -/
lemma dA_lower_algebraic
    (E_card P1_card C1_card : ℝ) (m2 K1 : ℕ) (H_raw : ℝ)
    (hP1_pos : 0 < P1_card)
    (hK1_pos : 0 < (K1 : ℝ))
    (hE_ge : E_card ≥ H_raw * C1_card)
    (h_C1_lower : H_raw * C1_card ≥ (m2 : ℝ) * P1_card / (4 * (K1 : ℝ))) :
    E_card / P1_card ≥ (m2 : ℝ) / (4 * (K1 : ℝ)) := by
  have h3 : E_card ≥ (m2 : ℝ) * P1_card / (4 * (K1 : ℝ)) := le_trans h_C1_lower hE_ge
  have h4 : E_card * (4 * (K1 : ℝ)) ≥ (m2 : ℝ) * P1_card := by
    have h6 : 0 < (4 * (K1 : ℝ)) := by positivity
    have h7 : E_card * (4 * (K1 : ℝ)) ≥
        (((m2 : ℝ) * P1_card / (4 * (K1 : ℝ))) * (4 * (K1 : ℝ))) :=
      mul_le_mul_of_nonneg_right h3 h6.le
    have h8 : ((m2 : ℝ) * P1_card / (4 * (K1 : ℝ))) * (4 * (K1 : ℝ)) =
        (m2 : ℝ) * P1_card := by
      exact div_mul_cancel₀ _ h6.ne'
    rw [h8] at h7
    exact h7
  have h12 : 0 < (4 * (K1 : ℝ)) := by positivity
  have h_div_lemma : ∀ (a b c d : ℝ), 0 < b → 0 < d → a * d ≥ c * b → a / b ≥ c / d := by
    intro a b c d hb hd h
    have h6 : a / b = (a * d) / (b * d) := by
      rw [←mul_div_mul_left _ _ hd.ne'] <;> ring
    have h7 : c / d = (c * b) / (b * d) := by
      rw [←mul_div_mul_left _ _ hb.ne'] <;> ring
    rw [h6, h7]
    apply div_le_div_of_nonneg_right h
    exact mul_nonneg hb.le hd.le
  exact h_div_lemma E_card P1_card (m2 : ℝ) (4 * (K1 : ℝ)) hP1_pos h12 h4

/-- Extract Frostman property for C' and compute C2_val. -/
lemma frostman_section
    {α L : Type*} [PseudoMetricSpace L] [DecidableEq α] [DecidableEq L]
    {δ Δ C₁ : ℝ} {M : ℕ}
    (P : Finset α) (T : α → Finset L) (P' : Finset α) (T' : α → Finset L)
    (coarse : L → L) (C' : Finset L)
    (K_frost H_final : ℝ) (s : ℝ) (K1 : ℕ)
    (hK_frost_eq : K_frost = 4096 * (K1 : ℝ)^2)
    (hδ_pos : 0 < δ) (hδΔ : δ ≤ Δ) (hΔ_half : Δ ≤ 1 / 2)
    (hC1 : 1 ≤ C₁) (hs : 0 < s) (hK1_ge1 : 1 ≤ K1)
    (hT_frostman : ∀ p ∈ P, BallGrowth δ s C₁ (T p))
    (hT'_sub : ∀ p ∈ P', T' p ⊆ T p)
    (hP'_sub_P : P' ⊆ P)
    (hC'_nonempty : C'.Nonempty)
    (h_sep_C' : SeparatedAt Δ (C' : Set L))
    (h_coarse_dist' : ∀ ℓ ∈ P'.biUnion T', dist ℓ (coarse ℓ) ≤ Δ)
    (h_inc_lower : ∀ c ∈ C', (H_final : ℝ) ≤ ∑ p ∈ P', assignedCount coarse T' p c)
    (h_sum_T_upper : (∑ p ∈ P', (T p).card : ℝ) ≤ K_frost * H_final * (C'.card : ℝ))
    (hH_final_pos : 0 < H_final) :
    ∃ (C2_val : ℝ), IsFiniteDeltaSSet Δ s C2_val C' ∧ 1 ≤ C2_val ∧
      C2_val = 1024 * Real.rpow 2 (s + 2) * C₁ * (K1 : ℝ)^2 := by
  let C2_val : ℝ := 1024 * Real.rpow 2 (s + 2) * C₁ * (K1 : ℝ)^2
  have hC2_val_eq : C2_val = 1024 * Real.rpow 2 (s + 2) * C₁ * (K1 : ℝ)^2 := by
    rfl
  have hC2_eq : C₁ * (2 : ℝ) ^ s * K_frost = C2_val := by
    have h1 : (2 : ℝ) ^ s = Real.rpow 2 s := by
      simp [Real.rpow_natCast]
    have h2 : Real.rpow 2 (s + 2) = Real.rpow 2 s * 4 := by
      have h3 : Real.rpow 2 (s + 2) = Real.rpow 2 s * Real.rpow 2 2 :=
        Real.rpow_add (by norm_num) s 2
      rw [h3]
      have h4 : Real.rpow 2 2 = 4 := by norm_num
      rw [h4] <;> ring
    dsimp only [C2_val]
    rw [h1, hK_frost_eq, h2] <;> ring
  have hC2_ge1 : 1 ≤ C2_val := by
    dsimp only [C2_val]
    have h1 : 1 ≤ C₁ := hC1
    have h2 : (1 : ℝ) ≤ (K1 : ℝ) := by exact_mod_cast hK1_ge1
    have h3 : Real.rpow 2 (s + 2) ≥ 4 := by
      have h4 : (2 : ℝ) ≤ s + 2 := by linarith [hs]
      have h5 : Real.rpow 2 (s + 2) ≥ Real.rpow 2 2 := Real.rpow_le_rpow_of_exponent_le (by norm_num) h4
      have h6 : Real.rpow 2 2 = 4 := by norm_num
      rw [h6] at h5
      exact h5
    have h7 : (K1 : ℝ)^2 ≥ 1 := by
      have h8 : (K1 : ℝ)^2 ≥ (1 : ℝ)^2 := by gcongr
      simpa using h8
    have h9 : 1024 * Real.rpow 2 (s + 2) * C₁ * (K1 : ℝ)^2 ≥ 1 := by
      calc 1024 * Real.rpow 2 (s + 2) * C₁ * (K1 : ℝ)^2
        ≥ 1024 * 4 * C₁ * (K1 : ℝ)^2 := by gcongr
      _ ≥ 1024 * 4 * 1 * (K1 : ℝ)^2 := by gcongr
      _ ≥ 1024 * 4 * 1 * 1 := by gcongr
      _ ≥ 1 := by norm_num
    exact h9
  have hΔ_pos : 0 < Δ := by linarith [hδ_pos, hδΔ]
  have h4 : 0 ≤ s := le_of_lt hs
  have h_frostman_core : ∀ (x : L) (r : ℝ), Δ ≤ r →
      ((C'.filter fun c => dist c x ≤ r).card : ℝ) ≤
        (C₁ * (2 : ℝ) ^ s * K_frost) * r ^ s * (C'.card : ℝ) :=
    frostman_inheritance_core δ Δ s C₁ P T P' T' coarse C' K_frost H_final
      hδ_pos hδΔ (by linarith [hΔ_half]) hC1 hT_frostman hT'_sub
      hP'_sub_P h_coarse_dist' h_inc_lower h_sum_T_upper hH_final_pos
  have h6 : ∀ (x : L) (r : ℝ), Δ ≤ r →
      ((C'.filter fun c => dist c x ≤ r).card : ℝ) ≤
        C2_val * r ^ s * (C'.card : ℝ) := by
    intro x r hr
    have h7 := h_frostman_core x r hr
    rw [hC2_eq] at h7
    exact h7
  have h_sep_C'_half : SeparatedAt Δ (C' : Set L) := by
    intro x hx y hy hne
    have h : Δ ≤ dist x y := h_sep_C' hx hy hne
    linarith
  have h_frostman_C' : IsFiniteDeltaSSet Δ s C2_val C' :=
    ⟨hC'_nonempty, hΔ_pos, hC2_ge1, h4, h_sep_C'_half, h6⟩
  exact ⟨C2_val, h_frostman_C', hC2_ge1, hC2_val_eq⟩

/-- Algebraic bound: H_final ≥ H_raw * m1 / 16. -/
lemma h_final_ge_algebraic
    (m1 H_raw H_final : ℕ)
    (hH_final_def : H_final = (H_raw * m1 + 3) / 4) :
    (H_final : ℝ) ≥ (H_raw : ℝ) * (m1 : ℝ) / 16 := by
  have h1 : 4 * H_final ≥ H_raw * m1 := by
    rw [hH_final_def]
    exact four_mul_div_ceil_ge (H_raw * m1)
  have h2 : (4 * (H_final : ℝ)) ≥ (H_raw : ℝ) * (m1 : ℝ) := by
    exact_mod_cast h1
  have h5 : (H_final : ℝ) ≥ (H_raw : ℝ) * (m1 : ℝ) / 4 := by linarith
  have h6 : (H_raw : ℝ) * (m1 : ℝ) / 4 ≥ (H_raw : ℝ) * (m1 : ℝ) / 16 := by
    have h7 : 0 ≤ (H_raw : ℝ) * (m1 : ℝ) := by positivity
    linarith
  exact le_trans h6 h5

/-- Wrapper for explicit_C2_bound with C2_val rewriting. -/
lemma C2_bound_lemma
    (s C₁ : ℝ) (K1 : ℕ) (K_val A : ℝ)
    (hs : 0 ≤ s) (hC1 : 1 ≤ C₁) (hK1_ge1 : 1 ≤ K1)
    (hK_val_eq : K_val = (2^21 : ℝ) * (K1 : ℝ)^6)
    (hA_ge : A ≥ 1024 * Real.rpow 2 (s + 2))
    (C2_val : ℝ)
    (hC2_val_eq : C2_val = 1024 * Real.rpow 2 (s + 2) * C₁ * (K1 : ℝ)^2) :
    C2_val ≤ A * Real.rpow K_val A * C₁ := by
  rw [hC2_val_eq]
  exact explicit_C2_bound s C₁ K1 K_val A hs hC1 hK1_ge1 hK_val_eq hA_ge

-- ============================================================================
-- Main theorem
-- ============================================================================

/-- Construct the edge set E and prove its degree bounds. -/
lemma construct_E
    {α L : Type*} [DecidableEq α] [DecidableEq L]
    (P1 : Finset α) (C1 : Finset L) (C_p : α → Finset L)
    (m2 j H_raw : ℕ)
    (hP1_nonempty : P1.Nonempty) (hC1_nonempty : C1.Nonempty)
    (h_m2_range : ∀ p ∈ P1, m2 ≤ (C_p p).card ∧ (C_p p).card < 2 * m2)
    (h_dyadic : ∀ c ∈ C1, 2^j ≤ (P1.filter (fun p => c ∈ C_p p)).card ∧ (P1.filter (fun p => c ∈ C_p p)).card < 2^(j+1))
    (hH_raw_eq : H_raw = 2^j) :
    ∃ (E : Finset (α × L)),
      E ⊆ P1 ×ˢ C1 ∧
      E.Nonempty ∧
      (E.card = ∑ p ∈ P1, (C_p p ∩ C1).card) ∧
      (∀ p ∈ P1, (E.filter (fun q : α × L => q.1 = p)).card ≤ 2 * m2) ∧
      (∀ c ∈ C1, (E.filter (fun q : α × L => q.2 = c)).card ≤ 2 * H_raw) ∧
      (∀ (x : α × L), x ∈ E ↔ x.1 ∈ P1 ∧ x.2 ∈ C_p x.1 ∩ C1) := by
  let E : Finset (α × L) := P1.biUnion (fun p => (C_p p ∩ C1).image (fun c => (p, c)))
  have hE_sub : E ⊆ P1 ×ˢ C1 := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨p', hp', hpc⟩
    rcases Finset.mem_image.mp hpc with ⟨c', hc', rfl⟩
    have h2 : c' ∈ C1 := (Finset.mem_inter.mp hc').2
    exact Finset.mem_product.mpr ⟨hp', h2⟩
  have h_disj_images : ∀ p1 ∈ P1, ∀ p2 ∈ P1, p1 ≠ p2 →
      Disjoint ((C_p p1 ∩ C1).image (fun c : L => (p1, c)))
        ((C_p p2 ∩ C1).image (fun c : L => (p2, c))) := by
    intro p1 _ p2 _ hne
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨c1, _, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨c2, _, h_eq⟩
    have h : p1 = p2 := by
      have h' : (p2, c2) = (p1, c1) := h_eq
      have h'' : p2 = p1 := (Prod.ext_iff.mp h').1
      exact h''.symm
    exact hne h
  have hE_card_eq : E.card = ∑ p ∈ P1, (C_p p ∩ C1).card := by
    rw [Finset.card_biUnion h_disj_images]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.card_image_of_injective]
    intro c1 c2 h
    exact (Prod.ext_iff.mp h).2
  have hE_nonempty : E.Nonempty := by
    rcases hC1_nonempty with ⟨c, hc⟩
    have h2 : 2^j ≤ (P1.filter (fun p => c ∈ C_p p)).card := (h_dyadic c hc).1
    have h3 : 0 < 2^j := by
      have h4 : 1 ≤ (2 : ℕ) := by norm_num
      have h5 : 1 ≤ 2^j := Nat.one_le_pow j (2 : ℕ) h4
      omega
    have h1 : 0 < (P1.filter (fun p => c ∈ C_p p)).card := lt_of_lt_of_le h3 h2
    rcases Finset.card_pos.mp h1 with ⟨p, hp⟩
    have hpin : p ∈ P1 := (Finset.mem_filter.mp hp).1
    have hcin : c ∈ C_p p := (Finset.mem_filter.mp hp).2
    have h4 : c ∈ C_p p ∩ C1 := Finset.mem_inter.mpr ⟨hcin, hc⟩
    have h5 : (p, c) ∈ E := by
      apply Finset.mem_biUnion.mpr
      exact ⟨p, hpin, Finset.mem_image.mpr ⟨c, h4, rfl⟩⟩
    exact ⟨(p, c), h5⟩
  have hdegA : ∀ p ∈ P1, (E.filter (fun q : α × L => q.1 = p)).card ≤ 2 * m2 := by
    intro p hp
    have h1 : E.filter (fun q : α × L => q.1 = p) ⊆ (C_p p ∩ C1).image (fun c : L => (p, c)) := by
      intro x hx
      have h2 : x ∈ E := (Finset.mem_filter.mp hx).1
      have h3 : x.1 = p := (Finset.mem_filter.mp hx).2
      rcases Finset.mem_biUnion.mp h2 with ⟨p', hp', hpc⟩
      rcases Finset.mem_image.mp hpc with ⟨c', hc', h_eq⟩
      have h4 : p' = x.1 := (Prod.ext_iff.mp h_eq).1
      have h5 : c' = x.2 := (Prod.ext_iff.mp h_eq).2
      have h6 : p' = p := by rw [h4, h3]
      have h7 : c' ∈ C_p p ∩ C1 := by rw [h6] at hc'; exact hc'
      have h8 : x = (p, c') := by
        exact Prod.ext h3 h5.symm
      rw [h8]
      exact Finset.mem_image.mpr ⟨c', h7, rfl⟩
    have h2 : (E.filter (fun q : α × L => q.1 = p)).card ≤ ((C_p p ∩ C1).image (fun c : L => (p, c))).card :=
      Finset.card_le_card h1
    have h3 : ((C_p p ∩ C1).image (fun c : L => (p, c))).card = (C_p p ∩ C1).card := by
      rw [Finset.card_image_of_injective]
      intro c1 c2 h
      exact (Prod.ext_iff.mp h).2
    rw [h3] at h2
    have h4 : (C_p p ∩ C1).card ≤ (C_p p).card := by
      have h5 : C_p p ∩ C1 ⊆ C_p p := by simp
      exact Finset.card_le_card h5
    have h6 : (C_p p).card < 2 * m2 := (h_m2_range p hp).2
    exact le_trans h2 (le_trans h4 (by omega))
  have hdegB : ∀ c ∈ C1, (E.filter (fun q : α × L => q.2 = c)).card ≤ 2 * H_raw := by
    intro c hc
    have h1 : E.filter (fun q : α × L => q.2 = c) ⊆ (P1.filter (fun p => c ∈ C_p p)).image (fun p : α => (p, c)) := by
      intro x hx
      have h2 : x ∈ E := (Finset.mem_filter.mp hx).1
      have h3 : x.2 = c := (Finset.mem_filter.mp hx).2
      rcases Finset.mem_biUnion.mp h2 with ⟨p', hp', hpc⟩
      rcases Finset.mem_image.mp hpc with ⟨c', hc', h_eq⟩
      have h4 : p' = x.1 := (Prod.ext_iff.mp h_eq).1
      have h5 : c' = x.2 := (Prod.ext_iff.mp h_eq).2
      have h6 : c' = c := by rw [h5, h3]
      have h7 : c ∈ C_p p' := by
        have h71 : c' ∈ C_p p' := (Finset.mem_inter.mp hc').1
        rw [h6] at h71
        exact h71
      have h8 : p' ∈ P1.filter (fun p => c ∈ C_p p) := by
        apply Finset.mem_filter.mpr
        exact ⟨hp', h7⟩
      have h9 : x = (p', c) := by
        exact Prod.ext h4.symm h3
      rw [h9]
      exact Finset.mem_image.mpr ⟨p', h8, rfl⟩
    have h2 : (E.filter (fun q : α × L => q.2 = c)).card ≤ ((P1.filter (fun p => c ∈ C_p p)).image (fun p : α => (p, c))).card :=
      Finset.card_le_card h1
    have h3 : ((P1.filter (fun p => c ∈ C_p p)).image (fun p : α => (p, c))).card = (P1.filter (fun p => c ∈ C_p p)).card := by
      rw [Finset.card_image_of_injective]
      intro p1 p2 h
      exact (Prod.ext_iff.mp h).1
    rw [h3] at h2
    have h4 : (P1.filter (fun p => c ∈ C_p p)).card < 2^(j+1) := (h_dyadic c hc).2
    have h5 : 2^(j+1) = 2 * H_raw := by
      rw [hH_raw_eq] <;> ring
    rw [h5] at h4
    exact le_trans h2 (le_of_lt h4)
  have hE_iff : ∀ (x : α × L), x ∈ E ↔ x.1 ∈ P1 ∧ x.2 ∈ C_p x.1 ∩ C1 := by
    intro x
    simp only [E, Finset.mem_biUnion, Finset.mem_image, exists_prop]
    constructor
    · rintro ⟨p, hp, c, hc, h_eq⟩
      have hpe : p = x.1 := (Prod.ext_iff.mp h_eq).1
      have hce : c = x.2 := (Prod.ext_iff.mp h_eq).2
      have h1 : x.1 ∈ P1 := by rw [←hpe]; exact hp
      have h2 : x.2 ∈ C_p x.1 ∩ C1 := by
        rw [hpe, hce] at hc
        exact hc
      exact ⟨h1, h2⟩
    · rintro ⟨hp, hc⟩
      exact ⟨x.1, hp, x.2, hc, rfl⟩
  exact ⟨E, hE_sub, hE_nonempty, hE_card_eq, hdegA, hdegB, hE_iff⟩

/-- Explicit upper bound for the QTTC constant A. -/
def qttcA_bound (s D B : ℝ) : ℝ :=
  2^21 * (((Real.log B + D) / Real.log 2 + 4)^6) + 1024 * Real.rpow 2 (s + 2) + 8

lemma quantitative_thick_tube_cover_main
    (s D B : ℝ)
    (hs : 0 < s) (hsD : s ≤ D) (hD : 1 ≤ D) (hB : 1 ≤ B) :
    ∃ A : ℝ, 1 ≤ A ∧ A ≤ qttcA_bound s D B ∧
      ∀ {α L : Type*} [PseudoMetricSpace L]
        [DecidableEq α] [DecidableEq L]
        {δ Δ C₁ : ℝ} {M : ℕ}
        (P : Finset α) (U : Finset L) (T : α → Finset L)
        (coarse : L → L) (coarseRange : Finset L),
        0 < δ → δ ≤ Δ → Δ ≤ (1 / 2 : ℝ) →
        1 ≤ C₁ → P.Nonempty → 0 < M →
        (∀ p ∈ P, T p ⊆ U) →
        (∀ p ∈ P, M / 2 < (T p).card ∧ (T p).card ≤ M) →
        (∀ p ∈ P, BallGrowth δ s C₁ (T p)) →
        (∀ ℓ ∈ U,
          coarse ℓ ∈ coarseRange ∧ dist ℓ (coarse ℓ) ≤ Δ) →
        SeparatedAt Δ (coarseRange : Set L) →
        (coarseRange.card : ℝ) ≤ B * Δ ^ (-D) →
        ∃ (P' : Finset α) (T' : α → Finset L)
          (C' : Finset L) (K C₂ : ℝ) (H : ℕ),
          1 ≤ K ∧
          K = (2^21 : ℝ) * ((Nat.log 2 coarseRange.card + 4 : ℕ) : ℝ)^6 ∧
          K ≤ A * Real.rpow (Real.log (2 / Δ)) A ∧
          1 ≤ C₂ ∧ 0 < H ∧
          P' ⊆ P ∧
          (P.card : ℝ) ≤ K * (P'.card : ℝ) ∧
          (∀ p ∈ P', T' p ⊆ T p) ∧
          (∀ p ∈ P', (M : ℝ) ≤ K * ((T' p).card : ℝ)) ∧
          C' = P'.biUnion (fun p => (T' p).image coarse) ∧
          C' ⊆ coarseRange ∧
          IsFiniteDeltaSSet Δ s C₂ C' ∧
          C₂ ≤ A * Real.rpow K A * C₁ ∧
          C₂ = 1024 * Real.rpow 2 (s + 2) * C₁ * ((Nat.log 2 coarseRange.card + 4 : ℕ) : ℝ)^2 ∧
          (∀ c ∈ C',
            H ≤ ∑ p ∈ P', assignedCount coarse T' p c) ∧
          (M : ℝ) * (P.card : ℝ) ≤
            K * (H : ℝ) * (C'.card : ℝ) ∧
          (H : ℝ) * (C'.card : ℝ) ≤
            K * (M : ℝ) * (P.card : ℝ) := by
  let C : ℝ := (Real.log B + D) / Real.log 2 + 4
  let A1 : ℝ := max (2^21 * C^6) 7
  let A2 : ℝ := 1024 * Real.rpow 2 (s + 2) + 1
  let A : ℝ := max A1 A2
  have hA_ge1 : 1 ≤ A := by
    have h1 : 1 ≤ A1 := by
      have h2 : (7 : ℝ) ≤ max (2^21 * C^6) 7 := le_max_right _ _
      linarith
    have h3 : A1 ≤ A := le_max_left _ _
    linarith
  have hA1 : A ≥ 2^21 * C^6 := by
    have h1 : 2^21 * C^6 ≤ A1 := le_max_left _ _
    have h2 : A1 ≤ A := le_max_left _ _
    linarith
  have hA7 : A ≥ 7 := by
    have h1 : (7 : ℝ) ≤ A1 := le_max_right _ _
    have h2 : A1 ≤ A := le_max_left _ _
    linarith
  have hA_le : A ≤ qttcA_bound s D B := by
    dsimp only [qttcA_bound]
    have hC_nonneg : 0 ≤ C := by
      dsimp only [C]
      have h1 : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
      positivity
    have hC_def : C = (Real.log B + D) / Real.log 2 + 4 := by rfl
    have h_rpow_pos : 0 < Real.rpow 2 (s + 2) := Real.rpow_pos_of_pos (by norm_num) _
    have h_pos2 : 0 ≤ 1024 * Real.rpow 2 (s + 2) := by positivity
    have h1 : A1 ≤ 2^21 * C^6 + 7 := by
      dsimp only [A1]
      have h_pos1 : 0 ≤ 2^21 * C^6 :=
        mul_nonneg (by positivity) (pow_nonneg hC_nonneg 6)
      have h2 : max (2^21 * C^6) 7 ≤ 2^21 * C^6 + 7 := by
        apply max_le
        · linarith
        · linarith [h_pos1]
      exact h2
    have h3 : A2 ≤ 1024 * Real.rpow 2 (s + 2) + 1 := by
      dsimp only [A2] <;> linarith
    have h4 : A = max A1 A2 := by rfl
    rw [h4]
    apply max_le
    · calc A1 ≤ 2^21 * C^6 + 7 := h1
         _ ≤ 2^21 * C^6 + (1024 * Real.rpow 2 (s + 2) + 8) := by linarith [h_pos2]
         _ = 2^21 * ((Real.log B + D) / Real.log 2 + 4)^6 + 1024 * Real.rpow 2 (s + 2) + 8 := by
           rw [hC_def] <;> ring
    · calc A2 ≤ 1024 * Real.rpow 2 (s + 2) + 1 := h3
         _ ≤ 2^21 * C^6 + 1024 * Real.rpow 2 (s + 2) + 8 := by
           have h_pos1 : 0 ≤ 2^21 * C^6 := by
             exact mul_nonneg (by positivity) (pow_nonneg hC_nonneg 6)
           linarith
         _ = 2^21 * ((Real.log B + D) / Real.log 2 + 4)^6 + 1024 * Real.rpow 2 (s + 2) + 8 := by
           rw [hC_def] <;> ring
  refine ⟨A, hA_ge1, hA_le, ?_⟩
  intro α L _ _ _ δ Δ C₁ M P U T coarse coarseRange
    hδ_pos hδΔ hΔ_half hC1 hP_nonempty hM_pos hT_sub hT_card hT_frostman
    h_coarse_in h_sep h_coarseRange_card
  let N := coarseRange.card
  let K1_val := Nat.log 2 N + 4
  let K_val : ℝ := 2^21 * (K1_val : ℝ)^6
  have hN_pos : 0 < N := by
    rcases hP_nonempty with ⟨p, hp⟩
    have hTp_pos : 0 < (T p).card := by
      have h : M / 2 < (T p).card := (hT_card p hp).1
      omega
    have hTp_nonempty : (T p).Nonempty := Finset.card_pos.mp hTp_pos
    rcases hTp_nonempty with ⟨ℓ, hℓ⟩
    have hℓU : ℓ ∈ U := hT_sub p hp hℓ
    have h : coarse ℓ ∈ coarseRange := (h_coarse_in ℓ hℓU).1
    exact Finset.card_pos.mpr ⟨coarse ℓ, h⟩
  have hK1_pos : 0 < K1_val := by
    dsimp only [K1_val]
    omega
  have hΔ_pos : 0 < Δ := by linarith
  have hK_bound : K_val ≤ A * Real.rpow (Real.log (2 / Δ)) A :=
    explicit_K_bound s D B Δ N K1_val K_val C A
      hB hD hΔ_pos hΔ_half hN_pos h_coarseRange_card rfl rfl rfl hA1 hA7
  have hT_card1 : ∀ p ∈ P, M / 2 < (T p).card := fun p hp => (hT_card p hp).1
  have hT_le1 : ∀ p ∈ P, (T p).card ≤ M := fun p hp => (hT_card p hp).2
  have h_coarse_in1 : ∀ ℓ ∈ U, coarse ℓ ∈ coarseRange := fun ℓ hℓ => (h_coarse_in ℓ hℓ).1
  rcases first_pigeonhole P U T coarse coarseRange hM_pos hT_card1 hT_le1 hT_sub h_coarse_in1
    with ⟨K1, C_p, m1_p, M1_vals, hK1_eq, hM1_card, hM1_mem, hCp_sub, h_assigned, h_mass_lower, h_mass_upper, h_m1_pow2⟩
  have hK1_pos2 : 0 < K1 := by
    rw [hK1_eq] <;> omega
  have hK1_eq' : K1 = K1_val := by
    simpa [K1_val] using hK1_eq
  have h_Cp_le_N : ∀ p ∈ P, (C_p p).card ≤ N := by
    intro p hp
    have h : C_p p ⊆ coarseRange := hCp_sub p hp
    exact Finset.card_le_card h
  have h_K1_ge_log : Nat.log 2 N + 1 ≤ K1 := by
    rw [hK1_eq'] <;> simp [K1_val] <;> omega
  have h_K1_ge4 : Nat.log 2 N + 4 ≤ K1 := by
    rw [hK1_eq'] <;> simp [K1_val] <;> omega
  rcases second_pigeonhole (K1 := K1) P C_p m1_p hM_pos hK1_pos2 hP_nonempty
    ⟨M1_vals, hM1_card, hM1_mem⟩ h_Cp_le_N h_K1_ge_log h_mass_lower h_mass_upper
    with ⟨P1, m1, m2, hP1_sub, hP1_card, h_m1_range, h_m2_range, h_mass_lower2, h_mass_upper2⟩
  have hP1_nonempty : P1.Nonempty := by
    by_contra h
    have h_empty : P1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [h_empty] at hP1_card
    have h_pos : 0 < (P.card : ℝ) := by exact_mod_cast hP_nonempty.card_pos
    have h_cont : (P.card : ℝ) ≤ 0 := by simpa using hP1_card
    linarith
  have hm1_pos : 0 < m1 := by
    have h_pos1 : (0 : ℝ) < (M : ℝ) / (32 * (K1 : ℝ)) := by positivity
    have h_pos2 : (M : ℝ) / (32 * (K1 : ℝ)) ≤ (m1 : ℝ) * (m2 : ℝ) := h_mass_lower2
    have h_pos3 : 0 < (m1 : ℝ) * (m2 : ℝ) := by linarith
    have h : 0 < m1 := by
      by_contra h4
      have h5 : m1 = 0 := by omega
      rw [h5] at h_pos3 <;> simp at h_pos3
    exact h
  have hm2_pos : 0 < m2 := by
    have h_pos1 : (0 : ℝ) < (M : ℝ) / (32 * (K1 : ℝ)) := by positivity
    have h_pos2 : (M : ℝ) / (32 * (K1 : ℝ)) ≤ (m1 : ℝ) * (m2 : ℝ) := h_mass_lower2
    have h_pos3 : 0 < (m1 : ℝ) * (m2 : ℝ) := by linarith
    have h : 0 < m2 := by
      by_contra h4
      have h5 : m2 = 0 := by omega
      rw [h5] at h_pos3 <;> simp at h_pos3
    exact h
  rcases third_pigeonhole (m2 := m2) (K1 := K1) P1 C_p coarseRange
    hK1_pos2 hN_pos hm2_pos hP1_nonempty
    (fun p hp => hCp_sub p (hP1_sub hp))
    (fun p hp => (h_m2_range p hp).1)
    rfl h_K1_ge4
    with ⟨C1, j, hC1_sub, h_dyadic, h_C1_lower⟩
  let H_raw := 2^j
  have hH_raw_pos : 0 < H_raw := by positivity
  have hC1_nonempty : C1.Nonempty := by
    have h_pos : (0 : ℝ) < (m2 : ℝ) * (P1.card : ℝ) / (4 * (K1 : ℝ)) := by
      have h1 : 0 < (m2 : ℝ) := by exact_mod_cast hm2_pos
      have h2 : 0 < (P1.card : ℝ) := by exact_mod_cast hP1_nonempty.card_pos
      have h3 : 0 < (4 * (K1 : ℝ)) := by
        have h4 : 0 < (K1 : ℝ) := by exact_mod_cast hK1_pos2
        linarith
      exact div_pos (mul_pos h1 h2) h3
    have h : (0 : ℝ) < (2^j : ℝ) * (C1.card : ℝ) := h_pos.trans_le h_C1_lower
    have h3 : 0 < C1.card := by
      have h4 : 0 < (2^j : ℝ) := by positivity
      have h5 : (0 : ℝ) < (C1.card : ℝ) := by nlinarith
      exact_mod_cast h5
    exact Finset.card_pos.mp h3

  -- ======================================================================
  -- 7. E construction and bipartite peeling
  -- ======================================================================
  rcases construct_E P1 C1 C_p m2 j H_raw hP1_nonempty hC1_nonempty h_m2_range h_dyadic rfl
    with ⟨E, hE_sub, hE_nonempty, hE_card_eq, hdegA, hdegB, hE_iff⟩
  let dA : ℝ := (E.card : ℝ) / (P1.card : ℝ)
  let dB : ℝ := (E.card : ℝ) / (C1.card : ℝ)
  rcases bipartite_peeling P1 C1 E hE_sub dA dB rfl rfl (2 * m2) (2 * H_raw) hdegA hdegB hP1_nonempty hC1_nonempty hE_nonempty
    with ⟨P', C', hP'_sub_P1, hC'_sub_C1, hdegA_low, hdegB_low, hB'_eq, hP'_card_lower, hC'_card_lower⟩
  let E' := inducedEdges E P' C'

  -- ======================================================================
  -- 8. Define T' and prove image equality
  -- ======================================================================
  let T' : α → Finset L := fun p => (T p).filter (fun ℓ => coarse ℓ ∈ C_p p ∩ C')
  have hT'_sub : ∀ p ∈ P', T' p ⊆ T p := by
    intro p _; exact Finset.filter_subset _ _
  have h_m1p_pos : ∀ p ∈ P', 0 < m1_p p := by
    intro p hp
    rcases h_m1_pow2 p (hP1_sub (hP'_sub_P1 hp)) with ⟨k, hk⟩
    rw [hk]
    have h4 : 1 ≤ (2 : ℕ) := by norm_num
    have h5 : 1 ≤ 2^k := Nat.one_le_pow k (2 : ℕ) h4
    omega
  have h_exists : ∀ p ∈ P', ∀ c ∈ C_p p, ∃ ℓ ∈ T p, coarse ℓ = c := by
    intro p hp c hc
    have h1 : m1_p p ≤ assignedCount coarse T p c := (h_assigned p (hP1_sub (hP'_sub_P1 hp)) c hc).1
    have h2 : 0 < assignedCount coarse T p c := by
      have h3 : 0 < m1_p p := h_m1p_pos p hp
      omega
    rcases Finset.card_pos.mp h2 with ⟨ℓ, hℓ⟩
    have h3 : ℓ ∈ (T p).filter (fun x => coarse x = c) := hℓ
    have h4 : ℓ ∈ T p := (Finset.mem_filter.mp h3).1
    have h5 : coarse ℓ = c := (Finset.mem_filter.mp h3).2
    exact ⟨ℓ, h4, h5⟩
  have h_image : ∀ p ∈ P', (T' p).image coarse = C_p p ∩ C' := by
    intro p hp
    exact image_eq_with_C' T coarse C_p C' p (h_exists p hp)
  have h_biUnion : C' = P'.biUnion (fun p => (T' p).image coarse) := by
    have h1 : P'.biUnion (fun p => (T' p).image coarse) = P'.biUnion (fun p => C_p p ∩ C') := by
      apply Finset.biUnion_congr rfl
      intro p hp
      exact h_image p hp
    rw [h1]
    have h2 : P'.biUnion (fun p => C_p p ∩ C') = E'.image Prod.snd := by
      ext c
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_inter]
      constructor
      · rintro ⟨p, hp, ⟨hc1, hc2⟩⟩
        refine ⟨(p, c), ?_, rfl⟩
        have h_in_E : (p, c) ∈ E := (hE_iff (p, c)).mpr
          ⟨hP'_sub_P1 hp, Finset.mem_inter.mpr ⟨hc1, hC'_sub_C1 hc2⟩⟩
        exact Finset.mem_filter.mpr ⟨h_in_E, ⟨hp, hc2⟩⟩
      · rintro ⟨⟨p, c'⟩, hE', rfl⟩
        have h3 : (p, c') ∈ E := (Finset.mem_filter.mp hE').1
        have h4 : p ∈ P' := (Finset.mem_filter.mp hE').2.1
        have h5 : c' ∈ C' := (Finset.mem_filter.mp hE').2.2
        have h6 : p ∈ P1 ∧ c' ∈ C_p p ∩ C1 := (hE_iff (p, c')).mp h3
        have hcin : c' ∈ C_p p := (Finset.mem_inter.mp h6.2).1
        exact ⟨p, h4, hcin, h5⟩
    rw [h2, hB'_eq]

  -- ======================================================================
  -- 9. H_final and incidence lower bound
  -- ======================================================================
  let H_final : ℕ := (H_raw * m1 + 3) / 4
  have hH_final_pos : 0 < H_final := by
    have h1 : 0 < H_raw * m1 := by positivity
    omega
  have hE_card_double : E.card = ∑ c ∈ C1, (P1.filter (fun p => c ∈ C_p p)).card := by
    have h_card1 : ∀ p ∈ P1, (C_p p ∩ C1).card = ∑ c ∈ C1, if c ∈ C_p p then 1 else 0 := by
      intro p _
      have h : ∑ c ∈ C1, (if c ∈ C_p p then 1 else 0) = (C1.filter (fun c => c ∈ C_p p)).card := by
        rw [Finset.sum_ite] <;> simp
      rw [h]
      have h2 : C1.filter (fun c => c ∈ C_p p) = C_p p ∩ C1 := by
        ext x; simp [Finset.mem_inter] <;> tauto
      rw [h2]
    have h_card2 : ∀ c ∈ C1, ∑ p ∈ P1, (if c ∈ C_p p then 1 else 0) = (P1.filter (fun p => c ∈ C_p p)).card := by
      intro c _
      rw [Finset.sum_ite] <;> simp
    calc
      E.card = ∑ p ∈ P1, (C_p p ∩ C1).card := hE_card_eq
      _ = ∑ p ∈ P1, ∑ c ∈ C1, (if c ∈ C_p p then 1 else 0) := by
        apply Finset.sum_congr rfl; intro p hp; exact h_card1 p hp
      _ = ∑ c ∈ C1, ∑ p ∈ P1, (if c ∈ C_p p then 1 else 0) := by rw [Finset.sum_comm]
      _ = ∑ c ∈ C1, (P1.filter (fun p => c ∈ C_p p)).card := by
        apply Finset.sum_congr rfl; intro c hc; exact h_card2 c hc
  have hE_ge_dyadic : (E.card : ℝ) ≥ (H_raw : ℝ) * (C1.card : ℝ) := by
    rw [hE_card_double]
    have h2 : ∀ c ∈ C1, (2^j : ℝ) ≤ ((P1.filter (fun p => c ∈ C_p p)).card : ℝ) := by
      intro c hc
      exact_mod_cast (h_dyadic c hc).1
    have h3 : ∑ c ∈ C1, (2^j : ℝ) ≤ ∑ c ∈ C1, ((P1.filter (fun p => c ∈ C_p p)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro c hc
      exact h2 c hc
    have h4 : ∑ c ∈ C1, (2^j : ℝ) = (2^j : ℝ) * (C1.card : ℝ) := by
      simp [Finset.sum_const] <;> ring
    rw [h4] at h3
    simpa [H_raw] using h3
  have h_dB_lower : (dB : ℝ) ≥ (H_raw : ℝ) := by
    have h1 : (dB : ℝ) = (E.card : ℝ) / (C1.card : ℝ) := by rfl
    rw [h1]
    have h2 : 0 < (C1.card : ℝ) := by exact_mod_cast hC1_nonempty.card_pos
    have h3 : (H_raw : ℝ) * (C1.card : ℝ) ≤ (E.card : ℝ) := hE_ge_dyadic
    have h4 : (H_raw : ℝ) * (C1.card : ℝ) / (C1.card : ℝ) ≤ (E.card : ℝ) / (C1.card : ℝ) := by
      apply div_le_div_of_nonneg_right h3
      exact_mod_cast h2.le
    have h5 : (H_raw : ℝ) * (C1.card : ℝ) / (C1.card : ℝ) = (H_raw : ℝ) := by
      have h6 : (C1.card : ℝ) ≠ 0 := h2.ne'
      exact mul_div_cancel_right₀ (H_raw : ℝ) h6
    rw [h5] at h4
    exact h4
  have h_inc_lower : ∀ c ∈ C', H_final ≤ ∑ p ∈ P', assignedCount coarse T' p c := by
    intro c hc
    have h_degB_low' : (dB / 4 : ℝ) ≤ (degBInd E P' C' c : ℝ) := hdegB_low c hc
    have h_filter_set_eq : (E'.filter (fun q : α × L => q.2 = c)) =
        (P'.filter (fun p => c ∈ C_p p)).image (fun p : α => (p, c)) := by
      ext z
      rcases z with ⟨p0, c0⟩
      simp only [E', inducedEdges, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨hE', hp0, hc0⟩, h_eq : c0 = c⟩
        have hE_decomp : p0 ∈ P1 ∧ c0 ∈ C_p p0 ∩ C1 := (hE_iff (p0, c0)).mp hE'
        have hcin : c0 ∈ C_p p0 := (Finset.mem_inter.mp hE_decomp.2).1
        have h_final : c ∈ C_p p0 := by rw [←h_eq]; exact hcin
        exact ⟨p0, ⟨hp0, h_final⟩, by simp [h_eq]⟩
      · rintro ⟨p1, ⟨hp1, hcin⟩, h_eq⟩
        have hpe : p1 = p0 := (Prod.ext_iff.mp h_eq).1
        have hce : c = c0 := (Prod.ext_iff.mp h_eq).2
        have hpinP' : p1 ∈ P' := hp1
        have hcin' : c ∈ C_p p1 := hcin
        have h_in_E : (p1, c) ∈ E := by
          have hE_iff' := hE_iff (p1, c)
          rw [hE_iff']
          exact ⟨hP'_sub_P1 hpinP', Finset.mem_inter.mpr ⟨hcin, hC'_sub_C1 hc⟩⟩
        have h_goal : ((p0, c0) ∈ E ∧ p0 ∈ P' ∧ c0 ∈ C') ∧ c0 = c := by
          have h9 : (p1, c) = (p0, c0) := h_eq
          have h10 : (p0, c0) ∈ E := by rw [←h9]; exact h_in_E
          have h11 : p0 ∈ P' := by rw [←hpe]; exact hpinP'
          have h12 : c0 ∈ C' := by rw [←hce]; exact hc
          exact ⟨⟨h10, h11, h12⟩, hce.symm⟩
        exact h_goal
    have h_degB_eq : (degBInd E P' C' c : ℝ) = ((P'.filter (fun p => c ∈ C_p p)).card : ℝ) := by
      rw [degBInd, h_filter_set_eq]
      rw [Finset.card_image_of_injective]
      <;> intro p1 p2 h
      exact (Prod.ext_iff.mp h).1
    have h_filter_ge : ((P'.filter (fun p => c ∈ C_p p)).card : ℝ) ≥ (H_raw : ℝ) / 4 := by
      rw [←h_degB_eq]
      have h5 : (H_raw : ℝ) / 4 ≤ (dB / 4 : ℝ) := by gcongr
      exact h5.trans h_degB_low'
    have h_each_ge : ∀ p ∈ P'.filter (fun p => c ∈ C_p p), (m1 : ℝ) ≤ (assignedCount coarse T' p c : ℝ) := by
      intro p hp
      have h_p_in_P' : p ∈ P' := (Finset.mem_filter.mp hp).1
      have h_c_in_Cp : c ∈ C_p p := (Finset.mem_filter.mp hp).2
      have h_c_in_C' : c ∈ C' := hc
      have h6 : c ∈ C_p p ∩ C' := Finset.mem_inter.mpr ⟨h_c_in_Cp, h_c_in_C'⟩
      have h_filter_eq : (T' p).filter (fun ℓ : L => coarse ℓ = c) = (T p).filter (fun ℓ : L => coarse ℓ = c) := by
        ext ℓ
        simp only [T', Finset.mem_filter]
        <;> constructor
        · rintro ⟨⟨hℓ, _⟩, hcoarse⟩
          exact ⟨hℓ, hcoarse⟩
        · rintro ⟨hℓ, hcoarse⟩
          have h9 : coarse ℓ ∈ C_p p ∩ C' := by
            rw [hcoarse] <;> exact h6
          exact ⟨⟨hℓ, h9⟩, hcoarse⟩
      have h7 : assignedCount coarse T' p c = assignedCount coarse T p c := by
        dsimp only [assignedCount]
        rw [h_filter_eq]
      rw [h7]
      have h8 : (m1 : ℝ) ≤ (assignedCount coarse T p c : ℝ) := by
        have h9 : m1 ≤ m1_p p := (h_m1_range p (hP'_sub_P1 h_p_in_P')).1
        have h10 : m1_p p ≤ assignedCount coarse T p c := (h_assigned p (hP1_sub (hP'_sub_P1 h_p_in_P')) c h_c_in_Cp).1
        exact_mod_cast le_trans h9 h10
      exact h8
    let S : ℕ := ∑ p ∈ P', assignedCount coarse T' p c
    have hS_eq : (S : ℝ) = ∑ p ∈ P', (assignedCount coarse T' p c : ℝ) := by exact_mod_cast rfl
    have h_sum_ge : (S : ℝ) ≥ (m1 : ℝ) * (H_raw : ℝ) / 4 := by
      rw [hS_eq]
      have h9 : ∑ p ∈ P', (assignedCount coarse T' p c : ℝ) ≥ ∑ p ∈ P'.filter (fun p => c ∈ C_p p), (assignedCount coarse T' p c : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · apply Finset.filter_subset
        · intro _ _ _; positivity
      have h11 : ∑ p ∈ P'.filter (fun p => c ∈ C_p p), (assignedCount coarse T' p c : ℝ) ≥ ((P'.filter (fun p => c ∈ C_p p)).card : ℝ) * (m1 : ℝ) := by
        have h12 := Finset.sum_le_sum h_each_ge
        simpa using h12
      have h13 : ((P'.filter (fun p => c ∈ C_p p)).card : ℝ) * (m1 : ℝ) = (m1 : ℝ) * ((P'.filter (fun p => c ∈ C_p p)).card : ℝ) := by ring
      calc
        (∑ p ∈ P', (assignedCount coarse T' p c : ℝ))
          ≥ ∑ p ∈ P'.filter (fun p => c ∈ C_p p), (assignedCount coarse T' p c : ℝ) := h9
        _ ≥ ((P'.filter (fun p => c ∈ C_p p)).card : ℝ) * (m1 : ℝ) := h11
        _ = (m1 : ℝ) * ((P'.filter (fun p => c ∈ C_p p)).card : ℝ) := h13
        _ ≥ (m1 : ℝ) * ((H_raw : ℝ) / 4) := by gcongr
        _ = (m1 : ℝ) * (H_raw : ℝ) / 4 := by ring
    have h_H_final_le : H_final ≤ S :=
      incidence_algebraic m1 H_raw H_final S rfl h_sum_ge
    exact_mod_cast h_H_final_le

  -- ======================================================================
  -- 10. T' cardinality lower bound: M ≤ K_val * |T' p|
  -- ======================================================================
  have hK1_ge1 : 1 ≤ K1 := by
    rw [hK1_eq'] <;> simp [K1_val] <;> omega
  have h_dA_lower : (dA : ℝ) ≥ (m2 : ℝ) / (4 * (K1 : ℝ)) := by
    have hP1_pos : (P1.card : ℝ) > 0 := by exact_mod_cast hP1_nonempty.card_pos
    have hK1_pos' : (K1 : ℝ) > 0 := by exact_mod_cast hK1_pos2
    have h2 : (H_raw : ℝ) * (C1.card : ℝ) ≥ (m2 : ℝ) * (P1.card : ℝ) / (4 * (K1 : ℝ)) := by
      exact_mod_cast h_C1_lower
    simpa [dA] using dA_lower_algebraic (E.card : ℝ) (P1.card : ℝ) (C1.card : ℝ) m2 K1 (H_raw : ℝ) hP1_pos hK1_pos' hE_ge_dyadic h2
  have h_degA_eq : ∀ p ∈ P', (degAInd E P' C' p : ℝ) = ((C_p p ∩ C').card : ℝ) := by
    intro p hp
    have h1 : (E'.filter (fun q : α × L => q.1 = p)) =
        (C_p p ∩ C').image (fun c : L => (p, c)) := by
      apply Finset.Subset.antisymm
      · intro x hx
        have hxE' : x ∈ E' := (Finset.mem_filter.mp hx).1
        have hx1 : x.1 = p := (Finset.mem_filter.mp hx).2
        have hxE : x ∈ E := (Finset.mem_filter.mp hxE').1
        have hxC' : x.2 ∈ C' := (Finset.mem_filter.mp hxE').2.2
        have h2 : x.1 ∈ P1 ∧ x.2 ∈ C_p x.1 ∩ C1 := (hE_iff x).mp hxE
        rcases h2 with ⟨h21, h22⟩
        have h3 : x.2 ∈ C_p x.1 := (Finset.mem_inter.mp h22).1
        have h4 : x.2 ∈ C_p p := by rw [hx1] at h3; exact h3
        have h5 : x.2 ∈ C_p p ∩ C' := Finset.mem_inter.mpr ⟨h4, hxC'⟩
        have h6 : x = (p, x.2) := by
          ext <;> simp [hx1]
        rw [h6]
        exact Finset.mem_image.mpr ⟨x.2, h5, rfl⟩
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨c, hc, rfl⟩
        have hcinCp : c ∈ C_p p := (Finset.mem_inter.mp hc).1
        have hcinC' : c ∈ C' := (Finset.mem_inter.mp hc).2
        have h7 : (p, c) ∈ E := (hE_iff (p, c)).mpr
          ⟨hP'_sub_P1 hp, Finset.mem_inter.mpr ⟨hcinCp, hC'_sub_C1 hcinC'⟩⟩
        have h8 : (p, c) ∈ E' := by
          simp only [E', inducedEdges, Finset.mem_filter]
          exact ⟨h7, hp, hcinC'⟩
        apply Finset.mem_filter.mpr
        exact ⟨h8, by simp⟩
    rw [degAInd, h1]
    rw [Finset.card_image_of_injective]
    <;> intro c1 c2 h
    exact (Prod.ext_iff.mp h).2
  have h_T'_card_lower : ∀ p ∈ P', (M : ℝ) ≤ K_val * ((T' p).card : ℝ) := by
    intro p hp
    have h1 : (degAInd E P' C' p : ℝ) ≥ (dA : ℝ) / 4 := hdegA_low p hp
    have h2 : ((C_p p ∩ C').card : ℝ) ≥ (dA : ℝ) / 4 := by
      rw [←h_degA_eq p hp]; exact h1
    have h3 : ((C_p p ∩ C').card : ℝ) ≥ (m2 : ℝ) / (16 * (K1 : ℝ)) := by
      calc
        ((C_p p ∩ C').card : ℝ) ≥ (dA : ℝ) / 4 := h2
        _ ≥ ((m2 : ℝ) / (4 * (K1 : ℝ))) / 4 := by gcongr
        _ = (m2 : ℝ) / (16 * (K1 : ℝ)) := by ring
    have h4 : ∀ c ∈ C_p p ∩ C', (m1 : ℝ) ≤ (assignedCount coarse T' p c : ℝ) := by
      intro c hc
      have h_c_in_Cp : c ∈ C_p p := (Finset.mem_inter.mp hc).1
      have h_c_in_C' : c ∈ C' := (Finset.mem_inter.mp hc).2
      have h_filter_eq : (T' p).filter (fun ℓ : L => coarse ℓ = c) = (T p).filter (fun ℓ : L => coarse ℓ = c) := by
        ext ℓ
        simp only [T', Finset.mem_filter]
        <;> constructor
        · rintro ⟨⟨hℓ, _⟩, hcoarse⟩
          exact ⟨hℓ, hcoarse⟩
        · rintro ⟨hℓ, hcoarse⟩
          have h9 : coarse ℓ ∈ C_p p ∩ C' := by
            rw [hcoarse] <;> exact hc
          exact ⟨⟨hℓ, h9⟩, hcoarse⟩
      have h7 : assignedCount coarse T' p c = assignedCount coarse T p c := by
        dsimp only [assignedCount] <;> rw [h_filter_eq]
      rw [h7]
      have h8 : (m1 : ℝ) ≤ (assignedCount coarse T p c : ℝ) := by
        have h9 : m1 ≤ m1_p p := (h_m1_range p (hP'_sub_P1 hp)).1
        have h10 : m1_p p ≤ assignedCount coarse T p c := (h_assigned p (hP1_sub (hP'_sub_P1 hp)) c h_c_in_Cp).1
        exact_mod_cast le_trans h9 h10
      exact h8
    have h_sum_eq : ((T' p).card : ℝ) = ∑ c ∈ C_p p ∩ C', (assignedCount coarse T' p c : ℝ) := by
      have h_maps : Set.MapsTo coarse (↑(T' p)) (↑(C_p p ∩ C')) := by
        intro ℓ hℓ
        have h5 : coarse ℓ ∈ (C_p p ∩ C') := (Finset.mem_filter.mp hℓ).2
        simpa using h5
      have h6 : (T' p).card = ∑ c ∈ C_p p ∩ C', ((T' p).filter (fun ℓ => coarse ℓ = c)).card :=
        Finset.card_eq_sum_card_fiberwise (f := coarse) (s := T' p) (t := C_p p ∩ C') h_maps
      exact_mod_cast h6
    have h5 : ((T' p).card : ℝ) ≥ (m1 : ℝ) * ((C_p p ∩ C').card : ℝ) := by
      rw [h_sum_eq]
      have h6 : ∑ c ∈ C_p p ∩ C', (assignedCount coarse T' p c : ℝ) ≥
          ∑ c ∈ C_p p ∩ C', (m1 : ℝ) := Finset.sum_le_sum h4
      have h7 : ∑ c ∈ C_p p ∩ C', (m1 : ℝ) = (m1 : ℝ) * ((C_p p ∩ C').card : ℝ) := by
        simp [Finset.sum_const] <;> ring
      rw [h7] at h6
      exact h6
    have hK_val_eq : K_val = (2^21 : ℝ) * (K1 : ℝ)^6 := by
      simp [K_val, K1_val, hK1_eq'] <;> norm_cast <;> ring
    exact t_prime_card_algebraic M K1 m1 m2 K_val
      ((C_p p ∩ C').card : ℝ) ((T' p).card : ℝ)
      hK1_ge1 h_mass_lower2 h3 h5 hK_val_eq

  -- ======================================================================
  -- 11. P cardinality bound: |P| ≤ K_val * |P'|
  -- ======================================================================
  have h_P_card_lower1 : (P1.card : ℝ) ≤ (32 : ℝ) * (K1 : ℝ) * (P'.card : ℝ) := by
    have h5 : (m2 : ℝ) > 0 := by exact_mod_cast hm2_pos
    have h6 : (K1 : ℝ) > 0 := by exact_mod_cast hK1_pos2
    have h_pos8 : 0 < (8 * (m2 : ℝ)) := by positivity
    have h_pos4 : 0 < (4 * (K1 : ℝ)) := by positivity
    have h1' : (P'.card : ℝ) ≥ (P1.card : ℝ) * (dA : ℝ) / (8 * (m2 : ℝ)) := by
      have h_eq : (↑(2 * m2) : ℝ) = 2 * (m2 : ℝ) := by
        simp [Nat.cast_mul] <;> ring
      have h := hP'_card_lower
      rw [h_eq] at h
      have h2 : (4 * (2 * (m2 : ℝ))) = (8 * (m2 : ℝ)) := by ring
      rw [h2] at h
      exact h
    have h7 : (8 * (m2 : ℝ)) * (P'.card : ℝ) ≥ (P1.card : ℝ) * (dA : ℝ) := by
      have h71 : (8 * (m2 : ℝ)) * (P'.card : ℝ) ≥
          (8 * (m2 : ℝ)) * ((P1.card : ℝ) * (dA : ℝ) / (8 * (m2 : ℝ))) :=
        mul_le_mul_of_nonneg_left h1' h_pos8.le
      have h72 : (8 * (m2 : ℝ)) * ((P1.card : ℝ) * (dA : ℝ) / (8 * (m2 : ℝ))) =
          (P1.card : ℝ) * (dA : ℝ) := by
        rw [mul_comm]
        exact div_mul_cancel₀ _ h_pos8.ne'
      rw [h72] at h71
      exact h71
    have h8 : (4 * (K1 : ℝ)) * (dA : ℝ) ≥ (m2 : ℝ) := by
      have h81 : (4 * (K1 : ℝ)) * (dA : ℝ) ≥
          (4 * (K1 : ℝ)) * ((m2 : ℝ) / (4 * (K1 : ℝ))) :=
        mul_le_mul_of_nonneg_left h_dA_lower h_pos4.le
      have h82 : (4 * (K1 : ℝ)) * ((m2 : ℝ) / (4 * (K1 : ℝ))) = (m2 : ℝ) := by
        rw [mul_comm]
        exact div_mul_cancel₀ _ h_pos4.ne'
      rw [h82] at h81
      exact h81
    have h9 : (32 : ℝ) * (K1 : ℝ) * (m2 : ℝ) * (P'.card : ℝ) ≥
        (P1.card : ℝ) * (m2 : ℝ) := by
      calc
        (32 : ℝ) * (K1 : ℝ) * (m2 : ℝ) * (P'.card : ℝ)
          = (4 * (K1 : ℝ)) * ((8 * (m2 : ℝ)) * (P'.card : ℝ)) := by ring
        _ ≥ (4 * (K1 : ℝ)) * ((P1.card : ℝ) * (dA : ℝ)) := by
          exact mul_le_mul_of_nonneg_left h7 (by positivity)
        _ = (P1.card : ℝ) * ((4 * (K1 : ℝ)) * (dA : ℝ)) := by ring
        _ ≥ (P1.card : ℝ) * (m2 : ℝ) := by
          have h_pos : 0 ≤ (P1.card : ℝ) := by exact_mod_cast hP1_nonempty.card_pos.le
          exact mul_le_mul_of_nonneg_left h8 h_pos
    have h10 : (m2 : ℝ) > 0 := h5
    have h9' : (P1.card : ℝ) * (m2 : ℝ) ≤ ((32 : ℝ) * (K1 : ℝ) * (P'.card : ℝ)) * (m2 : ℝ) := by
      have h_comm : (32 : ℝ) * (K1 : ℝ) * (m2 : ℝ) * (P'.card : ℝ) =
          ((32 : ℝ) * (K1 : ℝ) * (P'.card : ℝ)) * (m2 : ℝ) := by ring
      rw [h_comm] at h9
      exact h9
    have h11 : (32 : ℝ) * (K1 : ℝ) * (P'.card : ℝ) ≥ (P1.card : ℝ) := by
      nlinarith
    exact h11
  have hK_val_eq2 : K_val = (2^21 : ℝ) * (K1 : ℝ)^6 := by
    simp [K_val, K1_val, hK1_eq'] <;> norm_cast <;> ring
  have h_P_card_bound : (P.card : ℝ) ≤ K_val * (P'.card : ℝ) :=
    p_card_bound_algebraic (P.card : ℝ) (P1.card : ℝ) (P'.card : ℝ) K1 K_val
      hK1_ge1 hP1_card h_P_card_lower1 (Nat.cast_nonneg P'.card) hK_val_eq2

  -- ======================================================================
  -- 12. Frostman for C'
  -- ======================================================================
  let K_frost : ℝ := 4096 * (K1 : ℝ)^2
  have hC'_nonempty : C'.Nonempty := by
    have h_eq : (↑(2 * H_raw) : ℝ) = 2 * (H_raw : ℝ) := by
      simp [Nat.cast_mul] <;> ring
    have h1 : (C'.card : ℝ) ≥ (C1.card : ℝ) * (dB : ℝ) / (4 * (2 * (H_raw : ℝ))) := by
      have h := hC'_card_lower
      rw [h_eq] at h
      exact h
    have h2 : (C1.card : ℝ) > 0 := Nat.cast_pos.mpr hC1_nonempty.card_pos
    have hE_pos : (E.card : ℝ) > 0 := Nat.cast_pos.mpr hE_nonempty.card_pos
    have h3 : (dB : ℝ) > 0 := by
      have h31 : (dB : ℝ) = (E.card : ℝ) / (C1.card : ℝ) := rfl
      rw [h31]
      exact div_pos hE_pos h2
    have hH_pos : (H_raw : ℝ) > 0 := Nat.cast_pos.mpr hH_raw_pos
    have h4 : (4 * (2 * (H_raw : ℝ))) > 0 := by positivity
    have h6 : (C1.card : ℝ) * (dB : ℝ) / (4 * (2 * (H_raw : ℝ))) > 0 :=
      div_pos (mul_pos h2 h3) h4
    have h7 : (C'.card : ℝ) > 0 := h6.trans_le h1
    have h8 : 0 < C'.card := Nat.cast_pos.mp h7
    exact Finset.card_pos.mp h8
  have hC'_sub_coarseRange : C' ⊆ coarseRange := by
    trans C1 <;> [exact hC'_sub_C1; exact hC1_sub]
  have h_sep_C' : SeparatedAt Δ (C' : Set L) := by
    have h : SeparatedAt Δ (coarseRange : Set L) := h_sep
    exact h.mono (show (C' : Set L) ⊆ (coarseRange : Set L) from hC'_sub_coarseRange)
  have h_coarse_dist' : ∀ ℓ ∈ P'.biUnion T', dist ℓ (coarse ℓ) ≤ Δ := by
    intro ℓ hℓ
    rcases Finset.mem_biUnion.mp hℓ with ⟨p, hp, hℓT'⟩
    have hℓT : ℓ ∈ T p := hT'_sub p hp hℓT'
    have hℓU : ℓ ∈ U := hT_sub p (hP1_sub (hP'_sub_P1 hp)) hℓT
    exact (h_coarse_in ℓ hℓU).2
  have hH_final_ge4 : 4 * H_final ≥ H_raw * m1 := by
    dsimp only [H_final]
    exact four_mul_div_ceil_ge (H_raw * m1)
  have h_C1_lower_Hraw : (H_raw : ℝ) * (C1.card : ℝ) ≥ (m2 : ℝ) * (P1.card : ℝ) / (4 * (K1 : ℝ)) := by
    have h_eq : (H_raw : ℝ) = (2^j : ℝ) := by
      exact_mod_cast rfl
    rw [h_eq]
    exact h_C1_lower
  have h_sum_T_upper : (∑ p ∈ P', (T p).card : ℝ) ≤ K_frost * (H_final : ℝ) * (C'.card : ℝ) := by
    have h := sum_T_upper_bound P P1 P' T M K1 m1 m2 C1 C' E H_raw H_final
      hT_card hP'_sub_P1 hP1_sub hC1_nonempty hE_nonempty hH_raw_pos hH_final_pos
      hC'_card_lower hE_ge_dyadic h_C1_lower_Hraw h_mass_lower2 hH_final_ge4 hK1_ge1
    have hK : K_frost = 4096 * (K1 : ℝ)^2 := by rfl
    rw [hK]
    exact h
  rcases frostman_section (M := M) P T P' T' coarse C' K_frost (H_final : ℝ) s K1 rfl
      hδ_pos hδΔ hΔ_half hC1 hs hK1_ge1 hT_frostman hT'_sub
      (fun x hx => hP1_sub (hP'_sub_P1 hx))
      hC'_nonempty h_sep_C' h_coarse_dist'
      (fun c hc => by exact_mod_cast h_inc_lower c hc)
      h_sum_T_upper (by exact_mod_cast hH_final_pos)
    with ⟨C2_val, h_frostman_C', hC2_ge1, hC2_val_eq⟩

  -- ======================================================================
  -- 13. Average upper bound
  -- ======================================================================
  have h_cover : ∀ p ∈ P', (T' p).image coarse ⊆ C' := by
    intro p hp
    have h_eq : (T' p).image coarse = C_p p ∩ C' := h_image p hp
    rw [h_eq]
    exact (show (C_p p ∩ C') ⊆ C' from by simp)
  have h_T'_le_M : ∀ p ∈ P', ((T' p).card : ℝ) ≤ (M : ℝ) := by
    intro p hp
    have h1 : T' p ⊆ T p := hT'_sub p hp
    have h2 : (T' p).card ≤ (T p).card := Finset.card_le_card h1
    have h3 : (T p).card ≤ M := (hT_card p (hP1_sub (hP'_sub_P1 hp))).2
    exact_mod_cast le_trans h2 h3
  have hK_val_ge1_inline : 1 ≤ K_val := by
    have h_eq : K_val = (2^21 : ℝ) * (K1 : ℝ)^6 := by
      simp [K_val, K1_val, hK1_eq'] <;> norm_cast <;> ring
    rw [h_eq]
    exact K_val_ge1_lemma K1 hK1_ge1
  have h_avg_upper : (H_final : ℝ) * (C'.card : ℝ) ≤ K_val * (M : ℝ) * (P.card : ℝ) :=
    avg_upper_bound P P' T' coarse C' H_final M K_val
      (fun x hx => hP1_sub (hP'_sub_P1 hx))
      hK_val_ge1_inline
      (fun c hc => by exact_mod_cast h_inc_lower c hc)
      h_T'_le_M h_cover

  -- ======================================================================
  -- 14. Average lower bound
  -- ======================================================================
  have h_m2_bound2 : (m2 : ℝ) * (P'.card : ℝ) ≤ (128 : ℝ) * (K1 : ℝ) * (H_raw : ℝ) * (C'.card : ℝ) := by
    have h1 : (C'.card : ℝ) ≥ (E.card : ℝ) / (8 * (H_raw : ℝ)) := by
      have h_eq : (↑(2 * H_raw) : ℝ) = 2 * (H_raw : ℝ) := by
        simp [Nat.cast_mul] <;> ring
      have h2 : (C'.card : ℝ) ≥ (C1.card : ℝ) * (dB : ℝ) / (4 * (2 * (H_raw : ℝ))) := by
        have h := hC'_card_lower
        rw [h_eq] at h
        exact h
      have h3 : (C1.card : ℝ) * (dB : ℝ) = (E.card : ℝ) := by
        rw [show (dB : ℝ) = (E.card : ℝ) / (C1.card : ℝ) from rfl]
        have h4 : (C1.card : ℝ) > 0 := by exact_mod_cast hC1_nonempty.card_pos
        have h5 : (C1.card : ℝ) * ((E.card : ℝ) / (C1.card : ℝ)) = (E.card : ℝ) := by
          rw [mul_comm]
          exact div_mul_cancel₀ _ h4.ne'
        exact h5
      rw [h3] at h2
      have h4 : (4 * ((2 * H_raw : ℝ))) = (8 * (H_raw : ℝ)) := by ring
      rw [h4] at h2
      exact h2
    have h5 : (E.card : ℝ) ≥ (m2 : ℝ) * (P1.card : ℝ) / (4 * (K1 : ℝ)) := by
      have h6 : (E.card : ℝ) ≥ (H_raw : ℝ) * (C1.card : ℝ) := hE_ge_dyadic
      have h7 : (H_raw : ℝ) * (C1.card : ℝ) ≥ (m2 : ℝ) * (P1.card : ℝ) / (4 * (K1 : ℝ)) := by
        exact_mod_cast h_C1_lower
      exact h7.trans h6
    have h8 : (H_raw : ℝ) * (C'.card : ℝ) ≥ (m2 : ℝ) * (P1.card : ℝ) / (32 * (K1 : ℝ)) := by
      have h9 : (H_raw : ℝ) > 0 := by exact_mod_cast hH_raw_pos
      calc
        (H_raw : ℝ) * (C'.card : ℝ)
          ≥ (H_raw : ℝ) * ((E.card : ℝ) / (8 * (H_raw : ℝ))) := by gcongr
        _ = (E.card : ℝ) / 8 := by
          have h_eq : (H_raw : ℝ) * ((E.card : ℝ) / (8 * (H_raw : ℝ))) = (E.card : ℝ) / 8 := by
            have h3 : (H_raw : ℝ) * ((E.card : ℝ) / (8 * (H_raw : ℝ))) =
                ((H_raw : ℝ) * (E.card : ℝ)) / (8 * (H_raw : ℝ)) := by
              rw [mul_div_assoc] <;> ring
            rw [h3]
            have h4 : (8 * (H_raw : ℝ)) = (H_raw : ℝ) * 8 := by ring
            rw [h4]
            have h10 : (8 : ℝ) ≠ 0 := by norm_num
            have h11 : (H_raw : ℝ) * 8 ≠ 0 := mul_ne_zero h9.ne' h10
            exact (div_eq_div_iff h11 h10).mpr (by ring)
          exact h_eq
        _ ≥ ((m2 : ℝ) * (P1.card : ℝ) / (4 * (K1 : ℝ))) / 8 := by gcongr
        _ = (m2 : ℝ) * (P1.card : ℝ) / (32 * (K1 : ℝ)) := by ring
    have h9 : (m2 : ℝ) * (P'.card : ℝ) ≤ (m2 : ℝ) * (P1.card : ℝ) := by
      gcongr <;> exact_mod_cast card_le_card hP'_sub_P1
    have h_pos32 : 0 < (32 : ℝ) * (K1 : ℝ) := by positivity
    have h10 : (m2 : ℝ) * (P1.card : ℝ) ≤ (32 : ℝ) * (K1 : ℝ) * ((H_raw : ℝ) * (C'.card : ℝ)) := by
      have h11 : (32 : ℝ) * (K1 : ℝ) * ((H_raw : ℝ) * (C'.card : ℝ)) ≥
          (32 : ℝ) * (K1 : ℝ) * ((m2 : ℝ) * (P1.card : ℝ) / (32 * (K1 : ℝ))) :=
        mul_le_mul_of_nonneg_left h8 h_pos32.le
      have h12 : (32 : ℝ) * (K1 : ℝ) * ((m2 : ℝ) * (P1.card : ℝ) / (32 * (K1 : ℝ))) =
          (m2 : ℝ) * (P1.card : ℝ) := by
        rw [mul_comm]
        exact div_mul_cancel₀ _ h_pos32.ne'
      rw [h12] at h11
      exact h11
    have h13 : (32 : ℝ) * (K1 : ℝ) * ((H_raw : ℝ) * (C'.card : ℝ)) ≤
        (128 : ℝ) * (K1 : ℝ) * (H_raw : ℝ) * (C'.card : ℝ) := by
      have h14 : (32 : ℝ) ≤ (128 : ℝ) := by norm_num
      have h15a : 0 ≤ (K1 : ℝ) := by
        have h : (1 : ℝ) ≤ (K1 : ℝ) := by exact_mod_cast hK1_ge1
        linarith
      have h15b : 0 ≤ (H_raw : ℝ) := by exact_mod_cast hH_raw_pos.le
      have h15c : 0 ≤ (C'.card : ℝ) := Nat.cast_nonneg _
      have h15 : 0 ≤ (K1 : ℝ) * (H_raw : ℝ) * (C'.card : ℝ) :=
        mul_nonneg (mul_nonneg h15a h15b) h15c
      have h16 : (32 : ℝ) * ((K1 : ℝ) * (H_raw : ℝ) * (C'.card : ℝ)) ≤
          (128 : ℝ) * ((K1 : ℝ) * (H_raw : ℝ) * (C'.card : ℝ)) :=
        mul_le_mul_of_nonneg_right h14 h15
      have h17 : (32 : ℝ) * (K1 : ℝ) * ((H_raw : ℝ) * (C'.card : ℝ)) =
          (32 : ℝ) * ((K1 : ℝ) * (H_raw : ℝ) * (C'.card : ℝ)) := by ring
      have h18 : (128 : ℝ) * (K1 : ℝ) * (H_raw : ℝ) * (C'.card : ℝ) =
          (128 : ℝ) * ((K1 : ℝ) * (H_raw : ℝ) * (C'.card : ℝ)) := by ring
      rw [h17, h18]
      exact h16
    exact h9.trans (h10.trans h13)
  have hH_final_ge : (H_final : ℝ) ≥ (H_raw : ℝ) * (m1 : ℝ) / 16 :=
    h_final_ge_algebraic m1 H_raw H_final rfl
  have hM_bound2 : (M : ℝ) ≤ (32 : ℝ) * (K1 : ℝ) * (m1 : ℝ) * (m2 : ℝ) := by
    have h1 : (M : ℝ) / (32 * (K1 : ℝ)) ≤ (m1 : ℝ) * (m2 : ℝ) := h_mass_lower2
    have h2 : 0 < (32 * (K1 : ℝ)) := by positivity
    have h3 : (M : ℝ) ≤ (32 * (K1 : ℝ)) * ((m1 : ℝ) * (m2 : ℝ)) := by
      have h_pos : 0 < (32 * (K1 : ℝ)) := h2
      have h4 : (M : ℝ) = (32 * (K1 : ℝ)) * ((M : ℝ) / (32 * (K1 : ℝ))) := by
        have h5 : (32 * (K1 : ℝ)) * ((M : ℝ) / (32 * (K1 : ℝ))) = (M : ℝ) := by
          rw [mul_comm]
          exact div_mul_cancel₀ _ h_pos.ne'
        exact h5.symm
      rw [h4]
      exact mul_le_mul_of_nonneg_left h1 h_pos.le
    have h4 : (32 * (K1 : ℝ)) * ((m1 : ℝ) * (m2 : ℝ)) = (32 : ℝ) * (K1 : ℝ) * (m1 : ℝ) * (m2 : ℝ) := by ring
    rw [h4] at h3
    exact h3
  have h_P_card_bound3 : (P.card : ℝ) ≤ 32 * (K1 : ℝ)^3 * (P'.card : ℝ) := by
    have h1 : (P.card : ℝ) ≤ (K1 : ℝ)^2 * (P1.card : ℝ) := hP1_card
    have hK1_sq_nonneg : 0 ≤ (K1 : ℝ)^2 := pow_nonneg (Nat.cast_nonneg K1) 2
    have h2 : (K1 : ℝ)^2 * (P1.card : ℝ) ≤ (K1 : ℝ)^2 * (32 * (K1 : ℝ) * (P'.card : ℝ)) :=
      mul_le_mul_of_nonneg_left h_P_card_lower1 hK1_sq_nonneg
    have h3 : (K1 : ℝ)^2 * (32 * (K1 : ℝ) * (P'.card : ℝ)) = 32 * (K1 : ℝ)^3 * (P'.card : ℝ) := by ring
    rw [h3] at h2
    exact h1.trans h2
  have h_avg_lower : (M : ℝ) * (P.card : ℝ) ≤ K_val * (H_final : ℝ) * (C'.card : ℝ) :=
    direct_avg_lower M m1 m2 H_raw H_final P.card P'.card C'.card K1 K_val
      hK1_ge1 hM_bound2 h_P_card_bound3 h_m2_bound2 hH_final_ge
      (by simp [K_val, K1_val, hK1_eq'] <;> norm_cast <;> ring)

  -- ======================================================================
  -- 15. K and C2 bounds
  -- ======================================================================
  have hK_val_eq : K_val = (2^21 : ℝ) * (K1 : ℝ)^6 := by
    simp [K_val, K1_val, hK1_eq'] <;> norm_cast <;> ring
  have hA_ge : A ≥ 1024 * Real.rpow 2 (s + 2) := by
    have hA2 : A2 ≤ A := le_max_right _ _
    have h_eq : A2 = 1024 * Real.rpow 2 (s + 2) + 1 := by rfl
    rw [h_eq] at hA2
    linarith
  have hC2_bound : C2_val ≤ A * Real.rpow K_val A * C₁ :=
    C2_bound_lemma s C₁ K1 K_val A hs.le hC1 hK1_ge1 hK_val_eq hA_ge C2_val hC2_val_eq

  -- ======================================================================
  -- 16. Final assembly
  -- ======================================================================
  refine ⟨P', T', C', K_val, C2_val, H_final, ?_⟩
  have hK_val_ge1 : 1 ≤ K_val := by
    rw [hK_val_eq]
    exact K_val_ge1_lemma K1 hK1_ge1
  exact ⟨hK_val_ge1, by
    have hK1_eq2 : K1 = Nat.log 2 coarseRange.card + 4 := by
      rw [hK1_eq'] <;> rfl
    rw [hK_val_eq, hK1_eq2] <;> rfl, hK_bound, hC2_ge1, hH_final_pos,
    show P' ⊆ P from fun x hx => hP1_sub (hP'_sub_P1 hx),
    h_P_card_bound,
    hT'_sub,
    h_T'_card_lower,
    h_biUnion,
    hC'_sub_coarseRange,
    h_frostman_C',
    hC2_bound,
    (by
      have hK1_eq2 : K1 = Nat.log 2 coarseRange.card + 4 := by
        rw [hK1_eq'] <;> rfl
      rw [hC2_val_eq, hK1_eq2] <;> rfl),
    h_inc_lower,
    h_avg_lower,
    h_avg_upper⟩

end Proofs

theorem quantitative_thick_tube_cover
    (s D B : ℝ)
    (hs : 0 < s) (hsD : s ≤ D) (hD : 1 ≤ D) (hB : 1 ≤ B) :
    ∃ A : ℝ, 1 ≤ A ∧ A ≤ qttcA_bound s D B ∧
      ∀ {α L : Type*} [PseudoMetricSpace L]
        [DecidableEq α] [DecidableEq L]
        {δ Δ C₁ : ℝ} {M : ℕ}
        (P : Finset α) (U : Finset L) (T : α → Finset L)
        (coarse : L → L) (coarseRange : Finset L),
        0 < δ → δ ≤ Δ → Δ ≤ (1 / 2 : ℝ) →
        1 ≤ C₁ → P.Nonempty → 0 < M →
        (∀ p ∈ P, T p ⊆ U) →
        (∀ p ∈ P, M / 2 < (T p).card ∧ (T p).card ≤ M) →
        (∀ p ∈ P, BallGrowth δ s C₁ (T p)) →
        (∀ ℓ ∈ U,
          coarse ℓ ∈ coarseRange ∧ dist ℓ (coarse ℓ) ≤ Δ) →
        SeparatedAt Δ (coarseRange : Set L) →
        (coarseRange.card : ℝ) ≤ B * Δ ^ (-D) →
        ∃ (P' : Finset α) (T' : α → Finset L)
          (C' : Finset L) (K C₂ : ℝ) (H : ℕ),
          1 ≤ K ∧
          K = (2^21 : ℝ) * ((Nat.log 2 coarseRange.card + 4 : ℕ) : ℝ)^6 ∧
          K ≤ A * Real.rpow (Real.log (2 / Δ)) A ∧
          1 ≤ C₂ ∧ 0 < H ∧
          P' ⊆ P ∧
          (P.card : ℝ) ≤ K * (P'.card : ℝ) ∧
          (∀ p ∈ P', T' p ⊆ T p) ∧
          (∀ p ∈ P', (M : ℝ) ≤ K * ((T' p).card : ℝ)) ∧
          C' = P'.biUnion (fun p => (T' p).image coarse) ∧
          C' ⊆ coarseRange ∧
          IsFiniteDeltaSSet Δ s C₂ C' ∧
          C₂ ≤ A * Real.rpow K A * C₁ ∧
          C₂ = 1024 * Real.rpow 2 (s + 2) * C₁ * ((Nat.log 2 coarseRange.card + 4 : ℕ) : ℝ)^2 ∧
          (∀ c ∈ C',
            H ≤ ∑ p ∈ P', assignedCount coarse T' p c) ∧
          (M : ℝ) * (P.card : ℝ) ≤
            K * (H : ℝ) * (C'.card : ℝ) ∧
          (H : ℝ) * (C'.card : ℝ) ≤
            K * (M : ℝ) * (P.card : ℝ) :=
  quantitative_thick_tube_cover_main s D B hs hsD hD hB
