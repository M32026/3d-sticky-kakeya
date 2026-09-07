module

public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.GeometricBounds
public import MyLeanRepo.InductionOnScales.Pigeonhole
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# K Polynomial Bound

Extracts the polylogarithmic K bound into a polynomial in n.

Given `config.tubes.card ≤ 12 * 16^n`, proves that the induction-step K
is bounded by `3145728 * (4*n+5)^7`.

## Main result

`prove_K_poly_bound`: single-call lemma for the K bound.
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace InductionOnScales

/-- If `0 < N < 2^k`, then `Nat.log 2 N ≤ k - 1`. -/
lemma nat_log_lt_pow {N k : ℕ} (hN_pos : 0 < N) (h : N < 2^k) :
    Nat.log 2 N ≤ k - 1 := by
  have hN_ne : N ≠ 0 := by omega
  by_cases hk : k = 0
  · have h' : N < 1 := by simpa [hk] using h
    omega
  · have h7 : k > 0 := by omega
    by_contra h8
    have h9 : k ≤ Nat.log 2 N := by omega
    have h10 : 2^k ≤ 2^(Nat.log 2 N) := by
      gcongr <;> norm_num
    have h11 : 2^(Nat.log 2 N) ≤ N := Nat.pow_log_le_self 2 hN_ne
    have h12 : 2^k ≤ N := by linarith
    linarith

/-- `numDyadicLevels N ≤ 4*n+5` when `N ≤ 12*16^n`. -/
lemma numDyadicLevels_le_4n5 {n N : ℕ} (hN_pos : 0 < N)
    (h : N ≤ 12 * 16^n) :
    (numDyadicLevels N : ℝ) ≤ 4 * (n : ℝ) + 5 := by
  have h1 : N < 2^(4*n+4) := by
    have h2 : 12 * 16^n < 16 * 16^n := by
      gcongr <;> norm_num
    have h4 : 16 * 16^n = 2^(4*n+4) := by
      have h5 : ∀ n : ℕ, 16 * 16^n = 2^(4*n+4) := by
        intro n
        induction n with
        | zero => norm_num
        | succ n ih =>
          simp [pow_succ] at * <;> ring_nf at * <;> omega
      exact h5 n
    have h3 : 12 * 16^n < 2^(4*n+4) := by
      calc 12 * 16^n
        < 16 * 16^n := h2
      _ = 2^(4*n+4) := h4
    have h5 : N ≤ 12 * 16^n := h
    omega
  have h6 : Nat.log 2 N ≤ 4*n+3 := nat_log_lt_pow hN_pos h1
  have h7 : numDyadicLevels N = Nat.log 2 N + 2 := by
    rfl
  rw [h7]
  exact_mod_cast (by omega)

/-- `numDyadicLevels N ≤ 6*n+5` when `N ≤ 12*4^n*16^n`. -/
lemma numDyadicLevels_le_6n5 {n N : ℕ} (hN_pos : 0 < N)
    (h : N ≤ 12 * 4^n * 16^n) :
    (numDyadicLevels N : ℝ) ≤ 6 * (n : ℝ) + 5 := by
  have h1 : N < 2^(6*n+4) := by
    have h2 : 12 * 4^n * 16^n < 16 * 4^n * 16^n := by
      gcongr <;> norm_num
    have h4 : 16 * 4^n * 16^n = 2^(6*n+4) := by
      have h5 : ∀ n : ℕ, 16 * 4^n * 16^n = 2^(6*n+4) := by
        intro n
        induction n with
        | zero => norm_num
        | succ n ih =>
          simp [pow_succ] at * <;> ring_nf at * <;> omega
      exact h5 n
    have h3 : 12 * 4^n * 16^n < 2^(6*n+4) := by
      calc 12 * 4^n * 16^n
        < 16 * 4^n * 16^n := h2
      _ = 2^(6*n+4) := h4
    have h5 : N ≤ 12 * 4^n * 16^n := h
    omega
  have h6 : Nat.log 2 N ≤ 6*n+3 := nat_log_lt_pow hN_pos h1
  have h7 : numDyadicLevels N = Nat.log 2 N + 2 := by rfl
  rw [h7]
  exact_mod_cast (by omega)

/-- Polynomial bound on the induction-step K.

Given `config.tubes.card ≤ 12 * 16^n`, the K factor is bounded by
`3145728 * (4*n+5)^7`. -/
lemma prove_K_poly_bound
    {n : ℕ} {s C₁ : ℝ} {M : ℕ} {config : NiceConfiguration n s C₁ M}
    (h_tubes_bounded : config.tubes.card ≤ 12 * 16^n)
    (K : ℝ) (max_size : ℕ)
    (hK_eq : K = 98304 * (numDyadicLevels max_size : ℝ) *
        (numDyadicLevels M : ℝ)^3 *
        (numDyadicLevels (config.points.card * M) : ℝ) *
        (numDyadicLevels config.tubes.card : ℝ)^2 *
        Real.rpow 16 s)
    (h_max_size_le : max_size ≤ config.tubes.card)
    (hM_le : M ≤ config.tubes.card)
    (hP_nonempty : config.points.Nonempty)
    (hM : 0 < M)
    (hs_one : s ≤ 1) (hs : 0 ≤ s) :
    K ≤ 3145728 * (4 * (n : ℝ) + 5)^7 := by
  have h_tubes_pos : 0 < config.tubes.card := by
    have h1 : 0 < M := hM
    have h2 : M ≤ config.tubes.card := hM_le
    omega

  have h_points_pos : 0 < config.points.card := hP_nonempty.card_pos

  have h_points_card_le : (config.points.card : ℝ) ≤ (4^n : ℝ) := by
    have h := point_count_bound config
    have hδ2 : 1 / (dyadicDelta n)^2 = (4^n : ℝ) := one_over_dyadicDelta_sq n
    rw [hδ2] at h
    exact h

  have h1 : max_size ≤ 12 * 16^n := by
    calc max_size
      ≤ config.tubes.card := h_max_size_le
    _ ≤ 12 * 16^n := h_tubes_bounded

  have h2 : M ≤ 12 * 16^n := by
    calc M
      ≤ config.tubes.card := hM_le
    _ ≤ 12 * 16^n := h_tubes_bounded

  have h3 : config.points.card * M ≤ 12 * 4^n * 16^n := by
    have h4 : (config.points.card : ℝ) ≤ (4^n : ℝ) := h_points_card_le
    have h5 : (M : ℝ) ≤ (12 * 16^n : ℝ) := by exact_mod_cast h2
    have h6 : ((config.points.card * M : ℕ) : ℝ) = (config.points.card : ℝ) * (M : ℝ) := by simp
    have h7 : ((config.points.card * M : ℕ) : ℝ) ≤ (12 * 4^n * 16^n : ℝ) := by
      rw [h6]
      have h8 : (config.points.card : ℝ) * (M : ℝ) ≤ (4^n : ℝ) * (12 * 16^n : ℝ) := by
        exact mul_le_mul h4 h5 (by positivity) (by positivity)
      have h9 : (4^n : ℝ) * (12 * 16^n : ℝ) = (12 * 4^n * 16^n : ℝ) := by ring
      rw [h9] at h8
      exact h8
    exact_mod_cast h7

  have h4 : config.tubes.card ≤ 12 * 16^n := h_tubes_bounded

  set L1 := (numDyadicLevels max_size : ℝ) with hL1
  set L2 := (numDyadicLevels M : ℝ) with hL2
  set L3 := (numDyadicLevels (config.points.card * M) : ℝ) with hL3
  set L4 := (numDyadicLevels config.tubes.card : ℝ) with hL4

  have hL1_le : L1 ≤ 4 * (n : ℝ) + 5 := by
    rw [hL1]
    by_cases h : max_size = 0
    · rw [h]
      simp [numDyadicLevels] <;> norm_num <;> linarith
    · exact numDyadicLevels_le_4n5 (Nat.pos_of_ne_zero h) h1

  have hL2_le : L2 ≤ 4 * (n : ℝ) + 5 := by
    rw [hL2]
    exact numDyadicLevels_le_4n5 hM h2

  have hL3_le : L3 ≤ 6 * (n : ℝ) + 5 := by
    rw [hL3]
    have h_pos : 0 < config.points.card * M := mul_pos h_points_pos hM
    exact numDyadicLevels_le_6n5 h_pos h3

  have hL4_le : L4 ≤ 4 * (n : ℝ) + 5 := by
    rw [hL4]
    exact numDyadicLevels_le_4n5 h_tubes_pos h4

  have h_rpow : Real.rpow 16 s ≤ 16 := by
    have h1 : 0 ≤ s := hs
    have h2 : s ≤ 1 := hs_one
    have h3 : Real.rpow 16 s ≤ Real.rpow 16 1 := Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
    have h4 : Real.rpow 16 1 = 16 := by
      simp
    rw [h4] at h3
    exact h3

  have h_nonneg1 : 0 ≤ 4 * (n : ℝ) + 5 := by positivity
  have h_nonneg2 : 0 ≤ 6 * (n : ℝ) + 5 := by positivity
  have h_nonneg3 : 0 ≤ L1 := by positivity
  have h_nonneg4 : 0 ≤ L2 := by positivity
  have h_nonneg5 : 0 ≤ L3 := by positivity
  have h_nonneg6 : 0 ≤ L4 := by positivity

  have h6n : 6 * (n : ℝ) + 5 ≤ 2 * (4 * (n : ℝ) + 5) := by
    linarith

  set X := 4 * (n : ℝ) + 5 with hX
  set Y := 6 * (n : ℝ) + 5 with hY
  have hX_pos : 0 ≤ X := by positivity
  have hY_pos : 0 ≤ Y := by positivity

  have h_main_ineq : 98304 * L1 * L2^3 * L3 * L4^2 * Real.rpow 16 s ≤
      98304 * X * X^3 * Y * X^2 * 16 := by
    have h1 : L1 ≤ X := hL1_le
    have h2 : L2 ≤ X := hL2_le
    have h3 : L3 ≤ Y := hL3_le
    have h4 : L4 ≤ X := hL4_le
    have h5 : Real.rpow 16 s ≤ 16 := h_rpow
    have h_pos1 : 0 ≤ L1 := by positivity
    have h_pos2 : 0 ≤ L2 := by positivity
    have h_pos3 : 0 ≤ L3 := by positivity
    have h_pos4 : 0 ≤ L4 := by positivity
    have h_pos5 : 0 ≤ Real.rpow 16 s := Real.rpow_nonneg (by norm_num) s
    have h_pos6 : 0 ≤ X := by positivity
    have h_pos7 : 0 ≤ Y := by positivity
    have h23 : L2^3 ≤ X^3 := by
      gcongr <;> linarith
    have h42 : L4^2 ≤ X^2 := by
      gcongr <;> linarith
    have h_goal : L1 * L2^3 * L3 * L4^2 * Real.rpow 16 s ≤ X * X^3 * Y * X^2 * 16 := by
      calc L1 * L2^3 * L3 * L4^2 * Real.rpow 16 s
        ≤ X * L2^3 * L3 * L4^2 * Real.rpow 16 s := by gcongr <;> linarith
      _ ≤ X * X^3 * L3 * L4^2 * Real.rpow 16 s := by gcongr <;> linarith
      _ ≤ X * X^3 * Y * L4^2 * Real.rpow 16 s := by gcongr <;> linarith
      _ ≤ X * X^3 * Y * X^2 * Real.rpow 16 s := by gcongr <;> linarith
      _ ≤ X * X^3 * Y * X^2 * 16 := by gcongr <;> linarith
    have h_e : 98304 * (L1 * L2^3 * L3 * L4^2 * Real.rpow 16 s) ≤ 98304 * (X * X^3 * Y * X^2 * 16) := by
      gcongr
      <;> linarith
    have h_f : 98304 * (L1 * L2^3 * L3 * L4^2 * Real.rpow 16 s) = 98304 * L1 * L2^3 * L3 * L4^2 * Real.rpow 16 s := by ring
    have h_g : 98304 * (X * X^3 * Y * X^2 * 16) = 98304 * X * X^3 * Y * X^2 * 16 := by ring
    rw [h_f, h_g] at h_e
    exact h_e

  rw [hK_eq]
  calc 98304 * L1 * L2^3 * L3 * L4^2 * Real.rpow 16 s
    ≤ 98304 * X * X^3 * Y * X^2 * 16 := h_main_ineq
  _ = 1572864 * X^6 * Y := by ring
  _ ≤ 1572864 * X^6 * (2 * X) := by
    have h : Y ≤ 2 * X := h6n
    have h_pos : 0 ≤ 1572864 * X^6 := by positivity
    nlinarith
  _ = 3145728 * X^7 := by ring
  _ = 3145728 * (4 * (n : ℝ) + 5)^7 := by
    simp [hX] <;> ring

/-- `numDyadicLevels N ≤ 4*n+7` when `N ≤ 36*16^n`. -/
lemma numDyadicLevels_le_4n7 {n N : ℕ} (hN_pos : 0 < N)
    (h : N ≤ 36 * 16^n) :
    (numDyadicLevels N : ℝ) ≤ 4 * (n : ℝ) + 7 := by
  have h1 : N < 2^(4*n+6) := by
    have h2 : 36 * 16^n < 64 * 16^n := by
      gcongr <;> norm_num
    have h4 : 64 * 16^n = 2^(4*n+6) := by
      have h5 : ∀ n : ℕ, 64 * 16^n = 2^(4*n+6) := by
        intro n
        induction n with
        | zero => norm_num
        | succ n ih =>
          simp [pow_succ] at * <;> ring_nf at * <;> omega
      exact h5 n
    have h3 : 36 * 16^n < 2^(4*n+6) := by
      calc 36 * 16^n
        < 64 * 16^n := h2
      _ = 2^(4*n+6) := h4
    have h5 : N ≤ 36 * 16^n := h
    omega
  have h6 : Nat.log 2 N ≤ 4*n+5 := nat_log_lt_pow hN_pos h1
  have h7 : numDyadicLevels N = Nat.log 2 N + 2 := by rfl
  rw [h7]
  exact_mod_cast (by omega)

/-- `numDyadicLevels N ≤ 6*n+7` when `N ≤ 36*4^n*16^n`. -/
lemma numDyadicLevels_le_6n7 {n N : ℕ} (hN_pos : 0 < N)
    (h : N ≤ 36 * 4^n * 16^n) :
    (numDyadicLevels N : ℝ) ≤ 6 * (n : ℝ) + 7 := by
  have h1 : N < 2^(6*n+6) := by
    have h2 : 36 * 4^n * 16^n < 64 * 4^n * 16^n := by
      gcongr <;> norm_num
    have h4 : 64 * 4^n * 16^n = 2^(6*n+6) := by
      have h5 : ∀ n : ℕ, 64 * 4^n * 16^n = 2^(6*n+6) := by
        intro n
        induction n with
        | zero => norm_num
        | succ n ih =>
          simp [pow_succ] at * <;> ring_nf at * <;> omega
      exact h5 n
    have h3 : 36 * 4^n * 16^n < 2^(6*n+6) := by
      calc 36 * 4^n * 16^n
        < 64 * 4^n * 16^n := h2
      _ = 2^(6*n+6) := h4
    have h5 : N ≤ 36 * 4^n * 16^n := h
    omega
  have h6 : Nat.log 2 N ≤ 6*n+5 := nat_log_lt_pow hN_pos h1
  have h7 : numDyadicLevels N = Nat.log 2 N + 2 := by rfl
  rw [h7]
  exact_mod_cast (by omega)

/-- Polynomial bound on the induction-step K for the 36*16^n tube bound.

Given `config.tubes.card ≤ 36 * 16^n`, the K factor is bounded by
`3145728 * (4*n+7)^7`. -/
lemma prove_K_poly_bound_36
    {n : ℕ} {s C₁ : ℝ} {M : ℕ} {config : NiceConfiguration n s C₁ M}
    (h_tubes_bounded : config.tubes.card ≤ 36 * 16^n)
    (K : ℝ) (max_size : ℕ)
    (hK_eq : K = 98304 * (numDyadicLevels max_size : ℝ) *
        (numDyadicLevels M : ℝ)^3 *
        (numDyadicLevels (config.points.card * M) : ℝ) *
        (numDyadicLevels config.tubes.card : ℝ)^2 *
        Real.rpow 16 s)
    (h_max_size_le : max_size ≤ config.tubes.card)
    (hM_le : M ≤ config.tubes.card)
    (hP_nonempty : config.points.Nonempty)
    (hM : 0 < M)
    (hs_one : s ≤ 1) (hs : 0 ≤ s) :
    K ≤ 3145728 * (4 * (n : ℝ) + 7)^7 := by
  have h_tubes_pos : 0 < config.tubes.card := by
    have h1 : 0 < M := hM
    have h2 : M ≤ config.tubes.card := hM_le
    omega
  have h_points_pos : 0 < config.points.card := hP_nonempty.card_pos
  have h_points_card_le : (config.points.card : ℝ) ≤ (4^n : ℝ) := by
    have h := point_count_bound config
    have hδ2 : 1 / (dyadicDelta n)^2 = (4^n : ℝ) := one_over_dyadicDelta_sq n
    rw [hδ2] at h
    exact h
  have h1 : max_size ≤ 36 * 16^n := by
    calc max_size
      ≤ config.tubes.card := h_max_size_le
    _ ≤ 36 * 16^n := h_tubes_bounded
  have h2 : M ≤ 36 * 16^n := by
    calc M
      ≤ config.tubes.card := hM_le
    _ ≤ 36 * 16^n := h_tubes_bounded
  have h3 : config.points.card * M ≤ 36 * 4^n * 16^n := by
    have h4 : (config.points.card : ℝ) ≤ (4^n : ℝ) := h_points_card_le
    have h5 : (M : ℝ) ≤ (36 * 16^n : ℝ) := by exact_mod_cast h2
    have h6 : ((config.points.card * M : ℕ) : ℝ) = (config.points.card : ℝ) * (M : ℝ) := by simp
    have h7 : ((config.points.card * M : ℕ) : ℝ) ≤ (36 * 4^n * 16^n : ℝ) := by
      rw [h6]
      have h8 : (config.points.card : ℝ) * (M : ℝ) ≤ (4^n : ℝ) * (36 * 16^n : ℝ) := by
        exact mul_le_mul h4 h5 (by positivity) (by positivity)
      have h9 : (4^n : ℝ) * (36 * 16^n : ℝ) = (36 * 4^n * 16^n : ℝ) := by ring
      rw [h9] at h8
      exact h8
    exact_mod_cast h7
  have h4 : config.tubes.card ≤ 36 * 16^n := h_tubes_bounded
  set L1 := (numDyadicLevels max_size : ℝ) with hL1
  set L2 := (numDyadicLevels M : ℝ) with hL2
  set L3 := (numDyadicLevels (config.points.card * M) : ℝ) with hL3
  set L4 := (numDyadicLevels config.tubes.card : ℝ) with hL4
  have hL1_le : L1 ≤ 4 * (n : ℝ) + 7 := by
    rw [hL1]
    by_cases h : max_size = 0
    · rw [h]; simp [numDyadicLevels] <;> norm_num <;> linarith
    · exact numDyadicLevels_le_4n7 (Nat.pos_of_ne_zero h) h1
  have hL2_le : L2 ≤ 4 * (n : ℝ) + 7 := by
    rw [hL2]
    exact numDyadicLevels_le_4n7 hM h2
  have hL3_le : L3 ≤ 6 * (n : ℝ) + 7 := by
    rw [hL3]
    have h_pos : 0 < config.points.card * M := mul_pos h_points_pos hM
    exact numDyadicLevels_le_6n7 h_pos h3
  have hL4_le : L4 ≤ 4 * (n : ℝ) + 7 := by
    rw [hL4]
    exact numDyadicLevels_le_4n7 h_tubes_pos h4
  have h_rpow : Real.rpow 16 s ≤ 16 := by
    have h1 : 0 ≤ s := hs
    have h2 : s ≤ 1 := hs_one
    have h3 : Real.rpow 16 s ≤ Real.rpow 16 1 := Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
    have h4 : Real.rpow 16 1 = 16 := by simp
    rw [h4] at h3
    exact h3
  have h_nonneg1 : 0 ≤ 4 * (n : ℝ) + 7 := by positivity
  have h_nonneg2 : 0 ≤ 6 * (n : ℝ) + 7 := by positivity
  set X := 4 * (n : ℝ) + 7 with hX
  set Y := 6 * (n : ℝ) + 7 with hY
  have hX_pos : 0 ≤ X := by positivity
  have hY_pos : 0 ≤ Y := by positivity
  have h6n : 6 * (n : ℝ) + 7 ≤ 2 * (4 * (n : ℝ) + 7) := by linarith
  have h_main_ineq : 98304 * L1 * L2^3 * L3 * L4^2 * Real.rpow 16 s ≤
      98304 * X * X^3 * Y * X^2 * 16 := by
    have h1 : L1 ≤ X := hL1_le
    have h2 : L2 ≤ X := hL2_le
    have h3 : L3 ≤ Y := hL3_le
    have h4 : L4 ≤ X := hL4_le
    have h5 : Real.rpow 16 s ≤ 16 := h_rpow
    have h_pos1 : 0 ≤ L1 := by positivity
    have h_pos2 : 0 ≤ L2 := by positivity
    have h_pos3 : 0 ≤ L3 := by positivity
    have h_pos4 : 0 ≤ L4 := by positivity
    have h_pos5 : 0 ≤ Real.rpow 16 s := Real.rpow_nonneg (by norm_num) s
    have h_pos6 : 0 ≤ X := by positivity
    have h_pos7 : 0 ≤ Y := by positivity
    have h23 : L2^3 ≤ X^3 := by gcongr <;> linarith
    have h42 : L4^2 ≤ X^2 := by gcongr <;> linarith
    have h_goal : L1 * L2^3 * L3 * L4^2 * Real.rpow 16 s ≤ X * X^3 * Y * X^2 * 16 := by
      calc L1 * L2^3 * L3 * L4^2 * Real.rpow 16 s
        ≤ X * L2^3 * L3 * L4^2 * Real.rpow 16 s := by gcongr <;> linarith
      _ ≤ X * X^3 * L3 * L4^2 * Real.rpow 16 s := by gcongr <;> linarith
      _ ≤ X * X^3 * Y * L4^2 * Real.rpow 16 s := by gcongr <;> linarith
      _ ≤ X * X^3 * Y * X^2 * Real.rpow 16 s := by gcongr <;> linarith
      _ ≤ X * X^3 * Y * X^2 * 16 := by gcongr <;> linarith
    have h_e : 98304 * (L1 * L2^3 * L3 * L4^2 * Real.rpow 16 s) ≤ 98304 * (X * X^3 * Y * X^2 * 16) := by
      gcongr <;> linarith
    have h_f : 98304 * (L1 * L2^3 * L3 * L4^2 * Real.rpow 16 s) = 98304 * L1 * L2^3 * L3 * L4^2 * Real.rpow 16 s := by ring
    have h_g : 98304 * (X * X^3 * Y * X^2 * 16) = 98304 * X * X^3 * Y * X^2 * 16 := by ring
    rw [h_f, h_g] at h_e
    exact h_e
  rw [hK_eq]
  calc 98304 * L1 * L2^3 * L3 * L4^2 * Real.rpow 16 s
    ≤ 98304 * X * X^3 * Y * X^2 * 16 := h_main_ineq
  _ = 1572864 * X^6 * Y := by ring
  _ ≤ 1572864 * X^6 * (2 * X) := by
    have h : Y ≤ 2 * X := h6n
    have h_pos : 0 ≤ 1572864 * X^6 := by positivity
    nlinarith
  _ = 3145728 * X^7 := by ring
  _ = 3145728 * (4 * (n : ℝ) + 7)^7 := by
    simp [hX] <;> ring

end InductionOnScales
