import MyLeanRepo.Kakeya.Cinematic.Section5.LocalAssembly.LogAbsorption

/-!
# Absorb a polynomially bounded dyadic logarithm

If a finite cardinality is at most `delta^(-C)`, then its dyadic logarithmic
loss is absorbed by any prescribed negative power of `delta` at sufficiently
small scale.
-/

namespace Kakeya.Cinematic

theorem dyadic_log_loss_absorption
    (C exponent : ℝ)
    (hC : 0 ≤ C)
    (hexponent : 0 < exponent) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 / 2 ∧
      ∀ {delta : ℝ} {N : ℕ},
        0 < delta →
        delta ≤ delta₀ →
        (N : ℝ) ≤ Real.rpow delta (-C) →
        (4 * (Nat.log2 N + 1) : ℕ) ≤
          Real.rpow delta (-exponent) := by
  let A : ℝ := 4 * (C + 2)
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  rcases localAssembly_logb_absorption_general
      A 1 exponent hA (by norm_num) hexponent with
    ⟨rawDelta, hraw, hraw_one, hmain⟩
  let delta₀ := min rawDelta (1 / 2)
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀_half : delta₀ ≤ 1 / 2 := by
    dsimp only [delta₀]
    exact min_le_right _ _
  have hdelta₀_raw : delta₀ ≤ rawDelta := by
    dsimp only [delta₀]
    exact min_le_left _ _
  refine ⟨delta₀, hdelta₀, hdelta₀_half, ?_⟩
  intro delta N hdelta hdelta_bound hN
  have hdelta_raw : delta ≤ rawDelta :=
    hdelta_bound.trans hdelta₀_raw
  have hdelta_one : delta ≤ 1 :=
    hdelta_bound.trans hdelta₀_half |>.trans (by norm_num)
  let x : ℝ := 1 / delta
  have hx_pos : 0 < x := by
    dsimp only [x]
    positivity
  have hx_two : 2 ≤ x := by
    dsimp only [x]
    apply (le_div_iff₀ hdelta).2
    linarith [hdelta_bound.trans hdelta₀_half]
  have hx_one : 1 ≤ x := by linarith
  have hpow_eq :
      Real.rpow delta (-C) = Real.rpow x C := by
    calc
      Real.rpow delta (-C) =
          (Real.rpow delta C)⁻¹ :=
        Real.rpow_neg hdelta.le C
      _ = Real.rpow delta⁻¹ C :=
        (Real.inv_rpow hdelta.le C).symm
      _ = Real.rpow x C := by
        congr 1
        simp [x]
  have hxpow_one : 1 ≤ Real.rpow x C :=
    Real.one_le_rpow hx_one hC
  have hN_plus_pos : 0 < ((N + 1 : ℕ) : ℝ) := by
    positivity
  have hN_plus :
      ((N + 1 : ℕ) : ℝ) ≤
        2 * Real.rpow x C := by
    have hN' : (N : ℝ) ≤ Real.rpow x C := by
      rw [← hpow_eq]
      exact hN
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hlog_product :
      Real.logb 2 (2 * Real.rpow x C) =
        1 + C * Real.logb 2 x := by
    have hln2 : Real.log 2 ≠ 0 := by
      exact ne_of_gt (Real.log_pos (by norm_num))
    have hlogMul :
        Real.log (2 * Real.rpow x C) =
          Real.log 2 + C * Real.log x := by
      have hmul :=
        Real.log_mul (x := (2 : ℝ)) (y := Real.rpow x C)
          (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hx_pos C))
      exact hmul.trans <|
        congrArg (fun z : ℝ => Real.log 2 + z)
          (Real.log_rpow hx_pos C)
    rw [Real.logb, hlogMul]
    dsimp only [Real.logb]
    field_simp [hln2]
  have hlevels :
      ((Nat.log2 N + 1 : ℕ) : ℝ) ≤
        (C + 2) * (Real.logb 2 x + 1) := by
    have hlog2 :
        (Nat.log2 N : ℝ) ≤
          Real.logb 2 ((N + 1 : ℕ) : ℝ) := by
      have hlogNat :
          Nat.log2 N ≤ Nat.log2 (N + 1) := by
        rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
        exact Nat.log_mono_right (Nat.le_succ N)
      calc
        (Nat.log2 N : ℝ) ≤ (Nat.log2 (N + 1) : ℝ) := by
          exact_mod_cast hlogNat
        _ ≤ Real.logb 2 ((N + 1 : ℕ) : ℝ) :=
          Real.log2_le_logb (N + 1)
    have hlogmono :
        Real.logb 2 ((N + 1 : ℕ) : ℝ) ≤
          Real.logb 2 (2 * Real.rpow x C) := by
      exact
        (Real.logb_le_logb (by norm_num)
          hN_plus_pos (by positivity)).2 hN_plus
    have hlogx_nonneg : 0 ≤ Real.logb 2 x := by
      rw [Real.logb]
      exact div_nonneg (Real.log_nonneg hx_one)
        (Real.log_pos (by norm_num)).le
    calc
      ((Nat.log2 N + 1 : ℕ) : ℝ) =
          (Nat.log2 N : ℝ) + 1 := by norm_num
      _ ≤
          Real.logb 2 ((N + 1 : ℕ) : ℝ) + 1 := by
        gcongr
      _ ≤
          Real.logb 2 (2 * Real.rpow x C) + 1 := by
        gcongr
      _ = C * Real.logb 2 x + 2 := by
        rw [hlog_product]
        ring
      _ ≤ (C + 2) * (Real.logb 2 x + 1) := by
        nlinarith
  have habsorb :=
    hmain delta hdelta hdelta_raw
  have hcast :
      ((4 * (Nat.log2 N + 1) : ℕ) : ℝ) ≤
        Real.rpow delta (-exponent) := by
    calc
      ((4 * (Nat.log2 N + 1) : ℕ) : ℝ) =
          4 * (((Nat.log2 N + 1 : ℕ) : ℝ)) := by norm_num
      _ ≤
          A * (Real.logb 2 (1 / delta) + 1) := by
        have hx_eq : x = 1 / delta := rfl
        rw [← hx_eq]
        calc
          4 * (((Nat.log2 N + 1 : ℕ) : ℝ)) ≤
              4 * ((C + 2) * (Real.logb 2 x + 1)) := by
            exact mul_le_mul_of_nonneg_left hlevels (by norm_num)
          _ = A * (Real.logb 2 x + 1) := by
            dsimp only [A]
            ring
      _ ≤ Real.rpow delta (-exponent) := habsorb
  exact hcast

end Kakeya.Cinematic
