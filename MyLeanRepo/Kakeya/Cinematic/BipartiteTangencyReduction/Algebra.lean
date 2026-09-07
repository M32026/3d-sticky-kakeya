import MyLeanRepo.Kakeya.Cinematic.Geometry
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Algebraic absorption for the bipartite estimate
-/

namespace Kakeya.Cinematic

lemma normalized_count_le_rpow_log {N : ℝ} (hN : 2 ≤ N) :
    N ≤ 2 * Real.rpow N (3 / 2 : ℝ) * Real.log N := by
  have hN_pos : 0 < N := by linarith
  have hpow :
      Real.rpow N (3 / 2 : ℝ) =
        N * Real.rpow N (1 / 2 : ℝ) := by
    calc
      Real.rpow N (3 / 2 : ℝ) =
          Real.rpow N (1 + 1 / 2 : ℝ) := by norm_num
      _ = Real.rpow N 1 * Real.rpow N (1 / 2 : ℝ) :=
        Real.rpow_add hN_pos 1 (1 / 2)
      _ = N * Real.rpow N (1 / 2 : ℝ) := by simp
  have hsqrt : 1 ≤ Real.rpow N (1 / 2 : ℝ) := by
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have hlog2 : 1 / 2 < Real.log 2 := by
    have hexp : Real.exp 1 < (4 : ℝ) := by
      linarith [Real.exp_one_lt_three]
    have hlog4 : 1 < Real.log 4 := by
      have := Real.log_lt_log (Real.exp_pos 1) hexp
      simpa using this
    have hlog4_eq : Real.log 4 = 2 * Real.log 2 := by
      calc
        Real.log 4 = Real.log ((2 : ℝ) * 2) := by norm_num
        _ = Real.log 2 + Real.log 2 :=
          Real.log_mul (by norm_num) (by norm_num)
        _ = 2 * Real.log 2 := by ring
    linarith
  have hlog : 1 / 2 ≤ Real.log N := by
    have : Real.log 2 ≤ Real.log N :=
      Real.log_le_log (by norm_num) hN
    linarith
  rw [hpow]
  have hproduct :
      (1 / 2 : ℝ) ≤
        Real.rpow N (1 / 2 : ℝ) * Real.log N := by
    calc
      (1 / 2 : ℝ) = 1 * (1 / 2 : ℝ) := by ring
      _ ≤ Real.rpow N (1 / 2 : ℝ) * Real.log N := by
        exact mul_le_mul hsqrt hlog (by norm_num) (by positivity)
  calc
    N = 2 * N * (1 / 2 : ℝ) := by ring
    _ ≤ 2 * N *
        (Real.rpow N (1 / 2 : ℝ) * Real.log N) := by
      gcongr
    _ = 2 * (N * Real.rpow N (1 / 2 : ℝ)) *
        Real.log N := by ring

/--
Any bound of the form `C0 * A^p0` with `C0 > 0` and `p0 ≥ 0` is dominated by
`C * A^C` for some `C ≥ 1`, uniformly for all `A ≥ 1`.

This lets us absorb arbitrary polynomial-in-`A` losses into the single
`C * A^C` factor appearing in `BipartiteTangencyStatement`.
-/
lemma polynomial_absorption {C0 p0 : ℝ} (_hC0 : 0 < C0) (hp0 : 0 ≤ p0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ A : ℝ, A ≥ 1 →
      C0 * Real.rpow A p0 ≤ C * Real.rpow A C := by
  let C : ℝ := max C0 p0 + 1
  have hC1 : 1 ≤ C := by
    dsimp only [C]
    have h : 0 ≤ max C0 p0 := by
      apply le_max_of_le_right
      linarith
    linarith
  have hC0_le : C0 ≤ C := by
    dsimp only [C]
    have h : C0 ≤ max C0 p0 := le_max_left _ _
    linarith
  have hp0_le : p0 ≤ C := by
    dsimp only [C]
    have h : p0 ≤ max C0 p0 := le_max_right _ _
    linarith
  refine ⟨C, hC1, ?_⟩
  intro A hA
  have hApos : 0 < A := by linarith
  have hrp_nonneg : 0 ≤ Real.rpow A p0 := Real.rpow_nonneg (by linarith) _
  have h1 : Real.rpow A p0 ≤ Real.rpow A C :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hp0_le
  have hC_nonneg : 0 ≤ C := by linarith
  calc
    C0 * Real.rpow A p0 ≤ C * Real.rpow A p0 :=
      mul_le_mul_of_nonneg_right hC0_le hrp_nonneg
    _ ≤ C * Real.rpow A C :=
      mul_le_mul_of_nonneg_left h1 hC_nonneg

/--
The product of two polynomial bounds in `A` is again a polynomial bound in `A`
in the standard form `C * A^C`.
-/
lemma polynomial_product_absorption {C1 C2 p1 p2 : ℝ}
    (hC1 : 0 < C1) (hC2 : 0 < C2) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ A : ℝ, A ≥ 1 →
      (C1 * Real.rpow A p1) * (C2 * Real.rpow A p2) ≤
        C * Real.rpow A C := by
  have h_main : ∃ C : ℝ, 1 ≤ C ∧ ∀ A : ℝ, A ≥ 1 →
      (C1 * C2) * Real.rpow A (p1 + p2) ≤ C * Real.rpow A C :=
    polynomial_absorption (mul_pos hC1 hC2) (add_nonneg hp1 hp2)
  rcases h_main with ⟨C, hC1, hC⟩
  refine ⟨C, hC1, ?_⟩
  intro A hA
  have hApos : 0 < A := by linarith
  have h_add : Real.rpow A p1 * Real.rpow A p2 = Real.rpow A (p1 + p2) :=
    Eq.symm (Real.rpow_add hApos p1 p2)
  have h_eq : (C1 * Real.rpow A p1) * (C2 * Real.rpow A p2) =
      (C1 * C2) * Real.rpow A (p1 + p2) := by
    calc
      (C1 * Real.rpow A p1) * (C2 * Real.rpow A p2)
        = (C1 * C2) * (Real.rpow A p1 * Real.rpow A p2) := by ring
      _ = (C1 * C2) * Real.rpow A (p1 + p2) := by rw [h_add]
  rw [h_eq]
  exact hC A hA

/--
A polynomial bound raised to a non-negative power is again a polynomial bound
in the standard form `C * A^C`.
-/
lemma polynomial_rpow_absorption {C0 p0 q : ℝ}
    (hC0 : 0 < C0) (hp0 : 0 ≤ p0) (hq : 0 ≤ q) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ A : ℝ, A ≥ 1 →
      Real.rpow (C0 * Real.rpow A p0) q ≤ C * Real.rpow A C := by
  have hC0q_pos : 0 < Real.rpow C0 q := Real.rpow_pos_of_pos hC0 q
  have hp0q_nonneg : 0 ≤ p0 * q := mul_nonneg hp0 hq
  have h_main : ∃ C : ℝ, 1 ≤ C ∧ ∀ A : ℝ, A ≥ 1 →
      Real.rpow C0 q * Real.rpow A (p0 * q) ≤ C * Real.rpow A C :=
    polynomial_absorption hC0q_pos hp0q_nonneg
  rcases h_main with ⟨C, hC1, hC⟩
  refine ⟨C, hC1, ?_⟩
  intro A hA
  have hApos : 0 < A := by linarith
  have hrp_pos : 0 < Real.rpow A p0 := Real.rpow_pos_of_pos hApos p0
  have h_inner_pos : 0 < C0 * Real.rpow A p0 := mul_pos hC0 hrp_pos
  have h_mul_rpow : Real.rpow (C0 * Real.rpow A p0) q =
      Real.rpow C0 q * Real.rpow (Real.rpow A p0) q :=
    Real.mul_rpow hC0.le hrp_pos.le
  have h_rpow_mul : Real.rpow (Real.rpow A p0) q = Real.rpow A (p0 * q) :=
    Eq.symm (Real.rpow_mul hApos.le p0 q)
  have h_eq : Real.rpow (C0 * Real.rpow A p0) q =
      Real.rpow C0 q * Real.rpow A (p0 * q) := by
    rw [h_mul_rpow, h_rpow_mul]
  rw [h_eq]
  exact hC A hA

end Kakeya.Cinematic
