import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Order

open scoped MatrixOrder Pointwise
open MeasureTheory

namespace JohnEllipsoid

variable {n : ℕ}

lemma det_rank_one_update (hn : 0 < n) (w : Fin n → ℝ) (t : ℝ) (ht : t ≠ 1) :
    Matrix.det ((1 - t) • (1 : Matrix (Fin n) (Fin n) ℝ) + t • Matrix.vecMulVec w w)
    = (1 - t)^(n - 1) * (1 + t * ((∑ i, w i ^ 2) - 1)) := by
  let A : Matrix (Fin n) (Fin n) ℝ := (1 - t) • 1
  let U : Matrix (Fin n) (Fin 1) ℝ := fun i _ => t * w i
  let V : Matrix (Fin 1) (Fin n) ℝ := fun _ j => w j
  have h1t : (1 - t) ≠ 0 := by intro h; exact ht (by linarith)
  have hUV : U * V = t • Matrix.vecMulVec w w := by
    ext i j; simp [U, V, Matrix.mul_apply, Matrix.vecMulVec, Fin.sum_univ_one] <;> ring
  have hA : IsUnit A.det := by
    have h : A.det = (1 - t)^n := by simp [A, Matrix.det_smul] <;> ring
    rw [h]; exact IsUnit.mk0 _ (pow_ne_zero n h1t)
  have h_main : (A + U * V).det = A.det * (1 + V * A⁻¹ * U).det :=
    Matrix.det_add_mul U V hA
  have hAinv : A⁻¹ = (1 - t)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    have h : A * ((1 - t)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) = 1 := by
      simp [A, Matrix.smul_mul, Matrix.mul_smul, h1t] <;> field_simp [h1t] <;> rfl
    exact Matrix.inv_eq_right_inv h
  have hVAinvU : (V * A⁻¹ * U) 0 0 = t / (1 - t) * (∑ i, w i ^ 2) := by
    have h3 : ∀ (k : Fin n), (V * A⁻¹) 0 k = (1 - t)⁻¹ * w k := by
      intro k; simp [hAinv, Matrix.mul_apply, V, U, Matrix.one_apply, Fin.sum_univ_one] <;> ring
    calc
      (V * A⁻¹ * U) 0 0
        = ∑ k : Fin n, (V * A⁻¹) 0 k * U k 0 := by simp [Matrix.mul_apply, Fin.sum_univ_one]
      _ = ∑ k : Fin n, ((1 - t)⁻¹ * w k) * (t * w k) := by
          apply Finset.sum_congr rfl; intro k _; rw [h3 k] <;> rfl
      _ = t / (1 - t) * (∑ i, w i ^ 2) := by
          have h5 : ∀ k : Fin n, ((1 - t)⁻¹ * w k) * (t * w k) = t / (1 - t) * (w k ^ 2) := by
            intro k; field_simp [h1t] <;> ring
          rw [Finset.sum_congr rfl (fun k _ => h5 k), Finset.mul_sum] <;> rfl
  have hdet1 : (1 + V * A⁻¹ * U).det = 1 + t / (1 - t) * (∑ i, w i ^ 2) := by
    rw [Matrix.det_unique]; simpa using hVAinvU
  have hAdet : A.det = (1 - t)^n := by simp [A, Matrix.det_smul] <;> ring
  set S : ℝ := ∑ i, w i ^ 2 with hS
  have hpow : (1 - t)^n = (1 - t)^(n - 1) * (1 - t) := by
    cases n with | zero => contradiction | succ n' => simp [pow_succ] <;> ring
  have h_alg : (1 - t)^n * (1 + t / (1 - t) * S) = (1 - t)^(n - 1) * (1 + t * (S - 1)) := by
    rw [hpow]
    have h2 : (1 - t) * (1 + t / (1 - t) * S) = (1 - t) + t * S := by field_simp [h1t] <;> ring
    have h3 : (1 - t)^(n - 1) * (1 - t) * (1 + t / (1 - t) * S)
        = (1 - t)^(n - 1) * ((1 - t) + t * S) := by
      calc _ = (1 - t)^(n - 1) * ((1 - t) * (1 + t / (1 - t) * S)) := by ring
           _ = (1 - t)^(n - 1) * ((1 - t) + t * S) := by rw [h2]
    rw [h3] <;> ring
  have h_goal : (A + U * V).det = (1 - t)^(n - 1) * (1 + t * (S - 1)) := by
    rw [h_main, hAdet, hdet1]; exact h_alg
  have h_eq : (A + U * V) = (1 - t) • (1 : Matrix (Fin n) (Fin n) ℝ) + t • Matrix.vecMulVec w w := by
    simp [A, hUV] <;> rfl
  rw [←h_eq]; exact h_goal

lemma exists_t_det_gt_one (hn : 0 < n) {S : ℝ} (hS : (n : ℝ) < S) :
    ∃ (t : ℝ), 0 < t ∧ t < 1 ∧ (1 - t)^(n - 1) * (1 + t * (S - 1)) > 1 := by
  by_cases hn1 : n = 1
  · subst hn1
    have hS1 : 1 < S := by simpa using hS
    refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    norm_num at *; linarith
  · have hn2 : 2 ≤ n := by omega
    have hn2' : (n : ℝ) ≥ 2 := by exact_mod_cast hn2
    have hS1 : 1 < S := by linarith
    have hSn : 0 < S - n := by linarith
    have hS1' : 0 < S - 1 := by linarith
    have hnm1_pos : 0 < (n : ℝ) - 1 := by
      have h : (n : ℝ) ≥ 2 := hn2'
      linarith
    have hnm1' : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      cases n with
      | zero => contradiction
      | succ n' =>
        simp [Nat.cast_add] <;> norm_num
    set t0 : ℝ := (S - n) / (2 * ((n : ℝ) - 1) * (S - 1)) with ht0
    have ht0_pos : 0 < t0 := by positivity
    set t : ℝ := min t0 (1 / 2) with ht
    have ht_pos : 0 < t := by positivity
    have ht_lt_one : t < 1 := by
      have h : t ≤ 1 / 2 := min_le_right _ _
      linarith
    have h_t_le_t0 : t ≤ t0 := min_le_left _ _
    have h_denom_pos : 0 < ((n : ℝ) - 1) * (S - 1) := by positivity
    have h_main_ineq : t * (((n : ℝ) - 1) * (S - 1)) < S - n := by
      calc
        t * (((n : ℝ) - 1) * (S - 1))
          ≤ t0 * (((n : ℝ) - 1) * (S - 1)) := by gcongr
        _ = (S - n) / 2 := by
          rw [ht0]; field_simp [h_denom_pos.ne'] <;> ring
        _ < S - n := by linarith
    have h_bernoulli : (1 - t)^(n - 1) ≥ 1 - ((n : ℝ) - 1) * t := by
      have h'' : -1 ≤ (1 - t : ℝ) := by linarith
      have h3 := one_add_mul_sub_le_pow h'' (n - 1)
      rw [hnm1'] at *
      <;> linarith
    have h4 : (1 - t)^(n - 1) * (1 + t * (S - 1)) > 1 := by
      have h5 : (1 - t)^(n - 1) * (1 + t * (S - 1)) ≥
          (1 - ((n : ℝ) - 1) * t) * (1 + t * (S - 1)) := by
        gcongr <;> linarith
      have h6 : (1 - ((n : ℝ) - 1) * t) * (1 + t * (S - 1)) > 1 := by
        have h7 : (1 - ((n : ℝ) - 1) * t) * (1 + t * (S - 1)) =
            1 + t * (S - n) - ((n : ℝ) - 1) * t^2 * (S - 1) := by ring
        rw [h7]
        have h8 : t * (S - n) - ((n : ℝ) - 1) * t^2 * (S - 1) > 0 := by
          have h9 : t * (S - n) > ((n : ℝ) - 1) * t^2 * (S - 1) := by
            have h10 : 0 < t := ht_pos
            have h11 : t * (((n : ℝ) - 1) * (S - 1)) < S - n := h_main_ineq
            have h12 : ((n : ℝ) - 1) * t^2 * (S - 1) = t * (t * (((n : ℝ) - 1) * (S - 1))) := by ring
            rw [h12]
            exact mul_lt_mul_of_pos_left h11 h10
          linarith
        linarith
      linarith
    exact ⟨t, ht_pos, ht_lt_one, h4⟩

end JohnEllipsoid
