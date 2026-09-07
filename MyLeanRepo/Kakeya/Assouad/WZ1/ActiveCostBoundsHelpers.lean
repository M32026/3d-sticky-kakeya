import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26RepairedStatements
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic

/-!
# Active cost bounds for WZ1 correction segments

For sufficiently small `delta`, the active first, second, and value costs are
all bounded by `delta^(-rawLoss)` where `rawLoss = 1/levelCount + 2*hierarchyLoss`.

## Proof strategy

1. For each level, bound each cost by `C * delta^(-(1/N + hierarchyLoss))`.
2. Since at most one segment per level is active (disjoint supports), the total
   active cost is at most `N * C * delta^(-(1/N + hierarchyLoss))`.
3. Choose `delta₀` so that `N * C ≤ delta^(-hierarchyLoss)`.
4. Then `N * C * delta^(-(1/N + hierarchyLoss)) ≤ delta^(-(1/N + 2*hierarchyLoss))`.
-/

namespace Kakeya.Assouad

open Real WZ1VerticalTrapezoid

/-- Slope difference bound from numerical nesting on a finite interval. -/
lemma slope_diff_bound
    (child parent : WZ1VerticalTrapezoid)
    (hnest : child.IsNumericallyNestedIn parent) :
    |child.slope - parent.slope| ≤
      2 * (child.height + parent.height) / child.length := by
  have h_left_in : child.left ∈ child.core := by
    simp only [WZ1VerticalTrapezoid.core, Set.mem_Icc]
    exact ⟨le_refl child.left, le_of_lt child.left_lt_right⟩
  have h_right_in : child.right ∈ child.core := by
    simp only [WZ1VerticalTrapezoid.core, Set.mem_Icc]
    exact ⟨le_of_lt child.left_lt_right, le_refl child.right⟩
  have h1 : |child.affine child.right - parent.affine child.right| ≤ child.height + parent.height :=
    hnest.2 child.right h_right_in
  have h2 : |child.affine child.left - parent.affine child.left| ≤ child.height + parent.height :=
    hnest.2 child.left h_left_in
  have h_len_pos : 0 < child.length := by
    simp [WZ1VerticalTrapezoid.length, child.left_lt_right] <;> linarith
  set f := fun x : ℝ => child.affine x - parent.affine x with hf_def
  have hf_affine : ∀ x, f x = (child.slope - parent.slope) * x + (child.intercept - parent.intercept) := by
    intro x; simp [hf_def, WZ1VerticalTrapezoid.affine] <;> ring
  have h3 : f child.right - f child.left = (child.slope - parent.slope) * child.length := by
    rw [hf_affine child.right, hf_affine child.left]
    have h_len : child.length = child.right - child.left := by
      simp [WZ1VerticalTrapezoid.length] <;> linarith
    rw [h_len] <;> ring
  have h4 : |child.slope - parent.slope| = |f child.right - f child.left| / child.length := by
    rw [h3]
    have h5 : |(child.slope - parent.slope) * child.length| = |child.slope - parent.slope| * child.length := by
      rw [abs_mul, abs_of_pos h_len_pos]
    rw [h5]
    <;> field_simp [h_len_pos.ne'] <;> ring
  rw [h4]
  have h6 : |f child.right - f child.left| ≤ |f child.right| + |f child.left| := by
    exact abs_sub _ _
  have h7 : |f child.right| ≤ child.height + parent.height := h1
  have h8 : |f child.left| ≤ child.height + parent.height := h2
  have h9 : |f child.right - f child.left| / child.length ≤
      (|f child.right| + |f child.left|) / child.length := by gcongr
  have h10 : (|f child.right| + |f child.left|) / child.length ≤
      2 * (child.height + parent.height) / child.length := by
    have h11 : |f child.right| + |f child.left| ≤ 2 * (child.height + parent.height) := by linarith
    gcongr
  exact le_trans h9 h10

/-- For `0 < δ ≤ 1`, if `y ≤ x` then `δ^x ≤ δ^y`. -/
lemma rpow_decreasing {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    {x y : ℝ} (h : y ≤ x) : Real.rpow delta x ≤ Real.rpow delta y := by
  apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one
  exact h

/-- For `0 < δ ≤ 1` and `a ≤ b`, `δ^(-a) ≤ δ^(-b)`. -/
lemma rpow_neg_mono {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    {a b : ℝ} (h : a ≤ b) : Real.rpow delta (-a) ≤ Real.rpow delta (-b) := by
  have h' : -b ≤ -a := by linarith
  exact rpow_decreasing hdelta hdelta_one h'

/-- For `0 < δ ≤ 1` and `a ≥ 0`, `1 ≤ δ^(-a)`. -/
lemma one_le_rpow_neg {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    {a : ℝ} (ha : 0 ≤ a) : (1 : ℝ) ≤ Real.rpow delta (-a) := by
  have h : Real.rpow delta (-a) ≥ 1 := by
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta_one
    linarith
  exact h

/-- Exponent inequality: `-(1/N+h) ≤ (k-1-2h(k+1))/(2N)` for `1 ≤ k < N`. -/
lemma exp_ineq_b {N : ℕ} (hN : 0 < N) {h : ℝ} (hh : 0 ≤ h) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < N) :
    -(1 / (N : ℝ) + h) ≤ ((k : ℝ) - 1 - 2 * h * (k + 1 : ℝ)) / (2 * (N : ℝ)) := by
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have h7 : -2 - 2 * (N : ℝ) * h ≤ (k : ℝ) - 1 - 2 * h * (k + 1 : ℝ) := by
    have h_k1_le_N : (k + 1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show k + 1 ≤ N from by omega)
    nlinarith
  have h8 : -(1 / (N : ℝ) + h) = (-2 - 2 * (N : ℝ) * h) / (2 * (N : ℝ)) := by
    field_simp [hN_pos.ne'] <;> ring
  rw [h8]
  exact div_le_div_of_nonneg_right h7 (by positivity)

/-- Exponent inequality: `-(1/N+h) ≤ -(1+h(k+1))/N` for `k < N`. -/
lemma exp_ineq_d {N : ℕ} (hN : 0 < N) {h : ℝ} (hh : 0 ≤ h) {k : ℕ} (hk2 : k < N) :
    -(1 / (N : ℝ) + h) ≤ -((1 + (k + 1 : ℝ) * h) / (N : ℝ)) := by
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have h_k1_le_N : (k + 1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk2
  have h1 : (k + 1 : ℝ) * h ≤ (N : ℝ) * h := by nlinarith
  have h2 : 1 + (k + 1 : ℝ) * h ≤ 1 + (N : ℝ) * h := by linarith
  have h3 : (1 + (k + 1 : ℝ) * h) / (N : ℝ) ≤ (1 + (N : ℝ) * h) / (N : ℝ) := by gcongr
  have h4 : (1 + (N : ℝ) * h) / (N : ℝ) = 1 / (N : ℝ) + h := by
    field_simp [hN_pos.ne'] <;> ring
  rw [h4] at h3
  linarith

/-- For `C ≥ 0`, `ε > 0`, exists `δ₀ ∈ (0,1]` with `C ≤ δ^(-ε)` for `0 < δ ≤ δ₀`. -/
lemma exists_delta₀_rpow_neg (C : ℝ) (hC : 0 ≤ C) (eps : ℝ) (heps : 0 < eps) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ → C ≤ Real.rpow delta (-eps) := by
  by_cases h : C ≤ 1
  · refine ⟨1, by norm_num, by norm_num, fun delta hdelta _ => ?_⟩
    have h1 : 1 ≤ Real.rpow delta (-eps) := by
      apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta (by linarith) (by linarith)
    linarith
  · have hC_pos : 0 < C := by linarith
    have h_inv_pos : 0 < 1 / C := by positivity
    have h_inv_lt_one : 1 / C < 1 := by
      apply (div_lt_one hC_pos).mpr; linarith
    have h_eps_pos' : 0 < 1 / eps := by positivity
    let delta₀ := Real.rpow (1 / C) (1 / eps)
    have hdelta₀_pos : 0 < delta₀ := Real.rpow_pos_of_pos h_inv_pos _
    have hdelta₀_one : delta₀ < 1 := Real.rpow_lt_one (by positivity) h_inv_lt_one h_eps_pos'
    refine ⟨delta₀, hdelta₀_pos, hdelta₀_one.le, fun delta hdelta hle => ?_⟩
    have h9 : Real.rpow delta eps ≤ Real.rpow delta₀ eps :=
      Real.rpow_le_rpow (by linarith) hle (by linarith)
    have h10 : Real.rpow delta₀ eps = 1 / C := by
      have h11 : Real.rpow (Real.rpow (1 / C) (1 / eps)) eps =
          Real.rpow (1 / C) ((1 / eps) * eps) := by
        have h_pos : 0 ≤ (1 / C) := by positivity
        exact (Real.rpow_mul h_pos (1 / eps) eps).symm
      have h12 : (1 / eps : ℝ) * eps = 1 := by field_simp [heps.ne'] <;> ring
      have h13 : Real.rpow (1 / C) ((1 / eps) * eps) = 1 / C := by
        rw [h12]; simp
      have h14 : Real.rpow delta₀ eps = Real.rpow (1 / C) ((1 / eps) * eps) := by
        simpa [delta₀] using h11
      rw [h14, h13]
    rw [h10] at h9
    have h12' : C * Real.rpow delta eps ≤ 1 := by
      calc
        C * Real.rpow delta eps ≤ C * (1 / C) := by gcongr
        _ = 1 := by field_simp [hC_pos.ne'] <;> ring
    have h14 : 0 < Real.rpow delta eps := Real.rpow_pos_of_pos hdelta eps
    have h15 : C ≤ (Real.rpow delta eps)⁻¹ := by
      calc
        C = C * (Real.rpow delta eps) / (Real.rpow delta eps) := by
          field_simp [h14.ne'] <;> ring
        _ ≤ 1 / (Real.rpow delta eps) := by gcongr
        _ = (Real.rpow delta eps)⁻¹ := by ring
    have h13' : Real.rpow delta (-eps) = (Real.rpow delta eps)⁻¹ := by
      have h_def1 : Real.rpow delta (-eps) = Real.exp (Real.log delta * (-eps)) :=
        Real.rpow_def_of_pos hdelta (-eps)
      have h_def2 : Real.rpow delta eps = Real.exp (Real.log delta * eps) :=
        Real.rpow_def_of_pos hdelta eps
      rw [h_def1, h_def2]
      have h : Real.log delta * (-eps) = -(Real.log delta * eps) := by ring
      rw [h, Real.exp_neg] <;> ring
    rw [h13']
    exact h15

/-- Helper: `sqrt(delta^a) = delta^(a/2)` for `delta > 0`. -/
lemma sqrt_rpow {delta a : ℝ} (hdelta : 0 < delta) :
    Real.sqrt (Real.rpow delta a) = Real.rpow delta (a / 2) := by
  have h1 : Real.sqrt (Real.rpow delta a) = (Real.rpow delta a) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
  rw [h1]
  have h2 : (Real.rpow delta a) ^ (1 / 2 : ℝ) = Real.rpow delta (a * (1 / 2 : ℝ)) := by
    exact (Real.rpow_mul (by linarith) a (1 / 2 : ℝ)).symm
  rw [h2]
  have h3 : a * (1 / 2 : ℝ) = a / 2 := by ring
  rw [h3]

end Kakeya.Assouad
