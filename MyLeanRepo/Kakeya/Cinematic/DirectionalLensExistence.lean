import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.DirectionalLensExistenceInputs
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.LensExistenceArithmetic

/-!
# Directional graph-lens existence

PYZ Lemma 37: construct a graph lens after shifting one of two well-separated
functions upward or downward, with both endpoints localized.

This module contains the comparator-validated proof integrated from MR #737.
The compatibility target imports this closed module.
-/

namespace Kakeya.Cinematic

open Set Real

-- ============================================================================
-- Internal helper lemmas
-- ============================================================================

noncomputable section

/-! ### Lemma 1: Derivative bound on enlarged interval -/

/-- Lipschitz: if |f'| ≤ C on [a,b], then |f y - f x| ≤ C * |y - x|. -/
private lemma lipschitz_from_deriv_bound
    {f f' : ℝ → ℝ} {a b C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (f_cont : ContinuousOn f (Icc a b))
    (f_deriv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (f'_bound : ∀ x ∈ Icc a b, |f' x| ≤ C) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f y - f x| ≤ C * |y - x| := by
  intro x hx y hy
  by_cases h_eq : x = y
  · rw [h_eq]; simp
  · by_cases h_lt : x < y
    · -- x < y
      have hcont : ContinuousOn f (Icc x y) := f_cont.mono (Icc_subset_Icc hx.1 hy.2)
      have hdiff : DifferentiableOn ℝ f (Ioo x y) := by
        intro z hz
        have hz1 : a < z := by linarith [hx.1, hz.1]
        have hz2 : z < b := by linarith [hz.2, hy.2]
        exact (f_deriv z ⟨hz1, hz2⟩).differentiableAt.differentiableWithinAt
      obtain ⟨ξ, hξ, hξ_slope⟩ := exists_deriv_eq_slope f h_lt hcont hdiff
      have hξ_mem : ξ ∈ Icc a b := ⟨by linarith [hx.1, hξ.1], by linarith [hξ.2, hy.2]⟩
      have hderiv : deriv f ξ = f' ξ := (f_deriv ξ ⟨by linarith [hx.1, hξ.1], by linarith [hξ.2, hy.2]⟩).deriv
      have hlen : 0 < y - x := by linarith
      have heq : f y - f x = f' ξ * (y - x) := by
        rw [←hderiv, hξ_slope]; field_simp [hlen.ne'] <;> ring
      have h_abs : |f y - f x| = |f' ξ| * (y - x) := by
        rw [heq, abs_mul, abs_of_pos hlen]
      have h_goal : |f' ξ| * (y - x) ≤ C * |y - x| := by
        have h9 : |y - x| = y - x := by rw [abs_of_pos hlen]
        rw [h9]
        exact mul_le_mul_of_nonneg_right (f'_bound ξ hξ_mem) hlen.le
      rw [h_abs]; exact h_goal
    · -- y < x
      have h_gt : y < x := by by_contra h; exact h_eq (by linarith)
      have hcont : ContinuousOn f (Icc y x) := f_cont.mono (Icc_subset_Icc hy.1 hx.2)
      have hdiff : DifferentiableOn ℝ f (Ioo y x) := by
        intro z hz
        have hz1 : a < z := by linarith [hy.1, hz.1]
        have hz2 : z < b := by linarith [hz.2, hx.2]
        exact (f_deriv z ⟨hz1, hz2⟩).differentiableAt.differentiableWithinAt
      obtain ⟨ξ, hξ, hξ_slope⟩ := exists_deriv_eq_slope f h_gt hcont hdiff
      have hξ_mem : ξ ∈ Icc a b := ⟨by linarith [hy.1, hξ.1], by linarith [hξ.2, hx.2]⟩
      have hderiv : deriv f ξ = f' ξ := (f_deriv ξ ⟨by linarith [hy.1, hξ.1], by linarith [hξ.2, hx.2]⟩).deriv
      have hlen : 0 < x - y := by linarith
      have heq : f x - f y = f' ξ * (x - y) := by
        rw [←hderiv, hξ_slope]; field_simp [hlen.ne'] <;> ring
      have h_abs : |f y - f x| = |f' ξ| * (x - y) := by
        have h : f y - f x = -(f x - f y) := by ring
        rw [h, abs_neg, heq, abs_mul, abs_of_pos hlen]
      have h_goal : |f' ξ| * (x - y) ≤ C * |y - x| := by
        have h9 : |y - x| = x - y := by rw [abs_of_neg (show y - x < 0 by linarith)] <;> ring
        rw [h9]
        exact mul_le_mul_of_nonneg_right (f'_bound ξ hξ_mem) hlen.le
      rw [h_abs]; exact h_goal

/-- If |h''| ≤ d on [x0-B, x0+B] and |h'(x0)| ≤ S, then |h'(y)| ≤ S + d*B. -/
lemma enlarged_deriv_bound
    {h' h'' : ℝ → ℝ} {x0 B S d : ℝ}
    (hB : 0 ≤ B) (hd_nonneg : 0 ≤ d)
    (h'_cont : ContinuousOn h' (Icc (x0 - B) (x0 + B)))
    (h'_deriv : ∀ x ∈ Ioo (x0 - B) (x0 + B), HasDerivAt h' (h'' x) x)
    (h''_bound : ∀ x ∈ Icc (x0 - B) (x0 + B), |h'' x| ≤ d)
    (hx0 : |h' x0| ≤ S) :
    ∀ y ∈ Icc (x0 - B) (x0 + B), |h' y| ≤ S + d * B := by
  set a := x0 - B with ha_def
  set b := x0 + B with hb_def
  have h_lip := lipschitz_from_deriv_bound hd_nonneg h'_cont h'_deriv h''_bound
  intro y hy
  have hx0_mem : x0 ∈ Icc a b := by
    dsimp only [a, b]; constructor <;> linarith
  have h2 : |h' y - h' x0| ≤ d * |y - x0| := by
    simpa [abs_sub_comm] using h_lip y hy x0 hx0_mem
  have h3 : |y - x0| ≤ B := by
    rw [abs_le] <;> constructor <;> linarith [hy.1, hy.2]
  have h4 : |h' y - h' x0| ≤ d * B := by
    calc |h' y - h' x0| ≤ d * |y - x0| := h2
      _ ≤ d * B := mul_le_mul_of_nonneg_left h3 hd_nonneg
  have h5 : |h' y| ≤ |h' x0| + |h' y - h' x0| := by
    calc |h' y| = |h' x0 + (h' y - h' x0)| := by ring_nf
      _ ≤ |h' x0| + |h' y - h' x0| := abs_add_le _ _
  linarith

/-! ### Lemma 2: Value bound on enlarged interval -/

/-- If |h'| ≤ S' on [x0-B, x0+B] and |h(x0)| ≤ M, then |h(y)| ≤ M + S'*B. -/
lemma enlarged_value_bound
    {h h' : ℝ → ℝ} {x0 B M S' : ℝ}
    (hB : 0 ≤ B) (hS'_nonneg : 0 ≤ S')
    (h_cont : ContinuousOn h (Icc (x0 - B) (x0 + B)))
    (h_deriv : ∀ x ∈ Ioo (x0 - B) (x0 + B), HasDerivAt h (h' x) x)
    (h'_bound : ∀ y ∈ Icc (x0 - B) (x0 + B), |h' y| ≤ S')
    (hx0 : |h x0| ≤ M) :
    ∀ y ∈ Icc (x0 - B) (x0 + B), |h y| ≤ M + S' * B := by
  set a := x0 - B with ha_def
  set b := x0 + B with hb_def
  have h_lip := lipschitz_from_deriv_bound hS'_nonneg h_cont h_deriv h'_bound
  intro y hy
  have hx0_mem : x0 ∈ Icc a b := by
    dsimp only [a, b]; constructor <;> linarith
  have h2 : |h y - h x0| ≤ S' * |y - x0| := by
    simpa [abs_sub_comm] using h_lip y hy x0 hx0_mem
  have h3 : |y - x0| ≤ B := by
    rw [abs_le] <;> constructor <;> linarith [hy.1, hy.2]
  have h4 : |h y - h x0| ≤ S' * B := by
    calc |h y - h x0| ≤ S' * |y - x0| := h2
      _ ≤ S' * B := mul_le_mul_of_nonneg_left h3 hS'_nonneg
  have h5 : |h y| ≤ |h x0| + |h y - h x0| := by
    calc |h y| = |h x0 + (h y - h x0)| := by ring_nf
      _ ≤ |h x0| + |h y - h x0| := abs_add_le _ _
  linarith

/-- Convert interval membership from `Icc (x0-B) (x0+B)` to `Icc a b`. -/
private lemma directional_lens_interval_conv
    {a b x0 B x : ℝ} (ha_def : a = x0 - B) (hb_def : b = x0 + B)
    (hx : x ∈ Icc (x0 - B) (x0 + B)) : x ∈ Icc a b := by
  have h1 : x0 - B ≤ x := hx.1
  have h2 : x ≤ x0 + B := hx.2
  have h3 : a ≤ x := by
    calc a = x0 - B := ha_def
      _ ≤ x := h1
  have h4 : x ≤ b := by
    calc x ≤ x0 + B := h2
      _ = b := hb_def.symm
  exact ⟨h3, h4⟩

/-- Convert derivative bound through interval and definitional equality. -/
private lemma directional_lens_deriv_bound_conv
    {x0 B a b d : ℝ} {h1 h2 : ℝ → ℝ}
    (ha_def : a = x0 - B) (hb_def : b = x0 + B)
    (h_deriv2 : ∀ y, deriv h1 y = h2 y)
    (h2_bound : ∀ x ∈ Icc a b, |h2 x| ≤ d)
    {x : ℝ} (hx : x ∈ Icc (x0 - B) (x0 + B)) :
    |deriv h1 x| ≤ d := by
  have hx' : x ∈ Icc a b := directional_lens_interval_conv ha_def hb_def hx
  have h_eq : deriv h1 x = h2 x := h_deriv2 x
  rw [h_eq]
  exact h2_bound x hx'

/-! ### Lemma 3: Key enlargement estimate -/

/-- Crude polynomial bound: V + (2T+1)*C0 + C0^2 ≤ 2*10^6*K^2*T^20. -/
lemma enlargement_poly_bound1
    {K tangency : ℝ} (hK : 1 ≤ K) (htang : 5 ≤ tangency)
    (V C0 : ℝ) (hV_le : V ≤ 30 * tangency ^ 10)
    (hC0_le : C0 ≤ 1000 * K * tangency ^ 10)
    (hC0_nonneg : 0 ≤ C0) :
    V + (2 * tangency + 1) * C0 + C0 ^ 2 ≤ 2000000 * K ^ 2 * tangency ^ 20 := by
  have h_tang_pos : 0 < tangency := by linarith
  have hK_pos : 0 < K := by linarith
  have h1 : tangency ^ 10 ≤ tangency ^ 20 := by
    have h2 : tangency ^ 20 = tangency ^ 10 * tangency ^ 10 := by ring
    rw [h2]
    have h3 : tangency ^ 10 ≥ 1 := by
      have h4 : 1 ≤ tangency := by linarith
      have h5 : (1 : ℝ) ^ 10 ≤ tangency ^ 10 := by gcongr
      simpa using h5
    have h6 : 0 ≤ tangency ^ 10 := by positivity
    nlinarith
  have h2 : tangency ^ 11 ≤ tangency ^ 20 := by
    have h3 : tangency ^ 20 = tangency ^ 11 * tangency ^ 9 := by ring
    rw [h3]
    have h4 : tangency ^ 9 ≥ 1 := by
      have h5 : 1 ≤ tangency := by linarith
      have h6 : (1 : ℝ) ^ 9 ≤ tangency ^ 9 := by gcongr
      simpa using h6
    have h7 : 0 ≤ tangency ^ 11 := by positivity
    nlinarith
  have hV2 : V ≤ 30 * K ^ 2 * tangency ^ 20 := by
    calc V
        ≤ 30 * tangency ^ 10 := hV_le
      _ ≤ 30 * tangency ^ 20 := by exact mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ ≤ 30 * K ^ 2 * tangency ^ 20 := by
        have hK2 : 1 ≤ K ^ 2 := by
          have h : 1 ≤ K := hK
          nlinarith
        have h_pos : 0 ≤ 30 * tangency ^ 20 := by positivity
        have h' : 1 * (30 * tangency ^ 20) ≤ K ^ 2 * (30 * tangency ^ 20) :=
          mul_le_mul_of_nonneg_right hK2 h_pos
        have h_eq : 1 * (30 * tangency ^ 20) = 30 * tangency ^ 20 := by ring
        have h_eq2 : K ^ 2 * (30 * tangency ^ 20) = 30 * K ^ 2 * tangency ^ 20 := by ring
        rw [h_eq, h_eq2] at h'; exact h'
  have hC02 : (2 * tangency + 1) * C0 ≤ 3000 * K ^ 2 * tangency ^ 20 := by
    have h3 : 2 * tangency + 1 ≤ 3 * tangency := by linarith
    have h4 : (2 * tangency + 1) * C0 ≤ 3 * tangency * C0 :=
      mul_le_mul_of_nonneg_right h3 hC0_nonneg
    have h5 : 3 * tangency * C0 ≤ 3 * tangency * (1000 * K * tangency ^ 10) :=
      mul_le_mul_of_nonneg_left hC0_le (by positivity)
    have h6 : 3 * tangency * (1000 * K * tangency ^ 10) = 3000 * K * tangency ^ 11 := by ring
    have h7 : 3000 * K * tangency ^ 11 ≤ 3000 * K ^ 2 * tangency ^ 20 := by
      have hK2 : K ≤ K ^ 2 := by
        have h : 1 ≤ K := hK
        nlinarith
      have h8 : 3000 * K * tangency ^ 11 ≤ 3000 * K * tangency ^ 20 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h9 : 3000 * K * tangency ^ 20 ≤ 3000 * K ^ 2 * tangency ^ 20 := by
        have h_pos : 0 ≤ 3000 * tangency ^ 20 := by positivity
        have h' : K * (3000 * tangency ^ 20) ≤ K ^ 2 * (3000 * tangency ^ 20) :=
          mul_le_mul_of_nonneg_right hK2 h_pos
        have h_eq : K * (3000 * tangency ^ 20) = 3000 * K * tangency ^ 20 := by ring
        have h_eq2 : K ^ 2 * (3000 * tangency ^ 20) = 3000 * K ^ 2 * tangency ^ 20 := by ring
        rw [h_eq, h_eq2] at h'; exact h'
      calc 3000 * K * tangency ^ 11
          ≤ 3000 * K * tangency ^ 20 := h8
        _ ≤ 3000 * K ^ 2 * tangency ^ 20 := h9
    calc (2 * tangency + 1) * C0
        ≤ 3 * tangency * C0 := h4
      _ ≤ 3 * tangency * (1000 * K * tangency ^ 10) := h5
      _ = 3000 * K * tangency ^ 11 := h6
      _ ≤ 3000 * K ^ 2 * tangency ^ 20 := h7
  have hC0sq : C0 ^ 2 ≤ 1000000 * K ^ 2 * tangency ^ 20 := by
    have h_pos1 : 0 ≤ C0 := hC0_nonneg
    have h_pos2 : 0 ≤ 1000 * K * tangency ^ 10 := by positivity
    have h_abs : |C0| ≤ |1000 * K * tangency ^ 10| := by
      rw [abs_of_nonneg h_pos1, abs_of_nonneg h_pos2]
      exact hC0_le
    have h4 : C0 ^ 2 ≤ (1000 * K * tangency ^ 10) ^ 2 := sq_le_sq.mpr h_abs
    have h10 : (1000 * K * tangency ^ 10) ^ 2 = 1000000 * K ^ 2 * tangency ^ 20 := by ring
    rw [h10] at h4; exact h4
  have h_final : V + (2 * tangency + 1) * C0 + C0 ^ 2 ≤
      30 * K ^ 2 * tangency ^ 20 + 3000 * K ^ 2 * tangency ^ 20 + 1000000 * K ^ 2 * tangency ^ 20 :=
    add_le_add (add_le_add hV2 hC02) hC0sq
  have h_last : 30 * K ^ 2 * tangency ^ 20 + 3000 * K ^ 2 * tangency ^ 20 + 1000000 * K ^ 2 * tangency ^ 20 ≤
      2000000 * K ^ 2 * tangency ^ 20 := by
    have h_pos : 0 ≤ K ^ 2 * tangency ^ 20 := by positivity
    have h_coeff : (30 + 3000 + 1000000 : ℝ) ≤ 2000000 := by norm_num
    have h : (30 + 3000 + 1000000) * (K ^ 2 * tangency ^ 20) ≤ 2000000 * (K ^ 2 * tangency ^ 20) :=
      mul_le_mul_of_nonneg_right h_coeff h_pos
    have h_eq : (30 + 3000 + 1000000) * (K ^ 2 * tangency ^ 20) =
        30 * K ^ 2 * tangency ^ 20 + 3000 * K ^ 2 * tangency ^ 20 + 1000000 * K ^ 2 * tangency ^ 20 := by ring
    have h_rhs : 2000000 * (K ^ 2 * tangency ^ 20) = 2000000 * K ^ 2 * tangency ^ 20 := by ring
    rw [h_eq, h_rhs] at h
    exact h
  exact h_final.trans h_last

/-- First division bound: r * term1 ≤ 2000 / (K^2 * T^30). -/
lemma enlargement_div_bound1
    {K tangency r : ℝ} (hK : 1 ≤ K) (htang : 5 ≤ tangency)
    (term1 : ℝ) (hterm1 : term1 ≤ 2000000 * K ^ 2 * tangency ^ 20)
    (hterm1_nonneg : 0 ≤ term1)
    (hr_bound : r ≤ 1 / (1000 * K ^ 4 * tangency ^ 50)) :
    r * term1 ≤ 2000 / (K ^ 2 * tangency ^ 30) := by
  have hK_pos : 0 < K := by linarith
  have htang_pos : 0 < tangency := by linarith
  have h_a : r * term1 ≤ (1 / (1000 * K ^ 4 * tangency ^ 50)) * term1 :=
    mul_le_mul_of_nonneg_right hr_bound hterm1_nonneg
  have h_b : (1 / (1000 * K ^ 4 * tangency ^ 50)) * term1 ≤
      (1 / (1000 * K ^ 4 * tangency ^ 50)) * (2000000 * K ^ 2 * tangency ^ 20) :=
    mul_le_mul_of_nonneg_left hterm1 (by positivity)
  have h_c : r * term1 ≤
      (1 / (1000 * K ^ 4 * tangency ^ 50)) * (2000000 * K ^ 2 * tangency ^ 20) :=
    h_a.trans h_b
  have h_eq : (1 / (1000 * K ^ 4 * tangency ^ 50)) * (2000000 * K ^ 2 * tangency ^ 20) =
      2000 / (K ^ 2 * tangency ^ 30) := by
    have h1 : (1000 * K ^ 4 * tangency ^ 50) ≠ 0 := by positivity
    have h2 : (K ^ 2 * tangency ^ 30) ≠ 0 := by positivity
    field_simp [h1, h2] <;> ring_nf <;> field_simp [h1, h2] <;> ring
  rw [h_eq] at h_c
  exact h_c

/-- Second division bound: L * term2 ≤ 2000 / (30 * T^15). -/
lemma enlargement_div_bound2
    {K tangency L : ℝ} (hK : 1 ≤ K) (htang : 5 ≤ tangency)
    (term2 : ℝ) (hterm2 : term2 ≤ 2000 * K * tangency ^ 10)
    (hterm2_nonneg : 0 ≤ term2)
    (hL_bound : L ≤ 1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25))
    (h_sqrt1000_ge30 : (30 : ℝ) ≤ Real.sqrt 1000) :
    L * term2 ≤ 2000 / (30 * K * tangency ^ 15) := by
  have hK_pos : 0 < K := by linarith
  have htang_pos : 0 < tangency := by linarith
  have h_a : L * term2 ≤
      (1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25)) * term2 :=
    mul_le_mul_of_nonneg_right hL_bound hterm2_nonneg
  have h_b : (1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25)) * term2 ≤
      (1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25)) * (2000 * K * tangency ^ 10) :=
    mul_le_mul_of_nonneg_left hterm2 (by positivity)
  have h_c : L * term2 ≤
      (1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25)) * (2000 * K * tangency ^ 10) :=
    h_a.trans h_b
  have h_eq : (1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25)) * (2000 * K * tangency ^ 10) =
      2000 / (Real.sqrt 1000 * K * tangency ^ 15) := by
    have h1 : (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) ≠ 0 := by positivity
    field_simp [h1] <;> ring
  rw [h_eq] at h_c
  have h_pos15 : 0 < K * tangency ^ 15 := by positivity
  have h_final : 2000 / (Real.sqrt 1000 * K * tangency ^ 15) ≤ 2000 / (30 * K * tangency ^ 15) := by
    have h2 : 0 ≤ K * tangency ^ 15 := by positivity
    have h3 : (30 : ℝ) ≤ Real.sqrt 1000 := h_sqrt1000_ge30
    have h4 : 30 * (K * tangency ^ 15) ≤ Real.sqrt 1000 * (K * tangency ^ 15) :=
      mul_le_mul_of_nonneg_right h3 h2
    have h5 : 30 * (K * tangency ^ 15) = 30 * K * tangency ^ 15 := by ring
    have h6 : Real.sqrt 1000 * (K * tangency ^ 15) = Real.sqrt 1000 * K * tangency ^ 15 := by ring
    rw [h5, h6] at h4
    have h_b : 0 < 30 * K * tangency ^ 15 := by positivity
    have h9 : (1 : ℝ) / (Real.sqrt 1000 * K * tangency ^ 15) ≤ (1 : ℝ) / (30 * K * tangency ^ 15) :=
      one_div_le_one_div_of_le h_b h4
    have h10 : 2000 / (Real.sqrt 1000 * K * tangency ^ 15) =
        2000 * ((1 : ℝ) / (Real.sqrt 1000 * K * tangency ^ 15)) := by ring
    have h11 : 2000 / (30 * K * tangency ^ 15) =
        2000 * ((1 : ℝ) / (30 * K * tangency ^ 15)) := by ring
    rw [h10, h11]
    exact mul_le_mul_of_nonneg_left h9 (by norm_num)
  exact h_c.trans h_final

/-- Sum bound: 2000/(K*T^30) + 2000/(30*T^15) < 1. -/
lemma enlargement_sum_bound
    {K tangency : ℝ} (hK : 1 ≤ K) (htang : 5 ≤ tangency) :
    2000 / (K * tangency ^ 30) + 2000 / (30 * tangency ^ 15) < 1 := by
  have h_tang5_gt : tangency ^ 5 > 100 := by
    have h2 : tangency ^ 5 ≥ (5 : ℝ)^5 := by gcongr <;> linarith
    have h3 : (5 : ℝ)^5 > 100 := by norm_num
    linarith
  have h_tang15_gt : tangency ^ 15 > 1000000 := by
    have h4 : tangency ^ 15 = (tangency ^ 5) ^ 3 := by ring
    rw [h4]
    have h5 : tangency ^ 5 > 100 := h_tang5_gt
    have h6 : (tangency ^ 5) ^ 3 > (100 : ℝ) ^ 3 := by gcongr
    have h7 : (100 : ℝ) ^ 3 = 1000000 := by norm_num
    rw [h7] at h6; exact h6
  have h_tang30_gt : tangency ^ 30 > 1000000000000 := by
    have h4 : tangency ^ 30 = (tangency ^ 15) ^ 2 := by ring
    rw [h4]
    have h5 : tangency ^ 15 > 1000000 := h_tang15_gt
    have h6 : (tangency ^ 15) ^ 2 > (1000000 : ℝ) ^ 2 := by gcongr
    have h7 : (1000000 : ℝ) ^ 2 = 1000000000000 := by norm_num
    rw [h7] at h6; exact h6
  have h_posK : 0 < K := by linarith
  have h_strict1 : 2000 / (K * tangency ^ 30) < 1 / 2 := by
    have h6 : K * tangency ^ 30 > 1000000000000 := by
      have h7 : tangency ^ 30 > 1000000000000 := h_tang30_gt
      have h8 : 1 ≤ K := hK
      have h9 : K * tangency ^ 30 ≥ tangency ^ 30 := by
        have h10 : 0 ≤ tangency ^ 30 := by positivity
        nlinarith
      linarith
    have h9 : (0 : ℝ) < 1000000000000 := by norm_num
    have h_pos2 : 0 < K * tangency ^ 30 := by positivity
    have h10 : 2000 / (K * tangency ^ 30) < 2000 / 1000000000000 :=
      div_lt_div_of_pos_left (by norm_num) h9 h6
    have h14 : (2000 : ℝ) / 1000000000000 < 1 / 2 := by norm_num
    exact h10.trans h14
  have h_strict2 : 2000 / (30 * tangency ^ 15) < 1 / 2 := by
    have h11 : 30 * tangency ^ 15 > 30 * 1000000 := by
      have h12 : tangency ^ 15 > 1000000 := h_tang15_gt
      have h13 : (0 : ℝ) < 30 := by norm_num
      have h14 : (1000000 : ℝ) < tangency ^ 15 := h12
      exact mul_lt_mul_of_pos_left h14 h13
    have h14 : 0 < (30 * 1000000 : ℝ) := by norm_num
    have h15 : 2000 / (30 * tangency ^ 15) < 2000 / (30 * 1000000) := by
      apply div_lt_div_of_pos_left (by norm_num) h14
      exact h11
    have h16 : (2000 : ℝ) / (30 * 1000000) < 1 / 2 := by norm_num
    exact h15.trans h16
  linarith

/-- Specialized wrapper for div_bound1 that proves non-negativity internally. -/
lemma enlargement_div_bound1'
    {K tangency r V C0 : ℝ} (hK : 1 ≤ K) (htang : 5 ≤ tangency)
    (hV_nonneg : 0 ≤ V) (hC0_nonneg : 0 ≤ C0)
    (hterm1 : V + (2 * tangency + 1) * C0 + C0 ^ 2 ≤ 2000000 * K ^ 2 * tangency ^ 20)
    (hr_bound : r ≤ 1 / (1000 * K ^ 4 * tangency ^ 50)) :
    r * (V + (2 * tangency + 1) * C0 + C0 ^ 2) ≤ 2000 / (K ^ 2 * tangency ^ 30) := by
  have h_nonneg : 0 ≤ V + (2 * tangency + 1) * C0 + C0 ^ 2 := by positivity
  exact enlargement_div_bound1 hK htang (V + (2 * tangency + 1) * C0 + C0 ^ 2) hterm1 h_nonneg hr_bound

/-- Specialized wrapper for div_bound2 that proves non-negativity internally. -/
lemma enlargement_div_bound2'
    {K tangency L C0 : ℝ} (hK : 1 ≤ K) (htang : 5 ≤ tangency)
    (hC0_nonneg : 0 ≤ C0)
    (hterm2 : 2 * tangency + 1 + C0 ≤ 2000 * K * tangency ^ 10)
    (hL_bound : L ≤ 1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25))
    (h_sqrt1000_ge30 : (30 : ℝ) ≤ Real.sqrt 1000) :
    L * (2 * tangency + 1 + C0) ≤ 2000 / (30 * K * tangency ^ 15) := by
  have h_nonneg : 0 ≤ 2 * tangency + 1 + C0 := by positivity
  exact enlargement_div_bound2 hK htang (2 * tangency + 1 + C0) hterm2 h_nonneg hL_bound h_sqrt1000_ge30

/-- Algebraic expansion of the main enlargement inequality. -/
lemma enlargement_main_ineq
    {V C0 d L r tangency delta : ℝ}
    (hL_sq : L ^ 2 = r)
    (hM_le : V * delta ≤ V * d * r) :
    V * delta + ((2 * tangency + 1) * d * L + d * (C0 * L)) * (C0 * L) +
      ((2 * tangency + 1) * d * L + d * (C0 * L)) ≤
    d * (r * (V + (2 * tangency + 1) * C0 + C0 ^ 2) +
      L * (2 * tangency + 1 + C0)) := by
  have h1 : ((2 * tangency + 1) * d * L + d * (C0 * L)) * (C0 * L) =
      d * r * ((2 * tangency + 1) * C0 + C0 ^ 2) := by
    have h2 : L * (C0 * L) = C0 * L ^ 2 := by ring
    have h3 : (C0 * L) * (C0 * L) = C0 ^ 2 * L ^ 2 := by ring
    calc ((2 * tangency + 1) * d * L + d * (C0 * L)) * (C0 * L)
        = (2 * tangency + 1) * d * (L * (C0 * L)) + d * ((C0 * L) * (C0 * L)) := by ring
      _ = (2 * tangency + 1) * d * (C0 * L ^ 2) + d * (C0 ^ 2 * L ^ 2) := by rw [h2, h3]
      _ = (2 * tangency + 1) * d * C0 * r + d * C0 ^ 2 * r := by rw [hL_sq] <;> ring
      _ = d * r * ((2 * tangency + 1) * C0 + C0 ^ 2) := by ring
  have h4 : ((2 * tangency + 1) * d * L + d * (C0 * L)) =
      d * L * (2 * tangency + 1 + C0) := by ring
  have h5 : d * (r * (V + (2 * tangency + 1) * C0 + C0 ^ 2) +
        L * (2 * tangency + 1 + C0)) =
      d * r * V + d * r * ((2 * tangency + 1) * C0 + C0 ^ 2) +
      d * L * (2 * tangency + 1 + C0) := by ring
  rw [h1, h4, h5]
  have h6 : V * delta ≤ d * r * V := by
    have h7 : V * d * r = d * r * V := by ring
    rw [h7] at hM_le
    exact hM_le
  linarith

/--
Core arithmetic: given all precomputed bounds, prove the final strict inequality.
Extracted to minimize elaboration context.
-/
lemma enlarged_bounds_small_core
    {K tangency d V L C0 r delta : ℝ}
    (hK : 1 ≤ K)
    (htang : 5 ≤ tangency)
    (hd_pos : 0 < d)
    (hV_nonneg : 0 ≤ V)
    (hC0_nonneg : 0 ≤ C0)
    (hL_sq : L ^ 2 = r)
    (hM_le : V * delta ≤ V * d * r)
    (hterm1_bound : V + (2 * tangency + 1) * C0 + C0 ^ 2 ≤ 2000000 * K ^ 2 * tangency ^ 20)
    (hterm2_bound : (2 * tangency + 1 + C0) ≤ 2000 * K * tangency ^ 10)
    (hr_bound : r ≤ 1 / (1000 * K ^ 4 * tangency ^ 50))
    (hL_bound : L ≤ 1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25))
    (h_sqrt1000_ge30 : (30 : ℝ) ≤ Real.sqrt 1000) :
    V * delta + ((2 * tangency + 1) * d * L + d * (C0 * L)) * (C0 * L) +
      ((2 * tangency + 1) * d * L + d * (C0 * L)) < d / K := by
  have h_main_ineq :
      V * delta + ((2 * tangency + 1) * d * L + d * (C0 * L)) * (C0 * L) +
        ((2 * tangency + 1) * d * L + d * (C0 * L)) ≤
      d * (r * (V + (2 * tangency + 1) * C0 + C0 ^ 2) +
        L * (2 * tangency + 1 + C0)) :=
    enlargement_main_ineq hL_sq hM_le

  have h1_div : r * (V + (2 * tangency + 1) * C0 + C0 ^ 2) ≤
      2000 / (K ^ 2 * tangency ^ 30) :=
    enlargement_div_bound1' hK htang hV_nonneg hC0_nonneg hterm1_bound hr_bound

  have h2_div : L * (2 * tangency + 1 + C0) ≤ 2000 / (30 * K * tangency ^ 15) :=
    enlargement_div_bound2' hK htang hC0_nonneg hterm2_bound hL_bound h_sqrt1000_ge30

  have h_sum : 2000 / (K * tangency ^ 30) + 2000 / (30 * tangency ^ 15) < 1 :=
    enlargement_sum_bound hK htang

  have hK_pos : 0 < K := by linarith
  have h_factor : 2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15) =
      (1 / K) * (2000 / (K * tangency ^ 30) + 2000 / (30 * tangency ^ 15)) := by
    field_simp [hK_pos.ne'] <;> ring

  have h_arith : r * (V + (2 * tangency + 1) * C0 + C0 ^ 2) +
      L * (2 * tangency + 1 + C0) < 1 / K := by
    have h_left : r * (V + (2 * tangency + 1) * C0 + C0 ^ 2) +
        L * (2 * tangency + 1 + C0) ≤
        2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15) :=
      add_le_add h1_div h2_div
    rw [h_factor] at h_left
    have h_right : (1 / K) * (2000 / (K * tangency ^ 30) + 2000 / (30 * tangency ^ 15)) < (1 / K) * (1 : ℝ) :=
      mul_lt_mul_of_pos_left h_sum (by positivity)
    have h_one : (1 / K) * (1 : ℝ) = 1 / K := by ring
    rw [h_one] at h_right
    exact h_left.trans_lt h_right

  have h_final : d * (r * (V + (2 * tangency + 1) * C0 + C0 ^ 2) +
      L * (2 * tangency + 1 + C0)) < d / K := by
    have h : d * (r * (V + (2 * tangency + 1) * C0 + C0 ^ 2) +
        L * (2 * tangency + 1 + C0)) < d * (1 / K) :=
      mul_lt_mul_of_pos_left h_arith hd_pos
    have h2 : d * (1 / K) = d / K := by ring
    rw [h2] at h
    exact h
  exact h_main_ineq.trans_lt h_final

/--
Quantitative version: the enlarged bound is at most
`d * (2000/(K^2*T^30) + 2000/(30*K*T^15))`.
-/
lemma enlarged_bounds_quantitative_core
    {K tangency d V L C0 r delta : ℝ}
    (hK : 1 ≤ K)
    (htang : 5 ≤ tangency)
    (hd_pos : 0 < d)
    (hV_nonneg : 0 ≤ V)
    (hC0_nonneg : 0 ≤ C0)
    (hL_sq : L ^ 2 = r)
    (hM_le : V * delta ≤ V * d * r)
    (hterm1_bound : V + (2 * tangency + 1) * C0 + C0 ^ 2 ≤ 2000000 * K ^ 2 * tangency ^ 20)
    (hterm2_bound : (2 * tangency + 1 + C0) ≤ 2000 * K * tangency ^ 10)
    (hr_bound : r ≤ 1 / (1000 * K ^ 4 * tangency ^ 50))
    (hL_bound : L ≤ 1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25))
    (h_sqrt1000_ge30 : (30 : ℝ) ≤ Real.sqrt 1000) :
    V * delta + ((2 * tangency + 1) * d * L + d * (C0 * L)) * (C0 * L) +
      ((2 * tangency + 1) * d * L + d * (C0 * L)) ≤
    d * (2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15)) := by
  have h_main_ineq := @enlargement_main_ineq V C0 d L r tangency delta hL_sq hM_le
  have h1_div := enlargement_div_bound1' hK htang hV_nonneg hC0_nonneg hterm1_bound hr_bound
  have h2_div := enlargement_div_bound2' hK htang hC0_nonneg hterm2_bound hL_bound h_sqrt1000_ge30
  have h_sum : r * (V + (2 * tangency + 1) * C0 + C0 ^ 2) + L * (2 * tangency + 1 + C0) ≤
      2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15) :=
    add_le_add h1_div h2_div
  have h3 : d * (r * (V + (2 * tangency + 1) * C0 + C0 ^ 2) + L * (2 * tangency + 1 + C0)) ≤
      d * (2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15)) :=
    mul_le_mul_of_nonneg_left h_sum (by linarith)
  exact h_main_ineq.trans h3

/--
With the small-scale hypothesis, the enlarged value+derivative bound
is strictly less than `d/K`.
-/
lemma enlarged_bounds_small
    {K tangency delta t d : ℝ}
    (hK : 1 ≤ K)
    (htang : 5 ≤ tangency)
    (hdelta : 0 < delta)
    (ht : 0 < t)
    (hdt : delta ≤ t)
    (hd_ge_2t : 2 * t ≤ d)
    (hd_le_K : d ≤ K)
    (h_small : tangency ^ 50 * delta ≤ t / (1000 * K ^ 4)) :
    let V := 25 * tangency ^ 10 + 2 * tangency + 2
    let L := Real.sqrt (delta / t)
    let C0 := 20 * K * V + 20 * K
    let M := V * delta
    let S := (2 * tangency + 1) * d * L
    let B := C0 * L
    M + (S + d * B) * B + (S + d * B) < d / K := by
  dsimp only
  set V := 25 * tangency ^ 10 + 2 * tangency + 2 with hV_def
  set L := Real.sqrt (delta / t) with hL_def
  set C0 := 20 * K * V + 20 * K with hC0_def
  set r := delta / t with hr_def
  have hK_pos : 0 < K := by linarith
  have htang_pos : 0 < tangency := by linarith
  have hd_pos : 0 < d := by linarith
  have hr_pos : 0 < r := by positivity
  have hL_pos : 0 < L := Real.sqrt_pos.mpr hr_pos
  have hL_sq : L ^ 2 = r := by
    rw [hL_def]; exact Real.sq_sqrt (by positivity)
  have hV_pos : 0 < V := by positivity

  have hr_bound : r ≤ 1 / (1000 * K ^ 4 * tangency ^ 50) := by
    have h_pos1 : 0 < tangency ^ 50 * t := by positivity
    have h : (tangency ^ 50 * delta) / (tangency ^ 50 * t) ≤
        (t / (1000 * K ^ 4)) / (tangency ^ 50 * t) := by gcongr
    have h2 : (tangency ^ 50 * delta) / (tangency ^ 50 * t) = r := by
      rw [hr_def]; field_simp [htang_pos.ne', ht.ne'] <;> ring
    have h3 : (t / (1000 * K ^ 4)) / (tangency ^ 50 * t) =
        1 / (1000 * K ^ 4 * tangency ^ 50) := by
      field_simp [hK_pos.ne', htang_pos.ne', ht.ne'] <;> ring
    rw [h2, h3] at h; exact h

  have hL_bound : L ≤ 1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) := by
    have h4 : L ≤ Real.sqrt (1 / (1000 * K ^ 4 * tangency ^ 50)) :=
      Real.sqrt_le_sqrt hr_bound
    have h_pos : 0 ≤ Real.sqrt 1000 * K ^ 2 * tangency ^ 25 := by positivity
    have h_sq : (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) ^ 2 =
        1000 * K ^ 4 * tangency ^ 50 := by
      have h7 : (Real.sqrt 1000) ^ 2 = 1000 := Real.sq_sqrt (by norm_num)
      calc (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) ^ 2
        = (Real.sqrt 1000) ^ 2 * (K ^ 2) ^ 2 * (tangency ^ 25) ^ 2 := by ring
      _ = 1000 * K ^ 4 * tangency ^ 50 := by rw [h7] <;> ring
    have h8 : Real.sqrt (1000 * K ^ 4 * tangency ^ 50) =
        Real.sqrt 1000 * K ^ 2 * tangency ^ 25 := by
      rw [←h_sq]; exact Real.sqrt_sq h_pos
    have h6 : Real.sqrt (1 / (1000 * K ^ 4 * tangency ^ 50)) =
        1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_one, h8]
    rw [h6] at h4; exact h4

  have h_tang_ge1 : 1 ≤ tangency := by linarith
  have h_tang5_ge : tangency ^ 5 ≥ 100 := by
    have h : (5 : ℝ)^5 ≤ tangency^5 := by gcongr <;> linarith
    have h2 : (100 : ℝ) ≤ (5 : ℝ)^5 := by norm_num
    exact h2.trans h
  have h_pow9_ge1 : tangency ^ 9 ≥ 1 := by
    have h1 : 1 ≤ tangency := h_tang_ge1
    have h2 : (1 : ℝ)^9 ≤ tangency^9 := by gcongr
    simpa using h2
  have h_pow10_ge1 : tangency ^ 10 ≥ 1 := by
    have h1 : 1 ≤ tangency := h_tang_ge1
    have h2 : (1 : ℝ)^10 ≤ tangency^10 := by gcongr
    simpa using h2
  have h_tang_le_pow10 : tangency ≤ tangency ^ 10 := by
    have h1 : tangency ^ 9 ≥ 1 := h_pow9_ge1
    nlinarith

  have hV_le : V ≤ 30 * tangency ^ 10 := by
    rw [hV_def]
    have h1 : 2 * tangency + 2 ≤ 5 * tangency ^ 10 := by
      have h2 : tangency ≤ tangency ^ 10 := h_tang_le_pow10
      nlinarith
    nlinarith

  have hV_nonneg : 0 ≤ V := by
    rw [hV_def]; nlinarith

  have hC0_nonneg : 0 ≤ C0 := by
    rw [hC0_def]; nlinarith

  have hC0_le : C0 ≤ 1000 * K * tangency ^ 10 := by
    rw [hC0_def]
    have h1 : 20 * K * V ≤ 20 * K * (30 * tangency ^ 10) :=
      mul_le_mul_of_nonneg_left hV_le (by nlinarith)
    have h2 : 20 * K ≤ 20 * K * tangency ^ 10 := by
      have h3 : 1 ≤ tangency ^ 10 := h_pow10_ge1
      have h4 : 0 ≤ 20 * K := by nlinarith
      calc 20 * K = 20 * K * 1 := by ring
        _ ≤ 20 * K * tangency ^ 10 := by gcongr
    have h_sum : 20 * K * V + 20 * K ≤ 620 * K * tangency ^ 10 := by
      calc 20 * K * V + 20 * K
          ≤ 20 * K * (30 * tangency ^ 10) + 20 * K * tangency ^ 10 := by
            exact add_le_add h1 h2
        _ = 620 * K * tangency ^ 10 := by ring
    have h_final : 620 * K * tangency ^ 10 ≤ 1000 * K * tangency ^ 10 := by
      have h_pos : 0 ≤ K * tangency ^ 10 := by positivity
      have h : (620 : ℝ) ≤ 1000 := by norm_num
      have h' : 620 * (K * tangency ^ 10) ≤ 1000 * (K * tangency ^ 10) :=
        mul_le_mul_of_nonneg_right h h_pos
      have h_eq1 : 620 * (K * tangency ^ 10) = 620 * K * tangency ^ 10 := by ring
      have h_eq2 : 1000 * (K * tangency ^ 10) = 1000 * K * tangency ^ 10 := by ring
      rw [h_eq1, h_eq2] at h'
      exact h'
    exact h_sum.trans h_final

  have hterm1_bound : V + (2 * tangency + 1) * C0 + C0 ^ 2 ≤
      2000000 * K ^ 2 * tangency ^ 20 :=
    enlargement_poly_bound1 hK htang V C0 hV_le hC0_le hC0_nonneg

  have hterm2_bound : (2 * tangency + 1 + C0) ≤ 2000 * K * tangency ^ 10 := by
    have h1 : 2 * tangency + 1 ≤ 3 * tangency := by linarith
    have h2 : 3 * tangency ≤ 3 * K * tangency ^ 10 := by
      have h3 : tangency ≤ tangency ^ 10 := h_tang_le_pow10
      have h4 : 1 ≤ K := by linarith
      have h5 : 3 * tangency ≤ 3 * tangency ^ 10 := mul_le_mul_of_nonneg_left h3 (by norm_num)
      have h6 : 3 * tangency ^ 10 ≤ 3 * K * tangency ^ 10 := by
        have h_pos : 0 ≤ 3 * tangency ^ 10 := by positivity
        have h7 : 1 * (3 * tangency ^ 10) ≤ K * (3 * tangency ^ 10) := mul_le_mul_of_nonneg_right h4 h_pos
        have h_eq1 : 1 * (3 * tangency ^ 10) = 3 * tangency ^ 10 := by ring
        have h_eq2 : K * (3 * tangency ^ 10) = 3 * K * tangency ^ 10 := by ring
        rw [h_eq1, h_eq2] at h7; exact h7
      exact h5.trans h6
    have h3 : C0 ≤ 1000 * K * tangency ^ 10 := hC0_le
    calc (2 * tangency + 1 + C0)
        ≤ 3 * tangency + C0 := by linarith
      _ ≤ 3 * K * tangency ^ 10 + 1000 * K * tangency ^ 10 := by gcongr
      _ = 1003 * K * tangency ^ 10 := by ring
      _ ≤ 2000 * K * tangency ^ 10 := by
        have h_pos : 0 ≤ K * tangency ^ 10 := by positivity
        have h : (1003 : ℝ) ≤ 2000 := by norm_num
        have h2 : 1003 * (K * tangency ^ 10) ≤ 2000 * (K * tangency ^ 10) := mul_le_mul_of_nonneg_right h h_pos
        have h_eq1 : 1003 * (K * tangency ^ 10) = 1003 * K * tangency ^ 10 := by ring
        have h_eq2 : 2000 * (K * tangency ^ 10) = 2000 * K * tangency ^ 10 := by ring
        rw [h_eq1, h_eq2] at h2; exact h2

  have hM_le : V * delta ≤ V * d * r := by
    have h1 : delta = t * r := by
      rw [hr_def]; field_simp [ht.ne'] <;> ring
    have h2 : t ≤ d := by linarith
    have h3 : 0 ≤ V := hV_nonneg
    have h4 : V * t ≤ V * d := mul_le_mul_of_nonneg_left h2 h3
    have h5 : 0 ≤ r := by positivity
    have h6 : (V * t) * r ≤ (V * d) * r := mul_le_mul_of_nonneg_right h4 h5
    have h7 : V * delta = (V * t) * r := by
      have h71 : V * delta = V * (t * r) := by rw [h1]
      have h72 : V * (t * r) = (V * t) * r := by simp [mul_assoc]
      exact h71.trans h72
    have h8 : (V * d) * r = V * d * r := by simp [mul_assoc]
    calc V * delta = (V * t) * r := h7
      _ ≤ (V * d) * r := h6
      _ = V * d * r := h8

  have h_sqrt1000_ge30 : (30 : ℝ) ≤ Real.sqrt 1000 := by
    have h : (30 : ℝ) ^ 2 ≤ 1000 := by norm_num
    exact Real.le_sqrt_of_sq_le h

  exact enlarged_bounds_small_core hK htang hd_pos hV_nonneg hC0_nonneg hL_sq hM_le
    hterm1_bound hterm2_bound hr_bound hL_bound h_sqrt1000_ge30

/--
Intermediate arithmetic bound: the enlarged value+derivative expression is
bounded by `d * (2000/(K^2*T^30) + 2000/(30*K*T^15))`, which is stronger
than `d/K`. Used to prove `c_new ≥ d/(6*K)`.
Takes `V, L, C0, B, X` as explicit arguments with equality assumptions to
avoid `let`-binding unification issues.
-/
lemma enlarged_bounds_intermediate
    {K tangency delta t d V L C0 B X : ℝ}
    (hK : 1 ≤ K)
    (htang : 5 ≤ tangency)
    (hdelta : 0 < delta)
    (ht : 0 < t)
    (hdt : delta ≤ t)
    (hd_ge_2t : 2 * t ≤ d)
    (hd_le_K : d ≤ K)
    (h_small : tangency ^ 50 * delta ≤ t / (1000 * K ^ 4))
    (hV : V = 25 * tangency ^ 10 + 2 * tangency + 2)
    (hL : L = Real.sqrt (delta / t))
    (hC0 : C0 = 20 * K * V + 20 * K)
    (hB : B = C0 * L)
    (hX : X = (2 * tangency + 1) * d * L + d * B) :
    V * delta + X * B + X ≤ d * (2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15)) := by
  set V' := 25 * tangency ^ 10 + 2 * tangency + 2 with hV'_def
  set L' := Real.sqrt (delta / t) with hL'_def
  set C0' := 20 * K * V' + 20 * K with hC0'_def
  set r := delta / t with hr_def
  set B' := C0' * L' with hB'_def
  set X' := (2 * tangency + 1) * d * L' + d * B' with hX'_def

  have hK_pos : 0 < K := by linarith
  have htang_pos : 0 < tangency := by linarith
  have hd_pos : 0 < d := by linarith
  have hr_pos : 0 < r := by positivity
  have hL'_pos : 0 < L' := Real.sqrt_pos.mpr hr_pos
  have hL'_sq : L' ^ 2 = r := by
    rw [hL'_def]; exact Real.sq_sqrt (by positivity)
  have hV'_nonneg : 0 ≤ V' := by positivity
  have hC0'_nonneg : 0 ≤ C0' := by rw [hC0'_def]; nlinarith

  have hr_bound : r ≤ 1 / (1000 * K ^ 4 * tangency ^ 50) := by
    have h_pos1 : 0 < tangency ^ 50 * t := by positivity
    have h : (tangency ^ 50 * delta) / (tangency ^ 50 * t) ≤
        (t / (1000 * K ^ 4)) / (tangency ^ 50 * t) := by gcongr
    have h2 : (tangency ^ 50 * delta) / (tangency ^ 50 * t) = r := by
      rw [hr_def]; field_simp [htang_pos.ne', ht.ne'] <;> ring
    have h3 : (t / (1000 * K ^ 4)) / (tangency ^ 50 * t) =
        1 / (1000 * K ^ 4 * tangency ^ 50) := by
      field_simp [hK_pos.ne', htang_pos.ne', ht.ne'] <;> ring
    rw [h2, h3] at h; exact h

  have hL'_bound : L' ≤ 1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) := by
    have h4 : L' ≤ Real.sqrt (1 / (1000 * K ^ 4 * tangency ^ 50)) :=
      Real.sqrt_le_sqrt hr_bound
    have h_pos : 0 ≤ Real.sqrt 1000 * K ^ 2 * tangency ^ 25 := by positivity
    have h_sq : (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) ^ 2 =
        1000 * K ^ 4 * tangency ^ 50 := by
      have h7 : (Real.sqrt 1000) ^ 2 = 1000 := Real.sq_sqrt (by norm_num)
      calc (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) ^ 2
        = (Real.sqrt 1000) ^ 2 * (K ^ 2) ^ 2 * (tangency ^ 25) ^ 2 := by ring
      _ = 1000 * K ^ 4 * tangency ^ 50 := by rw [h7] <;> ring
    have h8 : Real.sqrt (1000 * K ^ 4 * tangency ^ 50) =
        Real.sqrt 1000 * K ^ 2 * tangency ^ 25 := by
      rw [←h_sq]; exact Real.sqrt_sq h_pos
    have h6 : Real.sqrt (1 / (1000 * K ^ 4 * tangency ^ 50)) =
        1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_one, h8]
    rw [h6] at h4; exact h4

  have h_tang_ge1 : 1 ≤ tangency := by linarith
  have h_pow10_ge1 : tangency ^ 10 ≥ 1 := by
    have h1 : 1 ≤ tangency := h_tang_ge1
    have h2 : (1 : ℝ)^10 ≤ tangency^10 := by gcongr
    simpa using h2
  have h_tang_le_pow10 : tangency ≤ tangency ^ 10 := by
    have h1 : tangency ^ 9 ≥ 1 := by
      have h1 : 1 ≤ tangency := h_tang_ge1
      have h2 : (1 : ℝ)^9 ≤ tangency^9 := by gcongr
      simpa using h2
    nlinarith

  have hV'_le : V' ≤ 30 * tangency ^ 10 := by
    rw [hV'_def]
    have h1 : 2 * tangency + 2 ≤ 5 * tangency ^ 10 := by
      have h2 : tangency ≤ tangency ^ 10 := h_tang_le_pow10
      nlinarith
    nlinarith

  have hC0'_le : C0' ≤ 1000 * K * tangency ^ 10 := by
    rw [hC0'_def]
    have h1 : 20 * K * V' ≤ 20 * K * (30 * tangency ^ 10) :=
      mul_le_mul_of_nonneg_left hV'_le (by nlinarith)
    have h2 : 20 * K ≤ 20 * K * tangency ^ 10 := by
      have h3 : 1 ≤ tangency ^ 10 := h_pow10_ge1
      have h4 : 0 ≤ 20 * K := by nlinarith
      calc 20 * K = 20 * K * 1 := by ring
        _ ≤ 20 * K * tangency ^ 10 := by gcongr
    have h_sum : 20 * K * V' + 20 * K ≤ 620 * K * tangency ^ 10 := by
      calc 20 * K * V' + 20 * K
          ≤ 20 * K * (30 * tangency ^ 10) + 20 * K * tangency ^ 10 := by
            exact add_le_add h1 h2
      _ = 620 * K * tangency ^ 10 := by ring
    have h_final : 620 * K * tangency ^ 10 ≤ 1000 * K * tangency ^ 10 := by
      have h_pos : 0 ≤ K * tangency ^ 10 := by positivity
      have h : (620 : ℝ) ≤ 1000 := by norm_num
      have h' : 620 * (K * tangency ^ 10) ≤ 1000 * (K * tangency ^ 10) :=
        mul_le_mul_of_nonneg_right h h_pos
      have h_eq1 : 620 * (K * tangency ^ 10) = 620 * K * tangency ^ 10 := by ring
      have h_eq2 : 1000 * (K * tangency ^ 10) = 1000 * K * tangency ^ 10 := by ring
      rw [h_eq1, h_eq2] at h'; exact h'
    exact h_sum.trans h_final

  have hterm1_bound : V' + (2 * tangency + 1) * C0' + C0' ^ 2 ≤
      2000000 * K ^ 2 * tangency ^ 20 :=
    enlargement_poly_bound1 hK htang V' C0' hV'_le hC0'_le hC0'_nonneg

  have hterm2_bound : (2 * tangency + 1 + C0') ≤ 2000 * K * tangency ^ 10 := by
    have h1 : 2 * tangency + 1 ≤ 3 * tangency := by linarith
    have h2 : 3 * tangency ≤ 3 * K * tangency ^ 10 := by
      have h3 : tangency ≤ tangency ^ 10 := h_tang_le_pow10
      have h4 : 1 ≤ K := by linarith
      have h5 : 3 * tangency ≤ 3 * tangency ^ 10 := mul_le_mul_of_nonneg_left h3 (by norm_num)
      have h6 : 3 * tangency ^ 10 ≤ 3 * K * tangency ^ 10 := by
        have h_pos : 0 ≤ 3 * tangency ^ 10 := by positivity
        have h7 : 1 * (3 * tangency ^ 10) ≤ K * (3 * tangency ^ 10) := mul_le_mul_of_nonneg_right h4 h_pos
        have h_eq1 : 1 * (3 * tangency ^ 10) = 3 * tangency ^ 10 := by ring
        have h_eq2 : K * (3 * tangency ^ 10) = 3 * K * tangency ^ 10 := by ring
        rw [h_eq1, h_eq2] at h7; exact h7
      exact h5.trans h6
    have h3 : C0' ≤ 1000 * K * tangency ^ 10 := hC0'_le
    calc (2 * tangency + 1 + C0')
        ≤ 3 * tangency + C0' := by linarith
      _ ≤ 3 * K * tangency ^ 10 + 1000 * K * tangency ^ 10 := by gcongr
      _ = 1003 * K * tangency ^ 10 := by ring
      _ ≤ 2000 * K * tangency ^ 10 := by
        have h_pos : 0 ≤ K * tangency ^ 10 := by positivity
        have h : (1003 : ℝ) ≤ 2000 := by norm_num
        have h2 : 1003 * (K * tangency ^ 10) ≤ 2000 * (K * tangency ^ 10) := mul_le_mul_of_nonneg_right h h_pos
        have h_eq1 : 1003 * (K * tangency ^ 10) = 1003 * K * tangency ^ 10 := by ring
        have h_eq2 : 2000 * (K * tangency ^ 10) = 2000 * K * tangency ^ 10 := by ring
        rw [h_eq1, h_eq2] at h2; exact h2

  have hM_le : V' * delta ≤ V' * d * r := by
    have h1 : delta = t * r := by
      rw [hr_def]; field_simp [ht.ne'] <;> ring
    have h2 : t ≤ d := by linarith
    have h3 : 0 ≤ V' := hV'_nonneg
    have h4 : V' * t ≤ V' * d := mul_le_mul_of_nonneg_left h2 h3
    have h5 : 0 ≤ r := by positivity
    have h6 : (V' * t) * r ≤ (V' * d) * r := mul_le_mul_of_nonneg_right h4 h5
    have h7 : V' * delta = (V' * t) * r := by
      have h71 : V' * delta = V' * (t * r) := by rw [h1]
      have h72 : V' * (t * r) = (V' * t) * r := by simp [mul_assoc]
      exact h71.trans h72
    have h8 : (V' * d) * r = V' * d * r := by simp [mul_assoc]
    calc V' * delta = (V' * t) * r := h7
      _ ≤ (V' * d) * r := h6
      _ = V' * d * r := h8

  have h_sqrt1000_ge30 : (30 : ℝ) ≤ Real.sqrt 1000 := by
    have h : (30 : ℝ) ^ 2 ≤ 1000 := by norm_num
    exact Real.le_sqrt_of_sq_le h

  have h_main_ineq : V' * delta + X' * B' + X' ≤
      d * (r * (V' + (2 * tangency + 1) * C0' + C0' ^ 2) + L' * (2 * tangency + 1 + C0')) :=
    enlargement_main_ineq hL'_sq hM_le

  have h1_div : r * (V' + (2 * tangency + 1) * C0' + C0' ^ 2) ≤
      2000 / (K ^ 2 * tangency ^ 30) :=
    enlargement_div_bound1' hK htang hV'_nonneg hC0'_nonneg hterm1_bound hr_bound

  have h2_div : L' * (2 * tangency + 1 + C0') ≤ 2000 / (30 * K * tangency ^ 15) :=
    enlargement_div_bound2' hK htang hC0'_nonneg hterm2_bound hL'_bound h_sqrt1000_ge30

  have h_main : V' * delta + X' * B' + X' ≤ d * (2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15)) := by
    calc V' * delta + X' * B' + X'
      ≤ d * (r * (V' + (2 * tangency + 1) * C0' + C0' ^ 2) + L' * (2 * tangency + 1 + C0')) := h_main_ineq
    _ = d * (r * (V' + (2 * tangency + 1) * C0' + C0' ^ 2)) + d * (L' * (2 * tangency + 1 + C0')) := by ring
    _ ≤ d * (2000 / (K ^ 2 * tangency ^ 30)) + d * (2000 / (30 * K * tangency ^ 15)) := by gcongr <;> linarith
    _ = d * (2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15)) := by ring

  have hV_eq : V = V' := by rw [hV, hV'_def]
  have hL_eq : L = L' := by rw [hL, hL'_def]
  have hC0_eq : C0 = C0' := by
    rw [hC0, hC0'_def, hV_eq]
  have hB_eq : B = B' := by
    rw [hB, hB'_def, hC0_eq, hL_eq]
  have hX_eq : X = X' := by
    rw [hX, hX'_def, hL_eq, hB_eq]
  rw [hV_eq, hX_eq, hB_eq]
  exact h_main

lemma helper_pow30_bound (K tangency : ℝ) (hK : 1 ≤ K) (htang : 5 ≤ tangency) :
    K ^ 2 * tangency ^ 30 ≥ 24000 * K := by
  have h1 : tangency ^ 30 ≥ (5 : ℝ)^30 := by gcongr <;> linarith
  have h2 : (5 : ℝ)^30 ≥ 24000 := by norm_num
  have h3 : tangency ^ 30 ≥ 24000 := by linarith
  have h4 : K ^ 2 ≥ K := by nlinarith
  have h5 : K ^ 2 * tangency ^ 30 ≥ K * 24000 :=
    mul_le_mul h4 h3 (by positivity) (by linarith)
  linarith

lemma helper_pow15_bound (K tangency : ℝ) (hK : 1 ≤ K) (htang : 5 ≤ tangency) :
    30 * K * tangency ^ 15 ≥ 24000 * K := by
  have h1 : tangency ^ 15 ≥ (5 : ℝ)^15 := by gcongr <;> linarith
  have h2 : (5 : ℝ)^15 ≥ 800 := by norm_num
  have h3 : tangency ^ 15 ≥ 800 := by linarith
  have h4 : 30 * K * tangency ^ 15 ≥ 30 * K * 800 := by gcongr
  have h5 : 30 * K * 800 = 24000 * K := by ring
  rw [h5] at h4
  exact h4

lemma helper_div_sum_le_6K (K tangency : ℝ) (hK : 1 ≤ K) (htang : 5 ≤ tangency) :
    2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15) ≤ 1 / (6 * K) := by
  have hK_pos : 0 < K := by linarith
  have h6 : K ^ 2 * tangency ^ 30 ≥ 24000 * K := helper_pow30_bound K tangency hK htang
  have h7 : 30 * K * tangency ^ 15 ≥ 24000 * K := helper_pow15_bound K tangency hK htang
  have h_pos1 : 0 < K ^ 2 * tangency ^ 30 := by positivity
  have h_pos2 : 0 < 12 * K := by positivity
  have h_pos3 : 0 < 30 * K * tangency ^ 15 := by positivity
  have h8 : 2000 / (K ^ 2 * tangency ^ 30) ≤ 1 / (12 * K) := by
    have h9 : K ^ 2 * tangency ^ 30 ≥ 2000 * (12 * K) := by
      have h10 : 2000 * (12 * K) = 24000 * K := by ring
      rw [h10]; exact h6
    have h11 : 2000 / (K ^ 2 * tangency ^ 30) ≤ 2000 / (2000 * (12 * K)) := by gcongr
    have h12 : 2000 / (2000 * (12 * K)) = 1 / (12 * K) := by
      field_simp [h_pos2.ne'] <;> ring
    rw [h12] at h11
    exact h11
  have h9 : 2000 / (30 * K * tangency ^ 15) ≤ 1 / (12 * K) := by
    have h10 : 30 * K * tangency ^ 15 ≥ 2000 * (12 * K) := by
      have h11 : 2000 * (12 * K) = 24000 * K := by ring
      rw [h11]; exact h7
    have h12 : 2000 / (30 * K * tangency ^ 15) ≤ 2000 / (2000 * (12 * K)) := by gcongr
    have h13 : 2000 / (2000 * (12 * K)) = 1 / (12 * K) := by
      field_simp [h_pos2.ne'] <;> ring
    rw [h13] at h12
    exact h12
  have h10 : 2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15) ≤
      1 / (12 * K) + 1 / (12 * K) := by gcongr
  have h11 : 1 / (12 * K) + 1 / (12 * K) = 1 / (6 * K) := by
    field_simp [hK_pos.ne'] <;> ring
  rw [h11] at h10
  exact h10

/-- Stronger bound: the enlarged expression is at most `d/(6K)`. -/
lemma enlarged_bounds_le_6K
    {K tangency delta t d : ℝ}
    (hK : 1 ≤ K) (htang : 5 ≤ tangency) (hdelta : 0 < delta) (ht : 0 < t)
    (hdt : delta ≤ t) (hd_ge_2t : 2 * t ≤ d) (hd_le_K : d ≤ K)
    (h_small : tangency ^ 50 * delta ≤ t / (1000 * K ^ 4)) :
    let V := 25 * tangency ^ 10 + 2 * tangency + 2
    let L := Real.sqrt (delta / t)
    let C0 := 20 * K * V + 20 * K
    let B := C0 * L
    V * delta + ((2 * tangency + 1) * d * L + d * B) * B +
      ((2 * tangency + 1) * d * L + d * B) ≤ d / (6 * K) := by
  dsimp only
  set V := 25 * tangency ^ 10 + 2 * tangency + 2 with hV_def
  set L := Real.sqrt (delta / t) with hL_def
  set C0 := 20 * K * V + 20 * K with hC0_def
  set r := delta / t with hr_def
  set B := C0 * L with hB_def
  have hK_pos : 0 < K := by linarith
  have htang_pos : 0 < tangency := by linarith
  have hd_pos : 0 < d := by linarith
  have hr_pos : 0 < r := by positivity
  have hL_pos : 0 < L := Real.sqrt_pos.mpr hr_pos
  have hL_sq : L ^ 2 = r := by
    rw [hL_def]; exact Real.sq_sqrt (by positivity)
  have hV_nonneg : 0 ≤ V := by positivity
  have hC0_nonneg : 0 ≤ C0 := by rw [hC0_def]; positivity
  have h_tang_ge1 : 1 ≤ tangency := by linarith
  have h_pow10_ge1 : tangency ^ 10 ≥ 1 := by
    have h1 : (1 : ℝ)^10 ≤ tangency^10 := by gcongr
    simpa using h1
  have h_tang_le_pow10 : tangency ≤ tangency ^ 10 := by
    have h1 : tangency ^ 9 ≥ 1 := by
      have h2 : (1 : ℝ)^9 ≤ tangency^9 := by gcongr
      simpa using h2
    nlinarith
  have hV_le : V ≤ 30 * tangency ^ 10 := by
    rw [hV_def]
    have h1 : 2 * tangency + 2 ≤ 5 * tangency ^ 10 := by
      have h2 : tangency ≤ tangency ^ 10 := h_tang_le_pow10
      nlinarith
    nlinarith
  have hC0_le : C0 ≤ 1000 * K * tangency ^ 10 := by
    rw [hC0_def]
    have h1 : 20 * K * V ≤ 20 * K * (30 * tangency ^ 10) := by gcongr
    have h2 : 20 * K ≤ 20 * K * tangency ^ 10 := by
      have h3 : 1 ≤ tangency ^ 10 := h_pow10_ge1
      have h4 : 0 ≤ 20 * K := by positivity
      calc 20 * K = 20 * K * 1 := by ring
        _ ≤ 20 * K * tangency ^ 10 := by gcongr
    have h_sum : 20 * K * V + 20 * K ≤ 620 * K * tangency ^ 10 := by
      calc 20 * K * V + 20 * K
          ≤ 20 * K * (30 * tangency ^ 10) + 20 * K * tangency ^ 10 := by gcongr
        _ = 620 * K * tangency ^ 10 := by ring
    have h_final : 620 * K * tangency ^ 10 ≤ 1000 * K * tangency ^ 10 := by
      have h_pos : 0 ≤ K * tangency ^ 10 := by positivity
      have h : (620 : ℝ) ≤ 1000 := by norm_num
      nlinarith
    exact h_sum.trans h_final
  have hterm1_bound : V + (2 * tangency + 1) * C0 + C0 ^ 2 ≤
      2000000 * K ^ 2 * tangency ^ 20 :=
    enlargement_poly_bound1 hK htang V C0 hV_le hC0_le hC0_nonneg
  have hterm2_bound : (2 * tangency + 1 + C0) ≤ 2000 * K * tangency ^ 10 := by
    have h1 : 2 * tangency + 1 ≤ 3 * tangency := by linarith
    have h2 : 3 * tangency ≤ 3 * K * tangency ^ 10 := by
      have h3 : tangency ≤ tangency ^ 10 := h_tang_le_pow10
      have h4 : 1 ≤ K := by linarith
      have h5 : 3 * tangency ≤ 3 * tangency ^ 10 := mul_le_mul_of_nonneg_left h3 (by norm_num)
      have h6 : 3 * tangency ^ 10 ≤ 3 * K * tangency ^ 10 := by
        have h_pos : 0 ≤ 3 * tangency ^ 10 := by positivity
        have h7 : 1 * (3 * tangency ^ 10) ≤ K * (3 * tangency ^ 10) := mul_le_mul_of_nonneg_right h4 h_pos
        have h_eq1 : 1 * (3 * tangency ^ 10) = 3 * tangency ^ 10 := by ring
        have h_eq2 : K * (3 * tangency ^ 10) = 3 * K * tangency ^ 10 := by ring
        rw [h_eq1, h_eq2] at h7; exact h7
      exact h5.trans h6
    calc (2 * tangency + 1 + C0)
        ≤ 3 * tangency + C0 := by linarith
      _ ≤ 3 * K * tangency ^ 10 + 1000 * K * tangency ^ 10 := by gcongr
      _ = 1003 * K * tangency ^ 10 := by ring
      _ ≤ 2000 * K * tangency ^ 10 := by nlinarith
  have hr_bound : r ≤ 1 / (1000 * K ^ 4 * tangency ^ 50) := by
    have h_pos1 : 0 < tangency ^ 50 * t := by positivity
    have h : (tangency ^ 50 * delta) / (tangency ^ 50 * t) ≤
        (t / (1000 * K ^ 4)) / (tangency ^ 50 * t) := by gcongr
    have h2 : (tangency ^ 50 * delta) / (tangency ^ 50 * t) = r := by
      rw [hr_def]; field_simp [htang_pos.ne', ht.ne'] <;> ring
    have h3 : (t / (1000 * K ^ 4)) / (tangency ^ 50 * t) =
        1 / (1000 * K ^ 4 * tangency ^ 50) := by
      field_simp [hK_pos.ne', htang_pos.ne', ht.ne'] <;> ring
    rw [h2, h3] at h; exact h
  have hL_bound : L ≤ 1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) := by
    have h4 : L ≤ Real.sqrt (1 / (1000 * K ^ 4 * tangency ^ 50)) := Real.sqrt_le_sqrt hr_bound
    have h_pos : 0 ≤ Real.sqrt 1000 * K ^ 2 * tangency ^ 25 := by positivity
    have h_sq : (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) ^ 2 = 1000 * K ^ 4 * tangency ^ 50 := by
      have h7 : (Real.sqrt 1000) ^ 2 = 1000 := Real.sq_sqrt (by norm_num)
      calc (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) ^ 2
        = (Real.sqrt 1000) ^ 2 * (K ^ 2) ^ 2 * (tangency ^ 25) ^ 2 := by ring
      _ = 1000 * K ^ 4 * tangency ^ 50 := by rw [h7] <;> ring
    have h8 : Real.sqrt (1000 * K ^ 4 * tangency ^ 50) = Real.sqrt 1000 * K ^ 2 * tangency ^ 25 := by
      rw [←h_sq]; exact Real.sqrt_sq h_pos
    have h6 : Real.sqrt (1 / (1000 * K ^ 4 * tangency ^ 50)) = 1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_one, h8]
    rw [h6] at h4; exact h4
  have h_sqrt1000_ge30 : (30 : ℝ) ≤ Real.sqrt 1000 := by
    have h : (30 : ℝ) ^ 2 ≤ 1000 := by norm_num
    exact Real.le_sqrt_of_sq_le h
  have hM_le : V * delta ≤ V * d * r := by
    have h1 : delta = t * r := by
      rw [hr_def]; field_simp [ht.ne'] <;> ring
    have h2 : t ≤ d := by linarith
    have h3 : 0 ≤ V := hV_nonneg
    have h4 : V * t ≤ V * d := mul_le_mul_of_nonneg_left h2 h3
    have h5 : 0 ≤ r := by positivity
    have h6 : (V * t) * r ≤ (V * d) * r := mul_le_mul_of_nonneg_right h4 h5
    have h7 : V * delta = (V * t) * r := by rw [h1]; ring
    rw [h7]; exact h6
  have h_main_ineq := enlargement_main_ineq (V := V) (C0 := C0) (d := d) (L := L) (r := r) (tangency := tangency) (delta := delta) hL_sq hM_le
  have h1_div := enlargement_div_bound1' hK htang hV_nonneg hC0_nonneg hterm1_bound hr_bound
  have h2_div := enlargement_div_bound2' hK htang hC0_nonneg hterm2_bound hL_bound h_sqrt1000_ge30
  have h_bound : r * (V + (2 * tangency + 1) * C0 + C0 ^ 2) + L * (2 * tangency + 1 + C0) ≤
      2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15) := by
    linarith [h1_div, h2_div]
  have h4 : 2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15) ≤ 1 / (6 * K) :=
    helper_div_sum_le_6K K tangency hK htang
  have h5 : V * delta + ((2 * tangency + 1) * d * L + d * B) * B +
        ((2 * tangency + 1) * d * L + d * B) ≤
      d * (r * (V + (2 * tangency + 1) * C0 + C0 ^ 2) + L * (2 * tangency + 1 + C0)) := by
    simpa [hB_def] using h_main_ineq
  have h6 : d * (r * (V + (2 * tangency + 1) * C0 + C0 ^ 2) + L * (2 * tangency + 1 + C0)) ≤
      d * (2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15)) := by
    exact mul_le_mul_of_nonneg_left h_bound (by positivity)
  have h7 : d * (2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15)) ≤ d / (6 * K) := by
    have h8 : d * (2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15)) ≤ d * (1 / (6 * K)) := by gcongr
    have h9 : d * (1 / (6 * K)) = d / (6 * K) := by ring
    rw [h9] at h8
    exact h8
  exact h5.trans (h6.trans h7)

/-- Wrapper for `enlarged_bounds_le_6K` with explicit `V, L, C0, B`. -/
lemma enlarged_bounds_le_6K_explicit
    {K tangency delta t d V L C0 B X : ℝ}
    (hK : 1 ≤ K) (htang : 5 ≤ tangency) (hdelta : 0 < delta) (ht : 0 < t)
    (hdt : delta ≤ t) (hd_ge_2t : 2 * t ≤ d) (hd_le_K : d ≤ K)
    (h_small : tangency ^ 50 * delta ≤ t / (1000 * K ^ 4))
    (hV : V = 25 * tangency ^ 10 + 2 * tangency + 2)
    (hL : L = Real.sqrt (delta / t))
    (hC0 : C0 = 20 * K * V + 20 * K)
    (hB : B = C0 * L)
    (hX : X = (2 * tangency + 1) * d * L + d * B) :
    V * delta + X * B + X ≤ d / (6 * K) := by
  have h_intermediate : V * delta + X * B + X ≤ d * (2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15)) :=
    enlarged_bounds_intermediate hK htang hdelta ht hdt hd_ge_2t hd_le_K h_small hV hL hC0 hB hX
  have h4 : 2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15) ≤ 1 / (6 * K) := by
    have hK_pos : 0 < K := by linarith
    have h_tang30 : tangency ^ 30 ≥ (5 : ℝ)^30 := by gcongr <;> linarith
    have h_tang15 : tangency ^ 15 ≥ (5 : ℝ)^15 := by gcongr <;> linarith
    have h61 : K ^ 2 * tangency ^ 30 ≥ 24000 * K := by
      have h8 : (5 : ℝ)^30 ≥ 24000 := by norm_num
      have h9 : K ^ 2 ≥ K := by nlinarith
      nlinarith
    have h62 : 30 * K * tangency ^ 15 ≥ 24000 * K := by
      have h8 : (5 : ℝ)^15 ≥ 800 := by norm_num
      nlinarith
    have h_pos1 : 0 < K ^ 2 * tangency ^ 30 := by positivity
    have h_pos2 : 0 < 12 * K := by positivity
    have h_pos3 : 0 < 30 * K * tangency ^ 15 := by positivity
    have h51 : 2000 / (K ^ 2 * tangency ^ 30) ≤ 1 / (12 * K) := by
      have h7 : 2000 * (12 * K) ≤ K ^ 2 * tangency ^ 30 := by linarith
      have h_pos4 : 0 < 2000 * (12 * K) := by positivity
      have h : 2000 / (K ^ 2 * tangency ^ 30) ≤ 2000 / (2000 * (12 * K)) :=
        div_le_div_of_nonneg_left (by norm_num) h_pos4 h7
      have h2 : 2000 / (2000 * (12 * K)) = 1 / (12 * K) := by
        field_simp [hK_pos.ne'] <;> ring
      rw [h2] at h
      exact h
    have h52 : 2000 / (30 * K * tangency ^ 15) ≤ 1 / (12 * K) := by
      have h7 : 2000 * (12 * K) ≤ 30 * K * tangency ^ 15 := by linarith
      have h_pos4 : 0 < 2000 * (12 * K) := by positivity
      have h : 2000 / (30 * K * tangency ^ 15) ≤ 2000 / (2000 * (12 * K)) :=
        div_le_div_of_nonneg_left (by norm_num) h_pos4 h7
      have h2 : 2000 / (2000 * (12 * K)) = 1 / (12 * K) := by
        field_simp [hK_pos.ne'] <;> ring
      rw [h2] at h
      exact h
    have h_sum : 2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15) ≤ 1 / (12 * K) + 1 / (12 * K) := by
      exact add_le_add h51 h52
    have h_final : 1 / (12 * K) + 1 / (12 * K) = 1 / (6 * K) := by
      field_simp [hK_pos.ne'] <;> ring
    rw [h_final] at h_sum
    exact h_sum
  have h5 : V * delta + X * B + X ≤ d * (1 / (6 * K)) := by
    have h_pos : 0 ≤ d := by linarith
    exact h_intermediate.trans (mul_le_mul_of_nonneg_left h4 h_pos)
  have h6 : d * (1 / (6 * K)) = d / (6 * K) := by ring
  rw [h6] at h5
  exact h5

/-- Explicit-argument wrapper for the strict enlarged bound. -/
lemma enlarged_bounds_small_explicit
    {K tangency delta t d V L C0 B X : ℝ}
    (hK : 1 ≤ K) (htang : 5 ≤ tangency) (hdelta : 0 < delta) (ht : 0 < t)
    (hdt : delta ≤ t) (hd_ge_2t : 2 * t ≤ d) (hd_le_K : d ≤ K)
    (h_small : tangency ^ 50 * delta ≤ t / (1000 * K ^ 4))
    (hV : V = 25 * tangency ^ 10 + 2 * tangency + 2)
    (hL : L = Real.sqrt (delta / t))
    (hC0 : C0 = 20 * K * V + 20 * K)
    (hB : B = C0 * L)
    (hX : X = (2 * tangency + 1) * d * L + d * B) :
    V * delta + X * B + X < d / K := by
  have h_intermediate : V * delta + X * B + X ≤ d * (2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15)) :=
    enlarged_bounds_intermediate hK htang hdelta ht hdt hd_ge_2t hd_le_K h_small hV hL hC0 hB hX
  have h_fraction_lt : 2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15) < 1 / K := by
    have hK_pos : 0 < K := by linarith
    have h_factor : 2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15) =
        (1 / K) * (2000 / (K * tangency ^ 30) + 2000 / (30 * tangency ^ 15)) := by
      field_simp [hK_pos.ne'] <;> ring
    rw [h_factor]
    have h_sum := enlargement_sum_bound hK htang
    have hK_pos : 0 < K := by
      have h1 : (0 : ℝ) < 1 := by norm_num
      exact lt_of_lt_of_le h1 hK
    have h_pos : 0 < 1 / K := by positivity
    have h : (1 / K) * (2000 / (K * tangency ^ 30) + 2000 / (30 * tangency ^ 15)) < (1 / K) * (1 : ℝ) :=
      mul_lt_mul_of_pos_left h_sum h_pos
    have h2 : (1 / K) * (1 : ℝ) = 1 / K := by ring
    rw [h2] at h
    exact h
  have hK_pos2 : 0 < d := by linarith [hd_ge_2t, ht]
  calc V * delta + X * B + X
    ≤ d * (2000 / (K ^ 2 * tangency ^ 30) + 2000 / (30 * K * tangency ^ 15)) := h_intermediate
  _ < d * (1 / K) := by exact mul_lt_mul_of_pos_left h_fraction_lt hK_pos2
  _ = d / K := by ring

lemma directional_lens_M_plus_S_le
    (M_enl S_enl B V delta d L tangency K X M_core : ℝ)
    (hM_enl_def : M_enl = M_core + S_enl * B)
    (hM_core_def : M_core = 2 * tangency * delta)
    (hV_def : V = 25 * tangency ^ 10 + 2 * tangency + 2)
    (hS_le : S_enl ≤ X)
    (hB_nonneg : 0 ≤ B)
    (hdelta : 0 < delta) (htang : 5 ≤ tangency) :
    M_enl + S_enl ≤ V * delta + X * B + X := by
  have h1 : M_core ≤ V * delta := by
    rw [hM_core_def, hV_def]
    have h_pos : 0 ≤ delta := by linarith
    have h2 : 2 * tangency ≤ 25 * tangency ^ 10 + 2 * tangency + 2 := by
      have h3 : 0 ≤ tangency := by linarith
      nlinarith [pow_nonneg h3 10]
    nlinarith
  have h2 : S_enl * B ≤ X * B := mul_le_mul_of_nonneg_right hS_le hB_nonneg
  have h3 : S_enl ≤ X := hS_le
  have h4 : M_enl = M_core + S_enl * B := hM_enl_def
  linarith

/-! ### Lemma 5: Convex/concave growth forces sign change -/

/--
If `h'' ≥ c > 0`, `|h(x0)| ≤ M`, `|h'(x0)| ≤ S` with `S > 0`, and
`B ≥ 2*S/c + sqrt(2*M/c)`, then `h(x0±B) > 0` when `h(x0) < 0`.
-/
lemma convex_sign_change_at_distance
    {h h' h'' : ℝ → ℝ} {x0 B c M S : ℝ}
    (hc_pos : 0 < c)
    (hS_pos : 0 < S)
    (hB_pos : 0 < B)
    (h_cont : ContinuousOn h (Icc (x0 - B) (x0 + B)))
    (h'_cont : ContinuousOn h' (Icc (x0 - B) (x0 + B)))
    (h_deriv : ∀ x ∈ Ioo (x0 - B) (x0 + B), HasDerivAt h (h' x) x)
    (h'_deriv : ∀ x ∈ Ioo (x0 - B) (x0 + B), HasDerivAt h' (h'' x) x)
    (h''_ge : ∀ x ∈ Ioo (x0 - B) (x0 + B), c ≤ h'' x)
    (hx0_val : |h x0| ≤ M)
    (hx0_deriv : |h' x0| ≤ S)
    (hx0_neg : h x0 < 0)
    (hB_large : B ≥ 2 * S / c + Real.sqrt (2 * M / c)) :
    h (x0 + B) > 0 ∧ h (x0 - B) > 0 := by
  let a := x0 - B
  let b := x0 + B
  have hab : a < b := by dsimp only [a, b]; linarith
  have hx0_in : x0 ∈ Ioo a b := by
    dsimp only [a, b]; exact ⟨by linarith, by linarith⟩
  have hright_in : b ∈ Icc a b := by
    dsimp only [a, b]; exact ⟨by linarith, le_rfl⟩
  have hleft_in : a ∈ Icc a b := by
    dsimp only [a, b]; exact ⟨le_rfl, by linarith⟩

  have hM_pos : 0 < M := by
    have h1 : |h x0| > 0 := by
      have h2 : h x0 ≠ 0 := by linarith
      exact abs_pos.mpr h2
    have h3 : |h x0| ≤ M := hx0_val
    linarith

  have h_sqrt_add_lt : ∀ (x y : ℝ), 0 < x → 0 < y →
      Real.sqrt (x + y) < Real.sqrt x + Real.sqrt y := by
    intro x y hx hy
    have h1 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    have h2 : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
    have h3 : 0 < Real.sqrt x * Real.sqrt y := mul_pos h1 h2
    have h4 : (Real.sqrt x + Real.sqrt y) ^ 2 = x + y + 2 * (Real.sqrt x * Real.sqrt y) := by
      calc (Real.sqrt x + Real.sqrt y) ^ 2
          = (Real.sqrt x) ^ 2 + (Real.sqrt y) ^ 2 + 2 * (Real.sqrt x * Real.sqrt y) := by ring
        _ = x + y + 2 * (Real.sqrt x * Real.sqrt y) := by
          rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)] <;> ring
    have h5 : x + y < (Real.sqrt x + Real.sqrt y) ^ 2 := by
      rw [h4]; linarith
    have h6 : 0 ≤ x + y := by linarith
    have h7 : 0 ≤ Real.sqrt x + Real.sqrt y := by positivity
    have h8 : Real.sqrt (x + y) < Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) :=
      Real.sqrt_lt_sqrt h6 h5
    have h9 : Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) = Real.sqrt x + Real.sqrt y := by
      rw [Real.sqrt_sq_eq_abs]; rw [abs_of_nonneg h7]
    rw [h9] at h8; exact h8

  have hS2_pos : 0 < S ^ 2 := by positivity
  have h2cM_pos : 0 < 2 * c * M := by positivity

  have h_root2 : Real.sqrt (2 * c * M) = c * Real.sqrt (2 * M / c) := by
    have h4 : 0 ≤ c := by linarith
    have h5 : c ^ 2 * (2 * M / c) = 2 * c * M := by
      field_simp [hc_pos.ne'] <;> ring
    have h6 : Real.sqrt (2 * c * M) = Real.sqrt (c ^ 2 * (2 * M / c)) := by rw [h5]
    rw [h6, Real.sqrt_mul (by positivity)]
    have h7 : Real.sqrt (c ^ 2) = c := by
      rw [Real.sqrt_sq_eq_abs]; rw [abs_of_nonneg h4]
    rw [h7] <;> ring

  have hS_sqrt : Real.sqrt (S ^ 2) = S := by
    rw [Real.sqrt_sq_eq_abs]; rw [abs_of_pos hS_pos]
  have h10 : Real.sqrt (S ^ 2 + 2 * c * M) < S + Real.sqrt (2 * c * M) := by
    have h := h_sqrt_add_lt (S ^ 2) (2 * c * M) hS2_pos h2cM_pos
    rw [hS_sqrt] at h; exact h

  have h11 : S + Real.sqrt (S ^ 2 + 2 * c * M) <
      2 * S + c * Real.sqrt (2 * M / c) := by
    rw [h_root2] at *
    <;> linarith

  have h_strict : B > (S + Real.sqrt (S ^ 2 + 2 * c * M)) / c := by
    have h13 : (S + Real.sqrt (S ^ 2 + 2 * c * M)) / c <
        2 * S / c + Real.sqrt (2 * M / c) := by
      have h14 : 0 < c := hc_pos
      calc (S + Real.sqrt (S ^ 2 + 2 * c * M)) / c
          < (2 * S + c * Real.sqrt (2 * M / c)) / c := by gcongr
        _ = 2 * S / c + Real.sqrt (2 * M / c) := by
          field_simp [h14.ne'] <;> ring
    have h9 : B ≥ 2 * S / c + Real.sqrt (2 * M / c) := hB_large
    linarith

  have h_quad : (c / 2) * B ^ 2 - S * B - M > 0 := by
    have h14 : 0 < c := hc_pos
    have h15 : B - S / c > Real.sqrt (S ^ 2 + 2 * c * M) / c := by
      have h16 : (S + Real.sqrt (S ^ 2 + 2 * c * M)) / c = S / c + Real.sqrt (S ^ 2 + 2 * c * M) / c := by
        field_simp [h14.ne'] <;> ring
      rw [h16] at h_strict
      linarith
    have h17 : 0 < B - S / c := by
      have h_pos2 : 0 < Real.sqrt (S ^ 2 + 2 * c * M) / c := by positivity
      linarith [h15, h_pos2]
    have h18 : (B - S / c) ^ 2 > (Real.sqrt (S ^ 2 + 2 * c * M) / c) ^ 2 := by
      gcongr <;> positivity
    have h19 : (Real.sqrt (S ^ 2 + 2 * c * M) / c) ^ 2 = (S ^ 2 + 2 * c * M) / c ^ 2 := by
      have h20 : (Real.sqrt (S ^ 2 + 2 * c * M)) ^ 2 = S ^ 2 + 2 * c * M := by
        rw [Real.sq_sqrt (by positivity)]
      field_simp [h14.ne'] <;> nlinarith
    have h21 : (c / 2) * (B - S / c) ^ 2 > (c / 2) * ((S ^ 2 + 2 * c * M) / c ^ 2) := by
      have h_c2 : 0 < c / 2 := by linarith
      have h_ineq : (B - S / c) ^ 2 > (S ^ 2 + 2 * c * M) / c ^ 2 := by
        rw [h19] at h18; exact h18
      exact mul_lt_mul_of_pos_left h_ineq h_c2
    have h22 : (c / 2) * ((S ^ 2 + 2 * c * M) / c ^ 2) = S ^ 2 / (2 * c) + M := by
      field_simp [h14.ne'] <;> ring
    have h23 : (c / 2) * B ^ 2 - S * B - M = (c / 2) * (B - S / c) ^ 2 - (S ^ 2 / (2 * c) + M) := by
      field_simp [h14.ne'] <;> ring
    rw [h23]
    linarith [h21, h22]

  have hB_nonneg : 0 ≤ B := by linarith

  have h_b_diff : b - x0 = B := by dsimp only [b]; linarith
  have h_lower_right : h b ≥ h x0 + h' x0 * B + (c / 2) * B ^ 2 := by
    have h := convex_value_lower_bound hab hc_pos h_cont h'_cont h_deriv h'_deriv
      (fun x hx => h''_ge x hx) hx0_in hright_in
    rw [h_b_diff] at h; exact h

  have h_right_pos : h b > 0 := by
    have h3 : h x0 ≥ -M := (abs_le.mp hx0_val).1
    have h6 : h' x0 * B ≥ -S * B := by
      have h7 : h' x0 ≥ -S := (abs_le.mp hx0_deriv).1
      exact mul_le_mul_of_nonneg_right h7 hB_nonneg
    have h9 : -M - S * B + (c / 2) * B ^ 2 > 0 := by linarith [h_quad]
    have h10 : h b ≥ h x0 + h' x0 * B + (c / 2) * B ^ 2 := h_lower_right
    linarith

  have h_a_diff : a - x0 = -B := by dsimp only [a]; linarith
  have h_lower_left : h a ≥ h x0 + h' x0 * (-B) + (c / 2) * (-B) ^ 2 := by
    have h := convex_value_lower_bound hab hc_pos h_cont h'_cont h_deriv h'_deriv
      (fun x hx => h''_ge x hx) hx0_in hleft_in
    rw [h_a_diff] at h; exact h

  have h_left_pos : h a > 0 := by
    have h1 : h a ≥ h x0 + h' x0 * (-B) + (c / 2) * (-B) ^ 2 := h_lower_left
    have h1' : h x0 + h' x0 * (-B) + (c / 2) * (-B) ^ 2 = h x0 - h' x0 * B + (c / 2) * B ^ 2 := by ring
    have h2 : h a ≥ h x0 - h' x0 * B + (c / 2) * B ^ 2 := by
      rw [h1'] at h1; exact h1
    have h3 : h x0 ≥ -M := (abs_le.mp hx0_val).1
    have h7 : h' x0 ≤ S := (abs_le.mp hx0_deriv).2
    have h8 : -h' x0 * B ≥ -S * B := by
      have h9 : -S ≤ -h' x0 := by linarith
      exact mul_le_mul_of_nonneg_right h9 hB_nonneg
    have h10 : -M - S * B + (c / 2) * B ^ 2 > 0 := by linarith [h_quad]
    linarith

  exact ⟨h_right_pos, h_left_pos⟩

/-- Concave counterpart: h(x0±B) < 0 when h(x0) > 0. -/
lemma concave_sign_change_at_distance
    {h h' h'' : ℝ → ℝ} {x0 B c M S : ℝ}
    (hc_pos : 0 < c)
    (hS_pos : 0 < S)
    (hB_pos : 0 < B)
    (h_cont : ContinuousOn h (Icc (x0 - B) (x0 + B)))
    (h'_cont : ContinuousOn h' (Icc (x0 - B) (x0 + B)))
    (h_deriv : ∀ x ∈ Ioo (x0 - B) (x0 + B), HasDerivAt h (h' x) x)
    (h'_deriv : ∀ x ∈ Ioo (x0 - B) (x0 + B), HasDerivAt h' (h'' x) x)
    (h''_le : ∀ x ∈ Ioo (x0 - B) (x0 + B), h'' x ≤ -c)
    (hx0_val : |h x0| ≤ M)
    (hx0_deriv : |h' x0| ≤ S)
    (hx0_pos : 0 < h x0)
    (hB_large : B ≥ 2 * S / c + Real.sqrt (2 * M / c)) :
    h (x0 + B) < 0 ∧ h (x0 - B) < 0 := by
  let g : ℝ → ℝ := fun x => -h x
  let g' : ℝ → ℝ := fun x => -h' x
  let g'' : ℝ → ℝ := fun x => -h'' x
  have hg_cont : ContinuousOn g (Icc (x0 - B) (x0 + B)) := h_cont.neg
  have hg'_cont : ContinuousOn g' (Icc (x0 - B) (x0 + B)) := h'_cont.neg
  have hg_deriv : ∀ x ∈ Ioo (x0 - B) (x0 + B), HasDerivAt g (g' x) x := by
    intro x hx; exact (h_deriv x hx).neg
  have hg'_deriv : ∀ x ∈ Ioo (x0 - B) (x0 + B), HasDerivAt g' (g'' x) x := by
    intro x hx; exact (h'_deriv x hx).neg
  have hg''_ge : ∀ x ∈ Ioo (x0 - B) (x0 + B), c ≤ g'' x := by
    intro x hx
    have h1 : h'' x ≤ -c := h''_le x hx
    dsimp only [g'']; linarith
  have hg_x0_val : |g x0| ≤ M := by
    dsimp only [g]; rw [abs_neg]; exact hx0_val
  have hg_x0_deriv : |g' x0| ≤ S := by
    dsimp only [g']; rw [abs_neg]; exact hx0_deriv
  have hg_x0_neg : g x0 < 0 := by dsimp only [g]; linarith
  have h_result := convex_sign_change_at_distance hc_pos hS_pos hB_pos
    hg_cont hg'_cont hg_deriv hg'_deriv hg''_ge hg_x0_val hg_x0_deriv hg_x0_neg hB_large
  have h1 : g (x0 + B) > 0 := h_result.1
  have h2 : g (x0 - B) > 0 := h_result.2
  have h3 : h (x0 + B) < 0 := by dsimp only [g] at h1; linarith
  have h4 : h (x0 - B) < 0 := by dsimp only [g] at h2; linarith
  exact ⟨h3, h4⟩

-- ============================================================================
-- Endpoint containment helpers (from cobalt)
-- ============================================================================

private lemma endpoint_in_I_carrier
    {delta t : ℝ}
    (I : ParameterInterval)
    (R : CurvilinearRectangle delta t)
    (hR : R.interval.carrier ⊆ I.centeredCarrier (1 / 4))
    (E L : ℝ)
    (h_small : E * L ≤ I.length / 4)
    (z : ℝ)
    (hz : z ∈ Icc (R.interval.left - E * L)
        (R.interval.right + E * L)) :
    z ∈ Icc I.left I.right := by
  let leftP : UnitPoint := ⟨R.interval.left, R.interval.left_mem⟩
  let rightP : UnitPoint := ⟨R.interval.right, R.interval.right_mem⟩
  have hleftP_in_R : leftP ∈ R.interval.carrier := by
    simp [ParameterInterval.carrier, leftP] <;> exact R.interval.left_le_right
  have hrightP_in_R : rightP ∈ R.interval.carrier := by
    simp [ParameterInterval.carrier, rightP] <;> exact R.interval.left_le_right
  have hleftP_in_I : leftP ∈ I.centeredCarrier (1 / 4) := hR hleftP_in_R
  have hrightP_in_I : rightP ∈ I.centeredCarrier (1 / 4) := hR hrightP_in_R
  have hleft_bound : |R.interval.left - I.midpoint| ≤ I.length / 8 := by
    have h : |R.interval.left - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := by
      simpa [ParameterInterval.centeredCarrier, leftP] using hleftP_in_I
    have h2 : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
    rw [h2] at h; exact h
  have hright_bound : |R.interval.right - I.midpoint| ≤ I.length / 8 := by
    have h : |R.interval.right - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := by
      simpa [ParameterInterval.centeredCarrier, rightP] using hrightP_in_I
    have h2 : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
    rw [h2] at h; exact h
  have h1 : z - I.midpoint ≥ -3 * I.length / 8 := by
    have h_left_lower : R.interval.left - I.midpoint ≥ -I.length / 8 := by
      have h := (abs_le.mp hleft_bound).1; linarith
    linarith [hz.1]
  have h4 : z - I.midpoint ≤ 3 * I.length / 8 := by
    have h_right_upper : R.interval.right - I.midpoint ≤ I.length / 8 := by
      have h := (abs_le.mp hright_bound).2; linarith
    linarith [hz.2]
  have h8 : |z - I.midpoint| ≤ I.length / 2 := by
    have h7 : |z - I.midpoint| ≤ 3 * I.length / 8 := by
      rw [abs_le] <;> constructor <;> linarith
    have h9 : 0 ≤ I.length := I.length_nonneg
    calc |z - I.midpoint| ≤ 3 * I.length / 8 := h7
      _ ≤ I.length / 2 := by linarith
  have h11 : I.left ≤ z := by
    have h12 : -(I.length / 2) ≤ z - I.midpoint := (abs_le.mp h8).1
    simp [ParameterInterval.midpoint, ParameterInterval.length] at h12 ⊢ <;> linarith
  have h13 : z ≤ I.right := by
    have h14 : z - I.midpoint ≤ I.length / 2 := (abs_le.mp h8).2
    simp [ParameterInterval.midpoint, ParameterInterval.length] at h14 ⊢ <;> linarith
  exact ⟨h11, h13⟩

private lemma mkUnitPoint_in_carrier
    (I : ParameterInterval) {z : ℝ} (hz : z ∈ Icc I.left I.right) :
    ∃ (p : UnitPoint), (p : ℝ) = z ∧ p ∈ I.carrier := by
  have hz01 : z ∈ unitInterval := by
    have h1 : I.left ∈ unitInterval := I.left_mem
    have h2 : I.right ∈ unitInterval := I.right_mem
    exact ⟨by linarith [hz.1, h1.1], by linarith [hz.2, h2.2]⟩
  let p : UnitPoint := ⟨z, hz01⟩
  have hp_in : p ∈ I.carrier := by
    simpa [ParameterInterval.carrier, p] using ⟨hz.1, hz.2⟩
  exact ⟨p, rfl, hp_in⟩

private lemma enlargement_E_bound
    {K t d V : ℝ} (hK : 1 ≤ K) (ht : 0 < t) (hd : 2 * t ≤ d) (hV : 0 ≤ V)
    (curvature E : ℝ) (hcurv : curvature = d / (6 * K * t))
    (hE : E = 2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature)) :
    E ≤ 12 * K * V + 12 * K + Real.sqrt (6 * V * K) := by
  have hK_pos : 0 < K := by linarith
  have hd_pos : 0 < d := by linarith
  have hcurv_pos : 0 < curvature := by rw [hcurv] <;> positivity
  have hratio : t / d ≤ 1 / 2 := by
    rw [div_le_iff₀ hd_pos] <;> linarith
  have h1 : 2 * (2 * V + d / t) / curvature ≤ 12 * K * V + 12 * K := by
    have h_eq : 2 * (2 * V + d / t) / curvature = 24 * K * V * (t / d) + 12 * K := by
      rw [hcurv]; field_simp [hK_pos.ne', ht.ne', hd_pos.ne'] <;> ring
    rw [h_eq]
    have h : 24 * K * V * (t / d) ≤ 24 * K * V * (1 / 2 : ℝ) := by gcongr <;> linarith
    have h2 : 24 * K * V * (1 / 2 : ℝ) = 12 * K * V := by ring
    rw [h2] at h; linarith
  have h2 : Real.sqrt (2 * V / curvature) ≤ Real.sqrt (6 * V * K) := by
    have h_eq : 2 * V / curvature = 12 * V * K * (t / d) := by
      rw [hcurv]; field_simp [hK_pos.ne', ht.ne', hd_pos.ne'] <;> ring
    rw [h_eq]
    have h3 : 12 * V * K * (t / d) ≤ 6 * V * K := by
      have h4 : 12 * V * K * (t / d) ≤ 12 * V * K * (1 / 2 : ℝ) := by gcongr <;> linarith
      have h5 : 12 * V * K * (1 / 2 : ℝ) = 6 * V * K := by ring
      rw [h5] at h4; exact h4
    exact Real.sqrt_le_sqrt h3
  rw [hE]; linarith

private lemma sqrt_delta_t_bound
    {K tangency delta t : ℝ} (hK : 1 ≤ K) (htang : 5 ≤ tangency)
    (hdelta : 0 < delta) (ht : 0 < t)
    (h_small : tangency ^ 50 * delta ≤ t / (1000 * K ^ 4)) :
    Real.sqrt (delta / t) ≤ 1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) := by
  have hK_pos : 0 < K := by linarith
  have h_tang_pos : 0 < tangency := by linarith
  have hratio : delta / t ≤ 1 / (1000 * K ^ 4 * tangency ^ 50) := by
    have h_pos1 : 0 < tangency ^ 50 * t := by positivity
    have h : (tangency ^ 50 * delta) / (tangency ^ 50 * t) ≤
        (t / (1000 * K ^ 4)) / (tangency ^ 50 * t) := by gcongr
    have h2 : (tangency ^ 50 * delta) / (tangency ^ 50 * t) = delta / t := by
      field_simp [h_tang_pos.ne', ht.ne'] <;> ring
    have h3 : (t / (1000 * K ^ 4)) / (tangency ^ 50 * t) =
        1 / (1000 * K ^ 4 * tangency ^ 50) := by
      field_simp [hK_pos.ne', h_tang_pos.ne', ht.ne'] <;> ring
    rw [h2, h3] at h; exact h
  have h4 : Real.sqrt (delta / t) ≤ Real.sqrt (1 / (1000 * K ^ 4 * tangency ^ 50)) :=
    Real.sqrt_le_sqrt hratio
  have h_pos : 0 ≤ Real.sqrt 1000 * K ^ 2 * tangency ^ 25 := by positivity
  have h_sq : (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) ^ 2 =
      1000 * K ^ 4 * tangency ^ 50 := by
    have h5 : (Real.sqrt 1000) ^ 2 = 1000 := Real.sq_sqrt (by norm_num)
    calc (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) ^ 2
      = (Real.sqrt 1000) ^ 2 * (K ^ 2) ^ 2 * (tangency ^ 25) ^ 2 := by ring
    _ = 1000 * K ^ 4 * tangency ^ 50 := by rw [h5] <;> ring
  have h6 : Real.sqrt (1000 * K ^ 4 * tangency ^ 50) =
      Real.sqrt 1000 * K ^ 2 * tangency ^ 25 := by
    rw [← h_sq]; exact Real.sqrt_sq h_pos
  have h7 : Real.sqrt (1 / (1000 * K ^ 4 * tangency ^ 50)) =
      1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_one, h6]
  rw [h7] at h4; exact h4

private lemma E_times_sqrt_bound
    {K tangency delta t d V : ℝ} (hK : 1 ≤ K) (htang : 5 ≤ tangency)
    (hdelta : 0 < delta) (ht : 0 < t) (hd : 2 * t ≤ d)
    (h_small : tangency ^ 50 * delta ≤ t / (1000 * K ^ 4))
    (hV : 0 ≤ V) (hV_def : V = 25 * tangency ^ 10 + 2 * tangency + 2)
    (curvature E : ℝ) (hcurv : curvature = d / (6 * K * t))
    (hE_def : E = 2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature)) :
    E * Real.sqrt (delta / t) ≤ 1 / (48 * K) := by
  have hK_pos : 0 < K := by linarith
  have h_tang_pos : 0 < tangency := by linarith
  have h_tang_ge1 : 1 ≤ tangency := by linarith
  have h10 : 1 ≤ tangency ^ 10 := by
    have h : (1 : ℝ)^10 ≤ tangency^10 := by gcongr
    have h' : (1 : ℝ)^10 = 1 := by norm_num
    rw [h'] at h
    exact h
  have h9 : 1 ≤ tangency ^ 9 := by
    have h : (1 : ℝ)^9 ≤ tangency^9 := by gcongr
    have h' : (1 : ℝ)^9 = 1 := by norm_num
    rw [h'] at h
    exact h
  have h_tang_le_pow10 : tangency ≤ tangency ^ 10 := by
    have h : tangency * 1 ≤ tangency * tangency ^ 9 := by gcongr
    have h2 : tangency * tangency ^ 9 = tangency ^ 10 := by ring
    have h4 : tangency * 1 = tangency := by ring
    rw [h4] at h; rw [h2] at h; exact h
  have hE_bound : E ≤ 12 * K * V + 12 * K + Real.sqrt (6 * V * K) :=
    enlargement_E_bound hK ht hd hV curvature E hcurv hE_def
  have hL_bound : Real.sqrt (delta / t) ≤ 1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) :=
    sqrt_delta_t_bound hK htang hdelta ht h_small
  have hV_le : V ≤ 29 * tangency ^ 10 := by
    rw [hV_def]
    have ha : 2 * tangency ≤ 2 * tangency ^ 10 := by gcongr <;> exact h_tang_le_pow10
    have hb : (2 : ℝ) ≤ 2 * tangency ^ 10 := by linarith [h10]
    linarith
  have h_term1 : 12 * K * V ≤ 348 * K * tangency ^ 10 := by
    calc 12 * K * V ≤ 12 * K * (29 * tangency ^ 10) := by gcongr
      _ = 348 * K * tangency ^ 10 := by ring
  have h_term2 : 12 * K ≤ 12 * K * tangency ^ 10 := by
    have h : 1 ≤ tangency ^ 10 := h10
    have h' : 12 * K ≤ 12 * K * tangency ^ 10 := by
      calc 12 * K = 12 * K * 1 := by ring
        _ ≤ 12 * K * tangency ^ 10 := by gcongr
    exact h'
  have h_sqrt : Real.sqrt (6 * V * K) ≤ 14 * K * tangency ^ 10 := by
    have h4 : 6 * V * K ≤ (14 * K * tangency ^ 10) ^ 2 := by
      have h5 : 6 * V * K ≤ 174 * K * tangency ^ 10 := by
        calc 6 * V * K ≤ 6 * (29 * tangency ^ 10) * K := by gcongr
          _ = 174 * K * tangency ^ 10 := by ring
      have h6 : 174 * K * tangency ^ 10 ≤ (14 * K * tangency ^ 10) ^ 2 := by
        have h7 : (14 * K * tangency ^ 10) ^ 2 = 196 * K ^ 2 * tangency ^ 20 := by ring
        rw [h7]
        have h8 : 0 < K * tangency ^ 10 := by positivity
        nlinarith [hK, htang]
      linarith
    have h9 : 0 ≤ 14 * K * tangency ^ 10 := by positivity
    exact Real.sqrt_le_iff.mpr ⟨by positivity, h4⟩
  have h_sum : 12 * K * V + 12 * K + Real.sqrt (6 * V * K) ≤ 374 * K * tangency ^ 10 := by linarith
  have hd_pos : 0 < d := by linarith
  have hcurv_pos : 0 < curvature := by rw [hcurv]; exact div_pos hd_pos (by positivity)
  have hE_nonneg : 0 ≤ E := by
    rw [hE_def]
    have h1 : 0 ≤ 2 * (2 * V + d / t) := by positivity
    have h1' : 0 ≤ 2 * (2 * V + d / t) / curvature := by exact div_nonneg h1 hcurv_pos.le
    have h2 : 0 ≤ Real.sqrt (2 * V / curvature) := Real.sqrt_nonneg _
    linarith
  have h_main : E * Real.sqrt (delta / t) ≤
      (374 * K * tangency ^ 10) / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) := by
    calc E * Real.sqrt (delta / t)
      ≤ (12 * K * V + 12 * K + Real.sqrt (6 * V * K)) * Real.sqrt (delta / t) := by gcongr
    _ ≤ (12 * K * V + 12 * K + Real.sqrt (6 * V * K)) *
          (1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25)) := by gcongr <;> positivity
    _ ≤ (374 * K * tangency ^ 10) * (1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25)) := by gcongr <;> positivity
    _ = (374 * K * tangency ^ 10) / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) := by ring
  have h_tang15_ge : tangency ^ 15 ≥ (17952 : ℝ) := by
    have h1 : tangency ^ 15 ≥ 5 ^ 15 := by gcongr <;> linarith
    have h2 : (5 : ℝ)^15 ≥ 17952 := by norm_num
    linarith
  have h_sqrt_ge1 : Real.sqrt 1000 ≥ 1 := by
    have h : (1 : ℝ) ≤ 1000 := by norm_num
    have h' : Real.sqrt 1 ≤ Real.sqrt 1000 := Real.sqrt_le_sqrt h
    have h'' : Real.sqrt 1 = 1 := by simp
    linarith
  have h_arith : (17952 : ℝ) ≤ Real.sqrt 1000 * tangency ^ 15 := by
    have h15_nonneg : 0 ≤ tangency ^ 15 := by positivity
    have h_sqrt_mul : Real.sqrt 1000 * tangency ^ 15 ≥ tangency ^ 15 := by nlinarith
    linarith [h_tang15_ge, h_sqrt_mul]
  have h_pos_denom1 : 0 < Real.sqrt 1000 * K ^ 2 * tangency ^ 25 := by positivity
  have h_pos_denom2 : 0 < 48 * K := by positivity
  have h_cross : 48 * K * (374 * K * tangency ^ 10) ≤ Real.sqrt 1000 * K ^ 2 * tangency ^ 25 := by
    have h_pos1 : 0 < K ^ 2 * tangency ^ 10 := by positivity
    have h_eq1 : 48 * K * (374 * K * tangency ^ 10) = (17952 : ℝ) * (K ^ 2 * tangency ^ 10) := by ring
    have h_eq2 : Real.sqrt 1000 * K ^ 2 * tangency ^ 25 =
        (Real.sqrt 1000 * tangency ^ 15) * (K ^ 2 * tangency ^ 10) := by ring
    rw [h_eq1, h_eq2]; gcongr <;> linarith
  set A := 374 * K * tangency ^ 10 with hA
  set B := Real.sqrt 1000 * K ^ 2 * tangency ^ 25 with hB
  set C := (1 : ℝ) with hC
  set D := 48 * K with hD
  have h_cross' : A * D ≤ C * B := by simpa [hA, hB, hC, hD, mul_comm] using h_cross
  have h_final : A / B ≤ C / D := by
    have hB_pos : 0 < B := h_pos_denom1
    have hD_pos : 0 < D := h_pos_denom2
    calc A / B
      = (A * D) / (B * D) := by field_simp [hB_pos.ne', hD_pos.ne'] <;> ring
    _ ≤ (C * B) / (B * D) := by gcongr
    _ = C / D := by field_simp [hB_pos.ne', hD_pos.ne'] <;> ring
  exact h_main.trans h_final

private lemma endpoint_containment
    {K tangency delta t d V : ℝ} (hK : 1 ≤ K) (htang : 5 ≤ tangency)
    (hdelta : 0 < delta) (ht : 0 < t) (hd : 2 * t ≤ d)
    (h_small : tangency ^ 50 * delta ≤ t / (1000 * K ^ 4))
    (hV_def : V = 25 * tangency ^ 10 + 2 * tangency + 2)
    (curvature E : ℝ) (hcurv : curvature = d / (6 * K * t))
    (hE_def : E = 2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature))
    (I : ParameterInterval) (hI : I.IsControlled K)
    (R : CurvilinearRectangle delta t)
    (hR : R.interval.carrier ⊆ I.centeredCarrier (1 / 4))
    (z : ℝ) (hz : z ∈ Icc (R.interval.left - E * Real.sqrt (delta / t))
        (R.interval.right + E * Real.sqrt (delta / t))) :
    ∃ (p : UnitPoint), (p : ℝ) = z ∧ p ∈ I.carrier := by
  have hV : 0 ≤ V := by rw [hV_def] <;> positivity
  have hI_length : (12 * K)⁻¹ ≤ I.length := hI.1
  have hE_times_L : E * Real.sqrt (delta / t) ≤ 1 / (48 * K) :=
    E_times_sqrt_bound hK htang hdelta ht hd h_small hV hV_def curvature E hcurv hE_def
  have h_quarter : 1 / (48 * K) ≤ I.length / 4 := by
    have hK_pos : 0 < K := by linarith
    have h : (12 * K)⁻¹ ≤ I.length := hI_length
    have h2 : 1 / (48 * K) = ((12 * K)⁻¹) / 4 := by field_simp [hK_pos.ne'] <;> ring
    rw [h2]; gcongr
  have h_small' : E * Real.sqrt (delta / t) ≤ I.length / 4 := hE_times_L.trans h_quarter
  have hz' : z ∈ Icc I.left I.right :=
    endpoint_in_I_carrier I R hR E (Real.sqrt (delta / t)) h_small' z hz
  exact mkUnitPoint_in_carrier I hz'

-- ============================================================================
-- Main theorem
-- ============================================================================

lemma directional_lens_C0_bound (K tangency : ℝ) (hK : 1 ≤ K) (htang : 5 ≤ tangency) :
    20 * K * (25 * tangency ^ 10 + 2 * tangency + 2) + 20 * K ≤ 1000 * K * tangency ^ 10 := by
  have h1 : 1 ≤ tangency := by linarith
  have h2 : 0 ≤ tangency := by linarith
  have h3 : tangency ^ 9 ≥ 1 := by
    have h4 : ∀ n : ℕ, tangency ^ n ≥ 1 := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
        calc tangency ^ (n + 1)
          = tangency * tangency ^ n := by ring
        _ ≥ tangency * 1 := by exact mul_le_mul_of_nonneg_left ih h2
        _ ≥ 1 := by linarith
    exact h4 9
  have h4 : tangency ≤ tangency ^ 10 := by
    calc tangency
      = tangency * 1 := by ring
    _ ≤ tangency * tangency ^ 9 := by exact mul_le_mul_of_nonneg_left h3 h2
    _ = tangency ^ 10 := by ring
  have h5 : 2 * tangency ≤ 2 * tangency ^ 10 := by
    exact mul_le_mul_of_nonneg_left h4 (by norm_num)
  have h6 : tangency ^ 10 ≥ 1 := by
    have h7 : ∀ n : ℕ, tangency ^ n ≥ 1 := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
        calc tangency ^ (n + 1)
          = tangency * tangency ^ n := by ring
        _ ≥ tangency * 1 := by exact mul_le_mul_of_nonneg_left ih h2
        _ ≥ 1 := by linarith
    exact h7 10
  have h7 : 2 ≤ 3 * tangency ^ 10 := by
    calc 2
      ≤ 3 * (1 : ℝ) := by norm_num
    _ ≤ 3 * tangency ^ 10 := by exact mul_le_mul_of_nonneg_left h6 (by norm_num)
  have h8 : 25 * tangency ^ 10 + 2 * tangency + 2 ≤ 30 * tangency ^ 10 := by
    have h9 : 25 * tangency ^ 10 + 2 * tangency + 2 ≤ 25 * tangency ^ 10 + 2 * tangency ^ 10 + 3 * tangency ^ 10 :=
      add_le_add (add_le_add (le_refl _) h5) h7
    have h10 : 25 * tangency ^ 10 + 2 * tangency ^ 10 + 3 * tangency ^ 10 = 30 * tangency ^ 10 := by ring
    rw [h10] at h9
    exact h9
  have hK_pos : 0 ≤ K := by linarith
  have h10 : 20 * K * (25 * tangency ^ 10 + 2 * tangency + 2) ≤ 20 * K * (30 * tangency ^ 10) :=
    mul_le_mul_of_nonneg_left h8 (by positivity)
  have h11 : 20 * K ≤ 20 * K * tangency ^ 10 := by
    have h12 : 0 ≤ 20 * K := by positivity
    calc 20 * K
      = 20 * K * 1 := by ring
    _ ≤ 20 * K * tangency ^ 10 := by exact mul_le_mul_of_nonneg_left h6 h12
  have h13 : 20 * K * (25 * tangency ^ 10 + 2 * tangency + 2) + 20 * K ≤ 620 * K * tangency ^ 10 := by
    have h14 : 20 * K * (25 * tangency ^ 10 + 2 * tangency + 2) + 20 * K ≤ 20 * K * (30 * tangency ^ 10) + 20 * K * tangency ^ 10 :=
      add_le_add h10 h11
    have h15 : 20 * K * (30 * tangency ^ 10) + 20 * K * tangency ^ 10 = 620 * K * tangency ^ 10 := by ring
    rw [h15] at h14
    exact h14
  have h16 : 0 ≤ K * tangency ^ 10 := by positivity
  have h17 : (620 : ℝ) ≤ 1000 := by norm_num
  have h18 : 620 * (K * tangency ^ 10) ≤ 1000 * (K * tangency ^ 10) :=
    mul_le_mul_of_nonneg_right h17 h16
  have h19 : 620 * K * tangency ^ 10 ≤ 1000 * K * tangency ^ 10 := by
    have h20 : 620 * (K * tangency ^ 10) = 620 * K * tangency ^ 10 := by ring
    have h21 : 1000 * (K * tangency ^ 10) = 1000 * K * tangency ^ 10 := by ring
    rw [h20, h21] at h18
    exact h18
  exact h13.trans h19

lemma directional_lens_B_bound (K tangency : ℝ) (hK : 1 ≤ K) (htang : 5 ≤ tangency) :
    (1000 * K * tangency ^ 10) * (1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25)) ≤ 1 / (32 * K) := by
  have hK_pos : 0 < K := by linarith
  have htang_pos : 0 < tangency := by linarith
  have h1 : 1 ≤ Real.sqrt 1000 := by
    have h2 : (1 : ℝ) ^ 2 ≤ 1000 := by norm_num
    exact Real.le_sqrt_of_sq_le h2
  have h5 : tangency ^ 15 ≥ 32000 := by
    have h6 : tangency ^ 15 ≥ (5 : ℝ)^15 := by
      gcongr <;> linarith
    have h7 : (5 : ℝ)^15 ≥ 32000 := by norm_num
    linarith
  have h8 : Real.sqrt 1000 * tangency ^ 15 ≥ 32000 := by
    have h9 : Real.sqrt 1000 * tangency ^ 15 ≥ 1 * tangency ^ 15 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h10 : 1 * tangency ^ 15 = tangency ^ 15 := by ring
    rw [h10] at h9
    linarith
  set A : ℝ := Real.sqrt 1000 * K * tangency ^ 15 with hA_def
  set B : ℝ := 32 * K with hB_def
  have hA_pos : 0 < A := by positivity
  have hB_pos : 0 < B := by positivity
  have h9 : 1000 * B ≤ A := by
    have h10 : 1000 * B = 32000 * K := by
      simp [hB_def] <;> ring
    rw [h10]
    have h11 : 32000 * K ≤ (Real.sqrt 1000 * tangency ^ 15) * K :=
      mul_le_mul_of_nonneg_right h8 (by linarith)
    have h12 : (Real.sqrt 1000 * tangency ^ 15) * K = A := by
      simp [hA_def] <;> ring
    rw [h12] at h11
    exact h11
  have h_final : 1000 / A ≤ 1 / B := by
    have h13 : 1000 / A = (1000 * B) / (A * B) := by
      field_simp [hA_pos.ne', hB_pos.ne'] <;> ring
    have h14 : 1 / B = A / (A * B) := by
      field_simp [hA_pos.ne', hB_pos.ne'] <;> ring
    rw [h13, h14]
    apply div_le_div_of_nonneg_right h9
    positivity
  have h_simp : (1000 * K * tangency ^ 10) * (1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25)) =
      1000 / A := by
    simp [hA_def]
    field_simp [hK_pos.ne', htang_pos.ne'] <;> ring
  rw [h_simp]
  exact h_final

lemma directional_lens_p_ge (K : ℝ) (hK : 1 ≤ K) (I : ParameterInterval)
    (hI : I.IsControlled K) (p : ℝ) (hp_lower : p ≥ I.left + 3 * I.length / 8) :
    p ≥ 1 / (32 * K) := by
  have hK_pos : 0 < K := by linarith
  have h1 : 0 ≤ I.left := I.left_mem.1
  have h2 : (12 * K)⁻¹ ≤ I.length := hI.1
  have h3 : 3 * ((12 * K)⁻¹) / 8 ≤ 3 * I.length / 8 := by
    have h_pos : (0 : ℝ) ≤ 3 / 8 := by norm_num
    have h_eq1 : 3 * ((12 * K)⁻¹) / 8 = (3 / 8 : ℝ) * ((12 * K)⁻¹) := by ring
    have h_eq2 : 3 * I.length / 8 = (3 / 8 : ℝ) * I.length := by ring
    rw [h_eq1, h_eq2]
    exact mul_le_mul_of_nonneg_left h2 h_pos
  have h4 : I.left + 3 * ((12 * K)⁻¹) / 8 ≥ 3 * ((12 * K)⁻¹) / 8 := by
    exact le_add_of_nonneg_left h1
  have h5 : 3 * ((12 * K)⁻¹) / 8 = 1 / (32 * K) := by
    field_simp [hK_pos.ne'] <;> ring
  calc p
    ≥ I.left + 3 * I.length / 8 := hp_lower
  _ ≥ I.left + 3 * ((12 * K)⁻¹) / 8 := by gcongr
  _ ≥ 3 * ((12 * K)⁻¹) / 8 := h4
  _ = 1 / (32 * K) := h5

lemma directional_lens_q_le (K : ℝ) (hK : 1 ≤ K) (I : ParameterInterval)
    (hI : I.IsControlled K) (q : ℝ) (hq_upper : q ≤ I.right - 3 * I.length / 8) :
    q ≤ 1 - 1 / (32 * K) := by
  have hK_pos : 0 < K := by linarith
  have h1 : I.right ≤ 1 := I.right_mem.2
  have h2 : (12 * K)⁻¹ ≤ I.length := hI.1
  have h3 : 3 * ((12 * K)⁻¹) / 8 ≤ 3 * I.length / 8 := by
    have h_pos : (0 : ℝ) ≤ 3 / 8 := by norm_num
    have h_eq1 : 3 * ((12 * K)⁻¹) / 8 = (3 / 8 : ℝ) * ((12 * K)⁻¹) := by ring
    have h_eq2 : 3 * I.length / 8 = (3 / 8 : ℝ) * I.length := by ring
    rw [h_eq1, h_eq2]
    exact mul_le_mul_of_nonneg_left h2 h_pos
  have h4 : I.right - 3 * I.length / 8 ≤ I.right - 3 * ((12 * K)⁻¹) / 8 := by
    exact sub_le_sub_left h3 I.right
  have h5 : I.right - 3 * ((12 * K)⁻¹) / 8 ≤ 1 - 3 * ((12 * K)⁻¹) / 8 := by
    exact sub_le_sub_right h1 (3 * ((12 * K)⁻¹) / 8)
  have h6 : 3 * ((12 * K)⁻¹) / 8 = 1 / (32 * K) := by
    field_simp [hK_pos.ne'] <;> ring
  calc q
    ≤ I.right - 3 * I.length / 8 := hq_upper
  _ ≤ I.right - 3 * ((12 * K)⁻¹) / 8 := h4
  _ ≤ 1 - 3 * ((12 * K)⁻¹) / 8 := h5
  _ = 1 - 1 / (32 * K) := by rw [h6]

lemma directional_lens_endpoint_bounds (K : ℝ) (hK : 1 ≤ K)
    (x0 p q B : ℝ) (hx0_core : x0 ∈ Icc p q)
    (hp_ge : p ≥ 1 / (32 * K)) (hq_le : q ≤ 1 - 1 / (32 * K))
    (hB_le : B ≤ 1 / (32 * K)) (hB_pos : 0 < B) :
    0 ≤ x0 - B ∧ x0 + B ≤ 1 ∧ x0 - B < x0 + B := by
  have hK_pos : 0 < K := by linarith
  have h1 : x0 ≥ p := hx0_core.1
  have h2 : x0 ≤ q := hx0_core.2
  have h3 : 0 ≤ x0 - B := by
    calc x0 - B
      ≥ p - B := by linarith
    _ ≥ 1 / (32 * K) - B := by linarith
    _ ≥ 0 := by linarith
  have h4 : x0 + B ≤ 1 := by
    calc x0 + B
      ≤ q + B := by linarith
    _ ≤ 1 - 1 / (32 * K) + B := by linarith
    _ ≤ 1 := by linarith
  have h5 : x0 - B < x0 + B := by linarith
  exact ⟨h3, h4, h5⟩

lemma directional_lens_C0_ge1 (K V C0 : ℝ) (hK : 1 ≤ K) (hV_pos : 0 < V)
    (hC0_def : C0 = 20 * K * V + 20 * K) : C0 ≥ 1 := by
  have hK_pos : 0 < K := by linarith
  rw [hC0_def]
  nlinarith

lemma directional_lens_B_gt_L2 (C0 L : ℝ) (hC0_ge1 : C0 ≥ 1) (hL_pos : 0 < L) :
    C0 * L > L / 2 := by
  have hC0_nonneg : 0 ≤ C0 := by linarith
  have h1 : C0 * L ≥ L := by
    calc C0 * L
      ≥ 1 * L := by gcongr <;> linarith
    _ = L := by ring
  linarith

lemma directional_lens_core_shift_bounds (x0 p q B L : ℝ)
    (hx0_def : x0 = (p + q) / 2) (hcore_length : q - p = L)
    (hB_gt_L2 : B > L / 2) :
    (x0 - B < p) ∧ (q < x0 + B) := by
  have h1 : x0 - B < p := by
    rw [hx0_def]
    linarith [hcore_length, hB_gt_L2]
  have h2 : q < x0 + B := by
    rw [hx0_def]
    linarith [hcore_length, hB_gt_L2]
  exact ⟨h1, h2⟩

lemma directional_lens_in_unit_interval (a b x : ℝ) (ha_ge0 : 0 ≤ a) (hb_le1 : b ≤ 1)
    (hx : x ∈ Icc a b) : x ∈ unitInterval := by
  have h1 : a ≤ x := hx.1
  have h2 : x ≤ b := hx.2
  exact ⟨by linarith, by linarith⟩

lemma directional_lens_h2_bound_enl
    (w b : C2Function) (a b_val x d : ℝ)
    (hd_def : d = c2Distance w b)
    (ha_ge0 : 0 ≤ a) (hb_le1 : b_val ≤ 1) (hx : x ∈ Icc a b_val)
    (h2 : ℝ → ℝ)
    (h2_eq : h2 x = deriv (deriv w.extension) x - deriv (deriv b.extension) x) :
    |h2 x| ≤ d := by
  have hx01 : x ∈ unitInterval := ⟨le_trans ha_ge0 hx.1, le_trans hx.2 hb_le1⟩
  let xp : UnitPoint := ⟨x, hx01⟩
  have h51 : deriv (deriv w.extension) x = w.secondDeriv xp :=
    w.secondDeriv_extension_eq_secondDeriv xp
  have h52 : deriv (deriv b.extension) x = b.secondDeriv xp :=
    b.secondDeriv_extension_eq_secondDeriv xp
  have h5 : h2 x = w.secondDeriv xp - b.secondDeriv xp := by
    rw [h2_eq, h51, h52]
  rw [h5, hd_def]
  exact abs_secondDeriv_sub_le_c2Distance w b xp

lemma directional_lens_curv_gap_enl
    {family : Set C2Function} {K : ℝ} (hK : 1 ≤ K) (hcurv : HasCinematicCurvature family K)
    {w b : C2Function} (hw : w ∈ family) (hb : b ∈ family)
    (d : ℝ) (hd_def : d = c2Distance w b)
    (a b_val x : ℝ) (ha_ge0 : 0 ≤ a) (hb_le1 : b_val ≤ 1) (hx : x ∈ Icc a b_val)
    (h0 h1 h2 : ℝ → ℝ)
    (h0_def : ∀ y, h0 y = w.extension y - b.extension y)
    (h1_def : ∀ y, h1 y = deriv w.extension y - deriv b.extension y)
    (h2_def : ∀ y, h2 y = deriv (deriv w.extension) y - deriv (deriv b.extension) y) :
    d / K ≤ |h0 x| + |h1 x| + |h2 x| := by
  have hx01 : x ∈ unitInterval := ⟨le_trans ha_ge0 hx.1, le_trans hx.2 hb_le1⟩
  let xp : UnitPoint := ⟨x, hx01⟩
  have hK_pos : 0 < K := by linarith
  have h9 : d / K ≤ jetGap w b xp := by
    have h10 : K⁻¹ * c2Distance w b ≤ jetGap w b xp := hcurv.2 hw hb xp
    have h11 : K⁻¹ * c2Distance w b = d / K := by
      rw [hd_def]
      field_simp [hK_pos.ne'] <;> ring
    rw [h11] at h10; exact h10
  have h41 : w.extension x = w xp := C2Function.extension_eq_value w xp
  have h42 : b.extension x = b xp := C2Function.extension_eq_value b xp
  have hd1 : deriv w.extension x = w.firstDeriv xp := w.deriv_extension_eq_firstDeriv xp
  have hd2 : deriv b.extension x = b.firstDeriv xp := b.deriv_extension_eq_firstDeriv xp
  have hd3 : deriv (deriv w.extension) x = w.secondDeriv xp :=
    w.secondDeriv_extension_eq_secondDeriv xp
  have hd4 : deriv (deriv b.extension) x = b.secondDeriv xp :=
    b.secondDeriv_extension_eq_secondDeriv xp
  have h_val : w xp - b xp = h0 x := by
    have h : h0 x = w.extension x - b.extension x := h0_def x
    rw [h, h41, h42]
  have h_deriv : w.firstDeriv xp - b.firstDeriv xp = h1 x := by
    have h : h1 x = deriv w.extension x - deriv b.extension x := h1_def x
    rw [h, hd1, hd2]
  have h_deriv2 : w.secondDeriv xp - b.secondDeriv xp = h2 x := by
    have h : h2 x = deriv (deriv w.extension) x - deriv (deriv b.extension) x := h2_def x
    rw [h, hd3, hd4]
  have h11 : jetGap w b xp = |h0 x| + |h1 x| + |h2 x| := by
    simp [jetGap, h_val, h_deriv, h_deriv2] <;> rfl
  rw [h11] at h9; exact h9

lemma directional_lens_h2_bound_unit
    (w b : C2Function) (x d : ℝ) (hd_def : d = c2Distance w b)
    (hx01 : x ∈ unitInterval) (h2 : ℝ → ℝ)
    (h2_eq : h2 x = deriv (deriv w.extension) x - deriv (deriv b.extension) x) :
    |h2 x| ≤ d := by
  let xp : UnitPoint := ⟨x, hx01⟩
  have h51 : deriv (deriv w.extension) x = w.secondDeriv xp :=
    w.secondDeriv_extension_eq_secondDeriv xp
  have h52 : deriv (deriv b.extension) x = b.secondDeriv xp :=
    b.secondDeriv_extension_eq_secondDeriv xp
  have h5 : h2 x = w.secondDeriv xp - b.secondDeriv xp := by
    rw [h2_eq, h51, h52]
  rw [h5, hd_def]
  exact abs_secondDeriv_sub_le_c2Distance w b xp

lemma directional_lens_h2_bound_simple
    (w b : C2Function) (x d : ℝ) (hd_def : d = c2Distance w b)
    (hx01 : x ∈ unitInterval) :
    |deriv (deriv w.extension) x - deriv (deriv b.extension) x| ≤ d := by
  let xp : UnitPoint := ⟨x, hx01⟩
  have h51 : deriv (deriv w.extension) x = w.secondDeriv xp :=
    w.secondDeriv_extension_eq_secondDeriv xp
  have h52 : deriv (deriv b.extension) x = b.secondDeriv xp :=
    b.secondDeriv_extension_eq_secondDeriv xp
  have h5 : deriv (deriv w.extension) x - deriv (deriv b.extension) x = w.secondDeriv xp - b.secondDeriv xp := by
    rw [h51, h52]
  rw [h5, hd_def]
  exact abs_secondDeriv_sub_le_c2Distance w b xp

lemma directional_lens_hp_lower (delta t K : ℝ) (hK : 1 ≤ K) (I : ParameterInterval)
    (hI : I.IsControlled K) (R : CurvilinearRectangle delta t)
    (hRsub : R.interval.carrier ⊆ I.centeredCarrier (1 / 4)) (p : ℝ)
    (hp_def : p = R.interval.left) : p ≥ I.left + 3 * I.length / 8 := by
  let leftP : UnitPoint := ⟨R.interval.left, R.interval.left_mem⟩
  have hleftP_in_R : leftP ∈ R.interval.carrier := by
    simp [ParameterInterval.carrier, leftP] <;> exact R.interval.left_le_right
  have hleftP_in_I : leftP ∈ I.centeredCarrier (1 / 4) := hRsub hleftP_in_R
  have hleft_bound : |R.interval.left - I.midpoint| ≤ I.length / 8 := by
    have h : |R.interval.left - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := by
      simpa [ParameterInterval.centeredCarrier, leftP] using hleftP_in_I
    have h2 : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
    rw [h2] at h; exact h
  have h3 : -(I.length / 8) ≤ R.interval.left - I.midpoint := (abs_le.mp hleft_bound).1
  have h_mid : I.midpoint = (I.left + I.right) / 2 := by rw [ParameterInterval.midpoint]
  have h_len : I.length = I.right - I.left := by rw [ParameterInterval.length]
  have h4 : p = R.interval.left := hp_def
  rw [h4]
  rw [h_mid, h_len] at h3
  have h_goal : R.interval.left ≥ I.left + 3 * I.length / 8 := by linarith
  exact h_goal

lemma directional_lens_hq_upper (delta t K : ℝ) (hK : 1 ≤ K) (I : ParameterInterval)
    (hI : I.IsControlled K) (R : CurvilinearRectangle delta t)
    (hRsub : R.interval.carrier ⊆ I.centeredCarrier (1 / 4)) (q : ℝ)
    (hq_def : q = R.interval.right) : q ≤ I.right - 3 * I.length / 8 := by
  let rightP : UnitPoint := ⟨R.interval.right, R.interval.right_mem⟩
  have hrightP_in_R : rightP ∈ R.interval.carrier := by
    simp [ParameterInterval.carrier, rightP] <;> exact R.interval.left_le_right
  have hrightP_in_I : rightP ∈ I.centeredCarrier (1 / 4) := hRsub hrightP_in_R
  have hright_bound : |R.interval.right - I.midpoint| ≤ I.length / 8 := by
    have h : |R.interval.right - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := by
      simpa [ParameterInterval.centeredCarrier, rightP] using hrightP_in_I
    have h2 : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
    rw [h2] at h; exact h
  have h3 : R.interval.right - I.midpoint ≤ I.length / 8 := (abs_le.mp hright_bound).2
  have h_mid : I.midpoint = (I.left + I.right) / 2 := by rw [ParameterInterval.midpoint]
  have h_len : I.length = I.right - I.left := by rw [ParameterInterval.length]
  have h4 : q = R.interval.right := hq_def
  rw [h4]
  rw [h_mid, h_len] at h3
  have h_goal : R.interval.right ≤ I.right - 3 * I.length / 8 := by linarith
  exact h_goal

lemma directional_lens_M_enl_le (tangency delta V S_enl B M_enl M_core : ℝ)
    (hV_def : V = 25 * tangency ^ 10 + 2 * tangency + 2)
    (hM_enl_def : M_enl = M_core + S_enl * B)
    (hM_core_def : M_core = 2 * tangency * delta)
    (hdelta : 0 < delta) (htang : 5 ≤ tangency) :
    M_enl ≤ V * delta + S_enl * B := by
  rw [hM_enl_def, hM_core_def, hV_def]
  have h_pos : 0 ≤ delta := by linarith
  have h : 2 * tangency ≤ 25 * tangency ^ 10 + 2 * tangency + 2 := by
    have h2 : 0 ≤ tangency := by linarith
    nlinarith [pow_nonneg h2 10]
  nlinarith

lemma directional_lens_S_enl_le (S_enl S_core d B L tangency : ℝ)
    (hS_enl_def : S_enl = S_core + d * B)
    (hS_core_def : S_core = (2 * tangency + 1) * d * L) :
    S_enl ≤ (2 * tangency + 1) * d * L + d * B := by
  rw [hS_enl_def, hS_core_def] <;> ring_nf <;> exact le_refl _

lemma directional_lens_enl_small (M_enl S_enl B V delta d L tangency K X : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hM_le : M_enl ≤ V * delta + S_enl * B)
    (hS_le : S_enl ≤ X)
    (h_main : V * delta + X * B + X < d / K) :
    M_enl + S_enl < d / K := by
  have h2 : S_enl * B + S_enl ≤ X * B + X :=
    add_le_add (mul_le_mul_of_nonneg_right hS_le hB_nonneg) hS_le
  have h3 : M_enl + S_enl ≤ V * delta + (S_enl * B + S_enl) := by
    have h : M_enl ≤ V * delta + S_enl * B := hM_le
    linarith
  have h4 : M_enl + S_enl ≤ V * delta + X * B + X := by
    calc M_enl + S_enl
      ≤ V * delta + (S_enl * B + S_enl) := h3
    _ ≤ V * delta + (X * B + X) := by gcongr
    _ = V * delta + X * B + X := by ring
  exact h4.trans_lt h_main

private lemma directional_lens_c_new_ge (d K M_enl S_enl : ℝ)
    (hK_pos : 0 < K) (hd_pos : 0 < d)
    (h5 : M_enl + S_enl ≤ d / (6 * K)) :
    d / K - M_enl - S_enl ≥ d / (6 * K) := by
  have h1 : d / K - (M_enl + S_enl) ≥ d / K - d / (6 * K) := by
    exact sub_le_sub_left h5 (d / K)
  have h2 : d / K - d / (6 * K) = 5 * d / (6 * K) := by
    field_simp [hK_pos.ne'] <;> ring
  have h_pos4 : 0 ≤ 4 * d / (6 * K) := by positivity
  have h3 : 5 * d / (6 * K) ≥ d / (6 * K) := by
    have h4 : 5 * d / (6 * K) = d / (6 * K) + 4 * d / (6 * K) := by ring
    rw [h4]
    exact le_add_of_nonneg_right h_pos4
  have h5' : d / K - M_enl - S_enl = d / K - (M_enl + S_enl) := by ring
  rw [h5']
  calc d / K - (M_enl + S_enl)
    ≥ d / K - d / (6 * K) := h1
  _ = 5 * d / (6 * K) := h2
  _ ≥ d / (6 * K) := h3

private lemma directional_lens_c_new_pos (d K M_enl S_enl : ℝ)
    (h_enl_small : M_enl + S_enl < d / K) :
    0 < d / K - M_enl - S_enl := by
  have h_eq : d / K - M_enl - S_enl = d / K - (M_enl + S_enl) := by
    rw [sub_sub]
  rw [h_eq]
  exact sub_pos.mpr h_enl_small

private lemma directional_lens_c_new_ge_full
    (K tangency delta t d V L C0 B X M_enl S_enl M_core : ℝ)
    (hK : 1 ≤ K) (htang : 5 ≤ tangency) (hdelta : 0 < delta) (ht : 0 < t)
    (hdt : delta ≤ t) (hd_ge_2t : 2 * t ≤ d) (hd_le_K : d ≤ K)
    (hsmall : tangency ^ 50 * delta ≤ t / (1000 * K ^ 4))
    (hV : V = 25 * tangency ^ 10 + 2 * tangency + 2)
    (hL : L = Real.sqrt (delta / t))
    (hC0 : C0 = 20 * K * V + 20 * K)
    (hB : B = C0 * L)
    (hX : X = (2 * tangency + 1) * d * L + d * B)
    (hM_enl : M_enl = M_core + S_enl * B)
    (hM_core : M_core = 2 * tangency * delta)
    (hS_enl_le : S_enl ≤ X)
    (hB_pos : 0 < B)
    (hK_pos : 0 < K) (hd_pos : 0 < d) :
    d / K - M_enl - S_enl ≥ d / (6 * K) := by
  have h_le6K : V * delta + X * B + X ≤ d / (6 * K) :=
    enlarged_bounds_le_6K_explicit hK htang hdelta ht hdt hd_ge_2t hd_le_K hsmall hV hL hC0 hB hX
  have h_MplusS : M_enl + S_enl ≤ V * delta + X * B + X :=
    directional_lens_M_plus_S_le M_enl S_enl B V delta d L tangency K X M_core
      hM_enl hM_core hV hS_enl_le hB_pos.le hdelta htang
  have h5 : M_enl + S_enl ≤ d / (6 * K) := h_MplusS.trans h_le6K
  exact directional_lens_c_new_ge d K M_enl S_enl hK_pos hd_pos h5

/-- Prove 0 < S_core outside saturated context. -/
private lemma directional_lens_basic_nonneg
    (K tangency d L delta t B V C0 S_core S_enl : ℝ)
    (hK : 1 ≤ K) (htang : 5 ≤ tangency) (hd_pos : 0 < d) (hdelta : 0 < delta) (ht : 0 < t)
    (hL_def : L = Real.sqrt (delta / t))
    (hV_def : V = 25 * tangency ^ 10 + 2 * tangency + 2)
    (hC0_def : C0 = 20 * K * V + 20 * K)
    (hB_def : B = C0 * L)
    (hS_core_def : S_core = (2 * tangency + 1) * d * L)
    (hS_enl_def : S_enl = S_core + d * B) :
    (0 < V) ∧ (0 ≤ V) ∧ (0 ≤ C0) ∧ (0 ≤ B) ∧ (0 < B) ∧ (0 ≤ S_core) ∧ (0 ≤ S_enl) := by
  have hK_pos : 0 < K := by linarith
  have hL_nonneg : 0 ≤ L := by rw [hL_def] <;> exact Real.sqrt_nonneg _
  have hV_pos : 0 < V := by rw [hV_def] <;> positivity
  have hV_nonneg : 0 ≤ V := by positivity
  have hC0_pos : 0 < C0 := by
    rw [hC0_def]
    have hK_pos : 0 < K := by linarith
    nlinarith
  have hC0_nonneg : 0 ≤ C0 := by linarith
  have hL_pos : 0 < L := by
    rw [hL_def]
    exact Real.sqrt_pos.mpr (div_pos hdelta ht)
  have hB_nonneg : 0 ≤ B := by rw [hB_def] <;> exact mul_nonneg hC0_nonneg (by linarith)
  have hB_pos : 0 < B := by
    rw [hB_def]
    exact mul_pos hC0_pos hL_pos
  have hS_core_nonneg : 0 ≤ S_core := by
    rw [hS_core_def, hL_def] <;> positivity
  have hS_enl_nonneg : 0 ≤ S_enl := by
    rw [hS_enl_def] <;> positivity
  exact ⟨hV_pos, hV_nonneg, hC0_nonneg, hB_nonneg, hB_pos, hS_core_nonneg, hS_enl_nonneg⟩

private lemma directional_lens_S_core_pos
    (tangency d L delta t S_core : ℝ) (htang : 5 ≤ tangency) (hd_pos : 0 < d)
    (hdelta : 0 < delta) (ht : 0 < t)
    (hS_core_def : S_core = (2 * tangency + 1) * d * L)
    (hL_def : L = Real.sqrt (delta / t)) : 0 < S_core := by
  rw [hS_core_def, hL_def]
  have h1 : 0 < 2 * tangency + 1 := by linarith
  have h2 : 0 < Real.sqrt (delta / t) := Real.sqrt_pos.mpr (div_pos hdelta ht)
  exact mul_pos (mul_pos h1 hd_pos) h2

/-- Derivative witness for h_down → h1 outside saturated context. -/
private lemma directional_lens_deriv_witness_down
    {h_down h1 : ℝ → ℝ} (h_down_diff1 : Differentiable ℝ h_down)
    (h_down_deriv : ∀ x, deriv h_down x = h1 x) (x : ℝ) :
    HasDerivAt h_down (h1 x) x := by
  have hder : HasDerivAt h_down (deriv h_down x) x := (h_down_diff1 x).hasDerivAt
  have h_eq : deriv h_down x = h1 x := h_down_deriv x
  rw [h_eq] at hder
  exact hder

/-- Derivative witness for h_up → h1 outside saturated context. -/
private lemma directional_lens_deriv_witness_up
    {h_up h1 : ℝ → ℝ} (h_up_diff1 : Differentiable ℝ h_up)
    (h_up_deriv : ∀ x, deriv h_up x = h1 x) (x : ℝ) :
    HasDerivAt h_up (h1 x) x := by
  have hder : HasDerivAt h_up (deriv h_up x) x := (h_up_diff1 x).hasDerivAt
  have h_eq : deriv h_up x = h1 x := h_up_deriv x
  rw [h_eq] at hder
  exact hder

/-- Derivative witness for h1 → h2 outside saturated context. -/
private lemma directional_lens_deriv_witness1
    {h1 h2 : ℝ → ℝ} (h1_diff : Differentiable ℝ h1)
    (h_deriv2 : ∀ x, deriv h1 x = h2 x) (x : ℝ) :
    HasDerivAt h1 (h2 x) x := by
  have hder : HasDerivAt h1 (deriv h1 x) x := (h1_diff x).hasDerivAt
  have h_eq : deriv h1 x = h2 x := h_deriv2 x
  rw [h_eq] at hder
  exact hder

/-- Convert absolute-value lower bound to direct lower bound when function is positive. -/
private lemma directional_lens_abs_to_pos
    {c_new : ℝ} {h2 : ℝ → ℝ} {a b : ℝ}
    (h2_abs_lower : ∀ x ∈ Icc a b, c_new ≤ |h2 x|)
    (h2_pos : ∀ x ∈ Icc a b, 0 < h2 x) :
    ∀ x ∈ Icc a b, c_new ≤ h2 x := by
  intro x hx
  have h1 : c_new ≤ |h2 x| := h2_abs_lower x hx
  have h2p : 0 < h2 x := h2_pos x hx
  rw [abs_of_pos h2p] at h1
  exact h1

private lemma directional_lens_curvature_t_eq
    (curvature d K t : ℝ) (hcurvature_def : curvature = d / (6 * K * t))
    (hK_pos : 0 < K) (ht : 0 < t) :
    curvature * t = d / (6 * K) := by
  rw [hcurvature_def]
  have h_ne1 : (6 * K * t) ≠ 0 := by positivity
  have h_ne2 : (6 * K) ≠ 0 := by positivity
  field_simp [h_ne1, h_ne2] <;> ring

private lemma directional_lens_h1_bound_enl
    {h1 h2 : ℝ → ℝ} {x0 B S_core S_enl d a b : ℝ}
    (hB_nonneg : 0 ≤ B) (hd_pos : 0 < d)
    (h1_diff : Differentiable ℝ h1)
    (h_deriv2 : ∀ y, deriv h1 y = h2 y)
    (h2_bound : ∀ x ∈ Icc a b, |h2 x| ≤ d)
    (hx0_core : |h1 x0| ≤ S_core)
    (hS_enl_def : S_enl = S_core + d * B)
    (ha_def : a = x0 - B) (hb_def : b = x0 + B) :
    ∀ x ∈ Icc a b, |h1 x| ≤ S_enl := by
  have h2_bound' : ∀ x ∈ Icc (x0 - B) (x0 + B), |h2 x| ≤ d := by
    intro x hx
    have hx' : x ∈ Icc a b := directional_lens_interval_conv ha_def hb_def hx
    exact h2_bound x hx'
  have h'_deriv : ∀ y ∈ Ioo (x0 - B) (x0 + B), HasDerivAt h1 (h2 y) y := by
    intro y _
    have hda : DifferentiableAt ℝ h1 y := h1_diff.differentiableAt
    have hder : HasDerivAt h1 (deriv h1 y) y := hda.hasDerivAt
    have h_eq : deriv h1 y = h2 y := h_deriv2 y
    rw [h_eq] at hder
    exact hder
  intro x hx
  have hx' : x ∈ Icc (x0 - B) (x0 + B) := by
    have h_left : x0 - B ≤ x := by
      calc x0 - B = a := ha_def.symm
        _ ≤ x := hx.1
    have h_right : x ≤ x0 + B := by
      calc x ≤ b := hx.2
        _ = x0 + B := hb_def
    exact ⟨h_left, h_right⟩
  have h_result : |h1 x| ≤ S_core + d * B :=
    enlarged_deriv_bound hB_nonneg hd_pos.le
      h1_diff.continuous.continuousOn h'_deriv h2_bound' hx0_core x hx'
  have h_eq : S_core + d * B = S_enl := by
    rw [hS_enl_def] <;> ring
  rw [h_eq] at h_result
  exact h_result

private lemma directional_lens_enlarged_bounds_full
    (K tangency delta t d V L C0 B S_enl M_enl M_core S_core : ℝ)
    (hK : 1 ≤ K) (htang : 5 ≤ tangency) (hdelta : 0 < delta) (ht : 0 < t)
    (hdt : delta ≤ t) (hd_ge_2t : 2 * t ≤ d) (hd_le_K : d ≤ K)
    (hsmall : tangency ^ 50 * delta ≤ t / (1000 * K ^ 4))
    (hV : V = 25 * tangency ^ 10 + 2 * tangency + 2)
    (hL : L = Real.sqrt (delta / t))
    (hC0 : C0 = 20 * K * V + 20 * K)
    (hB : B = C0 * L)
    (hM_enl : M_enl = M_core + S_enl * B)
    (hM_core : M_core = 2 * tangency * delta)
    (hS_enl : S_enl = S_core + d * B)
    (hS_core : S_core = (2 * tangency + 1) * d * L)
    (hB_pos : 0 < B) (hK_pos : 0 < K) (hd_pos : 0 < d) :
    (M_enl + S_enl < d / K) ∧ (d / K - M_enl - S_enl ≥ d / (6 * K)) := by
  let X : ℝ := (2 * tangency + 1) * d * L + d * B
  have hX : X = (2 * tangency + 1) * d * L + d * B := by rfl
  have h_small_result : V * delta + X * B + X < d / K :=
    enlarged_bounds_small_explicit hK htang hdelta ht hdt hd_ge_2t hd_le_K hsmall hV hL hC0 hB hX
  have hS_enl_le : S_enl ≤ X :=
    directional_lens_S_enl_le S_enl S_core d B L tangency hS_enl hS_core
  have hM_enl_le : M_enl ≤ V * delta + S_enl * B :=
    directional_lens_M_enl_le tangency delta V S_enl B M_enl M_core hV hM_enl hM_core hdelta htang
  have h_enl_small : M_enl + S_enl < d / K :=
    directional_lens_enl_small M_enl S_enl B V delta d L tangency K X hB_pos.le hM_enl_le hS_enl_le h_small_result
  have hc_new_ge : d / K - M_enl - S_enl ≥ d / (6 * K) :=
    directional_lens_c_new_ge_full K tangency delta t d V L C0 B X M_enl S_enl M_core
      hK htang hdelta ht hdt hd_ge_2t hd_le_K hsmall hV hL hC0 hB hX
      hM_enl hM_core hS_enl_le hB_pos hK_pos hd_pos
  exact ⟨h_enl_small, hc_new_ge⟩

/-- Given a constant-sign disjunction on an enlarged interval and a known positive
sign at a point in the core, deduce the sign is positive everywhere. -/
private lemma directional_lens_match_pos (h2 : ℝ → ℝ) (a b x0 p q : ℝ)
    (h2_sign_enl : (∀ x ∈ Icc a b, 0 < h2 x) ∨ (∀ x ∈ Icc a b, h2 x < 0))
    (h2_pos_core : ∀ x ∈ Icc p q, 0 < h2 x)
    (hx0_core : x0 ∈ Icc p q)
    (ha_lt_p : a < p) (hq_lt_b : q < b) :
    ∀ x ∈ Icc a b, 0 < h2 x := by
  cases h2_sign_enl with
  | inl h_pos => exact h_pos
  | inr h_neg =>
    have h1 : a ≤ x0 := le_trans ha_lt_p.le hx0_core.1
    have h2' : x0 ≤ b := le_trans hx0_core.2 hq_lt_b.le
    have h_x0_in_ab : x0 ∈ Icc a b := ⟨h1, h2'⟩
    have h_contra : h2 x0 < 0 := h_neg x0 h_x0_in_ab
    have h_core_pos : 0 < h2 x0 := h2_pos_core x0 hx0_core
    exact False.elim (not_lt.mpr h_contra.le h_core_pos)

/-- Given a constant-sign disjunction on an enlarged interval and a known negative
sign at a point in the core, deduce the sign is negative everywhere. -/
private lemma directional_lens_match_neg (h2 : ℝ → ℝ) (a b x0 p q : ℝ)
    (h2_sign_enl : (∀ x ∈ Icc a b, 0 < h2 x) ∨ (∀ x ∈ Icc a b, h2 x < 0))
    (h2_neg_core : ∀ x ∈ Icc p q, h2 x < 0)
    (hx0_core : x0 ∈ Icc p q)
    (ha_lt_p : a < p) (hq_lt_b : q < b) :
    ∀ x ∈ Icc a b, h2 x < 0 := by
  cases h2_sign_enl with
  | inr h_neg => exact h_neg
  | inl h_pos =>
    have h1 : a ≤ x0 := le_trans ha_lt_p.le hx0_core.1
    have h2' : x0 ≤ b := le_trans hx0_core.2 hq_lt_b.le
    have h_x0_in_ab : x0 ∈ Icc a b := ⟨h1, h2'⟩
    have h_contra : 0 < h2 x0 := h_pos x0 h_x0_in_ab
    have h_core_neg : h2 x0 < 0 := h2_neg_core x0 hx0_core
    exact False.elim (not_lt.mpr h_core_neg.le h_contra)

/-- Lower bound: if curvature sign is positive everywhere, then `h2 x ≥ curvature * t`. -/
private lemma directional_lens_curvature_lower (h2 : ℝ → ℝ) (a b c_new curvature t d K M_enl S_enl : ℝ)
    (hc_new_def : c_new = d / K - M_enl - S_enl)
    (h2_abs_lower : ∀ x ∈ Icc a b, d / K - M_enl - S_enl ≤ |h2 x|)
    (h2_pos_enl : ∀ x ∈ Icc a b, 0 < h2 x)
    (hc_new_ge : c_new ≥ d / (6 * K))
    (hcurvature_t : curvature * t = d / (6 * K)) :
    ∀ x ∈ Icc a b, curvature * t ≤ h2 x := by
  intro x hx
  have h1 : c_new ≤ h2 x := by
    have h2' : d / K - M_enl - S_enl ≤ |h2 x| := h2_abs_lower x hx
    have h2'' : c_new ≤ |h2 x| := by rw [hc_new_def]; exact h2'
    have h3 : 0 < h2 x := h2_pos_enl x hx
    rw [abs_of_pos h3] at h2''
    exact h2''
  have h4 : curvature * t ≤ c_new := by
    calc curvature * t = d / (6 * K) := hcurvature_t
      _ ≤ c_new := hc_new_ge
  exact le_trans h4 h1

/-- Upper bound: if curvature sign is negative everywhere, then `h2 x ≤ -curvature * t`. -/
private lemma directional_lens_curvature_upper (h2 : ℝ → ℝ) (a b c_new curvature t d K M_enl S_enl : ℝ)
    (hc_new_def : c_new = d / K - M_enl - S_enl)
    (h2_abs_lower : ∀ x ∈ Icc a b, d / K - M_enl - S_enl ≤ |h2 x|)
    (h2_neg_enl : ∀ x ∈ Icc a b, h2 x < 0)
    (hc_new_ge : c_new ≥ d / (6 * K))
    (hcurvature_t : curvature * t = d / (6 * K)) :
    ∀ x ∈ Icc a b, h2 x ≤ -(curvature * t) := by
  intro x hx
  have h1 : d / K - M_enl - S_enl ≤ |h2 x| := h2_abs_lower x hx
  have h1' : c_new ≤ |h2 x| := by rw [hc_new_def]; exact h1
  have h2' : h2 x < 0 := h2_neg_enl x hx
  have h3 : |h2 x| = -h2 x := abs_of_neg h2'
  rw [h3] at h1'
  have h4 : curvature * t ≤ c_new := by
    calc curvature * t = d / (6 * K) := hcurvature_t
      _ ≤ c_new := hc_new_ge
  linarith

private lemma directional_lens_B_ge
    (K tangency delta t d V L C0 B S_core c_new : ℝ)
    (hK : 1 ≤ K) (htang : 5 ≤ tangency) (hdelta : 0 < delta) (ht : 0 < t)
    (hd_ge_2t : 2 * t ≤ d) (hd_pos : 0 < d)
    (hV_def : V = 25 * tangency ^ 10 + 2 * tangency + 2)
    (hL_sq : L ^ 2 = delta / t)
    (hL_nonneg : 0 ≤ L)
    (hC0_def : C0 = 20 * K * V + 20 * K)
    (hB_def : B = C0 * L)
    (hS_core_def : S_core = (2 * tangency + 1) * d * L)
    (hc_new_ge : c_new ≥ d / (6 * K))
    (hc_new_pos : 0 < c_new) :
    B ≥ 2 * S_core / c_new + Real.sqrt (2 * (V * delta) / c_new) := by
  have hK_pos : 0 < K := by
    have h1 : (0 : ℝ) < 1 := by norm_num
    exact lt_of_lt_of_le h1 hK
  have hV_nonneg : 0 ≤ V := by
    rw [hV_def]
    have h_t_pos : 0 ≤ tangency := by linarith
    positivity
  have h1 : c_new ≥ d / (6 * K) := hc_new_ge
  have h2 : 2 * S_core / c_new ≤ 12 * K * (2 * tangency + 1) * L := by
    have h3 : S_core ≤ (2 * tangency + 1) * d * L := by
      rw [hS_core_def] <;> ring_nf <;> exact le_refl _
    have h4 : 0 < c_new := hc_new_pos
    have h51 : 0 < d / (6 * K) := by positivity
    have h52 : 1 / c_new ≤ 1 / (d / (6 * K)) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    have h5 : 2 * S_core / c_new ≤ 2 * ((2 * tangency + 1) * d * L) / (d / (6 * K)) := by
      calc 2 * S_core / c_new
        = 2 * S_core * (1 / c_new) := by ring
      _ ≤ 2 * ((2 * tangency + 1) * d * L) * (1 / c_new) := by gcongr
      _ ≤ 2 * ((2 * tangency + 1) * d * L) * (1 / (d / (6 * K))) := by gcongr
      _ = 2 * ((2 * tangency + 1) * d * L) / (d / (6 * K)) := by ring
    have h6 : 2 * ((2 * tangency + 1) * d * L) / (d / (6 * K)) = 12 * K * (2 * tangency + 1) * L := by
      field_simp [hK_pos.ne', hd_pos.ne'] <;> ring
    rw [h6] at h5; exact h5
  have h7 : Real.sqrt (2 * V * delta / c_new) ≤ L * Real.sqrt (6 * V * K) := by
    have h8 : 2 * V * delta / c_new ≤ 6 * V * K * L ^ 2 := by
      have h9 : 0 < c_new := hc_new_pos
      have h10 : 2 * V * delta / c_new ≤ 2 * V * delta / (d / (6 * K)) := by
        have h101 : 0 ≤ 2 * V * delta := by positivity
        calc 2 * V * delta / c_new
          = (2 * V * delta) * (1 / c_new) := by ring
        _ ≤ (2 * V * delta) * (1 / (d / (6 * K))) := by gcongr
        _ = 2 * V * delta / (d / (6 * K)) := by ring
      have h11 : 2 * V * delta / (d / (6 * K)) = 12 * V * K * delta / d := by
        field_simp [hK_pos.ne', hd_pos.ne'] <;> ring
      rw [h11] at h10
      have h12 : delta / d ≤ L ^ 2 / 2 := by
        rw [hL_sq]
        field_simp [hd_pos.ne', ht.ne'] <;> linarith
      have h13 : 0 ≤ V * K := mul_nonneg hV_nonneg (by linarith)
      have h14 : 12 * V * K * (delta / d) ≤ 12 * V * K * (L ^ 2 / 2) := by gcongr
      have h15 : 12 * V * K * (L ^ 2 / 2) = 6 * V * K * L ^ 2 := by ring
      rw [h15] at h14
      have h10' : 2 * V * delta / c_new ≤ 12 * V * K * (delta / d) := by
        have h_eq : 12 * V * K * delta / d = 12 * V * K * (delta / d) := by ring
        rw [h_eq] at h10
        exact h10
      exact le_trans h10' h14
    have h16 : 0 ≤ 6 * V * K * L ^ 2 := by positivity
    have h17 : Real.sqrt (6 * V * K * L ^ 2) = L * Real.sqrt (6 * V * K) := by
      have h18 : 0 ≤ L := hL_nonneg
      have h19 : Real.sqrt (L ^ 2) = L := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h18]
      have h20 : Real.sqrt (6 * V * K * L ^ 2) = Real.sqrt (6 * V * K) * Real.sqrt (L ^ 2) := by
        rw [←Real.sqrt_mul (by positivity)] <;> ring
      rw [h20, h19] <;> ring
    have h21 : Real.sqrt (2 * V * delta / c_new) ≤ Real.sqrt (6 * V * K * L ^ 2) :=
      Real.sqrt_le_sqrt h8
    rw [h17] at h21
    exact h21
  have h8 : (12 * K * (2 * tangency + 1) + Real.sqrt (6 * V * K)) * L ≤ C0 * L := by
    have h9 : 12 * K * (2 * tangency + 1) + Real.sqrt (6 * V * K) ≤ C0 := by
      have h10 : 12 * K * (2 * tangency + 1) ≤ 36 * K * tangency ^ 10 := by
        have h11 : 2 * tangency + 1 ≤ 3 * tangency := by linarith
        have h12 : tangency ≤ tangency ^ 10 := by
          have h13 : tangency ^ 9 ≥ 1 := by
            have h14 : 1 ≤ tangency := by linarith
            have h15 : (1 : ℝ)^9 ≤ tangency ^ 9 := by
              gcongr <;> linarith
            simpa using h15
          nlinarith
        nlinarith
      have h13_sqrt : Real.sqrt (6 * V * K) ≤ 14 * K * tangency ^ 10 := by
        have h14 : V ≤ 30 * tangency ^ 10 := by
          rw [hV_def]
          have h15 : tangency ^ 10 ≥ 1 := by
            have h16 : 1 ≤ tangency := by linarith
            have h17 : (1 : ℝ)^10 ≤ tangency ^ 10 := by
              gcongr <;> linarith
            simpa using h17
          have h18 : tangency ≤ tangency ^ 10 := by
            have h19 : tangency ^ 9 ≥ 1 := by
              have h20 : 1 ≤ tangency := by linarith
              have h21 : (1 : ℝ)^9 ≤ tangency ^ 9 := by
                gcongr <;> linarith
              simpa using h21
            nlinarith
          nlinarith
        have h15 : 6 * V * K ≤ (14 * K * tangency ^ 10) ^ 2 := by
          have h16 : 6 * V * K ≤ 180 * K * tangency ^ 10 := by
            calc 6 * V * K ≤ 6 * (30 * tangency ^ 10) * K := by gcongr
              _ = 180 * K * tangency ^ 10 := by ring
          set y := K * tangency ^ 10 with hy_def
          have hy_pos : 0 < y := by positivity
          have hy_ge1 : 1 ≤ y := by
            have h1 : 1 ≤ K := hK
            have h2 : 1 ≤ tangency ^ 10 := by
              have h3 : (1 : ℝ) ≤ tangency := by linarith
              have h4 : (1 : ℝ)^10 ≤ tangency^10 := by gcongr
              simpa using h4
            nlinarith
          have h17 : 180 * y ≤ (14 * y) ^ 2 := by
            have h_eq : (14 * y) ^ 2 = 196 * y ^ 2 := by ring
            rw [h_eq]
            have h5 : 0 ≤ y * (196 * y - 180) := by
              have h6 : 0 ≤ y := by linarith
              have h7 : 0 ≤ 196 * y - 180 := by linarith [hy_ge1]
              exact mul_nonneg h6 h7
            have h8 : 196 * y ^ 2 - 180 * y = y * (196 * y - 180) := by ring
            have h9 : 0 ≤ 196 * y ^ 2 - 180 * y := by rw [h8] <;> exact h5
            exact sub_nonneg.mp h9
          have h18 : 180 * K * tangency ^ 10 ≤ (14 * K * tangency ^ 10) ^ 2 := by
            have h19 : 180 * K * tangency ^ 10 = 180 * y := by
              simp only [hy_def] <;> ring
            have h20 : (14 * K * tangency ^ 10) ^ 2 = (14 * y) ^ 2 := by
              simp only [hy_def] <;> ring
            rw [h19, h20]
            exact h17
          exact le_trans h16 h18
        have h20 : 0 ≤ 14 * K * tangency ^ 10 := by positivity
        exact Real.sqrt_le_iff.mpr ⟨by positivity, h15⟩
      have h14 : C0 ≥ 500 * K * tangency ^ 10 := by
        rw [hC0_def]
        have h15 : V ≥ 25 * tangency ^ 10 := by
          rw [hV_def]; nlinarith
        nlinarith
      have h_sum : 12 * K * (2 * tangency + 1) + Real.sqrt (6 * V * K) ≤ 50 * K * tangency ^ 10 := by
        calc
          12 * K * (2 * tangency + 1) + Real.sqrt (6 * V * K)
            ≤ 36 * K * tangency ^ 10 + 14 * K * tangency ^ 10 := add_le_add h10 h13_sqrt
          _ = 50 * K * tangency ^ 10 := by ring
      have h_kt_pos : 0 ≤ K * tangency ^ 10 := by positivity
      have h_50 : 50 * K * tangency ^ 10 ≤ 500 * K * tangency ^ 10 := by
        have h_diff : 500 * K * tangency ^ 10 - 50 * K * tangency ^ 10 = 450 * (K * tangency ^ 10) := by ring
        have h_nonneg : 0 ≤ 450 * (K * tangency ^ 10) := by positivity
        have h : 0 ≤ 500 * K * tangency ^ 10 - 50 * K * tangency ^ 10 := by
          rw [h_diff] <;> exact h_nonneg
        exact sub_nonneg.mp h
      exact le_trans h_sum (le_trans h_50 h14)
    exact mul_le_mul_of_nonneg_right h9 hL_nonneg
  calc B
    = C0 * L := by rw [hB_def]
  _ ≥ (12 * K * (2 * tangency + 1) + Real.sqrt (6 * V * K)) * L := h8
  _ = 12 * K * (2 * tangency + 1) * L + L * Real.sqrt (6 * V * K) := by ring
  _ ≥ 2 * S_core / c_new + Real.sqrt (2 * (V * delta) / c_new) := by
    have h7' : Real.sqrt (2 * (V * delta) / c_new) ≤ L * Real.sqrt (6 * V * K) := by
      have h_eq : 2 * (V * delta) / c_new = 2 * V * delta / c_new := by ring
      rw [h_eq]
      exact h7
    exact add_le_add h2 h7'

/-- Helper: value bound on enlarged interval using Lipschitz estimate. -/
private lemma directional_lens_value_bound_enl
    {h0 h1 : ℝ → ℝ} {x0 B M_core S_enl a b : ℝ}
    (hB_nonneg : 0 ≤ B)
    (hS_enl_nonneg : 0 ≤ S_enl)
    (h0_diff : Differentiable ℝ h0)
    (h1_bound : ∀ y ∈ Icc (x0 - B) (x0 + B), |h1 y| ≤ S_enl)
    (h_deriv1 : ∀ y, deriv h0 y = h1 y)
    (hx0_core' : |h0 x0| ≤ M_core)
    (ha_def : a = x0 - B) (hb_def : b = x0 + B)
    {x : ℝ} (hx : x ∈ Icc a b) :
    |h0 x| ≤ M_core + S_enl * B := by
  have hx' : x ∈ Icc (x0 - B) (x0 + B) := by
    have h_left : x0 - B ≤ x := by
      calc x0 - B = a := ha_def.symm
        _ ≤ x := hx.1
    have h_right : x ≤ x0 + B := by
      calc x ≤ b := hx.2
        _ = x0 + B := hb_def
    exact ⟨h_left, h_right⟩
  have h_cont : ContinuousOn h0 (Icc (x0 - B) (x0 + B)) :=
    (Differentiable.continuous h0_diff).continuousOn
  have h_deriv_bound' : ∀ y ∈ Icc (x0 - B) (x0 + B), |deriv h0 y| ≤ S_enl := by
    intro y hy
    have h_eq : deriv h0 y = h1 y := h_deriv1 y
    rw [h_eq]
    exact h1_bound y hy
  have h_da : ∀ (x : ℝ), DifferentiableAt ℝ h0 x := by
    intro x
    exact h0_diff.differentiableAt
  exact enlarged_value_bound (h := h0) (h' := deriv h0) (x0 := x0) (B := B) (M := M_core) (S' := S_enl)
    hB_nonneg hS_enl_nonneg h_cont
    (fun x _ => (h_da x).hasDerivAt)
    h_deriv_bound' hx0_core' x hx'

/-- Wrapper for convex_two_zeros_localized_to_rectangle that converts core bounds
from `Icc p q` to `Icc R.interval.left R.interval.right`. -/
private lemma directional_lens_convex_zeros
    {h_down : ℝ → ℝ} {delta t curvature V d a b p q : ℝ}
    {R : CurvilinearRectangle delta t}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hcurv_pos : 0 < curvature)
    (hV_nonneg : 0 ≤ V) (hdt_nonneg : 0 ≤ d / t)
    (ha_lt_p : a < R.interval.left) (hq_lt_b : R.interval.right < b)
    (h_down_diff1 : Differentiable ℝ h_down)
    (h_down_diff2 : Differentiable ℝ (deriv h_down))
    (h''_lower : ∀ x ∈ Icc a b, curvature * t ≤ deriv (deriv h_down) x)
    (h''_upper : ∀ x ∈ Icc R.interval.left R.interval.right, |deriv (deriv h_down) x| ≤ (d / t) * t)
    (h_core_bound_pq : ∀ x ∈ Icc p q, |h_down x| ≤ V * delta)
    (h_core_neg_pq : ∀ x ∈ Icc p q, h_down x < 0)
    (ha_pos : 0 < h_down a) (hb_pos : 0 < h_down b)
    (hp_def : p = R.interval.left) (hq_def : q = R.interval.right) :
  let C := 2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature)
  ∃ z1 z2 : ℝ,
    a < z1 ∧ z1 < z2 ∧ z2 < b ∧
    h_down z1 = 0 ∧ h_down z2 = 0 ∧
    deriv h_down z1 < 0 ∧ 0 < deriv h_down z2 ∧
    (∀ x, z1 < x → x < z2 → h_down x < 0) ∧
    z1 ∈ Icc (R.interval.left - C * Real.sqrt (delta / t)) (R.interval.right + C * Real.sqrt (delta / t)) ∧
    z2 ∈ Icc (R.interval.left - C * Real.sqrt (delta / t)) (R.interval.right + C * Real.sqrt (delta / t)) := by
  have h_core_bound : ∀ x ∈ Icc R.interval.left R.interval.right, |h_down x| ≤ V * delta := by
    intro x hx
    have hx' : x ∈ Icc p q := by
      exact ⟨hp_def.symm ▸ hx.1, hq_def.symm ▸ hx.2⟩
    exact h_core_bound_pq x hx'
  have h_core_neg : ∀ x ∈ Icc R.interval.left R.interval.right, h_down x < 0 := by
    intro x hx
    have hx' : x ∈ Icc p q := by
      exact ⟨hp_def.symm ▸ hx.1, hq_def.symm ▸ hx.2⟩
    exact h_core_neg_pq x hx'
  exact convex_two_zeros_localized_to_rectangle
    hdelta ht hcurv_pos hV_nonneg hdt_nonneg
    R ha_lt_p hq_lt_b h_down_diff1 h_down_diff2
    h''_lower h''_upper h_core_bound h_core_neg ha_pos hb_pos

/-- Construct h''_abs for concave case outside saturated context. -/
private lemma directional_lens_h''_abs_concave
    {h_up h2 : ℝ → ℝ} {delta t : ℝ} {R : CurvilinearRectangle delta t} {p q d : ℝ}
    (h_up_deriv2 : ∀ x, deriv (deriv h_up) x = h2 x)
    (h2_bound_core : ∀ x ∈ Icc p q, |h2 x| ≤ d)
    (hp_def : p = R.interval.left) (hq_def : q = R.interval.right)
    (ht : 0 < t) :
    ∀ (x : ℝ), x ∈ Icc R.interval.left R.interval.right → |deriv (deriv h_up) x| ≤ (d / t) * t :=
  fun x hx => by
    have h_eq : deriv (deriv h_up) x = h2 x := h_up_deriv2 x
    rw [h_eq]
    have h1' : p ≤ x := by
      have h : p = R.interval.left := hp_def
      rw [h]
      exact hx.1
    have h2' : x ≤ q := by
      have h : R.interval.right = q := hq_def.symm
      rw [h] at hx
      exact hx.2
    have hx' : x ∈ Icc p q := ⟨h1', h2'⟩
    have h_bound : |h2 x| ≤ d := h2_bound_core x hx'
    have h_dt : (d / t) * t = d := div_mul_cancel₀ d ht.ne'
    have h_goal : |h2 x| ≤ (d / t) * t := by
      rw [h_dt]
      exact h_bound
    exact h_goal

/-- Wrapper for concave_two_zeros_localized_to_rectangle to avoid elaboration in saturated context. -/
private lemma directional_lens_concave_zeros
    {h_up h2 : ℝ → ℝ} {delta t curvature V d a b p q : ℝ}
    {R : CurvilinearRectangle delta t}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hcurv_pos : 0 < curvature)
    (hV_nonneg : 0 ≤ V) (hdt_nonneg : 0 ≤ d / t)
    (ha_lt_p : a < R.interval.left) (hq_lt_b : R.interval.right < b)
    (h_up_diff1 : Differentiable ℝ h_up)
    (h_up_diff2 : Differentiable ℝ (deriv h_up))
    (h_up_deriv2 : ∀ x, deriv (deriv h_up) x = h2 x)
    (h2_bound_core : ∀ x ∈ Icc p q, |h2 x| ≤ d)
    (h''_upper : ∀ x ∈ Icc a b, deriv (deriv h_up) x ≤ -(curvature * t))
    (h_core_bound_pq : ∀ x ∈ Icc p q, |h_up x| ≤ V * delta)
    (h_core_pos_pq : ∀ x ∈ Icc p q, 0 < h_up x)
    (ha_neg : h_up a < 0) (hb_neg : h_up b < 0)
    (hp_def : p = R.interval.left) (hq_def : q = R.interval.right) :
  ∃ z1 z2 : ℝ,
    a < z1 ∧ z1 < z2 ∧ z2 < b ∧
    h_up z1 = 0 ∧ h_up z2 = 0 ∧
    0 < deriv h_up z1 ∧ deriv h_up z2 < 0 ∧
    (∀ x, z1 < x → x < z2 → 0 < h_up x) ∧
    z1 ∈ Icc (R.interval.left - (2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature)) * Real.sqrt (delta / t))
                (R.interval.right + (2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature)) * Real.sqrt (delta / t)) ∧
    z2 ∈ Icc (R.interval.left - (2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature)) * Real.sqrt (delta / t))
                (R.interval.right + (2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature)) * Real.sqrt (delta / t)) := by
  have h''_abs : ∀ x ∈ Icc R.interval.left R.interval.right, |deriv (deriv h_up) x| ≤ (d / t) * t :=
    directional_lens_h''_abs_concave h_up_deriv2 h2_bound_core hp_def hq_def ht
  have h_core_bound : ∀ x ∈ Icc R.interval.left R.interval.right, |h_up x| ≤ V * delta := by
    intro x hx
    have hx' : x ∈ Icc p q := by
      exact ⟨hp_def.symm ▸ hx.1, hq_def.symm ▸ hx.2⟩
    exact h_core_bound_pq x hx'
  have h_core_pos : ∀ x ∈ Icc R.interval.left R.interval.right, 0 < h_up x := by
    intro x hx
    have hx' : x ∈ Icc p q := by
      exact ⟨hp_def.symm ▸ hx.1, hq_def.symm ▸ hx.2⟩
    exact h_core_pos_pq x hx'
  have h_main := concave_two_zeros_localized_to_rectangle
    hdelta ht hcurv_pos hV_nonneg hdt_nonneg
    R ha_lt_p hq_lt_b h_up_diff1 h_up_diff2
    h''_upper h''_abs h_core_bound h_core_pos ha_neg hb_neg
  exact h_main

/-- Wrapper for concave_zeros to avoid type inference in saturated context. -/
private lemma directional_lens_concave_zeros_wrapper
    {h_up h2 : ℝ → ℝ} {delta t curvature V d a b p q E : ℝ}
    {R : CurvilinearRectangle delta t}
    (hE_def : E = 2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature))
    (hdelta : 0 < delta) (ht : 0 < t) (hcurv_pos : 0 < curvature)
    (hV_nonneg : 0 ≤ V) (hdt_nonneg : 0 ≤ d / t)
    (ha_lt_p : a < R.interval.left) (hq_lt_b : R.interval.right < b)
    (h_up_diff1 : Differentiable ℝ h_up)
    (h_up_diff2 : Differentiable ℝ (deriv h_up))
    (h_up_deriv2 : ∀ x, deriv (deriv h_up) x = h2 x)
    (h2_bound_core : ∀ x ∈ Icc p q, |h2 x| ≤ d)
    (h''_upper : ∀ x ∈ Icc a b, deriv (deriv h_up) x ≤ -(curvature * t))
    (h_core_bound_pq : ∀ x ∈ Icc p q, |h_up x| ≤ V * delta)
    (h_core_pos_pq : ∀ x ∈ Icc p q, 0 < h_up x)
    (ha_neg : h_up a < 0) (hb_neg : h_up b < 0)
    (hp_def : p = R.interval.left) (hq_def : q = R.interval.right) :
    ∃ z1 z2 : ℝ, a < z1 ∧ z1 < z2 ∧ z2 < b ∧
      h_up z1 = 0 ∧ h_up z2 = 0 ∧
      0 < deriv h_up z1 ∧ deriv h_up z2 < 0 ∧
      (∀ x, z1 < x → x < z2 → 0 < h_up x) ∧
      z1 ∈ Icc (R.interval.left - E * Real.sqrt (delta / t)) (R.interval.right + E * Real.sqrt (delta / t)) ∧
      z2 ∈ Icc (R.interval.left - E * Real.sqrt (delta / t)) (R.interval.right + E * Real.sqrt (delta / t)) := by
  have h_main := directional_lens_concave_zeros
    (h_up := h_up) (h2 := h2) (R := R)
    hdelta ht hcurv_pos hV_nonneg hdt_nonneg
    ha_lt_p hq_lt_b h_up_diff1 h_up_diff2
    h_up_deriv2 h2_bound_core h''_upper
    h_core_bound_pq h_core_pos_pq ha_neg hb_neg hp_def hq_def
  simpa [hE_def] using h_main

/-- Wrapper for curvature_constant_sign to avoid elaboration in saturated context. -/
private lemma directional_lens_curv_sign_wrapper
    {h0 h1 h2 : ℝ → ℝ} {a b d K M_enl S_enl : ℝ}
    (hab : a < b) (hK : 1 ≤ K) (hd_pos : 0 < d)
    (h2_cont : Continuous h2)
    (hcurv_gap : ∀ x ∈ Icc a b, d / K ≤ |h0 x| + |h1 x| + |h2 x|)
    (h0_bound : ∀ x ∈ Icc a b, |h0 x| ≤ M_enl)
    (h1_bound : ∀ x ∈ Icc a b, |h1 x| ≤ S_enl)
    (h_small : M_enl + S_enl < d / K) :
    (∀ x ∈ Icc a b, d / K - M_enl - S_enl ≤ |h2 x|) ∧
    ((∀ x ∈ Icc a b, 0 < h2 x) ∨ (∀ x ∈ Icc a b, h2 x < 0)) :=
  curvature_constant_sign (h := h0) (h' := h1) (h'' := h2)
    (a := a) (b := b) (d := d) (K := K) (M := M_enl) (M' := S_enl)
    hab hK hd_pos h2_cont.continuousOn hcurv_gap h0_bound h1_bound h_small

/-- Combined wrapper: establish M_enl + S_enl < d/K without exposing X in saturated context. -/
private lemma directional_lens_enl_small_combined
    (K tangency delta t d V L C0 B S_enl M_enl M_core S_core : ℝ)
    (hK : 1 ≤ K) (htang : 5 ≤ tangency) (hdelta : 0 < delta) (ht : 0 < t)
    (hdt : delta ≤ t) (hd_ge_2t : 2 * t ≤ d) (hd_le_K : d ≤ K)
    (hsmall : tangency ^ 50 * delta ≤ t / (1000 * K ^ 4))
    (hV_def : V = 25 * tangency ^ 10 + 2 * tangency + 2)
    (hL_def : L = Real.sqrt (delta / t))
    (hC0_def : C0 = 20 * K * V + 20 * K)
    (hB_def : B = C0 * L)
    (hM_enl_def : M_enl = M_core + S_enl * B)
    (hM_core_def : M_core = 2 * tangency * delta)
    (hS_enl_def : S_enl = S_core + d * B)
    (hS_core_def : S_core = (2 * tangency + 1) * d * L)
    (hB_pos : 0 < B) :
    M_enl + S_enl < d / K := by
  let X : ℝ := (2 * tangency + 1) * d * L + d * B
  have hX_def : X = (2 * tangency + 1) * d * L + d * B := by rfl
  have h_small_result : V * delta + X * B + X < d / K :=
    enlarged_bounds_small_explicit hK htang hdelta ht hdt hd_ge_2t hd_le_K hsmall
      hV_def hL_def hC0_def hB_def hX_def
  have hM_enl_le : M_enl ≤ V * delta + S_enl * B :=
    directional_lens_M_enl_le tangency delta V S_enl B M_enl M_core hV_def hM_enl_def hM_core_def hdelta htang
  have hS_enl_le : S_enl ≤ X := by
    have h : S_enl ≤ (2 * tangency + 1) * d * L + d * B :=
      directional_lens_S_enl_le S_enl S_core d B L tangency hS_enl_def hS_core_def
    have hX : (2 * tangency + 1) * d * L + d * B = X := hX_def.symm
    exact le_trans h (le_of_eq hX)
  exact directional_lens_enl_small M_enl S_enl B V delta d L tangency K X hB_pos.le hM_enl_le hS_enl_le h_small_result

/-- Wrapper for convex_sign_change_at_distance with Differentiable arguments.
All lambda construction happens in this clean context. -/
private lemma directional_lens_convex_sign_change_wrapper
    {h_down h1 h2 : ℝ → ℝ} {x0 B a b c_new V_delta S_core : ℝ}
    (ha_def : a = x0 - B) (hb_def : b = x0 + B)
    (hc_new_pos : 0 < c_new) (hS_core_pos : 0 < S_core) (hB_pos : 0 < B)
    (h_down_diff1 : Differentiable ℝ h_down)
    (h1_diff : Differentiable ℝ h1)
    (h_down_deriv_eq : ∀ x, deriv h_down x = h1 x)
    (h_deriv2 : ∀ x, deriv h1 x = h2 x)
    (h2_ge : ∀ x ∈ Icc a b, c_new ≤ h2 x)
    (h_down_x0_val : |h_down x0| ≤ V_delta)
    (h1_x0_bound : |h1 x0| ≤ S_core)
    (h_down_x0_neg : h_down x0 < 0)
    (hB_ge : B ≥ 2 * S_core / c_new + Real.sqrt (2 * V_delta / c_new)) :
    h_down (x0 + B) > 0 ∧ h_down (x0 - B) > 0 := by
  let h_down_cont : ContinuousOn h_down (Icc (x0 - B) (x0 + B)) :=
    h_down_diff1.continuous.continuousOn
  let h1_cont : ContinuousOn h1 (Icc (x0 - B) (x0 + B)) :=
    h1_diff.continuous.continuousOn
  let h_down_deriv' : ∀ x ∈ Ioo (x0 - B) (x0 + B), HasDerivAt h_down (h1 x) x :=
    fun x _ => directional_lens_deriv_witness_down h_down_diff1 h_down_deriv_eq x
  let h1_deriv' : ∀ x ∈ Ioo (x0 - B) (x0 + B), HasDerivAt h1 (h2 x) x :=
    fun x _ => directional_lens_deriv_witness1 h1_diff h_deriv2 x
  let h2_ge' : ∀ x ∈ Ioo (x0 - B) (x0 + B), c_new ≤ h2 x :=
    fun x hx => h2_ge x (directional_lens_interval_conv ha_def hb_def (Ioo_subset_Icc_self hx))
  exact convex_sign_change_at_distance
    (h := h_down) (h' := h1) (h'' := h2) (x0 := x0) (B := B) (c := c_new) (M := V_delta) (S := S_core)
    hc_new_pos hS_core_pos hB_pos h_down_cont h1_cont h_down_deriv' h1_deriv' h2_ge'
    h_down_x0_val h1_x0_bound h_down_x0_neg hB_ge

/-- Wrapper for concave_sign_change_at_distance with Differentiable arguments.
All lambda construction happens in this clean context. -/
private lemma directional_lens_concave_sign_change_wrapper
    {h_up h1 h2 : ℝ → ℝ} {x0 B a b c_new V_delta S_core : ℝ}
    (ha_def : a = x0 - B) (hb_def : b = x0 + B)
    (hc_new_pos : 0 < c_new) (hS_core_pos : 0 < S_core) (hB_pos : 0 < B)
    (h_up_diff1 : Differentiable ℝ h_up)
    (h1_diff : Differentiable ℝ h1)
    (h_up_deriv_eq : ∀ x, deriv h_up x = h1 x)
    (h_deriv2 : ∀ x, deriv h1 x = h2 x)
    (h2_le : ∀ x ∈ Icc a b, h2 x ≤ -c_new)
    (h_up_x0_val : |h_up x0| ≤ V_delta)
    (h1_x0_bound : |h1 x0| ≤ S_core)
    (h_up_x0_pos : 0 < h_up x0)
    (hB_ge : B ≥ 2 * S_core / c_new + Real.sqrt (2 * V_delta / c_new)) :
    h_up (x0 + B) < 0 ∧ h_up (x0 - B) < 0 := by
  let h_up_cont : ContinuousOn h_up (Icc (x0 - B) (x0 + B)) :=
    h_up_diff1.continuous.continuousOn
  let h1_cont : ContinuousOn h1 (Icc (x0 - B) (x0 + B)) :=
    h1_diff.continuous.continuousOn
  let h_up_deriv' : ∀ x ∈ Ioo (x0 - B) (x0 + B), HasDerivAt h_up (h1 x) x :=
    fun x _ => directional_lens_deriv_witness_up h_up_diff1 h_up_deriv_eq x
  let h1_deriv' : ∀ x ∈ Ioo (x0 - B) (x0 + B), HasDerivAt h1 (h2 x) x :=
    fun x _ => directional_lens_deriv_witness1 h1_diff h_deriv2 x
  let h2_le' : ∀ x ∈ Ioo (x0 - B) (x0 + B), h2 x ≤ -c_new :=
    fun x hx => h2_le x (directional_lens_interval_conv ha_def hb_def (Ioo_subset_Icc_self hx))
  exact concave_sign_change_at_distance
    (h := h_up) (h' := h1) (h'' := h2) (x0 := x0) (B := B) (c := c_new) (M := V_delta) (S := S_core)
    hc_new_pos hS_core_pos hB_pos h_up_cont h1_cont h_up_deriv' h1_deriv' h2_le'
    h_up_x0_val h1_x0_bound h_up_x0_pos hB_ge

/-- Extract sign change results with endpoint rewriting outside saturated context. -/
private lemma directional_lens_extract_sign_change
    {h_up : ℝ → ℝ} {x0 B a b : ℝ}
    (ha_def : a = x0 - B) (hb_def : b = x0 + B)
    (h : h_up (x0 + B) < 0 ∧ h_up (x0 - B) < 0) :
    (h_up b < 0) ∧ (h_up a < 0) := by
  have h1 : h_up b < 0 := by
    rw [hb_def]
    exact h.1
  have h2 : h_up a < 0 := by
    rw [ha_def]
    exact h.2
  exact ⟨h1, h2⟩

/-- Construct h''_lower for convex case outside saturated context. -/
private lemma directional_lens_h''_lower_convex
    {h_down h2 : ℝ → ℝ} {a b curvature t : ℝ}
    (h_down_deriv2 : ∀ x, deriv (deriv h_down) x = h2 x)
    (h2_lower_enl : ∀ x ∈ Icc a b, curvature * t ≤ h2 x) :
    ∀ x ∈ Icc a b, curvature * t ≤ deriv (deriv h_down) x :=
  fun x hx => by
    have h_eq : deriv (deriv h_down) x = h2 x := h_down_deriv2 x
    rw [h_eq]
    exact h2_lower_enl x hx

/-- Construct h''_upper for convex case outside saturated context. -/
private lemma directional_lens_h''_upper_convex
    {h_down h2 : ℝ → ℝ} {delta t : ℝ} {R : CurvilinearRectangle delta t} {p q d : ℝ}
    (h_down_deriv2 : ∀ x, deriv (deriv h_down) x = h2 x)
    (h2_bound_core : ∀ x ∈ Icc p q, |h2 x| ≤ d)
    (hp_def : p = R.interval.left) (hq_def : q = R.interval.right)
    (ht : 0 < t) :
    ∀ (x : ℝ), x ∈ Icc R.interval.left R.interval.right → |deriv (deriv h_down) x| ≤ (d / t) * t :=
  fun x hx => by
    have h_eq : deriv (deriv h_down) x = h2 x := h_down_deriv2 x
    have h1' : p ≤ x := by
      have h : p = R.interval.left := hp_def
      rw [h]
      exact hx.1
    have h2' : x ≤ q := by
      have h : R.interval.right = q := hq_def.symm
      rw [h] at hx
      exact hx.2
    have hx' : x ∈ Icc p q := ⟨h1', h2'⟩
    have h_bound : |h2 x| ≤ d := h2_bound_core x hx'
    have h_dt : (d / t) * t = d := div_mul_cancel₀ d ht.ne'
    have h_goal : |h2 x| ≤ (d / t) * t := by
      rw [h_dt]
      exact h_bound
    rw [h_eq]
    exact h_goal

/-- Construct h''_upper for concave case outside saturated context. -/
private lemma directional_lens_h''_upper_concave
    {h_up h2 : ℝ → ℝ} {a b curvature t : ℝ}
    (h_up_deriv2 : ∀ x, deriv (deriv h_up) x = h2 x)
    (h2_upper_enl : ∀ x ∈ Icc a b, h2 x ≤ -(curvature * t)) :
    ∀ x ∈ Icc a b, deriv (deriv h_up) x ≤ -(curvature * t) :=
  fun x hx => by
    have h_eq : deriv (deriv h_up) x = h2 x := h_up_deriv2 x
    rw [h_eq]
    exact h2_upper_enl x hx

/-- Prove z ∈ [0,1] from interval bounds outside saturated context. -/
private lemma directional_lens_z_in_01
    {z a b : ℝ} (ha_ge0 : 0 ≤ a) (hb_le1 : b ≤ 1)
    (hz_a : a ≤ z) (hz_b : z ≤ b) : z ∈ Icc (0 : ℝ) 1 :=
  ⟨by linarith, by linarith⟩

/-- Prove both z1, z2 ∈ [0,1] from a < z1 < z2 < b outside saturated context. -/
private lemma directional_lens_both_zeros_in_01
    {z1 z2 a b : ℝ} (ha_ge0 : 0 ≤ a) (hb_le1 : b ≤ 1)
    (hz1_a : a < z1) (hz12 : z1 < z2) (hz2_b : z2 < b) :
    (z1 ∈ Icc (0 : ℝ) 1) ∧ (z2 ∈ Icc (0 : ℝ) 1) :=
  ⟨directional_lens_z_in_01 ha_ge0 hb_le1 (le_of_lt hz1_a) (le_of_lt (lt_trans hz12 hz2_b)),
   directional_lens_z_in_01 ha_ge0 hb_le1 (le_of_lt (lt_trans hz1_a hz12)) (le_of_lt hz2_b)⟩

/-- Prove z1 ∈ [0,1] from interval ordering outside saturated context. -/
private lemma directional_lens_z1_in_01
    {z1 z2 a b : ℝ} (ha_ge0 : 0 ≤ a) (hb_le1 : b ≤ 1)
    (hz1_a : a < z1) (hz12 : z1 < z2) (hz2_b : z2 < b) : z1 ∈ Icc (0 : ℝ) 1 :=
  directional_lens_z_in_01 ha_ge0 hb_le1 (le_of_lt hz1_a) (le_of_lt (lt_trans hz12 hz2_b))

/-- Prove z2 ∈ [0,1] from interval ordering outside saturated context. -/
private lemma directional_lens_z2_in_01
    {z1 z2 a b : ℝ} (ha_ge0 : 0 ≤ a) (hb_le1 : b ≤ 1)
    (hz1_a : a < z1) (hz12 : z1 < z2) (hz2_b : z2 < b) : z2 ∈ Icc (0 : ℝ) 1 :=
  directional_lens_z_in_01 ha_ge0 hb_le1 (le_of_lt (lt_trans hz1_a hz12)) (le_of_lt hz2_b)

/-- Convert zeros localization interval to E*L form outside saturated context. -/
private lemma directional_lens_localize_interval
    {delta t : ℝ} {z : ℝ} {R : CurvilinearRectangle delta t} {V d curvature E L : ℝ}
    (hE_def : E = 2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature))
    (hL_def : L = Real.sqrt (delta / t))
    (hz_loc : z ∈ Icc (R.interval.left - (2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature)) * Real.sqrt (delta / t))
                                (R.interval.right + (2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature)) * Real.sqrt (delta / t))) :
    z ∈ Icc (R.interval.left - E * L) (R.interval.right + E * L) := by
  let C := 2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature)
  have hC : C * Real.sqrt (delta / t) = E * L := by
    dsimp only [C]
    rw [hE_def, hL_def] <;> ring
  have h_left : R.interval.left - C * Real.sqrt (delta / t) = R.interval.left - E * L := by rw [hC]
  have h_right : R.interval.right + C * Real.sqrt (delta / t) = R.interval.right + E * L := by rw [hC]
  have h_goal : z ∈ Icc (R.interval.left - E * L) (R.interval.right + E * L) := by
    convert hz_loc using 1 <;> rw [hC]
  exact h_goal

/-- Wrapper for localize_interval with all explicit parameters to avoid saturated-context inference. -/
private lemma directional_lens_localize_interval_explicit
    (delta t z V d curvature E L : ℝ) (R : CurvilinearRectangle delta t)
    (hE_def : E = 2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature))
    (hL_def : L = Real.sqrt (delta / t))
    (hz_loc : z ∈ Icc (R.interval.left - (2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature)) * Real.sqrt (delta / t))
                                (R.interval.right + (2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature)) * Real.sqrt (delta / t))) :
    z ∈ Icc (R.interval.left - E * L) (R.interval.right + E * L) :=
  directional_lens_localize_interval (hE_def := hE_def) (hL_def := hL_def) hz_loc

/-- Combine two localize_interval calls into one outside saturated context. -/
private lemma directional_lens_both_localize
    (delta t z1 z2 V d curvature E L : ℝ) (R : CurvilinearRectangle delta t)
    (hE_def : E = 2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature))
    (hL_def : L = Real.sqrt (delta / t))
    (hz1_loc : z1 ∈ Icc (R.interval.left - (2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature)) * Real.sqrt (delta / t))
                                (R.interval.right + (2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature)) * Real.sqrt (delta / t)))
    (hz2_loc : z2 ∈ Icc (R.interval.left - (2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature)) * Real.sqrt (delta / t))
                                (R.interval.right + (2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature)) * Real.sqrt (delta / t))) :
    (z1 ∈ Icc (R.interval.left - E * L) (R.interval.right + E * L)) ∧
    (z2 ∈ Icc (R.interval.left - E * L) (R.interval.right + E * L)) := by
  let C := 2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature)
  have hC : C * Real.sqrt (delta / t) = E * L := by
    dsimp only [C]; rw [hE_def, hL_def] <;> ring
  have h_left : R.interval.left - C * Real.sqrt (delta / t) = R.interval.left - E * L := by rw [hC]
  have h_right : R.interval.right + C * Real.sqrt (delta / t) = R.interval.right + E * L := by rw [hC]
  constructor
  · convert hz1_loc using 1 <;> rw [hC]
  · convert hz2_loc using 1 <;> rw [hC]

/-- Prove vertical translates are distinct using nonzero second derivative gap. -/
private lemma directional_lens_translates_distinct
    {w b : C2Function} {h2 : ℝ → ℝ} {x0 : ℝ}
    (hx0_in : x0 ∈ Icc (0 : ℝ) 1)
    (h2_eq : ∀ y, h2 y = deriv (deriv w.extension) y - deriv (deriv b.extension) y)
    (h2_nonzero : h2 x0 ≠ 0)
    (c1 c2 : ℝ) :
    w.verticalTranslate c1 ≠ b.verticalTranslate c2 := by
  intro h
  have hsd : (w.verticalTranslate c1).secondDeriv = (b.verticalTranslate c2).secondDeriv := by
    rw [h]
  have hwsd : w.secondDeriv = b.secondDeriv := by
    simpa [C2Function.verticalTranslate] using hsd
  let x0' : UnitPoint := ⟨x0, hx0_in⟩
  have h3 : w.secondDeriv x0' = b.secondDeriv x0' := by rw [hwsd]
  have h4 : h2 x0 = 0 := by
    have h5 : h2 x0 = deriv (deriv w.extension) x0 - deriv (deriv b.extension) x0 := h2_eq x0
    rw [h5]
    have h6 : deriv (deriv w.extension) x0 = w.secondDeriv x0' :=
      w.secondDeriv_extension_eq_secondDeriv x0'
    have h7 : deriv (deriv b.extension) x0 = b.secondDeriv x0' :=
      b.secondDeriv_extension_eq_secondDeriv x0'
    rw [h6, h7, h3] <;> ring
  exact h2_nonzero h4

/-- Prove h_down evaluation equals vertical translates difference outside saturated context. -/
private lemma directional_lens_eval_down
    {w b_fn : C2Function} {h0 h_down : ℝ → ℝ}
    {epsilon s shift0_w shift0_b : ℝ}
    (h0_eq : ∀ y, h0 y = w.extension y - b_fn.extension y)
    (hs_def : s = shift0_w - shift0_b)
    (h_down_def : ∀ x, h_down x = h0 x - epsilon + s)
    (x : UnitPoint) :
    h_down (x : ℝ) = (w.verticalTranslate (-epsilon + shift0_w)) x - (b_fn.verticalTranslate shift0_b) x := by
  have h3 : w.extension (x : ℝ) = w x := C2Function.extension_eq_value w x
  have h4 : b_fn.extension (x : ℝ) = b_fn x := C2Function.extension_eq_value b_fn x
  have h5 : h_down (x : ℝ) = h0 (x : ℝ) - epsilon + s := h_down_def (x : ℝ)
  rw [h5, h0_eq (x : ℝ), h3, h4, hs_def]
  have h6 : (w.verticalTranslate (-epsilon + shift0_w)) x = w x + (-epsilon + shift0_w) :=
    verticalTranslate_apply w (-epsilon + shift0_w) x
  have h7 : (b_fn.verticalTranslate shift0_b) x = b_fn x + shift0_b :=
    verticalTranslate_apply b_fn shift0_b x
  rw [h6, h7] <;> ring

/-- Prove h_up evaluation equals vertical translates difference outside saturated context. -/
private lemma directional_lens_eval_up
    {w b_fn : C2Function} {h0 h_up : ℝ → ℝ}
    {epsilon s shift0_w shift0_b : ℝ}
    (h0_eq : ∀ y, h0 y = w.extension y - b_fn.extension y)
    (hs_def : s = shift0_w - shift0_b)
    (h_up_def : ∀ x, h_up x = h0 x + epsilon + s)
    (x : UnitPoint) :
    h_up (x : ℝ) = (w.verticalTranslate (epsilon + shift0_w)) x - (b_fn.verticalTranslate shift0_b) x := by
  have h3 : w.extension (x : ℝ) = w x := C2Function.extension_eq_value w x
  have h4 : b_fn.extension (x : ℝ) = b_fn x := C2Function.extension_eq_value b_fn x
  have h5 : h_up (x : ℝ) = h0 (x : ℝ) + epsilon + s := h_up_def (x : ℝ)
  rw [h5, h0_eq (x : ℝ), h3, h4, hs_def]
  have h6 : (w.verticalTranslate (epsilon + shift0_w)) x = w x + (epsilon + shift0_w) :=
    verticalTranslate_apply w (epsilon + shift0_w) x
  have h7 : (b_fn.verticalTranslate shift0_b) x = b_fn x + shift0_b :=
    verticalTranslate_apply b_fn shift0_b x
  rw [h6, h7] <;> ring

/-- Prove 0 < V outside saturated context. -/
private lemma directional_lens_V_pos (tangency V : ℝ) (htang : 5 ≤ tangency)
    (hV_def : V = 25 * tangency ^ 10 + 2 * tangency + 2) : 0 < V := by
  rw [hV_def]
  positivity

/-- Prove 0 < C0 outside saturated context. -/
private lemma directional_lens_C0_pos (K V C0 : ℝ) (hK : 1 ≤ K)
    (hV_pos : 0 < V) (hC0_def : C0 = 20 * K * V + 20 * K) : 0 < C0 := by
  rw [hC0_def]
  have hK_pos : 0 < K := by linarith
  positivity

/-- Prove 0 < B outside saturated context. -/
private lemma directional_lens_B_pos (C0 L B : ℝ) (hC0_pos : 0 < C0)
    (hL_pos : 0 < L) (hB_def : B = C0 * L) : 0 < B := by
  rw [hB_def]
  exact mul_pos hC0_pos hL_pos

/-- Prove B ≤ 1/(32K) outside saturated context. -/
private lemma directional_lens_B_le
    (K tangency C0 L B : ℝ) (hK : 1 ≤ K) (htang : 5 ≤ tangency)
    (hC0_le : C0 ≤ 1000 * K * tangency ^ 10)
    (hL_bound : L ≤ 1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25))
    (hL_nonneg : 0 ≤ L)
    (hB_def : B = C0 * L) : B ≤ 1 / (32 * K) := by
  rw [hB_def]
  have h1 : C0 * L ≤ (1000 * K * tangency ^ 10) * L :=
    mul_le_mul_of_nonneg_right hC0_le hL_nonneg
  have h_coeff_nonneg : 0 ≤ 1000 * K * tangency ^ 10 := by positivity
  have h2 : (1000 * K * tangency ^ 10) * L ≤ (1000 * K * tangency ^ 10) * (1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25)) :=
    mul_le_mul_of_nonneg_left hL_bound h_coeff_nonneg
  have h3 : C0 * L ≤ (1000 * K * tangency ^ 10) * (1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25)) :=
    le_trans h1 h2
  exact h3.trans (directional_lens_B_bound K tangency hK htang)

/-- Convert c ≤ |x| and x < 0 to x ≤ -c outside saturated context. -/
private lemma directional_lens_neg_from_abs {c x : ℝ} (h_abs : c ≤ |x|) (h_neg : x < 0) : x ≤ -c := by
  have h1 : |x| = -x := abs_of_neg h_neg
  rw [h1] at h_abs
  exact le_neg.mp h_abs

/-- Prove h2 x ≤ -c_new from abs lower bound and negativity outside saturated context. -/
private lemma directional_lens_h2_le_neg_c_new
    (h2 : ℝ → ℝ) (a b c_new : ℝ)
    (h2_abs_lower_enl : ∀ x ∈ Icc a b, c_new ≤ |h2 x|)
    (h2_neg_enl : ∀ x ∈ Icc a b, h2 x < 0) :
    ∀ x ∈ Icc a b, h2 x ≤ -c_new := by
  intro x hx
  exact directional_lens_neg_from_abs (h2_abs_lower_enl x hx) (h2_neg_enl x hx)

/-- Prove p ≤ q from rectangle interval outside saturated context. -/
private lemma directional_lens_p_le_q
    {delta t : ℝ} {p q : ℝ} {R : CurvilinearRectangle delta t}
    (hp_def : p = R.interval.left) (hq_def : q = R.interval.right) : p ≤ q := by
  have h : R.interval.left ≤ R.interval.right := R.interval.left_le_right
  rw [hp_def, hq_def]
  exact h

/-- Prove x0 ∈ Icc a b from x0 ∈ Icc p q and a < p, q < b. -/
private lemma directional_lens_x0_in_Icc_ab
    {a b x0 p q : ℝ} (ha_lt_p : a < p) (hq_lt_b : q < b)
    (hx0_core : x0 ∈ Icc p q) : x0 ∈ Icc a b :=
  ⟨by linarith [ha_lt_p, hx0_core.1], by linarith [hq_lt_b, hx0_core.2]⟩

/-- Prove x0 ∈ [0,1] from interval bounds outside saturated context. -/
private lemma directional_lens_x0_in_01
    {a b x0 p q : ℝ} (ha_ge0 : 0 ≤ a) (hb_le1 : b ≤ 1)
    (ha_lt_p : a < p) (hq_lt_b : q < b)
    (hp_le_q : p ≤ q) (hx0_core : x0 ∈ Icc p q) : x0 ∈ Icc (0 : ℝ) 1 := by
  have h1 : p ≤ x0 := hx0_core.1
  have h2 : x0 ≤ q := hx0_core.2
  have h3 : 0 ≤ x0 := by linarith [ha_ge0, ha_lt_p, h1]
  have h4 : x0 ≤ 1 := by linarith [hb_le1, hq_lt_b, h2]
  exact ⟨h3, h4⟩

/-- Deduce h2 x0 ≠ 0 from c_new ≤ h2 x0 and 0 < c_new. -/
private lemma directional_lens_h2_nonzero_from_pos {c v : ℝ} (h_ge : c ≤ v) (hc_pos : 0 < c) : v ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le hc_pos h_ge)

/-- Deduce h2 x0 ≠ 0 from h2 x0 ≤ -c_new and 0 < c_new. -/
private lemma directional_lens_h2_nonzero_from_neg {c v : ℝ} (h_le : v ≤ -c) (hc_pos : 0 < c) : v ≠ 0 :=
  ne_of_lt (lt_of_le_of_lt h_le (by linarith))

/-- Prove 0 ≤ S_core + d * B from component positivity outside saturated context. -/
private lemma directional_lens_S_enl_nonneg
    (S_core d B : ℝ) (hS_core_nonneg : 0 ≤ S_core) (hd_pos : 0 < d) (hB_pos : 0 < B) :
    0 ≤ S_core + d * B :=
  add_nonneg hS_core_nonneg (mul_nonneg hd_pos.le hB_pos.le)

/-- Construct final lens properties for downward shift (Or.inr) outside saturated context. -/
private lemma directional_lens_final_lens_down
    {delta t E L_real : ℝ} {I : ParameterInterval} {R : CurvilinearRectangle delta t}
    {w b b_fn : C2Function} {epsilon shift0_w shift0_b : ℝ}
    {z1 z2 : ℝ} {z1p z2p : UnitPoint}
    {L : GraphLens}
    (hbf : b_fn = b)
    (hLleft : (L.left : ℝ) = z1)
    (hLright : (L.right : ℝ) = z2)
    (hz1p_val : (z1p : ℝ) = z1)
    (hz2p_val : (z2p : ℝ) = z2)
    (hz1p_in : z1p ∈ I.carrier)
    (hz2p_in : z2p ∈ I.carrier)
    (hz1_Icc : z1 ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real))
    (hz2_Icc : z2 ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real))
    (hLf : L.f = w.verticalTranslate (-epsilon + shift0_w))
    (hLg : L.g = b_fn.verticalTranslate shift0_b) :
    L.left ∈ I.carrier ∧
    L.right ∈ I.carrier ∧
    (L.left : ℝ) ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real) ∧
    (L.right : ℝ) ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real) ∧
    L.f = w.verticalTranslate (-epsilon + shift0_w) ∧
    L.g = b.verticalTranslate shift0_b := by
  have h1 : L.left = z1p := by
    apply Subtype.ext
    exact hLleft.trans hz1p_val.symm
  have h2 : L.right = z2p := by
    apply Subtype.ext
    exact hLright.trans hz2p_val.symm
  have h3 : (L.left : ℝ) ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real) := by
    rw [hLleft]; exact hz1_Icc
  have h4 : (L.right : ℝ) ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real) := by
    rw [hLright]; exact hz2_Icc
  have h5 : L.g = b.verticalTranslate shift0_b := by
    rw [hbf] at hLg; exact hLg
  have h6 : L.left ∈ I.carrier := by rw [h1]; exact hz1p_in
  have h7 : L.right ∈ I.carrier := by rw [h2]; exact hz2p_in
  exact ⟨h6, h7, h3, h4, hLf, h5⟩

/-- Construct final lens properties for upward shift (Or.inl) outside saturated context. -/
private lemma directional_lens_final_lens_up
    {delta t E L_real : ℝ} {I : ParameterInterval} {R : CurvilinearRectangle delta t}
    {w b b_fn : C2Function} {epsilon shift0_w shift0_b : ℝ}
    {z1 z2 : ℝ} {z1p z2p : UnitPoint}
    {L : GraphLens}
    (hbf : b_fn = b)
    (hLleft : (L.left : ℝ) = z1)
    (hLright : (L.right : ℝ) = z2)
    (hz1p_val : (z1p : ℝ) = z1)
    (hz2p_val : (z2p : ℝ) = z2)
    (hz1p_in : z1p ∈ I.carrier)
    (hz2p_in : z2p ∈ I.carrier)
    (hz1_Icc : z1 ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real))
    (hz2_Icc : z2 ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real))
    (hLf : L.f = w.verticalTranslate (epsilon + shift0_w))
    (hLg : L.g = b_fn.verticalTranslate shift0_b) :
    L.left ∈ I.carrier ∧
    L.right ∈ I.carrier ∧
    (L.left : ℝ) ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real) ∧
    (L.right : ℝ) ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real) ∧
    L.f = w.verticalTranslate (epsilon + shift0_w) ∧
    L.g = b.verticalTranslate shift0_b := by
  have h1 : L.left = z1p := by
    apply Subtype.ext
    exact hLleft.trans hz1p_val.symm
  have h2 : L.right = z2p := by
    apply Subtype.ext
    exact hLright.trans hz2p_val.symm
  have h3 : (L.left : ℝ) ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real) := by
    rw [hLleft]; exact hz1_Icc
  have h4 : (L.right : ℝ) ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real) := by
    rw [hLright]; exact hz2_Icc
  have h5 : L.g = b.verticalTranslate shift0_b := by
    rw [hbf] at hLg; exact hLg
  have h6 : L.left ∈ I.carrier := by rw [h1]; exact hz1p_in
  have h7 : L.right ∈ I.carrier := by rw [h2]; exact hz2p_in
  exact ⟨h6, h7, h3, h4, hLf, h5⟩

/-- Assemble downward-shift lens conclusion from graphLens existential outside saturated context. -/
private lemma directional_lens_assemble_down
    {delta t E L_real : ℝ} {I : ParameterInterval} {R : CurvilinearRectangle delta t}
    {w b b_fn : C2Function} {epsilon shift0_w shift0_b : ℝ}
    {z1 z2 : ℝ} {z1p z2p : UnitPoint}
    (hbf : b_fn = b)
    (hz1p_val : (z1p : ℝ) = z1)
    (hz2p_val : (z2p : ℝ) = z2)
    (hz1p_in : z1p ∈ I.carrier)
    (hz2p_in : z2p ∈ I.carrier)
    (hz1_Icc : z1 ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real))
    (hz2_Icc : z2 ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real))
    (hLens : ∃ (L : GraphLens), L.f = w.verticalTranslate (-epsilon + shift0_w) ∧
                L.g = b_fn.verticalTranslate shift0_b ∧
                (L.left : ℝ) = z1 ∧ (L.right : ℝ) = z2) :
    ∃ (L : GraphLens), L.left ∈ I.carrier ∧ L.right ∈ I.carrier ∧
      (L.left : ℝ) ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real) ∧
      (L.right : ℝ) ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real) ∧
      L.f = w.verticalTranslate (-epsilon + shift0_w) ∧
      L.g = b.verticalTranslate shift0_b := by
  rcases hLens with ⟨L, hLf, hLg, hLleft, hLright⟩
  exact ⟨L, directional_lens_final_lens_down hbf hLleft hLright hz1p_val hz2p_val hz1p_in hz2p_in hz1_Icc hz2_Icc hLf hLg⟩

/-- Assemble upward-shift lens conclusion from graphLens existential outside saturated context. -/
private lemma directional_lens_assemble_up
    {delta t E L_real : ℝ} {I : ParameterInterval} {R : CurvilinearRectangle delta t}
    {w b b_fn : C2Function} {epsilon shift0_w shift0_b : ℝ}
    {z1 z2 : ℝ} {z1p z2p : UnitPoint}
    (hbf : b_fn = b)
    (hz1p_val : (z1p : ℝ) = z1)
    (hz2p_val : (z2p : ℝ) = z2)
    (hz1p_in : z1p ∈ I.carrier)
    (hz2p_in : z2p ∈ I.carrier)
    (hz1_Icc : z1 ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real))
    (hz2_Icc : z2 ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real))
    (hLens : ∃ (L : GraphLens), L.f = w.verticalTranslate (epsilon + shift0_w) ∧
                L.g = b_fn.verticalTranslate shift0_b ∧
                (L.left : ℝ) = z1 ∧ (L.right : ℝ) = z2) :
    ∃ (L : GraphLens), L.left ∈ I.carrier ∧ L.right ∈ I.carrier ∧
      (L.left : ℝ) ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real) ∧
      (L.right : ℝ) ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real) ∧
      L.f = w.verticalTranslate (epsilon + shift0_w) ∧
      L.g = b.verticalTranslate shift0_b := by
  rcases hLens with ⟨L, hLf, hLg, hLleft, hLright⟩
  exact ⟨L, directional_lens_final_lens_up hbf hLleft hLright hz1p_val hz2p_val hz1p_in hz2p_in hz1_Icc hz2_Icc hLf hLg⟩

/-- Construct concave-branch graph lens outside saturated context. -/
private lemma directional_lens_concave_graph_lens
    {delta t : ℝ} {R : CurvilinearRectangle delta t}
    {w b_fn : C2Function} {h0 h_up h2 : ℝ → ℝ}
    {epsilon s shift0_w shift0_b x0 p q a b c_new : ℝ}
    {z1 z2 : ℝ}
    (h0_eq : ∀ y, h0 y = w.extension y - b_fn.extension y)
    (hs_def : s = shift0_w - shift0_b)
    (h_up_def : ∀ (x : ℝ), h_up x = h0 x + epsilon + s)
    (h2_eq : ∀ y, h2 y = deriv (deriv w.extension) y - deriv (deriv b_fn.extension) y)
    (hp_def : p = R.interval.left) (hq_def : q = R.interval.right)
    (ha_ge0 : 0 ≤ a) (hb_le1 : b ≤ 1)
    (ha_lt_p : a < p) (hq_lt_b : q < b)
    (hx0_core : x0 ∈ Icc p q)
    (h2_le_neg_c_new : ∀ x ∈ Icc a b, h2 x ≤ -c_new)
    (hc_new_pos : 0 < c_new)
    (hz1_01 : z1 ∈ Icc (0 : ℝ) 1) (hz2_01 : z2 ∈ Icc (0 : ℝ) 1)
    (hz12 : z1 < z2) (hzero1 : h_up z1 = 0) (hzero2 : h_up z2 = 0)
    (hbetween : ∀ x, z1 < x → x < z2 → 0 < h_up x) :
    ∃ (L : GraphLens), L.f = w.verticalTranslate (epsilon + shift0_w) ∧
                L.g = b_fn.verticalTranslate shift0_b ∧
                (L.left : ℝ) = z1 ∧ (L.right : ℝ) = z2 := by
  have heval_up : ∀ (x : UnitPoint), h_up (x : ℝ) =
      (w.verticalTranslate (epsilon + shift0_w)) x - (b_fn.verticalTranslate shift0_b) x :=
    fun x => directional_lens_eval_up h0_eq hs_def h_up_def x
  have hp_le_q : p ≤ q := directional_lens_p_le_q hp_def hq_def
  have hx0_01 : x0 ∈ Icc (0 : ℝ) 1 :=
    directional_lens_x0_in_01 ha_ge0 hb_le1 ha_lt_p hq_lt_b hp_le_q hx0_core
  have hx0_enl : x0 ∈ Icc a b := directional_lens_x0_in_Icc_ab ha_lt_p hq_lt_b hx0_core
  have h2_x0_nonzero : h2 x0 ≠ 0 :=
    directional_lens_h2_nonzero_from_neg (h2_le_neg_c_new x0 hx0_enl) hc_new_pos
  have hne_up : (w.verticalTranslate (epsilon + shift0_w)) ≠ (b_fn.verticalTranslate shift0_b) :=
    directional_lens_translates_distinct hx0_01 h2_eq h2_x0_nonzero (epsilon + shift0_w) shift0_b
  exact graphLens_of_positive_between
    hne_up heval_up hz1_01 hz2_01 hz12 hzero1 hzero2
    (fun x hx1 hx2 => hbetween x hx1 hx2)

/-- Structure to hold both extracted endpoints outside saturated context. -/
private structure BothEndpoints (I : ParameterInterval) (z1 z2 : ℝ) where
  z1p : UnitPoint
  z2p : UnitPoint
  hz1p_val : (z1p : ℝ) = z1
  hz2p_val : (z2p : ℝ) = z2
  hz1p_in : z1p ∈ I.carrier
  hz2p_in : z2p ∈ I.carrier

/-- Extract both endpoints from containment proofs outside saturated context. -/
private def directional_lens_mk_both_endpoints
    {I : ParameterInterval} {z1 z2 : ℝ}
    (h1 : ∃ (p : UnitPoint), (p : ℝ) = z1 ∧ p ∈ I.carrier)
    (h2 : ∃ (p : UnitPoint), (p : ℝ) = z2 ∧ p ∈ I.carrier) :
    BothEndpoints I z1 z2 :=
  let z1p : UnitPoint := Classical.choose h1
  let hz1p_spec : (z1p : ℝ) = z1 ∧ z1p ∈ I.carrier := Classical.choose_spec h1
  let z2p : UnitPoint := Classical.choose h2
  let hz2p_spec : (z2p : ℝ) = z2 ∧ z2p ∈ I.carrier := Classical.choose_spec h2
  ⟨z1p, z2p, hz1p_spec.1, hz2p_spec.1, hz1p_spec.2, hz2p_spec.2⟩

/-- Combined concave-branch final assembly outside saturated context. -/
private lemma directional_lens_concave_final
    (delta t E L_real : ℝ) (I : ParameterInterval) (R : CurvilinearRectangle delta t)
    (w b b_fn : C2Function) (h0 h_up h2 : ℝ → ℝ)
    (epsilon s shift0_w shift0_b x0 p q a b_pt c_new : ℝ)
    (z1 z2 : ℝ) (z1p z2p : UnitPoint)
    (hbf : b_fn = b)
    (h0_eq : ∀ y, h0 y = w.extension y - b_fn.extension y)
    (hs_def : s = shift0_w - shift0_b)
    (h_up_def : ∀ (x : ℝ), h_up x = h0 x + epsilon + s)
    (h2_eq : ∀ y, h2 y = deriv (deriv w.extension) y - deriv (deriv b_fn.extension) y)
    (hp_def : p = R.interval.left) (hq_def : q = R.interval.right)
    (ha_ge0 : 0 ≤ a) (hb_le1 : b_pt ≤ 1)
    (ha_lt_p : a < p) (hq_lt_b : q < b_pt)
    (hx0_core : x0 ∈ Icc p q)
    (h2_le_neg_c_new : ∀ x ∈ Icc a b_pt, h2 x ≤ -c_new)
    (hc_new_pos : 0 < c_new)
    (hz1_01 : z1 ∈ Icc (0 : ℝ) 1) (hz2_01 : z2 ∈ Icc (0 : ℝ) 1)
    (hz12 : z1 < z2) (hzero1 : h_up z1 = 0) (hzero2 : h_up z2 = 0)
    (hbetween : ∀ x, z1 < x → x < z2 → 0 < h_up x)
    (hz1p_val : (z1p : ℝ) = z1) (hz2p_val : (z2p : ℝ) = z2)
    (hz1p_in : z1p ∈ I.carrier) (hz2p_in : z2p ∈ I.carrier)
    (hz1_Icc : z1 ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real))
    (hz2_Icc : z2 ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real)) :
    ∃ (L : GraphLens), L.left ∈ I.carrier ∧ L.right ∈ I.carrier ∧
      (L.left : ℝ) ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real) ∧
      (L.right : ℝ) ∈ Icc (R.interval.left - E * L_real) (R.interval.right + E * L_real) ∧
      L.f = w.verticalTranslate (epsilon + shift0_w) ∧
      L.g = b.verticalTranslate shift0_b := by
  have hLens := directional_lens_concave_graph_lens
    (h0_eq := h0_eq) (hs_def := hs_def) (h_up_def := h_up_def) (h2_eq := h2_eq)
    (hp_def := hp_def) (hq_def := hq_def)
    (ha_ge0 := ha_ge0) (hb_le1 := hb_le1)
    (ha_lt_p := ha_lt_p) (hq_lt_b := hq_lt_b) (hx0_core := hx0_core)
    (h2_le_neg_c_new := h2_le_neg_c_new) (hc_new_pos := hc_new_pos)
    (hz1_01 := hz1_01) (hz2_01 := hz2_01)
    (hz12 := hz12) (hzero1 := hzero1) (hzero2 := hzero2)
    (hbetween := hbetween)
  exact directional_lens_assemble_up hbf hz1p_val hz2p_val hz1p_in hz2p_in hz1_Icc hz2_Icc hLens

theorem directional_lens_existence : DirectionalLensExistenceStatement := by
  intro K tangency delta t hK htang hdelta ht hdt hsmall family hcurv w b hne hw hb hd_ge_2t
    R hRw hRb I hI hRsub epsilon hepsilon_gt hepsilon_le shift0_w shift0_b hshift_w hshift_b
  dsimp only

  set d : ℝ := c2Distance w b with hd_def
  set V : ℝ := 25 * tangency ^ 10 + 2 * tangency + 2 with hV_def
  set curvature : ℝ := d / (6 * K * t) with hcurvature_def
  have hK_pos : 0 < K := by linarith
  have hd_pos : 0 < d := by linarith
  have hcurv_pos : 0 < curvature := by
    rw [hcurvature_def]
    exact div_pos hd_pos (mul_pos (mul_pos (by norm_num) hK_pos) ht)
  set E : ℝ := 2 * (2 * V + d / t) / curvature + Real.sqrt (2 * V / curvature) with hE_def
  set L : ℝ := Real.sqrt (delta / t) with hL_def
  set p : ℝ := R.interval.left with hp_def
  set q : ℝ := R.interval.right with hq_def
  set x0 : ℝ := (p + q) / 2 with hx0_def

  let h0 : ℝ → ℝ := fun x => w.extension x - b.extension x
  let h1 : ℝ → ℝ := fun x => deriv w.extension x - deriv b.extension x
  let h2 : ℝ → ℝ := fun x => deriv (deriv w.extension) x - deriv (deriv b.extension) x

  have h0_eq : ∀ y, h0 y = w.extension y - b.extension y := by intro y; rfl
  have h1_eq : ∀ y, h1 y = deriv w.extension y - deriv b.extension y := by intro y; rfl
  have h2_eq : ∀ y, h2 y = deriv (deriv w.extension) y - deriv (deriv b.extension) y := by intro y; rfl

  have hfc2 : ContDiff ℝ 2 w.extension := w.extension_contDiff
  have hgc2 : ContDiff ℝ 2 b.extension := b.extension_contDiff
  have h0_c2 : ContDiff ℝ 2 h0 := hfc2.sub hgc2
  have hfc1 : ContDiff ℝ 1 (deriv w.extension) := hfc2.deriv'
  have hgc1 : ContDiff ℝ 1 (deriv b.extension) := hgc2.deriv'
  have h1_c1 : ContDiff ℝ 1 h1 := hfc1.sub hgc1
  have h0_diff : Differentiable ℝ h0 := h0_c2.differentiable (by norm_num)
  have h1_diff : Differentiable ℝ h1 := h1_c1.differentiable (by norm_num)
  have h_deriv1 : ∀ (x : ℝ), deriv h0 x = h1 x := by
    intro x; have h : deriv h0 x = deriv w.extension x - deriv b.extension x := by
      have h_eq : h0 = w.extension - b.extension := by funext y; rfl
      rw [h_eq]; exact deriv_sub (hfc2.differentiable (by norm_num)).differentiableAt
        (hgc2.differentiable (by norm_num)).differentiableAt
    simpa [h1] using h
  have h_deriv2 : ∀ (x : ℝ), deriv h1 x = h2 x := by
    intro x; have h : deriv h1 x = deriv (deriv w.extension) x - deriv (deriv b.extension) x := by
      have h_eq : h1 = deriv w.extension - deriv b.extension := by funext y; rfl
      rw [h_eq]; exact deriv_sub (hfc1.differentiable (by norm_num)).differentiableAt
        (hgc1.differentiable (by norm_num)).differentiableAt
    simpa [h2] using h

  have hK_pos : 0 < K := by linarith
  have htang_pos : 0 < tangency := by linarith
  have hd_pos : 0 < d := by
    have h : 0 < 2 * t := by positivity
    exact lt_of_lt_of_le h hd_ge_2t
  have hL_pos : 0 < L := Real.sqrt_pos.mpr (by positivity)
  have hpq : p < q := by
    rw [← sub_pos]; change 0 < R.interval.length; rw [R.interval_length]; positivity
  have hcore_length : q - p = L := R.interval_length
  have hx0_core : x0 ∈ Icc p q := by dsimp only [x0]; constructor <;> linarith
  have hL_sq : L ^ 2 = delta / t := by rw [hL_def]; exact Real.sq_sqrt (by positivity)

  -- Helper: pack real x in [p,q] as UnitPoint
  have hpack : ∀ (x : ℝ), x ∈ Icc p q → ∃ (xp : UnitPoint), (xp : ℝ) = x := by
    intro x hx
    have hx01 : x ∈ unitInterval := by
      have h1 : p ∈ unitInterval := R.interval.left_mem
      have h2 : q ∈ unitInterval := R.interval.right_mem
      exact ⟨by linarith [h1.1, hx.1], by linarith [h2.2, hx.2]⟩
    exact ⟨⟨x, hx01⟩, rfl⟩

  -- Step 1: Core value bound
  have hval_core : ∀ x ∈ Icc p q, |h0 x| ≤ 2 * tangency * delta := by
    intro x hx
    have hx01 : x ∈ unitInterval := by
      have h1 : p ∈ unitInterval := R.interval.left_mem
      have h2 : q ∈ unitInterval := R.interval.right_mem
      exact ⟨by linarith [h1.1, hx.1], by linarith [h2.2, hx.2]⟩
    let xp : UnitPoint := ⟨x, hx01⟩
    have hxp_I : xp ∈ R.interval.carrier := by
      simp only [ParameterInterval.carrier, Set.mem_setOf_eq]; exact ⟨hx.1, hx.2⟩
    have hcar : (xp, R.function xp) ∈ R.carrier := by
      simp only [CurvilinearRectangle.carrier, verticalNeighborhoodOn, Set.mem_setOf_eq]
      exact ⟨hxp_I, by simp [hdelta.le]⟩
    have hw_tan : |R.function xp - w xp| ≤ tangency * delta := hRw (xp, R.function xp) hcar
    have hb_tan : |R.function xp - b xp| ≤ tangency * delta := hRb (xp, R.function xp) hcar
    have h3 : |w xp - b xp| ≤ 2 * tangency * delta := by
      have h_eq : w xp - b xp = (w xp - R.function xp) + (R.function xp - b xp) := by ring
      rw [h_eq]
      have h31 : |(w xp - R.function xp) + (R.function xp - b xp)| ≤
          |w xp - R.function xp| + |R.function xp - b xp| := abs_add_le _ _
      have h32 : |w xp - R.function xp| = |R.function xp - w xp| := by rw [abs_sub_comm]
      rw [h32] at h31; linarith
    have h4 : h0 x = w xp - b xp := by
      have h41 : w.extension x = w xp := C2Function.extension_eq_value w xp
      have h42 : b.extension x = b xp := C2Function.extension_eq_value b xp
      have h : h0 x = w.extension x - b.extension x := by rfl
      rw [h, h41, h42]
    rw [h4]; exact h3

  -- Step 2: Core second derivative bound
  have h2_bound_all : ∀ (x : ℝ), x ∈ unitInterval → |h2 x| ≤ d := by
    intro x hx01
    let xp : UnitPoint := ⟨x, hx01⟩
    have h51 : deriv (deriv w.extension) x = w.secondDeriv xp :=
      w.secondDeriv_extension_eq_secondDeriv xp
    have h52 : deriv (deriv b.extension) x = b.secondDeriv xp :=
      b.secondDeriv_extension_eq_secondDeriv xp
    have h5 : h2 x = w.secondDeriv xp - b.secondDeriv xp := by
      have h : h2 x = deriv (deriv w.extension) x - deriv (deriv b.extension) x := by rfl
      rw [h, h51, h52]
    rw [h5]; exact abs_secondDeriv_sub_le_c2Distance w b xp

  have h2_bound_core : ∀ x ∈ Icc p q, |h2 x| ≤ d := by
    intro x hx
    have hx01 : x ∈ unitInterval := by
      have h1 : p ∈ unitInterval := R.interval.left_mem
      have h2 : q ∈ unitInterval := R.interval.right_mem
      exact ⟨by linarith [h1.1, hx.1], by linarith [h2.2, hx.2]⟩
    exact h2_bound_all x hx01

  -- Step 3: Core derivative bound
  have hderiv_core_raw : ∀ x ∈ Icc p q, |h1 x| ≤ 4 * tangency * Real.sqrt (delta * t) + d * L := by
    have h_bound := core_deriv_bound hpq h0_diff.continuous.continuousOn
      (fun x _ => by
        have hda : DifferentiableAt ℝ h0 x := Differentiable.differentiableAt (h := h0_diff)
        have h : HasDerivAt h0 (deriv h0 x) x := hda.hasDerivAt
        rw [h_deriv1 x] at h
        exact h)
      h1_diff.continuous.continuousOn
      (fun x _ => by
        have hda : DifferentiableAt ℝ h1 x := Differentiable.differentiableAt (h := h1_diff)
        have h : HasDerivAt h1 (deriv h1 x) x := hda.hasDerivAt
        rw [h_deriv2 x] at h
        exact h)
      hval_core h2_bound_core
    intro x hx
    have h9 := h_bound x hx
    have h11 : L ^ 2 = delta / t := hL_sq
    have h12 : delta / L = Real.sqrt (delta * t) := by
      have h13 : L > 0 := hL_pos
      have h14 : (delta / L) ^ 2 = delta * t := by
        calc (delta / L) ^ 2 = delta ^ 2 / L ^ 2 := by ring
          _ = delta ^ 2 / (delta / t) := by rw [h11]
          _ = delta * t := by field_simp [hdelta.ne', ht.ne'] <;> ring
      have h15 : 0 ≤ delta / L := by positivity
      have h16 : 0 ≤ Real.sqrt (delta * t) := by positivity
      have h17 : (delta / L) ^ 2 = (Real.sqrt (delta * t)) ^ 2 := by
        rw [h14, Real.sq_sqrt (by positivity : 0 ≤ delta * t)]
      nlinarith
    have h10 : 2 * (2 * tangency * delta) / (q - p) + d * (q - p) =
        4 * tangency * Real.sqrt (delta * t) + d * L := by
      rw [hcore_length]
      have h : 2 * (2 * tangency * delta) / L = 4 * tangency * (delta / L) := by
        field_simp [hL_pos.ne'] <;> ring
      rw [h, h12] <;> ring
    rw [h10] at h9; exact h9

  -- Strengthen derivative bound to (2T+1)*d*L
  have hderiv_core : ∀ x ∈ Icc p q, |h1 x| ≤ (2 * tangency + 1) * d * L := by
    intro x hx
    have h_raw := hderiv_core_raw x hx
    have h_sqrt_eq : Real.sqrt (delta * t) = delta / L := by
      have h15 : 0 ≤ delta / L := by positivity
      have h16 : (delta / L) ^ 2 = delta * t := by
        calc (delta / L) ^ 2 = delta ^ 2 / L ^ 2 := by ring
          _ = delta ^ 2 / (delta / t) := by rw [hL_sq]
          _ = delta * t := by field_simp [hdelta.ne', ht.ne'] <;> ring
      have h17 : Real.sqrt ((delta / L) ^ 2) = delta / L := Real.sqrt_sq h15
      have h19 : Real.sqrt (delta * t) = Real.sqrt ((delta / L) ^ 2) := by rw [h16]
      exact h19.trans h17
    have h22 : 2 * (delta / L) ≤ d * L := by
      have h1 : 2 * delta ≤ d * L ^ 2 := by
        have h2 : L ^ 2 = delta / t := hL_sq
        rw [h2]
        have h3 : 0 ≤ delta / t := by positivity
        have h4 : (2 * t) * (delta / t) ≤ d * (delta / t) := mul_le_mul_of_nonneg_right hd_ge_2t h3
        have h5 : 2 * delta = (2 * t) * (delta / t) := by field_simp [ht.ne'] <;> ring
        rw [h5]; exact h4
      have h6 : 0 < L := hL_pos
      calc 2 * (delta / L)
        = (2 * delta) / L := by ring
      _ ≤ (d * L ^ 2) / L := by exact div_le_div_of_nonneg_right h1 h6.le
      _ = d * L := by field_simp [h6.ne'] <;> ring
    have h21 : 4 * tangency * (delta / L) ≤ 2 * tangency * d * L := by
      have h_pos : 0 ≤ 2 * tangency := by positivity
      calc 4 * tangency * (delta / L)
        = 2 * tangency * (2 * (delta / L)) := by ring
      _ ≤ 2 * tangency * (d * L) := by gcongr
      _ = 2 * tangency * d * L := by ring
    have h13 : 4 * tangency * Real.sqrt (delta * t) ≤ 2 * tangency * d * L := by
      rw [h_sqrt_eq]; exact h21
    linarith

  -- Distance bound
  have hd_le_K : d ≤ K := hcurv.1 hw hb

  -- Curvature gap on core
  have hcurv_gap : ∀ x ∈ Icc p q, d / K ≤ |h0 x| + |h1 x| + |h2 x| := by
    intro x hx
    have hx01 : x ∈ unitInterval := by
      have h1 : p ∈ unitInterval := R.interval.left_mem
      have h2 : q ∈ unitInterval := R.interval.right_mem
      exact ⟨by linarith [h1.1, hx.1], by linarith [h2.2, hx.2]⟩
    let xp : UnitPoint := ⟨x, hx01⟩
    have h9 : d / K ≤ jetGap w b xp := by
      have h10 : K⁻¹ * c2Distance w b ≤ jetGap w b xp := hcurv.2 hw hb xp
      have h11 : K⁻¹ * c2Distance w b = d / K := by
        field_simp [hK_pos.ne'] <;> rfl
      rw [h11] at h10; exact h10
    have h41 : w.extension x = w xp := C2Function.extension_eq_value w xp
    have h42 : b.extension x = b xp := C2Function.extension_eq_value b xp
    have hd1 : deriv w.extension x = w.firstDeriv xp := w.deriv_extension_eq_firstDeriv xp
    have hd2 : deriv b.extension x = b.firstDeriv xp := b.deriv_extension_eq_firstDeriv xp
    have hd3 : deriv (deriv w.extension) x = w.secondDeriv xp :=
      w.secondDeriv_extension_eq_secondDeriv xp
    have hd4 : deriv (deriv b.extension) x = b.secondDeriv xp :=
      b.secondDeriv_extension_eq_secondDeriv xp
    have h_val : w xp - b xp = h0 x := by
      have h : h0 x = w.extension x - b.extension x := by rfl
      rw [h, h41, h42]
    have h_deriv : w.firstDeriv xp - b.firstDeriv xp = h1 x := by
      have h : h1 x = deriv w.extension x - deriv b.extension x := by rfl
      rw [h, hd1, hd2]
    have h_deriv2 : w.secondDeriv xp - b.secondDeriv xp = h2 x := by
      have h : h2 x = deriv (deriv w.extension) x - deriv (deriv b.extension) x := by rfl
      rw [h, hd3, hd4]
    have h11 : jetGap w b xp = |h0 x| + |h1 x| + |h2 x| := by
      simp [jetGap, h_val, h_deriv, h_deriv2] <;> rfl
    rw [h11] at h9; exact h9

  -- Step 4: Arithmetic
  set M_core : ℝ := 2 * tangency * delta with hM_core_def
  set S_core_raw : ℝ := 4 * tangency * Real.sqrt (delta * t) + d * L with hS_core_raw_def
  set S_core : ℝ := (2 * tangency + 1) * d * L with hS_core_def

  have hK2_le_K4 : K ^ 2 ≤ K ^ 4 := by
    have h2 : K ^ 2 - 1 ≥ 0 := by nlinarith
    have h3 : 0 ≤ K ^ 2 * (K ^ 2 - 1) := by positivity
    have h4 : K ^ 4 - K ^ 2 = K ^ 2 * (K ^ 2 - 1) := by ring
    linarith
  have hsmall2 : tangency ^ 50 * delta ≤ t / (1000 * K ^ 2) := by
    have h : t / (1000 * K ^ 4) ≤ t / (1000 * K ^ 2) := by gcongr <;> linarith
    exact hsmall.trans h

  have harith : M_core + S_core_raw < d / K := by
    have h := lens_existence_arithmetic hK htang hdelta ht hdt hd_ge_2t hd_le_K hsmall2
    simpa [hM_core_def, hS_core_raw_def, hL_def, add_assoc] using h

  -- Step 5: Curvature constant sign on core
  have h2_cont : Continuous h2 := by
    have h_deriv_cont : Continuous (deriv h1) := h1_c1.continuous_deriv (by norm_num)
    have h_eq : deriv h1 = h2 := by funext x; exact h_deriv2 x
    rw [h_eq] at h_deriv_cont
    exact h_deriv_cont

  have hcurv_sign := curvature_constant_sign hpq hK hd_pos
    h2_cont.continuousOn hcurv_gap hval_core hderiv_core_raw harith

  have h2_abs_lower_core_raw : ∀ x ∈ Icc p q, d / K - M_core - S_core_raw ≤ |h2 x| := hcurv_sign.1
  have h2_sign : (∀ x ∈ Icc p q, 0 < h2 x) ∨ (∀ x ∈ Icc p q, h2 x < 0) := hcurv_sign.2

  have hS_core_raw_le : S_core_raw ≤ S_core := by
    dsimp only [S_core_raw, S_core]
    have h_sqrt_eq : Real.sqrt (delta * t) = delta / L := by
      have h15 : 0 ≤ delta / L := by positivity
      have h16 : (delta / L) ^ 2 = delta * t := by
        calc (delta / L) ^ 2 = delta ^ 2 / L ^ 2 := by ring
          _ = delta ^ 2 / (delta / t) := by rw [hL_sq]
          _ = delta * t := by field_simp [hdelta.ne', ht.ne'] <;> ring
      have h17 : Real.sqrt ((delta / L) ^ 2) = delta / L := Real.sqrt_sq h15
      have h19 : Real.sqrt (delta * t) = Real.sqrt ((delta / L) ^ 2) := by rw [h16]
      exact h19.trans h17
    rw [h_sqrt_eq]
    have h22 : 2 * (delta / L) ≤ d * L := by
      have h1 : 2 * delta ≤ d * L ^ 2 := by
        have h2 : L ^ 2 = delta / t := hL_sq
        rw [h2]
        have h3 : 0 ≤ delta / t := by positivity
        have h4 : (2 * t) * (delta / t) ≤ d * (delta / t) := mul_le_mul_of_nonneg_right hd_ge_2t h3
        have h5 : 2 * delta = (2 * t) * (delta / t) := by field_simp [ht.ne'] <;> ring
        rw [h5]; exact h4
      have h6 : 0 < L := hL_pos
      calc 2 * (delta / L)
        = (2 * delta) / L := by ring
      _ ≤ (d * L ^ 2) / L := by exact div_le_div_of_nonneg_right h1 h6.le
      _ = d * L := by field_simp [h6.ne'] <;> ring
    have h21 : 4 * tangency * (delta / L) ≤ 2 * tangency * d * L := by
      have h_pos : 0 ≤ 2 * tangency := by positivity
      calc 4 * tangency * (delta / L)
        = 2 * tangency * (2 * (delta / L)) := by ring
      _ ≤ 2 * tangency * (d * L) := by gcongr
      _ = 2 * tangency * d * L := by ring
    linarith

  have h2_abs_lower_core : ∀ x ∈ Icc p q, d / K - M_core - S_core ≤ |h2 x| := by
    intro x hx
    have h1 : d / K - M_core - S_core_raw ≤ |h2 x| := h2_abs_lower_core_raw x hx
    have h2 : d / K - M_core - S_core ≤ d / K - M_core - S_core_raw := by
      linarith [hS_core_raw_le]
    linarith

  -- Step 6: Shift signs with perturbation
  set s : ℝ := shift0_w - shift0_b with hs_def
  have hs_bound : |s| ≤ 2 * delta := by
    rw [hs_def]
    have h1 : |shift0_w - shift0_b| ≤ 2 * delta := by
      rw [abs_le]
      constructor
      · have h2 : -delta ≤ shift0_w := (abs_le.mp hshift_w).1
        have h3 : shift0_b ≤ delta := (abs_le.mp hshift_b).2
        linarith
      · have h2 : shift0_w ≤ delta := (abs_le.mp hshift_w).2
        have h3 : -delta ≤ shift0_b := (abs_le.mp hshift_b).1
        linarith
    exact h1

  let h_down : ℝ → ℝ := fun x => h0 x - epsilon + s
  let h_up : ℝ → ℝ := fun x => h0 x + epsilon + s

  have h_down_def : ∀ (x : ℝ), h_down x = h0 x - epsilon + s := fun x => rfl
  have h_up_def : ∀ (x : ℝ), h_up x = h0 x + epsilon + s := fun x => rfl

  have h_down_neg : ∀ x ∈ Icc p q, h_down x < 0 := by
    intro x hx
    have h1 : |h0 x| ≤ 2 * tangency * delta := by
      simpa [hM_core_def] using hval_core x hx
    have h2 : h0 x ≤ 2 * tangency * delta := by
      have h21 : h0 x ≤ |h0 x| := le_abs_self (h0 x)
      linarith [h1]
    have h3 : s ≤ 2 * delta := by
      have h31 : s ≤ |s| := le_abs_self s
      linarith [hs_bound]
    have h4 : (2 * tangency + 2) * delta < epsilon := hepsilon_gt
    have h5 : h_down x = h0 x - epsilon + s := by rfl
    rw [h5]
    linarith

  have h_up_pos : ∀ x ∈ Icc p q, 0 < h_up x := by
    intro x hx
    have h1 : |h0 x| ≤ 2 * tangency * delta := by
      simpa [hM_core_def] using hval_core x hx
    have h2 : -(2 * tangency * delta) ≤ h0 x := by
      have h21 : -h0 x ≤ |h0 x| := by
        calc -h0 x ≤ |-h0 x| := le_abs_self (-h0 x)
          _ = |h0 x| := by rw [abs_neg]
      linarith [h1]
    have h3 : -2 * delta ≤ s := by
      have h31 : -s ≤ |s| := by
        calc -s ≤ |-s| := le_abs_self (-s)
          _ = |s| := by rw [abs_neg]
      linarith [hs_bound]
    have h4 : (2 * tangency + 2) * delta < epsilon := hepsilon_gt
    have h5 : h_up x = h0 x + epsilon + s := by rfl
    rw [h5]
    linarith

  -- Core value bound for shifted functions
  have h_down_bound_core : ∀ x ∈ Icc p q, |h_down x| ≤ V * delta := by
    intro x hx
    have h1 : |h0 x| ≤ M_core := hval_core x hx
    have h2 : |s| ≤ 2 * delta := hs_bound
    have h1_lo : -M_core ≤ h0 x := by
      have h' : -h0 x ≤ |-h0 x| := le_abs_self (-h0 x)
      have h'' : |-h0 x| = |h0 x| := by rw [abs_neg]
      rw [h''] at h'
      linarith [h1]
    have h1_hi : h0 x ≤ M_core := by
      have h : h0 x ≤ |h0 x| := le_abs_self (h0 x)
      linarith [h1]
    have h2_lo : -2 * delta ≤ s := by
      have h' : -s ≤ |-s| := le_abs_self (-s)
      have h'' : |-s| = |s| := by rw [abs_neg]
      rw [h''] at h'
      linarith [h2]
    have h2_hi : s ≤ 2 * delta := by
      have h : s ≤ |s| := le_abs_self s
      linarith [h2]
    have h3 : |h_down x| ≤ V * delta := by
      dsimp only [h_down]
      rw [abs_le]
      constructor
      · have h4 : -M_core ≤ h0 x := h1_lo
        have h5 : -2 * delta ≤ s := h2_lo
        have h6 : -(V * delta) ≤ h0 x - epsilon + s := by
          rw [hV_def, hM_core_def] at *
          <;> linarith [hepsilon_le]
        exact h6
      · have h4 : h0 x ≤ M_core := h1_hi
        have h5 : s ≤ 2 * delta := h2_hi
        have h6 : h0 x - epsilon + s ≤ V * delta := by
          rw [hV_def, hM_core_def] at *
          <;> linarith [hepsilon_le]
        exact h6
    exact h3

  have h_up_bound_core : ∀ x ∈ Icc p q, |h_up x| ≤ V * delta := by
    intro x hx
    have h1 : |h0 x| ≤ M_core := hval_core x hx
    have h2 : |s| ≤ 2 * delta := hs_bound
    have h1_lo : -M_core ≤ h0 x := by
      have h' : -h0 x ≤ |-h0 x| := le_abs_self (-h0 x)
      have h'' : |-h0 x| = |h0 x| := by rw [abs_neg]
      rw [h''] at h'
      linarith [h1]
    have h1_hi : h0 x ≤ M_core := by
      have h : h0 x ≤ |h0 x| := le_abs_self (h0 x)
      linarith [h1]
    have h2_lo : -2 * delta ≤ s := by
      have h' : -s ≤ |-s| := le_abs_self (-s)
      have h'' : |-s| = |s| := by rw [abs_neg]
      rw [h''] at h'
      linarith [h2]
    have h2_hi : s ≤ 2 * delta := by
      have h : s ≤ |s| := le_abs_self s
      linarith [h2]
    have h3 : |h_up x| ≤ V * delta := by
      dsimp only [h_up]
      rw [abs_le]
      constructor
      · have h4 : -M_core ≤ h0 x := h1_lo
        have h5 : -2 * delta ≤ s := h2_lo
        have h6 : -(V * delta) ≤ h0 x + epsilon + s := by
          rw [hV_def, hM_core_def] at *
          <;> linarith [hepsilon_gt]
        exact h6
      · have h4 : h0 x ≤ M_core := h1_hi
        have h5 : s ≤ 2 * delta := h2_hi
        have h6 : h0 x + epsilon + s ≤ V * delta := by
          rw [hV_def, hM_core_def] at *
          <;> linarith [hepsilon_le]
        exact h6
    exact h3

  -- Derivatives of shifted functions
  have h_down_deriv : ∀ x, deriv h_down x = h1 x := by
    intro x
    have h2 : HasDerivAt h0 (deriv h0 x) x := (h0_diff x).hasDerivAt
    have h2' : deriv h0 x = h1 x := h_deriv1 x
    rw [h2'] at h2
    have h3 : HasDerivAt h_down (h1 x) x := by
      simpa [h_down] using h2.add_const (-epsilon + s)
    exact h3.deriv
  have h_down_deriv2 : ∀ x, deriv (deriv h_down) x = h2 x := by
    have h_eq : deriv h_down = h1 := by funext x; exact h_down_deriv x
    intro x
    rw [h_eq]
    exact h_deriv2 x
  have h_up_deriv : ∀ x, deriv h_up x = h1 x := by
    intro x
    have h2 : HasDerivAt h0 (deriv h0 x) x := (h0_diff x).hasDerivAt
    have h2' : deriv h0 x = h1 x := h_deriv1 x
    rw [h2'] at h2
    have h3 : HasDerivAt h_up (h1 x) x := by
      simpa [h_up] using h2.add_const (epsilon + s)
    exact h3.deriv
  have h_up_deriv2 : ∀ x, deriv (deriv h_up) x = h2 x := by
    have h_eq : deriv h_up = h1 := by funext x; exact h_up_deriv x
    intro x
    rw [h_eq]
    exact h_deriv2 x

  have h_down_diff1 : Differentiable ℝ h_down := by
    have h : h_down = fun x => h0 x + (-epsilon + s) := by funext x; simp [h_down] <;> ring
    rw [h]
    exact h0_diff.add_const _
  have h_down_diff2 : Differentiable ℝ (deriv h_down) := by
    have h_eq : deriv h_down = h1 := by funext x; exact h_down_deriv x
    rw [h_eq]
    exact h1_diff
  have h_up_diff1 : Differentiable ℝ h_up := by
    have h : h_up = fun x => h0 x + (epsilon + s) := by funext x; simp [h_up] <;> ring
    rw [h]
    exact h0_diff.add_const _
  have h_up_diff2 : Differentiable ℝ (deriv h_up) := by
    have h_eq : deriv h_up = h1 := by funext x; exact h_up_deriv x
    rw [h_eq]
    exact h1_diff

  rcases h2_sign with (h2_pos | h2_neg)

  -- ==========================================================================
  -- CONVEX CASE: h2 > 0 on core → downward shift → Or.inr
  -- ==========================================================================
  · -- Enlargement setup
    set C0 : ℝ := 20 * K * V + 20 * K with hC0_def
    set B : ℝ := C0 * L with hB_def
    let b_fn : C2Function := b
    have hbf : b_fn = b := by rfl
    set a : ℝ := x0 - B with ha_def
    set b : ℝ := x0 + B with hb_def
    let S_enl : ℝ := S_core + d * B
    let M_enl : ℝ := M_core + S_enl * B
    have hS_enl_def : S_enl = S_core + d * B := by rfl
    have hM_enl_def : M_enl = M_core + S_enl * B := by rfl
    have hS_enl_nonneg : 0 ≤ S_enl := by
      rw [hS_enl_def]
      exact add_nonneg (by positivity) (by positivity)

    have hV_pos : 0 < V := by rw [hV_def] <;> positivity
    have hV_nonneg : 0 ≤ V := by positivity
    have hC0_nonneg : 0 ≤ C0 := by rw [hC0_def] <;> positivity
    have hB_nonneg : 0 ≤ B := by positivity
    have hB_pos : 0 < B := mul_pos (by positivity) hL_pos

    -- B ≤ 1/(32K) for [a,b] ⊂ [0,1]
    have hC0_le : C0 ≤ 1000 * K * tangency ^ 10 := by
      simpa [hC0_def, hV_def] using directional_lens_C0_bound K tangency hK htang

    have hL_bound : L ≤ 1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) :=
      sqrt_delta_t_bound hK htang hdelta ht hsmall

    have hB_le : B ≤ 1 / (32 * K) :=
      directional_lens_B_le K tangency C0 L B hK htang hC0_le hL_bound hL_pos.le hB_def

    -- R.interval is within I.length/8 of I.midpoint
    have hp_lower : p ≥ I.left + 3 * I.length / 8 :=
      directional_lens_hp_lower delta t K hK I hI R hRsub p hp_def
    have hq_upper : q ≤ I.right - 3 * I.length / 8 :=
      directional_lens_hq_upper delta t K hK I hI R hRsub q hq_def

    have hI_length : (12 * K)⁻¹ ≤ I.length := hI.1
    have h6 : 3 * ((12 * K)⁻¹) / 8 = 1 / (32 * K) := by
      field_simp [hK_pos.ne'] <;> ring
    have hp_ge : p ≥ 1 / (32 * K) :=
      directional_lens_p_ge K hK I hI p hp_lower
    have hq_le : q ≤ 1 - 1 / (32 * K) :=
      directional_lens_q_le K hK I hI q hq_upper

    rcases directional_lens_endpoint_bounds K hK x0 p q B hx0_core hp_ge hq_le hB_le hB_pos
      with ⟨ha_ge0_raw, hb_le1_raw, hab_raw⟩
    have ha_ge0 : 0 ≤ a := ha_def.symm ▸ ha_ge0_raw
    have hb_le1 : b ≤ 1 := hb_def.symm ▸ hb_le1_raw
    have hab : a < b := by
      rw [ha_def, hb_def]
      exact hab_raw
    have hC0_ge1 : C0 ≥ 1 := directional_lens_C0_ge1 K V C0 hK hV_pos hC0_def
    have hB_gt_L2 : B > L / 2 := directional_lens_B_gt_L2 C0 L hC0_ge1 hL_pos
    rcases directional_lens_core_shift_bounds x0 p q B L hx0_def hcore_length hB_gt_L2
      with ⟨ha_lt_p_raw, hq_lt_b_raw⟩
    have ha_lt_p : a < p := ha_def.symm ▸ ha_lt_p_raw
    have hq_lt_b : q < b := hb_def.symm ▸ hq_lt_b_raw

    -- Enlarged bounds on [a,b]
    have h2_bound_enl : ∀ x ∈ Icc a b, |h2 x| ≤ d :=
      fun x hx => h2_bound_all x ⟨le_trans ha_ge0 hx.1, le_trans hx.2 hb_le1⟩

    have h2_bound_enl' : ∀ x ∈ Icc (x0 - B) (x0 + B), |deriv h1 x| ≤ d :=
      fun x hx => directional_lens_deriv_bound_conv ha_def hb_def h_deriv2 h2_bound_enl hx
    have h1_bound_enl : ∀ x ∈ Icc a b, |h1 x| ≤ S_enl :=
      directional_lens_h1_bound_enl hB_nonneg hd_pos h1_diff h_deriv2 h2_bound_enl
        (hderiv_core x0 hx0_core) hS_enl_def ha_def hb_def

    have h1_bound_enl' : ∀ x ∈ Icc (x0 - B) (x0 + B), |h1 x| ≤ S_enl :=
      fun x hx => h1_bound_enl x (directional_lens_interval_conv ha_def hb_def hx)
    have h0_bound_enl : ∀ x ∈ Icc a b, |h0 x| ≤ M_enl := by
      intro x hx
      have h : |h0 x| ≤ M_core + S_enl * B :=
        directional_lens_value_bound_enl hB_nonneg hS_enl_nonneg h0_diff h1_bound_enl' h_deriv1 (hval_core x0 hx0_core) ha_def hb_def hx
      have h_eq : M_core + S_enl * B = M_enl := by
        rw [hM_enl_def] <;> ring
      rw [h_eq] at h
      exact h

    -- Curvature gap on [a,b]
    have hcurv_gap_enl : ∀ x ∈ Icc a b, d / K ≤ |h0 x| + |h1 x| + |h2 x| := by
      intro x hx
      exact directional_lens_curv_gap_enl (hK := hK) (hcurv := hcurv) (hw := hw) (hb := hb) (d := d) (hd_def := hd_def)
        a b x ha_ge0 hb_le1 hx
        h0 h1 h2 h0_eq h1_eq h2_eq

    -- Strict bound and c_new ≥ d/(6K) via combined helper
    rcases directional_lens_enlarged_bounds_full K tangency delta t d V L C0 B S_enl M_enl M_core S_core
        hK htang hdelta ht hdt hd_ge_2t hd_le_K hsmall
        hV_def hL_def hC0_def hB_def hM_enl_def hM_core_def hS_enl_def hS_core_def hB_pos hK_pos hd_pos
      with ⟨h_enl_small, hc_new_ge⟩

    -- Curvature constant sign on [a,b]
    have h_curv_result : (∀ x ∈ Icc a b, d / K - M_enl - S_enl ≤ |h2 x|) ∧
        ((∀ x ∈ Icc a b, 0 < h2 x) ∨ (∀ x ∈ Icc a b, h2 x < 0)) :=
      directional_lens_curv_sign_wrapper
        (h0 := h0) (h1 := h1) (h2 := h2) (a := a) (b := b) (d := d) (K := K)
        (M_enl := M_enl) (S_enl := S_enl)
        hab hK hd_pos h2_cont hcurv_gap_enl h0_bound_enl h1_bound_enl h_enl_small
    have h2_abs_lower_enl : ∀ x ∈ Icc a b, d / K - M_enl - S_enl ≤ |h2 x| := h_curv_result.1
    have h2_sign_enl : (∀ x ∈ Icc a b, 0 < h2 x) ∨ (∀ x ∈ Icc a b, h2 x < 0) := h_curv_result.2

    let c_new : ℝ := d / K - M_enl - S_enl
    have hc_new_pos : 0 < c_new := directional_lens_c_new_pos d K M_enl S_enl h_enl_small

    -- Sign matching: since x0 ∈ [p,q] ⊂ [a,b] and h2(x0) > 0 on core, sign on [a,b] is positive
    have h2_pos_enl : ∀ x ∈ Icc a b, 0 < h2 x :=
      directional_lens_match_pos h2 a b x0 p q h2_sign_enl h2_pos hx0_core ha_lt_p hq_lt_b

    have hcurvature_t : curvature * t = d / (6 * K) :=
      directional_lens_curvature_t_eq curvature d K t hcurvature_def hK_pos ht

    have h2_lower_enl : ∀ x ∈ Icc a b, curvature * t ≤ h2 x :=
      directional_lens_curvature_lower h2 a b c_new curvature t d K M_enl S_enl rfl
        h2_abs_lower_enl h2_pos_enl hc_new_ge hcurvature_t

    -- B ≥ 2*S_core/c_new + sqrt(2*V*delta/c_new)
    have hL_nonneg : 0 ≤ L := Real.sqrt_nonneg _
    have hB_ge : B ≥ 2 * S_core / c_new + Real.sqrt (2 * (V * delta) / c_new) :=
      directional_lens_B_ge K tangency delta t d V L C0 B S_core c_new
        hK htang hdelta ht hd_ge_2t hd_pos hV_def hL_sq hL_nonneg hC0_def hB_def hS_core_def hc_new_ge hc_new_pos

    have h2_ge_c_new : ∀ x ∈ Icc a b, c_new ≤ h2 x :=
      directional_lens_abs_to_pos h2_abs_lower_enl h2_pos_enl

    -- Sign change at distance for h_down
    have h_down_x0_neg : h_down x0 < 0 := h_down_neg x0 hx0_core
    have h_down_x0_val : |h_down x0| ≤ V * delta := h_down_bound_core x0 hx0_core
    have h1_x0_bound : |h1 x0| ≤ S_core := hderiv_core x0 hx0_core

    have hS_core_pos : 0 < S_core := directional_lens_S_core_pos tangency d L delta t S_core htang hd_pos hdelta ht hS_core_def hL_def
    have h_sign_change := directional_lens_convex_sign_change_wrapper
      (h_down := h_down) (h1 := h1) (h2 := h2) (x0 := x0) (B := B) (a := a) (b := b) (c_new := c_new)
      (V_delta := V * delta) (S_core := S_core)
      ha_def hb_def
      hc_new_pos hS_core_pos hB_pos
      h_down_diff1 h1_diff h_down_deriv h_deriv2
      h2_ge_c_new
      h_down_x0_val h1_x0_bound h_down_x0_neg hB_ge

    have h_down_a_pos : 0 < h_down a := h_sign_change.2
    have h_down_b_pos : 0 < h_down b := h_sign_change.1

    -- Two zeros localization
    have hV_nonneg' : 0 ≤ V := by positivity
    have hdt_nonneg' : 0 ≤ d / t := by positivity
    have h''_lower : ∀ x ∈ Icc a b, curvature * t ≤ deriv (deriv h_down) x :=
      directional_lens_h''_lower_convex h_down_deriv2 h2_lower_enl
    have h''_upper : ∀ (x : ℝ), x ∈ Icc R.interval.left R.interval.right → |deriv (deriv h_down) x| ≤ (d / t) * t :=
      directional_lens_h''_upper_convex h_down_deriv2 h2_bound_core hp_def hq_def ht
    have hzeros := directional_lens_convex_zeros
      (h_down := h_down) (delta := delta) (t := t) (curvature := curvature)
      (V := V) (d := d) (a := a) (b := b) (p := p) (q := q) (R := R)
      hdelta ht hcurv_pos hV_nonneg' hdt_nonneg'
      ha_lt_p hq_lt_b h_down_diff1 h_down_diff2
      h''_lower h''_upper
      h_down_bound_core h_down_neg h_down_a_pos h_down_b_pos
      hp_def hq_def

    rcases hzeros with ⟨z1, z2, hz1_a, hz12, hz2_b, hzero1, hzero2, hderiv1, hderiv2, hbetween, hz1_loc, hz2_loc⟩

    -- z1, z2 ∈ [0,1]
    have hz1_01 := directional_lens_z1_in_01 (z1 := z1) (z2 := z2) (a := a) (b := b) ha_ge0 hb_le1 hz1_a hz12 hz2_b
    have hz2_01 := directional_lens_z2_in_01 (z1 := z1) (z2 := z2) (a := a) (b := b) ha_ge0 hb_le1 hz1_a hz12 hz2_b

    -- Endpoint containment in I.carrier
    have hz1_Icc : z1 ∈ Icc (R.interval.left - E * L) (R.interval.right + E * L) :=
      directional_lens_localize_interval hE_def hL_def hz1_loc
    have hz2_Icc : z2 ∈ Icc (R.interval.left - E * L) (R.interval.right + E * L) :=
      directional_lens_localize_interval hE_def hL_def hz2_loc

    have hz1_contain := endpoint_containment hK htang hdelta ht hd_ge_2t hsmall
      hV_def curvature E hcurvature_def hE_def I hI R hRsub z1 hz1_Icc
    have hz2_contain := endpoint_containment hK htang hdelta ht hd_ge_2t hsmall
      hV_def curvature E hcurvature_def hE_def I hI R hRsub z2 hz2_Icc

    let z1p : UnitPoint := Classical.choose hz1_contain
    have hz1p_val : (z1p : ℝ) = z1 := (Classical.choose_spec hz1_contain).1
    have hz1p_in : z1p ∈ I.carrier := (Classical.choose_spec hz1_contain).2
    let z2p : UnitPoint := Classical.choose hz2_contain
    have hz2p_val : (z2p : ℝ) = z2 := (Classical.choose_spec hz2_contain).1
    have hz2p_in : z2p ∈ I.carrier := (Classical.choose_spec hz2_contain).2

    -- Graph lens
    have heval_down : ∀ (x : UnitPoint), h_down (x : ℝ) =
        (w.verticalTranslate (-epsilon + shift0_w)) x - (b_fn.verticalTranslate shift0_b) x :=
      fun x => directional_lens_eval_down h0_eq hs_def h_down_def x

    have hp_le_q : p ≤ q := directional_lens_p_le_q hp_def hq_def
    have hx0_01 : x0 ∈ Icc (0 : ℝ) 1 :=
      directional_lens_x0_in_01 ha_ge0 hb_le1 ha_lt_p hq_lt_b hp_le_q hx0_core
    have hx0_enl : x0 ∈ Icc a b := directional_lens_x0_in_Icc_ab ha_lt_p hq_lt_b hx0_core
    have h2_x0_nonzero : h2 x0 ≠ 0 :=
      directional_lens_h2_nonzero_from_pos (h2_ge_c_new x0 hx0_enl) hc_new_pos
    have hne_down : (w.verticalTranslate (-epsilon + shift0_w)) ≠ (b_fn.verticalTranslate shift0_b) :=
      directional_lens_translates_distinct hx0_01 h2_eq h2_x0_nonzero (-epsilon + shift0_w) shift0_b

    have hLens := graphLens_of_negative_between
      (f := w.verticalTranslate (-epsilon + shift0_w))
      (g := b_fn.verticalTranslate shift0_b)
      hne_down heval_down hz1_01 hz2_01 hz12 hzero1 hzero2
      (fun x hx1 hx2 => hbetween x hx1 hx2)

    refine Or.inr (directional_lens_assemble_down
      hbf hz1p_val hz2p_val hz1p_in hz2p_in hz1_Icc hz2_Icc hLens)

  -- ==========================================================================
  -- CONCAVE CASE: h2 < 0 on core → upward shift → Or.inl
  -- ==========================================================================
  · -- Enlargement setup (same as convex)
    let C0 : ℝ := 20 * K * V + 20 * K
    have hC0_def : C0 = 20 * K * V + 20 * K := by rfl
    let B : ℝ := C0 * L
    have hB_def : B = C0 * L := by rfl
    let b_fn : C2Function := b
    have hbf : b_fn = b := by rfl
    let a : ℝ := x0 - B
    have ha_def : a = x0 - B := by rfl
    let b : ℝ := x0 + B
    have hb_def : b = x0 + B := by rfl
    let S_enl : ℝ := S_core + d * B
    let M_enl : ℝ := M_core + S_enl * B
    have hS_enl_def : S_enl = S_core + d * B := by rfl
    have hM_enl_def : M_enl = M_core + S_enl * B := by rfl
    have hV_pos : 0 < V := directional_lens_V_pos tangency V htang hV_def
    have hV_nonneg : 0 ≤ V := hV_pos.le
    have hC0_pos : 0 < C0 := directional_lens_C0_pos K V C0 hK hV_pos hC0_def
    have hC0_nonneg : 0 ≤ C0 := hC0_pos.le
    have hB_pos : 0 < B := directional_lens_B_pos C0 L B hC0_pos hL_pos hB_def
    have hB_nonneg : 0 ≤ B := hB_pos.le
    have hS_core_nonneg : 0 ≤ S_core := (directional_lens_S_core_pos tangency d L delta t S_core htang hd_pos hdelta ht hS_core_def hL_def).le
    have hS_enl_nonneg : 0 ≤ S_enl := by
      rw [hS_enl_def]
      exact directional_lens_S_enl_nonneg S_core d B hS_core_nonneg hd_pos hB_pos

    have hC0_le : C0 ≤ 1000 * K * tangency ^ 10 := by
      simpa [hC0_def, hV_def] using directional_lens_C0_bound K tangency hK htang

    have hL_bound : L ≤ 1 / (Real.sqrt 1000 * K ^ 2 * tangency ^ 25) :=
      sqrt_delta_t_bound hK htang hdelta ht hsmall

    have hB_le : B ≤ 1 / (32 * K) :=
      directional_lens_B_le K tangency C0 L B hK htang hC0_le hL_bound hL_pos.le hB_def

    have hp_lower : p ≥ I.left + 3 * I.length / 8 :=
      directional_lens_hp_lower delta t K hK I hI R hRsub p hp_def
    have hq_upper : q ≤ I.right - 3 * I.length / 8 :=
      directional_lens_hq_upper delta t K hK I hI R hRsub q hq_def

    have hI_length : (12 * K)⁻¹ ≤ I.length := hI.1
    have h6 : 3 * ((12 * K)⁻¹) / 8 = 1 / (32 * K) := by
      field_simp [hK_pos.ne'] <;> ring
    have hp_ge : p ≥ 1 / (32 * K) :=
      directional_lens_p_ge K hK I hI p hp_lower
    have hq_le : q ≤ 1 - 1 / (32 * K) :=
      directional_lens_q_le K hK I hI q hq_upper

    rcases directional_lens_endpoint_bounds K hK x0 p q B hx0_core hp_ge hq_le hB_le hB_pos
      with ⟨ha_ge0_raw, hb_le1_raw, hab_raw⟩
    have ha_ge0 : 0 ≤ a := ha_def.symm ▸ ha_ge0_raw
    have hb_le1 : b ≤ 1 := hb_def.symm ▸ hb_le1_raw
    have hab : a < b := by
      rw [ha_def, hb_def]
      exact hab_raw
    have hC0_ge1 : C0 ≥ 1 := directional_lens_C0_ge1 K V C0 hK hV_pos hC0_def
    have hB_gt_L2 : B > L / 2 := directional_lens_B_gt_L2 C0 L hC0_ge1 hL_pos
    rcases directional_lens_core_shift_bounds x0 p q B L hx0_def hcore_length hB_gt_L2
      with ⟨ha_lt_p_raw, hq_lt_b_raw⟩
    have ha_lt_p : a < p := ha_def.symm ▸ ha_lt_p_raw
    have hq_lt_b : q < b := hb_def.symm ▸ hq_lt_b_raw

    have h2_bound_enl : ∀ x ∈ Icc a b, |h2 x| ≤ d :=
      fun x hx => h2_bound_all x ⟨le_trans ha_ge0 hx.1, le_trans hx.2 hb_le1⟩

    have h2_bound_enl' : ∀ x ∈ Icc (x0 - B) (x0 + B), |deriv h1 x| ≤ d :=
      fun x hx => directional_lens_deriv_bound_conv ha_def hb_def h_deriv2 h2_bound_enl hx
    have h1_bound_enl : ∀ x ∈ Icc a b, |h1 x| ≤ S_enl :=
      directional_lens_h1_bound_enl hB_nonneg hd_pos h1_diff h_deriv2 h2_bound_enl
        (hderiv_core x0 hx0_core) hS_enl_def ha_def hb_def

    have h1_bound_enl' : ∀ x ∈ Icc (x0 - B) (x0 + B), |h1 x| ≤ S_enl :=
      fun x hx => h1_bound_enl x (directional_lens_interval_conv ha_def hb_def hx)
    have h0_bound_enl : ∀ x ∈ Icc a b, |h0 x| ≤ M_enl := by
      intro x hx
      have h : |h0 x| ≤ M_core + S_enl * B :=
        directional_lens_value_bound_enl hB_nonneg hS_enl_nonneg h0_diff h1_bound_enl' h_deriv1 (hval_core x0 hx0_core) ha_def hb_def hx
      have h_eq : M_core + S_enl * B = M_enl := by
        rw [hM_enl_def] <;> ring
      rw [h_eq] at h
      exact h

    have hcurv_gap_enl : ∀ x ∈ Icc a b, d / K ≤ |h0 x| + |h1 x| + |h2 x| := by
      intro x hx
      exact directional_lens_curv_gap_enl (hK := hK) (hcurv := hcurv) (hw := hw) (hb := hb) (d := d) (hd_def := hd_def)
        a b x ha_ge0 hb_le1 hx
        h0 h1 h2 h0_eq h1_eq h2_eq

    -- Strict bound and c_new ≥ d/(6K) via combined helper
    rcases directional_lens_enlarged_bounds_full K tangency delta t d V L C0 B S_enl M_enl M_core S_core
        hK htang hdelta ht hdt hd_ge_2t hd_le_K hsmall
        hV_def hL_def hC0_def hB_def hM_enl_def hM_core_def hS_enl_def hS_core_def hB_pos hK_pos hd_pos
      with ⟨h_enl_small, hc_new_ge⟩

    -- Curvature constant sign on [a,b]
    have h_curv_result : (∀ x ∈ Icc a b, d / K - M_enl - S_enl ≤ |h2 x|) ∧
        ((∀ x ∈ Icc a b, 0 < h2 x) ∨ (∀ x ∈ Icc a b, h2 x < 0)) :=
      directional_lens_curv_sign_wrapper
        (h0 := h0) (h1 := h1) (h2 := h2) (a := a) (b := b) (d := d) (K := K)
        (M_enl := M_enl) (S_enl := S_enl)
        hab hK hd_pos h2_cont hcurv_gap_enl h0_bound_enl h1_bound_enl h_enl_small
    have h2_abs_lower_enl : ∀ x ∈ Icc a b, d / K - M_enl - S_enl ≤ |h2 x| := h_curv_result.1
    have h2_sign_enl : (∀ x ∈ Icc a b, 0 < h2 x) ∨ (∀ x ∈ Icc a b, h2 x < 0) := h_curv_result.2

    let c_new : ℝ := d / K - M_enl - S_enl
    have hc_new_pos : 0 < c_new := directional_lens_c_new_pos d K M_enl S_enl h_enl_small

    have h2_neg_enl : ∀ x ∈ Icc a b, h2 x < 0 :=
      directional_lens_match_neg h2 a b x0 p q h2_sign_enl h2_neg hx0_core ha_lt_p hq_lt_b

    have hcurvature_t : curvature * t = d / (6 * K) :=
      directional_lens_curvature_t_eq curvature d K t hcurvature_def hK_pos ht

    have h2_upper_enl : ∀ x ∈ Icc a b, h2 x ≤ -(curvature * t) :=
      directional_lens_curvature_upper h2 a b c_new curvature t d K M_enl S_enl rfl
        h2_abs_lower_enl h2_neg_enl hc_new_ge hcurvature_t

    have hL_nonneg : 0 ≤ L := Real.sqrt_nonneg _
    have hB_ge : B ≥ 2 * S_core / c_new + Real.sqrt (2 * (V * delta) / c_new) :=
      directional_lens_B_ge K tangency delta t d V L C0 B S_core c_new
        hK htang hdelta ht hd_ge_2t hd_pos hV_def hL_sq hL_nonneg hC0_def hB_def hS_core_def hc_new_ge hc_new_pos

    have h2_le_neg_c_new : ∀ x ∈ Icc a b, h2 x ≤ -c_new :=
      directional_lens_h2_le_neg_c_new h2 a b c_new h2_abs_lower_enl h2_neg_enl

    have h_up_x0_pos : 0 < h_up x0 := h_up_pos x0 hx0_core
    have h_up_x0_val : |h_up x0| ≤ V * delta := h_up_bound_core x0 hx0_core
    have h1_x0_bound : |h1 x0| ≤ S_core := hderiv_core x0 hx0_core

    have hS_core_pos : 0 < S_core := directional_lens_S_core_pos tangency d L delta t S_core htang hd_pos hdelta ht hS_core_def hL_def
    have h_sign_change := directional_lens_concave_sign_change_wrapper
      (h_up := h_up) (h1 := h1) (h2 := h2) (x0 := x0) (B := B) (a := a) (b := b) (c_new := c_new)
      (V_delta := V * delta) (S_core := S_core)
      ha_def hb_def
      hc_new_pos hS_core_pos hB_pos
      h_up_diff1 h1_diff h_up_deriv h_deriv2
      h2_le_neg_c_new
      h_up_x0_val h1_x0_bound h_up_x0_pos hB_ge

    rcases directional_lens_extract_sign_change ha_def hb_def h_sign_change with ⟨h_up_b_neg, h_up_a_neg⟩

    have hV_nonneg'' : 0 ≤ V := by positivity
    have hdt_nonneg'' : 0 ≤ d / t := by positivity
    have h''_upper2 : ∀ x ∈ Icc a b, deriv (deriv h_up) x ≤ -(curvature * t) :=
      directional_lens_h''_upper_concave h_up_deriv2 h2_upper_enl
    have hzeros := directional_lens_concave_zeros_wrapper
      (h_up := h_up) (h2 := h2) (delta := delta) (t := t) (curvature := curvature)
      (V := V) (d := d) (a := a) (b := b) (p := p) (q := q) (E := E) (R := R)
      hE_def hdelta ht hcurv_pos
      hV_nonneg'' hdt_nonneg''
      ha_lt_p hq_lt_b h_up_diff1 h_up_diff2
      h_up_deriv2 h2_bound_core
      h''_upper2
      h_up_bound_core h_up_pos h_up_a_neg h_up_b_neg
      hp_def hq_def

    rcases hzeros with ⟨z1, z2, hz1_a, hz12, hz2_b, hzero1, hzero2, hderiv1, hderiv2, hbetween, hz1_loc, hz2_loc⟩

    have hz1_01 := directional_lens_z1_in_01 (z1 := z1) (z2 := z2) (a := a) (b := b) ha_ge0 hb_le1 hz1_a hz12 hz2_b
    have hz2_01 := directional_lens_z2_in_01 (z1 := z1) (z2 := z2) (a := a) (b := b) ha_ge0 hb_le1 hz1_a hz12 hz2_b

    rcases directional_lens_both_localize delta t z1 z2 V d curvature E L R hE_def hL_def hz1_loc hz2_loc
      with ⟨hz1_Icc, hz2_Icc⟩

    have hz1_contain := endpoint_containment hK htang hdelta ht hd_ge_2t hsmall
      hV_def curvature E hcurvature_def hE_def I hI R hRsub z1 hz1_Icc
    have hz2_contain := endpoint_containment hK htang hdelta ht hd_ge_2t hsmall
      hV_def curvature E hcurvature_def hE_def I hI R hRsub z2 hz2_Icc

    let edata := directional_lens_mk_both_endpoints hz1_contain hz2_contain
    let z1p : UnitPoint := edata.z1p
    let z2p : UnitPoint := edata.z2p
    have hz1p_val := edata.hz1p_val
    have hz2p_val := edata.hz2p_val
    have hz1p_in := edata.hz1p_in
    have hz2p_in := edata.hz2p_in

    -- Graph lens and final assembly
    have h_up_result := @directional_lens_concave_final
      delta t E L I R w b_fn b_fn h0 h_up h2 epsilon s shift0_w shift0_b x0 p q a b c_new
      z1 z2 z1p z2p
      (rfl : b_fn = b_fn)
      h0_eq hs_def h_up_def h2_eq
      hp_def hq_def
      ha_ge0 hb_le1
      ha_lt_p hq_lt_b hx0_core
      h2_le_neg_c_new hc_new_pos
      hz1_01 hz2_01
      hz12 hzero1 hzero2
      hbetween
      hz1p_val hz2p_val
      hz1p_in hz2p_in
      hz1_Icc hz2_Icc
    left
    exact h_up_result

end

end Kakeya.Cinematic
