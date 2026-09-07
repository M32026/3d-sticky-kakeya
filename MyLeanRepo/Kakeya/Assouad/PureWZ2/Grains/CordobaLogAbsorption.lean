import MyLeanRepo.Kakeya.Assouad.WZ1.AsymptoticHelpers
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Córdoba L² logarithmic absorption for PureWZ2

Proves the logarithmic absorption condition required by
`pureWz2_cordoba_slab_lower_no_incidence`:

`L^ε₁ * (288 + 56448 * (1 + log k)) ≤ 125/108`

for all `k ≤ 100/L³`, provided `L` is sufficiently small relative to `ε₁`.
-/

noncomputable section

namespace Kakeya.Assouad

open Real

/-- Existence of a scale threshold for the Córdoba log absorption. -/
lemma cordoba_log_absorption_exists
    {epsilon₁ : ℝ} (heps₁_pos : 0 < epsilon₁) :
    ∃ (L₀ : ℝ), 0 < L₀ ∧ L₀ ≤ 1 ∧
      ∀ (L : ℝ), 0 < L → L ≤ L₀ →
        ∀ (k : ℕ), 0 < k → (k : ℝ) ≤ 100 / L^3 →
          Real.rpow L epsilon₁ *
            (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108 := by
  have h_exp1_gt2 : (2 : ℝ) < Real.exp 1 := by
    have h : (1 + 1 : ℝ) < Real.exp 1 := Real.add_one_lt_exp (by norm_num)
    exact_mod_cast h
  have h_exp_pow : ∀ n : ℕ, Real.exp (n : ℝ) = (Real.exp 1)^n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      have h_add : Real.exp ((n.succ : ℝ)) = Real.exp (n : ℝ) * Real.exp 1 := by
        have h_eq : (n.succ : ℝ) = (n : ℝ) + 1 := by simp
        rw [h_eq, Real.exp_add]
      rw [h_add, ih]
      <;> simp [pow_succ] <;> ring
  have h_exp10 : Real.exp 10 = (Real.exp 1)^10 := h_exp_pow 10
  have h_exp10_gt100 : (100 : ℝ) < Real.exp 10 := by
    rw [h_exp10]
    have h3 : (2 : ℝ)^10 < (Real.exp 1)^10 := by gcongr <;> linarith
    norm_num at h3 ⊢ <;> linarith
  have hlog100 : Real.log 100 ≤ 10 := by
    have h : Real.log 100 < 10 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      exact h_exp10_gt100
    exact h.le
  let C : ℝ := 621216
  have hC_pos : 0 < C := by norm_num
  let K : ℝ := C * (108 / 125)
  have hK_pos : 0 < K := by positivity
  rcases log_poly_decay_general K epsilon₁ hK_pos heps₁_pos with
    ⟨L₀, hL₀_pos, hL₀_one, h_main⟩
  refine ⟨L₀, hL₀_pos, hL₀_one, ?_⟩
  intro L hL_pos hL_le k hk_pos hk_upper
  have hL_one : L ≤ 1 := hL_le.trans hL₀_one
  have hlog_inv_nonneg : 0 ≤ Real.log (1 / L) := by
    have h1 : 1 ≤ 1 / L := by
      rw [one_le_div hL_pos] <;> linarith
    exact Real.log_nonneg h1
  have hlog_k : Real.log (k : ℝ) ≤ Real.log (100 / L^3) :=
    Real.log_le_log (by exact_mod_cast hk_pos) hk_upper
  have hlog100_L3 : Real.log (100 / L^3) =
      Real.log 100 + 3 * Real.log (1 / L) := by
    have h1 : Real.log (100 / L^3) = Real.log 100 - Real.log (L^3) := by
      rw [Real.log_div (by norm_num) (by positivity)]
    have h2 : Real.log (L^3) = 3 * Real.log L := by
      rw [Real.log_pow] <;> norm_num
    have h3 : Real.log (1 / L) = -Real.log L := by
      rw [Real.log_div (by norm_num) hL_pos.ne'] <;> simp
    rw [h1, h2, h3] <;> ring
  have h_ineq : 1 + Real.log (k : ℝ) ≤ 11 + 3 * Real.log (1 / L) := by
    have h7 : Real.log (k : ℝ) ≤ Real.log 100 + 3 * Real.log (1 / L) := by
      rw [←hlog100_L3]
      exact hlog_k
    linarith [hlog100]
  have h_bracket : 288 + 56448 * (1 + Real.log (k : ℝ)) ≤
      C * (Real.log (1 / L) + 1) := by
    have h_step1 : 288 + 56448 * (1 + Real.log (k : ℝ)) ≤
        288 + 56448 * (11 + 3 * Real.log (1 / L)) := by
      have h : 1 + Real.log (k : ℝ) ≤ 11 + 3 * Real.log (1 / L) := h_ineq
      nlinarith
    have h_step2 : 288 + 56448 * (11 + 3 * Real.log (1 / L)) =
        621216 + 169344 * Real.log (1 / L) := by norm_num <;> ring
    have h_step3 : 621216 + 169344 * Real.log (1 / L) ≤
        C * (Real.log (1 / L) + 1) := by
      dsimp only [C]
      nlinarith [hlog_inv_nonneg]
    calc
      288 + 56448 * (1 + Real.log (k : ℝ))
        ≤ 288 + 56448 * (11 + 3 * Real.log (1 / L)) := h_step1
      _ = 621216 + 169344 * Real.log (1 / L) := h_step2
      _ ≤ C * (Real.log (1 / L) + 1) := h_step3
  have h_decay : K * (Real.log (1 / L) + 1) ≤ 1 / Real.rpow L epsilon₁ :=
    h_main L hL_pos hL_le
  have h_rpow_pos : 0 < Real.rpow L epsilon₁ := Real.rpow_pos_of_pos hL_pos _
  have hK_eq : C = K * (125 / 108) := by
    dsimp only [K] <;> ring
  have h_product : Real.rpow L epsilon₁ * K * (Real.log (1 / L) + 1) ≤ 1 := by
    have h4 : K * (Real.log (1 / L) + 1) ≤ 1 / Real.rpow L epsilon₁ := h_decay
    have h5 : Real.rpow L epsilon₁ * (K * (Real.log (1 / L) + 1)) ≤ 1 := by
      calc Real.rpow L epsilon₁ * (K * (Real.log (1 / L) + 1))
        ≤ Real.rpow L epsilon₁ * (1 / Real.rpow L epsilon₁) := by gcongr
      _ = 1 := by field_simp [h_rpow_pos.ne'] <;> ring
    linarith
  calc
    Real.rpow L epsilon₁ * (288 + 56448 * (1 + Real.log (k : ℝ)))
      ≤ Real.rpow L epsilon₁ * (C * (Real.log (1 / L) + 1)) := by gcongr
    _ = (125 / 108) * (Real.rpow L epsilon₁ * K * (Real.log (1 / L) + 1)) := by
      have h_eq : Real.rpow L epsilon₁ * (C * (Real.log (1 / L) + 1)) =
               (125 / 108) * (Real.rpow L epsilon₁ * K * (Real.log (1 / L) + 1)) := by
        rw [hK_eq] <;> ring
      exact h_eq
    _ ≤ (125 / 108) * 1 := by gcongr
    _ = 125 / 108 := by ring

/-- Axis-separation condition for the Córdoba argument.

`4 * (6L)^2 ≤ (3/4) * (L^(1-ε₃))^2` simplifies to `L^(2-4ε₁) ≤ 1/192`.
-/
lemma cordoba_ax_condition_exists
    {epsilon₁ : ℝ} (heps₁_pos : 0 < epsilon₁) (heps₁_lt_half : epsilon₁ < 1 / 2) :
    ∃ (L₁ : ℝ), 0 < L₁ ∧ L₁ ≤ 1 ∧
      ∀ (L : ℝ), 0 < L → L ≤ L₁ →
        ∀ (epsilon₃ : ℝ), epsilon₃ = 1 - 2 * epsilon₁ →
          4 * (6 * L)^2 ≤ (3 / 4 : ℝ) * (Real.rpow L (1 - epsilon₃))^2 := by
  set a : ℝ := 2 - 4 * epsilon₁ with ha_def
  have ha_pos : 0 < a := by linarith
  let L₁ : ℝ := (1 / 192 : ℝ) ^ (1 / a)
  have hL₁_pos : 0 < L₁ := by positivity
  have hL₁_one : L₁ ≤ 1 := by
    have h1 : (1 / 192 : ℝ) < 1 := by norm_num
    have h2 : 0 < 1 / a := by positivity
    have h3 : (1 / 192 : ℝ) ^ (1 / a) ≤ 1 :=
      Real.rpow_le_one (by norm_num) h1.le h2.le
    exact h3
  refine ⟨L₁, hL₁_pos, hL₁_one, ?_⟩
  intro L hL_pos hL_le epsilon₃ heps₃_eq
  have h1 : 1 - epsilon₃ = 2 * epsilon₁ := by linarith [heps₃_eq]
  have h2 : 2 * (1 - epsilon₃) = 4 * epsilon₁ := by linarith
  have h3 : Real.rpow L a ≤ 1 / 192 := by
    have h41 : 0 ≤ L := by linarith
    have h42 : 0 ≤ a := by linarith
    have h4 : Real.rpow L a ≤ Real.rpow L₁ a :=
      Real.rpow_le_rpow h41 hL_le h42
    have h5 : Real.rpow L₁ a = 1 / 192 := by
      have h_pos_base : 0 < (1 / 192 : ℝ) := by norm_num
      have h10 : Real.rpow L₁ a = Real.rpow (Real.rpow (1 / 192 : ℝ) (1 / a)) a := by
        congr 1 <;> simp [L₁]
      rw [h10]
      have h11 : Real.rpow (Real.rpow (1 / 192 : ℝ) (1 / a)) a =
                   Real.rpow (1 / 192 : ℝ) ((1 / a) * a) :=
        (Real.rpow_mul (by positivity) (1 / a) a).symm
      rw [h11]
      have h12 : (1 / a) * a = 1 := by field_simp [ha_pos.ne'] <;> ring
      rw [h12]
      have h13 : Real.rpow (1 / 192 : ℝ) 1 = 1 / 192 := by simp
      exact h13
    rw [h5] at h4
    exact h4
  have h4 : 4 * epsilon₁ = 2 - a := by dsimp only [a] <;> ring
  have h_pos_a : 0 < Real.rpow L a := Real.rpow_pos_of_pos hL_pos _
  have h5 : Real.rpow L (4 * epsilon₁) = L^2 / Real.rpow L a := by
    rw [h4]
    have h_posa : 0 < Real.rpow L a := Real.rpow_pos_of_pos hL_pos _
    have h_sum1 : (2 - a) + a = 2 := by ring
    have h61 : Real.rpow L (2 - a) * Real.rpow L a = Real.rpow L 2 := by
      have h : Real.rpow L (2 - a) * Real.rpow L a = Real.rpow L ((2 - a) + a) :=
        (Real.rpow_add hL_pos (2 - a) a).symm
      rw [h, h_sum1]
    have h64 : Real.rpow L (2 - a) = Real.rpow L 2 / Real.rpow L a := by
      field_simp [h_posa.ne'] at h61 ⊢ <;> linarith
    rw [h64]
    have h65 : Real.rpow L 2 = L ^ 2 := by simp
    rw [h65]
  have h6 : (Real.rpow L (1 - epsilon₃)) ^ 2 = Real.rpow L (2 * (1 - epsilon₃)) := by
    have h61 : (Real.rpow L (1 - epsilon₃)) ^ 2 =
        Real.rpow L (1 - epsilon₃) * Real.rpow L (1 - epsilon₃) := by ring
    rw [h61]
    have h62 : Real.rpow L ((1 - epsilon₃) + (1 - epsilon₃)) =
                 Real.rpow L (1 - epsilon₃) * Real.rpow L (1 - epsilon₃) :=
      Real.rpow_add hL_pos (1 - epsilon₃) (1 - epsilon₃)
    have h63 : (1 - epsilon₃) + (1 - epsilon₃) = 2 * (1 - epsilon₃) := by ring
    rw [h63] at h62
    exact h62.symm
  rw [h6, h2, h5]
  have h8 : (192 : ℝ) ≤ 1 / Real.rpow L a := by
    have h9 : Real.rpow L a ≤ 1 / 192 := h3
    have h10 : 1 / Real.rpow L a ≥ 1 / (1 / 192 : ℝ) := by gcongr
    have h11 : 1 / (1 / 192 : ℝ) = 192 := by norm_num
    rw [h11] at h10
    exact h10
  have h12 : (3 / 4 : ℝ) * (L^2 / Real.rpow L a) ≥ 144 * L^2 := by
    have h13 : (3 / 4 : ℝ) / Real.rpow L a ≥ 144 := by
      have h14 : (3 / 4 : ℝ) / Real.rpow L a = (3 / 4 : ℝ) * (1 / Real.rpow L a) := by ring
      rw [h14]
      have h15 : (3 / 4 : ℝ) * (1 / Real.rpow L a) ≥ (3 / 4 : ℝ) * 192 := by gcongr
      have h16 : (3 / 4 : ℝ) * 192 = 144 := by norm_num
      linarith
    have h17 : 0 ≤ L^2 := by positivity
    have h18 : (3 / 4 : ℝ) * (L^2 / Real.rpow L a) = L^2 * ((3 / 4 : ℝ) / Real.rpow L a) := by ring
    rw [h18]
    nlinarith
  have h19 : 4 * (6 * L)^2 = 144 * L^2 := by ring
  rw [h19]
  exact h12

end Kakeya.Assouad

end
