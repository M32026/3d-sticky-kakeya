import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Asymptotic helper lemmas for WZ1 Lemma 47

Provides the key logarithmic-vs-power decay estimate needed to turn a
`1 / log(|E|)` pigeonhole retention into a constant `rho^epsilon` retention.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal

/--
For any `K > 0` and `a > 0`, there exists `delta₀ ∈ (0,1]` such that
for all `0 < delta ≤ delta₀`:
`K * (Real.log (1/delta) + 1) ≤ 1 / delta^a`.

This follows from the standard fact that `log x = o(x^a)` as `x → ∞`.
-/
lemma log_poly_decay_general (K a : ℝ) (hK : 0 < K) (ha : 0 < a) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        K * (Real.log (1 / delta) + 1) ≤ 1 / delta ^ a := by
  have h_log_ineq : ∀ (y : ℝ), y ≥ 1 → ∀ (β : ℝ), 0 < β →
      Real.log y ≤ y^β / β := by
    intro y hy β hβ
    have h_pos : 0 < y^β := by positivity
    have h1 : Real.log (y^β) ≤ y^β - 1 := Real.log_le_sub_one_of_pos h_pos
    have h2 : Real.log (y^β) = β * Real.log y := by
      rw [Real.log_rpow (by linarith)]
    have h3 : β * Real.log y ≤ y^β - 1 := by linarith
    have h4 : Real.log y ≤ (y^β - 1) / β := by
      calc
        Real.log y = (β * Real.log y) / β := by field_simp [hβ.ne'] <;> ring
        _ ≤ (y^β - 1) / β := by gcongr
    have h5 : (y^β - 1) / β ≤ y^β / β := by
      have h6 : y^β - 1 ≤ y^β := by linarith
      gcongr
    exact h4.trans h5
  set b : ℝ := a / 2 with hb_def
  have hb_pos : 0 < b := by positivity
  let delta₁ : ℝ := (a / (4 * K)) ^ (1 / b)
  let delta₂ : ℝ := (1 / (2 * K)) ^ (1 / a)
  let delta₀ : ℝ := min 1 (min delta₁ delta₂)
  have hδ₀_pos : 0 < delta₀ := by positivity
  have hδ₀_le_one : delta₀ ≤ 1 := min_le_left _ _
  have hδ₀_le₁ : delta₀ ≤ delta₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₀_le₂ : delta₀ ≤ delta₂ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨delta₀, hδ₀_pos, hδ₀_le_one, ?_⟩
  intro delta hdelta hdelta_le
  have h1 : delta ^ b ≤ a / (4 * K) := by
    have h2 : delta ≤ delta₁ := hdelta_le.trans hδ₀_le₁
    have h3 : delta ^ b ≤ delta₁ ^ b := by gcongr <;> positivity
    have h4 : delta₁ ^ b = a / (4 * K) := by
      simp only [delta₁]
      rw [←Real.rpow_mul (by positivity)]
      have h5 : (1 / b) * b = 1 := by field_simp [hb_pos.ne'] <;> ring
      rw [h5, Real.rpow_one]
    rw [h4] at h3
    exact h3
  have h5 : delta ^ a ≤ 1 / (2 * K) := by
    have h6 : delta ≤ delta₂ := hdelta_le.trans hδ₀_le₂
    have h7 : delta ^ a ≤ delta₂ ^ a := by gcongr <;> positivity
    have h8 : delta₂ ^ a = 1 / (2 * K) := by
      simp only [delta₂]
      rw [←Real.rpow_mul (by positivity)]
      have h9 : (1 / a) * a = 1 := by field_simp [ha.ne'] <;> ring
      rw [h9, Real.rpow_one]
    rw [h8] at h7
    exact h7
  have h_y_ge1 : 1 / delta ≥ 1 := by
    have h9 : delta ≤ 1 := hdelta_le.trans hδ₀_le_one
    apply one_le_one_div <;> linarith
  have h_log : Real.log (1 / delta) ≤ (1 / delta) ^ b / b := h_log_ineq (1 / delta) h_y_ge1 b hb_pos
  have h10 : (1 / delta) ^ b = 1 / delta ^ b := by
    have h_pos1 : 0 ≤ (1 : ℝ) := by norm_num
    have h_pos2 : 0 ≤ delta := by linarith
    have h : (1 / delta) ^ b = (1 : ℝ) ^ b / delta ^ b := Real.div_rpow h_pos1 h_pos2 b
    rw [h]
    have h2 : (1 : ℝ) ^ b = 1 := by simp
    rw [h2] <;> ring
  have h11 : Real.log (1 / delta) ≤ (1 / delta ^ b) / b := by
    rw [h10] at h_log
    exact h_log
  have h12 : K * Real.log (1 / delta) * delta ^ a ≤ 1 / 2 := by
    calc
      K * Real.log (1 / delta) * delta ^ a
        ≤ K * ((1 / delta ^ b) / b) * delta ^ a := by gcongr
      _ = K / b * delta ^ (a - b) := by
        have h13 : a - b = b := by simp [hb_def] <;> ring
        have h_pos_b : 0 < delta ^ b := by positivity
        have h14 : K * ((1 / delta ^ b) / b) * delta ^ a = K / b * (delta ^ a / delta ^ b) := by
          ring
        rw [h14]
        have h15 : delta ^ a / delta ^ b = delta ^ (a - b) := by
          rw [←Real.rpow_sub (by linarith)] <;> ring
        rw [h15]
      _ = K / b * delta ^ b := by
        have h13 : a - b = b := by
          dsimp only [b] <;> ring
        rw [h13]
      _ ≤ K / b * (a / (4 * K)) := by gcongr
      _ = 1 / 2 := by
        have hK_ne : K ≠ 0 := hK.ne'
        have ha_ne : a ≠ 0 := ha.ne'
        dsimp only [b]
        have h_eq : K / (a / 2) * (a / (4 * K)) = 1 / 2 := by
          have h1 : K / (a / 2) = 2 * K / a := by
            field_simp [ha_ne] <;> ring
          rw [h1]
          have h2 : (2 * K / a) * (a / (4 * K)) = 1 / 2 := by
            field_simp [ha_ne, hK_ne] <;> ring
          exact h2
        exact h_eq
  have h14 : K * delta ^ a ≤ 1 / 2 := by
    calc
      K * delta ^ a ≤ K * (1 / (2 * K)) := by gcongr
      _ = 1 / 2 := by
        field_simp [hK.ne'] <;> ring
  have h15 : K * (Real.log (1 / delta) + 1) * delta ^ a ≤ 1 := by
    have h16 : K * (Real.log (1 / delta) + 1) * delta ^ a =
        K * Real.log (1 / delta) * delta ^ a + K * delta ^ a := by ring
    rw [h16]
    linarith
  have h17 : K * (Real.log (1 / delta) + 1) ≤ 1 / delta ^ a := by
    have h18 : 0 < delta ^ a := by positivity
    have h19 : K * (Real.log (1 / delta) + 1) * delta ^ a ≤ 1 := h15
    have h20 : K * (Real.log (1 / delta) + 1) ≤ 1 / delta ^ a := by
      calc
        K * (Real.log (1 / delta) + 1)
          = (K * (Real.log (1 / delta) + 1) * delta ^ a) / delta ^ a := by
            field_simp [h18.ne'] <;> ring
        _ ≤ 1 / delta ^ a := by gcongr
    exact h20
  exact h17

/--
Key asymptotic estimate for the WZ1 anisotropic Frostman rescaling.

For any `epsilon > 0` and `Cpack > 0`, there exists `delta₀ ∈ (0,1]` such that
for all `0 < delta ≤ delta₀`, all `0 < rho ≤ delta^epsilon`, and all natural
`N ≤ Cpack / delta^2`:

`4 * Real.rpow rho epsilon * (Real.log N + 2) ≤ 1`.

This justifies upgrading the `1/log` pigeonhole retention to a `4 * rho^epsilon`
retention: since `log_2(N) + 1 ≤ (log N + 1) / log 2 ≤ log N + 2` (for N ≥ 1),
we get `4 * rho^epsilon * (log_2(N) + 1) ≤ 1`.
-/
lemma frostman_rescaling_retention_bound
    (epsilon Cpack : ℝ) (hepsilon : 0 < epsilon) (hCpack : 1 ≤ Cpack) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      ∀ rho : ℝ, 0 < rho → rho ≤ Real.rpow delta epsilon →
      ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ Cpack / delta^2 →
        4 * Real.rpow rho epsilon * (Real.log (N : ℝ) + 2) ≤ 1 := by
  set a : ℝ := epsilon ^ 2 with ha_def
  have ha_pos : 0 < a := by positivity
  have hlogC_nonneg : 0 ≤ Real.log Cpack := Real.log_nonneg hCpack
  set B : ℝ := Real.log Cpack + 3 with hB_def
  have hB_ge2 : 2 ≤ B := by linarith
  set K : ℝ := 4 * B with hK_def
  have hK_pos : 0 < K := by positivity
  rcases log_poly_decay_general K a hK_pos ha_pos with ⟨delta₀, hdelta₀_pos, hdelta₀_le_one, h_main⟩
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_le_one, ?_⟩
  intro delta hdelta hdelta_le rho hrho hrho_le N hN1 hN_bound
  have h1 : Real.rpow rho epsilon ≤ Real.rpow delta a := by
    calc
      Real.rpow rho epsilon ≤ Real.rpow (Real.rpow delta epsilon) epsilon := by
        have h_nonneg : 0 ≤ rho := by linarith
        have h_eps : 0 ≤ epsilon := by linarith
        exact Real.rpow_le_rpow h_nonneg hrho_le h_eps
      _ = Real.rpow delta (epsilon * epsilon) := by
        have h_mul : Real.rpow delta (epsilon * epsilon) = Real.rpow (Real.rpow delta epsilon) epsilon :=
          Real.rpow_mul (show 0 ≤ delta by linarith) epsilon epsilon
        exact h_mul.symm
      _ = Real.rpow delta a := by
        have h_eq : epsilon * epsilon = a := by
          simp [ha_def] <;> ring
        rw [h_eq]
  have h_log2 : Real.log (N : ℝ) ≤ Real.log (Cpack / delta^2) := by
    apply Real.log_le_log
    · exact_mod_cast hN1
    · exact hN_bound
  have h_log3 : Real.log (Cpack / delta^2) = Real.log Cpack + 2 * Real.log (1 / delta) := by
    have h_pos1 : 0 < Cpack := by linarith
    have h_pos2 : 0 < delta^2 := by positivity
    have h1 : Real.log (Cpack / delta^2) = Real.log Cpack - Real.log (delta^2) :=
      Real.log_div (ne_of_gt h_pos1) (ne_of_gt h_pos2)
    have h2 : Real.log (delta^2) = 2 * Real.log delta := by
      have h21 : Real.log (delta^2) = Real.log (delta * delta) := by ring_nf
      rw [h21, Real.log_mul (by linarith) (by linarith)] <;> ring
    have h3 : Real.log (1 / delta) = -Real.log delta := by
      rw [Real.log_div (by norm_num) (ne_of_gt hdelta)]
      <;> simp
    rw [h1, h2, h3] <;> ring
  have h_log4 : Real.log (N : ℝ) + 2 ≤ B * (Real.log (1 / delta) + 1) := by
    have h5 : Real.log (1 / delta) ≥ 0 := by
      have h6 : 1 / delta ≥ 1 := by
        have h7 : delta ≤ 1 := hdelta_le.trans hdelta₀_le_one
        apply one_le_one_div <;> linarith
      exact Real.log_nonneg h6
    calc
      Real.log (N : ℝ) + 2
        ≤ Real.log Cpack + 2 * Real.log (1 / delta) + 2 := by linarith [h_log2, h_log3]
      _ = (Real.log Cpack + 2) + 2 * Real.log (1 / delta) := by ring
      _ ≤ B + B * Real.log (1 / delta) := by
        dsimp only [B]
        have h7 : Real.log Cpack + 2 ≤ Real.log Cpack + 3 := by linarith
        have h8 : 2 * Real.log (1 / delta) ≤ (Real.log Cpack + 3) * Real.log (1 / delta) := by
          gcongr
          <;> linarith
        linarith
      _ = B * (Real.log (1 / delta) + 1) := by ring
  have h_pos_a : 0 ≤ Real.rpow delta a := Real.rpow_nonneg (by linarith) a
  have h9 : 4 * Real.rpow rho epsilon * (Real.log (N : ℝ) + 2) ≤
      K * (Real.log (1 / delta) + 1) * Real.rpow delta a := by
    have h91 : 4 * Real.rpow rho epsilon ≤ 4 * Real.rpow delta a := by gcongr
    have h92 : 0 ≤ Real.log (N : ℝ) + 2 := by positivity
    calc
      4 * Real.rpow rho epsilon * (Real.log (N : ℝ) + 2)
        ≤ 4 * Real.rpow delta a * (Real.log (N : ℝ) + 2) := by
          exact mul_le_mul_of_nonneg_right h91 h92
      _ ≤ 4 * Real.rpow delta a * (B * (Real.log (1 / delta) + 1)) := by
          gcongr
      _ = K * (Real.log (1 / delta) + 1) * Real.rpow delta a := by
          dsimp only [K] <;> ring
  have h_decay : K * (Real.log (1 / delta) + 1) ≤ 1 / delta ^ a := h_main delta hdelta hdelta_le
  have h13 : K * (Real.log (1 / delta) + 1) * Real.rpow delta a ≤ 1 := by
    have h14 : Real.rpow delta a = delta ^ a := by rfl
    rw [h14]
    have h15 : K * (Real.log (1 / delta) + 1) * delta ^ a ≤ (1 / delta ^ a) * delta ^ a := by
      gcongr
    have h16 : (1 / delta ^ a) * delta ^ a = 1 := by
      field_simp [hdelta.ne'] <;> ring
    rw [h16] at h15
    exact h15
  exact h9.trans h13

end Kakeya.Assouad
