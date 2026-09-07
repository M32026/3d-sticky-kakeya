import MyLeanRepo.Kakeya.Cinematic.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Logarithmic absorption for the local cinematic assembly

These lemmas absorb the logarithmic losses produced by the Section 5 dyadic
selection and bipartite rectangle count.
-/

noncomputable section

open Real

namespace Kakeya.Cinematic

theorem localAssembly_log_absorption_general
    (A C ε : ℝ) (hA : 0 < A) (hC : 0 < C) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        A * (Real.log (C / δ) + 1) ≤ Real.rpow δ (-ε) := by
  let α : ℝ := ε / 2
  have hα : 0 < α := by positivity
  have h_log_bound :
      ∀ x : ℝ, 1 ≤ x → Real.log x ≤ Real.rpow x α / α := by
    intro x hx
    have hx_pos : 0 < x := by linarith
    have h1 : Real.log (Real.rpow x α) ≤ Real.rpow x α - 1 :=
      Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx_pos α)
    have h2 : Real.log (Real.rpow x α) = α * Real.log x := by
      simpa using Real.log_rpow hx_pos α
    have h3 : α * Real.log x ≤ Real.rpow x α - 1 := by
      rw [← h2]
      exact h1
    have h4 : Real.log x = (α * Real.log x) / α := by
      field_simp [hα.ne']
    rw [h4]
    have h5 :
        (α * Real.log x) / α ≤ (Real.rpow x α - 1) / α := by
      exact div_le_div_of_nonneg_right h3 hα.le
    have h6 :
        (Real.rpow x α - 1) / α ≤ Real.rpow x α / α := by
      exact div_le_div_of_nonneg_right (by linarith) hα.le
    exact h5.trans h6
  let K1 : ℝ := Real.rpow (4 * A / ε) (2 / ε)
  let K2 : ℝ := Real.rpow (2 * A * (|Real.log C| + 1)) (1 / ε)
  let x₀ : ℝ := max 1 (max K1 K2)
  have hx₀_pos : 0 < x₀ := by positivity
  have hx₀_ge_one : 1 ≤ x₀ := le_max_left _ _
  have hK1_pos : 0 < 4 * A / ε := by positivity
  have hK2_pos : 0 < 2 * A * (|Real.log C| + 1) := by positivity
  have h_rpow_comp :
      ∀ a : ℝ, 0 < a → ∀ b c : ℝ,
        Real.rpow (Real.rpow a b) c = Real.rpow a (b * c) := by
    intro a ha b c
    exact (Real.rpow_mul ha.le b c).symm
  have h_main :
      ∀ x : ℝ, x₀ ≤ x →
        A * (Real.log (C * x) + 1) ≤ Real.rpow x ε := by
    intro x hx
    have hx_ge_one : 1 ≤ x := hx₀_ge_one.trans hx
    have hx_pos : 0 < x := by linarith
    have h_log_Cx : Real.log (C * x) = Real.log C + Real.log x := by
      rw [Real.log_mul hC.ne' hx_pos.ne']
    have h_log_x : Real.log x ≤ Real.rpow x α / α :=
      h_log_bound x hx_ge_one
    have h_abs_log_C : Real.log C ≤ |Real.log C| := le_abs_self _
    have h_sum_le :
        Real.log C + Real.log x + 1 ≤
          |Real.log C| + 1 + Real.rpow x α / α := by
      linarith
    have h_bound1 :
        A * (Real.log C + Real.log x + 1) ≤
          A * (|Real.log C| + 1 + Real.rpow x α / α) :=
      mul_le_mul_of_nonneg_left h_sum_le hA.le
    have h_K1 : K1 ≤ x := by
      exact (le_max_left K1 K2).trans ((le_max_right 1 (max K1 K2)).trans hx)
    have h_K2 : K2 ≤ x := by
      exact (le_max_right K1 K2).trans ((le_max_right 1 (max K1 K2)).trans hx)
    have hK1_pos' : 0 < K1 := Real.rpow_pos_of_pos hK1_pos _
    have h_xε2_ge : 4 * A / ε ≤ Real.rpow x (ε / 2) := by
      have h6 :
          Real.rpow K1 (ε / 2) ≤ Real.rpow x (ε / 2) :=
        Real.rpow_le_rpow hK1_pos'.le h_K1 (by positivity)
      have h7 : Real.rpow K1 (ε / 2) = 4 * A / ε := by
        dsimp only [K1]
        rw [h_rpow_comp (4 * A / ε) hK1_pos (2 / ε) (ε / 2)]
        have h9 : (2 / ε) * (ε / 2) = 1 := by
          field_simp [hε.ne']
        rw [h9]
        simp
      rwa [h7] at h6
    have hK2_pos' : 0 < K2 := Real.rpow_pos_of_pos hK2_pos _
    have h_xε_ge :
        2 * A * (|Real.log C| + 1) ≤ Real.rpow x ε := by
      have h6 : Real.rpow K2 ε ≤ Real.rpow x ε :=
        Real.rpow_le_rpow hK2_pos'.le h_K2 hε.le
      have h7 :
          Real.rpow K2 ε = 2 * A * (|Real.log C| + 1) := by
        dsimp only [K2]
        rw [h_rpow_comp (2 * A * (|Real.log C| + 1)) hK2_pos (1 / ε) ε]
        have h9 : (1 / ε) * ε = 1 := by
          field_simp [hε.ne']
        rw [h9]
        simp
      rwa [h7] at h6
    have h8 :
        A * (|Real.log C| + 1 + Real.rpow x α / α) =
          A * (|Real.log C| + 1) + A * (Real.rpow x α / α) := by
      ring
    have h9 :
        A * (Real.rpow x α / α) =
          (2 * A / ε) * Real.rpow x (ε / 2) := by
      dsimp only [α]
      ring
    have h10 :
        (2 * A / ε) * Real.rpow x (ε / 2) ≤
          Real.rpow x ε / 2 := by
      have h12 :
          2 * A / ε ≤ Real.rpow x (ε / 2) / 2 := by
        have h :
            (4 * A / ε) / 2 ≤ Real.rpow x (ε / 2) / 2 :=
          div_le_div_of_nonneg_right h_xε2_ge (by norm_num)
        have h2 : (4 * A / ε) / 2 = 2 * A / ε := by ring
        rwa [h2] at h
      have h13 :
          (2 * A / ε) * Real.rpow x (ε / 2) ≤
            Real.rpow x (ε / 2) * Real.rpow x (ε / 2) / 2 := by
        nlinarith [Real.rpow_pos_of_pos hx_pos (ε / 2)]
      have h14 :
          Real.rpow x (ε / 2) * Real.rpow x (ε / 2) =
            Real.rpow x ε := by
        have h141 :
            Real.rpow x ((ε / 2) + (ε / 2)) =
              Real.rpow x (ε / 2) * Real.rpow x (ε / 2) :=
          Real.rpow_add hx_pos (ε / 2) (ε / 2)
        simpa using h141.symm
      rwa [h14] at h13
    have h15 :
        A * (|Real.log C| + 1) ≤ Real.rpow x ε / 2 := by
      linarith
    calc
      A * (Real.log (C * x) + 1) =
          A * (Real.log C + Real.log x + 1) := by rw [h_log_Cx]
      _ ≤ A * (|Real.log C| + 1 + Real.rpow x α / α) := h_bound1
      _ = A * (|Real.log C| + 1) + A * (Real.rpow x α / α) := h8
      _ = A * (|Real.log C| + 1) +
          (2 * A / ε) * Real.rpow x (ε / 2) := by rw [h9]
      _ ≤ Real.rpow x ε / 2 + Real.rpow x ε / 2 := by gcongr
      _ = Real.rpow x ε := by ring
  let δ₀ : ℝ := 1 / x₀
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_le_one : δ₀ ≤ 1 := by
    exact (div_le_one hx₀_pos).mpr hx₀_ge_one
  refine ⟨δ₀, hδ₀_pos, hδ₀_le_one, ?_⟩
  intro δ hδ hδ₀
  have h_x_ge : x₀ ≤ 1 / δ := by
    have h3 : 1 / δ₀ ≤ 1 / δ :=
      one_div_le_one_div_of_le hδ hδ₀
    have h4 : 1 / δ₀ = x₀ := by
      dsimp only [δ₀]
      field_simp [hx₀_pos.ne']
    rwa [h4] at h3
  set x : ℝ := 1 / δ with hx_def
  have hCδ : C / δ = C * x := by
    rw [hx_def, div_eq_mul_inv, one_div]
  have hδ_negε : Real.rpow δ (-ε) = Real.rpow x ε := by
    have h2 : x = δ⁻¹ := by simp [hx_def]
    have h31 : δ⁻¹ = Real.rpow δ (-1 : ℝ) := by
      simpa [Real.rpow_neg] using (Real.rpow_neg hδ.le 1).symm
    have h3 : Real.rpow (δ⁻¹) ε = Real.rpow δ (-ε) := by
      rw [h31, h_rpow_comp δ hδ (-1 : ℝ) ε]
      congr 1
      ring
    rw [h2, h3]
  rw [hCδ, hδ_negε]
  exact h_main x h_x_ge

theorem localAssembly_log_absorption
    (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        4 * (Real.logb 2 (C / δ) + 1) ≤ Real.rpow δ (-ε) := by
  have h_log2_le :
      ∀ x : ℝ, 0 < x →
        Real.logb 2 x + 1 ≤
          (1 / Real.log 2) * (Real.log x + 1) := by
    intro x hx
    have hln2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [Real.logb]
    have h2 : 1 ≤ 1 / Real.log 2 := by
      apply one_le_one_div
      · exact hln2_pos
      · linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    calc
      Real.log x / Real.log 2 + 1
          ≤ Real.log x / Real.log 2 + 1 / Real.log 2 := by gcongr
      _ = (1 / Real.log 2) * (Real.log x + 1) := by ring
  have hA_pos : 0 < 4 * (1 / Real.log 2) := by positivity
  rcases localAssembly_log_absorption_general
      (4 * (1 / Real.log 2)) C ε hA_pos hC hε with
    ⟨δ₀, hδ₀_pos, hδ₀_le_one, h⟩
  refine ⟨δ₀, hδ₀_pos, hδ₀_le_one, ?_⟩
  intro δ hδ hδ₀
  have h1 :
      4 * (Real.logb 2 (C / δ) + 1) ≤
        4 * ((1 / Real.log 2) * (Real.log (C / δ) + 1)) := by
    gcongr
    exact h_log2_le (C / δ) (by positivity)
  have h2 :
      4 * ((1 / Real.log 2) * (Real.log (C / δ) + 1)) =
        (4 * (1 / Real.log 2)) * (Real.log (C / δ) + 1) := by
    ring
  rw [h2] at h1
  exact h1.trans (h δ hδ hδ₀)

theorem localAssembly_logb_absorption_general
    (A C ε : ℝ) (hA : 0 < A) (hC : 0 < C) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        A * (Real.logb 2 (C / δ) + 1) ≤ Real.rpow δ (-ε) := by
  have hln2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA' : 0 < A / Real.log 2 := div_pos hA hln2_pos
  rcases localAssembly_log_absorption_general
      (A / Real.log 2) C ε hA' hC hε with
    ⟨δ₀, hδ₀_pos, hδ₀_one, hδ₀⟩
  refine ⟨δ₀, hδ₀_pos, hδ₀_one, ?_⟩
  intro δ hδ hδ_bound
  have hln2_le_one : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hone_le_div : 1 ≤ 1 / Real.log 2 :=
    one_le_one_div hln2_pos hln2_le_one
  have hone_le_inv : 1 ≤ (Real.log 2)⁻¹ := by
    simpa only [one_div] using hone_le_div
  have hlog :
      Real.logb 2 (C / δ) + 1 ≤
        (Real.log (C / δ) + 1) / Real.log 2 := by
    rw [Real.logb]
    calc
      Real.log (C / δ) / Real.log 2 + 1
          ≤ Real.log (C / δ) / Real.log 2 + 1 / Real.log 2 := by
        exact add_le_add le_rfl hone_le_div
      _ = (Real.log (C / δ) + 1) / Real.log 2 := by ring
  calc
    A * (Real.logb 2 (C / δ) + 1)
        ≤ A * ((Real.log (C / δ) + 1) / Real.log 2) :=
      mul_le_mul_of_nonneg_left hlog hA.le
    _ = (A / Real.log 2) * (Real.log (C / δ) + 1) := by ring
    _ ≤ Real.rpow δ (-ε) := hδ₀ δ hδ hδ_bound

end Kakeya.Cinematic
