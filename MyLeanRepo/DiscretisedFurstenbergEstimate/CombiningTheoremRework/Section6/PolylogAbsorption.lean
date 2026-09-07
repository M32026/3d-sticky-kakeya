module

/-
  Polylog scale absorption lemma.

  For any a > 0, K > 0, C > 0, and m : ℕ, there exists δ₀ > 0 such that
  for all 0 < δ ≤ δ₀:
    δ^a ≤ C * (log(1/δ) - m * log 2)^(-K)
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section6

/-- Core polylog absorption: δ^a * |log δ|^K → 0 as δ → 0+. -/
lemma polylog_absorption_core (a K C : ℝ) (ha : 0 < a) (hK : 0 < K) (hC : 0 < C) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → δ ^ a * |Real.log δ| ^ K ≤ C := by
  have h_neg_a : (-a : ℝ) < 0 := by linarith
  have h_littleO : (fun x : ℝ => |Real.log x| ^ K) =o[nhdsWithin 0 (Set.Ioi 0)] (fun x : ℝ => x ^ (-a)) :=
    isLittleO_abs_log_rpow_rpow_nhdsGT_zero K h_neg_a
  have h_eventually_norm : ∀ᶠ (x : ℝ) in nhdsWithin 0 (Set.Ioi 0), ‖|Real.log x| ^ K‖ ≤ C * ‖x ^ (-a)‖ :=
    h_littleO.def hC
  have h_pos : ∀ᶠ (x : ℝ) in nhdsWithin 0 (Set.Ioi 0), 0 < x := by
    have h : Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi (0 : ℝ)) := self_mem_nhdsWithin
    filter_upwards [h] with x hx
    exact hx
  have h_main : ∀ᶠ (x : ℝ) in nhdsWithin 0 (Set.Ioi 0), |Real.log x| ^ K * x ^ a ≤ C := by
    filter_upwards [h_eventually_norm, h_pos] with x hx_norm hx_pos
    have h1 : ‖|Real.log x| ^ K‖ = |Real.log x| ^ K := by
      have h2 : 0 ≤ |Real.log x| ^ K := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h2]
    have h3 : ‖x ^ (-a)‖ = x ^ (-a) := by
      have h4 : 0 ≤ x ^ (-a) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h4]
    rw [h1, h3] at hx_norm
    have h5 : |Real.log x| ^ K ≤ C * x ^ (-a) := hx_norm
    have h6 : 0 < x ^ a := by positivity
    have h7 : x ^ (-a) * x ^ a = 1 := by
      have h8 : x ^ (-a) * x ^ a = x ^ ((-a) + a) := by
        rw [←Real.rpow_add (by linarith)] <;> ring
      rw [h8]
      have h9 : (-a) + a = 0 := by ring
      rw [h9, Real.rpow_zero]
    have h8 : |Real.log x| ^ K * x ^ a ≤ C := by
      have h9 : |Real.log x| ^ K * x ^ a ≤ (C * x ^ (-a)) * x ^ a :=
        mul_le_mul_of_nonneg_right h5 (by positivity)
      have h10 : (C * x ^ (-a)) * x ^ a = C := by
        calc (C * x ^ (-a)) * x ^ a
          = C * (x ^ (-a) * x ^ a) := by ring
        _ = C * 1 := by rw [h7]
        _ = C := by ring
      rw [h10] at h9
      exact h9
    exact h8
  have h_exists : ∃ (u : Set ℝ), u ∈ nhds (0 : ℝ) ∧ u ∩ Set.Ioi (0 : ℝ) ⊆ {x : ℝ | |Real.log x| ^ K * x ^ a ≤ C} := by
    exact mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h_main
  rcases h_exists with ⟨u, hu_nhds, hU⟩
  rcases Metric.mem_nhds_iff.mp hu_nhds with ⟨δ₁, hδ₁_pos, hball⟩
  let δ₀ : ℝ := δ₁ / 2
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_lt => ?_⟩
  have hδ_in_ball : δ ∈ Metric.ball (0 : ℝ) δ₁ := by
    have h : δ < δ₁ / 2 := hδ_lt
    have h' : |δ| < δ₁ := by
      rw [abs_of_pos hδ_pos]
      linarith
    simpa [Metric.mem_ball] using h'
  have hδ_in_u : δ ∈ u := hball hδ_in_ball
  have h_in_set : δ ∈ {x : ℝ | |Real.log x| ^ K * x ^ a ≤ C} := hU ⟨hδ_in_u, hδ_pos⟩
  have h_goal : |Real.log δ| ^ K * δ ^ a ≤ C := by simpa using h_in_set
  have h_final : δ ^ a * |Real.log δ| ^ K ≤ C := by
    rw [mul_comm]
    exact h_goal
  exact h_final

/-- Polylog scale absorption with m-shift. -/
lemma polylog_absorption (a K C : ℝ) (ha : 0 < a) (hK : 0 < K) (hC : 0 < C) (m : ℕ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      δ ^ a ≤ C * (Real.log (1 / δ) - (m : ℝ) * Real.log 2) ^ (-K) := by
  rcases polylog_absorption_core a K C ha hK hC with ⟨δ_core, hδ_core_pos, hcore⟩
  let δ_half : ℝ := δ_core / 2
  let δ_one : ℝ := 1 / 2
  let δ_m : ℝ := (2 : ℝ) ^ (-(m : ℝ)) / 2
  have hδ_half_pos : 0 < δ_half := by positivity
  have hδ_one_pos : 0 < δ_one := by norm_num
  have hδ_m_pos : 0 < δ_m := by positivity
  let δ₀ : ℝ := min δ_half (min δ_one δ_m)
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_le => ?_⟩
  have h1 : δ ≤ δ_half := by
    have h : δ ≤ δ₀ := hδ_le
    have h2 : δ₀ ≤ δ_half := min_le_left _ _
    linarith
  have h2 : δ ≤ δ_one := by
    have h : δ ≤ δ₀ := hδ_le
    have h2 : δ₀ ≤ min δ_one δ_m := min_le_right _ _
    have h3 : δ₀ ≤ δ_one := le_trans h2 (min_le_left _ _)
    linarith
  have h3 : δ ≤ δ_m := by
    have h : δ ≤ δ₀ := hδ_le
    have h2 : δ₀ ≤ min δ_one δ_m := min_le_right _ _
    have h3 : δ₀ ≤ δ_m := le_trans h2 (min_le_right _ _)
    linarith
  have hδ_lt_core : δ < δ_core := by
    dsimp only [δ_half] at h1
    linarith
  have hδ_lt_one : δ < 1 := by
    dsimp only [δ_one] at h2
    linarith
  have hδ_lt_2m : δ < (2 : ℝ) ^ (-(m : ℝ)) := by
    dsimp only [δ_m] at h3
    linarith
  have h_main1 : δ ^ a * |Real.log δ| ^ K ≤ C := hcore δ hδ_pos hδ_lt_core
  set L : ℝ := Real.log (1 / δ) with hL_def
  have hL_pos : 0 < L := by
    have h4 : 1 < 1 / δ := by
      apply one_lt_one_div
      <;> linarith
    exact Real.log_pos h4
  have h_abs : |Real.log δ| = L := by
    have h5 : Real.log δ < 0 := Real.log_neg hδ_pos (by linarith)
    have h6 : Real.log (1 / δ) = -Real.log δ := by
      rw [Real.log_div (by norm_num) (ne_of_gt hδ_pos), Real.log_one] <;> ring
    have h7 : -Real.log δ = L := by
      exact h6.symm
    rw [abs_of_neg h5, h7]
  rw [h_abs] at h_main1
  have h4 : δ ^ a * L ^ K ≤ C := h_main1
  have h5 : 0 < L ^ K := by positivity
  have h6 : δ ^ a ≤ C * L ^ (-K) := by
    have h7 : δ ^ a ≤ C / L ^ K := by
      calc δ ^ a
        = (δ ^ a * L ^ K) / L ^ K := by field_simp [h5.ne'] <;> ring
      _ ≤ C / L ^ K := by gcongr
    have h8 : C / L ^ K = C * L ^ (-K) := by
      rw [Real.rpow_neg (by linarith)] <;> field_simp
    rw [h8] at h7
    exact h7
  have h9 : 0 < L - (m : ℝ) * Real.log 2 := by
    have h10 : 1 / δ > (2 : ℝ) ^ (m : ℝ) := by
      have h11 : δ < (2 : ℝ) ^ (-(m : ℝ)) := hδ_lt_2m
      have h12 : (2 : ℝ) ^ (-(m : ℝ)) = 1 / (2 : ℝ) ^ (m : ℝ) := by
        rw [Real.rpow_neg (by positivity)] <;> field_simp
      rw [h12] at h11
      have h13 : 0 < (2 : ℝ) ^ (m : ℝ) := by positivity
      have h14 : 1 / δ > 1 / ((2 : ℝ) ^ (-(m : ℝ))) := by gcongr
      rw [h12] at h14
      simpa using h14
    have h15 : Real.log (1 / δ) > Real.log ((2 : ℝ) ^ (m : ℝ)) := Real.log_lt_log (by positivity) h10
    have h16 : Real.log ((2 : ℝ) ^ (m : ℝ)) = (m : ℝ) * Real.log 2 := by
      rw [Real.log_rpow (by positivity)] <;> ring
    rw [h16] at h15
    linarith
  set Lm : ℝ := L - (m : ℝ) * Real.log 2 with hLm_def
  have hLm_pos : 0 < Lm := h9
  have h10 : Lm ≤ L := by
    have h11 : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
    have h12 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h13 : 0 ≤ (m : ℝ) * Real.log 2 := by positivity
    simp [hLm_def] <;> linarith
  have h11 : L ^ (-K) ≤ Lm ^ (-K) := by
    have h12 : Lm ^ K ≤ L ^ K := Real.rpow_le_rpow (by linarith) h10 (by linarith)
    have h13 : 0 < Lm ^ K := by positivity
    have h14 : 0 < L ^ K := by positivity
    have h15 : 1 / L ^ K ≤ 1 / Lm ^ K := one_div_le_one_div_of_le h13 h12
    have h16 : L ^ (-K) = 1 / L ^ K := by
      rw [Real.rpow_neg (by linarith)] <;> field_simp
    have h17 : Lm ^ (-K) = 1 / Lm ^ K := by
      rw [Real.rpow_neg (by linarith)] <;> field_simp
    rw [h16, h17]
    exact h15
  calc δ ^ a
    ≤ C * L ^ (-K) := h6
  _ ≤ C * Lm ^ (-K) := by gcongr
  _ = C * (Real.log (1 / δ) - (m : ℝ) * Real.log 2) ^ (-K) := by
    simp [hLm_def, hL_def] <;> ring

end DirecretisedFurstenbergEstimate.Section6

end
