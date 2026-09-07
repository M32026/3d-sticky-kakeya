module

/-
  Exponent absorption lemma for Section 9 Step 5.

  Takes the combining lower bound expansion, the M lower bound, and abstract
  product/log factor bounds, and absorbs all loss exponents to produce the
  final δ^{-(2s+ε_final+ρ_T)} lower bound on combiningLowerBound.

  The good product gain is an explicit parameter `good_gain` (to be instantiated
  as `ε_G * η / 8` per OS equation (90)), NOT `η`.

  Budget: `good_gain ≥ (1+C')*lam + ρ_M + ρ_T + ε_N + ε_bad + ε_log_loss + ε_final`.

  Whiteprint node: section9 / exponent_absorption
  Status: DRAFT — abstract algebra proved; source instantiation pending
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem

/-- Absorb all loss exponents into the final bound.

    Given lower bounds on the good product, bad product, and log factor,
    plus a budget inequality, conclude:
    `combiningLowerBound ≥ δ^{-(2*s+ε_final+ρ_T)}`.

    The `good_gain` parameter is the actual δ-exponent gain from the good product
    (per OS equation (90), `good_gain = ε_G * η / 8`). It is NOT `η`.

    Budget: `good_gain ≥ (1+C')*lam + ρ_M + ρ_T + ε_N + ε_bad + ε_log_loss + ε_final`.
-/
lemma exponent_absorption
    (δ s : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (M : ℕ) (hM_pos : 0 < M)
    (C C' lam ε_N η : ℝ)
    (good_gain : ℝ)
    (n : ℕ) (Δ : Fin (n + 1) → ℝ) (scaleClass : Fin n → ScaleClass)
    (ρ_M ρ_T ε_final ε_bad ε_log_loss : ℝ)
    -- M lower bound
    (hM : (M : ℝ) ≥ δ ^ (-s + lam + ρ_M))
    -- Good product gain: ∏_{good} ratio^η ≥ δ^{-good_gain}
    (h_good : (∏ j ∈ Finset.univ.filter (fun j => (scaleClass j).isGood),
                 (Δ j.castSucc / Δ (Fin.succ j)) ^ η) ≥
               δ ^ (-good_gain))
    -- Bad product loss: ∏_{bad} inverse_ratio ≥ δ^{ε_bad}
    (h_bad : (∏ j ∈ Finset.univ.filter (fun j => (scaleClass j).isBad),
                 Δ (Fin.succ j) / Δ j.castSucc) ≥ δ ^ ε_bad)
    -- Log factor loss: log(1/δ)^{-C} ≥ δ^{ε_log_loss}
    (h_log : (Real.log (1 / δ)) ^ (-C) ≥ δ ^ ε_log_loss)
    -- Budget: good_gain ≥ all losses + final target
    (h_budget : good_gain ≥ (1 + C') * lam + ρ_M + ρ_T + ε_N + ε_bad + ε_log_loss + ε_final)
    -- Positivity assumptions
    (hlam : 0 ≤ lam) (hεN : 0 ≤ ε_N) (hη : 0 ≤ η)
    (hρM : 0 ≤ ρ_M) (hρT : 0 ≤ ρ_T) (hεfinal : 0 ≤ ε_final)
    (hεbad : 0 ≤ ε_bad) (hεlog : 0 ≤ ε_log_loss)
    (hC' : 0 ≤ C') (hC : 0 ≤ C) (hgg : 0 ≤ good_gain)
    (hΔ_pos : ∀ i, 0 < Δ i) :
    combiningLowerBound δ (M : ℝ) C C' lam s ε_N η n Δ scaleClass ≥
      δ ^ (-(2 * s + ε_final + ρ_T)) := by
  let G := Finset.univ.filter (fun j : Fin n => (scaleClass j).isGood)
  let B := Finset.univ.filter (fun j : Fin n => (scaleClass j).isBad)
  set a : ℝ := δ ^ ε_log_loss with ha_def
  set b : ℝ := δ ^ (-s + lam + ρ_M) with hb_def
  set c : ℝ := δ ^ (C' * lam) with hc_def
  set d : ℝ := δ ^ (-s + ε_N) with hd_def
  set e : ℝ := δ ^ (-good_gain) with he_def
  set f : ℝ := δ ^ ε_bad with hf_def
  set GP : ℝ := (∏ j ∈ G, (Δ j.castSucc / Δ (Fin.succ j)) ^ η) with hGP_def
  set BP : ℝ := (∏ j ∈ B, Δ (Fin.succ j) / Δ j.castSucc) with hBP_def
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hc : 0 ≤ c := by positivity
  have hd : 0 ≤ d := by positivity
  have he : 0 ≤ e := by positivity
  have hf : 0 ≤ f := by positivity
  have hGP_nonneg : 0 ≤ GP := by
    dsimp only [GP]; apply Finset.prod_nonneg; intro j _
    have h2 : 0 ≤ Δ j.castSucc / Δ (Fin.succ j) := by
      apply div_nonneg <;> exact (hΔ_pos _).le
    exact Real.rpow_nonneg h2 _
  have hBP_nonneg : 0 ≤ BP := by
    dsimp only [BP]; apply Finset.prod_nonneg; intro j _
    exact div_nonneg (hΔ_pos _).le (hΔ_pos _).le
  have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
  set LHS : ℝ := (Real.log (1 / δ)) ^ (-C) * (M : ℝ) * c * d * GP * BP with hLHS_def
  set RHS : ℝ := a * b * c * d * e * f with hRHS_def
  have h1 : LHS ≥ a * (M : ℝ) * c * d * GP * BP := by
    simp only [hLHS_def]
    have h : (Real.log (1 / δ)) ^ (-C) ≥ a := h_log
    have h_rest : 0 ≤ (M : ℝ) * c * d * GP * BP := by positivity
    nlinarith
  have h2 : a * (M : ℝ) * c * d * GP * BP ≥ a * (M : ℝ) * c * d * e * BP := by
    have h : GP ≥ e := h_good
    have h_rest : 0 ≤ a * (M : ℝ) * c * d * BP := by positivity
    nlinarith
  have h3 : a * (M : ℝ) * c * d * e * BP ≥ a * (M : ℝ) * c * d * e * f := by
    have h : BP ≥ f := h_bad
    have h_rest : 0 ≤ a * (M : ℝ) * c * d * e := by positivity
    nlinarith
  have h4 : a * (M : ℝ) * c * d * e * f ≥ a * b * c * d * e * f := by
    have h : (M : ℝ) ≥ b := hM
    have h_rest : 0 ≤ a * c * d * e * f := by positivity
    nlinarith
  have h_step : LHS ≥ RHS := by
    calc LHS
      ≥ a * (M : ℝ) * c * d * GP * BP := h1
    _ ≥ a * (M : ℝ) * c * d * e * BP := h2
    _ ≥ a * (M : ℝ) * c * d * e * f := h3
    _ ≥ a * b * c * d * e * f := h4
    _ = RHS := by simp only [hRHS_def]
  have h_main_exp : RHS = δ ^ (-2 * s + ((1 + C') * lam + ρ_M + ε_N - good_gain + ε_bad + ε_log_loss)) := by
    simp only [hRHS_def, ha_def, hb_def, hc_def, hd_def, he_def, hf_def]
    rw [←Real.rpow_add hδ_pos, ←Real.rpow_add hδ_pos, ←Real.rpow_add hδ_pos,
        ←Real.rpow_add hδ_pos, ←Real.rpow_add hδ_pos]
    <;> ring_nf
  have h_final_exp : -2 * s + ((1 + C') * lam + ρ_M + ε_N - good_gain + ε_bad + ε_log_loss) ≤
      -(2 * s + ε_final + ρ_T) := by linarith
  have h_rpow : δ ^ (-2 * s + ((1 + C') * lam + ρ_M + ε_N - good_gain + ε_bad + ε_log_loss)) ≥
           δ ^ (-(2 * s + ε_final + ρ_T)) := by
    exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h_final_exp
  have h4' : combiningLowerBound δ (M : ℝ) C C' lam s ε_N η n Δ scaleClass = LHS := by rfl
  rw [h4']
  calc LHS
    ≥ RHS := h_step
  _ = δ ^ (-2 * s + ((1 + C') * lam + ρ_M + ε_N - good_gain + ε_bad + ε_log_loss)) := h_main_exp
  _ ≥ δ ^ (-(2 * s + ε_final + ρ_T)) := h_rpow

end DirecretisedFurstenbergEstimate.Section9
