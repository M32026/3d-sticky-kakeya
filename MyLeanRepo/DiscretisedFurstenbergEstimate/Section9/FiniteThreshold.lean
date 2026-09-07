module

/-
  Finite-range threshold helper for Section 9.

  Takes the bounded combining induction (CombiningInductionUniform_with_data_bounded)
  and produces uniform `lam`, `lam_0_uniform`, and `δ₀_uniform` valid for all
  `1 ≤ n ≤ n_max`.

  This is the operator defect #6 fix (OS line 1307): λ and all Prop 7.3
  thresholds must be uniform over `1 ≤ n ≤ n0(τ)`, chosen BEFORE introducing
  the arbitrary source scale. A dummy n=1 or after-the-fact δ₀_comb is NOT
  sufficient.

  Uses two-stage finite minimum:
  1. For each n, H_main gives lam_0(n). Finite min → lam_0_uniform.
  2. Choose lam ≤ lam_0_uniform.
  3. For each n with this lam, get δ₀(n). Finite min → δ₀_uniform.

  Whiteprint node: section9 / finite_threshold
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Contracts.Prop73
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.FormatConversion.M2
open DiscretisedFurstenbergEstimate.CombiningTheoremRework
open DiscretisedFurstenbergEstimate.CombiningTheorem

/-- Finite-minimum threshold with budget cap and ε_input selection.

    Given H_main (the inner function after extracting ε_G0, η0 from
    CombiningInductionUniform_with_data_bounded), produce uniform
    `lam`, `lam_0_uniform`, `δ₀_uniform`, and `ε_input` valid for all
    `1 ≤ n ≤ n_max`.

    Budget: `lam = min(lam_0_uniform/2, budget/(1+C'_max))` so that
    `(1+C'_max)*lam ≤ budget`.
    ε_input: `ε_input = lam/2`, so `0 < ε_input < lam`.

    C_P is fixed as an input (Section 9 uses C_P=1), so δ₀ is uniform
    over n only for this specific C_P. -/
lemma finite_minimum_threshold
    {s t ε_inc K ε_G0 η0 : ℝ} {n_max : ℕ} (hn_max_pos : 0 < n_max)
    (H_main : ∀ (τ : ℝ), 0 < τ → τ < 1 → ∀ (n : ℕ), 0 < n →
      ∃ (lam_0 : ℝ), 0 < lam_0 ∧
        ∀ (C_P : ℝ), 1 ≤ C_P →
          0 < combiningC τ K n C_P ∧
          ∀ (ε_N lam : ℝ), 0 < ε_N → 0 < lam → lam ≤ lam_0 →
            ∀ (h_uniform : UniformIncidenceData s t ε_inc),
              ∃ (δ₀ : ℝ), 0 < δ₀ ∧
              ∀ (ε_G η : ℝ), 0 < ε_G → ε_G ≤ ε_G0 → ε_N ≤ ε_G →
                0 < η → η ≤ η0 →
                  ∀ (k : ℕ), DiscretisedFurstenbergEstimate.dyadicDelta k ≤ δ₀ →
                    ∀ (M : ℕ)
                      (config : DiscretisedFurstenbergEstimate.CombiningTheorem.CTNiceConfiguration k s (Real.rpow (DiscretisedFurstenbergEstimate.dyadicDelta k) (-lam)) M)
                      (Δ : Fin (n + 1) → ℝ)
                      (scaleClass : Fin n → ScaleClass)
                      (N : Fin n → ℕ)
                      (C_between : Fin n → ℝ),
                      CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N →
                      B1BridgeHypotheses k config →
                      CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P ε_inc n lam k M config Δ scaleClass →
                      CombiningConclusion s t τ ε_G η ε_N C_P
                        (combiningC τ K n C_P) (combiningCprime n τ) lam n Δ scaleClass k M config)
    (τ : ℝ) (hτ_pos : 0 < τ) (hτ_lt_one : τ < 1)
    (C_P : ℝ) (hCP : 1 ≤ C_P)
    (ε_N : ℝ) (hεN_pos : 0 < ε_N)
    (h_uniform : UniformIncidenceData s t ε_inc)
    (budget : ℝ) (hbudget_pos : 0 < budget)
    (C'_max : ℝ) (hC'max_nonneg : 0 ≤ C'_max) :
    ∃ (lam lam_0_uniform δ₀_uniform ε_input : ℝ),
      0 < lam ∧ 0 < lam_0_uniform ∧ 0 < δ₀_uniform ∧ lam ≤ lam_0_uniform ∧
      (1 + C'_max) * lam ≤ budget ∧
      0 < ε_input ∧ ε_input < lam ∧
      ∀ (n : ℕ), 0 < n → n ≤ n_max →
        0 < combiningC τ K n C_P ∧
        ∀ (ε_G η : ℝ), 0 < ε_G → ε_G ≤ ε_G0 → ε_N ≤ ε_G →
          0 < η → η ≤ η0 →
            ∀ (k : ℕ), DiscretisedFurstenbergEstimate.dyadicDelta k ≤ δ₀_uniform →
              ∀ (M : ℕ)
                (config : DiscretisedFurstenbergEstimate.CombiningTheorem.CTNiceConfiguration k s (Real.rpow (DiscretisedFurstenbergEstimate.dyadicDelta k) (-lam)) M)
                (Δ : Fin (n + 1) → ℝ)
                (scaleClass : Fin n → ScaleClass)
                (N : Fin n → ℕ)
                (C_between : Fin n → ℝ),
                CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N →
                B1BridgeHypotheses k config →
                CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P ε_inc n lam k M config Δ scaleClass →
                CombiningConclusion s t τ ε_G η ε_N C_P
                  (combiningC τ K n C_P) (combiningCprime n τ) lam n Δ scaleClass k M config := by
  let S_n : Finset ℕ := Finset.Icc 1 n_max
  have h1_in_S : 1 ∈ S_n := by
    simp [S_n] <;> omega
  have hS_n_nonempty : S_n.Nonempty := ⟨1, h1_in_S⟩

  classical

  -- Stage 1: For each n, get lam_0 from H_main, then take finite minimum.
  let lam_0_total : ℕ → ℝ := fun n =>
    if h : n ∈ S_n then
      Classical.choose (H_main τ hτ_pos hτ_lt_one n
        (by simp only [S_n, Finset.mem_Icc] at h <;> omega))
    else 0

  have hlam0_total_spec : ∀ n ∈ S_n,
      0 < lam_0_total n ∧
      ∀ (C_P' : ℝ), 1 ≤ C_P' →
        0 < combiningC τ K n C_P' ∧
        ∀ (ε_N' lam' : ℝ), 0 < ε_N' → 0 < lam' → lam' ≤ lam_0_total n →
          ∀ (h_uniform' : UniformIncidenceData s t ε_inc),
            ∃ (δ₀ : ℝ), 0 < δ₀ ∧
            ∀ (ε_G' η' : ℝ), 0 < ε_G' → ε_G' ≤ ε_G0 → ε_N' ≤ ε_G' →
              0 < η' → η' ≤ η0 →
                ∀ (k : ℕ), DiscretisedFurstenbergEstimate.dyadicDelta k ≤ δ₀ →
                  ∀ (M : ℕ)
                    (config : DiscretisedFurstenbergEstimate.CombiningTheorem.CTNiceConfiguration k s (Real.rpow (DiscretisedFurstenbergEstimate.dyadicDelta k) (-lam')) M)
                    (Δ : Fin (n + 1) → ℝ)
                    (scaleClass : Fin n → ScaleClass)
                    (N : Fin n → ℕ)
                    (C_between : Fin n → ℝ),
                    CombiningConfig s t τ n ε_G' η' lam' ε_N' C_P' C_between k M config Δ scaleClass N →
                    B1BridgeHypotheses k config →
                    CombiningExtraHypotheses_v2 s t ε_G' η' ε_N' C_P' ε_inc n lam' k M config Δ scaleClass →
                    CombiningConclusion s t τ ε_G' η' ε_N' C_P'
                      (combiningC τ K n C_P') (combiningCprime n τ) lam' n Δ scaleClass k M config := by
    intro n hn
    have hn_pos : 0 < n := by
      simp only [S_n, Finset.mem_Icc] at hn <;> omega
    have h_eq : lam_0_total n = Classical.choose (H_main τ hτ_pos hτ_lt_one n hn_pos) := by
      simp [lam_0_total, hn] <;> rfl
    rw [h_eq]
    exact Classical.choose_spec (H_main τ hτ_pos hτ_lt_one n hn_pos)

  let S_lam : Finset ℝ := Finset.image lam_0_total S_n
  have hS_lam_nonempty : S_lam.Nonempty :=
    ⟨lam_0_total 1, Finset.mem_image.mpr ⟨1, h1_in_S, rfl⟩⟩
  let lam_0_uniform : ℝ := S_lam.min' hS_lam_nonempty
  have hlam_0_uniform_pos : 0 < lam_0_uniform := by
    have h : lam_0_uniform ∈ S_lam := Finset.min'_mem S_lam hS_lam_nonempty
    rcases Finset.mem_image.mp h with ⟨n, hn, h_eq⟩
    have h9 : lam_0_total n = lam_0_uniform := h_eq
    rw [←h9]
    exact (hlam0_total_spec n hn).1
  have hlam_0_uniform_le : ∀ n ∈ S_n, lam_0_uniform ≤ lam_0_total n := by
    intro n hn
    have h : lam_0_total n ∈ S_lam := Finset.mem_image.mpr ⟨n, hn, rfl⟩
    exact Finset.min'_le S_lam (lam_0_total n) h

  let budget_cap : ℝ := budget / (1 + C'_max)
  have h1_pos : 0 < 1 + C'_max := by linarith
  have hbudget_cap_pos : 0 < budget_cap := by positivity

  let lam : ℝ := min (lam_0_uniform / 2) budget_cap
  have hlam_pos : 0 < lam := by positivity
  have hlam_le : lam ≤ lam_0_uniform := by
    have h : lam ≤ lam_0_uniform / 2 := min_le_left _ _
    linarith [hlam_0_uniform_pos]
  have hlam_le_cap : lam ≤ budget_cap := min_le_right _ _
  have hbudget : (1 + C'_max) * lam ≤ budget := by
    calc (1 + C'_max) * lam ≤ (1 + C'_max) * budget_cap := by gcongr
      _ = budget := by
        dsimp only [budget_cap]
        field_simp [h1_pos.ne'] <;> ring

  let ε_input : ℝ := lam / 2
  have hε_input_pos : 0 < ε_input := by positivity
  have hε_input_lt : ε_input < lam := by
    dsimp only [ε_input]
    linarith [hlam_pos]

  -- Stage 2: For each n, with uniform lam, get δ₀, then take finite minimum.
  let δ₀_total : ℕ → ℝ := fun n =>
    if h : n ∈ S_n then
      let h_body := (hlam0_total_spec n h).2 C_P hCP
      Classical.choose (h_body.2 ε_N lam hεN_pos hlam_pos
        (le_trans hlam_le (hlam_0_uniform_le n h)) h_uniform)
    else 0

  have hδ₀_total_spec : ∀ n ∈ S_n,
      0 < δ₀_total n ∧
      ∀ (ε_G η : ℝ), 0 < ε_G → ε_G ≤ ε_G0 → ε_N ≤ ε_G →
        0 < η → η ≤ η0 →
          ∀ (k : ℕ), DiscretisedFurstenbergEstimate.dyadicDelta k ≤ δ₀_total n →
            ∀ (M : ℕ)
              (config : DiscretisedFurstenbergEstimate.CombiningTheorem.CTNiceConfiguration k s (Real.rpow (DiscretisedFurstenbergEstimate.dyadicDelta k) (-lam)) M)
              (Δ : Fin (n + 1) → ℝ)
              (scaleClass : Fin n → ScaleClass)
              (N : Fin n → ℕ)
              (C_between : Fin n → ℝ),
              CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N →
              B1BridgeHypotheses k config →
              CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P ε_inc n lam k M config Δ scaleClass →
              CombiningConclusion s t τ ε_G η ε_N C_P
                (combiningC τ K n C_P) (combiningCprime n τ) lam n Δ scaleClass k M config := by
    intro n hn
    have hn_pos : 0 < n := by
      simp only [S_n, Finset.mem_Icc] at hn <;> omega
    have hlam_le_fn : lam ≤ lam_0_total n :=
      le_trans hlam_le (hlam_0_uniform_le n hn)
    let h_body := (hlam0_total_spec n hn).2 C_P hCP
    have h_eq : δ₀_total n = Classical.choose (h_body.2 ε_N lam hεN_pos hlam_pos hlam_le_fn h_uniform) := by
      simp [δ₀_total, hn] <;> rfl
    rw [h_eq]
    exact Classical.choose_spec (h_body.2 ε_N lam hεN_pos hlam_pos hlam_le_fn h_uniform)

  let S_delta : Finset ℝ := Finset.image δ₀_total S_n
  have hS_delta_nonempty : S_delta.Nonempty :=
    ⟨δ₀_total 1, Finset.mem_image.mpr ⟨1, h1_in_S, rfl⟩⟩
  let δ₀_uniform : ℝ := S_delta.min' hS_delta_nonempty
  have hδ₀_uniform_pos : 0 < δ₀_uniform := by
    have h : δ₀_uniform ∈ S_delta := Finset.min'_mem S_delta hS_delta_nonempty
    rcases Finset.mem_image.mp h with ⟨n, hn, h_eq⟩
    have h9 : δ₀_total n = δ₀_uniform := h_eq
    rw [←h9]
    exact (hδ₀_total_spec n hn).1
  have hδ₀_uniform_le : ∀ n ∈ S_n, δ₀_uniform ≤ δ₀_total n := by
    intro n hn
    have h : δ₀_total n ∈ S_delta := Finset.mem_image.mpr ⟨n, hn, rfl⟩
    exact Finset.min'_le S_delta (δ₀_total n) h

  refine' ⟨lam, lam_0_uniform, δ₀_uniform, ε_input, hlam_pos, hlam_0_uniform_pos, hδ₀_uniform_pos, hlam_le, hbudget, hε_input_pos, hε_input_lt, _⟩
  intro n hn_pos hn_le
  have hn_in_S : n ∈ S_n := by
    simp only [S_n, Finset.mem_Icc] <;> omega
  have hC_pos : 0 < combiningC τ K n C_P :=
    (hlam0_total_spec n hn_in_S).2 C_P hCP |>.1
  have hδ₀_le : δ₀_uniform ≤ δ₀_total n := hδ₀_uniform_le n hn_in_S
  exact ⟨hC_pos, fun ε_G η hεG hεG_le hεN_le hη hη_le k hk =>
    (hδ₀_total_spec n hn_in_S).2 ε_G η hεG hεG_le hεN_le hη hη_le k
      (le_trans hk hδ₀_le)⟩

end DirecretisedFurstenbergEstimate.Section9
