module

public import MyLeanRepo.InductionOnScales.CardinalityBound
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Cardinality Phase (OS 5.5)

Proves condition (5.5) using the three-estimate algebra from CardinalityBound.

## Interface

The extended interface includes the uniform incidence parameter `N_Δ` and the
three intermediate estimates:

- `N_Δ : ℝ`, `0 ≤ N_Δ` — uniform packet size (fine tubes per coarse tube)
- `TQ_local` — intermediate tube set for each coarse square Q
- `h_est1`: `|config.tubes| ≥ |coarseConfig.tubes| * N_Δ`
- `h_est2`: `|TQ_local Q| ≤ M_Δ * N_Δ`
- `h_est3`: `|TQ_local Q| ≥ |fineConfig(Q).tubes| * M / M_Q`

These are supplied by the coarse_phase (est1, est2) and fine_phase (est3)
constructions.

## Whiteprint node
`cardinality_phase` under `InductionOnScales/CardinalityPhase/`.
-/

attribute [local instance] Classical.propDecidable

open scoped BigOperators

namespace InductionOnScales

section CardinalityPhase

/-- Cardinality phase with extended interface including uniform incidence N_Δ.

Proves condition (5.5):
`K * |config.tubes| * M_Δ * M_Q ≥ |coarseConfig.tubes| * |fineConfig(Q).tubes| * M`

using the three-estimate algebra. -/
theorem cardinality_phase_with_NΔ
    {n m : ℕ} (hnm : m ≤ n)
    (s : ℝ) (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁)
    (M : ℕ) (hM : 0 < M)
    (config : NiceConfiguration n s C₁ M)
    (K : ℝ) (hK : 1 ≤ K)
    -- Phase A outputs:
    (P : Finset (DyadicSquare n))
    (hP_sub : P ⊆ config.points)
    (tubeFamily : (p : DyadicSquare n) → p ∈ P → Finset (DyadicTube n))
    (CΔ : ℝ) (MΔ : ℕ) (hMΔ : 0 < MΔ)
    (coarseConfig : NiceConfiguration m s CΔ MΔ)
    -- Phase B outputs:
    (CQ : DyadicSquare m → ℝ)
    (MQ : DyadicSquare m → ℕ)
    (hMQ : ∀ Q ∈ coarseConfig.points, 0 < MQ Q)
    (fineConfig : (Q : DyadicSquare m) → Q ∈ coarseConfig.points →
      NiceConfiguration (n - m) s (CQ Q) (MQ Q))
    -- Uniform incidence parameter:
    (N_Δ : ℝ) (hNΔ : 0 ≤ N_Δ)
    -- Intermediate tube set for each coarse square:
    (TQ_local : (Q : DyadicSquare m) → Q ∈ coarseConfig.points → Finset (DyadicTube n))
    -- Estimate 1 (form80): total fine tubes ≥ coarse tubes × N_Δ
    (h_est1 : (config.tubes.card : ℝ) ≥ (coarseConfig.tubes.card : ℝ) * N_Δ)
    -- Estimate 2 (form71): local tubes ≤ M_Δ × N_Δ
    (h_est2 : ∀ Q hQ, (TQ_local Q hQ).card ≤ (MΔ : ℝ) * N_Δ)
    -- Estimate 3 (form46): local tubes ≥ fine tubes × M / M_Q
    (h_est3 : ∀ Q hQ, (TQ_local Q hQ).card ≥
        ((fineConfig Q hQ).tubes.card : ℝ) * (M : ℝ) / (MQ Q : ℝ)) :
    ∀ Q, ∀ hQ : Q ∈ coarseConfig.points,
      K * (config.tubes.card : ℝ) * MΔ * MQ Q ≥
        (coarseConfig.tubes.card : ℝ) *
          ((fineConfig Q hQ).tubes.card : ℝ) * M := by
  intro Q hQ
  by_cases hTΔ_empty : coarseConfig.tubes = ∅
  · -- Case: no coarse tubes → RHS is 0, goal trivial
    rw [hTΔ_empty]
    <;> simp <;> positivity
  · -- Case: coarse tubes nonempty
    have hTΔ_nonempty : coarseConfig.tubes.Nonempty := by
      rwa [Finset.nonempty_iff_ne_empty]
    have hTΔ_pos : (0 : ℝ) < (coarseConfig.tubes.card : ℝ) := by
      exact_mod_cast hTΔ_nonempty.card_pos
    set T₀ : ℝ := K * (config.tubes.card : ℝ) with hT₀
    set T_Δ : ℝ := (coarseConfig.tubes.card : ℝ) with hT_Δ
    set T_Q : ℝ := ((fineConfig Q hQ).tubes.card : ℝ) with hT_Q
    set T_Q_local : ℝ := ((TQ_local Q hQ).card : ℝ) with hT_Q_local
    set M_Δ' : ℝ := (MΔ : ℝ) with hM_Δ'
    set M_Q' : ℝ := (MQ Q : ℝ) with hM_Q'
    set M' : ℝ := (M : ℝ) with hM'
    have h1 : T₀ ≥ T_Δ * N_Δ := by
      have hK1 : (1 : ℝ) ≤ K := hK
      have h : (config.tubes.card : ℝ) ≥ T_Δ * N_Δ := h_est1
      rw [hT₀]
      have h3 : K * (config.tubes.card : ℝ) ≥ (config.tubes.card : ℝ) := by
        have h4 : 0 ≤ (config.tubes.card : ℝ) := by positivity
        nlinarith
      linarith
    have h2 : T_Q_local ≤ M_Δ' * N_Δ := by
      rw [hT_Q_local, hM_Δ']
      exact h_est2 Q hQ
    have h3 : T_Q_local ≥ T_Q * M' / M_Q' := by
      rw [hT_Q_local, hT_Q, hM', hM_Q']
      exact h_est3 Q hQ
    have hMΔ'_pos : (0 : ℝ) < M_Δ' := by
      rw [hM_Δ']; exact_mod_cast hMΔ
    have hMQ'_pos : (0 : ℝ) < M_Q' := by
      rw [hM_Q']; exact_mod_cast hMQ Q hQ
    have hM'_pos : (0 : ℝ) < M' := by
      rw [hM']; exact_mod_cast hM
    have h_main : T₀ * M_Δ' * M_Q' ≥ T_Δ * T_Q * M' :=
      cardinality_bound_three_estimates T₀ T_Δ T_Q T_Q_local N_Δ M_Δ' M_Q' M'
        hNΔ hMΔ'_pos hMQ'_pos hM'_pos hTΔ_pos h1 h2 h3
    simpa [hT₀, hT_Δ, hT_Q, hM_Δ', hM_Q', hM'] using h_main

/-- Variant of `cardinality_phase_with_NΔ` accepting a weaker estimate 1.

Given `h_est1 : |config.tubes| ≥ |coarseConfig.tubes| * N_Δ / est1_factor`
and `K ≥ est1_factor`, proves condition (5.5).

This is needed when `construct_TQ_local_absorbed` introduces a factor of 2
in estimate 1; set `est1_factor = 2`. -/
theorem cardinality_phase_with_NΔ_K
    {n m : ℕ} (hnm : m ≤ n)
    (s : ℝ) (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁)
    (M : ℕ) (hM : 0 < M)
    (config : NiceConfiguration n s C₁ M)
    (K : ℝ) (hK : 1 ≤ K)
    (est1_factor : ℝ) (h_factor_pos : 0 < est1_factor)
    (hK_factor : est1_factor ≤ K)
    (P : Finset (DyadicSquare n))
    (hP_sub : P ⊆ config.points)
    (tubeFamily : (p : DyadicSquare n) → p ∈ P → Finset (DyadicTube n))
    (CΔ : ℝ) (MΔ : ℕ) (hMΔ : 0 < MΔ)
    (coarseConfig : NiceConfiguration m s CΔ MΔ)
    (CQ : DyadicSquare m → ℝ)
    (MQ : DyadicSquare m → ℕ)
    (hMQ : ∀ Q ∈ coarseConfig.points, 0 < MQ Q)
    (fineConfig : (Q : DyadicSquare m) → Q ∈ coarseConfig.points →
      NiceConfiguration (n - m) s (CQ Q) (MQ Q))
    (N_Δ : ℝ) (hNΔ : 0 ≤ N_Δ)
    (TQ_local : (Q : DyadicSquare m) → Q ∈ coarseConfig.points → Finset (DyadicTube n))
    -- Estimate 1 with factor: |config.tubes| ≥ |coarseConfig.tubes| * N_Δ / est1_factor
    (h_est1 : (config.tubes.card : ℝ) ≥ (coarseConfig.tubes.card : ℝ) * N_Δ / est1_factor)
    (h_est2 : ∀ Q hQ, (TQ_local Q hQ).card ≤ (MΔ : ℝ) * N_Δ)
    (h_est3 : ∀ Q hQ, (TQ_local Q hQ).card ≥
        ((fineConfig Q hQ).tubes.card : ℝ) * (M : ℝ) / (MQ Q : ℝ)) :
    ∀ Q, ∀ hQ : Q ∈ coarseConfig.points,
      K * (config.tubes.card : ℝ) * MΔ * MQ Q ≥
        (coarseConfig.tubes.card : ℝ) *
          ((fineConfig Q hQ).tubes.card : ℝ) * M := by
  intro Q hQ
  by_cases hTΔ_empty : coarseConfig.tubes = ∅
  · rw [hTΔ_empty] <;> simp <;> positivity
  · have hTΔ_nonempty : coarseConfig.tubes.Nonempty := by
      rwa [Finset.nonempty_iff_ne_empty]
    have hTΔ_pos : (0 : ℝ) < (coarseConfig.tubes.card : ℝ) := by
      exact_mod_cast hTΔ_nonempty.card_pos
    set T₀ : ℝ := K * (config.tubes.card : ℝ) with hT₀
    set T_Δ : ℝ := (coarseConfig.tubes.card : ℝ) with hT_Δ
    set T_Q : ℝ := ((fineConfig Q hQ).tubes.card : ℝ) with hT_Q
    set T_Q_local : ℝ := ((TQ_local Q hQ).card : ℝ) with hT_Q_local
    set M_Δ' : ℝ := (MΔ : ℝ) with hM_Δ'
    set M_Q' : ℝ := (MQ Q : ℝ) with hM_Q'
    set M' : ℝ := (M : ℝ) with hM'
    have h1 : T₀ ≥ T_Δ * N_Δ := by
      rw [hT₀]
      have h2 : K * (config.tubes.card : ℝ) ≥ K * (T_Δ * N_Δ / est1_factor) := by
        gcongr <;> linarith
      have h3 : K * (T_Δ * N_Δ / est1_factor) ≥ T_Δ * N_Δ := by
        have h4 : 0 ≤ T_Δ * N_Δ := by positivity
        have h5 : K / est1_factor ≥ 1 := by
          have h51 : est1_factor ≤ K := hK_factor
          have h52 : 0 < est1_factor := h_factor_pos
          exact (one_le_div h52).mpr h51
        have h6 : K * (T_Δ * N_Δ / est1_factor) = (K / est1_factor) * (T_Δ * N_Δ) := by ring
        rw [h6]
        have h7 : (K / est1_factor) * (T_Δ * N_Δ) ≥ T_Δ * N_Δ := by
          have h71 : (K / est1_factor) * (T_Δ * N_Δ) ≥ 1 * (T_Δ * N_Δ) := by gcongr
          simpa using h71
        exact h7
      linarith
    have h2 : T_Q_local ≤ M_Δ' * N_Δ := by
      rw [hT_Q_local, hM_Δ']
      exact h_est2 Q hQ
    have h3 : T_Q_local ≥ T_Q * M' / M_Q' := by
      rw [hT_Q_local, hT_Q, hM', hM_Q']
      exact h_est3 Q hQ
    have hMΔ'_pos : (0 : ℝ) < M_Δ' := by
      dsimp only [M_Δ'] <;> exact_mod_cast hMΔ
    have hMQ'_pos : (0 : ℝ) < M_Q' := by
      dsimp only [M_Q'] <;> exact_mod_cast hMQ Q hQ
    have hM'_pos : (0 : ℝ) < M' := by
      dsimp only [M'] <;> exact_mod_cast hM
    have h_main : T₀ * M_Δ' * M_Q' ≥ T_Δ * T_Q * M' :=
      cardinality_bound_three_estimates T₀ T_Δ T_Q T_Q_local N_Δ M_Δ' M_Q' M'
        hNΔ hMΔ'_pos hMQ'_pos hM'_pos hTΔ_pos h1 h2 h3
    simpa [hT₀, hT_Δ, hT_Q, hM_Δ', hM_Q', hM'] using h_main

/-- Fully generalized cardinality phase with factors in both est1 and est3.

Given:
- `h_est1`: |config.tubes| ≥ |coarseConfig.tubes| * N_Δ / est1_factor
- `h_est3`: |TQ_local| ≥ |fineConfig.tubes| * M / (MQ * est3_factor)
- `K ≥ est1_factor * est3_factor`

Proves condition (5.5). Use this when both estimates have losses. -/
theorem cardinality_phase_with_both_factors
    {n m : ℕ} (hnm : m ≤ n)
    (s : ℝ) (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁)
    (M : ℕ) (hM : 0 < M)
    (config : NiceConfiguration n s C₁ M)
    (K : ℝ) (hK : 1 ≤ K)
    (est1_factor : ℝ) (h1_pos : 0 < est1_factor)
    (est3_factor : ℝ) (h3_pos : 0 < est3_factor)
    (hK_factors : est1_factor * est3_factor ≤ K)
    (P : Finset (DyadicSquare n))
    (hP_sub : P ⊆ config.points)
    (tubeFamily : (p : DyadicSquare n) → p ∈ P → Finset (DyadicTube n))
    (CΔ : ℝ) (MΔ : ℕ) (hMΔ : 0 < MΔ)
    (coarseConfig : NiceConfiguration m s CΔ MΔ)
    (CQ : DyadicSquare m → ℝ)
    (MQ : DyadicSquare m → ℕ)
    (hMQ : ∀ Q ∈ coarseConfig.points, 0 < MQ Q)
    (fineConfig : (Q : DyadicSquare m) → Q ∈ coarseConfig.points →
      NiceConfiguration (n - m) s (CQ Q) (MQ Q))
    (N_Δ : ℝ) (hNΔ : 0 ≤ N_Δ)
    (TQ_local : (Q : DyadicSquare m) → Q ∈ coarseConfig.points → Finset (DyadicTube n))
    (h_est1 : (config.tubes.card : ℝ) ≥ (coarseConfig.tubes.card : ℝ) * N_Δ / est1_factor)
    (h_est2 : ∀ Q hQ, (TQ_local Q hQ).card ≤ (MΔ : ℝ) * N_Δ)
    (h_est3 : ∀ Q hQ, (TQ_local Q hQ).card ≥
        ((fineConfig Q hQ).tubes.card : ℝ) * (M : ℝ) / ((MQ Q : ℝ) * est3_factor)) :
    ∀ Q, ∀ hQ : Q ∈ coarseConfig.points,
      K * (config.tubes.card : ℝ) * MΔ * MQ Q ≥
        (coarseConfig.tubes.card : ℝ) *
          ((fineConfig Q hQ).tubes.card : ℝ) * M := by
  intro Q hQ
  by_cases hTΔ_empty : coarseConfig.tubes = ∅
  · rw [hTΔ_empty] <;> simp <;> positivity
  · have hTΔ_nonempty : coarseConfig.tubes.Nonempty := by
      rwa [Finset.nonempty_iff_ne_empty]
    have hTΔ_pos : (0 : ℝ) < (coarseConfig.tubes.card : ℝ) := by
      exact_mod_cast hTΔ_nonempty.card_pos
    set T₀ : ℝ := K * (config.tubes.card : ℝ) with hT₀
    set T_Δ : ℝ := (coarseConfig.tubes.card : ℝ) with hT_Δ
    set T_Q : ℝ := ((fineConfig Q hQ).tubes.card : ℝ) with hT_Q
    set T_Q_local : ℝ := ((TQ_local Q hQ).card : ℝ) with hT_Q_local
    set M_Δ' : ℝ := (MΔ : ℝ) with hM_Δ'
    set M_Q' : ℝ := (MQ Q : ℝ) with hM_Q'
    set M' : ℝ := (M : ℝ) with hM'
    -- T₀ ≥ T_Δ * N_Δ * est3_factor (absorb both factors)
    have h1 : T₀ ≥ T_Δ * N_Δ * est3_factor := by
      rw [hT₀]
      have h2 : K * (config.tubes.card : ℝ) ≥
          K * (T_Δ * N_Δ / est1_factor) := by gcongr <;> linarith
      have h3 : K * (T_Δ * N_Δ / est1_factor) ≥ T_Δ * N_Δ * est3_factor := by
        have h4 : 0 ≤ T_Δ * N_Δ := by positivity
        have h5 : K / est1_factor ≥ est3_factor := by
          have h6 : est1_factor * est3_factor ≤ K := hK_factors
          have h7 : 0 < est1_factor := h1_pos
          calc K / est1_factor
            ≥ (est1_factor * est3_factor) / est1_factor := by gcongr
          _ = est3_factor := by
            field_simp [h7.ne'] <;> ring
        have h8 : K * (T_Δ * N_Δ / est1_factor) = (K / est1_factor) * (T_Δ * N_Δ) := by ring
        rw [h8]
        have h9 : (K / est1_factor) * (T_Δ * N_Δ) ≥ est3_factor * (T_Δ * N_Δ) := by gcongr
        linarith
      linarith
    have h2 : T_Q_local ≤ M_Δ' * N_Δ := by
      rw [hT_Q_local, hM_Δ']
      exact h_est2 Q hQ
    have h3 : T_Q_local ≥ T_Q * M' / (M_Q' * est3_factor) := by
      rw [hT_Q_local, hT_Q, hM', hM_Q']
      exact h_est3 Q hQ
    have hMΔ'_pos : (0 : ℝ) < M_Δ' := by
      dsimp only [M_Δ'] <;> exact_mod_cast hMΔ
    have hMQ'_pos : (0 : ℝ) < M_Q' := by
      dsimp only [M_Q'] <;> exact_mod_cast hMQ Q hQ
    have hM'_pos : (0 : ℝ) < M' := by
      dsimp only [M'] <;> exact_mod_cast hM
    -- Apply algebra with effective T₀' = T₀ / est3_factor and effective fine count T_Q * M' / est3_factor
    set T₀' : ℝ := T₀ / est3_factor with hT₀'
    have h1' : T₀' ≥ T_Δ * N_Δ := by
      rw [hT₀']
      have h11 : 0 < est3_factor := h3_pos
      have h12 : T₀ ≥ T_Δ * N_Δ * est3_factor := h1
      have h13 : T₀ / est3_factor ≥ (T_Δ * N_Δ * est3_factor) / est3_factor := by gcongr
      have h14 : (T_Δ * N_Δ * est3_factor) / est3_factor = T_Δ * N_Δ := by
        field_simp [h11.ne'] <;> ring
      rw [h14] at h13
      exact h13
    have h3' : T_Q_local ≥ (T_Q * M' / est3_factor) * (1 : ℝ) / M_Q' := by
      have h_eq : T_Q * M' / (M_Q' * est3_factor) = (T_Q * M' / est3_factor) / M_Q' := by ring
      rw [h_eq] at h3
      simpa using h3
    have h_main : T₀' * M_Δ' * M_Q' ≥ T_Δ * (T_Q * M' / est3_factor) * (1 : ℝ) :=
      cardinality_bound_three_estimates T₀' T_Δ (T_Q * M' / est3_factor) T_Q_local N_Δ M_Δ' M_Q' 1
        hNΔ hMΔ'_pos hMQ'_pos (by norm_num) hTΔ_pos h1' h2 h3'
    have h_final : T₀ * M_Δ' * M_Q' ≥ T_Δ * T_Q * M' := by
      have h10 : T₀' * M_Δ' * M_Q' = (T₀ * M_Δ' * M_Q') / est3_factor := by
        rw [hT₀'] <;> ring
      have h11 : T_Δ * (T_Q * M' / est3_factor) * (1 : ℝ) = (T_Δ * T_Q * M') / est3_factor := by
        have h12 : 0 < est3_factor := h3_pos
        field_simp [h12.ne'] <;> ring
      rw [h10, h11] at h_main
      have h13 : 0 < est3_factor := h3_pos
      have h14 : (T₀ * M_Δ' * M_Q') / est3_factor ≥ (T_Δ * T_Q * M') / est3_factor := h_main
      have h15 : T₀ * M_Δ' * M_Q' ≥ T_Δ * T_Q * M' := by
        calc T₀ * M_Δ' * M_Q'
          = est3_factor * ((T₀ * M_Δ' * M_Q') / est3_factor) := by field_simp [h13.ne'] <;> ring
        _ ≥ est3_factor * ((T_Δ * T_Q * M') / est3_factor) := by gcongr
        _ = T_Δ * T_Q * M' := by field_simp [h13.ne'] <;> ring
      exact h15
    simpa [hT₀, hT_Δ, hT_Q, hM_Δ', hM_Q', hM'] using h_final

end CardinalityPhase

end InductionOnScales
