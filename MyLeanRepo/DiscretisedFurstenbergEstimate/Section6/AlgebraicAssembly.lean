module

/-
  Section 6 algebraic assembly.

  Takes the four Section 6 data packages and assembles them into
  `CoarseCaseData` for consumption by `ConditionalAssembly.lean`.

  Contains:
  1. Two-case ratio theorem (coarse_two_case_ratio)
  2. Four-package assembly into TwoScaleIncidenceData
  3. Algebraic consumer: four packages → CoarseCaseData

  This is NOT the genuine source-facing consumer. It takes all four
  packages as hypotheses and constructs none from source data.
  The genuine consumer is in `SourceConsumer.lean`.

  Correct route (operator correction, 2026-08-10):
    Appendix fine-or-coarse alternative
    + B1 decomposition (Prop 5.1)
    + coarse two-case ratio (Cor 2.5 + coarse bound)
    + fine normalized Cor 2.5 ratio
    + B1 multiplicative reassembly
    -> fine-scale 2s gain via TwoScaleIncidenceData assembly

  Whiteprint node: section6_algebraic_assembly
  Dependencies: Section6.Types, improved_incidence_two_scale_assembly
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section6.Types
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5Wrapper
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section6

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem

/-! ========================================================================
   Two-case ratio theorem

   Case 1: MΔ large → uniform_prop5 (Cor 2.5) gives gain.
   Case 2: MΔ small → coarse Appendix bound gives gain directly.

   Threshold: MΔ * Δ^s = Δ^{-ε}.
   In both cases: NΔ / MΔ ≥ δ^{-(s/2 + coarseGain)}
   with coarseGain = ε * α / 2 - loss > 0, α = (u-s)/(1-s).
   ======================================================================== -/

/-- Coarse two-case ratio: from coarse bound + uniform_prop5 to CoarseRatioData.

    Let `X := MΔ * Δ^s` and `α := (u-s)/(1-s)`.

    **Case 1 (`X ≥ Δ^{-ε}`):**
      `NΔ / MΔ ≥ C_prop5 * Δ^{-s} * X^α ≥ C_prop5 * δ^{-(s/2 + εα/2)}`
      `≥ δ^{-(s/2 + εα/2 - loss)}`

    **Case 2 (`X < Δ^{-ε}`):**
      `MΔ < Δ^{-s-ε}`, so
      `NΔ / MΔ > δ^{-(s+ε)} / Δ^{-s-ε} = δ^{-(s/2 + ε/2)}`
      `≥ δ^{-(s/2 + coarseGain)}` (since coarseGain ≤ ε/2)
-/
def coarse_two_case_ratio
    {δ Δ s u ε : ℝ}
    (hδ : 0 < δ) (hδ_one : δ ≤ 1)
    (hΔ_pos : 0 < Δ) (hΔ_one : Δ < 1)
    (hδ_eq2 : δ = Δ ^ 2)
    (hs : 0 < s) (hs1 : s < 1) (hsu : s < u) (hu_one : u ≤ 1)
    (hε_pos : 0 < ε)
    (NΔ MΔ : ℝ)
    (hNΔ_nonneg : 0 ≤ NΔ)
    (hMΔ_pos : 0 < MΔ)
    (h_coarse_bound : NΔ ≥ δ ^ (-(s + ε)))
    (C_prop5 : ℝ)
    (hC_prop5_pos : 0 < C_prop5)
    (α : ℝ)
    (hα_def : α = (u - s) / (1 - s))
    (h_prop5 : NΔ ≥ C_prop5 * MΔ * Δ^(-s) * (MΔ * Δ^s)^α)
    (loss : ℝ)
    (hloss_pos : 0 ≤ loss)
    (h_absorb : C_prop5 ≥ δ ^ loss)
    (hloss_small : loss < ε * α / 2) :
    CoarseRatioData δ s := by
  have h1s : 0 < 1 - s := by linarith
  have hα_pos : 0 < α := by
    rw [hα_def]; apply div_pos <;> linarith
  have hα_le_one : α ≤ 1 := by
    rw [hα_def]; rw [div_le_one h1s] <;> linarith
  set coarseGain : ℝ := ε * α / 2 - loss with hcoarseGain_def
  have hcoarseGain_pos : 0 < coarseGain := by
    dsimp only [coarseGain]; linarith
  have hNΔ_pos : 0 < NΔ := by
    have h_pos : 0 < δ ^ (-(s + ε)) := Real.rpow_pos_of_pos hδ _
    linarith [h_coarse_bound]

  let X : ℝ := MΔ * Δ^s
  have hX_pos : 0 < X := by
    have h1 : 0 < Δ^s := Real.rpow_pos_of_pos hΔ_pos s
    positivity

  have h_rpow2 : ∀ (x : ℝ), (Δ ^ 2) ^ x = Δ ^ (2 * x) := by
    intro x
    have h : (Δ ^ 2) ^ x = Δ ^ (2 * x) := by
      rw [show (Δ ^ 2) = Δ ^ (2 : ℝ) by norm_cast]
      rw [Real.rpow_mul hΔ_pos.le] <;> ring
    exact h

  have h_main_bound : NΔ / MΔ ≥ δ ^ (-(s / 2 + coarseGain)) := by
    by_cases h_case : X ≥ Δ^(-ε)
    · -- Case 1: X large
      have h1 : X^α ≥ (Δ^(-ε))^α := by
        gcongr <;> exact Real.rpow_pos_of_pos hΔ_pos (-ε)
      have h2 : (Δ^(-ε))^α = Δ^(-ε * α) := by
        rw [Real.rpow_mul hΔ_pos.le] <;> ring
      have h3 : X^α ≥ Δ^(-ε * α) := by
        calc X^α ≥ (Δ^(-ε))^α := h1
             _ = Δ^(-ε * α) := h2
      have h4 : NΔ ≥ C_prop5 * MΔ * Δ^(-s) * X^α := by
        simpa [X] using h_prop5
      have h5 : C_prop5 * MΔ * Δ^(-s) * X^α =
          MΔ * (C_prop5 * Δ^(-s) * X^α) := by ring
      rw [h5] at h4
      have h6 : C_prop5 * Δ^(-s) * X^α ≤ NΔ / MΔ := by
        have h7 : MΔ * (C_prop5 * Δ^(-s) * X^α) ≤ NΔ := h4
        have h8 : C_prop5 * Δ^(-s) * X^α =
            (MΔ * (C_prop5 * Δ^(-s) * X^α)) / MΔ := by
          field_simp [hMΔ_pos.ne'] <;> ring
        rw [h8]; gcongr
      have h9 : Δ^(-s) * X^α ≥ Δ^(-s) * Δ^(-ε * α) := by gcongr
      have h10 : Δ^(-s) * Δ^(-ε * α) = Δ^(-(s + ε * α)) := by
        have h11 := Real.rpow_add hΔ_pos (-s) (-ε * α)
        have h12 : -s + -ε * α = -(s + ε * α) := by ring
        rw [h12] at h11; exact h11.symm
      have h131 : Δ^(-s) * X^α ≥ Δ^(-(s + ε * α)) := by
        calc Δ^(-s) * X^α ≥ Δ^(-s) * Δ^(-ε * α) := h9
          _ = Δ^(-(s + ε * α)) := h10
      have h13 : C_prop5 * Δ^(-s) * X^α ≥ C_prop5 * Δ^(-(s + ε * α)) := by
        have h_eq : C_prop5 * Δ^(-s) * X^α = C_prop5 * (Δ^(-s) * X^α) := by ring
        rw [h_eq]
        exact mul_le_mul_of_nonneg_left h131 hC_prop5_pos.le
      have h14 : Δ^(-(s + ε * α)) = δ^(-(s / 2 + ε * α / 2)) := by
        have h15 : δ = Δ^2 := hδ_eq2
        rw [h15]
        have h16 := h_rpow2 (-(s / 2 + ε * α / 2))
        have h17 : 2 * (-(s / 2 + ε * α / 2)) = -(s + ε * α) := by ring
        rw [h16, h17]
      have h18 : NΔ / MΔ ≥ C_prop5 * δ^(-(s / 2 + ε * α / 2)) := by
        calc NΔ / MΔ ≥ C_prop5 * Δ^(-s) * X^α := h6
          _ ≥ C_prop5 * Δ^(-(s + ε * α)) := h13
          _ = C_prop5 * δ^(-(s / 2 + ε * α / 2)) := by rw [h14]
      have h20 : C_prop5 * δ^(-(s / 2 + ε * α / 2)) ≥
          δ^loss * δ^(-(s / 2 + ε * α / 2)) := by
        gcongr <;> linarith [h_absorb]
      have h21 : δ^loss * δ^(-(s / 2 + ε * α / 2)) = δ^(-(s / 2 + coarseGain)) := by
        have h22 := Real.rpow_add hδ loss (-(s / 2 + ε * α / 2))
        have h23 : loss + (-(s / 2 + ε * α / 2)) = -(s / 2 + coarseGain) := by
          dsimp only [coarseGain] <;> ring
        rw [h23] at h22; exact h22.symm
      calc NΔ / MΔ ≥ C_prop5 * δ^(-(s / 2 + ε * α / 2)) := h18
        _ ≥ δ^loss * δ^(-(s / 2 + ε * α / 2)) := h20
        _ = δ^(-(s / 2 + coarseGain)) := h21
    · -- Case 2: X small
      have hX_lt : X < Δ^(-ε) := by linarith
      have hMΔ_lt : MΔ < Δ^(-s - ε) := by
        have h1 : MΔ * Δ^s < Δ^(-ε) := by simpa [X] using hX_lt
        have h2 : 0 < Δ^s := Real.rpow_pos_of_pos hΔ_pos s
        have h3 : MΔ < Δ^(-ε) / Δ^s := by
          calc MΔ = (MΔ * Δ^s) / Δ^s := by field_simp [h2.ne'] <;> ring
            _ < Δ^(-ε) / Δ^s := by gcongr
        have h4 : Δ^(-ε) / Δ^s = Δ^(-s - ε) := by
          have h5 : Δ^(-ε) / Δ^s = Δ^(-ε) * Δ^(-s) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg hΔ_pos.le] <;> ring
          rw [h5]
          have h6 := Real.rpow_add hΔ_pos (-ε) (-s)
          have h7 : -ε + -s = -s - ε := by ring
          rw [h7] at h6; exact h6.symm
        rw [h4] at h3; exact h3
      have h_pos1 : 0 < δ^(-(s + ε)) := Real.rpow_pos_of_pos hδ _
      have h_pos3 : 0 < Δ^(-s - ε) := Real.rpow_pos_of_pos hΔ_pos (-s - ε)
      have h9 : NΔ / MΔ ≥ δ^(-(s + ε)) / MΔ := by
        exact div_le_div_of_nonneg_right h_coarse_bound hMΔ_pos.le
      have h10 : δ^(-(s + ε)) / Δ^(-s - ε) < δ^(-(s + ε)) / MΔ := by
        rw [div_lt_div_iff_of_pos_left h_pos1 h_pos3 hMΔ_pos]
        exact hMΔ_lt
      have h11 : δ^(-(s + ε)) / Δ^(-s - ε) = Δ^(-(s + ε)) := by
        have h12 : δ = Δ^2 := hδ_eq2
        rw [h12]
        have h13 := h_rpow2 (-(s + ε))
        have h14 : 2 * (-(s + ε)) = -(2 * s + 2 * ε) := by ring
        rw [h13, h14]
        have h15 : Δ^(-(2 * s + 2 * ε)) / Δ^(-s - ε) = Δ^(-(s + ε)) := by
          have h16 : Δ^(-(2 * s + 2 * ε)) / Δ^(-s - ε) =
              Δ^(-(2 * s + 2 * ε)) * Δ^(s + ε) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg hΔ_pos.le] <;> ring_nf
          rw [h16]
          have h17 := Real.rpow_add hΔ_pos (-(2 * s + 2 * ε)) (s + ε)
          have h18 : -(2 * s + 2 * ε) + (s + ε) = -(s + ε) := by ring
          rw [h18] at h17; exact h17.symm
        exact h15
      have h19 : NΔ / MΔ > Δ^(-(s + ε)) := by
        calc NΔ / MΔ ≥ δ^(-(s + ε)) / MΔ := h9
          _ > δ^(-(s + ε)) / Δ^(-s - ε) := h10
          _ = Δ^(-(s + ε)) := h11
      have h20 : Δ^(-(s + ε)) = δ^(-(s / 2 + ε / 2)) := by
        have h21 : δ = Δ^2 := hδ_eq2
        rw [h21]
        have h22 := h_rpow2 (-(s / 2 + ε / 2))
        have h23 : 2 * (-(s / 2 + ε / 2)) = -(s + ε) := by ring
        rw [h22, h23]
      have h24 : NΔ / MΔ > δ^(-(s / 2 + ε / 2)) := by
        rw [h20] at h19; exact h19
      have h25 : s / 2 + coarseGain ≤ s / 2 + ε / 2 := by
        dsimp only [coarseGain]; nlinarith [hα_le_one, hloss_pos]
      have h26 : -(s / 2 + ε / 2) ≤ -(s / 2 + coarseGain) := by linarith
      have h27 : δ^(-(s / 2 + ε / 2)) ≥ δ^(-(s / 2 + coarseGain)) := by
        exact Real.rpow_le_rpow_of_exponent_ge hδ hδ_one h26
      exact le_trans h27 (le_of_lt h24)

  exact
    { coarseCount := NΔ
      coarseMultiplicity := MΔ
      coarseGain := coarseGain
      hMΔ_pos := hMΔ_pos
      hgainΔ := hcoarseGain_pos
      hcoarse := h_main_bound
    }

end DirecretisedFurstenbergEstimate.Section6

end
