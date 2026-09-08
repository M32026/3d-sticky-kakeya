/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.CoreLossEnvelope

/-!
# Sub-polynomial losses for Proposition 5.1, Part (B)

The two estimates below turn `c * M⁻¹ ≤ λ(𝒲, Y_𝒲)` into
`δ ^ ηₒ ≤ λ(𝒲, Y_𝒲)`, the outer fullness bound used by
`factoringAndMultPropGlobal_of_remark53`.

The selection-loss estimate uses `coe_outerScaleSelectionConstant`,
monotonicity of `logb` from `B/δ ≤ 1/δ`, and the eventual bound on powers of
`1 + logb`. Its scale range is `δ ≤ B ≤ 1`. The fullness estimate follows
from the pipeline-loss bound and
`factoringCoreAtScaleUniformRefinementConstant_eq_inv`.

The fullness constant must be positive. The theorem
`factoringCoreAtScaleUniformRefinementConstant_pos` supplies positivity when
the thick outer set is nonempty, as obtained from
`FactoringAndMultPropCoreAtScale.outerSet_nonempty_of_input_mass_pos`.
Without nonemptiness the retained-mass coefficient, and hence the fullness
constant, can vanish.
-/

@[expose] public section

open MeasureTheory Filter Topology

open scoped ENNReal NNReal

noncomputable section

namespace Kakeya

namespace PartBLoss

open ShadedBody

/-! ### Two inversion steps -/

/-- `L ≤ δ ^ (-η)` inverts to `δ ^ η ≤ L⁻¹`, for `L ≠ 0`. -/
theorem rpow_le_inv_of_le_rpow_neg {L δ : ℝ≥0} {η : ℝ}
    (hL : L ≠ 0) (h : (L : ENNReal) ≤ (δ : ENNReal) ^ (-η)) :
    (δ : ENNReal) ^ η ≤ ((L⁻¹ : ℝ≥0) : ENNReal) := by
  rw [ENNReal.rpow_neg] at h
  rw [ENNReal.coe_inv hL]
  have hinv := ENNReal.inv_le_inv.mpr h
  rwa [inv_inv] at hinv

/-- Squaring a lower bound `δ ^ η ≤ R` gives `δ ^ (2 η) ≤ R ^ 2`. -/
theorem rpow_two_mul_le_sq_of_rpow_le {R δ : ℝ≥0} {η : ℝ}
    (h : (δ : ENNReal) ^ η ≤ (R : ENNReal)) :
    (δ : ENNReal) ^ (2 * η) ≤ ((R ^ 2 : ℝ≥0) : ENNReal) := by
  have hsq : (δ : ENNReal) ^ (2 * η) = ((δ : ENNReal) ^ η) ^ (2 : ℕ) := by
    rw [← ENNReal.rpow_natCast ((δ : ENNReal) ^ η) 2, ← ENNReal.rpow_mul]
    congr 1
    push_cast
    ring
  rw [hsq, ENNReal.coe_pow]
  exact pow_le_pow_left' h 2

/-! ### Absorption 1: the outer-scale selection loss, for `δ ≤ B ≤ 1` -/

/-- **The outer-scale selection loss is sub-polynomial, in threshold form, on `δ ≤ B ≤ 1`.**

`ShadedBody.outerScaleSelectionConstant δ B = 1 + log₂(B / δ)` counts the dyadic scales between `δ`
and `B`, so on `B ≤ 1` it is at most `1 + log₂(1/δ)`.

This branch's `ShadedBody.eventually_outerScaleSelectionConstant_le_rpow_neg` proves the same bound
but under `1 ≤ B`, which the Part-(B) consumer cannot supply: its upper endpoint is the short plank
half-width `a ≤ 1` (`Kakeya.Section6PartBData.section6SelectScaleInput` is taken at `B = a`).  The
`B` here is quantified *inside* the threshold, so one `δ₀` serves every admissible `B`. -/
theorem exists_threshold_outerScaleSelectionConstant_le_rpow_neg {η : ℝ} (hη : 0 < η) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ δ B : ℝ≥0, 0 < δ → δ ≤ B → B ≤ 1 → δ ≤ δ₀ →
      (ShadedBody.outerScaleSelectionConstant δ B : ENNReal) ≤ (δ : ENNReal) ^ (-η) := by
  have h_ev : ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0),
      ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : ℝ))) ≤ (δ : ENNReal) ^ (-η) := by
    simpa [pow_one] using (ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg hη 1)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp h_ev
  refine ⟨u, hu, ?_⟩
  intro δ B hδ0 hδB hB1 hδu
  have h₀ := hsub ⟨hδ0, hδu⟩
  rw [ShadedBody.coe_outerScaleSelectionConstant]
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hB0 : (0 : ℝ≥0) < B := lt_of_lt_of_le hδ0 hδB
  have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB0
  have hratio_pos : (0 : ℝ) < (B : ℝ) / (δ : ℝ) := div_pos hBR hδR
  have hratio_le : (B : ℝ) / (δ : ℝ) ≤ 1 / (δ : ℝ) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hB1) (inv_nonneg.mpr hδR.le)
  have hlogb : Real.logb 2 ((B : ℝ) / (δ : ℝ)) ≤ Real.logb 2 (1 / (δ : ℝ)) :=
    Real.logb_le_logb_of_le (b := 2) (by norm_num : (1 : ℝ) < 2) hratio_pos hratio_le
  calc ENNReal.ofReal (1 + Real.logb 2 ((B : ℝ) / (δ : ℝ)))
      ≤ ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : ℝ))) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ (δ : ENNReal) ^ (-η) := h₀

/-! ### Absorption 2: Proposition 5.1's own fullness constant -/

set_option maxHeartbeats 800000 in
/-- **Proposition 5.1's uniform fullness constant is bounded below by any prescribed positive power
of the master scale.**

`ShadedBody.factoringCoreAtScaleUniformFullnessConstant 3 M N w = L⁻¹ · Rc ^ 2` with
`L = 8 · C_λ · (N + 1)` the induced-shading loss and `Rc` the uniform retained-mass coefficient.
Both factors are handled by facts already on this branch: `L` by
`ShadedBody.eventually_const_le_coe_rpow_neg` together with the `N`-hypothesis, and `Rc` by
`ShadedBody.factoringCoreAtScaleUniformRefinementConstant_eq_inv` against
`ShadedBody.eventually_factoringCoreAtScaleUniformPipelineLoss_le_rpow_neg`.

The three hypotheses on the configuration are the ones the pipeline envelope already demands — a
polynomially bounded cardinality `M ≤ δ ^ (-7)`, a logarithmically bounded volume exponent
`N + 1 ≤ δ ^ (-η/12)`, and a selected scale `δ ≤ w ≤ 1` — plus positivity of `Rc`, which has the
producer named in the module docstring and without which the statement is false. -/
theorem exists_threshold_rpow_le_fullnessConstant {η : ℝ} (hη : 0 < η) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ (δ w : ℝ≥0) (M N : ℕ), 0 < δ → δ ≤ δ₀ → δ ≤ w → w ≤ 1 →
      0 < M → (M : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) →
      ((N + 1 : ℕ) : ENNReal) ≤ (δ : ENNReal) ^ (-(η / 12)) →
      0 < ShadedBody.factoringCoreAtScaleUniformRefinementConstant 3 M N w →
      (δ : ENNReal) ^ η
        ≤ ((ShadedBody.factoringCoreAtScaleUniformFullnessConstant 3 M N w : ℝ≥0) : ENNReal) := by
  have hη3 : (0 : ℝ) < η / 3 := by positivity
  have hη6 : (0 : ℝ) < η / 6 := by positivity
  set A : ℝ≥0 := max 1 (2 * 2 ^ 2 * lambdaInducedSingleWUniform.C) with hA
  have hA1 : (1 : ENNReal) ≤ (A : ENNReal) := by
    have : (1 : ℝ≥0) ≤ A := le_max_left _ _
    exact_mod_cast this
  obtain ⟨u₁, hu₁, hev₁⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (ShadedBody.eventually_const_le_coe_rpow_neg hA1 ENNReal.coe_ne_top hη6)
  obtain ⟨u₂, hu₂, hev₂⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (ShadedBody.eventually_factoringCoreAtScaleUniformPipelineLoss_le_rpow_neg hη3)
  refine ⟨min u₁ u₂, lt_min hu₁ hu₂, ?_⟩
  intro δ w M N hδ0 hδ hδw hw1 hM hMcard hN hRc
  have hδ1 : δ ≤ 1 := hδw.trans hw1
  have hδE0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδEtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ1E : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have h1 := hev₁ ⟨hδ0, hδ.trans (min_le_left _ _)⟩
  have h2 := hev₂ ⟨hδ0, hδ.trans (min_le_right _ _)⟩
  have hN6 : ((N + 1 : ℕ) : ENNReal) ≤ (δ : ENNReal) ^ (-(η / 6)) :=
    hN.trans (ENNReal.rpow_le_rpow_of_exponent_ge hδ1E (by linarith))
  have hN12 : ((N + 1 : ℕ) : ENNReal) ≤ (δ : ENNReal) ^ (-((η / 3) / 4)) := by
    have hexp : -((η / 3) / 4) = -(η / 12) := by ring
    rw [hexp]; exact hN
  have hP : (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 M N w : ENNReal)
      ≤ (δ : ENNReal) ^ (-(η / 3)) := h2 M N hM hMcard hN12 w hδw hw1
  set P : ℝ≥0 := ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 M N w with hPdef
  set Rc : ℝ≥0 := ShadedBody.factoringCoreAtScaleUniformRefinementConstant 3 M N w with hRcdef
  have hRcP : Rc = P⁻¹ := ShadedBody.factoringCoreAtScaleUniformRefinementConstant_eq_inv 3 M N w
  have hPne : P ≠ 0 := by
    intro h0
    rw [h0, inv_zero] at hRcP
    exact absurd hRcP (ne_of_gt hRc)
  -- the induced-shading coefficient
  set L : ℝ≥0 := 2 * 2 ^ 2 * lambdaInducedSingleWUniform.C * ((N : ℝ≥0) + 1) with hL
  have hLne : L ≠ 0 := by
    dsimp [L]
    have hN1 : (0 : ℝ≥0) < (N : ℝ≥0) + 1 := by positivity
    exact ne_of_gt (mul_pos (mul_pos (by norm_num : (0 : ℝ≥0) < 2 * 2 ^ 2)
      lambdaInducedSingleWUniform.C_pos) hN1)
  have hLE : (L : ENNReal) ≤ (δ : ENNReal) ^ (-(η / 3)) := by
    have hsplit : (δ : ENNReal) ^ (-(η / 3))
        = (δ : ENNReal) ^ (-(η / 6)) * (δ : ENNReal) ^ (-(η / 6)) := by
      rw [← ENNReal.rpow_add _ _ hδE0 hδEtop]; congr 1; ring
    have hLA : (L : ENNReal) ≤ (A : ENNReal) * ((N + 1 : ℕ) : ENNReal) := by
      have hLprod : L = (2 * 2 ^ 2 * lambdaInducedSingleWUniform.C) * ((N : ℝ≥0) + 1) := by
        dsimp [L]
      have hstep : L ≤ A * ((N : ℝ≥0) + 1) := by
        rw [hLprod]
        exact mul_le_mul' (le_max_right _ _) le_rfl
      have hcast : ((A * ((N : ℝ≥0) + 1) : ℝ≥0) : ENNReal)
          = (A : ENNReal) * ((N + 1 : ℕ) : ENNReal) := by
        rw [ENNReal.coe_mul]
        congr 1
        push_cast
        ring
      calc (L : ENNReal) ≤ ((A * ((N : ℝ≥0) + 1) : ℝ≥0) : ENNReal) := by exact_mod_cast hstep
        _ = (A : ENNReal) * ((N + 1 : ℕ) : ENNReal) := hcast
    rw [hsplit]
    exact hLA.trans (mul_le_mul' h1.2.2 hN6)
  have hLinv : (δ : ENNReal) ^ (η / 3) ≤ ((L⁻¹ : ℝ≥0) : ENNReal) :=
    rpow_le_inv_of_le_rpow_neg hLne hLE
  have hRcge : (δ : ENNReal) ^ (η / 3) ≤ (Rc : ENNReal) := by
    rw [hRcP]
    exact rpow_le_inv_of_le_rpow_neg hPne hP
  have hRcsq : (δ : ENNReal) ^ (2 * (η / 3)) ≤ ((Rc ^ 2 : ℝ≥0) : ENNReal) :=
    rpow_two_mul_le_sq_of_rpow_le hRcge
  have hfc : ShadedBody.factoringCoreAtScaleUniformFullnessConstant 3 M N w = L⁻¹ * Rc ^ 2 := by
    dsimp [ShadedBody.factoringCoreAtScaleUniformFullnessConstant, L, Rc]
  rw [hfc]
  calc (δ : ENNReal) ^ η
      = (δ : ENNReal) ^ (η / 3) * (δ : ENNReal) ^ (2 * (η / 3)) := by
        rw [← ENNReal.rpow_add _ _ hδE0 hδEtop]; congr 1; ring
    _ ≤ ((L⁻¹ : ℝ≥0) : ENNReal) * ((Rc ^ 2 : ℝ≥0) : ENNReal) := mul_le_mul' hLinv hRcsq
    _ = ((L⁻¹ * Rc ^ 2 : ℝ≥0) : ENNReal) := by rw [ENNReal.coe_mul]

end PartBLoss

end Kakeya

end

end
