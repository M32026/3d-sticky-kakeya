/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.DenseInBodyConstants
public import Kakeya.DimensionThree.MainLemma2.SetupAbsorption

/-!
# A density threshold for the thick case

`Kakeya.VeryNotSticky.goalMult_of_a_ge_of_bareThreshold` proves
`cfg.goalMult (ϱβτ/8)` from the other fields of `ThickDensityThresholds`
and a threshold independent of the comparison constant `C`.
`goalMult_of_a_ge_of_goalDensity` supplies `C` together with
`C² ≤ δ^{-cfg.η}`, so its contribution is paid with one `η`; the
threshold exponent is consequently `-(ϱβτ/8 - cfg.η)`.
A threshold universal in `C` would be false by
`Kakeya.VeryNotSticky.no_densityAfter_forall_C`.

`statement_of_universal_thickDensity_bare` names the threshold, and
`goalMult_of_a_ge_of_thickBundle_bare` applies it to the assembled bundle.
`eventually_thickDensity_bare` supplies it by absorption when the relevant
constants are fixed: `thickGain_ge` gives `ϱβτ/8 - η ≥ 89η > 0`.

## Why the threshold is a field of the bundle

The `CaseSideData` bundle is obtained after `δ` is fixed. Its bias field
controls `C_bias · (48 C₀⁶)³ ≤ δ^{-τϱ}`, whereas
`denseInBodyΘ CP Θ₀ C_bias = CP · Θ₀ · C_bias²` uses the square of
`C_bias`. The bias bound therefore permits a cost `δ^{-2τϱ}`.
`bias_budget_below_Cbias_square_cost` shows that `2τϱ` exceeds the
entire budget `ϱβτ/8 - η` for the admissible parameters; the ratio
before subtracting `η` is `16/β ≥ 16`. Moreover, `hCP : 1 ≤ CP` and
`hΘ : 1 ≤ Θ` provide no upper bounds on `CP` or `Θ`.
Thus the density threshold is additional quantitative information, and
cannot be recovered from the bias field alone after the constants are
chosen. `DenseInBodyNamed.lean` provides the named witnesses needed to
state that threshold directly in the bundle.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter
open scoped NNReal ENNReal

universe u

/-! `Kakeya.VeryNotSticky.goalMult_of_a_ge_of_bareThreshold` now lives in
`MainLemma2/DenseInBodyConstants.lean`, next to `goalMult_of_denseInBody_at`, so that both
consumers of the re-cut field can reach it. -/

/-- **Why the field cannot simply be deleted**: the `Cbias²` factor alone costs more exponent
than the whole budget the bare threshold has. -/
theorem bias_budget_below_Cbias_square_cost {β ζ exscal ϱ η τ τ' : ℝ}
    (params : CaseParams β ζ exscal ϱ η τ τ') (hβ1 : β ≤ 1) (hη : 0 < η) (hϱ : 0 < ϱ) :
    ϱ * β * τ / 8 - η < 2 * (τ * ϱ) := by
  have hτ : 0 < τ := params.hτ
  have hprod : 0 ≤ ϱ * τ * (1 - β) := mul_nonneg (mul_pos hϱ hτ).le (sub_nonneg.mpr hβ1)
  nlinarith [hprod, hη, mul_pos hϱ hτ]

/-! ### The after-text, named, and its drop-in consumer -/

/-! The after-text `Kakeya.VeryNotSticky.statement_of_universal_thickDensity_bare` now lives
in `MainLemma2/ThickCase.lean`, immediately before `Kakeya.VeryNotSticky.ThickDensityThresholds`,
because the field `density` cites it. It was defined here
while the re-cut was auxiliary. -/

/-! ### The replacement is producible — which the deleted field was not -/

/-- **The bare threshold holds for every small `δ`**, at pinned `δ`-free constants. This is the
half the deleted field never had: `Kakeya.VeryNotSticky.ThickDensityThresholds.density` is
compiled-unsatisfiable, while this clause is a plain absorption of a `δ`-free
constant into `δ^{-(ν - η)}`, and `ν - η ≥ 89 η > 0` by
`Kakeya.VeryNotSticky.thickGain_ge`. So the re-cut turns an unsatisfiable field into a
producible one, and `thickDensityThresholds_general` (row G11) can discharge it. -/
theorem eventually_thickDensity_bare (C₀bd Cbias CP Θ₀ : NNReal) {β ϱ η τ τ' : ℝ}
    (hη : 0 < η) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.ϱ = ϱ →
      CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ' →
      bd.C₀ = C₀bd → bd.Cbias = Cbias →
      statement_of_universal_thickDensity_bare.{u} cfg bd τ CP Θ₀ := by
  filter_upwards [eventually_ennreal_le_rpow_neg
      (K := ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (C₀bd : ℝ)) ^ 3) *
        (denseInBodyC₁ CP (ϱ * β * τ / 8) β : ENNReal) *
        (denseInBodyΘ CP Θ₀ Cbias : ENNReal))
      (by
        refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) ?_ <;>
          exact ENNReal.coe_ne_top)
      (ν := 89 * η) (by linarith)] with d hd
  intro cfg bd hδ hβ hηc hϱ params hC₀ hCb _hthick
  have hgain : 90 * cfg.η ≤ cfg.ϱ * cfg.β * τ / 8 := thickGain_ge cfg params
  have hηpos : 0 < cfg.η := cfg.hη
  have hle : (89 : ℝ) * cfg.η ≤ cfg.ϱ * cfg.β * τ / 8 - cfg.η := by linarith
  have hδ1 : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
  have hmono : (cfg.δ : ENNReal) ^ (-(89 * cfg.η)) ≤
      (cfg.δ : ENNReal) ^ (-(cfg.ϱ * cfg.β * τ / 8 - cfg.η)) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hδ1 (by linarith)
  refine le_trans ?_ hmono
  rw [hC₀, hCb, hδ, hβ, hηc, hϱ] at *
  exact hd

/-- **The bare threshold, keyed on the exponent gap alone.** The variant of
`Kakeya.VeryNotSticky.eventually_thickDensity_bare` that a general-`(a, b)` assembly can use:
it asks for `η < ϱβτ/8` as a *number*, not for a `Kakeya.VeryNotSticky.CaseParams` at the
configuration's own `ζ`, which an assembly that pins only `β`, `η`, `exscal`, `ϱ` does not
have. Everything else is the same plain absorption. -/
theorem eventually_thickDensity_bare_of_gap (C₀bd Cbias CP Θ₀ : NNReal) {β ϱ η τ : ℝ}
    (hgap : 0 < ϱ * β * τ / 8 - η) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.ϱ = ϱ → bd.C₀ = C₀bd → bd.Cbias = Cbias →
      statement_of_universal_thickDensity_bare.{u} cfg bd τ CP Θ₀ := by
  filter_upwards [eventually_ennreal_le_rpow_neg
      (K := ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (C₀bd : ℝ)) ^ 3) *
        (denseInBodyC₁ CP (ϱ * β * τ / 8) β : ENNReal) *
        (denseInBodyΘ CP Θ₀ Cbias : ENNReal))
      (by
        refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) ?_ <;>
          exact ENNReal.coe_ne_top)
      (ν := ϱ * β * τ / 8 - η) hgap] with d hd
  intro cfg bd hδ hβ hηc hϱ hC₀ hCb _hthick
  subst hδ hβ hηc hϱ hC₀ hCb
  exact hd


/-! ### Tripwires on the existing re-cut -/

/-- **Tripwire 1: the field carries exactly the named after-text.** If
`Kakeya.VeryNotSticky.ThickDensityThresholds.density` is ever re-worded, this `example` stops
compiling. -/
example (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (τ : ℝ) (CP Θ C_NC : NNReal) (ηF : ℝ)
    (hdens : ThickDensityThresholds cfg bd τ CP Θ C_NC ηF) :
    statement_of_universal_thickDensity_bare.{u} cfg bd τ CP Θ :=
  hdens.density

/-- **Tripwire 2: the re-cut changed no consumer type.** `Kakeya.VeryNotSticky.exists_goalMult`
still has exactly the type it had before F33 — only its thick branch was re-routed through
`Kakeya.VeryNotSticky.goalMult_of_a_ge_of_bareThreshold`. -/
example (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ') (bd : BallData cfg)
    (hβ1 : cfg.β ≤ 1) {CP Θ C_NC : NNReal} {ηF : ℝ}
    (hdens : ThickDensityThresholds cfg bd τ CP Θ C_NC ηF)
    (thr : ScaleThresholds)
    (hthrThick : cfg.δ ≤ thr.aScale (cfg.ϱ * cfg.β * τ / 8))
    (hslabScale : ∃ tc : ThinConfig cfg bd,
      SlabScale cfg bd tc τ ∧ CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr ∧
        (cfg.a ≤ cfg.δ ^ (1 - τ) → cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) →
          Nonempty (TangentialInputs cfg tc τ'))) :
    cfg.goalMult (casesplitExponent cfg.β cfg.ζ cfg.exscal τ τ' cfg.ϱ) :=
  exists_goalMult cfg params bd hβ1 hdens thr hthrThick hslabScale

end Kakeya.VeryNotSticky

end
