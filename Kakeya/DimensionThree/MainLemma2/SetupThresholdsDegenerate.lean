/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SetupAbsorption

/-!
# The thick-case threshold bundle in the degenerate regime `a = δ`

GWZ split the proof of Lemma 9.1 on the smallest working dimension `a` of the factoring
bodies (`gwz.txt` l.2043-2044): `a ≥ δ^{1-τ}` is the *thick* case, `a ≤ δ^{1-τ}` the *thin*
case. The bundle `Kakeya.VeryNotSticky.ThickDensityThresholds` collects the hypotheses the
thick branch spends, and its three thick-case fields —
`plankPres`, `plankF`, `density` — are asserted **only under the guard `δ^{1-τ} ≤ a`**: GWZ
present the blocks as planks and prove (90)-(91) only in §9.4 (l.2048-2171, general version
l.2110-2140), and both consumers (`Kakeya.VeryNotSticky.goalMult_of_a_ge`,
`Kakeya.VeryNotSticky.exists_goalMult`) read the fields inside the thick branch.

The only regime in which the tree produces a configuration today is the *degenerate* one,
`a = b = δ` (the record body of `Kakeya.VeryNotSticky.exists_veryNotSticky_of_rhoCount`
instantiated at `a = b = δ`; the field `Kakeya.VeryNotSticky.hdims` allows it). There the
guard is **false**: for `0 < δ < 1` and `0 < τ` one has `δ = δ^1 < δ^{1-τ}`, so `δ^{1-τ} ≤ a`
fails at `a = δ`, and the three guarded fields hold by `absurd`. What is left of the bundle is
exactly what has producers: `bias` (`Kakeya.VeryNotSticky.eventually_thick_bias`), `budget`
and `hηF` (two conjuncts of `Kakeya.VeryNotSticky.PlankFrostmanBudget`, the binder `hplankF`
of `Kakeya.VeryNotSticky.exists_setup_caseSideData`), and the normalizations `hCP`, `hΘ`.

This file records that discharge, in four forms:

* `Kakeya.VeryNotSticky.thickDensityThresholds_of_not_thick` — the record from the five
  unguarded hypotheses and the negation of the guard, in any regime;
* `Kakeya.VeryNotSticky.thickDensityThresholds_degenerate` — the same at `a = δ`, `δ < 1`,
  `0 < τ` (the guard's negation is `Kakeya.VeryNotSticky.not_thick_of_a_eq_delta`);
* `Kakeya.VeryNotSticky.exists_thickDensityThresholds_degenerate_of_budget` — the exponent and
  the non-concentration dilation taken from a `PlankFrostmanBudget`;
* `Kakeya.VeryNotSticky.eventually_thickDensityThresholds_degenerate` and
  `Kakeya.VeryNotSticky.eventually_exists_thickDensityThresholds_degenerate_of_budget` — the
  `∀ᶠ δ` forms in which steps T6 (`exists_caseSideData_thresholds_degenerate`) consumes them,
  with `bias` discharged by `eventually_thick_bias` at `δ`-free `C_bias`, `C₀`.

Nothing here weakens the bundle: its statement, its guards and every consumer are untouched,
and the produced record is the full `ThickDensityThresholds`. The thick-case content of the
guarded fields is still owed by whichever construction first produces `a ≥ δ^{1-τ}`.
-/

@[expose] public section

open Filter Topology MeasureTheory

namespace Kakeya.VeryNotSticky

universe u

/-- A scale strictly below `1` is strictly below its own power `1 - τ` for every `τ > 0`:
`x = x^1 < x^{1-τ}`. This is the arithmetic content of "the thick-case guard fails at
`a = δ`". -/
theorem self_lt_rpow_one_sub_of_lt_one {x : NNReal} (hx0 : 0 < x) (hx1 : x < 1) {τ : ℝ}
    (hτ : 0 < τ) : x < x ^ (1 - τ) := by
  have h := NNReal.rpow_lt_rpow_of_exponent_gt hx0 hx1 (show 1 - τ < 1 by linarith)
  simpa [NNReal.rpow_one] using h

/-- **The thick-case guard is false in the degenerate regime.** At `a = δ` with `δ < 1` and
`τ > 0`, `δ^{1-τ} ≤ a` fails (GWZ l.2043-2044: `a = δ ≤ δ^{1-τ}` is the thin case, and
strictly so). The configuration's own bound `Kakeya.VeryNotSticky.hδ1 : δ ≤ 1` is not
enough — at `δ = 1` the guard holds — so the strict `δ < 1` is a hypothesis, met eventually
along `𝓝[>] 0`. -/
theorem not_thick_of_a_eq_delta (cfg : VeryNotSticky.{u}) {τ : ℝ} (hτ : 0 < τ)
    (hδ1 : cfg.δ < 1) (ha : cfg.a = cfg.δ) : ¬ cfg.δ ^ (1 - τ) ≤ cfg.a := by
  rw [ha]
  exact not_le.mpr (self_lt_rpow_one_sub_of_lt_one cfg.hδ hδ1 hτ)

/-- **The bundle from its unguarded fields and the negation of the thick-case guard.**

The three guarded fields `plankPres`, `plankF`, `density` of
`Kakeya.VeryNotSticky.ThickDensityThresholds` are each an implication from `δ^{1-τ} ≤ a`; when
that guard is false they hold by `absurd`, and the bundle reduces to `hCP`, `hΘ`, `bias`,
`hηF`, `budget`. This is the exact complement of
`Kakeya.VeryNotSticky.thickDensityThresholds_canonical`, which discharges `plankF` *under* the
guard and takes the other two guarded fields as hypotheses. -/
theorem thickDensityThresholds_of_not_thick {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    {τ ηF : ℝ} {CP Θ C_NC : NNReal} (hCP : 1 ≤ CP) (hΘ : 1 ≤ Θ) (hηF : 0 < ηF)
    (hbudget : 2 * cfg.η < τ * ηF)
    (hbias : (bd.Cbias : ENNReal) * (((48 * bd.C₀ ^ 6) ^ 3 : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(τ * cfg.ϱ)))
    (hthin : ¬ cfg.δ ^ (1 - τ) ≤ cfg.a) :
    ThickDensityThresholds cfg bd τ CP Θ C_NC ηF where
  hCP := hCP
  hΘ := hΘ
  bias := hbias
  plankPres := fun h => absurd h hthin
  hηF := hηF
  budget := hbudget
  plankF := fun h => absurd h hthin
  density := fun h => absurd h hthin

/-- **The thick-case threshold bundle in the degenerate regime `a = δ`**.

At `a = δ < 1` and `τ > 0` the thick-case guard `δ^{1-τ} ≤ a` is false
(`Kakeya.VeryNotSticky.not_thick_of_a_eq_delta`), so `plankPres`, `plankF` and `density` hold
vacuously, and the bundle is produced from `bias` — supplied eventually by
`Kakeya.VeryNotSticky.eventually_thick_bias` — together with `0 < ηF` and the budget
`2η < τ ηF` (R16-A), which are the first two conjuncts of
`Kakeya.VeryNotSticky.PlankFrostmanBudget`,
and the normalizations `1 ≤ CP`, `1 ≤ Θ`. The constants `CP`, `Θ`, `C_NC` are otherwise
unconstrained in this regime, since the only fields that read them are the guarded ones. -/
theorem thickDensityThresholds_degenerate {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    {τ ηF : ℝ} {CP Θ C_NC : NNReal} (hτ : 0 < τ) (hδ1 : cfg.δ < 1) (ha : cfg.a = cfg.δ)
    (hCP : 1 ≤ CP) (hΘ : 1 ≤ Θ) (hηF : 0 < ηF) (hbudget : 2 * cfg.η < τ * ηF)
    (hbias : (bd.Cbias : ENNReal) * (((48 * bd.C₀ ^ 6) ^ 3 : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(τ * cfg.ϱ))) :
    ThickDensityThresholds cfg bd τ CP Θ C_NC ηF :=
  thickDensityThresholds_of_not_thick hCP hΘ hηF hbudget hbias
    (not_thick_of_a_eq_delta cfg hτ hδ1 ha)

/-- **The degenerate bundle at the exponent and dilation of a plank-Frostman budget.**

`Kakeya.VeryNotSticky.PlankFrostmanBudget β ϱ τ η` supplies `ηF` with `0 < ηF`, `2η < τ ηF`,
and a dilation `C_NC ≥ 1`; its plank estimate is not needed here, because the field `plankF`
that would spend it is vacuous at `a = δ`. The parameters `β`, `ϱ'` of the budget are free,
since only its exponent conjuncts are read. -/
theorem exists_thickDensityThresholds_degenerate_of_budget {cfg : VeryNotSticky.{u}}
    {bd : BallData cfg} {τ β ϱ' : ℝ} {CP Θ : NNReal} (hτ : 0 < τ) (hδ1 : cfg.δ < 1)
    (ha : cfg.a = cfg.δ) (hCP : 1 ≤ CP) (hΘ : 1 ≤ Θ)
    (hbias : (bd.Cbias : ENNReal) * (((48 * bd.C₀ ^ 6) ^ 3 : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(τ * cfg.ϱ)))
    (hplankF : PlankFrostmanBudget.{u} β ϱ' τ cfg.η) :
    ∃ (ηF : ℝ) (C_NC : NNReal), 0 < ηF ∧ 2 * cfg.η < τ * ηF ∧ 1 ≤ C_NC ∧
      ThickDensityThresholds cfg bd τ CP Θ C_NC ηF := by
  obtain ⟨ηF, hηF, hbudget, C_NC, hC_NC, -⟩ := hplankF
  exact ⟨ηF, C_NC, hηF, hbudget, hC_NC,
    thickDensityThresholds_degenerate hτ hδ1 ha hCP hΘ hηF hbudget hbias⟩

/-- **The degenerate bundle is eventually available**, with `bias` discharged by
`Kakeya.VeryNotSticky.eventually_thick_bias` at `δ`-free constants `C_bias`, `C₀` and a
`δ`-free bias exponent `ϱ`; the strict scale bound `δ < 1` comes from the filter. The
configuration and its ball data may depend on the scale; only the displayed pins must hold.
This is the form in which steps T6 of  (the planned
`exists_caseSideData_thresholds_degenerate`, not yet in the tree) is to read the bundle. -/
theorem eventually_thickDensityThresholds_degenerate (Cbias C₀ : NNReal) {τ ϱ : ℝ}
    (hτ : 0 < τ) (hϱ : 0 < ϱ) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg), cfg.δ = d → cfg.ϱ = ϱ →
        bd.Cbias = Cbias → bd.C₀ = C₀ → cfg.a = cfg.δ →
        ∀ {CP Θ C_NC : NNReal} {ηF : ℝ}, 1 ≤ CP → 1 ≤ Θ → 0 < ηF → 2 * cfg.η < τ * ηF →
          ThickDensityThresholds cfg bd τ CP Θ C_NC ηF := by
  filter_upwards [eventually_thick_bias Cbias C₀ hτ hϱ, Ioo_mem_nhdsGT zero_lt_one]
    with d hbias hd01
  intro cfg bd hδ hϱ' hCbias hC₀ ha CP Θ C_NC ηF hCP hΘ hηF hbudget
  subst hδ hϱ' hCbias hC₀
  exact thickDensityThresholds_degenerate hτ hd01.2 ha hCP hΘ hηF hbudget hbias

/-- **The eventual degenerate bundle at the exponent and dilation of a plank-Frostman budget**
— `Kakeya.VeryNotSticky.eventually_thickDensityThresholds_degenerate` composed with
`Kakeya.VeryNotSticky.exists_thickDensityThresholds_degenerate_of_budget`, with `η` pinned so
that the binder `hplankF` of `Kakeya.VeryNotSticky.exists_setup_caseSideData` (or of
`Kakeya.VeryNotSticky.SideDataResidue`) can be passed through unchanged. -/
theorem eventually_exists_thickDensityThresholds_degenerate_of_budget (Cbias C₀ : NNReal)
    {β ϱ η τ : ℝ} (hτ : 0 < τ) (hϱ : 0 < ϱ) (hplankF : PlankFrostmanBudget.{u} β ϱ τ η) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg), cfg.δ = d → cfg.ϱ = ϱ → cfg.η = η →
        bd.Cbias = Cbias → bd.C₀ = C₀ → cfg.a = cfg.δ →
        ∀ {CP Θ : NNReal}, 1 ≤ CP → 1 ≤ Θ →
          ∃ (ηF : ℝ) (C_NC : NNReal), 0 < ηF ∧ 2 * η < τ * ηF ∧ 1 ≤ C_NC ∧
            ThickDensityThresholds cfg bd τ CP Θ C_NC ηF := by
  filter_upwards [eventually_thickDensityThresholds_degenerate.{u} Cbias C₀ hτ hϱ]
    with d hd
  intro cfg bd hδ hϱ' hη hCbias hC₀ ha CP Θ hCP hΘ
  obtain ⟨ηF, hηF, hbudget, C_NC, hC_NC, -⟩ := hplankF
  exact ⟨ηF, C_NC, hηF, hbudget, hC_NC,
    hd cfg bd hδ hϱ' hCbias hC₀ ha hCP hΘ hηF (hη ▸ hbudget)⟩

end Kakeya.VeryNotSticky
