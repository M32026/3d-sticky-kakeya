/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BodiesCardBound
public import Kakeya.DimensionThree.MainLemma2.CaseScaleO5Producer

/-!
# G7 / G7b — the thresholds of `SideDataObligations` conjunct 2, re-cut at general `(a, b)`

This is the general-`(a, b)` twin of `MainLemma2/SetupThresholdsAssembly.lean` and of the
outright closure `Kakeya.VeryNotSticky.sideDataObligations_conjunct2`
(`MainLemma2/BodiesCardBound.lean`). Both existing results are confined to the degenerate path
`cfg.a = cfg.b = cfg.δ` by **two** uses of the pins, and this file removes both.

## What the existing proof spends the pins on, and what replaces it

1. **O5.** `eventually_caseScale_of_C_le` discharges the clause
   `CaseScale.transverseFill_fullness` vacuously, by `not_transverseGuard_of_a_eq_b` applied to
   `(ha.trans hb.symm)`. Here `Kakeya.VeryNotSticky.eventually_caseScale_O5_of_C_le` (row G6,
   `MainLemma2/CaseScaleO5Producer.lean`) **proves** it, under the thin guard
   `cfg.a ≤ cfg.δ^{1-τ}`.
2. **The body count.** `card_bodies_le` turns `card_bodies_mul_le` into `#𝕎_B ≤ C·δ^{-4}` by
   rewriting `r₁·b·a` to `r₁·δ²`. Here `card_bodies_le_general` gets the same `δ^{-4}` bound from
   `cfg.hdims`'s *lower* halves `δ ≤ a ≤ b` alone, through the sharp general form
   `card_bodies_mul_ab_le`.
3. **The thin constant.** `exists_thinConfig_le_of_card_bounds` needs the `δ`-free pin
   `bd.Cg = Cg` to size it. Here `eventually_thinSetupConstant_le` (the `Cg`-free half) plus
   `exists_thinConfig_le_of_card_bounds_Cg_le` take `bd.Cg ≤ cfg.δ^{-εg}` for any `εg < ε`.

`Kakeya.VeryNotSticky.eventually_slabScale_of_C_le` needed **no** change: it is already general in
`(a, b)` (measured — its statement has no `a`/`b` pin and its proof reads none), and the same is
true of `Kakeya.VeryNotSticky.eventually_densityConstant_of_C_le`, of
`Kakeya.VeryNotSticky.eventually_caseScale_clauses` and of
`Kakeya.VeryNotSticky.card_bodies_mul_le`.

## The one hypothesis the general branch must carry: the thin guard

`eventually_caseScale_of_C_le_general` and `eventually_thresholds_general` carry
`cfg.a ≤ cfg.δ ^ (1 - τ)`, and this is *necessary*, not an artefact — see the module docstring of
`MainLemma2/CaseScaleO5Producer.lean`. It is the guard that
`Kakeya.VeryNotSticky.CaseScale.plank_small` already carries as an antecedent, and the guard the
general-branch row G9 must carry as well. It is discharged on the
degenerate path by `cfg.a = cfg.δ` and `Kakeya.VeryNotSticky.CaseParams.hτ` (`0 ≤ τ`), which is
exactly how `sideDataObligations_conjunct2_of_general` below recovers the existing conjunct.

## SP-A: what this file can and cannot be wired into

Conjunct 2 of the **existing** `Kakeya.VeryNotSticky.SideDataObligations` pins `cfg.a = cfg.δ`,
`cfg.b = cfg.δ` and `bd.Cg = Cg`, so the general theorem `eventually_thresholds_general` is not
its type. SP-A — the re-statement of all six conjuncts at general `(a, b)` — is **uncut**.

What is *not* left to trust: `sideDataObligations_conjunct2_of_general` **derives the existing
conjunct 2, verbatim**, from `eventually_thresholds_general`, and the `example` after it feeds
that derivation into `SideDataObligations` by the anonymous constructor. So the general form is
compiler-checked to be a generalisation and not a divergence, and the wiring cost of SP-A is
bounded above by the two-goal specialisation in that proof.

Nothing here changes an existing statement.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody
open scoped NNReal ENNReal

universe u

/-- **Right cancellation of a finite non-zero factor in `ENNReal`.** Mathlib has
`ENNReal.le_div_iff_mul_le` and `ENNReal.mul_div_cancel_right` but no `mul_le_mul_right`
cancellation lemma at this signature; this is the two-line composition, used twice below to clear
`r₁` and `δ²` from the body count. -/
lemma ennreal_le_of_mul_le_mul_right {a b c : ENNReal} (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (h : a * c ≤ b * c) : a ≤ b := by
  rw [← ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct)] at h
  rwa [ENNReal.mul_div_cancel_right hc0 hct] at h

/-! ### G7: `CaseScale` at general `(a, b)` -/

/-- **G7: `Kakeya.VeryNotSticky.CaseScale` at general `(a, b)`.**

Byte-for-byte the fourteen non-O5 clauses of
`Kakeya.VeryNotSticky.eventually_caseScale_of_C_le`; the fifteenth, O5, is supplied by
`Kakeya.VeryNotSticky.eventually_caseScale_O5_of_C_le` (row G6) instead of being discharged
vacuously from `cfg.a = cfg.b`. The pin `cfg.a = cfg.b` is gone; in its place stand the thin guard
`cfg.a ≤ cfg.δ^{1-τ}` and the exponent budget `hbud`, the latter supplied from
`Kakeya.VeryNotSticky.CaseParams.thinHalf` by `Kakeya.VeryNotSticky.o5_budget_of_thinHalf`. -/
theorem eventually_caseScale_of_C_le_general (C₀ Cbias : NNReal) (hC₀ : 1 ≤ C₀)
    {exscal η ϱ τ τ' ν ε : ℝ} (hexscal : 0 < exscal) (hexscal1 : exscal < 1) (hη : 0 < η)
    (hϱ : 0 < ϱ) (hτ' : 0 < τ') (hthinScale : τ + exscal < 1) (hε : 5 * ε < η)
    (hbud : 6 * η + ε < 16 * η * (1 - τ - exscal)) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (thr : ScaleThresholds) (C : NNReal),
        cfg.δ = d → cfg.exscal = exscal → cfg.η = η → cfg.ϱ = ϱ →
        bd.C₀ = C₀ → bd.Cbias = Cbias → cfg.a ≤ cfg.δ ^ (1 - τ) →
        1 ≤ C → C ≤ d ^ (-ε) →
        cfg.δ ≤ thr.aScale ν → cfg.δ ≤ thr.typical →
        CaseScale cfg bd τ τ' ν C thr := by
  filter_upwards [eventually_caseScale_clauses C₀ Cbias 1 hC₀ hexscal hexscal1 hη hϱ hτ' hthinScale,
    eventually_transverseFill_threshold (exscal := exscal) (ϱ := ϱ) hη hexscal1,
    eventually_multiplicity_large (η := 16 * η) (exscal := exscal)
      (by linarith : (0:ℝ) < 16 * η) hexscal1,
    eventually_typicalAngle_const.{u} (exscal := exscal) hη hϱ hexscal1,
    eventually_nnreal_mul_pow_le_rpow_neg (1000 * (8 * netPolyConstant C₀)) 5 (ε := ε)
      (ν := η) (by push_cast; linarith),
    eventually_caseScale_O5_of_C_le.{u} C₀ hC₀ (exscal := exscal) (η := η) (τ := τ) (τ' := τ')
      (ε := ε) hη hbud,
    self_mem_nhdsWithin] with d hcl hfill hmult htyp hball hO5 hd0
  intro cfg bd thr C hδ hex hη' hϱ' hC hCb _hthin h1C hCle hthrA hthrT
  obtain ⟨c1, c2, c3, c4, c5, -, c7, c8, c9⟩ := hcl cfg bd hδ hex hη' hϱ' hC hCb
  exact
    { rho2Star_le_one := c1
      body_fits_ball := c2
      plank_small := c3
      multiplicity_large := by
        have hr : (cfg.δ / cfg.r₁ : NNReal) = (d / d ^ exscal : NNReal) := by
          simp only [VeryNotSticky.r₁, hδ, hex]
        rw [hr, hη']
        exact hmult
      transverse_radius := c4
      transverse_fill := c5
      transverse_ballFill := by
        rw [hC, hδ, hη']
        calc 1000 * ThinCase.transferConstant C C₀
            ≤ 1000 * (8 * netPolyConstant C₀ * C ^ 5) := by
              gcongr
              exact transferConstant_le_mul_pow h1C
          _ = 1000 * (8 * netPolyConstant C₀) * C ^ 5 := by ring
          _ ≤ d ^ (-η) := hball C hCle
      aScaleData_threshold := hthrA
      typicalAngle_threshold := hthrT
      typicalAngle_const := by
        have hr : (cfg.δ / cfg.r₁ : NNReal) = (d / d ^ exscal : NNReal) := by
          simp only [VeryNotSticky.r₁, hδ, hex]
        rw [hr, hη', hϱ', hδ]
        refine htyp (plankEnclosureConstant bd.C₀ * bd.Cbias) ?_
        rw [← hδ, ← hϱ']
        exact c7
      plankCard_bias := c7
      transverseFill_threshold := hfill cfg bd hδ hex hη' hϱ'
      transverseFill_fullness :=
        hO5 cfg bd C hδ hex hη' hC h1C (by rw [hδ]; exact hCle)
      typicalAngle_selection := c8
      typicalAngle_cap := c9 }


/-! ### G7b (i): the body count at general `(a, b)` -/

/-- **The sharp general body count, division-free**: `#W_B * (a*b) <= C(C0,Cbias) * d^{-2r} * r1^2`,
i.e. 's `#bodies ≤ C·(r₁²/(a b))·δ^{-2ϱ}` cleared of division.

The input `Kakeya.VeryNotSticky.card_bodies_mul_le` is **already** general in `(a, b)` ; all that
is done here is to evaluate the ball volume as `r₁³·|B(0,1)|` and cancel one power of `r₁`. On the
degenerate path this is `Kakeya.VeryNotSticky.card_bodies_le`'s content before its `rw [ha, hb]`. -/
theorem card_bodies_mul_ab_le (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    {B : bd.bι} (hB : B ∈ bd.bs) :
    ((bd.bodies B).card : ENNReal) * ((cfg.a * cfg.b : NNReal) : ENNReal)
      ≤ bodiesCardConst bd.C₀ bd.Cbias * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) *
          (cfg.r₁ : ENNReal) ^ 2 := by
  have hr0 : (0 : ℝ) ≤ (cfg.r₁ : ℝ) := (cfg.r₁).coe_nonneg
  have hr₁pos : (0 : NNReal) < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  have key := card_bodies_mul_le cfg bd hB
  have hvol : volume (Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ))
      = ENNReal.ofReal ((cfg.r₁ : ℝ) ^ 3) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    rw [Measure.addHaar_closedBall (volume : Measure (EuclideanSpace ℝ (Fin 3))) (bd.ctr B) hr0]
    simp
  have hofReal : ENNReal.ofReal ((cfg.r₁ : ℝ) ^ 3) = (cfg.r₁ : ENNReal) ^ 3 := by
    rw [ENNReal.ofReal_pow hr0, ENNReal.ofReal_coe_nnreal]
  rw [hvol, hofReal] at key
  have hRne : (cfg.r₁ : ENNReal) ≠ 0 := by simp [hr₁pos.ne']
  have hRtop : (cfg.r₁ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  refine ennreal_le_of_mul_le_mul_right hRne hRtop ?_
  calc ((bd.bodies B).card : ENNReal) * ((cfg.a * cfg.b : NNReal) : ENNReal) *
        (cfg.r₁ : ENNReal)
      = ((bd.bodies B).card : ENNReal) * ((cfg.r₁ * cfg.b * cfg.a : NNReal) : ENNReal) := by
        push_cast; ring
    _ ≤ (((6 * bd.C₀ ^ 3 * bd.Cbias : NNReal)) : ENNReal) *
          (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) *
          ((cfg.r₁ : ENNReal) ^ 3 * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)) := key
    _ = bodiesCardConst bd.C₀ bd.Cbias * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) *
          (cfg.r₁ : ENNReal) ^ 2 * (cfg.r₁ : ENNReal) := by
        rw [bodiesCardConst]; ring

/-- **The `δ^{-4}` body count at general `(a, b)`**, the shape the thin-constant pipeline
consumes. The existing `Kakeya.VeryNotSticky.card_bodies_le` spends `cfg.a = cfg.δ` and
`cfg.b = cfg.δ`; the general bound needs only the *lower* halves `cfg.δ ≤ cfg.a ≤ cfg.b` of
`Kakeya.VeryNotSticky.hdims`, together with `r₁ ≤ 1` and `ϱ ≤ 1` — so the pins were never
load-bearing here, only convenient. -/
theorem card_bodies_le_general (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (hϱ1 : cfg.ϱ ≤ 1) {B : bd.bι} (hB : B ∈ bd.bs) :
    ((bd.bodies B).card : ENNReal)
      ≤ bodiesCardConst bd.C₀ bd.Cbias * ((cfg.δ : ENNReal)⁻¹) ^ 4 := by
  have hδ0 : (0 : NNReal) < cfg.δ := cfg.hδ
  have hδ1 : cfg.δ ≤ 1 := cfg.hδ1
  have hr₁1 : cfg.r₁ ≤ 1 := NNReal.rpow_le_one hδ1 cfg.hexscal.le
  obtain ⟨hδa, hab, -⟩ := cfg.hdims
  have hδb : cfg.δ ≤ cfg.b := hδa.trans hab
  set d : ENNReal := (cfg.δ : ENNReal) with hd
  have hdne : d ≠ 0 := by simp [hd, hδ0.ne']
  have hdtop : d ≠ ⊤ := by simp [hd]
  have key := card_bodies_mul_ab_le cfg bd hB
  -- `δ² ≤ a b`
  have hab2 : d * d ≤ ((cfg.a * cfg.b : NNReal) : ENNReal) := by
    rw [hd]
    push_cast
    gcongr
  -- `δ^{-2ϱ} ≤ δ^{-2}` and `r₁² ≤ 1`
  have hrpow : d ^ (-(2 * cfg.ϱ)) ≤ (d⁻¹) ^ 2 := by
    have h : d ^ (-(2 * cfg.ϱ)) ≤ d ^ (-(2 : ℝ)) := by
      refine ENNReal.rpow_le_rpow_of_exponent_ge (by rw [hd]; exact_mod_cast hδ1) ?_
      have h2 : (2 : ℝ) * cfg.ϱ ≤ 2 := by nlinarith [cfg.hϱ]
      linarith
    have hδinv2 : d ^ (-(2 : ℝ)) = (d⁻¹) ^ 2 := by
      rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_neg, ENNReal.rpow_natCast,
        ← ENNReal.inv_pow]
    rwa [hδinv2] at h
  have hR2 : (cfg.r₁ : ENNReal) ^ 2 ≤ 1 := by
    have h1 : (cfg.r₁ : ENNReal) ≤ 1 := by exact_mod_cast hr₁1
    calc (cfg.r₁ : ENNReal) ^ 2 ≤ (1 : ENNReal) ^ 2 := by gcongr
      _ = 1 := one_pow 2
  have hstep : ((bd.bodies B).card : ENNReal) * (d * d)
      ≤ bodiesCardConst bd.C₀ bd.Cbias * (d⁻¹) ^ 2 := by
    calc ((bd.bodies B).card : ENNReal) * (d * d)
        ≤ ((bd.bodies B).card : ENNReal) * ((cfg.a * cfg.b : NNReal) : ENNReal) := by gcongr
      _ ≤ bodiesCardConst bd.C₀ bd.Cbias * d ^ (-(2 * cfg.ϱ)) * (cfg.r₁ : ENNReal) ^ 2 := key
      _ ≤ bodiesCardConst bd.C₀ bd.Cbias * (d⁻¹) ^ 2 * 1 := by gcongr
      _ = bodiesCardConst bd.C₀ bd.Cbias * (d⁻¹) ^ 2 := mul_one _
  have hmul : d * d ≠ 0 := by simp [hdne]
  have hmultop : d * d ≠ ⊤ := ENNReal.mul_ne_top hdtop hdtop
  have hdd : (d⁻¹) ^ 4 * (d * d) = (d⁻¹) ^ 2 := by
    have h : (d⁻¹) ^ 4 * (d * d) = (d⁻¹) ^ 2 * ((d⁻¹ * d) * (d⁻¹ * d)) := by ring
    rw [h, ENNReal.inv_mul_cancel hdne hdtop, one_mul, mul_one]
  refine ennreal_le_of_mul_le_mul_right hmul hmultop ?_
  calc ((bd.bodies B).card : ENNReal) * (d * d)
      ≤ bodiesCardConst bd.C₀ bd.Cbias * (d⁻¹) ^ 2 := hstep
    _ = bodiesCardConst bd.C₀ bd.Cbias * (d⁻¹) ^ 4 * (d * d) := by rw [mul_assoc, hdd]


/-! ### G7b (ii): the thin constant with `bd.Cg` bounded rather than pinned -/

set_option maxHeartbeats 1000000 in
-- the proof threads one bit budget through eleven pipeline constants and closes with a
-- fourteen-step `calc` in `ℝ`; the default budget is not enough for a declaration of this size
-- (the same reason `Kakeya.VeryNotSticky.exists_thinConfig_le_of_card_bounds` carries it)
/-- **The `Kakeya.VeryNotSticky.BallData.Cg`-free half of
`Kakeya.VeryNotSticky.exists_thinConfig_le_of_card_bounds`**: the *thin setup constant* built from
the polylogarithmic core envelope is sub-polynomial in `δ⁻¹`, with no reference to `bd.Cg`.

This is the existing proof with the working constant `A` re-set from `Cg · sc3² · coreConst²` to
`sc3² · coreConst²` and the conclusion moved from `tc.C` to the constant itself; the `bd.Cg = Cg`
pin is thereby not used at all. Separating it is what makes the general branch possible: there
`bd.Cg` is only *bounded*, and a `δ`-free pin is
unavailable because the retention losses of the heavy balls, the Markov tier, Lemma 9.2's subset
and the dims class are polylogarithmic in `δ⁻¹`, not `≲ 1`. -/
theorem eventually_thinSetupConstant_le (ε : ℝ) (hε : 0 < ε)
    (C₀bd CF c₁ Csegs Cbodies : NNReal) (D Ksegs Kbodies : ℕ) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → bd.C₀ = C₀bd → bd.CF = CF → bd.c₁ = c₁ → bd.D = D →
      bd.Cm = 1 → cfg.δ ≤ bd.w₁ → bd.w₁ ≤ 1 →
      (∀ B ∈ bd.bs, (((bd.segs B).card : ℕ) : NNReal) ≤ Csegs * cfg.δ⁻¹ ^ Ksegs) →
      (∀ B ∈ bd.bs, (((bd.bodies B).card : ℕ) : NNReal) ≤ Cbodies * cfg.δ⁻¹ ^ Kbodies) →
      ThinCase.thinSetupConstant bd.C₀ bd.CF bd.c₁ (thinCoreEnvelope cfg bd) bd.D bd.Cm
        ≤ cfg.δ ^ (-ε) := by
  classical
  set A : NNReal := ThinSizing.sc3 C₀bd CF c₁ D ^ 2 * ThinSizing.coreConst ^ 2 with hAdef
  set K : ℕ := ThinCase.twoPowExponent CF + ThinCase.twoPowExponent (volume_comparison.C 3)
      + ThinCase.twoPowExponent C₀bd + ThinCase.twoPowExponent Csegs
      + ThinCase.twoPowExponent Cbodies with hKdef
  set J : ℕ := Ksegs + Kbodies + 1 with hJdef
  set A' : ℝ := max 1 ((A : ℝ) * ((K + J + 1 : ℕ) : ℝ) ^ 42) with hA'def
  obtain ⟨δ₀, hδ₀pos, hδ₀one, habs⟩ :=
    ThinSizing.polylog_pow_le A' (le_max_left _ _) 1 42 ε hε
  filter_upwards [eventually_le_nhdsGT' hδ₀pos] with δ hδle
  intro cfg bd hδeq hC₀ hCF hc₁ hD hCm hδw₁ hw₁one hsegs hbodies
  have hδ0 : 0 < cfg.δ := cfg.hδ
  have hδle' : cfg.δ ≤ δ₀ := by rw [hδeq]; exact hδle
  -- the bit budget
  set c : ℝ := ((cfg.δ⁻¹ : NNReal) : ℝ) with hc
  set Λ : ℕ := ⌊Real.logb 2 c⌋₊ + 1 with hΛdef
  have hΛ : cfg.δ⁻¹ ≤ 2 ^ Λ := ThinSizing.inv_le_two_pow_floor_logb hδ0
  set m : ℕ := J * Λ + K with hmdef
  have hJ1 : 1 ≤ J := by rw [hJdef]; omega
  have hΛ1 : 1 ≤ Λ := by rw [hΛdef]; omega
  have hJΛ : Λ ≤ J * Λ := by
    calc Λ = 1 * Λ := by ring
      _ ≤ J * Λ := Nat.mul_le_mul_right Λ hJ1
  have hKm : K ≤ m := by rw [hmdef]; omega
  have hsegsΛ : Ksegs * Λ ≤ J * Λ := Nat.mul_le_mul_right Λ (by rw [hJdef]; omega)
  have hbodiesΛ : Kbodies * Λ ≤ J * Λ := Nat.mul_le_mul_right Λ (by rw [hJdef]; omega)
  have hpow_mono : ∀ {j : ℕ}, j ≤ m → (2 : NNReal) ^ j ≤ 2 ^ m :=
    fun {j} hj => pow_le_pow_right₀ (by norm_num) hj
  have hΛm : Λ ≤ m := by rw [hmdef]; exact le_trans hJΛ (Nat.le_add_right _ _)
  have hδm : cfg.δ⁻¹ ≤ 2 ^ m := hΛ.trans (hpow_mono hΛm)
  have hCFm : bd.CF ≤ 2 ^ m := by
    rw [hCF]
    refine (ThinCase.le_two_pow_twoPowExponent CF).trans (hpow_mono ?_)
    refine le_trans ?_ hKm
    rw [hKdef]; omega
  have hVm : volume_comparison.C 3 ≤ 2 ^ m := by
    refine (ThinCase.le_two_pow_twoPowExponent _).trans (hpow_mono ?_)
    refine le_trans ?_ hKm
    rw [hKdef]; omega
  have hw0 : 0 < bd.w₁ := lt_of_lt_of_le hδ0 hδw₁
  have hwm : bd.w₁⁻¹ ≤ 2 ^ m := le_trans (inv_anti₀ hδ0 hδw₁) hδm
  have hC₀0 : 0 < bd.C₀ := lt_of_lt_of_le zero_lt_one bd.hC₀
  have hδC₀m : (cfg.δ / bd.C₀)⁻¹ ≤ 2 ^ m := by
    rw [inv_div]
    have h1 : bd.C₀ / cfg.δ = bd.C₀ * cfg.δ⁻¹ := by rw [div_eq_mul_inv]
    rw [h1, hC₀]
    have h2 : C₀bd * cfg.δ⁻¹ ≤ 2 ^ ThinCase.twoPowExponent C₀bd * 2 ^ Λ := by
      exact mul_le_mul' (ThinCase.le_two_pow_twoPowExponent C₀bd) hΛ
    refine h2.trans ?_
    rw [← pow_add]
    refine hpow_mono ?_
    rw [hmdef]
    calc ThinCase.twoPowExponent C₀bd + Λ ≤ K + J * Λ :=
          Nat.add_le_add (by rw [hKdef]; omega) hJΛ
      _ = J * Λ + K := Nat.add_comm _ _
  have hcard : ∀ (C : NNReal) (K' : ℕ) (x : NNReal), x ≤ C * cfg.δ⁻¹ ^ K' →
      ThinCase.twoPowExponent C + K' * Λ ≤ m → x ≤ 2 ^ m := by
    intro C K' x hx hle
    refine hx.trans ?_
    have h4 : cfg.δ⁻¹ ^ K' ≤ 2 ^ (K' * Λ) := by
      have := ThinSizing.pow_le_two_pow (x := cfg.δ⁻¹) (j := Λ) (n := K') hΛ
      simpa [Nat.mul_comm] using this
    refine le_trans (mul_le_mul' (ThinCase.le_two_pow_twoPowExponent C) h4) ?_
    rw [← pow_add]
    exact hpow_mono hle
  have hsegsm : ∀ B ∈ bd.bs, (((bd.segs B).card : ℕ) : NNReal) ≤ 2 ^ m := by
    intro B hB
    refine hcard Csegs Ksegs _ (hsegs B hB) ?_
    rw [hmdef]
    calc ThinCase.twoPowExponent Csegs + Ksegs * Λ ≤ K + J * Λ :=
          Nat.add_le_add (by rw [hKdef]; omega) hsegsΛ
      _ = J * Λ + K := Nat.add_comm _ _
  have hbodiesm : ∀ B ∈ bd.bs, (((bd.bodies B).card : ℕ) : NNReal) ≤ 2 ^ m := by
    intro B hB
    refine hcard Cbodies Kbodies _ (hbodies B hB) ?_
    rw [hmdef]
    calc ThinCase.twoPowExponent Cbodies + Kbodies * Λ ≤ K + J * Λ :=
          Nat.add_le_add (by rw [hKdef]; omega) hbodiesΛ
      _ = J * Λ + K := Nat.add_comm _ _
  -- the envelope is polylogarithmic
  have hcore := thinCoreEnvelope_le (cfg := cfg) (bd := bd) (m := m) hCFm hVm hw0 hw₁one hwm
    hδm hδC₀m hC₀0 hsegsm hbodiesm
  have h2core : (2 : NNReal) ≤ thinCoreEnvelope cfg bd := two_le_thinCoreEnvelope cfg bd
  have h1core : (1 : NNReal) ≤ thinCoreEnvelope cfg bd := le_trans one_le_two h2core
  set M : NNReal := ((m + 1 : ℕ) : NNReal) with hMdef
  have hM1 : (1 : NNReal) ≤ M := by rw [hMdef]; exact ThinSizing.one_le_M m
  -- the comparison constant is `A · M ^ 42`
  have hchain : ThinCase.thinSetupConstant bd.C₀ bd.CF bd.c₁ (thinCoreEnvelope cfg bd) bd.D bd.Cm
      ≤ A * M ^ 42 := by
    have hsetup : ThinCase.thinSetupConstant bd.C₀ bd.CF bd.c₁ (thinCoreEnvelope cfg bd) bd.D
        bd.Cm ≤ ThinSizing.sc3 bd.C₀ bd.CF bd.c₁ bd.D ^ 2 * thinCoreEnvelope cfg bd ^ 2 := by
      rw [hCm]
      exact ThinSizing.thinSetupConstant_le h1core
    calc ThinCase.thinSetupConstant bd.C₀ bd.CF bd.c₁ (thinCoreEnvelope cfg bd) bd.D bd.Cm
        ≤ ThinSizing.sc3 bd.C₀ bd.CF bd.c₁ bd.D ^ 2 * thinCoreEnvelope cfg bd ^ 2 := hsetup
      _ ≤ ThinSizing.sc3 bd.C₀ bd.CF bd.c₁ bd.D ^ 2 *
            (ThinSizing.coreConst * M ^ 21) ^ 2 := by
          gcongr
      _ = ThinSizing.sc3 C₀bd CF c₁ D ^ 2 * ThinSizing.coreConst ^ 2 * M ^ 42 := by
          rw [hC₀, hCF, hc₁, hD]
          ring
      _ = A * M ^ 42 := by rw [hAdef]
  -- absorption
  have hcnn : (0 : ℝ) ≤ c := by rw [hc]; exact NNReal.coe_nonneg _
  have hcK : c ≤ (cfg.δ : ℝ) ^ (-((1 : ℕ) : ℝ)) := by
    rw [Nat.cast_one, Real.rpow_neg_one, hc]
    push_cast
    exact le_rfl
  have hfinal := habs hδ0 hδle' c hcnn hcK
  have hMreal : ((M : NNReal) : ℝ) ≤ ((K + J + 1 : ℕ) : ℝ) * (Λ : ℝ) := by
    have hnat : m + 1 ≤ (K + J + 1) * Λ := by
      have hKΛ : K ≤ K * Λ := by
        calc K = K * 1 := by ring
          _ ≤ K * Λ := Nat.mul_le_mul_left K hΛ1
      calc m + 1 = J * Λ + K + 1 := by rw [hmdef]
        _ ≤ J * Λ + K * Λ + Λ := Nat.add_le_add (Nat.add_le_add_left hKΛ _) hΛ1
        _ = (K + J + 1) * Λ := by ring
    have := (Nat.cast_le (α := ℝ)).2 hnat
    rw [hMdef]
    push_cast at this ⊢
    linarith
  have hApos : (0 : ℝ) ≤ (A : ℝ) := NNReal.coe_nonneg _
  have hAbig : (A : ℝ) * ((K + J + 1 : ℕ) : ℝ) ^ 42 ≤ A' := by rw [hA'def]; exact le_max_right _ _
  have hA'1 : (1 : ℝ) ≤ A' := by rw [hA'def]; exact le_max_left _ _
  have hkey : ((ThinCase.thinSetupConstant bd.C₀ bd.CF bd.c₁ (thinCoreEnvelope cfg bd) bd.D
      bd.Cm : NNReal) : ℝ) ≤ (cfg.δ : ℝ) ^ (-ε) := by
    refine le_trans (NNReal.coe_le_coe.2 hchain) ?_
    have hMr : (0 : ℝ) ≤ ((M : NNReal) : ℝ) := NNReal.coe_nonneg _
    have hΛr : (0 : ℝ) ≤ (Λ : ℝ) := Nat.cast_nonneg _
    calc ((A * M ^ 42 : NNReal) : ℝ) = (A : ℝ) * ((M : NNReal) : ℝ) ^ 42 := by push_cast; ring
      _ ≤ (A : ℝ) * (((K + J + 1 : ℕ) : ℝ) * (Λ : ℝ)) ^ 42 := by
          gcongr
      _ = ((A : ℝ) * ((K + J + 1 : ℕ) : ℝ) ^ 42) * (Λ : ℝ) ^ 42 := by ring
      _ ≤ A' * (Λ : ℝ) ^ 42 := by gcongr
      _ ≤ A' ^ 42 * (Λ : ℝ) ^ 42 := by
          gcongr
          calc A' = A' ^ 1 := by ring
            _ ≤ A' ^ 42 := pow_le_pow_right₀ hA'1 (by norm_num)
      _ = (A' * (Λ : ℝ)) ^ 42 := by ring
      _ = (A' * ((⌊Real.logb 2 c⌋₊ : ℝ) + 1)) ^ 42 := by rw [hΛdef]; push_cast; ring
      _ ≤ (cfg.δ : ℝ) ^ (-ε) := hfinal
  rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
  exact hkey


/-- `Kakeya.VeryNotSticky.card_bodies_le_general` in the `NNReal` shape
`Kakeya.VeryNotSticky.exists_thinConfig_le_of_card_bounds_Cg_le` consumes, at `Kbodies = 4`. -/
theorem card_bodies_le_general_nnreal (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (hϱ1 : cfg.ϱ ≤ 1) {B : bd.bι} (hB : B ∈ bd.bs) :
    (((bd.bodies B).card : ℕ) : NNReal)
      ≤ bodiesCardConstNN bd.C₀ bd.Cbias * cfg.δ⁻¹ ^ 4 := by
  have hδ0 : (0 : NNReal) < cfg.δ := cfg.hδ
  have h := card_bodies_le_general cfg bd hϱ1 hB
  rw [← coe_bodiesCardConstNN, ← ENNReal.coe_inv hδ0.ne', ← ENNReal.coe_pow,
    ← ENNReal.coe_mul] at h
  have hcast : ((bd.bodies B).card : ENNReal)
      = (((((bd.bodies B).card : ℕ) : NNReal)) : ENNReal) := by simp
  rw [hcast, ENNReal.coe_le_coe] at h
  exact h

/-- **G7b (ii): the thin configuration with sub-polynomial comparison constant, when `bd.Cg` is
only bounded.** `bd.Cg ≤ δ^{-εg}` with `εg < ε` in place of the existing pin `bd.Cg = Cg`; the two
exponents add. No positivity of `εg` is needed: at `εg ≤ 0` the hypothesis is only stronger. -/
theorem exists_thinConfig_le_of_card_bounds_Cg_le (ε εg : ℝ) (hlt : εg < ε)
    (C₀bd CF c₁ Csegs Cbodies : NNReal) (D Ksegs Kbodies : ℕ) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → bd.C₀ = C₀bd → bd.CF = CF → bd.c₁ = c₁ → bd.D = D →
      bd.Cg ≤ cfg.δ ^ (-εg) →
      bd.Cm = 1 → cfg.δ ≤ bd.w₁ → bd.w₁ ≤ 1 →
      (∀ B ∈ bd.bs, (((bd.segs B).card : ℕ) : NNReal) ≤ Csegs * cfg.δ⁻¹ ^ Ksegs) →
      (∀ B ∈ bd.bs, (((bd.bodies B).card : ℕ) : NNReal) ≤ Cbodies * cfg.δ⁻¹ ^ Kbodies) →
      ∃ tc : ThinConfig cfg bd, tc.C ≤ cfg.δ ^ (-ε) := by
  filter_upwards [eventually_thinSetupConstant_le.{u} (ε - εg) (by linarith) C₀bd CF c₁
    Csegs Cbodies D Ksegs Kbodies] with δ hset
  intro cfg bd hδ hC₀ hCF hc₁ hD hCg hCm hδw₁ hw₁one hsegs hbodies
  have hdne : cfg.δ ≠ 0 := cfg.hδ.ne'
  obtain ⟨tc, htc⟩ := exists_thinConfig_C_le cfg bd hδw₁ hw₁one
  refine ⟨tc, htc.trans ?_⟩
  have h := hset cfg bd hδ hC₀ hCF hc₁ hD hCm hδw₁ hw₁one hsegs hbodies
  calc bd.Cg * ThinCase.thinSetupConstant bd.C₀ bd.CF bd.c₁ (thinCoreEnvelope cfg bd) bd.D bd.Cm
      ≤ cfg.δ ^ (-εg) * cfg.δ ^ (-(ε - εg)) := by gcongr
    _ = cfg.δ ^ (-ε) := by
        rw [← NNReal.rpow_add hdne]
        congr 1
        ring

/-- **G7b (i)+(ii) composed**: the thin configuration with `tc.C ≤ δ^{-ε}` at general `(a, b)`,
from the general body count and the `Cg`-bounded producer. This is the general twin of
`Kakeya.VeryNotSticky.thinConstantObligation_of_le_one`; the side conditions `η ≤ 1`, `ϱ ≤ 1` are
`Kakeya.VeryNotSticky.CaseParams.eta_le_one` and `Kakeya.VeryNotSticky.CaseParams.rho_le_one` at
the call site. -/
theorem eventually_exists_thinConfig_le_general (ε εg η ϱ : ℝ) (hlt : εg < ε)
    (hη1 : η ≤ 1) (hϱ1 : ϱ ≤ 1) (C₀bd Cbias CF c₁ : NNReal) (D : ℕ) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.ϱ = ϱ →
      bd.C₀ = C₀bd → bd.Cbias = Cbias → bd.CF = CF → bd.c₁ = c₁ →
      bd.D = D → bd.Cg ≤ cfg.δ ^ (-εg) → bd.Cm = 1 → cfg.δ ≤ bd.w₁ → bd.w₁ ≤ 1 →
      ∃ tc : ThinConfig cfg bd, tc.C ≤ cfg.δ ^ (-ε) := by
  filter_upwards [exists_thinConfig_le_of_card_bounds_Cg_le.{u} ε εg hlt C₀bd CF c₁ 1
      (bodiesCardConstNN C₀bd Cbias) D 4 4,
    eventually_card_segs_le.{u} (η := η) hη1] with δ hred hseg
  intro cfg bd hδ hη hϱ hC₀ hCbias hCF hc₁ hD hCg hCm hδw₁ hw₁one
  refine hred cfg bd hδ hC₀ hCF hc₁ hD hCg hCm hδw₁ hw₁one (hseg cfg bd hδ hη) ?_
  intro B hB
  have hϱ1' : cfg.ϱ ≤ 1 := by rw [hϱ]; exact hϱ1
  have h := card_bodies_le_general_nnreal cfg bd hϱ1' hB
  rwa [hC₀, hCbias] at h


/-! ### G7: the three thresholds of conjunct 2, at general `(a, b)` -/

/-- **G7 + G7b: conjunct 2's three thresholds at general `(a, b)`.**

The conclusion is that of `Kakeya.VeryNotSticky.sideDataObligations_conjunct2` **verbatim**; the
binders differ in exactly three places, and those three are the interface SP-A must adopt for
conjunct 2:

* `cfg.a = cfg.δ → cfg.b = cfg.δ` is replaced by `cfg.a ≤ cfg.δ ^ (1 - τ)` (the thin guard; the
  `hdims` bracket `δ ≤ a ≤ b ≤ δ^{exscal}` is already a field of `Kakeya.VeryNotSticky`);
* `bd.Cg = Cg` is replaced by `bd.Cg ≤ cfg.δ ^ (-εg)`, and the `δ`-free parameter `Cg` disappears
  from the statement (/§6, form (c));
* the new parameter `εg` carries the side condition
  `εg < Kakeya.VeryNotSticky.thresholdExponent β exscal η τ`.

Everything else — `SlabScale cfg bd tc τ`, `CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr₀` and
the tangential density threshold — is unchanged, and so are the constant pins. -/
theorem eventually_thresholds_general {β ζ exscal ϱ η τ τ' : ℝ}
    (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    {C₀bd Cbias CF Cdil c₁ : NNReal} (hC₀bd : 1 ≤ C₀bd) {D : ℕ}
    {εg : ℝ} (hεg : εg < thresholdExponent β exscal η τ) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
    cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
    cfg.a ≤ cfg.δ ^ (1 - τ) →
    bd.C₀ = C₀bd → bd.Cbias = Cbias → bd.CF = CF → bd.Cdil ≤ Cdil → bd.c₁ = c₁ → bd.D = D →
    bd.Cg ≤ cfg.δ ^ (-εg) → bd.Cm = 1 →
    (bd.Cm : ENNReal) * (bd.m : ENNReal) ≤
      (fibreMassConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) →
    cfg.δ ≤ bd.w₁ → bd.w₁ ≤ 1 →
    ∃ (tc : ThinConfig cfg bd) (thr₀ : ScaleThresholds),
      SlabScale cfg bd tc τ ∧
      CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr₀ ∧
      ((tangentialSlabDecompConstant tc.C : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := by
  set ε := thresholdExponent β exscal η τ with hεdef
  have hε := thresholdExponent_pos hη params
  have hεd := thresholdExponent_le_density β exscal η τ
  have hεf := thresholdExponent_le_final β exscal η τ
  have hεη := thresholdExponent_le_eta β exscal η τ
  rw [← hεdef] at hε hεd hεf hεη
  have hslabDensity := params.slabDensity
  have hslab := params.slab
  have hscale := params.scale
  have hτ := params.hτ
  have hτ' := params.hτ'
  have hanti : 2 * ϱ < exscal := by
    have h := params.slabBias
    rw [parameterSeparationConstant] at h
    nlinarith
  have hbud : 6 * η + ε < 16 * η * (1 - τ - exscal) :=
    o5_budget_of_thinHalf hη params.thinHalf (by linarith)
  filter_upwards [eventually_exists_thinConfig_le_general.{u} ε εg η ϱ hεg
      (params.eta_le_one hη) params.rho_le_one C₀bd Cbias CF c₁ D,
    eventually_slabScale_of_C_le.{u} (β := β) (exscal := exscal) (η := η) (ϱ := ϱ) (τ := τ)
      (ε := ε) C₀bd Cbias Cdil (by linarith) hanti (by linarith),
    eventually_caseScale_of_C_le_general.{u} C₀bd Cbias hC₀bd (exscal := exscal) (η := η)
      (ϱ := ϱ) (τ := τ) (τ' := τ') (ν := τ' * β / 2) (ε := ε) hexscal (by linarith) hη hϱ
      (by linarith) params.thinScale (by linarith) hbud,
    eventually_densityConstant_of_C_le (η := η) (ε := ε) (by linarith)] with
    d hC hslabS hcaseS hdens
  intro cfg bd hδ hβ hη' hex hϱ' hthin hC₀ hCb hCF hCdil hc₁ hD hCg hCm hSPH hδw₁ hw₁
  obtain ⟨tc, htc⟩ := hC cfg bd hδ hη' hϱ' hC₀ hCb hCF hc₁ hD hCg hCm hδw₁ hw₁
  rw [hδ] at htc
  have h1C : 1 ≤ tc.C := by
    obtain ⟨B, hB⟩ := bd.bs_nonempty
    exact (tc.tb B hB).one_le_C
  refine ⟨tc, unitScaleThresholds, ?_, ?_, ?_⟩
  · exact hslabS cfg bd tc hδ hβ hex hη' hϱ' hC₀ hCb hCdil hSPH h1C htc
  · rw [hβ]
    exact hcaseS cfg bd unitScaleThresholds tc.C hδ hex hη' hϱ' hC₀ hCb hthin h1C htc
      (by simpa using cfg.hδ1) (by simpa using cfg.hδ1)
  · rw [hδ, hη']
    exact hdens tc.C htc


/-! ### The specialisation control: the general form subsumes the existing conjunct -/

/-- **The existing conjunct 2, re-derived from the general theorem.**

Its statement is `Kakeya.VeryNotSticky.sideDataObligations_conjunct2`'s, character for character;
the point is the *proof*, which is the two-goal specialisation `cfg.a = cfg.δ ⇒ thin guard` (by
`Kakeya.VeryNotSticky.CaseParams.hτ`) and `bd.Cg = Cg ⇒ bd.Cg ≤ δ^{-εg}` (by
`Kakeya.VeryNotSticky.eventually_nnreal_le_rpow_neg` at `εg := thresholdExponent/2`). It is the
compiled evidence that `eventually_thresholds_general` **generalises** the existing conjunct rather
than diverging from it, and it bounds the wiring cost of SP-A's conjunct-2 row from above.

The duplication with the existing theorem is deliberate: this is a control, not a second producer. -/
theorem sideDataObligations_conjunct2_of_general {β ζ exscal ϱ η τ τ' : ℝ}
    (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    {C₀bd Cbias CF Cdil c₁ Cg : NNReal} (hC₀bd : 1 ≤ C₀bd) {D : ℕ} :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
    cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
    cfg.a = cfg.δ → cfg.b = cfg.δ →
    bd.C₀ = C₀bd → bd.Cbias = Cbias → bd.CF = CF → bd.Cdil = Cdil → bd.c₁ = c₁ → bd.D = D →
    bd.Cg = Cg → bd.m = 1 → bd.Cm = 1 → cfg.δ ≤ bd.w₁ → bd.w₁ ≤ 1 →
    ∃ (tc : ThinConfig cfg bd) (thr₀ : ScaleThresholds),
      SlabScale cfg bd tc τ ∧
      CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr₀ ∧
      ((tangentialSlabDecompConstant tc.C : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := by
  have hεpos : (0 : ℝ) < thresholdExponent β exscal η τ := thresholdExponent_pos hη params
  have hτ := params.hτ
  filter_upwards [eventually_thresholds_general.{u} hexscal hϱ hη params (C₀bd := C₀bd)
      (Cbias := Cbias) (CF := CF) (Cdil := Cdil) (c₁ := c₁) hC₀bd (D := D)
      (εg := thresholdExponent β exscal η τ / 2) (by linarith),
    eventually_nnreal_le_rpow_neg Cg (show (0 : ℝ) < thresholdExponent β exscal η τ / 2 by
      linarith)] with d hgen hCgle
  intro cfg bd hδ hβ hη' hex hϱ' ha hb hC₀ hCb hCF hCdil hc₁ hD hCg hm hCm hδw₁ hw₁
  refine hgen cfg bd hδ hβ hη' hex hϱ' ?_ hC₀ hCb hCF hCdil.le hc₁ hD ?_ hCm
    (fibreBudget_of_pins hm hCm) hδw₁ hw₁
  · rw [ha]
    nth_rewrite 1 [show cfg.δ = cfg.δ ^ (1 : ℝ) from (NNReal.rpow_one _).symm]
    exact NNReal.rpow_le_rpow_of_exponent_ge cfg.hδ cfg.hδ1 (by linarith)
  · rw [hCg, hδ]
    exact hCgle

/-- Tripwire: the general theorem's specialisation slots into the second component of
`Kakeya.VeryNotSticky.SideDataObligations` by the anonymous constructor, the other five conjuncts
taken from any witness. This fails to elaborate the moment either conjunct 2's text or the general
theorem's conclusion moves. -/
example {β ζ exscal ϱ η τ τ' : ℝ} (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    {C₀bd Cbias CF Cdil c₁ Cg : NNReal} (hC₀bd : 1 ≤ C₀bd) {D : ℕ}
    (hall : SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D) :
    SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D :=
  ⟨hall.1, sideDataObligations_conjunct2_of_general hexscal hϱ hη params hC₀bd,
    hall.2.2.1, hall.2.2.2.1, hall.2.2.2.2⟩

end Kakeya.VeryNotSticky
