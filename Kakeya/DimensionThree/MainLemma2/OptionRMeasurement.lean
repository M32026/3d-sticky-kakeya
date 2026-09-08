/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.TangentialSlabFamily

/-!
# Threshold-to-loss ratios in the tangential case

GWZ choose `η_bias` before `τ' ≪ η(η_bias, β)`
(`gwz.txt` l.2392-2396). This file studies the scalar restrictions
needed to express that order in the window parameters.

1. `hwe_rederives_without_rhoLeTau` derives the consumer bound
   `we ≤ ν/180`, at `ν = ϱβτ/8`, from
   `we ≤ ϱ² wb/1440` and `ϱ * wb ≤ β * τ`. It does not use
   `CaseParams.rhoLeTau`.
2. `optionR_forces_threshold_floor` combines
   `c * τ' ≤ exscal * wη`, `wη ≤ Λ * we`,
   `we ≤ ϱβτ/1440`, and `τ < τ'` to obtain
   `1440 * c ≤ exscal * Λ * β * ϱ`. This is a lower bound
   on the threshold-to-loss ratio `Λ`; removing `ϱ ≤ τ` does
   not remove it.
3. `optionR_floor_vs_tangential` uses `CaseParams.tangential`
   to derive `1440 * c * 2^21 ≤ exscal² * β² * ζ * Λ`.
   `ζ` is universally quantified in `exists_caseParams`, and
   `optionR_witness_tangential` and `optionR_floor_fails_at_witness`
   exhibit admissible scalar data violating this bound.

`CoarseKTWindow` is indexed by `(β, ϱ, η, exscal)` and does not
contain `τ'`. It can express `c * we ≤ 2^18 * wη` using its
existing fields; the form involving `τ'` requires data carrying
both `τ'` and `wη`.

`exists_uniformWindowPair` takes a positive loss `ε` as input
and returns a pair `(wη, wρ)`. Its conclusion contains no
comparison of `ε` with `wη`. Such a ratio condition is therefore
additional quantitative information about the threshold function,
not a consequence of this quantifier order alone.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open scoped NNReal

/-- **Finding 1 — Option R's priced cost is payable.** The consumer bound `we ≤ ν/180` at the
thick gain `ν = ϱβτ/8` follows from `Kakeya.CoarseKTWindow.hwe` and a re-cut of `hwb`
(`ϱ · wb ≤ β · τ` in place of `wb ≤ β`), with `Kakeya.VNSUniform.CaseParams.rhoLeTau` nowhere in
the derivation. Thus this estimate requires no `rhoLeTau` hypothesis. -/
theorem hwe_rederives_without_rhoLeTau
    {we ϱ wb β τ : ℝ} (hϱ0 : 0 < ϱ)
    (hwe : we ≤ ϱ ^ 2 * wb / 1440) (hwb' : ϱ * wb ≤ β * τ) :
    we ≤ ϱ * β * τ / 1440 := by
  have h : ϱ ^ 2 * wb = ϱ * (ϱ * wb) := by ring
  nlinarith [hwe, hwb', hϱ0]

/-- **Finding 2 — the real blocker, and `rhoLeTau` is not it.** From Option R's clause
`c τ' ≤ exscal · wη`, the shape of GWZ Remark 3.6's threshold `wη ≤ Λ · we`, the consumer bound
`we ≤ ϱβτ/1440` that `Kakeya.CoarseKTWindow.hwe` exists to serve, and `τ < τ'`, one gets a floor
on the Katz–Tao threshold-to-loss ratio `Λ = wη/we`. **`ϱ ≤ τ` is used nowhere**, so dropping
`Kakeya.VNSUniform.CaseParams.rhoLeTau` — the whole of Option R's re-parametrisation — does not
remove it: the same `τ` re-enters through `hwe`'s own consumer requirement. -/
theorem optionR_forces_threshold_floor
    {c τ τ' exscal wη Λ we ϱ β : ℝ}
    (hc : 0 < c) (hτ : 0 < τ) (hexscal : 0 < exscal)
    (hR : c * τ' ≤ exscal * wη)
    (hΛ : wη ≤ Λ * we)
    (hwe : we ≤ ϱ * β * τ / 1440)
    (hττ' : τ < τ')
    (hexΛ : 0 ≤ exscal * Λ) :
    1440 * c ≤ exscal * Λ * β * ϱ := by
  have h1 : c * τ < c * τ' := by nlinarith
  have h2 : exscal * wη ≤ exscal * (Λ * we) := by nlinarith
  have h3 : exscal * (Λ * we) ≤ exscal * (Λ * (ϱ * β * τ / 1440)) := by nlinarith
  nlinarith [h1, h2, h3, hR]

/-- **Finding 2′ — the same, with no assumption on the threshold function at all: Option R's
clause *is* the window ratio.**

Eliminate `τ` and `τ'` between Option R's clause `c τ' ≤ exscal · wη` and the thick-gain consumer
bound `we ≤ ϱβτ/1440` that `Kakeya.CoarseKTWindow.hwe` exists to serve, using only `τ < τ'`:

`1440 · c · we ≤ exscal · ϱ · β · wη` .

This is 's `c · we ≤ 2¹⁸ · wη` re-derived **from Option R's own clause**, and it
needs neither `wη ≤ Λ · we` nor `ϱ ≤ τ`. So Option R does not *escape* the loss-to-fullness ratio
of §2.4 — **it is that ratio**, written in the parameters `τ, τ'` instead of in `we, wη`. Since
`Kakeya.exists_uniformWindowPair` relates its input loss to its output pair by nothing
(module docstring), neither form is supplied, and re-parametrising `τ, τ'` cannot make it so. -/
theorem optionR_is_the_window_ratio
    {c τ τ' exscal wη we ϱ β : ℝ}
    (hc : 0 < c) (hϱ0 : 0 ≤ ϱ) (hβ0 : 0 ≤ β)
    (hR : c * τ' ≤ exscal * wη)
    (hwe : we ≤ ϱ * β * τ / 1440)
    (hττ' : τ < τ') :
    1440 * c * we ≤ exscal * ϱ * β * wη := by
  have hτ : c * τ ≤ exscal * wη := by nlinarith
  nlinarith [hwe, hτ, mul_nonneg hϱ0 hβ0]

/-- **Finding 3 — the floor against `Kakeya.VNSUniform.CaseParams.tangential`.** `tangential`
bounds `ϱ` above by `exscal β ζ / 2²¹`, so the floor becomes `1440 c 2²¹ ≤ exscal² β² ζ Λ`. Since
`ζ` is **universally quantified** in `Kakeya.VeryNotSticky.exists_caseParams`
(`∃ exscal > 0, ∀ ζ > 0, ∃ τ τ' ϱ η, …`), no bound of this shape can hold for every `ζ`. -/
theorem optionR_floor_vs_tangential
    {c exscal Λ β ϱ τ' ζ : ℝ}
    (hfloor : 1440 * c ≤ exscal * Λ * β * ϱ)
    (htang : parameterSeparationConstant * (ϱ + τ') < exscal * β * ζ / 2)
    (hτ'0 : 0 < τ') (hexscal : 0 < exscal) (hΛ0 : 0 ≤ Λ) (hβ0 : 0 < β) :
    1440 * c * 2 ^ 21 ≤ exscal * exscal * (β * β) * ζ * Λ := by
  have hps : parameterSeparationConstant = 2 ^ 20 := rfl
  rw [hps] at htang
  have hϱ : ϱ < exscal * β * ζ / 2 ^ 21 := by nlinarith
  nlinarith [hfloor, hϱ, mul_nonneg (mul_nonneg hexscal.le hΛ0) hβ0.le]

/-- The numeral witness: `Kakeya.VNSUniform.CaseParams.tangential` holds at
`ϱ = τ' = 10⁻¹²`, `exscal = β = 1/100`, `ζ = 1`. -/
theorem optionR_witness_tangential :
    parameterSeparationConstant * ((1 / 1000000000000 : ℝ) + 1 / 1000000000000)
      < (1 / 100 : ℝ) * (1 / 100) * 1 / 2 := by
  have hps : parameterSeparationConstant = 2 ^ 20 := rfl
  rw [hps]; norm_num

/-- …and at the same numerals, with the entirely admissible window ratio `Λ = 1` (nothing in
`Kakeya.CoarseKTWindow` forbids `wη ≤ we`), the floor of finding 2 **fails**. So Option R's
clause is not satisfiable at an admissible package unless the Katz–Tao threshold function is
given a floor in terms of its own loss — which `Kakeya.exists_uniformWindowPair` does not
supply. -/
theorem optionR_floor_fails_at_witness :
    ¬ (1440 * (1 : ℝ) ≤ (1 / 100 : ℝ) * 1 * (1 / 100) * (1 / 1000000000000)) := by
  norm_num

end Kakeya.VeryNotSticky
