/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The `⪅` ("less than or approximately") notation

Many estimates in the proof are only true up to factors of the form `log (1 / δ)` or
`log |𝒱|`, which are harmless distractions. To streamline these arguments we follow
the convention that, when `X` and `Y` are quantities depending on an (often implicit)
parameter `ρ : ℝ≥0`, we write

  `X ⪅ Y`

to mean that for every `ε > 0` there is a constant `C = C ε` such that
`X ρ ≤ C * ρ ^ (-ε) * Y ρ` for all `0 < ρ ≤ 1`. Since `ρ ^ (-ε) → 1` as `ε → 0`, this absorbs
any sub-polynomial loss (such as the logarithmic factors above) into the inequality.

(The bound is only required for `0 < ρ ≤ 1`, matching the intended domain: `ρ` is always a
ratio in `(0, 1]` such as `δ`, `|𝒱|⁻¹`, or `a / A`. Requiring it at `ρ = 0` would force
`X 0 = 0`, since `(0 : ℝ≥0) ^ (-ε) = 0`; and requiring it for large `ρ` would make the
`ρ ^ (-ε)` factor a gain rather than a loss, so that e.g. `log (1 / ρ) ⪅ 1` would fail.)

This file defines this relation as `LEApprox` and introduces the scoped notation `X ⪅ Y`
for it (together with the reversed `X ⪆ Y`).

Alongside `⪅` we also define the coarser, constant-factor relations that appear in the same
arguments:

* `X ≲ Y` (`LEsssim`): `X ρ ≤ C * Y ρ` for some constant `C` and all `0 < ρ ≤ 1`. This is the
  usual harmonic-analysis convention, hiding only absolute constants (those allowed to depend
  on fixed parameters such as the dimension, but not on `ρ`). It carries no `ρ ^ (-ε)` factor.
* `X ∼ Y` (`Comparable`): the two-sided version of `≲`, i.e. `X ≲ Y` and `Y ≲ X`.
* `X ≈ Y` (`ApproxEq`): the two-sided version of `⪅`, i.e. `X ⪅ Y` and `Y ⪅ X`.
-/

namespace Kakeya

@[expose] public section

open scoped NNReal

/-- `LEApprox X Y` (notation `X ⪅ Y`) holds when, for every `ε > 0`, there is a constant
`C` such that `X ρ ≤ C * ρ ^ (-ε) * Y ρ` for all `ρ : ℝ≥0` with `0 < ρ ≤ 1`.

Here `X Y : ℝ≥0 → ℝ≥0` are thought of as quantities depending on an implicit parameter
`ρ`. The factor `ρ ^ (-ε)` lets the bound absorb any sub-polynomial loss (e.g. factors of
`log (1 / δ)` or `log |𝒱|`) uniformly in `ρ`; this is why the bound is only asked for on the
intended domain `0 < ρ ≤ 1`, where `ρ ^ (-ε) ≥ 1`.

See also `Kakeya.LEApproxWith` for the variant `X ⪅[C] Y` that names the constant. -/
def LEApprox (X Y : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ ρ : ℝ≥0, 0 < ρ → ρ ≤ 1 → X ρ ≤ C * ρ ^ (-ε) * Y ρ

@[inherit_doc]
scoped infix:50 " ⪅ " => LEApprox

/-- `X ⪆ Y` means `Y ⪅ X`; see `Kakeya.LEApprox`. -/
scoped infix:50 " ⪆ " => fun X Y => LEApprox Y X

/-- `LEApproxWith C X Y` (notation `X ⪅[C] Y`) is the explicit-constant form of `X ⪅ Y`:
for every `ε > 0` and every `0 < ρ ≤ 1` we have `X ρ ≤ C ε * ρ ^ (-ε) * Y ρ`.

The constant is allowed to depend on `ε`, hence `C : ℝ → ℝ≥0`. This mirrors the relationship
between `Asymptotics.IsBigO` and `Asymptotics.IsBigOWith`: `X ⪅ Y` holds exactly when
`X ⪅[C] Y` does for some `C` (see `Kakeya.leApprox_iff_exists_leApproxWith`).

See also `Kakeya.LEApprox` for the variant `X ⪅ Y` that leaves the constant existentially
quantified. -/
def LEApproxWith (C : ℝ → ℝ≥0) (X Y : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ ρ : ℝ≥0, 0 < ρ → ρ ≤ 1 → X ρ ≤ C ε * ρ ^ (-ε) * Y ρ

@[inherit_doc]
scoped notation:50 X:51 " ⪅[" C "] " Y:51 => LEApproxWith C X Y

/-- `X ⪅ Y` holds iff `X ⪅[C] Y` holds for some constant `C : ℝ → ℝ≥0`. -/
theorem leApprox_iff_exists_leApproxWith {X Y : ℝ≥0 → ℝ≥0} :
    X ⪅ Y ↔ ∃ C : ℝ → ℝ≥0, X ⪅[C] Y := by
  classical
  constructor
  · intro h
    choose C hC using h
    exact ⟨fun ε => if hε : 0 < ε then C ε hε else 0,
      fun ε hε ρ hρ hρ1 => by simpa [dif_pos hε] using hC ε hε ρ hρ hρ1⟩
  · rintro ⟨C, hC⟩ ε hε
    exact ⟨C ε, fun ρ hρ hρ1 => hC ε hε ρ hρ hρ1⟩

/-- `LEsssim X Y` (notation `X ≲ Y`) holds when there is a constant `C` such that
`X ρ ≤ C * Y ρ` for all `ρ : ℝ≥0` with `0 < ρ ≤ 1`.

This is the constant-factor relation of harmonic analysis: `X ≲ Y` means `X` is bounded by
`Y` up to an absolute constant (one allowed to depend on fixed parameters such as the
dimension, but not on `ρ`). Unlike `Kakeya.LEApprox`, it carries no `ρ ^ (-ε)` factor. The
domain is `0 < ρ ≤ 1`, as for `Kakeya.LEApprox`.

See `Kakeya.LEApprox` for the sub-polynomial variant `X ⪅ Y`, and `Kakeya.LEsssimWith` for the
variant `X ≲[C] Y` that names the constant. -/
def LEsssim (X Y : ℝ≥0 → ℝ≥0) : Prop :=
  ∃ C : ℝ≥0, ∀ ρ : ℝ≥0, 0 < ρ → ρ ≤ 1 → X ρ ≤ C * Y ρ

@[inherit_doc]
scoped infix:50 " ≲ " => LEsssim

/-- `X ≳ Y` means `Y ≲ X`; see `Kakeya.LEsssim`. -/
scoped infix:50 " ≳ " => fun X Y => LEsssim Y X

/-- `LEsssimWith C X Y` (notation `X ≲[C] Y`) is the explicit-constant form of `X ≲ Y`:
for every `0 < ρ ≤ 1` we have `X ρ ≤ C * Y ρ`.

This mirrors the relationship between `Asymptotics.IsBigO` and `Asymptotics.IsBigOWith`:
`X ≲ Y` holds exactly when `X ≲[C] Y` does for some `C` (see
`Kakeya.lesssim_iff_exists_lesssimWith`).

See also `Kakeya.LEsssim` for the variant `X ≲ Y` that leaves the constant existentially
quantified. -/
def LEsssimWith (C : ℝ≥0) (X Y : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ ρ : ℝ≥0, 0 < ρ → ρ ≤ 1 → X ρ ≤ C * Y ρ

@[inherit_doc]
scoped notation:50 X:51 " ≲[" C "] " Y:51 => LEsssimWith C X Y

/-- `X ≲ Y` holds iff `X ≲[C] Y` holds for some constant `C : ℝ≥0`. -/
theorem lesssim_iff_exists_lesssimWith {X Y : ℝ≥0 → ℝ≥0} :
    X ≲ Y ↔ ∃ C : ℝ≥0, X ≲[C] Y := Iff.rfl

/-- `Comparable X Y` (notation `X ∼ Y`) holds when `X ≲ Y` and `Y ≲ X`, i.e. `X` and `Y` agree
up to absolute constants in both directions.

This is the two-sided version of `Kakeya.LEsssim`. For example, "each tube lies in `∼ 1` of the
sets" means the count is bounded above and below by absolute constants.

See `Kakeya.ComparableWith` for the variant `X ∼[C₁, C₂] Y` that names the constants. -/
def Comparable (X Y : ℝ≥0 → ℝ≥0) : Prop :=
  X ≲ Y ∧ Y ≲ X

@[inherit_doc]
scoped infix:50 " ∼ " => Comparable

/-- `ComparableWith C₁ C₂ X Y` (notation `X ∼[C₁, C₂] Y`) is the explicit-constant form of
`X ∼ Y`: we have `X ≲[C₁] Y` and `Y ≲[C₂] X`.

This is the two-sided version of `Kakeya.LEsssimWith`: `X ∼ Y` holds exactly when
`X ∼[C₁, C₂] Y` does for some constants `C₁ C₂` (see
`Kakeya.comparable_iff_exists_comparableWith`). -/
def ComparableWith (C₁ C₂ : ℝ≥0) (X Y : ℝ≥0 → ℝ≥0) : Prop :=
  X ≲[C₁] Y ∧ Y ≲[C₂] X

@[inherit_doc]
scoped notation:50 X:51 " ∼[" C₁ ", " C₂ "] " Y:51 => ComparableWith C₁ C₂ X Y

/-- `X ∼ Y` holds iff `X ∼[C₁, C₂] Y` holds for some constants `C₁ C₂ : ℝ≥0`. -/
theorem comparable_iff_exists_comparableWith {X Y : ℝ≥0 → ℝ≥0} :
    X ∼ Y ↔ ∃ C₁ C₂ : ℝ≥0, X ∼[C₁, C₂] Y := by
  constructor
  · rintro ⟨⟨C₁, h₁⟩, C₂, h₂⟩
    exact ⟨C₁, C₂, h₁, h₂⟩
  · rintro ⟨C₁, C₂, h₁, h₂⟩
    exact ⟨⟨C₁, h₁⟩, C₂, h₂⟩

/-- `ApproxEq X Y` (notation `X ≈ Y`) holds when `X ⪅ Y` and `Y ⪅ X`, i.e. `X` and `Y` agree up
to sub-polynomial factors `C_ε * ρ ^ (-ε)` in both directions.

This is the two-sided version of `Kakeya.LEApprox`. For example, a `≈ 1`-refinement keeps all
but a sub-polynomial fraction of the total shading mass.

See `Kakeya.ApproxEqWith` for the variant `X ≈[C₁, C₂] Y` that names the constants. -/
def ApproxEq (X Y : ℝ≥0 → ℝ≥0) : Prop :=
  X ⪅ Y ∧ Y ⪅ X

@[inherit_doc]
scoped infix:50 " ≈ " => ApproxEq

/-- `ApproxEqWith C₁ C₂ X Y` (notation `X ≈[C₁, C₂] Y`) is the explicit-constant form of
`X ≈ Y`: we have `X ⪅[C₁] Y` and `Y ⪅[C₂] X`.

This is the two-sided version of `Kakeya.LEApproxWith`: `X ≈ Y` holds exactly when
`X ≈[C₁, C₂] Y` does for some constants `C₁ C₂ : ℝ → ℝ≥0` (see
`Kakeya.approxEq_iff_exists_approxEqWith`). -/
def ApproxEqWith (C₁ C₂ : ℝ → ℝ≥0) (X Y : ℝ≥0 → ℝ≥0) : Prop :=
  X ⪅[C₁] Y ∧ Y ⪅[C₂] X

@[inherit_doc]
scoped notation:50 X:51 " ≈[" C₁ ", " C₂ "] " Y:51 => ApproxEqWith C₁ C₂ X Y

/-- `X ≈ Y` holds iff `X ≈[C₁, C₂] Y` holds for some constants `C₁ C₂ : ℝ → ℝ≥0`. -/
theorem approxEq_iff_exists_approxEqWith {X Y : ℝ≥0 → ℝ≥0} :
    X ≈ Y ↔ ∃ C₁ C₂ : ℝ → ℝ≥0, X ≈[C₁, C₂] Y := by
  constructor
  · rintro ⟨hXY, hYX⟩
    obtain ⟨C₁, hC₁⟩ := leApprox_iff_exists_leApproxWith.1 hXY
    obtain ⟨C₂, hC₂⟩ := leApprox_iff_exists_leApproxWith.1 hYX
    exact ⟨C₁, C₂, hC₁, hC₂⟩
  · rintro ⟨C₁, C₂, hC₁, hC₂⟩
    exact ⟨leApprox_iff_exists_leApproxWith.2 ⟨C₁, hC₁⟩,
      leApprox_iff_exists_leApproxWith.2 ⟨C₂, hC₂⟩⟩

/-!
## The basic calculus of `⪅`

The following elementary facts are used wherever `⪅` is manipulated: the loss factor is really a
loss on the intended domain, `⪅` is monotone in its left argument, and `⪅ 1` is stable under
adding and multiplying by constants and (given a positive lower bound) under taking reciprocals.

They are followed by the logarithmic estimates that make `⪅` useful in the first place: the
unbounded loss `log₂ (1 / ρ)` is `⪅ 1`, and the logarithm of a ratio splits pointwise into a
constant part and such a logarithmic part. Combining the two gives
`Kakeya.toNNReal_logb_div_leApprox_one`: if `b / a ≲ ρ⁻¹` then `(log₂ (b / a))₊ ⪅ 1`.
-/

/-- **The loss factor is at least `1` on the intended domain** (blueprint `lem:rhoNegPowGeOne`):
for `0 ≤ ε` and `0 < ρ ≤ 1` the factor `ρ ^ (-ε)` appearing in `Kakeya.LEApprox` is a loss rather
than a gain.

Only `0 ≤ ε` is needed, although `Kakeya.LEApprox` is applied with `0 < ε`. -/
theorem one_le_rpow_neg {ε : ℝ} (hε : 0 ≤ ε) {ρ : ℝ≥0} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    1 ≤ ρ ^ (-ε) :=
  NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hρ hρ1 (neg_nonpos.mpr hε)

/-- **`⪅` is monotone in its left argument** (blueprint `lem:leApproxMono`): a pointwise smaller
function on the domain `0 < ρ ≤ 1` inherits the bound. -/
theorem LEApprox.mono_left {X X' Y : ℝ≥0 → ℝ≥0} (hX' : X' ⪅ Y)
    (h : ∀ ρ : ℝ≥0, 0 < ρ → ρ ≤ 1 → X ρ ≤ X' ρ) :
    X ⪅ Y :=
  fun ε hε => (hX' ε hε).imp fun _ hC ρ hρ hρ1 => (h ρ hρ hρ1).trans (hC ρ hρ hρ1)

/-- **Adding a constant preserves `⪅ 1`** (blueprint `lem:leApproxAddConst`, first conclusion).

This uses `Kakeya.one_le_rpow_neg`: the constant `c` is absorbed because `ρ ^ (-ε) ≥ 1` on the
domain `0 < ρ ≤ 1`. -/
theorem LEApprox.const_add_one {X : ℝ≥0 → ℝ≥0} (hX : X ⪅ fun _ : ℝ≥0 => (1 : ℝ≥0)) (c : ℝ≥0) :
    (fun ρ => c + X ρ) ⪅ fun _ : ℝ≥0 => (1 : ℝ≥0) := by
  intro ε hε
  obtain ⟨C, hC⟩ := hX ε hε
  refine ⟨c + C, fun ρ hρ hρ1 => ?_⟩
  have h1 : (1 : ℝ≥0) ≤ ρ ^ (-ε) := one_le_rpow_neg hε.le hρ hρ1
  simp only [mul_one] at hC ⊢
  calc c + X ρ ≤ c * ρ ^ (-ε) + C * ρ ^ (-ε) :=
        add_le_add ((mul_one c).ge.trans (mul_le_mul_right h1 c)) (hC ρ hρ hρ1)
    _ = (c + C) * ρ ^ (-ε) := (add_mul c C _).symm

/-- **Multiplying by a constant preserves `⪅ 1`** (blueprint `lem:leApproxAddConst`, second
conclusion). -/
theorem LEApprox.const_mul_one {X : ℝ≥0 → ℝ≥0} (hX : X ⪅ fun _ : ℝ≥0 => (1 : ℝ≥0)) (k : ℝ≥0) :
    (fun ρ => k * X ρ) ⪅ fun _ : ℝ≥0 => (1 : ℝ≥0) := by
  intro ε hε
  obtain ⟨C, hC⟩ := hX ε hε
  refine ⟨k * C, fun ρ hρ hρ1 => ?_⟩
  simp only [mul_one] at hC ⊢
  calc k * X ρ ≤ k * (C * ρ ^ (-ε)) := mul_le_mul_right (hC ρ hρ hρ1) k
    _ = k * C * ρ ^ (-ε) := (mul_assoc k C _).symm

/-- **Reciprocal of a quantity that is `⪅ 1` and bounded below** (blueprint `lem:leApproxInv`).

The positive lower bound `c` rules out the degenerate `ℝ≥0` convention `0⁻¹ = 0`, under which the
conclusion would fail. -/
theorem one_leApprox_inv {X : ℝ≥0 → ℝ≥0} {c : ℝ≥0} (hX : X ⪅ fun _ : ℝ≥0 => (1 : ℝ≥0))
    (hc : 0 < c) (hcX : ∀ ρ : ℝ≥0, 0 < ρ → ρ ≤ 1 → c ≤ X ρ) :
    (fun ρ => (X ρ)⁻¹) ⪆ fun _ : ℝ≥0 => (1 : ℝ≥0) := by
  -- (fun ρ => (X ρ)⁻¹) ⪆ (fun _ => 1) means (fun _ => 1) ⪅ (fun ρ => (X ρ)⁻¹)
  intro ε hε
  obtain ⟨C, hC⟩ := hX ε hε
  refine ⟨C, fun ρ hρ hρ1 => ?_⟩
  -- multiply `X ρ ≤ C * ρ ^ (-ε)` on the right by `(X ρ)⁻¹`, which is legal since `X ρ ≠ 0`.
  simp only [mul_one] at hC
  have h := mul_le_mul_left (hC ρ hρ hρ1) (X ρ)⁻¹
  rwa [mul_inv_cancel₀ (hc.trans_le (hcX ρ hρ hρ1)).ne'] at h

/-- **The logarithmic loss is dominated by `ρ ^ (-ε)`** (blueprint `lem:logbInvLeRpowNegDiv`).

This is the only genuinely analytic ingredient of the calculus of `⪅`: it is where the unbounded
logarithmic loss is absorbed into the factor `ρ ^ (-ε)`. No upper bound on `ρ` is needed; the
restriction `ρ ≤ 1` enters only when the bound is packaged as a `⪅` statement in
`Kakeya.toNNReal_logb_inv_leApprox_one`. -/
theorem logb_inv_le_rpow_neg_div {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    Real.logb 2 (1 / ρ) ≤ ρ ^ (-ε) / (ε * Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `Real.log_le_rpow_div` gives `log x ≤ x ^ ε / ε`; at `x = 1 / ρ` we have `x ^ ε = ρ ^ (-ε)`.
  have hlog : Real.log ρ⁻¹ ≤ ρ ^ (-ε) / ε := by
    have h := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ 1 / ρ) hε
    rwa [one_div, Real.inv_rpow hρ.le, ← Real.rpow_neg hρ.le] at h
  rw [← Real.log_div_log, one_div, ← div_div]
  gcongr

/-- **`log₂ (1 / ρ) ⪅ 1`** (blueprint `lem:logbInvLeApproxOne`): the prototypical `⪅` statement,
repackaging `Kakeya.logb_inv_le_rpow_neg_div` in the `ℝ≥0`-valued language of
`Kakeya.LEApprox`. -/
theorem toNNReal_logb_inv_leApprox_one :
    (fun ρ : ℝ≥0 => Real.toNNReal (Real.logb 2 (1 / (ρ : ℝ)))) ⪅
      fun _ : ℝ≥0 => (1 : ℝ≥0) := by
  intro ε hε
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : (0 : ℝ) ≤ 1 / (ε * Real.log 2) := by positivity
  refine ⟨Real.toNNReal (1 / (ε * Real.log 2)), fun ρ hρ hρ1 => ?_⟩
  rw [Real.toNNReal_le_iff_le_coe]
  refine (logb_inv_le_rpow_neg_div (by exact_mod_cast hρ) hε).trans (le_of_eq ?_)
  push_cast [Real.coe_toNNReal _ hC]
  ring

/-- **Splitting the logarithm of a ratio, positive case** (blueprint
`lem:logbLeLogbAddLogbInv`). -/
theorem logb_le_logb_add_logb_inv {x C₀ ρ : ℝ} (hx : 0 < x) (hC₀ : 0 < C₀) (hρ : 0 < ρ)
    (hxC : x ≤ C₀ * ρ⁻¹) :
    Real.logb 2 x ≤ Real.logb 2 C₀ + Real.logb 2 (1 / ρ) := by
  calc
    Real.logb 2 x ≤ Real.logb 2 (C₀ * ρ⁻¹) :=
      Real.logb_le_logb_of_le (by norm_num) hx hxC
    _ = Real.logb 2 C₀ + Real.logb 2 ρ⁻¹ := Real.logb_mul hC₀.ne' (inv_ne_zero hρ.ne')
    _ = Real.logb 2 C₀ + Real.logb 2 (1 / ρ) := by rw [one_div]

/-- **The degenerate branches vanish** (blueprint `lem:toNNRealLogbEqZero`): these are exactly the
two branches on which the positivity side conditions of `Kakeya.logb_le_logb_add_logb_inv` fail.

Note that `C₀ = 0` forces `x = 0`, since `x ≤ C₀ * ρ⁻¹`. -/
theorem toNNReal_logb_eq_zero_of_degenerate {x C₀ ρ : ℝ≥0} (hxC : x ≤ C₀ * ρ⁻¹)
    (hdeg : x = 0 ∨ C₀ = 0) :
    Real.toNNReal (Real.logb 2 (x : ℝ)) = 0 := by
  -- `C₀ = 0` forces `x ≤ C₀ * ρ⁻¹ = 0`, so either branch gives `x = 0`.
  have hx : x = 0 :=
    hdeg.elim id fun h => nonpos_iff_eq_zero.mp (by rwa [h, zero_mul] at hxC)
  simp [hx]

/-- **Pointwise splitting of the logarithm of a ratio** (blueprint `lem:toNNRealLogbDivLe`).

This is a purely pointwise statement: there is no `ε` and no implicit constant, and no relation
between `a` and `b` is assumed. No bound on `ρ` is needed either: for `ρ ≥ 1` the term
`(log₂ (1 / ρ))₊` vanishes and the bound still holds, while at `ρ = 0` the `ℝ≥0` convention
`0⁻¹ = 0` makes `C₀ * ρ⁻¹ = 0`, so the hypothesis forces `b / a = 0` and the left-hand side
vanishes. The blueprint statement `lem:toNNRealLogbDivLe` records the same total condition. -/
theorem toNNReal_logb_div_le {a b C₀ ρ : ℝ≥0} (hab : b / a ≤ C₀ * ρ⁻¹) :
    Real.toNNReal (Real.logb 2 ((b : ℝ) / (a : ℝ)))
      ≤ Real.toNNReal (Real.logb 2 (C₀ : ℝ)) + Real.toNNReal (Real.logb 2 (1 / (ρ : ℝ))) := by
  -- On either degenerate branch the left-hand side vanishes and the bound is trivial.
  have hdeg : b / a = 0 ∨ C₀ = 0 → Real.toNNReal (Real.logb 2 ((b : ℝ) / (a : ℝ))) = 0 :=
    fun h => by simpa using toNNReal_logb_eq_zero_of_degenerate hab h
  rcases eq_or_ne (b / a) 0 with hba | hba
  · simp [hdeg (Or.inl hba)]
  rcases eq_or_ne C₀ 0 with hC₀ | hC₀
  · simp [hdeg (Or.inr hC₀)]
  -- Otherwise `ρ ≠ 0` too, since `ρ = 0` would force `b / a ≤ C₀ * 0⁻¹ = 0`.
  have hρ : ρ ≠ 0 := fun h => hba (by simpa [h] using hab)
  refine (Real.toNNReal_mono (logb_le_logb_add_logb_inv ?_ ?_ ?_ ?_)).trans Real.toNNReal_add_le
  · simpa using NNReal.coe_pos.mpr (pos_of_ne_zero hba)
  · exact NNReal.coe_pos.mpr (pos_of_ne_zero hC₀)
  · exact NNReal.coe_pos.mpr (pos_of_ne_zero hρ)
  · simpa using NNReal.coe_le_coe.mpr hab

/-- **The logarithm of a ratio bounded by `ρ⁻¹` is `⪅ 1`** (blueprint
`lem:factoringStep1LogRatioApprox`).

Following the convention (ii′) of the blueprint section `defnLessapprox`, the implicit parameter
of `Kakeya.LEApprox` is `ρ = |𝒱|⁻¹`, so the hypothesis `b / a ≲ |𝒱|` reads
`(fun ρ => b ρ / a ρ) ≲ fun ρ => ρ⁻¹`.

The conclusion is stated for the positive part `Real.toNNReal`, so that both sides are `ℝ≥0`
valued as `Kakeya.LEApprox` requires; since `a ≤ b` is *not* assumed, `log₂ (b / a)` may genuinely
be negative and the positive part is not merely a change of type.

The proof is the composition of the pointwise splitting `Kakeya.toNNReal_logb_div_le` with
`Kakeya.toNNReal_logb_inv_leApprox_one`, `Kakeya.LEApprox.const_add_one` and
`Kakeya.LEApprox.mono_left`. -/
theorem toNNReal_logb_div_leApprox_one {a b : ℝ≥0 → ℝ≥0}
    (hratio : (fun ρ => b ρ / a ρ) ≲ fun ρ : ℝ≥0 => ρ⁻¹) :
    (fun ρ => Real.toNNReal (Real.logb 2 ((b ρ : ℝ) / (a ρ : ℝ)))) ⪅
      fun _ : ℝ≥0 => (1 : ℝ≥0) := by
  obtain ⟨C₀, hC₀⟩ := hratio
  exact LEApprox.mono_left
    (X' := fun ρ : ℝ≥0 => Real.toNNReal (Real.logb 2 (C₀ : ℝ))
      + Real.toNNReal (Real.logb 2 (1 / (ρ : ℝ))))
    (toNNReal_logb_inv_leApprox_one.const_add_one _)
    fun ρ hρ hρ1 => toNNReal_logb_div_le (hC₀ ρ hρ hρ1)

end

end Kakeya
