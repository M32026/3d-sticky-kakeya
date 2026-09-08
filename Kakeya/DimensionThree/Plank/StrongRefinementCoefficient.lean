/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.AngleDef
public import Kakeya.DimensionThree.Plank.Geometry

/-!
# The strong refinement coefficient and the Item 4 exponent ledger

`Kakeya.representativeWitness_strong_uniform` returns its refinement coefficient `rRef`
together with a uniform lower bound of the shape `Cref⁻¹ · a ^ η · a ^ ε ≤ rRef`, with `Cref`
quantified **before** the configuration.  Item 4 consumes that bound in reciprocal form,
`rRef⁻¹ ≤ Cref · a ^ (-η) · a ^ (-ε)`, since the symbolic reduction
`Kakeya.multiplicityReduction_of_refinement_and_fullness_ratio` produces the coefficient
`Cgeom · rRef⁻¹ · cOv⁻¹ · β⁻¹ · (aN)/(bθ)`.

The three lemmas below are the whole arithmetic of that conversion.

* `Kakeya.inv_le_of_strongRefinementCoeff` is the reciprocal form, in `ℝ≥0`.
* `Kakeya.one_le_mul_of_strongRefinementCoeff` is the division-free form
  `1 ≤ Cref · rRef · a ^ (-η) · a ^ (-ε)`.
* `Kakeya.coe_inv_le_of_strongRefinementCoeff` is the `ℝ≥0∞` form, which is where the symbolic
  reduction reads it.

**The exponent ledger.**  `Kakeya.multiplicity_ledger` records the intended arithmetic of the Item 4
coefficient in one place: the strong refinement contributes `a ^ (-η) · a ^ (-ε)` and the aggregate
fullness lower bound contributes `a ^ (-3η)`, and the two multiply to the public `a ^ (-4η)`.  The
ledger is stated symbolically, so it makes the *budget* explicit without asserting either factor.
Its two hard-coded exponents `η` and `3η` are exactly what charging `rRef` at the *polynomial* rate
forces; `Kakeya.multiplicity_ledger_general` is the same arithmetic with all four exponents
free, which is what the corrected Item 2 ledger consumes.

`Kakeya.mul_rpow_le_of_exponent_ge` is the weakening in the other direction, used to derive the
weakened output clauses of the witness from the strong ones: since `a ≤ 1`,
a larger exponent is a smaller coefficient, hence a weaker refinement/cardinality/fullness clause.

**Charging the loss at its true rate.**  The exponent `η` in `Cref⁻¹ · a ^ η · a ^ ε ≤ rRef` is not
forced by the geometry.  `rRef = (cGood - q) · cAngle` with `q = cGood/2`, and
`Kakeya.pigeonhole_of_phi_packing_sharp` bounds `cGood` below by the *sharp*
`(Cres · plankAngleScaleA a)⁻¹` as well as by the polynomial `cEta · a ^ η`.  Since
`plankAngleScaleA a = exp (√(log a⁻¹))` is sub-polynomial, the last four declarations of this file
convert the sharp branch into a power of `a` at an **arbitrary** exponent `η' > 0` chosen by the
caller:

* `Kakeya.exists_plankAngleScaleA_le_rpow` — `A(a) ≤ C(η') · a ^ (-η')` for every `0 < a < 1`;
* `Kakeya.exists_absorb_sharp_pigeonhole` — the absorption theorem, `Cabs⁻¹ · a ^ η' ≤ cGood`;
* `Kakeya.exists_absorb_strongRefinementCoeff` — `Cref'⁻¹ · a ^ η' · a ^ ε ≤ rRef`;
* `Kakeya.multiplicity_ledger_general` — the Item 4 budget at free exponents.

All constants are quantified before the configuration and there is no smallness threshold `a < a₀`.
-/

@[expose] public section

open scoped NNReal Real

noncomputable section

namespace Kakeya

/-- **Weakening a coefficient by raising the exponent of `a`.**  For `0 < a ≤ 1` and `m ≤ n`,
`c · a ^ n · a ^ ε ≤ c · a ^ m · a ^ ε`.  Since all three of `Kakeya.plankReduction`'s quantitative
clauses (refinement, cardinality, fullness) are monotone decreasing in their coefficient, this is
what turns the strong clauses of `Kakeya.representativeWitness_strong_uniform` into the weakened
clauses its downstream consumers state. -/
theorem mul_rpow_le_of_exponent_ge {c a : ℝ≥0} {ε m n : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hmn : m ≤ n) :
    c * a ^ n * a ^ ε ≤ c * a ^ m * a ^ ε :=
  mul_le_mul_left (mul_le_mul_right (NNReal.rpow_le_rpow_of_exponent_ge ha0 ha1 hmn) c) _

/-- **The `Cref` absorption lemma, reciprocal form.**  A strong refinement coefficient bounded below
by `Cref⁻¹ · a ^ η · a ^ ε` has its reciprocal bounded above by `Cref · a ^ (-η) · a ^ (-ε)`. -/
theorem inv_le_of_strongRefinementCoeff {Cref rRef a : ℝ≥0} {η ε : ℝ}
    (hCref : 0 < Cref) (ha : 0 < a)
    (h : Cref⁻¹ * a ^ η * a ^ ε ≤ rRef) :
    rRef⁻¹ ≤ Cref * a ^ (-η) * a ^ (-ε) := by
  have h' : rRef⁻¹ ≤ (Cref⁻¹ * a ^ η * a ^ ε)⁻¹ := inv_anti₀ (by positivity) h
  rwa [mul_inv, mul_inv, inv_inv, ← NNReal.rpow_neg, ← NNReal.rpow_neg] at h'

/-- **The `Cref` absorption lemma, division-free form.**  The same content as
`Kakeya.inv_le_of_strongRefinementCoeff` written with no reciprocal of `rRef`. -/
theorem one_le_mul_of_strongRefinementCoeff {Cref rRef a : ℝ≥0} {η ε : ℝ}
    (hCref : 0 < Cref) (ha : 0 < a)
    (h : Cref⁻¹ * a ^ η * a ^ ε ≤ rRef) :
    1 ≤ Cref * rRef * a ^ (-η) * a ^ (-ε) := by
  have hr : rRef ≠ 0 := ((by positivity : (0 : ℝ≥0) < Cref⁻¹ * a ^ η * a ^ ε).trans_le h).ne'
  calc
    (1 : ℝ≥0) ≤ rRef * (Cref * a ^ (-η) * a ^ (-ε)) :=
      (NNReal.inv_le hr).mp (inv_le_of_strongRefinementCoeff hCref ha h)
    _ = Cref * rRef * a ^ (-η) * a ^ (-ε) := by ring

/-- **The `Cref` absorption lemma in `ℝ≥0∞`.**  The shape in which
`Kakeya.multiplicityReduction_of_refinement_and_fullness_ratio` reads the strong coefficient: its
output has the factor `(rRef : ℝ≥0∞)⁻¹`. -/
theorem coe_inv_le_of_strongRefinementCoeff {Cref rRef a : ℝ≥0} {η ε : ℝ}
    (hCref : 0 < Cref) (ha : 0 < a)
    (h : Cref⁻¹ * a ^ η * a ^ ε ≤ rRef) :
    (rRef : ENNReal)⁻¹ ≤ ((Cref * a ^ (-η) * a ^ (-ε) : ℝ≥0) : ENNReal) := by
  have hr : rRef ≠ 0 := ((by positivity : (0 : ℝ≥0) < Cref⁻¹ * a ^ η * a ^ ε).trans_le h).ne'
  rw [← ENNReal.coe_inv hr]
  exact ENNReal.coe_le_coe.mpr (inv_le_of_strongRefinementCoeff hCref ha h)

/-- **The Item 4 exponent ledger.**  The strong refinement factor `a ^ (-η) · a ^ (-ε)` times an
aggregate fullness factor `a ^ (-3η)` is the public Item 4 factor `a ^ (-4η) · a ^ (-ε)`.

Stated symbolically in both inputs, so it asserts nothing about either: it records that Item 4's
public exponent is reachable precisely when the fullness lower bound `β` has reciprocal controlled
by `c₂⁻¹ · a ^ (-3η)`, i.e. when Item 2's *internal* aggregate fullness exponent is at most `3η`. -/
theorem multiplicity_ledger {Cref c2 rRef β a : ℝ≥0} {η ε : ℝ} (ha : 0 < a)
    (hrRef : rRef⁻¹ ≤ Cref * a ^ (-η) * a ^ (-ε))
    (hβ : β⁻¹ ≤ c2⁻¹ * a ^ (-(3 * η))) :
    rRef⁻¹ * β⁻¹ ≤ (Cref * c2⁻¹) * a ^ (-(4 * η)) * a ^ (-ε) := by
  calc
    rRef⁻¹ * β⁻¹ ≤ (Cref * a ^ (-η) * a ^ (-ε)) * (c2⁻¹ * a ^ (-(3 * η))) :=
      mul_le_mul' hrRef hβ
    _ = (Cref * c2⁻¹) * a ^ (-(4 * η)) * a ^ (-ε) := by
      rw [show -(4 * η) = -η + -(3 * η) by ring, NNReal.rpow_add ha.ne']; ring

/-! ## Charging the refinement loss at its true, sub-polynomial rate

`Kakeya.pigeonhole_of_phi_packing_sharp` returns two lower bounds on its retention coefficient
`cGood`: the *polynomial* `cEta · a ^ η` and the *sharp* `(Cres · A(a))⁻¹`, where
`A(a) = Kakeya.plankAngleScaleA a = exp (√(log a⁻¹))`.  Every downstream consumer of `cGood` read
only the polynomial branch, which fixes the exponent at `η`.  But `A(a)` is *sub-polynomial*, so by
`Kakeya.subpolyExp` at `α = 1/2` the sharp branch dominates a power of `a` at **every** positive
exponent, up to a constant depending only on that exponent.  Charging the refinement loss at `a ^ η`
is therefore an over-charge, and the three declarations below replace it by a charge at an arbitrary
`η' > 0` chosen by the caller.

There is no smallness threshold: `Kakeya.subpolyExp` holds for every `0 < a < 1`, and none may be
introduced. -/

/-- **The step scale is sub-polynomial, uniformly and without a threshold** (extra69,
`rem:existsPlankAngleScaleALeRpow`).

For every `η' > 0` there is `C = C(η') > 0`, quantified before any configuration, with
`A(a) ≤ C · a ^ (-η')` for *every* `0 < a < 1`.  This is `Kakeya.subpolyExp` at `α = 1/2`,
transported to `ℝ≥0` through `Real.toNNReal` so that it composes with the `ℝ≥0`-valued coefficients
of `Kakeya.pigeonhole_of_phi_packing_sharp`.

The constant cannot be dropped: the pointwise inequality `A(a) ≤ a ^ (-η')` fails for `a`
near `1`. -/
theorem exists_plankAngleScaleA_le_rpow {η' : ℝ} (hη' : 0 < η') :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ a : ℝ≥0, 0 < a → a < 1 →
      Real.toNNReal (plankAngleScaleA a) ≤ C * a ^ (-η') := by
  obtain ⟨Creal, hCrealpos, hCreal⟩ := subpolyExp (α := 1/2) (by norm_num) (by norm_num) hη'
  refine ⟨Real.toNNReal Creal, Real.toNNReal_pos.mpr hCrealpos, fun a ha ha1 => ?_⟩
  rw [Real.toNNReal_le_iff_le_coe]
  push_cast [Real.coe_toNNReal _ hCrealpos.le]
  simpa [plankAngleScaleA, Real.sqrt_eq_rpow] using
    hCreal (a : ℝ) (mod_cast ha) (mod_cast ha1)

/-- **The absorption theorem: a sub-polynomial loss is a power of `a` at every rate** (extra69,
`rem:existsAbsorbSharpPigeonhole`).

For every `η' > 0` and every `Cres > 0` there is `Cabs = Cabs(η', Cres) > 0`, quantified before the
configuration, such that the *sharp* dyadic pigeonhole bound `(Cres · A(a))⁻¹ ≤ cGood` of
`Kakeya.pigeonhole_of_phi_packing_sharp` implies `Cabs⁻¹ · a ^ η' ≤ cGood` for every `0 < a < 1`.

Note the order of quantifiers: `η'` is chosen by the **caller**, after it knows which target
exponent it has to hit and still before the configuration.  It is *not* tied to the `η` of the
pigeonhole.  The polynomial branch `cEta · a ^ η ≤ cGood` is a bound at one fixed exponent and is
retained unchanged, since it is what supplies the uniform constants `cP`, `cLam` and `Cref` of
`Kakeya.representativeWitness_strong_uniform`; the sharp branch remains the only one that can
control the reserve scale. -/
theorem exists_absorb_sharp_pigeonhole {η' : ℝ} (hη' : 0 < η') {Cres : ℝ≥0} (hCres : 0 < Cres) :
    ∃ Cabs : ℝ≥0, 0 < Cabs ∧ ∀ {a cGood : ℝ≥0}, 0 < a → a < 1 →
      (Cres * Real.toNNReal (plankAngleScaleA a))⁻¹ ≤ cGood →
      Cabs⁻¹ * a ^ η' ≤ cGood := by
  obtain ⟨C, hCpos, hC⟩ := exists_plankAngleScaleA_le_rpow hη'
  refine ⟨Cres * C, mul_pos hCres hCpos, fun {a cGood} ha ha1 hsharp => le_trans ?_ hsharp⟩
  have hApos : 0 < Cres * Real.toNNReal (plankAngleScaleA a) :=
    mul_pos hCres (Real.toNNReal_pos.mpr (zero_lt_one.trans (one_lt_plankAngleScaleA ha ha1)))
  have hmul : Cres * Real.toNNReal (plankAngleScaleA a) ≤ Cres * C * a ^ (-η') := by
    rw [mul_assoc]; exact mul_le_mul_right (hC a ha ha1) Cres
  calc
    (Cres * C)⁻¹ * a ^ η' = (Cres * C * a ^ (-η'))⁻¹ := by
      rw [NNReal.rpow_neg, mul_inv, mul_inv, mul_inv, inv_inv]
    _ ≤ (Cres * Real.toNNReal (plankAngleScaleA a))⁻¹ := inv_anti₀ hApos hmul

/-- **The strong refinement coefficient at an arbitrary positive exponent** (extra69,
`rem:existsAbsorbStrongRefinementCoeff`).

For every `η' > 0`, every `Cres > 0` and every `Cuni ≥ 1` there is
`Cref' = Cref'(η', Cres, Cuni) ≥ 1`, quantified before the configuration, such that the four clauses
`q = cGood / 2`, `rRef = (cGood - q) · cAngle`, `(Cres · A(a))⁻¹ ≤ cGood` and
`Cuni⁻¹ · a ^ ε ≤ cAngle` give `Cref'⁻¹ · a ^ η' · a ^ ε ≤ rRef`.

All four are exposed by `Kakeya.representativeWitness_strong_uniform`, and `Cres`, `Cuni`
both sit in its *outer* existential, so `Cref'` is still produced before any geometric datum.
Compare that theorem's own bound `Cref⁻¹ · a ^ η · a ^ ε ≤ rRef`: it is the same computation
with the
*polynomial* pigeonhole branch substituted instead, which is why its exponent is `η`.  The factor
`a ^ ε` is untouched and is not absorbed — it comes from `cAngle`, not from `cGood`.

The constant is `Cref' = max 1 (2 · Cabs · Cuni)` with `Cabs` from
`Kakeya.exists_absorb_sharp_pigeonhole`, so it is exponentially large in `1 / η'`.  That is the
bargain: a fatal exponent is traded for a large uniform constant. -/
theorem exists_absorb_strongRefinementCoeff {η' : ℝ} (hη' : 0 < η') {Cres Cuni : ℝ≥0}
    (hCres : 0 < Cres) (hCuni : 1 ≤ Cuni) :
    ∃ Cref' : ℝ≥0, 1 ≤ Cref' ∧
      ∀ {a cGood q cAngle rRef : ℝ≥0} {ε : ℝ}, 0 < a → a < 1 →
        q = cGood / 2 → rRef = (cGood - q) * cAngle →
        (Cres * Real.toNNReal (plankAngleScaleA a))⁻¹ ≤ cGood →
        Cuni⁻¹ * a ^ ε ≤ cAngle →
        Cref'⁻¹ * a ^ η' * a ^ ε ≤ rRef := by
  obtain ⟨Cabs, hCabs_pos, hCabs⟩ := exists_absorb_sharp_pigeonhole hη' hCres
  refine ⟨max 1 (2 * Cabs * Cuni), le_max_left _ _, ?_⟩
  intro a cGood q cAngle rRef ε ha0 ha1 hq hrRef hcGood hcAngle
  have hCuni_pos : 0 < Cuni := zero_lt_one.trans_le hCuni
  have hcGood_sub : cGood - q = cGood / 2 := by
    rw [hq]; exact tsub_eq_of_eq_add (by ring)
  have hleft : (2 * Cabs)⁻¹ * a ^ η' ≤ cGood / 2 := by
    rw [mul_inv, mul_comm (2 : ℝ≥0)⁻¹, mul_assoc, mul_comm (2 : ℝ≥0)⁻¹, ← div_eq_mul_inv,
      ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hCabs ha0 ha1 hcGood) zero_le
  rw [hrRef, hcGood_sub]
  calc
    (max 1 (2 * Cabs * Cuni))⁻¹ * a ^ η' * a ^ ε
        ≤ (2 * Cabs * Cuni)⁻¹ * a ^ η' * a ^ ε :=
      mul_le_mul_left (mul_le_mul_left
        (inv_anti₀ (show (0 : ℝ≥0) < 2 * Cabs * Cuni by positivity) (le_max_right 1 _))
        (a ^ η')) (a ^ ε)
    _ = ((2 * Cabs)⁻¹ * a ^ η') * (Cuni⁻¹ * a ^ ε) := by rw [mul_inv]; ring
    _ ≤ (cGood / 2) * cAngle := mul_le_mul' hleft hcAngle

/-- **The refined family's fullness at the sharpened rate** (extra69,
`rem:existsAbsorbRefinedFullness`, the arithmetic half).

The strong fullness clause `rRef · λ(s, Y) ≤ λ(s', Y'')` of
`Kakeya.representativeWitness_strong_uniform`, read against the incoming bound
`a ^ η ≤ λ(s, Y)` and the sharpened coefficient bound `(Cref')⁻¹ · a ^ η' · a ^ ε ≤ rRef` of
`Kakeya.exists_absorb_strongRefinementCoeff`, gives the refined family's fullness at the exponent
`η + η'`:

`(Cref')⁻¹ · a ^ (η + η') · a ^ ε ≤ λ(s', Y'')`.

This is the *whole* arithmetic of the threading step; the exponent `η + η'` is an addition of powers
of `a` and nothing else happens.  Against the polynomial accounting, which read
`Cref⁻¹ · a ^ η · a ^ ε ≤ rRef` and hence `Cref⁻¹ · a ^ (2η) · a ^ ε`, the gain is exactly
`a ^ (η - η')` with `η'` free. -/
theorem le_fullness_of_strongRefinementCoeff {a Cref' rRef lamY μ : ℝ≥0} {η η' ε : ℝ}
    (ha : 0 < a)
    (hrr : Cref'⁻¹ * a ^ η' * a ^ ε ≤ rRef)
    (hlam : a ^ η ≤ lamY)
    (hfull : rRef * lamY ≤ μ) :
    Cref'⁻¹ * a ^ (η + η') * a ^ ε ≤ μ := by
  calc
    Cref'⁻¹ * a ^ (η + η') * a ^ ε = (Cref'⁻¹ * a ^ η' * a ^ ε) * a ^ η := by
      rw [show η + η' = η' + η by ring, NNReal.rpow_add ha.ne']; ring
    _ ≤ rRef * lamY := mul_le_mul' hrr hlam
    _ ≤ μ := hfull

/-- **The Item 4 exponent ledger, with every exponent a bare symbol** (extra69,
the general multiplicity-ledger remark).

`Kakeya.multiplicity_ledger` hard-codes the two exponents `η` and `3η`, which is what the polynomial
charging of `rRef` forced.  This is the same arithmetic with all four exponents symbolic: the
reciprocal refinement factor `a ^ (-η') · a ^ (-ε')` times the reciprocal aggregate fullness factor
`a ^ (-ρ) · a ^ (-εtot)` is `a ^ (-(η' + ρ)) · a ^ (-(ε' + εtot))`.

It asserts nothing about either factor: it records the Item 4 *budget*, namely that Item 4's public
`a ^ (-(4η))` is reachable exactly when `η' + ρ ≤ 4η`. -/
theorem multiplicity_ledger_general {Cref c2 rRef β a : ℝ≥0} {η' ρ ε' εtot : ℝ}
    (ha : 0 < a)
    (hrRef : rRef⁻¹ ≤ Cref * a ^ (-η') * a ^ (-ε'))
    (hβ : β⁻¹ ≤ c2⁻¹ * a ^ (-ρ) * a ^ (-εtot)) :
    rRef⁻¹ * β⁻¹ ≤ (Cref * c2⁻¹) * a ^ (-(η' + ρ)) * a ^ (-(ε' + εtot)) := by
  calc
    rRef⁻¹ * β⁻¹ ≤ (Cref * a ^ (-η') * a ^ (-ε')) * (c2⁻¹ * a ^ (-ρ) * a ^ (-εtot)) :=
      mul_le_mul' hrRef hβ
    _ = (Cref * c2⁻¹) * a ^ (-(η' + ρ)) * a ^ (-(ε' + εtot)) := by
      rw [show -(η' + ρ) = -η' + -ρ by ring, show -(ε' + εtot) = -ε' + -εtot by ring,
        NNReal.rpow_add ha.ne', NNReal.rpow_add ha.ne']
      ring

end Kakeya

end
