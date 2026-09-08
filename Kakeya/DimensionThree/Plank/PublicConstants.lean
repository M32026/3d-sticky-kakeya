/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabwiseTransport

/-!
# The two public absolute constants of GWZ Lemma 6.13

The public statement of Lemma 6.13 binds `cN` and `Cbox` *before* `η` and `ε`.  This file fixes
both, from the absolute geometry block that `Kakeya.refinement_preassembly_uniform` publishes
before its `∀ {η ε}` binder, and proves the inequalities the final assembly needs.  Nothing here
depends on `η`, `ε`, `Cθ`, `C611`, `cEta`, `Cres` or `kappa`, and no constant is absorbed into a
power of `a`.

## The fibre constant

The preassembly returns a two-sided fibre bound at an internal `cN` with `1 ≤ cN ≤ 2`; the public
statement asks for the literal `2`.  `Kakeya.fibre_bounds_two` widens the whole
clause, using the already-proved `Plank.fibre_bounds_two_of_le_two`.  The preassembly's constant is
untouched and no new pigeonhole is run.

## The box constant

The assigned Item 2 route does not take the box dilation as a parameter constrained by a region
inequality: `Kakeya.slabwiseRepresentativeShading` *builds* its shading at the dilation
`4 * Cang + 8 + Cc`, where `Cang` is the constant of its representative-angle hypothesis and `Cc`
the constant of its shade-containment hypothesis.  Instantiated at the preassembly's block those
are `Cang2` and `Ccarrier`, so the public choice is forced to be

`Kakeya.plankReduction.boxDilation Cang2 Ccarrier = 4 * Cang2 + 8 + Ccarrier`

so the "region inequality" holds definitionally, by `Kakeya.plankReduction.boxDilation_eq`.
-/

@[expose] public section

open scoped NNReal

namespace Kakeya

/-! ## The public box dilation -/

/-- **The public box-dilation constant `Cbox` of GWZ Lemma 6.13.**

`Kakeya.slabwiseRepresentativeShading` shades at the dilation `4 * Cang + 8 + Cc` of the
typed representative's prism, with `Cang` its representative-angle constant and `Cc` its
shade-containment constant.  At the preassembly's absolute block those are `Cang2` and `Ccarrier`,
which is exactly this expression.

It depends only on the geometry block published before the `η, ε` binder, so it is selectable
before `intro η ε`. -/
def plankReduction.boxDilation (Cang2 Ccarrier : ℝ≥0) : ℝ≥0 :=
  4 * Cang2 + 8 + Ccarrier

@[simp] theorem plankReduction.boxDilation_eq (Cang2 Ccarrier : ℝ≥0) :
    plankReduction.boxDilation Cang2 Ccarrier = 4 * Cang2 + 8 + Ccarrier := by
  rfl

/-- The carrier constant sits below the box dilation. -/
theorem plankReduction.le_boxDilation (Cang2 Ccarrier : ℝ≥0) :
    Ccarrier ≤ plankReduction.boxDilation Cang2 Ccarrier :=
  le_add_self

/-- **`cThk ≤ Cbox`**, from the preassembly's `cThk ≤ Ccarrier`. -/
theorem plankReduction.cThk_le_boxDilation {cThk Cang2 Ccarrier : ℝ≥0}
    (h : cThk ≤ Ccarrier) : cThk ≤ plankReduction.boxDilation Cang2 Ccarrier :=
  h.trans (plankReduction.le_boxDilation Cang2 Ccarrier)

/-! ## The public fibre constant `cN = 2` -/

open Classical in
/-- **The preassembly's fibre clause at the public constant `cN = 2`.**

The preassembly states the near-constant fibre bound at its internal `cN`, which it only guarantees
to satisfy `1 ≤ cN ≤ 2`.  The public statement of Lemma 6.13 exposes the literal `2`; both
directions are plain monotonicity, discharged by `Plank.fibre_bounds_two_of_le_two`.  The internal
constant is not modified and no second pigeonhole is run. -/
theorem fibre_bounds_two {ι τ : Type*} {s' : Finset ι} {𝒯 : Finset τ}
    {repr : ι → τ} {cN : ℝ≥0} {N : ℕ} (hcN1 : 1 ≤ cN) (hcN2 : cN ≤ 2)
    (hfib : ∀ t ∈ 𝒯, (N : ℝ) / (cN : ℝ) ≤ ((s'.filter (fun i => repr i = t)).card : ℝ) ∧
      ((s'.filter (fun i => repr i = t)).card : ℝ) ≤ (cN : ℝ) * (N : ℝ)) :
    ∀ t ∈ 𝒯, (N : ℝ) / 2 ≤ ((s'.filter (fun i => repr i = t)).card : ℝ) ∧
      ((s'.filter (fun i => repr i = t)).card : ℝ) ≤ 2 * (N : ℝ) :=
  fun t ht => Plank.fibre_bounds_two_of_le_two (NNReal.one_le_coe.mpr hcN1)
    (NNReal.coe_le_coe.mpr hcN2) (Nat.cast_nonneg N) (hfib t ht).1 (hfib t ht).2

end Kakeya

end
