/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Section6CompatSmallAngle

/-!
# The comparability constant of `reduction_to_slab_atTypicalAngle` is an `a`-scale constant

The module docstring of `Section6Compat.lean` records the following as *the* blocker for
`ShadedPlank.reduction_to_slab_atTypicalAngle`:

> The data this statement receives are controlled only at the *auxiliary* scale `δ ≤ a` […] Since
> `δ` may be an arbitrarily high power of `a`, `δ ^ ε · a ^ η` is not bounded below by any power of
> `a`, so the `a`-scale hypotheses are not derivable from the `δ`-scale ones.

That is true of the hypotheses **as stated**, and false of the *theorem*: the regime in which `δ` is
a high power of `a` is exactly the regime that
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_smallRadius` already discharges, so it may be
assumed away.  Writing `g` for the gap multiplier (`g = 128` at the binder
`128 * ε ≤ ε'`), the residual hypothesis of
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_budgetExcess` is

```
a ^ η * a  <  432 · δ ^ ε' · a ^ (4η) · a ^ ε · C · θ b ,
```

and with `θ b ≤ 1`, `δ ^ ε' * C ≤ δ ^ (ε' - ε) ≤ δ ^ ((g-1) ε)` it forces

```
a ^ (1 - 3η - ε) / 432  <  δ ^ (127 ε),      hence      C ≤ δ ^ (-ε) < 2 · a ^ (-(1 - 3η - ε)/127).
```

So **`C` is bounded by a fixed power of the plank scale `a`**, with an exponent
`(1 - 3η - ε) / 127` that is fixed before the configuration, exactly like `η`, `ε`, `ε'`
themselves.  The scale mismatch the docstring names is therefore *not* an obstruction to the
theorem; it is an obstruction only to a proof that refuses to case-split on the scalar budget.

`ShadedPlank.reduction_to_slab_atTypicalAngle_of_aScaleConstant` is that statement: the target
verbatim, from the target with the single extra hypothesis

```
C ≤ 2 * a ^ (-((1 - 3 * η - ε) / 127)).
```

## Why this is the shape the slab layer asks for

`Plank.localAngleConcentration_of_preassemblyData`, the producer of the `hLAC` hypothesis of
`Plank.slabwiseDensity_of_preassembly`, asks for the two-sided typicality at a constant of the
shape `Cstab0 * a ^ (-εs)` with `Cstab0` and `εs` **bound before the configuration** and
`0 < εs < ηL`.  The bound above supplies precisely that shape, at `Cstab0 = 2` and
`εs = (1 - 3η - ε)/127`: from `Kakeya.IsTypicalPlankAngle s Y'' P θ C A` and `C ≤ 2 * a ^ (-εs)`,
`Kakeya.IsTypicalPlankAngle.mono_const` (or `Kakeya.IsTypicalPlankAngle` monotonicity in the
constant) gives `Kakeya.IsTypicalPlankAngle s Y'' P θ (2 * a ^ (-εs)) A`.

What this does **not** do is make the whole slab route affordable, and the reason is recorded here
so it is not rediscovered.  `εs` is one number, fixed before the configuration, so it must be
chosen for the *worst* configuration in the residual region, `εs = (1 - 3η - ε)/127`; whereas
`Plank.slabwiseDensity_of_preassembly` also requires `3 * ηL ≤ 4 * η + εwork`, and its Item-1
output constant `cBall * cLamBox ^ 2 * a ^ (4η + εwork)` has to beat the demanded
`c1 * a ^ (4η + ε)` with `c1 = δ ^ ε'`, which at the *other* end of the residual region (`δ = a`,
where `c1 = a ^ (128 ε)`) caps `εwork` at `O(ε + η)` and hence `ηL` at `O(ε + η)`.  The two ends
are compatible only if `(1 - 3η - ε)/127 < ηL = O(η + ε)`, i.e. only for `η` and `ε` bounded below
by an absolute constant.  Covering the residual region therefore needs **finitely many** instances
of the slab layer, one per dyadic block of the exponent `t = log δ / log a`, with its own
`(εs_j, ηL_j)`; the blocks grow geometrically (`t_{j+1} ≈ 126 t_j`), so `O(log (1/ε))` of them
suffice, but a single instance provably does not.
-/

@[expose] public section

open MeasureTheory Metric
open scoped NNReal Real ENNReal

noncomputable section

namespace ShadedPlank

/-! ## The numeric fact behind the constant `2` -/

/-- `432 ^ (1/127) ≤ 2`, because `432 ≤ 2 ^ 127`. -/
theorem rpow_inv_127_432_le_two : (432 : ℝ≥0) ^ ((127 : ℝ)⁻¹) ≤ 2 := by
  have hbase : (432 : ℝ≥0) ≤ (2 : ℝ≥0) ^ (127 : ℝ) := by
    rw [show ((127 : ℝ)) = ((127 : ℕ) : ℝ) by norm_num, NNReal.rpow_natCast]
    norm_num
  calc (432 : ℝ≥0) ^ ((127 : ℝ)⁻¹)
      ≤ ((2 : ℝ≥0) ^ (127 : ℝ)) ^ ((127 : ℝ)⁻¹) := by
        exact NNReal.rpow_le_rpow hbase (by norm_num)
    _ = (2 : ℝ≥0) ^ ((127 : ℝ) * (127 : ℝ)⁻¹) := (NNReal.rpow_mul _ _ _).symm
    _ = 2 := by norm_num

/-! ## The residual budget bounds `C` by a power of `a` -/

/-- **The scalar core: in the residual regime the comparability constant is an `a`-power.**

From the failure of the small-radius budget
`432 · δ ^ ε' · a ^ (4η) · a ^ ε · C · θ b ≤ a ^ η · a`, together with `θ b ≤ 1`,
`C ≤ δ ^ (-ε)` and `128 * ε ≤ ε'`, one gets `C ≤ 2 * a ^ (-((1 - 3η - ε)/127))`.

Nothing geometric enters: this is an inequality between `δ, a, b, θ, C` alone. -/
theorem le_two_mul_rpow_of_budgetExcess {η ε ε' : ℝ} (hε : 0 < ε) (hgap : 128 * ε ≤ ε')
    {δ a b θ C : ℝ≥0} (hδ : 0 < δ) (hδa : δ ≤ a) (ha1 : a < 1) (hθ1 : θ ≤ 1) (hb1 : b ≤ 1)
    (hCδ : C ≤ δ ^ (-ε))
    (hres : a ^ η * a < 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C * (θ * b)) :
    C ≤ 2 * a ^ (-((1 - 3 * η - ε) / 127)) := by
  have ha : (0 : ℝ≥0) < a := lt_of_lt_of_le hδ hδa
  have hane : (a : ℝ≥0) ≠ 0 := ha.ne'
  have hδne : (δ : ℝ≥0) ≠ 0 := hδ.ne'
  have hδ1 : (δ : ℝ≥0) ≤ 1 := le_trans hδa ha1.le
  -- drop the factor `θ * b ≤ 1`
  have hθb : (θ : ℝ≥0) * b ≤ 1 := by
    calc (θ : ℝ≥0) * b ≤ 1 * 1 := by gcongr
      _ = 1 := by ring
  have hstep1 : a ^ η * a < 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C := by
    refine lt_of_lt_of_le hres ?_
    calc 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C * (θ * b)
        ≤ 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C * 1 := by gcongr
      _ = 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C := by ring
  -- `δ ^ ε' * C ≤ δ ^ (127 * ε)`
  have hδC : (δ : ℝ≥0) ^ ε' * C ≤ δ ^ (127 * ε) := by
    have h1 : (δ : ℝ≥0) ^ ε' * C ≤ δ ^ ε' * δ ^ (-ε) := by gcongr
    have h2 : (δ : ℝ≥0) ^ ε' * δ ^ (-ε) = δ ^ (ε' - ε) := by
      rw [← NNReal.rpow_add hδne]; ring_nf
    have h3 : (δ : ℝ≥0) ^ (ε' - ε) ≤ δ ^ (127 * ε) :=
      NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    exact le_trans h1 (h2 ▸ h3)
  -- collect the `a`-powers
  have hrw : a ^ η * a = a ^ (1 - 3 * η - ε) * (a ^ (4 * η) * a ^ ε) := by
    have h1 : a ^ (1 - 3 * η - ε) * (a ^ (4 * η) * a ^ ε) = a ^ (1 + η) := by
      rw [← NNReal.rpow_add hane, ← NNReal.rpow_add hane]
      congr 1
      ring
    have h2 : a ^ η * a = a ^ (1 + η) := by
      rw [show (1 + η) = η + 1 by ring, NNReal.rpow_add hane, NNReal.rpow_one]
    rw [h1, h2]
  have hrw2 : 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C
      = 432 * ((δ : ℝ≥0) ^ ε' * C) * (a ^ (4 * η) * a ^ ε) := by ring
  have hpos : (0 : ℝ≥0) < a ^ (4 * η) * a ^ ε :=
    mul_pos (NNReal.rpow_pos ha) (NNReal.rpow_pos ha)
  rw [hrw, hrw2] at hstep1
  have hcancel : a ^ (1 - 3 * η - ε) < 432 * ((δ : ℝ≥0) ^ ε' * C) :=
    lt_of_mul_lt_mul_right hstep1 (le_of_lt hpos)
  have hstep2 : a ^ (1 - 3 * η - ε) ≤ 432 * (δ : ℝ≥0) ^ (127 * ε) := by
    calc a ^ (1 - 3 * η - ε) ≤ 432 * ((δ : ℝ≥0) ^ ε' * C) := hcancel.le
      _ ≤ 432 * (δ : ℝ≥0) ^ (127 * ε) := by gcongr
  -- invert
  have hvpos : (0 : ℝ≥0) < a ^ (1 - 3 * η - ε) * 432⁻¹ :=
    mul_pos (NNReal.rpow_pos ha) (by norm_num)
  have hvu : a ^ (1 - 3 * η - ε) * 432⁻¹ ≤ (δ : ℝ≥0) ^ (127 * ε) := by
    calc a ^ (1 - 3 * η - ε) * 432⁻¹ ≤ (432 * (δ : ℝ≥0) ^ (127 * ε)) * 432⁻¹ := by gcongr
      _ = (δ : ℝ≥0) ^ (127 * ε) := by
          rw [mul_comm (432 : ℝ≥0), mul_assoc, mul_inv_cancel₀ (by norm_num : (432 : ℝ≥0) ≠ 0),
            mul_one]
  have hmono : (a ^ (1 - 3 * η - ε) * 432⁻¹) ^ ((127 : ℝ)⁻¹)
      ≤ ((δ : ℝ≥0) ^ (127 * ε)) ^ ((127 : ℝ)⁻¹) :=
    NNReal.rpow_le_rpow hvu (by norm_num)
  have hvrpos : (0 : ℝ≥0) < (a ^ (1 - 3 * η - ε) * 432⁻¹) ^ ((127 : ℝ)⁻¹) :=
    NNReal.rpow_pos hvpos
  have hCδ' : C ≤ (((δ : ℝ≥0) ^ (127 * ε)) ^ ((127 : ℝ)⁻¹))⁻¹ := by
    refine le_trans hCδ (le_of_eq ?_)
    rw [← NNReal.rpow_mul, ← NNReal.rpow_neg]
    congr 1
    field_simp
  have hCle : C ≤ ((a ^ (1 - 3 * η - ε) * 432⁻¹) ^ ((127 : ℝ)⁻¹))⁻¹ := by
    refine le_trans hCδ' ?_
    gcongr
  -- evaluate the right-hand side
  have heval : ((a ^ (1 - 3 * η - ε) * 432⁻¹) ^ ((127 : ℝ)⁻¹))⁻¹
      = (432 : ℝ≥0) ^ ((127 : ℝ)⁻¹) * a ^ (-((1 - 3 * η - ε) / 127)) := by
    rw [NNReal.mul_rpow, NNReal.inv_rpow, mul_inv, inv_inv, ← NNReal.rpow_mul,
      ← NNReal.rpow_neg, mul_comm]
    congr 2
  rw [heval] at hCle
  refine le_trans hCle ?_
  gcongr
  exact rpow_inv_127_432_le_two

/-! ## The reduction -/

/-- **The target reduces to the regime in which `C` is an `a`-scale constant.**

`H` is `ShadedPlank.reduction_to_slab_atTypicalAngle` with the single extra hypothesis

```
C ≤ 2 * a ^ (-((1 - 3 * η - ε) / 127)),
```

and the conclusion is the target *verbatim*.  So the comparability constant, which the leaf's own
hypotheses control only at the auxiliary scale (`C ≤ δ ^ (-ε)` with `δ ≤ a` an arbitrary power of
`a`), may be assumed to be bounded by a **fixed power of the plank scale `a`**, with an exponent
`(1 - 3 * η - ε) / 127` that is determined by `η` and `ε` alone and is therefore fixed before the
configuration.

The proof is one case split on the scalar budget of
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_smallRadius`: below the budget that theorem closes
the target outright, and above it `ShadedPlank.le_two_mul_rpow_of_budgetExcess` converts the excess
into the displayed bound.  Nothing geometric is used.

This is the exact shape that `Plank.localAngleConcentration_of_preassemblyData` requires of its
angular-stability input (`Cstab0 * a ^ (-εs)` with `Cstab0` and `εs` bound before the
configuration), so it removes the scale mismatch that the module docstring of `Section6Compat.lean`
records as the blocker.  It does **not** by itself make the slab route affordable; see the module
docstring above for the residual `εs < ηL` tension and the finite dyadic split it forces. -/
theorem reduction_to_slab_atTypicalAngle_of_aScaleConstant.{u}
    (H :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type u} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (_hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
      a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
      Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
      (C ≤ 2 * a ^ (-((1 - 3 * η - ε) / 127))) →
    ∃ (s' : Finset ι)
      (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (c1 : ℝ≥0),
      0 < c1 ∧
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s' Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      (∀ x,
        ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε')) :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type u} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (_hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
      a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
      Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
    ∃ (s' : Finset ι)
      (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (c1 : ℝ≥0),
      0 < c1 ∧
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s' Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      (∀ x,
        ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε')  := by
  intro η ε ε' hη hε hε' hgap Ccard D
  obtain ⟨δ₁, hδ₁pos, hδ₁one, hnarrow⟩ :=
    reduction_to_slab_atTypicalAngle_of_smallRadius hη hε hε' hgap Ccard D
  obtain ⟨δ₂, hδ₂pos, hδ₂one, hascale⟩ := H hη hε hε' hgap Ccard D
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, le_trans (min_le_left _ _) hδ₁one, ?_⟩
  intro ι s δ a b hab hb1 Y θ hθ1 C Y'' hδ hδa ha1 hδthr hwin hfull hma hmd h2 hcard
    hθlb hC1 hCδ hYref hYmult htyp hmaxA
  by_cases hcase : 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C * (θ * b) ≤ a ^ η * a
  · exact hnarrow s Y θ hθ1 C Y'' hδ hδa ha1 (le_trans hδthr (min_le_left _ _)) hwin hfull
      hma hmd h2 hcard hθlb hC1 hCδ hYref hYmult htyp hmaxA hcase
  · exact hascale s Y θ hθ1 C Y'' hδ hδa ha1 (le_trans hδthr (min_le_right _ _)) hwin hfull
      hma hmd h2 hcard hθlb hC1 hCδ hYref hYmult htyp hmaxA
      (le_two_mul_rpow_of_budgetExcess hε hgap hδ hδa ha1 hθ1 hb1 hCδ (not_le.mp hcase))

/-- **The target reduces to the version whose typicality constant is an `a`-scale constant.**

`H` is `ShadedPlank.reduction_to_slab_atTypicalAngle` with its angular hypothesis

```
Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C (plankAngleScaleA a).toNNReal
```

replaced by the same predicate at the **fixed** constant `2 * a ^ (-((1 - 3η - ε)/127))`; every
other hypothesis, `C ≤ δ ^ (-ε)` and the two `C`-clauses included, is unchanged, and the conclusion
is the target *verbatim*.

This is the form a producer for the slab route wants:
`Plank.localAngleConcentration_of_preassemblyData` takes its angular-stability input as
`Kakeya.IsTypicalPlankAngle s' Y' P θ (Cstab0 * a ^ (-εs)) A` with `Cstab0` and `εs` bound
**before** the configuration, and here `Cstab0 = 2` and `εs = (1 - 3η - ε)/127` are functions of
`η` and `ε` alone.

The proof is `ShadedPlank.reduction_to_slab_atTypicalAngle_of_aScaleConstant` followed by
`Kakeya.IsTypicalPlankAngle.mono_const`.  Note that it is a genuine reduction and not a
restatement: the replacement is legal only because `C ≤ 2 * a ^ (-((1 - 3η - ε)/127))` holds
throughout the regime that the small-radius theorem leaves open. -/
theorem reduction_to_slab_atTypicalAngle_of_aScaleTypicality.{u}
    (H :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type u} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (_hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
      a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ
        (2 * a ^ (-((1 - 3 * η - ε) / 127)))
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
      Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
    ∃ (s' : Finset ι)
      (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (c1 : ℝ≥0),
      0 < c1 ∧
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s' Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      (∀ x,
        ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε')) :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type u} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (_hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
      a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
      Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
    ∃ (s' : Finset ι)
      (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (c1 : ℝ≥0),
      0 < c1 ∧
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s' Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      (∀ x,
        ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε')  := by
  have H' :
      ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
      ∀ (Ccard : ℝ≥0) (D : ℝ),
      ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
      ∀ {ι : Type u} (s : Finset ι)
        {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
        (Y : ι → ShadedPlank a b hab hb1)
        (θ : ℝ≥0) (_hθ1 : θ ≤ 1) (C : ℝ≥0)
        (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
        0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
        Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
        a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
        (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
        (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
        2 ≤ (δ : ENNReal) ^ (-η) →
        (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
        a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
        ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
        ShadedBody.HasCConstantMultiplicity s Y'' C →
        Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
          (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
        Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
        (C ≤ 2 * a ^ (-((1 - 3 * η - ε) / 127))) →
      ∃ (s' : Finset ι)
        (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (c1 : ℝ≥0),
        0 < c1 ∧
        ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
        ShadedBody.IsRefinement s' Y' s Y'' ∧
        (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
          ShadedBody.fullness s' Y' ∧
        (∀ x,
          ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
          (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
              volume (Metric.closedBall x ((θ * b : ℝ))) ≤
            volume ((⋃ i ∈ s', (Y' i).shade) ∩
              Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
        c1⁻¹ ≤ δ ^ (-ε') := by
    intro η ε ε' hη hε hε' hgap Ccard D
    obtain ⟨δthr, hpos, hone, hH⟩ := H hη hε hε' hgap Ccard D
    refine ⟨δthr, hpos, hone, ?_⟩
    intro ι s δ a b hab hb1 Y θ hθ1 C Y'' hδ hδa ha1 hδthr hwin hfull hma hmd h2 hcard
      hθlb hC1 hCδ hYref hYmult htyp hmaxA hCa
    exact hH s Y θ hθ1 C Y'' hδ hδa ha1 hδthr hwin hfull hma hmd h2 hcard hθlb hC1 hCδ
      hYref hYmult (Kakeya.IsTypicalPlankAngle.mono_const hCa htyp) hmaxA
  intro η ε ε' hη hε hε' hgap Ccard D
  exact reduction_to_slab_atTypicalAngle_of_aScaleConstant H' hη hε hε' hgap Ccard D

/-! ## Why one instance of the slab layer is not enough -/

/-- **The slab route's exponent ledger and the residual regime are incompatible for small `η`.**

This is a statement about the *route*, not about the theorem: it says that a proof of
`ShadedPlank.reduction_to_slab_atTypicalAngle` which runs `Plank.slabwiseDensity_of_preassembly`
**once**, with one pair `(εs, ηL)` chosen before the configuration, cannot cover the regime that
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_smallRadius` leaves open.

The three hypotheses are:

* `hstab : εs < ηL` — literally `hlt` of `Plank.localAngleConcentration_of_preassemblyData`, whose
  `εs` and `ηL` are bound *before* the configuration;
* `hwork : 3 * ηL ≤ 4 * η + εwork` — literally the hypothesis `h3ηL` of
  `Plank.slabwiseDensity_of_preassembly`;
* `hbudget : εwork ≤ 2 * ηL + 129 * ε` — the **ledger step**, and the only one that is not a
  literal hypothesis of a tree theorem.  It is the requirement that the Item-1 constant
  `cBall * cLamBox ^ 2 * a ^ (4η + εwork)` produced by `Plank.slabwiseDensity_of_preassembly`
  dominate the demanded `c1 * a ^ (4η + ε)` at the *tight* end of the residual regime, `δ = a`,
  where `c1 = δ ^ ε' = a ^ (128 ε)`; `cLamBox ≤ a ^ (-ηL)` follows from
  `cLamBox * a ^ ηL ≤ lamScale ≤ 1`, and the extra `ε` absorbs the absolute constant `cBall` as
  `a → 0`.

The conclusion is that `εs < (1 - 3η - ε)/127`, i.e. `εs` is *too small* for the residual regime,
in which `ShadedPlank.le_two_mul_rpow_of_budgetExcess` gives only
`C ≤ 2 * a ^ (-((1 - 3η - ε)/127))` and no better.  Stated at the transverse branch's own exponents
`ε = η / 256` and `η = 1/1000`; the same arithmetic excludes every `η ≤ 1/572` at that `ε`.

The escape is not a bigger gap multiplier — the ledger bound scales with `ε` while
`(1 - 3η - ε)/(g - 1)` scales with `1/g` — but **finitely many** instances, one per dyadic block of
`t = log δ / log a`; the blocks grow geometrically, so `O(log (1/ε))` of them suffice to cover the
whole interval `[1, 1/(127 ε)]`. -/
theorem slabRoute_exponents_incompatible_at_small_eta
    {η ε εs ηL εwork : ℝ} (hη : η = 1 / 1000) (hε : ε = η / 256)
    (hstab : εs < ηL) (hwork : 3 * ηL ≤ 4 * η + εwork)
    (hbudget : εwork ≤ 2 * ηL + 129 * ε) :
    εs < (1 - 3 * η - ε) / 127 := by
  subst hη
  subst hε
  linarith

end ShadedPlank

end
