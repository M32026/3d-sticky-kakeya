/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Section6CompatThicken

/-!
# The constant in the thickening obligation is free

`ShadedPlank.reduction_to_slab_atTypicalAngle_of_thickening` records the residue of
`ShadedPlank.reduction_to_slab_atTypicalAngle` as the scalar inequality

```
54 * (δ ^ ε' * a ^ (4 * η) * a ^ ε) * C * |N_{θb}(U(s, Y''))| ≤ |U(s, Y''))|.
```

Three of the five factors on the left are **not** part of the obligation.

* `C` and `δ ^ ε'` cancel: the hypotheses give `C ≤ δ ^ (-ε)` and `128 * ε ≤ ε'`, so
  `δ ^ ε' * C ≤ δ ^ (ε' - ε) ≤ δ ^ ε`, which is at most `1`.
* What is left, `δ ^ (ε' - ε)`, is a *free small factor*: the reduction is allowed to name its own
  smallness threshold `δthr` before seeing the scale, and `δ ^ (ε' - ε) ≤ δthr ^ (ε' - ε)` can be
  pushed below any prescribed `kappa / 54`.

So the numeric constant `54` is not binding either, and the genuine residue is the *exponent*
statement

```
∀ kappa > 0,  kappa * a ^ (4 * η + ε) * |N_{θb}(U(s, Y''))| ≤ |U(s, Y''))|,
```

with `kappa` chosen by the producer.
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_smallThickening` is that statement, proved: for
every `kappa > 0` there is a threshold below which the displayed inequality closes the leaf.
Equivalently, the whole remaining content of the leaf is the bound

```
|N_{θb}(U(s, Y''))| / |U(s, Y''))| ≤ kappa⁻¹ * a ^ (-(4 * η + ε))
```

on the *thickening ratio* of the shading union at radius `θ b`, at one (any) constant `kappa⁻¹`.

This matters for two reasons.

1. It removes the two scale parameters from the obligation.  A producer no longer has to track
   `δ` or `C` at all: the residue mentions only `a`, `θ`, `b` and the configuration, and the
   δ-scale/plank-scale mismatch that the `Section6Compat.lean` docstring records as the blocker
   does **not** appear in it.
2. It fixes the size of the prize.  Any route that needs a constant factor of room — a
   bounded-overlap covering constant, a Vitali constant, a dyadic-pigeonhole loss of a bounded
   number of levels — gets it for free.  Only a loss that is a *power of `a`* costs anything.

No new geometry is proved here; this is exactly the observation that two of the recorded factors
were slack, plus the threshold bookkeeping that turns the third into an arbitrary constant.
-/

@[expose] public section

open MeasureTheory Metric
open scoped NNReal Real ENNReal

noncomputable section

namespace ShadedPlank

/-- **`δ ^ ε' * C ≤ δ ^ (ε' - ε)` under the leaf's own hypotheses.**

The one arithmetic step behind `ShadedPlank.reduction_to_slab_atTypicalAngle_of_smallThickening`:
the constant `C` that the leaf hands the producer is bounded by `δ ^ (-ε)`, which cancels one of
the `ε'` powers of `δ`. -/
theorem rpow_mul_le_rpow_sub_of_le_rpow_neg {δ C : ℝ≥0} {ε ε' : ℝ}
    (hδ : 0 < δ) (hC : C ≤ δ ^ (-ε)) :
    δ ^ ε' * C ≤ δ ^ (ε' - ε) := by
  have hδne : (δ : ℝ≥0) ≠ 0 := hδ.ne'
  calc δ ^ ε' * C ≤ δ ^ ε' * δ ^ (-ε) := by gcongr
    _ = δ ^ (ε' + -ε) := (NNReal.rpow_add hδne _ _).symm
    _ = δ ^ (ε' - ε) := by rw [sub_eq_add_neg]

/-- **The thickening obligation with an arbitrary constant** — the leaf's genuine residue.

`ShadedPlank.reduction_to_slab_atTypicalAngle` verbatim (same binders, same hypotheses, same
`128 * ε ≤ ε'`, same conclusion), with exactly one hypothesis inserted, namely

```
kappa * (a ^ (4 * η) * a ^ ε) * |N_{θb}(U(s, Y''))| ≤ |U(s, Y''))|
```

for a positive `kappa` **chosen by the caller, before everything else**.  Compared with
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_thickening` the inserted hypothesis is strictly
weaker as soon as `kappa < 54`: the factors `δ ^ ε'` and `C` are gone, and the numeric constant is
the caller's.

The threshold is `min δthr₀ (min 1 ((kappa / 54) ^ (ε' - ε)⁻¹))` with `δthr₀` the threshold of the
thickening reduction; `ε' - ε ≥ ε > 0` is where `128 * ε ≤ ε'` is used, and it is used only here —
and it needs only `2 * ε ≤ ε'` of it. -/
theorem reduction_to_slab_atTypicalAngle_of_smallThickening (kappa : ℝ≥0) (hkappa : 0 < kappa) :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type*} (s : Finset ι)
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
      (((kappa * (a ^ (4 * η) * a ^ ε) : ℝ≥0) : ENNReal)
          * volume (Metric.cthickening ((θ * b : ℝ≥0) : ℝ) (⋃ i ∈ s, (Y'' i).shade))
        ≤ volume (⋃ i ∈ s, (Y'' i).shade)) →
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
  classical
  obtain ⟨δthr₀, hδthr₀pos, hδthr₀le, hred⟩ :=
    reduction_to_slab_atTypicalAngle_of_thickening (η := η) (ε := ε) (ε' := ε') hη hε hε' hgap
      Ccard D
  -- `ε' - ε ≥ ε > 0`: the only place `128 * ε ≤ ε'` is used.
  have hgap' : 0 < ε' - ε := by linarith
  set δκ : ℝ≥0 := (kappa / 54) ^ (ε' - ε)⁻¹ with hδκ
  have hδκpos : 0 < δκ := NNReal.rpow_pos (by positivity)
  refine ⟨min δthr₀ (min 1 δκ), lt_min hδthr₀pos (lt_min one_pos hδκpos),
    (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  intro ι s δ a b hab hb1 Y θ hθ1 C Y'' hδ hδa ha1 hδthr hwin hfull hma hmd h2 hcard
    hθlb hC1 hCδ hYref hYmult htyp hmaxA hthick
  refine hred s Y θ hθ1 C Y'' hδ hδa ha1 (hδthr.trans (min_le_left _ _)) hwin hfull hma hmd
    h2 hcard hθlb hC1 hCδ hYref hYmult htyp hmaxA ?_
  -- `54 * (δ ^ ε' * C) ≤ 54 * δ ^ (ε' - ε) ≤ 54 * δκ ^ (ε' - ε) = kappa`
  have h1 : (δ : ℝ≥0) ^ ε' * C ≤ δ ^ (ε' - ε) :=
    rpow_mul_le_rpow_sub_of_le_rpow_neg hδ hCδ
  have hδle : (δ : ℝ≥0) ≤ δκ := hδthr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h3 : δκ ^ (ε' - ε) = kappa / 54 := by
    rw [hδκ, ← NNReal.rpow_mul, inv_mul_cancel₀ hgap'.ne', NNReal.rpow_one]
  have hmain : (54 : ℝ≥0) * ((δ : ℝ≥0) ^ ε' * C) ≤ kappa := by
    calc (54 : ℝ≥0) * ((δ : ℝ≥0) ^ ε' * C) ≤ 54 * δ ^ (ε' - ε) := by gcongr
      _ ≤ 54 * δκ ^ (ε' - ε) := by gcongr
      _ = 54 * (kappa / 54) := by rw [h3]
      _ = kappa := by field_simp
  -- it suffices to dominate the recorded coefficient by `kappa * (a ^ (4η) * a ^ ε)`
  have hcoe : (54 : ℝ≥0) * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C
      ≤ kappa * (a ^ (4 * η) * a ^ ε) := by
    have hstep : (54 : ℝ≥0) * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C
        = (54 * ((δ : ℝ≥0) ^ ε' * C)) * (a ^ (4 * η) * a ^ ε) := by ring
    rw [hstep]
    gcongr
  exact le_trans (by gcongr) hthick

end ShadedPlank

end
