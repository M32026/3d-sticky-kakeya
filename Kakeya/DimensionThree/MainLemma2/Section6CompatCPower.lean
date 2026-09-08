/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Section6CompatBudget
public import Kakeya.DimensionThree.MainLemma2.Section6CompatDensity

/-!
# The Step-3 obligation stated in the currency the producer controls: powers of `C`

`ShadedPlank.reduction_to_slab_atTypicalAngle_of_ballDensity` asks its producer for a refinement
coefficient `r` and a ball-density threshold `t` bounded below in powers of the **auxiliary scale**,

```
δ ^ ε' * a ^ ε * C ≤ r          and          δ ^ ε' * a ^ (4 * η) * a ^ ε ≤ t.
```

That is not what the Step-3 assembly controls.  `Plank.slabwiseDensity_of_preassembly` returns
`r = (256 · Nov · Cmult)⁻¹ · a ^ εint` and `t = cBall · cLamBox ^ 2 · a ^ (4η + εwork)`, and every
one of `cBall⁻¹`, `Cmult`, `Nov`, `cTan`, `lamLower⁻¹` is bounded by a **power of the constant `C`
the leaf hands it**, times an absolute constant — that is the accounting of
`Plank.routePower_of_bounds`.  Between the two spellings sits exactly one conversion, and
`Section6CompatBudget.lean` has already reduced that conversion to a decidable arithmetic question:
`Plank.RouteAffordsCPower ε ε' k Kabs` holds iff `k * ε < ε'` (`Plank.not_routeAffordsCPower`,
`Plank.routeAffordsCPower_of_strict`).

This file performs that conversion once, so that no producer has to.
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_cPowerBallDensity` is the target statement
verbatim with the obligation restated as

```
(K * C ^ k)⁻¹ * a ^ ε ≤ r        and        (K * C ^ k)⁻¹ * a ^ (4 * η) * a ^ ε ≤ t,
```

with `K` and `k` quantified **before** the exponents and before the configuration — the position a
route constant actually occupies — and with the single numeric side condition

```
(k + 1) * ε < ε'.
```

The `+ 1` is the explicit `C` that the `ballDensity` spelling carries on its own `r` clause; the
`t` clause needs only `k * ε < ε'` and is covered by the same hypothesis because `1 ≤ C`.

## What this changes, in one line per gap multiplier

* At the gap the leaf currently offers, `2 * ε ≤ ε'`, the side condition `(k + 1) * ε < ε'` forces
  `k < 1`.  The Step-3 route has `k ≥ 5` unconditionally (`Plank.routePower_floor`), so the
  hypothesis of this theorem is **unsatisfiable** for that route — which is
  `Plank.step3_floor_refutes_two_eps` seen from the other side, and is recorded here as
  `ShadedPlank.cPower_hypothesis_fails_at_gap_two`.
* At `128 * ε ≤ ε'` the side condition holds for **every `k ≤ 126`**, which covers every trace of
  the route's `C`-power on the record (see `ShadedPlank.cPower_hypothesis_of_gap_128`).

### Which trace of the route's `C`-power is right

Two were on the record, `k = 57` and `k = 105`, and they differ only in the exponent `m` of
`Nov ≤ K₅ * C ^ m` in `Plank.routePower_of_bounds` (`k = 9 + 2 m`).  The `Nov` witness is
`⌈(2 * (4 * K + r) / r) ^ 12⌉₊` with `K` and `r` from `exists_refPose_constants ρ Cs`, where
`K = 1 + ρ + 2 Cs + (Cs + 2 ρ Cs)` and `r = 1 / (1024 K) / 2`.  So `K / r` is of order `K ^ 2` and
`Nov` is of order `(K ^ 2) ^ 12 = K ^ 24`, and everything turns on whether `K` is linear or
quadratic in `C`:

* evaluated at the **unenlarged** pair `(Cset, Cang)`, which are absolute, `ρ = 2 Cang + 2 C` is
  linear and `Cs` is absolute, so `K` is linear, `m = 24` and `k = 57`;
* evaluated at the **enlarged** pair `(Cset', Cang')`, `Plank.slabwiseDensity_of_preassembly`
  requires `Cset + 4 * (2 * Cang + 4 * C) + 8 ≤ Cset'` and `2 * Cang + 4 * C ≤ Cang'`, so **both**
  are of order `C`, the cross term `2 ρ Cs` makes `K` quadratic, `m = 48` and `k = 105`.

`Plank.slabwiseDensity_of_preassembly` demands **one** `Nov` that bounds *both* overlaps — the
pointwise one at `(Cset, Cang)` and the index one at `(Cset', Cang')` — so the enlarged evaluation
is the binding one and **`k = 105` is the correct trace**.  The `k = 57` reading looks only at the
pointwise clause, which is the unenlarged one, and undercounts.  `128` clears `105` as well:
`(105 + 1) * ε = 106 * ε < 128 * ε ≤ ε'`, margin `22`.

So the conversion is not the obstruction; the gap multiplier is, and `128` clears the whole
recorded range `[5, 105]`.
-/

@[expose] public section

open MeasureTheory Metric
open scoped NNReal Real ENNReal

noncomputable section

namespace ShadedPlank

/-! ## The two numeric readings of the side condition -/

/-- **At the gap multiplier `128` the side condition is free for every `k ≤ 126`.**

`(k + 1) * ε ≤ 127 * ε < 128 * ε ≤ ε'`.  The bound `126` is stated rather than either trace of the
route's power, so that the lemma is insensitive to which is right: it covers `k = 5` (the
irreducible floor of `Plank.routePower_floor`), `k = 57` (the unenlarged reading) and `k = 105`
(the enlarged reading, which the module docstring argues is the correct one). -/
theorem cPower_hypothesis_of_gap_128 {ε ε' k : ℝ} (hε : 0 < ε) (hk : k ≤ 126)
    (hgap : 128 * ε ≤ ε') : (k + 1) * ε < ε' := by
  have h1 : (k + 1) * ε ≤ 127 * ε := by nlinarith
  have h2 : (127 : ℝ) * ε < 128 * ε := by nlinarith
  linarith

/-- **At the gap multiplier the leaf currently offers, `2`, the side condition is unsatisfiable for
the Step-3 route.**

`Plank.routePower_floor` gives `5 ≤ k`, so `(k + 1) * ε ≥ 6 * ε > 2 * ε = ε'`.  This is the same
verdict as `Plank.step3_floor_refutes_two_eps`, stated about the side condition of
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_cPowerBallDensity` rather than about
`Plank.RouteAffordsCPower`, so that a reader of this file cannot mistake the conversion below for a
route. -/
theorem cPower_hypothesis_fails_at_gap_two {ε ε' k : ℝ} (hε : 0 < ε) (hk : 5 ≤ k)
    (hgap : ε' = 2 * ε) : ¬ ((k + 1) * ε < ε') := by
  rw [hgap]
  have h : (6 : ℝ) * ε ≤ (k + 1) * ε := by nlinarith
  have h2 : (2 : ℝ) * ε < 6 * ε := by nlinarith
  linarith

/-! ## The conversion -/

/-- **`ShadedPlank.reduction_to_slab_atTypicalAngle` modulo a Step-3 obligation stated in powers
of `C`.**

The target statement verbatim — same binders, same hypotheses, same conclusion — with exactly one
hypothesis inserted, and with `K`, `k` and the side condition `(k + 1) * ε < ε'` fixed before the
configuration.  The inserted hypothesis is the literal output shape of
`Plank.slabwiseDensity_of_preassembly` once each of its constants is bounded by an absolute
constant times a power of `C`, which is what `Plank.routePower_of_bounds` does.

The gap binder `128 * ε ≤ ε'` is the leaf's own, carried verbatim; the side condition
`(k + 1) * ε < ε'` is the *extra* hypothesis, and `ShadedPlank.cPower_hypothesis_of_gap_128`
discharges it from the binder for every `k ≤ 126`.  (Before the 2026-09 gap change the binder read
`2 * ε ≤ ε'` and was derivable from `1 ≤ k` and the side condition; at `128` it is not, which is
exactly what `ShadedPlank.cPower_hypothesis_fails_at_gap_two` records.)

No smallness threshold beyond the one `Plank.routeAffordsCPower_of_strict` names is used, and that
one is explicit: `K ^ (-(ε' - (k + 1) * ε)⁻¹)`. -/
theorem reduction_to_slab_atTypicalAngle_of_cPowerBallDensity
    (K : ℝ≥0) (hK : 1 ≤ K) (k : ℝ) (hk : 1 ≤ k) :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' → (k + 1) * ε < ε' →
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
      (∃ (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (r t : ℝ≥0),
        ShadedBody.IsCRefinement s Y' s Y'' r ∧
        (K * C ^ k)⁻¹ * a ^ ε ≤ r ∧
        (K * C ^ k)⁻¹ * a ^ (4 * η) * a ^ ε ≤ t ∧
        (∀ x,
          ((⋃ i ∈ s, (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
          (t : ENNReal) * volume (Metric.closedBall x ((θ * b : ℝ))) ≤
            volume ((⋃ i ∈ s, (Y' i).shade) ∩
              Metric.closedBall x (redPlankTube.ballDilation * θ * b)))) →
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
  intro η ε ε' hη hε hε' hgap hpow Ccard D
  classical
  have hk0 : (0 : ℝ) ≤ k + 1 := by linarith
  obtain ⟨δthr₀, h0pos, h0le, hbd⟩ :=
    reduction_to_slab_atTypicalAngle_of_ballDensity (η := η) (ε := ε) (ε' := ε') hη hε hε' hgap
      Ccard D
  obtain ⟨δthr₁, h1pos, h1le, haff⟩ :=
    Plank.routeAffordsCPower_of_strict (ε := ε) (ε' := ε') (k := k + 1) hk0 hpow (Kabs := K) hK
  refine ⟨min δthr₀ δthr₁, lt_min h0pos h1pos, (min_le_left _ _).trans h0le, ?_⟩
  intro ι s δ a b hab hb1 Y θ hθ1 C Y'' hδ hδa ha1 hδthr hwin hfull hma hmd h2 hcard
    hθlb hC1 hCδ hYref hYmult htyp hmaxA hdata
  obtain ⟨Y', r, t, hCr, hr, ht, hitem⟩ := hdata
  -- the affordability instance at this scale and this constant
  have hKC : K * C ^ (k + 1) ≤ δ ^ (-ε') :=
    haff δ C hδ (hδthr.trans (min_le_right _ _)) hC1 hCδ
  have hCne : (C : ℝ≥0) ≠ 0 := (lt_of_lt_of_le zero_lt_one hC1).ne'
  have hδne : (δ : ℝ≥0) ≠ 0 := hδ.ne'
  have hCk1 : (C : ℝ≥0) ^ (k + 1) = C ^ k * C := by
    rw [NNReal.rpow_add hCne, NNReal.rpow_one]
  have hCkpos : (0 : ℝ≥0) < C ^ k := NNReal.rpow_pos (lt_of_lt_of_le zero_lt_one hC1)
  have hMne : (K * C ^ k : ℝ≥0) ≠ 0 :=
    (mul_pos (lt_of_lt_of_le zero_lt_one hK) hCkpos).ne'
  -- `δ ^ ε' * δ ^ (-ε') = 1`
  have hδcancel : (δ : ℝ≥0) ^ ε' * δ ^ (-ε') = 1 := by
    rw [← NNReal.rpow_add hδne]
    simp
  -- the `t` clause: `δ ^ ε' ≤ (K * C ^ k)⁻¹`
  have hstep_t : (δ : ℝ≥0) ^ ε' ≤ (K * C ^ k)⁻¹ := by
    refine (NNReal.le_inv_iff_mul_le hMne).mpr ?_
    have hrpow : (C : ℝ≥0) ^ k ≤ C ^ (k + 1) :=
      NNReal.rpow_le_rpow_of_exponent_le hC1 (by linarith)
    have hmono : (K : ℝ≥0) * C ^ k ≤ K * C ^ (k + 1) := by gcongr
    calc (δ : ℝ≥0) ^ ε' * (K * C ^ k) ≤ δ ^ ε' * (K * C ^ (k + 1)) := by gcongr
      _ ≤ δ ^ ε' * δ ^ (-ε') := by gcongr
      _ = 1 := hδcancel
  -- the `r` clause: `δ ^ ε' * C ≤ (K * C ^ k)⁻¹`
  have hstep_r : (δ : ℝ≥0) ^ ε' * C ≤ (K * C ^ k)⁻¹ := by
    refine (NNReal.le_inv_iff_mul_le hMne).mpr ?_
    calc (δ : ℝ≥0) ^ ε' * C * (K * C ^ k) = δ ^ ε' * (K * (C ^ k * C)) := by ring
      _ = δ ^ ε' * (K * C ^ (k + 1)) := by rw [hCk1]
      _ ≤ δ ^ ε' * δ ^ (-ε') := by gcongr
      _ = 1 := hδcancel
  refine hbd s Y θ hθ1 C Y'' hδ hδa ha1 (hδthr.trans (min_le_left _ _)) hwin hfull hma hmd
    h2 hcard hθlb hC1 hCδ hYref hYmult htyp hmaxA ⟨Y', r, t, hCr, ?_, ?_, hitem⟩
  · calc (δ : ℝ≥0) ^ ε' * a ^ ε * C = (δ ^ ε' * C) * a ^ ε := by ring
      _ ≤ (K * C ^ k)⁻¹ * a ^ ε := by gcongr
      _ ≤ r := hr
  · calc (δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε ≤ (K * C ^ k)⁻¹ * a ^ (4 * η) * a ^ ε := by gcongr
      _ ≤ t := ht

end ShadedPlank

end
