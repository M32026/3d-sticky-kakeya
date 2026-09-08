/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTowerArrayFibre
public import Kakeya.ShadedUniform

/-!
# `le_window_maxDensity`'s owner, and the `2 ≤ Cu` discharge

Two rows the estimate hand-off named, settled here.

## 1. `le_window_maxDensity` is NOT `le_level_maxDensity`, and its owner is the COUNT

the estimate brief routed `le_window_maxDensity` through
`Kakeya.ML2Core.le_mul_maxDensity_nodesUnder_of_lt_towerDensityArrayFibre`.  That is the wrong
field, and the difference is the one the twin exists to record:

* `IsKatzTaoDividingWindow.le_window_maxDensity` reads the **fine** nodes `nodesUnder b a j`
  **rescaled** to an arbitrary window radius `ρ`, i.e. `(𝒰.cover.tube b j').rescale ρ` — **with
  multiplicity**;
* `IsKatzTaoDividingWindowLevels.le_level_maxDensity` reads the **distinct** level-`c` cells
  `𝒰.cover.tube c j'` over `nodesUnder c a j` — no rescaling, no multiplicity.

**Which is weaker is measured, not guessed.**  `Kakeya.ML2Core.gridModel_window`
(`SpineCountFloorObstruction.lean`) is a configuration on which the *rescaled* clause holds
— "the bottom nodes, rescaled to any window radius, are nearly coincident `ρ`-tubes … by
**multiplicity**, not by many distinct intermediate nodes" — while the distinct-cell count stays
bounded.  So the rescaled clause is the **weaker** one, and the only sound bridge direction is
`le_level_maxDensity ⇒ le_window_maxDensity`.  That direction is not free either: it needs the
convex hull of a family of level-`b` tubes rescaled to `ρ` compared with the hull of the level-`c`
tubes it sits inside, and no existing fact does that.

**The tree's own route does not go through the bridge at all.**  `gridModel_window` produces
`le_window_maxDensity` from a **count** of fine nodes plus two volume bounds, through the existing
`Kakeya.ML2Core.le_mul_maxDensity_of_bounds`.  This file abstracts that route:
`le_mul_maxDensity_of_le_body` and `le_window_maxDensity_of_card` take the containing body and the
per-tube volume floor as parameters, so no geometric fact is spent here and the caller supplies
whichever it has.

> **Owner, on the record: `le_window_maxDensity`'s owner is the count of `nodesUnder b a j`, i.e.
> the same quantity as `FloorHypothesisAt`'s third conjunct — not the density band and not the
> fibre array.**  Its cost is the ratio of the two dimensional tube-volume constants
> (`Tube.volume_le.C 3 / Tube.le_volume.c 3`, `δ`-free) together with whatever bounds the inset
> band gives on `ρ_a / ρ`; both enter through `hx` and neither is fixed here.

## 2. `2 ≤ Cu`, discharged by name

The joint-bin theorems of `SpineLevelBandDescent.lean` ask `2 ≤ Cu`, where A1's factor two is paid
into the tower's own uniformity constant.  Post-`HUNI-TIGHT` the constant is
`ShadedTube.ssfUniformConst n = max (uniformConst n) 4`, so it is bounded below by `4`:
`four_le_ssfUniformConst` and `two_le_ssfUniformConst` below.  Any consumer sitting at a `Cu` that
is **not** bracketed below by `4` must say so; every site this run reaches is at
`ssfUniformConst 3`.

## 3. `FloorHypothesisAt` on `refinedHierarchy`: the A1-b column, per conjunct

Recorded here because the same Condition-R reading has to be checked on it and it is the largest
row left.  `FloorHypothesisAt β ϖ ε₁ gain dens η' 𝒰 a b m` is `∃ p, a ≤ p ∧` three conjuncts
(`SpineFloorShapeM1.lean`, the `Iff.rfl` unfolding):

1. **the parent is beyond the inset** — `∀ m'` in the `ε_d`-inset window range, `p < m'`.  Pure
   grid arithmetic; **no family, no shading, no density**.  Level pair: `(a,b)` through the range.
2. **the parent-density row** — `∀ jθ ∈ 𝒰.cover.indexSet a`,
   `Δ_max(𝒰.nodesUnder p a jθ) ≤ δ^{-2η'}`.  An **upper** bound on a maximal density, so Condition R
   puts it safely on `nodesUnder` in both senses and the **containment** array produces it
   (`maxDensity_nodesUnder_le_of_towerGood`).  Family: the tower's own; shading: none.  Level pair:
   `(a,p)`.  This is `ParentAdmissible 𝒰 η' a a` at `p := a`.
3. **the count floor** — `∀ jθ`, `∀ jp ∈ 𝒰.nodesUnder p a jθ`, `∀ m'` in range with `p < m'`,
   `(ρ_p/ρ_{m'})^{2+4ζ} ≤ #(𝒰.nodesUnder m' p jp)`.  A **lower** bound on a *cardinality*, not on a
   density, so the Condition R does not apply verbatim; but the same monotonicity does — a count
   on `nodesUnder` is the **larger** set, hence the *weaker* floor, so the field as stated is safe
   and a witness produced on the fibre (`assignFibre`) transfers to it by
   `Tube.UniformTubeSet.assignFibre_subset_nodesUnder` and `Finset.card_le_card`.  Family: the
   tower's own; shading: none.  Level pair: `(p,m')` inside `(a,b)`.

**Producer:** `Kakeya.ML2Core.floorHypothesisAt_of_windowLevels` (existing) takes the window plus
`ParentAdmissible` (conjunct 2), `FillAt` and four scalar rows, and returns the whole predicate; so
conjunct 3 is *derived* there and is not a separate obligation.  What the (F) route still owes on
`refinedHierarchy` is `ParentAdmissible` and `FillAt`, both geometric, with
`fillAt_of_biasedMaximizer` the existing per-node engine for the second.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `four_le_ssfUniformConst`, `two_le_ssfUniformConst` | none | none |
| `sum_div_volume_le_maxDensity`, `le_mul_maxDensity_of_le_body` | abstract | none |
| `le_window_maxDensity_of_card` | the tower's `u`, `T`; no shading | `(a,b)` at radius `ρ` |

## A1-a

No `GridUniformCore`; no (F)-branch interface statement is defined or altered.  The window field is
*supplied by shape*.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory Tube

namespace Kakeya.ML2Core

section UniformConstant

/-- **`ssfUniformConst` is at least `4`** — `max (uniformConst n) 4`, `ShadedUniform.lean:895`. -/
theorem four_le_ssfUniformConst (n : ℕ) : 4 ≤ ShadedTube.ssfUniformConst n :=
  le_max_right _ _

/-- **`2 ≤ Cu` at the tower constant this run carries**, which is what the joint-bin theorems of
`SpineLevelBandDescent.lean` ask for.  `δ`-free, and it enters no exponent account. -/
theorem two_le_ssfUniformConst (n : ℕ) : 2 ≤ ShadedTube.ssfUniformConst n :=
  le_trans (by norm_num : (2 : NNReal) ≤ 4) (four_le_ssfUniformConst n)

end UniformConstant

section DensityFromCount

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- **The density of a family inside a test body is at most its maximal density.**  The
`densityInConvexHulliUnion` half of `Kakeya.maxDensity`'s definition, in the quotient form
`le_mul_maxDensity_of_bounds` consumes. -/
theorem sum_div_volume_le_maxDensity {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} (hsub : ∀ i ∈ s, W i ≤ K) :
    (∑ i ∈ s, volume (W i).carrier) / volume K.carrier ≤ Kakeya.maxDensity s W := by
  refine ENNReal.div_le_of_le_mul ?_
  exact Kakeya.sum_volume_le_maxDensity_mul_volume' hsub

/-- **The count-to-density device, abstract.**  A family lying inside a test body `K` of positive
finite volume, and a numerical inequality `x · |K| ≤ C · ∑ |W i|`, give `x ≤ C · Δ_max`.

This is the shape that produces `IsKatzTaoDividingWindow.le_window_maxDensity`; the geometry lives
entirely in the caller's `hsub` and `hx`, so the device itself is free of dimensional constants. -/
theorem le_mul_maxDensity_of_le_body {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} (hsub : ∀ i ∈ s, W i ≤ K)
    (hK0 : volume K.carrier ≠ 0) (hKtop : volume K.carrier ≠ ⊤)
    {x C : ENNReal} (hx : x * volume K.carrier ≤ C * ∑ i ∈ s, volume (W i).carrier) :
    x ≤ C * Kakeya.maxDensity s W := by
  have h1 : x ≤ (C * ∑ i ∈ s, volume (W i).carrier) / volume K.carrier := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hK0) (Or.inl hKtop)]
    exact hx
  refine h1.trans ?_
  calc (C * ∑ i ∈ s, volume (W i).carrier) / volume K.carrier
      = C * ((∑ i ∈ s, volume (W i).carrier) / volume K.carrier) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
    _ ≤ C * Kakeya.maxDensity s W :=
        mul_le_mul' le_rfl (sum_div_volume_le_maxDensity hsub)

/-- **The same device driven by a cardinality and a per-member volume floor** — the form the window
field needs, where the count is the quantity in play. -/
theorem le_mul_maxDensity_of_card {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} (hsub : ∀ i ∈ s, W i ≤ K)
    (hK0 : volume K.carrier ≠ 0) (hKtop : volume K.carrier ≠ ⊤)
    {v₀ : ENNReal} (hv₀ : ∀ i ∈ s, v₀ ≤ volume (W i).carrier)
    {x C : ENNReal} (hx : x * volume K.carrier ≤ C * ((s.card : ENNReal) * v₀)) :
    x ≤ C * Kakeya.maxDensity s W := by
  refine le_mul_maxDensity_of_le_body hsub hK0 hKtop (le_trans hx (mul_le_mul' le_rfl ?_))
  calc ((s.card : ENNReal) * v₀) = ∑ _i ∈ s, v₀ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ s, volume (W i).carrier := Finset.sum_le_sum hv₀

end DensityFromCount

section WindowField

universe u

variable {ι : Type u} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **`le_window_maxDensity`'s producer, in the field's own shape**, from the **count** of
`nodesUnder b a j` — the owner named in the module docstring.

Everything geometric is a parameter: `K` is the body containing the rescaled fine tubes (in the
source's run, the level-`a` tube inflated by `ρ`), `v₀` the per-tube volume floor at radius `ρ`
(`Tube.le_volume`), and `hx` the numerical inequality the inset band and the two dimensional
constants supply.  So this file spends no geometry and fixes no constant; it records **which**
quantity the field rests on.

**Family/shading:** the tower's `u`, `T`; no shading — the window is about tubes only.
**Level pair:** `(a,b)` at the window radius `ρ`. -/
theorem le_window_maxDensity_of_card (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    {a b : ℕ} {j : ι} {ρ : NNReal}
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (hK0 : volume K.carrier ≠ 0) (hKtop : volume K.carrier ≠ ⊤)
    (hsub : ∀ j' ∈ 𝒰.nodesUnder b a j,
      ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody ≤ K)
    {v₀ : ENNReal}
    (hv₀ : ∀ j' ∈ 𝒰.nodesUnder b a j, v₀ ≤ volume ((𝒰.cover.tube b j').rescale ρ).carrier)
    {x Cstar : ENNReal}
    (hx : x * volume K.carrier
      ≤ Cstar * (((𝒰.nodesUnder b a j).card : ENNReal) * v₀)) :
    x ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder b a j)
        (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody) :=
  le_mul_maxDensity_of_card hsub hK0 hKtop hv₀ hx

/-- **Firing control: the count is load-bearing.**  At `v₀ = 0` — no volume floor on the rescaled
tubes — the hypothesis `hx` degenerates to `x · |K| ≤ 0`, so the device delivers nothing unless the
count is paired with a genuine per-tube floor.  Recorded so that a caller cannot satisfy `hx`
vacuously and believe the field has been produced. -/
theorem le_window_maxDensity_of_card_vacuous_at_zero
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) {a b : ℕ} {j : ι}
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (hK0 : volume K.carrier ≠ 0)
    {x Cstar : ENNReal}
    (hx : x * volume K.carrier ≤ Cstar * (((𝒰.nodesUnder b a j).card : ENNReal) * 0)) :
    x = 0 := by
  rw [mul_zero, mul_zero, nonpos_iff_eq_zero, mul_eq_zero] at hx
  exact hx.resolve_right hK0

end WindowField

end Kakeya.ML2Core

end
