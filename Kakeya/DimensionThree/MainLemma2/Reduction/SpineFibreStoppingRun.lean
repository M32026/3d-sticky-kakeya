/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineWindowFieldsFromArrays
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineLevelBandDescent

/-!
# The stopping run on the fibre array, and the dividing window it produces

 item 1.  The previous hand measured that `exists_fixedTowerCutsFibre`'s three
inputs are supplied except `hsplit`, whose `hdata` — the source's *"insert `m`"* step,
l.5289-5297 — *"is the stopping-time step; nothing supplies it"*.  **This file supplies it, and
the reason it was not supplied before is a reading, not a missing estimate.**

## Why `hdata` looked hard: the existing splitter is the *mirror* of Part (B)'s

`Kakeya.ML2Core.towerGoodFibre_split_of_calibration` (existing, untouched) asks for

> `∃ m, a + w ≤ m ∧ m + w ≤ b ∧ Z_fib(a,m) ≤ E · Z_fib(a,b) ∧ TowerGoodFibre (j+1) m b`.

Its `(H4)` component varies the **fine** index (`Z_fib(a,m)` against `Z_fib(a,b)`), and its
`TowerGood` component is at the pair `(m,b)`, which shares the **right** endpoint.  That is
**Part (A)**'s reading, l.2726-2728: *"descendant-count regularity gives `X_F(k,m) ≤ 4X_F(k,b)`"*
— a genuine hypothesis, at `E = 4`, and one the source states only for the `C_F` array.

Part (B) is different, and the source says so in the same paragraph (l.2739-2745): it applies
`lemabstractstopping` not to `Z` but to the **transposed** array
`X̃(k,l) = Z(M-l, M-k)`, adding *"This also explains why Part (B) is not merely Part (A) with
names changed."*  Undoing the transposition `k ↦ M-k` on the split step turns the source's
`(H4)` `X̃(a,m) ≤ E X̃(a,b)` into

> `Z_fib(c,b) ≤ E · Z_fib(a,b)`   for `a ≤ c ≤ b` — the **anchor** index varies,

and turns the failed-witness component into `Z_fib(a,c) ≤ bound (j+1) a c`, at the pair `(a,c)`
which shares the **left** endpoint.  Both differences are exactly the transposition.

## The consequence: Part (B)'s `(H4)` is free, at `E = 1`

`towerDensityArrayFibre_anti_left` proves `Z_fib(a',c) ≤ Z_fib(a,c)` for `a ≤ a'` outright.  Its
whole content is Definition 2.1(ii)'s compatible-partition clause read on the *classes*: a
level-`a'` class is contained in the level-`a` class of any of its members
(`Tube.ChainCoverSystem.assign_eq_of_le`), so the thread cell `𝕋_c⟨S'⟩` is contained in
`𝕋_c⟨S⟩` for the ancestor `S`, and `Kakeya.maxDensity_mono` finishes.  No geometry, no constant,
no `Cu`.

**So the stopping run on the fibre array has no undischarged input.**
`exists_fibreStoppingRun` is unconditional in the estimates: it consumes only the entry bound
(H3, which the source *assumes* at l.2683-2684), the `η`-schedule monotonicity, and the
calibration `δ^{-ε²η₁/2} ≥ E` — all three copied, never fitted.  `(H1)` and `(H2)` are **not**
inputs of the run at all: the "at most `N` pieces" bound comes from the margin `w` with
`M ≤ w·N` (`Kakeya.MultiScaleFac.exists_maximal_cuts_abstract_state_margin`), not from the
crude exponent.  `(H1)`/`(H2)` are needed only for the source's *tail* conclusion
`eqdividingKfirst`, which is the one row this file leaves named (see below).

## The middle field, and the price of the containment reading — measured, `Cu`

`Kakeya.ML2Core.middle_maxDensity_le` is stated on `nodesUnder`, and the run tracks the fibre
array, so the fibre `TowerGood` does **not** deliver it: the fibre array is the *smaller* one
(`towerDensityArrayFibre_le_towerDensityArray`).
`maxDensity_nodesUnder_le_mul_towerDensityArrayFibre` closes the gap in the other direction, at
one factor `Cu` and by Definition 2.1(ii) **bounded overlap**:

every level-`b` node contained in `T_a(j)` is assigned from some leaf, hence lies in the thread
cell of *that leaf's* level-`a` node `j'`, and `T_{j'}` shares that leaf with `T_a(j)` — so `j'`
ranges over the `≤ Cu` nodes the `boundedOverlap` clause permits at `V = T_a(j)`.  Summing
(`Kakeya.maxDensity_le_sum_of_subset_biUnion`) gives
`Δ_max(nodesUnder b a j) ≤ Cu · Z_fib(a,b)`.

This **refines** `SpineTowerArrayFibre.lean`'s docstring sentence *"and that is the only relation
between them"*: the reverse relation exists and its price is one `Cu`, which is `δ`-free
; the sentence stays true as a statement
about *free* relations.

## What is produced, and what is named

`isKatzTaoDividingWindowLevels_of_fibreRun` takes **one adjacent piece `(a,b)` of the run that is
Long** and produces `Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels` — the whole twin — from:

| field | direction | stated on | witness produced on | supplied by |
|---|---|---|---|---|
| `scale_sep` etc. | — | grid | — | `scale_sep_of_width` (existing) |
| `coarse_maxDensity_le` | upper | level family | fibre array | `hcoarse`, **named** (see below) |
| `middle_maxDensity_le` | upper | `nodesUnder` | **fibre** array, `+Cu` | the run's `TowerGood` |
| `le_window_maxDensity` | lower | `nodesUnder` | count | `hwindow`, **named** (the estimate item 2) |
| `le_level_maxDensity` | lower | `nodesUnder` | **fibre** array | the run's `¬Test` |
| `level_density_band` | two-sided | `assignFibre` | A1's joint bin | `hband` |

That is Condition R  discharged field by field: **every lower-bound
witness is produced on the fibre array**, and no field moves off `nodesUnder`.

**The two named rows.**

1. `hcoarse` is the source's `eqdividingKfirst`, i.e. `lemabstractstopping`'s *tail* conclusion
   `X(b,M) ≤ B^N r(b,M)^{-η_J}`, whose proof is *"submultiplicativity over the pieces after
   it"* — a chained application of `towerDensityArrayFibre_submultiplicative` along the cut set,
   telescoping `∏ (ρ_{c_{i-1}}/ρ_{c_i})^{η_m} = (ρ_0/ρ_a)^{η_m}`.  Exact goal, at the run's
   output `(S, m, a)`:
   `Cu * towerDensityArrayFibre 𝒰 0 a ≤ Cstar * ENNReal.ofReal (ρ_a ^ (-η m))`,
   with `ρ_0 = 1` making the telescoped ratio `ρ_a^{-η m}` on the nose.  Not proved here.
2. `hwindow` is `le_window_maxDensity`, whose owner  item 2 already measured: the
   **count** of `nodesUnder b a j` through `le_window_maxDensity_of_card`, not the density band
   and not the fibre array.  Not proved here.

## The dichotomy is real: a Long piece is not free — measured

The run returns `S.card = m + 2` cut points with `m < N`, i.e. at most `N` pieces covering
`[0, L]`, so the pigeonhole gives a piece with `b - a ≥ L/N` and no more.  `Long` must give
`b - a ≥ ε_d·L` for the width field.  With the tree's own parameters
`ε_d = spineDiv ϖ ε₁ = 1/√(spineCount ϖ ε₁)` (`SpineParams.lean:340`) and `N = spineCount`,
`ε_d·L = L/√N`, and `L/N < L/√N` for `N > 1`: **the pigeonhole does not force a Long piece.**

The margin itself is consistent — `w := ⌈ε_d·⌈ε_d·L⌉₊⌉₊` satisfies both `L ≤ w·N` (since
`w ≥ ε_d²L = L/N`) and `w ≤ ⌈ε_d(b-a)⌉₊` at any Long piece — and it is consistent only because
`ε_d = N^{-1/2}` makes `ε_d² = 1/N` an equality.  So there is no slack to buy a Long piece with,
which is precisely why the source states `lemabstractstopping` as an **either/or**:
`eqstoppingallscales` (all-scale density bound, no window) or
`eqstoppingab`-`eqstoppingwitness` (window).

So `RefinedFloorSupplyAt` — which offers only the `(F)` disjunct — cannot be reached from the
stopping run alone: the branch *"every adjacent piece is short"* has no `(F)` window to hand,
and `Kakeya.ML2Core.FloorDataAtTrichotomy`'s other disjunct is `DefectBranchAt`.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `towerDensityArrayFibre_anti_left` | the tower's `s`, `T`; no shading | `(a,a',c)` |
| `FibreTest` | as above | the piece `(a,b)` and the inserted `c` |
| `towerGoodFibre_split_of_fibreTest` | as above | `(a,b)`, cut at `c` |
| `exists_fibreStoppingRun` | as above | the cut set; each adjacent `(a,b)` |
| `maxDensity_nodesUnder_le_mul_towerDensityArrayFibre` | as above | `(a,b)` |
| `towerDensityArray_le_mul_towerDensityArrayFibre` | as above | `(a,b)` |
| `isKatzTaoDividingWindowLevels_of_fibreRun` | as above | the window `(a,b,m)` |

## A1-a

No `GridUniformCore` is named, and no `(F)`-branch interface statement is defined or altered:
`IsKatzTaoDividingWindowLevels` is *inhabited by shape* through the existing
`isKatzTaoDividingWindowLevels_of_width_and_band`.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory Tube

namespace Kakeya.ML2Core

section FibreStoppingRun

universe u

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **(H4) of `lemabstractstopping` on the fibre array, at `E = 1` and for free** — the source's
hypothesis `X̃(a,m) ≤ E X̃(a,b)` (l.5262) after the Part (B) transposition `k ↦ M-k`, which turns
it into monotonicity of `Z` in its **anchor** index.

`Z_fib(a',c) ≤ Z_fib(a,c)` for `a ≤ a'`.  Content: Definition 2.1(ii)'s compatible-partition
clause read on classes.  Pick any member `i` of the level-`a'` class of `S'`
(`Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent`); every other member `i'` of that class
has the same level-`a` node as `i` (`Tube.ChainCoverSystem.assign_eq_of_le`), so the thread cell
`𝕋_c⟨S'⟩` is contained in `𝕋_c⟨assign a i⟩`, and `Kakeya.maxDensity_mono` plus `Finset.le_sup`
finish.  No geometry, no constant, and in particular **no `Cu`** — the same reason
`towerDensityArrayFibre_submultiplicative` pays none.

Note `c` is completely free: no relation between `a'` and `c` is used.

**Family/shading:** the tower's `s`, `T`; no shading.  **Level pair:** `(a,a',c)`. -/
theorem towerDensityArrayFibre_anti_left
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty) {a a' c : ℕ}
    (haa' : a ≤ a') (ha' : a' ≤ Tube.ssfGridLen δ) :
    towerDensityArrayFibre 𝒰 a' c ≤ towerDensityArrayFibre 𝒰 a c := by
  classical
  refine Finset.sup_le fun S' hS' => ?_
  obtain ⟨i, hi⟩ := Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰 ha' hs hS'
  simp only [coverClass, Finset.mem_filter] at hi
  obtain ⟨his, hiS⟩ := hi
  have hsub : 𝒰.assignFibre c a' S' ⊆ 𝒰.assignFibre c a (𝒰.cover.assign a i) := by
    intro x hx
    simp only [Tube.UniformTubeSet.assignFibre, Finset.mem_image] at hx ⊢
    obtain ⟨i', hi', rfl⟩ := hx
    simp only [coverClass, Finset.mem_filter] at hi'
    refine ⟨i', ?_, rfl⟩
    simp only [coverClass, Finset.mem_filter]
    exact ⟨hi'.1, 𝒰.cover.toChain.assign_eq_of_le haa' ha' hi'.1 his (hi'.2.trans hiS.symm)⟩
  refine le_trans (Kakeya.maxDensity_mono _ hsub) ?_
  exact Finset.le_sup (f := fun j => Kakeya.maxDensity (𝒰.assignFibre c a j)
    (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody))
    (𝒰.cover.assign_mem a (haa'.trans ha') i his)

open scoped Classical in
/-- **The source's stopping test, in Part (B)'s reading**: the piece `(a,b)` admits an inset level
`c` at which the array is still *good*.

Its failure is `eqstoppingwitness` (l.5297 / `eqdividingKwitness` l.2700-2703):
`Z_fib(a,c) > r(a,c)^{-η_{J+1}}` at every inset `c` — and the source stresses that this conclusion
*"is existential at each intermediate level"*, i.e. it is a statement about the array, not about
every cell.  Both the test and its failure sit at pairs sharing the **left** endpoint `a`, which is
the Part (B) transposition of the source's own `(m,b)` pairs.

**Family/shading:** the tower's `s`, `T`; no shading.  **Level pair:** the piece `(a,b)` and the
inserted `c`. -/
def FibreTest (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    (bound : ℕ → ℕ → ℕ → ENNReal) (w : ℕ) (j a b : ℕ) (_ : Unit) : Prop :=
  ∃ c : ℕ, a + w ≤ c ∧ c + w ≤ b ∧ TowerGoodFibre 𝒰 bound j a c ()

open scoped Classical in
/-- **`hsplit`: the source's *"insert `m`"* step (l.5289-5297), on the fibre array, in Part (B)'s
reading — and with no undischarged data.**

The test hands over the inset level `c` together with `Z_fib(a,c) ≤ bound (j+1) a c`, which is the
source's *"second new estimate is the assumed failure of `eqstoppingwitness`"*.  The **first** new
estimate is the source's chain

> `X(a,m) ≤ E r(a,b)^{-η_J} ≤ r(a,b)^{-ε η_{J+1}} ≤ r(a,m)^{-η_{J+1}}`,
> *"The middle inequality is precisely the calibration `δ^{-ε²η₁/2} ≥ E`."*

read at the transposed pair: `Z_fib(c,b) ≤ E · Z_fib(a,b)` is `towerDensityArrayFibre_anti_left`
(free, `E = 1` suffices, and any `E ≥ 1` is absorbed), the old estimate gives
`≤ E · bound j a b`, and `hcal` is the calibration.  **Copied, not fitted**: the proof never
inspects `E`, `ε`, `η₁` or the scale convention, so no printed constant can drift here.

Contrast `Kakeya.ML2Core.towerGoodFibre_split_of_calibration` (existing, untouched): it is the
mirror — Part (A)'s reading — and its `hdata` needs `Z_fib(a,m) ≤ E·Z_fib(a,b)`, the **fine**-index
comparison, which the source supplies only for `C_F` and only from *descendant-count regularity*
(l.2726-2728).  That asymmetry is the whole reason this sibling is cut.

**Family/shading:** the tower's `s`, `T`; no shading.  **Level pair:** `(a,b)`, cut at `c`. -/
theorem towerGoodFibre_split_of_fibreTest
    {𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu} (hs : s.Nonempty)
    {rinv : ℕ → ℕ → ℝ} {η : ℕ → ℝ} {Efac : ℝ} (hE : 1 ≤ Efac) {w : ℕ}
    (hcal : ∀ j a c b : ℕ, ENNReal.ofReal Efac * sourceBound rinv η j a b
      ≤ sourceBound rinv η (j + 1) c b)
    {j a b : ℕ} (hbL : b ≤ Tube.ssfGridLen δ)
    (hold : TowerGoodFibre 𝒰 (sourceBound rinv η) j a b ())
    (htest : FibreTest 𝒰 (sourceBound rinv η) w (j + 1) a b ()) :
    ∃ c : ℕ, a + w ≤ c ∧ c + w ≤ b ∧
      TowerGoodFibre 𝒰 (sourceBound rinv η) (j + 1) a c () ∧
      TowerGoodFibre 𝒰 (sourceBound rinv η) (j + 1) c b () := by
  obtain ⟨c, h1, h2, hac⟩ := htest
  refine ⟨c, h1, h2, hac, ?_⟩
  have hcL : c ≤ Tube.ssfGridLen δ := le_trans (Nat.le_add_right c w) (h2.trans hbL)
  have hE1 : (1 : ENNReal) ≤ ENNReal.ofReal Efac := ENNReal.one_le_ofReal.mpr hE
  calc towerDensityArrayFibre 𝒰 c b
      ≤ towerDensityArrayFibre 𝒰 a b :=
        towerDensityArrayFibre_anti_left 𝒰 hs (le_trans (Nat.le_add_right a w) h1) hcL
    _ ≤ ENNReal.ofReal Efac * towerDensityArrayFibre 𝒰 a b :=
        le_mul_of_one_le_left (by simp) hE1
    _ ≤ ENNReal.ofReal Efac * sourceBound rinv η j a b := mul_le_mul' le_rfl hold
    _ ≤ sourceBound rinv η (j + 1) c b := hcal j a c b

open scoped Classical in
/-- **`lemabstractstopping` run on the fibre array over a fixed tower, with every input
discharged** —  item 1.

`exists_fixedTowerCutsFibre`'s five inputs: `bound := sourceBound rinv η` (the piece bound
`r(a,b)^{-η_J}`, l.5288), `Test := FibreTest`, `Long` left as a parameter (the caller's
`r(a,b) ≤ δ^ε`), `N` and `w` the source's own margin data (`0 < w`, `w ≤ M`, `M ≤ w·N` is
`ε^{-2} ≤ N`), `hGood` the assumed top-cell estimate (H3, l.2683-2684), `hmono` from
`sourceBound_mono`, `hsplit` from `towerGoodFibre_split_of_fibreTest`.

**(H1) and (H2) are not inputs.**  The engine's piece count comes from the margin
(`M ≤ w·N`), not from submultiplicativity or the crude exponent; those are needed only for the
source's *tail* conclusion `eqdividingKfirst`.

Output, at every adjacent pair of the maximal cut set: `eqstoppingab` (`Z_fib(a,b) ≤
r(a,b)^{-η_m}`) and the alternative *short piece* / `eqstoppingwitness` at every inset level.

**Family/shading:** the fixed tower `𝒰` on `(s,T)`; no shading.  **Level pair:** the cut set, and
each adjacent `(a,b)` as a candidate window. -/
theorem exists_fibreStoppingRun
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty)
    {rinv : ℕ → ℕ → ℝ} {η : ℕ → ℝ} {Efac : ℝ} (hE : 1 ≤ Efac)
    (hr : ∀ a b : ℕ, 1 ≤ rinv a b) (hη : ∀ j j' : ℕ, j ≤ j' → η j ≤ η j')
    (hcal : ∀ j a c b : ℕ, ENNReal.ofReal Efac * sourceBound rinv η j a b
      ≤ sourceBound rinv η (j + 1) c b)
    (N w : ℕ) (hw : 0 < w) (hwM : w ≤ Tube.ssfGridLen δ)
    (hwN : Tube.ssfGridLen δ ≤ w * N) (Long : ℕ → ℕ → Prop)
    (hGood : towerDensityArrayFibre 𝒰 0 (Tube.ssfGridLen δ)
      ≤ sourceBound rinv η 0 0 (Tube.ssfGridLen δ)) :
    ∃ (S : Finset ℕ) (m : ℕ), m < N ∧ 0 ∈ S ∧ Tube.ssfGridLen δ ∈ S ∧
      S ⊆ Finset.range (Tube.ssfGridLen δ + 1) ∧ S.card = m + 2 ∧
      ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ y ∈ S, ¬(a < y ∧ y < b)) →
        towerDensityArrayFibre 𝒰 a b ≤ sourceBound rinv η m a b ∧
        (¬ Long a b ∨ ∀ c : ℕ, a + w ≤ c → c + w ≤ b →
          sourceBound rinv η (m + 1) a c < towerDensityArrayFibre 𝒰 a c) := by
  classical
  obtain ⟨S, m, hmN, h0, hM, hsub, hcard, hpieces⟩ :=
    exists_fixedTowerCutsFibre 𝒰 (Tube.ssfGridLen δ) N w hw hwM hwN (sourceBound rinv η)
      (FibreTest 𝒰 (sourceBound rinv η) w) Long hGood
      (fun j j' hjj' _ a b _ hg =>
        towerGoodFibre_mono_of_bound_mono
          (fun j₁ j₂ a₁ b₁ h => sourceBound_mono hr hη j₁ j₂ a₁ b₁ h) hjj' hg)
      (fun j a b _ _ hbM _ hg htest =>
        towerGoodFibre_split_of_fibreTest hs hE hcal hbM hg htest)
  refine ⟨S, m, hmN, h0, hM, hsub, hcard, fun a ha b hb hab hadj => ?_⟩
  obtain ⟨hgood, halt⟩ := hpieces a ha b hb hab hadj
  refine ⟨hgood, halt.imp id (fun hnt c h1 h2 => ?_)⟩
  by_contra hcon
  exact hnt ⟨c, h1, h2, not_lt.mp hcon⟩

open scoped Classical in
/-- **The containment reading is at most `Cu` times the fibre reading, per cell** — the reverse
comparison to `towerDensityArrayFibre_le_towerDensityArray`, and the row that lets the fibre run
discharge `middle_maxDensity_le`, which is stated on `nodesUnder`.

Proof, and where the `Cu` comes from: a level-`b` node `x` contained in `T_a(j)` is
`assign b i` for some leaf `i` (`coverClass_nonempty_of_mem_parent`), so `x` lies in the thread
cell of `j' := assign a i`; and `T i ≤ T_b(x) ≤ T_a(j)` together with `T i ≤ T_a(j')` puts `j'` in
exactly the family Definition 2.1(ii) **bounded overlap** caps by `Cu` at `V := T_a(j)`.  Summing
over that family (`Kakeya.maxDensity_le_sum_of_subset_biUnion`) gives the claim.

`Cu` is `δ`-free, so the factor enters no exponent account.  Note the level-`a` node `j` need not
be active: the argument never uses `j ∈ indexSet a`.

**Family/shading:** the tower's `s`, `T`; no shading.  **Level pair:** `(a,b)`. -/
theorem maxDensity_nodesUnder_le_mul_towerDensityArrayFibre
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty)
    {a b : ℕ} (ha : a ≤ Tube.ssfGridLen δ) (hb : b ≤ Tube.ssfGridLen δ)
    {j : ι} (_hj : j ∈ 𝒰.cover.indexSet a) :
    Kakeya.maxDensity (𝒰.nodesUnder b a j) (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
      ≤ (Cu : ENNReal) * towerDensityArrayFibre 𝒰 a b := by
  classical
  set W : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun j' => (𝒰.cover.tube b j').toConvexSpaceBody with hW
  set J : Finset ι := (𝒰.cover.indexSet a).filter (fun j' => ∃ i ∈ s,
      (T i).toConvexSpaceBody ≤ (𝒰.cover.tube a j').toConvexSpaceBody ∧
      (T i).toConvexSpaceBody ≤ (𝒰.cover.tube a j).toConvexSpaceBody) with hJ
  have hJcard : (J.card : NNReal) ≤ Cu := 𝒰.boundedOverlap a ha (𝒰.cover.tube a j)
  have hsub : 𝒰.nodesUnder b a j ⊆ J.biUnion (fun j' => 𝒰.assignFibre b a j') := by
    intro x hx
    rw [Tube.UniformTubeSet.nodesUnder_eq_nodesIn, Tube.UniformTubeSet.mem_nodesIn_iff] at hx
    obtain ⟨hxidx, hxle⟩ := hx
    obtain ⟨i, hi⟩ := Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰 hb hs hxidx
    simp only [coverClass, Finset.mem_filter] at hi
    obtain ⟨his, hix⟩ := hi
    have hTib : (T i).toConvexSpaceBody ≤ (𝒰.cover.tube b (𝒰.cover.assign b i)).toConvexSpaceBody :=
      𝒰.cover.le_tube_assign b hb i his
    have hTia : (T i).toConvexSpaceBody ≤ (𝒰.cover.tube a (𝒰.cover.assign a i)).toConvexSpaceBody :=
      𝒰.cover.le_tube_assign a ha i his
    have hTij : (T i).toConvexSpaceBody ≤ (𝒰.cover.tube a j).toConvexSpaceBody := by
      refine le_trans hTib ?_
      rw [hix]; exact hxle
    refine Finset.mem_biUnion.mpr ⟨𝒰.cover.assign a i, ?_, ?_⟩
    · rw [hJ]
      exact Finset.mem_filter.mpr ⟨𝒰.cover.assign_mem a ha i his, ⟨i, his, hTia, hTij⟩⟩
    · simp only [Tube.UniformTubeSet.assignFibre, Finset.mem_image]
      exact ⟨i, by simp [coverClass, his], hix⟩
  calc Kakeya.maxDensity (𝒰.nodesUnder b a j) W
      ≤ ∑ j' ∈ J, Kakeya.maxDensity (𝒰.assignFibre b a j') W :=
        Kakeya.maxDensity_le_sum_of_subset_biUnion W hsub
    _ ≤ ∑ _j' ∈ J, towerDensityArrayFibre 𝒰 a b :=
        Finset.sum_le_sum (fun j' hj' =>
          Finset.le_sup (f := fun p => Kakeya.maxDensity (𝒰.assignFibre b a p) W)
            (Finset.mem_filter.mp hj').1)
    _ = (J.card : ENNReal) * towerDensityArrayFibre 𝒰 a b := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Cu : ENNReal) * towerDensityArrayFibre 𝒰 a b := by
        gcongr
        exact_mod_cast hJcard

open scoped Classical in
/-- **The same comparison at the array level**: `Z_cont(a,b) ≤ Cu · Z_fib(a,b)`.  Read together
with `towerDensityArrayFibre_le_towerDensityArray` the two arrays are equivalent up to `Cu`, so
`SpineTowerArrayFibre.lean`'s *"that is the only relation between them"* is exactly right about
**free** relations and this is the priced one.  It does **not** make the fibre array redundant:
Condition R's prohibitive half is about *lower* bounds, where a factor `Cu` on the wrong side is
not a weakening one may spend.

**Family/shading:** the tower's `s`, `T`; no shading.  **Level pair:** `(a,b)`. -/
theorem towerDensityArray_le_mul_towerDensityArrayFibre
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty)
    {a b : ℕ} (ha : a ≤ Tube.ssfGridLen δ) (hb : b ≤ Tube.ssfGridLen δ) :
    towerDensityArray 𝒰 a b ≤ (Cu : ENNReal) * towerDensityArrayFibre 𝒰 a b :=
  Finset.sup_le fun _j hj =>
    maxDensity_nodesUnder_le_mul_towerDensityArrayFibre 𝒰 hs ha hb hj

open scoped Classical in
/-- **`IsKatzTaoDividingWindowLevels` produced from one Long adjacent piece of the fibre run.**

Generic in the tower, so it applies verbatim at `Kakeya.ML2Core.refinedHierarchy`.  Of the twin's
six fields, three are produced here from the run — `middle_maxDensity_le` from its `TowerGood`
through `maxDensity_nodesUnder_le_mul_towerDensityArrayFibre` (cost `Cu`, hence `hCuCstar`),
`le_level_maxDensity` from its `¬Test` through the existing
`le_level_maxDensity_of_fibre_witness`, and the four scale fields from the width
(`scale_sep_of_width`) — one is A1's (`level_density_band`, from `hband`/`hidx` through
`levelDensityBand_indexSet`), and two are **named**: `hcoarse` (the source's `eqdividingKfirst`,
whose proof is the chained submultiplicativity over the cut set) and `hwindow`
`hwmargin` is the only arithmetic link between the run's global margin `w` and the window's own
inset `⌈ε_d(b-a)⌉₊`: the run's witness must cover the *wider* range, so `w` must be the smaller.

**A1-b:** every lower-bound field's witness is produced on the fibre array; no field moves off
`nodesUnder`.

**Family/shading:** the tower's `s`, `T`; no shading.  **Level pair:** the window `(a,b,m)`, and
every inset `c`. -/
theorem isKatzTaoDividingWindowLevels_of_fibreRun (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {Cstar : ENNReal} (hCstar : 2 ≤ Cstar) (hCuCstar : (Cu : ENNReal) ≤ Cstar)
    {η : ℕ → ℝ} {εd : ℝ} {N a b m w : ℕ} {rinv : ℕ → ℕ → ℝ}
    (hrinv : ∀ p c : ℕ, rinv p c = (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ))
    (hmN : m < N) (hab : a < b) (hbL : b ≤ Tube.ssfGridLen δ)
    (hwidth : εd * (Tube.ssfGridLen δ : ℝ) + (a : ℝ) ≤ (b : ℝ))
    (hwmargin : w ≤ ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊)
    (hgood : towerDensityArrayFibre 𝒰 a b ≤ sourceBound rinv η m a b)
    (hwit : ∀ c : ℕ, a + w ≤ c → c + w ≤ b →
      sourceBound rinv η (m + 1) a c < towerDensityArrayFibre 𝒰 a c)
    (hcoarse : (Cu : ENNReal) * towerDensityArrayFibre 𝒰 0 a
      ≤ Cstar * ENNReal.ofReal ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) ^ (-η m)))
    (hwindow : ∀ ρ : NNReal,
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ εd ≤ (ρ : ℝ) →
      (ρ : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ εd →
      ∀ j ∈ 𝒰.cover.indexSet a,
        ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ η (m + 1))
          ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder b a j)
              (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody))
    (hidx : ∀ p : ℕ, ∀ j ∈ 𝒰.cover.indexSet p, ∃ k ∈ s, 𝒰.cover.assign p k = j)
    {Φ : ℕ → ℕ → ENNReal}
    (hband : ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ, ∀ k ∈ s,
      Φ p c ≤ levelDensityStat 𝒰 p c s k ∧ levelDensityStat 𝒰 p c s k ≤ 2 * Φ p c) :
    ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar η εd N a b m := by
  classical
  have haL : a ≤ Tube.ssfGridLen δ := le_trans hab.le hbL
  -- the middle field: the containment array, from the fibre run at cost `Cu`
  have hmiddle : ∀ j ∈ 𝒰.cover.indexSet a,
      Kakeya.maxDensity (𝒰.nodesUnder b a j) (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
        ≤ Cstar * ENNReal.ofReal
            (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
              / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ η m) := by
    intro j hj
    refine le_trans (maxDensity_nodesUnder_le_mul_towerDensityArrayFibre 𝒰 hs haL hbL hj) ?_
    refine le_trans (mul_le_mul' le_rfl hgood) ?_
    rw [sourceBound, hrinv a b]
    exact mul_le_mul' hCuCstar le_rfl
  -- the coarse field
  have hcoarse' : Kakeya.maxDensity (𝒰.cover.indexSet a)
      (fun j => (𝒰.cover.tube a j).toConvexSpaceBody)
      ≤ Cstar * ENNReal.ofReal ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) ^ (-η m)) :=
    le_trans (maxDensity_indexSet_le_mul_towerDensityArrayFibre 𝒰 hs hball haL) hcoarse
  -- the band at the window's coarse level, in the fibre shape
  have hbandA : ∀ c ≤ Tube.ssfGridLen δ, ∀ j ∈ 𝒰.cover.indexSet a,
      Φ a c ≤ Kakeya.maxDensity (𝒰.assignFibre c a j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity (𝒰.assignFibre c a j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ≤ Cstar * Φ a c := by
    intro c hc j hj
    obtain ⟨k, hk, rfl⟩ := hidx a j hj
    obtain ⟨hlo, hhi⟩ := hband a haL c hc k hk
    rw [levelDensityStat_eq_maxDensity_assignFibre 𝒰 a c k] at hlo hhi
    exact ⟨hlo, hhi.trans (mul_le_mul' hCstar le_rfl)⟩
  -- the level field, from the run's witness
  have hlevel := le_level_maxDensity_of_fibre_witness (εd := εd) (η := η) (m := m) 𝒰 hbL hbandA
    (fun c h1 h2 => by
      have := hwit c (by omega) (by omega)
      rwa [sourceBound, hrinv a c] at this)
  exact isKatzTaoDividingWindowLevels_of_width_and_band hδ0 hδ1 𝒰 hCstar hmN hab hbL hwidth
    hcoarse' hmiddle hwindow hlevel hidx hband

/-! ### Firing controls -/

open scoped Classical in
/-- **Firing control: the margin `w` is load-bearing in the run's second alternative.**  Read at
`w = 0`, the alternative asserts the strict lower bound at the degenerate pair `(a,a)`, where
`towerDensityArrayFibre 𝒰 a a` is the density of the level-`a` thread cells *at their own level*.
That is why `exists_fibreStoppingRun` carries `0 < w`, and why the window field's inset
`⌈ε_d(b-a)⌉₊` must dominate `w` (`hwmargin`) rather than the other way round. -/
theorem fibreStoppingRun_margin_load_bearing
    {𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu} {rinv : ℕ → ℕ → ℝ} {η : ℕ → ℝ}
    {m a b : ℕ} (hab : a ≤ b)
    (hwit : ∀ c : ℕ, a + 0 ≤ c → c + 0 ≤ b →
      sourceBound rinv η (m + 1) a c < towerDensityArrayFibre 𝒰 a c) :
    sourceBound rinv η (m + 1) a a < towerDensityArrayFibre 𝒰 a a :=
  hwit a (by omega) (by omega)

open scoped Classical in
/-- **Firing control: the `Cu` of the containment comparison is load-bearing.**  At `Cu = 0` the
`boundedOverlap` clause admits no level-`a` node at all, and the comparison collapses the
containment density to `0` — so the factor is not decoration, it is the whole content of the
inclusion into the bounded-overlap family. -/
theorem maxDensity_nodesUnder_le_mul_towerDensityArrayFibre_vacuous_at_zero
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) 0) (hs : s.Nonempty)
    {a b : ℕ} (ha : a ≤ Tube.ssfGridLen δ) (hb : b ≤ Tube.ssfGridLen δ)
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet a) :
    Kakeya.maxDensity (𝒰.nodesUnder b a j)
      (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody) = 0 := by
  refine le_antisymm ?_ (by simp)
  simpa using maxDensity_nodesUnder_le_mul_towerDensityArrayFibre 𝒰 hs ha hb hj

open scoped Classical in
/-- **Match control: the run's second alternative is the `hwit` slot of the existing
`Kakeya.ML2Core.le_level_maxDensity_of_fibre_witness`, verbatim.**  The only step is the margin
comparison `w ≤ ⌈ε_d(b-a)⌉₊`; nothing is reshaped. -/
example {𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu} {rinv : ℕ → ℕ → ℝ} {η : ℕ → ℝ}
    {εd : ℝ} {a b m w : ℕ} (hwmargin : w ≤ ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊)
    (hrinv : ∀ p c : ℕ, rinv p c = (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ))
    (hwit : ∀ c : ℕ, a + w ≤ c → c + w ≤ b →
      sourceBound rinv η (m + 1) a c < towerDensityArrayFibre 𝒰 a c) :
    ∀ c : ℕ, a + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c → c + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b →
      ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ η (m + 1))
        < towerDensityArrayFibre 𝒰 a c := by
  intro c h1 h2
  have := hwit c (by omega) (by omega)
  rwa [sourceBound, hrinv a c] at this

end FibreStoppingRun

end Kakeya.ML2Core

end
