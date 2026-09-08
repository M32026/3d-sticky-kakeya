/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac
public import Kakeya.ShadedUniform
public import Kakeya.Pigeonhole
public import Kakeya.Factoring.Pigeonhole

/-!
# The mass-banded shade refinement, and the shaded dividing-scales dichotomy

The Section-9 reduction of GWZ Main Lemma 2 consumes GWZ Lemma 7.7(B) in a *shaded* form: given a
uniform family of `δ`-tubes carrying a shading, the dividing-scales dichotomy must return, besides
the scales, (i) a sub-shading `Y' ⊆ Y`, (ii) a shaded-mass loss, and (iii) comparability of the
per-tube shading densities.  `StickyKakeya.dividingScalesKatzTao` (`Kakeya/MultiScaleFac.lean`) is
proved but unshaded and returns none of the three.

`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet` (`Kakeya/ShadedUniform.lean`) supplies
(i) and (ii): it refines a shading against a *given* hierarchy, pinning
`cover.{indexSet, assign, tube}` and `branchingN` to that hierarchy's, so both alternatives of the
dichotomy transfer verbatim, and it returns the `ShadedBody.fullness'` loss.  Item (iii) is the gap,
and it is what this file closes.

## What is here

* `Kakeya.ML2Shaded.HasComparableDensities` — the obligation, in cross-multiplied form
  (`|Y_i| |T_j| ≤ K |Y_j| |T_i|`), together with `.subset` and `.mono`.
* `Kakeya.ML2Shaded.massBandLoss` and `Kakeya.ML2Shaded.exists_massBanded_shadeRefinement` — the
  **mass-banded** analogue of `ShadedTube.exists_balanced_shadeRefinement`, which bands shade-*class
  cardinalities* and therefore cannot produce (iii).  Every finite family of shaded `δ`-tubes has a
  subfamily retaining all but a `massBandLoss` share of the shaded mass and on which the densities
  are comparable at the absolute constant `2`.
* `Kakeya.ML2Shaded.massBandLoss_le_gridLoss` and
  `Kakeya.ML2Shaded.exists_threshold_massBandLoss_le` — the loss bookkeeping, honestly: the loss is
  `Θ(η log (1/δ))`, hence `≤ δ^{-α}` only *below a threshold determined by `α` and `η`*, which is
  derived explicitly and exposed in the `∃ δ₀ > 0, ∀ δ ≤ δ₀` idiom the development uses.
* `Kakeya.ML2Shaded.card_le_of_sum_shade_le` — a share of the shaded mass is a share of the index
  set, at the price of the fullness and of the dimensional tube-volume ratio.  This is what makes
  the banded subfamily usable by a consumer that needs a cardinality bound; the two are packaged
  together as `Kakeya.ML2Shaded.exists_massBanded_shadeRefinement_card`.
* `Kakeya.ML2Shaded.sum_shade_le_of_card_le` — the converse of `card_le_of_sum_shade_le`: a
  cardinality share becomes a mass share against a pointwise density lower bound, which is what the
  reduction actually spends its input comparability on (in both of the two places it spends it).
* `Kakeya.ML2Shaded.HasDenseShading` and `Kakeya.ML2Shaded.exists_denseShading_refinement` — the
  **one-sided** half of the banding: a pointwise lower bound `lam · |T_i| ≤ |Y_i|`, obtained by the
  below-average discard alone, so at the absolute cost `2` and with *no* logarithm.  It is weaker
  than `HasComparableDensities` at an absolute constant (its own comparability constant is `2/λ`,
  a `δ`-power) and stronger where the consumer needs it: being pointwise it restricts to every
  subfamily, and therefore hands the fullness to every subfamily
  (`Kakeya.ML2Shaded.HasDenseShading.le_fullness'`), which no aggregate hypothesis on the parent
  family can do.
* `Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao` — the shaded dichotomy, assembled from the
  three ingredients above.
* `Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao_dense` — the same dichotomy with a dense
  input shading, which is what puts a density invariant **and** a fullness lower bound for the
  refined shading on the returned index set `s'` itself rather than on a further subfamily.  This
  is the form the Section-9 reduction consumes; see its docstring for why the two comparability
  clauses it returns are genuinely different statements.
* Guardrails: `nonempty_of_massBand`, `shade_eq_zero_of_hasComparableDensities`,
  `not_hasComparableDensities_of_aggregate_retention`, `massBand_must_discard`,
  `massBand_forced_on_concrete_family`, `coverClass_nonempty_of_uniformTubeSet`.

## The loss, and where the threshold comes from

Write `λ = λ(𝕋, Y)` for the fullness and `L = log (1/δ)`.  The banding is two pigeonholes:

1. *Discard below average.*  Keeping `{i : |Y_i| ≥ (λ/2) |T_i|}` costs a factor `2` of the shaded
   mass (`ShadedBody.one_sub_mul_sum_volume_shade_le_sum_discardLowShading` at `c = 1/2`) and
   confines the retained densities `|Y_i| / |T_i|` to `[λ/2, 1]`.
2. *Dyadic pigeonhole on that range.*  A range of ratio `2/λ` has `1 + log₂ (2/λ)` dyadic bands, and
   the heaviest one retains that share of the mass and has densities comparable within a factor `2`
   (`ENNReal.dyadic_pigeonhole₁''`).

So `massBandLoss λ = 2 (1 + log₂ (2/λ))`.  Under the standing hypothesis `δ^η ≤ λ`,

  `massBandLoss λ ≤ 2 (2 + η L / log 2) = 4 + (2η / log 2) L ≤ (4 + 2η/log 2) (1 + L)`,

and `1 + L = 1 - log δ ≤ (1 - log δ)^{(⌈log log 1/δ⌉+1)^2} = StickyKakeya.gridLoss 1 1 δ`.  That is
`massBandLoss_le_gridLoss`.  Absorbing the *constant* `4 + 2η/log 2` into `δ^{-α/2}`
(`exists_threshold_const_le_rpow_neg'`, threshold `(max (4 + 2η/log 2) 1)^{-2/α}`) and the grid loss
into `δ^{-α/2}` (`StickyKakeya.exists_threshold_gridLoss_le`) gives

  `massBandLoss λ ≤ δ^{-α}` for `δ ≤ δ₀(η, α)`,

with `δ₀` bound **before** `δ`, before `λ` and before the family.  The retained mass is `⪆ 1/L`, not
`⪆ 1`; there is no threshold at which it becomes `⪆ 1`, only one at which `1/L ≥ δ^α`.

## Why comparability lands on a *further* subfamily, and what that costs

`HasComparableDensities` is pointwise and two-sided, so it fails outright as soon as one retained
index has zero shaded mass beside one with positive mass
(`shade_eq_zero_of_hasComparableDensities`).  A shade refinement that keeps every index therefore
cannot deliver it, however good its aggregate retention:
`not_hasComparableDensities_of_aggregate_retention` exhibits a sub-shading with an aggregate
retention of `1/2` — better than any loss charged anywhere in this development — whose densities
are comparable at no constant at all.  This is the aggregate-versus-pointwise gap, and no
sharpening of the `ShadedBody.fullness'` loss of
`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet` can bridge it.

Discarding indices is therefore forced.  But discarding indices destroys
`Tube.UniformTubeSet.le_card_class` at every node whose class is emptied, and the only repair —
shrinking `Tube.GridCoverSystem.indexSet` to the nodes still hit — shrinks
`Tube.UniformTubeSet.nodesUnder`, under which the **third** window bullet of alternative (ii), being
a *lower* bound on `Kakeya.maxDensity`, does not survive.  (Alternative (i) and the first two
bullets, being upper bounds, do survive, by `Kakeya.maxDensity_mono`.)

So `exists_shaded_dividingScalesKatzTao` returns the `ShadedTube.ShadedUniformTubeSet` on `s'` and
the comparability on a further `s'' ⊆ s'`, and this is the strongest form obtainable by composing
the three proved ingredients.  Putting both on the same index set requires the shaded uniformization
to be *interleaved* with the stopping time — a different proof of 7.7(B), not a different
composition.  `card_le_of_sum_shade_le` makes the returned `s''` quantitatively usable all the same:
it converts the mass share into the cardinality share `#s'' ≥ (λ c_n)/(massBandLoss · C_n) · #s'`.

## What lands on `s'` and what does not, once more

The consumer of 7.7(B) wants comparability of the densities on the index set that carries the
hierarchy, because what it does with comparability is recover a fullness lower bound for the
refined shading on that set.  The two are not the same ask, and only the second is obtainable here:

* the **fullness** lower bound on `s'` *is* obtainable, and
  `Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao_dense` delivers it, provided the input
  fullness was handed in pointwise (`HasDenseShading`) rather than as an aggregate;
* **absolute-constant comparability of `Y'` on `s'`** is not, and cannot be, for the reason
  isolated by `Kakeya.ML2Shaded.not_hasComparableDensities_of_aggregate_retention`.

## Absorbing the two `δ`-dependent losses

The cardinality loss is `StickyKakeya.totalLoss`, absorbed by
`StickyKakeya.exists_threshold_totalLoss_le`.  The mass loss is `(log₂ #s + 1)^{2M+2}` with
`M = Tube.ssfGridLen δ`, absorbed by `Tube.exists_threshold_polylog_pow_ssfGridLen_le` at `A = 1`,
`m = 2` once the consumer supplies a cardinality bound `#s ≤ δ^{-K₀}`.  The banding loss is
`massBandLoss`, absorbed by `exists_threshold_massBandLoss_le`.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube ShadedTube

universe u

namespace Kakeya.ML2Shaded

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-! ### Pairwise comparable shading densities -/

/-- **Pairwise comparable shading densities**, in cross-multiplied form. -/
def HasComparableDensities (K : NNReal) (u : Finset ι) (V : ι → ShadedBody E) : Prop :=
  ∀ i ∈ u, ∀ j ∈ u,
    volume (V i).shade * volume (V j).carrier
      ≤ (K : ENNReal) * (volume (V j).shade * volume (V i).carrier)

omit [Nontrivial E] in
theorem HasComparableDensities.subset {K : NNReal} {u u' : Finset ι} {V : ι → ShadedBody E}
    (h : HasComparableDensities K u V) (hsub : u' ⊆ u) : HasComparableDensities K u' V :=
  fun i hi j hj => h i (hsub hi) j (hsub hj)

omit [Nontrivial E] in
theorem HasComparableDensities.mono {K K' : NNReal} {u : Finset ι} {V : ι → ShadedBody E}
    (h : HasComparableDensities K u V) (hK : K ≤ K') : HasComparableDensities K' u V :=
  fun i hi j hj => (h i hi j hj).trans
    (mul_le_mul_left (ENNReal.coe_le_coe.mpr hK) _)

/-! ### Positivity and finiteness of the carrier volume of a `δ`-tube -/

/-- A `δ`-tube with `0 < δ` has positive carrier volume. -/
theorem volume_carrier_ne_zero {δ : NNReal} (hδ : 0 < δ) (T : Tube δ E) :
    volume T.carrier ≠ 0 := by
  have hle := Tube.le_volume (E := E) T
  have h1 : (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) ≠ 0 := by
    have := Tube.le_volume.c_pos (Module.finrank ℝ E)
    simpa using this.ne'
  have h2 : ((δ : ENNReal)) ^ (Module.finrank ℝ E - 1) ≠ 0 := by
    refine pow_ne_zero _ ?_
    simpa using hδ.ne'
  have hpos : (0 : ENNReal)
      < (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
        * (δ : ENNReal) ^ (Module.finrank ℝ E - 1) := ENNReal.mul_pos h1 h2
  exact (lt_of_lt_of_le hpos hle).ne'

omit [Nontrivial E] in
/-- The carrier of a tube is compact, so its volume is finite. -/
theorem volume_carrier_ne_top {δ : NNReal} (T : Tube δ E) : volume T.carrier ≠ ⊤ :=
  T.isCompact'.measure_ne_top


/-! ### The loss of the mass-banding pigeonhole -/

/-- **The loss of the mass-banded shade refinement.**

Two factors.  The `2` is the below-average discard: throwing away the indices whose shaded mass
falls below half the average density `λ` costs half the shaded mass and no more.  The
`1 + log₂ (2/λ)` is the dyadic pigeonhole over the bands the *retained* densities can occupy: after
the discard they lie in `[λ/2, 1]`, a range of ratio `2/λ`, so `⌈log₂ (2/λ)⌉ + 1` bands suffice.

The loss is governed by the fullness `λ` alone, not by the cardinality of the family.  Under the
standing hypothesis `δ^η ≤ λ` of this development it is `O(η log (1/δ))`, hence subpolynomial
(`Kakeya.ML2Shaded.exists_threshold_massBandLoss_le`). -/
noncomputable def massBandLoss (lam : NNReal) : ENNReal :=
  2 * ENNReal.ofReal (1 + Real.logb 2 (2 / (lam : ℝ)))

theorem one_le_massBandLoss {lam : NNReal} (hlam : lam ≤ 1) : 1 ≤ massBandLoss lam := by
  have hbase : (1 : ENNReal) ≤ ENNReal.ofReal (1 + Real.logb 2 (2 / (lam : ℝ))) := by
    rcases eq_or_lt_of_le (zero_le (a := lam)) with h0 | hpos
    · have h2 : (2 : ℝ) / (lam : ℝ) = 0 := by
        rw [← h0]; simp
      rw [h2]
      simp
    · have hlamR : (0 : ℝ) < (lam : ℝ) := by exact_mod_cast hpos
      have hlam1R : (lam : ℝ) ≤ 1 := by exact_mod_cast hlam
      have h2le : (1 : ℝ) ≤ 2 / (lam : ℝ) := by
        rw [le_div_iff₀ hlamR]; linarith
      rw [ENNReal.one_le_ofReal]
      have := Real.logb_nonneg (b := 2) (by norm_num) h2le
      linarith
  calc (1 : ENNReal) = 1 * 1 := by ring
    _ ≤ 2 * ENNReal.ofReal (1 + Real.logb 2 (2 / (lam : ℝ))) :=
        mul_le_mul' (by norm_num) hbase

theorem massBandLoss_ne_top (lam : NNReal) : massBandLoss lam ≠ ⊤ := by
  unfold massBandLoss
  exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top

/-! ### The mass-banded shade refinement -/

/-- **Mass-banded shade refinement** (the mass analogue of
`ShadedTube.exists_balanced_shadeRefinement`, which bands shade-*class cardinalities*).

Every finite family of shaded `δ`-tubes has a subfamily which retains all but a
`Kakeya.ML2Shaded.massBandLoss` share of the shaded mass and on which the per-tube shading
densities are pairwise comparable *within a factor `2`* — a genuine pointwise conclusion, obtained
from the aggregate mass bound by discarding, not by averaging.

**Discarding is not optional.**  `Kakeya.ML2Shaded.HasComparableDensities` is a two-sided pointwise
statement, so it fails outright as soon as one retained index carries zero shaded mass beside one
carrying positive mass.  A shade refinement that keeps every index — in particular the refinement
performed by `ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet`, which returns only the
aggregate `ShadedBody.fullness'` loss — therefore cannot deliver it; see
`Kakeya.ML2Shaded.not_hasComparableDensities_of_aggregate_retention`.

The comparability constant is the absolute `2`, and the whole loss sits in the retained mass. -/
theorem exists_massBanded_shadeRefinement {δ : NNReal} (hδ : 0 < δ)
    (s : Finset ι) (V : ι → ShadedTube δ E) :
    ∃ s' ⊆ s,
      (∑ i ∈ s, volume (V i).shade)
          ≤ massBandLoss (ShadedBody.fullness s (fun i => (V i).toShadedBody))
              * ∑ i ∈ s', volume (V i).shade ∧
        HasComparableDensities 2 s' (fun i => (V i).toShadedBody) := by
  classical
  set Vb : ι → ShadedBody E := fun i => (V i).toShadedBody with hVbdef
  have hcar0 : ∀ i, volume (Vb i).carrier ≠ 0 :=
    fun i => volume_carrier_ne_zero hδ (V i).toTube
  have hcarT : ∀ i, volume (Vb i).carrier ≠ ⊤ :=
    fun i => volume_carrier_ne_top (V i).toTube
  set lam : NNReal := ShadedBody.fullness s Vb with hlamdef
  set S : ENNReal := ∑ i ∈ s, volume (Vb i).shade with hSdef
  by_cases hS0 : S = 0
  · refine ⟨s, Finset.Subset.refl s, ?_, ?_⟩
    · change S ≤ massBandLoss lam * S
      rw [hS0, mul_zero]
    · have h0 : ∀ k ∈ s, volume (Vb k).shade = 0 := by
        intro k hk
        exact le_antisymm (hS0 ▸ Finset.single_le_sum (f := fun i => volume (Vb i).shade)
          (fun i _ => zero_le) hk) (zero_le)
      intro i hi j hj
      simp [h0 i hi, h0 j hj]
  · -- the total shaded mass is positive, hence so is the fullness
    have hsne : s.Nonempty := by
      rcases Finset.eq_empty_or_nonempty s with h | h
      · exact absurd (by simp [hSdef, h]) hS0
      · exact h
    have hD_ne_top : (∑ i ∈ s, volume (Vb i).carrier) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr (fun i _ => hcarT i)
    have hlam_pos : 0 < lam := by
      rw [hlamdef]
      have hne : ShadedBody.fullness' s Vb ≠ 0 := by
        rw [ShadedBody.fullness']
        exact ENNReal.div_ne_zero.mpr ⟨hS0, hD_ne_top⟩
      have : ShadedBody.fullness s Vb ≠ 0 := by
        intro h
        exact hne (by
          have := ShadedBody.coe_fullness s Vb
          rw [h] at this
          simpa using this.symm)
      exact pos_iff_ne_zero.mpr this
    -- Step 1: discard the indices of below-average shading
    set s₀ : Finset ι := ShadedBody.discardLowShading s Vb (1 / 2) with hs₀def
    have hs₀sub : s₀ ⊆ s := ShadedBody.discardLowShading_subset s Vb _
    have hhalf : ((1 / 2 : NNReal) : ENNReal) * S ≤ ∑ i ∈ s₀, volume (Vb i).shade := by
      have := ShadedBody.one_sub_mul_sum_volume_shade_le_sum_discardLowShading s Vb
        (c := (1 / 2 : NNReal)) (by norm_num)
      have hsub2 : (1 - (1 / 2 : NNReal)) = (1 / 2 : NNReal) := by
        rw [← NNReal.coe_inj, NNReal.coe_sub (by norm_num : (1 / 2 : NNReal) ≤ 1)]
        norm_num
      simpa [hs₀def, hSdef, hsub2] using this
    have hS_le_two : S ≤ 2 * ∑ i ∈ s₀, volume (Vb i).shade := by
      have h2 : (2 : ENNReal) * (((1 / 2 : NNReal) : ENNReal) * S) = S := by
        have hcoe : ((1 / 2 : NNReal) : ENNReal)
            = ((1 : NNReal) : ENNReal) / ((2 : NNReal) : ENNReal) :=
          ENNReal.coe_div (by norm_num)
        have : ((1 / 2 : NNReal) : ENNReal) = (2 : ENNReal)⁻¹ := by
          rw [hcoe]; simp
        rw [this, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      calc S = 2 * (((1 / 2 : NNReal) : ENNReal) * S) := h2.symm
        _ ≤ 2 * ∑ i ∈ s₀, volume (Vb i).shade := mul_le_mul' le_rfl hhalf
    -- Step 2: the retained densities live in `[lam/2, 1]`
    set f : ι → ENNReal := fun i => volume (Vb i).shade / volume (Vb i).carrier with hfdef
    have hcoe_half : (((lam / 2 : NNReal)) : ENNReal)
        = ((1 / 2 : NNReal) : ENNReal) * (lam : ENNReal) := by
      rw [show ((lam / 2 : NNReal) : ENNReal) = (lam : ENNReal) / ((2 : NNReal) : ENNReal)
        from ENNReal.coe_div (by norm_num),
        show ((1 / 2 : NNReal) : ENNReal) = ((1 : NNReal) : ENNReal) / ((2 : NNReal) : ENNReal)
        from ENNReal.coe_div (by norm_num)]
      simp [ENNReal.div_eq_inv_mul]
    have hIcc : ∀ i ∈ s₀,
        f i ∈ Set.Icc (((lam / 2 : NNReal)) : ENNReal) ((1 : NNReal) : ENNReal) := by
      intro i hi
      constructor
      · have hlow := ShadedBody.le_volume_shade_of_mem_discardLowShading (hi := hi)
        rw [hfdef]
        refine (ENNReal.le_div_iff_mul_le (Or.inl (hcar0 i)) (Or.inl (hcarT i))).2 ?_
        rw [hcoe_half]
        simpa [mul_assoc, hlamdef] using hlow
      · have hsub : volume (Vb i).shade ≤ volume (Vb i).carrier :=
          measure_mono (Vb i).shade_subset
        rw [hfdef]
        simp only [ENNReal.coe_one]
        exact ENNReal.div_le_of_le_mul (by simpa using hsub)
    have hapos : 0 < (lam / 2 : NNReal) := by
      have : (0 : NNReal) < lam := hlam_pos
      positivity
    obtain ⟨s', hs'sub, hsum, hband⟩ :=
      ENNReal.dyadic_pigeonhole₁'' (s := s₀) (w := fun i => volume (Vb i).shade) (f := f)
        (a := lam / 2) (b := 1) hapos hIcc
    refine ⟨s', hs'sub.trans hs₀sub, ?_, ?_⟩
    · -- the two losses compose into `massBandLoss`
      have hloss : ENNReal.ofReal (1 + Real.logb 2 (((1 : NNReal) : ℝ) / ((lam / 2 : NNReal) : ℝ)))
          = ENNReal.ofReal (1 + Real.logb 2 (2 / (lam : ℝ))) := by
        congr 2
        push_cast
        rw [one_div_div]
      change S ≤ massBandLoss lam * ∑ i ∈ s', volume (Vb i).shade
      unfold massBandLoss
      calc S ≤ 2 * ∑ i ∈ s₀, volume (Vb i).shade := hS_le_two
        _ ≤ 2 * (ENNReal.ofReal
              (1 + Real.logb 2 (((1 : NNReal) : ℝ) / ((lam / 2 : NNReal) : ℝ)))
              * ∑ i ∈ s', volume (Vb i).shade) := mul_le_mul' le_rfl hsum
        _ = 2 * ENNReal.ofReal (1 + Real.logb 2 (2 / (lam : ℝ)))
              * ∑ i ∈ s', volume (Vb i).shade := by rw [hloss, mul_assoc]
    · -- pointwise comparability of the densities, cleared of denominators
      intro i hi j hj
      have key : f i ≤ 2 * f j := hband i hi j hj
      have hmul := mul_le_mul' key
        (le_refl (volume (Vb i).carrier * volume (Vb j).carrier))
      have hL : f i * (volume (Vb i).carrier * volume (Vb j).carrier)
          = volume (Vb i).shade * volume (Vb j).carrier := by
        rw [hfdef]
        rw [← mul_assoc, ENNReal.div_mul_cancel (hcar0 i) (hcarT i)]
      have hR : 2 * f j * (volume (Vb i).carrier * volume (Vb j).carrier)
          = 2 * (volume (Vb j).shade * volume (Vb i).carrier) := by
        calc 2 * f j * (volume (Vb i).carrier * volume (Vb j).carrier)
            = 2 * (f j * volume (Vb j).carrier * volume (Vb i).carrier) := by ring
          _ = 2 * (volume (Vb j).shade * volume (Vb i).carrier) := by
              rw [hfdef, ENNReal.div_mul_cancel (hcar0 j) (hcarT j)]
      rw [hL, hR] at hmul
      simpa using hmul



omit [Nontrivial E] in
/-- Any constant is eventually dominated by a negative power of `δ`, with the threshold written as
an `NNReal` in `(0, 1]`.  (The version in `Kakeya.StickyKakeya.BallReduction` returns a real
threshold and lives behind a much heavier import.) -/
theorem exists_threshold_const_le_rpow_neg' (c : ℝ) {β : ℝ} (hβ : 0 < β) :
    ∃ d : NNReal, 0 < d ∧ d ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ d → c ≤ (δ : ℝ) ^ (-β) := by
  set C : ℝ := max c 1 with hCdef
  have hC1 : (1 : ℝ) ≤ C := le_max_right _ _
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have hbase : (0 : ℝ) < C ^ (-(1 / β)) := Real.rpow_pos_of_pos hCpos _
  have hbase1 : C ^ (-(1 / β)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hC1 (by
      simp only [neg_nonpos]
      positivity)
  refine ⟨Real.toNNReal (C ^ (-(1 / β))), Real.toNNReal_pos.mpr hbase, ?_, ?_⟩
  · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hbase.le]
    simpa using hbase1
  · intro δ hδpos hδle
    have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδpos
    have hδleR : (δ : ℝ) ≤ C ^ (-(1 / β)) := by
      have := NNReal.coe_le_coe.mpr hδle
      rwa [Real.coe_toNNReal _ hbase.le] at this
    have hmono : (C ^ (-(1 / β))) ^ (-β) ≤ (δ : ℝ) ^ (-β) :=
      Real.rpow_le_rpow_of_nonpos hδR hδleR (by linarith)
    have heq : (C ^ (-(1 / β))) ^ (-β) = C := by
      rw [← Real.rpow_mul hCpos.le]
      have hone : (-(1 / β)) * (-β) = 1 := by field_simp
      rw [hone, Real.rpow_one]
    rw [heq] at hmono
    exact le_trans (le_max_left c 1) hmono

/-! ### The banding loss is subpolynomial: the explicit threshold -/

/-- **The banding loss against the grid loss.**

`massBandLoss λ ≤ (4 + 2η/log 2) · gridLoss 1 1 δ` whenever `δ^η ≤ λ`.  This is the whole content
of the loss bookkeeping: with `L = log (1/δ)` the retained densities lie in `[λ/2, 1]`, hence in
`[δ^η/2, 1]`, whose ratio is `2 δ^{-η}`, so the number of dyadic bands is `1 + log₂ 2 + η log₂ (1/δ)
= 2 + ηL/log 2`, and the discard doubles it.  The right-hand side is a *linear* function of `L`,
whereas `StickyKakeya.gridLoss 1 1 δ = (1 + L)^{(⌈log log 1/δ⌉+1)^2} ≥ 1 + L`. -/
theorem massBandLoss_le_gridLoss {η : ℝ} (hη : 0 ≤ η) {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {lam : NNReal} (hlam : ENNReal.ofReal ((δ : ℝ) ^ η) ≤ (lam : ENNReal)) :
    massBandLoss lam
      ≤ ENNReal.ofReal ((4 + 2 * η / Real.log 2) * StickyKakeya.gridLoss 1 1 δ) := by
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδ1R : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set L : ℝ := -Real.log (δ : ℝ) with hLdef
  have hLnn : 0 ≤ L := by
    rw [hLdef, neg_nonneg]
    exact Real.log_nonpos hδR.le hδ1R
  -- the fullness lower bound, transported to the reals
  have hpowpos : (0 : ℝ) < (δ : ℝ) ^ η := Real.rpow_pos_of_pos hδR η
  have hlamR : (δ : ℝ) ^ η ≤ (lam : ℝ) := by
    have := (ENNReal.ofReal_le_iff_le_toReal (by simp)).mp hlam
    simpa using this
  have hlampos : (0 : ℝ) < (lam : ℝ) := lt_of_lt_of_le hpowpos hlamR
  -- the number of dyadic bands
  have hloglam : η * Real.log (δ : ℝ) ≤ Real.log (lam : ℝ) := by
    have := Real.log_le_log hpowpos hlamR
    rwa [Real.log_rpow hδR] at this
  have hlogb : Real.logb 2 (2 / (lam : ℝ)) ≤ 1 + η * L / Real.log 2 := by
    have hdiv : Real.log (2 / (lam : ℝ)) = Real.log 2 - Real.log (lam : ℝ) :=
      Real.log_div (by norm_num) (ne_of_gt hlampos)
    rw [Real.logb, hdiv]
    rw [div_le_iff₀ hlog2]
    have : Real.log 2 - Real.log (lam : ℝ) ≤ Real.log 2 - η * Real.log (δ : ℝ) := by linarith
    have hrw : (1 + η * L / Real.log 2) * Real.log 2 = Real.log 2 + η * L := by
      field_simp
    rw [hrw, hLdef]
    linarith
  -- assemble
  have hstep : (1 : ℝ) + Real.logb 2 (2 / (lam : ℝ)) ≤ 2 + η * L / Real.log 2 := by linarith
  have hnn2 : (0 : ℝ) ≤ 2 + η * L / Real.log 2 := by positivity
  have hgrid : (1 : ℝ) + L ≤ StickyKakeya.gridLoss 1 1 δ := by
    have hbase : (1 : ℝ) ≤ 1 - Real.log (δ : ℝ) := by
      have : Real.log (δ : ℝ) ≤ 0 := Real.log_nonpos hδR.le hδ1R
      linarith
    have hexp : 1 ≤ 1 * (Tube.ssfGridLen δ + 1) ^ 2 := by
      have : 1 ≤ (Tube.ssfGridLen δ + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
      omega
    have : (1 - Real.log (δ : ℝ)) ^ (1 : ℕ)
        ≤ (1 - Real.log (δ : ℝ)) ^ (1 * (Tube.ssfGridLen δ + 1) ^ 2) :=
      pow_le_pow_right₀ hbase hexp
    rw [StickyKakeya.gridLoss]
    simp only [NNReal.coe_one, one_pow, one_mul]
    rw [one_mul] at this
    rw [hLdef]
    linarith
  have hfinal : (2 : ℝ) * (2 + η * L / Real.log 2)
      ≤ (4 + 2 * η / Real.log 2) * StickyKakeya.gridLoss 1 1 δ := by
    have hc : (0 : ℝ) ≤ 2 * η / Real.log 2 := by positivity
    have h1 : (2 : ℝ) * (2 + η * L / Real.log 2) = 4 + (2 * η / Real.log 2) * L := by
      field_simp
      ring
    have h2 : (4 : ℝ) + (2 * η / Real.log 2) * L ≤ (4 + 2 * η / Real.log 2) * (1 + L) := by
      nlinarith [hLnn, hc]
    have h3 : (4 + 2 * η / Real.log 2) * (1 + L)
        ≤ (4 + 2 * η / Real.log 2) * StickyKakeya.gridLoss 1 1 δ :=
      mul_le_mul_of_nonneg_left hgrid (by positivity)
    linarith
  unfold massBandLoss
  calc 2 * ENNReal.ofReal (1 + Real.logb 2 (2 / (lam : ℝ)))
      ≤ 2 * ENNReal.ofReal (2 + η * L / Real.log 2) := by
        exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hstep)
    _ = ENNReal.ofReal (2 * (2 + η * L / Real.log 2)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
    _ ≤ ENNReal.ofReal ((4 + 2 * η / Real.log 2) * StickyKakeya.gridLoss 1 1 δ) :=
        ENNReal.ofReal_le_ofReal hfinal

/-- **The banding loss is subpolynomial** — the threshold form the development consumes.

For every fullness exponent `η ≥ 0` and every budget `α > 0` there is a threshold `δ₀ > 0`,
depending only on `(η, α)`, below which the mass-banding loss of a family of fullness at least
`δ^η` is at most `δ^{-α}`.  The threshold is genuinely needed: the loss is `Θ(η log (1/δ))`, which
is `≤ δ^{-α}` only once `log (1/δ)` exceeds a value determined by `α` and `η`. -/
theorem exists_threshold_massBandLoss_le {η α : ℝ} (hη : 0 ≤ η) (hα : 0 < α) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ → ∀ lam : NNReal,
        ENNReal.ofReal ((δ : ℝ) ^ η) ≤ (lam : ENNReal) →
        massBandLoss lam ≤ ENNReal.ofReal ((δ : ℝ) ^ (-α)) := by
  have hα2 : (0 : ℝ) < α / 2 := by linarith
  obtain ⟨d1, hd1pos, hd1le1, hd1⟩ :=
    exists_threshold_const_le_rpow_neg' (4 + 2 * η / Real.log 2) hα2
  obtain ⟨d2, hd2pos, hd2le1, hd2⟩ :=
    StickyKakeya.exists_threshold_gridLoss_le 1 le_rfl 1 (α / 2) hα2
  refine ⟨min d2 d1, lt_min hd2pos hd1pos, (min_le_right _ _).trans hd1le1, ?_⟩
  · intro δ hδpos hδle lam hlam
    have hδd2 : δ ≤ d2 := hδle.trans (min_le_left _ _)
    have hδd1 : δ ≤ d1 := hδle.trans (min_le_right _ _)
    have hδ1 : δ ≤ 1 := hδd1.trans hd1le1
    have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδpos
    have hconst : (4 + 2 * η / Real.log 2) ≤ (δ : ℝ) ^ (-(α / 2)) := hd1 hδpos hδd1
    have hgl : StickyKakeya.gridLoss 1 1 δ ≤ (δ : ℝ) ^ (-(α / 2)) := hd2 hδpos hδd2
    have hglnn : (0 : ℝ) ≤ StickyKakeya.gridLoss 1 1 δ := by
      have := StickyKakeya.one_le_gridLoss 1 le_rfl 1 hδ1
      linarith
    have hprod : (4 + 2 * η / Real.log 2) * StickyKakeya.gridLoss 1 1 δ ≤ (δ : ℝ) ^ (-α) := by
      have hsplit : (δ : ℝ) ^ (-α) = (δ : ℝ) ^ (-(α / 2)) * (δ : ℝ) ^ (-(α / 2)) := by
        rw [← Real.rpow_add hδR]
        ring_nf
      rw [hsplit]
      have hcnn : (0 : ℝ) ≤ 4 + 2 * η / Real.log 2 := by
        have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        positivity
      exact mul_le_mul hconst hgl hglnn (Real.rpow_nonneg hδR.le _)
    exact (massBandLoss_le_gridLoss hη hδpos hδ1 hlam).trans (ENNReal.ofReal_le_ofReal hprod)


/-! ### Guardrails: the statement is neither vacuous nor trivially satisfiable -/

omit [Nontrivial E] in
/-- **The retained family is nonempty whenever there is mass to retain.**

The mass clause of `Kakeya.ML2Shaded.exists_massBanded_shadeRefinement` is not satisfiable by the
empty subfamily: `∅` carries no shaded mass, and `massBandLoss` is finite. -/
theorem nonempty_of_massBand {s s' : Finset ι} {V : ι → ShadedTube δ E} {lam : NNReal}
    (hpos : 0 < ∑ i ∈ s, volume (V i).shade)
    (hmass : (∑ i ∈ s, volume (V i).shade) ≤ massBandLoss lam * ∑ i ∈ s', volume (V i).shade) :
    s'.Nonempty := by
  rcases Finset.eq_empty_or_nonempty s' with rfl | h
  · simp only [Finset.sum_empty, mul_zero] at hmass
    exact absurd (le_antisymm hmass zero_le) hpos.ne'
  · exact h

omit [Nontrivial E] in
/-- **Comparability is all-or-nothing on masses.**

On a family of bodies of positive finite volume, `K`-comparability of the densities forces the
shaded masses to vanish simultaneously.  This is the structural reason a mass-banding *must*
discard indices and cannot be achieved by shrinking shades alone: the moment one retained index
loses all of its mass while another keeps some, comparability fails at every constant. -/
theorem shade_eq_zero_of_hasComparableDensities {K : NNReal} {u : Finset ι} {V : ι → ShadedBody E}
    (hcar0 : ∀ i, volume (V i).carrier ≠ 0) (_hcarT : ∀ i, volume (V i).carrier ≠ ⊤)
    (h : HasComparableDensities K u V) {i j : ι} (hi : i ∈ u) (hj : j ∈ u)
    (hzero : volume (V j).shade = 0) : volume (V i).shade = 0 := by
  have hij := h i hi j hj
  rw [hzero, zero_mul, mul_zero] at hij
  have : volume (V i).shade * volume (V j).carrier = 0 := le_antisymm hij zero_le
  rcases mul_eq_zero.mp this with h1 | h2
  · exact h1
  · exact absurd h2 (hcar0 j)

/-- The unit ball, fully shaded. -/
noncomputable def unitFull : ShadedBody E where
  toConvexSpaceBody := ConvexSpaceBody.closedUnitBall
  shade := Metric.closedBall (0 : E) 1
  measurableSet_shade := measurableSet_closedBall
  shade_subset := subset_rfl

/-- The unit ball, with empty shading. -/
noncomputable def unitEmpty : ShadedBody E where
  toConvexSpaceBody := ConvexSpaceBody.closedUnitBall
  shade := ∅
  measurableSet_shade := MeasurableSet.empty
  shade_subset := Set.empty_subset _

omit [Nontrivial E] in
/-- **An aggregate mass retention does not preserve comparability of the densities.**

A two-body family, both bodies the unit ball, both fully shaded; the sub-shading empties the second
one.  It retains *half* of the aggregate shaded mass — a `2`-refinement, better than any loss this
development ever charges — the carriers are literally unchanged, and yet the resulting densities are
comparable at **no** constant whatsoever.

This is the exact shape of the conclusion of
`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet`, which returns a sub-shading together
with an aggregate `ShadedBody.fullness'` loss and nothing per-index.  So no amount of tightening of
that aggregate loss can yield `Kakeya.ML2Shaded.HasComparableDensities` for the refined shading:
the missing information is pointwise, and an aggregate bound never supplies it. -/
theorem not_hasComparableDensities_of_aggregate_retention :
    ∃ (u : Finset (Fin 2)) (V V' : Fin 2 → ShadedBody E),
      (∀ i, (V' i).toConvexSpaceBody = (V i).toConvexSpaceBody) ∧
      (∀ i, (V' i).shade ⊆ (V i).shade) ∧
      (∑ i ∈ u, volume (V i).shade) ≤ 2 * ∑ i ∈ u, volume (V' i).shade ∧
      HasComparableDensities 1 u V ∧
      ∀ K : NNReal, ¬ HasComparableDensities K u V' := by
  classical
  have hBpos : 0 < volume (Metric.closedBall (0 : E) 1) :=
    Metric.measure_closedBall_pos volume 0 one_pos
  have hBtop : volume (Metric.closedBall (0 : E) 1) ≠ ⊤ :=
    (isCompact_closedBall (0 : E) 1).measure_ne_top
  refine ⟨Finset.univ, fun _ => unitFull, fun i => if i = 0 then unitFull else unitEmpty,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i; by_cases h : i = 0 <;> simp [h, unitFull, unitEmpty]
  · intro i; by_cases h : i = 0 <;> simp [h, unitFull, unitEmpty]
  · have h1 : ∑ i : Fin 2, volume ((fun _ : Fin 2 => (unitFull : ShadedBody E)) i).shade
        = 2 * volume (Metric.closedBall (0 : E) 1) := by
      simp [unitFull, two_mul]
    have h2 : ∑ i : Fin 2, volume ((if i = 0 then (unitFull : ShadedBody E) else unitEmpty)).shade
        = volume (Metric.closedBall (0 : E) 1) := by
      simp [unitFull, unitEmpty, Fin.sum_univ_two]
    rw [h1, h2]
  · intro i _ j _
    simp [unitFull]
  · intro K hK
    have h01 := hK 0 (Finset.mem_univ 0) 1 (Finset.mem_univ 1)
    simp only [show ((1 : Fin 2) = 0) = False by simp, if_false] at h01
    have : volume (Metric.closedBall (0 : E) 1) * volume (Metric.closedBall (0 : E) 1) ≤ 0 := by
      simpa [unitFull, unitEmpty, ConvexSpaceBody.closedUnitBall] using h01
    exact absurd (le_antisymm this zero_le) (by
      exact (ENNReal.mul_pos hBpos.ne' hBpos.ne').ne')



/-- **Discarding is forced.**  On a family carrying one index of positive shaded mass and one of
zero shaded mass, no subfamily containing both is `2`-comparable.  So the subfamily returned by
`Kakeya.ML2Shaded.exists_massBanded_shadeRefinement` is in general a *proper* subfamily: the
statement is not satisfiable by `s' = s`. -/
theorem massBand_must_discard {δ : NNReal} (hδ : 0 < δ) {V : ι → ShadedTube δ E}
    {i j : ι} (hipos : volume (V i).shade ≠ 0) (hjzero : volume (V j).shade = 0)
    {s' : Finset ι} (hcomp : HasComparableDensities 2 s' (fun i => (V i).toShadedBody))
    (hi : i ∈ s') (hj : j ∈ s') : False :=
  hipos (shade_eq_zero_of_hasComparableDensities
    (fun k => volume_carrier_ne_zero hδ (V k).toTube)
    (fun k => volume_carrier_ne_top (V k).toTube) hcomp hi hj hjzero)

/-- **A concrete family of shaded `δ`-tubes on which the mass banding is forced to discard.**

Two copies of one and the same `δ`-tube, the first fully shaded and the second not shaded at all.
Every subfamily satisfying *both* clauses of `Kakeya.ML2Shaded.exists_massBanded_shadeRefinement`
is exactly `{0}`: the mass clause rules out `∅` and `{1}`, the comparability clause rules out
`{0, 1}`.  So the theorem is inhabited, its conclusion is not satisfiable by the whole family, and
the discard it performs is doing real work. -/
theorem massBand_forced_on_concrete_family {δ : NNReal} (hδ : 0 < δ) :
    ∃ V : Fin 2 → ShadedTube δ E,
      ∀ s' ⊆ (Finset.univ : Finset (Fin 2)),
        (∑ i ∈ (Finset.univ : Finset (Fin 2)), volume (V i).shade)
            ≤ massBandLoss (ShadedBody.fullness Finset.univ (fun i => (V i).toShadedBody))
              * ∑ i ∈ s', volume (V i).shade →
          HasComparableDensities 2 s' (fun i => (V i).toShadedBody) →
          s' = {0} := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hvne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  set u : E := ‖v‖⁻¹ • v with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
    exact inv_mul_cancel₀ hvne
  set T : Tube δ E := Tube.ofMidpointDirection δ 0 u hu with hT_def
  have hTmeas : MeasurableSet T.carrier := T.isCompact'.isClosed.measurableSet
  set Vfull : ShadedTube δ E :=
    { toTube := T
      shade := T.carrier
      measurableSet_shade := hTmeas
      shade_subset := subset_rfl } with hVfull
  set Vempty : ShadedTube δ E :=
    { toTube := T
      shade := ∅
      measurableSet_shade := MeasurableSet.empty
      shade_subset := Set.empty_subset _ } with hVempty
  set V : Fin 2 → ShadedTube δ E := fun i => if i = 0 then Vfull else Vempty with hV
  have hTpos : volume T.carrier ≠ 0 := volume_carrier_ne_zero hδ T
  have hshade0 : volume (V 0).shade = volume T.carrier := by simp [hV, hVfull]
  have hshade1 : volume (V 1).shade = 0 := by simp [hV, hVempty]
  refine ⟨V, ?_⟩
  intro s' _ hmass hcomp
  -- `1 ∉ s'`, else comparability would force the mass at `0` to vanish
  have h1notmem : (1 : Fin 2) ∉ s' := by
    intro h1
    by_cases h0 : (0 : Fin 2) ∈ s'
    · exact massBand_must_discard hδ (V := V) (i := 0) (j := 1)
        (by rw [hshade0]; exact hTpos) hshade1 hcomp h0 h1
    · -- `s' ⊆ {1}` carries no mass, contradicting the mass clause
      have hsum' : ∑ i ∈ s', volume (V i).shade = 0 := by
        refine Finset.sum_eq_zero (fun i hi => ?_)
        have : i = 1 := by
          fin_cases i
          · exact absurd hi h0
          · rfl
        rw [this, hshade1]
      rw [hsum', mul_zero] at hmass
      have htot : ∑ i ∈ (Finset.univ : Finset (Fin 2)), volume (V i).shade
          = volume T.carrier := by
        rw [Fin.sum_univ_two, hshade0, hshade1, add_zero]
      rw [htot] at hmass
      exact hTpos (le_antisymm hmass zero_le)
  -- `0 ∈ s'`, else `s'` is empty and carries no mass
  have h0mem : (0 : Fin 2) ∈ s' := by
    by_contra h0
    have hsum' : ∑ i ∈ s', volume (V i).shade = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      fin_cases i
      · exact absurd hi h0
      · exact absurd hi h1notmem
    rw [hsum', mul_zero] at hmass
    have htot : ∑ i ∈ (Finset.univ : Finset (Fin 2)), volume (V i).shade
        = volume T.carrier := by
      rw [Fin.sum_univ_two, hshade0, hshade1, add_zero]
    rw [htot] at hmass
    exact hTpos (le_antisymm hmass zero_le)
  ext i
  fin_cases i <;> simp [h0mem, h1notmem]


omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Every node of a uniform hierarchy on a nonempty family has a nonempty class.**

The two halves of Definition 2.1(iii) force this: an empty class at one node makes `branchingN k`
vanish through `Tube.UniformTubeSet.le_card_class`, and then
`Tube.UniformTubeSet.card_class_le` empties *every* class at that grid index, contradicting
`Tube.GridCoverSystem.assign_mem` on a nonempty family.

This is the precise obstruction to promoting the mass-banded subfamily `s''` of
`Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao` back into a
`Tube.UniformTubeSet` carrying the *same* cover: a subfamily that misses even one node of
`GridCoverSystem.indexSet` cannot carry one, and the mass banding has no control over which nodes
it misses.  Shrinking `indexSet` to the nodes still hit is the only repair, and it shrinks
`Tube.UniformTubeSet.nodesUnder`, under which the third window bullet — a *lower* bound on
`Kakeya.maxDensity` — is not inherited. -/
theorem coverClass_nonempty_of_uniformTubeSet {δ : NNReal} {u : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet u T N C) (hu : u.Nonempty) {k : ℕ} (hk : k ≤ N)
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet k) : (coverClass u (𝒰.cover.assign k) j).Nonempty := by
  classical
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hbr : 𝒰.branchingN k = 0 := by
    have := 𝒰.le_card_class k hk j hj
    rw [hempty] at this
    simpa using this
  obtain ⟨i₀, hi₀⟩ := hu
  have hj₀ : 𝒰.cover.assign k i₀ ∈ 𝒰.cover.indexSet k := 𝒰.cover.assign_mem k hk i₀ hi₀
  have hcard := 𝒰.card_class_le k hk _ hj₀
  rw [hbr, mul_zero] at hcard
  have hzero : (coverClass u (𝒰.cover.assign k) (𝒰.cover.assign k i₀)).card = 0 := by
    exact_mod_cast le_antisymm hcard (zero_le (a := ((coverClass u (𝒰.cover.assign k)
      (𝒰.cover.assign k i₀)).card : NNReal)))
  have hmem : i₀ ∈ coverClass u (𝒰.cover.assign k) (𝒰.cover.assign k i₀) := by
    simp [coverClass, hi₀]
  exact absurd (Finset.card_eq_zero.mp hzero ▸ hmem) (by simp)

/-! ### Transport helpers -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Two hierarchies with literally the same node index sets and node tubes have the same
`Tube.UniformTubeSet.nodesUnder`, whatever families or constants they are carried on.  This is what
makes both alternatives of GWZ 7.7(B) survive the shaded uniformization of
`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet`, which returns exactly these two
equalities. -/
theorem nodesUnder_congr {δ : NNReal} {s₁ s₂ : Finset ι} {T₁ T₂ : ι → Tube δ E} {N : ℕ}
    {C₁ C₂ : NNReal} (𝒰₁ : UniformTubeSet s₁ T₁ N C₁) (𝒰₂ : UniformTubeSet s₂ T₂ N C₂)
    (hIdx : 𝒰₁.cover.indexSet = 𝒰₂.cover.indexSet)
    (hTube : 𝒰₁.cover.tube = 𝒰₂.cover.tube) (b a : ℕ) (j : ι) :
    𝒰₁.nodesUnder b a j = 𝒰₂.nodesUnder b a j := by
  classical
  simp only [UniformTubeSet.nodesUnder, UniformTubeSet.nodesIn, hIdx, hTube]

/-- **The fullness loss, read on the shaded masses.**  The carriers are literally unchanged by a
sub-shading on the same tubes, so the `ShadedBody.fullness'` inequality returned by
`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet` is the mass inequality that
`ShadedBody.isCRefinement_of_isRefinement_of_sum_le` consumes. -/
theorem sum_shade_le_of_fullness_le {δ : NNReal} (hδ : 0 < δ) {u : Finset ι}
    {V V' : ι → ShadedTube δ E} (htube : ∀ i, (V' i).toTube = (V i).toTube)
    {L : ENNReal} (hL : ShadedBody.fullness' u (fun i => (V i).toShadedBody)
        ≤ L * ShadedBody.fullness' u (fun i => (V' i).toShadedBody)) :
    (∑ i ∈ u, volume (V i).shade) ≤ L * ∑ i ∈ u, volume (V' i).shade := by
  classical
  rcases Finset.eq_empty_or_nonempty u with rfl | hune
  · simp
  set D : ENNReal := ∑ i ∈ u, volume (V i).carrier with hDdef
  have hDeq : (∑ i ∈ u, volume (V' i).carrier) = D := by
    rw [hDdef]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    calc (V' i).carrier = (V' i).toTube.carrier := rfl
      _ = (V i).toTube.carrier := by rw [htube i]
      _ = (V i).carrier := rfl
  have hD0 : D ≠ 0 := by
    obtain ⟨i₀, hi₀⟩ := hune
    intro h
    have := Finset.sum_eq_zero_iff.mp h i₀ hi₀
    exact volume_carrier_ne_zero hδ (V i₀).toTube this
  have hDT : D ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => volume_carrier_ne_top (V i).toTube)
  have hL' : (∑ i ∈ u, volume (V i).shade) / D
      ≤ (L * ∑ i ∈ u, volume (V' i).shade) / D := by
    have h1 : ShadedBody.fullness' u (fun i => (V i).toShadedBody)
        = (∑ i ∈ u, volume (V i).shade) / D := rfl
    have h2 : L * ShadedBody.fullness' u (fun i => (V' i).toShadedBody)
        = (L * ∑ i ∈ u, volume (V' i).shade) / D := by
      change L * ((∑ i ∈ u, volume (V' i).shade) / (∑ i ∈ u, volume (V' i).carrier))
        = (L * ∑ i ∈ u, volume (V' i).shade) / D
      rw [hDeq, mul_div_assoc]
    rw [← h1, ← h2]
    exact hL
  have hmul := mul_le_mul' hL' (le_refl D)
  rwa [ENNReal.div_mul_cancel hD0 hDT, ENNReal.div_mul_cancel hD0 hDT] at hmul



/-! ### From a share of the shaded mass to a share of the index set -/

/-- **A mass share is a cardinality share, at the price of the fullness and of the dimensional
tube-volume ratio.**

If a subfamily `s' ⊆ s` carries all but a factor `L` of the shaded mass, then it carries all but a
factor `L · C_n / (λ c_n)` of the *indices*, where `λ = λ(𝕋, Y)` is the fullness of the whole family
and `c_n ≤ |T| / δ^{n-1} ≤ C_n` are the two dimensional tube-volume constants.

No comparability of the densities is used — only `Y_i ⊆ T_i` and the two-sided volume bracket for a
`δ`-tube.  This is the converse direction to the blueprint's
`exists_massShare_of_comparableDensities`, and it is what makes the mass-banded subfamily of
`Kakeya.ML2Shaded.exists_massBanded_shadeRefinement` usable by a consumer that needs a cardinality
bound: under the standing hypothesis `δ^η ≤ λ` the extra factor is `δ^{-η}` times a constant. -/
theorem card_le_of_sum_shade_le {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {s s' : Finset ι} {V : ι → ShadedTube δ E} {L : ENNReal}
    (hmass : (∑ i ∈ s, volume (V i).shade) ≤ L * ∑ i ∈ s', volume (V i).shade) :
    (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal)
        * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) * (s.card : ENNReal)
      ≤ L * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * (s'.card : ENNReal) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set p : ENNReal := (δ : ENNReal) ^ (n - 1) with hp
  have hp0 : p ≠ 0 := by
    rw [hp]
    exact pow_ne_zero _ (by simpa using hδ0.ne')
  have hpT : p ≠ ⊤ := by
    rw [hp]
    exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  set lam : NNReal := ShadedBody.fullness s (fun i => (V i).toShadedBody) with hlam
  -- lower bound on the total shaded mass
  have hlow : (lam : ENNReal) * ((Tube.le_volume.c n : ENNReal) * p) * (s.card : ENNReal)
      ≤ ∑ i ∈ s, volume (V i).shade := by
    have hsum : ∑ i ∈ s, volume (V i).shade
        = (lam : ENNReal) * ∑ i ∈ s, volume ((V i).toShadedBody).carrier :=
      ShadedBody.sum_volumeReal_shade_eq_fullness_mul s (fun i => (V i).toShadedBody)
    have hcar : (s.card : ENNReal) * ((Tube.le_volume.c n : ENNReal) * p)
        ≤ ∑ i ∈ s, volume ((V i).toShadedBody).carrier := by
      have := Finset.card_nsmul_le_sum s (fun i => volume ((V i).toShadedBody).carrier)
        ((Tube.le_volume.c n : ENNReal) * p) (fun i _ => by
          simpa [hn, hp] using Tube.le_volume (E := E) (V i).toTube)
      simpa [nsmul_eq_mul] using this
    calc (lam : ENNReal) * ((Tube.le_volume.c n : ENNReal) * p) * (s.card : ENNReal)
        = (lam : ENNReal) * ((s.card : ENNReal) * ((Tube.le_volume.c n : ENNReal) * p)) := by ring
      _ ≤ (lam : ENNReal) * ∑ i ∈ s, volume ((V i).toShadedBody).carrier :=
          mul_le_mul' le_rfl hcar
      _ = ∑ i ∈ s, volume (V i).shade := hsum.symm
  -- upper bound on the retained shaded mass
  have hup : (∑ i ∈ s', volume (V i).shade)
      ≤ (s'.card : ENNReal) * ((Tube.volume_le.C n : ENNReal) * p) := by
    have := Finset.sum_le_card_nsmul s' (fun i => volume (V i).shade)
      ((Tube.volume_le.C n : ENNReal) * p) (fun i _ => by
        refine le_trans (measure_mono ((V i).toShadedBody).shade_subset) ?_
        simpa [hn, hp] using Tube.volume_le (E := E) hδ1 (V i).toTube)
    simpa [nsmul_eq_mul] using this
  -- chain and cancel the common factor `δ^{n-1}`
  have hchain : p * ((lam : ENNReal) * (Tube.le_volume.c n : ENNReal) * (s.card : ENNReal))
      ≤ p * (L * (Tube.volume_le.C n : ENNReal) * (s'.card : ENNReal)) := by
    calc p * ((lam : ENNReal) * (Tube.le_volume.c n : ENNReal) * (s.card : ENNReal))
        = (lam : ENNReal) * ((Tube.le_volume.c n : ENNReal) * p) * (s.card : ENNReal) := by ring
      _ ≤ ∑ i ∈ s, volume (V i).shade := hlow
      _ ≤ L * ∑ i ∈ s', volume (V i).shade := hmass
      _ ≤ L * ((s'.card : ENNReal) * ((Tube.volume_le.C n : ENNReal) * p)) :=
          mul_le_mul' le_rfl hup
      _ = p * (L * (Tube.volume_le.C n : ENNReal) * (s'.card : ENNReal)) := by ring
  exact (ENNReal.mul_le_mul_iff_right hp0 hpT).mp hchain


/-- **The mass-banded shade refinement with its cardinality share.**

`Kakeya.ML2Shaded.exists_massBanded_shadeRefinement` composed with
`Kakeya.ML2Shaded.card_le_of_sum_shade_le`: the retained subfamily carries a share of the *indices*
as well as of the mass, at the price of the fullness and of the dimensional tube-volume ratio.  This
is the form a consumer needing `#s ≤ Loss · #s'` uses. -/
theorem exists_massBanded_shadeRefinement_card {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (s : Finset ι) (V : ι → ShadedTube δ E) :
    ∃ s' ⊆ s,
      (∑ i ∈ s, volume (V i).shade)
          ≤ massBandLoss (ShadedBody.fullness s (fun i => (V i).toShadedBody))
              * ∑ i ∈ s', volume (V i).shade ∧
        HasComparableDensities 2 s' (fun i => (V i).toShadedBody) ∧
        (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) * (s.card : ENNReal)
          ≤ massBandLoss (ShadedBody.fullness s (fun i => (V i).toShadedBody))
              * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * (s'.card : ENNReal) := by
  obtain ⟨s', hsub, hmass, hcomp⟩ := exists_massBanded_shadeRefinement hδ0 s V
  exact ⟨s', hsub, hmass, hcomp, card_le_of_sum_shade_le hδ0 hδ1 hmass⟩


/-! ### One-sided density: the pointwise invariant a consumer of 7.7(B) actually needs

`Kakeya.ML2Shaded.HasComparableDensities` is two-sided, and the price of establishing it is the
`Kakeya.ML2Shaded.massBandLoss` logarithm.  The *one-sided* half — a pointwise lower bound
`lam · |T_i| ≤ |Y_i|` — costs only a factor `2` of the shaded mass, and it is strictly stronger
where it matters: it is inherited by **every** subfamily together with the fullness bound
`lam ≤ λ(u', Y)`, whereas a fullness bound on `u` alone says nothing about a subfamily of `u`.

This is the aggregate-versus-pointwise conversion in its safe direction, and the direction the
consumer needs: the dividing-scales dichotomy hands back an arbitrary subfamily `s' ⊆ s`, and the
consumer must recover `δ^{η'} ≤ λ(s', Y')` from `δ^{η} ≤ λ(s, Y)`.  Nothing but a pointwise
hypothesis can do that. -/

/-- **A pointwise lower bound on the shading densities**: every body of `u` has shaded mass at
least `lam` times its own volume.

Unlike `ShadedBody.fullness`, which is an aggregate, this restricts to subfamilies
(`Kakeya.ML2Shaded.HasDenseShading.subset`) and therefore *transports* the fullness to every
subfamily (`Kakeya.ML2Shaded.HasDenseShading.le_fullness'`). -/
def HasDenseShading (lam : NNReal) (u : Finset ι) (V : ι → ShadedBody E) : Prop :=
  ∀ i ∈ u, (lam : ENNReal) * volume (V i).carrier ≤ volume (V i).shade

omit [Nontrivial E] in
theorem HasDenseShading.subset {lam : NNReal} {u u' : Finset ι} {V : ι → ShadedBody E}
    (h : HasDenseShading lam u V) (hsub : u' ⊆ u) : HasDenseShading lam u' V :=
  fun i hi => h i (hsub hi)

omit [Nontrivial E] in
theorem HasDenseShading.mono {lam lam' : NNReal} {u : Finset ι} {V : ι → ShadedBody E}
    (h : HasDenseShading lam u V) (hle : lam' ≤ lam) : HasDenseShading lam' u V :=
  fun i hi => le_trans (mul_le_mul_left (ENNReal.coe_le_coe.mpr hle) _) (h i hi)

omit [Nontrivial E] in
/-- **A dense shading gives the fullness of the family, and of every subfamily.**  This is the
payoff of the pointwise form: the hypothesis is inherited by subfamilies, so the conclusion is
available at every subfamily too, with the *same* `lam` and no loss. -/
theorem HasDenseShading.le_fullness' {lam : NNReal} {u : Finset ι} {V : ι → ShadedBody E}
    (h : HasDenseShading lam u V)
    (hne : (∑ i ∈ u, volume (V i).carrier) ≠ 0)
    (hnt : (∑ i ∈ u, volume (V i).carrier) ≠ ⊤) :
    (lam : ENNReal) ≤ ShadedBody.fullness' u V := by
  rw [ShadedBody.fullness', ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl hnt)]
  calc (lam : ENNReal) * ∑ i ∈ u, volume (V i).carrier
      = ∑ i ∈ u, (lam : ENNReal) * volume (V i).carrier := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ u, volume (V i).shade := Finset.sum_le_sum h

/-- The `δ`-tube instance of `Kakeya.ML2Shaded.HasDenseShading.le_fullness'`: for a nonempty family
of `δ`-tubes with `0 < δ` the two side conditions are automatic. -/
theorem HasDenseShading.le_fullness_tube {δ : NNReal} (hδ : 0 < δ) {lam : NNReal} {u : Finset ι}
    {V : ι → ShadedTube δ E} (h : HasDenseShading lam u (fun i => (V i).toShadedBody))
    (hu : u.Nonempty) :
    (lam : ENNReal) ≤ ShadedBody.fullness' u (fun i => (V i).toShadedBody) := by
  classical
  refine h.le_fullness' ?_ ?_
  · obtain ⟨i₀, hi₀⟩ := hu
    intro hzero
    exact volume_carrier_ne_zero hδ (V i₀).toTube
      (Finset.sum_eq_zero_iff.mp hzero i₀ hi₀)
  · exact ENNReal.sum_ne_top.mpr (fun i _ => volume_carrier_ne_top (V i).toTube)

omit [Nontrivial E] in
/-- **A dense shading is a comparable shading**, at the constant `lam⁻¹`: the densities lie in
`[lam, 1]`.  The constant is *not* absolute — it is `δ^{-η}` under the standing hypothesis
`δ^η ≤ lam` — which is exactly why `Kakeya.ML2Shaded.exists_massBanded_shadeRefinement` pays a
logarithm to reach the absolute constant `2` instead. -/
theorem HasDenseShading.hasComparableDensities {lam : NNReal} {u : Finset ι}
    {V : ι → ShadedBody E} (h : HasDenseShading lam u V) (hlam : 0 < lam) :
    HasComparableDensities lam⁻¹ u V := by
  intro i hi j hj
  have hj' : (lam : ENNReal) * volume (V j).carrier ≤ volume (V j).shade := h j hj
  have hi' : volume (V i).shade ≤ volume (V i).carrier := measure_mono (V i).shade_subset
  have hlam0 : (lam : NNReal) ≠ 0 := hlam.ne'
  have hcoe : ((lam⁻¹ : NNReal) : ENNReal) = ((lam : ENNReal))⁻¹ := ENNReal.coe_inv hlam0
  have hcancel : ((lam : ENNReal))⁻¹ * (lam : ENNReal) = 1 :=
    ENNReal.inv_mul_cancel (by simpa using hlam0) ENNReal.coe_ne_top
  calc volume (V i).shade * volume (V j).carrier
      ≤ volume (V i).carrier * volume (V j).carrier := mul_le_mul' hi' le_rfl
    _ = (((lam : ENNReal))⁻¹ * (lam : ENNReal)) * (volume (V j).carrier
          * volume (V i).carrier) := by rw [hcancel]; ring
    _ = ((lam : ENNReal))⁻¹ * (((lam : ENNReal) * volume (V j).carrier)
          * volume (V i).carrier) := by ring
    _ ≤ ((lam : ENNReal))⁻¹ * (volume (V j).shade * volume (V i).carrier) :=
        mul_le_mul' le_rfl (mul_le_mul' hj' le_rfl)
    _ = ((lam⁻¹ : NNReal) : ENNReal) * (volume (V j).shade * volume (V i).carrier) := by
        rw [hcoe]

/-! ### The dense-shading refinement: the below-average discard, and nothing else -/

omit [Nontrivial E] in
/-- Half the shaded mass survives the below-average discard at level `1/2`. -/
theorem sum_shade_le_two_mul_discardLowShading (s : Finset ι) (V : ι → ShadedBody E) :
    (∑ i ∈ s, volume (V i).shade)
      ≤ 2 * ∑ i ∈ ShadedBody.discardLowShading s V (1 / 2), volume (V i).shade := by
  classical
  have h := ShadedBody.one_sub_mul_sum_volume_shade_le_sum_discardLowShading s V
    (c := (1 / 2 : NNReal)) (by norm_num)
  have hsub2 : (1 - (1 / 2 : NNReal)) = (1 / 2 : NNReal) := by
    rw [← NNReal.coe_inj, NNReal.coe_sub (by norm_num : (1 / 2 : NNReal) ≤ 1)]
    norm_num
  rw [hsub2] at h
  have hcoe : ((1 / 2 : NNReal) : ENNReal) = (2 : ENNReal)⁻¹ := by
    rw [show ((1 / 2 : NNReal) : ENNReal) = ((1 : NNReal) : ENNReal) / ((2 : NNReal) : ENNReal)
      from ENNReal.coe_div (by norm_num)]
    simp
  rw [hcoe] at h
  calc (∑ i ∈ s, volume (V i).shade)
      = 2 * ((2 : ENNReal)⁻¹ * ∑ i ∈ s, volume (V i).shade) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ 2 * ∑ i ∈ ShadedBody.discardLowShading s V (1 / 2), volume (V i).shade :=
        mul_le_mul' le_rfl h

omit [Nontrivial E] in
/-- **The dense-shading refinement.**  Every finite family of shaded bodies has a subfamily
retaining half of the shaded mass on which the shading is *pointwise* dense at `λ/2`, `λ` the
fullness of the whole family.

This is `ShadedBody.discardLowShading` at `c = 1/2`, packaged as the pointwise invariant.  It is
the cheap half of `Kakeya.ML2Shaded.exists_massBanded_shadeRefinement`: no dyadic pigeonhole, hence
no logarithm — the entire loss is the absolute factor `2`.  What it does *not* give is a two-sided
comparability at an absolute constant; see
`Kakeya.ML2Shaded.HasDenseShading.hasComparableDensities`, whose constant is `2/λ`. -/
theorem exists_denseShading_refinement (s : Finset ι) (V : ι → ShadedBody E) :
    ∃ s' ⊆ s,
      (∑ i ∈ s, volume (V i).shade) ≤ 2 * ∑ i ∈ s', volume (V i).shade ∧
        HasDenseShading (ShadedBody.fullness s V / 2) s' V := by
  classical
  refine ⟨ShadedBody.discardLowShading s V (1 / 2),
    ShadedBody.discardLowShading_subset s V _, sum_shade_le_two_mul_discardLowShading s V, ?_⟩
  intro i hi
  have hlow := ShadedBody.le_volume_shade_of_mem_discardLowShading (hi := hi)
  have hcoe_half : ((ShadedBody.fullness s V / 2 : NNReal) : ENNReal)
      = ((1 / 2 : NNReal) : ENNReal) * ((ShadedBody.fullness s V : NNReal) : ENNReal) := by
    rw [show ((ShadedBody.fullness s V / 2 : NNReal) : ENNReal)
        = ((ShadedBody.fullness s V : NNReal) : ENNReal) / ((2 : NNReal) : ENNReal)
      from ENNReal.coe_div (by norm_num),
      show ((1 / 2 : NNReal) : ENNReal) = ((1 : NNReal) : ENNReal) / ((2 : NNReal) : ENNReal)
      from ENNReal.coe_div (by norm_num)]
    simp [ENNReal.div_eq_inv_mul]
  rw [hcoe_half]
  exact hlow

/-- **A cardinality share is a mass share, given a pointwise density lower bound.**

The converse of `Kakeya.ML2Shaded.card_le_of_sum_shade_le`, and the direction the Section-9
reduction performs (as `exists_massShare_of_comparableDensities`) from *two-sided* comparability.
The one-sided `Kakeya.ML2Shaded.HasDenseShading` suffices, and the resulting constant is
`(L · C_n)/(lam · c_n)` with `c_n ≤ |T|/δ^{n-1} ≤ C_n` the two dimensional tube-volume constants —
no fullness of the parent family and no comparability constant enters, and `0 < δ` is not needed
(the bound is one-sided).

This is what makes the subfamily returned by the dividing-scales dichotomy a
`ShadedBody.IsCRefinement` of the original family, via
`ShadedBody.isCRefinement_of_isRefinement_of_sum_le`; both places where the reduction consumes an
input comparability go through exactly this inequality. -/
theorem sum_shade_le_of_card_le {δ : NNReal} (hδ1 : δ ≤ 1)
    {lam : NNReal} {s s' : Finset ι} {V : ι → ShadedTube δ E}
    (hdense : HasDenseShading lam s' (fun i => (V i).toShadedBody))
    {L : ENNReal} (hcard : (s.card : ENNReal) ≤ L * (s'.card : ENNReal)) :
    (lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
        * (∑ i ∈ s, volume (V i).shade)
      ≤ L * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
        * ∑ i ∈ s', volume (V i).shade := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set p : ENNReal := (δ : ENNReal) ^ (n - 1) with hp
  -- the shaded mass of the whole family, from above
  have hup : (∑ i ∈ s, volume (V i).shade)
      ≤ (s.card : ENNReal) * ((Tube.volume_le.C n : ENNReal) * p) := by
    have := Finset.sum_le_card_nsmul s (fun i => volume (V i).shade)
      ((Tube.volume_le.C n : ENNReal) * p) (fun i _ => by
        refine le_trans (measure_mono ((V i).toShadedBody).shade_subset) ?_
        simpa [hn, hp] using Tube.volume_le (E := E) hδ1 (V i).toTube)
    simpa [nsmul_eq_mul] using this
  -- the shaded mass of the subfamily, from below, pointwise
  have hlow : (lam : ENNReal) * ((Tube.le_volume.c n : ENNReal) * p) * (s'.card : ENNReal)
      ≤ ∑ i ∈ s', volume (V i).shade := by
    have hpt : ∀ i ∈ s', (lam : ENNReal) * ((Tube.le_volume.c n : ENNReal) * p)
        ≤ volume (V i).shade := by
      intro i hi
      refine le_trans (mul_le_mul' (le_refl (lam : ENNReal)) ?_) (hdense i hi)
      simpa [hn, hp] using Tube.le_volume (E := E) (V i).toTube
    have := Finset.card_nsmul_le_sum s' (fun i => volume (V i).shade)
      ((lam : ENNReal) * ((Tube.le_volume.c n : ENNReal) * p)) hpt
    simpa [nsmul_eq_mul, mul_comm] using this
  calc (lam : ENNReal) * (Tube.le_volume.c n : ENNReal) * (∑ i ∈ s, volume (V i).shade)
      ≤ (lam : ENNReal) * (Tube.le_volume.c n : ENNReal)
          * ((s.card : ENNReal) * ((Tube.volume_le.C n : ENNReal) * p)) :=
        mul_le_mul' le_rfl hup
    _ ≤ (lam : ENNReal) * (Tube.le_volume.c n : ENNReal)
          * ((L * (s'.card : ENNReal)) * ((Tube.volume_le.C n : ENNReal) * p)) :=
        mul_le_mul' le_rfl (mul_le_mul' hcard le_rfl)
    _ = L * (Tube.volume_le.C n : ENNReal)
          * ((lam : ENNReal) * ((Tube.le_volume.c n : ENNReal) * p) * (s'.card : ENNReal)) := by
        ring
    _ ≤ L * (Tube.volume_le.C n : ENNReal) * ∑ i ∈ s', volume (V i).shade :=
        mul_le_mul' le_rfl hlow

/-! ### Guardrails for the dense form -/

omit [Nontrivial E] in
/-- **A dense shading at a positive level forbids an unshaded index.**  So
`Kakeya.ML2Shaded.exists_denseShading_refinement`, like the mass banding, is not satisfiable by
`s' = s` in general: the discard is doing real work. -/
theorem shade_ne_zero_of_hasDenseShading {lam : NNReal} (hlam : 0 < lam) {u : Finset ι}
    {V : ι → ShadedBody E} (hcar0 : ∀ i, volume (V i).carrier ≠ 0)
    (h : HasDenseShading lam u V) {i : ι} (hi : i ∈ u) : volume (V i).shade ≠ 0 := by
  intro hzero
  have hle := h i hi
  rw [hzero, nonpos_iff_eq_zero] at hle
  rcases mul_eq_zero.mp hle with h1 | h2
  · exact absurd h1 (by simpa using hlam.ne')
  · exact hcar0 i h2

omit [Nontrivial E] in
/-- **The retained family is nonempty whenever there is mass to retain** — the dense analogue of
`Kakeya.ML2Shaded.nonempty_of_massBand`. -/
theorem nonempty_of_denseShading_mass {s s' : Finset ι} {V : ι → ShadedBody E}
    (hpos : 0 < ∑ i ∈ s, volume (V i).shade)
    (hmass : (∑ i ∈ s, volume (V i).shade) ≤ 2 * ∑ i ∈ s', volume (V i).shade) :
    s'.Nonempty := by
  rcases Finset.eq_empty_or_nonempty s' with rfl | h
  · simp only [Finset.sum_empty, mul_zero] at hmass
    exact absurd (le_antisymm hmass zero_le) hpos.ne'
  · exact h

omit [Nontrivial E] in
/-- **The fullness clause is not satisfiable by an empty subfamily.**  `fullness' ∅ = 0`, so any
conclusion of the form `lam ≤ L · λ(u, Y)` with `lam > 0` forces `u` to be nonempty. -/
theorem nonempty_of_le_mul_fullness' {lam : NNReal} (hlam : 0 < lam) {L : ENNReal}
    {u : Finset ι} {V : ι → ShadedBody E}
    (h : (lam : ENNReal) ≤ L * ShadedBody.fullness' u V) : u.Nonempty := by
  rcases Finset.eq_empty_or_nonempty u with rfl | hne
  · rw [show ShadedBody.fullness' (∅ : Finset ι) V = 0 by simp [ShadedBody.fullness'],
      mul_zero, nonpos_iff_eq_zero] at h
    exact absurd h (by simpa using hlam.ne')
  · exact hne

omit [Nontrivial E] in
/-- **A fully shaded family is densely shaded at `1`.**  The dense hypothesis is therefore not
vacuous, and it is satisfiable at the top constant on a nonempty family. -/
theorem hasDenseShading_one_of_shade_eq_carrier {u : Finset ι} {V : ι → ShadedBody E}
    (h : ∀ i ∈ u, (V i).shade = (V i).carrier) : HasDenseShading 1 u V := by
  intro i hi
  rw [h i hi]
  simp

omit [Nontrivial E] in
theorem nonempty_of_card_le_mul {s s' : Finset ι} {L : ENNReal} (hs : s.Nonempty)
    (h : (s.card : ENNReal) ≤ L * (s'.card : ENNReal)) : s'.Nonempty := by
  rcases Finset.eq_empty_or_nonempty s' with rfl | h'
  · rw [Finset.card_empty, Nat.cast_zero, mul_zero, nonpos_iff_eq_zero, Nat.cast_eq_zero,
      Finset.card_eq_zero] at h
    exact absurd h (Finset.nonempty_iff_ne_empty.mp hs)
  · exact h'


omit [Nontrivial E] in
/-- A family carrying some shaded mass has positive fullness.  (Extracted so that the concrete
guardrails below can name the level `λ/2` of `Kakeya.ML2Shaded.exists_denseShading_refinement`
without recomputing it.) -/
theorem fullness_pos_of_sum_shade_ne_zero {u : Finset ι} {V : ι → ShadedBody E}
    (hS : (∑ i ∈ u, volume (V i).shade) ≠ 0)
    (hD : (∑ i ∈ u, volume (V i).carrier) ≠ ⊤) :
    0 < ShadedBody.fullness u V := by
  have hne : ShadedBody.fullness' u V ≠ 0 := by
    rw [ShadedBody.fullness']
    exact ENNReal.div_ne_zero.mpr ⟨hS, hD⟩
  refine pos_iff_ne_zero.mpr (fun h => hne ?_)
  have := ShadedBody.coe_fullness u V
  rw [h] at this
  simpa using this.symm

omit [Nontrivial E] in
/-- **The fullness clause of `Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao_dense` is a
genuine constraint on the loss.**  Since `λ' ≤ 1` always, `lam ≤ L · λ'` implies `lam ≤ L`; the
clause is therefore not satisfiable by an arbitrarily small `L`, and in particular is not the
vacuous `lam ≤ ⊤`-style bound that an unconstrained loss would give. -/
theorem le_of_le_mul_fullness' {lam : NNReal} {L : ENNReal} {u : Finset ι} {V : ι → ShadedBody E}
    (h : (lam : ENNReal) ≤ L * ShadedBody.fullness' u V) : (lam : ENNReal) ≤ L :=
  h.trans (by simpa using mul_le_mul' (le_refl L) (ShadedBody.fullness'_le_one u V))

/-- **The dense hypothesis is satisfiable on a nonempty family of genuine `δ`-tubes**, at the top
level `1`: a single fully shaded `δ`-tube.  So
`Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao_dense` is not vacuous through its two new
hypotheses `s.Nonempty` and `HasDenseShading lam s Y` — they hold simultaneously, with `lam = 1`,
on an actual tube. -/
theorem exists_denseShading_tubeFamily {δ : NNReal} :
    ∃ V : Fin 1 → ShadedTube δ E,
      (Finset.univ : Finset (Fin 1)).Nonempty ∧
      (∀ i, (V i).shade = (V i).carrier) ∧
      HasDenseShading 1 (Finset.univ : Finset (Fin 1)) (fun i => (V i).toShadedBody) := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hvne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  set u : E := ‖v‖⁻¹ • v with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
    exact inv_mul_cancel₀ hvne
  set T : Tube δ E := Tube.ofMidpointDirection δ 0 u hu with hT_def
  have hTmeas : MeasurableSet T.carrier := T.isCompact'.isClosed.measurableSet
  refine ⟨fun _ =>
    { toTube := T
      shade := T.carrier
      measurableSet_shade := hTmeas
      shade_subset := subset_rfl }, ⟨0, Finset.mem_univ 0⟩, fun i => rfl, ?_⟩
  exact hasDenseShading_one_of_shade_eq_carrier (fun i _ => rfl)

omit [Nontrivial E] in
/-- **The dense hypothesis is independent of the rest of the dichotomy's hypotheses.**

Every other hypothesis of `Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao_dense` — ball
containment, essential distinctness, the `UniformTubeSet`, the `Kakeya.maxDensity` bound — mentions
the family only through `(V i).toTube`.  So any witness of those hypotheses can be re-shaded fully,
keeping the *same* tubes and hence the same witnesses, and the re-shaded family satisfies
`HasDenseShading 1` on the nose.

Consequently the three hypotheses added by the dense form (`s.Nonempty`, `0 < lam`,
`HasDenseShading lam s Y`) cannot make the hypothesis set contradictory: they are satisfiable
simultaneously with every instance of the unshaded hypotheses, at `lam = 1`.  This is the
non-vacuity check for the dense corollary. -/
theorem exists_fullShading_of_tubes {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) :
    ∃ V : ι → ShadedTube δ E,
      (∀ i, (V i).toTube = T i) ∧
      (∀ i, (V i).shade = (V i).carrier) ∧
      HasDenseShading 1 s (fun i => (V i).toShadedBody) := by
  refine ⟨fun i =>
    { toTube := T i
      shade := (T i).carrier
      measurableSet_shade := (T i).isCompact'.isClosed.measurableSet
      shade_subset := subset_rfl }, fun i => rfl, fun i => rfl, ?_⟩
  exact hasDenseShading_one_of_shade_eq_carrier (fun i _ => rfl)

/-- **A concrete family of shaded `δ`-tubes on which the dense-shading refinement is forced to
discard.**  Two copies of one `δ`-tube, the first fully shaded and the second not shaded at all.
Every subfamily satisfying *both* clauses of `Kakeya.ML2Shaded.exists_denseShading_refinement` is
exactly `{0}`: the mass clause rules out `∅` and `{1}`, and the density clause — at the positive
level `λ/2` the refinement actually produces — rules out `{0, 1}`.

So the dense refinement, like the mass banding, is not satisfiable by `s' = s`, nor by the empty
subfamily; the discard it performs is doing real work. -/
theorem denseShading_forced_on_concrete_family {δ : NNReal} (hδ : 0 < δ) :
    ∃ V : Fin 2 → ShadedTube δ E,
      0 < ShadedBody.fullness (Finset.univ : Finset (Fin 2)) (fun i => (V i).toShadedBody) ∧
      ∀ s' ⊆ (Finset.univ : Finset (Fin 2)),
        (∑ i ∈ (Finset.univ : Finset (Fin 2)), volume (V i).shade)
            ≤ 2 * ∑ i ∈ s', volume (V i).shade →
          HasDenseShading
              (ShadedBody.fullness (Finset.univ : Finset (Fin 2))
                (fun i => (V i).toShadedBody) / 2) s' (fun i => (V i).toShadedBody) →
          s' = {0} := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hvne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  set u : E := ‖v‖⁻¹ • v with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
    exact inv_mul_cancel₀ hvne
  set T : Tube δ E := Tube.ofMidpointDirection δ 0 u hu with hT_def
  have hTmeas : MeasurableSet T.carrier := T.isCompact'.isClosed.measurableSet
  set Vfull : ShadedTube δ E :=
    { toTube := T
      shade := T.carrier
      measurableSet_shade := hTmeas
      shade_subset := subset_rfl } with hVfull
  set Vempty : ShadedTube δ E :=
    { toTube := T
      shade := ∅
      measurableSet_shade := MeasurableSet.empty
      shade_subset := Set.empty_subset _ } with hVempty
  set V : Fin 2 → ShadedTube δ E := fun i => if i = 0 then Vfull else Vempty with hV
  have hTpos : volume T.carrier ≠ 0 := volume_carrier_ne_zero hδ T
  have hTtop : volume T.carrier ≠ ⊤ := volume_carrier_ne_top T
  have hshade0 : volume (V 0).shade = volume T.carrier := by simp [hV, hVfull]
  have hshade1 : volume (V 1).shade = 0 := by simp [hV, hVempty]
  have hcar : ∀ i : Fin 2, volume ((V i).toShadedBody).carrier = volume T.carrier := by
    intro i; fin_cases i <;> simp [hV, hVfull, hVempty]
  have htot : ∑ i ∈ (Finset.univ : Finset (Fin 2)), volume (V i).shade = volume T.carrier := by
    rw [Fin.sum_univ_two, hshade0, hshade1, add_zero]
  have hlampos : 0 < ShadedBody.fullness (Finset.univ : Finset (Fin 2))
      (fun i => (V i).toShadedBody) := by
    refine fullness_pos_of_sum_shade_ne_zero (by rw [htot]; exact hTpos) ?_
    rw [Fin.sum_univ_two, hcar 0, hcar 1]
    exact ENNReal.add_ne_top.mpr ⟨hTtop, hTtop⟩
  refine ⟨V, hlampos, ?_⟩
  intro s' _ hmass hdense
  have hhalfpos : 0 < ShadedBody.fullness (Finset.univ : Finset (Fin 2))
      (fun i => (V i).toShadedBody) / 2 := by positivity
  have h1notmem : (1 : Fin 2) ∉ s' := by
    intro h1
    exact shade_ne_zero_of_hasDenseShading hhalfpos
      (fun k => by rw [hcar k]; exact hTpos) hdense h1 hshade1
  have h0mem : (0 : Fin 2) ∈ s' := by
    by_contra h0
    have hsum' : ∑ i ∈ s', volume (V i).shade = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      fin_cases i
      · exact absurd hi h0
      · exact absurd hi h1notmem
    rw [hsum', mul_zero, htot] at hmass
    exact hTpos (le_antisymm hmass zero_le)
  ext i
  fin_cases i <;> simp [h0mem, h1notmem]

omit [Nontrivial E] in
/-- **The mass loss, read on the fullness** — the converse of
`Kakeya.ML2Shaded.sum_shade_le_of_fullness_le`.  A sub-shading on the same tubes leaves the
denominators alone, so the two forms are interchangeable. -/
theorem fullness_le_of_sum_shade_le {δ : NNReal} {u : Finset ι} {V V' : ι → ShadedTube δ E}
    (htube : ∀ i, (V' i).toTube = (V i).toTube) {L : ENNReal}
    (hmass : (∑ i ∈ u, volume (V i).shade) ≤ L * ∑ i ∈ u, volume (V' i).shade) :
    ShadedBody.fullness' u (fun i => (V i).toShadedBody)
      ≤ L * ShadedBody.fullness' u (fun i => (V' i).toShadedBody) := by
  classical
  have hDeq : (∑ i ∈ u, volume ((V' i).toShadedBody).carrier)
      = ∑ i ∈ u, volume ((V i).toShadedBody).carrier := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    calc ((V' i).toShadedBody).carrier = (V' i).toTube.carrier := rfl
      _ = (V i).toTube.carrier := by rw [htube i]
      _ = ((V i).toShadedBody).carrier := rfl
  have hgoal : (∑ i ∈ u, volume (V i).shade) / (∑ i ∈ u, volume ((V i).toShadedBody).carrier)
      ≤ (L * ∑ i ∈ u, volume (V' i).shade)
        / (∑ i ∈ u, volume ((V i).toShadedBody).carrier) :=
    ENNReal.div_le_div_right hmass _
  calc ShadedBody.fullness' u (fun i => (V i).toShadedBody)
      = (∑ i ∈ u, volume (V i).shade)
        / (∑ i ∈ u, volume ((V i).toShadedBody).carrier) := rfl
    _ ≤ (L * ∑ i ∈ u, volume (V' i).shade)
        / (∑ i ∈ u, volume ((V i).toShadedBody).carrier) := hgoal
    _ = L * ShadedBody.fullness' u (fun i => (V' i).toShadedBody) := by
        rw [ShadedBody.fullness', hDeq, mul_div_assoc]
/-! ### The shaded dividing-scales dichotomy -/

open scoped Classical in
/-- **GWZ Lemma 7.7(B), in shaded form** — assembled from the proved unshaded
`StickyKakeya.dividingScalesKatzTao`, the shaded uniformization
`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet`, and the mass banding
`Kakeya.ML2Shaded.exists_massBanded_shadeRefinement`.

The input is the *unshaded* hierarchy `𝒰` on the underlying tubes, which is weaker than the donor's
`ShadedUniformTubeSet` input (a caller holding one passes its `tubeUniform` field).

The output carries, on the retained index set `s'`:

* a sub-shading `Y' ⊆ Y` on the *same* tubes;
* the cardinality loss `#s ≤ totalLoss · #s'`, verbatim from the unshaded dichotomy;
* the **mass loss** `∑_{s'} |Y_i| ≤ (log₂ #s + 1)^{2M+2} · ∑_{s'} |Y'_i|`, the shaded-uniformization
  loss read on the masses rather than on `ShadedBody.fullness'` (the carriers being unchanged, the
  two say the same thing, and the mass form is what
  `ShadedBody.isCRefinement_of_isRefinement_of_sum_le` consumes);
* a `ShadedUniformTubeSet` on `(s', Y')` **carrying the very cover the dichotomy produced**, so that
  both alternatives are transcribed with no transport and no reproof; and
* a further mass-banded subfamily `s'' ⊆ s'` on which the shading densities of `Y'` are comparable
  at the absolute constant `2`, at the cost of `Kakeya.ML2Shaded.massBandLoss` of the shaded mass.

**The comparability is on `s''` and not on `s'`, and that is not a slip.**  It cannot be on `s'`:
`Kakeya.ML2Shaded.HasComparableDensities` is pointwise and two-sided, whereas the only thing the
shaded uniformization returns about `Y'` is the aggregate mass loss, and
`Kakeya.ML2Shaded.not_hasComparableDensities_of_aggregate_retention` exhibits a sub-shading with a
*better* aggregate retention than any loss charged here and with densities comparable at no constant
at all.  Nor can `s''` be promoted back into a `ShadedUniformTubeSet`: passing to a subfamily
destroys `Tube.UniformTubeSet.le_card_class` at every node whose class is emptied, and repairing it
by shrinking `GridCoverSystem.indexSet` to the nodes still hit shrinks
`Tube.UniformTubeSet.nodesUnder`, under which the *lower* bound of the third window bullet does not
survive (the first two bullets and alternative (i), being upper bounds, do).  Closing that gap needs
the shaded uniformization to be interleaved with the stopping time, which is a different proof, not
a different composition of these three. -/
theorem exists_shaded_dividingScalesKatzTao (hn : Module.finrank ℝ E = 3)
    (N : ℕ) (hN : 4096 ≤ N) {ε : ℝ} (hε : ε = 1 / Real.sqrt (N : ℝ)) (Cu : NNReal) :
    ∃ (C δ₀ : NNReal) (K c : ℕ), 1 ≤ C ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (η : ℕ → ℝ), 0 ≤ η 0 → (∀ k < N, η k ≤ ε * η (k + 1)) → η N ≤ ε →
      ∀ (s : Finset ι) (V : ι → ShadedTube δ E),
      (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (s : Set ι).Pairwise (fun i j ↦ IsEssentiallyDistinct ((V i).carrier) ((V j).carrier)) →
      UniformTubeSet s (fun i => (V i).toTube) (ssfGridLen δ) Cu →
      Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody)
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η 0)) →
      ∃ s' ⊆ s, ∃ V' : ι → ShadedTube δ E,
        (∀ i, (V' i).toTube = (V i).toTube) ∧
        (∀ i, (V' i).shade ⊆ (V i).shade) ∧
        (s.card : ENNReal) ≤ StickyKakeya.totalLoss C K c δ * (s'.card : ENNReal) ∧
        (∑ i ∈ s', volume (V i).shade)
            ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
              * ∑ i ∈ s', volume (V' i).shade ∧
        (∃ s'' ⊆ s',
            (∑ i ∈ s', volume (V' i).shade)
              ≤ massBandLoss (ShadedBody.fullness s' (fun i => (V' i).toShadedBody))
                * ∑ i ∈ s'', volume (V' i).shade ∧
            HasComparableDensities 2 s'' (fun i => (V' i).toShadedBody)) ∧
        ∃ 𝒱' : ShadedUniformTubeSet s' V' (ssfGridLen δ) (max C 4),
          (𝒱'.tubeUniform.IsKatzTaoAtEveryScale
                ((C : ENNReal) * StickyKakeya.totalLoss C K c δ
                  * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε)))) ∨
            ∃ a b m : ℕ,
              m < N ∧ a < b ∧ b ≤ ssfGridLen δ ∧
              ((gridScale δ (ssfGridLen δ) b : ℝ)
                ≤ (δ : ℝ) ^ ε * (gridScale δ (ssfGridLen δ) a : ℝ)) ∧
              Kakeya.maxDensity (𝒱'.tubeUniform.cover.indexSet a)
                  (fun j => (𝒱'.tubeUniform.cover.tube a j).toConvexSpaceBody)
                ≤ (C : ENNReal) * StickyKakeya.totalLoss C K c δ *
                    ENNReal.ofReal ((gridScale δ (ssfGridLen δ) a : ℝ) ^ (-η m)) ∧
              (∀ j ∈ 𝒱'.tubeUniform.cover.indexSet a,
                Kakeya.maxDensity (𝒱'.tubeUniform.nodesUnder b a j)
                    (fun j' => (𝒱'.tubeUniform.cover.tube b j').toConvexSpaceBody)
                  ≤ (C : ENNReal) * StickyKakeya.totalLoss C K c δ *
                      ENNReal.ofReal
                        (((gridScale δ (ssfGridLen δ) a : ℝ)
                            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ η m)) ∧
              (∀ ρ : NNReal,
                (gridScale δ (ssfGridLen δ) b : ℝ)
                    * ((gridScale δ (ssfGridLen δ) a : ℝ)
                        / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ε ≤ (ρ : ℝ) →
                (ρ : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
                    * ((gridScale δ (ssfGridLen δ) b : ℝ)
                        / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ ε →
                ∀ j ∈ 𝒱'.tubeUniform.cover.indexSet a,
                  ENNReal.ofReal
                      (((gridScale δ (ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ η (m + 1))
                    ≤ (C : ENNReal) * StickyKakeya.totalLoss C K c δ *
                        Kakeya.maxDensity (𝒱'.tubeUniform.nodesUnder b a j)
                          (fun j' =>
                            ((𝒱'.tubeUniform.cover.tube b j').rescale ρ).toConvexSpaceBody)) ∧
              (∀ k : ℕ, a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ k →
                k + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b →
                ∀ j ∈ 𝒱'.tubeUniform.cover.indexSet a,
                  ENNReal.ofReal
                      (((gridScale δ (ssfGridLen δ) a : ℝ)
                          / (gridScale δ (ssfGridLen δ) k : ℝ)) ^ η (m + 1))
                    ≤ (C : ENNReal) * StickyKakeya.totalLoss C K c δ *
                        Kakeya.maxDensity (𝒱'.tubeUniform.nodesUnder k a j)
                          (fun j' => (𝒱'.tubeUniform.cover.tube k j').toConvexSpaceBody)) ∧
              (∃ Φ : ℕ → ℕ → ENNReal, ∀ p ≤ ssfGridLen δ, ∀ k ≤ ssfGridLen δ,
                ∀ j ∈ 𝒱'.tubeUniform.cover.indexSet p,
                Φ p k ≤ Kakeya.maxDensity
                    ((coverClass s' (𝒱'.tubeUniform.cover.assign p) j).image
                      (𝒱'.tubeUniform.cover.assign k))
                    (fun j' => (𝒱'.tubeUniform.cover.tube k j').toConvexSpaceBody) ∧
                  Kakeya.maxDensity
                      ((coverClass s' (𝒱'.tubeUniform.cover.assign p) j).image
                        (𝒱'.tubeUniform.cover.assign k))
                      (fun j' => (𝒱'.tubeUniform.cover.tube k j').toConvexSpaceBody)
                    ≤ (C : ENNReal) * StickyKakeya.totalLoss C K c δ * Φ p k)) := by
  classical
  obtain ⟨C, δ₀, K, c, hC, hδ₀pos, hδ₀le, hmain⟩ :=
    StickyKakeya.dividingScalesKatzTao.{u} (E := E) hn N hN hε Cu
  obtain ⟨d1, hd1pos, hd1le1, hd1⟩ :=
    MultiScaleFac.exists_threshold_ssfGridLen_hypotheses 0 (show (0 : ℝ) < 1 by norm_num)
  refine ⟨C, min δ₀ d1, K, c, hC, lt_min hδ₀pos hd1pos, (min_le_left _ _).trans hδ₀le, ?_⟩
  intro ι δ hδpos hδle η hη0 hηstep hηN s V hball hED hU hDens
  have hδδ₀ : δ ≤ δ₀ := hδle.trans (min_le_left _ _)
  have hδd1 : δ ≤ d1 := hδle.trans (min_le_right _ _)
  have hMpos : 0 < ssfGridLen δ :=
    lt_of_lt_of_le (by norm_num) (hd1 hδpos hδd1).1
  obtain ⟨s', hs's, hcard, 𝒰', halt⟩ :=
    hmain (ι := ι) (δ := δ) hδpos hδδ₀ η hη0 hηstep hηN s (fun i => (V i).toTube)
      hball hED hU hDens
  have hclamp : ∀ t ⊆ s', Nat.log 2 t.card ≤ Nat.log 2 s.card := by
    intro t ht
    exact Nat.log_mono_right (Finset.card_le_card (ht.trans hs's))
  obtain ⟨V', htube, hshade, hfull, 𝒱', hIdx, hAss, hTube, hBr⟩ :=
    ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet (V := V) (𝒰 := 𝒰') hMpos
      (Nat.log 2 s.card) hclamp
  obtain ⟨s'', hs''sub, hbandmass, hcomp⟩ := exists_massBanded_shadeRefinement hδpos s' V'
  refine ⟨s', hs's, V', htube, hshade, hcard,
    sum_shade_le_of_fullness_le hδpos htube hfull, ⟨s'', hs''sub, hbandmass, hcomp⟩, 𝒱', ?_⟩
  have hnodes : ∀ b a j, 𝒱'.tubeUniform.nodesUnder b a j = 𝒰'.nodesUnder b a j :=
    fun b a j => nodesUnder_congr 𝒱'.tubeUniform 𝒰' hIdx hTube b a j
  rcases halt with hKT | ⟨a, b, m, hm, hab, hb, hsep, h1, h2, h3, hlev, hband⟩
  · refine Or.inl ?_
    intro k hk
    have := hKT k hk
    rw [hIdx, hTube]
    exact this
  · refine Or.inr ⟨a, b, m, hm, hab, hb, hsep, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hIdx, hTube]; exact h1
    · intro j hj
      rw [hIdx] at hj
      rw [hnodes, hTube]
      exact h2 j hj
    · intro ρ hρlo hρhi j hj
      rw [hIdx] at hj
      rw [hnodes, hTube]
      exact h3 ρ hρlo hρhi j hj
    · intro k hk1 hk2 j hj
      rw [hIdx] at hj
      rw [hnodes, hTube]
      exact hlev k hk1 hk2 j hj
    · obtain ⟨Φ, hΦ⟩ := hband
      refine ⟨Φ, fun p hp k hk j hj => ?_⟩
      rw [hIdx] at hj
      rw [hAss, hTube]
      exact hΦ p hp k hk j hj

open scoped Classical in
/-- **GWZ Lemma 7.7(B) in shaded form, with the density invariant on the *same* index set as the
hierarchy** — the form the Section-9 reduction consumes.

The difference from `Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao` is the extra input
`HasDenseShading lam s Y`, a *pointwise* lower bound on the shading densities of the family the
dichotomy is applied to.  With it, three conclusions land on `s'` itself rather than on a further
subfamily:

* `s'.Nonempty`;
* `HasDenseShading lam s' Y` and hence `HasComparableDensities lam⁻¹ s' Y` — comparability of the
  densities of the *given* shading, at the constant `lam⁻¹` (which is `δ^{-η}` under the standing
  hypothesis `δ^η ≤ lam`, not an absolute constant); and
* `lam ≤ (log₂ #s + 1)^{2M+2} · λ(s', Y')` — the fullness of the *refined* shading on `s'`, which
  is the quantitative consequence the consumer actually wants comparability for.

The last clause is the point.  A consumer of 7.7(B) needs, for the next round of the reduction, a
lower bound on `λ(s', Y')` given one on `λ(s, Y)`; the dichotomy returns an arbitrary `s' ⊆ s`, so
an aggregate hypothesis on `s` cannot supply it and a pointwise one can.  This is the honest
statement of "the dichotomy preserves the fullness": it does, at the cost of the
shaded-uniformization polylogarithm, and provided the input fullness was pointwise to begin with.

The mass-banded subfamily `s''` of the unprimed version, with its **absolute** comparability
constant `2` for `Y'`, is retained unchanged; the two comparability clauses are genuinely different
statements — one about `Y` at a `δ`-power constant on all of `s'`, one about `Y'` at the constant
`2` on a further subfamily — and neither implies the other.  See
`Kakeya.ML2Shaded.not_hasComparableDensities_of_aggregate_retention` for why no clause of this
lemma can give absolute comparability of `Y'` on `s'` itself. -/
theorem exists_shaded_dividingScalesKatzTao_dense (hn : Module.finrank ℝ E = 3)
    (N : ℕ) (hN : 4096 ≤ N) {ε : ℝ} (hε : ε = 1 / Real.sqrt (N : ℝ)) (Cu : NNReal) :
    ∃ (C δ₀ : NNReal) (K c : ℕ), 1 ≤ C ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (η : ℕ → ℝ), 0 ≤ η 0 → (∀ k < N, η k ≤ ε * η (k + 1)) → η N ≤ ε →
      ∀ (s : Finset ι) (V : ι → ShadedTube δ E), s.Nonempty →
      (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (s : Set ι).Pairwise (fun i j ↦ IsEssentiallyDistinct ((V i).carrier) ((V j).carrier)) →
      UniformTubeSet s (fun i => (V i).toTube) (ssfGridLen δ) Cu →
      Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody)
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η 0)) →
      ∀ lam : NNReal, 0 < lam →
      HasDenseShading lam s (fun i => (V i).toShadedBody) →
      ∃ s' ⊆ s, ∃ V' : ι → ShadedTube δ E,
        s'.Nonempty ∧
        (∀ i, (V' i).toTube = (V i).toTube) ∧
        (∀ i, (V' i).shade ⊆ (V i).shade) ∧
        (s.card : ENNReal) ≤ StickyKakeya.totalLoss C K c δ * (s'.card : ENNReal) ∧
        (∑ i ∈ s', volume (V i).shade)
            ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
              * ∑ i ∈ s', volume (V' i).shade ∧
        HasDenseShading lam s' (fun i => (V i).toShadedBody) ∧
        HasComparableDensities lam⁻¹ s' (fun i => (V i).toShadedBody) ∧
        (lam : ENNReal)
            ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
              * ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) ∧
        (∃ s'' ⊆ s',
            (∑ i ∈ s', volume (V' i).shade)
              ≤ massBandLoss (ShadedBody.fullness s' (fun i => (V' i).toShadedBody))
                * ∑ i ∈ s'', volume (V' i).shade ∧
            HasComparableDensities 2 s'' (fun i => (V' i).toShadedBody)) ∧
        ∃ 𝒱' : ShadedUniformTubeSet s' V' (ssfGridLen δ) (max C 4),
          (𝒱'.tubeUniform.IsKatzTaoAtEveryScale
                ((C : ENNReal) * StickyKakeya.totalLoss C K c δ
                  * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε)))) ∨
            ∃ a b m : ℕ,
              m < N ∧ a < b ∧ b ≤ ssfGridLen δ ∧
              ((gridScale δ (ssfGridLen δ) b : ℝ)
                ≤ (δ : ℝ) ^ ε * (gridScale δ (ssfGridLen δ) a : ℝ)) ∧
              Kakeya.maxDensity (𝒱'.tubeUniform.cover.indexSet a)
                  (fun j => (𝒱'.tubeUniform.cover.tube a j).toConvexSpaceBody)
                ≤ (C : ENNReal) * StickyKakeya.totalLoss C K c δ *
                    ENNReal.ofReal ((gridScale δ (ssfGridLen δ) a : ℝ) ^ (-η m)) ∧
              (∀ j ∈ 𝒱'.tubeUniform.cover.indexSet a,
                Kakeya.maxDensity (𝒱'.tubeUniform.nodesUnder b a j)
                    (fun j' => (𝒱'.tubeUniform.cover.tube b j').toConvexSpaceBody)
                  ≤ (C : ENNReal) * StickyKakeya.totalLoss C K c δ *
                      ENNReal.ofReal
                        (((gridScale δ (ssfGridLen δ) a : ℝ)
                            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ η m)) ∧
              (∀ ρ : NNReal,
                (gridScale δ (ssfGridLen δ) b : ℝ)
                    * ((gridScale δ (ssfGridLen δ) a : ℝ)
                        / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ε ≤ (ρ : ℝ) →
                (ρ : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
                    * ((gridScale δ (ssfGridLen δ) b : ℝ)
                        / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ ε →
                ∀ j ∈ 𝒱'.tubeUniform.cover.indexSet a,
                  ENNReal.ofReal
                      (((gridScale δ (ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ η (m + 1))
                    ≤ (C : ENNReal) * StickyKakeya.totalLoss C K c δ *
                        Kakeya.maxDensity (𝒱'.tubeUniform.nodesUnder b a j)
                          (fun j' =>
                            ((𝒱'.tubeUniform.cover.tube b j').rescale ρ).toConvexSpaceBody)) ∧
              (∀ k : ℕ, a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ k →
                k + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b →
                ∀ j ∈ 𝒱'.tubeUniform.cover.indexSet a,
                  ENNReal.ofReal
                      (((gridScale δ (ssfGridLen δ) a : ℝ)
                          / (gridScale δ (ssfGridLen δ) k : ℝ)) ^ η (m + 1))
                    ≤ (C : ENNReal) * StickyKakeya.totalLoss C K c δ *
                        Kakeya.maxDensity (𝒱'.tubeUniform.nodesUnder k a j)
                          (fun j' => (𝒱'.tubeUniform.cover.tube k j').toConvexSpaceBody)) ∧
              (∃ Φ : ℕ → ℕ → ENNReal, ∀ p ≤ ssfGridLen δ, ∀ k ≤ ssfGridLen δ,
                ∀ j ∈ 𝒱'.tubeUniform.cover.indexSet p,
                Φ p k ≤ Kakeya.maxDensity
                    ((coverClass s' (𝒱'.tubeUniform.cover.assign p) j).image
                      (𝒱'.tubeUniform.cover.assign k))
                    (fun j' => (𝒱'.tubeUniform.cover.tube k j').toConvexSpaceBody) ∧
                  Kakeya.maxDensity
                      ((coverClass s' (𝒱'.tubeUniform.cover.assign p) j).image
                        (𝒱'.tubeUniform.cover.assign k))
                      (fun j' => (𝒱'.tubeUniform.cover.tube k j').toConvexSpaceBody)
                    ≤ (C : ENNReal) * StickyKakeya.totalLoss C K c δ * Φ p k)) := by
  classical
  obtain ⟨C, δ₀, K, c, hC, hδ₀pos, hδ₀le, hmain⟩ :=
    exists_shaded_dividingScalesKatzTao.{u} (E := E) hn N hN hε Cu
  refine ⟨C, δ₀, K, c, hC, hδ₀pos, hδ₀le, ?_⟩
  intro ι δ hδpos hδle η hη0 hηstep hηN s V hsne hball hED hU hDens lam hlam hdense
  obtain ⟨s', hs's, V', htube, hshade, hcard, hmass, hband, 𝒱', halt⟩ :=
    hmain (ι := ι) (δ := δ) hδpos hδle η hη0 hηstep hηN s V hball hED hU hDens
  have hs'ne : s'.Nonempty := nonempty_of_card_le_mul hsne hcard
  have hdense' : HasDenseShading lam s' (fun i => (V i).toShadedBody) := hdense.subset hs's
  have hfull : (lam : ENNReal)
      ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
        * ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) :=
    (hdense'.le_fullness_tube hδpos hs'ne).trans (fullness_le_of_sum_shade_le htube hmass)
  exact ⟨s', hs's, V', hs'ne, htube, hshade, hcard, hmass, hdense',
    hdense'.hasComparableDensities hlam, hfull, hband, 𝒱', halt⟩


end Kakeya.ML2Shaded
