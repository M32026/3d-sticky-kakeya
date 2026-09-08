/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.FlatPrisms
public import Kakeya.DimensionThree.BoundedOverlapCount
public import Kakeya.DimensionThree.MainLemma1.Factoring

/-!
# The occupied-parent count of GWZ Proposition 6.6(A) from bounded overlap

`Kakeya.flatPrismOccupiedParents_le` bounds the number of *occupied parent labels* of the
factorization by an absolute constant `Kakeya.edParentCount.C n D Ctest`, and it does so from
pairwise essential distinctness of the coarse family `(Vρ k)_{k ∈ t}`.  That hypothesis is not
available to Main Lemma 1, and is not the hypothesis GWZ uses:

* GWZ invoke essential distinctness in the proof of 6.6(A) exactly once, and at the **leaf**
  scale (`blueprint/src/GWZAdapted/section6_estimates.tex:340`), which the development already
  carries as the `essDistinct` field of `Kakeya.IsFlatPrismFamily`;
* the blueprint's erratum to GWZ Definition 2.1(ii) (`section2.tex:1093--1139`) *refutes* the
  parent-scale reading: an axial stack forces any essentially-distinct refinement of a parent
  cover to have cardinality `O(1)` where the family has `∼ δ ^ (-1/2)` members.  The clause is
  replaced there by **bounded overlap**, and essential distinctness is "required and supplied at
  the leaf scale `δ`, and never at the parent scale";
* concretely, `Kakeya.ml1Boot.flatPrism_dichotomy_decoupled` carries only
  `Kakeya.ml1Boot.IsParentFamily` (injective indexing, not distinctness), and
  `Kakeya/DimensionThree/MainLemma1/Rescaling/KatzTao.lean` instantiates the coarse family at a
  *single* fixed unit tube, where `Pairwise IsEssentiallyDistinct` is outright false as soon as
  the index set has two members.

What the coarse family of Main Lemma 1 does satisfy is `Tube.HasBoundedOverlap` at a constant
`Co`.  The theorem below is the occupied-parent count run off that hypothesis instead.

## What it costs

The bounded-overlap count `Kakeya.ml1Boot.card_occupiedLabels_le_of_boundedOverlapLabels` is
`Co · C · ρ ^ (-5)` and not a constant, and the `ρ`-power is unavoidable: bounded overlap does
not identify a `ρ`-tube with its axial slides, and an axial pencil of `∼ ρ ^ (-1)` parents at
`Co = 1` occupies a single test body (module docstring of
`Kakeya/DimensionThree/BoundedOverlapCount.lean`; the same pencil refutes the scale-free parent
refinement in `Kakeya.ml1Boot.not_exists_essDistinct_parentFamily`).

In *this* lemma the `ρ`-power costs nothing, and that is the whole point.  The hypotheses
`bSmall ≤ b ≤ D · ρ` with `0 < bSmall` force `1 ≤ Ctest · ρ` for `Ctest = max 1 (D / bSmall)` --
the coarse scale is bounded below by a *constant* in this branch, which is exactly why a single
rescaled unit tube can test every leaf.  Hence `ρ ^ (-5) ≤ Ctest ^ 5` and the conclusion is again
a constant depending only on `Co`, `D` and `bSmall`, in the same way that
`Kakeya.edParentCount.C n D Ctest` depends only on `n`, `D` and `bSmall`.  So this consumer of
the coarse-distinctness hypothesis is dischargeable from bounded overlap at no exponent cost and
with no extra scale hypothesis.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya

section FlatPrismsBoundedOverlap

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- **`Kakeya.flatPrismOccupiedParents_le` with bounded overlap in place of coarse essential
distinctness.**

Hypothesis-for-hypothesis this is `Kakeya.flatPrismOccupiedParents_le` with

    (hED : (r : Set κ).Pairwise fun k l ↦ IsEssentiallyDistinct (R k).carrier (R l).carrier)

deleted and

    (hoverlap : ∀ (W : Tube ρ E) (u : Finset κ), u ⊆ r →
      (∀ k ∈ u, ∃ i ∈ q, assign i = k ∧ (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody) →
      (u.card : NNReal) ≤ Co)

put in its place, at the cost of `Module.finrank ℝ E = 3` and `2 σ ≤ ρ`, and with the constant
`Kakeya.edParentCount.C (finrank ℝ E) D Ctest` replaced by
`Co · Kakeya.ml1Boot.parentCount.C · Ctest ^ 5`.  The parent tubes `R` and the assignment
containment `hassign` are not needed at all: the bounded-overlap count is purely leaf-side.

`hoverlap` is discharged from `Tube.HasBoundedOverlap` by
`Kakeya.ml1Boot.boundedOverlapLabels_of_hasBoundedOverlap`, whose only geometric input is the
`le_parent` field of `Kakeya.ml1Boot.IsParentFamily`.  `2 σ ≤ ρ` is free at the call site: `ρ` is
bounded below by the constant `Ctest ⁻¹` here, while `σ → 0`. -/
theorem flatPrismOccupiedParents_le_of_boundedOverlap
    {ι κ : Type*} [DecidableEq κ]
    {σ ρ D bSmall b Co : NNReal} (hdim : Module.finrank ℝ E = 3)
    (hσ0 : 0 < σ) (hσρ : 2 * σ ≤ ρ) (hρ1 : ρ ≤ 1)
    (hD : 1 ≤ D) (hbSmall0 : 0 < bSmall) (hbLarge : bSmall ≤ b)
    (hbρ : b ≤ D * ρ) (q : Finset ι) (T : ι → Tube σ E)
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1)
    (r : Finset κ) (assign : ι → κ)
    (hoverlap : ∀ (W : Tube ρ E) (u : Finset κ), u ⊆ r →
      (∀ k ∈ u, ∃ i ∈ q, assign i = k ∧ (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody) →
      ((u.card : NNReal)) ≤ Co) :
    let Ctest : NNReal := max 1 (D * bSmall⁻¹)
    let parents := r.filter fun k ↦ ∃ i ∈ q, assign i = k
    (parents.card : ENNReal) ≤
      (Co : ENNReal) * (ml1Boot.parentCount.C : ENNReal) * (Ctest : ENNReal) ^ 5 := by
  dsimp only
  set Ctest : NNReal := max 1 (D * bSmall⁻¹) with hCtestDef
  have hCtest : 1 ≤ Ctest := le_max_left _ _
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hσρ
  have hscale : 1 ≤ Ctest * ρ := by
    have hbDρ : bSmall ≤ D * ρ := hbLarge.trans hbρ
    calc
      1 = bSmall⁻¹ * bSmall := (inv_mul_cancel₀ hbSmall0.ne').symm
      _ ≤ bSmall⁻¹ * (D * ρ) := by gcongr
      _ = (D * bSmall⁻¹) * ρ := by ring
      _ ≤ Ctest * ρ := by gcongr; exact le_max_right _ _
  have hcount :=
    ml1Boot.card_occupiedLabels_le_of_boundedOverlapLabels (E := E) hdim hσ0 hρ1 hσρ hball
      hoverlap
  refine hcount.trans ?_
  have hinv : (ρ : ENNReal)⁻¹ ≤ (Ctest : ENNReal) := by
    have h1 : (1 : ENNReal) ≤ (Ctest : ENNReal) * (ρ : ENNReal) := by
      have := hscale
      rw [← ENNReal.coe_le_coe] at this
      simpa using this
    have hρne : (ρ : ENNReal) ≠ 0 := by
      simpa using (ne_of_gt hρ0)
    calc
      (ρ : ENNReal)⁻¹ = (ρ : ENNReal)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (ρ : ENNReal)⁻¹ * ((Ctest : ENNReal) * (ρ : ENNReal)) := by gcongr
      _ = (Ctest : ENNReal) * ((ρ : ENNReal)⁻¹ * (ρ : ENNReal)) := by ring
      _ = (Ctest : ENNReal) * 1 := by
            rw [ENNReal.inv_mul_cancel hρne ENNReal.coe_ne_top]
      _ = (Ctest : ENNReal) := mul_one _
  have hpow : (ρ : ENNReal) ^ (-5 : ℝ) ≤ (Ctest : ENNReal) ^ 5 := by
    rw [ml1Boot.coe_rpow_neg_five]
    exact pow_le_pow_left' hinv 5
  gcongr

/-- **`Kakeya.edParentCount.card_assignedParents_le` and
`Kakeya.edParentCount.card_assignedParents_le_homotheticDilatedThickenedPlank` with bounded
overlap in place of coarse essential distinctness.**

The test body is arbitrary, since the bounded-overlap count does not use its shape: it dominates
the count of *all* occupied labels.  This is the drop-in replacement at the outer plank
nonconcentration step of GWZ Proposition 6.6(A) (`Kakeya.multiplicity_le_of_factorsThroughFlatPrisms_of_parentPresentation`,
the `hOuterNC` step), where the absolute constant `Kakeya.edParentCount.COfTestDilate 3 D 1 L` is
replaced by `Co · Kakeya.ml1Boot.parentCount.C · ρ ^ (-5)`.

Unlike `Kakeya.flatPrismOccupiedParents_le_of_boundedOverlap`, that step runs at an arbitrary
`σ ≤ ρ ≤ 1`, so the `ρ`-power here is a genuine loss; see
`Kakeya.not_occupiedParents_le_const_of_boundedOverlap` below. -/
theorem card_assignedParents_le_of_boundedOverlap
    {ι κ : Type*} [DecidableEq κ] {σ ρ Co : NNReal} (hdim : Module.finrank ℝ E = 3)
    (hσ0 : 0 < σ) (hσρ : 2 * σ ≤ ρ) (hρ1 : ρ ≤ 1)
    (q : Finset ι) (T : ι → Tube σ E)
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1)
    (r : Finset κ) (assign : ι → κ)
    (hoverlap : ∀ (W : Tube ρ E) (u : Finset κ), u ⊆ r →
      (∀ k ∈ u, ∃ i ∈ q, assign i = k ∧ (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody) →
      ((u.card : NNReal)) ≤ Co)
    (Q : ConvexSpaceBody E) :
    (((r.filter fun k ↦ ∃ i ∈ q, assign i = k ∧ (T i).toConvexSpaceBody ≤ Q).card : ENNReal))
      ≤ (Co : ENNReal) * (ml1Boot.parentCount.C : ENNReal) * (ρ : ENNReal) ^ (-5 : ℝ) := by
  classical
  refine le_trans ?_
    (ml1Boot.card_occupiedLabels_le_of_boundedOverlapLabels (E := E) (q := q) (r := r)
      (assign := assign) hdim hσ0 hρ1 hσρ hball hoverlap)
  refine Nat.cast_le.mpr (Finset.card_le_card ?_)
  intro k hk
  rcases Finset.mem_filter.mp hk with ⟨hkr, i, hiq, hik, -⟩
  exact Finset.mem_filter.mpr ⟨hkr, i, hiq, hik⟩

/-- **The scale hypothesis converts the `ρ`-power into an `σ`-power.**

If `σ ^ ηρ ≤ ρ` then `ρ ^ (-5) ≤ σ ^ (-5 ηρ)`.  This is the arithmetic that a bounded-overlap
form of GWZ Proposition 6.6(A) needs in order to charge the parent count against the loss budget
`σ ^ (-ε')`: the ledger of
`Kakeya.multiplicity_le_of_factorsThroughFlatPrisms_of_parentPresentation` absorbs its parent
constants through `ShadedBody.eventually_const_le_coe_rpow_neg`, which applies only to a
`σ`-independent constant.  With the hypothesis in force the two consumers become
`σ ^ (-5 ηρ)` and a constant, and `5 ηρ` is what has to fit inside the per-constant budget
`eFund ≤ ε' / 512`. -/
theorem rpow_neg_five_le_of_scale {σ ρ : NNReal} {ηo : ℝ}
    (hscale : (σ : ENNReal) ^ ηo ≤ (ρ : ENNReal)) :
    (ρ : ENNReal) ^ (-5 : ℝ) ≤ (σ : ENNReal) ^ (-(5 * ηo)) := by
  have h1 : (ρ : ENNReal)⁻¹ ≤ ((σ : ENNReal) ^ ηo)⁻¹ := ENNReal.inv_le_inv.mpr hscale
  have h3 : ((σ : ENNReal) ^ ηo)⁻¹ = (σ : ENNReal) ^ (-ηo) := (ENNReal.rpow_neg _ _).symm
  rw [h3] at h1
  rw [ml1Boot.coe_rpow_neg_five]
  calc
    ((ρ : ENNReal)⁻¹) ^ 5 ≤ ((σ : ENNReal) ^ (-ηo)) ^ 5 := pow_le_pow_left' h1 5
    _ = (σ : ENNReal) ^ (-(5 * ηo)) := by
        rw [← ENNReal.rpow_natCast ((σ : ENNReal) ^ (-ηo)) 5, ← ENNReal.rpow_mul]
        norm_num
        ring_nf

/-! ### The `ρ`-power is not removable

The count above is a constant only because `1 ≤ Ctest · ρ` holds in that branch.  The *other*
consumer of coarse essential distinctness inside GWZ Proposition 6.6(A) --
`Kakeya.edParentCount.card_assignedParents_le_homotheticDilatedThickenedPlank`, used at the outer
plank nonconcentration step -- runs at an arbitrary `σ ≤ ρ ≤ 1`, and there no constant bound is
available from bounded overlap at all.  The theorem below proves that: it refutes the
bounded-overlap analogue of `Kakeya.edParentCount.card_assignedParents_le` with a constant
conclusion, at the sharpest admissible overlap constant `Co = 1`, for *every* constant `C`.

The witness is the axial pencil `Kakeya.ml1Boot.essDistinctCex.leaf` already in the development:
`M = 2 ^ (2 n + 1)` leaves at `σ = 2 ^ (-8 n)` under `M` parents at `ρ = 2 ^ (-(2 n + 9))`, every
parent occupied, all leaves in `B₁`, `Tube.HasBoundedOverlap` at `1`
(`Kakeya.ml1Boot.essDistinctCex.hasBoundedOverlap`) and `Kakeya.ml1Boot.IsParentFamily`
(`Kakeya.ml1Boot.essDistinctCex.isParentFamily`).  Since `M = ρ ⁻¹ / 2 ^ 8`, the occupied-parent
count is `≍ ρ ^ (-1)` here, so the honest bounded-overlap replacement of that step degrades by a
factor `≍ ρ ^ (-1)` -- and `ρ ^ (-5)`, the bound
`Kakeya.ml1Boot.card_occupiedLabels_le_of_boundedOverlapLabels` actually proves, is an
overestimate of a real loss, not an artefact of the covering argument.

This is the obstruction to running the whole of GWZ Proposition 6.6(A) on bounded overlap without
a scale hypothesis relating `ρ` to `σ`: the loss ledger of
`Kakeya.multiplicity_le_of_factorsThroughFlatPrisms_of_parentPresentation` charges its parent
constants against `σ ^ (-eFund)` through
`ShadedBody.eventually_const_le_coe_rpow_neg`, which requires a `σ`- and `ρ`-independent
constant.  The same pencil is what forces the scale hypothesis
`δ ^ ε' ≤ c ρ / Co` of `Kakeya.ml1Boot.exists_essDistinct_parentFamily`, by
`Kakeya.ml1Boot.not_exists_essDistinct_parentFamily`; so *both* routes to 6.6(A) from bounded
overlap pay a scale hypothesis, and for the same reason. -/
theorem not_occupiedParents_le_const_of_boundedOverlap (C : NNReal) :
    ¬ ∀ (σ ρ : NNReal), 0 < σ → σ ≤ ρ → ρ ≤ 1 →
        ∀ (q r : Finset ℕ) (T : ℕ → Tube σ (EuclideanSpace ℝ (Fin 3)))
          (R : ℕ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (assign : ℕ → ℕ),
          (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
          ml1Boot.IsParentFamily q T r R assign →
          Tube.HasBoundedOverlap q T r R 1 →
          ((r.filter fun k ↦ ∃ i ∈ q, assign i = k).card : ENNReal) ≤ (C : ENNReal) := by
  classical
  intro hbound
  obtain ⟨m, hm⟩ := exists_nat_gt (C : ℝ)
  let n : ℕ := max 5 m
  have hn5 : 5 ≤ n := le_max_left _ _
  have hnm : m ≤ n := le_max_right _ _
  have hn2 : 2 ≤ n := le_trans (by norm_num) hn5
  set σ : NNReal := ml1Boot.essDistinctCex.leafScale n with hσdef
  set ρ : NNReal := ml1Boot.essDistinctCex.parentScale n with hρdef
  set M : ℕ := ml1Boot.essDistinctCex.count n with hMdef
  have hσ0 : 0 < σ := ml1Boot.essDistinctCex.leafScale_pos n
  have hρ0 : 0 < ρ := ml1Boot.essDistinctCex.parentScale_pos n
  have hσρ : σ ≤ ρ := ml1Boot.essDistinctCex.leafScale_le_parentScale hn2
  have hρ1 : ρ ≤ 1 := ml1Boot.essDistinctCex.parentScale_le_one n
  have hρ128 : (ρ : ℝ) ≤ 1 / 128 := ml1Boot.essDistinctCex.parentScale_le_inv128 n
  have hball : ∀ i ∈ Finset.range M,
      (ml1Boot.essDistinctCex.leaf σ ρ i).carrier ⊆
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro i hi
    exact ml1Boot.essDistinctCex.leaf_carrier_subset_ball hσρ hρ128
      (ml1Boot.essDistinctCex.axial_bound n)
      (ml1Boot.essDistinctCex.trans_bound_inv12 hn5)
      (le_of_lt (Finset.mem_range.mp hi))
  have hkey := hbound σ ρ hσ0 hσρ hρ1 (Finset.range M) (Finset.range M)
    (ml1Boot.essDistinctCex.leaf σ ρ) (ml1Boot.essDistinctCex.parent σ ρ) id hball
    (ml1Boot.essDistinctCex.isParentFamily hσρ hρ0 hρ128 (Finset.range M))
    (ml1Boot.essDistinctCex.hasBoundedOverlap hσρ hρ0 hρ128 (Finset.range M) (Finset.range M))
  have hfilter :
      ((Finset.range M).filter fun k ↦ ∃ i ∈ Finset.range M, id i = k) = Finset.range M := by
    ext k
    simp only [Finset.mem_filter, id]
    constructor
    · rintro ⟨hk, -⟩
      exact hk
    · intro hk
      exact ⟨hk, k, hk, rfl⟩
  rw [hfilter, Finset.card_range] at hkey
  -- the pencil has `M = 2 ^ (2 n + 1) > C` members
  have hMC : (C : ℝ) < (M : ℝ) := by
    have h1 : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnm
    have h2 : (n : ℝ) < (M : ℝ) := by
      have : n < M := by
        have hlt : n < 2 ^ n := Nat.lt_two_pow_self
        have hle : (2 : ℕ) ^ n ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        simpa [hMdef, ml1Boot.essDistinctCex.count] using lt_of_lt_of_le hlt hle
      exact_mod_cast this
    linarith
  have hMC' : (C : ENNReal) < (M : ENNReal) := by
    have : (C : NNReal) < (M : NNReal) := by
      rw [← NNReal.coe_lt_coe]
      simpa using hMC
    exact_mod_cast this
  exact absurd hkey (not_le.mpr hMC')

/-! #### The pencil inside one test tube

The refutation above bounds no test body: it counts *all* occupied labels.  The outer plank step
of GWZ Proposition 6.6(A) counts only the labels whose leaf lies in a fixed dilate of a `ρ`-tube
(`Kakeya.edParentCount.card_assignedParents_le_of_subset_dilate`, through which
`Kakeya.edParentCount.card_assignedParents_le_homotheticDilatedThickenedPlank` factors -- the
plank test body is first enclosed in its long-axis `ρ`-tube).  The next two results show the
pencil already lives inside one such dilate, so the refutation applies verbatim to *that*
interface, which is the one the ledger of 6.6(A) consumes.

The extra scale condition is `3 σ M ≤ ρ`: the pencil's transverse spread must fit the parent
radius.  The existing scale sequence satisfies it for `n ≥ 5` (`3 · 2 ^ (-8n) · 2 ^ (2n+1) ≤
2 ^ (-(2n+9))` reduces to `3 ≤ 2 ^ (4n-10)`), so the same stages that refute the constant bound
refute the test-tube-restricted one. -/

open scoped ENNReal in
/-- **The pencil's transverse spread fits inside the parent radius**, for `n ≥ 5`. -/
theorem essDistinctCex_trans_bound_le_parentScale {n : ℕ} (hn : 5 ≤ n) :
    3 * (ml1Boot.essDistinctCex.leafScale n : ℝ) * (ml1Boot.essDistinctCex.count n : ℝ)
      ≤ (ml1Boot.essDistinctCex.parentScale n : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [ml1Boot.essDistinctCex.leafScale, ml1Boot.essDistinctCex.parentScale,
    ml1Boot.essDistinctCex.count, NNReal.coe_pow, NNReal.coe_pow]
  push_cast
  rw [div_pow, div_pow, one_pow, one_pow]
  have hgoal : 3 * (1 / (2 : ℝ) ^ (8 * (m + 5))) * (2 : ℝ) ^ (2 * (m + 5) + 1)
      = (3 * (2 : ℝ) ^ (2 * (m + 5) + 1)) / (2 : ℝ) ^ (8 * (m + 5)) := by
    ring
  rw [hgoal, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have e1 : 2 * (m + 5) + 1 + (2 * (m + 5) + 9) = 4 * m + 30 := by ring
  rw [mul_assoc, ← pow_add, e1]
  have hbig : (2 : ℝ) ^ (8 * (m + 5)) = (2 : ℝ) ^ (4 * m + 30) * (2 : ℝ) ^ (4 * m + 10) := by
    rw [show 8 * (m + 5) = (4 * m + 30) + (4 * m + 10) from by ring]
    exact pow_add 2 _ _
  rw [hbig]
  have h10 : (2 : ℝ) ^ (10 : ℕ) ≤ (2 : ℝ) ^ (4 * m + 10) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : (3 : ℝ) ≤ (2 : ℝ) ^ (4 * m + 10) := by
    refine le_trans ?_ h10
    norm_num
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (4 * m + 30) := by positivity
  calc
    3 * (2 : ℝ) ^ (4 * m + 30) ≤ (2 : ℝ) ^ (4 * m + 10) * (2 : ℝ) ^ (4 * m + 30) :=
      mul_le_mul_of_nonneg_right h3 hpos.le
    _ = (2 : ℝ) ^ (4 * m + 30) * (2 : ℝ) ^ (4 * m + 10) := by ring

open ml1Boot.essDistinctCex in
/-- **Every leaf of the pencil lies in the `4`-dilate of the parent of the first leaf.**

The `0`-th parent is centred at the origin with direction `e₁`
(`Kakeya.ml1Boot.essDistinctCex.parent_direction`), the cores of the pencil have axial coordinate
in `[-1/2, 1/2 + 7ρM]` and transverse coordinate `3σi ≤ 3σM ≤ ρ`, and a leaf point is within `σ`
of a core point.  So a leaf point is within `2` of the origin along the axis and within `3ρ` of
the axis, which is `Kakeya.Tube.mem_dilate_of_dist_axis_le` at `C = 4`. -/
theorem essDistinctCex_leaf_carrier_subset_parentZero_dilate {σ ρ : NNReal} {M : ℕ}
    (hσρ : σ ≤ ρ) (hρ : (ρ : ℝ) ≤ 1 / 128) (hax : 7 * (ρ : ℝ) * (M : ℝ) ≤ 1 / 12)
    (htr : 3 * (σ : ℝ) * (M : ℝ) ≤ (ρ : ℝ)) {i : ℕ} (hi : i ≤ M) :
    (leaf σ ρ i).carrier ⊆ (Tube.dilate (parent σ ρ 0) 4).carrier := by
  classical
  have hσ0 : (0 : ℝ) ≤ (σ : ℝ) := NNReal.coe_nonneg σ
  have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) := NNReal.coe_nonneg ρ
  have hσρ' : (σ : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hσρ
  have hσ128 : (σ : ℝ) ≤ 1 / 128 := le_trans hσρ' hρ
  have hi' : (i : ℝ) ≤ (M : ℝ) := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := by positivity
  have hax_i : 7 * (ρ : ℝ) * (i : ℝ) ≤ 1 / 12 :=
    le_trans (mul_le_mul_of_nonneg_left hi' (by positivity)) hax
  have htr_i : 3 * (σ : ℝ) * (i : ℝ) ≤ (ρ : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hi' (by positivity)) htr
  have hax0 : (0 : ℝ) ≤ 7 * (ρ : ℝ) * (i : ℝ) := by positivity
  have htr0 : (0 : ℝ) ≤ 3 * (σ : ℝ) * (i : ℝ) := by positivity
  have hnorm1 : ‖e₁‖ = 1 := norm_e₁
  have hnorm2 : ‖e₂‖ = 1 := norm_e₂
  have hcentre : (parent σ ρ 0).center = (0 : EuclideanSpace ℝ (Fin 3)) := by
    have hbase : base σ ρ 0 = (-(1 / 2 : ℝ)) • e₁ := by
      rw [base, axial, ml1Boot.essDistinctCex.trans]
      norm_num
    show midpoint ℝ (parent σ ρ 0).x (parent σ ρ 0).y = 0
    rw [show (parent σ ρ 0).x = base σ ρ 0 from rfl,
      show (parent σ ρ 0).y = base σ ρ 0 + e₁ from rfl, hbase, midpoint_eq_smul_add,
      invOf_eq_inv]
    rw [show (-(1 / 2 : ℝ)) • e₁ + ((-(1 / 2 : ℝ)) • e₁ + e₁)
      = (0 : EuclideanSpace ℝ (Fin 3)) by module, smul_zero]
  have hdir : (parent σ ρ 0).direction = e₁ := parent_direction σ ρ 0
  intro w hw
  rw [(leaf σ ρ i).carrier_eq, leaf_x, leaf_y, Set.mem_iUnion₂] at hw
  rcases hw with ⟨z, hzseg, hwz⟩
  have hwz' : dist w z ≤ (σ : ℝ) := Metric.mem_closedBall.mp hwz
  rw [segment_eq_image' ℝ] at hzseg
  rcases hzseg with ⟨t, ht, hzt⟩
  have hz2 : z = (axial ρ i + t) • e₁ + (ml1Boot.essDistinctCex.trans σ i) • e₂ := by
    rw [← hzt, base]
    module
  set a : ℝ := axial ρ i + t with ha
  set c : ℝ := ml1Boot.essDistinctCex.trans σ i with hc
  set d : EuclideanSpace ℝ (Fin 3) := w - (a • e₁ + c • e₂) with hd
  have hdnorm : ‖d‖ ≤ (σ : ℝ) := by
    rw [hd, ← hz2, ← dist_eq_norm]
    exact hwz'
  set u : ℝ := (inner ℝ e₁ d : ℝ) with hu
  have huabs : |u| ≤ (σ : ℝ) := by
    have hcs := abs_real_inner_le_norm e₁ d
    rw [hnorm1, one_mul] at hcs
    exact le_trans hcs hdnorm
  set s : ℝ := a + u with hs
  have habs_a : |a| ≤ 1 / 2 + 1 / 12 := by
    rw [ha, axial, abs_le]
    constructor
    · nlinarith [ht.1, ht.2, hax0]
    · nlinarith [ht.1, ht.2, hax_i]
  have hsabs : |s| ≤ 4 / 2 := by
    have habs : |s| ≤ |a| + |u| := by
      rw [hs]; exact abs_add_le a u
    linarith
  have hcabs : |c| ≤ (ρ : ℝ) := by
    rw [hc, ml1Boot.essDistinctCex.trans, abs_le]
    constructor
    · nlinarith [htr0]
    · nlinarith [htr_i]
  have hzeq : w - ((0 : EuclideanSpace ℝ (Fin 3)) + s • e₁) = c • e₂ + (d - u • e₁) := by
    rw [hs, hd]
    module
  have hdist : dist w ((parent σ ρ 0).center + s • (parent σ ρ 0).direction) ≤ 4 * (ρ : ℝ) := by
    rw [hcentre, hdir, dist_eq_norm, hzeq]
    calc
      ‖c • e₂ + (d - u • e₁)‖ ≤ ‖c • e₂‖ + ‖d - u • e₁‖ := norm_add_le _ _
      _ ≤ ‖c • e₂‖ + (‖d‖ + ‖u • e₁‖) := by gcongr; exact norm_sub_le _ _
      _ = |c| + (‖d‖ + |u|) := by
            rw [norm_smul, norm_smul, hnorm1, hnorm2]
            simp [Real.norm_eq_abs]
      _ ≤ (ρ : ℝ) + ((σ : ℝ) + (σ : ℝ)) := by gcongr
      _ ≤ 4 * (ρ : ℝ) := by linarith
  exact Tube.mem_dilate_of_dist_axis_le (parent σ ρ 0)
    (by norm_num : (0 : ℝ) < 4) hsabs hdist

open ml1Boot.essDistinctCex in
/-- **(the decisive refutation) No constant bounds the bounded-overlap assigned-parent count
inside a fixed test-tube dilate.**

This is `Kakeya.edParentCount.card_assignedParents_le_of_subset_dilate` -- the lemma through
which the outer plank step of GWZ Proposition 6.6(A) counts parents -- with pairwise essential
distinctness of the coarse family replaced by `Tube.HasBoundedOverlap` at `Co = 1`, and it is
false for every constant `C`, at the fixed test dilation `4`.  A fortiori it is false at every
dilation `≥ 4`, the counted set only growing with the dilation.

Consequently a bounded-overlap form of GWZ Proposition 6.6(A) *cannot* keep the ledger constant
`Kakeya.edParentCount.COfTestDilate 3 Dpar 1 L` constant: the loss envelope
`partAFixedEnvelope` of `Kakeya.multiplicity_le_of_factorsThroughFlatPrisms_of_parentPresentation`
is charged against `σ ^ (-eFund)` by `ShadedBody.eventually_const_le_coe_rpow_neg`, which needs a
`σ`- and `ρ`-independent constant, and no such constant exists.  What the count *is* bounded by is
`Co · Kakeya.ml1Boot.parentCount.C · ρ ^ (-5)`
(`Kakeya.card_assignedParents_le_of_boundedOverlap`), and the pencil shows the truth is at least
`≍ ρ ^ (-1)`; either way a hypothesis forcing `ρ ≥ σ ^ ηo` is required, and
`Kakeya.rpow_neg_five_le_of_scale` is the arithmetic that then closes the ledger. -/
theorem not_card_assignedParents_le_const_of_boundedOverlap (C : NNReal) :
    ¬ ∀ (σ ρ : NNReal), 0 < σ → σ ≤ ρ → ρ ≤ 1 →
        ∀ (q r : Finset ℕ) (T : ℕ → Tube σ (EuclideanSpace ℝ (Fin 3)))
          (R : ℕ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (assign : ℕ → ℕ)
          (V : Tube ρ (EuclideanSpace ℝ (Fin 3))),
          (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
          ml1Boot.IsParentFamily q T r R assign →
          Tube.HasBoundedOverlap q T r R 1 →
          ((r.filter fun k ↦ ∃ i ∈ q, assign i = k ∧
              (T i).toConvexSpaceBody ≤ Tube.dilate V (4 : ℝ)).card : ENNReal) ≤ (C : ENNReal) := by
  classical
  intro hbound
  obtain ⟨m, hm⟩ := exists_nat_gt (C : ℝ)
  let n : ℕ := max 5 m
  have hn5 : 5 ≤ n := le_max_left _ _
  have hnm : m ≤ n := le_max_right _ _
  have hn2 : 2 ≤ n := le_trans (by norm_num) hn5
  set σ : NNReal := leafScale n with hσdef
  set ρ : NNReal := parentScale n with hρdef
  set M : ℕ := count n with hMdef
  have hσ0 : 0 < σ := leafScale_pos n
  have hρ0 : 0 < ρ := parentScale_pos n
  have hσρ : σ ≤ ρ := leafScale_le_parentScale hn2
  have hρ1 : ρ ≤ 1 := parentScale_le_one n
  have hρ128 : (ρ : ℝ) ≤ 1 / 128 := parentScale_le_inv128 n
  have hax : 7 * (ρ : ℝ) * (M : ℝ) ≤ 1 / 12 := axial_bound n
  have htr : 3 * (σ : ℝ) * (M : ℝ) ≤ (ρ : ℝ) := essDistinctCex_trans_bound_le_parentScale hn5
  have hball : ∀ i ∈ Finset.range M,
      (leaf σ ρ i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro i hi
    exact leaf_carrier_subset_ball hσρ hρ128 hax (trans_bound_inv12 hn5)
      (le_of_lt (Finset.mem_range.mp hi))
  have hkey := hbound σ ρ hσ0 hσρ hρ1 (Finset.range M) (Finset.range M) (leaf σ ρ)
    (parent σ ρ) id (parent σ ρ 0) hball
    (isParentFamily hσρ hρ0 hρ128 (Finset.range M))
    (hasBoundedOverlap hσρ hρ0 hρ128 (Finset.range M) (Finset.range M))
  have hfilter :
      ((Finset.range M).filter fun k ↦ ∃ i ∈ Finset.range M, id i = k ∧
        (leaf σ ρ i).toConvexSpaceBody ≤ Tube.dilate (parent σ ρ 0) (4 : ℝ))
        = Finset.range M := by
    ext k
    simp only [Finset.mem_filter, id]
    constructor
    · rintro ⟨hk, -⟩
      exact hk
    · intro hk
      refine ⟨hk, k, hk, rfl, ?_⟩
      exact essDistinctCex_leaf_carrier_subset_parentZero_dilate hσρ hρ128 hax htr
        (le_of_lt (Finset.mem_range.mp hk))
  rw [hfilter, Finset.card_range] at hkey
  have hMC : (C : ℝ) < (M : ℝ) := by
    have h1 : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnm
    have h2 : (n : ℝ) < (M : ℝ) := by
      have hnM : n < M := by
        have hlt : n < 2 ^ n := Nat.lt_two_pow_self
        have hle : (2 : ℕ) ^ n ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        simpa [hMdef, count] using lt_of_lt_of_le hlt hle
      exact_mod_cast hnM
    linarith
  have hMC' : (C : ENNReal) < (M : ENNReal) := by
    have hlt : (C : NNReal) < (M : NNReal) := by
      rw [← NNReal.coe_lt_coe]
      simpa using hMC
    exact_mod_cast hlt
  exact absurd hkey (not_le.mpr hMC')

end FlatPrismsBoundedOverlap

end Kakeya
