/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Data.Nat.Log
public import Kakeya.MultiScaleFac.Clump
public import Kakeya.MultiScaleFac.GridUniformBand
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Kakeya.MultiScaleLoss

/-!
# Homogenizing the node maximal densities

One pass from the finest grid level to the coarsest brackets the node maximal densities of a
family between one number and twice it, at single levels and at pairs of levels, and re-runs the
pass inside a grid-uniform bundle so that the band it establishes survives the next refinement.

This module is the merge of the former `HomogenizeBase`, `HomogenizePairs`, `GridUniformBand`,
`HomogenizeBand`.  Each keeps its own section, so its file-level `open`s and `variable`s stay
confined to it.

## Homogenization of the node maximal densities along the grid

This section carries the `Δ_max` homogenization machinery that both halves of the dividing-scales
dichotomy need.  It was originally developed inside `Kakeya/MultiScaleFac/GapsKT.lean`; nothing in
it depends on either half, so it is hoisted here, below both, and lives in its own namespace
`Kakeya.Homogenize`.

The dyadic pigeonhole and restriction lemmas below build the single-level band machinery.  The
public paired pass culminates in `Kakeya.Homogenize.exists_homogenizing_pass_gridUniform`: it
returns a subfamily, again grid-uniform along the same grid, whose node maximal densities lie in a
common band at every pair of levels.

## Homogenization of the node maximal densities at pairs of grid levels

The paired refinement of `Kakeya/MultiScaleFac/Homogenize.lean`: a uniform family has a subfamily,
retaining all but a `totalLoss` share, again uniform along the same grid, in which for *every* pair
of levels `a`, `b` the maximal densities of the level-`b` node families met by the level-`a`
classes lie in a common band.

This machinery was originally developed inside `Kakeya/MultiScaleFac/GapsKT.lean`; nothing in it
depends on either half of the dividing-scales dichotomy, so it is hoisted here, below both, and
lives in the namespace `Kakeya.Homogenize`.  Its public grid-uniform entry point is
`Kakeya.Homogenize.exists_homogenizing_pass_gridUniform`.

## One homogenizing pass, in and out of a grid-uniform bundle

The paired homogenizing pass of `Kakeya/MultiScaleFac/Homogenize.lean` takes a
`Tube.UniformTubeSet` and hands back a `Tube.UniformTubeSet`.  A
stopping time whose state is a `Kakeya.MultiScaleFac.GridUniform` cannot use it in that form:
the pass
has to be the *last* operation of a refinement step — re-uniformizing after it would delete members
and deleting members lowers `Kakeya.maxDensity`, which destroys the lower half of the band it has
just established — and therefore its output has to be the state of the next step.

This section closes that gap.  Its entry point,
`Kakeya.Homogenize.exists_homogenizing_pass_gridUniform`, performs one paired pass on the bundle
underlying a grid-uniform system and restricts the *system* along the class-size band the pass
produces, by `Kakeya.MultiScaleFac.exists_gridUniform_restrict_band`.  It returns a grid-uniform
system on the retained family, with the assignments and node tubes of the original, together with
the paired band.

Two design points are worth recording.

* The grid length is an arbitrary `Mg`, not `ssfGridLen δ`.  Both halves of the dividing-scales
  dichotomy run their stopping times at a grid length separated from the step bound, and both call
  this lemma; tying it to `ssfGridLen δ` would force a rounding step into each caller.  The
  cardinality loss is displayed as the explicit polylogarithmic power
  `(1 - log δ)^{2 (Mg+2)(Mg+1)}`, and `Kakeya.Homogenize.polylog_pow_le_gridLoss` converts it into a
  `Kakeya.MultiScaleFac.gridLoss` as soon as `Mg ≤ ssfGridLen δ`.
* The class-size band, not merely the paired band, is what the restriction consumes, and the two
  must come from the *same* pass: a second pass performed to produce the class-size band would
  delete members and destroy the lower half of the paired band.  The pass of this section therefore
  produces both bands at once, and it is the only pass in the file: the paired-band-only layer it
  once duplicated is gone, and the pigeonhole and saturation helpers of the first section, which
  are private, serve this pass alone.
-/

@[expose] public section

open MeasureTheory Real Metric
open Kakeya.StickyKakeya
open scoped Topology

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace Homogenize
open MultiScaleFac

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
open _root_.StickyKakeya

/-! ### Homogenization of the node maximal densities -/

section HomogenizationKT

/-- **An essentially distinct family of `δ`-tubes in the unit ball is polynomially large**
(blueprint `lem:cardLeOfEssDistinctInBall`).  The exponent `8` is not sharp — `2n = 6` is what
`Tube.card_le_of_EssDistinct` gives in dimension `3` — and is chosen so that the bucket count below
is literally the one already used on the Frostman side. -/
private theorem exists_card_bucket_bound (hn : Module.finrank ℝ E = 3) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (s : Set ι).Pairwise (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
        (s.card : ℝ) ≤ A * (δ : ℝ) ^ (-(8 : ℝ)) := by
  letI : ProperSpace E := FiniteDimensional.proper_real E
  set Cess : ℝ := Tube.card_le_of_EssDistinct.C (Module.finrank ℝ E) with hCess
  refine ⟨max 1 Cess, le_max_left _ _, ?_⟩
  intro ι δ hδ hδ1 s T hball hED
  have hd0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hd1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hd6 : (1 / (δ : ℝ)) ^ (2 * Module.finrank ℝ E) = (δ : ℝ) ^ (-(6 : ℝ)) := by
    rw [show 2 * Module.finrank ℝ E = 6 by rw [hn], ← Real.rpow_natCast (1 / (δ : ℝ)) 6,
      Real.rpow_neg_eq_inv_rpow]
    norm_num
  calc
    (s.card : ℝ) ≤ Cess * (1 / (δ : ℝ)) ^ (2 * Module.finrank ℝ E) :=
      Tube.card_le_of_EssDistinct hδ (1 : ℝ) s T hball hED
    _ = Cess * (δ : ℝ) ^ (-(6 : ℝ)) := by rw [hd6]
    _ ≤ Cess * (δ : ℝ) ^ (-(8 : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hd0 hd1 (by norm_num))
        Tube.card_le_of_EssDistinct.C_pos.le
    _ ≤ max 1 Cess * (δ : ℝ) ^ (-(8 : ℝ)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_pos_of_pos hd0 _).le

/-- The number of dyadic buckets below `A δ^{-8}` is at most a constant multiple of `1 - log δ`.
This is the second display of blueprint `lem:cardLeOfEssDistinctInBall`. -/
private theorem bucket_count_le (A : ℝ) (hA : 1 ≤ A) {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((Nat.log 2 ⌊A * (δ : ℝ) ^ (-(8 : ℝ))⌋₊ + 1 : ℕ) : ℝ)
      ≤ (2 * Real.log A + 17) * (1 - Real.log (δ : ℝ)) := by
  have hδ0 : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hδ1' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hlogd : Real.log (δ : ℝ) ≤ 0 := Real.log_nonpos hδ0.le hδ1'
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hd8pos : 0 < (δ : ℝ) ^ (-(8 : ℝ)) := Real.rpow_pos_of_pos hδ0 _
  have hprod2 : 0 ≤ 2 * Real.log A * -Real.log (δ : ℝ) :=
    mul_nonneg (by linarith) (by linarith)
  set c : ℕ := ⌊A * (δ : ℝ) ^ (-(8 : ℝ))⌋₊ with hcdef
  push_cast
  rcases Nat.eq_zero_or_pos c with hc | hcpos
  · rw [hc, Nat.log_zero_right]
    push_cast
    linarith
  · have hlge := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ Nat.log 2 c)
      (le_trans (by exact_mod_cast Nat.pow_log_le_self 2 hcpos.ne')
        (hcdef ▸ Nat.floor_le (mul_pos hA0 hd8pos).le))
    rw [Real.log_pow, Real.log_mul hA0.ne' hd8pos.ne', Real.log_rpow hδ0] at hlge
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 :=
      lt_trans (by norm_num : (1 / 2 : ℝ) < (0.6931471803 : ℝ)) Real.log_two_gt_d9
    linarith [hlge, mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.log 2 - 1)
      (Nat.cast_nonneg (α := ℝ) (Nat.log 2 c))]

variable {ι : Type*}

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
open scoped Classical in
/-- **Whole-fibre deletion does not move a class at a finer level** (blueprint
`lem:maxDensityBandSurvivesCoarserDeletion`).  If `u'` retains, together with any of its members,
the whole level-`k` class of that member in `u`, then at every level `l ≥ k` the class of a node
still used by `u'` is literally unchanged. -/
private theorem coverClass_eq_of_saturated {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    (G : GridCoverSystem s T N) {u u' : Finset ι} (hus : u ⊆ s) (hu'u : u' ⊆ u) (k : ℕ)
    (hsat : ∀ i ∈ u, ∀ i' ∈ u', G.assign k i = G.assign k i' → i ∈ u')
    {l : ℕ} (hkl : k ≤ l) (hl : l ≤ N) {j : ι} (hj : j ∈ u'.image (G.assign l)) :
    coverClass u' (G.assign l) j = coverClass u (G.assign l) j := by
  obtain ⟨i', hi'u', hi'l⟩ := Finset.mem_image.mp hj
  refine Finset.Subset.antisymm (coverClass_subset_of_subset hu'u (G.assign l) j) fun i hi => ?_
  simp only [coverClass, Finset.mem_filter] at hi ⊢
  exact ⟨hsat i hi.1 i' hi'u' (G.assign_eq_of_le hkl hl (hus hi.1) (hus (hu'u hi'u'))
    (hi.2.trans hi'l.symm)), hi.2⟩

open scoped Classical in
/-- **Bucket pigeonhole.**  A finite set split into at most `B` buckets has a bucket carrying at
least a `1/B` share of it. -/
private theorem exists_dominant_bucket (u : Finset ι) (p : ι → ℕ) (B : ℕ) (hB : 0 < B)
    (hp : ∀ i ∈ u, p i < B) :
    ∃ m : ℕ, (u.card : ℝ) ≤ (B : ℝ) *
      (((u.filter (fun i => p i = m)) : Finset ι).card : ℝ) := by
  classical
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image (Finset.range B)
    (fun m => (u.filter (fun i => p i = m)).card) ⟨0, Finset.mem_range.mpr hB⟩
  refine ⟨m, ?_⟩
  have hle : u.card ≤ B * (u.filter (fun i => p i = m)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := p) (t := Finset.range B)
      (fun i hi => Finset.mem_range.mpr (hp i hi))]
    simpa using Finset.sum_le_sum (fun b hb => hm b hb)
  exact_mod_cast hle

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **One dyadic pigeonhole on whole `ρ_k`-fibres.**  A bucket function of the level-`k` node
keeps a `1/B` share of `u` and, being a function of the node alone, retains whole classes. -/
private theorem exists_fibre_pigeonhole {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {M : ℕ}
    {Cu : NNReal} (𝒰 : UniformTubeSet s T M Cu) (u : Finset ι) (k : ℕ) (p : ι → ℕ) (B : ℕ)
    (hB : 0 < B) (hp : ∀ i ∈ u, p (𝒰.cover.assign k i) < B) :
    ∃ (u' : Finset ι) (m : ℕ), u' ⊆ u ∧
      (∀ i ∈ u, ∀ i' ∈ u', 𝒰.cover.assign k i = 𝒰.cover.assign k i' → i ∈ u') ∧
      (u.card : ℝ) ≤ (B : ℝ) * (u'.card : ℝ) ∧
      (∀ i ∈ u', p (𝒰.cover.assign k i) = m) := by
  classical
  obtain ⟨m, hm⟩ := exists_dominant_bucket u (fun i => p (𝒰.cover.assign k i)) B hB hp
  exact ⟨u.filter (fun i => p (𝒰.cover.assign k i) = m), m, Finset.filter_subset _ _,
    fun i hi i' hi' h => Finset.mem_filter.mpr ⟨hi, by rw [h]; exact (Finset.mem_filter.mp hi').2⟩,
    hm, fun i hi => (Finset.mem_filter.mp hi).2⟩

/-- **A nonempty family of `δ`-tubes has maximal density at least one.**  Test against the body of
one of its members; a `δ`-tube has positive volume. -/
theorem one_le_maxDensity_tube {δ : NNReal} (hδ : 0 < δ) {t : Finset ι}
    {T : ι → Tube δ E} (hne : t.Nonempty) :
    1 ≤ Kakeya.maxDensity t (fun i => (T i).toConvexSpaceBody) := by
  obtain ⟨i, hi⟩ := hne
  exact Kakeya.one_le_maxDensity ⟨i, hi, lt_of_lt_of_le
    (ENNReal.coe_pos.mpr (mul_pos (Tube.le_volume.c_pos (Module.finrank ℝ E)) (pow_pos hδ _)))
    (Tube.le_volume (T i))⟩

end HomogenizationKT

/-! ### Homogenization of the node maximal densities at pairs of levels -/

section HomogenizationKTPairs

variable {ι : Type*}

open scoped Classical in
/-- The maximal density of the level-`b` nodes met by the class of the level-`a` node `j`, after the
ambient family has been cut down to `u`.  The index set is the image of the *class* of `j` under the
level-`b` assignment, which makes the quantity a function of the class alone, hence invariant under
the deletion of whole level-`a` fibres that the homogenizing pass performs. -/
noncomputable def pairNodeMaxDensity {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : UniformTubeSet s T N C) (u : Finset ι) (a b : ℕ) (j : ι) : ENNReal :=
  Kakeya.maxDensity ((coverClass u (𝒰.cover.assign a) j).image (𝒰.cover.assign b))
    (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)

end HomogenizationKTPairs

section PassBand

variable {ι : Type*}

/-! ### Numerical preliminaries -/

/-- **A constant is dominated by the polylogarithm below a threshold chosen from it alone**
(blueprint `lem:existsThresholdLeOneSubLog`).  Since `1 - log δ → ∞` as `δ → 0⁺`, any fixed
nonnegative `r` is below it once `δ ≤ exp (-r)`; packaging this as a threshold is what lets the
caller quantify `δ₀` before `δ`. -/
theorem exists_threshold_le_one_sub_log {r : ℝ} (hr : 0 ≤ r) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : NNReal, 0 < δ → δ ≤ δ₀ → r ≤ 1 - Real.log (δ : ℝ) := by
  refine ⟨Real.toNNReal (Real.exp (-r)), Real.toNNReal_pos.mpr (Real.exp_pos _), ?_, ?_⟩
  · rw [Real.toNNReal_le_one, Real.exp_le_one_iff]
    exact neg_nonpos.mpr hr
  · intro d hd hle
    have hdr : (d : ℝ) ≤ Real.exp (-r) := by
      rw [← Real.coe_toNNReal (Real.exp (-r)) (Real.exp_nonneg _)]
      exact_mod_cast hle
    have hlog := Real.log_le_log (mod_cast hd : (0 : ℝ) < (d : ℝ)) hdr
    rw [Real.log_exp] at hlog
    linarith

/-- **A bucket count that is a constant multiple of the polylogarithm is a power of it** (blueprint
`lem:powLePolylogPow`).  Below the threshold of `Kakeya.Homogenize.exists_threshold_le_one_sub_log`
the constant `c` is itself dominated by the polylogarithm, so `B ≤ c (1 - log δ) ≤ (1 - log δ)^2`
and the `n`-th power of the bucket count costs `2n` powers of it.  The exponent `n` is left free. -/
theorem pow_le_polylog_pow {B : ℕ} {δ : NNReal} (hδ1 : δ ≤ 1) {c : ℝ} (hc : 0 ≤ c)
    (hB : (B : ℝ) ≤ c * (1 - Real.log (δ : ℝ))) (hct : c ≤ 1 - Real.log (δ : ℝ)) (n : ℕ) :
    (B : ℝ) ^ n ≤ (1 - Real.log (δ : ℝ)) ^ (2 * n) := by
  have hlog : Real.log (δ : ℝ) ≤ 0 :=
    Real.log_nonpos (by positivity) (by exact_mod_cast hδ1)
  rw [pow_mul, sq]
  exact pow_le_pow_left₀ (Nat.cast_nonneg B)
    (hB.trans (mul_le_mul_of_nonneg_right hct (hc.trans hct))) n

/-- **The paired pass at a grid length below `ssfGridLen δ` costs one `gridLoss`** (blueprint
`lem:polylogPowLeGridLoss`).  The polylogarithmic exponent of `Kakeya.MultiScaleFac.gridLoss` is
`K (ssfGridLen δ + 1)^2`, quadratic in the grid length precisely so that a pass indexed by *pairs*
of levels fits into it: at `K = 6` it absorbs `2 (Mg+2)(Mg+1)` for every `Mg ≤ ssfGridLen δ`. -/
theorem polylog_pow_le_gridLoss {Mg : ℕ} {δ : NNReal} (hδ1 : δ ≤ 1) (hMg : Mg ≤ ssfGridLen δ)
    {C : NNReal} (hC : 1 ≤ C) :
    (1 - Real.log (δ : ℝ)) ^ (2 * ((Mg + 2) * (Mg + 1))) ≤ gridLoss C 6 δ := by
  have hlog : Real.log (δ : ℝ) ≤ 0 :=
    Real.log_nonpos (by positivity) (by exact_mod_cast hδ1)
  have hexp : 2 * ((Mg + 2) * (Mg + 1)) ≤ 6 * (ssfGridLen δ + 1) ^ 2 :=
    calc 2 * ((Mg + 2) * (Mg + 1)) = (2 * Mg + 4) * (Mg + 1) := by ring
      _ ≤ (6 * ssfGridLen δ + 6) * (ssfGridLen δ + 1) := Nat.mul_le_mul (by omega) (by omega)
      _ = 6 * (ssfGridLen δ + 1) ^ 2 := by ring
  refine (pow_le_pow_right₀ (by linarith) hexp).trans ?_
  exact le_mul_of_one_le_left (pow_nonneg (by linarith) _)
    (one_le_pow₀ (by exact_mod_cast hC))

/-! ### The paired pass, carrying the class-size band -/

omit [Nontrivial E] in
open scoped Classical in
/-- **Whole-fibre deletion at a coarse level does not move the pair quantity at a finer level**
(blueprint `lem:bandPairNodeMaxDensityInvariance`).  The paired reading of
`Kakeya.Homogenize.coverClass_eq_of_saturated`. -/
theorem pairNodeMaxDensity_eq_of_saturated {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C) {u u' : Finset ι} (hus : u ⊆ s)
    (hu'u : u' ⊆ u) (k : ℕ)
    (hsat : ∀ i ∈ u, ∀ i' ∈ u', 𝒰.cover.assign k i = 𝒰.cover.assign k i' → i ∈ u')
    {a : ℕ} (hka : k ≤ a) (ha : a ≤ N) {j : ι} (hj : j ∈ u'.image (𝒰.cover.assign a)) (b : ℕ) :
    pairNodeMaxDensity 𝒰 u' a b j = pairNodeMaxDensity 𝒰 u a b j := by
  unfold pairNodeMaxDensity
  rw [coverClass_eq_of_saturated 𝒰.cover hus hu'u k hsat hka ha hj]

open scoped Classical in
/-- **The pair quantity is at least one at a node in use** (blueprint
`lem:bandOneLePairNodeMaxDensity`).  The class of a node in use is nonempty, so its image under the
level-`b` assignment is, and a node tube has positive radius. -/
theorem one_le_pairNodeMaxDensity {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (hδ : 0 < δ) (𝒰 : UniformTubeSet s T N C) {u : Finset ι} {a b : ℕ} {j : ι}
    (hj : j ∈ u.image (𝒰.cover.assign a)) :
    1 ≤ pairNodeMaxDensity 𝒰 u a b j := by
  classical
  unfold pairNodeMaxDensity
  obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
  have hmem : i ∈ coverClass u (𝒰.cover.assign a) j := by
    simpa [coverClass] using ⟨hi, hij⟩
  exact one_le_maxDensity_tube (δ := gridScale δ N b) (gridScale_pos hδ N b)
    (T := fun j' => 𝒰.cover.tube b j') ⟨_, Finset.mem_image_of_mem _ hmem⟩

open scoped Classical in
omit [Nontrivial E] in
/-- **The pair quantity is bounded by the cardinality of the ambient family** (blueprint
`lem:bandPairNodeMaxDensityLeCard`).  Its index set is the image of a subset of `s`, and
`Kakeya.maxDensity` is bounded by the cardinality of its index set. -/
theorem pairNodeMaxDensity_le_card {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : UniformTubeSet s T N C) {u : Finset ι} (hu : u ⊆ s) (a b : ℕ) (j : ι) :
    pairNodeMaxDensity 𝒰 u a b j ≤ (s.card : ENNReal) := by
  classical
  unfold pairNodeMaxDensity
  refine (Kakeya.maxDensity_le_card _ _).trans (Nat.cast_le.mpr ?_)
  refine Finset.card_image_le.trans (Finset.card_le_card ?_)
  exact (Finset.filter_subset _ u).trans hu

open scoped Classical in
/-- **The range hypothesis of the paired pass**, supplied at every subfamily at once (blueprint
`lem:bandPairNodeMaxDensityInRange`): the pair quantity lies between one and the cardinality bound
of the ambient family. -/
theorem pairNodeMaxDensity_mem_range {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (hδ : 0 < δ) (𝒰 : UniformTubeSet s T N Cu) {V : ℝ}
    (hcard : (s.card : ℝ) ≤ V) :
    ∀ v : Finset ι, v ⊆ s → ∀ a ≤ N, ∀ b ≤ N, ∀ j ∈ v.image (𝒰.cover.assign a),
      1 ≤ pairNodeMaxDensity 𝒰 v a b j ∧
        pairNodeMaxDensity 𝒰 v a b j ≤ ENNReal.ofReal V := by
  refine fun v hv a _ b _ j hj => ⟨one_le_pairNodeMaxDensity hδ 𝒰 hj,
    (pairNodeMaxDensity_le_card 𝒰 hv a b j).trans ?_⟩
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hcard

omit [Nontrivial E] in
open scoped Classical in
/-- **One dyadic pigeonhole on the pair quantity at a fixed pair of levels** (blueprint
`lem:bandPairStepSubset`), deleting whole level-`a` fibres.  The bucket function depends on the
level-`a` node alone, so whole classes are retained and the resulting band is not disturbed by later
deletions saturated at level `a`. -/
theorem exists_pair_step_subset {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {M : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T M Cu) (V : ℝ) (hV : 1 ≤ V) (B : ℕ)
    (hB : Nat.log 2 ⌊V⌋₊ + 1 ≤ B)
    (hFc : ∀ v : Finset ι, v ⊆ s → ∀ a ≤ M, ∀ b ≤ M, ∀ j ∈ v.image (𝒰.cover.assign a),
      1 ≤ pairNodeMaxDensity 𝒰 v a b j ∧ pairNodeMaxDensity 𝒰 v a b j ≤ ENNReal.ofReal V)
    {u : Finset ι} (hu : u ⊆ s) {a : ℕ} (ha : a ≤ M) {b : ℕ} (hb : b ≤ M) :
    ∃ u' ⊆ u,
      (∀ i ∈ u, ∀ i' ∈ u', 𝒰.cover.assign a i = 𝒰.cover.assign a i' → i ∈ u') ∧
      (u.card : ℝ) ≤ (B : ℝ) * (u'.card : ℝ) ∧
      ∃ Φ : ENNReal, ∀ j ∈ u'.image (𝒰.cover.assign a),
        Φ ≤ pairNodeMaxDensity 𝒰 u' a b j ∧ pairNodeMaxDensity 𝒰 u' a b j ≤ 2 * Φ := by
  classical
  have hB0 : 0 < B := by omega
  have hp1 : ∀ i ∈ u,
      Nat.log 2 ⌊(pairNodeMaxDensity 𝒰 u a b (𝒰.cover.assign a i)).toReal⌋₊ < B := fun i hi =>
    lt_of_le_of_lt
      (Nat.log_mono_right (Nat.floor_le_floor (ENNReal.toReal_le_of_le_ofReal (by linarith)
        (hFc u hu a ha b hb _ (Finset.mem_image_of_mem (𝒰.cover.assign a) hi)).2)))
      (Nat.lt_of_succ_le hB)
  obtain ⟨u1, m1, hu1u, hsat1, hcard1, hval1⟩ :=
    exists_fibre_pigeonhole 𝒰 u a
      (fun j => Nat.log 2 ⌊(pairNodeMaxDensity 𝒰 u a b j).toReal⌋₊) B hB0 hp1
  refine ⟨u1, hu1u, hsat1, hcard1, (2 : ENNReal) ^ m1, fun j hj => ?_⟩
  have hj0 : j ∈ u.image (𝒰.cover.assign a) := Finset.image_subset_image hu1u hj
  obtain ⟨i, hi, hji⟩ := Finset.mem_image.mp hj
  have hband := ENNReal.dyadic_band (x := pairNodeMaxDensity 𝒰 u a b j)
    (hFc u hu a ha b hb j hj0).1
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hFc u hu a ha b hb j hj0).2)
  rw [show Nat.log 2 ⌊(pairNodeMaxDensity 𝒰 u a b j).toReal⌋₊ = m1 by
    rw [← hji]; exact hval1 i hi] at hband
  rwa [pairNodeMaxDensity_eq_of_saturated 𝒰 hu hu1u a hsat1 le_rfl ha hj b]

omit [Nontrivial E] in
open scoped Classical in
/-- **The inner pass at a fixed coarse level `a`** (blueprint `lem:bandPairInnerPass`), by induction
on the number `e` of fine levels already treated.  All `e` deletions are saturated at level `a`, so
each preserves the bands the earlier ones established. -/
theorem exists_pair_inner_pass {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {M : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T M Cu) (V : ℝ) (hV : 1 ≤ V) (B : ℕ)
    (hB : Nat.log 2 ⌊V⌋₊ + 1 ≤ B)
    (hFc : ∀ v : Finset ι, v ⊆ s → ∀ a ≤ M, ∀ b ≤ M, ∀ j ∈ v.image (𝒰.cover.assign a),
      1 ≤ pairNodeMaxDensity 𝒰 v a b j ∧ pairNodeMaxDensity 𝒰 v a b j ≤ ENNReal.ofReal V)
    {u : Finset ι} (hu : u ⊆ s) {a : ℕ} (ha : a ≤ M) :
    ∀ e ≤ M + 1, ∃ u' ⊆ u,
      (∀ i ∈ u, ∀ i' ∈ u', 𝒰.cover.assign a i = 𝒰.cover.assign a i' → i ∈ u') ∧
      (u.card : ℝ) ≤ (B : ℝ) ^ e * (u'.card : ℝ) ∧
      ∃ Φ : ℕ → ENNReal, ∀ b, M + 1 - e ≤ b → b ≤ M →
        ∀ j ∈ u'.image (𝒰.cover.assign a),
          Φ b ≤ pairNodeMaxDensity 𝒰 u' a b j ∧
            pairNodeMaxDensity 𝒰 u' a b j ≤ 2 * Φ b := by
  classical
  intro e
  induction e with
  | zero =>
      exact fun _ => ⟨u, Finset.Subset.refl u, fun _ hi _ _ _ => hi, by simp, fun _ => 0,
        fun _ _ _ _ _ => by omega⟩
  | succ e ih =>
      intro he
      obtain ⟨u1, hu1u, hsat1, hloss1, Phi1, hband1⟩ := ih (by omega)
      have hu1s : u1 ⊆ s := hu1u.trans hu
      obtain ⟨u2, hu2u1, hsat2, hstep, Phik, hbandk⟩ :=
        exists_pair_step_subset 𝒰 V hV B hB hFc hu1s ha (b := M - e) (by omega)
      refine ⟨u2, hu2u1.trans hu1u,
        fun i hi i' hi' h => hsat2 i (hsat1 i hi i' (hu2u1 hi') h) i' hi' h, ?_,
        Function.update Phi1 (M - e) Phik, ?_⟩
      · rw [pow_succ, mul_assoc]
        exact hloss1.trans (mul_le_mul_of_nonneg_left hstep (by positivity))
      · intro b hb1 hb2 j hj
        rcases eq_or_lt_of_le (show M - e ≤ b by omega) with heq | hlt
        · subst b
          rw [Function.update_self]
          exact hbandk j hj
        · rw [Function.update_of_ne (by omega),
            pairNodeMaxDensity_eq_of_saturated 𝒰 hu1s hu2u1 a hsat2 le_rfl ha hj b]
          exact hband1 b (by omega) hb2 j (Finset.image_subset_image hu2u1 hj)

omit [Nontrivial E] in
open scoped Classical in
/-- **One level of the paired homogenizing pass** (blueprint `lem:bandPairLevelStep`): the inner
pass over all fine levels, followed by one more dyadic pigeonhole on the retained class size, which
restores GWZ Definition 2.1(iii) at level `a`.  All `M + 2` deletions are saturated at level `a`. -/
theorem exists_pair_level_step {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {M : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T M Cu) (V : ℝ) (hV : 1 ≤ V) (B : ℕ)
    (hB : Nat.log 2 ⌊V⌋₊ + 1 ≤ B)
    (hFc : ∀ v : Finset ι, v ⊆ s → ∀ a ≤ M, ∀ b ≤ M, ∀ j ∈ v.image (𝒰.cover.assign a),
      1 ≤ pairNodeMaxDensity 𝒰 v a b j ∧ pairNodeMaxDensity 𝒰 v a b j ≤ ENNReal.ofReal V)
    (hsV : (s.card : ℝ) ≤ V) {u : Finset ι} (hu : u ⊆ s) {a : ℕ} (ha : a ≤ M) :
    ∃ u' ⊆ u,
      (∀ i ∈ u, ∀ i' ∈ u', 𝒰.cover.assign a i = 𝒰.cover.assign a i' → i ∈ u') ∧
      (u.card : ℝ) ≤ (B : ℝ) ^ (M + 2) * (u'.card : ℝ) ∧
      ∃ (Φ : ℕ → ENNReal) (cnt : ℕ), ∀ j ∈ u'.image (𝒰.cover.assign a),
        (∀ b ≤ M, Φ b ≤ pairNodeMaxDensity 𝒰 u' a b j ∧
            pairNodeMaxDensity 𝒰 u' a b j ≤ 2 * Φ b) ∧
          (2 ^ cnt ≤ (coverClass u' (𝒰.cover.assign a) j).card ∧
            (coverClass u' (𝒰.cover.assign a) j).card ≤ 2 * 2 ^ cnt) := by
  classical
  have hB0 : 0 < B := by omega
  have hVfloor : s.card ≤ ⌊V⌋₊ := Nat.le_floor hsV
  obtain ⟨u1, hu1u, hsat1, hloss1, Φ, hband1⟩ :=
    exists_pair_inner_pass 𝒰 V hV B hB hFc hu ha (M + 1) le_rfl
  have hu1s : u1 ⊆ s := hu1u.trans hu
  have hp2 : ∀ i ∈ u1,
      Nat.log 2 (coverClass u1 (𝒰.cover.assign a) (𝒰.cover.assign a i)).card < B := by
    intro i _
    refine lt_of_le_of_lt (Nat.log_mono_right ?_) (Nat.lt_of_succ_le hB)
    exact ((Finset.card_le_card (Finset.filter_subset _ u1)).trans
      (Finset.card_le_card hu1s)).trans hVfloor
  obtain ⟨u2, m2, hu2u1, hsat2, hloss2, hval2⟩ :=
    exists_fibre_pigeonhole 𝒰 u1 a
      (fun j => Nat.log 2 (coverClass u1 (𝒰.cover.assign a) j).card) B hB0 hp2
  refine ⟨u2, hu2u1.trans hu1u,
    fun i hi i' hi' h => hsat2 i (hsat1 i hi i' (hu2u1 hi') h) i' hi' h, ?_, ⟨Φ, m2, ?_⟩⟩
  · calc
      (u.card : ℝ) ≤ (B : ℝ) ^ (M + 1) * (u1.card : ℝ) := hloss1
      _ ≤ (B : ℝ) ^ (M + 1) * ((B : ℝ) * (u2.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hloss2 (by positivity)
      _ = (B : ℝ) ^ (M + 2) * (u2.card : ℝ) := by ring
  · intro j hj
    obtain ⟨i, hi, hji⟩ := Finset.mem_image.mp hj
    refine ⟨fun b hb => by
      rw [pairNodeMaxDensity_eq_of_saturated 𝒰 hu1s hu2u1 a hsat2 le_rfl ha hj b]
      exact hband1 b (by omega) hb j (Finset.image_subset_image hu2u1 hj), ?_⟩
    rw [coverClass_eq_of_saturated 𝒰.cover hu1s hu2u1 a hsat2 le_rfl ha hj]
    have hmem : i ∈ coverClass u1 (𝒰.cover.assign a) j := by
      simp only [coverClass, Finset.mem_filter]
      exact ⟨hu2u1 hi, hji⟩
    have hd := Nat.dyadic_band (c := (coverClass u1 (𝒰.cover.assign a) j).card)
      (Finset.card_pos.mpr ⟨i, hmem⟩)
    rwa [show Nat.log 2 (coverClass u1 (𝒰.cover.assign a) j).card = m2 by
      rw [← hji]; exact hval2 i hi] at hd

omit [Nontrivial E] in
open scoped Classical in
/-- **The paired homogenizing pass** (blueprint `lem:bandPairPassSubset`), by induction on the
number `d` of coarse levels already treated, from the finest downwards.  After `d` steps the finest
`d` coarse levels carry, at every fine level, both the pair band and the class-size band, and the
retained proportion is `B^{(M+2)d}`. -/
theorem exists_pair_pass_subset {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {M : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T M Cu) (V : ℝ) (hV : 1 ≤ V) (B : ℕ)
    (hB : Nat.log 2 ⌊V⌋₊ + 1 ≤ B)
    (hFc : ∀ v : Finset ι, v ⊆ s → ∀ a ≤ M, ∀ b ≤ M, ∀ j ∈ v.image (𝒰.cover.assign a),
      1 ≤ pairNodeMaxDensity 𝒰 v a b j ∧ pairNodeMaxDensity 𝒰 v a b j ≤ ENNReal.ofReal V)
    (hsV : (s.card : ℝ) ≤ V) :
    ∀ d ≤ M + 1, ∃ u ⊆ s, (s.card : ℝ) ≤ (B : ℝ) ^ ((M + 2) * d) * (u.card : ℝ) ∧
      ∃ (Φ : ℕ → ℕ → ENNReal) (cnt : ℕ → ℕ), ∀ a, M + 1 - d ≤ a → a ≤ M →
        ∀ j ∈ u.image (𝒰.cover.assign a),
          (∀ b ≤ M, Φ a b ≤ pairNodeMaxDensity 𝒰 u a b j ∧
              pairNodeMaxDensity 𝒰 u a b j ≤ 2 * Φ a b) ∧
            (2 ^ cnt a ≤ (coverClass u (𝒰.cover.assign a) j).card ∧
              (coverClass u (𝒰.cover.assign a) j).card ≤ 2 * 2 ^ cnt a) := by
  classical
  intro d
  induction d with
  | zero =>
      exact fun _ => ⟨s, Finset.Subset.refl s, by simp, fun _ _ => 0, fun _ => 0,
        fun _ _ _ _ _ => by omega⟩
  | succ d ih =>
      intro hd
      obtain ⟨u, hus, hloss, Phi, cnt, hband⟩ := ih (by omega)
      obtain ⟨u1, hu1u, hsat, hstep, Phik, cntk, hbandk⟩ :=
        exists_pair_level_step 𝒰 V hV B hB hFc hsV hus (show M - d ≤ M by omega)
      refine ⟨u1, hu1u.trans hus, ?_, Function.update Phi (M - d) Phik,
        Function.update cnt (M - d) cntk, ?_⟩
      · rw [show (M + 2) * (d + 1) = (M + 2) * d + (M + 2) by ring, pow_add, mul_assoc]
        exact hloss.trans (mul_le_mul_of_nonneg_left hstep (by positivity))
      · intro l hl1 hl2 j hj
        rcases eq_or_lt_of_le (show M - d ≤ l by omega) with heq | hlt
        · subst l
          rw [Function.update_self, Function.update_self]
          exact hbandk j hj
        · have hbandu := hband l (by omega) hl2 j (Finset.image_subset_image hu1u hj)
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            coverClass_eq_of_saturated 𝒰.cover hus hu1u (M - d) hsat (by omega) hl2 hj]
          refine ⟨fun b hb => ?_, hbandu.2⟩
          rw [pairNodeMaxDensity_eq_of_saturated 𝒰 hus hu1u (M - d) hsat (by omega) hl2 hj b]
          exact hbandu.1 b hb

end PassBand

/-! ### The pass, in and out of a grid-uniform bundle -/

open scoped Classical in
/-- **The paired pass run on the bundle underlying a grid-uniform system** (blueprint
`lem:pairPassOfGridUniform`).  The combinatorial half of
`Kakeya.Homogenize.exists_homogenizing_pass_gridUniform`: the pass itself, with its two bands and
with the cardinality loss already converted into an explicit power of the polylogarithm.  Nothing is
restricted yet — the output is still a bare subfamily. -/
theorem exists_pairPass_of_gridUniform (hn : Module.finrank ℝ E = 3) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (Mg : ℕ) (C : NNReal) (t : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (t : Set ι).Pairwise (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ∀ 𝒢 : GridUniform t T Mg C,
      ∃ t' ⊆ t,
        (t.card : ℝ)
            ≤ (1 - Real.log (δ : ℝ)) ^ (2 * ((Mg + 2) * (Mg + 1))) * (t'.card : ℝ) ∧
        ∃ (Φ : ℕ → ℕ → ENNReal) (cnt : ℕ → ℕ),
          ∀ a ≤ Mg, ∀ j ∈ t'.image (𝒢.cover.assign a),
            (∀ c ≤ Mg,
              Φ a c ≤ pairNodeMaxDensity 𝒢.toUniformTubeSet t' a c j ∧
                pairNodeMaxDensity 𝒢.toUniformTubeSet t' a c j ≤ 2 * Φ a c) ∧
            (2 ^ cnt a ≤ (coverClass t' (𝒢.cover.assign a) j).card ∧
              (coverClass t' (𝒢.cover.assign a) j).card ≤ 2 * 2 ^ cnt a) := by
  obtain ⟨A, hA1, hA⟩ := exists_card_bucket_bound (E := E) hn
  set r : ℝ := 2 * Real.log A + 17 with hr
  have hr0 : 0 ≤ r := by
    dsimp [r]
    linarith [Real.log_nonneg hA1]
  obtain ⟨d0, hd0pos, hd0le1, hthr⟩ := exists_threshold_le_one_sub_log (r := r) hr0
  refine ⟨d0, hd0pos, hd0le1, ?_⟩
  intro ι δ hδ hd0 Mg C t T hball hED 𝒢
  have hδ1 : δ ≤ 1 := le_trans hd0 hd0le1
  set V : ℝ := A * (δ : ℝ) ^ (-(8 : ℝ)) with hV
  have hcard : (t.card : ℝ) ≤ V := hA hδ hδ1 t T hball hED
  have hV1 : 1 ≤ V := by
    have hpow8 : 1 ≤ (δ : ℝ) ^ (-(8 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by exact_mod_cast hδ)
        (by exact_mod_cast hδ1) (by norm_num)
    dsimp [V]
    calc
      (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ A * (δ : ℝ) ^ (-(8 : ℝ)) := mul_le_mul hA1 hpow8 zero_le_one (by linarith)
  set B : ℕ := Nat.log 2 ⌊V⌋₊ + 1 with hB
  obtain ⟨t2, ht2t, hloss, Phi, cnt, hband⟩ :=
    exists_pair_pass_subset 𝒢.toUniformTubeSet V hV1 B le_rfl
      (pairNodeMaxDensity_mem_range hδ 𝒢.toUniformTubeSet hcard) hcard (Mg + 1) le_rfl
  have hpolylog : (B : ℝ) ^ ((Mg + 2) * (Mg + 1)) ≤
      (1 - Real.log (δ : ℝ)) ^ (2 * ((Mg + 2) * (Mg + 1))) :=
    pow_le_polylog_pow hδ1 hr0 (bucket_count_le A hA1 hδ hδ1) (hthr δ hδ hd0) _
  refine ⟨t2, ht2t, hloss.trans (mul_le_mul_of_nonneg_right hpolylog (by positivity)),
    Phi, cnt, fun a ha j hj => hband a (by omega) ha j hj⟩

open scoped Classical in
/-- **The class-size band pass, run on a bare bundle** (the `Tube.UniformTubeSet`-level reading of
`Kakeya.Homogenize.exists_pairPass_of_gridUniform`).

`Kakeya.Homogenize.exists_pairPass_of_gridUniform` needs a `Kakeya.MultiScaleFac.GridUniform`
only in order to form `GridUniform.toUniformTubeSet`; the pass itself
(`Kakeya.Homogenize.exists_pair_pass_subset`) consumes a bare `Tube.UniformTubeSet`.  This variant
therefore takes the bundle directly and keeps only the *class-size* half of the output, which is
what a band restriction against the tight net
(`Kakeya.ml1Boot.exists_restrict_uniformTubeSet_band_of_nice`) consumes.

The point of having it is that `StickyKakeya.dividingScalesFrostman` returns a
`Tube.UniformTubeSet` and its tight-net certificate, not a `GridUniform`. -/
theorem exists_classBand_pass_of_uniformTubeSet (hn : Module.finrank ℝ E = 3) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (Mg : ℕ) (C : NNReal) (t : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (t : Set ι).Pairwise (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ∀ 𝒰 : UniformTubeSet t T Mg C,
      ∃ t' ⊆ t,
        (t.card : ℝ)
            ≤ (1 - Real.log (δ : ℝ)) ^ (2 * ((Mg + 2) * (Mg + 1))) * (t'.card : ℝ) ∧
        ∃ cnt : ℕ → ℕ,
          ∀ a ≤ Mg, ∀ j ∈ t'.image (𝒰.cover.assign a),
            2 ^ cnt a ≤ (coverClass t' (𝒰.cover.assign a) j).card ∧
              (coverClass t' (𝒰.cover.assign a) j).card ≤ 2 * 2 ^ cnt a := by
  obtain ⟨A, hA1, hA⟩ := exists_card_bucket_bound (E := E) hn
  set r : ℝ := 2 * Real.log A + 17 with hr
  have hr0 : 0 ≤ r := by
    dsimp [r]
    linarith [Real.log_nonneg hA1]
  obtain ⟨d0, hd0pos, hd0le1, hthr⟩ := exists_threshold_le_one_sub_log (r := r) hr0
  refine ⟨d0, hd0pos, hd0le1, ?_⟩
  intro ι δ hδ hd0 Mg C t T hball hED 𝒰
  have hδ1 : δ ≤ 1 := le_trans hd0 hd0le1
  set V : ℝ := A * (δ : ℝ) ^ (-(8 : ℝ)) with hV
  have hcard : (t.card : ℝ) ≤ V := hA hδ hδ1 t T hball hED
  have hV1 : 1 ≤ V := by
    have hpow8 : 1 ≤ (δ : ℝ) ^ (-(8 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by exact_mod_cast hδ)
        (by exact_mod_cast hδ1) (by norm_num)
    dsimp [V]
    calc
      (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ A * (δ : ℝ) ^ (-(8 : ℝ)) := mul_le_mul hA1 hpow8 zero_le_one (by linarith)
  set B : ℕ := Nat.log 2 ⌊V⌋₊ + 1 with hB
  obtain ⟨t2, ht2t, hloss, Phi, cnt, hband⟩ :=
    exists_pair_pass_subset 𝒰 V hV1 B le_rfl
      (pairNodeMaxDensity_mem_range hδ 𝒰 hcard) hcard (Mg + 1) le_rfl
  have hpolylog : (B : ℝ) ^ ((Mg + 2) * (Mg + 1)) ≤
      (1 - Real.log (δ : ℝ)) ^ (2 * ((Mg + 2) * (Mg + 1))) :=
    pow_le_polylog_pow hδ1 hr0 (bucket_count_le A hA1 hδ hδ1) (hthr δ hδ hd0) _
  exact ⟨t2, ht2t, hloss.trans (mul_le_mul_of_nonneg_right hpolylog (by positivity)),
    cnt, fun a ha j hj => (hband a (by omega) ha j hj).2⟩

open scoped Classical in
/-- **One homogenizing pass on a grid-uniform system** (blueprint
`lem:homogenizingPassGridUniform`).  Below a threshold `δ₀` depending on the ambient dimension
alone, a grid-uniform family `t` of essentially distinct `δ`-tubes in the unit ball has a subfamily
`t'` retaining all but a `(1 - log δ)^{2 (Mg+2)(Mg+1)}` share which is again grid-uniform along the
*same* grid and carries the paired homogenization band at every pair of levels. -/
theorem exists_homogenizing_pass_gridUniform (hn : Module.finrank ℝ E = 3) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (Mg : ℕ) (C : NNReal) (t : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (t : Set ι).Pairwise (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ∀ 𝒢 : GridUniform t T Mg C,
      ∃ t' ⊆ t,
        (t.card : ℝ)
            ≤ (1 - Real.log (δ : ℝ)) ^ (2 * ((Mg + 2) * (Mg + 1))) * (t'.card : ℝ) ∧
        ∃ (𝒢' : GridUniform t' T Mg (gridUniformBandConst (E := E) C 2))
          (Φ : ℕ → ℕ → ENNReal),
          (∀ k ≤ Mg, 𝒢'.cover.assign k = 𝒢.cover.assign k) ∧
          (∀ k, 𝒢'.cover.tube k = 𝒢.cover.tube k) ∧
          (∀ k (_hk : k ≤ Mg), 𝒢'.cover.indexSet k = t'.image (𝒢.cover.assign k)) ∧
          (∀ a ≤ Mg, ∀ c ≤ Mg, ∀ j ∈ 𝒢'.cover.indexSet a,
            Φ a c ≤ Kakeya.maxDensity
                      ((coverClass t' (𝒢'.cover.assign a) j).image (𝒢'.cover.assign c))
                      (fun j' => (𝒢'.cover.tube c j').toConvexSpaceBody) ∧
              Kakeya.maxDensity
                  ((coverClass t' (𝒢'.cover.assign a) j).image (𝒢'.cover.assign c))
                  (fun j' => (𝒢'.cover.tube c j').toConvexSpaceBody) ≤ 2 * Φ a c) := by
  classical
  obtain ⟨d0, hd0pos, hd0le1, hpass⟩ := exists_pairPass_of_gridUniform (E := E) hn
  refine ⟨d0, hd0pos, hd0le1, ?_⟩
  intro ι δ hdelta hdeltad0 Mg C t T hball hED calG
  obtain ⟨t', ht't, hloss, Phi, cnt, hband⟩ := hpass hdelta hdeltad0 Mg C t T hball hED calG
  obtain ⟨calG2, hassign, htub, hidx, -⟩ :=
    exists_gridUniform_restrict_band calG ht't (fun k => (2 : NNReal) ^ cnt k)
      (fun k hk j hj => NNReal.dyadic_band (hband k hk j hj).2.1 (hband k hk j hj).2.2)
  refine ⟨t', ht't, hloss, calG2, Phi, hassign, htub, hidx, fun a ha c hc j hj => ?_⟩
  rw [hidx a ha] at hj
  have hpair := (hband a ha j hj).1 c hc
  unfold pairNodeMaxDensity at hpair
  rw [hassign a ha, hassign c hc, htub c]
  exact hpair

end Homogenize
end Kakeya

end
