/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.CoarseDensity

/-!
# The mass-share half of the coarse endgame seam, at the fibre's own hull

The coarse endgame seam of `Kakeya.ml1Boot.multTildeT_of_planksClose` has to discharge
hypothesis (a) of `Kakeya.ml1Boot.normalized_le_of_coarse_dilate`: at every `b`-tube index
`l ∈ t_b`, a bound

`C_F(fibre u'' p_b l, K_{b,l}) ≤ 2 C_T δ̃ ^ (-a'_p)`

on the Frostman constant of the *parent-map fibre* over `l`, read in a caller-chosen ambient
body `K_{b,l}` that lies in the `c`-dilate of the `b`-tube and contains the whole fibre.  This
file states that bound, once, at the smallest ambient body meeting those two side conditions:
the fibre's own convex hull.

## Why the hull and not the dilated `b`-tube

Reading the bound at the hull of the fibre is what makes the *index set* and the *ambient body*
agree, and that is the whole point.  At the dilated tube `2 · T_{b,l}` the produced bound
(`Kakeya.ml1Boot.frostmanConstIn_fibre_le_rpow`) lives at the containment index set
`familyIn u'' 𝕍 (2 · T_{b,l})`, the consumed one at `fibre u'' p_b l`, and
`Kakeya.frostmanConstIn` is monotone in neither direction in its index set, so the two have to
be *equated* — which is the inclusion `hcatch` that blueprint
`note:ml1bootFibreInclusionNotAutomatic` refutes as automatic and that
`Kakeya.ml1Boot.disjoint_familyIn_of_familyIn_subset_fibre` identifies with a separation
property of the `b`-tubes that essential distinctness does not deliver.  At the hull there is
nothing to equate: `Kakeya.ml1Boot.familyIn_convexHull_biUnion_self` says the family caught by
the hull of a set of indices *is* that set, so
`familyIn (fibre u'' p_b l) 𝕍 (hull (fibre u'' p_b l)) = fibre u'' p_b l` and the seam closes
by definition.  This is the option the `K_b` parameter of
`Kakeya.ml1Boot.normalized_le_of_coarse_dilate` was introduced to make available.

## The intended proof, and where the `|t_ρ|` of the blueprint route goes

Blueprint `lem:ml1bootFibreMassShare` states the share at the dilated tube and pays two
explicit factors, `|t_ρ|` and `b_p / a_p`; `note:ml1bootFibreMassShareNoConstantShare` refutes
the `O(1)` form of *that* statement, and `item:massShareExitSlot` of the same note shows the
`|t_ρ| = O(ρ ^ (-4)) = O(δ̃ ^ (-24 ε))` cannot be charged to the Frostman slot, whose budget
`a'_p ≤ 2 η'_{j-1}` is of order `ε ³`.  None of that refutes the statement below, which is a
different statement: the route to it never mentions the whole family's mass, so the count
never appears.  In outline, with `𝕍 i = T̃ i` and `s = fibre u'' p_b l`:

1. `Kakeya.ml1Boot.frostmanConstIn_le_of_density_le` at `s` and `B = hull s` reduces the goal
   to a density comparison `Δ(𝕍|_s, K) ≤ C Δ(𝕍|_s, hull s)` for every `K ≤ hull s`; the
   index-set bookkeeping is free, by `familyIn_convexHull_biUnion_self`.
2. `p_b` factors through the block map of `Kakeya.ml1Boot.plankBlocks_partition` — this is the
   `∀ k k', q k = q k' → p_b k = p_b k'` clause of
   `Kakeya.ml1Boot.exists_merged_parentFamily`, exported from
   `Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct` as the no-split clause `hnosplit`
   below — so `s` is a *disjoint union of plank blocks*, and `Kakeya.densityIn` is additive in
   its index set.  Summing, `Δ(𝕍|_s, K) ≤ ∑_blocks Δ_max(𝕍|_{P})`.
3. Each block's term is `Kakeya.ml1Boot.Factorization.maxDensity_le_mul`:
   `Δ_max(𝔽_{m_P}) ≤ 2 Δ(𝕍|_P, hull P)`, and `P ⊆ 𝔽_{m_P}` makes the left side dominate
   `Δ_max(𝕍|_P)`.  With clause (iv) of `Kakeya.ml1Boot.exists_plankDimensions`
   (`|hull P| ≥ C_vol⁻¹ a_p b_p`) this is `≤ 2 C_vol |P|-mass / (a_p b_p)`.
4. Summing over the blocks recovers the *fibre's* mass — this is where the block count
   cancels, and it is why no `|t_ρ|` survives — so
   `Δ(𝕍|_s, K) ≤ 2 C_vol · mass(s) / (a_p b_p) = 2 C_vol (|hull s| / (a_p b_p)) Δ(𝕍|_s, hull s)`.
5. `hull s ≤ c · T_{b,l}`: each `T̃ i` with `p_b i = l` lies in `c · T_{b,l}` by the
   `le_parent_dilate` field of `Kakeya.ml1Boot.IsParentFamilyDilate` (Factoring.lean:159), and
   the dilate is convex, so the hull does too.  Then
   `Kakeya.Tube.tubeDilateVolume` (IntersectionVolume.lean:614) charges the homothety
   `Kakeya.Tube.tubeDilateVolume.C' 3 c = c ³` and `Kakeya.Tube.volume_le` (Basic.lean:885)
   bounds the `b`-tube itself by `2 ⁴ (C_𝕎 b_p) ²`, giving
   `|hull s| / (a_p b_p) ≤ 2 ⁴ c ³ C_𝕎 ² (b_p / a_p)`, which `hratio` bounds by
   `δ̃ ^ (-a'_p)`.  `Kakeya.Tube.volume_le` is stated for tubes of thickness at most `1`, which
   is why `hbq1 : C_𝕎 b_p ≤ 1` is hypothesised below; it is the hypothesis of the same name of
   `Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct` (CoarseDensity.lean:1543), so
   every caller of that producer already holds it.

**The constant, now settled.**  Step 5 is where the constant is decided, and the comparison
that earlier versions of this docstring left open has been carried out.  Writing
`c = C_{lem:ml1bootPlankTubeParents}(3)` and `C_𝕎 = C_{lem:ml1bootPlankPigeonhole}`, the route
delivers `2 · (2 ⁴ C^vol c ³ C_𝕎 ²) (b_p / a_p)` — the leading `2` from
`Kakeya.ml1Boot.Factorization.maxDensity_le_mul` in step 3, the rest from step 5.  Since
`C^vol = 8 C_𝕎 ³ V` and `C_T = 256 C_𝕎 ⁶ V` with `V = Metric.volume_comparison.C 3`, the route
constant is `2 ¹⁵ · 3 · V c ³ C_𝕎 ⁵` and the old budget `2 C_T` is `2 ¹⁵ · 3 · V C_𝕎 ⁶`, so
their ratio is exactly

`(route) / (2 C_T) = c ³ / (2 C_𝕎)`,

which is about `1.8 · 10 ¹⁰`.  The route therefore does **not** land inside `2 C_T`, and the
earlier estimate of `10 ³` for the overrun was itself two accounting errors: it used `c ²`
where the dilate costs `c ³`, and it dropped the tube-volume constant `2 ⁴`.  Nor is sharpening
available: `c ³` is the volume of the homothety the fibre's hull is read inside, and
CoarseDensity.lean:115 records that `c = 6 C_ov ²` is already the least ratio its own route
allows.

So the statement below is asserted at its own constant `Kakeya.ml1Boot.fibreMassShare.C`
instead, and the five steps above are now *proved* at that constant, so nothing is owed here.
Because `C_T ≤ C_{lem:ml1bootFibreMassShareAtHull}`, this is a strict weakening
of the earlier conclusion: it cannot turn a true statement false, and it removes the risk that
the tree was assembled from a claim no route reaches.  Whether the *old* conclusion is in fact
false is not decided here — no counterexample was produced, only the route's shortfall — and
that is exactly why widening, rather than a refutation note, is the right repair.

**The knock-on, which is not in this file.**  Hypotheses (a) (Assembly.lean:627-628) and (d)
(Assembly.lean:633-636) of `Kakeya.ml1Boot.normalized_le_of_coarse_dilate` both read the factor
`2 C_T`, and both must read `2 C_{lem:ml1bootFibreMassShareAtHull}` for the substitution to go
through.  The change is `δ̃`-free in both, and (d) has the form
`(δ̃-free constant) · δ̃ ^ (-a'_p) ≤ δ̃ ^ (-5 a'_p)`, i.e. `4 a'_p` of slack for `δ̃`-free
constants, so it stays dischargeable eventually in `δ̃` for every fixed `c`, `M`.  No exponent
moves.

The four other declarations that an earlier version of this module docstring announced —
`volume_dilate_le_of_plank_volume_ge`,
`volume_ne_zero_and_ne_top_of_isPlankOfDimensions`, `volume_dilate_mul_sum_le_of_plankBlock`,
`volume_dilate_mul_sum_le_of_fibreMassShare` — were never written, and they belonged to the
dilated-tube shape that the `K_b` parameter replaced.  They are not planned.  The fifth,
`fibreMassShare.C`, is now here, for the reason above and not in its old role.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The constant `C_{lem:ml1bootFibreMassShareAtHull}`**: the constant at which the hull route
of `Kakeya.ml1Boot.frostmanConstIn_fibre_convexHull_le` bounds the fibre's Frostman constant.

The blueprint environment for it does **not** exist yet and has to be added; it is *not*
`def:ml1bootFibreMassShareConstant`, which belongs to the dilated-tube
`lem:ml1bootFibreMassShare` — a different statement, carrying the extra factors `|t_ρ| b_p/a_p`
and a different value `1280 C_𝕎 ³ C^vol` (section8_endgame.tex:1424-1469).  Per 
constants of different lemmas must carry different lemma subscripts, so the hull form needs its
own `lem:` label and its own `Constant in Lemma~\ref{...}` environment carrying the `\lean`
pointer to this definition.

Reading that conclusion as `2 C_{lem:ml1bootFibreMassShareAtHull} δ̃ ^ (-a'_p)`, the leading `2` is
the factoring loss of `Kakeya.ml1Boot.Factorization.maxDensity_le_mul` and this constant is
everything the volume step then costs:

* `Kakeya.Tube.volume_le.C 3` for the `b`-tube's volume from above and
  `C^vol_{lem:ml1bootPlankPigeonhole}` for the plank's from below
  (`Kakeya.ml1Boot.volume_bounds_of_isPlankOfDimensions_vol`);
* `C_𝕎 ²` for the plank-tube scale `C_𝕎 b_p` of
  `Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct`, squared because a tube's volume in
  `ℝ³` is a constant times its thickness squared;
* `c ³` for the homothety factor `Kakeya.Tube.tubeDilateVolume.C' 3 c` of the `c`-dilate the
  fibre's hull is read inside, at `c = C_{lem:ml1bootPlankTubeParents}(3)`.

It is deliberately *not* `C_{lem:ml1bootDensityTransfer}`, the constant the consumer
`Kakeya.ml1Boot.normalized_le_of_coarse_dilate` was stated at: that budget is smaller than this
one by the factor `c ³ / (2 C_𝕎)`, about `1.8 · 10 ¹⁰`, and the module docstring carries the
comparison.  The two are ordered,
`C_{lem:ml1bootDensityTransfer} ≤ C_{lem:ml1bootFibreMassShareAtHull}`, so reading the conclusion
here is a weakening.

Like the constants it is built from it depends only on the ambient dimension `3`; in particular
not on `δ̃`, on `a_p`, on `b_p`, on `ρ`, on `γ`, on `j`, or on the family.  It is kept as an
expression in those constants and never collapsed to a numeral, so that a missing power shows up
here rather than at a use site.  `Real.toNNReal` repackages the `ℝ`-valued
`Kakeya.ml1Boot.plankTubeParents.C` as an `NNReal`; the coercion back is faithful, that constant
being positive. -/
noncomputable abbrev fibreMassShare.C : NNReal :=
  Tube.volume_le.C 3 * plankPigeonhole.C_vol * plankPigeonhole.C ^ 2
    * Real.toNNReal (plankTubeParents.C 3) ^ 3

/-! ### Auxiliary steps of the five-step route

The five lemmas below are the steps of the module docstring, each stated so that it can be
proved on its own.  Nothing in this group is specific to the coarse endgame except the last
two, which name the constants of `Kakeya.ml1Boot.fibreMassShare.C`. -/

/-- **A density is additive along a partition of its index set** (step 2 of the module
docstring, in the form the block decomposition delivers it).

The hypothesis `hsum` says that the finitely many index sets `blk j`, `j ∈ Bl`, partition `s`,
expressed as the equality of *every* `ℝ≥0∞`-weighted sum over `s` with the corresponding double
sum.  Since `Kakeya.densityIn` is a sum over a filtered index set divided by the fixed volume
`|K|`, it inherits the same additivity. -/
theorem densityIn_eq_sum_blocks {ι κ' : Type*} {s : Finset ι} {Bl : Finset κ'}
    {blk : κ' → Finset ι} (V : ι → ConvexSpaceBody E)
    (hsum : ∀ f : ι → ENNReal, ∑ i ∈ s, f i = ∑ j ∈ Bl, ∑ i ∈ blk j, f i)
    (K : ConvexSpaceBody E) :
    densityIn s V K = ∑ j ∈ Bl, densityIn (blk j) V K := by
  let g : ι → ENNReal := fun i => if V i ≤ K then volume (V i).carrier else 0
  calc
    densityIn s V K = (∑ i ∈ s, g i) / volume K.carrier := by
      simp only [Kakeya.densityIn, g, Finset.sum_filter]
    _ = (∑ j ∈ Bl, ∑ i ∈ blk j, g i) / volume K.carrier := by
      rw [hsum g]
    _ = ∑ j ∈ Bl, ((∑ i ∈ blk j, g i) / volume K.carrier) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = ∑ j ∈ Bl, densityIn (blk j) V K := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Kakeya.densityIn, g, Finset.sum_filter]

/-- **A block carries its plank's share of the density** (step 3 of the module docstring).

For a part `t` of a `C`-factorization of `s` and **any** test body `K`, the density of the part
inside `K` is at most `C · D` times the part's mass, whenever the part's hull has volume at
least `D⁻¹`.  The three positivity hypotheses are what turns the lower bound
`C_vol⁻¹ a b ≤ |hull t|` of clause (iv) of `Kakeya.ml1Boot.exists_plankDimensions` into the
factor `C_vol (a b)⁻¹` displayed here.

No property of `K` is used: the left side is bounded by `Δ_max(𝕍)` for every `K`, which is what
`Kakeya.ConvexSpaceBody.Factorization.maxDensity_le_mul` compares with the part's own density. -/
theorem densityIn_part_le_of_volume_convexHull_ge {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {V : ι → ConvexSpaceBody E} {C : NNReal}
    (F : ConvexSpaceBody.Factorization s V C) {t : Finset ι} (ht : t ∈ F.parts)
    {Cvol ap bp : NNReal} (hCvol : 0 < Cvol) (hap : 0 < ap) (hbp : 0 < bp)
    (hlo : (Cvol : ENNReal)⁻¹ * (ap : ENNReal) * (bp : ENNReal)
      ≤ volume (t.convexHull_biUnion V).carrier)
    (K : ConvexSpaceBody E) :
    densityIn t V K
      ≤ (C : ENNReal) * (Cvol : ENNReal) * ((ap : ENNReal) * (bp : ENNReal))⁻¹
        * ∑ i ∈ t, volume (V i).carrier := by
  classical
  -- `hlo` says the hull has volume at least `Cvol⁻¹ · ap · bp`.  Take reciprocals so the
  -- density `(mass / |hull|)` is bounded by `mass · Cvol · (ap · bp)⁻¹`.
  -- The three positivity hypotheses make `Cvol⁻¹ · ap · bp` a perfectly invertible atom:
  -- `Cvol` and the product `ap · bp` split the inverse, with `hCvol` / `hap` / `hbp` giving
  -- the nonzeroness that lets the product-inverse distribute.
  have hCvol0 : (Cvol : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hCvol)
  have hCvolinvTop : (Cvol : ENNReal)⁻¹ ≠ ⊤ := by
    intro h
    exact hCvol0 (ENNReal.inv_eq_top.mp h)
  have habTop : (ap : ENNReal) * (bp : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hab0 : (ap : ENNReal) * (bp : ENNReal) ≠ 0 := by positivity
  have hX : ((Cvol : ENNReal)⁻¹ * (ap : ENNReal) * (bp : ENNReal))⁻¹
      = (Cvol : ENNReal) * ((ap : ENNReal) * (bp : ENNReal))⁻¹ := by
    calc
      ((Cvol : ENNReal)⁻¹ * (ap : ENNReal) * (bp : ENNReal))⁻¹
          = ((Cvol : ENNReal)⁻¹ * ((ap : ENNReal) * (bp : ENNReal)))⁻¹ := by
            rw [mul_assoc]
      _ = ((Cvol : ENNReal)⁻¹)⁻¹ * ((ap : ENNReal) * (bp : ENNReal))⁻¹ := by
            rw [ENNReal.mul_inv (a := (Cvol : ENNReal)⁻¹) (b := (ap : ENNReal) * (bp : ENNReal))
              (Or.inr habTop) (Or.inl hCvolinvTop)]
      _ = (Cvol : ENNReal) * ((ap : ENNReal) * (bp : ENNReal))⁻¹ := by
            rw [inv_inv]
  have hB : densityIn t V (t.convexHull_biUnion V)
      = (∑ i ∈ t, volume (V i).carrier) / volume (t.convexHull_biUnion V).carrier := by
    rw [densityIn_of_all_le (K := t.convexHull_biUnion V)]
    exact t.le_convexHull_biUnion V
  have hvolinv : (volume (t.convexHull_biUnion V).carrier)⁻¹
      ≤ ((Cvol : ENNReal)⁻¹ * (ap : ENNReal) * (bp : ENNReal))⁻¹ := by
    exact (ENNReal.inv_le_inv (a := volume (t.convexHull_biUnion V).carrier)
      (b := (Cvol : ENNReal)⁻¹ * (ap : ENNReal) * (bp : ENNReal))).mpr hlo
  have hden : densityIn t V (t.convexHull_biUnion V)
      ≤ (Cvol : ENNReal) * ((ap : ENNReal) * (bp : ENNReal))⁻¹
        * ∑ i ∈ t, volume (V i).carrier := by
    rw [hB]
    calc
      (∑ i ∈ t, volume (V i).carrier) / volume (t.convexHull_biUnion V).carrier
          = (∑ i ∈ t, volume (V i).carrier) * (volume (t.convexHull_biUnion V).carrier)⁻¹ := by
            rw [div_eq_mul_inv]
      _ ≤ (∑ i ∈ t, volume (V i).carrier)
          * ((Cvol : ENNReal)⁻¹ * (ap : ENNReal) * (bp : ENNReal))⁻¹ := by
            gcongr
      _ = (∑ i ∈ t, volume (V i).carrier)
          * ((Cvol : ENNReal) * ((ap : ENNReal) * (bp : ENNReal))⁻¹) := by
            rw [hX]
      _ ≤ (Cvol : ENNReal) * ((ap : ENNReal) * (bp : ENNReal))⁻¹
          * ∑ i ∈ t, volume (V i).carrier := by
            rw [mul_comm]
  calc
    densityIn t V K ≤ densityIn s V K := Kakeya.densityIn_mono' V K t s (F.subset ht)
    _ ≤ maxDensity s V := Kakeya.le_maxDensity s V K
    _ ≤ (C : ENNReal) * densityIn t V (t.convexHull_biUnion V) := F.maxDensity_le_mul t ht
    _ ≤ (C : ENNReal) * ((Cvol : ENNReal) * ((ap : ENNReal) * (bp : ENNReal))⁻¹
        * ∑ i ∈ t, volume (V i).carrier) := by
      gcongr
    _ = (C : ENNReal) * (Cvol : ENNReal) * ((ap : ENNReal) * (bp : ENNReal))⁻¹
        * ∑ i ∈ t, volume (V i).carrier := by
      ring

/-- **The fibre of the merged block map is a union of whole plank blocks** (step 2 of the module
docstring).

`Kakeya.ml1Boot.plankBlocks_partition` exhibits the blocks as the fibres of a single map `q` on
`u''`, and `hnosplit` — the no-split clause exported by
`Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct` — says that whenever one member of a
block is sent to `l` by the merged map `pb`, the *whole* block is.  So the `pb`-fibre over `l`
is a disjoint union of complete blocks, which is what the additivity of
`Kakeya.ml1Boot.densityIn_eq_sum_blocks` consumes.

The blocks are returned as a `Finset` of block indices `(m, t)` together with the two facts a
consumer needs about each of them: that `m` is a `ρ`-parent and that `t` is one of the parts of
`F m`, so that the plank dimensions of `hdims` are available at `t`. -/
theorem exists_blocks_fibre {δt : NNReal}
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (pρ : ι → κ)
    (hu'' : u'' ⊆ u) (hmapsTo : ∀ i ∈ u, pρ i ∈ tρ)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hparts : ∀ m ∈ tρ, ∀ part ∈ (F m).parts, part.Nonempty)
    (pb : ι → κ × Finset ι) (l : κ × Finset ι)
    (hnosplit : ∀ j' ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)),
      ∀ k ∈ j'.2, pb k = l → j'.2 ⊆ fibre u'' pb l) :
    ∃ Bl : Finset (κ × Finset ι),
      (∀ j ∈ Bl, j.1 ∈ tρ ∧ j.2 ∈ (F j.1).parts) ∧
      ∀ f : ι → ENNReal, ∑ i ∈ fibre u'' pb l, f i = ∑ j ∈ Bl, ∑ i ∈ j.2, f i := by
  classical
  obtain ⟨q, hq1, hq2, hq3, hq4⟩ := plankBlocks_partition T pρ hu'' hmapsTo F hparts
  let Bl : Finset (κ × Finset ι) := (fibre u'' pb l).image q
  have hfil : ∀ j ∈ Bl, (fibre u'' pb l).filter (fun i => q i = j) = j.2 := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨k, hkfib, hqk⟩
    have hku : k ∈ u'' := (Finset.mem_filter.mp hkfib).1
    have hpbk : pb k = l := (Finset.mem_filter.mp hkfib).2
    have hjin : j ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)) := by
      rw [← hqk]
      exact hq2 k hku
    rcases Finset.mem_biUnion.mp hjin with ⟨m, hmtρ, hmem⟩
    rcases Finset.mem_image.mp hmem with ⟨part, hpartmem, hjeq⟩
    apply Finset.ext
    intro i
    constructor
    · intro hif
      have hif' : i ∈ fibre u'' pb l := (Finset.mem_filter.mp hif).1
      have hqi : q i = j := (Finset.mem_filter.mp hif).2
      have hiu : i ∈ u'' := (Finset.mem_filter.mp hif').1
      have hifilter : i ∈ u''.filter (fun k => q k = (m, part)) := by
        exact Finset.mem_filter.mpr ⟨hiu, hqi.trans hjeq.symm⟩
      rw [hq4 m hmtρ part hpartmem] at hifilter
      rwa [← congrArg Prod.snd hjeq]
    · intro hij
      have hkj2 : k ∈ j.2 := by
        rw [← congrArg Prod.snd hqk]
        exact (hq1 k hku).2.2
      have hsub : j.2 ⊆ fibre u'' pb l := hnosplit j hjin k hkj2 hpbk
      have hif' : i ∈ fibre u'' pb l := hsub hij
      have hiq : q i = j := by
        have hpart : i ∈ part := by
          rw [hjeq.symm] at hij
          exact hij
        have hifilter : i ∈ u''.filter (fun k => q k = (m, part)) := by
          rw [hq4 m hmtρ part hpartmem]
          exact hpart
        exact (Finset.mem_filter.mp hifilter).2.trans hjeq
      exact Finset.mem_filter.mpr ⟨hif', hiq⟩
  refine ⟨Bl, ?_, ?_⟩
  · intro j hj
    rcases Finset.mem_image.mp hj with ⟨k, hkfib, hqk⟩
    have hku : k ∈ u'' := (Finset.mem_filter.mp hkfib).1
    have hjin : j ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)) := by
      rw [← hqk]
      exact hq2 k hku
    rcases Finset.mem_biUnion.mp hjin with ⟨m, hmtρ, hmem⟩
    rcases Finset.mem_image.mp hmem with ⟨part, hpartmem, hjeq⟩
    constructor
    · rw [← congrArg Prod.fst hjeq]
      exact hmtρ
    · rw [← congrArg Prod.snd hjeq]
      rw [← congrArg Prod.fst hjeq]
      exact hpartmem
  · intro f
    rw [← Finset.sum_fiberwise_of_maps_to (s := fibre u'' pb l) (t := Bl) (g := q)
        (fun i hi => Finset.mem_image_of_mem q hi) f]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hfil j hj]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The hull of a fibre lies in the dilate of the parent tube** (the containment half of step 5
of the module docstring).

Every member of the `pb`-fibre over `l` lies in the `c`-dilate of `T_{b,l}` by the
`le_parent_dilate` field, and the dilate is a convex body, so the hull of the fibre lies there
too by `Finset.Nonempty.convexHull_biUnion_le_iff`.  This is also the side condition that the
`K_b` parameter of `Kakeya.ml1Boot.normalized_le_of_coarse_dilate` asks of its ambient family. -/
theorem convexHull_biUnion_fibre_le_parent_dilate [Nontrivial E] {δt σ : NNReal} {c : ℝ}
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u'' : Finset ι} {tb : Finset κ}
    (T : ι → Tube δt E) (Tb : κ → Tube σ E) (pb : ι → κ)
    (hpf : IsParentFamilyDilate c u'' T tb Tb pb) {l : κ}
    (hne : (fibre u'' pb l).Nonempty) :
    ((fibre u'' pb l).convexHull_biUnion fun i => (T i).toConvexSpaceBody)
      ≤ Tube.dilate (Tb l) c := by
  classical
  exact (Finset.Nonempty.convexHull_biUnion_le_iff hne
    (fun i => (T i).toConvexSpaceBody) (Tube.dilate (Tb l) c)).mpr (by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨hiu, hpl⟩
      rw [← hpl]
      exact hpf.le_parent_dilate i hiu)

/-- **The volume of a tube dilate in `ℝ³`** (the volume half of step 5 of the module docstring).

`Kakeya.Tube.tubeDilateVolume` charges the homothety the factor
`Kakeya.Tube.tubeDilateVolume.C' 3 c = c ³` and `Kakeya.Tube.volume_le` bounds the tube itself by
`C_{volume_le}(3) σ ²`; the hypothesis `σ ≤ 1` is the one `Kakeya.Tube.volume_le` carries. -/
theorem volume_dilate_le_of_dim_three [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {σ : NNReal} (hσ1 : σ ≤ 1) {c : ℝ} (hc : 1 < c) (Tb : Tube σ E) :
    volume (Tube.dilate Tb c).carrier
      ≤ (Real.toNNReal c : ENNReal) ^ 3 * (Tube.volume_le.C 3 : ENNReal) * (σ : ENNReal) ^ 2 := by
  have h0 : (0 : ℝ) ≤ c := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hc)
  have hof : ENNReal.ofReal c = (Real.toNNReal c : ENNReal) := by
    rw [ENNReal.ofReal_eq_coe_nnreal h0]
    rw [Real.toNNReal_of_nonneg h0]
  have hconv : ENNReal.ofReal (c ^ 3) = (Real.toNNReal c : ENNReal) ^ 3 := by
    calc
      ENNReal.ofReal (c ^ 3) = (ENNReal.ofReal c) ^ 3 := by rw [ENNReal.ofReal_pow h0 3]
      _ = (Real.toNNReal c : ENNReal) ^ 3 := by rw [hof]
  have htd' : volume (Tube.dilate Tb c).carrier
      = ENNReal.ofReal (c ^ 3) * volume Tb.carrier := by
    rw [Tube.tubeDilateVolume Tb hc]
    congr 1
    rw [hdim]
  have hv' : volume Tb.carrier ≤ (Tube.volume_le.C 3 : ENNReal) * (σ : ENNReal) ^ 2 := by
    have hv := Tube.volume_le hσ1 Tb
    rw [hdim] at hv
    simpa [ENNReal.coe_mul, ENNReal.coe_pow] using hv
  calc
    volume (Tube.dilate Tb c).carrier = ENNReal.ofReal (c ^ 3) * volume Tb.carrier := htd'
    _ ≤ ENNReal.ofReal (c ^ 3) * ((Tube.volume_le.C 3 : ENNReal) * (σ : ENNReal) ^ 2) := by
      gcongr
    _ = ENNReal.ofReal (c ^ 3) * (Tube.volume_le.C 3 : ENNReal) * (σ : ENNReal) ^ 2 := by
      rw [mul_assoc]
    _ = (Real.toNNReal c : ENNReal) ^ 3 * (Tube.volume_le.C 3 : ENNReal) * (σ : ENNReal) ^ 2 := by
      rw [hconv]

/-- **A hull containing a body of positive volume has positive volume.**  Immediate from
`Finset.le_convexHull_biUnion` and monotonicity of the measure; it is what makes the denominator
`|hull s|` of `Δ(𝕍|_s, hull s)` invertible in the last step of the route. -/
theorem volume_convexHull_biUnion_ne_zero {ι : Type*} {t : Finset ι}
    (V : ι → ConvexSpaceBody E) {i : ι} (hi : i ∈ t) (hV : volume (V i).carrier ≠ 0) :
    volume (t.convexHull_biUnion V).carrier ≠ 0 := by
  intro h
  exact hV
    (measure_mono_null (SetLike.le_def.mp (Finset.le_convexHull_biUnion V hi)) h)

/-- **A mass bound becomes a density comparison** (step 4 of the module docstring, and the shape
`Kakeya.ml1Boot.frostmanConstIn_le_of_density_le` consumes).

If every member of the family lies in the ambient body `B`, then `Δ(𝕍, B)` is the family's mass
over `|B|`; so a bound `Δ(𝕍, K) ≤ D · mass` turns into `Δ(𝕍, K) ≤ 𝒞 Δ(𝕍, B)` as soon as
`D |B| ≤ 𝒞`.  This is where the block count cancels: `mass` is the *fibre's* mass, summed back
up from the blocks, and no count of them survives. -/
theorem densityIn_le_mul_densityIn_of_le_mul_sum {ι : Type*} {s : Finset ι}
    (V : ι → ConvexSpaceBody E) {B : ConvexSpaceBody E} (hall : ∀ i ∈ s, V i ≤ B)
    (hB0 : volume B.carrier ≠ 0) (hBtop : volume B.carrier ≠ ⊤)
    {D Cst : ENNReal} (hD : D * volume B.carrier ≤ Cst)
    {K : ConvexSpaceBody E} (hK : densityIn s V K ≤ D * ∑ i ∈ s, volume (V i).carrier) :
    densityIn s V K ≤ Cst * densityIn s V B := by
  rw [densityIn_of_all_le (K := B) hall]
  calc
    densityIn s V K ≤ D * ∑ i ∈ s, volume (V i).carrier := hK
    _ = D * volume B.carrier * ((∑ i ∈ s, volume (V i).carrier) / volume B.carrier) := by
      rw [mul_assoc, ENNReal.mul_div_cancel hB0 hBtop]
    _ ≤ Cst * ((∑ i ∈ s, volume (V i).carrier) / volume B.carrier) := by
      gcongr

/-- **The constant of the route is `2 C_{lem:ml1bootFibreMassShareAtHull}`** (the arithmetic of
steps 3 and 5 of the module docstring, collected).

With `v` the volume of the fibre's hull, bounded as step 5 bounds it, the factor
`2 C^vol (a_p b_p)⁻¹ v` that steps 3 and 4 leave is
`2 C_{lem:ml1bootFibreMassShareAtHull} (b_p / a_p)`, and `hratio` absorbs the width ratio into
`δ̃ ^ (-a'_p)`.  The exponent `2` on `b_p` in `hv` against the single `b_p` in the denominator is
what leaves exactly one power of the ratio; no other cancellation occurs. -/
theorem massShare_const_le {ap bp : NNReal} (hap : 0 < ap) (hbp : 0 < bp)
    {δt : NNReal} {ap' : ℝ}
    (hratio : (bp : ENNReal) / (ap : ENNReal) ≤ (δt : ENNReal) ^ (-ap'))
    {v : ENNReal}
    (hv : v ≤ (Tube.volume_le.C 3 : ENNReal) * (plankPigeonhole.C : ENNReal) ^ 2
      * (Real.toNNReal (plankTubeParents.C 3) : ENNReal) ^ 3 * (bp : ENNReal) ^ 2) :
    2 * (plankPigeonhole.C_vol : ENNReal) * ((ap : ENNReal) * (bp : ENNReal))⁻¹ * v
      ≤ 2 * (fibreMassShare.C : ENNReal) * (δt : ENNReal) ^ (-ap') := by
  have hA0 : (ap : ENNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt hap)
  have hB0 : (bp : ENNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt hbp)
  have hBtop : (bp : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hC : (fibreMassShare.C : ENNReal)
      = (Tube.volume_le.C 3 : ENNReal) * (plankPigeonhole.C_vol : ENNReal)
        * (plankPigeonhole.C : ENNReal) ^ 2
        * (Real.toNNReal (plankTubeParents.C 3) : ENNReal) ^ 3 := by
    rfl
  have hB2 : (bp : ENNReal) ^ 2 * ((ap : ENNReal) * (bp : ENNReal))⁻¹
      = (bp : ENNReal) / (ap : ENNReal) := by
    calc
      (bp : ENNReal) ^ 2 * ((ap : ENNReal) * (bp : ENNReal))⁻¹
          = ((bp : ENNReal) * (bp : ENNReal)) * ((ap : ENNReal) * (bp : ENNReal))⁻¹ := by
            rw [pow_two]
      _ = ((bp : ENNReal) * (bp : ENNReal)) * ((ap : ENNReal)⁻¹ * (bp : ENNReal)⁻¹) := by
            rw [ENNReal.mul_inv (Or.inl hA0) (Or.inr hB0)]
      _ = ((bp : ENNReal) * (bp : ENNReal)⁻¹) * ((bp : ENNReal) * (ap : ENNReal)⁻¹) := by
            ring
      _ = 1 * ((bp : ENNReal) * (ap : ENNReal)⁻¹) := by
            rw [ENNReal.mul_inv_cancel hB0 hBtop]
      _ = (bp : ENNReal) * (ap : ENNReal)⁻¹ := by
            rw [one_mul]
      _ = (bp : ENNReal) / (ap : ENNReal) := by
            rfl
  calc
    2 * (plankPigeonhole.C_vol : ENNReal) * ((ap : ENNReal) * (bp : ENNReal))⁻¹ * v
      ≤ 2 * (plankPigeonhole.C_vol : ENNReal) * ((ap : ENNReal) * (bp : ENNReal))⁻¹
        * ((Tube.volume_le.C 3 : ENNReal) * (plankPigeonhole.C : ENNReal) ^ 2
          * (Real.toNNReal (plankTubeParents.C 3) : ENNReal) ^ 3 * (bp : ENNReal) ^ 2) := by
        gcongr
    _ = (2 * ((Tube.volume_le.C 3 : ENNReal) * (plankPigeonhole.C_vol : ENNReal)
          * (plankPigeonhole.C : ENNReal) ^ 2
              * (Real.toNNReal (plankTubeParents.C 3) : ENNReal) ^ 3))
          * ((bp : ENNReal) ^ 2 * ((ap : ENNReal) * (bp : ENNReal))⁻¹) := by
        ring
    _ = 2 * (fibreMassShare.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) := by
        rw [← hC, hB2]
    _ ≤ 2 * (fibreMassShare.C : ENNReal) * (δt : ENNReal) ^ (-ap') := by
        gcongr

/-- **The fibre's density is bounded by its own mass** (steps 2, 3 and 4 of the module
docstring, collected).

For **any** test body `K`, the density of the `p_b`-fibre over `l` inside `K` is at most
`2 C^vol (a_p b_p)⁻¹` times the *fibre's* mass.  This is where the block count cancels: the
fibre is a disjoint union of whole plank blocks (`Kakeya.ml1Boot.exists_blocks_fibre`), the
density splits along that partition (`Kakeya.ml1Boot.densityIn_eq_sum_blocks`), each block
contributes its own mass at the shared factor
(`Kakeya.ml1Boot.densityIn_part_le_of_volume_convexHull_ge`, whose volume hypothesis is clause
(iv) of the plank dimensions via
`Kakeya.ml1Boot.volume_bounds_of_isPlankOfDimensions_vol`), and summing the block masses
recovers the fibre's mass with no count of blocks left over.

Nothing about the ambient body enters, and `hnosplit` is the `l`-specialisation of the no-split
clause exported by `Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct`. -/
theorem densityIn_fibre_le_mul_sum (hdim : Module.finrank ℝ E = 3)
    {δt ap bp : NNReal} (hap : 0 < ap) (hbp : 0 < bp)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (pρ : ι → κ)
    (hu'' : u'' ⊆ u) (hmapsTo : ∀ i ∈ u, pρ i ∈ tρ)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hparts : ∀ m ∈ tρ, ∀ part ∈ (F m).parts, part.Nonempty)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)))
    (pb : ι → κ × Finset ι) (l : κ × Finset ι)
    (hnosplit : ∀ j' ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)),
      ∀ k ∈ j'.2, pb k = l → j'.2 ⊆ fibre u'' pb l)
    (K : ConvexSpaceBody E) :
    densityIn (fibre u'' pb l) (fun i => (T i).toConvexSpaceBody) K
      ≤ 2 * (plankPigeonhole.C_vol : ENNReal) * ((ap : ENNReal) * (bp : ENNReal))⁻¹
        * ∑ i ∈ fibre u'' pb l, volume ((T i).toConvexSpaceBody).carrier := by
  classical
  obtain ⟨Bl, hBl, hsum⟩ := exists_blocks_fibre T pρ hu'' hmapsTo F hparts pb l hnosplit
  have hCvol : 0 < plankPigeonhole.C_vol := by
    dsimp [plankPigeonhole.C_vol]
    positivity
  have hblock : ∀ j ∈ Bl,
      densityIn j.2 (fun i ↦ (T i).toConvexSpaceBody) K ≤
        2 * (plankPigeonhole.C_vol : ENNReal) * ((ap : ENNReal) * (bp : ENNReal))⁻¹
          * ∑ i ∈ j.2, volume (T i).carrier := by
    intro j hj
    have hW : IsPlankOfDimensions plankPigeonhole.C ap bp
        (j.2.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)) :=
      hdims j.1 (hBl j hj).1 j.2 (hBl j hj).2
    have hlo : (plankPigeonhole.C_vol : ENNReal)⁻¹ * (ap : ENNReal) * (bp : ENNReal)
        ≤ volume (j.2.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier :=
      (volume_bounds_of_isPlankOfDimensions_vol hdim hW).1
    exact densityIn_part_le_of_volume_convexHull_ge (F := F j.1) (t := j.2)
      (ht := (hBl j hj).2) hCvol hap hbp (hlo := hlo) K
  calc
    densityIn (fibre u'' pb l) (fun i ↦ (T i).toConvexSpaceBody) K
        = ∑ j ∈ Bl, densityIn j.2 (fun i ↦ (T i).toConvexSpaceBody) K := by
          exact densityIn_eq_sum_blocks (V := fun i => (T i).toConvexSpaceBody) hsum K
    _ ≤ ∑ j ∈ Bl, (2 * (plankPigeonhole.C_vol : ENNReal) * ((ap : ENNReal) * (bp : ENNReal))⁻¹
        * ∑ i ∈ j.2, volume (T i).carrier) := Finset.sum_le_sum hblock
    _ = 2 * (plankPigeonhole.C_vol : ENNReal) * ((ap : ENNReal) * (bp : ENNReal))⁻¹
        * ∑ j ∈ Bl, ∑ i ∈ j.2, volume (T i).carrier := by
          rw [← Finset.mul_sum]
    _ = 2 * (plankPigeonhole.C_vol : ENNReal) * ((ap : ENNReal) * (bp : ENNReal))⁻¹
        * ∑ i ∈ fibre u'' pb l, volume (T i).carrier := by
          rw [← hsum (fun i => volume (T i).carrier)]

/-- **The volume of the fibre's hull** (step 5 of the module docstring, collected).

The hull of the fibre lies in the `c`-dilate of its parent `b`-tube
(`Kakeya.ml1Boot.convexHull_biUnion_fibre_le_parent_dilate`), whose volume
`Kakeya.ml1Boot.volume_dilate_le_of_dim_three` bounds by `c ³ C_{volume_le}(3) (C_𝕎 b_p) ²`.
Expanding the square of the plank-tube scale puts it in exactly the shape
`Kakeya.ml1Boot.massShare_const_le` consumes.

`hbq1` is where `Kakeya.Tube.volume_le`'s thickness restriction is discharged. -/
theorem volume_convexHull_biUnion_fibre_le [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt bp : NNReal} (hbq1 : plankPigeonhole.C * bp ≤ 1)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u'' : Finset ι}
    {tb : Finset (κ × Finset ι)}
    (T : ι → Tube δt E) (Tb : κ × Finset ι → Tube (plankPigeonhole.C * bp) E)
    (pb : ι → κ × Finset ι)
    (hpf : IsParentFamilyDilate (plankTubeParents.C 3) u'' T tb Tb pb)
    {l : κ × Finset ι} (hne : (fibre u'' pb l).Nonempty) :
    volume ((fibre u'' pb l).convexHull_biUnion
          (fun i => (T i).toConvexSpaceBody)).carrier
      ≤ (Tube.volume_le.C 3 : ENNReal) * (plankPigeonhole.C : ENNReal) ^ 2
        * (Real.toNNReal (plankTubeParents.C 3) : ENNReal) ^ 3 * (bp : ENNReal) ^ 2 := by
  have hc : 1 < (plankTubeParents.C 3 : ℝ) := by
    have h1 : (1 : ℝ) ≤ Tube.tubeOverlapCoreClose.C 3 :=
      (Tube.tubeOverlapCoreClose.one_lt_C 3).le
    have hpos : (0 : ℝ) ≤ Tube.tubeOverlapCoreClose.C 3 := by linarith
    have hsq1 : (1 : ℝ) ≤ Tube.tubeOverlapCoreClose.C 3 ^ 2 := by
      nlinarith [mul_le_mul h1 h1 (by norm_num : (0 : ℝ) ≤ 1) hpos]
    dsimp [plankTubeParents.C]
    nlinarith [hsq1]
  have hleq : ((fibre u'' pb l).convexHull_biUnion (fun i => (T i).toConvexSpaceBody))
      ≤ Tube.dilate (Tb l) (plankTubeParents.C 3) := by
    exact convexHull_biUnion_fibre_le_parent_dilate T Tb pb hpf hne
  have hmono : volume ((fibre u'' pb l).convexHull_biUnion
          (fun i => (T i).toConvexSpaceBody)).carrier
      ≤ volume (Tube.dilate (Tb l) (plankTubeParents.C 3)).carrier :=
    measure_mono (SetLike.le_def.mp hleq)
  have hvd : volume (Tube.dilate (Tb l) (plankTubeParents.C 3)).carrier
      ≤ (Real.toNNReal (plankTubeParents.C 3) : ENNReal) ^ 3 * (Tube.volume_le.C 3 : ENNReal)
        * ((plankPigeonhole.C * bp : NNReal) : ENNReal) ^ 2 := by
    exact volume_dilate_le_of_dim_three hdim hbq1 hc (Tb l)
  calc
    volume ((fibre u'' pb l).convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier
        ≤ volume (Tube.dilate (Tb l) (plankTubeParents.C 3)).carrier := hmono
    _ ≤ (Real.toNNReal (plankTubeParents.C 3) : ENNReal) ^ 3 * (Tube.volume_le.C 3 : ENNReal)
        * ((plankPigeonhole.C * bp : NNReal) : ENNReal) ^ 2 := hvd
    _ = (Tube.volume_le.C 3 : ENNReal) * (plankPigeonhole.C : ENNReal) ^ 2
        * (Real.toNNReal (plankTubeParents.C 3) : ENNReal) ^ 3 * (bp : ENNReal) ^ 2 := by
        rw [ENNReal.coe_mul]
        rw [mul_pow]
        ring

/-- **(GWZ Lemma 8.1, coarse endgame) The fibre Frostman bound at the fibre's own hull**
(the hull form; a *different* statement from blueprint `lem:ml1bootFibreMassShare`, which is at
the dilated tube and carries the extra factors `|t_ρ| b_p/a_p`.  The hull form has no blueprint
environment yet; see the module docstring and `Kakeya.ml1Boot.fibreMassShare.C`).

This is hypothesis (a) of `Kakeya.ml1Boot.normalized_le_of_coarse_dilate` at the ambient family
`K_b l = hull (fibre u'' p_b l)`, so that the coarse endgame consumes it by substitution.  The
two side conditions the `K_b` parameter carries are free at this body:
`hull (fibre u'' p_b l) ≤ c · T_{b,l}` is the `le_parent_dilate` field of `hpf`, and
`T̃ i ≤ hull (fibre u'' p_b l)` for `p_b i = l` is `Finset.le_convexHull_biUnion`.

**The ρ-parent hypothesis is a bare `mapsTo`, and that is the whole of ledger item (3).**  This
statement used to hypothesise the *undilated* `Kakeya.ml1Boot.IsParentFamily u T tρ Tρ pρ`
together with `hbρ : bp ≤ ρ`, `hρ1 : ρ ≤ 1`, `hap' : 0 ≤ ap'`, `hball` and `htbs` — "written
exactly as `Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct` exports it", i.e. as the
*undilated* `b`-tube producer the coarse route has since stopped using.  That made it unusable at
its only consumer: `Kakeya.ml1Boot.multTildeT_of_planksClose` carries
`Kakeya.ml1Boot.IsParentFamilyDilate 2` and **cannot** carry `IsParentFamily`, because its only
ρ-parent producer, `Kakeya.ml1Boot.exists_parentFamilyDilate_atSixEps_card` (KatzTao.lean:1305),
places a leaf in the `19/16`-rescale of its representative and not in the representative.

The mismatch was an artefact, not mathematics.  In the 41-line proof body below `hparent`
occurred **exactly once**, as `hparent.mapsTo`, and `hbρ`, `hρ1`, `hap'`, `hball`, `htbs`
occurred **not at all** — certified by the compiler's own `unusedVariables` linter, which flagged
all five on the pre-trim statement.  So the ρ-parent bundle, and with it the family `Tρ` and the
scale `ρ` themselves, were read only through `∀ i ∈ u, pρ i ∈ tρ`.  That is what is hypothesised
now; the proof body is unchanged apart from `hparent.mapsTo ↦ hmapsTo`.  This matches
`Kakeya.ml1Boot.volume_dilate_le_mul_volume_fibre_convexHull` below, the `M`-half of the very
same seam, which already took its parent hypothesis as a bare `hmapsTo`.  The corollary at
`Kakeya.ml1Boot.IsParentFamilyDilate` is
`Kakeya.ml1Boot.frostmanConstIn_fibre_convexHull_le_dilate`, and the `example` beside it recovers
the pre-trim statement binder for binder, so nothing is lost.

`hratio` is the planks-close hypothesis of `Kakeya.ml1Boot.multTildeT_of_planksClose` in the
form the width ratio is used in, at the exponent `a'_p` that
`Kakeya.ml1Boot.normalized_le_of_coarse_dilate` pins by `γ a'_p = 10 a / ε`.

`hbq1` is the plank-tube scale bound, hypothesised for the same reason
`Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct` (CoarseDensity.lean:1543)
hypothesises it: `Kakeya.Tube.volume_le` reads tubes of thickness at most `1`, and the parent
tubes here have thickness `C_𝕎 b_p`.  It is therefore free at every call site of that producer.

**This declaration is proved**, by the five-step route of the module docstring at the constant
`Kakeya.ml1Boot.fibreMassShare.C`, which is the constant that route delivers; the numeral
question that earlier versions left open has been settled there, against the consumer's
`2 C_T`.  The route is assembled from `Kakeya.ml1Boot.densityIn_fibre_le_mul_sum` (steps 2-4)
and `Kakeya.ml1Boot.volume_convexHull_biUnion_fibre_le` (step 5), with step 1 free by
`Kakeya.ml1Boot.familyIn_convexHull_biUnion_self`.  Since `Kakeya.ml1Boot.IsParentFamilyDilate`
carries no surjectivity, `hl` does not make the fibre nonempty and the empty fibre is handled
separately, where the Frostman constant is `0`. -/
theorem frostmanConstIn_fibre_convexHull_le [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp : NNReal} (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp)
    (hbq1 : plankPigeonhole.C * bp ≤ 1)
    {ap' : ℝ}
    (hratio : (bp : ENNReal) / (ap : ENNReal) ≤ (δt : ENNReal) ^ (-ap'))
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (pρ : ι → κ)
    (hu'' : u'' ⊆ u)
    (hmapsTo : ∀ i ∈ u, pρ i ∈ tρ)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hparts : ∀ m ∈ tρ, ∀ part ∈ (F m).parts, part.Nonempty)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)))
    {tb : Finset (κ × Finset ι)} (Tb : κ × Finset ι → Tube (plankPigeonhole.C * bp) E)
    (pb : ι → κ × Finset ι)
    (hpf : IsParentFamilyDilate (plankTubeParents.C 3) u'' T tb Tb pb)
    (hnosplit : ∀ j ∈ tb, ∀ j' ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)),
      ∀ k ∈ j'.2, pb k = j → j'.2 ⊆ fibre u'' pb j)
    {l : κ × Finset ι} (hl : l ∈ tb) :
    frostmanConstIn (fibre u'' pb l) (fun i => (T i).toConvexSpaceBody)
        ((fibre u'' pb l).convexHull_biUnion (fun i => (T i).toConvexSpaceBody))
      ≤ 2 * (fibreMassShare.C : ENNReal) * (δt : ENNReal) ^ (-ap') := by
  let s : Finset ι := fibre u'' pb l
  let V : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody
  let B : ConvexSpaceBody E := s.convexHull_biUnion V
  let D : ENNReal := 2 * (plankPigeonhole.C_vol : ENNReal) * ((ap : ENNReal) * (bp : ENNReal))⁻¹
  let Cst : ENNReal := 2 * (fibreMassShare.C : ENNReal) * (δt : ENNReal) ^ (-ap')
  change frostmanConstIn s V B ≤ Cst
  by_cases hs : s.Nonempty
  · rcases hs with ⟨i₀, hi₀⟩
    have hap : 0 < ap := lt_of_lt_of_le hδt hδa
    have hbp : 0 < bp := lt_of_lt_of_le hap hab
    have hvol := volume_convexHull_biUnion_fibre_le hdim hbq1 T Tb pb hpf ⟨i₀, hi₀⟩
    have hD : D * volume B.carrier ≤ Cst :=
      massShare_const_le hap hbp hratio (v := volume B.carrier) hvol
    have hBtop : volume B.carrier ≠ ⊤ := B.isCompact.measure_ne_top
    have hle := Tube.le_volume (T i₀)
    have hle3 : (Tube.le_volume.c 3 : ENNReal) * (δt : ENNReal) ^ 2 ≤ volume (T i₀).carrier := by
      rw [hdim, show (3 : ℕ) - 1 = 2 by rfl] at hle
      exact hle
    have hc3n : (0 : NNReal) < Tube.le_volume.c 3 := Tube.le_volume.c_pos 3
    have hpos_lb : (0 : ENNReal) < (Tube.le_volume.c 3 : ENNReal) * (δt : ENNReal) ^ 2 := by
      have hN : 0 < (Tube.le_volume.c 3 : NNReal) * δt ^ 2 := by
        positivity
      rw [← ENNReal.coe_pow, ← ENNReal.coe_mul]
      exact_mod_cast hN
    have hgt0 : (0 : ENNReal) < volume (T i₀).carrier := lt_of_lt_of_le hpos_lb hle3
    have h₀ : volume (V i₀).carrier ≠ 0 := ne_of_gt hgt0
    have hB0 : volume B.carrier ≠ 0 := volume_convexHull_biUnion_ne_zero V hi₀ h₀
    have hall : ∀ i ∈ s, V i ≤ B := fun i hi => Finset.le_convexHull_biUnion V hi
    have hdens : ∀ K : ConvexSpaceBody E, K ≤ B →
        densityIn s V K ≤ Cst * densityIn s V B := by
      intro K hK
      have hK' : densityIn s V K ≤ D * ∑ i ∈ s, volume (V i).carrier :=
        densityIn_fibre_le_mul_sum hdim hap hbp T pρ hu'' hmapsTo F hparts hdims pb l
          (hnosplit l hl) K
      exact densityIn_le_mul_densityIn_of_le_mul_sum V hall hB0 hBtop hD hK'
    rw [← familyIn_convexHull_biUnion_self s V]
    exact frostmanConstIn_le_of_density_le (s := s) V B hdens
  · have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hs_empty]
    rw [frostmanConstIn_empty]
    exact bot_le

/-! **The trim of `Kakeya.ml1Boot.frostmanConstIn_fibre_convexHull_le` loses nothing.**

The statement below is the pre-trim one, binder for binder — the undilated
`Kakeya.ml1Boot.IsParentFamily` with `hbρ`, `hρ1`, `hap'`, `hball` and `htbs` — and it is proved
by one application of the trimmed form.  It is an `example` because it has no consumer and must
not become a second API entry point; it is here as the machine-checked no-loss certificate for
the trim recorded in that declaration's docstring.  The five `unusedVariables` warnings it
raises are the point of it, so the linter is switched off over it. -/

set_option linter.unusedVariables false in
example [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp ρ : NNReal} (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp) (hbρ : bp ≤ ρ)
    (hρ1 : ρ ≤ 1) (hbq1 : plankPigeonhole.C * bp ≤ 1)
    {ap' : ℝ} (hap' : 0 ≤ ap')
    (hratio : (bp : ENNReal) / (ap : ENNReal) ≤ (δt : ENNReal) ^ (-ap'))
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (hu'' : u'' ⊆ u)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamily u T tρ Tρ pρ)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hparts : ∀ m ∈ tρ, ∀ part ∈ (F m).parts, part.Nonempty)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)))
    {tb : Finset (κ × Finset ι)} (Tb : κ × Finset ι → Tube (plankPigeonhole.C * bp) E)
    (pb : ι → κ × Finset ι)
    (htbs : tb ⊆ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)))
    (hpf : IsParentFamilyDilate (plankTubeParents.C 3) u'' T tb Tb pb)
    (hnosplit : ∀ j ∈ tb, ∀ j' ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)),
      ∀ k ∈ j'.2, pb k = j → j'.2 ⊆ fibre u'' pb j)
    {l : κ × Finset ι} (hl : l ∈ tb) :
    frostmanConstIn (fibre u'' pb l) (fun i => (T i).toConvexSpaceBody)
        ((fibre u'' pb l).convexHull_biUnion (fun i => (T i).toConvexSpaceBody))
      ≤ 2 * (fibreMassShare.C : ENNReal) * (δt : ENNReal) ^ (-ap') :=
  frostmanConstIn_fibre_convexHull_le hdim hδt hδa hab hbq1 hratio T pρ hu''
    hparent.mapsTo F hparts hdims Tb pb hpf hnosplit hl

/-- **Item (3)'s lemma at the dilated ρ-parent — the shape the coarse endgame holds.**

`Kakeya.ml1Boot.multTildeT_of_planksClose` carries `Kakeya.ml1Boot.IsParentFamilyDilate 2` and
**cannot** carry `Kakeya.ml1Boot.IsParentFamily`: its only ρ-parent producer,
`Kakeya.ml1Boot.exists_parentFamilyDilate_atSixEps_card` (KatzTao.lean:1305), places a leaf in
the `19/16`-rescale of its representative, not in the representative.  This is
`Kakeya.ml1Boot.frostmanConstIn_fibre_convexHull_le` at every ratio `c`; the `c` is never read,
only the `mapsTo` field that `IsParentFamilyDilate` shares with `IsParentFamily`. -/
theorem frostmanConstIn_fibre_convexHull_le_dilate [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3)
    {δt ap bp ρ : NNReal} {c : ℝ} (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp)
    (hbq1 : plankPigeonhole.C * bp ≤ 1)
    {ap' : ℝ}
    (hratio : (bp : ENNReal) / (ap : ENNReal) ≤ (δt : ENNReal) ^ (-ap'))
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (hu'' : u'' ⊆ u)
    (hparent : IsParentFamilyDilate c u T tρ Tρ pρ)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hparts : ∀ m ∈ tρ, ∀ part ∈ (F m).parts, part.Nonempty)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)))
    {tb : Finset (κ × Finset ι)} (Tb : κ × Finset ι → Tube (plankPigeonhole.C * bp) E)
    (pb : ι → κ × Finset ι)
    (hpf : IsParentFamilyDilate (plankTubeParents.C 3) u'' T tb Tb pb)
    (hnosplit : ∀ j ∈ tb, ∀ j' ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)),
      ∀ k ∈ j'.2, pb k = j → j'.2 ⊆ fibre u'' pb j)
    {l : κ × Finset ι} (hl : l ∈ tb) :
    frostmanConstIn (fibre u'' pb l) (fun i => (T i).toConvexSpaceBody)
        ((fibre u'' pb l).convexHull_biUnion (fun i => (T i).toConvexSpaceBody))
      ≤ 2 * (fibreMassShare.C : ENNReal) * (δt : ENNReal) ^ (-ap') :=
  frostmanConstIn_fibre_convexHull_le hdim hδt hδa hab hbq1 hratio T pρ hu''
    hparent.mapsTo F hparts hdims Tb pb hpf hnosplit hl
/-! ### The two pieces the coarse seam needs to instantiate its free constants

`Kakeya.ml1Boot.normalized_le_of_coarse_dilate` is stated over a free constant `CF` with side
condition `C_T ≤ CF`, and over a free `M` bounding the dilated `b`-tube against the caller's
ambient body.  Instantiating it at `CF := fibreMassShare.C` and the ambient body at the fibre's
own hull needs exactly the two comparisons below. -/

/-- **The parent-dilation ratio in `ℝ³` is at least `486`.**

`Kakeya.ml1Boot.plankTubeParents.C n = 6 C_ov(n) ²` with
`C_ov(n) = 9 + 2 · 4 ⁿ / c_{le_volume}(n)`, and `Kakeya.Tube.le_volume.c_pos` makes the second
summand strictly positive, so `C_ov(3) > 9` and the ratio exceeds `6 · 81 = 486`.  Only
positivity of `c_{le_volume}(3)` is used: the transcendental value `4 π / 9` is never needed,
which is what keeps the constant comparison
`Kakeya.ml1Boot.densityTransfer_C_le_fibreMassShare_C` elementary. -/
theorem le_plankTubeParents_C_three : (486 : ℝ) ≤ plankTubeParents.C 3 := by
  have h9 : (9 : ℝ) ≤ Tube.tubeOverlapCoreClose.C 3 := by
    have hK : (0 : ℝ) ≤ 2 * 4 ^ 3 / (Tube.le_volume.c 3 : ℝ) := by positivity
    unfold Tube.tubeOverlapCoreClose.C
    linarith
  have hpos : (0 : ℝ) ≤ Tube.tubeOverlapCoreClose.C 3 := by linarith
  have hsq : (81 : ℝ) ≤ Tube.tubeOverlapCoreClose.C 3 ^ 2 := by
    nlinarith [mul_le_mul h9 h9 (by norm_num : (0 : ℝ) ≤ 9) hpos]
  dsimp [plankTubeParents.C]
  nlinarith [hsq]

/-- **The coarse seam's budget is dominated by the hull route's constant.**

`C_{lem:ml1bootDensityTransfer} ≤ C_{lem:ml1bootFibreMassShareAtHull}`, the ordering asserted in
the module docstring of `Kakeya.ml1Boot.fibreMassShare.C` and the side condition
`densityTransfer.C ≤ CF` that `Kakeya.ml1Boot.normalized_le_of_coarse_dilate` carries, so that
the coarse endgame may be read at `CF := Kakeya.ml1Boot.fibreMassShare.C`.

Expanding both sides against `V = Metric.volume_comparison.C 3` and `C_𝕎 = 16 V`,
`densityTransfer.C = 256 C_𝕎 ⁶ V` and `fibreMassShare.C = 128 C_𝕎 ⁵ V c ³` at
`c = plankTubeParents.C 3`, so the claim is exactly `2 C_𝕎 ≤ c ³`.  With `V = 4 ³ · 3! = 384`
the left side is `12288`, and `Kakeya.ml1Boot.le_plankTubeParents_C_three` makes the right side
at least `486 ³`. -/
theorem densityTransfer_C_le_fibreMassShare_C :
    densityTransfer.C ≤ fibreMassShare.C := by
  -- The `486` bound, self-contained: only positivity of `Tube.le_volume.c 3` is used.
  have hcpos : (0 : ℝ) < (Tube.le_volume.c 3 : ℝ) := by exact_mod_cast Tube.le_volume.c_pos 3
  have h9 : (9 : ℝ) ≤ Tube.tubeOverlapCoreClose.C 3 := by
    have hK : (0 : ℝ) < 2 * 4 ^ 3 / (Tube.le_volume.c 3 : ℝ) := by positivity
    unfold Tube.tubeOverlapCoreClose.C
    linarith
  have h486 : (486 : ℝ) ≤ plankTubeParents.C 3 := by
    have hpos : (0 : ℝ) ≤ Tube.tubeOverlapCoreClose.C 3 := by linarith
    have hsq : (81 : ℝ) ≤ Tube.tubeOverlapCoreClose.C 3 ^ 2 := by
      nlinarith [mul_le_mul h9 h9 (by norm_num : (0 : ℝ) ≤ 9) hpos]
    dsimp [plankTubeParents.C]
    nlinarith [hsq]
  -- Transfer to `NNReal` and cube.
  have h486nn : (486 : NNReal) ≤ Real.toNNReal (plankTubeParents.C 3) := by
    have hc0 : (0 : ℝ) ≤ plankTubeParents.C 3 := le_trans (by norm_num) h486
    have hcast : (Real.toNNReal (plankTubeParents.C 3) : ℝ) = plankTubeParents.C 3 := by
      rw [Real.toNNReal_of_nonneg hc0]
      rfl
    have : (486 : ℝ) ≤ (Real.toNNReal (plankTubeParents.C 3) : ℝ) := by
      rw [hcast]
      exact h486
    exact_mod_cast this
  have hc3 : (12288 : NNReal) ≤ Real.toNNReal (plankTubeParents.C 3) ^ 3 := by
    have hpow : (486 : NNReal) ^ 3 ≤ Real.toNNReal (plankTubeParents.C 3) ^ 3 := by
      exact pow_le_pow_left₀ (by norm_num : (0 : NNReal) ≤ 486) h486nn 3
    have h486c : (12288 : NNReal) ≤ (486 : NNReal) ^ 3 := by norm_num
    exact le_trans h486c hpow
  -- The volume-comparison normalization: `Metric.volume_comparison.C 3 = 384`.
  have hV : Metric.volume_comparison.C 3 = 384 := by
    have hCval : (Metric.volume_comparison.C 3 : ℝ) = (4 : ℝ) ^ 3 * (Nat.factorial 3 : ℝ) := by
      dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
      push_cast
      field_simp
    apply NNReal.coe_injective
    rw [hCval]
    norm_num
  -- Cast the whole inequality to ℝ and compute.
  rw [← NNReal.coe_le_coe]
  have hc3r : (12288 : ℝ) ≤ (Real.toNNReal (plankTubeParents.C 3) : ℝ) ^ 3 := by
    simpa using (NNReal.coe_le_coe.mpr hc3)
  calc
    (densityTransfer.C : ℝ) = 256 * (16 * 384) ^ 6 * 384 := by
      simp only [densityTransfer.C, plankInTube.C, plankPigeonhole.C]
      rw [hV]
      push_cast
      rfl
    _ = 128 * (16 * 384) ^ 5 * 384 * 12288 := by ring
    _ ≤ 128 * (16 * 384) ^ 5 * 384 * (Real.toNNReal (plankTubeParents.C 3) : ℝ) ^ 3 := by
      have hpos : (0 : ℝ) ≤ 128 * (16 * 384) ^ 5 * 384 := by positivity
      exact mul_le_mul_of_nonneg_left hc3r hpos
    _ = 16 * (8 * (16 * 384) ^ 3 * 384) * (16 * 384) ^ 2
        * (Real.toNNReal (plankTubeParents.C 3) : ℝ) ^ 3 := by ring
    _ = (fibreMassShare.C : ℝ) := by
      simp only [fibreMassShare.C, plankPigeonhole.C_vol, plankPigeonhole.C, Tube.volume_le.C]
      rw [hV]
      push_cast
      ring

/-- **A plank block sitting inside the fibre** (the containment the lower volume bound needs).

`Kakeya.ml1Boot.exists_blocks_fibre` exhibits the fibre as a union of whole blocks but does not
export the containment of an individual block, which is what transfers a *lower* bound from a
block's hull up to the fibre's hull.  Picking any `i₀` in the fibre and taking `j` to be its own
block gives one directly: `hnosplit` applied at `i₀` says the whole block is caught by the
fibre, and `i₀ ∈ j.2` makes the block nonempty.

The reverse containment is false and is not attempted: `p_b` merges indices whose parent bodies
coincide, so a `p_b`-fibre generally meets many blocks. -/
theorem exists_block_subset_fibre {δt : NNReal}
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (pρ : ι → κ)
    (hu'' : u'' ⊆ u) (hmapsTo : ∀ i ∈ u, pρ i ∈ tρ)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hparts : ∀ m ∈ tρ, ∀ part ∈ (F m).parts, part.Nonempty)
    (pb : ι → κ × Finset ι) (l : κ × Finset ι)
    (hnosplit : ∀ j' ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)),
      ∀ k ∈ j'.2, pb k = l → j'.2 ⊆ fibre u'' pb l)
    (hne : (fibre u'' pb l).Nonempty) :
    ∃ j : κ × Finset ι, j.1 ∈ tρ ∧ j.2 ∈ (F j.1).parts ∧ j.2.Nonempty ∧
      j.2 ⊆ fibre u'' pb l := by
  classical
  rcases hne with ⟨i₀, hi₀⟩
  have hi₀u : i₀ ∈ u'' := (Finset.mem_filter.mp hi₀).1
  have hpb : pb i₀ = l := (Finset.mem_filter.mp hi₀).2
  obtain ⟨q, hq1, hq2, hq3, hq4⟩ := plankBlocks_partition T pρ hu'' hmapsTo F hparts
  have hjin : q i₀ ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)) :=
    hq2 i₀ hi₀u
  refine ⟨q i₀, ?_, ?_, ?_, ?_⟩
  · rcases Finset.mem_biUnion.mp hjin with ⟨m, hmtρ, hmem⟩
    rcases Finset.mem_image.mp hmem with ⟨part, hpartmem, hjeq⟩
    rw [← congrArg Prod.fst hjeq]
    exact hmtρ
  · rcases Finset.mem_biUnion.mp hjin with ⟨m, hmtρ, hmem⟩
    rcases Finset.mem_image.mp hmem with ⟨part, hpartmem, hjeq⟩
    rw [← congrArg Prod.snd hjeq]
    rw [← congrArg Prod.fst hjeq]
    exact hpartmem
  · exact ⟨i₀, (hq1 i₀ hi₀u).2.2⟩
  · exact hnosplit (q i₀) hjin i₀ ((hq1 i₀ hi₀u).2.2) hpb

/-- **The fibre's hull has at least a plank's volume** (the lower half of the `M` clause).

The left conjunct of `Kakeya.ml1Boot.volume_bounds_of_isPlankOfDimensions_vol` bounds a *block*
hull below by `C^vol⁻¹ a_p b_p`, reading only the plank hypothesis of `hdims`.  A block sits
inside the fibre (`Kakeya.ml1Boot.exists_block_subset_fibre`), so its hull sits inside the
fibre's hull by `Finset.Nonempty.convexHull_biUnion_le_iff` against
`Finset.le_convexHull_biUnion`, and the bound transfers up by monotonicity of the measure.

This `C^vol` is exactly the `C^vol` factor inside `Kakeya.ml1Boot.fibreMassShare.C`: the upper
bound `Kakeya.ml1Boot.volume_convexHull_biUnion_fibre_le` carries none, so the two meet with no
slack. -/
theorem volume_convexHull_biUnion_fibre_ge (hdim : Module.finrank ℝ E = 3)
    {δt ap bp : NNReal}
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (pρ : ι → κ)
    (hu'' : u'' ⊆ u) (hmapsTo : ∀ i ∈ u, pρ i ∈ tρ)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hparts : ∀ m ∈ tρ, ∀ part ∈ (F m).parts, part.Nonempty)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)))
    (pb : ι → κ × Finset ι) (l : κ × Finset ι)
    (hnosplit : ∀ j' ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)),
      ∀ k ∈ j'.2, pb k = l → j'.2 ⊆ fibre u'' pb l)
    (hne : (fibre u'' pb l).Nonempty) :
    (plankPigeonhole.C_vol : ENNReal)⁻¹ * (ap : ENNReal) * (bp : ENNReal)
      ≤ volume ((fibre u'' pb l).convexHull_biUnion
          (fun i => (T i).toConvexSpaceBody)).carrier := by
  classical
  obtain ⟨j, hj1, hj2, hjne, hjsub⟩ :=
    exists_block_subset_fibre T pρ hu'' hmapsTo F hparts pb l hnosplit hne
  have hW : IsPlankOfDimensions plankPigeonhole.C ap bp
      (j.2.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)) :=
    hdims j.1 hj1 j.2 hj2
  have hlo : (plankPigeonhole.C_vol : ENNReal)⁻¹ * (ap : ENNReal) * (bp : ENNReal)
      ≤ volume (j.2.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier :=
    (volume_bounds_of_isPlankOfDimensions_vol hdim hW).1
  have hmono : (j.2.convexHull_biUnion (fun i => (T i).toConvexSpaceBody))
      ≤ ((fibre u'' pb l).convexHull_biUnion (fun i => (T i).toConvexSpaceBody)) :=
    (Finset.Nonempty.convexHull_biUnion_le_iff hjne
      (fun i => (T i).toConvexSpaceBody)
      ((fibre u'' pb l).convexHull_biUnion (fun i => (T i).toConvexSpaceBody))).mpr
      (fun i hi => Finset.le_convexHull_biUnion (fun i => (T i).toConvexSpaceBody) (hjsub hi))
  have hmonoVol : volume (j.2.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier
      ≤ volume ((fibre u'' pb l).convexHull_biUnion
          (fun i => (T i).toConvexSpaceBody)).carrier :=
    measure_mono (SetLike.le_def.mp hmono)
  exact le_trans hlo hmonoVol

/-- **The `M` clause of the coarse seam, at the fibre's own hull.**

`Kakeya.ml1Boot.normalized_le_of_coarse_dilate` carries, per `b`-tube index `l`, a clause
`|c · T_{b,l}| ≤ M |K_{b,l}|`.  At the ambient body
`K_{b,l} = hull (fibre u'' p_b l)` — the body at which
`Kakeya.ml1Boot.frostmanConstIn_fibre_convexHull_le` produces hypothesis (a) — it holds at
`M = C_{lem:ml1bootFibreMassShareAtHull} b_p / a_p`.

The clause exists because generalizing the ambient body with only an upper bound is unsound:
`Kakeya.frostmanConstIn` divides by `|K|` (Density.lean:45-46, Frostman.lean:30-31), so an
ambient body allowed to shrink with `δ̃` makes the seam false.  `M` bounds that shrinkage.

The two halves are already available: `Kakeya.ml1Boot.volume_dilate_le_of_dim_three` bounds the
dilate above by `c ³ C_{volume_le}(3) (C_𝕎 b_p) ² = (C/C^vol) b_p ²`, and
`Kakeya.ml1Boot.volume_convexHull_biUnion_fibre_ge` bounds the hull below by
`C^vol⁻¹ a_p b_p`; their quotient is `C (b_p / a_p)` with the `C^vol` cancelling exactly.  Both
sides carry `b_p ²` against `a_p b_p`, leaving exactly one power of the width ratio and no power
of `δ̃`, which is the check that the factor is placed rather than merely large.

`M` does not mention `l`: it is uniform over the `b`-tube indices, as the single `M` binder of
the consumer requires.  `hpf` is not needed — the dilate's volume is bounded without reference
to the parent structure. -/
theorem volume_dilate_le_mul_volume_fibre_convexHull [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3)
    {δt ap bp : NNReal} (hap : 0 < ap) (hbp : 0 < bp)
    (hbq1 : plankPigeonhole.C * bp ≤ 1)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (pρ : ι → κ)
    (hu'' : u'' ⊆ u) (hmapsTo : ∀ i ∈ u, pρ i ∈ tρ)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hparts : ∀ m ∈ tρ, ∀ part ∈ (F m).parts, part.Nonempty)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)))
    (Tb : κ × Finset ι → Tube (plankPigeonhole.C * bp) E)
    (pb : ι → κ × Finset ι) (l : κ × Finset ι)
    (hnosplit : ∀ j' ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)),
      ∀ k ∈ j'.2, pb k = l → j'.2 ⊆ fibre u'' pb l)
    (hne : (fibre u'' pb l).Nonempty) :
    volume (Tube.dilate (Tb l) (plankTubeParents.C 3)).carrier
      ≤ ((fibreMassShare.C * bp / ap : NNReal) : ENNReal)
        * volume ((fibre u'' pb l).convexHull_biUnion
            (fun i => (T i).toConvexSpaceBody)).carrier := by
  let A : ENNReal := (Tube.volume_le.C 3 : ENNReal) * (plankPigeonhole.C : ENNReal) ^ 2
    * (Real.toNNReal (plankTubeParents.C 3) : ENNReal) ^ 3
  let M : ENNReal := ((fibreMassShare.C * bp / ap : NNReal) : ENNReal)
  have hap0 : (ap : ENNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt hap)
  have hapTop : (ap : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hbp0 : (bp : ENNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt hbp)
  have hbpTop : (bp : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCvol0 : (plankPigeonhole.C_vol : ENNReal) ≠ 0 := by
    have hpos : 0 < plankPigeonhole.C_vol := by
      dsimp [plankPigeonhole.C_vol]
      positivity
    exact_mod_cast (ne_of_gt hpos)
  have hCvolTop : (plankPigeonhole.C_vol : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hcoef : ((fibreMassShare.C * bp / ap : NNReal) : ENNReal)
      = (fibreMassShare.C : ENNReal) * (bp : ENNReal) / (ap : ENNReal) := by
    rw [ENNReal.coe_div (ne_of_gt hap)]
    rw [ENNReal.coe_mul]
  have hC' : (fibreMassShare.C : ENNReal) = (plankPigeonhole.C_vol : ENNReal) * A := by
    simp [A, fibreMassShare.C, ENNReal.coe_mul, ENNReal.coe_pow]
    ring
  have hM : M * ((plankPigeonhole.C_vol : ENNReal)⁻¹ * (ap : ENNReal) * (bp : ENNReal))
      = A * (bp : ENNReal) ^ 2 := by
    have hM_coef : M = (fibreMassShare.C : ENNReal) * (bp : ENNReal) / (ap : ENNReal) := by
      dsimp [M]
      exact hcoef
    rw [hM_coef]
    rw [div_eq_mul_inv]
    rw [hC']
    calc
      ((plankPigeonhole.C_vol : ENNReal) * A) * (bp : ENNReal) * (ap : ENNReal)⁻¹
          * ((plankPigeonhole.C_vol : ENNReal)⁻¹ * (ap : ENNReal) * (bp : ENNReal))
          = A * ((plankPigeonhole.C_vol : ENNReal) * (plankPigeonhole.C_vol : ENNReal)⁻¹)
              * (ap : ENNReal)⁻¹ * (ap : ENNReal) * (bp : ENNReal) * (bp : ENNReal) := by
              ring
      _ = A * (ap : ENNReal)⁻¹ * (ap : ENNReal) * (bp : ENNReal) * (bp : ENNReal) := by
              rw [ENNReal.mul_inv_cancel hCvol0 hCvolTop]
              rw [mul_one]
      _ = A * ((ap : ENNReal) * (ap : ENNReal)⁻¹) * (bp : ENNReal) * (bp : ENNReal) := by
              ring
      _ = A * (bp : ENNReal) * (bp : ENNReal) := by
              rw [ENNReal.mul_inv_cancel hap0 hapTop]
              rw [mul_one]
      _ = A * (bp : ENNReal) ^ 2 := by
              rw [mul_assoc, ← pow_two]
  have hc : 1 < (plankTubeParents.C 3 : ℝ) := by
    have h1 : (1 : ℝ) ≤ Tube.tubeOverlapCoreClose.C 3 :=
      (Tube.tubeOverlapCoreClose.one_lt_C 3).le
    have hpos : (0 : ℝ) ≤ Tube.tubeOverlapCoreClose.C 3 := by linarith
    have hsq1 : (1 : ℝ) ≤ Tube.tubeOverlapCoreClose.C 3 ^ 2 := by
      nlinarith [mul_le_mul h1 h1 (by norm_num : (0 : ℝ) ≤ 1) hpos]
    dsimp [plankTubeParents.C]
    nlinarith [hsq1]
  have hvd : volume (Tube.dilate (Tb l) (plankTubeParents.C 3)).carrier
      ≤ A * (bp : ENNReal) ^ 2 := by
    have hvd' : volume (Tube.dilate (Tb l) (plankTubeParents.C 3)).carrier
        ≤ (Real.toNNReal (plankTubeParents.C 3) : ENNReal) ^ 3
          * (Tube.volume_le.C 3 : ENNReal)
          * ((plankPigeonhole.C * bp : NNReal) : ENNReal) ^ 2 :=
      volume_dilate_le_of_dim_three hdim hbq1 hc (Tb l)
    refine le_trans hvd' ?_
    unfold A
    rw [ENNReal.coe_mul]
    rw [mul_pow]
    exact le_of_eq (by ring)
  have hlo : (plankPigeonhole.C_vol : ENNReal)⁻¹ * (ap : ENNReal) * (bp : ENNReal)
      ≤ volume ((fibre u'' pb l).convexHull_biUnion
          (fun i => (T i).toConvexSpaceBody)).carrier :=
    volume_convexHull_biUnion_fibre_ge hdim T pρ hu'' hmapsTo F hparts hdims pb l hnosplit
      hne
  calc
    volume (Tube.dilate (Tb l) (plankTubeParents.C 3)).carrier ≤ A * (bp : ENNReal) ^ 2 := hvd
    _ = M * ((plankPigeonhole.C_vol : ENNReal)⁻¹ * (ap : ENNReal) * (bp : ENNReal)) := hM.symm
    _ ≤ M * volume ((fibre u'' pb l).convexHull_biUnion
          (fun i => (T i).toConvexSpaceBody)).carrier := by
      gcongr

/-- **The `M` of `Kakeya.ml1Boot.volume_dilate_le_mul_volume_fibre_convexHull` is at least `1`**,
which is the side condition `Kakeya.ml1Boot.normalized_le_of_coarse_dilate` imposes on its `M`
binder.  Both factors are: `fibreMassShare.C ≥ 1` as a product of constants each at least `1`,
and `b_p / a_p ≥ 1` since the plank's long side dominates its short one (`hab`, the hypothesis
of the same name of `Kakeya.ml1Boot.frostmanConstIn_fibre_convexHull_le`). -/
theorem one_le_fibreMassShare_mul_ratio {ap bp : NNReal} (hap : 0 < ap) (hab : ap ≤ bp) :
    (1 : NNReal) ≤ fibreMassShare.C * bp / ap := by
  have one_le_volC : ∀ n : ℕ, (1 : NNReal) ≤ Metric.volume_comparison.C n := by
    intro n
    have hCval : Metric.volume_comparison.C n = ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) : ℝ) := by
      dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
      push_cast
      field_simp
    have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hfac : (1 : ℝ) ≤ (Nat.factorial n : ℝ) :=
      mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
    have : (1 : ℝ) ≤ (Metric.volume_comparison.C n : ℝ) := by
      rw [hCval]
      nlinarith
    exact_mod_cast this
  have hCw : (1 : NNReal) ≤ plankPigeonhole.C := by
    dsimp [plankPigeonhole.C]
    exact one_le_mul (by norm_num : (1 : NNReal) ≤ 16) (one_le_volC 3)
  have hCvol : (1 : NNReal) ≤ plankPigeonhole.C_vol := by
    dsimp [plankPigeonhole.C_vol]
    exact one_le_mul (one_le_mul (by norm_num : (1 : NNReal) ≤ 8) (one_le_pow₀ hCw))
      (one_le_volC 3)
  have hc : 1 < (plankTubeParents.C 3 : ℝ) := by
    have h1 : (1 : ℝ) ≤ Tube.tubeOverlapCoreClose.C 3 :=
      (Tube.tubeOverlapCoreClose.one_lt_C 3).le
    have hpos : (0 : ℝ) ≤ Tube.tubeOverlapCoreClose.C 3 := by linarith
    have hsq1 : (1 : ℝ) ≤ Tube.tubeOverlapCoreClose.C 3 ^ 2 := by
      nlinarith [mul_le_mul h1 h1 (by norm_num : (0 : ℝ) ≤ 1) hpos]
    dsimp [plankTubeParents.C]
    nlinarith [hsq1]
  have hptp : (1 : NNReal) ≤ Real.toNNReal (plankTubeParents.C 3) := by
    have hc0 : (0 : ℝ) ≤ plankTubeParents.C 3 := le_trans (by norm_num) (le_of_lt hc)
    have hcast : (Real.toNNReal (plankTubeParents.C 3) : ℝ) = plankTubeParents.C 3 := by
      rw [Real.toNNReal_of_nonneg hc0]
      rfl
    have : (1 : ℝ) ≤ (Real.toNNReal (plankTubeParents.C 3) : ℝ) := by
      rw [hcast]
      exact le_of_lt hc
    exact_mod_cast this
  have hC : (1 : NNReal) ≤ fibreMassShare.C := by
    dsimp [fibreMassShare.C]
    exact one_le_mul
      (one_le_mul
        (one_le_mul (by norm_num [Tube.volume_le.C] : (1 : NNReal) ≤ Tube.volume_le.C 3) hCvol)
        (one_le_pow₀ hCw))
      (one_le_pow₀ hptp)
  have hdiv : (1 : NNReal) ≤ bp / ap := by
    exact (one_le_div hap).2 hab
  calc
    (1 : NNReal) ≤ fibreMassShare.C * (bp / ap) := one_le_mul hC hdiv
    _ = fibreMassShare.C * bp / ap := (mul_div_assoc fibreMassShare.C bp ap).symm

end ml1Boot

end Kakeya
