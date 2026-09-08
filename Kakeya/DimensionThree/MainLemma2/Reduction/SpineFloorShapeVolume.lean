/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Thickness.Volume
public import Kakeya.Thickness.Diam
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeFillWitness
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeForcing

/-!
# `T-S2`'s `hvol` engine — the two input obligations, named and discharged

Clause 2 of `Kakeya.ML2Core.IsFillSeparationCertificate` needs a **lower** bound on the volume of
the convex hull of a spread-out family of cells.  Three routes were tried across earlier rounds and
the record is :

* **tube containment** (hull `⊇` a fat tube, then `measure_mono` + `Tube.le_volume`) — **REFUTED**.
  Every `Kakeya.Tube` has axis length exactly one (`Tube.dist_eq_one`), so a tube inscribed in
  `seg + square + ball(0, δ)` has its end caps protruding past the segment's ends and its radius is
  capped by `δ`, not by the transverse spread.  The route is blind to the spread, which is the
  entire content of clause 2.
* **`Metric.lt_volume_convexHull`** (`Kakeya/Mathlib/MeasureTheory/Simplex.lean`) — needs four
  `infEDist pᵢ₊₁ (affineSpan {p₀.. pᵢ})` lower bounds, of which the tree has none.
* **`Convex.lt_volume_of_lt_ethickness` / `Convex.ethickness_prod_le_volume`** — needs
  `Metric.ethickness ℝ s i` lower bounds at ranks `0`, `1`, `2`.

This file settles the third route, and the settlement is **cheaper than the plan **.  That
plan priced ranks `1` and `2` at a new `ethickness_ge_of_orthogonal_spread` lemma (a 150–250 line
affine-independence argument).  That lemma is **not needed**:

> in an ambient space of dimension `3`, ranks `1` and `2` are both supplied by a **single inscribed
> closed ball**, via the existing `le_ethickness_closedBall`, and rank `0` is supplied by **two points
> far apart**, via the existing `Metric.half_dist_le_ethickness_zero`.

The reason the cheap route suffices is exactly the reason the tube route failed, read the other way
round.  For a `1 × w × w` box the honest values are `ethickness = (1/2, w/2, w/2)`; the inscribed
ball of radius `w/2` realizes ranks `1` and `2` with **no loss at all**, and only rank `0` — where
the ball would give `w/2` instead of `1/2` — needs the separate long-axis input.  A general spread
lemma would buy nothing beyond this.

So the two input obligations at the `T-S2` site, stated in Lean, are the hypotheses of
`Kakeya.ML2Core.le_volume_of_dist_of_closedBall_subset`:

* `hx : x ∈ s`, `hy : y ∈ s` — two hull points at distance `dist x y` (at the site: the two ends of
  any one cell's axis, at distance `1`);
* `hball : Metric.closedBall z r ⊆ s` — an inscribed ball (at the site: radius `w / 2` at the centre
  of the `w × w` transverse square, valid once `w ≤ 1`).

Nothing else about the family is used: no disjointness, no cardinality, no lattice structure.
-/

@[expose] public section

open MeasureTheory Metric

namespace Kakeya.ML2Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Inscribed-ball lower bound for `ethickness` at every rank below the ambient dimension.**
If `s` contains a closed ball of radius `r`, then `ethickness ℝ s n ≥ r` for every `n` below the
ambient dimension.  This is `le_ethickness_closedBall` composed with `Metric.ethickness_monotone`;
it is the rank-`1`/rank-`2` input obligation of `T-S2`'s `hvol`. -/
theorem ofReal_le_ethickness_of_closedBall_subset {s : Set E} {z : E} {r : ℝ} (hr : 0 ≤ r)
    (hball : Metric.closedBall z r ⊆ s) {n : ℕ} (hn : n < Module.finrank ℝ E) :
    ENNReal.ofReal r ≤ Metric.ethickness ℝ s n := by
  have hcoe : ((r.toNNReal : NNReal) : ℝ) = r := Real.coe_toNNReal r hr
  have h1 : ((r.toNNReal : NNReal) : ENNReal)
      ≤ Metric.ethickness ℝ (Metric.closedBall z ((r.toNNReal : NNReal) : ℝ)) n :=
    le_ethickness_closedBall (V := E) (x := z) r.toNNReal hn
  rw [hcoe] at h1
  exact h1.trans (Metric.ethickness_monotone hball n)

/-- **The `hvol` engine.**  In an ambient space of dimension `3`, a convex set containing two points
`x`, `y` and a closed ball of radius `r` has volume at least
`c(3) · (dist x y / 2) · r · r`, with `c(3) = Metric.lt_volume_convexHull.c 3 = 1 / 3!`.

The two hypotheses are exactly the two input obligations of `T-S2`'s clause 2: a long axis (rank
`0`) and a transverse inscribed ball (ranks `1` and `2`).  No general orthogonal-spread lemma is
needed; see this file's module docstring. -/
theorem le_volume_of_dist_of_closedBall_subset (hE : Module.finrank ℝ E = 3)
    {s : Set E} (hs : Convex ℝ s) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    {r : ℝ} (hr : 0 ≤ r) (hball : Metric.closedBall z r ⊆ s) :
    (Metric.lt_volume_convexHull.c 3 : ENNReal) * ENNReal.ofReal (dist x y / 2 * r * r)
      ≤ volume s := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hE]; norm_num)
  have h0 : ENNReal.ofReal (dist x y / 2) ≤ Metric.ethickness ℝ s 0 :=
    Metric.half_dist_le_ethickness_zero (𝕜 := ℝ) hx hy
  have h1 : ENNReal.ofReal r ≤ Metric.ethickness ℝ s 1 :=
    ofReal_le_ethickness_of_closedBall_subset hr hball (by rw [hE]; norm_num)
  have h2 : ENNReal.ofReal r ≤ Metric.ethickness ℝ s 2 :=
    ofReal_le_ethickness_of_closedBall_subset hr hball (by rw [hE]; norm_num)
  have key := hs.ethickness_prod_le_volume
  rw [hE] at key
  refine le_trans ?_ key
  have hd : (0 : ℝ) ≤ dist x y / 2 := by positivity
  rw [show (3 : ℕ) = 2 + 1 from rfl, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_one, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hd]
  gcongr

/-! ### The site: what `hvol` actually asks, and why `κ = 1` cannot be asked

`Kakeya.ML2Core.fillAt_one_of_maximizer_witness` carries
`hvol : volume (𝒰.cover.tube q jq).carrier ≤ volume (convexHull ℝ (⋃ cells))`.

`Tube.UniformTubeSet.nodesUnder` is *literal* containment (`Tube.UniformTubeSet.mem_nodesIn_iff`),
so every cell counted lies inside the node, the node's carrier is convex, and therefore the hull is
a subset of the node.  The inequality `hvol` then runs against
`Kakeya.ML2Core.volume_convexHull_nodesUnder_le` and **forces measure equality**: the cells' convex
hull must fill the node up to a null set.  That is recorded here as
`Kakeya.ML2Core.volume_eq_of_hvol_nodesUnder`.

This is a genuine obstruction to the `κ = 1` form, not a defect of any particular host: a finite
family of `ρ_c`-tubes inside a `ρ_q`-tube with `ρ_c < ρ_q` has a hull that is a *proper* convex
subset, and its volume is strictly smaller.  The lattice certificate must therefore run at some
`κ < 1`, which is what `Kakeya.ML2Core.fillAt_of_maximizer_witness` below provides, at the cost of
the honest hypothesis `κ · |node| ≤ |hull|` — the fraction of the node that the hull occupies.
-/

section Certificate

open scoped NNReal ENNReal
open Tube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ C : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
open scoped Classical in
/-- **The cells' hull lies inside their node.**  `Tube.UniformTubeSet.nodesUnder` is literal
containment and a node's carrier is convex, so the convex hull of the counted cells is a subset of
the node. -/
theorem convexHull_nodesUnder_subset (𝒰 : Tube.UniformTubeSet s T N C) (c q : ℕ) (jq : ι) :
    Convexity.convexHull ℝ (⋃ j' ∈ 𝒰.nodesUnder c q jq, (𝒰.cover.tube c j').carrier)
      ⊆ (𝒰.cover.tube q jq).carrier := by
  classical
  refine Convexity.convexHull_min ?_ (𝒰.cover.tube q jq).toConvexSpaceBody.isConvexSet
  refine Set.iUnion₂_subset fun j' hj' => ?_
  exact SetLike.coe_subset_coe.mpr
    ((𝒰.mem_nodesIn_iff c _ j').mp hj').2

omit [Nontrivial E] in
open scoped Classical in
/-- **The hull is never bigger than the node.**  The `≥` direction of `hvol`, always true. -/
theorem volume_convexHull_nodesUnder_le (𝒰 : Tube.UniformTubeSet s T N C) (c q : ℕ) (jq : ι) :
    volume (Convexity.convexHull ℝ (⋃ j' ∈ 𝒰.nodesUnder c q jq, (𝒰.cover.tube c j').carrier))
      ≤ volume (𝒰.cover.tube q jq).carrier :=
  measure_mono (convexHull_nodesUnder_subset 𝒰 c q jq)

omit [Nontrivial E] in
open scoped Classical in
/-- **`κ = 1`'s `hvol` forces measure equality.**  Combined with
`Kakeya.ML2Core.volume_convexHull_nodesUnder_le`, the hypothesis of
`Kakeya.ML2Core.fillAt_one_of_maximizer_witness` says the cells' hull fills the node up to a null
set.  A host whose cells are `ρ_c`-tubes strictly inside a `ρ_q`-tube cannot supply this, which is
why the certificate is cut at `κ < 1`. -/
theorem volume_eq_of_hvol_nodesUnder (𝒰 : Tube.UniformTubeSet s T N C) {c q : ℕ} {jq : ι}
    (hvol : volume (𝒰.cover.tube q jq).carrier
      ≤ volume (Convexity.convexHull ℝ (⋃ j' ∈ 𝒰.nodesUnder c q jq,
          (𝒰.cover.tube c j').carrier))) :
    volume (Convexity.convexHull ℝ (⋃ j' ∈ 𝒰.nodesUnder c q jq, (𝒰.cover.tube c j').carrier))
      = volume (𝒰.cover.tube q jq).carrier :=
  le_antisymm (volume_convexHull_nodesUnder_le 𝒰 c q jq) hvol

omit [Nontrivial E] in
open scoped Classical in
/-- **The `κ`-parametrised witness form.**  The `κ = 1` statement
`Kakeya.ML2Core.fillAt_one_of_maximizer_witness` asks for an unattainable `hvol`
(`Kakeya.ML2Core.volume_eq_of_hvol_nodesUnder`).  Here the hypothesis is the honest one: the hull
occupies at least a `κ` fraction of the node. -/
theorem fillAt_of_maximizer_witness (𝒰 : Tube.UniformTubeSet s T N C) {κ : ℝ} (hκ0 : 0 < κ)
    {c k q : ℕ} {j jq : ι}
    (hsub : 𝒰.nodesUnder c q jq ⊆ 𝒰.nodesUnder c k j)
    (hattain : Kakeya.densityInConvexHulliUnion
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) (𝒰.nodesUnder c q jq)
      = Kakeya.maxDensity (𝒰.nodesUnder c k j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody))
    (hvol : ENNReal.ofReal κ * volume (𝒰.cover.tube q jq).carrier
      ≤ volume (Convexity.convexHull ℝ (⋃ j' ∈ 𝒰.nodesUnder c q jq,
          (𝒰.cover.tube c j').carrier))) :
    FillAt 𝒰 κ q c jq := by
  classical
  set A : ENNReal := ∑ j' ∈ 𝒰.nodesUnder c q jq, volume (𝒰.cover.tube c j').carrier with hA
  set H : ENNReal := volume (Convexity.convexHull ℝ (⋃ j' ∈ 𝒰.nodesUnder c q jq,
    (𝒰.cover.tube c j').carrier)) with hH
  set V : ENNReal := volume (𝒰.cover.tube q jq).carrier with hV
  have hκne : ENNReal.ofReal κ ≠ 0 := by
    simpa using (ENNReal.ofReal_pos.mpr hκ0).ne'
  unfold FillAt
  rw [densityIn_nodesUnder_self 𝒰 c q jq]
  calc ENNReal.ofReal κ * Kakeya.maxDensity (𝒰.nodesUnder c q jq)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
      ≤ ENNReal.ofReal κ * Kakeya.maxDensity (𝒰.nodesUnder c k j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := by
        gcongr
        exact Kakeya.maxDensity_mono _ hsub
    _ = ENNReal.ofReal κ * (A / H) := by rw [← hattain]
    _ ≤ ENNReal.ofReal κ * (A / (ENNReal.ofReal κ * V)) :=
        mul_le_mul_right (ENNReal.div_le_div_left hvol A) _
    _ = (ENNReal.ofReal κ * A) / (ENNReal.ofReal κ * V) := by
        rw [← mul_div_assoc]
    _ = A / V := ENNReal.mul_div_mul_left A V hκne ENNReal.ofReal_ne_top

end Certificate

/-! ### The target admits a **false pass**, and (2) already forbade it

the bar is *"the rescue by restriction at a **fixed** reading node — and if both family and node
change, a demonstration that the node change alone does not suffice."*  The named target
`Kakeya.ML2Core.IsFillSeparationCertificate` does **not** encode that bar:
`Kakeya.ML2Core.isFillSeparationCertificate_of_nodesUnder_eq` below builds a certificate in which
the family does not change at all, so the whole separation comes from the node's shrinkage.

The construction needs no host: any nested pair of nodes carrying the *same* level-`c` family, with
the finer node of strictly smaller volume, gives a certificate at the explicit
`κ = (Σ|cells| / |node_q|).toReal`.  Clause 3 is then literally `rfl`, which is the form of
"clause 3 carries no information once the family is fixed".

**This is reported as a statement-level finding, not used as a certificate.**  Building the host for
it would be exactly the false pass  rejects.

**The two horns, both.**  Together with the existing
`Kakeya.ML2Core.node_ne_of_fillSeparationCertificate` this brackets the target:

* **fixed reading node.**  Clauses 1 and 3 force the node to move
  (`Kakeya.ML2Core.node_ne_of_fillSeparationCertificate`, existing), because at a fixed node with
  `Δ_max` preserved a restriction only shrinks the numerator
  (`Kakeya.ML2Core.fillAt_restrict_forces_maxDensity_lt`, existing).  So the *"fixed reading
  node"* reading is **provably unreachable**.
* **moving reading node.**  Once the node moves, the move alone suffices
  (`Kakeya.ML2Core.isFillSeparationCertificate_of_nodesUnder_eq`, this file), with the family held
  fixed.  So the *"a demonstration that the node change alone does not suffice"* is **not
  implied by the target's four clauses**.

Hence no host can make `IsFillSeparationCertificate`, as stated, meet the bar: the bar asks for
something the four clauses do not express.  The remedy is a fifth clause — a *proper* restriction
`𝒰.nodesUnder c q jq ⊊ 𝒰.nodesUnder c k j` together with a necessity clause pinning the failure of
the same `κ` at the level-`q` node for the **unrestricted** family — which is the source comparison's call,
since `IsFillSeparationCertificate` is a existing definition and this hand does not change it.
-/

section FalsePass

open scoped NNReal ENNReal
open Tube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ C : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}

omit [Nontrivial E] in
open scoped Classical in
/-- **A certificate with no restriction at all.**  If the level-`q` node carries exactly the same
level-`c` family as the level-`k` node, and the finer node has strictly smaller volume relative to
the family's mass, then `Kakeya.ML2Core.IsFillSeparationCertificate` holds at an explicit `κ`.

Nothing is restricted, so (2)'s bar is violated while the named target is met: the
target is missing a properness clause.  See this section's docstring. -/
theorem isFillSeparationCertificate_of_nodesUnder_eq (𝒰 : Tube.UniformTubeSet s T N C)
    {c k q : ℕ} {j jq : ι} (hkq : k < q)
    (hnodes : 𝒰.nodesUnder c q jq = 𝒰.nodesUnder c k j)
    (hM : Kakeya.maxDensity (𝒰.nodesUnder c k j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) = 1)
    (hfin : (∑ j' ∈ 𝒰.nodesUnder c k j, volume (𝒰.cover.tube c j').carrier)
      / volume (𝒰.cover.tube q jq).carrier ≠ ⊤)
    (hlt : (∑ j' ∈ 𝒰.nodesUnder c k j, volume (𝒰.cover.tube c j').carrier)
        / volume (𝒰.cover.tube k j).carrier
      < (∑ j' ∈ 𝒰.nodesUnder c k j, volume (𝒰.cover.tube c j').carrier)
        / volume (𝒰.cover.tube q jq).carrier) :
    IsFillSeparationCertificate 𝒰
      (((∑ j' ∈ 𝒰.nodesUnder c k j, volume (𝒰.cover.tube c j').carrier)
        / volume (𝒰.cover.tube q jq).carrier).toReal) c k q j jq := by
  classical
  set A : ENNReal := ∑ j' ∈ 𝒰.nodesUnder c k j, volume (𝒰.cover.tube c j').carrier with hA
  set Vk : ENNReal := volume (𝒰.cover.tube k j).carrier with hVk
  set Vq : ENNReal := volume (𝒰.cover.tube q jq).carrier with hVq
  have hofReal : ENNReal.ofReal ((A / Vq).toReal) = A / Vq := ENNReal.ofReal_toReal hfin
  refine ⟨hkq, ?_, ?_, by rw [hnodes]⟩
  · unfold FillAt
    rw [densityIn_nodesUnder_self 𝒰 c k j, hM, hofReal, mul_one, ← hA, ← hVk]
    exact not_le.mpr hlt
  · unfold FillAt
    rw [densityIn_nodesUnder_self 𝒰 c q jq, hnodes, hM, hofReal, mul_one, ← hA, ← hVq]

end FalsePass

end Kakeya.ML2Core
