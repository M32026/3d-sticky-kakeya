/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.EnlargementCover

/-!
# Main Lemma 1, Case (ii), Step 5a: the two loads, related

Blueprint `note:ml1bootStep5aTwoLoads`.  Step 5a produces two per-coarse-node load parameters and
the collision of Steps 5b–5c needs them related.  The note records the required inequality
`D_m ≤ Λ N_m (τ/θ) ^ 2` as **open**, lists three differences between the two quantities, and
offers two routes.  This file carries out both, because they are complementary rather than
alternative: each closes a different one of the three differences, and the third closes itself.

The three differences of the note, and what closes each:

1. *A density against a cardinality.*  `D_m` bounds `Δ(𝒩_b(P_a(l'')), P_a(l''))` while `N_m` is a
   count.  The direction the collision needs is `density ≤ cardinality × (τ/θ) ^ {n-1}`, and that
   is the **trivial** direction: a sum of at most `|s|` tube volumes over a body, each tube volume
   bounded above by `Kakeya.Tube.volume_le` and the body's volume bounded below by
   `Kakeya.Tube.le_volume`.  No essential distinctness and no efficient filling is used.  The
   note's caution — that `(τ/θ) ^ 2` "is the right conversion only if the fibre members are
   essentially distinct and fill `P_a(l'')` efficiently" — is about the *converse* direction, which
   is not needed here and is not proved here.  `Kakeya.densityIn_le_card_mul` and
   `Kakeya.ml1Boot.densityIn_nodesUnder_le_of_card` are this step.
2. *The retained family against the unrefined one.*  This is the note's route (ii): run the fibre
   completion at the unrefined level-`b` family `𝒰'_b` rather than at the retained `t_τ`.  It needs
   no new mathematics and no restatement — `Kakeya.ml1Boot.completedFibre` already takes the fine
   family as a parameter subject only to `t_τ ⊆ 𝒰'_b`, so `t_τ := 𝒰'.cover.indexSet b` is a legal
   instantiation at `Finset.Subset.refl`.  `Kakeya.ml1Boot.card_completedFibre_unrefined_le` is
   that instantiation, and it makes `N_m` an *unrefined* fibre cardinality.
3. *A parent-map fibre against a containment family.*  This is the note's route (i), the
   uniformity of the hierarchy, and it is already proved:
   `Kakeya.ml1Boot.card_nodesIn_le_card_coarseFibre` bounds `|𝒩_b(P_a(l))|` by
   `Cu ^ 5 |fibre(𝒰'_b, ϖ, l)|` — the containment family by the parent-map fibre of the *same*
   unrefined family.  `Kakeya.ml1Boot.card_nodesUnder_le_of_load` is the step that reads it against
   the load hypothesis.

The composite is `Kakeya.ml1Boot.densityIn_nodesUnder_le_of_load`: from the single load pair
`(N_m, Λ_load)` of the **unrefined** fibres it derives the density hypothesis `hdens` of
`Kakeya.ml1Boot.densityIn_le_of_rescale`, with

```
D_m = Cu ^ 5 · Λ_load · N_m · C_{loadToDensity}(n) · (τ/θ) ^ (n - 1).
```

In dimension `3` the exponent is `2`, so this **is** the note's `D_m ≤ Λ N_m (τ/θ) ^ 2` with
`Λ = Cu ^ 5 · Λ_load · C_{loadToDensity}(3)`.  Since the same `(N_m, Λ_load)` drives the completion
bound through `Kakeya.ml1Boot.card_completedFibre_unrefined_le`, the two loads of Step 5a are no
longer two: the question the note raised does not arise once the completion is run at `𝒰'_b`.

That relation speaks about **one** coarse node, while the hypothesis it is meant to discharge is
quantified over **every** neighbouring parent, so the composition is not immediate and is carried
out here: `Kakeya.ml1Boot.neighbouringParents_subset_indexSet` says a neighbouring parent is an
`a`-node, and `Kakeya.ml1Boot.densityIn_le_of_load` is (5.10a) with *both* Step 5a hypotheses
discharged — the covering family produced, and the density input produced from the load pair alone
at `t_θ = 𝒰'_a` and `Λ_Δ = 1`.  That declaration is the whole of Step 5a's upper side on one family
and one parameter, and it is what a consumer should cite.

The source runs the same three steps: its Step 5a(b) writes
`Δ(fibre, parent) ≈ N_m τ² / θ² = N_m δ̃²` at the unrefined family, with the `≈`-equality of the
neighbouring parents' fibre sizes coming from the uniformization (R2).  Only the upper half of that
`≈` is needed for the collision's numerator, and only the upper half is proved here.

## The load pair, and what is still owed

For the **unrefined** fibres the uniformity of the hierarchy supplies the pair, and the two halves
of the bracket are `Kakeya.ml1Boot.card_coarseFibre_le_branchingRatio` and
`Kakeya.ml1Boot.branchingRatio_le_card_coarseFibre`, which give
`Cu ⁻³ (N_a/N_b) ≤ |𝒰'_b[l]| ≤ Cu ³ (N_a/N_b)` at every `a`-node, so the pair is
`N_m = N_a/N_b`, `Λ_load = Cu ³`, and `Kakeya.ml1Boot.densityIn_le_of_uniformity` is (5.10a) read at
it with no free load parameter left.  All three are proved, each body being a short composition of
`Kakeya/DimensionThree/MainLemma1/CoarseFibre.lean`.

That is **weaker than the source's (R2)** on two counts, and must not be reported as it: it is
stated at the unrefined fibres only, so nothing is supplied for a retained `t_τ ⊊ 𝒰'_b`, for which
blueprint `lem:ml1bootFibreCompletion` still has no supplier; and `Λ_load = Cu ³` is a power of the
hierarchy's uniformity constant and not absolute, so the budget question — whether it meets
`δ ^ (-O(ε'))` — is moved and not answered.  Item (1) of blueprint
`note:ml1bootFibreCompletionStatus` is therefore discharged for the unrefined route and remains
owed for the retained families; what is closed outright is item (5) of that list — the *relation*
between the two loads — and nothing else.

A fourth statement now stands between the bracket and `Kakeya.ml1Boot.densityIn_le_of_uniformity`:
`Kakeya.ml1Boot.branchingRatio_le_card_completedFibre` (blueprint
`lem:ml1bootCompletionCardLower`), the composition of the lower half with
`Kakeya.ml1Boot.fibre_subset_completedFibre` at `t_τ = 𝒰'_b`.  It is proved, it is what gives the
lower half a consumer, and it is the cardinality input (C1) of the count at the tested body in
`Kakeya/DimensionThree/MainLemma1/Rescaling/AnchorDenominator.lean`.

## A generic lemma out of place

`Kakeya.densityIn_le_card_mul` mentions no tube, scale or hierarchy and belongs beside its mirror
image `Kakeya.densityIn_ge_of_count_volume` in `Kakeya/Density.lean`.  It is stated here to keep
this pass local to Step 5a; moving it is owed.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody StickyKakeya Tube Convexity

namespace Kakeya

section GenericDensity

variable {E : Type*} [TopologicalSpace E] [ConvexSpace ℝ E] [MeasureSpace E] {ι : Type*}

/-- **A density is at most a cardinality times a relative volume.**

If every member of `s` has volume at most `c` times that of the test body `K`, then
`Δ(𝕎, K) ≤ |s| c`.  This is the trivial half of the passage between a count and a density: the
sum defining `Kakeya.densityIn` has at most `|s|` terms, each at most `c · |K|`.

There is no hypothesis on `K` at all — in particular none excluding `|K| = 0` or `|K| = ∞` — the
statement being about the numerator of the quotient before it is divided.

The converse direction, bounding a cardinality below by a density, is
`Kakeya.densityIn_ge_of_count_volume` and needs the members to be pairwise disjoint or otherwise
efficiently packed; nothing of that kind is used here. -/
theorem densityIn_le_card_mul (s : Finset ι) (W : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E)
    {c : ENNReal} (hv : ∀ i ∈ s, volume (W i).carrier ≤ c * volume K.carrier) :
    densityIn s W K ≤ (s.card : ENNReal) * c := by
  classical
  unfold densityIn
  by_cases hK : volume K.carrier = 0
  · have hS : (∑ i ∈ s with W i ≤ K, volume (W i).carrier : ENNReal) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      have h_le0 : volume (W i).carrier ≤ (0 : ENNReal) := by
        simpa [hK] using hv i (Finset.mem_filter.mp hi).1
      exact le_antisymm h_le0 (by simp)
    simp [hK, hS]
  · by_cases hKtop : volume K.carrier = ⊤
    · simp [hKtop]
    · rw [ENNReal.div_le_iff hK hKtop]
      calc ∑ i ∈ s with W i ≤ K, volume (W i).carrier
          ≤ {i ∈ s | W i ≤ K}.card • (c * volume K.carrier) :=
            Finset.sum_le_card_nsmul _ _ _ fun i hi ↦ hv i (Finset.mem_filter.mp hi).1
        _ ≤ s.card • (c * volume K.carrier) :=
            nsmul_le_nsmul_left (by positivity) (Finset.card_filter_le s _)
        _ = (s.card : ENNReal) * c * volume K.carrier := by
            rw [nsmul_eq_mul, mul_assoc]

end GenericDensity

end Kakeya

namespace Tube

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- **The volume of a `σ`-tube against the volume of a `ρ`-tube.**

`|V| ≤ C(n) σ ^ (n-1)` by `Tube.volume_le` and `|W| ≥ c(n) ρ ^ (n-1)` by
`Tube.le_volume`, so `|V| ≤ (C(n)/c(n)) (σ/ρ) ^ (n-1) |W|`.  Both tubes have unit core, so
only the radii enter; `Tube.volume_carrier_eq_volume_carrier` makes the volume of a tube a
function of its radius alone, and this is the comparison of two such radii.

`0 < ρ` is what lets `ρ ^ (n-1)` be cancelled; `σ ≤ 1` is the hypothesis of
`Tube.volume_le`.  Nothing is asked of `σ / ρ`. -/
theorem volume_le_ratio_mul_volume {σ ρ : NNReal} (hσ1 : σ ≤ 1) (hρ0 : 0 < ρ)
    (V : Tube σ E) (W : Tube ρ E) :
    volume V.carrier
      ≤ ((volume_le.C (Module.finrank ℝ E)
            / le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
          * ((σ / ρ : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1) * volume W.carrier := by
  set n := Module.finrank ℝ E
  have hc : le_volume.c n ≠ 0 := (le_volume.c_pos n).ne'
  have hρ' : ρ ≠ 0 := hρ0.ne'
  have hc' : (volume_le.C n / le_volume.c n) * le_volume.c n = volume_le.C n :=
    div_mul_cancel₀ (volume_le.C n) hc
  have hpow : (σ / ρ) ^ (n - 1) * ρ ^ (n - 1) = σ ^ (n - 1) := by
    rw [← mul_pow, div_mul_cancel₀ σ hρ']
  have key : (volume_le.C n / le_volume.c n) * (σ / ρ) ^ (n - 1)
      * (le_volume.c n * ρ ^ (n - 1)) = volume_le.C n * σ ^ (n - 1) := by
    calc
      (volume_le.C n / le_volume.c n) * (σ / ρ) ^ (n - 1)
          * (le_volume.c n * ρ ^ (n - 1))
          = (volume_le.C n / le_volume.c n) * le_volume.c n
              * ((σ / ρ) ^ (n - 1) * ρ ^ (n - 1)) := by ac_rfl
      _ = volume_le.C n * σ ^ (n - 1) := by rw [hc', hpow]
  calc
    volume V.carrier ≤ ↑(volume_le.C n * σ ^ (n - 1)) := volume_le hσ1 V
    _ = ↑(((volume_le.C n / le_volume.c n) * (σ / ρ) ^ (n - 1))
        * (le_volume.c n * ρ ^ (n - 1))) := by rw [← key]
    _ = ↑((volume_le.C n / le_volume.c n) * (σ / ρ) ^ (n - 1))
        * ↑(le_volume.c n * ρ ^ (n - 1)) := by rw [ENNReal.coe_mul]
    _ ≤ ↑((volume_le.C n / le_volume.c n) * (σ / ρ) ^ (n - 1)) * volume W.carrier := by
        exact mul_le_mul_right (le_volume W)
          (↑((volume_le.C n / le_volume.c n) * (σ / ρ) ^ (n - 1)))
    _ = ↑(volume_le.C n / le_volume.c n) * ↑((σ / ρ) ^ (n - 1) : NNReal)
        * volume W.carrier := by rw [ENNReal.coe_mul]
    _ = ((volume_le.C n / le_volume.c n : NNReal) : ENNReal)
        * ((σ / ρ : NNReal) : ENNReal) ^ (n - 1) * volume W.carrier := by
        rw [ENNReal.coe_pow]

end Tube

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- **The dimensional constant of the cardinality-to-density conversion**, the ratio of the upper
constant of `Kakeya.Tube.volume_le` to the lower constant of `Kakeya.Tube.le_volume`.

It is the `O(1)` hidden in the source's `Δ(fibre, parent) ≈ N_m τ² / θ²` (Step 5a(b)), and it
depends on the ambient dimension and on nothing else. -/
noncomputable def loadToDensity.C (n : ℕ) : NNReal :=
  _root_.Tube.volume_le.C n / _root_.Tube.le_volume.c n

/-- **The density of a containment family at its parent, from a bare cardinality bound**
(blueprint `note:ml1bootStep5aTwoLoads`, difference 1).

`Δ(𝒩_b(P_a(l)), P_a(l)) ≤ N_m · C(n) · (τ/θ) ^ (n-1)` whenever `|𝒩_b(P_a(l))| ≤ N_m`.

This is `Kakeya.densityIn_le_card_mul` with the relative volume supplied by
`Kakeya.Tube.volume_le_ratio_mul_volume` at `σ = ρ_b` and `ρ = ρ_a`.  **No essential distinctness
and no packing hypothesis occurs**, because the direction proved is the trivial one; see the
module docstring. -/
theorem densityIn_nodesUnder_le_of_card {ι : Type*} {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (l : ι) {Nm : ENNReal}
    (hcard : ((𝒰'.nodesUnder b a l).card : ENNReal) ≤ Nm) :
    densityIn (𝒰'.nodesUnder b a l) (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
        (𝒰'.cover.tube a l).toConvexSpaceBody
      ≤ Nm * (loadToDensity.C (Module.finrank ℝ E) : ENNReal)
          * ((gridScale δ N b / gridScale δ N a : NNReal) : ENNReal)
              ^ (Module.finrank ℝ E - 1) := by
  let c₀ : ENNReal :=
    (loadToDensity.C (Module.finrank ℝ E) : ENNReal) *
      ((gridScale δ N b / gridScale δ N a : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)
  have hv : ∀ k ∈ 𝒰'.nodesUnder b a l,
      volume (𝒰'.cover.tube b k).toConvexSpaceBody.carrier
        ≤ c₀ * volume (𝒰'.cover.tube a l).toConvexSpaceBody.carrier := by
    intro k hk
    have h := Tube.volume_le_ratio_mul_volume
      (hσ1 := gridScale_le_one hδ1 N b) (hρ0 := gridScale_pos hδ0 N a)
      (V := 𝒰'.cover.tube b k) (W := 𝒰'.cover.tube a l)
    simpa [c₀, loadToDensity.C, mul_assoc] using h
  have hle := densityIn_le_card_mul (𝒰'.nodesUnder b a l)
    (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) (𝒰'.cover.tube a l).toConvexSpaceBody
    (c := c₀) hv
  have hfin : densityIn (𝒰'.nodesUnder b a l) (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
      (𝒰'.cover.tube a l).toConvexSpaceBody ≤ Nm * c₀ :=
    hle.trans (by simpa [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul_right hcard c₀)
  simpa [c₀, mul_assoc] using hfin

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The containment family of a coarse node, counted against the unrefined load**
(blueprint `note:ml1bootStep5aTwoLoads`, difference 3).

`|𝒩_b(P_a(l))| ≤ Cu ^ 5 · Λ_load · N_m`.  This is
`Kakeya.ml1Boot.card_nodesIn_le_card_coarseFibre` — the uniformity of the hierarchy, which is
route (i) of the note and is already proved — read against a load bound for the parent-map fibres
of the **unrefined** level-`b` family.  The `Cu ^ 5` is the whole cost of passing from the fibre
the load is stated at to the containment family the density is stated at. -/
theorem card_nodesUnder_le_of_load {ι : Type*} [DecidableEq ι] {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal} (hCu : 1 ≤ Cu)
    (𝒰' : UniformTubeSet s' T N Cu) {pθ : ι → ι} (hcnp : IsCoarseNodeParents 𝒰' a b pθ)
    {tθ : Finset ι} {Nm Λload : NNReal}
    (hload : ∀ l' ∈ tθ, ((fibre (𝒰'.cover.indexSet b) pθ l').card : NNReal) ≤ Λload * Nm)
    {l : ι} (hl : l ∈ 𝒰'.cover.indexSet a) (hltθ : l ∈ tθ) :
    ((𝒰'.nodesUnder b a l).card : NNReal) ≤ Cu ^ 5 * Λload * Nm := by
  have hcard : ((𝒰'.nodesUnder b a l).card : NNReal)
      ≤ Cu ^ 5 * (fibre (𝒰'.cover.indexSet b) pθ l).card := by
    rw [UniformTubeSet.nodesUnder]
    exact_mod_cast (card_nodesIn_le_card_coarseFibre hCu 𝒰' hcnp hl).2
  calc
    ((𝒰'.nodesUnder b a l).card : NNReal)
        ≤ Cu ^ 5 * (fibre (𝒰'.cover.indexSet b) pθ l).card := hcard
    _ ≤ Cu ^ 5 * (Λload * Nm) := by
      exact mul_le_mul_right (hload l hltθ) (Cu ^ 5)
    _ = Cu ^ 5 * Λload * Nm := by
      rw [mul_assoc]

/-- **The two loads of Step 5a, related** (blueprint `note:ml1bootStep5aTwoLoads`).

From the single load pair `(N_m, Λ_load)` of the parent-map fibres of the **unrefined** level-`b`
family,

```
Δ(𝒩_b(P_a(l)), P_a(l)) ≤ Cu ^ 5 · Λ_load · N_m · C(n) · (τ/θ) ^ (n-1),
```

which at `n = 3` is exactly the inequality `D_m ≤ Λ N_m (τ/θ) ^ 2` the note states and refuses to
assume, with `Λ = Cu ^ 5 · Λ_load · C(3)` — a constant of the hierarchy and of the dimension, and
in particular independent of the test body and of `l`.

This discharges hypothesis `hdens` of `Kakeya.ml1Boot.densityIn_le_of_rescale` and of
`Kakeya.ml1Boot.densityIn_le_of_neighbouringParents` at every neighbouring parent that lies in
`t_θ`, from the same data that
`Kakeya.ml1Boot.card_completedFibre_unrefined_le` reads on the completion side.  The two sides of
the collision are then stated in one parameter and not two.

It is the composition of `Kakeya.ml1Boot.card_nodesUnder_le_of_load` with
`Kakeya.ml1Boot.densityIn_nodesUnder_le_of_card`, and contains no argument of its own. -/
theorem densityIn_nodesUnder_le_of_load {ι : Type*} [DecidableEq ι] {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal} (hCu : 1 ≤ Cu)
    (𝒰' : UniformTubeSet s' T N Cu) {pθ : ι → ι} (hcnp : IsCoarseNodeParents 𝒰' a b pθ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {tθ : Finset ι} {Nm Λload : NNReal}
    (hload : ∀ l' ∈ tθ, ((fibre (𝒰'.cover.indexSet b) pθ l').card : NNReal) ≤ Λload * Nm)
    {l : ι} (hl : l ∈ 𝒰'.cover.indexSet a) (hltθ : l ∈ tθ) :
    densityIn (𝒰'.nodesUnder b a l) (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
        (𝒰'.cover.tube a l).toConvexSpaceBody
      ≤ ((Cu ^ 5 * Λload * Nm : NNReal) : ENNReal)
          * (loadToDensity.C (Module.finrank ℝ E) : ENNReal)
          * ((gridScale δ N b / gridScale δ N a : NNReal) : ENNReal)
              ^ (Module.finrank ℝ E - 1) := by
  have hcard1 : ((𝒰'.nodesUnder b a l).card : NNReal) ≤ Cu ^ 5 * Λload * Nm :=
    card_nodesUnder_le_of_load hCu 𝒰' hcnp hload hl hltθ
  have hcard : ((𝒰'.nodesUnder b a l).card : ENNReal) ≤
      ((Cu ^ 5 * Λload * Nm : NNReal) : ENNReal) := by
    exact_mod_cast hcard1
  simpa using densityIn_nodesUnder_le_of_card 𝒰' hδ0 hδ1 l hcard

omit [Nontrivial E] in
/-- **The completion, run at the unrefined level-`b` family** (blueprint
`note:ml1bootStep5aTwoLoads`, route (ii); `lem:ml1bootFibreCompletion`(c)).

`Kakeya.ml1Boot.card_completedFibre_le_rescale` at `t_τ = 𝒰'_b` and `t_θ = 𝒰'_a`.  It is a bare
instantiation: `Kakeya.ml1Boot.completedFibre` already takes the fine family as a parameter
subject only to `t_τ ⊆ 𝒰'_b`, so no definition and no structural fact of Step 5a is restated.
What changes is the *meaning* of `N_m`: the load pair is now that of the unrefined fibres, which
is the pair `Kakeya.ml1Boot.densityIn_nodesUnder_le_of_load` reads on the density side.

`h_pθ` is `Kakeya.ml1Boot.IsParentFamily.mapsTo` of `hcnp.parent`; it is written out rather than
bundled because `card_completedFibre_le_rescale` asks for it at an arbitrary `t_θ`. -/
theorem card_completedFibre_unrefined_le {ι : Type*} [DecidableEq ι] {δ : NNReal}
    {s' : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu)
    (hδ0 : 0 < δ) (hδ : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) {a b : ℕ} (haN : a < N) {pθ : ι → ι}
    (hcnp : IsCoarseNodeParents 𝒰' a b pθ) (Λ : NNReal) (l : ι) {Nm Λload : NNReal}
    (hload : ∀ l' ∈ 𝒰'.cover.indexSet a,
      ((fibre (𝒰'.cover.indexSet b) pθ l').card : NNReal) ≤ Λload * Nm) :
    ((completedFibre 𝒰' a b (𝒰'.cover.indexSet b) Λ l).card : NNReal)
      ≤ Λload * ((enlargementCoverConstant E Λ : ℕ) * Cu) * Nm := by
  exact card_completedFibre_le_rescale (δ := δ) (s' := s') (T := T) (N := N) (Cu := Cu)
    𝒰' hδ0 hδ (a := a) (b := b) haN (pθ := pθ) hcnp
    (tτ := 𝒰'.cover.indexSet b) (tθ := 𝒰'.cover.indexSet a)
    (htτ := Finset.Subset.refl (s := 𝒰'.cover.indexSet b))
    (hpθ := hcnp.parent.mapsTo) (Λ := Λ) l (Nm := Nm) (Λload := Λload)
    hload

/-! ### Assembling the relation into (5.10a)

`Kakeya.ml1Boot.densityIn_nodesUnder_le_of_load` is a statement about **one** coarse node, while
the hypothesis it is meant to discharge — `hdens` of `Kakeya.ml1Boot.densityIn_le_of_rescale` — is
quantified over **every** neighbouring parent.  The two are joined by the observation that a
neighbouring parent is an `a`-node, so that reading the relation at `t_θ = 𝒰'_a` covers the whole
quantifier.  Without this the relation discharges nothing downstream. -/

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **A neighbouring parent is an `a`-node.**

`Kakeya.ml1Boot.neighbouringParents 𝒰' a K` is the image of a subset of `s'` under `assign_a`, and
`Tube.GridCoverSystem.assign_mem` puts every such value in `𝒰'_a`. -/
theorem neighbouringParents_subset_indexSet {ι : Type*} {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {N a : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu) (ha : a ≤ N)
    (K : ConvexSpaceBody E) :
    neighbouringParents 𝒰' a K ⊆ 𝒰'.cover.indexSet a := by
  classical
  intro x hx
  rw [neighbouringParents, Finset.mem_image] at hx
  rcases hx with ⟨i, hi, rfl⟩
  exact 𝒰'.cover.assign_mem a ha i (Finset.mem_filter.mp hi).1

/-- **(GWZ (5.10a)) The local density bound at a coarse node, from a load pair alone**
(blueprint `lem:ml1bootLocalDensityUnrefined`, assembled through
blueprint `note:ml1bootStep5aTwoLoads`).

`Kakeya.ml1Boot.densityIn_le_of_rescale` with **both** of its Step 5a hypotheses discharged: the
covering family is produced by `Kakeya.ml1Boot.isEnlargementCover_node_rescale`, and the density
input `hdens` is produced by `Kakeya.ml1Boot.densityIn_nodesUnder_le_of_load` read at
`t_θ = 𝒰'_a`, which covers the whole quantifier by
`Kakeya.ml1Boot.neighbouringParents_subset_indexSet`.  So the bound is stated in terms of the
**single** load pair `(N_m, Λ_load)` of the unrefined fibres and of nothing else:

```
Δ(𝒰'_b, K') ≤ M(E,Λ) · C_ds · δ ^ (-ε') · (θ/τ) ^ (η m)
                · (C_ds ^ 5 · Λ_load · N_m · C_{loadToDensity}(n) · (τ/θ) ^ (n-1)).
```

`Λ_Δ` is `1` here and not a free parameter: the relation supplies the density bound exactly, with
no slack to absorb.

**This is the whole of Step 5a's upper side on one family and one parameter.**  What it does not
do is supply `(N_m, Λ_load)`: that pair is still given data here.  For the *unrefined* fibres a
supplier is stated below — `Kakeya.ml1Boot.card_coarseFibre_le_branchingRatio` and its lower
companion, read at `N_m = N_a / N_b` and `Λ_load = Cu ^ 3`, which is what
`Kakeya.ml1Boot.densityIn_le_of_uniformity` spends — and for the *retained* families there is
still none.  That is item (1) of blueprint `note:ml1bootFibreCompletionStatus`, which this lemma
leaves exactly where it is. -/
theorem densityIn_le_of_load {ι : Type*} {δ : NNReal} {s' : Finset ι} [DecidableEq ι]
    {T : ι → Tube δ E} {Cu : NNReal} {Kds cds a b m : ℕ} {p : Params} {ε' : ℝ}
    (hCu : 1 ≤ Cu) (𝒰' : UniformTubeSet s' T (ssfGridLen δ) Cu)
    (hblock : IsFrostmanDividingBlock 𝒰' Cu Kds cds p.η p.ε a b m p.N)
    (hloss : (Cu : ENNReal) * totalLoss Cu Kds cds δ ≤ (δ : ENNReal) ^ (-ε'))
    (hleaf : ∀ k ∈ 𝒰'.cover.indexSet b, ∃ i ∈ s', 𝒰'.cover.assign b i = k)
    {pθ : ι → ι} (hcnp : IsCoarseNodeParents 𝒰' a b pθ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδ : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ)))
    (Λ : NNReal) (l : ι) {Nm Λload : NNReal}
    (hload : ∀ l' ∈ 𝒰'.cover.indexSet a,
      ((fibre (𝒰'.cover.indexSet b) pθ l').card : NNReal) ≤ Λload * Nm)
    {K' : ConvexSpaceBody E}
    (hK' : K' ≤
      ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ (ssfGridLen δ) a)).toConvexSpaceBody) :
    densityIn (𝒰'.cover.indexSet b) (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K'
      ≤ 1 * ((enlargementCoverConstant E Λ : ℕ) * Cu : NNReal) * (δ : ENNReal) ^ (-ε') *
          ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m) *
          (((Cu ^ 5 * Λload * Nm : NNReal) : ENNReal)
            * (loadToDensity.C (Module.finrank ℝ E) : ENNReal)
            * ((gridScale δ (ssfGridLen δ) b / gridScale δ (ssfGridLen δ) a : NNReal) : ENNReal)
                ^ (Module.finrank ℝ E - 1)) := by
  refine densityIn_le_of_rescale 𝒰' hblock hloss hleaf hδ0 hδ Λ l ?_ hK'
  intro l'' hl''
  have ha : a ≤ ssfGridLen δ :=
    le_of_lt (lt_of_lt_of_le hblock.coarse_lt_fine hblock.fine_le)
  have hl''a : l'' ∈ 𝒰'.cover.indexSet a :=
    neighbouringParents_subset_indexSet 𝒰' ha _ hl''
  rw [one_mul]
  exact densityIn_nodesUnder_le_of_load hCu 𝒰' hcnp hδ0 hδ1 hload hl''a hl''a

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The unrefined load, upper half, from the uniformity** (blueprint
`lem:ml1bootLoadUpperFromUniformity`).

`|𝒰'_b[l]| ≤ Cu ^ 3 · (N_a / N_b)`, where `𝒰'_b[l] = Kakeya.ml1Boot.fibre (𝒰'_b) ϖ l` is the fibre
of the coarse parent map over the **unrefined** level-`b` family.  That bracket is neither the
containment family `𝒩_b(P_a(l))` of `Tube.UniformTubeSet.nodesUnder` nor the
contained-subfamily index set `Kakeya.familyIn`; the collision of notation is inherited from the
source.

Together with `Kakeya.ml1Boot.branchingRatio_le_card_coarseFibre` this is the load pair
`N_m = N_a / N_b`, `Λ_load = Cu ^ 3` at the unrefined fibres, in exactly the shape the `hload`
binder of `Kakeya.ml1Boot.densityIn_le_of_load` and of
`Kakeya.ml1Boot.card_completedFibre_unrefined_le` asks for.  **It is weaker than the source's (R2)
on two counts** — it is stated at the unrefined fibres only, so it says nothing about a retained
`t_τ ⊊ 𝒰'_b`, and its `Λ_load` is a power of the hierarchy's uniformity constant rather than an
absolute constant, so the budget question of blueprint `note:ml1bootLoadSupplierStatus` is moved and
not answered.

*Intended proof.*  The containment half of `Kakeya.ml1Boot.card_nodesIn_le_card_coarseFibre` gives
`𝒰'_b[l] ⊆ 𝒩_b(P_a(l))`, hence `|𝒰'_b[l]| ≤ |𝒩_b(P_a(l))|` — that first conjunct and not the
standalone `Kakeya.ml1Boot.fibre_subset_nodesIn`, which is the same containment but lives in the
*downstream* top-level `Kakeya/DimensionThree/MainLemma1.lean` and so cannot be imported here — and
`Kakeya.ml1Boot.branching_mul_card_nodesIn_le` gives `N_b · |𝒩_b(P_a(l))| ≤ Cu ^ 3 · N_a`; divide by
the strictly positive `N_b`.

`hNb` is what makes the ratio a number: at `N_b = 0` the `NNReal` quotient is `0` and the display
would be false.  It is free at every intended reading, following from any single `b`-node carrying a
leaf through the upper class bracket `Tube.UniformTubeSet.card_class_le`, as in the proof of
`Kakeya.ml1Boot.card_nodesIn_le_card_coarseFibre`; it is carried explicitly because nothing is asked
of `𝒰'_b[l]` here, and in particular not that it be nonempty.  No relation between `a` and `b`
beyond the `a ≤ b` of `Kakeya.ml1Boot.IsCoarseNodeParents` is used. -/
theorem card_coarseFibre_le_branchingRatio {ι : Type*} [DecidableEq ι] {δ : NNReal}
    {s' : Finset ι} {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal} (hCu : 1 ≤ Cu)
    (𝒰' : UniformTubeSet s' T N Cu) {pθ : ι → ι} (hcnp : IsCoarseNodeParents 𝒰' a b pθ)
    (hNb : 0 < 𝒰'.branchingN b) {l : ι} (hl : l ∈ 𝒰'.cover.indexSet a) :
    ((fibre (𝒰'.cover.indexSet b) pθ l).card : NNReal)
      ≤ Cu ^ 3 * (𝒰'.branchingN a / 𝒰'.branchingN b) := by
  classical
  -- Step 1: the fibre is contained in the containment family, so the counts compare.
  have hcard_le : (fibre (𝒰'.cover.indexSet b) pθ l).card
      ≤ (𝒰'.nodesIn b (𝒰'.cover.tube a l).toConvexSpaceBody).card := by
    exact Finset.card_le_card (card_nodesIn_le_card_coarseFibre hCu 𝒰' hcnp hl).1
  -- Step 2: `N_b · |𝒩_b(P_a(l))| ≤ Cu³ · N_a` in ℝ, from the counting lemma.
  have hbranch : (𝒰'.branchingN b : ℝ) *
        ((𝒰'.nodesIn b (𝒰'.cover.tube a l).toConvexSpaceBody).card : ℝ)
      ≤ (Cu : ℝ) ^ 3 * (𝒰'.branchingN a : ℝ) :=
    branching_mul_card_nodesIn_le 𝒰' hcnp.le_index hcnp.le_gridLen l
  have hNbR : 0 < (𝒰'.branchingN b : ℝ) := by exact_mod_cast hNb
  -- Chain: `N_b · |fibre| ≤ N_b · |nodesIn| ≤ Cu³ · N_a`.
  have hchain : (𝒰'.branchingN b : ℝ) * ((fibre (𝒰'.cover.indexSet b) pθ l).card : ℝ)
      ≤ (Cu : ℝ) ^ 3 * (𝒰'.branchingN a : ℝ) := by
    calc
      (𝒰'.branchingN b : ℝ) * ((fibre (𝒰'.cover.indexSet b) pθ l).card : ℝ)
          ≤ (𝒰'.branchingN b : ℝ) *
                ((𝒰'.nodesIn b (𝒰'.cover.tube a l).toConvexSpaceBody).card : ℝ) := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcard_le) (by positivity)
      _ ≤ (Cu : ℝ) ^ 3 * (𝒰'.branchingN a : ℝ) := hbranch
  -- Divide by the strictly positive `N_b`.
  have hdiv : ((fibre (𝒰'.cover.indexSet b) pθ l).card : ℝ)
      ≤ ((Cu : ℝ) ^ 3 * (𝒰'.branchingN a : ℝ)) / (𝒰'.branchingN b : ℝ) := by
    exact (le_div_iff₀ hNbR).mpr (by simpa [mul_comm] using hchain)
  -- Convert the quotient product to `Cu³ · (N_a / N_b)` and cast back to NNReal.
  have hdiv' : ((fibre (𝒰'.cover.indexSet b) pθ l).card : ℝ)
      ≤ (Cu : ℝ) ^ 3 * ((𝒰'.branchingN a : ℝ) / (𝒰'.branchingN b : ℝ)) := by
    rwa [mul_div_assoc] at hdiv
  exact_mod_cast hdiv'

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **The unrefined load, lower half, from the uniformity** (blueprint
`lem:ml1bootLoadLowerFromUniformity`).

`(Cu ^ 3)⁻¹ · (N_a / N_b) ≤ |𝒰'_b[l]|`, the companion of
`Kakeya.ml1Boot.card_coarseFibre_le_branchingRatio` at the *same* pair
`N_m = N_a / N_b`, `Λ_load = Cu ^ 3`.

*Intended proof.*  `Kakeya.ml1Boot.branching_le_mul_card_coarseFibre` delivers the sharper
`N_a ≤ Cu ^ 2 · N_b · |𝒰'_b[l]|`; divide by the strictly positive `Cu ^ 2 · N_b` and weaken
`Cu ⁻²` to `Cu ⁻³` using `hCu`.  The exponent is `3` and not `2` only so that the two halves may be
read at one constant; nothing downstream reads the value `3`, only that it is a power of `Cu` fixed
before `δ`.

**Its consumer is `Kakeya.ml1Boot.branchingRatio_le_card_completedFibre`** below, the cardinality
input (C1) of the count at the tested body; an earlier version of this docstring recorded the half
as having none, which the composition makes false.  It is not read by the completion bound
`Kakeya.ml1Boot.card_completedFibre_le` nor by the load binder of
`Kakeya.ml1Boot.densityIn_le_of_load`, which are upper bounds alone; it is stated at this pair
because `(N_m, Λ_load)` is what blueprint `lem:ml1bootFibreCompletion` is written in and that
lemma's hypothesis is two-sided; see blueprint `note:ml1bootLoadSupplierStatus`. -/
theorem branchingRatio_le_card_coarseFibre {ι : Type*} [DecidableEq ι] {δ : NNReal}
    {s' : Finset ι} {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal} (hCu : 1 ≤ Cu)
    (𝒰' : UniformTubeSet s' T N Cu) {pθ : ι → ι} (hcnp : IsCoarseNodeParents 𝒰' a b pθ)
    (hNb : 0 < 𝒰'.branchingN b) {l : ι} (hl : l ∈ 𝒰'.cover.indexSet a) :
    (Cu ^ 3)⁻¹ * (𝒰'.branchingN a / 𝒰'.branchingN b)
      ≤ ((fibre (𝒰'.cover.indexSet b) pθ l).card : NNReal) := by
  set F : ℝ := ((fibre (𝒰'.cover.indexSet b) pθ l).card : ℝ)
  have hNa : (𝒰'.branchingN a : ℝ)
      ≤ (Cu : ℝ) ^ 2 * (𝒰'.branchingN b : ℝ) * F := by
    simpa [F] using branching_le_mul_card_coarseFibre 𝒰' hcnp hl
  have hCu1 : (1 : ℝ) ≤ (Cu : ℝ) := by exact_mod_cast hCu
  have hCup : 0 < (Cu : ℝ) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hCu1
  have hCu3p : 0 < (Cu : ℝ) ^ 3 := pow_pos hCup 3
  have hNbR : 0 < (𝒰'.branchingN b : ℝ) := by exact_mod_cast hNb
  have hdiv : (𝒰'.branchingN a : ℝ) / (𝒰'.branchingN b : ℝ) ≤ (Cu : ℝ) ^ 2 * F := by
    rw [div_le_iff₀ hNbR]
    calc
      (𝒰'.branchingN a : ℝ) ≤ (Cu : ℝ) ^ 2 * (𝒰'.branchingN b : ℝ) * F := hNa
      _ = (Cu : ℝ) ^ 2 * F * (𝒰'.branchingN b : ℝ) := by ring
  have hinv0 : 0 ≤ ((Cu : ℝ) ^ 3)⁻¹ := inv_nonneg.mpr (le_of_lt hCu3p)
  have hmul : ((Cu : ℝ) ^ 3)⁻¹ * ((𝒰'.branchingN a : ℝ) / (𝒰'.branchingN b : ℝ))
      ≤ ((Cu : ℝ) ^ 3)⁻¹ * ((Cu : ℝ) ^ 2 * F) :=
    mul_le_mul_of_nonneg_left hdiv hinv0
  have hpow : (Cu : ℝ) ^ 2 ≤ (Cu : ℝ) ^ 3 := by
    simpa [pow_succ] using mul_le_mul_of_nonneg_left hCu1 (sq_nonneg (Cu : ℝ))
  have hfac : ((Cu : ℝ) ^ 3)⁻¹ * (Cu : ℝ) ^ 2 ≤ 1 := by
    rw [inv_mul_le_iff₀ hCu3p, mul_one]
    exact hpow
  have hF0 : 0 ≤ F := by positivity
  have hfin : ((Cu : ℝ) ^ 3)⁻¹ * ((Cu : ℝ) ^ 2 * F) ≤ F := by
    calc
      ((Cu : ℝ) ^ 3)⁻¹ * ((Cu : ℝ) ^ 2 * F) = (((Cu : ℝ) ^ 3)⁻¹ * (Cu : ℝ) ^ 2) * F := by ring
      _ ≤ 1 * F := mul_le_mul_of_nonneg_right hfac hF0
      _ = F := by ring
  have hmain : ((Cu : ℝ) ^ 3)⁻¹ * ((𝒰'.branchingN a : ℝ) / (𝒰'.branchingN b : ℝ)) ≤ F :=
    hmul.trans hfin
  exact_mod_cast hmain

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **(GWZ Step 5a bullet (b), the cardinality input) The completed unrefined fibre is
`≳ N_a / N_b`** (blueprint `lem:ml1bootCompletionCardLower`).

`(Cu ^ 3)⁻¹ (N_a / N_b) ≤ |\widetilde{𝒰'_b}(l)|`, the completion being
`Kakeya.ml1Boot.completedFibre` run at the **unrefined** fine family `t_τ = 𝒰'_b`, as
`Kakeya.ml1Boot.card_completedFibre_unrefined_le` runs it.  This is link (C1) of the route to the
anchor denominator: the cardinality lower bound the count at the tested body spends.

It is the composition of two proved facts and contains no argument of its own: the lower half of the
bracket, `Kakeya.ml1Boot.branchingRatio_le_card_coarseFibre`, bounds `(Cu ^ 3)⁻¹ (N_a/N_b)` by the
fibre `𝒰'_b[l]`, and `Kakeya.ml1Boot.fibre_subset_completedFibre` at `t_τ = 𝒰'_b`
(`Finset.Subset.refl`) puts that fibre inside the completion, whence the counts compare.  `hΛ` is
what the containment needs — a radius-rescaling to a *larger* radius contains the tube — and `hNb`
is what makes the ratio `N_a / N_b` a number, exactly as in the lower half.

**No load hypothesis is asked and the completion's own upper bound is not restated.**  The
containment reads neither the load pair nor the parent count, so `(N_m, Λ_load)` does not occur;
the matching upper bound is `Kakeya.ml1Boot.card_completedFibre_unrefined_le`, and the two together
are the two-sided count at the unrefined family in the reading `N_m = N_a / N_b`,
`Λ_load = Cu ^ 3`. -/
theorem branchingRatio_le_card_completedFibre {ι : Type*} [DecidableEq ι] {δ : NNReal}
    {s' : Finset ι} {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal} (hCu : 1 ≤ Cu)
    (𝒰' : UniformTubeSet s' T N Cu) {pθ : ι → ι} (hcnp : IsCoarseNodeParents 𝒰' a b pθ)
    (hNb : 0 < 𝒰'.branchingN b) {Λ : NNReal} (hΛ : 1 ≤ Λ) {l : ι}
    (hl : l ∈ 𝒰'.cover.indexSet a) :
    (Cu ^ 3)⁻¹ * (𝒰'.branchingN a / 𝒰'.branchingN b)
      ≤ ((completedFibre 𝒰' a b (𝒰'.cover.indexSet b) Λ l).card : NNReal) := by
  calc
    (Cu ^ 3)⁻¹ * (𝒰'.branchingN a / 𝒰'.branchingN b)
        ≤ ((fibre (𝒰'.cover.indexSet b) pθ l).card : NNReal) :=
          branchingRatio_le_card_coarseFibre hCu 𝒰' hcnp hNb hl
    _ ≤ ((completedFibre 𝒰' a b (𝒰'.cover.indexSet b) Λ l).card : NNReal) := by
          exact_mod_cast
            (Finset.card_le_card
              (fibre_subset_completedFibre 𝒰' hcnp (tτ := 𝒰'.cover.indexSet b)
                (htτ := Finset.Subset.refl (s := 𝒰'.cover.indexSet b)) hΛ l))

/-- **(GWZ (5.10a)) The local density bound at a coarse node, from the uniformity alone**
(blueprint `lem:ml1bootLocalDensityFromUniformity`).

`Kakeya.ml1Boot.densityIn_le_of_load` with its load hypothesis **deleted**: the pair is
instantiated at `N_m = N_a / N_b` and `Λ_load = Cu ^ 3`, the values
`Kakeya.ml1Boot.card_coarseFibre_le_branchingRatio` supplies at every `a`-node, so that

```
Δ(𝒰'_b, K') ≤ M(E,Λ) · C_ds · δ ^ (-ε') · (θ/τ) ^ (η m)
                · (C_ds ^ 5 · C_ds ^ 3 · (N_a / N_b) · C_{loadToDensity}(n) · (τ/θ) ^ (n-1))
```

for every convex body `K' ⊆ P_a(l) ^ (Λ ρ_a)`.  **There is no free load parameter left in it**:
everything on the right is a branching number of the hierarchy, a grid scale, one of the block's
own `δ`-dependent factors, or a constant already named.  Only the *upper* half of the bracket is
spent.

*Intended proof.*  `Kakeya.ml1Boot.densityIn_le_of_load` at that pair, its `hload` being
`Kakeya.ml1Boot.card_coarseFibre_le_branchingRatio` read at each `l' ∈ 𝒰'_a`.

*Divergence from the blueprint display, recorded.*  The blueprint also asks `N_b ≤ N_a`, because it
states `lem:ml1bootLocalDensityUnrefined` with the side condition `N_m ≥ 1`.  The Lean form
`Kakeya.ml1Boot.densityIn_le_of_load` carries no such side condition, so that hypothesis would be
read by nothing here and is omitted.  The constant is left as `Cu ^ 5 * Cu ^ 3` rather than
contracted to `Cu ^ 8`, so that the reading at `Λ_load = Cu ^ 3` stays visible.  What the omission
does **not** do is settle the budget question about `Cu ^ 3`, which is untouched here as it is at
`Kakeya.ml1Boot.densityIn_nodesUnder_le_of_load`. -/
theorem densityIn_le_of_uniformity {ι : Type*} {δ : NNReal} {s' : Finset ι} [DecidableEq ι]
    {T : ι → Tube δ E} {Cu : NNReal} {Kds cds a b m : ℕ} {p : Params} {ε' : ℝ}
    (hCu : 1 ≤ Cu) (𝒰' : UniformTubeSet s' T (ssfGridLen δ) Cu)
    (hblock : IsFrostmanDividingBlock 𝒰' Cu Kds cds p.η p.ε a b m p.N)
    (hloss : (Cu : ENNReal) * totalLoss Cu Kds cds δ ≤ (δ : ENNReal) ^ (-ε'))
    (hleaf : ∀ k ∈ 𝒰'.cover.indexSet b, ∃ i ∈ s', 𝒰'.cover.assign b i = k)
    {pθ : ι → ι} (hcnp : IsCoarseNodeParents 𝒰' a b pθ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδ : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ)))
    (hNb : 0 < 𝒰'.branchingN b)
    (Λ : NNReal) (l : ι) {K' : ConvexSpaceBody E}
    (hK' : K' ≤
      ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ (ssfGridLen δ) a)).toConvexSpaceBody) :
    densityIn (𝒰'.cover.indexSet b) (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K'
      ≤ ((enlargementCoverConstant E Λ : ℕ) * Cu : NNReal) * (δ : ENNReal) ^ (-ε') *
          ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m) *
          (((Cu ^ 5 * Cu ^ 3 * (𝒰'.branchingN a / 𝒰'.branchingN b) : NNReal) : ENNReal)
            * (loadToDensity.C (Module.finrank ℝ E) : ENNReal)
            * ((gridScale δ (ssfGridLen δ) b / gridScale δ (ssfGridLen δ) a : NNReal) : ENNReal)
                ^ (Module.finrank ℝ E - 1)) := by
  simpa only [one_mul] using densityIn_le_of_load hCu 𝒰' hblock hloss hleaf hcnp hδ0 hδ1 hδ Λ l
    (Nm := 𝒰'.branchingN a / 𝒰'.branchingN b) (Λload := Cu ^ 3)
    (fun l' hl' => card_coarseFibre_le_branchingRatio hCu 𝒰' hcnp hNb hl') hK'

end ml1Boot

end Kakeya
