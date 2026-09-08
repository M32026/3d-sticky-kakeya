/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeForcing

/-!
# 's two notes on `R5`, folded in without re-cutting `the estimate`

 cleared `R5` (`Reduction/SpineFloorShapeFill.lean`) with **no re-cut**: the tie between the
reading node and the maximizer is `hretain` **and** `hvol` together — a *family* tie and a *size*
tie — both load-bearing, and the fixed-node refutation does not reach `R5` because the family
co-varies with the node.  The two notes it asks to be recorded are recorded here rather than by
editing a cleared patch.

## Note 1 — what `fillAt_of_biasedMaximizer_needs_hvol` is, and is not

It is an **arithmetic control on the chain's division step** — `x/b ≤ x/a` needs `a ≤ b` — and *not*
a firing control on `Kakeya.ML2Core.fillAt_of_biasedMaximizer`.  A firing control would have to
exhibit a hierarchy, a maximizer and a node at which the theorem's conclusion fails once `hvol` is
dropped; the statement does no such thing.  It records only that the last step of the chain
is the one `hvol` pays for.  `Kakeya.ML2Core.hvol_is_the_division_step` below is that reading, said
in the type.

## Note 2 — `hretain` is a `Finset` **equality**, and that is not automatic

`Kakeya.ML2Core.fillAt_of_biasedMaximizer` asks

```
    hretain : 𝒰.nodesUnder c q jq = Kakeya.familyIn (𝒰.nodesUnder c k j) V (t.convexHull_biUnion V)
```

— the level-`q` node's cells are **exactly** the cells of the level-`k` family inside the
maximizer's hull.  `X2`/`X2′` produce a grid-scale node *comparable to* the hull; **that a grid node
exists whose `nodesUnder` is exactly the hull's cell set is a further demand and is not automatic**:
a grid node at the hull's scale may clip a cell the hull contains, or contain one the hull does not.

**The escape, and it costs nothing on the left.**  Weaken `hretain` to `⊇` — the node retains *at
least* the hull's cells — and the chain still closes:

* the **right** side only grows, since `Kakeya.densityIn_mono'` is monotone in the family and the
  numerator of `Kakeya.ML2Core.densityIn_nodesUnder_self` is the full sum over the larger set;
* the **left** side is re-derived from `Kakeya.maxDensity_mono` **against the original family**
  `𝒰.nodesUnder c k j`, not against the hull's cells — which is what the chain already does
  (`hsub : 𝒰.nodesUnder c q jq ⊆ 𝒰.nodesUnder c k j`).

`Kakeya.ML2Core.fillAt_of_biasedMaximizer_supseteq` compiles that variant, so the escape is
available rather than merely described, and the equality form remains the one `the estimate` existing.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section Notes

/-- **Note 1, in the type.**  `Kakeya.ML2Core.fillAt_of_biasedMaximizer_needs_hvol` is a statement
about division in `ℝ≥0∞` and nothing more: the chain's last step needs the container to be no larger
than the hull.  Recording it this way keeps the word *"firing control"* off it. -/
theorem hvol_is_the_division_step {x a b : ℝ≥0∞} (hab : a ≤ b) : x / b ≤ x / a := by
  gcongr

end Notes

section Supseteq

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ C : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}

omit [Nontrivial E] in
open scoped Classical in
/-- **Note 2's escape,.**  `Kakeya.ML2Core.fillAt_of_biasedMaximizer` with `hretain`
weakened from a `Finset` **equality** to `⊇`: the level-`q` node need only retain *at least* the
cells of the maximizer's hull.

The left side is re-derived from `Kakeya.maxDensity_mono` against the **original** family, and the
right side only grows, so nothing in the chain is lost.  See the module docstring for why the
equality form is not automatic from `X2`/`X2′`. -/
theorem fillAt_of_biasedMaximizer_supseteq (𝒰 : Tube.UniformTubeSet s T N C) {ϖ κ : ℝ}
    {c k q : ℕ} {j jq : ι} {t : Finset ι}
    (hg2 : (volume (t.convexHull_biUnion
              (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)).carrier
            / volume (𝒰.cover.tube k j).carrier) ^ ϖ
        * Kakeya.maxDensity (𝒰.nodesUnder c k j)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
      ≤ Kakeya.densityIn (𝒰.nodesUnder c k j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
          (t.convexHull_biUnion (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)))
    -- the node retains AT LEAST the hull's cells, and no more than the level-`k` family
    (hretain : Kakeya.familyIn (𝒰.nodesUnder c k j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
          (t.convexHull_biUnion (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody))
        ⊆ 𝒰.nodesUnder c q jq)
    (hsub : 𝒰.nodesUnder c q jq ⊆ 𝒰.nodesUnder c k j)
    (hvol : volume (𝒰.cover.tube q jq).carrier
      ≤ volume (t.convexHull_biUnion
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)).carrier)
    (hκ : ENNReal.ofReal κ
      ≤ (volume (t.convexHull_biUnion
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)).carrier
          / volume (𝒰.cover.tube k j).carrier) ^ ϖ) :
    FillAt 𝒰 κ q c jq := by
  classical
  set V : ι → ConvexSpaceBody E := fun j' => (𝒰.cover.tube c j').toConvexSpaceBody with hV
  set Wh : ConvexSpaceBody E := t.convexHull_biUnion V with hWh
  -- the right side only grows: the numerator is now a sum over a LARGER set
  have hsum : (∑ i ∈ Kakeya.familyIn (𝒰.nodesUnder c k j) V Wh, volume (V i).carrier)
      ≤ ∑ j' ∈ 𝒰.nodesUnder c q jq, volume (V j').carrier :=
    Finset.sum_le_sum_of_subset hretain
  have hnum : Kakeya.densityIn (𝒰.nodesUnder c k j) V Wh
      ≤ (∑ j' ∈ 𝒰.nodesUnder c q jq, volume (V j').carrier) / volume Wh.carrier := by
    change (∑ i ∈ Kakeya.familyIn (𝒰.nodesUnder c k j) V Wh, volume (V i).carrier)
        / volume Wh.carrier ≤ _
    gcongr
  unfold FillAt
  rw [densityIn_nodesUnder_self 𝒰 c q jq]
  calc ENNReal.ofReal κ * Kakeya.maxDensity (𝒰.nodesUnder c q jq) V
      ≤ (volume Wh.carrier / volume (𝒰.cover.tube k j).carrier) ^ ϖ
          * Kakeya.maxDensity (𝒰.nodesUnder c k j) V :=
        mul_le_mul' hκ (Kakeya.maxDensity_mono _ hsub)
    _ ≤ Kakeya.densityIn (𝒰.nodesUnder c k j) V Wh := hg2
    _ ≤ (∑ j' ∈ 𝒰.nodesUnder c q jq, volume (V j').carrier) / volume Wh.carrier := hnum
    _ ≤ (∑ j' ∈ 𝒰.nodesUnder c q jq, volume (V j').carrier)
          / volume (𝒰.cover.tube q jq).carrier := by gcongr

end Supseteq

end Kakeya.ML2Core
