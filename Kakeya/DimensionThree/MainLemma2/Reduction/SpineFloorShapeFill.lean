/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorGate
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeFillWitness

/-!
# `R5` — the fill is **manufactured** by the restriction, at `G2′`'s own constant

 and §5.2 (the plan's riskiest row).  The source, l.4133: *"Otherwise retain
complete factor cells."*

`Kakeya.ML2Core.exists_biasedMaximizer_densityIn_ge` (**`G2′`**, existing) produces,
on the **unrestricted** family of level-`c` cells under a level-`k` node, a subfamily `t` whose hull
`W` carries density within `(|W|/|U|)^ϖ` of `Δ_max`.  What this file adds is the one step `G2′` does
not take: **restricting to the cells inside `W` and reading the density at a grid node no larger
than `W` turns that into `Kakeya.ML2Core.FillAt`, by construction.**

## The chain, in six lines

Write `𝕍 := 𝒰.nodesUnder c k j`, `V j' := (𝒰.cover.tube c j').toConvexSpaceBody`,
`U := (𝒰.cover.tube k j).toConvexSpaceBody`, `W := hull t`, and `𝕍[W]` for the cells of `𝕍` inside
`W`.  Suppose a level-`q` node `jq` retains exactly `𝕍[W]` and is no larger than `W`.  Then

```
 κ · Δ_max(𝕍[W]) ≤ (|W|/|U|)^ϖ · Δ_max(𝕍[W])          (the choice of κ)
                 ≤ (|W|/|U|)^ϖ · Δ_max(𝕍)             (maxDensity_mono, 𝕍[W] ⊆ 𝕍)
                 ≤ Δ(𝕍, W)                             (G2′)
                 = (Σ_{𝕍[W]}|V|)/|W|                    (definition of Δ)
                 ≤ (Σ_{𝕍[W]}|V|)/|T_q|                  (|T_q| ≤ |W|)
                 = Δ(𝕍[W], T_q)                         (every retained cell is in T_q)
```

— which is `FillAt 𝒰 κ q c jq`.  **Every step is an inequality already in the tree**; the content is
that the *restriction* is what closes the gap between `Δ_max` and `Δ`, and that is why the fill is
*manufactured* and not found.

## What this does **not** claim, and the two hazards it avoids

* **`Δ_max` is not claimed to survive the cut.**
  `Kakeya.ML2Core.SpineFloorGateRed.not_biasedFactorization_retains_maxDensity` is the record that it does not, and 's hazard 2 is exactly a proof that quietly
  assumed otherwise.  Here `Δ_max(𝕍[W])` is bounded *above* by `Δ_max(𝕍)` and never below: the
  conclusion is about the **restricted** family only, and the survival of the ambient concentration
  remains a question to be **tested**, whose failure is `(D)`
  (`Kakeya.ML2Core.defect_of_refinement_concentration_destroyed`).
* **The re-selection ordering hazard does not arise**, because nothing here
  re-homogenizes.  `hretain` is a hypothesis about a grid node, and re-establishing
  `Kakeya.ML2Core.IsClassHomogeneousOn` on the retained family is `A1`'s job
  (`Kakeya.ML2Core.exists_classHomogeneous_pass_of_uniformTubeSet`), performed *before* this step in
  the source's order of operations (l.5899–5901), not after.  's hazard 1 is
  avoided by not having the composition at all.

## The two hypotheses that are genuinely owed

`hretain` — *the level-`q` node retains exactly the cells inside the hull* — and `hvol` —
*the node is no larger than the hull*.  Together they are the source's *"complete factor cells"* and
the blueprint's *"the grid level `q` of `W`'s middle John dimension"*.  They are **binders here**:
producing the level `q` from `W`'s John dimensions is `X2`/`X2′` and the `Metric.ethickness` rank
indexing, which is the floor block's `H-3` and is not this file's.  Naming them is the honest split.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section Fill

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ C : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}

omit [Nontrivial E] in
open scoped Classical in
/-- **`R5`, the core: the restriction manufactures the fill, at `G2′`'s constant.**

`hg2` is `Kakeya.ML2Core.exists_biasedMaximizer_densityIn_ge`'s conclusion, named; `hretain`
and `hvol` say the level-`q` node retains *exactly* the cells inside the maximizer's hull and is
no larger than it.  See the module docstring for the chain and for the two hazards this shape
avoids. -/
theorem fillAt_of_biasedMaximizer (𝒰 : Tube.UniformTubeSet s T N C) {ϖ κ : ℝ}
    {c k q : ℕ} {j jq : ι} {t : Finset ι}
    (hg2 : (volume (t.convexHull_biUnion
              (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)).carrier
            / volume (𝒰.cover.tube k j).carrier) ^ ϖ
        * Kakeya.maxDensity (𝒰.nodesUnder c k j)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
      ≤ Kakeya.densityIn (𝒰.nodesUnder c k j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
          (t.convexHull_biUnion (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)))
    (hretain : 𝒰.nodesUnder c q jq
      = Kakeya.familyIn (𝒰.nodesUnder c k j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
          (t.convexHull_biUnion (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)))
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
  have hsub : 𝒰.nodesUnder c q jq ⊆ 𝒰.nodesUnder c k j := by
    rw [hretain]; exact Finset.filter_subset _ _
  -- the retained cells are exactly the numerator of `Δ(𝕍, W)`
  have hnum : Kakeya.densityIn (𝒰.nodesUnder c k j) V Wh
      = (∑ j' ∈ 𝒰.nodesUnder c q jq, volume (V j').carrier) / volume Wh.carrier := by
    rw [hretain]; rfl
  unfold FillAt
  rw [densityIn_nodesUnder_self 𝒰 c q jq]
  calc ENNReal.ofReal κ * Kakeya.maxDensity (𝒰.nodesUnder c q jq) V
      ≤ (volume Wh.carrier / volume (𝒰.cover.tube k j).carrier) ^ ϖ
          * Kakeya.maxDensity (𝒰.nodesUnder c k j) V := by
        exact mul_le_mul' hκ (Kakeya.maxDensity_mono _ hsub)
    _ ≤ Kakeya.densityIn (𝒰.nodesUnder c k j) V Wh := hg2
    _ = (∑ j' ∈ 𝒰.nodesUnder c q jq, volume (V j').carrier) / volume Wh.carrier := hnum
    _ ≤ (∑ j' ∈ 𝒰.nodesUnder c q jq, volume (V j').carrier)
          / volume (𝒰.cover.tube q jq).carrier := by gcongr

omit [Nontrivial E] in
open scoped Classical in
/-- **`R5`, with `G2′` invoked: the fill exists.**

The level-`q` node is still a hypothesis (`hretain`, `hvol`) — producing it from the maximizer's
John dimensions is the floor block's `H-3`/`X2′` — but the *maximizer* and its constant are now
obtained rather than assumed.  This is 's statement with the one piece it
owns. -/
theorem exists_fillAt_of_maximizerRestriction (𝒰 : Tube.UniformTubeSet s T N C) {ϖ : ℝ}
    (hϖ : 0 < ϖ) {c k : ℕ} {j : ι}
    (hpos : ∃ j' ∈ 𝒰.nodesUnder c k j, 0 < volume (𝒰.cover.tube c j').carrier)
    (hU : ∀ j' ∈ 𝒰.nodesUnder c k j,
      (𝒰.cover.tube c j').toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody) :
    ∃ t ⊆ 𝒰.nodesUnder c k j, t.Nonempty ∧
      ∀ (q : ℕ) (jq : ι) (κ : ℝ),
        𝒰.nodesUnder c q jq
            = Kakeya.familyIn (𝒰.nodesUnder c k j)
                (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
                (t.convexHull_biUnion (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)) →
        volume (𝒰.cover.tube q jq).carrier
            ≤ volume (t.convexHull_biUnion
                (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)).carrier →
        ENNReal.ofReal κ
            ≤ (volume (t.convexHull_biUnion
                  (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)).carrier
                / volume (𝒰.cover.tube k j).carrier) ^ ϖ →
        FillAt 𝒰 κ q c jq := by
  classical
  obtain ⟨t, htsub, htne, hg2⟩ :=
    exists_biasedMaximizer_densityIn_ge (E := E)
      (𝕍 := 𝒰.nodesUnder c k j)
      (V := fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) hϖ hpos hU
  exact ⟨t, htsub, htne, fun q jq κ hretain hvol hκ =>
    fillAt_of_biasedMaximizer 𝒰 hg2 hretain hvol hκ⟩

end Fill

/-! ### Control -/

section Control

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ C : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}

omit [Nontrivial E] in
open scoped Classical in
/-- **Control: `hvol` is load-bearing.**  Without *"the node is no larger than the hull"* the last
step of the chain reverses — a bigger container lowers the density — and the fill does not follow.
Compiled as the arithmetic that fails: `x/A ≤ x/B` needs `B ≤ A`. -/
theorem fillAt_of_biasedMaximizer_needs_hvol :
    ∃ x a b : ℝ≥0∞, b < a ∧ ¬ x / b ≤ x / a :=
  ⟨1, 2, 1, by norm_num, by norm_num⟩

end Control

end Kakeya.ML2Core
